
# /// script
# requires-python = ">=3.14"
# dependencies = ["marimo>=0.24.2", "pysmt", "z3-solver"]
# ///

import marimo

__generated_with = "0.24.2"
app = marimo.App(width="medium")


@app.cell
def _():
    import marimo as mo
    return (mo,)


@app.cell
def _(mo):
    mo.md(r"""
    # TP2 — Exercício 1: Game of Life (etapa 3: BMC)

    **Âmbito desta versão:** FSM, testes das transições e BMC
    da primeira propriedade (estado de erro inalcançável).
    Não inclui indução nem k-indução.

    **Fontes:** enunciado do TP2, Capítulo 3 (FOTS/SFOTS)
    e fichas práticas 7–9.

    O código foi proposto com assistência de uma LLM e
    necessita de validação na instalação local com pySMT e Z3.

    **Convenções e decisões:**

    - Para `N >= 3`, a grelha normal tem coordenadas
      `(1..N, 1..N)`; para a entrega usar `N > 16`.
    - Fronteira inicial: coordenadas com `i=0` ou `j=0`,
      valores fixos ao longo das transições. No início podem
      ser escolhidos por semente ou deixados simbólicos.
    - Fronteira final: coordenadas com `i=N+1` ou `j=N+1`,
      valor constante `False`, sem variáveis de estado.
    - Modo `individual`: a cada passo aplica-se B3/S23
      a exatamente uma célula, podendo o seu valor manter-se.
    - O índice inteiro auxiliar da célula escolhida é uma
      escolha não determinística por transição, não uma
      variável do estado. Ao fazer testes SAT, o índice livre
      é procurado existencialmente.
    """)
    return


@app.cell
def _():
    # Contributo da LLM: proposta de modelação FOTS e
    # construção das fórmulas pySMT.
    # Os testes SMT devem ser executados com pySMT e Z3.

    import random
    from pysmt.shortcuts import (
        And, Bool, Equals, Iff, Int, Ite,
        Not, Or, Plus, Symbol, is_sat
    )
    from pysmt.typing import BOOL, INT

    def declare(t, N):
        """Cópia t das células normais e da fronteira inicial."""
        if N < 3:
            raise ValueError(
                "Usar N >= 3; no problema final exige-se N > 16."
            )
        return {
            (i, j): Symbol(f"x_{i}_{j}_{t}", BOOL)
            for i in range(N + 1)
            for j in range(N + 1)
        }

    def fronteira_aleatoria(N, semente):
        """Gera uma fronteira inicial reprodutível."""
        rng = random.Random(semente)
        return {
            (i, j): rng.getrandbits(1)
            for i in range(N + 1)
            for j in range(N + 1)
            if i == 0 or j == 0
        }

    def init(state, N, fronteira=None):
        """
        Estado inicial.
        fronteira=None deixa as células iniciais livres.
        """
        normais = [
            state[i, j] if i <= 3 and j <= 3
            else Not(state[i, j])
            for i in range(1, N + 1)
            for j in range(1, N + 1)
        ]

        if fronteira is None:
            return And(normais)

        posicoes = [
            (i, j)
            for i in range(N + 1)
            for j in range(N + 1)
            if i == 0 or j == 0
        ]

        if set(fronteira) != set(posicoes) or any(
            v not in (0, 1) for v in fronteira.values()
        ):
            raise ValueError(
                "A fronteira deve conter exatamente 2N+1 valores 0/1."
            )

        fixas = [
            state[p] if fronteira[p] else Not(state[p])
            for p in posicoes
        ]

        return And(normais + fixas)

    def valor_celula(state, N, i, j):
        """
        Lê uma célula existente.
        Apenas a fronteira final é constante False.
        """
        if 0 <= i <= N and 0 <= j <= N:
            return state[i, j]

        if (
            0 <= i <= N + 1
            and 0 <= j <= N + 1
            and (i == N + 1 or j == N + 1)
        ):
            return Bool(False)

        raise ValueError(
            f"Coordenadas inválidas: ({i}, {j})"
        )

    def regra(state, N, i, j):
        """Regra B3/S23 para uma célula normal."""
        if not (1 <= i <= N and 1 <= j <= N):
            raise ValueError(
                "A regra B3/S23 só se aplica a células normais."
            )

        vizinhos = [
            valor_celula(state, N, i + di, j + dj)
            for di in (-1, 0, 1)
            for dj in (-1, 0, 1)
            if (di, dj) != (0, 0)
        ]

        vivos = Plus([
            Ite(v, Int(1), Int(0))
            for v in vizinhos
        ])

        return Or(
            Equals(vivos, Int(3)),
            And(state[i, j], Equals(vivos, Int(2)))
        )

    def trans(curr, prox, N, modo="simultanea"):
        """
        Relação de transição T(X,X').
        Atualização simultânea ou individual (interpretação A).
        """
        if modo not in ("simultanea", "individual"):
            raise ValueError(
                "modo deve ser 'simultanea' ou 'individual'."
            )

        # As células da fronteira inicial não mudam.
        fixas = [
            Iff(prox[i, j], curr[i, j])
            for i in range(N + 1)
            for j in range(N + 1)
            if i == 0 or j == 0
        ]

        restricoes = []

        if modo == "individual":
            # Escolha independente para cada transição.
            escolha = Symbol(
                "q_" + prox[1, 1].symbol_name(),
                INT
            )
            restricoes.extend([
                escolha >= Int(0),
                escolha < Int(N * N)
            ])

        for i in range(1, N + 1):
            for j in range(1, N + 1):
                novo = regra(curr, N, i, j)

                if modo == "individual":
                    indice = (i - 1) * N + (j - 1)
                    novo = Ite(
                        Equals(escolha, Int(indice)),
                        novo,
                        curr[i, j]
                    )

                restricoes.append(
                    Iff(prox[i, j], novo)
                )

        return And(fixas + restricoes)

    return (
        And, Not, declare, fronteira_aleatoria,
        init, is_sat, trans, valor_celula, regra
    )


@app.cell
def _(mo):
    mo.md(r"""
    ## Testes de coerência com pySMT e Z3

    Os testes usam inicialmente `N=5`, apenas para depurar
    a implementação.

    Verificamos:
    - dimensões e fronteiras;
    - estado inicial fixo e simbólico;
    - conservação da fronteira;
    - atualização simultânea;
    - atualização individual, incluindo uma atualização sem
      alteração do valor.

    **Organização Marimo:** as variáveis temporárias estão
    dentro de uma função local, evitando redefinições entre
    células. Isto não altera as fórmulas SMT.
    """)
    return


@app.cell
def _(
    And, Not, declare, fronteira_aleatoria,
    init, is_sat, trans, valor_celula
):
    def _testes_coerencia():
        # Contributo da LLM: testes de inicialização
        # e das duas relações de transição.

        def configuracao(state, vivas):
            return And([
                simbolo if pos in vivas else Not(simbolo)
                for pos, simbolo in state.items()
            ])

        N = 5
        x0 = declare("t0", N)
        x1 = declare("t1", N)
        fr = fronteira_aleatoria(N, 42)

        assert len(x0) == (N + 1) ** 2
        assert len(fr) == 2 * N + 1

        # Fronteira final: células mortas.
        assert valor_celula(x0, N, N + 1, 1).is_false()
        assert valor_celula(x0, N, 1, N + 1).is_false()

        # Coordenadas inválidas devem ser rejeitadas.
        try:
            valor_celula(x0, N, -1, 1)
            raise AssertionError(
                "Uma coordenada inválida não foi rejeitada."
            )
        except ValueError:
            pass

        # Uma célula normal em falta não é tratada como morta.
        try:
            valor_celula({}, N, 1, 1)
            raise AssertionError(
                "Uma célula normal em falta não foi rejeitada."
            )
        except KeyError:
            pass

        # Estado inicial com fronteira fixa.
        assert is_sat(
            init(x0, N, fr),
            solver_name="z3"
        )

        assert not is_sat(
            And(init(x0, N, fr), Not(x0[1, 1])),
            solver_name="z3"
        )

        assert not is_sat(
            And(init(x0, N, fr), x0[4, 4]),
            solver_name="z3"
        )

        # Fronteira simbólica: ambos os valores são possíveis.
        assert is_sat(
            And(init(x0, N), x0[0, 0]),
            solver_name="z3"
        )

        assert is_sat(
            And(init(x0, N), Not(x0[0, 0])),
            solver_name="z3"
        )

        # Fronteiras constantes em ambas as modalidades.
        for modo in ("individual", "simultanea"):
            assert not is_sat(
                And(
                    trans(x0, x1, N, modo),
                    x0[0, 0],
                    Not(x1[0, 0])
                ),
                solver_name="z3"
            )

        # Blinker horizontal -> vertical.
        horizontal = {(2, 1), (2, 2), (2, 3)}
        vertical = {(1, 2), (2, 2), (3, 2)}

        base = configuracao(x0, horizontal)
        sim = trans(x0, x1, N, "simultanea")
        ind = trans(x0, x1, N, "individual")

        assert is_sat(
            And(base, sim, configuracao(x1, vertical)),
            solver_name="z3"
        )

        assert not is_sat(
            And(
                base,
                sim,
                Not(configuracao(x1, vertical))
            ),
            solver_name="z3"
        )

        # Uma única célula morre na modalidade individual.
        assert is_sat(
            And(
                base,
                ind,
                configuracao(x1, {(2, 2), (2, 3)})
            ),
            solver_name="z3"
        )

        # Não podem ocorrer três mudanças numa transição individual.
        assert not is_sat(
            And(base, ind, configuracao(x1, vertical)),
            solver_name="z3"
        )

        # Uma atualização individual pode não alterar a grelha.
        assert is_sat(
            And(base, ind, configuracao(x1, horizontal)),
            solver_name="z3"
        )

        print("Testes SMT para N=5 concluídos.")

    _testes_coerencia()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Teste na dimensão mínima obrigatória

    O enunciado exige `N > 16`; por isso, usamos `N=17`.

    Este teste verifica a construção da grelha, a dimensão
    da fronteira e a satisfatibilidade de uma transição
    em ambas as modalidades.

    Ainda não constitui uma prova da primeira propriedade.
    """)
    return


@app.cell
def _(
    And, declare, fronteira_aleatoria,
    init, is_sat, trans
):
    def _teste_n17():
        # Contributo da LLM: teste de construção
        # na dimensão mínima exigida.

        N = 17
        X = declare("N17_a", N)
        Y = declare("N17_b", N)
        b17 = fronteira_aleatoria(N, 42)

        assert len(X) == 324
        assert len(b17) == 35

        I17 = init(X, N, b17)
        T17_sim = trans(X, Y, N, "simultanea")
        T17_ind = trans(X, Y, N, "individual")

        assert is_sat(
            And(I17, T17_sim),
            solver_name="z3"
        )

        assert is_sat(
            And(I17, T17_ind),
            solver_name="z3"
        )

        print(
            "Construção e testes de um passo "
            "para N=17 concluídos."
        )

    _teste_n17()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Teste de escolhas individuais consecutivas

    No modo individual, cada transição deve permitir
    uma escolha diferente da célula a atualizar.

    Usamos `N=5`, com fronteira morta:

    1. A primeira transição seleciona `(5,5)`, que continua morta.
    2. A segunda seleciona `(2,2)`, que morre por ter oito
       vizinhos vivos.

    Este teste confirma também que uma atualização pode não
    alterar o valor da célula selecionada.
    """)
    return


@app.cell
def _(And, Not, declare, init, is_sat, trans):
    def _teste_duas_escolhas():
        # Contributo da LLM: teste SMT de
        # duas escolhas individuais consecutivas.

        from pysmt.shortcuts import (
            Symbol as TestSymbol,
            Equals as TestEquals,
            Int as TestInt
        )
        from pysmt.typing import INT as TEST_INT

        n_teste = 5

        a, b, c = [
            declare(f"duas_escolhas_{t}", n_teste)
            for t in range(3)
        ]

        zeros = {
            (i, j): 0
            for i in range(n_teste + 1)
            for j in range(n_teste + 1)
            if i == 0 or j == 0
        }

        q_ab = TestSymbol(
            "q_" + b[1, 1].symbol_name(),
            TEST_INT
        )

        q_bc = TestSymbol(
            "q_" + c[1, 1].symbol_name(),
            TEST_INT
        )

        dois_passos = And(
            init(a, n_teste, zeros),
            trans(a, b, n_teste, "individual"),
            trans(b, c, n_teste, "individual"),

            TestEquals(q_ab, TestInt(24)),  # (5,5)
            TestEquals(q_bc, TestInt(6)),   # (2,2)

            init(b, n_teste, zeros),
            Not(c[2, 2]),
            c[1, 1]
        )

        assert is_sat(
            dois_passos,
            solver_name="z3"
        )

        print(
            "Teste SMT de duas escolhas individuais "
            "consecutivas: SAT (conforme esperado)."
        )

    _teste_duas_escolhas()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Primeira propriedade — não alcançar o estado de erro

    Segundo o enunciado, um estado de erro ocorre quando
    todas as células **normais** estão mortas.

    $$E(X)=\bigwedge_{i=1}^{N}\bigwedge_{j=1}^{N}\neg x_{i,j}$$

    A propriedade de segurança é:

    $$G\neg E$$

    Usando BMC, procuramos um percurso de comprimento `k`
    que termine num estado de erro:

    $$
    I(X^0)\land
    \bigwedge_{t=0}^{k-1}T(X^t,X^{t+1})
    \land E(X^k)
    $$

    Testamos `k=0,1,...,K` por ordem crescente.

    - `SAT`: existe um contraexemplo até à profundidade testada.
    - `UNSAT`: não existe contraexemplo nessa profundidade.

    Se todas as profundidades até `K` forem `UNSAT`,
    **não temos ainda uma prova global**.

    Quando existir um contraexemplo, extraímos os estados
    e validamos as transições com regras Python independentes
    das fórmulas SMT.
    """)
    return


@app.cell
def _(And, Not, declare, init, trans):
    # Contributo da LLM: predicado de erro,
    # BMC incremental e validador independente.

    from pysmt.shortcuts import (
        Solver as BMCSolver,
        Symbol as BMCSymbol
    )
    from pysmt.typing import INT as BMC_INT

    def error(state, N):
        """Todas as N² células normais estão mortas."""
        return And([
            Not(state[i, j])
            for i in range(1, N + 1)
            for j in range(1, N + 1)
        ])

    def validar_traco(estados, N, modo, escolhas, fronteira=None):
        """Valida um percurso sem usar pySMT nem Z3."""
        if modo not in ("individual", "simultanea"):
            raise ValueError("Modo inválido")

        if len(estados) != len(escolhas) + 1:
            raise AssertionError(
                "Número de transições inválido"
            )

        posicoes = {
            (i, j)
            for i in range(N + 1)
            for j in range(N + 1)
        }

        iniciais = {
            (i, j)
            for i, j in posicoes
            if i == 0 or j == 0
        }

        normais = [
            (i, j)
            for i in range(1, N + 1)
            for j in range(1, N + 1)
        ]

        def valor(s, i, j):
            if 0 <= i <= N and 0 <= j <= N:
                return int(s[i, j])

            if (
                0 <= i <= N + 1
                and 0 <= j <= N + 1
                and (i == N + 1 or j == N + 1)
            ):
                return 0

            raise ValueError(
                f"Coordenadas inválidas: ({i}, {j})"
            )

        for s in estados:
            assert set(s) == posicoes

            assert all(
                type(v) is bool for v in s.values()
            )

            if fronteira is not None:
                assert all(
                    s[p] == bool(fronteira[p])
                    for p in iniciais
                )

            assert all(
                s[p] == estados[0][p]
                for p in iniciais
            )

        # Confirmar o estado inicial.
        assert all(
            estados[0][i, j] == (i <= 3 and j <= 3)
            for i, j in normais
        )

        # Confirmar cada transição.
        for t, (antes, depois) in enumerate(
            zip(estados, estados[1:])
        ):
            escolhido = escolhas[t]

            if modo == "individual":
                assert (
                    isinstance(escolhido, int)
                    and 0 <= escolhido < N * N
                )
            else:
                assert escolhido is None

            for i, j in normais:
                viz = sum(
                    valor(antes, i + di, j + dj)
                    for di in (-1, 0, 1)
                    for dj in (-1, 0, 1)
                    if (di, dj) != (0, 0)
                )

                novo = (
                    (viz == 3)
                    or (antes[i, j] and viz == 2)
                )

                indice = (i - 1) * N + (j - 1)

                esperado = (
                    novo
                    if (
                        modo == "simultanea"
                        or escolhido == indice
                    )
                    else antes[i, j]
                )

                assert depois[i, j] == esperado, (
                    t, i, j
                )

        # O estado final deve ser um estado de erro.
        assert not any(
            estados[-1][i, j]
            for i, j in normais
        )

        return True

    def bmc_erro(N, modo, K, fronteira=None):
        """
        Procura um estado de erro até à profundidade K.
        Devolve o primeiro contraexemplo encontrado.
        """
        if (
            N < 3
            or K < 0
            or modo not in ("individual", "simultanea")
        ):
            raise ValueError(
                "Exige-se N>=3, K>=0 e um modo válido"
            )

        estados = [
            declare(f"bmc_{modo}_{N}_{t}", N)
            for t in range(K + 1)
        ]

        with BMCSolver(name="z3") as s:
            s.add_assertion(
                init(estados[0], N, fronteira)
            )

            for k in range(K + 1):
                if k > 0:
                    s.add_assertion(
                        trans(
                            estados[k - 1],
                            estados[k],
                            N,
                            modo
                        )
                    )

                s.push()
                s.add_assertion(error(estados[k], N))

                encontrado = s.solve()

                if encontrado:
                    # Extrair o modelo SAT.
                    concretos = [
                        {
                            p: bool(s.get_py_value(simbolo))
                            for p, simbolo in estado.items()
                        }
                        for estado in estados[:k + 1]
                    ]

                    if modo == "individual":
                        escolhas = [
                            int(s.get_py_value(
                                BMCSymbol(
                                    "q_" + estados[t + 1][1, 1].symbol_name(),
                                    BMC_INT
                                )
                            ))
                            for t in range(k)
                        ]
                    else:
                        escolhas = [None] * k

                    # Validação independente do solver.
                    validar_traco(
                        concretos,
                        N,
                        modo,
                        escolhas,
                        fronteira
                    )

                    print(
                        f"SAT: estado de erro alcançado em k={k}; "
                        "percurso validado."
                    )

                    # Apresentar os estados.
                    for t, grelha in enumerate(concretos):
                        print(f"Estado {t}:")

                        for i in range(N + 2):
                            print("".join(
                                "#"
                                if (
                                    grelha[i, j]
                                    if i <= N and j <= N
                                    else False
                                )
                                else "."
                                for j in range(N + 2)
                            ))

                        if t < k and modo == "individual":
                            q = escolhas[t]
                            print(
                                "  Próxima célula escolhida: "
                                f"({q // N + 1},{q % N + 1}), q={q}"
                            )

                    return {
                        "profundidade": k,
                        "estados": concretos,
                        "escolhas": escolhas,
                        "validado": True
                    }

                s.pop()

        print(
            f"UNSAT nas profundidades 0..{K}: "
            "sem contraexemplo neste limite; "
            "não é prova global."
        )
        return None

    return (error, validar_traco, bmc_erro)


@app.cell
def _(mo):
    mo.md(r"""
    ## Teste de controlo: contraexemplo conhecido

    Neste teste de depuração usamos `N=3` e uma fronteira
    inteiramente morta.

    Com atualização simultânea:

    - Estado inicial: 9 células vivas.
    - Após uma transição: 4 células vivas nos cantos.
    - Após duas transições: 0 células vivas.

    Esperamos encontrar um contraexemplo em `k=2`.

    Este exemplo não satisfaz a dimensão mínima do enunciado.
    Serve apenas para testar a implementação do BMC.
    """)
    return


@app.cell
def _(bmc_erro):
    def _teste_controlo_bmc():
        # Contributo da LLM: teste positivo do BMC
        # e da validação independente.

        n_controle = 3

        borda_zero = {
            (i, j): 0
            for i in range(n_controle + 1)
            for j in range(n_controle + 1)
            if i == 0 or j == 0
        }

        controle = bmc_erro(
            n_controle,
            "simultanea",
            2,
            borda_zero
        )

        assert (
            controle is not None
            and controle["profundidade"] == 2
            and controle["validado"]
        )

        print(
            "Teste de controlo SAT em N=3 concluído "
            "(se o solver confirmou k=2)."
        )

    _teste_controlo_bmc()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Experiências BMC de profundidade reduzida

    Vamos testar `N=5`, com profundidade máxima `K=2`,
    nas quatro combinações:

    1. Simultânea, fronteira fixa.
    2. Simultânea, fronteira simbólica.
    3. Individual, fronteira fixa.
    4. Individual, fronteira simbólica.

    Os resultados observados podem depender da modalidade
    e da configuração inicial.

    Estes testes continuam a ser apenas experiências de
    depuração e não provas para `N > 16`.
    """)
    return


@app.cell
def _(bmc_erro, fronteira_aleatoria):
    def _teste_cenarios_bmc():
        # Contributo da LLM: experiências BMC
        # nas quatro combinações.

        N_pequeno = 5
        K_pequeno = 2

        fixa = fronteira_aleatoria(N_pequeno, 42)

        for modo_pequeno in (
            "simultanea",
            "individual"
        ):
            for fronteira_nome, fronteira_valores in (
                ("fixa", fixa),
                ("simbólica", None)
            ):
                print(
                    f"\nModo {modo_pequeno} | "
                    f"fronteira {fronteira_nome} | "
                    f"N={N_pequeno}, K={K_pequeno}"
                )

                bmc_erro(
                    N_pequeno,
                    modo_pequeno,
                    K_pequeno,
                    fronteira_valores
                )

    _teste_cenarios_bmc()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Verificação na dimensão obrigatória: N=17

    Começamos por uma experiência com `N=17`, `K=1`,
    fronteira fixa com semente 42 e atualização simultânea.

    As outras combinações estão indicadas no código,
    para serem executadas posteriormente, uma de cada vez.

    Não devemos aumentar a profundidade antes de verificar
    os resultados e os tempos de execução.
    """)
    return


@app.cell
def _(bmc_erro, fronteira_aleatoria):
    def _teste_bmc_n17():
        # Contributo da LLM: primeira experiência BMC
        # com a dimensão mínima exigida.

        n_real = 17
        k_real = 1

        fronteira_real = fronteira_aleatoria(
            n_real, 42
        )

        resultado_real = bmc_erro(
            n_real,
            "simultanea",
            k_real,
            fronteira_real
        )

        # Experiências seguintes, a executar uma a uma:
        # bmc_erro(n_real, "individual", k_real, fronteira_real)
        # bmc_erro(n_real, "simultanea", k_real, None)
        # bmc_erro(n_real, "individual", k_real, None)

    _teste_bmc_n17()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Limitações e reprodução

    - `N=3` e `N=5` servem apenas para depuração.
    - A dimensão mínima válida é `N=17`.
    - `UNSAT` até `K` não prova que o erro nunca será alcançado.
    - `SAT` fornece um contraexemplo, que deve ser validado.
    - Uma fronteira fixa com semente representa apenas uma
      configuração inicial.
    - A fronteira simbólica considera todas as configurações
      possíveis, sem lhes atribuir probabilidades.
    - As versões das ferramentas, parâmetros e resultados reais
      devem ser registados após a execução.

    **Contribuição da LLM:**

    - Formalização e implementação da FSM.
    - Construção das relações de transição.
    - Predicado de erro e BMC.
    - Extração e validação independente dos contraexemplos.
    - Testes e organização das células Marimo.

    A solução e os resultados devem ser revistos pelos alunos,
    e a ligação para o diálogo com a LLM deve acompanhar
    a entrega do trabalho.

    **Próxima etapa:** após validar este BMC, discutir
    indução e k-indução para a primeira propriedade.
    """)
    return


if __name__ == "__main__":
    app.run()
