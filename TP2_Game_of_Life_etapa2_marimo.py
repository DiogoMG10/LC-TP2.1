
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
    # TP2 — Exercício 1: Game of Life

    ## Etapa 4 — Indução e k-indução

    Este notebook contém:

    - Modelação da FSM do Game of Life modificado.
    - Atualização simultânea e individual.
    - Fronteiras fixas ou simbolicamente livres.
    - Testes das regras e transições.
    - Predicado de erro e BMC.
    - Indução simples e k-indução da primeira propriedade.

    **Fontes:** enunciado do TP2, Capítulos 3 e 4,
    fichas práticas 7, 8 e 9.

    **Decisões de modelação:**

    - Células normais: índices de 1 a N, com N > 16.
    - Células iniciais: índice 0, constantes nas transições.
    - Células finais: índice N+1, sempre mortas.
    - A atualização individual aplica B3/S23 a uma célula,
      mesmo quando o seu valor não muda.
    - A fronteira pode ser fixada por semente ou deixada livre.

    O código foi desenvolvido com assistência de uma LLM.
    Os testes e resultados devem ser validados pelos alunos.
    """)
    return


@app.cell
def _():
    # Contributo da LLM:
    # Formulação da FSM e implementação com pySMT.

    import random

    from pysmt.shortcuts import (
        And, Bool, Equals, Iff, Int, Ite,
        Not, Or, Plus, Symbol, is_sat
    )
    from pysmt.typing import BOOL, INT

    def declare(t, N):
        """Cria uma cópia das variáveis de estado."""
        if N < 3:
            raise ValueError(
                "N deve ser >= 3; para o enunciado, N > 16."
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
        """Predicado dos estados iniciais."""
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
            raise ValueError("Fronteira inválida")

        fixas = [
            state[p] if fronteira[p]
            else Not(state[p])
            for p in posicoes
        ]
        return And(normais + fixas)

    def valor_celula(state, N, i, j):
        """Distingue células existentes, finais e inválidas."""
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
                "A regra só se aplica a células normais."
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
        """Relação de transição T(X,X')."""
        if modo not in ("simultanea", "individual"):
            raise ValueError("Modo inválido")

        # As células iniciais da fronteira não mudam.
        fixas = [
            Iff(prox[i, j], curr[i, j])
            for i in range(N + 1)
            for j in range(N + 1)
            if i == 0 or j == 0
        ]

        restricoes = []

        if modo == "individual":
            escolha = Symbol(
                "q_" + prox[1, 1].symbol_name(), INT
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
    ## Testes da FSM

    Começamos por testar as regras em grelhas pequenas.

    Estes testes verificam a inicialização, a preservação
    das fronteiras, a atualização simultânea e a atualização
    individual, incluindo situações em que a célula não muda.

    São testes de depuração: não substituem o requisito N > 16.
    """)
    return


@app.cell
def _(
    And, Not, declare, fronteira_aleatoria,
    init, is_sat, trans, valor_celula
):
    def _testes_coerencia():
        # Contributo da LLM: testes da FSM.
        # Variáveis temporárias locais para evitar
        # conflitos entre células Marimo.

        def configuracao(state, vivas):
            return And([
                simbolo if pos in vivas
                else Not(simbolo)
                for pos, simbolo in state.items()
            ])

        N = 5
        x0 = declare("t0", N)
        x1 = declare("t1", N)
        fr = fronteira_aleatoria(N, 42)

        assert len(x0) == (N + 1) ** 2
        assert len(fr) == 2 * N + 1
        assert valor_celula(x0, N, N + 1, 1).is_false()
        assert valor_celula(x0, N, 1, N + 1).is_false()

        try:
            valor_celula(x0, N, -1, 1)
            raise AssertionError(
                "Coordenada inválida não rejeitada"
            )
        except ValueError:
            pass

        try:
            valor_celula({}, N, 1, 1)
            raise AssertionError(
                "Célula em falta não rejeitada"
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

        # Fronteira simbólica.
        assert is_sat(
            And(init(x0, N), x0[0, 0]),
            solver_name="z3"
        )
        assert is_sat(
            And(init(x0, N), Not(x0[0, 0])),
            solver_name="z3"
        )

        # Fronteiras constantes.
        for modo in ("individual", "simultanea"):
            assert not is_sat(
                And(
                    trans(x0, x1, N, modo),
                    x0[0, 0],
                    Not(x1[0, 0])
                ),
                solver_name="z3"
            )

        # Blinker: horizontal -> vertical.
        horizontal = {(2, 1), (2, 2), (2, 3)}
        vertical = {(1, 2), (2, 2), (3, 2)}

        base = configuracao(x0, horizontal)
        sim = trans(x0, x1, N, "simultanea")
        ind = trans(x0, x1, N, "individual")

        assert is_sat(
            And(
                base,
                sim,
                configuracao(x1, vertical)
            ),
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

        # Atualização individual de uma célula.
        assert is_sat(
            And(
                base,
                ind,
                configuracao(x1, {(2, 2), (2, 3)})
            ),
            solver_name="z3"
        )

        # Não podem mudar três células num passo individual.
        assert not is_sat(
            And(
                base,
                ind,
                configuracao(x1, vertical)
            ),
            solver_name="z3"
        )

        # Uma atualização pode não alterar o estado.
        assert is_sat(
            And(
                base,
                ind,
                configuracao(x1, horizontal)
            ),
            solver_name="z3"
        )

        print("Testes SMT para N=5 concluídos.")

    _testes_coerencia()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Teste na dimensão mínima obrigatória

    Para N=17 temos 289 células normais e 35 células
    iniciais, totalizando 324 variáveis de estado.

    Verificamos a existência de uma transição em ambas
    as modalidades.
    """)
    return


@app.cell
def _(
    And, declare, fronteira_aleatoria,
    init, is_sat, trans
):
    def _teste_n17():
        # Contributo da LLM: teste na dimensão mínima.

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
    ## Duas atualizações individuais consecutivas

    Testamos que cada transição individual possui
    uma escolha independente.

    Com N=5 e fronteira morta:

    - Primeiro passo: selecionar (5,5), que não muda.
    - Segundo passo: selecionar (2,2), que morre
      por ter oito vizinhos vivos.

    Os dois passos utilizam escolhas diferentes.
    """)
    return


@app.cell
def _(And, Not, declare, init, is_sat, trans):
    def _teste_duas_escolhas():
        # Contributo da LLM: teste de escolhas consecutivas.

        from pysmt.shortcuts import (
            Symbol as TestSymbol,
            Equals as TestEquals,
            Int as TestInt
        )
        from pysmt.typing import INT as TEST_INT

        N = 5
        a, b, c = [
            declare(f"duas_escolhas_{t}", N)
            for t in range(3)
        ]

        zeros = {
            (i, j): 0
            for i in range(N + 1)
            for j in range(N + 1)
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
            init(a, N, zeros),
            trans(a, b, N, "individual"),
            trans(b, c, N, "individual"),
            TestEquals(q_ab, TestInt(24)),
            TestEquals(q_bc, TestInt(6)),
            init(b, N, zeros),
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
    ## Primeira propriedade: estado de erro

    Um estado de erro ocorre quando todas as células
    normais estão mortas.

    $$E(X)=\bigwedge_{i=1}^{N}
    \bigwedge_{j=1}^{N}\neg x_{i,j}$$

    Queremos provar a propriedade:

    $$G\neg E$$

    O BMC procura um percurso com k transições
    que termine num estado de erro:

    $$
    I(X^0)\land
    \bigwedge_{t=0}^{k-1}T(X^t,X^{t+1})
    \land E(X^k)
    $$

    SAT fornece um contraexemplo alcançável.
    UNSAT até K não constitui uma prova global.
    """)
    return


@app.cell
def _(And, Not, declare, init, trans):
    # Contributo da LLM:
    # Predicado de erro, BMC e validador independente.

    from pysmt.shortcuts import (
        Solver as BMCSolver,
        Symbol as BMCSymbol
    )
    from pysmt.typing import INT as BMC_INT

    def error(state, N):
        """Todas as células normais estão mortas."""
        return And([
            Not(state[i, j])
            for i in range(1, N + 1)
            for j in range(1, N + 1)
        ])

    def validar_traco(estados, N, modo, escolhas, fronteira=None):
        """Valida um contraexemplo sem utilizar o solver."""

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

        # Verificar os estados.
        for s in estados:
            assert set(s) == posicoes

            assert all(
                type(v) is bool
                for v in s.values()
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

        # Estado inicial.
        assert all(
            estados[0][i, j] == (i <= 3 and j <= 3)
            for i, j in normais
        )

        # Verificar todas as transições.
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
                    viz == 3
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

        # O último estado tem de ser um erro.
        assert not any(
            estados[-1][i, j]
            for i, j in normais
        )

        return True

    def bmc_erro(N, modo, K, fronteira=None):
        """Procura um contraexemplo até profundidade K."""

        if (
            N < 3
            or K < 0
            or modo not in ("individual", "simultanea")
        ):
            raise ValueError("Parâmetros inválidos")

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
                s.add_assertion(
                    error(estados[k], N)
                )

                encontrado = s.solve()

                if encontrado:
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

                    # Verificação independente.
                    validar_traco(
                        concretos,
                        N,
                        modo,
                        escolhas,
                        fronteira
                    )

                    print(
                        f"SAT: erro alcançado em k={k}; "
                        "percurso validado."
                    )

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
                                "Próxima célula: "
                                f"({q // N + 1},{q % N + 1}), "
                                f"q={q}"
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
    ## Teste positivo do BMC

    Grelha N=3 com fronteira toda morta.

    Na atualização simultânea:

    - Inicialmente: 9 células vivas.
    - Depois do primeiro passo: 4 células vivas.
    - Depois do segundo passo: 0 células vivas.

    Esperamos um contraexemplo em k=2.

    Este teste serve apenas para verificar o BMC.
    """)
    return


@app.cell
def _(bmc_erro):
    def _teste_controlo():
        # Contributo da LLM:
        # Teste conhecido de contraexemplo.

        N = 3

        zeros = {
            (i, j): 0
            for i in range(N + 1)
            for j in range(N + 1)
            if i == 0 or j == 0
        }

        resultado = bmc_erro(
            N, "simultanea", 2, zeros
        )

        assert resultado is not None
        assert resultado["profundidade"] == 2
        assert resultado["validado"]

        print("Teste de controlo BMC concluído.")

    _teste_controlo()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## BMC com quatro configurações

    Começamos por N=5 e K=2.

    Testamos:
    - Atualização simultânea com fronteira fixa.
    - Atualização simultânea com fronteira simbólica.
    - Atualização individual com fronteira fixa.
    - Atualização individual com fronteira simbólica.

    Estes resultados não substituem testes com N>16.
    """)
    return


@app.cell
def _(bmc_erro, fronteira_aleatoria):
    def _testes_bmc_pequeno():
        # Contributo da LLM:
        # Comparação das quatro configurações.

        N = 5
        K = 2

        fixa = fronteira_aleatoria(N, 42)

        for modo in ("simultanea", "individual"):
            for nome, fronteira in (
                ("fixa", fixa),
                ("simbólica", None)
            ):
                print(
                    f"\nModo={modo}, fronteira={nome}, "
                    f"N={N}, K={K}"
                )

                bmc_erro(N, modo, K, fronteira)

    _testes_bmc_pequeno()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## BMC para N=17

    Primeira experiência na dimensão mínima obrigatória.

    Utilizamos K=1, fronteira gerada com semente 42
    e atualização simultânea.
    """)
    return


@app.cell
def _(bmc_erro, fronteira_aleatoria):
    def _teste_bmc_n17():
        # Contributo da LLM:
        # Primeira experiência obrigatória.

        N = 17
        K = 1

        fixa = fronteira_aleatoria(N, 42)

        bmc_erro(
            N, "simultanea", K, fixa
        )

        # Outras experiências:
        # bmc_erro(N, "individual", K, fixa)
        # bmc_erro(N, "simultanea", K, None)
        # bmc_erro(N, "individual", K, None)

    _teste_bmc_n17()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Limitações do BMC

    - SAT com percurso validado demonstra que a segurança
      é violada.
    - UNSAT até K exclui contraexemplos nesse limite.
    - Uma fronteira aleatória fixa representa apenas uma
      configuração inicial.
    - A fronteira simbólica representa todas as configurações
      possíveis, mas não probabilidades.
    - As medições de desempenho devem ser registadas
      após execução real.

    **Contribuição LLM:** construção do BMC, extração
    de contraexemplos e verificação independente.
    """)
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Indução simples e k-indução

    Queremos provar o invariante:

    $$P(X)=\neg E(X)$$

    Ou seja, pelo menos uma célula normal está viva.

    ### Indução simples

    Verificar que ambas as fórmulas são UNSAT:

    **Base:**

    $$I(X_0)\land E(X_0)$$

    **Passo:**

    $$\neg E(X_0)\land T(X_0,X_1)\land E(X_1)$$

    ### k-indução

    A base exclui estados de erro alcançáveis nas
    profundidades `0,...,k-1`, através do BMC.

    O passo procura uma sequência arbitrária de k transições:

    $$
    \bigwedge_{t=0}^{k-1}\neg E(X_t)
    \land
    \bigwedge_{t=0}^{k-1}T(X_t,X_{t+1})
    \land E(X_k)
    $$

    **Com fronteira fixa**, acrescentamos o predicado
    $B_b(X_0)$ que fixa os seus valores no início do passo.
    A relação `trans` preserva esses valores nos estados
    seguintes.

    Não se impõe `init(X_0)` no passo: isso restringiria
    indevidamente os estados arbitrários.

    **Interpretação dos resultados:**

    - BASE SAT: contraexemplo alcançável, encontrado pelo BMC.
    - BASE UNSAT e PASSO UNSAT: prova global.
    - BASE UNSAT e PASSO SAT: tentativa inconclusiva.

    O modelo SAT do passo indutivo não prova acessibilidade.
    """)
    return


@app.cell
def _(
    And, Not, declare, trans,
    error, bmc_erro
):
    # Contributo da LLM:
    # Implementação de indução simples e k-indução.
    #
    # Alteração nesta revisão:
    # - Resultados BASE e PASSO apresentados separadamente.
    # - Confirmação da fronteira fixa nos modelos SAT do passo.

    from pysmt.shortcuts import Solver as IndSolver

    def k_inducao(N, modo, k, fronteira=None):
        """
        Verifica base e passo da k-indução.

        Resultados:
        - 'provada': base e passo UNSAT;
        - 'refutada': BMC encontrou contraexemplo real;
        - 'inconclusiva': passo indutivo SAT.
        """

        if (
            N < 3
            or k < 1
            or modo not in ("simultanea", "individual")
        ):
            raise ValueError("Parâmetros inválidos")

        print(
            f"\n{k}-indução | N={N} | modo={modo} | "
            f"fronteira={'simbólica' if fronteira is None else 'fixa'}"
        )

        # BASE: verificar acessibilidade até k-1.
        print(
            f"BASE: procurar erro nas profundidades 0..{k - 1}."
        )

        contraexemplo = bmc_erro(
            N, modo, k - 1, fronteira
        )

        if contraexemplo is not None:
            print(
                "BASE: SAT — contraexemplo alcançável e validado "
                f"em k={contraexemplo['profundidade']}."
            )
            print(
                "PASSO: não executado "
                "(a propriedade já foi refutada)."
            )
            print("CONCLUSÃO: REFUTADA.")

            return "refutada"

        print(
            f"BASE: UNSAT para as profundidades 0..{k - 1}."
        )

        # PASSO INDUTIVO:
        # Os estados não são necessariamente alcançáveis.
        print(
            "PASSO: a verificar preservação da propriedade..."
        )

        X = [
            declare(f"kind_{modo}_{N}_{k}_{t}", N)
            for t in range(k + 1)
        ]

        # P(X0), ..., P(X(k-1)).
        formulas = [
            Not(error(X[t], N))
            for t in range(k)
        ]

        # k transições consecutivas.
        formulas += [
            trans(X[t], X[t + 1], N, modo)
            for t in range(k)
        ]

        # Negação da propriedade no último estado.
        formulas.append(error(X[k], N))

        if fronteira is not None:
            # O primeiro estado é arbitrário, mas a fronteira
            # tem de coincidir com a configuração fixa.
            #
            # As transições preservam a fronteira.
            # Não impomos init(X[0]), pois isso seria
            # incorreto para um passo indutivo geral.

            formulas.extend([
                X[0][p] if valor else Not(X[0][p])
                for p, valor in fronteira.items()
            ])

        with IndSolver(name="z3") as solver:
            solver.add_assertion(And(formulas))

            if solver.solve():
                # Verificar que um modelo SAT com fronteira
                # fixa respeita essa fronteira em todos
                # os estados do passo indutivo.

                if fronteira is not None:
                    assert all(
                        bool(solver.get_py_value(X[t][p]))
                        == bool(valor)
                        for t in range(k + 1)
                        for p, valor in fronteira.items()
                    ), (
                        "A fronteira do modelo indutivo "
                        "não foi preservada"
                    )

                # Contar as células normais vivas
                # em cada estado do modelo indutivo.
                vivos = [
                    sum(
                        bool(solver.get_py_value(X[t][i, j]))
                        for i in range(1, N + 1)
                        for j in range(1, N + 1)
                    )
                    for t in range(k + 1)
                ]

                print(
                    "PASSO: SAT — a hipótese indutiva "
                    "é insuficiente."
                )

                print(
                    "Células normais vivas nos estados "
                    "arbitrários:", vivos
                )

                if fronteira is not None:
                    print(
                        "Fronteira fixa respeitada "
                        "em todos os estados."
                    )

                print(
                    "A acessibilidade do primeiro estado "
                    "não foi demonstrada."
                )

                print(
                    "CONCLUSÃO: INCONCLUSIVA "
                    "(não é uma refutação)."
                )

                return "inconclusiva"

        print(
            "PASSO: UNSAT — a preservação foi demonstrada."
        )
        print(
            "CONCLUSÃO: PROVADA (base e passo UNSAT)."
        )

        return "provada"

    def inducao_simples(N, modo, fronteira=None):
        """Indução simples corresponde a k=1."""
        return k_inducao(N, modo, 1, fronteira)

    return (inducao_simples, k_inducao)


@app.cell
def _(mo):
    mo.md(r"""
    ## Testes da indução com N=5

    Começamos por casos pequenos, cujos resultados
    conseguimos justificar logicamente.

    Com fronteira simbólica, existe um estado arbitrário
    com apenas uma célula normal viva, que pode evoluir
    para o estado de erro.

    Assim, o passo da indução simples deve falhar nas
    duas modalidades, sem que isso constitua um
    contraexemplo alcançável.

    Na modalidade individual, podemos prolongar um
    estado com uma única célula viva através de
    atualizações que não mudam o estado e, no último
    passo, atualizar a célula viva.

    Por isso, testamos também k=2 e k=3.
    """)
    return


@app.cell
def _(inducao_simples, k_inducao):
    def _testes_indutivos_pequenos():
        # Contributo da LLM:
        # Testes dos métodos indutivos.

        N = 5

        # Indução simples com fronteira simbólica.
        for modo in ("simultanea", "individual"):
            resultado = inducao_simples(
                N, modo, None
            )
            assert resultado == "inconclusiva"

        # k-indução individual.
        assert k_inducao(
            N, "individual", 2, None
        ) == "inconclusiva"

        assert k_inducao(
            N, "individual", 3, None
        ) == "inconclusiva"

        # k-indução simultânea, k=2:
        # observar o resultado sem o pressupor.
        k_inducao(
            N, "simultanea", 2, None
        )

        print(
            "Testes indutivos com N=5 concluídos."
        )

    _testes_indutivos_pequenos()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Indução simples com N=17

    Agora testamos a dimensão mínima exigida pelo
    enunciado.

    Para cada modalidade consideramos:

    - Fronteira fixa, com semente 42.
    - Fronteira simbolicamente livre.

    Não assumimos antecipadamente que a propriedade
    seja verdadeira ou falsa.

    Um resultado `inconclusiva` significa apenas que
    a indução simples não conseguiu demonstrá-la.

    Depois de observarmos estes resultados, poderemos
    executar k=2 com N=17, se houver justificação.
    """)
    return


@app.cell
def _(inducao_simples, fronteira_aleatoria):
    def _testes_indutivos_n17():
        # Contributo da LLM:
        # Experiências na dimensão mínima obrigatória.

        N = 17
        fixa = fronteira_aleatoria(N, 42)

        for modo in ("simultanea", "individual"):
            for fronteira in (fixa, None):
                inducao_simples(
                    N, modo, fronteira
                )

    _testes_indutivos_n17()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## Conclusões e limitações

    A primeira propriedade é uma propriedade de segurança:
    nunca alcançar o estado de erro.

    Os métodos têm significados diferentes:

    - BMC SAT com percurso validado: refutação real.
    - BMC UNSAT até K: ausência de erro apenas até K.
    - BASE UNSAT e PASSO UNSAT: prova global.
    - BASE UNSAT e PASSO SAT: tentativa inconclusiva.

    A fronteira fixa é considerada no passo indutivo.
    Os seus valores são preservados por todas as transições.

    A k-indução não tem de conseguir provar uma
    propriedade verdadeira.

    Na modalidade individual, os passos sem mudança
    permitem construir sequências arbitrárias que podem
    impedir o sucesso da k-indução simples.

    Para reproduzir os resultados devem registar-se:

    - Versões de Python, pySMT e Z3.
    - Dimensão N.
    - Modalidade de transição.
    - Fronteira fixa ou simbólica.
    - Semente, quando aplicável.
    - Profundidade K ou valor de k.
    - Resultados e tempos efetivamente observados.

    **Contribuições da LLM nesta etapa:**

    - Formulação das obrigações indutivas.
    - Implementação da indução e k-indução.
    - Reutilização do BMC para os casos de base.
    - Restrição correta das fronteiras fixas.
    - Verificação dos modelos SAT do passo indutivo.
    - Organização dos resultados em BASE, PASSO e CONCLUSÃO.

    A validação experimental deve ser confirmada pelos
    alunos antes de constar como resultado do trabalho.

    A segunda propriedade será tratada depois de
    analisarmos os resultados desta etapa.
    """)
    return


if __name__ == "__main__":
    app.run()
