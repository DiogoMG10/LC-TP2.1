
# /// script
# requires-python = ">=3.14"
# dependencies = ["marimo>=0.25.0", "pysmt", "z3-solver"]
# ///

import marimo

__generated_with = "0.25.0"
app = marimo.App(width="medium")


@app.cell
def _():
    import marimo as mo
    return (mo,)


@app.cell
def _(mo):
    mo.md(r"""
    # TP2 — Exercício 1: Game of Life modificado

    **Fontes:** enunciado do TP2, Capítulos 3 e 4 e
    fichas práticas 7, 8 e 9.

    ## 1. Descrição e formulação da FSM

    Construímos uma FSM `Σ = (X, I, T)` que representa
    uma versão modificada do Game of Life.

    - A grelha normal contém N×N células booleanas,
      com N > 16 no exercício.
    - As nove células do bloco inicial 3×3 começam vivas.
    - As restantes células normais começam mortas.
    - Existem 2N+1 células na fronteira inicial,
      com valor inicial aleatório de probabilidade 1/2.
    - Estas células conservam o seu valor nas transições.
    - Existem 2N+3 células na fronteira final,
      sempre mortas.
    - Cada célula normal tem oito vizinhos de Moore.

    **Regra B3/S23**

    Uma célula fica viva no passo seguinte se tiver
    exatamente três vizinhos vivos ou se estiver
    viva e tiver exatamente dois vizinhos vivos.

    **Relações de transição**

    - `simultanea`: todas as células normais são
      atualizadas no mesmo passo.
    - `individual`: exatamente uma célula normal
      aplica a regra num passo, podendo manter o
      mesmo valor (interpretação A).

    Na modalidade individual, um índice auxiliar
    inteiro identifica a célula selecionada. O índice
    não pertence às variáveis de estado.

    **Fronteiras**

    Podemos fixar uma fronteira reprodutível através
    de uma semente ou deixá-la simbolicamente livre.

    A fronteira simbólica permite todas as atribuições
    iniciais possíveis; não representa uma distribuição
    probabilística.

    **Contribuição da LLM**

    A modelação, as fórmulas e a implementação foram
    desenvolvidas com assistência de LLM. A interpretação
    A e as alternativas de fronteira foram discutidas
    ao longo do desenvolvimento.
    """)
    return


@app.cell
def _():
    # LLM — Formulação e implementação simbólica da FSM.
    # Preservada das etapas anteriores.

    import random

    from pysmt.shortcuts import (
        And, Bool, Equals, Iff, Int, Ite,
        Not, Or, Plus, Symbol, is_sat
    )
    from pysmt.typing import BOOL, INT

    def declare(t, N):
        if N < 3:
            raise ValueError(
                "N>=3 para depuração; N>16 no enunciado"
            )

        return {
            (i, j): Symbol(f"x_{i}_{j}_{t}", BOOL)
            for i in range(N+1)
            for j in range(N+1)
        }

    def fronteira_aleatoria(N, semente):
        rng = random.Random(semente)

        return {
            (i, j): rng.getrandbits(1)
            for i in range(N+1)
            for j in range(N+1)
            if i == 0 or j == 0
        }

    def init(state, N, fronteira=None):
        normais = [
            state[i, j] if i <= 3 and j <= 3
            else Not(state[i, j])
            for i in range(1, N+1)
            for j in range(1, N+1)
        ]

        if fronteira is None:
            return And(normais)

        posicoes = {
            (i, j)
            for i in range(N+1)
            for j in range(N+1)
            if i == 0 or j == 0
        }

        if set(fronteira) != posicoes or any(
            v not in (0, 1)
            for v in fronteira.values()
        ):
            raise ValueError("Fronteira inválida")

        return And(normais + [
            state[p] if fronteira[p] else Not(state[p])
            for p in sorted(posicoes)
        ])

    def valor_celula(state, N, i, j):
        if 0 <= i <= N and 0 <= j <= N:
            return state[i, j]

        if (
            0 <= i <= N+1
            and 0 <= j <= N+1
            and (i == N+1 or j == N+1)
        ):
            return Bool(False)

        raise ValueError(
            f"Coordenadas inválidas: {(i, j)}"
        )

    def regra(state, N, i, j):
        if not (1 <= i <= N and 1 <= j <= N):
            raise ValueError(
                "A regra apenas se aplica a células normais"
            )

        vizinhos = [
            valor_celula(state, N, i+di, j+dj)
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
        if modo not in ("individual", "simultanea"):
            raise ValueError("Modo inválido")

        fixas = [
            Iff(prox[i, j], curr[i, j])
            for i in range(N+1)
            for j in range(N+1)
            if i == 0 or j == 0
        ]

        restricoes = []

        if modo == "individual":
            escolha = Symbol(
                "q_" + prox[1, 1].symbol_name(),
                INT
            )

            restricoes += [
                escolha >= Int(0),
                escolha < Int(N*N)
            ]

        for i in range(1, N+1):
            for j in range(1, N+1):
                novo = regra(curr, N, i, j)

                if modo == "individual":
                    indice = (i-1)*N + j-1

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
        And, Bool, Equals, Iff, Int, Not, Or,
        Symbol, declare, fronteira_aleatoria,
        init, is_sat, trans, valor_celula, regra
    )


@app.cell
def _(mo):
    botao_fsm17 = mo.ui.run_button(
        label="Testar FSM N=17"
    )
    botao_bmc = mo.ui.run_button(
        label="Testes BMC P1"
    )
    botao_inducao = mo.ui.run_button(
        label="Testes de indução / k-indução"
    )
    botao_lacos = mo.ui.run_button(
        label="Laços P2: pesquisa"
    )
    botao_testemunhas = mo.ui.run_button(
        label="Confirmar testemunhas P1 e P2"
    )

    mo.vstack([
        mo.md(r"""
        ## 2. Controlo de execução

        Os testes básicos N=5 executam-se automaticamente.

        Os testes N=17, BMC, indução, pesquisa de laços
        e confirmação de testemunhas executam-se
        manualmente para evitar trabalho pesado
        ao abrir o notebook.

        Os botões não alteram a formulação lógica.
        """),
        botao_fsm17,
        botao_bmc,
        botao_inducao,
        botao_lacos,
        botao_testemunhas
    ])

    return (
        botao_fsm17, botao_bmc, botao_inducao,
        botao_lacos, botao_testemunhas
    )


@app.cell
def _(mo):
    mo.md(r"""
    ## 3. Testes básicos de correção

    Os testes seguintes verificam:

    - Estado inicial com fronteira fixa e simbólica.
    - Células finais e coordenadas inválidas.
    - Conservação da fronteira inicial.
    - Regra B3/S23, usando um oscilador `blinker`.
    - Atualização individual com e sem mudança de valor.
    - Escolhas independentes em passos consecutivos.

    N=5 é utilizado apenas para depuração.
    """)
    return


@app.cell
def _(
    And, Not, declare, fronteira_aleatoria,
    init, is_sat, trans, valor_celula
):
    # LLM — Testes SMT de regressão da FSM.

    def _testes_fsm():
        def configuracao(s, vivas):
            return And([
                v if p in vivas else Not(v)
                for p, v in s.items()
            ])

        N = 5
        a = declare("teste_fsm_a", N)
        b = declare("teste_fsm_b", N)
        fr = fronteira_aleatoria(N, 42)

        assert len(a) == 36
        assert len(fr) == 11

        assert valor_celula(
            a, N, N+1, 1
        ).is_false()

        assert valor_celula(
            a, N, 1, N+1
        ).is_false()

        try:
            valor_celula(a, N, -1, 1)
            raise AssertionError("Posição inválida aceite")
        except ValueError:
            pass

        try:
            valor_celula({}, N, 1, 1)
            raise AssertionError("Célula em falta aceite")
        except KeyError:
            pass

        assert is_sat(
            init(a, N, fr),
            solver_name="z3"
        )

        assert not is_sat(
            And(init(a, N, fr), Not(a[1, 1])),
            solver_name="z3"
        )

        assert not is_sat(
            And(init(a, N, fr), a[4, 4]),
            solver_name="z3"
        )

        assert is_sat(
            And(init(a, N), a[0, 0]),
            solver_name="z3"
        )

        assert is_sat(
            And(init(a, N), Not(a[0, 0])),
            solver_name="z3"
        )

        for modo in ("individual", "simultanea"):
            assert not is_sat(
                And(
                    trans(a, b, N, modo),
                    a[0, 0],
                    Not(b[0, 0])
                ),
                solver_name="z3"
            )

        horizontal = {(2, 1), (2, 2), (2, 3)}
        vertical = {(1, 2), (2, 2), (3, 2)}

        base = configuracao(a, horizontal)
        sim = trans(a, b, N, "simultanea")
        ind = trans(a, b, N, "individual")

        assert is_sat(
            And(
                base, sim,
                configuracao(b, vertical)
            ),
            solver_name="z3"
        )

        assert not is_sat(
            And(
                base, sim,
                Not(configuracao(b, vertical))
            ),
            solver_name="z3"
        )

        assert is_sat(
            And(
                base, ind,
                configuracao(b, {(2, 2), (2, 3)})
            ),
            solver_name="z3"
        )

        assert not is_sat(
            And(
                base, ind,
                configuracao(b, vertical)
            ),
            solver_name="z3"
        )

        assert is_sat(
            And(
                base, ind,
                configuracao(b, horizontal)
            ),
            solver_name="z3"
        )

        print("FSM N=5: testes SMT concluídos")

    _testes_fsm()
    return


@app.cell
def _(
    And, Equals, Int, Not, Symbol,
    declare, init, is_sat, trans
):
    # LLM — Duas escolhas individuais consecutivas.

    def _testar_duas_escolhas():
        from pysmt.typing import INT as T_INT

        N = 5

        a, b, c = [
            declare(f"duas_escolhas_{t}", N)
            for t in range(3)
        ]

        zeros = {
            (i, j): 0
            for i in range(N+1)
            for j in range(N+1)
            if i == 0 or j == 0
        }

        q1 = Symbol(
            "q_" + b[1, 1].symbol_name(),
            T_INT
        )

        q2 = Symbol(
            "q_" + c[1, 1].symbol_name(),
            T_INT
        )

        formula = And(
            init(a, N, zeros),
            trans(a, b, N, "individual"),
            trans(b, c, N, "individual"),
            Equals(q1, Int(24)),
            Equals(q2, Int(6)),
            init(b, N, zeros),
            Not(c[2, 2]),
            c[1, 1]
        )

        assert is_sat(formula, solver_name="z3")

        print(
            "Duas escolhas individuais consecutivas: "
            "SAT (esperado)"
        )

    _testar_duas_escolhas()
    return


@app.cell
def _(
    And, declare, fronteira_aleatoria,
    init, is_sat, trans, mo, botao_fsm17
):
    mo.stop(not botao_fsm17.value)

    def _testar_n17():
        N = 17
        a = declare("N17_a", N)
        b = declare("N17_b", N)
        fr = fronteira_aleatoria(N, 42)

        assert len(a) == 324
        assert len(fr) == 35

        for modo in ("simultanea", "individual"):
            assert is_sat(
                And(
                    init(a, N, fr),
                    trans(a, b, N, modo)
                ),
                solver_name="z3"
            )

        print(
            "FSM N=17: transições satisfazíveis "
            "nos dois modos"
        )

    _testar_n17()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## 4. Primeira propriedade — segurança

    Um estado de erro tem todas as células normais mortas:

    $$
    E(X)=\bigwedge_{i=1}^{N}
    \bigwedge_{j=1}^{N}\neg x_{i,j}
    $$

    A propriedade de segurança pretendida é:

    $$P_1=G\neg E$$

    ### Bounded Model Checking

    Procuramos um percurso que satisfaça:

    $$
    I(X_0)\land
    \bigwedge_{t=0}^{k-1}T(X_t,X_{t+1})
    \land E(X_k)
    $$

    `SAT` com um percurso validado refuta a propriedade.

    `UNSAT` até uma profundidade K não demonstra
    segurança global.

    Para cada contraexemplo, o validador Python verifica
    independentemente o estado inicial, a fronteira,
    todas as transições e o erro final.
    """)
    return


@app.cell
def _(And, Not, declare, init, trans):
    # LLM — Predicado de erro, BMC e validador independente.

    from pysmt.shortcuts import (
        Solver as BMCSolver,
        Symbol as BMCSymbol
    )
    from pysmt.typing import INT as BMC_INT

    def error(state, N):
        return And([
            Not(state[i, j])
            for i in range(1, N+1)
            for j in range(1, N+1)
        ])

    def validar_traco(
        estados, N, modo, escolhas, fronteira=None
    ):
        """Valida um percurso de erro sem usar SMT."""

        if (
            modo not in ("individual", "simultanea")
            or len(estados) != len(escolhas)+1
        ):
            raise ValueError("Traço inválido")

        posicoes = {
            (i, j)
            for i in range(N+1)
            for j in range(N+1)
        }

        iniciais = {
            (i, j)
            for i, j in posicoes
            if i == 0 or j == 0
        }

        normais = [
            (i, j)
            for i in range(1, N+1)
            for j in range(1, N+1)
        ]

        def valor(s, i, j):
            if 0 <= i <= N and 0 <= j <= N:
                return int(s[i, j])

            if (
                0 <= i <= N+1
                and 0 <= j <= N+1
                and (i == N+1 or j == N+1)
            ):
                return 0

            raise ValueError("Coordenada inválida")

        for s in estados:
            assert set(s) == posicoes

            assert all(
                type(v) is bool
                for v in s.values()
            )

            assert all(
                s[p] == estados[0][p]
                for p in iniciais
            )

            if fronteira is not None:
                assert all(
                    s[p] == bool(fronteira[p])
                    for p in iniciais
                )

        assert all(
            estados[0][i, j] == (i <= 3 and j <= 3)
            for i, j in normais
        )

        for t, (a, b) in enumerate(
            zip(estados, estados[1:])
        ):
            q = escolhas[t]

            if modo == "individual":
                assert (
                    isinstance(q, int)
                    and 0 <= q < N*N
                )
            else:
                assert q is None

            for i, j in normais:
                viz = sum(
                    valor(a, i+di, j+dj)
                    for di in (-1, 0, 1)
                    for dj in (-1, 0, 1)
                    if (di, dj) != (0, 0)
                )

                novo = (
                    viz == 3
                    or (a[i, j] and viz == 2)
                )

                esperado = (
                    novo
                    if (
                        modo == "simultanea"
                        or q == (i-1)*N+j-1
                    )
                    else a[i, j]
                )

                assert b[i, j] == esperado, (t, i, j)

        assert not any(
            estados[-1][p]
            for p in normais
        )

        return True

    def bmc_erro(N, modo, K, fronteira=None):
        """Verifica as profundidades 0 até K."""

        if (
            N < 3 or K < 0
            or modo not in ("individual", "simultanea")
        ):
            raise ValueError("Parâmetros inválidos")

        X = [
            declare(f"bmc_{modo}_{N}_{t}", N)
            for t in range(K+1)
        ]

        with BMCSolver(name="z3") as s:
            s.add_assertion(
                init(X[0], N, fronteira)
            )

            for k in range(K+1):
                if k > 0:
                    s.add_assertion(
                        trans(X[k-1], X[k], N, modo)
                    )

                s.push()
                s.add_assertion(error(X[k], N))

                if s.solve():
                    concretos = [
                        {
                            p: bool(s.get_py_value(v))
                            for p, v in st.items()
                        }
                        for st in X[:k+1]
                    ]

                    if modo == "individual":
                        escolhas = [
                            int(s.get_py_value(
                                BMCSymbol(
                                    "q_" + X[t+1][1, 1].symbol_name(),
                                    BMC_INT
                                )
                            ))
                            for t in range(k)
                        ]
                    else:
                        escolhas = [None]*k

                    validar_traco(
                        concretos, N, modo,
                        escolhas, fronteira
                    )

                    print(
                        f"BMC erro: SAT em k={k}, "
                        "percurso validado"
                    )

                    for t, st in enumerate(concretos):
                        print(f"Estado {t}:")

                        for i in range(N+2):
                            print("".join(
                                "#"
                                if (
                                    st[i, j]
                                    if i <= N and j <= N
                                    else False
                                )
                                else "."
                                for j in range(N+2)
                            ))

                        if t < k and modo == "individual":
                            q = escolhas[t]

                            print(
                                f"Selecionada: "
                                f"({q//N+1},{q%N+1})"
                            )

                    return {
                        "profundidade": k,
                        "estados": concretos,
                        "escolhas": escolhas,
                        "validado": True
                    }

                s.pop()

        print(
            f"BMC erro: UNSAT nas profundidades "
            f"0..{K}; não é prova global"
        )

        return None

    return (error, validar_traco, bmc_erro)


@app.cell
def _(bmc_erro, fronteira_aleatoria, mo, botao_bmc):
    mo.stop(not botao_bmc.value)

    def _testes_bmc():
        N = 3

        zeros = {
            (i, j): 0
            for i in range(N+1)
            for j in range(N+1)
            if i == 0 or j == 0
        }

        r = bmc_erro(N, "simultanea", 2, zeros)

        assert r is not None
        assert r["profundidade"] == 2
        assert r["validado"]

        for modo in ("simultanea", "individual"):
            for nome, fr in (
                ("fixa", fronteira_aleatoria(5, 42)),
                ("simbolica", None)
            ):
                print(
                    f"BMC N=5, modo={modo}, "
                    f"fronteira={nome}, K=2"
                )

                bmc_erro(5, modo, 2, fr)

        bmc_erro(
            17, "simultanea", 1,
            fronteira_aleatoria(17, 42)
        )

        print("Testes BMC concluídos")

    _testes_bmc()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## 5. Indução simples e k-indução

    Definimos o invariante:

    $$P(X)=\neg E(X)$$

    ### Base

    Verificamos que não existe erro alcançável nas
    profundidades 0,...,k-1, através do BMC.

    ### Passo indutivo

    Testamos a insatisfatibilidade da fórmula:

    $$
    \bigwedge_{t=0}^{k-1}P(X_t)\land
    \bigwedge_{t=0}^{k-1}T(X_t,X_{t+1})
    \land\neg P(X_k)
    $$

    Quando a fronteira é fixa, restringimos os seus
    valores no primeiro estado do passo indutivo.

    Não impomos `init(X0)` no passo, pois os estados
    analisados não são necessariamente alcançáveis.

    **Interpretação dos resultados**

    - Base SAT: existe um contraexemplo alcançável.
    - Base UNSAT e passo UNSAT: prova do invariante.
    - Base UNSAT e passo SAT: tentativa inconclusiva.

    Na modalidade individual, passos que não alteram
    o valor da célula permitem construir sequências
    que podem fazer falhar a k-indução para profundidades
    arbitrárias.

    Estes métodos continuam documentados, mesmo
    depois de encontrados contraexemplos reais.
    """)
    return


@app.cell
def _(And, Not, declare, trans, error, bmc_erro):
    # LLM — Indução simples e k-indução.

    from pysmt.shortcuts import Solver as IndSolver

    def k_inducao(N, modo, k, fronteira=None):
        if (
            N < 3 or k < 1
            or modo not in ("individual", "simultanea")
        ):
            raise ValueError("Parâmetros inválidos")

        print(
            f"\n{k}-indução N={N}, modo={modo}, "
            f"fronteira="
            f"{'simbólica' if fronteira is None else 'fixa'}"
        )

        print(
            f"BASE: procurar erro nas profundidades "
            f"0..{k-1}"
        )

        contraexemplo = bmc_erro(
            N, modo, k-1, fronteira
        )

        if contraexemplo is not None:
            print(
                "BASE SAT: contraexemplo alcançável; "
                "REFUTADA; PASSO dispensado"
            )
            return "refutada"

        print("BASE UNSAT no limite verificado")

        X = [
            declare(f"kind_{modo}_{N}_{k}_{t}", N)
            for t in range(k+1)
        ]

        formulas = (
            [
                Not(error(X[t], N))
                for t in range(k)
            ]
            + [
                trans(X[t], X[t+1], N, modo)
                for t in range(k)
            ]
            + [error(X[k], N)]
        )

        if fronteira is not None:
            formulas += [
                X[0][p] if v else Not(X[0][p])
                for p, v in fronteira.items()
            ]

        with IndSolver(name="z3") as s:
            s.add_assertion(And(formulas))

            if s.solve():
                if fronteira is not None:
                    assert all(
                        bool(s.get_py_value(X[t][p])) == bool(v)
                        for t in range(k+1)
                        for p, v in fronteira.items()
                    )

                vivos = [
                    sum(
                        bool(s.get_py_value(X[t][i, j]))
                        for i in range(1, N+1)
                        for j in range(1, N+1)
                    )
                    for t in range(k+1)
                ]

                print(
                    "PASSO SAT: números de células "
                    "vivas =", vivos
                )

                print(
                    "CONCLUSÃO: INCONCLUSIVA "
                    "(início não necessariamente alcançável)"
                )
                return "inconclusiva"

        print("PASSO UNSAT e BASE UNSAT: PROVADA")
        return "provada"

    def inducao_simples(N, modo, fronteira=None):
        return k_inducao(N, modo, 1, fronteira)

    return (inducao_simples, k_inducao)


@app.cell
def _(
    inducao_simples, k_inducao,
    fronteira_aleatoria, mo, botao_inducao
):
    mo.stop(not botao_inducao.value)

    def _testes_inducao():
        for modo in ("simultanea", "individual"):
            assert inducao_simples(
                5, modo, None
            ) == "inconclusiva"

        assert k_inducao(
            5, "individual", 2, None
        ) == "inconclusiva"

        assert k_inducao(
            5, "individual", 3, None
        ) == "inconclusiva"

        k_inducao(5, "simultanea", 2, None)

        N = 17
        fixa = fronteira_aleatoria(N, 42)

        for modo in ("simultanea", "individual"):
            for fr in (fixa, None):
                inducao_simples(N, modo, fr)

        print("Testes de indução concluídos")

    _testes_inducao()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## 6. Segunda propriedade — permanência das células

    Para cada célula normal c, pretendemos verificar:

    $$
    P_2=\bigwedge_{c\in C}
    (GF\,x_c\land GF\,\neg x_c)
    $$

    A negação é satisfeita quando alguma célula,
    a partir de certo instante, permanece viva
    ou morta indefinidamente.

    ### BMC com laços

    Procuramos estados X0,...,Xk,X{k+1}, com:

    - `init(X0)`;
    - todas as transições T(Xt,X{t+1});
    - igualdade X{k+1}=Xl para algum l<=k;
    - uma célula com valor constante no ciclo.

    A transição de fecho é obrigatória. A igualdade
    isolada de estados não demonstra um comportamento
    infinito válido.

    Um ciclo encontrado e validado pode repetir-se
    indefinidamente.

    A ausência de ciclos até determinada profundidade
    não prova a propriedade temporal global.
    """)
    return


@app.cell
def _(
    And, Equals, Iff, Int, Not, Or, Symbol,
    declare, init, trans
):
    # LLM — BMC com laços e validador independente.

    from pysmt.shortcuts import Solver as LassoSolver
    from pysmt.typing import INT as LASSO_INT

    def validar_laco(
        estados, N, modo, escolhas,
        inicio_laco, celula, fronteira=None
    ):
        """Verifica init, todas as transições, fecho
        e permanência sem usar SMT."""

        if (
            modo not in ("individual", "simultanea")
            or len(estados) < 2
        ):
            raise ValueError("Traço inválido")

        if len(escolhas) != len(estados)-1:
            raise ValueError("Escolhas inválidas")

        k = len(estados)-2

        if (
            not (0 <= inicio_laco <= k)
            or not (
                1 <= celula[0] <= N
                and 1 <= celula[1] <= N
            )
        ):
            raise ValueError(
                "Índice de laço ou célula inválido"
            )

        posicoes = {
            (i, j)
            for i in range(N+1)
            for j in range(N+1)
        }

        iniciais = {
            (i, j)
            for i, j in posicoes
            if i == 0 or j == 0
        }

        normais = [
            (i, j)
            for i in range(1, N+1)
            for j in range(1, N+1)
        ]

        def valor(s, i, j):
            if 0 <= i <= N and 0 <= j <= N:
                return int(s[i, j])

            if (
                0 <= i <= N+1
                and 0 <= j <= N+1
                and (i == N+1 or j == N+1)
            ):
                return 0

            raise ValueError("Posição inválida")

        for s in estados:
            assert set(s) == posicoes

            assert all(
                type(v) is bool
                for v in s.values()
            )

            assert all(
                s[p] == estados[0][p]
                for p in iniciais
            )

            if fronteira is not None:
                assert all(
                    s[p] == bool(fronteira[p])
                    for p in iniciais
                )

        assert all(
            estados[0][i, j] == (i <= 3 and j <= 3)
            for i, j in normais
        )

        for t, (a, b) in enumerate(
            zip(estados, estados[1:])
        ):
            q = escolhas[t]

            if modo == "individual":
                assert (
                    isinstance(q, int)
                    and 0 <= q < N*N
                )
            else:
                assert q is None

            for i, j in normais:
                viz = sum(
                    valor(a, i+di, j+dj)
                    for di in (-1, 0, 1)
                    for dj in (-1, 0, 1)
                    if (di, dj) != (0, 0)
                )

                novo = (
                    viz == 3
                    or (a[i, j] and viz == 2)
                )

                esperado = (
                    novo
                    if (
                        modo == "simultanea"
                        or q == (i-1)*N+j-1
                    )
                    else a[i, j]
                )

                assert b[i, j] == esperado, (t, i, j)

        assert estados[-1] == estados[inicio_laco], (
            "Laço não fecha"
        )

        constante = estados[inicio_laco][celula]

        assert all(
            estados[t][celula] == constante
            for t in range(inicio_laco, k+1)
        )

        return True

    def bmc_permanencia(
        N, modo, K, fronteira=None,
        celula=None, escolher=None
    ):
        if (
            N < 3 or K < 0
            or modo not in ("individual", "simultanea")
        ):
            raise ValueError("Parâmetros inválidos")

        if celula is not None and not (
            1 <= celula[0] <= N
            and 1 <= celula[1] <= N
        ):
            raise ValueError("Célula inválida")

        if escolher is not None and (
            modo != "individual"
            or not (
                1 <= escolher[0] <= N
                and 1 <= escolher[1] <= N
            )
        ):
            raise ValueError("Escolha inválida")

        for k in range(K+1):
            X = [
                declare(f"laco_{modo}_{N}_{k}_{t}", N)
                for t in range(k+2)
            ]

            formula = [init(X[0], N, fronteira)]

            formula += [
                trans(X[t], X[t+1], N, modo)
                for t in range(k+1)
            ]

            if escolher is not None:
                indice = (
                    (escolher[0]-1)*N + escolher[1]-1
                )

                formula += [
                    Equals(
                        Symbol(
                            "q_" + X[t+1][1, 1].symbol_name(),
                            LASSO_INT
                        ),
                        Int(indice)
                    )
                    for t in range(k+1)
                ]

            with LassoSolver(name="z3") as s:
                s.add_assertion(And(formula))

                for l in range(k+1):
                    fecho = And([
                        Iff(X[k+1][p], X[l][p])
                        for p in X[l]
                    ])

                    alvos = (
                        [celula]
                        if celula is not None
                        else [
                            (i, j)
                            for i in range(1, N+1)
                            for j in range(1, N+1)
                        ]
                    )

                    estavel = Or([
                        Or(
                            And([
                                X[t][p]
                                for t in range(l, k+1)
                            ]),
                            And([
                                Not(X[t][p])
                                for t in range(l, k+1)
                            ])
                        )
                        for p in alvos
                    ])

                    s.push()
                    s.add_assertion(And(fecho, estavel))

                    if s.solve():
                        concretos = [
                            {
                                p: bool(s.get_py_value(v))
                                for p, v in st.items()
                            }
                            for st in X
                        ]

                        if modo == "individual":
                            escolhas = [
                                int(s.get_py_value(
                                    Symbol(
                                        "q_" + X[t+1][1, 1].symbol_name(),
                                        LASSO_INT
                                    )
                                ))
                                for t in range(k+1)
                            ]
                        else:
                            escolhas = [None]*(k+1)

                        encontrada = next(
                            p for p in alvos
                            if all(
                                concretos[t][p] == concretos[l][p]
                                for t in range(l, k+1)
                            )
                        )

                        validar_laco(
                            concretos, N, modo, escolhas,
                            l, encontrada, fronteira
                        )

                        vivo = concretos[l][encontrada]

                        print(
                            f"SAT: ciclo validado k={k}, "
                            f"início={l}, célula={encontrada}, "
                            f"permanentemente "
                            f"{'viva' if vivo else 'morta'}"
                        )

                        for t, st in enumerate(concretos):
                            etiqueta = (
                                f" (fecho = estado {l})"
                                if t == k+1 else ""
                            )

                            vivas = sum(
                                st[i, j]
                                for i in range(1, N+1)
                                for j in range(1, N+1)
                            )

                            print(
                                f"Estado {t}{etiqueta}: "
                                f"{vivas} vivas"
                            )

                            for i in range(N+2):
                                print("".join(
                                    "#"
                                    if (
                                        st[i, j]
                                        if i <= N and j <= N
                                        else False
                                    )
                                    else "."
                                    for j in range(N+2)
                                ))

                            if (
                                t <= k
                                and modo == "individual"
                            ):
                                q = escolhas[t]
                                print(
                                    f"Selecionada: "
                                    f"({q//N+1},{q%N+1})"
                                )

                        return {
                            "k": k,
                            "loop_inicio": l,
                            "celula": encontrada,
                            "valor": vivo,
                            "estados": concretos,
                            "escolhas": escolhas,
                            "validado": True
                        }

                    s.pop()

        print(
            f"UNSAT para laços k<= {K}; "
            "não é prova global"
        )

        return None

    return (validar_laco, bmc_permanencia)


@app.cell
def _(bmc_permanencia, fronteira_aleatoria, mo, botao_lacos):
    mo.stop(not botao_lacos.value)

    def _testes_lacos():
        N = 17

        for nome, fr in (
            ("fixa", fronteira_aleatoria(N, 42)),
            ("simbólica", None)
        ):
            print(
                f"Laço individual N={N}, "
                f"fronteira={nome}"
            )

            r = bmc_permanencia(
                N, "individual", 0, fr,
                celula=(17, 17),
                escolher=(17, 17)
            )

            assert r is not None
            assert r["validado"]
            assert r["k"] == 0
            assert r["loop_inicio"] == 0
            assert not r["valor"]
            assert r["escolhas"] == [288]
            assert r["estados"][0][1, 1]

        for N, K in ((5, 1), (17, 0)):
            for nome, fr in (
                ("fixa", fronteira_aleatoria(N, 42)),
                ("simbólica", None)
            ):
                print(
                    f"Pesquisa simultânea N={N}, "
                    f"K={K}, fronteira={nome}"
                )

                bmc_permanencia(
                    N, "simultanea", K, fr
                )

        print("Testes de laços concluídos")

    _testes_lacos()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## 7. Testemunhas concretas e validação

    As testemunhas permitem verificar as duas propriedades
    sem aumentar indefinidamente a profundidade do BMC.

    **P1 — Alcançar o erro**

    - Simultânea: fronteira viva apenas em `(0,2)` e
      `(2,0)`; contagens 9,3,1,0.
    - Individual: fronteira toda morta; nove atualizações;
      contagens 9,8,7,6,5,4,3,2,1,0.

    **P2 — Permanência**

    - Individual: atualizar repetidamente `(17,17)`
      conserva o estado inicial.
    - Simultânea: fronteira toda morta; após quatro
      passos obtém-se um ponto fixo, X5=X4.

    O ponto fixo exige também `T(X4,X5)`.
    Esta transição é verificada explicitamente.

    As testemunhas foram propostas e investigadas com
    assistência LLM, incluindo sugestões e simulações
    noutra conversa.

    As suas verificações SMT são acompanhadas por
    validadores independentes.
    """)
    return


@app.cell
def _(And, Iff, Not, declare, init, trans, validar_laco):
    # LLM — Testemunha P2 simultânea e confirmação SMT.

    from pysmt.shortcuts import Solver as TestemunhaSolver

    def testemunha_simultanea(N):
        if N < 5:
            raise ValueError("N>=5 para esta testemunha")

        fr = {
            (i, j): 0
            for i in range(N+1)
            for j in range(N+1)
            if i == 0 or j == 0
        }

        inicial = {
            (i, j): bool(
                1 <= i <= 3 and 1 <= j <= 3
            )
            for i in range(N+1)
            for j in range(N+1)
        }

        estados = [inicial]

        def ler(s, i, j):
            if 0 <= i <= N and 0 <= j <= N:
                return int(s[i, j])

            if (
                0 <= i <= N+1
                and 0 <= j <= N+1
                and (i == N+1 or j == N+1)
            ):
                return 0

            raise ValueError("Coordenada inválida")

        for _passo in range(5):
            antes = estados[-1]
            depois = antes.copy()

            for i in range(1, N+1):
                for j in range(1, N+1):
                    viz = sum(
                        ler(antes, i+di, j+dj)
                        for di in (-1, 0, 1)
                        for dj in (-1, 0, 1)
                        if (di, dj) != (0, 0)
                    )

                    depois[i, j] = (
                        viz == 3
                        or (antes[i, j] and viz == 2)
                    )

            estados.append(depois)

        return estados, fr

    def confirmar_testemunha_simultanea(
        N, simbolica=False
    ):
        ref, fr_zero = testemunha_simultanea(N)

        contagens = [
            sum(
                s[i, j]
                for i in range(1, N+1)
                for j in range(1, N+1)
            )
            for s in ref
        ]

        assert contagens == [9, 6, 5, 7, 7, 7]
        assert ref[4] == ref[5]

        tag = (
            f"testemunha_{N}_"
            f"{'simbolica' if simbolica else 'fixa'}"
        )

        X = [
            declare(f"{tag}_{t}", N)
            for t in range(6)
        ]

        formulas = [
            init(
                X[0], N,
                None if simbolica else fr_zero
            )
        ]

        formulas += [
            trans(X[t], X[t+1], N, "simultanea")
            for t in range(5)
        ]

        for t in range(5):
            formulas.append(And([
                X[t][p] if ref[t][p]
                else Not(X[t][p])
                for p in X[t]
            ]))

        formulas.append(And([
            Iff(X[5][p], X[4][p])
            for p in X[4]
        ]))

        with TestemunhaSolver(name="z3") as s:
            s.add_assertion(And(formulas))

            assert s.solve(), (
                "Testemunha de P2 inconsistente com SMT"
            )

            concretos = [
                {
                    p: bool(s.get_py_value(v))
                    for p, v in st.items()
                }
                for st in X
            ]

        assert concretos == ref

        assert validar_laco(
            concretos, N, "simultanea",
            [None]*5, 4, (1, 3), fr_zero
        )

        assert concretos[4][1, 3]
        assert not concretos[4][N, N]

        print(
            f"P2 simultânea N={N}: SAT e laço "
            f"X4->X4 validado; contagens={contagens}"
        )

        return {
            "sat": True,
            "N": N,
            "contagens": contagens,
            "inicio_laco": 4,
            "estados": concretos,
            "validado": True
        }

    return (
        testemunha_simultanea,
        confirmar_testemunha_simultanea
    )


@app.cell
def _(
    And, Equals, Int, Not, Symbol, declare,
    init, trans, error, validar_traco
):
    # LLM — Testemunhas P1 e confirmação SMT.

    from pysmt.shortcuts import Solver as ErroTestSolver
    from pysmt.typing import INT as ERRO_INT

    def testemunha_erro(N, modo):
        if (
            N < 5
            or modo not in ("individual", "simultanea")
        ):
            raise ValueError("Parâmetros inválidos")

        fr = {
            (i, j): 0
            for i in range(N+1)
            for j in range(N+1)
            if i == 0 or j == 0
        }

        if modo == "simultanea":
            fr[(0, 2)] = fr[(2, 0)] = 1
            escolhas = [None]*3
        else:
            escolhas = [
                (1, 2), (2, 1), (1, 1),
                (2, 3), (2, 2),
                (3, 1), (3, 2), (3, 3),
                (1, 3)
            ]

        inicial = {
            (i, j): bool(
                1 <= i <= 3 and 1 <= j <= 3
            )
            for i in range(N+1)
            for j in range(N+1)
        }

        for p, v in fr.items():
            inicial[p] = bool(v)

        estados = [inicial]

        def ler(s, i, j):
            if 0 <= i <= N and 0 <= j <= N:
                return int(s[i, j])

            if (
                0 <= i <= N+1
                and 0 <= j <= N+1
                and (i == N+1 or j == N+1)
            ):
                return 0

            raise ValueError("Coordenada inválida")

        for escolhida in escolhas:
            antes = estados[-1]
            depois = antes.copy()

            posicoes = (
                [
                    (i, j)
                    for i in range(1, N+1)
                    for j in range(1, N+1)
                ]
                if modo == "simultanea"
                else [escolhida]
            )

            for i, j in posicoes:
                viz = sum(
                    ler(antes, i+di, j+dj)
                    for di in (-1, 0, 1)
                    for dj in (-1, 0, 1)
                    if (di, dj) != (0, 0)
                )

                depois[i, j] = (
                    viz == 3
                    or (antes[i, j] and viz == 2)
                )

            if modo == "individual":
                assert antes[escolhida]
                assert not depois[escolhida]

            estados.append(depois)

        contagens = [
            sum(
                s[i, j]
                for i in range(1, N+1)
                for j in range(1, N+1)
            )
            for s in estados
        ]

        esperado = (
            [9, 3, 1, 0]
            if modo == "simultanea"
            else list(range(9, -1, -1))
        )

        assert contagens == esperado

        return estados, fr, escolhas, contagens

    def confirmar_erro_testemunha(
        N, modo, simbolica=False
    ):
        ref, fr, escolhas, contagens = (
            testemunha_erro(N, modo)
        )

        tag = (
            f"prova_erro_{N}_{modo}_"
            f"{'simbolica' if simbolica else 'fixa'}"
        )

        X = [
            declare(f"{tag}_{t}", N)
            for t in range(len(ref))
        ]

        formulas = [
            init(
                X[0], N,
                None if simbolica else fr
            )
        ]

        for t in range(len(ref)-1):
            formulas.append(
                trans(X[t], X[t+1], N, modo)
            )

            if modo == "individual":
                i, j = escolhas[t]

                q = Symbol(
                    "q_" + X[t+1][1, 1].symbol_name(),
                    ERRO_INT
                )

                formulas.append(
                    Equals(q, Int((i-1)*N+j-1))
                )

        for t, st in enumerate(ref):
            formulas.append(And([
                X[t][p] if v else Not(X[t][p])
                for p, v in st.items()
            ]))

        formulas.append(error(X[-1], N))

        with ErroTestSolver(name="z3") as s:
            s.add_assertion(And(formulas))

            assert s.solve(), (
                "Testemunha de P1 inconsistente com SMT"
            )

            concretos = [
                {
                    p: bool(s.get_py_value(v))
                    for p, v in st.items()
                }
                for st in X
            ]

            if modo == "individual":
                indices = [
                    int(s.get_py_value(
                        Symbol(
                            "q_" + X[t+1][1, 1].symbol_name(),
                            ERRO_INT
                        )
                    ))
                    for t in range(len(escolhas))
                ]

                assert indices == [
                    (i-1)*N+j-1
                    for i, j in escolhas
                ]

        assert concretos == ref

        val_escolhas = (
            [None]*(len(concretos)-1)
            if modo == "simultanea"
            else indices
        )

        assert validar_traco(
            concretos, N, modo, val_escolhas, fr
        )

        print(
            f"P1 N={N}, modo={modo}: "
            f"SAT e percurso validado; "
            f"contagens={contagens}"
        )

        return {
            "sat": True,
            "N": N,
            "modo": modo,
            "contagens": contagens,
            "estados": concretos,
            "escolhas": escolhas,
            "fronteira": fr,
            "validado": True
        }

    return (testemunha_erro, confirmar_erro_testemunha)


@app.cell
def _(
    confirmar_testemunha_simultanea,
    confirmar_erro_testemunha,
    mo, botao_testemunhas
):
    mo.stop(not botao_testemunhas.value)

    def _testar_testemunhas():
        for N, simbolica in (
            (5, False),
            (17, False),
            (17, True)
        ):
            r = confirmar_testemunha_simultanea(
                N, simbolica
            )

            assert r["sat"]
            assert r["validado"]
            assert r["inicio_laco"] == 4

        for N, modo, simbolica in (
            (5, "simultanea", False),
            (5, "individual", False),
            (17, "simultanea", False),
            (17, "individual", False)
        ):
            r = confirmar_erro_testemunha(
                N, modo, simbolica
            )

            assert r["sat"]
            assert r["validado"]

        # Testes simbólicos opcionais:
        # confirmar_erro_testemunha(17, "simultanea", True)
        # confirmar_erro_testemunha(17, "individual", True)

        print(
            "Testemunhas de P1 e P2: "
            "validações concluídas"
        )

    _testar_testemunhas()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## 8. Resultados das propriedades

    | Propriedade | Individual | Simultânea |
    |---|---|---|
    | P1: erro inalcançável | Testemunha de 9 transições até erro | Testemunha de 3 transições até erro |
    | P2: nenhuma célula permanentemente viva/morta | Auto-laço inicial ao atualizar (17,17) | Ponto fixo alcançado em X4 |

    **P1**

    A modalidade simultânea chega ao estado de erro
    com a fronteira inicial viva apenas em `(0,2)`
    e `(2,0)`.

    A modalidade individual chega ao estado de erro
    com a fronteira toda morta, atualizando as nove
    células inicialmente vivas numa ordem específica.

    **P2**

    Na modalidade individual, selecionar `(17,17)`
    repetidamente não altera o estado inicial.

    Na modalidade simultânea, com fronteira toda
    morta, existe uma evolução até X4, com
    X5=X4 e T(X4,X5).

    **Alcance das conclusões**

    Contraexemplos SAT com validação independente
    refutam as propriedades nas configurações concretas
    consideradas.

    Como essas fronteiras são admitidas no modelo
    simbolicamente livre, as testemunhas também refutam
    a validade universal das propriedades nesse modelo.

    Não demonstram que todos os valores possíveis de
    uma fronteira fixa produzam os mesmos resultados.

    A fronteira de semente 42 não deve ser confundida
    com as fronteiras usadas nas testemunhas de erro.
    """)
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## 9. Metodologia de desempenho

    Para avaliar a eficiência computacional e a
    escalabilidade, executámos as experiências com
    `N=17` e `N=21`, em ambas as modalidades.

    Cada cenário foi repetido **três vezes** no
    computador dos alunos.

    ### Medições

    Para cada repetição foram registados:

    - Tempo de construção: declaração das variáveis
      e construção da fórmula pySMT.
    - Tempo do solver: criação, introdução da fórmula,
      resolução e libertação do solver.
    - Tempo total da experiência.

    Os tempos foram medidos com `time.perf_counter()`.

    As medianas são calculadas separadamente para
    construção, solver e total. Por isso, a soma das
    medianas de construção e solver não tem de
    coincidir com a mediana do tempo total.

    ### Métodos comparados

    **FSM:** satisfatibilidade de uma transição
    a partir do estado inicial.

    **BMC:** erro **exatamente em k=2**, após duas
    transições. Não é uma pesquisa de erros em
    todas as profundidades de 0 até 2.

    **Indução simples:** apenas o passo indutivo,
    sem o caso base.

    **k-indução:** apenas o passo indutivo com k=2,
    sem a verificação da base.

    **Laços:** consistência de uma testemunha temporal
    conhecida com a relação de transição e o fecho.

    No benchmark de laços a fronteira é **toda morta**,
    independentemente da opção selecionada no controlo.

    A testemunha simultânea tem cinco transições;
    a individual tem uma única transição.

    ### Ambiente e parâmetros

    - Sistema operativo: Windows 11.
    - Python: 3.14.7.
    - pySMT: 0.9.6.
    - z3-solver: 5.3.2.0.
    - Marimo: 0.25.0.
    - Solver: Z3.
    - Limite: 5000 ms por consulta SMT.
    - Repetições: 3 por modalidade.
    - Ordem: simultânea, seguida de individual.
    - Fronteira: fixa, `random.Random(42)`, exceto
      nas experiências de laços.

    Não foram reportados erros nem timeouts.

    O limite Z3 é aplicado à resolução SMT e não
    garante um limite para o tempo total de construção.
    """)
    return


@app.cell
def _(mo):
    dimensao_exp = mo.ui.dropdown(
        options={
            "17": 17,
            "21": 21,
            "25 (opcional)": 25
        },
        value="17",
        label="Dimensão N"
    )

    metodo_exp = mo.ui.dropdown(
        options={
            "FSM: um passo": "fsm",
            "BMC: erro exatamente em k=2": "bmc",
            "Indução simples: só passo": "ind1",
            "k-indução: só passo k=2": "kind2",
            "Laço P2: testemunha conhecida, fronteira zero": "laco"
        },
        value="FSM: um passo",
        label="Método"
    )

    fronteira_exp = mo.ui.dropdown(
        options={
            "Fixa, semente 42": "fixa42",
            "Simbólica": "simbolica"
        },
        value="Fixa, semente 42",
        label="Fronteira (exceto laço)"
    )

    limite_exp = mo.ui.dropdown(
        options={
            "2 segundos": 2000,
            "5 segundos": 5000,
            "10 segundos": 10000
        },
        value="5 segundos",
        label="Limite Z3 por consulta"
    )

    botao_medir = mo.ui.run_button(
        label="Medir agora — 3 repetições por modalidade"
    )

    mo.vstack([
        dimensao_exp,
        metodo_exp,
        fronteira_exp,
        limite_exp,
        botao_medir
    ])

    return (
        dimensao_exp, metodo_exp,
        fronteira_exp, limite_exp, botao_medir
    )


@app.cell
def _(
    And, Iff, Not, Equals, Int, Symbol,
    declare, init, trans, error,
    testemunha_simultanea, fronteira_aleatoria
):
    # LLM — Construção das fórmulas para desempenho.
    # Não modifica as funções lógicas existentes.

    from pysmt.typing import INT as BENCH_INT

    def formula_experiencia(
        N, modo, metodo, tipo_fronteira, repeticao
    ):
        if (
            N < 17
            or modo not in ("individual", "simultanea")
        ):
            raise ValueError("N ou modo inválidos")

        if metodo not in (
            "fsm", "bmc", "ind1", "kind2", "laco"
        ):
            raise ValueError("Método inválido")

        if metodo == "laco":
            fr = {
                (i, j): 0
                for i in range(N+1)
                for j in range(N+1)
                if i == 0 or j == 0
            }
        elif tipo_fronteira == "fixa42":
            fr = fronteira_aleatoria(N, 42)
        elif tipo_fronteira == "simbolica":
            fr = None
        else:
            raise ValueError("Fronteira inválida")

        n_passos = {
            "fsm": 1,
            "bmc": 2,
            "ind1": 1,
            "kind2": 2,
            "laco": (
                1 if modo == "individual" else 5
            )
        }[metodo]

        tag = f"med_{metodo}_{modo}_{N}_{repeticao}"

        X = [
            declare(f"{tag}_{t}", N)
            for t in range(n_passos+1)
        ]

        if metodo == "fsm":
            formulas = [
                init(X[0], N, fr),
                trans(X[0], X[1], N, modo)
            ]

        elif metodo == "bmc":
            formulas = [init(X[0], N, fr)]

            formulas += [
                trans(X[t], X[t+1], N, modo)
                for t in range(2)
            ]

            formulas.append(error(X[2], N))

        elif metodo in ("ind1", "kind2"):
            k = n_passos

            formulas = [
                Not(error(X[t], N))
                for t in range(k)
            ]

            formulas += [
                trans(X[t], X[t+1], N, modo)
                for t in range(k)
            ]

            formulas.append(error(X[k], N))

            if fr is not None:
                formulas += [
                    X[0][p] if v else Not(X[0][p])
                    for p, v in fr.items()
                ]

        elif modo == "individual":
            formulas = [
                init(X[0], N, fr),
                trans(X[0], X[1], N, modo)
            ]

            formulas += [
                Iff(X[0][p], X[1][p])
                for p in X[0]
            ]

            q = Symbol(
                "q_" + X[1][1, 1].symbol_name(),
                BENCH_INT
            )

            formulas.append(
                Equals(q, Int(N*N-1))
            )

        else:
            referencia, _ = testemunha_simultanea(N)

            formulas = [init(X[0], N, fr)]

            formulas += [
                trans(X[t], X[t+1], N, modo)
                for t in range(5)
            ]

            for t in range(5):
                formulas += [
                    X[t][p] if v else Not(X[t][p])
                    for p, v in referencia[t].items()
                ]

            formulas += [
                Iff(X[5][p], X[4][p])
                for p in X[4]
            ]

        return (
            And(formulas),
            "zeros" if metodo == "laco" else tipo_fronteira,
            n_passos
        )

    return (formula_experiencia,)


@app.cell
def _(
    mo, botao_medir, dimensao_exp, metodo_exp,
    fronteira_exp, limite_exp, formula_experiencia
):
    # LLM — Medição reproduzível com três repetições.
    # Só executa mediante o botão.

    mo.stop(
        not botao_medir.value,
        mo.md(
            "Carrega em **Medir agora** para executar "
            "a experiência selecionada."
        )
    )

    from time import perf_counter as _relogio
    from statistics import median as _mediana
    from importlib.metadata import version as _versao

    from pysmt.shortcuts import Solver as _SolverMedicao
    from pysmt.exceptions import (
        SolverReturnedUnknownResultError
        as _ResultadoDesconhecido
    )

    import sys as _sys
    import platform as _platform

    def _medir():
        N = dimensao_exp.value
        metodo = metodo_exp.value
        tipo_fr = fronteira_exp.value
        limite_ms = limite_exp.value

        print(
            "AMBIENTE:",
            _platform.platform(),
            "| CPU:",
            _platform.processor()
        )

        print("Python:", _sys.version.split()[0])

        for pacote in ("PySMT", "z3-solver", "marimo"):
            print(pacote + ":", _versao(pacote))

        print(
            f"PARÂMETROS: N={N}; método={metodo}; "
            f"fronteira_selecionada={tipo_fr}; "
            f"semente=42 (exceto laço); "
            f"limite_Z3_ms={limite_ms}; "
            "repetições=3; ordem=simultânea,individual"
        )

        linhas = []

        for modo in ("simultanea", "individual"):
            for rep in range(1, 4):
                t0 = _relogio()

                formula, fr_real, passos = (
                    formula_experiencia(
                        N, modo, metodo, tipo_fr, rep
                    )
                )

                t1 = _relogio()
                estado, detalhe = "UNKNOWN", ""

                try:
                    with _SolverMedicao(
                        name="z3",
                        solver_options={
                            "timeout": limite_ms
                        }
                    ) as solver:
                        solver.add_assertion(formula)

                        estado = (
                            "SAT" if solver.solve()
                            else "UNSAT"
                        )

                except _ResultadoDesconhecido as exc:
                    estado = "UNKNOWN"
                    detalhe = str(exc)[:120]

                t2 = _relogio()

                linha = dict(
                    N=N,
                    modo=modo,
                    metodo=metodo,
                    fronteira=fr_real,
                    profundidade=passos,
                    repeticao=rep,
                    estado=estado,
                    construcao_s=t1-t0,
                    solver_s=t2-t1,
                    total_s=t2-t0,
                    limite_solver_ms=limite_ms,
                    detalhe=detalhe
                )

                linhas.append(linha)

                print(
                    f"{modo:12s} rep={rep} {estado:7s} "
                    f"constr={linha['construcao_s']:.4f}s "
                    f"solver={linha['solver_s']:.4f}s "
                    f"total={linha['total_s']:.4f}s "
                    f"fronteira={fr_real}; passos={passos}"
                )

                if detalhe:
                    print("Motivo UNKNOWN:", detalhe)

        for modo in ("simultanea", "individual"):
            grupo = [
                l for l in linhas
                if l["modo"] == modo
            ]

            print(
                f"MEDIANAS {modo}: "
                f"construção="
                f"{_mediana(l['construcao_s'] for l in grupo):.4f}s; "
                f"solver="
                f"{_mediana(l['solver_s'] for l in grupo):.4f}s; "
                f"total="
                f"{_mediana(l['total_s'] for l in grupo):.4f}s; "
                f"estados="
                f"{[l['estado'] for l in grupo]}"
            )

        print(
            "UNKNOWN/timeout não significa UNSAT; "
            "medição da construção não tem timeout."
        )

        return linhas

    _linhas_experiencia = _medir()
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## 10. Resultados de desempenho observados

    **Origem:** medições executadas localmente pelos alunos
    em 29/10/2026 e comunicadas no diálogo com a LLM.

    Esta secção regista os valores observados. Não depende
    da execução do botão de benchmarking.

    **Ambiente:** Windows 11; Python 3.14.7;
    pySMT 0.9.6; z3-solver 5.3.2.0; Marimo 0.25.0.

    **Parâmetros:** três repetições por modalidade;
    timeout Z3 de 5000 ms por consulta; fronteira fixa
    por semente 42, exceto nas experiências de laços.

    Todas as consultas terminaram sem erros nem timeouts.

    ### 10.1. Medições individuais

    Todos os tempos desta tabela estão em
    **milissegundos (ms)**.

    S = simultânea; I = individual.

    C = construção da fórmula; Z3 = tempo do solver;
    Total = tempo total medido.

    | Método | N | Modo | Rep. | C (ms) | Z3 (ms) | Total (ms) |
    |:--|--:|:--:|--:|--:|--:|--:|
    | FSM | 17 | S | 1 | 10.0 | 42.3 | 52.3 |
    | FSM | 17 | S | 2 | 10.1 | 37.9 | 48.0 |
    | FSM | 17 | S | 3 | 10.8 | 37.0 | 47.8 |
    | FSM | 17 | I | 1 | 11.1 | 68.6 | 79.7 |
    | FSM | 17 | I | 2 | 10.4 | 59.6 | 70.1 |
    | FSM | 17 | I | 3 | 15.7 | 57.0 | 72.6 |
    | FSM | 21 | S | 1 | 72.8 | 52.3 | 125.1 |
    | FSM | 21 | S | 2 | 57.5 | 60.8 | 118.3 |
    | FSM | 21 | S | 3 | 65.0 | 63.0 | 128.0 |
    | FSM | 21 | I | 1 | 55.6 | 104.6 | 160.1 |
    | FSM | 21 | I | 2 | 56.6 | 98.3 | 154.9 |
    | FSM | 21 | I | 3 | 52.0 | 94.2 | 146.1 |
    | BMC k=2 | 17 | S | 1 | 61.2 | 72.2 | 133.4 |
    | BMC k=2 | 17 | S | 2 | 64.7 | 69.3 | 134.0 |
    | BMC k=2 | 17 | S | 3 | 69.9 | 68.7 | 138.6 |
    | BMC k=2 | 17 | I | 1 | 74.9 | 94.9 | 169.8 |
    | BMC k=2 | 17 | I | 2 | 73.8 | 90.8 | 164.6 |
    | BMC k=2 | 17 | I | 3 | 73.7 | 85.3 | 158.9 |
    | BMC k=2 | 21 | S | 1 | 129.7 | 139.2 | 268.9 |
    | BMC k=2 | 21 | S | 2 | 125.1 | 124.2 | 249.3 |
    | BMC k=2 | 21 | S | 3 | 156.2 | 116.8 | 272.9 |
    | BMC k=2 | 21 | I | 1 | 422.7 | 152.8 | 575.5 |
    | BMC k=2 | 21 | I | 2 | 123.9 | 179.7 | 303.6 |
    | BMC k=2 | 21 | I | 3 | 109.4 | 146.4 | 255.8 |
    | Ind. simples | 17 | S | 1 | 33.5 | 445.6 | 479.1 |
    | Ind. simples | 17 | S | 2 | 38.0 | 517.4 | 555.4 |
    | Ind. simples | 17 | S | 3 | 32.5 | 438.8 | 471.3 |
    | Ind. simples | 17 | I | 1 | 42.5 | 549.9 | 592.4 |
    | Ind. simples | 17 | I | 2 | 46.6 | 547.3 | 593.9 |
    | Ind. simples | 17 | I | 3 | 41.2 | 556.2 | 597.4 |
    | Ind. simples | 21 | S | 1 | 71.0 | 693.6 | 764.6 |
    | Ind. simples | 21 | S | 2 | 62.4 | 652.5 | 714.8 |
    | Ind. simples | 21 | S | 3 | 346.8 | 837.5 | 1184.3 |
    | Ind. simples | 21 | I | 1 | 61.7 | 774.9 | 836.7 |
    | Ind. simples | 21 | I | 2 | 61.9 | 792.4 | 854.3 |
    | Ind. simples | 21 | I | 3 | 65.2 | 1037.3 | 1102.9 |
    | k-ind. k=2 | 17 | S | 1 | 69.7 | 1293.8 | 1363.5 |
    | k-ind. k=2 | 17 | S | 2 | 68.3 | 1325.5 | 1393.9 |
    | k-ind. k=2 | 17 | S | 3 | 65.2 | 1205.8 | 1271.0 |
    | k-ind. k=2 | 17 | I | 1 | 74.4 | 1504.9 | 1579.3 |
    | k-ind. k=2 | 17 | I | 2 | 76.2 | 1408.0 | 1484.2 |
    | k-ind. k=2 | 17 | I | 3 | 74.4 | 1480.5 | 1554.9 |
    | Laço P2 | 17 | S | 1 | 159.7 | 185.5 | 345.2 |
    | Laço P2 | 17 | S | 2 | 164.3 | 208.2 | 372.5 |
    | Laço P2 | 17 | S | 3 | 150.5 | 178.0 | 328.4 |
    | Laço P2 | 17 | I | 1 | 38.0 | 61.5 | 99.5 |
    | Laço P2 | 17 | I | 2 | 55.0 | 66.5 | 121.5 |
    | Laço P2 | 17 | I | 3 | 425.2 | 77.8 | 503.0 |

    **Nota sobre o registo original:** na terceira
    repetição da indução simples N=21 individual,
    C=65,2 ms e Z3=1037,3 ms somam 1102,5 ms,
    enquanto o total comunicado foi 1102,9 ms.

    A diferença de 0,4 ms fica documentada e os
    três valores originais são preservados.
    Não houve correção retroativa dos dados.

    ### 10.2. Medianas das três repetições

    As medianas foram calculadas **separadamente**
    para cada uma das três medidas.

    | Método | N | Modo | C med. (ms) | Z3 med. (ms) | Total med. (ms) | Estado SMT |
    |:--|--:|:--:|--:|--:|--:|:--:|
    | FSM | 17 | S | 10.1 | 37.9 | 48.0 | SAT |
    | FSM | 17 | I | 11.1 | 59.6 | 72.6 | SAT |
    | FSM | 21 | S | 65.0 | 60.8 | 125.1 | SAT |
    | FSM | 21 | I | 55.6 | 98.3 | 154.9 | SAT |
    | BMC k=2 | 17 | S | 64.7 | 69.3 | 134.0 | UNSAT |
    | BMC k=2 | 17 | I | 73.8 | 90.8 | 164.6 | UNSAT |
    | BMC k=2 | 21 | S | 129.7 | 124.2 | 268.9 | UNSAT |
    | BMC k=2 | 21 | I | 123.9 | 152.8 | 303.6 | UNSAT |
    | Ind. simples | 17 | S | 33.5 | 445.6 | 479.1 | SAT |
    | Ind. simples | 17 | I | 42.5 | 549.9 | 593.9 | SAT |
    | Ind. simples | 21 | S | 71.0 | 693.6 | 764.6 | SAT |
    | Ind. simples | 21 | I | 61.9 | 792.4 | 854.3 | SAT |
    | k-ind. k=2 | 17 | S | 68.3 | 1293.8 | 1363.5 | SAT |
    | k-ind. k=2 | 17 | I | 74.4 | 1480.5 | 1554.9 | SAT |
    | Laço P2 | 17 | S | 159.7 | 185.5 | 345.2 | SAT |
    | Laço P2 | 17 | I | 55.0 | 66.5 | 121.5 | SAT |

    ### 10.3. Análise de escalabilidade

    Para N=17, cada estado tem 324 variáveis booleanas;
    para N=21, tem 484.

    O aumento das variáveis é de aproximadamente 49,4%.

    Nas experiências com FSM, BMC e indução simples,
    as medianas dos tempos totais aumentaram quando
    se passou de N=17 para N=21, nas duas modalidades.

    As observações sugerem que a dimensão da grelha
    influencia o custo de construção e resolução.
    Não é possível inferir uma lei de crescimento
    geral a partir de apenas duas dimensões.

    Nas experiências medidas com configurações
    comparáveis, as medianas da modalidade individual
    foram superiores às da simultânea.

    Este resultado não deve ser generalizado para
    qualquer instância ou profundidade.

    O benchmark de laços é particularmente diferente:
    - simultânea: cinco transições até ao ponto fixo;
    - individual: uma transição que conserva o estado.

    Portanto, os tempos dos dois laços não correspondem
    a tarefas SMT equivalentes.

    ### 10.4. Variabilidade e limitações

    Foram observadas diferenças entre repetições.

    No laço individual N=17, os totais foram
    99,5 ms, 121,5 ms e 503,0 ms.

    A terceira repetição foi aproximadamente cinco
    vezes mais demorada do que a primeira. O aumento
    ocorreu sobretudo no tempo de construção registado.

    Também se observaram valores elevados de construção
    em BMC N=21 individual, repetição 1, e na indução
    simples N=21 simultânea, repetição 3.

    Não existe evidência suficiente para identificar
    a causa destas diferenças.

    Apresentam-se os valores individuais e as medianas
    para que a variabilidade não fique escondida.

    Os três testes por cenário são suficientes para
    uma análise exploratória, mas não para caracterizar
    estatisticamente a distribuição dos tempos.

    ### 10.5. Significado dos resultados SMT

    - FSM SAT: existe uma transição permitida.
    - BMC UNSAT: não existe estado de erro exatamente
      em X2, após duas transições, com a fronteira
      fixa da experiência.
    - Passo de indução SAT: a obrigação indutiva falha;
      não é, por si só, um contraexemplo alcançável.
    - Passo de k-indução SAT: a hipótese considerada
      não basta para provar a propriedade.
    - Laço SAT: a testemunha imposta é consistente
      com as transições e o fecho, devendo também
      passar pelo validador independente.

    Todos os resultados reportados foram obtidos
    dentro do limite de 5000 ms por consulta SMT.

    Os resultados de desempenho não constituem provas
    gerais sobre as duas propriedades.
    """)
    return


@app.cell
def _(mo):
    mo.md(r"""
    ## 11. Conclusões e limites do Exercício 1

    ### Cobertura dos requisitos

    | Requisito | Implementação |
    |:--|:--|
    | Grelha N×N, N>16 | `declare`; testes N=17 e N=21 |
    | Células booleanas | Símbolos pySMT `BOOL` |
    | Estado inicial 3×3 | `init` |
    | Fronteira inicial aleatória | `fronteira_aleatoria` |
    | Fronteira inicial constante | `trans` |
    | Fronteira final sempre morta | `valor_celula` |
    | Regra B3/S23 | `regra` |
    | Transições individual e simultânea | `trans(..., modo)` |
    | Propriedade de segurança | `error`, BMC, indução e testemunhas |
    | Propriedade de permanência | BMC com laços e testemunhas |
    | Validação independente | `validar_traco`, `validar_laco` |
    | Eficiência e escalabilidade | 48 medições N=17 e N=21 |

    ### Conclusões lógicas

    Na primeira propriedade foram construídas
    testemunhas que chegam ao estado de erro nas
    duas modalidades de transição.

    Na segunda propriedade foram construídos laços
    que permitem repetir indefinidamente uma
    configuração com células permanentes.

    Com SAT e validação independente, estes
    contraexemplos refutam as propriedades nas
    configurações concretas usadas.

    Como essas configurações são permitidas
    pela inicialização simbólica, refutam também
    as propriedades universais desse modelo.

    Não se conclui que todas as fronteiras fixas
    tenham o mesmo comportamento.

    ### Limitações do modelo e das verificações

    - A modalidade individual admite atualização
      sem mudança de valor.
    - Não foi imposta justiça na seleção de células.
    - A fronteira simbólica não define probabilidades.
    - BMC UNSAT limitado não é prova global.
    - A falha do passo indutivo pode envolver
      estados não alcançáveis.
    - As experiências de desempenho usam apenas
      N=17 e N=21 e três repetições por cenário.
    - O limite temporal Z3 não inclui a construção.
    - Os benchmarks com laços utilizam fronteira
      toda morta, e não a semente 42.

    ### Reprodutibilidade

    1. Ativar o ambiente Conda `logica`.
    2. Confirmar Python 3.14.7, pySMT 0.9.6,
       z3-solver 5.3.2.0 e Marimo 0.25.0.
    3. Abrir com `marimo edit nome_do_ficheiro.py`.
    4. Confirmar os testes básicos.
    5. Executar manualmente os testes principais
       e a confirmação de testemunhas N=17.
    6. Os dados de desempenho já observados estão
       registados nas tabelas da secção 10.
       Não é preciso repetir benchmarks para os ler.
    7. Para novas medições, usar o botão de desempenho.
    8. Confirmar que o PDF da entrega contém
       explicações, código, resultados e conclusões.

    ### Contribuições da LLM

    | Componente | Participação |
    |:--|:--|
    | Formulação da FSM e regras B3/S23 | Modelação e código assistidos por LLM |
    | Fronteiras fixa e simbólica | Decisão discutida e implementação assistida |
    | Interpretação A | Decisão discutida durante o desenvolvimento |
    | BMC, indução e k-indução | Propostas, implementação e testes da LLM |
    | BMC temporal com laços | Formulação, implementação e testes da LLM |
    | Testemunhas P1 e P2 | Sugestões e simulações assistidas por LLM, incluindo outra conversa |
    | Validadores independentes | Implementação assistida por LLM |
    | Benchmark | Metodologia e código assistidos por LLM |
    | Execução e interpretação dos resultados | Execuções locais e análise dos alunos com apoio LLM |

    **Ligações dos diálogos LLM:**

    - Conversa de desenvolvimento deste exercício:
      [INSERIR LIGAÇÃO REAL]
    - Conversa adicional de investigação e testemunhas:
      [INSERIR LIGAÇÃO REAL]

    Estas ligações devem ser substituídas antes
    da entrega. Não devem ser inventadas.

    ### Referências

    - Enunciado do TP2 — Exercício 1.
    - Regras gerais dos trabalhos práticos
      de Lógica Computacional 2026/2027.
    - Documento sobre utilização de ferramentas LLM.
    - Materiais da disciplina: Capítulos 3 e 4,
      fichas práticas 7, 8 e 9.
    - Documentação oficial de pySMT, Z3 e Marimo.

    ### Entrega

    O notebook deve permanecer executável e
    acompanhado por um PDF correspondente à
    versão final efetivamente executada.

    O Exercício 3 do TP2 é obrigatório e será
    desenvolvido separadamente.
    """)
    return


if __name__ == "__main__":
    app.run()
