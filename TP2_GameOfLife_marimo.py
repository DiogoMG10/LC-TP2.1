
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
    # TP2 — Game of Life: FSM, BMC, indução e laços

    **Referências:** enunciado TP2; Capítulos 3/4; fichas 7, 8 e 9.

    **Contributo da LLM:** modelação, código e propostas de testes;
    os resultados SMT devem ser executados e documentados pelos alunos.

    - `N > 16` nos resultados principais (`N=3,5` apenas para depuração).
    - Fronteira inicial: fixa por semente ou simbólica; preservada em todos os passos.
    - Fronteira final: sempre morta.
    - Modo individual: apenas uma célula **é atualizada** por passo, podendo não mudar.
    """)
    return


@app.cell
def _():
    # LLM — codificação simbólica da FSM (mantida das etapas anteriores).
    import random
    from pysmt.shortcuts import (And, Bool, Equals, Iff, Int, Ite,
                                 Not, Or, Plus, Symbol, is_sat)
    from pysmt.typing import BOOL, INT

    def declare(t, N):
        if N < 3:
            raise ValueError("N>=3 para testes; N>16 no enunciado")
        return {(i, j): Symbol(f"x_{i}_{j}_{t}", BOOL)
                for i in range(N + 1) for j in range(N + 1)}

    def fronteira_aleatoria(N, semente):
        rng = random.Random(semente)
        return {(i, j): rng.getrandbits(1)
                for i in range(N + 1) for j in range(N + 1)
                if i == 0 or j == 0}

    def init(state, N, fronteira=None):
        normais = [state[i, j] if i <= 3 and j <= 3 else Not(state[i, j])
                   for i in range(1, N + 1) for j in range(1, N + 1)]
        if fronteira is None:
            return And(normais)
        posicoes = {(i, j) for i in range(N + 1) for j in range(N + 1)
                    if i == 0 or j == 0}
        if set(fronteira) != posicoes or any(v not in (0, 1) for v in fronteira.values()):
            raise ValueError("Fronteira inválida")
        return And(normais + [state[p] if fronteira[p] else Not(state[p])
                              for p in sorted(posicoes)])

    def valor_celula(state, N, i, j):
        if 0 <= i <= N and 0 <= j <= N:
            return state[i, j]  # KeyError se a célula não foi declarada.
        if 0 <= i <= N + 1 and 0 <= j <= N + 1 and (i == N + 1 or j == N + 1):
            return Bool(False)
        raise ValueError(f"Coordenadas inválidas: {(i, j)}")

    def regra(state, N, i, j):
        if not (1 <= i <= N and 1 <= j <= N):
            raise ValueError("A regra só se aplica a células normais")
        vizinhos = [valor_celula(state, N, i + di, j + dj)
                    for di in (-1, 0, 1) for dj in (-1, 0, 1)
                    if (di, dj) != (0, 0)]
        vivos = Plus([Ite(v, Int(1), Int(0)) for v in vizinhos])
        return Or(Equals(vivos, Int(3)), And(state[i, j], Equals(vivos, Int(2))))

    def trans(curr, prox, N, modo="simultanea"):
        if modo not in ("individual", "simultanea"):
            raise ValueError("Modo inválido")
        fixas = [Iff(prox[i, j], curr[i, j])
                 for i in range(N + 1) for j in range(N + 1)
                 if i == 0 or j == 0]
        restricoes = []
        if modo == "individual":
            escolha = Symbol("q_" + prox[1, 1].symbol_name(), INT)
            restricoes.extend([escolha >= Int(0), escolha < Int(N * N)])
        for i in range(1, N + 1):
            for j in range(1, N + 1):
                novo = regra(curr, N, i, j)
                if modo == "individual":
                    indice = (i - 1) * N + (j - 1)
                    novo = Ite(Equals(escolha, Int(indice)), novo, curr[i, j])
                restricoes.append(Iff(prox[i, j], novo))
        return And(fixas + restricoes)

    return (And, Bool, Equals, Iff, Int, Not, Or, Symbol, declare,
            fronteira_aleatoria, init, is_sat, trans, valor_celula)


@app.cell
def _(mo):
    mo.md(r"""## Testes da FSM (N=5) e das escolhas individuais (N=5)

    As células de teste usam funções locais para evitar colisões de nomes no Marimo.
    """)
    return


@app.cell
def _(And, Not, declare, fronteira_aleatoria, init, is_sat, trans, valor_celula):
    # LLM — testes SMT da primeira implementação (preservados).
    def _testes_fsm():
        def configuracao(s, vivas):
            return And([v if p in vivas else Not(v) for p, v in s.items()])
        N = 5
        a, b = declare("teste_fsm_a", N), declare("teste_fsm_b", N)
        fr = fronteira_aleatoria(N, 42)
        assert len(a) == 36 and len(fr) == 11
        assert valor_celula(a, N, N + 1, 1).is_false()
        assert valor_celula(a, N, 1, N + 1).is_false()
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
        assert is_sat(init(a, N, fr), solver_name="z3")
        assert not is_sat(And(init(a, N, fr), Not(a[1, 1])), solver_name="z3")
        assert not is_sat(And(init(a, N, fr), a[4, 4]), solver_name="z3")
        assert is_sat(And(init(a, N), a[0, 0]), solver_name="z3")
        assert is_sat(And(init(a, N), Not(a[0, 0])), solver_name="z3")
        for modo in ("individual", "simultanea"):
            assert not is_sat(And(trans(a, b, N, modo), a[0, 0], Not(b[0, 0])),
                              solver_name="z3")
        horizontal, vertical = {(2, 1), (2, 2), (2, 3)}, {(1, 2), (2, 2), (3, 2)}
        base = configuracao(a, horizontal)
        sim, ind = trans(a, b, N, "simultanea"), trans(a, b, N, "individual")
        assert is_sat(And(base, sim, configuracao(b, vertical)), solver_name="z3")
        assert not is_sat(And(base, sim, Not(configuracao(b, vertical))), solver_name="z3")
        assert is_sat(And(base, ind, configuracao(b, {(2, 2), (2, 3)})), solver_name="z3")
        assert not is_sat(And(base, ind, configuracao(b, vertical)), solver_name="z3")
        assert is_sat(And(base, ind, configuracao(b, horizontal)), solver_name="z3")
        print("FSM N=5: testes SMT concluídos")
    _testes_fsm()
    return


@app.cell
def _(And, Equals, Int, Not, Symbol, declare, init, is_sat, trans):
    # LLM — teste de duas seleções independentes do modo individual.
    def _testar_duas_escolhas():
        from pysmt.typing import INT as T_INT
        N = 5
        a, b, c = [declare(f"duas_escolhas_{t}", N) for t in range(3)]
        zeros = {(i, j): 0 for i in range(N + 1) for j in range(N + 1)
                 if i == 0 or j == 0}
        q1 = Symbol("q_" + b[1, 1].symbol_name(), T_INT)
        q2 = Symbol("q_" + c[1, 1].symbol_name(), T_INT)
        formula = And(init(a, N, zeros), trans(a, b, N, "individual"),
                      trans(b, c, N, "individual"),
                      Equals(q1, Int(24)), Equals(q2, Int(6)),
                      init(b, N, zeros), Not(c[2, 2]), c[1, 1])
        assert is_sat(formula, solver_name="z3")
        print("Duas escolhas individuais consecutivas: SAT (esperado)")
    _testar_duas_escolhas()
    return


@app.cell
def _(And, declare, fronteira_aleatoria, init, is_sat, trans):
    def _testar_N17():
        N = 17
        a, b = declare("N17_a", N), declare("N17_b", N)
        fr = fronteira_aleatoria(N, 42)
        assert len(a) == 324 and len(fr) == 35
        for modo in ("simultanea", "individual"):
            assert is_sat(And(init(a, N, fr), trans(a, b, N, modo)), solver_name="z3")
        print("FSM N=17: transições satisfazíveis nos dois modos")
    _testar_N17()
    return


@app.cell
def _(mo):
    mo.md(r"""## Primeira propriedade: segurança (SFOTS)

    $$E(X)=\bigwedge_{i=1}^N\bigwedge_{j=1}^N\neg x_{i,j},\quad P(X)=\neg E(X).$$

    BMC procura uma execução inicial de comprimento `k` terminada em erro. `SAT`
    é uma refutação, desde que o percurso seja validado; `UNSAT` até `K` não é prova global.
    """)
    return


@app.cell
def _(And, Not, declare, init, trans):
    # LLM — predicado de erro, BMC e validador independente (etapa 3).
    from pysmt.shortcuts import Solver as BMCSolver, Symbol as BMCSymbol
    from pysmt.typing import INT as BMC_INT

    def error(state, N):
        return And([Not(state[i, j]) for i in range(1, N + 1)
                    for j in range(1, N + 1)])

    def validar_traco(estados, N, modo, escolhas, fronteira=None):
        """Valida um contraexemplo da propriedade de erro, sem SMT."""
        if modo not in ("individual", "simultanea") or len(estados) != len(escolhas) + 1:
            raise ValueError("Traço inválido")
        posicoes = {(i, j) for i in range(N + 1) for j in range(N + 1)}
        iniciais = {(i, j) for i, j in posicoes if i == 0 or j == 0}
        normais = [(i, j) for i in range(1, N + 1) for j in range(1, N + 1)]

        def valor(s, i, j):
            if 0 <= i <= N and 0 <= j <= N:
                return int(s[i, j])
            if 0 <= i <= N + 1 and 0 <= j <= N + 1 and (i == N + 1 or j == N + 1):
                return 0
            raise ValueError("Coordenada inválida")

        for s in estados:
            assert set(s) == posicoes
            assert all(type(v) is bool for v in s.values())
            assert all(s[p] == estados[0][p] for p in iniciais)
            if fronteira is not None:
                assert all(s[p] == bool(fronteira[p]) for p in iniciais)
        assert all(estados[0][i, j] == (i <= 3 and j <= 3) for i, j in normais)
        for t, (a, b) in enumerate(zip(estados, estados[1:])):
            q = escolhas[t]
            assert (isinstance(q, int) and 0 <= q < N*N) if modo == "individual" else q is None
            for i, j in normais:
                viz = sum(valor(a, i + di, j + dj) for di in (-1, 0, 1)
                          for dj in (-1, 0, 1) if (di, dj) != (0, 0))
                novo = viz == 3 or (a[i, j] and viz == 2)
                esperado = novo if modo == "simultanea" or q == (i-1)*N+j-1 else a[i, j]
                assert b[i, j] == esperado, (t, i, j)
        assert not any(estados[-1][p] for p in normais)
        return True

    def bmc_erro(N, modo, K, fronteira=None):
        if N < 3 or K < 0 or modo not in ("individual", "simultanea"):
            raise ValueError("Parâmetros inválidos")
        estados = [declare(f"bmc_{modo}_{N}_{t}", N) for t in range(K + 1)]
        with BMCSolver(name="z3") as s:
            s.add_assertion(init(estados[0], N, fronteira))
            for k in range(K + 1):
                if k > 0:
                    s.add_assertion(trans(estados[k-1], estados[k], N, modo))
                s.push()
                s.add_assertion(error(estados[k], N))
                if s.solve():
                    concretos = [{p: bool(s.get_py_value(v)) for p, v in estado.items()}
                                for estado in estados[:k+1]]
                    escolhas = ([int(s.get_py_value(BMCSymbol(
                        "q_" + estados[t+1][1, 1].symbol_name(), BMC_INT)))
                        for t in range(k)] if modo == "individual" else [None]*k)
                    validar_traco(concretos, N, modo, escolhas, fronteira)
                    print(f"BMC erro: SAT em k={k}, percurso validado")
                    for t, grelha in enumerate(concretos):
                        print(f"Estado {t}:")
                        for i in range(N + 2):
                            print("".join("#" if (grelha[i, j] if i <= N and j <= N else False)
                                          else "." for j in range(N + 2)))
                        if t < k and modo == "individual":
                            q = escolhas[t]
                            print(f"Selecionada: ({q//N+1},{q%N+1})")
                    return {"profundidade": k, "estados": concretos,
                            "escolhas": escolhas, "validado": True}
                s.pop()
        print(f"BMC erro: UNSAT para profundidades 0..{K}; não é prova global")
        return None

    return (error, validar_traco, bmc_erro)


@app.cell
def _(bmc_erro):
    def _controlo_bmc():
        N = 3
        zeros = {(i,j):0 for i in range(N+1) for j in range(N+1) if i==0 or j==0}
        r = bmc_erro(N, "simultanea", 2, zeros)
        assert r is not None and r["profundidade"] == 2 and r["validado"]
        print("BMC N=3: contraexemplo de controlo confirmado")
    _controlo_bmc()
    return


@app.cell
def _(bmc_erro, fronteira_aleatoria):
    def _bmc_n5():
        N, K = 5, 2
        fixa = fronteira_aleatoria(N, 42)
        for modo in ("simultanea", "individual"):
            for nome, fr in (("fixa", fixa), ("simbólica", None)):
                print(f"BMC N=5, K={K}, modo={modo}, fronteira={nome}")
                bmc_erro(N, modo, K, fr)
    _bmc_n5()
    return


@app.cell
def _(bmc_erro, fronteira_aleatoria):
    def _bmc_n17():
        N, K = 17, 1
        bmc_erro(N, "simultanea", K, fronteira_aleatoria(N, 42))
        # bmc_erro(N, "individual", K, fronteira_aleatoria(N, 42))
        # bmc_erro(N, "simultanea", K, None)
        # bmc_erro(N, "individual", K, None)
    _bmc_n17()
    return


@app.cell
def _(mo):
    mo.md(r"""## Indução simples e k-indução: primeira propriedade

    Base: ausência de erro alcançável até `k-1`, verificada por BMC.

    Passo: `P(X0) ∧ ... ∧ P(X{k-1}) ∧ T(X0,X1) ∧ ... ∧ T(X{k-1},Xk) ∧ ¬P(Xk)`.

    Se a fronteira for fixa, os seus valores são impostos em X0 no passo
    indutivo e preservados pelas transições. Não se impõe `init(X0)` no passo.
    """)
    return


@app.cell
def _(And, Not, declare, trans, error, bmc_erro):
    # LLM — etapa 4: indução e k-indução.
    from pysmt.shortcuts import Solver as IndSolver

    def k_inducao(N, modo, k, fronteira=None):
        if N < 3 or k < 1 or modo not in ("individual", "simultanea"):
            raise ValueError("Parâmetros inválidos")
        print(f"\n{k}-indução N={N}, modo={modo}, fronteira={'simbólica' if fronteira is None else 'fixa'}")
        print(f"BASE: erro nas profundidades 0..{k-1}?")
        contraexemplo = bmc_erro(N, modo, k-1, fronteira)
        if contraexemplo is not None:
            print("BASE SAT: contraexemplo real; PASSO não necessário; REFUTADA")
            return "refutada"
        print("BASE UNSAT (dentro do limite)")
        X = [declare(f"kind_{modo}_{N}_{k}_{t}", N) for t in range(k + 1)]
        formulas = ([Not(error(X[t], N)) for t in range(k)] +
                    [trans(X[t], X[t+1], N, modo) for t in range(k)] +
                    [error(X[k], N)])
        if fronteira is not None:
            formulas += [X[0][p] if v else Not(X[0][p]) for p, v in fronteira.items()]
        with IndSolver(name="z3") as s:
            s.add_assertion(And(formulas))
            if s.solve():
                if fronteira is not None:
                    assert all(bool(s.get_py_value(X[t][p])) == bool(v)
                               for t in range(k+1) for p, v in fronteira.items())
                vivos = [sum(bool(s.get_py_value(X[t][i,j]))
                             for i in range(1, N+1) for j in range(1, N+1))
                         for t in range(k+1)]
                print("PASSO SAT: estados arbitrários com vivas =", vivos)
                print("INCONCLUSIVA: a acessibilidade do primeiro estado não foi provada")
                return "inconclusiva"
        print("PASSO UNSAT + BASE UNSAT: PROVADA")
        return "provada"

    def inducao_simples(N, modo, fronteira=None):
        return k_inducao(N, modo, 1, fronteira)

    return (inducao_simples, k_inducao)


@app.cell
def _(inducao_simples, k_inducao):
    def _inducao_n5():
        N = 5
        for modo in ("simultanea", "individual"):
            assert inducao_simples(N, modo, None) == "inconclusiva"
        assert k_inducao(N, "individual", 2, None) == "inconclusiva"
        assert k_inducao(N, "individual", 3, None) == "inconclusiva"
        k_inducao(N, "simultanea", 2, None)
        print("Indução N=5: testes concluídos")
    _inducao_n5()
    return


@app.cell
def _(inducao_simples, fronteira_aleatoria):
    def _inducao_n17():
        N = 17
        fixa = fronteira_aleatoria(N, 42)
        for modo in ("simultanea", "individual"):
            for fr in (fixa, None):
                inducao_simples(N, modo, fr)
    _inducao_n17()
    return


@app.cell
def _(mo):
    mo.md(r"""## Segunda propriedade: nenhuma célula normal fica permanentemente viva ou morta

    Para cada célula normal `c`, a propriedade temporal é
    $$GF\,x_c \land GF\,\neg x_c.$$

    A negação exige um percurso com alguma célula constante no sufixo infinito.

    Procuramos um **laço** com estados `X0,...,Xk` e uma transição adicional
    `T(Xk,X{k+1})`, obrigando `X{k+1}=Xl` para algum `0<=l<=k`.

    É essencial usar `X{k+1}` novo: no modo individual, o seletor auxiliar
    de uma transição é identificado pelo estado de destino. Reutilizar diretamente
    `Xl` como destino da transição de fecho poderia ligar indevidamente dois seletores.

    A violação ocorre se existe uma célula `c` que permanece viva ou morta
    em **todos** os estados do ciclo `Xl,...,Xk`. O prefixo anterior a `l`
    pode ter valores diferentes. Como o laço volta ao mesmo estado, pode repetir-se
    indefinidamente. A ausência de laços até K não prova a propriedade.
    """)
    return


@app.cell
def _(And, Equals, Iff, Int, Not, Or, Symbol, declare, init, trans):
    # LLM — BMC com laço para a propriedade temporal 2 e validador Python.
    from pysmt.shortcuts import Solver as LassoSolver
    from pysmt.typing import INT as LASSO_INT

    def validar_laco(estados, N, modo, escolhas, inicio_laco, celula, fronteira=None):
        """Confirma estado inicial, TODAS as transições, fecho e permanência."""
        if modo not in ("individual", "simultanea") or len(estados) < 2:
            raise ValueError("Traço inválido")
        if len(escolhas) != len(estados) - 1:
            raise ValueError("Número de escolhas inválido")
        k = len(estados) - 2
        if not (0 <= inicio_laco <= k) or not (1 <= celula[0] <= N and 1 <= celula[1] <= N):
            raise ValueError("Início do ciclo ou célula inválidos")

        posicoes = {(i,j) for i in range(N+1) for j in range(N+1)}
        iniciais = {(i,j) for i,j in posicoes if i==0 or j==0}
        normais = [(i,j) for i in range(1,N+1) for j in range(1,N+1)]

        def valor(s, i, j):
            if 0 <= i <= N and 0 <= j <= N:
                return int(s[i,j])
            if 0 <= i <= N+1 and 0 <= j <= N+1 and (i == N+1 or j == N+1):
                return 0
            raise ValueError(f"Posição inválida {(i,j)}")

        for s in estados:
            assert set(s) == posicoes
            assert all(type(v) is bool for v in s.values())
            assert all(s[p] == estados[0][p] for p in iniciais)
            if fronteira is not None:
                assert all(s[p] == bool(fronteira[p]) for p in iniciais)
        assert all(estados[0][i,j] == (i<=3 and j<=3) for i,j in normais)

        for t, (a,b) in enumerate(zip(estados, estados[1:])):
            q = escolhas[t]
            assert (isinstance(q,int) and 0 <= q < N*N) if modo == "individual" else q is None
            for i,j in normais:
                viz = sum(valor(a, i+di, j+dj) for di in (-1,0,1)
                          for dj in (-1,0,1) if (di,dj) != (0,0))
                novo = viz == 3 or (a[i,j] and viz == 2)
                esperado = novo if modo == "simultanea" or q == (i-1)*N+j-1 else a[i,j]
                assert b[i,j] == esperado, ("Transição inválida",t,i,j)

        assert estados[-1] == estados[inicio_laco], "O laço não fecha"
        valor_constante = estados[inicio_laco][celula]
        assert all(estados[t][celula] == valor_constante
                   for t in range(inicio_laco,k+1)), "Célula alterou-se no ciclo"
        return True

    def bmc_permanencia(N, modo, K, fronteira=None, celula=None, escolher=None):
        """Pesquisa laços violadores de GF(viva) e GF(morta), até K.

        `celula` restringe a célula observada; `escolher` é usado só
        para testar uma seleção individual específica em todos os passos.
        """
        if N < 3 or K < 0 or modo not in ("individual", "simultanea"):
            raise ValueError("Parâmetros inválidos")
        if celula is not None and not (1 <= celula[0] <= N and 1 <= celula[1] <= N):
            raise ValueError("Célula observada inválida")
        if escolher is not None and (modo != "individual" or not
                                    (1 <= escolher[0] <= N and 1 <= escolher[1] <= N)):
            raise ValueError("Seleção só permitida no modo individual")

        for k in range(K + 1):
            # X[k+1] é um NOVO clone que representa o estado após a aresta de fecho.
            X = [declare(f"laco_{modo}_{N}_{k}_{t}", N) for t in range(k+2)]
            formula = [init(X[0], N, fronteira)]
            formula += [trans(X[t], X[t+1], N, modo) for t in range(k+1)]
            if escolher is not None:
                indice = (escolher[0]-1)*N + escolher[1]-1
                formula += [Equals(Symbol("q_" + X[t+1][1,1].symbol_name(), LASSO_INT),
                                   Int(indice)) for t in range(k+1)]

            with LassoSolver(name="z3") as s:
                s.add_assertion(And(formula))
                for l in range(k+1):
                    # X[k+1] coincide com X[l], INCLUINDO células da fronteira.
                    fecho = And([Iff(X[k+1][p], X[l][p]) for p in X[l]])
                    alvos = [celula] if celula is not None else [
                        (i,j) for i in range(1,N+1) for j in range(1,N+1)]
                    estavel = Or([
                        Or(And([X[t][p] for t in range(l,k+1)]),
                           And([Not(X[t][p]) for t in range(l,k+1)]))
                        for p in alvos
                    ])
                    s.push()
                    s.add_assertion(And(fecho, estavel))

                    if s.solve():
                        concretos = [{p: bool(s.get_py_value(v)) for p,v in st.items()}
                                    for st in X]
                        escolhas = ([int(s.get_py_value(Symbol(
                            "q_" + X[t+1][1,1].symbol_name(), LASSO_INT)))
                            for t in range(k+1)] if modo == "individual" else [None]*(k+1))
                        encontrada = next(p for p in alvos
                            if all(concretos[t][p] == concretos[l][p] for t in range(l,k+1)))
                        assert validar_laco(concretos, N, modo, escolhas, l, encontrada, fronteira)
                        valor = concretos[l][encontrada]
                        print(f"SAT: ciclo validado; k={k}, início={l}, célula={encontrada}, "
                              f"permanentemente {'viva' if valor else 'morta'}")

                        for t, st in enumerate(concretos):
                            etiqueta = " (fecho = estado %d)" % l if t == k+1 else ""
                            print(f"Estado {t}{etiqueta}: " +
                                  f"{sum(st[i,j] for i in range(1,N+1) for j in range(1,N+1))} vivas")
                            for i in range(N+2):
                                print("".join("#" if (st[i,j] if i<=N and j<=N else False)
                                              else "." for j in range(N+2)))
                            if t <= k and modo == "individual":
                                q = escolhas[t]
                                print(f"  Célula selecionada no passo {t}: ({q//N+1},{q%N+1})")

                        return {"k":k, "loop_inicio":l, "celula":encontrada,
                                "valor":valor, "estados":concretos,
                                "escolhas":escolhas, "validado":True}
                    s.pop()
        print(f"UNSAT: sem ciclo violador com k<= {K}; NÃO é prova global")
        return None

    return (validar_laco, bmc_permanencia)


@app.cell
def _(mo):
    mo.md(r"""## Teste de controlo da segunda propriedade: N=17, individual

    Escolhemos sempre `(17,17)` e procuramos um laço de um estado
    (`k=0`, uma transição que regressa ao estado inicial).
    A célula `(17,17)` está morta e continua morta; `(1,1)` continua viva.
    Executamos com fronteira fixa (semente 42) e também simbólica.
    O modelo SAT deve ser validado independentemente antes da conclusão.
    """)
    return


@app.cell
def _(bmc_permanencia, fronteira_aleatoria):
    def _teste_laco_individual_N17():
        N = 17
        for nome, fr in (("fixa", fronteira_aleatoria(N,42)), ("simbólica", None)):
            print(f"\nTeste de laço N=17 individual, fronteira {nome}")
            r = bmc_permanencia(N, "individual", 0, fr,
                                celula=(17,17), escolher=(17,17))
            assert r is not None and r["validado"] and r["k"] == 0
            assert r["loop_inicio"] == 0 and not r["valor"]
            assert r["escolhas"] == [288]
            assert r["estados"][0][1,1] is True
            assert r["estados"][0][17,17] is False
            print("Confirmadas: (1,1) permanentemente viva; (17,17) permanentemente morta")
    _teste_laco_individual_N17()
    return


@app.cell
def _(mo):
    mo.md(r"""## Experiências exploratórias: modo simultâneo

    Começar com `K=1` em `N=5` e `K=0` em `N=17`,
    usando fronteira fixa e simbólica. O caso `N=17, K=1`
    fica indicado em comentário para testar depois de observar os tempos.
    `UNSAT` limitado não prova a propriedade temporal.
    """)
    return


@app.cell
def _(bmc_permanencia, fronteira_aleatoria):
    def _explorar_simultanea():
        for N, K in ((5, 1), (17, 0)):
            for nome, fr in (("fixa", fronteira_aleatoria(N,42)), ("simbólica", None)):
                print(f"\nModo simultâneo N={N}, K={K}, fronteira {nome}")
                bmc_permanencia(N, "simultanea", K, fr)

        # Mais tarde, caso o tempo seja aceitável:
        # bmc_permanencia(17, "simultanea", 1, fronteira_aleatoria(17,42))
        # bmc_permanencia(17, "simultanea", 1, None)

    _explorar_simultanea()
    return


@app.cell
def _(mo):
    mo.md(r"""## Confirmação SMT do ponto fixo na modalidade simultânea

    Usamos uma testemunha **concreta**, construída em Python sem solver, com
    todas as células iniciais da fronteira mortas. Para `N=5` e `N=17`
    observamos 9, 6, 5, 7, 7 e 7 células vivas em `X0,...,X5`.

    No SMT impomos: `init(X0)`, **cinco** relações `trans(Xt,Xt+1)`
    para `t=0,...,4`, as configurações conhecidas `X0,...,X4` e a
    **igualdade completa** `X5=X4` (incluindo as células da fronteira).

    A transição `T(X4,X5)` é indispensável: a igualdade isolada não provaria
    que `X4` é um ponto fixo.

    O resultado `SAT` é extraído e verificado novamente com `validar_laco`,
    que não usa SMT. Uma fronteira de zeros é uma configuração admitida
    pelo modelo simbólico, suficiente para refutar uma propriedade universal.
    """)
    return


@app.cell
def _(And, Iff, Not, declare, init, trans, validar_laco):
    # LLM — Etapa 6: testemunha de atualização simultânea e confirmação SMT.
    # Esta função NÃO substitui a pesquisa geral bmc_permanencia.
    from pysmt.shortcuts import Solver as TestemunhaSolver

    def testemunha_simultanea(N):
        """Seis estados concretos calculados independentemente do solver."""
        if N < 5:
            raise ValueError("A testemunha conhecida requer N >= 5")

        fronteira = {(i, j): 0 for i in range(N + 1)
                    for j in range(N + 1) if i == 0 or j == 0}
        inicial = {(i, j): bool(1 <= i <= 3 and 1 <= j <= 3)
                   for i in range(N + 1) for j in range(N + 1)}
        estados = [inicial]

        def ler(estado, i, j):
            if 0 <= i <= N and 0 <= j <= N:
                return int(estado[i, j])
            if 0 <= i <= N + 1 and 0 <= j <= N + 1 and (i == N + 1 or j == N + 1):
                return 0
            raise ValueError(f"Coordenada inválida: {(i, j)}")

        for _passo in range(5):
            anterior = estados[-1]
            seguinte = anterior.copy()
            for i in range(1, N + 1):
                for j in range(1, N + 1):
                    vizinhos = sum(ler(anterior, i + di, j + dj)
                                   for di in (-1, 0, 1) for dj in (-1, 0, 1)
                                   if (di, dj) != (0, 0))
                    seguinte[i, j] = (vizinhos == 3 or
                                      (anterior[i, j] and vizinhos == 2))
            estados.append(seguinte)

        return estados, fronteira

    def confirmar_testemunha_simultanea(N, simbolica=False):
        """Confirma no Z3 uma testemunha completa com laço X4 -> X4."""
        referencia, fronteira_zero = testemunha_simultanea(N)
        contagens = [sum(s[i, j] for i in range(1, N + 1)
                         for j in range(1, N + 1)) for s in referencia]

        assert contagens == [9, 6, 5, 7, 7, 7], contagens
        assert referencia[4] == referencia[5], "A testemunha não fecha o laço"

        etiqueta = f"testemunha_{N}_{'simbolica' if simbolica else 'fixa'}"
        X = [declare(f"{etiqueta}_{t}", N) for t in range(6)]

        formulas = [init(X[0], N, None if simbolica else fronteira_zero)]

        # Inclui obrigatoriamente a transição do estado X4 para X5.
        formulas += [trans(X[t], X[t + 1], N, "simultanea")
                     for t in range(5)]

        # Fixar a testemunha nos estados X0,...,X4.
        # O estado X5 será determinado pelo solver.
        for t in range(5):
            formulas.append(And([
                X[t][p] if referencia[t][p] else Not(X[t][p])
                for p in X[t]
            ]))

        # Fecho do laço: todas as células de X5 iguais às de X4.
        formulas.append(And([
            Iff(X[5][p], X[4][p])
            for p in X[4]
        ]))

        with TestemunhaSolver(name="z3") as solver:
            solver.add_assertion(And(formulas))
            sat = solver.solve()

            print(
                f"N={N}, "
                f"fronteira={'simbólica (testemunha zero)' if simbolica else 'fixa zero'}: "
                f"SMT={'SAT' if sat else 'UNSAT'}"
            )

            if not sat:
                raise AssertionError(
                    "Testemunha inconsistente com init/trans/fecho"
                )

            concretos = [
                {p: bool(solver.get_py_value(v)) for p, v in estado.items()}
                for estado in X
            ]

        # Verificação independente das fórmulas SMT.
        assert concretos == referencia, "Estados extraídos diferem da testemunha"

        assert validar_laco(
            concretos,
            N,
            "simultanea",
            [None] * 5,
            4,
            (1, 3),
            fronteira_zero
        )

        assert concretos[4][1, 3] and not concretos[4][N, N]

        print(f"Estados 0..5: {contagens} células normais vivas")
        print("init, cinco transições B3/S23 e fecho X5=X4: confirmados")
        print("Validador independente: OK; (1,3) permanentemente viva no ciclo")

        return {
            "sat": True,
            "N": N,
            "contagens": contagens,
            "inicio_laco": 4,
            "estados": concretos,
            "validado": True
        }

    return (testemunha_simultanea, confirmar_testemunha_simultanea)


@app.cell
def _(confirmar_testemunha_simultanea):
    def _testar_ponto_fixo():
        # LLM — N=5 para depuração, N=17 para a conclusão do exercício.
        # Também testamos que a testemunha é permitida na fronteira simbólica.
        for N, simbolica in (
            (5, False),
            (17, False),
            (17, True)
        ):
            resultado = confirmar_testemunha_simultanea(N, simbolica)

            assert resultado["sat"] and resultado["validado"]
            assert resultado["inicio_laco"] == 4

        print("Confirmação da testemunha simultânea concluída.")

    _testar_ponto_fixo()
    return


@app.cell
def _(mo):
    mo.md(r"""## Limitações e reprodução

    - Resultados `SAT` com laço e transições validadas refutam a propriedade
      temporal para o modelo considerado.
    - `UNSAT` para laços de tamanho até `K+1` **não** é prova global.
    - A variante individual admite passos sem alterações e **não** impõe justiça
      na escolha das células; acrescentá-la modificaria a especificação.
    - No caso simbólico, uma testemunha com fronteira toda morta refuta
      a propriedade universal, mas não mostra que falha em todas as fronteiras.
    - A confirmação de um ponto fixo exige tanto X5=X4 como T(X4,X5).
    - Registar versão do Python, pySMT e Z3, `N`, `K`, semente, modo, tempo
      e resultados efetivamente obtidos. Não existem medições nesta versão.

    **LLM:** modelação temporal, codificação do fecho do ciclo,
    implementação do BMC com laço e do validador independente.
    Partilhar o diálogo com a LLM e validar os resultados pelos alunos.
    """)
    return


if __name__ == "__main__":
    app.run()
