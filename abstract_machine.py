#!/usr/bin/env python3
"""abstract_machine - SECD abstract machine for lambda calculus evaluation.

Usage: python abstract_machine.py [--demo]
"""

# AST
class Var:
    def __init__(self, n): self.n = n
    def __repr__(self): return self.n
class Lam:
    def __init__(self, p, b): self.p = p; self.b = b
    def __repr__(self): return f"(λ{self.p}. {self.b})"
class App:
    def __init__(self, f, a): self.f = f; self.a = a
    def __repr__(self): return f"({self.f} {self.a})"
class Num:
    def __init__(self, v): self.v = v
    def __repr__(self): return str(self.v)
class BinOp:
    def __init__(self, op, l, r): self.op = op; self.l = l; self.r = r
    def __repr__(self): return f"({self.l} {self.op} {self.r})"
class If:
    def __init__(self, c, t, e): self.c = c; self.t = t; self.e = e
    def __repr__(self): return f"(if {self.c} {self.t} {self.e})"
class Let:
    def __init__(self, n, v, b): self.n = n; self.v = v; self.b = b
    def __repr__(self): return f"(let {self.n}={self.v} in {self.b})"
class LetRec:
    def __init__(self, n, v, b): self.n = n; self.v = v; self.b = b
    def __repr__(self): return f"(letrec {self.n}={self.v} in {self.b})"

class Closure:
    def __init__(self, param, body, env):
        self.param = param; self.body = body; self.env = env
    def __repr__(self): return f"<closure λ{self.param}>"

class RecClosure(Closure):
    def __init__(self, name, param, body, env):
        super().__init__(param, body, env); self.name = name

# SECD Machine
class SECD:
    def __init__(self):
        self.steps = 0

    def eval(self, expr, env=None):
        if env is None: env = {}
        # S=stack, E=environment, C=control, D=dump
        S, E, C, D = [], dict(env), [expr], []
        ops = {'+': lambda a,b: a+b, '-': lambda a,b: a-b,
               '*': lambda a,b: a*b, '/': lambda a,b: a//b if b else 0,
               '==': lambda a,b: a==b, '<': lambda a,b: a<b, '>': lambda a,b: a>b,
               '%': lambda a,b: a%b}

        while C or D:
            self.steps += 1
            if self.steps > 100000:
                raise RuntimeError("Max steps exceeded")

            if not C:
                # Return from function call
                if not D: break
                result = S[-1]
                S, E, C = D.pop()
                S.append(result)
                continue

            ctrl = C.pop()

            if isinstance(ctrl, Num):
                S.append(ctrl.v)
            elif isinstance(ctrl, Var):
                if ctrl.n not in E:
                    raise NameError(f"Unbound: {ctrl.n}")
                S.append(E[ctrl.n])
            elif isinstance(ctrl, Lam):
                S.append(Closure(ctrl.p, ctrl.b, dict(E)))
            elif isinstance(ctrl, App):
                C.append(('ap',))
                C.append(ctrl.a)
                C.append(ctrl.f)
            elif isinstance(ctrl, BinOp):
                C.append(('binop', ctrl.op))
                C.append(ctrl.r)
                C.append(ctrl.l)
            elif isinstance(ctrl, If):
                C.append(('if', ctrl.t, ctrl.e))
                C.append(ctrl.c)
            elif isinstance(ctrl, Let):
                C.append(('let', ctrl.n, ctrl.b))
                C.append(ctrl.v)
            elif isinstance(ctrl, LetRec):
                clos = RecClosure(ctrl.n, ctrl.v.p, ctrl.v.b, dict(E))
                clos.env[ctrl.n] = clos
                E[ctrl.n] = clos
                C.append(ctrl.b)
            elif isinstance(ctrl, tuple):
                tag = ctrl[0]
                if tag == 'ap':
                    arg = S.pop(); fn = S.pop()
                    if isinstance(fn, (Closure, RecClosure)):
                        D.append((S[:], dict(E), C[:]))
                        S.clear()
                        E.clear()
                        E.update(fn.env)
                        E[fn.param] = arg
                        if isinstance(fn, RecClosure):
                            E[fn.name] = fn
                        C.clear()
                        C.append(fn.body)
                    elif callable(fn):
                        S.append(fn(arg))
                elif tag == 'binop':
                    b = S.pop(); a = S.pop()
                    S.append(ops[ctrl[1]](a, b))
                elif tag == 'if':
                    cond = S.pop()
                    C.append(ctrl[1] if cond else ctrl[2])
                elif tag == 'let':
                    val = S.pop()
                    E[ctrl[1]] = val
                    C.append(ctrl[2])

        return S[-1] if S else None

def main():
    print("=== SECD Abstract Machine ===\n")
    machine = SECD()

    tests = [
        ("42", Num(42), 42),
        ("3 + 4", BinOp('+', Num(3), Num(4)), 7),
        ("(λx. x + 1) 5", App(Lam("x", BinOp('+', Var("x"), Num(1))), Num(5)), 6),
        ("let x=10 in x*2", Let("x", Num(10), BinOp('*', Var("x"), Num(2))), 20),
        ("if 1 then 42 else 0", If(Num(1), Num(42), Num(0)), 42),
        ("(λf. λx. f(f(x))) (λy. y+1) 0",
         App(App(Lam("f", Lam("x", App(Var("f"), App(Var("f"), Var("x"))))),
                 Lam("y", BinOp('+', Var("y"), Num(1)))), Num(0)), 2),
    ]

    for name, expr, expected in tests:
        machine.steps = 0
        result = machine.eval(expr)
        status = "✓" if result == expected else f"✗ (got {result})"
        print(f"  {name:40s} = {result:5} {status} ({machine.steps} steps)")

    # Factorial with letrec
    print(f"\nRecursion (letrec):")
    fact = LetRec("fact",
        Lam("n", If(BinOp('<', Var("n"), Num(2)),
                     Num(1),
                     BinOp('*', Var("n"), App(Var("fact"), BinOp('-', Var("n"), Num(1)))))),
        App(Var("fact"), Num(10)))
    machine.steps = 0
    result = machine.eval(fact)
    print(f"  fact(10) = {result} {'✓' if result==3628800 else '✗'} ({machine.steps} steps)")

if __name__ == "__main__":
    main()
