import sympy as sp
from sympy import prod

def test(N):
    a = list(sp.symbols(f'a1:{N+1}'))
    c = [sp.Integer(1)] + list(sp.symbols(f'c2:{N+1}'))   # rate c1 = 1, others symbolic
    def D(expr):
        expr = sp.expand(expr)
        out = 0
        for i in range(N):
            out += sp.diff(expr, a[i]) * (c[i]*(a[i]-a[i]**2))
        return sp.expand(out)
    g = prod(a)
    jets = [g]
    for _ in range(N-1):
        jets.append(D(jets[-1]))
    J = sp.Matrix([[sp.diff(jets[k], a[i]) for i in range(N)] for k in range(N)])
    det = sp.factor(J.det())
    nonzero = det != 0
    # look for Vandermonde-in-rates factor prod_{i<j}(c_i-c_j)
    vand = prod([ (c[i]-c[j]) for i in range(N) for j in range(i+1,N) ]) if N>1 else sp.Integer(1)
    quotient = sp.simplify(det/vand) if nonzero and vand!=0 else None
    div_clean = quotient is not None and sp.simplify(quotient*vand - det)==0 and quotient.is_polynomial(*a)
    print(f"=== N={N} ===")
    print(f"  order = N (det != 0)? {nonzero}")
    print(f"  det factored: {det}")
    print(f"  Vandermonde(rates) divides det cleanly? {div_clean}")
    if div_clean:
        print(f"  det / Vandermonde = {sp.factor(quotient)}")

for N in (2,3,4):
    test(N)
