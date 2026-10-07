# Actual radial subpolynomial bridge

Eighth cycle. Verdict **BRIDGE**, not a standalone novelty claim. G remains unproved until its refined remainder and coefficient argument are closed.

Exact statement: for every actual hW and every p>0 there exists C≥0 such that
|F(x+iy)|≤C(1+|y|)^p for 1/2<x≤3/2 and |y|≥2. Here F is the quotient of the already constructed canonical completion by s(s−1)Γ_R(s). Its everywhere-defined radial trace satisfies the same type of bound for every y. No edge continuity is supplied.

## Dependency-closed paper proof

1. Fix 0<δ<1/2 and ε>0. The compiled `exists_producerZeta_subpolynomial_of_weilPositiveFull` supplies, for all sufficiently large |y|, a holomorphic logarithm g on B(3+iy,5/2−δ/4). Its exponential is bounded by (|y|+3)^ε on 1/2+δ≤x≤5/2 and agrees with the defining logarithmic Dirichlet series on Re s>1. The ball lies in Re s>1/2 and avoids 1 when |y|≥2: the squared distance from its centre to 1 is 4+y², greater than its radius squared. F is therefore holomorphic on the ball. The existing arithmetic identity on Re s>1 and the identity theorem give F=exp(g) throughout it. This proves the asserted interior bound uniformly in x.
2. For 1/2≤x≤u≤3/2 and |y|≥2, the compiled uniform Gamma shift estimate, with a=x/2, b=u/2 and τ=|y|/2, gives
   |Γ_R(u+iy)|≤exp(3)(1+|y|)^((u−x)/2)|Γ_R(x+iy)|.
   Indeed τ≥1, (1/2)log(b²+τ²)≤log(1+|y|), and 1/τ²+π/(2τ)≤3. Multiplication by d=(u−x)/2∈[0,1/2] bounds the exponent by d log(1+|y|)+3/2. The prefactor π^(−u/2)≤π^(−x/2). Conjugation covers both signs of y. Every bound is uniform in x,u.
3. Horizontal monotonicity of the actual completion gives |G(x+iy)|≤|G(u+iy)|. Each of |u+iy|/|x+iy| and |u−1+iy|/|x−1+iy| is at most 2, since |y|≥2 and x,u∈[1/2,3/2]. Dividing by the nonzero Gamma and polynomial factors yields
   |F(x+iy)|≤4 exp(3)(1+|y|)^((u−x)/2)|F(u+iy)|.
4. Set δ=min(p,1/4), ε=p/2, and u=max(x,1/2+δ). Then 0≤u−x≤δ and u≤3/2. Steps 1–3 and (|y|+3)^ε≤3^ε(1+|y|)^ε give a constant times (1+|y|)^(ε+δ/2)≤(1+|y|)^p. On the remaining bounded height range, the already compiled square-root open-strip bound gives one uniform constant; no compact extension of G is needed.
5. At each fixed |y|≥2 take x↓1/2 in the actual radial limit, retaining the uniform bound. On |y|≤2, use the compiled compact bound for the actual trace and (1+|y|)^p≥1. Enlarging C completes the all-height trace statement.

This proof has no open inference. It supplies G's refined-growth input only. The moving-tail remainder, cumulative residual phase and coefficient comparison still require separate proofs; no source growth law for residual mass follows from these analytic bounds.
