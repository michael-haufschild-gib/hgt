# CCM-FU proportional-admission no-go — paper proof, Lean incomplete

This is an own scratch research note, not an edit to the read-only route map. The theorem below is a proposed source-specific obstruction to a class of exhaustive histories. It does not prove RH or the existence/nonexistence of arbitrary source-selected histories. Literature priority is not established.

## Theorem

Fix a real `c>1`. At every integer cutoff `M`, process exactly the active primes `p` with `c p≤M`; denote this core by `P_c(M)`. Then there are a natural `k=k(c)` and a nonzero real `m_k(c)` such that the literal processed head satisfies

`H_c(M) ~ m_k(c) M^(3/2)/(log M)^(k+1)`.

Consequently `mobiusDivisorSelectionEnergy M P_c(M) / M² → +∞`. Thus no fixed multiplicative admission lag, however close to one, can be an all-cutoff quadratic-budget history. The result covers exceptional ratios where the first, or any finite initial run of, signed quotient-window moments vanishes.

## Proof

Write `C(x)=criticalContinuousAbel x`. The corpus proves `C(x)=0` for `x≤1`, `C(M)=Σ_{d≤M}mobiusDivisorDilationChannel M d`, and the arbitrary terminal-core head identity. Since `M≥c²` and `p²≤M` imply `cp≤M`, `P_c(M)` is terminal for all sufficiently large `M`. Its unprocessed primes are exactly `M/c<p<M`, so the source identity is

`H_c(M)=C(M)+Σ_{M/c<p<M}√p C(M/p)`.                                                   (1)

The square-root Abel interpolation gives, for `1≤y≤2`,

`C(y)=(√y−1)(2γ−1)`.

The corpus proves `γ>1/2`, so `C(y)>0` throughout `(1,2]`. On every compact interval `[1,c]`, `C` is continuous and piecewise `C¹`, hence of bounded variation.

Define signed log moments

`m_j(c)=∫_1^c C(y)y^(-5/2)(log y)^j dy`.

Some `m_j(c)` is nonzero. Otherwise put `t=log y` and `f(t)=C(e^t)e^(-3t/2)` on `[0,log c]`. All polynomial moments of the continuous `f` vanish. Uniform polynomial approximation to `f` would imply `∫ f²=0`, contradicting its strict positivity on `(0,min(log c,log 2))`. Let `k` be the first nonzero moment.

The corpus's strong Chebyshev-theta PNT gives `θ(x)=x+O(x exp(-a√log x))`. Apply Stieltjes partial summation on `[M/c,M]` to the bounded-variation weight `g_M(t)=√t C(M/t)/log t`. Since `t≈M` on this interval and `C` is piecewise `C¹` on `[1,c]`, the boundary and variation errors are `O_c(M^(3/2) exp(-a'√log M))` for some `a'>0`. Therefore

`Σ_{M/c<p<M}√p C(M/p)
 = M^(3/2)∫_1^c C(y)y^(-5/2)/log(M/y)dy
   + O_c(M^(3/2)exp(-a'√log M))`.                                              (2)

For `M>c²`, expand `1/log(M/y)` uniformly on `1≤y≤c` through order `k`:

`1/log(M/y) = Σ_{j=0}^k (log y)^j/(log M)^(j+1)
                 + O_c((log M)^(-k-2))`.

By the choice of `k`, (2) becomes `m_k(c) M^(3/2)/(log M)^(k+1)` plus a lower-order term. Strong PNT for `ψ`, inserted into the exact Abel primitive, gives `C(M)=O(M^(3/2)exp(-a''√log M))`; the constant `2γ` contributes only `O(√M)`. This is lower order than the displayed main term. Equation (1) proves the head asymptotic.

The literal selection energy contains `H_c(M)²` as a nonnegative summand, even before using terminality. Hence its ratio to `M²` is at least asymptotic to `m_k(c)² M/(log M)^(2k+2)`, which tends to infinity.

## Independent Mellin check

Let `H_c(x)=C(x)+Σ_{p<x<cp}√p C(x/p)` for real `x≥1`. At integers this is (1). On each unit cell, the literal source interpolation and `|ψ(n)-n+2γ|=O(n)` give `|C(x)-C(⌊x⌋)|=O(√x)` and a total prime-child change `O(√x log x)`. The indicator `x<cp` can switch for at most one integer prime in a unit cell because `c>1`; its jump is `O_c(√x)`. Thus an assumed `H_c(M)=O(M)` would imply `H_c(x)=O(x)`.

For real `s>3/2`, dilation and absolute convergence give the exact identity

`Mellin(H_c)(s)=J(s)+primeZeta(s−1/2)J_c(s)`,

where `J(s)=∫_1^∞C(y)y^(−s−1)dy` and `J_c(s)=∫_1^c C(y)y^(−s−1)dy`. Strong PNT gives every absolute boundary log moment of `C`, so `J` is `C^∞` from the right at `s=3/2`. The compactly supported `J_c` is entire and not identically zero by the unit-cell positivity; let `k` be its finite zero order at `3/2`. Since `primeZeta(1+δ)=log(1/δ)+O(1)`, the product has a nonzero `δ^k log(1/δ)` term and cannot be `C^k` at the boundary. But `H_c(x)=O(x)` would make its Mellin transform holomorphic on `Re(s)>1`, hence `C^k` there. Contradiction. This verifies the no-go without relying on the full asymptotic expansion, though it does not replace the asymptotic proof of the stated sharp rate.

## Whole-route meaning and audit boundary

This excludes every history whose admission front is one fixed proportional distance behind prime birth. It complements the earlier paper law excluding arbitrary *polynomially delayed* histories: this result reaches much shorter delay but assumes a rigid fixed-ratio schedule. It extends the corpus's half-prime (`c=2`) head escape to all `c>1`, including cancellation of finitely many window moments. It does **not** imply that every prime in a viable history must be admitted at ratio `1+o(1)`; a nonstationary, source-selected mix of early and late admissions may still balance. The theorem does not control the changing-core covariance or produce an RH proof.

Lean status: local unit-cell positivity is being checked in `scratch/codex-root-proportional-delay.lean`; terminal-core identity is already corpus-certified. The compact moment nonflatness and weighted-PNT asymptotic (2) have not been formalized. No broad/umbrella build was run.
