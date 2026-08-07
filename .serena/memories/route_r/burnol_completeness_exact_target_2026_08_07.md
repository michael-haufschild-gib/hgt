# Burnol completeness: the exact statements to formalize (literature-anchored)

Source: J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann
zeta function*, J. Théor. Nombres Bordeaux 16 (2004) 65--94 (arXiv math/0203120).  Aperture
convention **matches the corpus**: `L_a` = extended Sonine space at aperture `a`; the co-Poisson
subspace `P_a` is defined for `0 < a < 1` as the square-integrable co-Poisson sums of
`g in L^1(a, 1/a)`.  `Y_a` = closed span of the zero evaluators `Y_{a,rho,k}`, `0 <= k < m_rho`.

**Theorem 3.1.**  `Y_{a,rho,k}` are minimal in `L_a` iff `a <= 1`, complete iff `a >= 1`.
**For `a < 1` the perpendicular complement to `Y_a` is `P_a`.**  For `a > 1` one may omit finitely
many and still have a complete system.

That last clause is exactly what the `gamma-copoisson-sonin-full-quotient-flatness-syzygy` card's
equation `(2)` needs:

    0 < a < 1  =>  closure (span {Y_{a,rho,k}}) = burnolCoPoissonQuotientSpace a.

Burnol attributes the proof to *Entrelacement de co-Poisson*, Chap. 6, Thms 6.24--6.25.

**Proposition 2.2** (from *Entrelacement* 6.10) is the enabling construction, and it is what the
corpus lacks:

    f in L_a  =>  M(f)(s) = pi^{-s/2} Gamma(s/2) f^(s) is meromorphic on all of C with poles only
    at 0 and 1; f |-> M(f)^{(k)}(w) is a continuous linear form for w != 0,1; and
    M(F_+ f)(s) = M(f)(1-s).

`Y_{a,w,k}` is its Riesz vector **for the bilinear form** `[f,g] = ∫_0^∞ f g dt`, not the Hermitian
one.

**Why this matters.**  The corpus's `burnolExtendedSoninEvaluationVector` is built from an
absolutely convergent integral, so it exists only for `Re w != 1/2`; on the critical line the
integral diverges for a constant-head `L^2` vector.  Under RH all nontrivial zeros are on the line,
so any completeness statement using only the corpus's present evaluators has an empty index family
and is **false** (the quotient is not trivial).  The fix is the meromorphic **continuation** of
Prop. 2.2, not a limiting/Riesz construction on the line.

Also useful from the same paper: Prop 6.1 (completeness for `a >= 1` via Krein's theorem on
Nevanlinna-class functions of finite exponential type), Prop 6.4 (`a < 1`: minimal, not complete),
Theorem 6.3 (`a = 1`: minimal and complete), Prop 4.3 (division: if
`s(s-1) pi^{-s/2}Gamma(s/2) G(s)` vanishes at `w` then `G(s)/(s-w)` is again in `L^_a`),
Theorem 4.8 (the L-property, with the explicit constant-head splitting
`G(s) = -c(g) a^{1-s}/(s-1) + int_a^infty g t^{-s} dt`), Theorem 7.1--7.3 and 7.8 (the general
threshold `a(Z)`).

Lean sub-targets, in order: (1) the meromorphic continuation; (2) evaluator vectors at every
`w != 0,1`; (3) the functional equation on the whole space; (4) the perpendicular-complement
theorem for `0 < a < 1`.
