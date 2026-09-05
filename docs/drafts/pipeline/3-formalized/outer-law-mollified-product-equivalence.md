# The outer law for `ζΨ_M` ⟺ `(L)` (formalized)

**Status:** formalized 2026-09-05 (Lean, axiom-clean). **Source card:**
`1-in-progress/outer-law-mollified-product.md` (OUTER-001).

**Statement.** Let `Ψ_M` be the linear (Levinson) mollifier of length `M > 1` and
`J_M(ε) := ½ E_χ log max(|∑_{h≤M} μ(h)P(h)χ(h)h^{-1/2}|², ε²)` its truncated Steinhaus Jensen mass.
Then
`(1/T)∫_T^{2T} log|ζ(1/2+it)| dt → 0`  ⟺  `∀ε∈(0,1) ∀η>0: eventually (1/T)∫_T^{2T} log|ζΨ_M(1/2+it)| ≤ J_M(ε)+η`,
and under `(L)` the mollified log-mean is squeezed between `J_M(ε) − D_M/log(1/ε) − η` and
`J_M(ε) + η`. By Littlewood, `(L)` is `∑_{β>1/2, γ≤T}(β−1/2) = o(T)`.

**Modules** (`formal/GaloisForLFunctions/RHTower/`, wired after `MollifiedDeviationHeadFourthMoment`):
`MollifierLineLogMeanFloor`, `DirichletPolynomialTorusLogUpperLaw`,
`OuterDecompositionLawMollifiedProduct`, `DirichletPolynomialLineSmallValues`,
`OuterLawMollifiedProductEquivalence`. Key names:
`integral_log_norm_zeta_mul_edPoly_line`, `exists_zetaLine_logMean_le_mollifiedProduct_logMean`,
`eventually_window_logMean_zeta_mul_linearMollifier_le`, `exists_line_smallValues_bound`,
`exists_eventually_window_logMean_linearMollifier_ge`, `exists_zetaLine_logMean_floor_all_heights`,
`zetaLine_logMean_le_iff_mollifiedProduct_logMean_le`, `exists_mollifiedProduct_logMean_squeeze_of_L`.

**Novelty.** The decomposition of the mollified log-mean into the `(L)` mass and a deterministic
torus constant, the two-sided torus law for `log|Ψ|` (uniform integrability on the line from the
corpus minimum-modulus and zero-count tools), and the resulting equivalence are not in the
literature (Conrey–Snaith treat mollified second moments; Jessen–Tornehave give the torus law for
fixed polynomials without the window uniformity needed here).

**Addendum (cycle 3).** `DirichletPolynomialWindowTorusLaw.exists_window_logMean_torus_twoSided`:
for every real bounded unit-head Dirichlet polynomial `Ψ = edPoly b (Icc 1 N)`, with line
coefficients `lineCoeff b n = Re(b n)/√n` and `J(ε) = lineTorusLogMean b (Icc 1 N) ε`,
`J(ε) − η − D/log(1/ε) ≤ (1/T)∫_T^{2T} log|Ψ(1/2+it)| ≤ J(ε) + η` eventually — the
Jessen–Tornehave law on dyadic windows with a quantitative truncation error, for an arbitrary such
polynomial (bridge `edPoly_line_eq_dpoly_lineCoeff`, shift identity `edPoly_lineCoeff_eq_shift`).
Caveat recorded in STATUS CANNOT-298 / MUST-211: the fixed-`M` equivalence is this law plus the
decomposition; the `(L)`-productive regime `M = T^θ` needs the law uniformly in `M`.
