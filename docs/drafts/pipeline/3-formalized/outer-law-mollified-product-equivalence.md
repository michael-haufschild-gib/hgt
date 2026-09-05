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
