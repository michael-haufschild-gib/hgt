# Cauchy marginal of the critical-line log-derivative is blind to clustered horizontal displacement

- **ID:** cauchy-marginal-displacement-blindness
- **Stage:** 1-in-progress (theorem part is Lean-closed; the RH-bearing part is an audited failure)
- **Type:** THEOREM (Lean) for the picket-fence law · FALSIFIED for the naive converse · audit of two external leads
- **Source:** `docs/reports/This week produced one extraordinary but.md` (2026-09-18 leads):
  Najnudel–Nikeghbali arXiv 2609.15862 (14 Sep 2026); Desogus arXiv 2609.20367 (17 Sep 2026)
- **Statement:** (i) Exact cotangent law for the Poisson-smoothed `k`-periodic picket fence of mass-`k`
  atoms at width `η`; (ii) Boole's law `−cot(πU) ~ Cauchy(0,1)` exactly; (iii) the smoothed statistic is
  bounded for every `η > 0` yet its law tends to `Cauchy(0,1)` as `k → ∞` at fixed `η`. Hence the
  marginal Cauchy law of a one-point microscopic Stieltjes/log-derivative statistic cannot detect
  horizontal displacement hidden in growing clusters; Najnudel–Nikeghbali's sufficient condition
  `H(T) = o(T)` is not necessary in the abstract stationary setting.

## Goal
The two leads were read in full (HTML text in the session scratchpad). Their placement relative to
the corpus, and the producer attempts they suggest, are recorded here so that no later session
re-runs them.

### Lead 1 — Najnudel–Nikeghbali (NN), `2609.15862`
- Objects: `u_{ρ,T} = (γ − t_T)L/2π`, `η_{ρ,T} = (β − ½)L/2π`, `P_T = −(1/π)Σ m(ρ)/u_{ρ,T}` (projected,
  `|u| ≤ L²`), `A_T = (2i/L)(ζ'/ζ)(½ + i t_T) + i`, `H(T) = Σ_{0<γ≤2T, β>½} m(ρ)(β − ½)`.
- Theorem 7.1 (unconditional): `P_T ⟹ Cauchy(0,1)`; inputs are Riemann–von Mangoldt, Fujii's
  mean-square increment `∫_0^T |S(t+h) − S(t)|² ≪ T log²(2 + |h| log T)` (their (7.4)/(7.5)), and a
  stationary-measure transfer theorem. Theorem 8.7: `H(T) = o(T) ⟹ A_T ⟹ Cauchy(0,1)`, with
  `d_BL(Law A_T, Law P_T) ≤ C√(H(T)/T) + C/log T`.
- Prop 8.2 (exact): `A_T − P_T = (2/π)Σ_{β>½} m η²/(u(u²+η²)) + O(log L/L)` — the correction is
  `(4π/L)` times the Hilbert transform of `ν_T = Σ_off m(P_{β−½}(·−γ) − δ_γ)`.
- Prop 8.5: `H(T) = o(T)` ⟺ `D_ε(T) = o(T log T)` for every `ε` ⟺ any fixed positive moment
  `Σ m(β−½)^q = o(T L^{1−q})`; Lemma 8.4: `μ_T([b,∞)) ≤ Ce^{−b/4}` from Selberg density.
- Line 1583 of the paper: negligibility of the correction "is not asserted to be necessary for the
  marginal limit itself" — the converse is left open.

**Corpus placement.** `H(T)` is exactly the corpus gate `(L)` (`Σ(β−½)⁺ = o(T)` ⟺ log-mean of
`|ζ|` on the line → 0; cards `zeta-off-line-first-moment-mollified-ceiling`, `outer-law-mollified-product`,
`rs-phase-locking-geometric-mean-law`). The corpus's Lean ceiling
`exists_zetaOffLineFirstMoment_le_of_mollified_meanSquare` gives `H(T) ≤ 0.0714·T` (paper constant
with Conrey/Young; single remaining analytic input = the mollified mean square, owned by the analytic
lane) and the displacement tail `p_T(a) ≤ 2.40 e^{−8a/7}` (Conrey exponent), both sharper than NN's
Lemma 8.4 (`≪ T`, rate `1/4`). NN's new content relative to the corpus is the receiver
`(L) ⟹ Cauchy(A_T)`; it adds no mechanism for `(L)`.

### Lead 2 — Desogus (`2609.20367`, claimed proof of RH)
- Theorem 1.2 (odd restricted Weil criterion): for real odd `f`, `W[f] = Σ_λ −F(λ)²`; RH ⟺ `W ≥ 0`
  on real odd `C_c^∞`. Corpus already owns this: real odd tests = zero-mean Suzuki tests
  (`SuzukiSmoothZeroMeanTest`), exact ray-term law `Q(cos(γx)ψ) = Σ' −¼(A_q+A'_q)²/z_q²`
  (`ConstrainedWeilTwistedOddTest`), on-line terms `≥ 0`, and the negativity witness at an attained
  top excess (`ConstrainedWeilApertureWindowMean.exists_aperture_twistedOddTest_neg_of_attainedTop`,
  MUST-259). Nothing to formalize.
- Theorem 0.1 / Cor. 8.6: `A_{a,−} ⪰ 0` for all support radii `a`, by a computer certificate at `a = 7`
  (smallest eigenvalue `1.07·10⁻²⁴`) plus an induction `A_{k,−} ≻ 0 ⟹ A_{k+1,−} ≻ 0` (Theorem 8.5,
  "MASTER coercivity on the exact harmonic graph", Schur complement w.r.t. the collar `(k, k+1)`).
- Structural facts established here by reasoning (no computation, per the session rules):
  1. The base margin is the undersampling floor, not an arithmetic quantity: for real odd
     `f ∈ L²(−a,a)` with `F(z) = z(sinh(az/N)/(az/N))^N`, `N ≈ aγ₁/e`, one has
     `Σ_λ |F(λ)|² ≤ C e^{−(2γ₁/e)(1−o(1))a}` because the zeros below height `2πe^{2a}` are sparser
     than the Nyquist density `a/π` of `PW_a`; at `a = 7` this is `≈ 10^{−27}`, matching the certified
     `10^{−24}`. So `λ_min(A_{a,−}) ≤ e^{−ca}` for every `a` (unconditionally; negative if RH fails and
     `a` is large), and any uniform induction must transport margins that decay at least like `e^{−5k}`.
  2. The `k → k+1` Schur step is a statement about the exact prime data; its collar/cross blocks carry
     the smoothed PNT error `ψ(x) − x` at scale `x^{1/2}` over `(e^{2k}, e^{2k+2}]`. A uniform-in-`k`
     proof of the step is therefore a proof of an RH-strength prime estimate by finite-dimensional
     linear algebra. This is not a refutation; it is the reason the step cannot be checked by
     reasoning alone. The report's proposed falsification (recompute `A_{7,−}` and the `7 → 8` Schur
     complement) is a computation and is excluded by the session rules.
- Verdict: **not refuted, not verified**. The paper contains a fictional dialogue ("Mr. Fayman",
  "Herr G.F.B.R."); treat as unreviewed.

## Approach — producer attempts on `(L)` suggested by the leads, all failed
Each mechanism below was carried to the point where it reduces to Littlewood's first moment or to
an RH-strength error term; none gives a new inequality.

- **M1 (Boole tails).** For positive measures `|{Hμ > λ}| ≤ ‖μ‖/λ`, with equality for atomic `μ`
  (Boole; Hruščëv–Vinogradov for singular). So `P(A_T > λ) ≤ P(P_T > λ)` termwise, and the tail
  constant `lim_λ (π/2)λ P(|A_T| > λ)` at fixed `T` is exactly the on-line proportion. The deficit
  integrated against `dλ/λ` is `≍ Σ_off m η` = the first moment: Littlewood in disguise. No new bound.
- **M2 (Hilbert-pair defect).** Under RH `log|ζ(½+it)|` and `πS(t)` are a Hilbert pair; the defect
  `D = πS − H[log|ζ|]` has `‖D‖₂² ≍ H(T)`. So `(L)` ⟺ `⟨S, H log|ζ|⟩ = ½(‖πS‖² + ‖H log|ζ|‖²) + o(T)` —
  an `o(T)` error in a Selberg-type mixed second moment whose main term is `T log log T`: RH-strength.
- **M3 (Gaussian prime side + zero side).** Selberg's formula splits `A_T = G_T + K_T` with `G_T` a
  Dirichlet polynomial (Gaussian limit, variance `2θ²`, corpus torus machinery) and `K_T` a zero-side
  kernel sum with the `e^{2πθη}` amplification. `E log|ζ|` has prime-side mean `0` identically, so the
  mean of the zero side is `cH/T`: the identity carries no constraint. Variance of the zero side stays
  `≍ 1` even under RH (log singularities), so no moment of the decomposition is RH-sensitive
  (consistent with CANNOT-295, `first_moment_is_a_count`).
- **M4 (fractional moments reversed).** `E|C_T|^p ≍ W_p(2T)/(TL^p)` two-sided for separated
  configurations, but `E|A_T − P_T|^p` has no independent evaluation: circular.
- **Unconditional Montgomery cannot bound the off-line diagonal.** In `montgomeryForm` the pair
  `{ρ, 1−ρ̄}` contributes `2cosh(2αa L) + 2` to the diagonal, but the cross blocks with other
  ordinates have real part `∫ r̂(α) cos(αv)·4cosh(αLa_j)cosh(αLa_k) dα`, which is not signed for
  any admissible `r̂ ≥ 0` (analytic continuation `Re r(v ± ic)` changes sign). So `F(α) ~ α` gives no
  density estimate — as it must not.

## No-go closure
- **Exact killing theorem/mechanism (for the naive converse of NN Thm 8.7):** the `k`-periodic
  picket fence of mass-`k` atoms Poisson-smoothed at width `η` has Hilbert transform
  `π Re cot(π(x − iη)/k)` (Lean `picketTransform_eq_pi_mul_re_cot`); at a uniform microscopic point
  the normalised statistic is `−Re cot(π(U − iη/k))`, bounded by `cosh(πη/k)/|sinh(πη/k)|`
  (`abs_smoothedStat_le`, so its law has no Cauchy tail at all), and converges in law to
  `Cauchy(0,1)` as `k → ∞` at fixed `η` (`tendsto_integral_picketTransform_atTop`). Every atom is
  displaced by `η`; the mean spacing is preserved; the first moment per unit length is `η`, not `o(1)`.
- **Strongest positive survivor:** Boole's law in Lean, `∫_{(0,1)} φ(−cot(πu)) du = ∫ φ dCauchy(0,1)`
  for every `φ` (`integral_neg_cot_uniform_eq_cauchy`), and the weak limit `smoothedStat ε → Cauchy(0,1)`
  as `ε → 0⁺` (`tendsto_integral_smoothedStat`). For `ζ` itself the counterexample is excluded by
  Fujii's discrepancy bound (7.5) (`E|N(x) − x|² ≪ 1 + |x|^{4/3}` forbids clusters of size `k → ∞`
  at unit density); a converse `Cauchy(A_T) ⟹ H(T) = o(T)` therefore needs a cluster bound as an
  input and is a receiver in any case.
- **New insight (object-level):** one-point marginal laws of the critical-line log-derivative see
  horizontal displacement only through the singular/absolutely-continuous split of the Poisson-smoothed
  microscopic measure; clusters of growing mass move a.c. mass back into the Cauchy tail. Any
  marginal-law route to `(L)` must therefore carry a clustering bound and, even then, only reproduces
  Littlewood's first moment (M1).
- **Status:** Lean module `RHTower/PoissonSmoothedPicketFenceCauchyLaw.lean` (wired in `RHTower.lean`,
  `lake build` green, axioms `propext, Classical.choice, Quot.sound` only). Paper facts 1–2 on Desogus
  are not formalized (would need Paley–Wiener / iterated-convolution Laplace transforms; value low).

## Log
- 2026-09-18 — created from the weekly leads report; NN and Desogus read in full; M1–M4 attempted
  and failed on paper; picket-fence cotangent law, Boole's law and the Cauchy limit without collapse
  proved in Lean.
