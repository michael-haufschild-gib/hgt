# Producer Lindelöf: every Weil-positive system has a Lindelöf-quality zeta function

- **ID:** weil-producer-lindelof
- **Stage:** 3-formalized (paper and Lean 2026-10-01, MC loop cycle 204)
- **Type:** THEOREM (paper + Lean, standard axioms)
- **Source:** MC conjecture loop, cycle 204. Companion to `weil-cone-producer-short-interval-law.md` (HF L148), which transports "RH ⇒ PNT". This card transports "RH ⇒ Lindelöf" (Littlewood).
- **Statement.**
  - **Setting.** `lam` (with `lam(1) = 0`) is Weil-positive in Herglotz form for a datum `A` of logarithmic growth. This covers every full-cone producer for ζ's datum, by MUST-640. Its zeta function is `F = exp L`, where `L(s) = Σ lam(n)n^{−s}/log n`.
  - **Claim.** For every `0 < δ < ½` there are `C` and `θ < 1` such that at every height `|t| ≥ 6`, `L` continues holomorphically to `B(3+it, 5/2 − δ/4)` and satisfies `|L(σ+it)| ≤ C(log(|t|+3))^θ` for `½ + δ ≤ σ ≤ 5/2`.
  - **Consequence.** `|t|^{−ε} ≪ |F(σ+it)| ≪ |t|^ε` on `Re s ≥ ½ + δ`.
- **Lean.** Module `formal/GaloisForLFunctions/RHTower/WeilPositiveProducerLindelof.lean`, wired into `RHTower.lean`, axioms `[propext, Classical.choice, Quot.sound]`.
  - `exists_logZeta_lindelof`: the logarithmic form.
  - `exists_producerZeta_subpolynomial`: the `|t|^{±ε}` form.
  - `exists_producerZeta_subpolynomial_of_weilPositiveFull`: every full-cone producer.

## Proof
1. **Harnack strip bound** (corpus `norm_regularPart_le`): `|E(σ+it)| ≤ K' log(|t|+3)/(σ−½)`, with `E = A − Φ = D − 1/(s−1)`.
2. **Continuation.** On the disc, take a primitive of `−(E + 1/(s−1))` (mathlib `isExactOn_ball`). It agrees with `L` on `Re s > 1` by the identity theorem for primitives, since `L' = −D`.
3. **Two circle bounds.**
   - On the circle of radius ½ (`Re ≥ 5/2`), `L` is an absolutely convergent Dirichlet series, so `|L| ≤ Σ|lam|n^{−2}/log 2`.
   - On the circle of radius `5/2 − δ/2` (`Re ≥ ½ + δ/2`), the mean-value inequality with step 1 gives `|L| ≤ K₃ log(|t|+3)`.
4. **Three circles** (corpus `norm_le_of_three_circles_center`): `|L(σ+it)| ≤ M₁^{1−u}(K₃ log)^u` with `u ≤ θ < 1`. ∎

## Phase-4 verdict
- **BRIDGE**, new to the corpus.
  - The mechanism is Littlewood's 1912 "RH ⇒ Lindelöf", with Weil positivity in place of RH.
  - HF had only L224 Lemma B (`|F| ≪ t^{(2−σ)/2}`, crude) and L242 (mean square on the line within `e/2`); it had no pointwise Lindelöf bound for producers.
  - The free-weight cone is not studied in the literature (HF L148 audit).
- **Specialization.** For `lam = Λ`, which is a producer exactly under RH, this recovers Lindelöf for ζ and the `1/ζ` bound. The corpus already had these formal via `InvZetaRHSubpolynomial`.
- **What it gives.**
  - Every producer's zeta and its reciprocal are subpolynomial on `Re s > ½`. So the producer's own Möbius function `μ_lam` (coefficients of `1/F`) has smoothed partial sums `O(x^{½+ε})` once a Perron shift is attached. This is "Weil positivity ⇒ Möbius cancellation at the half power" for the system itself, i.e. route MC's target transported to the whole cone.
  - The Perron step is not yet formal: it needs a coefficient bound for `μ_lam`, or smoothed Perron with general coefficients.
- **Limit.** The constants degenerate as `δ → 0`. Lindelöf *on* the line needs, in addition, the Hermite–Biehler monotonicity of `|s(s−1)Γ_ℝ(s)F(s)|` (L242), which is not yet formal.

## Companion (cycle 206): the exact horizontal modulus law
- Module: `formal/GaloisForLFunctions/RHTower/WeilFullConeHorizontalPotential.lean`, wired, axioms `[propext, Classical.choice, Quot.sound]`.
- `integral_re_weilContinuation_eq`: for `½ < a ≤ b`,
  `∫_a^b Re Φ_lam(u+it) du = ½∫ log(((b−½)² + (r−t)²)/((a−½)² + (r−t)²)) dμ_lam(r)`.
  - Proof: Poisson representation on every line `Re s > ½`, Tonelli, and an arctan-free FTC for `½log((u−½)² + x²)`.
- `re_logZeta_sub_eq`: for every full-cone producer and every holomorphic logarithm `g` of its zeta function `F` along a horizontal segment,
  `log|F(σ'+it)| − log|F(σ+it)| = −∫_σ^{σ'} Re(A + 1/(s−1)) du + ½∫ log(((σ'−½)² + (r−t)²)/((σ−½)² + (r−t)²)) dμ_lam`.
- This is the exact, hypothesis-free form of HF L243's potential law and of the "Poisson damping factor" that L242 says controls Step A of the uniqueness programme. The only remaining question is analytic: how precisely this factor can be evaluated against `|F|²` at `σ − ½ ≍ 1/log T`.
