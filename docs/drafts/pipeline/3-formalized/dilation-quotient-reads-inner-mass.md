# How boundary dilation quotients read inner mass

- **ID:** dilation-quotient-reads-inner-mass
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/README.md` Open Topic 1; `TheBoundaryQuotientForgetsTheInnerMass`.
- **Statement:**
  1. *Beurling–Sarason–Hardy phase transition of exterior curve factors.* Let `β ∈ ℂ` satisfy `‖β‖ > 1`
     with interior root `α = β⁻¹` (`0 < ‖α‖ < 1`), normalized Blaschke factor
     `b_α(v) = (v − α) / (1 − ᾱ v)`, unit model-space reproducing kernel
     `k_α(v) = √(1 − ‖α‖²) / (1 − ᾱ v)`, and boundary dilation quotient
     `q_ρ(v) = (1 − β v) / (1 − ρ β v)` on `‖v‖ = 1`:
     - For `0 ≤ ρ < ‖β‖⁻¹`, `q_ρ ∈ b_α H²(𝔻)` obeys the holomorphic Szegő–Beurling floor
       `Real.circleAverage (fun v => ‖q_ρ v‖²) 0 1 ≥ ‖β‖² = exp(2 posLog ‖β‖) > 1`.
     - For `‖β‖⁻¹ < ρ`, `q_ρ` splits pointwise and `L²(𝕋)`-orthogonally across
       `b_α H²(𝔻) ⊕ K_{b_α} ⊕ H²_-(𝔻)` into `beurlingPart β ρ`, `modelPart β ρ`, and `antiHoloPart β ρ`
       with circle-average squares `ρ⁻² ‖β‖⁻²`, `ρ⁻² (1 − ‖β‖⁻²)`, and `(1 − ρ⁻¹)² / (ρ² ‖β‖² − 1)`.
       As `ρ → 1⁻`, the total `L²(𝕋)` norm tends to `1`, while the Sarason model-space projection
       `Real.circleAverage (fun v => ‖modelPart β ρ v‖²) 0 1 → 1 − ‖β‖⁻² = 1 − exp(−2 posLog ‖β‖) > 0`
       (`φ⁻¹` on `goldenDatum`), recovering `posLog ‖β‖` from the boundary quotient.
  2. *Shifted inner field, single-shift RH equivalence, and first-order dilation jet of `ζ`.*
     For `0 ≤ δ ≤ 1/2` and `1/2 < Re w` with `zetaEntire(w + δ) ≠ 0`, the shifted inner field
     `I_δ(w) = ∫ log ‖ζ(1/2 + δ + iτ)‖ P_w(τ) dτ + log ‖w − δ‖ − log ‖zetaEntire(w + δ)‖`
     satisfies `I_δ(w) = ∑'_{ρ : ZetaRightZero} 1_{Re ρ > 1/2 + δ} m_ρ G(w, ρ − δ)`.
     At `w = 1`, for every fixed shift `δ ∈ (0, 1/2)`,
     `∫ (log ‖ζ(1/2 + iτ)‖ − log ‖ζ(1/2 + δ + iτ)‖) P₁(τ) dτ = (I(1) − I_δ(1)) + log((1 − δ) / (δ ‖ζ(1 + δ)‖))`
     with `I(1) − I_δ(1) ≥ 0` and equality if and only if `RiemannHypothesis`. Unconditionally as
     `δ → 0⁺`, dividing this integral by `δ` converges to
     `−(1 + γ) + ∑'_{ρ : ZetaRightZero} m_ρ Re(ρ⁻¹ + (1 − ρ)⁻¹)`, so `RiemannHypothesis` holds if and
     only if the first-order boundary dilation jet equals `−(1 + γ)`.
  3. *Unshadowed `L²` blowup.* If `ρ₀` is a zero of `ζ` with `1/2 < Re ρ₀ < 1` and
     `ζ(1/2 + i Im ρ₀) ≠ 0`, then at `δ = Re ρ₀ − 1/2` the `L²` boundary quotient integrand
     `τ ↦ (‖ζ(1/2 + iτ)‖ / ‖ζ(1/2 + δ + iτ)‖)² P₁(τ)` fails to be Lebesgue integrable on `ℝ`.

## Proof

1. *Beurling–Sarason–Hardy phase transition.* Let `‖β‖ > 1` and `α = β⁻¹`.
   For `0 ≤ ρ < ‖β‖⁻¹`, `Ψ_ρ(z) = −β(1 − ᾱ z)/(1 − ρβz)` is holomorphic on `closedBall 0 1` with
   `Ψ_ρ(0) = −β`. Applying `DiffContOnCl.circleAverage` to `conj(Ψ_ρ 0) (Ψ_ρ z − Ψ_ρ 0)` gives
   `avg ‖Ψ_ρ‖² ≥ ‖Ψ_ρ 0‖² = ‖β‖²`, while `‖b_α(v)‖ = 1` on `‖v‖ = 1` gives `‖q_ρ(v)‖² = ‖Ψ_ρ(v)‖²`.
   For `ρ > ‖β‖⁻¹`, `(ρβ)⁻¹ ∈ 𝔻`, and on `‖v‖ = 1` the rational identity
   `(1 − βv)/(1 − ρβv) = ρ⁻¹ + (1 − ρ⁻¹)/(1 − ρβv)` together with
   `1 = (1 − ‖α‖²)/(1 − ᾱ v) − ᾱ (v − α)/(1 − ᾱ v)` yields `q_ρ = beurlingPart + modelPart + antiHoloPart`.
   For `‖w‖ < 1`, applying `DiffContOnCl.circleAverage` to `(1 + w̄ z)/(1 − w̄ z)` evaluates the Poisson
   kernel circle average `(1 − ‖w‖²)/‖1 − w̄ v‖²` to `1` (`w = α` and `w = (ρβ)⁻¹`), giving the three
   exact `L²(𝕋)` norms. On `‖v‖ = 1`, `conj(k_α(v)) b_α(v) = √(1 − ‖α‖²) v / (1 − ᾱ v)` and
   `conj(1/(1 − ρβv)) f(v) = (−w̄ v / (1 − w̄ v)) f(v)` (`w = (ρβ)⁻¹`, `f` holomorphic on `closedBall 0 1`)
   extend holomorphically to `closedBall 0 1` and vanish at `0`, so their circle averages vanish by
   `DiffContOnCl.circleAverage`. Passing to `ρ → 1⁻` yields the boundary limits.

2. *Shifted inner field and dilation jet.* For `0 ≤ δ ≤ 1/2`, `E_δ(s) = zetaEntire(s + δ)` is a
   half-plane datum and `L_δ(s) = s − δ` has no zeros in `Re s > 1/2`. Subtracting the Poisson–Jensen
   identity for `L_δ` from that of `E_δ` and reindexing `RightZeros E_δ` via `s ↦ s + δ` onto
   `{ρ : ZetaRightZero | 1/2 + δ < Re ρ}` proves `HasSum (shiftedZeroTerm δ w) (shiftedInnerField δ w)`.
   At `w = 1` and `δ ∈ (0, 1/2)`, subtracting from `hasSum_innerField` leaves summands that are
   strictly positive at every `ρ : ZetaRightZero`: if `Re ρ ≤ 1/2 + δ` because `G(1, ρ) > 0`, and if
   `1/2 + δ < Re ρ < 1` because `(u₂² + y²)((u₁ − 1)² + y²) − (u₁² + y²)((u₂ − 1)² + y²) =
   δ(2y² + u₁(1 − u₂) + u₂(1 − u₁)) > 0` (`u₁ = Re ρ − δ`, `u₂ = Re ρ`).
   Dividing by `δ > 0`, the elementary bound `log R ≤ R − 1` dominates every divided difference by
   `2 m_ρ / ‖ρ − 1‖²` uniformly in `δ > 0`, which is summable by clearance of `ZetaRightZero` from `1`
   and `RiemannGaussian.summable_distinct_zetaZeroInverseSquareNorm`. Dominated convergence on
   `ZetaRightZero` evaluates the zero slope to `∑'_ρ m_ρ Re(ρ⁻¹ + (1 − ρ)⁻¹)`, while `hasDerivAt_zetaEntire_one`
   evaluates the archimedean slope `δ⁻¹ log((1 − δ)/(δ ‖ζ(1 + δ)‖))` to `−(1 + γ)`.

3. *Unshadowed `L²` blowup.* Near `ρ₀ = 1/2 + δ + i γ₀` (`ζ(ρ₀) = 0`, `ρ₀ ≠ 1`), differentiability of
   `ζ` bounds `‖ζ(1/2 + δ + iτ)‖ ≤ L (τ − γ₀)` on `(γ₀, γ₀ + r]`, while continuity at `1/2 + i γ₀`
   gives `‖ζ(1/2 + iτ)‖ ≥ c₀ > 0` and `P₁(τ) ≥ p₀ > 0`. The quotient integrand therefore exceeds
   `K (τ − γ₀)⁻²` (`K > 0`) on `(γ₀, γ₀ + r]`, whose integral on `[γ₀ + ε, γ₀ + r]` is `K(ε⁻¹ − r⁻¹)`,
   contradicting global integrability for small `ε > 0`.

## Lean verification

Module: `GaloisForLFunctions/ArithmeticInnerFunctionTheory/TheDilationQuotientReadsTheInnerMass.lean`.
Main declarations: `sq_norm_le_circleAverage_subcritical`, `supercritical_pythagorean_split`,
`tendsto_circleAverage_modelPart_sq`, `golden_exterior_modelPart_limit`, `hasSum_shiftedInnerField`,
`riemannHypothesis_iff_log_dilation_quotient_eq`, `summable_zeroMult_div_norm_sub_one_sq`,
`tendsto_firstOrder_dilation_jet`, `riemannHypothesis_iff_firstOrder_jet_eq`, and
`not_integrable_zeta_dilationQuotient_sq`.

Direct `lake --old env lean` check passed with default limits and no warnings.
All ten transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
Imported by the `ArithmeticInnerFunctionTheory` umbrella.
