import GaloisForLFunctions.HTGeometry.KleinGordonMovingPotential

/-!
# A periodic potential is read off one period of experiments

The reconstruction of statement 384 probes at every instant. When the potential is periodic the
instants may be restricted to a single period, by the reduction of statement 379 — provided the
operator family inherits the periodicity, which it does: multiplication operators of potentials that
agree everywhere are equal.

The result is the sharpest form the inverse problem takes in the register the card was written for:

**a periodic moving real potential, Lipschitz in time, is determined almost everywhere at every
instant by one period of short-time clock observations at every cut-off.**
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section PeriodicPotential

variable {V₁ V₂ : ℝ → E → ℝ} {b L : ℝ}

/-- The operator family of a periodic potential is periodic. -/
theorem kgMulOp_periodic {V : ℝ → E → ℝ} (hV : ∀ r : ℝ, Measurable (V r)) (hb0 : 0 ≤ b)
    (hb : ∀ (r : ℝ) (a : E), |V r a| ≤ b) {P : ℝ} (hper : ∀ r : ℝ, V (r + P) = V r) (r : ℝ) :
    (fun ρ : ℝ => kgMulOp (hV ρ) hb0 (hb ρ)) (r + P)
      = (fun ρ : ℝ => kgMulOp (hV ρ) hb0 (hb ρ)) r := by
  have hVeq : V (r + P) = V r := hper r
  show kgMulOp (hV (r + P)) hb0 (hb (r + P)) = kgMulOp (hV r) hb0 (hb r)
  rw [kgMulOp, kgMulOp]
  refine lpBoundedMulCLM_congr (measurable_ofReal_potential (hV (r + P)))
    (measurable_ofReal_potential (hV r)) hb0 (norm_ofReal_potential_le (hb (r + P))) hb0
    (norm_ofReal_potential_le (hb r)) ?_
  refine Filter.Eventually.of_forall fun a => ?_
  rw [hVeq]

set_option maxHeartbeats 1000000 in
/-- **A periodic moving real potential is determined almost everywhere at every instant by one
period of short-time clock observations at every cut-off.** -/
theorem potentialT_ae_eq_of_exact_observation_period
    (hV₁ : ∀ r : ℝ, Measurable (V₁ r)) (hV₂ : ∀ r : ℝ, Measurable (V₂ r)) (hb0 : 0 ≤ b)
    (hb₁ : ∀ (r : ℝ) (a : E), |V₁ r a| ≤ b) (hb₂ : ∀ (r : ℝ) (a : E), |V₂ r a| ≤ b)
    (hs₁ : ∀ y : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgMulOp (hV₁ r) hb0 (hb₁ r) y)
    (hs₂ : ∀ y : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgMulOp (hV₂ r) hb0 (hb₂ r) y)
    (hL0 : 0 ≤ L)
    (hLip : ∀ (σ τ : ℝ) (a : E),
      |(V₁ σ a - V₂ σ a) - (V₁ τ a - V₂ τ a)| ≤ L * |σ - τ|)
    {P T : ℝ} (hP0 : 0 < P) (hT0 : 0 < T)
    (hper₁ : ∀ r : ℝ, V₁ (r + P) = V₁ r) (hper₂ : ∀ r : ℝ, V₂ (r + P) = V₂ r)
    (hobs : ∀ R : ℝ, ∀ s : ℝ, 0 ≤ s → s < P →
      ∀ (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
        kgFieldMildT (fun r : ℝ =>
            kgBandOpT (fun ρ : ℝ => kgMulOp (hV₁ ρ) hb0 (hb₁ ρ)) R (r + s)) g k t
          = kgFieldMildT (fun r : ℝ =>
              kgBandOpT (fun ρ : ℝ => kgMulOp (hV₂ ρ) hb0 (hb₂ ρ)) R (r + s)) g k t)
    (t : ℝ) : V₁ t =ᵐ[(volume : Measure E)] V₂ t := by
  have hWb₁ : ∀ r : ℝ, ‖kgMulOp (hV₁ r) hb0 (hb₁ r)‖ ≤ b := fun r =>
    norm_kgMulOp_le (hV₁ r) hb0 (hb₁ r)
  have hWb₂ : ∀ r : ℝ, ‖kgMulOp (hV₂ r) hb0 (hb₂ r)‖ ≤ b := fun r =>
    norm_kgMulOp_le (hV₂ r) hb0 (hb₂ r)
  have hLip' : ∀ σ τ : ℝ,
      ‖(kgMulOp (hV₁ σ) hb0 (hb₁ σ) - kgMulOp (hV₂ σ) hb0 (hb₂ σ))
          - (kgMulOp (hV₁ τ) hb0 (hb₁ τ) - kgMulOp (hV₂ τ) hb0 (hb₂ τ))‖ ≤ L * |σ - τ| := by
    intro σ τ
    have hD0 : (0 : ℝ) ≤ L * |σ - τ| := by positivity
    exact norm_kgMulOp_sub_sub_le (hV₁ σ) (hV₂ σ) (hV₁ τ) (hV₂ τ) hb0 (hb₁ σ) (hb₂ σ)
      (hb₁ τ) (hb₂ τ) hD0 (hLip σ τ)
  have hfun := eq_of_exact_observation_all_bands_period hb0 hWb₁ hs₁ hWb₂ hs₂ hL0 hLip'
    hP0 hT0 (kgMulOp_periodic hV₁ hb0 hb₁ hper₁) (kgMulOp_periodic hV₂ hb0 hb₂ hper₂) hobs
  exact kgMulOp_injective (hV₁ t) (hV₂ t) hb0 (hb₁ t) (hb₂ t) (congrFun hfun t)

end PeriodicPotential

end GaloisForLFunctions.HTGeometry
