import GaloisForLFunctions.HTGeometry.ShiftUniformPerturbedFreeness
import GaloisForLFunctions.HTGeometry.FamilyPowerGauge

/-!
# All-power independence of the perturbed outer orbit

A function is algebraic over any of its nonzero powers, so adjoining the roots cannot raise the
differential transcendence degree: powers of a differentially independent family stay independent.

Applied to the shift-uniform freeness of the translates, this gives the card's all-power statement --
for every exponent, every finite tuple of distinct real shifts, at one residual set of mass
parameters.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The perturbed outer family is smooth above the real axis. -/
theorem contDiffAt_perturbedOuterFamily {x ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Summable ε)
    (u : MassParameter) (c : ℂ) {A : ℂ → ℂ}
    (hA : ∀ ζ : ℂ, 0 < ζ.im → ContDiffAt ℂ (⊤ : ℕ∞) A ζ) {r : ℕ} (t : Fin r → ℝ) {z : ℂ}
    (hz : 0 < z.im) (i : Fin r) :
    ContDiffAt ℂ (⊤ : ℕ∞) (perturbedOuterFamily x ε u c A t i) z := by
  have hznode : 0 < (z + (t i : ℂ)).im := by simpa using hz
  have hS : ContDiffAt ℂ (⊤ : ℕ∞)
      (fun w => massOuterBackground x ε u (w + (t i : ℂ))) z :=
    contDiffAt_comp_add_const (contDiffAt_massOuterBackground hεpos hε u hznode)
  have hAt : ContDiffAt ℂ (⊤ : ℕ∞) (fun w => c * A (w + (t i : ℂ))) z :=
    contDiffAt_const.mul (contDiffAt_comp_add_const (hA _ hznode))
  exact hS.add hAt

/-- **All-power shift-uniform freeness.**  At a good mass parameter, every power of every finite
family of distinct real translates of the perturbed outer background is differentially algebraically
independent. -/
theorem not_familyDifferentiallyAlgebraicOn_pow_of_shiftUniformGood {x : ℕ → ℝ} {ε : ℕ → ℝ}
    (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) {c : ℂ} {A : ℂ → ℂ}
    (hA : AnalyticOnNhd ℂ A {ζ : ℂ | 0 < ζ.im}) {u : MassParameter}
    (hu : u ∈ shiftUniformGood x ε c A) {N : ℕ} (hN : N ≠ 0) {m' : ℕ} {t : Fin (m' + 1) → ℝ}
    (ht : Function.Injective t) :
    ¬ FamilyDifferentiallyAlgebraicOn
      (fun i w => perturbedOuterFamily x ε u c A t i w ^ N) {ζ : ℂ | 0 < ζ.im} := by
  have hAt : ∀ ζ : ℂ, 0 < ζ.im → ContDiffAt ℂ (⊤ : ℕ∞) A ζ := fun ζ hζ => (hA ζ hζ).contDiffAt
  refine not_familyDifferentiallyAlgebraicOn_pow _ hN (fun z hz i => ?_) ?_
  · exact contDiffAt_perturbedOuterFamily hεpos hε u c hAt t hz i
  · exact not_familyDifferentiallyAlgebraicOn_of_shiftUniformGood hεpos hε hA hu ht

/-- **Claim (1), all powers, shift-uniform.**  One residual set of bounded exponential mass
parameters makes every power of every finite family of distinct real translates of the
exponentially perturbed outer background differentially algebraically independent. -/
theorem residual_shiftUniform_perturbedOuterOrbit_pow {ι : Type*} {x : ℕ → ℝ}
    (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ)
    {a : ι → ℂ} {omega : ι → ℝ} (hcar : ExpSeriesNormallySummable a omega) :
    {u : MassParameter | ∀ (N : ℕ), N ≠ 0 → ∀ (m' : ℕ) (t : Fin (m' + 1) → ℝ),
        Function.Injective t → ¬ FamilyDifferentiallyAlgebraicOn
          (fun i w => perturbedOuterFamily x ε u c (cexpSeriesCarrier a omega) t i w ^ N)
          {ζ : ℂ | 0 < ζ.im}} ∈ residual MassParameter := by
  refine Filter.mem_of_superset
    (residual_shiftUniformGood hx hεpos hε c (analyticOnNhd_cexpSeriesCarrier hcar)) ?_
  intro u hu N hN m' t ht
  exact not_familyDifferentiallyAlgebraicOn_pow_of_shiftUniformGood hεpos hε
    (analyticOnNhd_cexpSeriesCarrier hcar) hu hN ht

/-- **The all-power good parameters are dense.** -/
theorem dense_shiftUniform_perturbedOuterOrbit_pow {ι : Type*} {x : ℕ → ℝ}
    (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ)
    {a : ι → ℂ} {omega : ι → ℝ} (hcar : ExpSeriesNormallySummable a omega) :
    Dense {u : MassParameter | ∀ (N : ℕ), N ≠ 0 → ∀ (m' : ℕ) (t : Fin (m' + 1) → ℝ),
        Function.Injective t → ¬ FamilyDifferentiallyAlgebraicOn
          (fun i w => perturbedOuterFamily x ε u c (cexpSeriesCarrier a omega) t i w ^ N)
          {ζ : ℂ | 0 < ζ.im}} :=
  dense_of_mem_residual (residual_shiftUniform_perturbedOuterOrbit_pow hx hεpos hε c hcar)

end

end GaloisForLFunctions.HTGeometry
