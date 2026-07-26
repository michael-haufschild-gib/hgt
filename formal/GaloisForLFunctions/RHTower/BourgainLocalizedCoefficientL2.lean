/-
# Complex localized-coefficient `L²` estimate

The complex coefficient sum supported on Bourgain's local boxes is
pointwise dominated by the corresponding nonnegative box mass.  Combining
this with the local-mass theorem bounds its `L²` norm by sharp weighted
spacing energy.
-/
import GaloisForLFunctions.RHTower.BourgainLocalMassL2

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

def bourgainLocalCoefficientSum
    {ι : Type*} [Fintype ι]
    (Y L : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℂ) (z : BourgainPhaseSpace) : ℂ := by
  classical
  exact ∑ i : ι,
    if z ∈ bourgainLocalBox Y L (p i) then a i else 0

theorem measurable_bourgainLocalCoefficientSum
    {ι : Type*} [Fintype ι]
    (Y L : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℂ) :
    Measurable (bourgainLocalCoefficientSum Y L p a) := by
  classical
  unfold bourgainLocalCoefficientSum
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite
    (measurableSet_bourgainLocalBox Y L (p i))
    measurable_const measurable_const

theorem norm_bourgainLocalCoefficientSum_le_mass
    {ι : Type*} [Fintype ι]
    (Y L : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℂ) (z : BourgainPhaseSpace) :
    ‖bourgainLocalCoefficientSum Y L p a z‖ ≤
      bourgainLocalBoxMass Y L p (fun i => ‖a i‖) z := by
  classical
  unfold bourgainLocalCoefficientSum bourgainLocalBoxMass
  calc
    ‖∑ i : ι,
        if z ∈ bourgainLocalBox Y L (p i) then a i else 0‖ ≤
      ∑ i : ι,
        ‖if z ∈ bourgainLocalBox Y L (p i) then a i else 0‖ :=
      norm_sum_le _ _
    _ = ∑ i : ι,
        if z ∈ bourgainLocalBox Y L (p i) then ‖a i‖ else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp

theorem integrable_norm_bourgainLocalCoefficientSum_sq
    {ι : Type*} [Fintype ι]
    (Y L : BourgainPhaseSpace) (p : ι → BourgainPhaseSpace)
    (a : ι → ℂ) :
    Integrable (fun z =>
      ‖bourgainLocalCoefficientSum Y L p a z‖ ^ (2 : ℕ)) := by
  let m : BourgainPhaseSpace → ℝ :=
    bourgainLocalBoxMass Y L p (fun i => ‖a i‖)
  let f : BourgainPhaseSpace → ℝ :=
    fun z => ‖bourgainLocalCoefficientSum Y L p a z‖ ^ (2 : ℕ)
  have hf0 (z : BourgainPhaseSpace) : 0 ≤ f z := by
    unfold f
    positivity
  have hpoint (z : BourgainPhaseSpace) :
      f z ≤ m z ^ (2 : ℕ) := by
    unfold f
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_bourgainLocalCoefficientSum_le_mass Y L p a z) 2
  have hmsq :
      Integrable (fun z => m z ^ (2 : ℕ)) :=
    integrable_bourgainLocalBoxMass_sq
      Y L p (fun i => ‖a i‖)
  have hfmeas : AEStronglyMeasurable f := by
    unfold f
    exact Measurable.aestronglyMeasurable
      ((measurable_bourgainLocalCoefficientSum Y L p a).norm.pow_const 2)
  apply hmsq.mono' hfmeas
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
  exact hpoint z

/-- Complex localized-coefficient `L²` norm is bounded by the first
sharp weighted spacing energy. -/
theorem integral_norm_bourgainLocalCoefficientSum_sq_le
    {ι : Type*} [Fintype ι]
    {Y L : BourgainPhaseSpace} (p : ι → BourgainPhaseSpace)
    (a : ι → ℂ) (hY : ∀ j, 0 < Y j)
    (hL : ∀ j, 0 < L j) :
    (∫ z : BourgainPhaseSpace,
        ‖bourgainLocalCoefficientSum Y L p a z‖ ^ (2 : ℕ)) ≤
      (∏ k : Fin 4,
        (2 * bourgainLocalizationEpsilon (Y k) / L k)) *
        bourgainWeightedScaledNearEnergy Y p (fun i => ‖a i‖) := by
  let m : BourgainPhaseSpace → ℝ :=
    bourgainLocalBoxMass Y L p (fun i => ‖a i‖)
  let f : BourgainPhaseSpace → ℝ :=
    fun z => ‖bourgainLocalCoefficientSum Y L p a z‖ ^ (2 : ℕ)
  have hm0 (z : BourgainPhaseSpace) : 0 ≤ m z := by
    unfold m bourgainLocalBoxMass
    exact Finset.sum_nonneg fun i hi => by
      split_ifs <;> positivity
  have hf0 (z : BourgainPhaseSpace) : 0 ≤ f z := by
    unfold f
    positivity
  have hpoint (z : BourgainPhaseSpace) :
      f z ≤ m z ^ (2 : ℕ) := by
    unfold f
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_bourgainLocalCoefficientSum_le_mass Y L p a z) 2
  have hmsq :
      Integrable (fun z => m z ^ (2 : ℕ)) :=
    integrable_bourgainLocalBoxMass_sq
      Y L p (fun i => ‖a i‖)
  have hfint : Integrable f :=
    integrable_norm_bourgainLocalCoefficientSum_sq Y L p a
  calc
    (∫ z : BourgainPhaseSpace,
        ‖bourgainLocalCoefficientSum Y L p a z‖ ^ (2 : ℕ)) =
        ∫ z, f z := rfl
    _ ≤ ∫ z, m z ^ (2 : ℕ) :=
      integral_mono hfint hmsq hpoint
    _ ≤ _ :=
      integral_bourgainLocalBoxMass_sq_le
        p (fun i => ‖a i‖) hY hL (fun i => norm_nonneg _)

end

end RHTower
