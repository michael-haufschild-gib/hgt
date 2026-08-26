import GaloisForLFunctions.HTGeometry.InfiniteProductFiniteHead
import GaloisForLFunctions.HTGeometry.IntervalUnitProbability
import GaloisForLFunctions.HTGeometry.PiMeasureAbsoluteContinuity

/-!
# Bounded independent complex coefficient law

Two independent uniform real coordinates on `[1,2]`, transported through the standard measurable
equivalence `ℝ × ℝ ≃ ℂ`, give an absolutely continuous complex probability law.  A measurable
clamp is pointwise bounded on the whole ambient space and is almost surely the identity for this
law.  Hence every finite clamped head of the countable product retains the exact finite product
law and its Lebesgue absolute continuity.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Uniform square law on `ℂ`, obtained from two independent uniform `[1,2]` coordinates. -/
def complexSquareProbability : Measure ℂ :=
  Measure.map Complex.measurableEquivRealProd.symm
    (intervalUnitProbability.prod intervalUnitProbability)

noncomputable instance complexSquareProbability_isProbabilityMeasure :
    IsProbabilityMeasure complexSquareProbability := by
  refine ⟨?_⟩
  rw [complexSquareProbability,
    Measure.map_apply_of_aemeasurable
      Complex.measurableEquivRealProd.symm.measurable.aemeasurable MeasurableSet.univ]
  simp

/-- The uniform complex square law is absolutely continuous with respect to planar Lebesgue
measure. -/
theorem complexSquareProbability_absolutelyContinuous :
    complexSquareProbability ≪ (volume : Measure ℂ) := by
  have hinterval : intervalUnitProbability ≪ (volume : Measure ℝ) :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hprod0 : intervalUnitProbability.prod intervalUnitProbability ≪
      (volume : Measure ℝ).prod (volume : Measure ℝ) := hinterval.prod hinterval
  have hvol : (volume : Measure ℝ).prod (volume : Measure ℝ) =
      (volume : Measure (ℝ × ℝ)) := rfl
  have hprod : intervalUnitProbability.prod intervalUnitProbability ≪
      (volume : Measure (ℝ × ℝ)) := by simpa only [hvol] using hprod0
  have hmap := hprod.map Complex.measurableEquivRealProd.symm.measurable
  rw [(Complex.volume_preserving_equiv_real_prod.symm
    Complex.measurableEquivRealProd).map_eq] at hmap
  exact hmap

/-- Clamp a real coordinate into `[1,2]`. -/
def clampIntervalUnit (x : ℝ) : ℝ := max 1 (min 2 x)

theorem clampIntervalUnit_mem_Icc (x : ℝ) :
    clampIntervalUnit x ∈ Set.Icc (1 : ℝ) 2 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clampIntervalUnit_eq_self {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    clampIntervalUnit x = x := by
  rw [clampIntervalUnit, min_eq_right hx.2, max_eq_right hx.1]

theorem measurable_clampIntervalUnit : Measurable clampIntervalUnit := by
  exact measurable_const.max (measurable_const.min measurable_id)

/-- Coordinatewise square clamp, transported to `ℂ`. -/
def clampComplexSquare (z : ℂ) : ℂ :=
  Complex.measurableEquivRealProd.symm
    (clampIntervalUnit z.re, clampIntervalUnit z.im)

theorem measurable_clampComplexSquare : Measurable clampComplexSquare := by
  exact Complex.measurableEquivRealProd.symm.measurable.comp
    ((measurable_clampIntervalUnit.comp Complex.measurable_re).prod
      (measurable_clampIntervalUnit.comp Complex.measurable_im))

/-- The totalized coefficient clamp is uniformly bounded on all inputs. -/
theorem norm_clampComplexSquare_le_four (z : ℂ) : ‖clampComplexSquare z‖ ≤ 4 := by
  apply le_trans (Complex.norm_le_abs_re_add_abs_im _)
  have hre := clampIntervalUnit_mem_Icc z.re
  have him := clampIntervalUnit_mem_Icc z.im
  change |clampIntervalUnit z.re| + |clampIntervalUnit z.im| ≤ 4
  rw [abs_of_nonneg (le_trans (by norm_num) hre.1),
    abs_of_nonneg (le_trans (by norm_num) him.1)]
  exact (add_le_add hre.2 him.2).trans_eq (by norm_num)

/-- The clamp is almost surely the identity for the square law. -/
theorem ae_complexSquareProbability_clamp_eq_self :
    ∀ᵐ z ∂complexSquareProbability, clampComplexSquare z = z := by
  rw [complexSquareProbability]
  change ∀ᵐ z ∂Measure.map Complex.measurableEquivRealProd.symm
    (intervalUnitProbability.prod intervalUnitProbability), clampComplexSquare z = id z
  rw [ae_map_iff Complex.measurableEquivRealProd.symm.measurable.aemeasurable
    (measurableSet_eq_fun measurable_clampComplexSquare measurable_id)]
  change ∀ᵐ p ∂intervalUnitProbability.prod intervalUnitProbability,
    (clampComplexSquare ∘ Complex.measurableEquivRealProd.symm) p =
      Complex.measurableEquivRealProd.symm p
  rw [Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun
      (measurable_clampComplexSquare.comp
        Complex.measurableEquivRealProd.symm.measurable)
      Complex.measurableEquivRealProd.symm.measurable)]
  filter_upwards [show ∀ᵐ x ∂intervalUnitProbability, x ∈ Set.Icc (1 : ℝ) 2 by
    exact ae_restrict_mem measurableSet_Icc] with x hx
  filter_upwards [show ∀ᵐ y ∂intervalUnitProbability, y ∈ Set.Icc (1 : ℝ) 2 by
    exact ae_restrict_mem measurableSet_Icc] with y hy
  change clampComplexSquare (Complex.measurableEquivRealProd.symm (x, y)) =
    Complex.measurableEquivRealProd.symm (x, y)
  rw [clampComplexSquare]
  simp only [Complex.measurableEquivRealProd_symm_apply]
  rw [clampIntervalUnit_eq_self hx, clampIntervalUnit_eq_self hy]

theorem map_clampComplexSquare_complexSquareProbability :
    Measure.map clampComplexSquare complexSquareProbability = complexSquareProbability := by
  rw [Measure.map_congr ae_complexSquareProbability_clamp_eq_self]
  exact Measure.map_id

/-- Every finite independent complex-square packet has a Lebesgue absolutely continuous law. -/
theorem pi_complexSquareProbability_absolutelyContinuous (M : ℕ) :
    Measure.pi (fun _ : Fin M => complexSquareProbability) ≪
      (volume : Measure (Fin M → ℂ)) := by
  rw [volume_pi]
  exact pi_absolutelyContinuous_pi M _ _
    (fun _ => complexSquareProbability_absolutelyContinuous)

/-- The clamped first `M` coordinates of a countable coefficient sequence. -/
def clampedComplexCoefficientHead (M : ℕ) (x : ℕ → ℂ) : Fin M → ℂ :=
  fun i => clampComplexSquare (x i)

theorem measurable_clampedComplexCoefficientHead (M : ℕ) :
    Measurable (clampedComplexCoefficientHead M) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_clampComplexSquare.comp
    (measurable_pi_apply (X := fun _ : ℕ => ℂ) (i : ℕ))

/-- Clamping preserves the exact finite-head product law. -/
theorem map_clampedComplexCoefficientHead_infinitePi (M : ℕ) :
    Measure.map (clampedComplexCoefficientHead M)
        (Measure.infinitePi (fun _ : ℕ => complexSquareProbability)) =
      Measure.pi (fun _ : Fin M => complexSquareProbability) := by
  let c : (Fin M → ℂ) → (Fin M → ℂ) := fun x i => clampComplexSquare (x i)
  have hc : Measurable c := by
    apply measurable_pi_lambda
    intro i
    exact measurable_clampComplexSquare.comp
      (measurable_pi_apply (X := fun _ : Fin M => ℂ) i)
  have hhead : Measurable (countableProductHead (α := ℂ) M) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply (X := fun _ : ℕ => ℂ) (i : ℕ)
  have hfun : clampedComplexCoefficientHead M = c ∘ countableProductHead M := by
    rfl
  rw [hfun, ← Measure.map_map hc hhead,
    map_countableProductHead_infinitePi complexSquareProbability M,
    Measure.pi_map_pi (fun _ : Fin M => measurable_clampComplexSquare.aemeasurable)]
  simp only [map_clampComplexSquare_complexSquareProbability]

/-- Consequently every finite clamped head is Lebesgue absolutely continuous. -/
theorem clampedComplexCoefficientHead_absolutelyContinuous (M : ℕ) :
    Measure.map (clampedComplexCoefficientHead M)
        (Measure.infinitePi (fun _ : ℕ => complexSquareProbability)) ≪
      (volume : Measure (Fin M → ℂ)) := by
  rw [map_clampedComplexCoefficientHead_infinitePi]
  exact pi_complexSquareProbability_absolutelyContinuous M

end

end GaloisForLFunctions.HTGeometry
