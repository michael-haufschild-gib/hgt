import GaloisForLFunctions.HTGeometry.NonstationaryPhaseSphere

/-!
# Aggregating a finite oscillatory family against a coefficient-mass bound

The transversality estimate splits a finite family of oscillatory integrals into three parts: the
terms whose phase vanishes identically, the part of the domain that is discarded, and the part on
which a nonstationary-phase bound is available.  The point of the coefficient-mass bound is that
the discarded part costs the **measure of the discarded region**, not that measure times the number
of terms: at every point the total absolute coefficient mass is at most one, so summing the
term-by-term bounds and then integrating gives one copy of the measure.

This module records that aggregation, with no reference to the sphere, the spectrum, or the
particular phases: a finite family, a unit total coefficient mass, a discarded set of finite
measure, and any individual bounds on the remaining region.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

/-- The oscillatory factor of a real phase. -/
def oscFactor (t : ℝ) (φ : X → ℝ) (x : X) : ℂ := Complex.exp (Complex.I * ((t * φ x : ℝ) : ℂ))

omit [MeasurableSpace X] in
@[simp] theorem norm_oscFactor (t : ℝ) (φ : X → ℝ) (x : X) : ‖oscFactor t φ x‖ = 1 := by
  rw [oscFactor, Complex.norm_exp]
  have hre : (Complex.I * ((t * φ x : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

omit [MeasurableSpace X] in
theorem norm_mul_oscFactor (a : ℂ) (t : ℝ) (φ : X → ℝ) (x : X) :
    ‖a * oscFactor t φ x‖ = ‖a‖ := by
  rw [norm_mul, norm_oscFactor, mul_one]

/-- **The discarded region costs one copy of its measure.**  A finite family whose total absolute
coefficient mass is at most one everywhere has the sum of the moduli of its integrals over a set
bounded by the measure of that set -- with no factor counting the terms. -/
theorem sum_norm_setIntegral_le_measure (a : ι → X → ℂ) {E : Set X}
    (hmeas : MeasurableSet E) (hint : ∀ j, IntegrableOn (a j) E μ)
    (hmass : ∀ x ∈ E, ∑ j, ‖a j x‖ ≤ 1) (hfin : μ E ≠ ⊤) :
    ∑ j, ‖∫ x in E, a j x ∂μ‖ ≤ μ.real E := by
  classical
  have hstep : ∀ j : ι, ‖∫ x in E, a j x ∂μ‖ ≤ ∫ x in E, ‖a j x‖ ∂μ := fun j =>
    norm_integral_le_integral_norm _
  have hsum : ∑ j, ‖∫ x in E, a j x ∂μ‖ ≤ ∑ j, ∫ x in E, ‖a j x‖ ∂μ :=
    Finset.sum_le_sum fun j _ => hstep j
  have hswap : ∑ j, ∫ x in E, ‖a j x‖ ∂μ = ∫ x in E, ∑ j, ‖a j x‖ ∂μ :=
    (integral_finsetSum _ fun j _ => (hint j).norm).symm
  have hintSum : IntegrableOn (fun x => ∑ j, ‖a j x‖) E μ :=
    integrable_finsetSum _ fun j _ => (hint j).norm
  have hone : IntegrableOn (fun _ : X => (1 : ℝ)) E μ := by
    haveI : IsFiniteMeasure (μ.restrict E) :=
      ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
    exact integrable_const 1
  have hmono : ∫ x in E, ∑ j, ‖a j x‖ ∂μ ≤ ∫ _x in E, (1 : ℝ) ∂μ :=
    setIntegral_mono_on hintSum hone hmeas hmass
  have hconst : ∫ _x in E, (1 : ℝ) ∂μ = μ.real E := by
    rw [setIntegral_const, smul_eq_mul, mul_one]
  calc ∑ j, ‖∫ x in E, a j x ∂μ‖ ≤ ∑ j, ∫ x in E, ‖a j x‖ ∂μ := hsum
    _ = ∫ x in E, ∑ j, ‖a j x‖ ∂μ := hswap
    _ ≤ ∫ _x in E, (1 : ℝ) ∂μ := hmono
    _ = μ.real E := hconst

/-- **The aggregated split.**  For a finite oscillatory family, the deviation of the total integral
from the integrals of the terms with vanishing phase is at most the sum of the moduli of the
remaining integrals. -/
theorem norm_integral_sub_diagonal_le [DecidableEq ι] (a : ι → X → ℂ) (φ : ι → X → ℝ) (t : ℝ)
    (D : Finset ι) (hzero : ∀ j ∈ D, ∀ x, φ j x = 0)
    (hint : ∀ j, Integrable (fun x => a j x * oscFactor t (φ j) x) μ) :
    ‖(∫ x, ∑ j, a j x * oscFactor t (φ j) x ∂μ) - ∑ j ∈ D, ∫ x, a j x ∂μ‖
      ≤ ∑ j ∈ Finset.univ \ D, ‖∫ x, a j x * oscFactor t (φ j) x ∂μ‖ := by
  classical
  have hsplit : (∫ x, ∑ j, a j x * oscFactor t (φ j) x ∂μ)
      = ∑ j, ∫ x, a j x * oscFactor t (φ j) x ∂μ :=
    integral_finsetSum _ fun j _ => hint j
  have hdiag : ∀ j ∈ D, (∫ x, a j x * oscFactor t (φ j) x ∂μ) = ∫ x, a j x ∂μ := by
    intro j hj
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [oscFactor, hzero j hj x]
    simp
  have hpart : ∑ j, ∫ x, a j x * oscFactor t (φ j) x ∂μ
      = (∑ j ∈ Finset.univ \ D, ∫ x, a j x * oscFactor t (φ j) x ∂μ)
        + ∑ j ∈ D, ∫ x, a j x * oscFactor t (φ j) x ∂μ :=
    (Finset.sum_sdiff (Finset.subset_univ D)).symm
  rw [hsplit, hpart, Finset.sum_congr rfl hdiag]
  have hcancel : (∑ j ∈ Finset.univ \ D, ∫ x, a j x * oscFactor t (φ j) x ∂μ)
        + (∑ j ∈ D, ∫ x, a j x ∂μ) - ∑ j ∈ D, ∫ x, a j x ∂μ
      = ∑ j ∈ Finset.univ \ D, ∫ x, a j x * oscFactor t (φ j) x ∂μ := by ring
  rw [hcancel]
  exact norm_sum_le _ _

/-- **`(17)` in aggregated form.**  Split a finite oscillatory family into the terms whose phase
vanishes identically, a discarded region of finite measure on which only the coefficient-mass
bound is used, and the rest, on which any individual bounds are available.  The deviation of the
total integral from the diagonal integrals is at most **one** copy of the measure of the discarded
region plus the sum of the individual bounds.  The number of terms never multiplies the discarded
measure. -/
theorem norm_integral_sub_diagonal_le_measureReal_add [DecidableEq ι]
    (a : ι → X → ℂ) (φ : ι → X → ℝ) (t : ℝ) (D : Finset ι) {E : Set X}
    (hmeas : MeasurableSet E)
    (hzero : ∀ j ∈ D, ∀ x, φ j x = 0)
    (hint : ∀ j, Integrable (fun x => a j x * oscFactor t (φ j) x) μ)
    (hmass : ∀ x ∈ E, ∑ j, ‖a j x‖ ≤ 1) (hfin : μ E ≠ ⊤)
    (b : ι → ℝ)
    (hgood : ∀ j, ‖∫ x in Eᶜ, a j x * oscFactor t (φ j) x ∂μ‖ ≤ b j) :
    ‖(∫ x, ∑ j, a j x * oscFactor t (φ j) x ∂μ) - ∑ j ∈ D, ∫ x, a j x ∂μ‖
      ≤ μ.real E + ∑ j ∈ Finset.univ \ D, b j := by
  classical
  have hsplitInt : ∀ j : ι, (∫ x, a j x * oscFactor t (φ j) x ∂μ)
      = (∫ x in E, a j x * oscFactor t (φ j) x ∂μ)
        + ∫ x in Eᶜ, a j x * oscFactor t (φ j) x ∂μ :=
    fun j => (integral_add_compl hmeas (hint j)).symm
  have hterm : ∀ j : ι, ‖∫ x, a j x * oscFactor t (φ j) x ∂μ‖
      ≤ ‖∫ x in E, a j x * oscFactor t (φ j) x ∂μ‖ + b j := by
    intro j
    rw [hsplitInt j]
    exact le_trans (norm_add_le _ _) (by linarith [hgood j])
  have hbad : ∑ j, ‖∫ x in E, a j x * oscFactor t (φ j) x ∂μ‖ ≤ μ.real E := by
    refine sum_norm_setIntegral_le_measure (fun j x => a j x * oscFactor t (φ j) x) hmeas
      (fun j => (hint j).integrableOn) (fun x hx => ?_) hfin
    calc ∑ j, ‖a j x * oscFactor t (φ j) x‖ = ∑ j, ‖a j x‖ :=
          Finset.sum_congr rfl fun j _ => norm_mul_oscFactor (a j x) t (φ j) x
      _ ≤ 1 := hmass x hx
  have hsub : ∑ j ∈ Finset.univ \ D, ‖∫ x in E, a j x * oscFactor t (φ j) x ∂μ‖
      ≤ ∑ j, ‖∫ x in E, a j x * oscFactor t (φ j) x ∂μ‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => norm_nonneg _
  calc ‖(∫ x, ∑ j, a j x * oscFactor t (φ j) x ∂μ) - ∑ j ∈ D, ∫ x, a j x ∂μ‖
      ≤ ∑ j ∈ Finset.univ \ D, ‖∫ x, a j x * oscFactor t (φ j) x ∂μ‖ :=
        norm_integral_sub_diagonal_le a φ t D hzero hint
    _ ≤ ∑ j ∈ Finset.univ \ D,
          (‖∫ x in E, a j x * oscFactor t (φ j) x ∂μ‖ + b j) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (∑ j ∈ Finset.univ \ D, ‖∫ x in E, a j x * oscFactor t (φ j) x ∂μ‖)
          + ∑ j ∈ Finset.univ \ D, b j := Finset.sum_add_distrib
    _ ≤ μ.real E + ∑ j ∈ Finset.univ \ D, b j := by
        linarith [le_trans hsub hbad]


end

end GaloisForLFunctions.HTGeometry
