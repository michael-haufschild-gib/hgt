import GaloisForLFunctions.HTGeometry.PosteriorContrastProjection
import GaloisForLFunctions.HTGeometry.HellingerAffinityFactorization

/-!
# The likelihood polarization and its information hierarchy

The posterior contrast `d` of a binary experiment and its visibility `a = √(1 - d²)` carry the
squared Hellinger distance, the triangular discrimination, and the coherence energy of the two
reflection lifts.  The coherence energy is exactly twice the triangular discrimination and is
sandwiched between twice and four times the squared Hellinger distance.  A common Markov
recovery kernel changes none of them.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- `(LPC.3)`  The positive visibility `a = √(1 - d²)`. -/
def visibilityDensity (P Q : Measure X) (x : X) : ℝ :=
  Real.sqrt (1 - (posteriorContrast P Q x) ^ 2)

theorem measurable_visibilityDensity (P Q : Measure X) : Measurable (visibilityDensity P Q) :=
  (Real.continuous_sqrt.measurable).comp
    (measurable_const.sub ((measurable_posteriorContrast P Q).pow_const 2))

theorem visibilityDensity_nonneg (P Q : Measure X) (x : X) : 0 ≤ visibilityDensity P Q x :=
  Real.sqrt_nonneg _

theorem visibilityDensity_le_one (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∀ᵐ x ∂(balancedLaw P Q), visibilityDensity P Q x ≤ 1 := by
  filter_upwards [abs_posteriorContrast_le_one P Q] with x hx
  rw [visibilityDensity, Real.sqrt_le_one]
  nlinarith [sq_nonneg (posteriorContrast P Q x), abs_nonneg (posteriorContrast P Q x),
    sq_abs (posteriorContrast P Q x)]

theorem sq_visibilityDensity (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∀ᵐ x ∂(balancedLaw P Q),
      (visibilityDensity P Q x) ^ 2 = 1 - (posteriorContrast P Q x) ^ 2 := by
  filter_upwards [abs_posteriorContrast_le_one P Q] with x hx
  rw [visibilityDensity, Real.sq_sqrt]
  nlinarith [sq_abs (posteriorContrast P Q x), abs_nonneg (posteriorContrast P Q x)]

/-- `(LPC.20)`  Squared Hellinger distance of a binary experiment. -/
def hellingerSqMeasure (P Q : Measure X) : ℝ :=
  ∫ x, (Real.sqrt ((P.rnDeriv (balancedLaw P Q) x).toReal)
    - Real.sqrt ((Q.rnDeriv (balancedLaw P Q) x).toReal)) ^ 2 ∂(balancedLaw P Q)

/-- `(LPC.20)`  The squared Hellinger distance is twice the lost visibility. -/
theorem hellingerSqMeasure_eq (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    hellingerSqMeasure P Q = 2 * ∫ x, (1 - visibilityDensity P Q x) ∂(balancedLaw P Q) := by
  rw [hellingerSqMeasure, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [rnDeriv_right_toReal P Q, abs_posteriorContrast_le_one P Q] with x hq hd
  rw [rnDeriv_left_toReal, hq, visibilityDensity]
  have h1 : (0:ℝ) ≤ 1 + posteriorContrast P Q x := by
    rw [abs_le] at hd; linarith [hd.1]
  have h2 : (0:ℝ) ≤ 1 - posteriorContrast P Q x := by
    rw [abs_le] at hd; linarith [hd.2]
  have hprod : (1 + posteriorContrast P Q x) * (1 - posteriorContrast P Q x)
      = 1 - (posteriorContrast P Q x) ^ 2 := by ring
  have hsq : Real.sqrt (1 + posteriorContrast P Q x) * Real.sqrt (1 - posteriorContrast P Q x)
      = Real.sqrt (1 - (posteriorContrast P Q x) ^ 2) := by
    rw [← Real.sqrt_mul h1, hprod]
  have e1 : Real.sqrt (1 + posteriorContrast P Q x) ^ 2 = 1 + posteriorContrast P Q x :=
    Real.sq_sqrt h1
  have e2 : Real.sqrt (1 - posteriorContrast P Q x) ^ 2 = 1 - posteriorContrast P Q x :=
    Real.sq_sqrt h2
  nlinarith [hsq, e1, e2]

/-! ## The information hierarchy -/

theorem integrable_one_sub_visibility (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    Integrable (fun x => 1 - visibilityDensity P Q x) (balancedLaw P Q) := by
  refine Integrable.mono' (integrable_const 1)
    ((measurable_const.sub (measurable_visibilityDensity P Q)).aestronglyMeasurable) ?_
  filter_upwards [visibilityDensity_le_one P Q] with x hx
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [visibilityDensity_nonneg P Q x], by
    linarith [visibilityDensity_nonneg P Q x]⟩

theorem integrable_sq_posteriorContrast (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    Integrable (fun x => (posteriorContrast P Q x) ^ 2) (balancedLaw P Q) := by
  refine Integrable.mono' (integrable_const 1)
    (((measurable_posteriorContrast P Q).pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [abs_posteriorContrast_le_one P Q] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  nlinarith [abs_nonneg (posteriorContrast P Q x)]

/-- The coherence energy in visibility coordinates. -/
theorem coherenceWork_eq_visibility (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    coherenceWork P Q
      = 4 * ∫ x, (1 - visibilityDensity P Q x) * (1 + visibilityDensity P Q x)
          ∂(balancedLaw P Q) := by
  rw [coherenceWork]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [sq_visibilityDensity P Q] with x hx
  nlinarith [hx]

/-- **Theorem 4.1, `(LPC.24)`**, lower half. -/
theorem two_mul_hellingerSq_le_coherenceWork (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    2 * hellingerSqMeasure P Q ≤ coherenceWork P Q := by
  rw [hellingerSqMeasure_eq, coherenceWork_eq_visibility]
  have hmono : ∫ x, (1 - visibilityDensity P Q x) ∂(balancedLaw P Q)
      ≤ ∫ x, (1 - visibilityDensity P Q x) * (1 + visibilityDensity P Q x)
          ∂(balancedLaw P Q) := by
    refine integral_mono_ae (integrable_one_sub_visibility P Q) ?_ ?_
    · have h := coherenceWork_eq_visibility P Q
      exact (integrable_sq_posteriorContrast P Q).congr
        (by filter_upwards [sq_visibilityDensity P Q] with x hx; nlinarith [hx])
    · filter_upwards [visibilityDensity_le_one P Q] with x hx
      nlinarith [visibilityDensity_nonneg P Q x]
  linarith

/-- **Theorem 4.1, `(LPC.24)`**, upper half. -/
theorem coherenceWork_le_four_mul_hellingerSq (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    coherenceWork P Q ≤ 4 * hellingerSqMeasure P Q := by
  rw [hellingerSqMeasure_eq, coherenceWork_eq_visibility]
  have hmono : ∫ x, (1 - visibilityDensity P Q x) * (1 + visibilityDensity P Q x)
        ∂(balancedLaw P Q)
      ≤ ∫ x, 2 * (1 - visibilityDensity P Q x) ∂(balancedLaw P Q) := by
    refine integral_mono_ae ?_ ((integrable_one_sub_visibility P Q).const_mul 2) ?_
    · exact (integrable_sq_posteriorContrast P Q).congr
        (by filter_upwards [sq_visibilityDensity P Q] with x hx; nlinarith [hx])
    · filter_upwards [visibilityDensity_le_one P Q] with x hx
      nlinarith [visibilityDensity_nonneg P Q x]
  rw [integral_const_mul] at hmono
  linarith

/-! ## Common recovery is exactly neutral -/

/-- `(LPC.26)`  The balanced law of the split packet pair is the split balanced law. -/
theorem balancedLaw_compProd (P Q : Measure X) [SFinite P] [SFinite Q] (κ : Kernel X Y)
    [IsSFiniteKernel κ] : balancedLaw (P ⊗ₘ κ) (Q ⊗ₘ κ) = (balancedLaw P Q) ⊗ₘ κ := by
  rw [balancedLaw, balancedLaw, Measure.compProd_smul_left, Measure.compProd_add_left]

/-- `(LPC.27)`  The density of a split packet is the source density read on the retained
coordinate. -/
theorem rnDeriv_compProd_left (P ν : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure ν]
    (κ : Kernel X Y) [IsMarkovKernel κ] (hPν : P ≪ ν) :
    (P ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p => P.rnDeriv ν p.1 := by
  have hw : (ν ⊗ₘ κ).withDensity (fun p => P.rnDeriv ν p.1) = P ⊗ₘ κ := by
    rw [compProd_withDensity_fst _ _ (Measure.measurable_rnDeriv _ _),
      Measure.withDensity_rnDeriv_eq P ν hPν]
  calc (P ⊗ₘ κ).rnDeriv (ν ⊗ₘ κ)
      = ((ν ⊗ₘ κ).withDensity (fun p => P.rnDeriv ν p.1)).rnDeriv (ν ⊗ₘ κ) := by rw [hw]
    _ =ᵐ[ν ⊗ₘ κ] fun p => P.rnDeriv ν p.1 :=
        Measure.rnDeriv_withDensity _ (by fun_prop)

/-- `(LPC.27)`  Common recovery preserves the posterior contrast. -/
theorem posteriorContrast_compProd (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (κ : Kernel X Y) [IsMarkovKernel κ] :
    posteriorContrast (P ⊗ₘ κ) (Q ⊗ₘ κ)
      =ᵐ[balancedLaw (P ⊗ₘ κ) (Q ⊗ₘ κ)] fun p => posteriorContrast P Q p.1 := by
  rw [balancedLaw_compProd]
  filter_upwards [rnDeriv_compProd_left P (balancedLaw P Q) κ
    (absolutelyContinuous_balancedLaw_left P Q)] with p hp
  rw [posteriorContrast, posteriorContrast, ← balancedLaw_compProd P Q κ] at *
  rw [hp]

/-- `(LPC.28)`  Common recovery preserves the coherence energy. -/
theorem coherenceWork_compProd (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    coherenceWork (P ⊗ₘ κ) (Q ⊗ₘ κ) = coherenceWork P Q := by
  rw [coherenceWork, coherenceWork]
  congr 1
  rw [integral_congr_ae (g := fun p : X × Y => (posteriorContrast P Q p.1) ^ 2) ?_]
  · rw [balancedLaw_compProd, integral_fst_compProd κ (balancedLaw P Q)
      ((measurable_posteriorContrast P Q).pow_const 2)]
  · filter_upwards [posteriorContrast_compProd P Q κ] with p hp
    rw [hp]

/-- `(LPC.28)`  Common recovery preserves the triangular discrimination. -/
theorem triangularDiscrimination_compProd (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (κ : Kernel X Y) [IsMarkovKernel κ] :
    triangularDiscrimination (P ⊗ₘ κ) (Q ⊗ₘ κ) = triangularDiscrimination P Q := by
  have h := coherenceWork_compProd P Q κ
  rw [coherenceWork_eq_two_mul, coherenceWork_eq_two_mul] at h
  linarith

/-- `(LPC.28)`  Common recovery preserves the squared Hellinger distance. -/
theorem hellingerSqMeasure_compProd (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (κ : Kernel X Y) [IsMarkovKernel κ] :
    hellingerSqMeasure (P ⊗ₘ κ) (Q ⊗ₘ κ) = hellingerSqMeasure P Q := by
  rw [hellingerSqMeasure_eq, hellingerSqMeasure_eq]
  congr 1
  rw [integral_congr_ae (g := fun p : X × Y => 1 - visibilityDensity P Q p.1) ?_]
  · rw [balancedLaw_compProd, integral_fst_compProd κ (balancedLaw P Q)
      (F := fun x => 1 - visibilityDensity P Q x)
      (measurable_const.sub (measurable_visibilityDensity P Q))]
  · filter_upwards [posteriorContrast_compProd P Q κ] with p hp
    rw [visibilityDensity, visibilityDensity, hp]

/-- `(LPC.28)`  Common recovery preserves Jeffreys information. -/
theorem formationJeffreys_compProd (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    formationJeffreys (P ⊗ₘ κ) (Q ⊗ₘ κ) = formationJeffreys P Q := by
  rw [formationJeffreys, formationJeffreys, klDiv_compProd_left, klDiv_compProd_left]

end

end GaloisForLFunctions.HTGeometry
