/-
Hilbert--Schmidt upgrade for the concrete Sonin time-band ideal.

The analytic input is the coordinate-free kernel theorem: an `L²` field of continuous
functionals induces a Hilbert--Schmidt operator.  Its proof uses finite basis sums only.  The
output energy is the integral of the coefficient energy, and pointwise Bessel bounds every
finite coefficient sum by the squared norm of the functional field.

The finite-rectangle Fourier blocks therefore satisfy the actual
`ContinuousLinearMap.IsHilbertSchmidt` interface.  The two-sided ideal induction then upgrades
the exact Sonin projection correction and the principal-subtracted dilation residual without
any Hilbert--Schmidt hypothesis.
-/
import GaloisForLFunctions.HilbertSchmidtOperator
import GaloisForLFunctions.RHTower.SoninPrimePowerRegularization
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RHTower

set_option maxHeartbeats 300000

section Kernel

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (μ : Measure α) [IsFiniteMeasure μ]

omit [CompleteSpace E] in
private theorem norm_kernelOperator_apply_sq
    (K : Lp (E →L[ℂ] ℂ) 2 μ) (e : E) :
    ‖kernelOperator (E := E) μ K e‖ ^ 2 = ∫ x, ‖K x e‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  rw [← integral_re (L2.integrable_inner
    (kernelOperator (E := E) μ K e) (kernelOperator (E := E) μ K e))]
  apply integral_congr_ae
  have hholder := (evalBilinear (E := E)).coeFn_holder
    (r := (2 : ENNReal)) K (Lp.const ∞ μ e)
  have hconst := Lp.coeFn_const (p := ∞) μ e
  filter_upwards [hholder, hconst] with x hholder hconst
  rw [kernelOperator, kernelOperatorMap_apply, hholder, hconst]
  simp [evalBilinear]
  norm_cast

omit [CompleteSpace E] [IsFiniteMeasure μ] in
private theorem norm_l2_sq
    (K : Lp (E →L[ℂ] ℂ) 2 μ) :
    ‖K‖ ^ 2 = ∫ x, ‖K x‖ ^ 2 ∂μ := by
  rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable K),
    lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable K)]
  norm_num [← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt]
  exact integral_nonneg fun x => sq_nonneg _

/-- **Hilbert--Schmidt kernel theorem.** An `L²` field of continuous functionals induces an
actual Hilbert--Schmidt operator into scalar `L²`. -/
theorem isHilbertSchmidt_kernelOperator
    (K : Lp (E →L[ℂ] ℂ) 2 μ) :
    ContinuousLinearMap.IsHilbertSchmidt (kernelOperator (E := E) μ K) := by
  let b := ContinuousLinearMap.hsBasis ℂ E
  show Summable (fun i => ‖kernelOperator (E := E) μ K (b i)‖ ^ 2)
  apply summable_of_sum_le (fun i => sq_nonneg _) (c := ‖K‖ ^ 2)
  intro u
  simp_rw [norm_kernelOperator_apply_sq (E := E) μ K]
  rw [← integral_finsetSum]
  rw [norm_l2_sq (E := E) μ K]
  · apply integral_mono_ae
    · exact integrable_finsetSum _ fun i _ =>
        (memLp_two_iff_integrable_sq_norm
          ((Lp.memLp K).continuousLinearMap_comp
            (ContinuousLinearMap.apply ℂ ℂ (b i))).1).mp
          ((Lp.memLp K).continuousLinearMap_comp
            (ContinuousLinearMap.apply ℂ ℂ (b i)))
    · exact (memLp_two_iff_integrable_sq_norm (Lp.memLp K).1).mp (Lp.memLp K)
    · exact Filter.Eventually.of_forall fun x => by
        let y : E := (InnerProductSpace.toDual ℂ E).symm (K x)
        calc
          ∑ i ∈ u, ‖K x (b i)‖ ^ 2 = ∑ i ∈ u, ‖inner ℂ y (b i)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [InnerProductSpace.toDual_symm_apply]
          _ = ∑ i ∈ u, ‖inner ℂ (b i) y‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [norm_inner_symm]
          _ ≤ ‖y‖ ^ 2 := b.orthonormal.sum_inner_products_le y
          _ = ‖K x‖ ^ 2 := by rw [(InnerProductSpace.toDual ℂ E).symm.norm_map]
  · intro i hi
    exact (memLp_two_iff_integrable_sq_norm
      ((Lp.memLp K).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℂ ℂ (b i))).1).mp
      ((Lp.memLp K).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℂ ℂ (b i)))

end Kernel

end RHTower

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Hilbert-space trace class in factorization form: a bounded operator is trace class when
it is a product of two Hilbert--Schmidt operators.  This is the standard factorization
characterization of the Schatten `S₁` ideal; no trace functional is inserted into the
definition. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ S U : H →L[ℂ] H, IsHilbertSchmidt S ∧ IsHilbertSchmidt U ∧ T = S ∘L U

/-- A product of two Hilbert--Schmidt operators is trace class by the factorization
characterization. -/
theorem IsHilbertSchmidt.comp_isTraceClass
    {S U : H →L[ℂ] H} (hS : IsHilbertSchmidt S) (hU : IsHilbertSchmidt U) :
    IsTraceClass (S ∘L U) :=
  ⟨S, U, hS, hU, rfl⟩

/-- The positive energy `T†T` of a Hilbert--Schmidt operator is trace class. -/
theorem IsHilbertSchmidt.adjoint_comp_self_isTraceClass
    {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsTraceClass (ContinuousLinearMap.adjoint T ∘L T) :=
  hT.adjoint.comp_isTraceClass hT

section Bounds

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Left composition multiplies the squared Hilbert--Schmidt norm by at most the squared
operator norm. -/
theorem hsNormSq_comp_left_le {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T)
    (A : F →L[ℂ] G) :
    hsNormSq (A ∘L T) ≤ ‖A‖ ^ 2 * hsNormSq T := by
  let b := hsBasis ℂ E
  have hAT := hT.comp_left A
  rw [hsNormSq_eq hAT b, hsNormSq_eq hT b, ← tsum_mul_left]
  exact (hAT.summable b).tsum_le_tsum (fun i => by
    calc
      ‖(A ∘L T) (b i)‖ ^ 2 = ‖A (T (b i))‖ ^ 2 := by rw [comp_apply]
      _ ≤ (‖A‖ * ‖T (b i)‖) ^ 2 := by gcongr; exact A.le_opNorm _
      _ = ‖A‖ ^ 2 * ‖T (b i)‖ ^ 2 := by ring)
    ((hT.summable b).mul_left (‖A‖ ^ 2))

/-- Right composition satisfies the corresponding squared Hilbert--Schmidt norm bound. -/
theorem hsNormSq_comp_right_le {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T)
    (B : G →L[ℂ] E) :
    hsNormSq (T ∘L B) ≤ ‖B‖ ^ 2 * hsNormSq T := by
  have hTB := hT.comp_right B
  rw [← hTB.hsNormSq_adjoint, adjoint_comp]
  have h := hsNormSq_comp_left_le hT.adjoint (ContinuousLinearMap.adjoint B)
  rw [hT.hsNormSq_adjoint] at h
  have hnorm : ‖ContinuousLinearMap.adjoint B‖ = ‖B‖ := by
    exact (ContinuousLinearMap.adjoint :
      (G →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] G)).norm_map B
  rw [hnorm] at h
  exact h

/-- A quadratic triangle bound for the Hilbert--Schmidt norm. -/
theorem hsNormSq_add_le {S T : E →L[ℂ] F}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    hsNormSq (S + T) ≤ 2 * hsNormSq S + 2 * hsNormSq T := by
  let b := hsBasis ℂ E
  have hST := hS.add hT
  rw [hsNormSq_eq hST b, hsNormSq_eq hS b, hsNormSq_eq hT b]
  calc
    ∑' i, ‖(S + T) (b i)‖ ^ 2 ≤
        ∑' i, (2 * ‖S (b i)‖ ^ 2 + 2 * ‖T (b i)‖ ^ 2) := by
      exact (hST.summable b).tsum_le_tsum (fun i => by
        have htri : ‖(S + T) (b i)‖ ≤ ‖S (b i)‖ + ‖T (b i)‖ := by
          simpa [add_apply] using norm_add_le (S (b i)) (T (b i))
        have hsq : ‖(S + T) (b i)‖ ^ 2 ≤
            (‖S (b i)‖ + ‖T (b i)‖) ^ 2 := by
          rw [sq, sq]
          exact mul_self_le_mul_self (norm_nonneg _) htri
        nlinarith [sq_nonneg (‖S (b i)‖ - ‖T (b i)‖)])
        (((hS.summable b).mul_left 2).add ((hT.summable b).mul_left 2))
    _ = 2 * ∑' i, ‖S (b i)‖ ^ 2 + 2 * ∑' i, ‖T (b i)‖ ^ 2 := by
      rw [Summable.tsum_add ((hS.summable b).mul_left 2) ((hT.summable b).mul_left 2),
        tsum_mul_left, tsum_mul_left]

theorem hsNormSq_neg_eq {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T) :
    hsNormSq (-T) = hsNormSq T := by
  let b := hsBasis ℂ E
  rw [hsNormSq_eq hT.neg b, hsNormSq_eq hT b]
  apply tsum_congr
  intro i
  simp

theorem hsNormSq_smul_eq {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T) (c : ℂ) :
    hsNormSq (c • T) = ‖c‖ ^ 2 * hsNormSq T := by
  let b := hsBasis ℂ E
  rw [hsNormSq_eq (hT.smul c) b, hsNormSq_eq hT b, ← tsum_mul_left]
  apply tsum_congr
  intro i
  simp only [smul_apply, norm_smul]
  ring

/-- A quadratic difference bound for the Hilbert--Schmidt norm. -/
theorem hsNormSq_sub_le {S T : E →L[ℂ] F}
    (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    hsNormSq (S - T) ≤ 2 * hsNormSq S + 2 * hsNormSq T := by
  rw [sub_eq_add_neg]
  have h := hsNormSq_add_le hS hT.neg
  rwa [hsNormSq_neg_eq hT] at h

end Bounds

end ContinuousLinearMap

namespace RHTower

/-- The full-input finite time-band operator into the restricted output `L²` space is
Hilbert--Schmidt. -/
theorem isHilbertSchmidt_fullToRestrictedTimeBandFourier
    (a b c d : ℝ) (hab : a ≤ b) :
    ContinuousLinearMap.IsHilbertSchmidt
      (fullToRestrictedTimeBandFourier a b c d hab) :=
  isHilbertSchmidt_kernelOperator ((volume : Measure ℝ).restrict (Set.Icc a b))
    (fullFourierFunctionalField a b c d hab)

/-- Extension by zero preserves the Hilbert--Schmidt finite time-band operator. -/
theorem isHilbertSchmidt_fullTimeBandFourier
    (a b c d : ℝ) (hab : a ≤ b) :
    ContinuousLinearMap.IsHilbertSchmidt (fullTimeBandFourier a b c d hab) := by
  exact (isHilbertSchmidt_fullToRestrictedTimeBandFourier a b c d hab).comp_left
    (lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
      (Set.Icc a b) measurableSet_Icc)

/-- The concrete cutoff--Fourier--cutoff operator on `L²(ℝ)` is Hilbert--Schmidt. -/
theorem isHilbertSchmidt_cutoffFourierCutoff
    (a b c d : ℝ) (hab : a ≤ b) :
    ContinuousLinearMap.IsHilbertSchmidt (cutoffFourierCutoff a b c d) := by
  rw [← fullTimeBandFourier_eq_cutoffFourierCutoff a b c d hab]
  exact isHilbertSchmidt_fullTimeBandFourier a b c d hab

/-- The Fourier-then-physical central cutoff block is Hilbert--Schmidt. -/
theorem isHilbertSchmidt_fourierCutoff_indicatorCutoff_central
    (s t : ℝ) (hs : 0 < s) :
    ContinuousLinearMap.IsHilbertSchmidt
      (fourierCutoff (centralInterval s) (measurableSet_centralInterval s) *
        indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)) := by
  let U : SoninL2 →L[Complex] SoninL2 :=
    fourierUnitary.symm.toLinearIsometry.toContinuousLinearMap
  let K : SoninL2 →L[Complex] SoninL2 := cutoffFourierCutoff (-s) s (-t) t
  have hK : ContinuousLinearMap.IsHilbertSchmidt K := by
    simpa [K] using isHilbertSchmidt_cutoffFourierCutoff (-s) s (-t) t (by linarith)
  have hEq :
      fourierCutoff (centralInterval s) (measurableSet_centralInterval s) *
          indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) =
        U * K := by
    apply ContinuousLinearMap.ext
    intro f
    rfl
  rw [hEq]
  exact hK.comp_left U

/-- The physical-then-Fourier central cutoff block is Hilbert--Schmidt. -/
theorem isHilbertSchmidt_indicatorCutoff_fourierCutoff_central
    (s t : ℝ) (hs : 0 < s) :
    ContinuousLinearMap.IsHilbertSchmidt
      (indicatorCutoff (centralInterval s) (measurableSet_centralInterval s) *
        fourierCutoff (centralInterval t) (measurableSet_centralInterval t)) := by
  let Aₛ : SoninL2 →L[Complex] SoninL2 :=
    indicatorCutoff (centralInterval s) (measurableSet_centralInterval s)
  let F : SoninL2 →L[Complex] SoninL2 :=
    fourierUnitary.toLinearIsometry.toContinuousLinearMap
  let J : SoninL2 →L[Complex] SoninL2 := l2Reflection
  let K : SoninL2 →L[Complex] SoninL2 := cutoffFourierCutoff (-s) s (-t) t
  have hK : ContinuousLinearMap.IsHilbertSchmidt K := by
    simpa [K] using isHilbertSchmidt_cutoffFourierCutoff (-s) s (-t) t (by linarith)
  have hEq :
      indicatorCutoff (centralInterval s) (measurableSet_centralInterval s) *
          fourierCutoff (centralInterval t) (measurableSet_centralInterval t) =
        J * K * F := by
    apply ContinuousLinearMap.ext
    intro f
    change Aₛ (fourierUnitary.symm
      (indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
        (fourierUnitary f))) = J (K (F f))
    rw [fourierUnitary_symm_eq_reflection_fourier]
    change indicatorCutoff (centralInterval s) (measurableSet_centralInterval s)
        (l2Reflection (fourierUnitary
          (indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)
            (fourierUnitary f)))) = J (K (F f))
    rw [← l2Reflection_indicatorCutoff_central]
    dsimp [J, K, F, cutoffFourierCutoff]
    rfl
  rw [hEq]
  exact (hK.comp_right F).comp_left J

namespace IsSoninTimeBandIdeal

/-- Every operator in the concrete Sonin time-band ideal is genuinely Hilbert--Schmidt. -/
theorem isHilbertSchmidt {T : SoninL2 →L[Complex] SoninL2}
    (hT : IsSoninTimeBandIdeal T) : ContinuousLinearMap.IsHilbertSchmidt T := by
  induction hT with
  | zero => exact ContinuousLinearMap.isHilbertSchmidt_zero
  | indicatorFourier s t hs ht =>
      exact isHilbertSchmidt_indicatorCutoff_fourierCutoff_central s t hs
  | fourierIndicator s t hs ht =>
      exact isHilbertSchmidt_fourierCutoff_indicatorCutoff_central s t hs
  | add hS hT ihS ihT => exact ihS.add ihT
  | neg hT ihT => exact ihT.neg
  | leftMul L hT ihT => exact ihT.comp_left L
  | rightMul hT R ihT => exact ihT.comp_right R

end IsSoninTimeBandIdeal

/-- The exact Sonin projection correction is Hilbert--Schmidt with no analytic premise. -/
theorem centralSoninProjectionCorrection_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt (centralSoninProjectionCorrection a) :=
  (centralSoninProjectionCorrection_mem_timeBandIdeal a ha).isHilbertSchmidt

/-- The exact principal-subtracted ambient Sonin dilation residual is Hilbert--Schmidt. -/
theorem centralSoninDilationCornerResidual_isHilbertSchmidt
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ContinuousLinearMap.IsHilbertSchmidt (centralSoninDilationCornerResidual a p hp) :=
  (centralSoninDilationCornerResidual_mem_timeBandIdeal a p ha hp).isHilbertSchmidt

theorem norm_one_sub_centralSoninProjection_le_one (a : ℝ) :
    ‖(1 : SoninL2 →L[ℂ] SoninL2) - centralSoninProjection a‖ ≤ 1 := by
  rw [centralSoninProjection]
  rw [← (centralSoninCarrier a).starProjection_orthogonal']
  exact Submodule.starProjection_norm_le _

theorem norm_centralSoninFormalComplement_le_three (a : ℝ) :
    ‖centralSoninFormalComplement a‖ ≤ 3 := by
  dsimp [centralSoninFormalComplement]
  calc
    ‖(1 : SoninL2 →L[ℂ] SoninL2) -
        indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) -
        fourierCutoff (centralInterval a) (measurableSet_centralInterval a)‖
        ≤ ‖(1 : SoninL2 →L[ℂ] SoninL2)‖ +
          ‖indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)‖ +
          ‖fourierCutoff (centralInterval a) (measurableSet_centralInterval a)‖ := by
            exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 1 + 1 + 1 := by
      gcongr
      · simp
      · rw [indicatorCutoff_eq_physicalForbidden_starProjection]
        exact Submodule.starProjection_norm_le _
      · rw [fourierCutoff_eq_fourierForbidden_starProjection]
        exact Submodule.starProjection_norm_le _
    _ = 3 := by norm_num

/-- **Uniform scale-independent residual bound.** The Hilbert--Schmidt energy of the exact
principal-subtracted Sonin dilation residual is controlled solely by the fixed projection
correction.  In particular, the bound does not grow with the dilation scale `p`. -/
theorem centralSoninDilationCornerResidual_hsNormSq_le
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ContinuousLinearMap.hsNormSq (centralSoninDilationCornerResidual a p hp) ≤
      80 * ContinuousLinearMap.hsNormSq (centralSoninProjectionCorrection a) := by
  open ContinuousLinearMap in
    let Q := centralSoninProjection a
    let Q₀ := centralSoninFormalComplement a
    let D := dilationSum p hp
    let C := centralSoninProjectionCorrection a
    let A : SoninL2 →L[ℂ] SoninL2 := (1 - Q) * D * C
    let B : SoninL2 →L[ℂ] SoninL2 := C * D * Q₀
    have hC : IsHilbertSchmidt C := by
      simpa [C] using centralSoninProjectionCorrection_isHilbertSchmidt a ha
    have hA : IsHilbertSchmidt A := by
      exact hC.comp_left ((1 - Q) * D)
    have hB : IsHilbertSchmidt B := by
      exact hC.comp_right (D * Q₀)
    have hEq : centralSoninDilationCornerResidual a p hp = A - B := by
      have hCeq : C = Q - Q₀ := by
        rfl
      have hgeneral : crossBoundary Q D - crossBoundary Q₀ D =
          (1 - Q) * D * (Q - Q₀) - (Q - Q₀) * D * Q₀ := by
        simp only [crossBoundary]
        noncomm_ring
      change centralSoninDilationCornerResidual a p hp =
        (1 - Q) * D * C - C * D * Q₀
      rw [hCeq]
      simpa [centralSoninDilationCornerResidual,
        centralSoninPrincipalDilationCorner, Q, Q₀, D] using hgeneral
    have hQ : ‖(1 : SoninL2 →L[ℂ] SoninL2) - Q‖ ≤ 1 := by
      simpa [Q] using norm_one_sub_centralSoninProjection_le_one a
    have hQ₀ : ‖Q₀‖ ≤ 3 := by
      simpa [Q₀] using norm_centralSoninFormalComplement_le_three a
    have hD : ‖D‖ ≤ 2 := by
      dsimp [D]
      apply (dilationSum p hp).opNorm_le_bound (by norm_num)
      intro f
      rw [dilationSum_apply]
      calc
        ‖dilation p (zero_lt_one.trans hp) f +
            dilation p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) f‖
            ≤ ‖dilation p (zero_lt_one.trans hp) f‖ +
              ‖dilation p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) f‖ := norm_add_le _ _
        _ = 2 * ‖f‖ := by
          rw [(dilation p (zero_lt_one.trans hp)).norm_map,
            (dilation p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp))).norm_map]
          ring
    have hLD : ‖(1 - Q) * D‖ ≤ 2 := by
      calc
        ‖(1 - Q) * D‖ ≤ ‖1 - Q‖ * ‖D‖ := norm_mul_le _ _
        _ ≤ 1 * 2 := mul_le_mul hQ hD (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have hDQ₀ : ‖D * Q₀‖ ≤ 6 := by
      calc
        ‖D * Q₀‖ ≤ ‖D‖ * ‖Q₀‖ := norm_mul_le _ _
        _ ≤ 2 * 3 := mul_le_mul hD hQ₀ (norm_nonneg _) (by norm_num)
        _ = 6 := by norm_num
    have hAbound : hsNormSq A ≤ 4 * hsNormSq C := by
      calc
        hsNormSq A ≤ ‖(1 - Q) * D‖ ^ 2 * hsNormSq C :=
          hsNormSq_comp_left_le hC ((1 - Q) * D)
        _ ≤ 4 * hsNormSq C := by
          apply mul_le_mul_of_nonneg_right _ (hsNormSq_nonneg C)
          nlinarith [norm_nonneg ((1 - Q) * D)]
    have hBbound : hsNormSq B ≤ 36 * hsNormSq C := by
      calc
        hsNormSq B ≤ ‖D * Q₀‖ ^ 2 * hsNormSq C :=
          hsNormSq_comp_right_le hC (D * Q₀)
        _ ≤ 36 * hsNormSq C := by
          apply mul_le_mul_of_nonneg_right _ (hsNormSq_nonneg C)
          nlinarith [norm_nonneg (D * Q₀)]
    rw [hEq]
    calc
      hsNormSq (A - B) ≤ 2 * hsNormSq A + 2 * hsNormSq B :=
        hsNormSq_sub_le hA hB
      _ ≤ 2 * (4 * hsNormSq C) + 2 * (36 * hsNormSq C) := by gcongr
      _ = 80 * hsNormSq C := by ring

/-- Every actual prime-power residual block is Hilbert--Schmidt. -/
theorem centralSoninPrimePowerResidual_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt (centralSoninPrimePowerResidual a pk) :=
  (centralSoninPrimePowerResidual_mem_timeBandIdeal a ha pk).isHilbertSchmidt

/-- Every logarithmically weighted actual prime-power residual block is Hilbert--Schmidt. -/
theorem centralSoninWeightedPrimePowerResidual_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt (centralSoninWeightedPrimePowerResidual a pk) :=
  (centralSoninWeightedPrimePowerResidual_mem_timeBandIdeal a ha pk).isHilbertSchmidt

/-- The weighted prime-power residual energy is bounded by the fixed correction energy times
the square of its logarithmic Euler coefficient. -/
theorem centralSoninWeightedPrimePowerResidual_hsNormSq_le
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ContinuousLinearMap.hsNormSq (centralSoninWeightedPrimePowerResidual a pk) ≤
      (80 * ContinuousLinearMap.hsNormSq (centralSoninProjectionCorrection a)) *
        ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := by
  open ContinuousLinearMap in
    have hR := centralSoninPrimePowerResidual_isHilbertSchmidt a ha pk
    rw [centralSoninWeightedPrimePowerResidual, hsNormSq_smul_eq hR]
    have hbound := centralSoninDilationCornerResidual_hsNormSq_le a
      (soninPrimePowerScale pk) ha (one_lt_soninPrimePowerScale pk)
    simp only [centralSoninPrimePowerResidual]
    nlinarith [sq_nonneg ‖soninLogPrimePowerCoefficient pk‖]

/-- **All-prime Hilbert--Schmidt energy summability.** The actual logarithmically weighted,
principal-subtracted Sonin residuals have summable Hilbert--Schmidt energies over every prime
power `p^(k+2)`.  This is the quantitative convergence input for the all-prime block assembly. -/
theorem summable_centralSoninWeightedPrimePowerResidual_hsNormSq
    (a : ℝ) (ha : 0 < a) :
    Summable (fun pk : Nat.Primes × ℕ =>
      ContinuousLinearMap.hsNormSq (centralSoninWeightedPrimePowerResidual a pk)) := by
  open ContinuousLinearMap in
    apply Summable.of_nonneg_of_le
      (fun pk => hsNormSq_nonneg (centralSoninWeightedPrimePowerResidual a pk))
      (centralSoninWeightedPrimePowerResidual_hsNormSq_le a ha)
    exact summable_norm_soninLogPrimePowerCoefficient_sq.mul_left
      (80 * hsNormSq (centralSoninProjectionCorrection a))

/-- Every finite regularized prime-power section is Hilbert--Schmidt, with no operator-ideal
hypothesis left to supply. -/
theorem finite_centralSoninWeightedPrimePowerResidual_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (s : Finset (Nat.Primes × ℕ)) :
    ContinuousLinearMap.IsHilbertSchmidt
      (∑ pk ∈ s, centralSoninWeightedPrimePowerResidual a pk) :=
  (finite_centralSoninWeightedPrimePowerResidual_mem_timeBandIdeal a ha s).isHilbertSchmidt

/-- The two factors in the constructive residual trace-ideal certificate are actual
Hilbert--Schmidt operators. -/
theorem IsSoninTimeBandTraceIdeal.exists_hilbertSchmidt_factors
    {T : SoninL2 →L[Complex] SoninL2} (hT : IsSoninTimeBandTraceIdeal T) :
    ∃ S U : SoninL2 →L[Complex] SoninL2,
      ContinuousLinearMap.IsHilbertSchmidt S ∧
      ContinuousLinearMap.IsHilbertSchmidt U ∧ T = S * U := by
  obtain ⟨S, U, hS, hU, rfl⟩ := hT
  exact ⟨S, U, hS.isHilbertSchmidt, hU.isHilbertSchmidt, rfl⟩

/-- A constructive Sonin trace-ideal certificate now yields the actual Hilbert-space trace-class
interface, because its two factors have been proved Hilbert--Schmidt. -/
theorem IsSoninTimeBandTraceIdeal.isTraceClass
    {T : SoninL2 →L[Complex] SoninL2} (hT : IsSoninTimeBandTraceIdeal T) :
    ContinuousLinearMap.IsTraceClass T := by
  obtain ⟨S, U, hS, hU, hEq⟩ := hT.exists_hilbertSchmidt_factors
  exact ⟨S, U, hS, hU, hEq⟩

/-- The positive energy of the principal-subtracted ambient Sonin dilation residual is
unconditionally trace class. -/
theorem centralSoninDilationCornerResidualEnergy_isTraceClass
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ContinuousLinearMap.IsTraceClass
      (centralSoninDilationCornerResidualEnergy a p hp) :=
  (centralSoninDilationCornerResidualEnergy_mem_traceIdeal a p ha hp).isTraceClass

end RHTower
