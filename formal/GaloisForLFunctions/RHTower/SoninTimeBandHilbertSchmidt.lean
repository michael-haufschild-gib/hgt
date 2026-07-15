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
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import GaloisForLFunctions.HTGeometry.TwoProjectionSupersymmetry
import GaloisForLFunctions.HTGeometry.TwoProjectionHilbertSchmidtEnergy
import GaloisForLFunctions.RHTower.SoninPrimePowerRegularization
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.SeparableMeasure

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

/-- **Exact Hilbert--Schmidt kernel energy.**  On a separable Hilbert input, Parseval and monotone
integration upgrade the kernel theorem from finiteness to the exact value
`\|kernelOperator K\|_HS² = \|K\|_L²²`.  This is the abstract localization-area identity used by
the finite Fourier rectangles below. -/
theorem hsNormSq_kernelOperator_eq_norm_sq [SeparableSpace E]
    (K : Lp (E →L[ℂ] ℂ) 2 μ) :
    ContinuousLinearMap.hsNormSq (kernelOperator (E := E) μ K) = ‖K‖ ^ 2 := by
  let b := ContinuousLinearMap.hsBasis ℂ E
  letI : Countable (exists_hilbertBasis ℂ E).choose :=
    b.orthonormal.countable_index
  have hT := isHilbertSchmidt_kernelOperator (E := E) μ K
  have hint (i) : Integrable (fun x => ‖K x (b i)‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm
      ((Lp.memLp K).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℂ ℂ (b i))).1).mp
      ((Lp.memLp K).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℂ ℂ (b i)))
  have hsum : Summable (fun i => ∫ x, ‖K x (b i)‖ ^ 2 ∂μ) := by
    refine (hT.summable b).congr (fun i => ?_)
    exact norm_kernelOperator_apply_sq (E := E) μ K (b i)
  have hsumNorm : Summable (fun i => ∫ x, ‖‖K x (b i)‖ ^ 2‖ ∂μ) := by
    refine hsum.congr (fun i => ?_)
    apply integral_congr_ae
    filter_upwards with x
    exact (Real.norm_of_nonneg (sq_nonneg ‖K x (b i)‖)).symm
  rw [ContinuousLinearMap.hsNormSq_eq hT b]
  calc
    ∑' i, ‖kernelOperator (E := E) μ K (b i)‖ ^ 2 =
        ∑' i, ∫ x, ‖K x (b i)‖ ^ 2 ∂μ := by
      apply tsum_congr
      intro i
      exact norm_kernelOperator_apply_sq (E := E) μ K (b i)
    _ = ∫ x, ∑' i, ‖K x (b i)‖ ^ 2 ∂μ :=
      integral_tsum_of_summable_integral_norm hint hsumNorm
    _ = ∫ x, ‖K x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      let y : E := (InnerProductSpace.toDual ℂ E).symm (K x)
      calc
        ∑' i, ‖K x (b i)‖ ^ 2 = ∑' i, ‖inner ℂ y (b i)‖ ^ 2 := by
          apply tsum_congr
          intro i
          rw [InnerProductSpace.toDual_symm_apply]
        _ = ∑' i, ‖inner ℂ (b i) y‖ ^ 2 := by
          apply tsum_congr
          intro i
          rw [norm_inner_symm]
        _ = ‖y‖ ^ 2 := b.tsum_norm_inner_sq y
        _ = ‖K x‖ ^ 2 := by
          rw [(InnerProductSpace.toDual ℂ E).symm.norm_map]
    _ = ‖K‖ ^ 2 := (HTGeometry.norm_l2_sq_eq_integral_norm_sq μ K).symm

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

/-- Left composition by a norm-preserving map preserves Hilbert--Schmidt energy exactly. -/
theorem hsNormSq_comp_left_eq_of_norm_map {T : E →L[ℂ] F} (hT : IsHilbertSchmidt T)
    (A : F →L[ℂ] G) (hA : ∀ x, ‖A x‖ = ‖x‖) :
    hsNormSq (A ∘L T) = hsNormSq T := by
  let b := hsBasis ℂ E
  rw [hsNormSq_eq (hT.comp_left A) b, hsNormSq_eq hT b]
  apply tsum_congr
  intro i
  rw [comp_apply, hA]

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

/-- A strictly contracting Hilbert--Schmidt operator has vanishing traces of its powers from
degree two onward.  The proof uses only the Hilbert--Schmidt ideal bound and the trace bound for a
product of two Hilbert--Schmidt operators. -/
theorem tendsto_opTrace_pow_add_two_zero_of_isHilbertSchmidt_norm_lt_one
    {T : E →L[ℂ] E} (hT : IsHilbertSchmidt T) (hcontract : ‖T‖ < 1) :
    Filter.Tendsto (fun n : ℕ => opTrace (T ^ (n + 2))) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun n : ℕ => T ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hcontract
  have hnormpow : Filter.Tendsto (fun n : ℕ => ‖T ^ n‖) Filter.atTop (nhds 0) := by
    simpa using hpow.norm
  have hmajor :
      Filter.Tendsto (fun n : ℕ => ‖T ^ n‖ ^ 2 * hsNormSq T) Filter.atTop (nhds 0) := by
    simpa using (hnormpow.pow 2).mul_const (hsNormSq T)
  have hsq :
      Filter.Tendsto (fun n : ℕ => hsNormSq (T ^ n * T)) Filter.atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => hsNormSq_nonneg (T ^ n * T)
    · exact Filter.Eventually.of_forall fun n => by
        simpa only [ContinuousLinearMap.mul_def] using hsNormSq_comp_left_le hT (T ^ n)
    · exact hmajor
  have hhsNorm :
      Filter.Tendsto (fun n : ℕ => hsNorm (T ^ n * T)) Filter.atTop (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_apply, hsNorm, Real.sqrt_zero] using hsqrt
  apply squeeze_zero_norm'
  · exact Filter.Eventually.of_forall fun n => by
      have hPow : IsHilbertSchmidt (T ^ n * T) := by
        simpa only [ContinuousLinearMap.mul_def] using hT.comp_left (T ^ n)
      have hEq : T ^ (n + 2) = (T ^ n * T) ∘L T := by
        change T ^ (n + 2) = (T ^ n * T) * T
        have hn1 : T ^ n * T = T ^ (n + 1) := by rw [← pow_succ]
        have hn2 : T ^ (n + 1) * T = T ^ (n + 2) := by
          simpa only [Nat.add_assoc] using (pow_succ T (n + 1)).symm
        noncomm_ring [hn1, hn2]
      rw [hEq]
      exact norm_opTrace_comp_le hPow hT
  · exact hhsNorm.mul_const (hsNorm T)

end Bounds

end ContinuousLinearMap

namespace RHTower

/-! ### Exact finite-rectangle localization energy -/

/-- The Riesz vector for the full-input Fourier functional.  It is the positive-phase plane wave
on the source interval and zero outside; conjugation in the complex inner product produces the
negative Fourier phase. -/
private theorem fullFourierRieszVector_memLp (x c d : ℝ) :
    MemLp ((Set.Icc c d).indicator fun y : ℝ =>
      Complex.exp ((2 * Real.pi * x * y : ℝ) * Complex.I)) 2
      (volume : Measure ℝ) := by
  apply (memLp_indicator_iff_restrict measurableSet_Icc).2
  refine MemLp.of_bound (p := (2 : ENNReal)) ?_ 1 ?_
  · exact (by fun_prop : Continuous fun y : ℝ =>
      Complex.exp ((2 * Real.pi * x * y : ℝ) * Complex.I)).aestronglyMeasurable
  · filter_upwards with y
    rw [Complex.norm_exp_ofReal_mul_I]

private def fullFourierRieszVector (x c d : ℝ) : RealL2 :=
  (fullFourierRieszVector_memLp x c d).toLp
    ((Set.Icc c d).indicator fun y : ℝ =>
      Complex.exp ((2 * Real.pi * x * y : ℝ) * Complex.I))

private theorem fullFourierRieszVector_coeFn (x c d : ℝ) :
    (fullFourierRieszVector x c d : ℝ → ℂ) =ᵐ[volume]
      (Set.Icc c d).indicator fun y : ℝ =>
        Complex.exp ((2 * Real.pi * x * y : ℝ) * Complex.I) :=
  MemLp.coeFn_toLp (fullFourierRieszVector_memLp x c d)

/-- A finite Fourier functional is exactly the Riesz functional of its zero-extended plane-wave
section. -/
theorem fullFourierFunctionalContinuous_eq_toDual
    (a b c d : ℝ) (x : Set.Icc a b) :
    fullFourierFunctionalContinuous a b c d x =
      InnerProductSpace.toDual ℂ RealL2 (fullFourierRieszVector (x : ℝ) c d) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [fullFourierFunctionalContinuous_apply,
    InnerProductSpace.toDual_apply_apply, L2.inner_def,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [fullFourierRieszVector_coeFn (x : ℝ) c d] with y hy
  rw [hy]
  by_cases hymem : y ∈ Set.Icc c d
  · simp only [Set.indicator_of_mem hymem]
    rw [RCLike.inner_apply, ← Complex.exp_conj]
    simp
    ring
  · simp [hymem, RCLike.inner_apply]

/-- The Riesz vector has squared norm equal to the source-interval length. -/
theorem norm_fullFourierRieszVector_sq (x c d : ℝ) (hcd : c ≤ d) :
    ‖fullFourierRieszVector x c d‖ ^ 2 = d - c := by
  rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  calc
    ∫ y, ‖fullFourierRieszVector x c d y‖ ^ 2 ∂volume =
        ∫ y in Set.Icc c d, (1 : ℝ) ∂volume := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [fullFourierRieszVector_coeFn x c d] with y hy
      rw [hy]
      by_cases hymem : y ∈ Set.Icc c d
      · simp [hymem, Complex.norm_exp_ofReal_mul_I]
      · simp [hymem]
    _ = d - c := by
      simp [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hcd)]

/-- Every Fourier functional in the output interval has the same squared norm: the length of the
source interval. -/
theorem norm_fullFourierFunctionalContinuous_sq
    (a b c d : ℝ) (x : Set.Icc a b) (hcd : c ≤ d) :
    ‖fullFourierFunctionalContinuous a b c d x‖ ^ 2 = d - c := by
  rw [fullFourierFunctionalContinuous_eq_toDual,
    (InnerProductSpace.toDual ℂ RealL2).norm_map,
    norm_fullFourierRieszVector_sq _ _ _ hcd]

/-- **Time--frequency area law for the functional field.**  Its `L²` energy is the product of
the output-interval and source-interval lengths. -/
theorem norm_fullFourierFunctionalField_sq
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    ‖fullFourierFunctionalField a b c d hab‖ ^ 2 = (b - a) * (d - c) := by
  rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  calc
    ∫ x, ‖fullFourierFunctionalField a b c d hab x‖ ^ 2
        ∂((volume : Measure ℝ).restrict (Set.Icc a b)) =
        ∫ _ : ℝ, (d - c)
          ∂((volume : Measure ℝ).restrict (Set.Icc a b)) := by
      apply integral_congr_ae
      filter_upwards [
        BoundedContinuousFunction.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
          (μ := (volume : Measure ℝ).restrict (Set.Icc a b))
          (fullFourierFunctionalBCF a b c d hab),
        ae_restrict_mem measurableSet_Icc
      ] with x hfield hx
      rw [fullFourierFunctionalField, hfield]
      change ‖fullFourierFunctionalContinuous a b c d (Set.projIcc a b hab x)‖ ^ 2 = _
      rw [Set.projIcc_of_mem hab hx,
        norm_fullFourierFunctionalContinuous_sq a b c d ⟨x, hx⟩ hcd]
    _ = (b - a) * (d - c) := by
      simp [integral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      ring

/-- The full-input finite time-band operator into the restricted output `L²` space is
Hilbert--Schmidt. -/
theorem isHilbertSchmidt_fullToRestrictedTimeBandFourier
    (a b c d : ℝ) (hab : a ≤ b) :
    ContinuousLinearMap.IsHilbertSchmidt
      (fullToRestrictedTimeBandFourier a b c d hab) :=
  isHilbertSchmidt_kernelOperator ((volume : Measure ℝ).restrict (Set.Icc a b))
    (fullFourierFunctionalField a b c d hab)

/-- **Shannon time--band area law.**  With the unitary Fourier convention
`exp (-2πixy)`, the squared Hilbert--Schmidt norm of a finite rectangle is exactly its
time--frequency area. -/
theorem hsNormSq_fullToRestrictedTimeBandFourier_eq_rectangleArea
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    ContinuousLinearMap.hsNormSq
        (fullToRestrictedTimeBandFourier a b c d hab) =
      (b - a) * (d - c) := by
  rw [fullToRestrictedTimeBandFourier,
    hsNormSq_kernelOperator_eq_norm_sq,
    norm_fullFourierFunctionalField_sq a b c d hab hcd]

/-- Extension by zero preserves the Hilbert--Schmidt finite time-band operator. -/
theorem isHilbertSchmidt_fullTimeBandFourier
    (a b c d : ℝ) (hab : a ≤ b) :
    ContinuousLinearMap.IsHilbertSchmidt (fullTimeBandFourier a b c d hab) := by
  exact (isHilbertSchmidt_fullToRestrictedTimeBandFourier a b c d hab).comp_left
    (lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
      (Set.Icc a b) measurableSet_Icc)

/-- Extension by zero preserves the exact rectangle energy. -/
theorem hsNormSq_fullTimeBandFourier_eq_rectangleArea
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    ContinuousLinearMap.hsNormSq (fullTimeBandFourier a b c d hab) =
      (b - a) * (d - c) := by
  let T := fullToRestrictedTimeBandFourier a b c d hab
  let A := lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
    (Set.Icc a b) measurableSet_Icc
  have hT : ContinuousLinearMap.IsHilbertSchmidt T := by
    simpa [T] using isHilbertSchmidt_fullToRestrictedTimeBandFourier a b c d hab
  calc
    ContinuousLinearMap.hsNormSq (fullTimeBandFourier a b c d hab) =
        ContinuousLinearMap.hsNormSq (A ∘L T) := by rfl
    _ = ContinuousLinearMap.hsNormSq T := by
      apply ContinuousLinearMap.hsNormSq_comp_left_eq_of_norm_map hT A
      intro f
      exact norm_lpExtendByZero (F := ℂ) (volume : Measure ℝ) 2
        (Set.Icc a b) measurableSet_Icc f
    _ = (b - a) * (d - c) := by
      simpa [T] using
        hsNormSq_fullToRestrictedTimeBandFourier_eq_rectangleArea a b c d hab hcd

/-- The concrete cutoff--Fourier--cutoff operator on `L²(ℝ)` is Hilbert--Schmidt. -/
theorem isHilbertSchmidt_cutoffFourierCutoff
    (a b c d : ℝ) (hab : a ≤ b) :
    ContinuousLinearMap.IsHilbertSchmidt (cutoffFourierCutoff a b c d) := by
  rw [← fullTimeBandFourier_eq_cutoffFourierCutoff a b c d hab]
  exact isHilbertSchmidt_fullTimeBandFourier a b c d hab

/-- Exact time--frequency area of the concrete cutoff--Fourier--cutoff operator. -/
theorem hsNormSq_cutoffFourierCutoff_eq_rectangleArea
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    ContinuousLinearMap.hsNormSq (cutoffFourierCutoff a b c d) =
      (b - a) * (d - c) := by
  rw [← fullTimeBandFourier_eq_cutoffFourierCutoff a b c d hab]
  exact hsNormSq_fullTimeBandFourier_eq_rectangleArea a b c d hab hcd

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

/-- The central Fourier-after-physical overlap has exact energy equal to the area of its
time--frequency rectangle. -/
theorem hsNormSq_fourierCutoff_indicatorCutoff_central
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ContinuousLinearMap.hsNormSq
        (fourierCutoff (centralInterval s) (measurableSet_centralInterval s) *
          indicatorCutoff (centralInterval t) (measurableSet_centralInterval t)) =
      4 * s * t := by
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
  calc
    ContinuousLinearMap.hsNormSq (U * K) = ContinuousLinearMap.hsNormSq K := by
      simpa only [ContinuousLinearMap.mul_def] using
        ContinuousLinearMap.hsNormSq_comp_left_eq_of_norm_map hK U
          (fun f => fourierUnitary.symm.norm_map f)
    _ = (s - (-s)) * (t - (-t)) := by
      simpa [K] using hsNormSq_cutoffFourierCutoff_eq_rectangleArea
        (-s) s (-t) t (by linarith) (by linarith)
    _ = 4 * s * t := by ring

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

/-- The correction response to every bounded observable is Hilbert--Schmidt.  This is the generic
operator-ideal consumer of the single projection correction. -/
theorem centralSoninCornerCorrectionResponse_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (D : SoninL2 →L[Complex] SoninL2) :
    ContinuousLinearMap.IsHilbertSchmidt
      (centralSoninCornerCorrectionResponse a D) :=
  (centralSoninCornerCorrectionResponse_mem_timeBandIdeal a ha D).isHilbertSchmidt

/-- The ordinary central Sonin time--band overlap has the exact Shannon area `4 a²`. -/
theorem hsNormSq_centralTimeBandOverlap_eq_four_mul_sq
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq
        ((centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) =
      4 * a ^ 2 := by
  calc
    ContinuousLinearMap.hsNormSq
        ((centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) =
        ContinuousLinearMap.hsNormSq
          (fourierCutoff (centralInterval a) (measurableSet_centralInterval a) *
            indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)) := by
      rw [fourierCutoff_eq_fourierForbidden_starProjection,
        indicatorCutoff_eq_physicalForbidden_starProjection]
    _ = 4 * a * a := hsNormSq_fourierCutoff_indicatorCutoff_central a a ha ha
    _ = 4 * a ^ 2 := by ring

/-- The physical/Fourier Jordan overlap is genuinely nonzero at every positive aperture.  For
sharp effects, vanishing of the anticommutator would force the time--band transition channel to
vanish, contradicting its exact positive Shannon area. -/
theorem centralSoninCutoffAnticommutator_ne_zero
    (a : ℝ) (ha : 0 < a) :
    (centralPhysicalForbidden a).starProjection *
          (centralFourierForbidden a).starProjection +
        (centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection ≠ 0 := by
  let P : SoninL2 →L[ℂ] SoninL2 :=
    (centralPhysicalForbidden a).starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 :=
    (centralFourierForbidden a).starProjection
  change P * Q + Q * P ≠ 0
  apply (HTGeometry.twoProjection_anticommutator_ne_zero_iff_mul_ne_zero
    P Q
    (centralPhysicalForbidden a).isIdempotentElem_starProjection
    (centralFourierForbidden a).isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
    (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq).2
  intro hQP
  have hHS : ContinuousLinearMap.IsHilbertSchmidt (Q * P) := by
    simpa [P, Q, centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
        isHilbertSchmidt_fourierCutoff_indicatorCutoff_central a a ha
  have hzero : ContinuousLinearMap.hsNormSq (Q * P) = 0 :=
    (ContinuousLinearMap.hsNormSq_eq_zero_iff hHS).2 hQP
  have harea := hsNormSq_centralTimeBandOverlap_eq_four_mul_sq a ha
  change ContinuousLinearMap.hsNormSq (Q * P) = 4 * a ^ 2 at harea
  nlinarith [sq_pos_of_pos ha]

/-- The correction response to the identity observable is nonzero at every positive aperture. -/
theorem centralSoninCornerCorrectionResponse_one_ne_zero
    (a : ℝ) (ha : 0 < a) :
    centralSoninCornerCorrectionResponse a 1 ≠ 0 := by
  rw [centralSoninCornerCorrectionResponse_one_eq_anticommutator]
  exact centralSoninCutoffAnticommutator_ne_zero a ha

/-- **Quadratic QSP response separation.**  The square of one prime signal differs from its
retained prime-square Chebyshev mode by exactly two identity channels.  Applying the Sonin
correction response therefore recovers twice the already nonzero anticommutator defect. -/
theorem centralSoninCornerCorrectionResponse_signalSq_sub_primeSquareResidual
    (a : ℝ) (p : Nat.Primes) :
    centralSoninCornerCorrectionResponse a
          (soninPrimeDilationSignal p * soninPrimeDilationSignal p) -
        centralSoninPrimePowerResidual a (p, 0) =
      2 * centralSoninCornerCorrectionResponse a 1 := by
  rw [centralSoninPrimePowerResidual_eq_cosineResponse]
  simp only [HTGeometry.unitaryCosineRecurrence]
  simp only [centralSoninCornerCorrectionResponse, crossBoundary]
  noncomm_ring

/-- At positive aperture the quadratic prime-signal response cannot equal the retained
prime-square residual.  This is an unconditional two-channel separation, not a claim that the
arithmetic residual alone is nonzero. -/
theorem centralSoninCornerCorrectionResponse_signalSq_ne_primeSquareResidual
    (a : ℝ) (ha : 0 < a) (p : Nat.Primes) :
    centralSoninCornerCorrectionResponse a
        (soninPrimeDilationSignal p * soninPrimeDilationSignal p) ≠
      centralSoninPrimePowerResidual a (p, 0) := by
  intro heq
  have hzero :
      2 * centralSoninCornerCorrectionResponse a 1 = 0 := by
    rw [← centralSoninCornerCorrectionResponse_signalSq_sub_primeSquareResidual a p,
      heq, sub_self]
  have hsmul :
      (2 : ℂ) • centralSoninCornerCorrectionResponse a 1 = 0 := by
    simpa [two_smul ℂ, two_mul] using hzero
  exact centralSoninCornerCorrectionResponse_one_ne_zero a ha
    ((smul_eq_zero.mp hsmul).resolve_left (by norm_num))

/-- Consequently at least one of the quadratic signal response and the retained prime-square
residual is nonzero for every prime and every positive aperture.  An augmented two-channel source
can therefore be normalized without a separate nondegeneracy hypothesis. -/
theorem centralSoninCornerCorrectionResponse_signalSq_ne_zero_or_primeSquareResidual_ne_zero
    (a : ℝ) (ha : 0 < a) (p : Nat.Primes) :
    centralSoninCornerCorrectionResponse a
          (soninPrimeDilationSignal p * soninPrimeDilationSignal p) ≠ 0 ∨
      centralSoninPrimePowerResidual a (p, 0) ≠ 0 := by
  by_contra hzero
  push_neg at hzero
  exact centralSoninCornerCorrectionResponse_signalSq_ne_primeSquareResidual a ha p
    (hzero.1.trans hzero.2.symm)

/-- Consequently the formal physical/Fourier complement is never an idempotent at positive
aperture.  Its nonzero identity response is the precise defect subtracted by the residual route. -/
theorem centralSoninFormalComplement_not_isIdempotentElem
    (a : ℝ) (ha : 0 < a) :
    ¬ IsIdempotentElem (centralSoninFormalComplement a) := by
  let P : SoninL2 →L[ℂ] SoninL2 :=
    (centralPhysicalForbidden a).starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 :=
    (centralFourierForbidden a).starProjection
  have htransition : Q * P ≠ 0 :=
    (HTGeometry.twoProjection_anticommutator_ne_zero_iff_mul_ne_zero
      P Q
      (centralPhysicalForbidden a).isIdempotentElem_starProjection
      (centralFourierForbidden a).isIdempotentElem_starProjection
      (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
      (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq).1
        (by simpa [P, Q] using centralSoninCutoffAnticommutator_ne_zero a ha)
  have hnot :=
    (HTGeometry.twoProjection_complement_not_isIdempotentElem_iff_mul_ne_zero
      P Q
      (centralPhysicalForbidden a).isIdempotentElem_starProjection
      (centralFourierForbidden a).isIdempotentElem_starProjection
      (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
      (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq).2 htransition
  simpa [centralSoninFormalComplement, P, Q,
    indicatorCutoff_eq_physicalForbidden_starProjection,
    fourierCutoff_eq_fourierForbidden_starProjection] using hnot

/-- The outside-time/outside-band overlap after subtracting the actual common-kernel projector.
Together with the ordinary time-band overlap, this is the second positive channel in the exact
Hilbert--Schmidt energy of the Sonin correction. -/
def centralSoninExteriorOverlap (a : ℝ) : SoninL2 →L[Complex] SoninL2 :=
  HTGeometry.twoProjectionExteriorOverlap
    (centralPhysicalForbidden a).starProjection
    (centralFourierForbidden a).starProjection
    (centralSoninProjection a)

/-- The common-kernel-subtracted positive compression in the exterior Fourier sector.  Its
interior supersymmetric partner is the existing prolate block
`soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a)`. -/
def centralSoninExteriorCompression (a : ℝ) : SoninL2 →L[Complex] SoninL2 :=
  HTGeometry.twoProjectionExteriorCompression
    (centralFourierForbidden a).starProjection
    (centralPhysicalForbidden a).starProjection
    (centralSoninProjection a)

/-- The exterior compression is the alternating block of the complementary forbidden sectors
with its full eigenvalue-one carrier projected away. -/
theorem centralSoninExteriorCompression_eq_complementaryAlternatingBlock_sub_carrier
    (a : ℝ) :
    centralSoninExteriorCompression a =
      soninAlternatingBlock (centralPhysicalForbidden a).orthogonal
          (centralFourierForbidden a).orthogonal -
        centralSoninProjection a := by
  rw [centralSoninExteriorCompression, HTGeometry.twoProjectionExteriorCompression,
    soninAlternatingBlock,
    (centralPhysicalForbidden a).starProjection_orthogonal',
    (centralFourierForbidden a).starProjection_orthogonal']

/-- The zero-mode-subtracted exterior time-band overlap is Hilbert--Schmidt. -/
theorem centralSoninExteriorOverlap_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt (centralSoninExteriorOverlap a) := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  have hC : ContinuousLinearMap.IsHilbertSchmidt (Q - (1 - P - R)) := by
    simpa only [P, R, Q, A, B, centralSoninProjectionCorrection,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      centralSoninProjectionCorrection_isHilbertSchmidt a ha
  have hRP : ContinuousLinearMap.IsHilbertSchmidt (R * P) := by
    simpa only [P, R, A, B, centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      isHilbertSchmidt_fourierCutoff_indicatorCutoff_central a a ha
  simpa only [centralSoninExteriorOverlap, P, R, Q, A, B] using
    HTGeometry.twoProjectionExteriorOverlap_isHilbertSchmidt P R Q hC hRP

/-- The exterior positive compression is Hilbert--Schmidt with no new analytic hypothesis. -/
theorem centralSoninExteriorCompression_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt (centralSoninExteriorCompression a) := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  have hP : IsIdempotentElem P := B.isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection B).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection A).star_eq
  have hSwap : Q - (1 - P - R) = Q - (1 - R - P) := by
    noncomm_ring
  have hC : ContinuousLinearMap.IsHilbertSchmidt (Q - (1 - P - R)) := by
    rw [hSwap]
    simpa only [P, R, Q, A, B, centralSoninProjectionCorrection,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      centralSoninProjectionCorrection_isHilbertSchmidt a ha
  have hRP : ContinuousLinearMap.IsHilbertSchmidt (R * P) := by
    simpa only [P, R, A, B, centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      isHilbertSchmidt_indicatorCutoff_fourierCutoff_central a a ha
  have hD := HTGeometry.twoProjectionExteriorOverlap_isHilbertSchmidt P R Q hC hRP
  simpa only [centralSoninExteriorCompression, P, R, Q, A, B] using
    HTGeometry.twoProjectionExteriorCompression_isHilbertSchmidt
      P R Q hP hPadj hRadj hRP hD

/-- The zero-mode-subtracted exterior compression is a strict contraction.  Compactness comes
from its Hilbert--Schmidt realization.  Positivity and contractivity come from compressing the
complementary alternating block away from its common carrier, and every eigenvalue-one vector of
that block lies in the carrier that was subtracted. -/
theorem norm_centralSoninExteriorCompression_lt_one
    (a : ℝ) (ha : 0 < a) :
    ‖centralSoninExteriorCompression a‖ < 1 := by
  let A : Submodule ℂ SoninL2 := centralPhysicalForbidden a
  let B : Submodule ℂ SoninL2 := centralFourierForbidden a
  let W : Submodule ℂ SoninL2 := A.orthogonal ⊓ B.orthogonal
  let T : SoninL2 →L[ℂ] SoninL2 := soninAlternatingBlock A.orthogonal B.orthogonal
  let Z : SoninL2 →L[ℂ] SoninL2 := W.starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 := W.orthogonal.starProjection
  let E : SoninL2 →L[ℂ] SoninL2 := centralSoninExteriorCompression a
  have hEeq : E = T - Z := by
    simpa only [E, T, Z, W, A, B, centralSoninProjection, centralSoninCarrier] using
      centralSoninExteriorCompression_eq_complementaryAlternatingBlock_sub_carrier a
  have hZZ : Z * Z = Z := by
    exact W.isIdempotentElem_starProjection
  have hZadj : ContinuousLinearMap.adjoint Z = Z :=
    (isSelfAdjoint_starProjection W).star_eq
  have hTadj : ContinuousLinearMap.adjoint T = T := by
    dsimp only [T, soninAlternatingBlock]
    change ContinuousLinearMap.adjoint
        ((B.orthogonal.starProjection ∘L A.orthogonal.starProjection) ∘L
          B.orthogonal.starProjection) = _
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection B.orthogonal).star_eq,
      (isSelfAdjoint_starProjection A.orthogonal).star_eq]
    simp only [mul_assoc]
  have hTZ : T * Z = Z := by
    apply ContinuousLinearMap.ext
    intro x
    have hxW := W.starProjection_apply_mem x
    change B.orthogonal.starProjection
        (A.orthogonal.starProjection (B.orthogonal.starProjection (W.starProjection x))) =
      W.starProjection x
    rw [B.orthogonal.starProjection_eq_self_iff.mpr hxW.2,
      A.orthogonal.starProjection_eq_self_iff.mpr hxW.1,
      B.orthogonal.starProjection_eq_self_iff.mpr hxW.2]
  have hZT : Z * T = Z := by
    calc
      Z * T = ContinuousLinearMap.adjoint (T * Z) := by
        change Z ∘L T = ContinuousLinearMap.adjoint (T ∘L Z)
        rw [ContinuousLinearMap.adjoint_comp, hZadj, hTadj]
      _ = ContinuousLinearMap.adjoint Z := by rw [hTZ]
      _ = Z := hZadj
  have hQeq : Q = 1 - Z := by
    simpa only [Q, Z] using W.starProjection_orthogonal'
  have hEcompression : E = Q * T * Q := by
    rw [hEeq, hQeq]
    noncomm_ring [hZZ, hTZ, hZT]
  have hle : ‖E‖ ≤ 1 := by
    rw [hEcompression]
    calc
      ‖Q * T * Q‖ ≤ ‖Q * T‖ * ‖Q‖ := norm_mul_le _ _
      _ ≤ (‖Q‖ * ‖T‖) * ‖Q‖ := by
        gcongr
        exact norm_mul_le Q T
      _ ≤ (1 * 1) * 1 := by
        gcongr
        · exact Submodule.starProjection_norm_le W.orthogonal
        · exact norm_soninAlternatingBlock_le_one A.orthogonal B.orthogonal
        · exact Submodule.starProjection_norm_le W.orthogonal
      _ = 1 := by norm_num
  have hsymm : (E : SoninL2 →ₗ[ℂ] SoninL2).IsSymmetric := by
    rw [hEcompression]
    intro x y
    change inner ℂ (Q (T (Q x))) y = inner ℂ x (Q (T (Q y)))
    dsimp only [Q]
    rw [W.orthogonal.inner_starProjection_left_eq_right,
      ← W.orthogonal.inner_starProjection_left_eq_right]
    exact soninAlternatingBlock_isSymmetric A.orthogonal B.orthogonal _ _
  have hnonneg : ∀ x, 0 ≤ Complex.re (inner ℂ x (E x)) := by
    intro x
    rw [hEcompression]
    change 0 ≤ Complex.re (inner ℂ x (Q (T (Q x))))
    dsimp only [Q]
    rw [← W.orthogonal.inner_starProjection_left_eq_right]
    exact soninAlternatingBlock_re_inner_nonneg A.orthogonal B.orthogonal _
  have hZE : Z * E = 0 := by
    rw [hEeq]
    noncomm_ring [hZZ, hZT]
  have hno : ¬ Module.End.HasEigenvalue (E : SoninL2 →ₗ[ℂ] SoninL2) 1 := by
    intro heig
    obtain ⟨x, hx, hxne⟩ := heig.exists_hasEigenvector
    simp only [Module.End.mem_genEigenspace_one, one_smul] at hx
    have hZx : Z x = 0 := by
      calc
        Z x = Z (E x) := congrArg Z hx.symm
        _ = (Z * E) x := rfl
        _ = 0 := by rw [hZE]; rfl
    have hTx : T x = x := by
      have hx' := hx
      rw [hEeq] at hx'
      change T x - Z x = x at hx'
      simpa only [hZx, sub_zero] using hx'
    have hxW : x ∈ W := by
      simpa only [W, T] using
        mem_inf_of_soninAlternatingBlock_apply_eq_self A.orthogonal B.orthogonal hTx
    have hZfix : Z x = x := by
      exact W.starProjection_eq_self_iff.mpr hxW
    exact hxne (hZfix.symm.trans hZx)
  change ‖E‖ < 1
  exact norm_lt_one_of_compact_of_symmetric_of_nonnegative_of_not_eigenvalue_one
    E hle (centralSoninExteriorCompression_isHilbertSchmidt a ha).isCompactOperator
    hsymm hnonneg hno

/-- The central alternating/prolate block is Hilbert--Schmidt. -/
theorem centralSoninAlternatingBlock_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt
      (soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a)) := by
  have hFX : ContinuousLinearMap.IsHilbertSchmidt
      ((centralFourierForbidden a).starProjection *
        (centralPhysicalForbidden a).starProjection) := by
    simpa only [centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      isHilbertSchmidt_fourierCutoff_indicatorCutoff_central a a ha
  simpa only [soninAlternatingBlock, mul_assoc] using
    hFX.comp_right (centralFourierForbidden a).starProjection

/-- **Sonin time-band correction energy split.**  The exact projection-correction energy is the
sum of the ordinary time-band overlap energy and the common-kernel-subtracted exterior overlap
energy.  Both terms are nonnegative Hilbert--Schmidt values; no trace of the correction itself is
taken. -/
theorem hsNormSq_centralSoninProjectionCorrection_eq_timeBand_add_exterior
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (centralSoninProjectionCorrection a) =
      ContinuousLinearMap.hsNormSq
          ((centralFourierForbidden a).starProjection *
            (centralPhysicalForbidden a).starProjection) +
        ContinuousLinearMap.hsNormSq (centralSoninExteriorOverlap a) := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  have hR : IsIdempotentElem R := B.isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection A).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection B).star_eq
  have hRQ : R * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change B.starProjection ((Aᵮ ⊓ Bᵮ).starProjection x) = 0
    apply B.starProjection_apply_eq_zero_iff.mpr
    exact ((Aᵮ ⊓ Bᵮ).starProjection_apply_mem x).2
  have hC : ContinuousLinearMap.IsHilbertSchmidt (Q - (1 - P - R)) := by
    simpa only [P, R, Q, A, B, centralSoninProjectionCorrection,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      centralSoninProjectionCorrection_isHilbertSchmidt a ha
  have hRP : ContinuousLinearMap.IsHilbertSchmidt (R * P) := by
    simpa only [P, R, A, B, centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      isHilbertSchmidt_fourierCutoff_indicatorCutoff_central a a ha
  have hsplit :=
    HTGeometry.hsNormSq_twoProjection_correctedComplement_eq_overlap_add_exterior
      P R Q hR hPadj hRadj hRQ hC hRP
  simpa only [P, R, Q, A, B, centralSoninProjectionCorrection,
    centralSoninExteriorOverlap,
    indicatorCutoff_eq_physicalForbidden_starProjection,
    fourierCutoff_eq_fourierForbidden_starProjection] using hsplit

/-- **Sonin supersymmetric partition.**  The correction energy is the sum of the existing
prolate-block energy, the exterior compressed energy, and twice the physical-to-Fourier
transition energy.  The last value is the free-fermion number variance already present in the
prolate commutator surface. -/
theorem hsNormSq_centralSoninProjectionCorrection_eq_compressions_add_two_mul_transition
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (centralSoninProjectionCorrection a) =
      ContinuousLinearMap.hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) +
        ContinuousLinearMap.hsNormSq (centralSoninExteriorCompression a) +
          2 * ContinuousLinearMap.hsNormSq
            (crossBoundary (centralFourierForbidden a).starProjection
              (centralPhysicalForbidden a).starProjection) := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  have hP : IsIdempotentElem P := B.isIdempotentElem_starProjection
  have hR : IsIdempotentElem R := A.isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection B).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection A).star_eq
  have hQadj : ContinuousLinearMap.adjoint Q = Q := by
    dsimp only [Q, centralSoninProjection, centralSoninCarrier]
    exact (isSelfAdjoint_starProjection (Aᵮ ⊓ Bᵮ)).star_eq
  have hPQ : P * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change B.starProjection ((Aᵮ ⊓ Bᵮ).starProjection x) = 0
    apply B.starProjection_apply_eq_zero_iff.mpr
    exact ((Aᵮ ⊓ Bᵮ).starProjection_apply_mem x).2
  have hZP : Q * P = 0 := by
    calc
      Q * P = ContinuousLinearMap.adjoint (P * Q) := by
        change Q ∘L P = ContinuousLinearMap.adjoint (P ∘L Q)
        rw [ContinuousLinearMap.adjoint_comp, hQadj, hPadj]
      _ = 0 := by rw [hPQ]; simp
  have hRZ : R * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change A.starProjection ((Aᵮ ⊓ Bᵮ).starProjection x) = 0
    apply A.starProjection_apply_eq_zero_iff.mpr
    exact ((Aᵮ ⊓ Bᵮ).starProjection_apply_mem x).1
  have hSwap : Q - (1 - P - R) = Q - (1 - R - P) := by
    noncomm_ring
  have hC : ContinuousLinearMap.IsHilbertSchmidt (Q - (1 - P - R)) := by
    rw [hSwap]
    simpa only [P, R, Q, A, B, centralSoninProjectionCorrection,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      centralSoninProjectionCorrection_isHilbertSchmidt a ha
  have hRP : ContinuousLinearMap.IsHilbertSchmidt (R * P) := by
    simpa only [P, R, A, B, centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      isHilbertSchmidt_indicatorCutoff_fourierCutoff_central a a ha
  have hpartition :=
    HTGeometry.hsNormSq_twoProjection_correctedComplement_eq_compressions_add_two_mul_transition
      P R Q hP hR hPadj hRadj hQadj hZP hRZ hC hRP
  rw [hSwap] at hpartition
  simpa only [P, R, Q, A, B, centralSoninProjectionCorrection,
    centralSoninExteriorCompression, soninAlternatingBlock, crossBoundary,
    HTGeometry.twoProjectionInteriorCompression,
    HTGeometry.twoProjectionExteriorCompression,
    HTGeometry.twoProjectionTransition,
    indicatorCutoff_eq_physicalForbidden_starProjection,
    fourierCutoff_eq_fourierForbidden_starProjection] using hpartition

/-- The ordinary time-band overlap splits exactly into the squared prolate block and the
free-fermion transition energy. -/
theorem hsNormSq_centralTimeBandOverlap_eq_prolateBlock_add_transition
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq
        ((centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) =
      ContinuousLinearMap.hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) +
        ContinuousLinearMap.hsNormSq
          (crossBoundary (centralFourierForbidden a).starProjection
            (centralPhysicalForbidden a).starProjection) := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  have hP : IsIdempotentElem P := B.isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection B).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection A).star_eq
  have hRP : ContinuousLinearMap.IsHilbertSchmidt (R * P) := by
    simpa only [P, R, A, B, centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      isHilbertSchmidt_indicatorCutoff_fourierCutoff_central a a ha
  have hAdj : ContinuousLinearMap.adjoint (R * P) = P * R := by
    change ContinuousLinearMap.adjoint (R ∘L P) = P ∘L R
    rw [ContinuousLinearMap.adjoint_comp, hPadj, hRadj]
  have hNorm : hsNormSq (P * R) = hsNormSq (R * P) := by
    rw [← hAdj]
    exact hRP.hsNormSq_adjoint
  have hsplit :=
    HTGeometry.hsNormSq_twoProjection_overlap_eq_interiorCompression_add_transition
      P R hP hPadj hRadj hRP
  calc
    hsNormSq
        ((centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) =
        hsNormSq (R * P) := by
      simpa only [P, R, A, B] using hNorm
    _ = hsNormSq (HTGeometry.twoProjectionInteriorCompression P R) +
          hsNormSq (HTGeometry.twoProjectionTransition P R) := hsplit
    _ = hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) +
        hsNormSq
          (crossBoundary (centralFourierForbidden a).starProjection
            (centralPhysicalForbidden a).starProjection) := by
      simp only [P, R, A, B, soninAlternatingBlock, crossBoundary,
        HTGeometry.twoProjectionInteriorCompression, HTGeometry.twoProjectionTransition]

/-- The former single exterior-overlap unknown is itself a positive two-channel value: the
exterior compressed Hamiltonian plus the same transition/number-variance energy as the prolate
sector. -/
theorem hsNormSq_centralSoninExteriorOverlap_eq_exteriorCompression_add_transition
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (centralSoninExteriorOverlap a) =
      ContinuousLinearMap.hsNormSq (centralSoninExteriorCompression a) +
        ContinuousLinearMap.hsNormSq
          (crossBoundary (centralFourierForbidden a).starProjection
            (centralPhysicalForbidden a).starProjection) := by
  have hCorrection :=
    hsNormSq_centralSoninProjectionCorrection_eq_timeBand_add_exterior a ha
  have hPartition :=
    hsNormSq_centralSoninProjectionCorrection_eq_compressions_add_two_mul_transition a ha
  have hTime := hsNormSq_centralTimeBandOverlap_eq_prolateBlock_add_transition a ha
  linarith

/-- **Concrete finite Witten-index descent.**  Equality of the interior and exterior overlap
energies is now exactly equality of the squared prolate block and the squared exterior
compression; the transition energy cancels with no spectral argument. -/
theorem hsNormSq_centralTimeBandOverlap_add_exteriorCompression_eq_exteriorOverlap_add_prolateBlock
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq
          ((centralFourierForbidden a).starProjection *
            (centralPhysicalForbidden a).starProjection) +
        ContinuousLinearMap.hsNormSq (centralSoninExteriorCompression a) =
      ContinuousLinearMap.hsNormSq (centralSoninExteriorOverlap a) +
        ContinuousLinearMap.hsNormSq
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a)) := by
  rw [hsNormSq_centralTimeBandOverlap_eq_prolateBlock_add_transition a ha,
    hsNormSq_centralSoninExteriorOverlap_eq_exteriorCompression_add_transition a ha]
  ring

/-- **All-power Sonin Witten cancellation.**  Every consecutive power difference of the prolate
and exterior compressed Hamiltonians has the same trace.  Both sides are traces of products of
Hilbert--Schmidt transition operators, never traces of the correction itself. -/
theorem opTrace_centralProlatePowerDifference_eq_exteriorCompressionPowerDifference
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ContinuousLinearMap.opTrace
        (soninAlternatingBlock (centralPhysicalForbidden a)
              (centralFourierForbidden a) ^ (n + 1) -
          soninAlternatingBlock (centralPhysicalForbidden a)
              (centralFourierForbidden a) ^ (n + 2)) =
      ContinuousLinearMap.opTrace
        (centralSoninExteriorCompression a ^ (n + 1) -
          centralSoninExteriorCompression a ^ (n + 2)) := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  have hP : IsIdempotentElem P := B.isIdempotentElem_starProjection
  have hR : IsIdempotentElem R := A.isIdempotentElem_starProjection
  have hQ : IsIdempotentElem Q := by
    dsimp only [Q, centralSoninProjection, centralSoninCarrier]
    exact (Aᵮ ⊓ Bᵮ).isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection B).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection A).star_eq
  have hQadj : ContinuousLinearMap.adjoint Q = Q := by
    dsimp only [Q, centralSoninProjection, centralSoninCarrier]
    exact (isSelfAdjoint_starProjection (Aᵮ ⊓ Bᵮ)).star_eq
  have hPZ : P * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change B.starProjection ((Aᵮ ⊓ Bᵮ).starProjection x) = 0
    apply B.starProjection_apply_eq_zero_iff.mpr
    exact ((Aᵮ ⊓ Bᵮ).starProjection_apply_mem x).2
  have hZP : Q * P = 0 := by
    calc
      Q * P = ContinuousLinearMap.adjoint (P * Q) := by
        change Q ∘L P = ContinuousLinearMap.adjoint (P ∘L Q)
        rw [ContinuousLinearMap.adjoint_comp, hQadj, hPadj]
      _ = 0 := by rw [hPZ]; simp
  have hRZ : R * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change A.starProjection ((Aᵮ ⊓ Bᵮ).starProjection x) = 0
    apply A.starProjection_apply_eq_zero_iff.mpr
    exact ((Aᵮ ⊓ Bᵮ).starProjection_apply_mem x).1
  have hZR : Q * R = 0 := by
    calc
      Q * R = ContinuousLinearMap.adjoint (R * Q) := by
        change Q ∘L R = ContinuousLinearMap.adjoint (R ∘L Q)
        rw [ContinuousLinearMap.adjoint_comp, hQadj, hRadj]
      _ = 0 := by rw [hRZ]; simp
  have hRP : ContinuousLinearMap.IsHilbertSchmidt (R * P) := by
    simpa only [P, R, A, B, centralPhysicalForbidden, centralFourierForbidden,
      indicatorCutoff_eq_physicalForbidden_starProjection,
      fourierCutoff_eq_fourierForbidden_starProjection] using
      isHilbertSchmidt_indicatorCutoff_fourierCutoff_central a a ha
  have htrace :=
    HTGeometry.opTrace_twoProjectionInteriorCompression_powerDifference_eq_exteriorCompression_powerDifference
      P R Q hP hR hQ hPadj hRadj hPZ hZP hRZ hZR hRP n
  simpa only [P, R, Q, A, B, soninAlternatingBlock,
    centralSoninExteriorCompression, HTGeometry.twoProjectionInteriorCompression,
    HTGeometry.twoProjectionExteriorCompression] using htrace

/-- The first power difference gives equality of the prolate and exterior impurity traces. -/
theorem opTrace_centralProlateImpurity_eq_exteriorCompressionImpurity
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.opTrace
        (soninAlternatingBlock (centralPhysicalForbidden a)
              (centralFourierForbidden a) -
          soninAlternatingBlock (centralPhysicalForbidden a)
              (centralFourierForbidden a) *
            soninAlternatingBlock (centralPhysicalForbidden a)
              (centralFourierForbidden a)) =
      ContinuousLinearMap.opTrace
        (centralSoninExteriorCompression a -
          centralSoninExteriorCompression a * centralSoninExteriorCompression a) := by
  simpa only [zero_add, pow_one, pow_two] using
    opTrace_centralProlatePowerDifference_eq_exteriorCompressionPowerDifference a ha 0

/-- The difference of the prolate and exterior individual power traces is constant from degree
two onward.  This is the finite telescoping invariant whose terminal limit would identify the two
compressed Hilbert--Schmidt energies. -/
theorem opTrace_centralProlate_sq_sub_exteriorCompression_sq_eq_power_sub_power
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ContinuousLinearMap.opTrace
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a) ^ 2) -
        ContinuousLinearMap.opTrace (centralSoninExteriorCompression a ^ 2) =
      ContinuousLinearMap.opTrace
          (soninAlternatingBlock (centralPhysicalForbidden a)
            (centralFourierForbidden a) ^ (n + 2)) -
        ContinuousLinearMap.opTrace (centralSoninExteriorCompression a ^ (n + 2)) := by
  let A : SoninL2 →L[ℂ] SoninL2 :=
    soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a)
  let E : SoninL2 →L[ℂ] SoninL2 := centralSoninExteriorCompression a
  have hA : IsHilbertSchmidt A := by
    simpa only [A] using centralSoninAlternatingBlock_isHilbertSchmidt a ha
  have hE : IsHilbertSchmidt E := by
    simpa only [E] using centralSoninExteriorCompression_isHilbertSchmidt a ha
  change opTrace (A ^ 2) - opTrace (E ^ 2) =
    opTrace (A ^ (n + 2)) - opTrace (E ^ (n + 2))
  induction n with
  | zero => simp
  | succ n ih =>
      have hPowerDifference :=
        opTrace_centralProlatePowerDifference_eq_exteriorCompressionPowerDifference
          a ha (n + 1)
      change opTrace (A ^ (n + 2) - A ^ (n + 3)) =
          opTrace (E ^ (n + 2) - E ^ (n + 3)) at hPowerDifference
      have hAlinear :=
        HTGeometry.opTrace_pow_add_two_sub_pow_add_three_of_isHilbertSchmidt A hA n
      have hElinear :=
        HTGeometry.opTrace_pow_add_two_sub_pow_add_three_of_isHilbertSchmidt E hE n
      rw [hAlinear, hElinear] at hPowerDifference
      have hstep :
          opTrace (A ^ (n + 2)) - opTrace (E ^ (n + 2)) =
            opTrace (A ^ (n + 3)) - opTrace (E ^ (n + 3)) := by
        linear_combination hPowerDifference
      calc
        opTrace (A ^ 2) - opTrace (E ^ 2) =
            opTrace (A ^ (n + 2)) - opTrace (E ^ (n + 2)) := ih
        _ = opTrace (A ^ (n + 3)) - opTrace (E ^ (n + 3)) := hstep
        _ = opTrace (A ^ (Nat.succ n + 2)) -
            opTrace (E ^ (Nat.succ n + 2)) := by
          simp only [Nat.succ_eq_add_one, Nat.add_assoc]

/-- The existing compact strict-contraction theorem for the central prolate block discharges its
terminal power-trace limit. -/
theorem tendsto_opTrace_centralSoninAlternatingBlock_pow_add_two_zero
    (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto
      (fun n : ℕ => ContinuousLinearMap.opTrace
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a) ^ (n + 2)))
      Filter.atTop (nhds 0) :=
  ContinuousLinearMap.tendsto_opTrace_pow_add_two_zero_of_isHilbertSchmidt_norm_lt_one
    (centralSoninAlternatingBlock_isHilbertSchmidt a ha)
    (norm_centralSoninAlternatingBlock_lt_one a ha)

/-- **Exterior strictness is the sole remaining supersymmetric hypothesis.**  If the new
zero-mode-subtracted exterior compression is a strict contraction, the finite trace invariant and
the two terminal power-trace limits identify its Hilbert--Schmidt energy with the prolate-block
energy. -/
theorem hsNormSq_centralSoninExteriorCompression_eq_prolateBlock_of_norm_lt_one
    (a : ℝ) (ha : 0 < a)
    (hExterior : ‖centralSoninExteriorCompression a‖ < 1) :
    ContinuousLinearMap.hsNormSq (centralSoninExteriorCompression a) =
      ContinuousLinearMap.hsNormSq
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a)) := by
  let A : SoninL2 →L[ℂ] SoninL2 :=
    soninAlternatingBlock (centralPhysicalForbidden a) (centralFourierForbidden a)
  let E : SoninL2 →L[ℂ] SoninL2 := centralSoninExteriorCompression a
  let P : SoninL2 →L[ℂ] SoninL2 := (centralFourierForbidden a).starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := (centralPhysicalForbidden a).starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  have hA : IsHilbertSchmidt A := by
    simpa only [A] using centralSoninAlternatingBlock_isHilbertSchmidt a ha
  have hE : IsHilbertSchmidt E := by
    simpa only [E] using centralSoninExteriorCompression_isHilbertSchmidt a ha
  have hAtend : Filter.Tendsto (fun n : ℕ => opTrace (A ^ (n + 2)))
      Filter.atTop (nhds 0) := by
    simpa only [A] using tendsto_opTrace_centralSoninAlternatingBlock_pow_add_two_zero a ha
  have hEtend : Filter.Tendsto (fun n : ℕ => opTrace (E ^ (n + 2)))
      Filter.atTop (nhds 0) :=
    ContinuousLinearMap.tendsto_opTrace_pow_add_two_zero_of_isHilbertSchmidt_norm_lt_one
      hE (by simpa only [E] using hExterior)
  have hdiff : Filter.Tendsto
      (fun n : ℕ => opTrace (A ^ (n + 2)) - opTrace (E ^ (n + 2)))
      Filter.atTop (nhds 0) := by
    simpa using hAtend.sub hEtend
  have hInvariant (n : ℕ) :
      opTrace (A ^ 2) - opTrace (E ^ 2) =
        opTrace (A ^ (n + 2)) - opTrace (E ^ (n + 2)) := by
    simpa only [A, E] using
      opTrace_centralProlate_sq_sub_exteriorCompression_sq_eq_power_sub_power a ha n
  have hconst : Filter.Tendsto
      (fun _ : ℕ => opTrace (A ^ 2) - opTrace (E ^ 2))
      Filter.atTop (nhds 0) :=
    hdiff.congr' (Filter.Eventually.of_forall fun n => (hInvariant n).symm)
  have htraceZero : opTrace (A ^ 2) - opTrace (E ^ 2) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  have htraceEq : opTrace (A ^ 2) = opTrace (E ^ 2) := sub_eq_zero.mp htraceZero
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
  have hQadj : ContinuousLinearMap.adjoint Q = Q := by
    dsimp only [Q, centralSoninProjection, centralSoninCarrier]
    exact (isSelfAdjoint_starProjection
      ((centralPhysicalForbidden a)ᵮ ⊓ (centralFourierForbidden a)ᵮ)).star_eq
  have hAadj : ContinuousLinearMap.adjoint A = A := by
    simpa only [A, P, R, soninAlternatingBlock,
      HTGeometry.twoProjectionInteriorCompression] using
      HTGeometry.adjoint_twoProjectionInteriorCompression P R hPadj hRadj
  have hEadj : ContinuousLinearMap.adjoint E = E := by
    simpa only [E, P, R, Q, centralSoninExteriorCompression] using
      HTGeometry.adjoint_twoProjectionExteriorCompression P R Q hPadj hRadj hQadj
  have hAenergy := ContinuousLinearMap.re_opTrace_adjoint_comp_self hA
  have hEenergy := ContinuousLinearMap.re_opTrace_adjoint_comp_self hE
  rw [hAadj] at hAenergy
  rw [hEadj] at hEenergy
  have hAtrace : Complex.re (opTrace (A ^ 2)) = hsNormSq A := by
    simpa only [pow_two, ContinuousLinearMap.mul_def] using hAenergy
  have hEtrace : Complex.re (opTrace (E ^ 2)) = hsNormSq E := by
    simpa only [pow_two, ContinuousLinearMap.mul_def] using hEenergy
  change hsNormSq E = hsNormSq A
  calc
    hsNormSq E = Complex.re (opTrace (E ^ 2)) := hEtrace.symm
    _ = Complex.re (opTrace (A ^ 2)) := congrArg Complex.re htraceEq.symm
    _ = hsNormSq A := hAtrace

/-- Exterior strictness identifies the original two overlap energies, not only their compressed
Hamiltonian factors.  The common transition/number-variance channel cancels exactly. -/
theorem hsNormSq_centralSoninExteriorOverlap_eq_timeBand_of_exteriorCompression_norm_lt_one
    (a : ℝ) (ha : 0 < a)
    (hExterior : ‖centralSoninExteriorCompression a‖ < 1) :
    ContinuousLinearMap.hsNormSq (centralSoninExteriorOverlap a) =
      ContinuousLinearMap.hsNormSq
        ((centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) := by
  rw [hsNormSq_centralSoninExteriorOverlap_eq_exteriorCompression_add_transition a ha,
    hsNormSq_centralTimeBandOverlap_eq_prolateBlock_add_transition a ha,
    hsNormSq_centralSoninExteriorCompression_eq_prolateBlock_of_norm_lt_one
      a ha hExterior]

/-- Under the sole remaining exterior-strictness condition, the full Sonin correction energy is
exactly twice the ordinary finite time-band energy. -/
theorem hsNormSq_centralSoninProjectionCorrection_eq_two_mul_timeBand_of_exteriorCompression_norm_lt_one
    (a : ℝ) (ha : 0 < a)
    (hExterior : ‖centralSoninExteriorCompression a‖ < 1) :
    ContinuousLinearMap.hsNormSq (centralSoninProjectionCorrection a) =
      2 * ContinuousLinearMap.hsNormSq
        ((centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) := by
  rw [hsNormSq_centralSoninProjectionCorrection_eq_timeBand_add_exterior a ha,
    hsNormSq_centralSoninExteriorOverlap_eq_timeBand_of_exteriorCompression_norm_lt_one
      a ha hExterior]
  ring

/-- **Exact Sonin supersymmetric factor equality.**  The zero-mode-subtracted exterior and
interior compressed Hamiltonians have the same Hilbert--Schmidt energy.  Exterior strictness is
now discharged by the complementary-block carrier subtraction. -/
theorem hsNormSq_centralSoninExteriorCompression_eq_prolateBlock
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (centralSoninExteriorCompression a) =
      ContinuousLinearMap.hsNormSq
        (soninAlternatingBlock (centralPhysicalForbidden a)
          (centralFourierForbidden a)) :=
  hsNormSq_centralSoninExteriorCompression_eq_prolateBlock_of_norm_lt_one
    a ha (norm_centralSoninExteriorCompression_lt_one a ha)

/-- The two original Sonin overlap channels have exactly the same Hilbert--Schmidt energy. -/
theorem hsNormSq_centralSoninExteriorOverlap_eq_timeBand
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (centralSoninExteriorOverlap a) =
      ContinuousLinearMap.hsNormSq
        ((centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) :=
  hsNormSq_centralSoninExteriorOverlap_eq_timeBand_of_exteriorCompression_norm_lt_one
    a ha (norm_centralSoninExteriorCompression_lt_one a ha)

/-- The complete zero-mode-corrected Sonin projection energy is exactly twice the ordinary
finite time-band energy. -/
theorem hsNormSq_centralSoninProjectionCorrection_eq_two_mul_timeBand
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (centralSoninProjectionCorrection a) =
      2 * ContinuousLinearMap.hsNormSq
        ((centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) :=
  hsNormSq_centralSoninProjectionCorrection_eq_two_mul_timeBand_of_exteriorCompression_norm_lt_one
    a ha (norm_centralSoninExteriorCompression_lt_one a ha)

/-- The zero-mode-subtracted exterior overlap carries the same exact area `4 a²`. -/
theorem hsNormSq_centralSoninExteriorOverlap_eq_four_mul_sq
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (centralSoninExteriorOverlap a) = 4 * a ^ 2 := by
  rw [hsNormSq_centralSoninExteriorOverlap_eq_timeBand a ha,
    hsNormSq_centralTimeBandOverlap_eq_four_mul_sq a ha]

/-- The complete Sonin projection correction has exact Hilbert--Schmidt energy `8 a²`. -/
theorem hsNormSq_centralSoninProjectionCorrection_eq_eight_mul_sq
    (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (centralSoninProjectionCorrection a) = 8 * a ^ 2 := by
  rw [hsNormSq_centralSoninProjectionCorrection_eq_two_mul_timeBand a ha,
    hsNormSq_centralTimeBandOverlap_eq_four_mul_sq a ha]
  ring

/-- The exact principal-subtracted ambient Sonin dilation residual is Hilbert--Schmidt. -/
theorem centralSoninDilationCornerResidual_isHilbertSchmidt
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ContinuousLinearMap.IsHilbertSchmidt (centralSoninDilationCornerResidual a p hp) :=
  (centralSoninDilationCornerResidual_mem_timeBandIdeal a p ha hp).isHilbertSchmidt

/-- **Sonin active-space conservation law.**  The physical/Fourier projection mismatch and the
exact projection correction exhaust the squared norm outside the actual Sonin carrier.  Thus the
Hilbert--Schmidt correction is not an independent error term: it is the zero-mode-subtracted
supersymmetric partner of the two forbidden-sector projections. -/
theorem norm_centralSoninProjectionDifference_sq_add_correction_sq
    (a : ℝ) (psi : SoninL2) :
    ‖((centralPhysicalForbidden a).starProjection -
        (centralFourierForbidden a).starProjection) psi‖ ^ 2 +
      ‖centralSoninProjectionCorrection a psi‖ ^ 2 =
        ‖((1 : SoninL2 →L[ℂ] SoninL2) - centralSoninProjection a) psi‖ ^ 2 := by
  let A := centralPhysicalForbidden a
  let B := centralFourierForbidden a
  let P : SoninL2 →L[ℂ] SoninL2 := A.starProjection
  let R : SoninL2 →L[ℂ] SoninL2 := B.starProjection
  let Q : SoninL2 →L[ℂ] SoninL2 := centralSoninProjection a
  have hP : IsIdempotentElem P := A.isIdempotentElem_starProjection
  have hR : IsIdempotentElem R := B.isIdempotentElem_starProjection
  have hQ : IsIdempotentElem Q := by
    dsimp only [Q, centralSoninProjection, centralSoninCarrier]
    exact (Aᵮ ⊓ Bᵮ).isIdempotentElem_starProjection
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (isSelfAdjoint_starProjection A).star_eq
  have hRadj : ContinuousLinearMap.adjoint R = R :=
    (isSelfAdjoint_starProjection B).star_eq
  have hQadj : ContinuousLinearMap.adjoint Q = Q := by
    dsimp only [Q, centralSoninProjection, centralSoninCarrier]
    exact (isSelfAdjoint_starProjection (Aᵮ ⊓ Bᵮ)).star_eq
  have hPQ : P * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change A.starProjection ((Aᵮ ⊓ Bᵮ).starProjection x) = 0
    apply A.starProjection_apply_eq_zero_iff.mpr
    exact ((Aᵮ ⊓ Bᵮ).starProjection_apply_mem x).1
  have hRQ : R * Q = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change B.starProjection ((Aᵮ ⊓ Bᵮ).starProjection x) = 0
    apply B.starProjection_apply_eq_zero_iff.mpr
    exact ((Aᵮ ⊓ Bᵮ).starProjection_apply_mem x).2
  have hQP : Q * P = 0 := by
    calc
      Q * P = ContinuousLinearMap.adjoint (P * Q) := by
        rw [adjoint_mul_soninL2, hQadj, hPadj]
      _ = 0 := by rw [hPQ]; simp
  have hQR : Q * R = 0 := by
    calc
      Q * R = ContinuousLinearMap.adjoint (R * Q) := by
        rw [adjoint_mul_soninL2, hQadj, hRadj]
      _ = 0 := by rw [hRQ]; simp
  have henergy := HTGeometry.norm_twoProjection_difference_sq_add_corrected_complement_sq
    P R Q hP hR hQ hPadj hRadj hQadj hPQ hQP hRQ hQR psi
  simpa only [P, R, Q, A, B, centralSoninProjectionCorrection,
    indicatorCutoff_eq_physicalForbidden_starProjection,
    fourierCutoff_eq_fourierForbidden_starProjection] using henergy

theorem norm_one_sub_centralSoninProjection_le_one (a : ℝ) :
    ‖(1 : SoninL2 →L[ℂ] SoninL2) - centralSoninProjection a‖ ≤ 1 := by
  rw [centralSoninProjection]
  rw [← (centralSoninCarrier a).starProjection_orthogonal']
  exact Submodule.starProjection_norm_le _

/-- The exact Sonin projection correction is itself a contraction.  This follows from the active
energy partition, rather than from a triangle estimate on its three projection terms. -/
theorem norm_centralSoninProjectionCorrection_le_one (a : ℝ) :
    ‖centralSoninProjectionCorrection a‖ ≤ 1 := by
  apply (centralSoninProjectionCorrection a).opNorm_le_bound zero_le_one
  intro psi
  have henergy := norm_centralSoninProjectionDifference_sq_add_correction_sq a psi
  have hcorr : ‖centralSoninProjectionCorrection a psi‖ ≤
      ‖((1 : SoninL2 →L[ℂ] SoninL2) - centralSoninProjection a) psi‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [sq_nonneg
      ‖((centralPhysicalForbidden a).starProjection -
        (centralFourierForbidden a).starProjection) psi‖]
  calc
    ‖centralSoninProjectionCorrection a psi‖ ≤
        ‖((1 : SoninL2 →L[ℂ] SoninL2) - centralSoninProjection a) psi‖ := hcorr
    _ ≤ ‖(1 : SoninL2 →L[ℂ] SoninL2) - centralSoninProjection a‖ * ‖psi‖ :=
      ((1 : SoninL2 →L[ℂ] SoninL2) - centralSoninProjection a).le_opNorm psi
    _ ≤ 1 * ‖psi‖ := mul_le_mul_of_nonneg_right
      (norm_one_sub_centralSoninProjection_le_one a) (norm_nonneg psi)
    _ = ‖psi‖ := one_mul _

/-- **Sharp two-projection bound.**  The formal physical/Fourier complement is a contraction.
This is the Sonin specialization of the anticommutative Pythagorean identity and removes the
former triangle bound `≤ 3`. -/
theorem norm_centralSoninFormalComplement_le_one (a : ℝ) :
    ‖centralSoninFormalComplement a‖ ≤ 1 := by
  rw [centralSoninFormalComplement,
    indicatorCutoff_eq_physicalForbidden_starProjection,
    fourierCutoff_eq_fourierForbidden_starProjection]
  exact HTGeometry.norm_twoProjection_complement_le_one
    (centralPhysicalForbidden a).starProjection
    (centralFourierForbidden a).starProjection
    (centralPhysicalForbidden a).isIdempotentElem_starProjection
    (centralFourierForbidden a).isIdempotentElem_starProjection
    (isSelfAdjoint_starProjection (centralPhysicalForbidden a)).star_eq
    (isSelfAdjoint_starProjection (centralFourierForbidden a)).star_eq

/-- The active-space correction law propagates to a scale-independent operator-norm estimate for
the principal-subtracted dilation corner.  Both cutoff factors and the exact correction are
contractions; only the symmetric dilation sum contributes the factor `2` in each of the two
linearized residual terms. -/
theorem norm_centralSoninDilationCornerResidual_le_four
    (a p : ℝ) (hp : 1 < p) :
    ‖centralSoninDilationCornerResidual a p hp‖ ≤ 4 := by
  let Q := centralSoninProjection a
  let Q₀ := centralSoninFormalComplement a
  let D := dilationSum p hp
  let C := centralSoninProjectionCorrection a
  have hEq : centralSoninDilationCornerResidual a p hp =
      (1 - Q) * D * C - C * D * Q₀ := by
    simpa [Q, Q₀, D, C] using
      centralSoninDilationCornerResidual_eq_correction_factorization a p hp
  have hQ : ‖(1 : SoninL2 →L[ℂ] SoninL2) - Q‖ ≤ 1 := by
    simpa [Q] using norm_one_sub_centralSoninProjection_le_one a
  have hQ₀ : ‖Q₀‖ ≤ 1 := by
    simpa [Q₀] using norm_centralSoninFormalComplement_le_one a
  have hC : ‖C‖ ≤ 1 := by
    simpa [C] using norm_centralSoninProjectionCorrection_le_one a
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
  rw [hEq]
  calc
    ‖(1 - Q) * D * C - C * D * Q₀‖ ≤
        ‖(1 - Q) * D * C‖ + ‖C * D * Q₀‖ := norm_sub_le _ _
    _ ≤ (‖1 - Q‖ * ‖D‖) * ‖C‖ + (‖C‖ * ‖D‖) * ‖Q₀‖ := by
      exact add_le_add
        ((norm_mul_le ((1 - Q) * D) C).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le (1 - Q) D) (norm_nonneg C)))
        ((norm_mul_le (C * D) Q₀).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le C D) (norm_nonneg Q₀)))
    _ ≤ (1 * 2) * 1 + (1 * 2) * 1 := by gcongr
    _ = 4 := by norm_num

/-- **Uniform scale-independent residual bound.** The Hilbert--Schmidt energy of the exact
principal-subtracted Sonin dilation residual is controlled solely by the fixed projection
correction.  In particular, the bound does not grow with the dilation scale `p`. -/
theorem centralSoninDilationCornerResidual_hsNormSq_le
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ContinuousLinearMap.hsNormSq (centralSoninDilationCornerResidual a p hp) ≤
      16 * ContinuousLinearMap.hsNormSq (centralSoninProjectionCorrection a) := by
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
      change centralSoninDilationCornerResidual a p hp =
        (1 - Q) * D * C - C * D * Q₀
      simpa [Q, Q₀, D, C] using
        centralSoninDilationCornerResidual_eq_correction_factorization a p hp
    have hQ : ‖(1 : SoninL2 →L[ℂ] SoninL2) - Q‖ ≤ 1 := by
      simpa [Q] using norm_one_sub_centralSoninProjection_le_one a
    have hQ₀ : ‖Q₀‖ ≤ 1 := by
      simpa [Q₀] using norm_centralSoninFormalComplement_le_one a
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
    have hDQ₀ : ‖D * Q₀‖ ≤ 2 := by
      calc
        ‖D * Q₀‖ ≤ ‖D‖ * ‖Q₀‖ := norm_mul_le _ _
        _ ≤ 2 * 1 := mul_le_mul hD hQ₀ (norm_nonneg _) (by norm_num)
        _ = 2 := by norm_num
    have hAbound : hsNormSq A ≤ 4 * hsNormSq C := by
      calc
        hsNormSq A ≤ ‖(1 - Q) * D‖ ^ 2 * hsNormSq C :=
          hsNormSq_comp_left_le hC ((1 - Q) * D)
        _ ≤ 4 * hsNormSq C := by
          apply mul_le_mul_of_nonneg_right _ (hsNormSq_nonneg C)
          nlinarith [norm_nonneg ((1 - Q) * D)]
    have hBbound : hsNormSq B ≤ 4 * hsNormSq C := by
      calc
        hsNormSq B ≤ ‖D * Q₀‖ ^ 2 * hsNormSq C :=
          hsNormSq_comp_right_le hC (D * Q₀)
        _ ≤ 4 * hsNormSq C := by
          apply mul_le_mul_of_nonneg_right _ (hsNormSq_nonneg C)
          nlinarith [norm_nonneg (D * Q₀)]
    rw [hEq]
    calc
      hsNormSq (A - B) ≤ 2 * hsNormSq A + 2 * hsNormSq B :=
        hsNormSq_sub_le hA hB
      _ ≤ 2 * (4 * hsNormSq C) + 2 * (4 * hsNormSq C) := by gcongr
      _ = 16 * hsNormSq C := by ring

/-- The residual estimate with the opaque correction energy eliminated.  The right-hand side is
now the sum of the concrete time-band overlap and its zero-mode-subtracted exterior partner. -/
theorem centralSoninDilationCornerResidual_hsNormSq_le_timeBand_add_exterior
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ContinuousLinearMap.hsNormSq (centralSoninDilationCornerResidual a p hp) ≤
      16 * (ContinuousLinearMap.hsNormSq
          ((centralFourierForbidden a).starProjection *
            (centralPhysicalForbidden a).starProjection) +
        ContinuousLinearMap.hsNormSq (centralSoninExteriorOverlap a)) := by
  rw [← hsNormSq_centralSoninProjectionCorrection_eq_timeBand_add_exterior a ha]
  exact centralSoninDilationCornerResidual_hsNormSq_le a p ha hp

/-- Under exterior strictness, the residual bound has only the ordinary time-band energy on its
right-hand side; the supersymmetric exterior partner contributes the same value. -/
theorem centralSoninDilationCornerResidual_hsNormSq_le_timeBand_of_exteriorCompression_norm_lt_one
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p)
    (hExterior : ‖centralSoninExteriorCompression a‖ < 1) :
    ContinuousLinearMap.hsNormSq (centralSoninDilationCornerResidual a p hp) ≤
      32 * ContinuousLinearMap.hsNormSq
        ((centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) := by
  have hbound :=
    centralSoninDilationCornerResidual_hsNormSq_le_timeBand_add_exterior a p ha hp
  rw [hsNormSq_centralSoninExteriorOverlap_eq_timeBand_of_exteriorCompression_norm_lt_one
    a ha hExterior] at hbound
  nlinarith

/-- The unconditional residual estimate after the exterior strictness hypothesis has been
discharged. -/
theorem centralSoninDilationCornerResidual_hsNormSq_le_timeBand
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ContinuousLinearMap.hsNormSq (centralSoninDilationCornerResidual a p hp) ≤
      32 * ContinuousLinearMap.hsNormSq
        ((centralFourierForbidden a).starProjection *
          (centralPhysicalForbidden a).starProjection) :=
  centralSoninDilationCornerResidual_hsNormSq_le_timeBand_of_exteriorCompression_norm_lt_one
    a p ha hp (norm_centralSoninExteriorCompression_lt_one a ha)

/-- The Shannon area law removes the last operator-valued quantity from the dilation-residual
bound. -/
theorem centralSoninDilationCornerResidual_hsNormSq_le_128_mul_sq
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ContinuousLinearMap.hsNormSq (centralSoninDilationCornerResidual a p hp) ≤
      128 * a ^ 2 := by
  have h := centralSoninDilationCornerResidual_hsNormSq_le_timeBand a p ha hp
  rw [hsNormSq_centralTimeBandOverlap_eq_four_mul_sq a ha] at h
  nlinarith

/-- The residual estimate expressed entirely through the two positive compressed Hamiltonians
and the already-existing prolate transition value.  This is the direct quantitative consumer of
the finite Witten-index partition. -/
theorem centralSoninDilationCornerResidual_hsNormSq_le_compressions_add_two_mul_transition
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ContinuousLinearMap.hsNormSq (centralSoninDilationCornerResidual a p hp) ≤
      16 *
        (ContinuousLinearMap.hsNormSq
            (soninAlternatingBlock (centralPhysicalForbidden a)
              (centralFourierForbidden a)) +
          ContinuousLinearMap.hsNormSq (centralSoninExteriorCompression a) +
            2 * ContinuousLinearMap.hsNormSq
              (crossBoundary (centralFourierForbidden a).starProjection
                (centralPhysicalForbidden a).starProjection)) := by
  rw [← hsNormSq_centralSoninProjectionCorrection_eq_compressions_add_two_mul_transition
    a ha]
  exact centralSoninDilationCornerResidual_hsNormSq_le a p ha hp

/-- Every actual prime-power residual block is Hilbert--Schmidt. -/
theorem centralSoninPrimePowerResidual_isHilbertSchmidt
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt (centralSoninPrimePowerResidual a pk) :=
  (centralSoninPrimePowerResidual_mem_timeBandIdeal a ha pk).isHilbertSchmidt

/-- Hilbert--Schmidt energy of the unconditional quadratic/prime-square two-channel anchor. -/
def soninPrimeQuadraticAnchorEnergy (a : ℝ) (p : Nat.Primes) : ℝ :=
  ContinuousLinearMap.hsNormSq
      (centralSoninCornerCorrectionResponse a
        (soninPrimeDilationSignal p * soninPrimeDilationSignal p)) +
    ContinuousLinearMap.hsNormSq (centralSoninPrimePowerResidual a (p, 0))

/-- The two-channel anchor energy is strictly positive at every positive aperture.  This is an
unconditional scalar denominator available to augmented coupled-source constructions. -/
theorem soninPrimeQuadraticAnchorEnergy_pos
    (a : ℝ) (ha : 0 < a) (p : Nat.Primes) :
    0 < soninPrimeQuadraticAnchorEnergy a p := by
  let A := centralSoninCornerCorrectionResponse a
    (soninPrimeDilationSignal p * soninPrimeDilationSignal p)
  let R := centralSoninPrimePowerResidual a (p, 0)
  change 0 < ContinuousLinearMap.hsNormSq A + ContinuousLinearMap.hsNormSq R
  have hAhs : ContinuousLinearMap.IsHilbertSchmidt A := by
    exact centralSoninCornerCorrectionResponse_isHilbertSchmidt a ha _
  have hRhs : ContinuousLinearMap.IsHilbertSchmidt R := by
    exact centralSoninPrimePowerResidual_isHilbertSchmidt a ha (p, 0)
  rcases centralSoninCornerCorrectionResponse_signalSq_ne_zero_or_primeSquareResidual_ne_zero
      a ha p with hA | hR
  · have hA' : A ≠ 0 := by simpa only [A] using hA
    have hAenergy : ContinuousLinearMap.hsNormSq A ≠ 0 := by
      intro hzero
      exact hA' ((ContinuousLinearMap.hsNormSq_eq_zero_iff hAhs).mp hzero)
    exact add_pos_of_pos_of_nonneg
      (lt_of_le_of_ne (ContinuousLinearMap.hsNormSq_nonneg A) (Ne.symm hAenergy))
      (ContinuousLinearMap.hsNormSq_nonneg R)
  · have hR' : R ≠ 0 := by simpa only [R] using hR
    have hRenergy : ContinuousLinearMap.hsNormSq R ≠ 0 := by
      intro hzero
      exact hR' ((ContinuousLinearMap.hsNormSq_eq_zero_iff hRhs).mp hzero)
    exact add_pos_of_nonneg_of_pos
      (ContinuousLinearMap.hsNormSq_nonneg A)
      (lt_of_le_of_ne (ContinuousLinearMap.hsNormSq_nonneg R) (Ne.symm hRenergy))

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
      (16 * ContinuousLinearMap.hsNormSq (centralSoninProjectionCorrection a)) *
        ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := by
  open ContinuousLinearMap in
    have hR := centralSoninPrimePowerResidual_isHilbertSchmidt a ha pk
    rw [centralSoninWeightedPrimePowerResidual, hsNormSq_smul_eq hR]
    have hbound := centralSoninDilationCornerResidual_hsNormSq_le a
      (soninPrimePowerScale pk) ha (one_lt_soninPrimePowerScale pk)
    simp only [centralSoninPrimePowerResidual]
    nlinarith [sq_nonneg ‖soninLogPrimePowerCoefficient pk‖]

/-- The weighted prime-power residual bound with the projection-correction and exterior energies
both eliminated in favor of the ordinary finite time-band overlap. -/
theorem centralSoninWeightedPrimePowerResidual_hsNormSq_le_timeBand
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ContinuousLinearMap.hsNormSq (centralSoninWeightedPrimePowerResidual a pk) ≤
      (32 * ContinuousLinearMap.hsNormSq
          ((centralFourierForbidden a).starProjection *
            (centralPhysicalForbidden a).starProjection)) *
        ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := by
  open ContinuousLinearMap in
    have hR := centralSoninPrimePowerResidual_isHilbertSchmidt a ha pk
    rw [centralSoninWeightedPrimePowerResidual, hsNormSq_smul_eq hR]
    have hbound := centralSoninDilationCornerResidual_hsNormSq_le_timeBand a
      (soninPrimePowerScale pk) ha (one_lt_soninPrimePowerScale pk)
    simp only [centralSoninPrimePowerResidual]
    nlinarith [sq_nonneg ‖soninLogPrimePowerCoefficient pk‖]

/-- Fully scalar weighted prime-power residual estimate obtained from the exact time--band area. -/
theorem centralSoninWeightedPrimePowerResidual_hsNormSq_le_128_mul_sq
    (a : ℝ) (ha : 0 < a) (pk : Nat.Primes × ℕ) :
    ContinuousLinearMap.hsNormSq (centralSoninWeightedPrimePowerResidual a pk) ≤
      (128 * a ^ 2) * ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := by
  have h := centralSoninWeightedPrimePowerResidual_hsNormSq_le_timeBand a ha pk
  rw [hsNormSq_centralTimeBandOverlap_eq_four_mul_sq a ha] at h
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
      (16 * hsNormSq (centralSoninProjectionCorrection a))

/-- The all-prime residual energy has a scalar aperture majorant.  This is the global consumer of
the local Shannon area law. -/
theorem tsum_centralSoninWeightedPrimePowerResidual_hsNormSq_le_area
    (a : ℝ) (ha : 0 < a) :
    ∑' pk : Nat.Primes × ℕ,
        ContinuousLinearMap.hsNormSq (centralSoninWeightedPrimePowerResidual a pk) ≤
      (128 * a ^ 2) *
        ∑' pk : Nat.Primes × ℕ, ‖soninLogPrimePowerCoefficient pk‖ ^ 2 := by
  exact (summable_centralSoninWeightedPrimePowerResidual_hsNormSq a ha).tsum_le_tsum
    (centralSoninWeightedPrimePowerResidual_hsNormSq_le_128_mul_sq a ha)
    (summable_norm_soninLogPrimePowerCoefficient_sq.mul_left (128 * a ^ 2))

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
