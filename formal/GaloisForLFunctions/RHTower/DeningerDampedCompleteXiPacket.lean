import GaloisForLFunctions.RHTower.DeningerDampedSourceMellinJets

/-!
# Complete damped Xi packet in the original Green and Gamma graph spaces

For each fixed damping `a > 1`, the actual original-prime source prefixes converge
in the full multiplicity-indexed Xi Hilbert space. A summable bound on their
successive differences proves convergence before any infinite multiplier is used.
Coordinate continuity identifies the limit with the literal Mellin integral of
the same weighted source constructed in `DeningerDampedWeightedSourceBoundary`.

The original Green resolvent, residue normalization and ordinary-prime Tate chains
retain their coefficients. The chains converge in the full Xi-indexed Gamma graph
norm. Both finite and completed physical readings are the original readings times
the exact nonzero source multiplier. Thus packet admission preserves the existing
critical-line discriminator; complete Green/BV-to-physical reader agreement remains
open. No endpoint or zero-damping limit is asserted.
-/

open Complex Filter Topology SchwartzMap MeasureTheory
noncomputable section
namespace RHTower
open DeningerMeyerGaussianGreen
open scoped TensorProduct

private theorem damped_character_norm_le_weight (L a : ℝ) (hL : 0 ≤ L)
    (s : ℂ) (hs : 0 ≤ s.re) :
    ‖(deningerDampedPrimeWeight L a : ℂ)*Complex.exp ((-L : ℂ)*s)‖ ≤
      deningerDampedPrimeWeight L a := by
  have he : ‖Complex.exp ((-L : ℂ)*s)‖ ≤ 1 := by
    rw [Complex.norm_exp,Real.exp_le_one_iff]
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,
      Complex.ofReal_im,neg_zero,zero_mul,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) hs
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0 < deningerDampedPrimeWeight L a from Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le).trans_eq (mul_one _)

/-- The original factor has a summable error on the whole closed Xi strip. -/
theorem deningerDampedPairedMultiplier_strip_bounds (L a : ℝ) (hL : 0 ≤ L)
    (ha : 0 ≤ a) (s : ℂ) (hs : 0 ≤ s.re ∧ s.re ≤ 1) :
    ‖deningerDampedPairedMultiplier L a s‖ ≤ Real.exp (2*deningerDampedPrimeWeight L a) ∧
      ‖deningerDampedPairedMultiplier L a s-1‖ ≤ 3*deningerDampedPrimeWeight L a := by
  let w := deningerDampedPrimeWeight L a
  let u : ℂ := (w : ℂ)*Complex.exp ((-L : ℂ)*s)
  let v : ℂ := (w : ℂ)*Complex.exp ((-L : ℂ)*(1-s))
  have hw : 0 ≤ w := (Real.exp_pos _).le
  have hw1 : w ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hL)
  have hu : ‖u‖ ≤ w := damped_character_norm_le_weight L a hL s hs.1
  have hv : ‖v‖ ≤ w := damped_character_norm_le_weight L a hL (1-s)
    (by simp only [Complex.sub_re,Complex.one_re]; linarith [hs.2])
  have hfu : ‖1-u‖ ≤ 1+w := (norm_sub_le (1 : ℂ) u).trans (by rw [norm_one]; linarith)
  have hfv : ‖1-v‖ ≤ 1+w := (norm_sub_le (1 : ℂ) v).trans (by rw [norm_one]; linarith)
  change ‖(1-u)*(1-v)‖ ≤ Real.exp (2*w) ∧ ‖(1-u)*(1-v)-1‖ ≤ 3*w
  constructor
  · rw [norm_mul]
    calc
      _ ≤ (1+w)*(1+w) := mul_le_mul hfu hfv (norm_nonneg _) (by positivity)
      _ ≤ Real.exp w*Real.exp w := by
        have he : 1+w ≤ Real.exp w := by linarith [Real.add_one_le_exp w]
        exact mul_le_mul he he (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · have he : (1-u)*(1-v)-1 = u*v-u-v := by ring
    rw [he]
    calc
      _ ≤ ‖u*v‖+‖u‖+‖v‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ w*w+w+w := by rw [norm_mul]; gcongr
      _ ≤ 3*w := by nlinarith

/-- Every finite original damped product is admitted on the full divisor. -/
theorem deningerDampedPrimeListMultiplier_norm_bound (a : ℝ) (ha : 0 ≤ a)
    (P : List Nat.Primes) (s : ℂ) (hs : 0 ≤ s.re ∧ s.re ≤ 1) :
    ‖deningerDampedPrimeListMultiplier a P s‖ ≤ (4 : ℝ)^P.length := by
  induction P with
  | nil => simp [deningerDampedPrimeListMultiplier]
  | cons p P ih =>
    simp only [deningerDampedPrimeListMultiplier,List.map_cons,List.prod_cons,norm_mul,
      List.length_cons,pow_succ] at *
    calc
      _ ≤ 4*‖(P.map fun (p : Nat.Primes) => deningerDampedPairedMultiplier (Real.log (p : ℕ)) a s).prod‖ :=
        mul_le_mul_of_nonneg_right (deningerDampedPairedMultiplier_norm_le_four (Real.log (p : ℕ)) a
          (Real.log_nonneg (by exact_mod_cast p.property.one_le)) ha s hs) (norm_nonneg _)
      _ ≤ 4*4^P.length := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := mul_comm _ _

/-- The entries are literal finite-source Mellin integrals on all native Xi copies. -/
def deningerDampedXiPrefix (a : {a : ℝ // 1<a}) (n : ℕ) : XiDivisorL2 :=
  ⟨fun q => deningerMeyerStrongLogMellin
      (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList) (q.1 : ℂ),
    Memℓp.mono ((lp.memℓp reflectedGaussianHorizonGradeL2).norm.const_smul
      ((4 : ℝ)^((GaloisForLFunctions.primesLE n).toList.length))) (fun q => by
        rw [deningerDampedPrimeListSource_mellin,norm_mul,Pi.smul_apply,smul_eq_mul,
          reflectedGaussianHorizonGradeL2_apply]
        exact mul_le_mul_of_nonneg_right
          (deningerDampedPrimeListMultiplier_norm_bound a.val (by linarith [a.property]) _ _
            ⟨(xi_divisor_support_re_mem_open_unit q.1).1.le,
              (xi_divisor_support_re_mem_open_unit q.1).2.le⟩) (norm_nonneg _))⟩

@[simp] theorem deningerDampedXiPrefix_apply (a : {a : ℝ // 1<a}) (n : ℕ) (q : XiZeroCopy) :
    deningerDampedXiPrefix a n q = deningerMeyerStrongLogMellin
      (deningerDampedPrimeListSource a.val (GaloisForLFunctions.primesLE n).toList) (q.1 : ℂ) := rfl

/-- Summable original-prime step majorant, without a spectral cutoff. -/
def deningerDampedXiStepWeight (a : ℝ) (n : ℕ) : ℝ :=
  deningerHalfDensityPrimeStepWeight (a-1/2) n

theorem deningerDampedXiStepWeight_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ deningerDampedXiStepWeight a n := deningerHalfDensityPrimeStepWeight_nonneg _ _

theorem deningerDampedXiStepWeight_summable {a : ℝ} (ha : 1<a) :
    Summable (deningerDampedXiStepWeight a) :=
  deningerHalfDensityPrimeStepWeight_summable (by linarith)

private theorem dampedXiStepWeight_prime (a : ℝ) {n : ℕ} (hn : n.Prime) :
    deningerDampedXiStepWeight a n = deningerDampedPrimeWeight (Real.log n) a := by
  have he := deningerHalfDensityPrimeStepWeight_eq_exp (a-1/2) (⟨n,hn⟩ : Nat.Primes)
  simpa only [deningerDampedXiStepWeight,sub_add_cancel,deningerDampedPrimeWeight] using he

private theorem dampedXiPrefix_step (a : {a : ℝ // 1<a}) (n : ℕ) (q : XiZeroCopy) :
    deningerDampedXiPrefix a (n+1) q =
      if (n+1).Prime then deningerDampedPairedMultiplier (Real.log (n+1 : ℕ)) a.val (q.1 : ℂ)*
        deningerDampedXiPrefix a n q else deningerDampedXiPrefix a n q := by
  simp only [deningerDampedXiPrefix_apply]
  rw [deningerDampedOriginalPrimePrefix_source_step]
  split_ifs with hn
  · exact deningerDampedPairedStrongLogDefect_mellin _ _ _ _
  · rfl

/-- Coordinate bounds retain the Gaussian source profile through each original-prime step. -/
theorem deningerDampedXiPrefix_pointwise_bounds (a : {a : ℝ // 1<a}) (n : ℕ) (q : XiZeroCopy) :
    ‖deningerDampedXiPrefix a (n+1) q‖ ≤
        Real.exp (2*deningerDampedXiStepWeight a.val (n+1))*‖deningerDampedXiPrefix a n q‖ ∧
      ‖deningerDampedXiPrefix a (n+1) q-deningerDampedXiPrefix a n q‖ ≤
        3*deningerDampedXiStepWeight a.val (n+1)*‖deningerDampedXiPrefix a n q‖ := by
  rw [dampedXiPrefix_step]
  split_ifs with hn
  · rw [dampedXiStepWeight_prime a.val hn]
    have hb := deningerDampedPairedMultiplier_strip_bounds (Real.log (n+1 : ℕ)) a.val
      (Real.log_nonneg (by exact_mod_cast hn.one_le)) (by linarith [a.property]) (q.1 : ℂ)
      ⟨(xi_divisor_support_re_mem_open_unit q.1).1.le,(xi_divisor_support_re_mem_open_unit q.1).2.le⟩
    constructor
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hb.1 (norm_nonneg _)
    · rw [show deningerDampedPairedMultiplier (Real.log (n+1 : ℕ)) a.val (q.1 : ℂ)*
          deningerDampedXiPrefix a n q-deningerDampedXiPrefix a n q =
        (deningerDampedPairedMultiplier (Real.log (n+1 : ℕ)) a.val (q.1 : ℂ)-1)*
          deningerDampedXiPrefix a n q by ring,norm_mul]
      exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)
  · simp [deningerDampedXiStepWeight,deningerHalfDensityPrimeStepWeight,hn]

theorem deningerDampedXiPrefix_step_bound (a : {a : ℝ // 1<a}) (n : ℕ) :
    ‖deningerDampedXiPrefix a (n+1)‖ ≤
      Real.exp (2*deningerDampedXiStepWeight a.val (n+1))*‖deningerDampedXiPrefix a n‖ := by
  calc
    _ ≤ ‖(Real.exp (2*deningerDampedXiStepWeight a.val (n+1)) : ℂ) • deningerDampedXiPrefix a n‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro q
      simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)] using (deningerDampedXiPrefix_pointwise_bounds a n q).1
    _ = _ := by simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

theorem deningerDampedXiPrefix_step_increment (a : {a : ℝ // 1<a}) (n : ℕ) :
    ‖deningerDampedXiPrefix a (n+1)-deningerDampedXiPrefix a n‖ ≤
      3*deningerDampedXiStepWeight a.val (n+1)*‖deningerDampedXiPrefix a n‖ := by
  have hw : 0 ≤ 3*deningerDampedXiStepWeight a.val (n+1) :=
    mul_nonneg (by norm_num) (deningerDampedXiStepWeight_nonneg _ _)
  calc
    _ ≤ ‖((3*deningerDampedXiStepWeight a.val (n+1) : ℝ) : ℂ) • deningerDampedXiPrefix a n‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro q
      simpa only [lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,norm_smul,
        Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw] using (deningerDampedXiPrefix_pointwise_bounds a n q).2
    _ = _ := by simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw]

theorem deningerDampedXiPrefix_norm_le (a : {a : ℝ // 1<a}) (n : ℕ) :
    ‖deningerDampedXiPrefix a n‖ ≤
      Real.exp (2*∑ k ∈ Finset.range n, deningerDampedXiStepWeight a.val (k+1))*
        ‖deningerDampedXiPrefix a 0‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ Real.exp (2*deningerDampedXiStepWeight a.val (n+1))*‖deningerDampedXiPrefix a n‖ :=
        deningerDampedXiPrefix_step_bound a n
      _ ≤ Real.exp (2*deningerDampedXiStepWeight a.val (n+1))*
          (Real.exp (2*∑ k ∈ Finset.range n, deningerDampedXiStepWeight a.val (k+1))*
            ‖deningerDampedXiPrefix a 0‖) := by gcongr
      _ = _ := by rw [← mul_assoc,← Real.exp_add,Finset.sum_range_succ]; congr 2; ring

def deningerDampedXiNormBound (a : {a : ℝ // 1<a}) : ℝ :=
  Real.exp (2*∑' k : ℕ, deningerDampedXiStepWeight a.val (k+1))*‖deningerDampedXiPrefix a 0‖

theorem deningerDampedXiPrefix_uniform_bound (a : {a : ℝ // 1<a}) (n : ℕ) :
    ‖deningerDampedXiPrefix a n‖ ≤ deningerDampedXiNormBound a := by
  apply (deningerDampedXiPrefix_norm_le a n).trans
  unfold deningerDampedXiNormBound
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact ((deningerDampedXiStepWeight_summable a.property).comp_injective
    (fun _ _ h => Nat.add_right_cancel h)).sum_le_tsum _
      (fun _ _ => deningerDampedXiStepWeight_nonneg a.val _)

/-- Full-divisor convergence is proved by a summable successive-difference bound. -/
theorem deningerDampedXiPrefix_cauchy (a : {a : ℝ // 1<a}) :
    CauchySeq (deningerDampedXiPrefix a) := by
  apply cauchySeq_of_dist_le_of_summable
    (fun n => 3*deningerDampedXiStepWeight a.val (n+1)*deningerDampedXiNormBound a)
  · intro n
    rw [dist_comm,dist_eq_norm]
    apply (deningerDampedXiPrefix_step_increment a n).trans
    exact mul_le_mul_of_nonneg_left (deningerDampedXiPrefix_uniform_bound a n)
      (mul_nonneg (by norm_num) (deningerDampedXiStepWeight_nonneg _ _))
  · exact (((deningerDampedXiStepWeight_summable a.property).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)).mul_left 3).mul_right _

def deningerDampedXiField (a : {a : ℝ // 1<a}) : XiDivisorL2 :=
  Classical.choose (cauchySeq_tendsto_of_complete (deningerDampedXiPrefix_cauchy a))

theorem deningerDampedXiPrefix_tendsto (a : {a : ℝ // 1<a}) :
    Tendsto (deningerDampedXiPrefix a) atTop (𝓝 (deningerDampedXiField a)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (deningerDampedXiPrefix_cauchy a))

/-- Coordinate continuity identifies the full Hilbert field with the SAME literal source. -/
theorem deningerDampedXiField_apply (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerDampedXiField a q = deningerMeyerStrongLogMellin
      (deningerDampedLogSource ⟨a.val,by linarith [a.property]⟩) (q.1 : ℂ) := by
  have hfield := ((lp.evalCLM ℂ (fun _ : XiZeroCopy => ℂ) 2 q).continuous.tendsto
    (deningerDampedXiField a)).comp (deningerDampedXiPrefix_tendsto a)
  have hsource := deningerDampedLogSource_mellin_tendsto
    ⟨a.val,by linarith [a.property]⟩ (q.1 : ℂ)
    (by linarith [(xi_divisor_support_re_mem_open_unit q.1).1,a.property])
    (by linarith [(xi_divisor_support_re_mem_open_unit q.1).2,a.property])
  change Tendsto (fun n => deningerDampedXiPrefix a n q) atTop (𝓝 (deningerDampedXiField a q)) at hfield
  simp only [deningerDampedXiPrefix_apply] at hfield
  exact tendsto_nhds_unique hfield hsource

/-- No native Xi copy is erased by completing the actual original-prime source. -/
theorem deningerDampedXiField_apply_ne_zero (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerDampedXiField a q ≠ 0 := by
  rw [deningerDampedXiField_apply]
  exact deningerDampedLogSource_mellin_ne_zero _ _
    (by linarith [(xi_divisor_support_re_mem_open_unit q.1).1,a.property])
    (by linarith [(xi_divisor_support_re_mem_open_unit q.1).2,a.property])


/-- Quantitative error of the full original divisor packet. -/
theorem deningerDampedXiPrefix_error_bound (a : {a : ℝ // 1<a}) (n : ℕ) :
    dist (deningerDampedXiPrefix a n) (deningerDampedXiField a) ≤
      ∑' k : ℕ, 3*deningerDampedXiStepWeight a.val (n+k+1)*deningerDampedXiNormBound a := by
  apply dist_le_tsum_of_dist_le_of_tendsto
    (fun j => 3*deningerDampedXiStepWeight a.val (j+1)*deningerDampedXiNormBound a)
  · intro j
    rw [dist_comm,dist_eq_norm]
    apply (deningerDampedXiPrefix_step_increment a j).trans
    exact mul_le_mul_of_nonneg_left (deningerDampedXiPrefix_uniform_bound a j)
      (mul_nonneg (by norm_num) (deningerDampedXiStepWeight_nonneg _ _))
  · exact (((deningerDampedXiStepWeight_summable a.property).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)).mul_left 3).mul_right _
  · exact deningerDampedXiPrefix_tendsto a

/-- The source-forced multiplier on the admitted divisor, without a new normalization. -/
def deningerDampedXiMultiplier (a : ℝ) (s : ℂ) : ℂ :=
  (riemannZeta ((a : ℂ)+s)*riemannZeta ((a : ℂ)+1-s))⁻¹

theorem deningerDampedXiMultiplier_reflect (a : ℝ) (s : ℂ) :
    deningerDampedXiMultiplier a (1-s) = deningerDampedXiMultiplier a s := by
  unfold deningerDampedXiMultiplier
  rw [show (a : ℂ)+(1-s)=(a : ℂ)+1-s by ring,
    show (a : ℂ)+1-(1-s)=(a : ℂ)+s by ring,mul_comm]

theorem deningerDampedXiField_factor (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerDampedXiField a q = deningerDampedXiMultiplier a.val (q.1 : ℂ)*
      reflectedGaussianHorizonGrade q := by
  rw [deningerDampedXiField_apply,deningerDampedLogSource_mellin_eq _ _
    (by linarith [(xi_divisor_support_re_mem_open_unit q.1).1,a.property])
    (by linarith [(xi_divisor_support_re_mem_open_unit q.1).2,a.property])]
  change _ / _ = _⁻¹ * _
  rw [div_eq_mul_inv,mul_comm]
  rfl

theorem deningerDampedXiMultiplier_ne_zero (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerDampedXiMultiplier a.val (q.1 : ℂ) ≠ 0 := by
  have h := deningerDampedXiField_apply_ne_zero a q
  rw [deningerDampedXiField_factor] at h
  exact (mul_ne_zero_iff.mp h).1

theorem deningerDampedXiField_reflect (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerDampedXiField a (xiZeroCopyReflectEquiv q) = deningerDampedXiField a q := by
  rw [deningerDampedXiField_factor,deningerDampedXiField_factor,reflectedGaussianHorizonGrade_reflect]
  change deningerDampedXiMultiplier a.val (1-(q.1 : ℂ))*_ = _
  rw [deningerDampedXiMultiplier_reflect]

/-- The completed Green primitive of the same admitted whole-divisor field. -/
def deningerDampedXiGreenPrimitive (a : {a : ℝ // 1<a}) : XiDivisorL2 :=
  -deningerArithmeticCompletedSourceGreen (deningerDampedXiField a)

theorem deningerDampedXiGreenPrimitive_resolves (a : {a : ℝ // 1<a}) :
    deningerArithmeticCompletedSourceGreen (deningerDampedXiGreenPrimitive a) = deningerDampedXiField a := by
  rw [deningerDampedXiGreenPrimitive,map_neg,deningerArithmeticCompletedSourceGreen_sq,neg_neg]

/-- Original source convergence passes through the fixed completed Green map. -/
theorem deningerDampedXiGreenPrimitive_tendsto (a : {a : ℝ // 1<a}) :
    Tendsto (fun n => -deningerArithmeticCompletedSourceGreen (deningerDampedXiPrefix a n))
      atTop (𝓝 (deningerDampedXiGreenPrimitive a)) :=
  ((deningerArithmeticCompletedSourceGreen.continuous.tendsto _).comp
    (deningerDampedXiPrefix_tendsto a)).neg

theorem deningerDampedXiGreenPrimitive_factor (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerDampedXiGreenPrimitive a q = deningerDampedXiMultiplier a.val (q.1 : ℂ)*
      reflectedGaussianHorizonCompletedGreenPrimitive q := by
  simp only [deningerDampedXiGreenPrimitive,lp.coeFn_neg,Pi.neg_apply,
    deningerArithmeticCompletedSourceGreen_apply,deningerDampedXiField_reflect]
  rw [deningerDampedXiField_factor,reflectedGaussianHorizonCompletedGreenPrimitive_apply]
  ring

/-- Original residue packet and normalizer retain every native multiplicity copy. -/
theorem deningerDampedXiField_original_residue_normalization
    (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    (deningerDampedXiField a q*xiGaussianGammaResidueNormalizer q)*xiGaussianGammaResiduePacket q =
      deningerDampedXiField a q := horizonGrade_mul_normalizer_mul_packet (deningerDampedXiField a) q

def deningerDampedXiGreenProvenance (a : {a : ℝ // 1<a}) : XiDivisorL2 :=
  deningerArithmeticCompletedGreenProvenance (deningerDampedXiField a)

theorem deningerDampedXiGreenProvenance_factor (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerDampedXiGreenProvenance a q = deningerDampedXiMultiplier a.val (q.1 : ℂ)*
      reflectedGaussianHorizonGreenProvenance q := by
  simp only [deningerDampedXiGreenProvenance,reflectedGaussianHorizonGreenProvenance,
    deningerArithmeticCompletedGreenProvenance_apply,deningerArithmeticOrientedHodgeLp_apply,
    deningerArithmeticCompletedRieszConjugation_apply]
  simp only [starRingEnd_apply,star_star]
  rw [deningerDampedXiField_reflect,deningerDampedXiField_factor,
    reflectedGaussianHorizonGradeL2_apply,reflectedGaussianHorizonGrade_reflect]
  ring

def deningerDampedXiVerticalBoundary (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    DeningerGammaSixCofinalSingularGraph :=
  deningerDampedXiGreenProvenance a q • deningerGammaSixCofinalGraphSingularVector

/-- Literal ordinary-prime Tate chain at every native cofinal depth. -/
def deningerDampedXiDegreeOneChain (a : {a : ℝ // 1<a}) (p : Nat.Primes)
    (q : XiZeroCopy) (n : ℕ) : DeningerGammaSixCofinalMeyerTateDegreeOneSource :=
  ccmRationalAdelicOrdinaryPrimeCycleAtom p ⊗ₜ[ℂ]
    (deningerDampedXiGreenProvenance a q • deningerGammaSixCofinalAveragingPacket n)

theorem tendsto_deningerDampedXi_chain (a : {a : ℝ // 1<a}) (p : Nat.Primes) (q : XiZeroCopy) :
    Tendsto (fun n => deningerGammaSixCofinalMeyerTateCompletedDifferential
      (deningerDampedXiDegreeOneChain a p q n)) atTop (𝓝 (deningerDampedXiVerticalBoundary a q)) := by
  simpa [deningerDampedXiDegreeOneChain,deningerDampedXiVerticalBoundary,map_smul] using
    tendsto_deningerGammaSixCofinalFiniteGraphAdmission_averagingPacket.const_smul
      (deningerDampedXiGreenProvenance a q)

theorem deningerDampedXi_finite_physical_readout (a : {a : ℝ // 1<a})
    (p : Nat.Primes) (q : XiZeroCopy) (n : ℕ) :
    deningerGammaSixCofinalGraphPhysicalTransport (2*(q.1 : ℂ).re-1)
      (deningerGammaSixCofinalMeyerTateCompletedDifferential (deningerDampedXiDegreeOneChain a p q n)) =
    deningerDampedXiMultiplier a.val (q.1 : ℂ) •
      deningerGammaSixCofinalGraphPhysicalTransport (2*(q.1 : ℂ).re-1)
        (deningerGammaSixCofinalXiGreenVerticalBoundary q) := by
  rw [deningerDampedXiDegreeOneChain,deningerGammaSixCofinalMeyerTateCompletedDifferential_primeAtom,
    map_smul,map_smul,deningerGammaSixCofinalGraphPhysicalTransport_finiteGraph,
    deningerGammaSixCofinalFiniteActualGammaTransport_averagingPacket,
    deningerDampedXiGreenProvenance_factor,deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary,mul_smul]

theorem deningerDampedXi_completed_physical_readout (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerGammaSixCofinalGraphPhysicalTransport (2*(q.1 : ℂ).re-1) (deningerDampedXiVerticalBoundary a q) =
    deningerDampedXiMultiplier a.val (q.1 : ℂ) •
      deningerGammaSixCofinalGraphPhysicalTransport (2*(q.1 : ℂ).re-1)
        (deningerGammaSixCofinalXiGreenVerticalBoundary q) := by
  rw [deningerDampedXiVerticalBoundary,map_smul,deningerGammaSixCofinalGraphPhysicalTransport_singularVector,
    deningerDampedXiGreenProvenance_factor,deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary,mul_smul]

/-- The completed original-prime source removes none of the old physical readout. -/
theorem deningerDampedXi_physical_readout_eq_zero_iff (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerGammaSixCofinalGraphPhysicalTransport (2*(q.1 : ℂ).re-1) (deningerDampedXiVerticalBoundary a q) = 0 ↔
      deningerGammaSixCofinalGraphPhysicalTransport (2*(q.1 : ℂ).re-1)
        (deningerGammaSixCofinalXiGreenVerticalBoundary q) = 0 := by
  rw [deningerDampedXi_completed_physical_readout,smul_eq_zero,or_iff_right (deningerDampedXiMultiplier_ne_zero a q)]


/-- The fixed physical reader retains exactly the original critical-line discriminator. -/
theorem deningerDampedXi_physical_readout_eq_zero_iff_criticalLine
    (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerGammaSixCofinalGraphPhysicalTransport (2*(q.1 : ℂ).re-1)
      (deningerDampedXiVerticalBoundary a q) = 0 ↔ (q.1 : ℂ).re = 1/2 := by
  rw [deningerDampedXi_physical_readout_eq_zero_iff,
    deningerGammaSixCofinalGraphPhysicalTransport_xiGreenBoundary_eq_zero_iff]

/-- All native Xi copies in the original singular Gamma graph norm. -/
abbrev DeningerXiFullGammaGraph := lp (fun _ : XiZeroCopy => DeningerGammaSixCofinalSingularGraph) 2

/-- Coefficient-faithful spread of one graph vector over the whole original divisor. -/
def deningerXiGraphSpread (x : XiDivisorL2) (v : DeningerGammaSixCofinalSingularGraph) :
    DeningerXiFullGammaGraph :=
  ⟨fun q => x q • v, Memℓp.mono ((lp.memℓp x).norm.const_smul ‖v‖) (fun q => by
    simp only [norm_smul,Pi.smul_apply,smul_eq_mul]
    exact le_of_eq (mul_comm _ _))⟩

private theorem deningerXiGraphSpread_norm_le (x : XiDivisorL2)
    (v : DeningerGammaSixCofinalSingularGraph) :
    ‖deningerXiGraphSpread x v‖ ≤ ‖x‖*‖v‖ := by
  calc
    _ ≤ ‖(‖v‖ : ℂ) • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro q
      change ‖x q • v‖ ≤ ‖((‖v‖ : ℂ) • x) q‖
      simp only [norm_smul,lp.coeFn_smul,Pi.smul_apply,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (norm_nonneg v)]
      exact le_of_eq (mul_comm _ _)
    _ = _ := by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg v),mul_comm]

def deningerXiGraphSpreadCLM (x : XiDivisorL2) :
    DeningerGammaSixCofinalSingularGraph →L[ℂ] DeningerXiFullGammaGraph :=
  LinearMap.mkContinuous
    { toFun := deningerXiGraphSpread x
      map_add' := by
        intro v w
        apply lp.ext
        funext q
        exact smul_add (x q) v w
      map_smul' := by
        intro c v
        apply lp.ext
        funext q
        change x q • (c • v) = c • (x q • v)
        rw [smul_smul,smul_smul,mul_comm] }
    ‖x‖ (deningerXiGraphSpread_norm_le x)

/-- Full graph image of actual original-prime Tate chains, at one common native depth. -/
def deningerDampedXiFullTateGraphPrefix (a : {a : ℝ // 1<a}) (n : ℕ) : DeningerXiFullGammaGraph :=
  deningerXiGraphSpreadCLM (deningerDampedXiGreenProvenance a)
    (deningerGammaSixCofinalFiniteGraphAdmission (deningerGammaSixCofinalAveragingPacket n))

theorem deningerDampedXiFullTateGraphPrefix_apply
    (a : {a : ℝ // 1<a}) (p : Nat.Primes) (n : ℕ) (q : XiZeroCopy) :
    deningerDampedXiFullTateGraphPrefix a n q =
      deningerGammaSixCofinalMeyerTateCompletedDifferential (deningerDampedXiDegreeOneChain a p q n) := by
  change deningerDampedXiGreenProvenance a q •
    deningerGammaSixCofinalFiniteGraphAdmission (deningerGammaSixCofinalAveragingPacket n) = _
  rw [deningerDampedXiDegreeOneChain,deningerGammaSixCofinalMeyerTateCompletedDifferential_primeAtom,map_smul]

def deningerDampedXiFullGraphBoundary (a : {a : ℝ // 1<a}) : DeningerXiFullGammaGraph :=
  deningerXiGraphSpreadCLM (deningerDampedXiGreenProvenance a) deningerGammaSixCofinalGraphSingularVector

@[simp] theorem deningerDampedXiFullGraphBoundary_apply
    (a : {a : ℝ // 1<a}) (q : XiZeroCopy) :
    deningerDampedXiFullGraphBoundary a q = deningerDampedXiVerticalBoundary a q := rfl

/-- Actual Tate chains converge in the complete zero-indexed Gamma graph, with every copy retained. -/
theorem deningerDampedXiFullTateGraphPrefix_tendsto (a : {a : ℝ // 1<a}) :
    Tendsto (deningerDampedXiFullTateGraphPrefix a) atTop (𝓝 (deningerDampedXiFullGraphBoundary a)) :=
  ((deningerXiGraphSpreadCLM (deningerDampedXiGreenProvenance a)).continuous.tendsto _).comp
    tendsto_deningerGammaSixCofinalFiniteGraphAdmission_averagingPacket

end RHTower
