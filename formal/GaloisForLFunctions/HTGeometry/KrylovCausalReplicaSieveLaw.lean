import Mathlib

/-!
# Krylov causal replica sieve

Finite spectral amplitudes whose moments vanish through order `K` obey a
factorial pointwise time-delay bound.  Raising to replica order `r` and
integrating on a symmetric finite window amplifies this delay to an explicit
`2r`th-moment bound.  No level-spacing or nonresonance assumption is used.
-/

open Set

noncomputable section

open Complex

namespace GaloisForLFunctions.HTGeometry

theorem iteratedDeriv_cexp_complex_mul_real (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp ((t : ℂ) * c)) =
      fun t : ℝ => c ^ n * Complex.exp ((t : ℂ) * c) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have hinner : HasDerivAt (fun x : ℝ => (x : ℂ) * c) c t := by
        simpa using Complex.ofRealCLM.hasDerivAt.mul_const c
      have h := hinner.cexp.const_mul (c ^ n)
      simpa [pow_succ', mul_assoc, mul_comm, mul_left_comm] using h.deriv

def finiteRealTimeComplexAmplitude
    {I : Type*} [Fintype I]
    (coefficient : I → ℂ) (frequency : I → ℝ) (t : ℝ) : ℂ :=
  ∑ i, coefficient i * Complex.exp ((t : ℂ) * (Complex.I * frequency i))

theorem finiteRealTimeComplexAmplitude_contDiff
    {I : Type*} [Fintype I]
    (coefficient : I → ℂ) (frequency : I → ℝ) :
    ContDiff ℝ ⊤ (finiteRealTimeComplexAmplitude coefficient frequency) := by
  unfold finiteRealTimeComplexAmplitude
  apply ContDiff.sum
  intro i hi
  have hinner : ContDiff ℝ ⊤
      (fun t : ℝ => (t : ℂ) * (Complex.I * frequency i)) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  exact contDiff_const.mul hinner.cexp

theorem iteratedDeriv_finiteRealTimeComplexAmplitude
    {I : Type*} [Fintype I]
    (coefficient : I → ℂ) (frequency : I → ℝ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (finiteRealTimeComplexAmplitude coefficient frequency) t =
      ∑ i, coefficient i * (Complex.I * frequency i) ^ k *
        Complex.exp ((t : ℂ) * (Complex.I * frequency i)) := by
  classical
  unfold finiteRealTimeComplexAmplitude
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_const_mul_field]
    rw [congrFun (iteratedDeriv_cexp_complex_mul_real
      (Complex.I * frequency i) k) t]
    ring
  · intro i hi
    have hinner : ContDiff ℝ ⊤
        (fun t : ℝ => (t : ℂ) * (Complex.I * frequency i)) :=
      Complex.ofRealCLM.contDiff.mul contDiff_const
    have hfull : ContDiff ℝ ⊤
        (fun t : ℝ => coefficient i *
          Complex.exp ((t : ℂ) * (Complex.I * frequency i))) :=
      contDiff_const.mul hinner.cexp
    exact hfull.contDiffAt.of_le le_top

theorem norm_of_zero_taylor_jet_le
    {f : ℝ → ℂ} {K : ℕ} {T C t : ℝ}
    (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    (hf : ContDiffOn ℝ (K + 1) f (Icc 0 T))
    (hzero : ∀ k ≤ K, iteratedDerivWithin k f (Icc 0 T) 0 = 0)
    (hC : ∀ y ∈ Icc 0 T,
      ‖iteratedDerivWithin (K + 1) f (Icc 0 T) y‖ ≤ C) :
    ‖f t‖ ≤ C * t ^ (K + 1) / K.factorial := by
  have hrem := taylor_mean_remainder_bound hT hf ht hC
  have hTaylor : taylorWithinEval f K (Icc 0 T) 0 t = 0 := by
    unfold taylorWithinEval taylorWithin taylorCoeffWithin
    simp only [map_sum, PolynomialModule.comp_eval,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.sum_eq_zero
    intro k hk
    rw [hzero k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    simp
  simpa [hTaylor, sub_zero] using hrem

theorem norm_of_zero_taylor_jet_le_factorial
    {f : ℝ → ℂ} {K : ℕ} {C t : ℝ}
    (ht : 0 ≤ t)
    (hf : ContDiffOn ℝ (K + 1) f (Icc 0 t))
    (hzero : ∀ k ≤ K, iteratedDerivWithin k f (Icc 0 t) 0 = 0)
    (hC : ∀ y ∈ Icc 0 t,
      ‖iteratedDerivWithin (K + 1) f (Icc 0 t) y‖ ≤ C) :
    ‖f t‖ ≤ C * t ^ (K + 1) / (K + 1).factorial := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · have hz := hzero 0 (Nat.zero_le K)
    simpa using hz
  have hTaylor : taylorWithinEval f K (Icc 0 t) 0 t = 0 := by
    unfold taylorWithinEval taylorWithin taylorCoeffWithin
    simp only [map_sum, PolynomialModule.comp_eval,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.sum_eq_zero
    intro k hk
    rw [hzero k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    simp
  have hrem := taylor_integral_remainder (n := K) (x := t) (x₀ := 0) (by
    simpa [uIcc_of_le ht.le] using hf)
  rw [uIcc_of_le ht.le, hTaylor, sub_zero] at hrem
  rw [hrem]
  have hcontDeriv : ContinuousOn
      (fun y => iteratedDerivWithin (K + 1) f (Icc 0 t) y) (Icc 0 t) :=
    hf.continuousOn_iteratedDerivWithin rfl.le
      (uniqueDiffOn_Icc ht)
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume) ht.le
    (f := fun y => ((t - y) ^ K / K.factorial) •
      iteratedDerivWithin (K + 1) f (Icc 0 t) y)
  have hmono :
      (∫ y in (0 : ℝ)..t,
          ‖((t - y) ^ K / K.factorial) •
            iteratedDerivWithin (K + 1) f (Icc 0 t) y‖) ≤
        ∫ y in (0 : ℝ)..t, C * (t - y) ^ K / K.factorial := by
    apply intervalIntegral.integral_mono_on ht.le
    · have hscalar : Continuous
          (fun y : ℝ => (t - y) ^ K / (K.factorial : ℝ)) := by
        fun_prop
      have hc : ContinuousOn
          (fun u => ‖((t - u) ^ K / (K.factorial : ℝ)) •
            iteratedDerivWithin (K + 1) f (Icc 0 t) u‖) (uIcc 0 t) := by
        simpa [uIcc_of_le ht.le] using
          (hscalar.continuousOn.smul hcontDeriv).norm
      exact hc.intervalIntegrable
    · exact ((continuous_const.mul ((continuous_const.sub continuous_id).pow K)).div_const
        (K.factorial : ℝ)).intervalIntegrable 0 t
    · intro y hy
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      · calc
          (t - y) ^ K / (K.factorial : ℝ) *
              ‖iteratedDerivWithin (K + 1) f (Icc 0 t) y‖
              ≤ (t - y) ^ K / (K.factorial : ℝ) * C :=
            mul_le_mul_of_nonneg_left (hC y hy)
              (div_nonneg (pow_nonneg (sub_nonneg.mpr hy.2) K) (by positivity))
          _ = C * (t - y) ^ K / (K.factorial : ℝ) := by ring
      · exact div_nonneg (pow_nonneg (sub_nonneg.mpr hy.2) K) (by positivity)
  have hmodel :
      (∫ y in (0 : ℝ)..t, C * (t - y) ^ K / K.factorial) =
        C * t ^ (K + 1) / (K + 1).factorial := by
    calc
      (∫ y in (0 : ℝ)..t, C * (t - y) ^ K / K.factorial) =
          ∫ y in (0 : ℝ)..t, (C / (K.factorial : ℝ)) * (t - y) ^ K := by
            apply intervalIntegral.integral_congr
            intro y hy
            ring
      _ = (C / (K.factorial : ℝ)) * ∫ y in (0 : ℝ)..t, (t - y) ^ K := by
            rw [intervalIntegral.integral_const_mul]
      _ = C * t ^ (K + 1) / (K + 1).factorial := by
            rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ K) t]
            rw [sub_self, sub_zero, integral_pow, Nat.factorial_succ]
            push_cast
            field_simp
            simp
  linarith

theorem norm_finiteRealTimeComplexAmplitude_le_of_moment_null
    {I : Type*} [Fintype I]
    {coefficient : I → ℂ} {frequency : I → ℝ}
    {K : ℕ} {T A B t : ℝ}
    (ht : t ∈ Icc 0 T) (hA : ∑ i, ‖coefficient i‖ ≤ A)
    (hB : 0 ≤ B) (hfrequency : ∀ i, ‖frequency i‖ ≤ B)
    (hmoment : ∀ k ≤ K,
      ∑ i, coefficient i * (frequency i : ℂ) ^ k = 0) :
    ‖finiteRealTimeComplexAmplitude coefficient frequency t‖ ≤
      (A * B ^ (K + 1)) * t ^ (K + 1) / (K + 1).factorial := by
  classical
  let F := finiteRealTimeComplexAmplitude coefficient frequency
  have hfull : ContDiff ℝ ⊤ F :=
    finiteRealTimeComplexAmplitude_contDiff coefficient frequency
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · have hzero := hmoment 0 (Nat.zero_le K)
    simp only [pow_zero, mul_one] at hzero
    simp [finiteRealTimeComplexAmplitude, hzero]
  have hunique : UniqueDiffOn ℝ (Icc 0 t) := uniqueDiffOn_Icc htpos
  apply norm_of_zero_taylor_jet_le_factorial ht.1 (hfull.contDiffOn.of_le le_top)
  · intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv hunique
      (hfull.contDiffAt.of_le le_top) (left_mem_Icc.mpr htpos.le)]
    rw [iteratedDeriv_finiteRealTimeComplexAmplitude]
    simp only [ofReal_zero, zero_mul, Complex.exp_zero, mul_one, mul_pow]
    calc
      (∑ x, coefficient x * (Complex.I ^ k * (frequency x : ℂ) ^ k)) =
          Complex.I ^ k * ∑ x, coefficient x * (frequency x : ℂ) ^ k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := by rw [hmoment k hk, mul_zero]
  · intro y hy
    rw [iteratedDerivWithin_eq_iteratedDeriv hunique
      (hfull.contDiffAt.of_le le_top) hy]
    rw [iteratedDeriv_finiteRealTimeComplexAmplitude]
    calc
      ‖∑ i, coefficient i * (Complex.I * frequency i) ^ (K + 1) *
          Complex.exp ((y : ℂ) * (Complex.I * frequency i))‖
          ≤ ∑ i, ‖coefficient i * (Complex.I * frequency i) ^ (K + 1) *
            Complex.exp ((y : ℂ) * (Complex.I * frequency i))‖ := norm_sum_le _ _
      _ = ∑ i, ‖coefficient i‖ * ‖frequency i‖ ^ (K + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
        simp
      _ ≤ ∑ i, ‖coefficient i‖ * B ^ (K + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg (frequency i)) (hfrequency i) _) (norm_nonneg _)
      _ = (∑ i, ‖coefficient i‖) * B ^ (K + 1) := by
        rw [Finset.sum_mul]
      _ ≤ A * B ^ (K + 1) := by
        gcongr

theorem norm_finiteRealTimeComplexAmplitude_le_of_moment_null_abs
    {I : Type*} [Fintype I]
    {coefficient : I → ℂ} {frequency : I → ℝ}
    {K : ℕ} {T A B t : ℝ}
    (ht : |t| ≤ T) (hA : ∑ i, ‖coefficient i‖ ≤ A)
    (hB : 0 ≤ B) (hfrequency : ∀ i, ‖frequency i‖ ≤ B)
    (hmoment : ∀ k ≤ K,
      ∑ i, coefficient i * (frequency i : ℂ) ^ k = 0) :
    ‖finiteRealTimeComplexAmplitude coefficient frequency t‖ ≤
      (A * B ^ (K + 1)) * |t| ^ (K + 1) / (K + 1).factorial := by
  by_cases hnonneg : 0 ≤ t
  · have htIcc : t ∈ Icc 0 T := ⟨hnonneg, (le_abs_self t).trans ht⟩
    simpa [abs_of_nonneg hnonneg] using
      norm_finiteRealTimeComplexAmplitude_le_of_moment_null
        htIcc hA hB hfrequency hmoment
  · have htneg : t < 0 := lt_of_not_ge hnonneg
    have hnegIcc : -t ∈ Icc 0 T := by
      constructor
      · linarith
      · simpa [abs_of_neg htneg] using ht
    have hfrequencyNeg : ∀ i, ‖-frequency i‖ ≤ B := by
      intro i
      simpa using hfrequency i
    have hmomentNeg : ∀ k ≤ K,
        ∑ i, coefficient i * ((-frequency i : ℝ) : ℂ) ^ k = 0 := by
      intro k hk
      calc
        (∑ i, coefficient i * ((-frequency i : ℝ) : ℂ) ^ k) =
            ((-1 : ℂ) ^ k) *
              ∑ i, coefficient i * (frequency i : ℂ) ^ k := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i hi
                push_cast
                rw [neg_pow]
                ring
        _ = 0 := by rw [hmoment k hk, mul_zero]
    have hbound := norm_finiteRealTimeComplexAmplitude_le_of_moment_null
      (coefficient := coefficient) (frequency := fun i => -frequency i)
      hnegIcc hA hB hfrequencyNeg hmomentNeg
    have hamp : finiteRealTimeComplexAmplitude coefficient
        (fun i => -frequency i) (-t) =
        finiteRealTimeComplexAmplitude coefficient frequency t := by
      unfold finiteRealTimeComplexAmplitude
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      push_cast
      ring
    simpa [hamp, abs_of_neg htneg] using hbound

theorem integral_abs_pow_neg_to_pos (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, |t| ^ m) =
      2 * T ^ (m + 1) / ((m : ℝ) + 1) := by
  have hcont : Continuous (fun t : ℝ => |t| ^ m) := continuous_abs.pow m
  have hpos : (∫ t in (0 : ℝ)..T, |t| ^ m) =
      T ^ (m + 1) / ((m : ℝ) + 1) := by
    calc
      (∫ t in (0 : ℝ)..T, |t| ^ m) = ∫ t in (0 : ℝ)..T, t ^ m := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT] at ht
        change |t| ^ m = t ^ m
        rw [abs_of_nonneg ht.1]
      _ = T ^ (m + 1) / ((m : ℝ) + 1) := by
        rw [integral_pow]
        simp
  have hneg : (∫ t in -T..(0 : ℝ), |t| ^ m) =
      ∫ t in (0 : ℝ)..T, |t| ^ m := by
    symm
    calc
      (∫ t in (0 : ℝ)..T, |t| ^ m) = ∫ t in (0 : ℝ)..T, |-t| ^ m := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp
      _ = ∫ t in -T..(0 : ℝ), |t| ^ m := by
        simpa using intervalIntegral.integral_comp_neg
          (f := fun t : ℝ => |t| ^ m) (a := 0) (b := T)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-T) 0) (hcont.intervalIntegrable 0 T)]
  rw [hneg, hpos]
  ring

theorem integral_norm_pow_finiteRealTimeComplexAmplitude_le_of_moment_null
    {I : Type*} [Fintype I]
    {coefficient : I → ℂ} {frequency : I → ℝ}
    {K r : ℕ} {T A B : ℝ}
    (hT : 0 < T) (hA : ∑ i, ‖coefficient i‖ ≤ A)
    (hB : 0 ≤ B) (hfrequency : ∀ i, ‖frequency i‖ ≤ B)
    (hmoment : ∀ k ≤ K,
      ∑ i, coefficient i * (frequency i : ℂ) ^ k = 0) :
    (∫ t in -T..T,
      ‖finiteRealTimeComplexAmplitude coefficient frequency t‖ ^ (2 * r)) ≤
      2 * (A * B ^ (K + 1) / (K + 1).factorial) ^ (2 * r) *
        T ^ (2 * r * (K + 1) + 1) /
          (((2 * r * (K + 1) : ℕ) : ℝ) + 1) := by
  classical
  let F := finiteRealTimeComplexAmplitude coefficient frequency
  let D : ℝ := A * B ^ (K + 1) / (K + 1).factorial
  have hAnonneg : 0 ≤ A := (Finset.sum_nonneg fun i hi => norm_nonneg _).trans hA
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hAnonneg (pow_nonneg hB _)) (by positivity)
  have hpoint : ∀ t ∈ Icc (-T) T,
      ‖F t‖ ^ (2 * r) ≤ D ^ (2 * r) * |t| ^ (2 * r * (K + 1)) := by
    intro t ht
    have htAbs : |t| ≤ T := (abs_le).mpr ⟨by linarith [ht.1], ht.2⟩
    have hb := norm_finiteRealTimeComplexAmplitude_le_of_moment_null_abs
      (coefficient := coefficient) (frequency := frequency)
      htAbs hA hB hfrequency hmoment
    have hb' : ‖F t‖ ≤ D * |t| ^ (K + 1) := by
      calc
        ‖F t‖ ≤ (A * B ^ (K + 1)) * |t| ^ (K + 1) /
            (K + 1).factorial := hb
        _ = D * |t| ^ (K + 1) := by
          dsimp [D]
          ring
    calc
      ‖F t‖ ^ (2 * r) ≤ (D * |t| ^ (K + 1)) ^ (2 * r) :=
        pow_le_pow_left₀ (norm_nonneg _) hb' _
      _ = D ^ (2 * r) * |t| ^ (2 * r * (K + 1)) := by
        rw [mul_pow, ← pow_mul]
        rw [Nat.mul_comm (K + 1) (2 * r)]
  have hcontF : Continuous F :=
    (finiteRealTimeComplexAmplitude_contDiff coefficient frequency).continuous
  have hmono :
      (∫ t in -T..T, ‖F t‖ ^ (2 * r)) ≤
        ∫ t in -T..T, D ^ (2 * r) * |t| ^ (2 * r * (K + 1)) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (hcontF.norm.pow _).intervalIntegrable (-T) T
    · exact (continuous_const.mul (continuous_abs.pow _)).intervalIntegrable (-T) T
    · exact hpoint
  calc
    (∫ t in -T..T, ‖F t‖ ^ (2 * r))
        ≤ ∫ t in -T..T, D ^ (2 * r) * |t| ^ (2 * r * (K + 1)) := hmono
    _ = D ^ (2 * r) * ∫ t in -T..T, |t| ^ (2 * r * (K + 1)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 2 * D ^ (2 * r) * T ^ (2 * r * (K + 1) + 1) /
          (((2 * r * (K + 1) : ℕ) : ℝ) + 1) := by
      rw [integral_abs_pow_neg_to_pos (2 * r * (K + 1)) hT.le]
      ring
    _ = 2 * (A * B ^ (K + 1) / (K + 1).factorial) ^ (2 * r) *
          T ^ (2 * r * (K + 1) + 1) /
            (((2 * r * (K + 1) : ℕ) : ℝ) + 1) := by rfl

theorem uniformMoment_finiteRealTimeComplexAmplitude_le_of_moment_null
    {I : Type*} [Fintype I]
    {coefficient : I → ℂ} {frequency : I → ℝ}
    {K r : ℕ} {T A B : ℝ}
    (hT : 0 < T) (hA : ∑ i, ‖coefficient i‖ ≤ A)
    (hB : 0 ≤ B) (hfrequency : ∀ i, ‖frequency i‖ ≤ B)
    (hmoment : ∀ k ≤ K,
      ∑ i, coefficient i * (frequency i : ℂ) ^ k = 0) :
    (∫ t in -T..T,
      ‖finiteRealTimeComplexAmplitude coefficient frequency t‖ ^ (2 * r)) /
        (2 * T) ≤
      ((A * B ^ (K + 1) / (K + 1).factorial) * T ^ (K + 1)) ^ (2 * r) /
        (((2 * r * (K + 1) : ℕ) : ℝ) + 1) := by
  have hi := integral_norm_pow_finiteRealTimeComplexAmplitude_le_of_moment_null
    (coefficient := coefficient) (frequency := frequency)
    hT hA hB hfrequency hmoment (r := r)
  apply (div_le_iff₀ (by positivity : 0 < 2 * T)).2
  calc
    (∫ t in -T..T,
        ‖finiteRealTimeComplexAmplitude coefficient frequency t‖ ^ (2 * r))
        ≤ 2 * (A * B ^ (K + 1) / (K + 1).factorial) ^ (2 * r) *
          T ^ (2 * r * (K + 1) + 1) /
            (((2 * r * (K + 1) : ℕ) : ℝ) + 1) := hi
    _ = (((A * B ^ (K + 1) / (K + 1).factorial) * T ^ (K + 1)) ^ (2 * r) /
          (((2 * r * (K + 1) : ℕ) : ℝ) + 1)) * (2 * T) := by
      rw [mul_pow, ← pow_mul]
      rw [Nat.mul_comm (K + 1) (2 * r)]
      rw [pow_succ]
      ring

end GaloisForLFunctions.HTGeometry
