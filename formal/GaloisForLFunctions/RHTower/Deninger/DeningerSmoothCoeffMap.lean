import GaloisForLFunctions.RHTower.Deninger.DeningerSmoothPeriodic

/-!
# The coefficient map of a smooth periodic function

Decay of order `k + 2` beats the weight `(1 + |n|)^k` with two powers to spare, so the weighted
sums of the Fourier coefficients of a smooth periodic function all converge: the coefficients lie
in the nuclear Köthe space of rapidly decreasing sequences.  The coefficient map is linear, the
integral defining it being linear in the function.

* `deningerSmoothPeriodic_coeff_summable` : all weighted sums converge.
* `deningerSmoothCoeff` : **the coefficient map into the Köthe space.**
-/

namespace RHTower

section CoeffMap

variable {T : ℝ}

theorem deningerSmoothPeriodic_integrable (f : DeningerSmoothPeriodic T) (n : ℤ) :
    IntervalIntegrable (fun x => deningerFourierKernel T n x * (f : ℝ → ℂ) x)
      MeasureTheory.volume 0 T := by
  refine Continuous.intervalIntegrable ?_ _ _
  refine Continuous.mul ?_ (deningerSmoothPeriodic_contDiff f).continuous
  refine Continuous.cexp ?_
  fun_prop

theorem deningerFourierCoeff_add (f g : ℝ → ℂ) (n : ℤ)
    (hf : IntervalIntegrable (fun x => deningerFourierKernel T n x * f x)
      MeasureTheory.volume 0 T)
    (hg : IntervalIntegrable (fun x => deningerFourierKernel T n x * g x)
      MeasureTheory.volume 0 T) :
    deningerFourierCoeff T (f + g) n
      = deningerFourierCoeff T f n + deningerFourierCoeff T g n := by
  rw [deningerFourierCoeff, deningerFourierCoeff, deningerFourierCoeff]
  have hfun : ∀ x, deningerFourierKernel T n x * (f + g) x
      = deningerFourierKernel T n x * f x + deningerFourierKernel T n x * g x := by
    intro x
    show deningerFourierKernel T n x * (f x + g x) = _
    ring
  rw [intervalIntegral.integral_congr fun x _ => hfun x, intervalIntegral.integral_add hf hg]
  ring

theorem deningerFourierCoeff_smul (c : ℂ) (f : ℝ → ℂ) (n : ℤ) :
    deningerFourierCoeff T (c • f) n = c * deningerFourierCoeff T f n := by
  rw [deningerFourierCoeff, deningerFourierCoeff]
  have hfun : ∀ x, deningerFourierKernel T n x * (c • f) x
      = c * (deningerFourierKernel T n x * f x) := by
    intro x
    show deningerFourierKernel T n x * (c * f x) = _
    ring
  rw [intervalIntegral.integral_congr fun x _ => hfun x, intervalIntegral.integral_const_mul]
  ring

/-- **All weighted sums of the coefficients of a smooth periodic function converge.** -/
theorem deningerSmoothPeriodic_coeff_summable (hT : 0 < T) (f : DeningerSmoothPeriodic T)
    (k : ℕ) :
    Summable fun n : ℤ => (1 + |(n : ℝ)|) ^ k * ‖deningerFourierCoeff T (f : ℝ → ℂ) n‖ := by
  classical
  obtain ⟨M, hM⟩ := deningerSmoothPeriodic_coeff_decay hT f (k + 2)
  set M' : ℝ := max M 0 with hM'
  have hM'nonneg : 0 ≤ M' := le_max_right _ _
  have hdecay : ∀ n : ℤ, n ≠ 0 →
      ‖deningerFourierCoeff T (f : ℝ → ℂ) n‖
        ≤ (T / (2 * Real.pi * |(n : ℝ)|)) ^ (k + 2) * M' := by
    intro n hn
    refine le_trans (hM n hn) ?_
    have hpow : (0 : ℝ) ≤ (T / (2 * Real.pi * |(n : ℝ)|)) ^ (k + 2) := by positivity
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hpow
  set C : ℝ := 2 ^ k * 4 * (T / (2 * Real.pi)) ^ (k + 2) * M' with hC
  have hbound : ∀ n : ℤ, n ≠ 0 →
      (1 + |(n : ℝ)|) ^ k * ‖deningerFourierCoeff T (f : ℝ → ℂ) n‖
        ≤ C * (1 + |(n : ℝ)|) ^ (-(2 : ℤ)) := by
    intro n hn
    have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by exact_mod_cast hn)
    have habs0 : (0 : ℝ) < |(n : ℝ)| := lt_of_lt_of_le one_pos habs
    have hle2 : 1 + |(n : ℝ)| ≤ 2 * |(n : ℝ)| := by linarith
    have hstep1 : (1 + |(n : ℝ)|) ^ k * ‖deningerFourierCoeff T (f : ℝ → ℂ) n‖
        ≤ (1 + |(n : ℝ)|) ^ k * ((T / (2 * Real.pi * |(n : ℝ)|)) ^ (k + 2) * M') := by
      refine mul_le_mul_of_nonneg_left (hdecay n hn) ?_
      positivity
    refine le_trans hstep1 ?_
    have hsplit : (T / (2 * Real.pi * |(n : ℝ)|)) ^ (k + 2)
        = (T / (2 * Real.pi)) ^ (k + 2) * (|(n : ℝ)| ^ (k + 2))⁻¹ := by
      rw [div_mul_eq_div_div, div_pow]
      field_simp
    have hpowsplit : (|(n : ℝ)| ^ (k + 2))⁻¹ = (|(n : ℝ)| ^ k)⁻¹ * (|(n : ℝ)| ^ 2)⁻¹ := by
      rw [pow_add, mul_inv]
    have hinv : (1 + |(n : ℝ)|) ^ (-(2 : ℤ)) = ((1 + |(n : ℝ)|) ^ 2)⁻¹ := by
      rw [zpow_neg, zpow_two, sq]
    have hpowle : (1 + |(n : ℝ)|) ^ k ≤ 2 ^ k * |(n : ℝ)| ^ k := by
      calc (1 + |(n : ℝ)|) ^ k ≤ (2 * |(n : ℝ)|) ^ k := pow_le_pow_left₀ (by positivity) hle2 k
        _ = 2 ^ k * |(n : ℝ)| ^ k := by rw [mul_pow]
    have hratio : (1 + |(n : ℝ)|) ^ k * (|(n : ℝ)| ^ k)⁻¹ ≤ 2 ^ k := by
      rw [mul_inv_le_iff₀ (by positivity)]
      exact hpowle
    have hfour : (|(n : ℝ)| ^ 2)⁻¹ ≤ 4 * ((1 + |(n : ℝ)|) ^ 2)⁻¹ := by
      have h1 : (0 : ℝ) < |(n : ℝ)| ^ 2 := by positivity
      have h2 : (0 : ℝ) < (1 + |(n : ℝ)|) ^ 2 := by positivity
      calc (|(n : ℝ)| ^ 2)⁻¹ = 1 / |(n : ℝ)| ^ 2 := by rw [one_div]
        _ ≤ 4 / (1 + |(n : ℝ)|) ^ 2 := by
            rw [div_le_div_iff₀ h1 h2]
            nlinarith
        _ = 4 * ((1 + |(n : ℝ)|) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
    rw [hsplit, hpowsplit, hinv, hC]
    have hA : (0 : ℝ) ≤ (T / (2 * Real.pi)) ^ (k + 2) := by positivity
    calc (1 + |(n : ℝ)|) ^ k * ((T / (2 * Real.pi)) ^ (k + 2)
          * ((|(n : ℝ)| ^ k)⁻¹ * (|(n : ℝ)| ^ 2)⁻¹) * M')
        = ((1 + |(n : ℝ)|) ^ k * (|(n : ℝ)| ^ k)⁻¹) * ((|(n : ℝ)| ^ 2)⁻¹)
            * ((T / (2 * Real.pi)) ^ (k + 2) * M') := by ring
      _ ≤ (2 ^ k) * (4 * ((1 + |(n : ℝ)|) ^ 2)⁻¹)
            * ((T / (2 * Real.pi)) ^ (k + 2) * M') := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine mul_le_mul hratio hfour (by positivity) (by positivity)
      _ = 2 ^ k * 4 * (T / (2 * Real.pi)) ^ (k + 2) * M' * ((1 + |(n : ℝ)|) ^ 2)⁻¹ := by ring
  have hsummable_compl : Summable fun n : {n : ℤ // n ∉ ({0} : Finset ℤ)} =>
      (1 + |((n : ℤ) : ℝ)|) ^ k * ‖deningerFourierCoeff T (f : ℝ → ℂ) (n : ℤ)‖ := by
    have hdom : Summable fun n : {n : ℤ // n ∉ ({0} : Finset ℤ)} =>
        C * (1 + |((n : ℤ) : ℝ)|) ^ (-(2 : ℤ)) :=
      (deningerFourier_summable_inv_sq.mul_left C).subtype _
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hdom
    exact hbound (n : ℤ) (by simpa using n.2)
  exact (Finset.summable_compl_iff ({0} : Finset ℤ)).mp hsummable_compl

/-- **The coefficient map** of a smooth periodic function into the Köthe space of rapidly
decreasing sequences. -/
noncomputable def deningerSmoothCoeff (hT : 0 < T) :
    DeningerSmoothPeriodic T →ₗ[ℂ] DeningerKotheCarrier ℂ deningerFourierWeights where
  toFun f := ⟨fun n => deningerFourierCoeff T (f : ℝ → ℂ) n, fun k =>
    deningerSmoothPeriodic_coeff_summable hT f k⟩
  map_add' f g := by
    refine Subtype.ext (funext fun n => ?_)
    exact deningerFourierCoeff_add (f : ℝ → ℂ) (g : ℝ → ℂ) n
      (deningerSmoothPeriodic_integrable f n) (deningerSmoothPeriodic_integrable g n)
  map_smul' c f := by
    refine Subtype.ext (funext fun n => ?_)
    exact deningerFourierCoeff_smul c (f : ℝ → ℂ) n

@[simp]
theorem deningerSmoothCoeff_apply (hT : 0 < T) (f : DeningerSmoothPeriodic T) (n : ℤ) :
    ((deningerSmoothCoeff hT f : DeningerKotheCarrier ℂ deningerFourierWeights) : ℤ → ℂ) n
      = deningerFourierCoeff T (f : ℝ → ℂ) n := rfl

end CoeffMap

end RHTower
