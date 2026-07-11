import GaloisForLFunctions.RHTower.XiOrderOne
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Order-one growth of the entire completed zeta `Λ₀`

The entire completion `Λ₀ = completedRiemannZeta₀` is, by mathlib's construction, half the Mellin
transform of the modified even theta kernel `F = (hurwitzEvenFEPair 0).f_modif` evaluated at `s/2`:

`completedRiemannZeta₀ s = mellin F (s/2) / 2`.

Because `‖(t : ℂ) ^ (w-1)‖ = t ^ (Re w - 1)` is independent of `Im w`, the modulus of the Mellin
transform is controlled by the purely real integral `∫₀^∞ t ^ (Re w - 1) ‖F t‖ dt`.  The kernel
decays exponentially at `∞` (Jacobi theta, `isBigO_atTop_evenKernel_sub`) and, after the theta
transformation `F t = t^{-1/2}(cosKernel 0 (1/t) - 1)` for `t < 1`, at `0` as well
(`isBigO_atTop_cosKernel_sub`), so that integral converges for every exponent and grows like an
order-one envelope in `Re w`.  This yields, unconditionally, the Hadamard order-one bound

`‖Λ₀ s‖ ≤ exp (C · (1 + ‖s‖) · log (2 + ‖s‖))`.

The analytic core `intbound_of_decay` bounds the real Mellin-modulus integral: the two tails are
flattened against `exp (-(p/2) t)` and `exp (-(p/2)/t)` via the concavity bound `log v ≤ v - 1`,
integrated in closed form, and the resulting peak exponents are absorbed into
`C · (1 + |σ|) · log (2 + |σ|)`.  The pointwise decay of `F` is upgraded from mathlib's `atTop`
asymptotics to global bounds on `[1, ∞)` and `(0, 1]` by compactness (`global_exp_bound`) and the
kernel functional equation (`hf_modif_FE`).
-/

open Complex Real MeasureTheory Set Filter Asymptotics HurwitzZeta
open scoped Real Topology

namespace RHTower

private theorem peak_ineq (p α t : ℝ) (hp : 0 < p) (hα : 0 ≤ α) (ht : 1 ≤ t) :
    α * Real.log t - (p/2) * t ≤ α * Real.log (1 + 2*α/p) := by
  rcases eq_or_lt_of_le hα with h0 | hpos
  · simp [← h0]; positivity
  · have htpos : 0 < t := lt_of_lt_of_le one_pos ht
    have h2αp : 0 < 2*α/p := by positivity
    set v : ℝ := t*p/(2*α) with hv
    have hvpos : 0 < v := by rw [hv]; positivity
    have hlogv : Real.log v ≤ v - 1 := Real.log_le_sub_one_of_pos hvpos
    have hmax : α * Real.log t - (p/2)*t ≤ α * Real.log (2*α/p) - α := by
      have hvval : (p/2)*t = α * v := by rw [hv]; field_simp
      have hlogsplit : Real.log v = Real.log t - Real.log (2*α/p) := by
        rw [hv, Real.log_div (by positivity) (by positivity), Real.log_mul htpos.ne' hp.ne',
          Real.log_div (by positivity) hp.ne']; ring
      have := mul_le_mul_of_nonneg_left hlogv hpos.le
      rw [hlogsplit] at this
      nlinarith [this, hvval]
    have hstep2 : α * Real.log (2*α/p) - α ≤ α * Real.log (1 + 2*α/p) := by
      have hle : Real.log (2*α/p) ≤ Real.log (1 + 2*α/p) := Real.log_le_log h2αp (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hle hpos.le, hpos]
    linarith [hmax, hstep2]

private theorem integrand_le (p α t : ℝ) (hp : 0 < p) (hα : 0 ≤ α) (ht : 1 ≤ t) :
    t ^ α * Real.exp (-(p*t)) ≤ Real.exp (α * Real.log (1 + 2*α/p)) * Real.exp (-(p/2)*t) := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  rw [Real.rpow_def_of_pos htpos, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [peak_ineq p α t hp hα ht]

private theorem head_integrand_le (p γ t : ℝ) (hp : 0 < p) (hγ : 0 ≤ γ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ^ (-γ) * Real.exp (-(p/t)) ≤ Real.exp (γ * Real.log (1 + 2*γ/p)) * Real.exp (-(p/2)*(1/t)) := by
  have hu : (1:ℝ) ≤ t⁻¹ := by rw [le_inv_comm₀ (by norm_num) ht0]; simpa using ht1
  have h1 : t ^ (-γ) = (t⁻¹) ^ γ := by rw [Real.rpow_neg ht0.le, ← Real.inv_rpow ht0.le]
  have h2 : -(p/t) = -(p * t⁻¹) := by rw [div_eq_mul_inv]
  have h3 : -(p/2)*(1/t) = -(p/2)*(t⁻¹) := by rw [one_div]
  rw [h1, h2, h3]
  exact integrand_le p γ (t⁻¹) hp hγ hu

-- === Dco : sign-cased peak exponent ===
private noncomputable def Dco (p a : ℝ) : ℝ := if 0 ≤ a then a * Real.log (1 + 2*a/p) else 0

private theorem Dco_nonneg (p a : ℝ) (hp : 0 < p) : 0 ≤ Dco p a := by
  unfold Dco
  split
  · rename_i h
    refine mul_nonneg h (Real.log_nonneg ?_)
    have : 0 ≤ 2*a/p := by positivity
    linarith
  · exact le_refl 0

-- tail pointwise (all sign)
private theorem tail_pt (p a t : ℝ) (hp : 0 < p) (ht : 1 ≤ t) :
    t ^ a * Real.exp (-(p*t)) ≤ Real.exp (Dco p a) * Real.exp (-(p/2)*t) := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  unfold Dco
  split
  · rename_i ha; exact integrand_le p a t hp ha ht
  · rename_i ha
    rw [Real.exp_zero, one_mul]
    have h1 : t ^ a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (not_le.mp ha).le
    have h2 : Real.exp (-(p*t)) ≤ Real.exp (-(p/2)*t) := by
      apply Real.exp_le_exp.mpr; nlinarith [htpos, hp]
    calc t ^ a * Real.exp (-(p*t)) ≤ 1 * Real.exp (-(p*t)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-(p*t)) := one_mul _
      _ ≤ Real.exp (-(p/2)*t) := h2

-- head pointwise (all sign)
private theorem head_pt (p γ t : ℝ) (hp : 0 < p) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ^ (-γ) * Real.exp (-(p/t)) ≤ Real.exp (Dco p γ) * Real.exp (-(p/2)*(1/t)) := by
  unfold Dco
  split
  · rename_i hγ; exact head_integrand_le p γ t hp hγ ht0 ht1
  · rename_i hγ
    rw [Real.exp_zero, one_mul]
    have hγ0 : γ ≤ 0 := (not_le.mp hγ).le
    have h1 : t ^ (-γ) ≤ 1 := Real.rpow_le_one ht0.le ht1 (by linarith)
    have h2 : Real.exp (-(p/t)) ≤ Real.exp (-(p/2)*(1/t)) := by
      apply Real.exp_le_exp.mpr
      rw [div_eq_mul_one_div p t]
      have hit : 0 ≤ 1/t := by positivity
      nlinarith [hit, hp]
    calc t ^ (-γ) * Real.exp (-(p/t)) ≤ 1 * Real.exp (-(p/t)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-(p/t)) := one_mul _
      _ ≤ _ := h2


private theorem qexp_le (p a : ℝ) (hp : 0 < p) (ha : 0 ≤ a) :
    a * Real.log (1 + 2*a/p)
      ≤ (1 + |Real.log (1 + 2/p)| / Real.log 2) * ((1 + a) * Real.log (2 + a)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod : (1 : ℝ) + 2*a/p ≤ (1 + 2/p) * (1 + a) := by
    have h : (1 + 2/p) * (1 + a) = 1 + a + 2/p + 2*a/p := by ring
    rw [h]; have : 0 ≤ a + 2/p := by positivity
    linarith
  have hlogle : Real.log (1 + 2*a/p) ≤ Real.log (1 + 2/p) + Real.log (1 + a) := by
    calc Real.log (1 + 2*a/p) ≤ Real.log ((1 + 2/p) * (1 + a)) := Real.log_le_log (by positivity) hprod
      _ = Real.log (1 + 2/p) + Real.log (1 + a) := Real.log_mul (by positivity) (by positivity)
  have hla : Real.log (1 + a) ≤ Real.log (2 + a) := Real.log_le_log (by positivity) (by linarith)
  have hlann : 0 ≤ Real.log (2 + a) := Real.log_nonneg (by linarith)
  have h2le : Real.log 2 ≤ Real.log (2 + a) := Real.log_le_log (by norm_num) (by linarith)
  have hstep : a * Real.log (1 + 2*a/p) ≤ a * Real.log (1 + 2/p) + a * Real.log (1 + a) := by
    nlinarith [mul_le_mul_of_nonneg_left hlogle ha]
  have hA : a * Real.log (1 + a) ≤ (1 + a) * Real.log (2 + a) := by
    nlinarith [mul_le_mul_of_nonneg_left hla ha, hlann, ha]
  have hB : a * Real.log (1 + 2/p) ≤ (|Real.log (1 + 2/p)| / Real.log 2) * ((1 + a) * Real.log (2 + a)) := by
    have hle1 : Real.log (1 + 2/p) ≤ |Real.log (1 + 2/p)| := le_abs_self _
    have habs : 0 ≤ |Real.log (1 + 2/p)| := abs_nonneg _
    have key : a * |Real.log (1 + 2/p)| ≤ (|Real.log (1 + 2/p)| / Real.log 2) * ((1 + a) * Real.log (2 + a)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith [mul_le_mul h2le (le_refl a) ha hlann, mul_le_mul_of_nonneg_left h2le habs,
        mul_nonneg habs hlann, ha]
    calc a * Real.log (1 + 2/p) ≤ a * |Real.log (1 + 2/p)| := mul_le_mul_of_nonneg_left hle1 ha
      _ ≤ _ := key
  nlinarith [hstep, hA, hB]

-- Dco ≤ Kp * (1+|a|) * log(2+|a|)
private theorem Dco_le (p a : ℝ) (hp : 0 < p) :
    Dco p a ≤ (1 + |Real.log (1 + 2/p)| / Real.log 2) * ((1 + |a|) * Real.log (2 + |a|)) := by
  set Kp : ℝ := 1 + |Real.log (1 + 2/p)| / Real.log 2 with hKp
  have hKp0 : 0 ≤ Kp := by rw [hKp]; positivity
  unfold Dco
  split
  · rename_i ha
    rw [abs_of_nonneg ha]
    exact qexp_le p a hp ha
  · rename_i ha
    have hrhs : 0 ≤ Kp * ((1 + |a|) * Real.log (2 + |a|)) := by
      apply mul_nonneg hKp0
      apply mul_nonneg (by positivity)
      apply Real.log_nonneg; have := abs_nonneg a; linarith
    linarith

-- shift envelope
private theorem shift_env_le (σ c : ℝ) (hc : |c| ≤ 3/2) :
    (1 + |σ + c|) * Real.log (2 + |σ + c|)
      ≤ (5/2) * (1 + Real.log (7/4) / Real.log 2) * ((1 + |σ|) * Real.log (2 + |σ|)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hσ0 : 0 ≤ |σ| := abs_nonneg _
  have hac : |σ + c| ≤ |σ| + 3/2 := le_trans (abs_add_le σ c) (by linarith [hc])
  have hasc0 : 0 ≤ |σ + c| := abs_nonneg _
  -- 1+|σ+c| ≤ (5/2)(1+|σ|)
  have h1 : 1 + |σ + c| ≤ (5/2) * (1 + |σ|) := by nlinarith [hac, hσ0]
  -- 2+|σ+c| ≤ (7/4)(2+|σ|)
  have h2 : 2 + |σ + c| ≤ (7/4) * (2 + |σ|) := by nlinarith [hac, hσ0]
  -- log(2+|σ+c|) ≤ (1+log(7/4)/log2)log(2+|σ|)
  have hlogbase : 0 < 2 + |σ| := by linarith
  have h2le : Real.log 2 ≤ Real.log (2 + |σ|) := Real.log_le_log (by norm_num) (by linarith)
  have hlann : 0 ≤ Real.log (2 + |σ|) := Real.log_nonneg (by linarith)
  have hlog74 : 0 ≤ Real.log (7/4) := Real.log_nonneg (by norm_num)
  have hlogle : Real.log (2 + |σ + c|) ≤ (1 + Real.log (7/4) / Real.log 2) * Real.log (2 + |σ|) := by
    have step1 : Real.log (2 + |σ + c|) ≤ Real.log ((7/4) * (2 + |σ|)) :=
      Real.log_le_log (by linarith) h2
    have step2 : Real.log ((7/4) * (2 + |σ|)) = Real.log (7/4) + Real.log (2 + |σ|) :=
      Real.log_mul (by norm_num) (by positivity)
    have step3 : Real.log (7/4) ≤ (Real.log (7/4) / Real.log 2) * Real.log (2 + |σ|) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith [mul_le_mul_of_nonneg_left h2le hlog74]
    nlinarith [step1, step2, step3]
  -- combine
  have hlogrhs0 : 0 ≤ (1 + Real.log (7/4) / Real.log 2) * Real.log (2 + |σ|) := by
    apply mul_nonneg (by positivity) hlann
  calc (1 + |σ + c|) * Real.log (2 + |σ + c|)
      ≤ ((5/2) * (1 + |σ|)) * ((1 + Real.log (7/4) / Real.log 2) * Real.log (2 + |σ|)) := by
        apply mul_le_mul h1 hlogle (Real.log_nonneg (by linarith)) (by positivity)
    _ = (5/2) * (1 + Real.log (7/4) / Real.log 2) * ((1 + |σ|) * Real.log (2 + |σ|)) := by ring


-- === extracted exponential-integral facts ===
private theorem exp_head_int (p : ℝ) (hp : 0 < p) :
    IntegrableOn (fun t => Real.exp (-(p/2)*(1/t))) (Ioc (0:ℝ) 1) := by
  have hmeas : AEStronglyMeasurable (fun t => Real.exp (-(p/2)*(1/t)))
      (volume.restrict (Ioc (0:ℝ) 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply Continuous.comp_continuousOn (Real.continuous_exp)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht; exact (mem_Ioc.mp ht).1.ne'
  have hfin : (volume (Ioc (0:ℝ) 1)) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  refine MeasureTheory.Integrable.mono' (g := fun _ => (1:ℝ)) (integrableOn_const hfin) hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  have : 0 < 1/t := by have := (mem_Ioc.mp ht).1; positivity
  nlinarith [this, hp]

private theorem exp_head_le (p : ℝ) (hp : 0 < p) :
    (∫ t in Ioc (0:ℝ) 1, Real.exp (-(p/2)*(1/t))) ≤ 1 := by
  have hfin : (volume (Ioc (0:ℝ) 1)) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hle : ∫ t in Ioc (0:ℝ) 1, Real.exp (-(p/2)*(1/t)) ≤ ∫ _t in Ioc (0:ℝ) 1, (1:ℝ) := by
    apply integral_mono_of_nonneg
    · filter_upwards with t; positivity
    · exact integrableOn_const hfin
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      apply Real.exp_le_one_iff.mpr
      have : 0 < 1/t := by have := (mem_Ioc.mp ht).1; positivity
      nlinarith [this, hp]
  rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc_of_le zero_le_one,
    sub_zero] at hle
  exact hle

private theorem exp_tail_val (p : ℝ) (hp : 0 < p) :
    (∫ t in Ioi (1:ℝ), Real.exp (-(p/2)*t)) = Real.exp (-(p/2)) * (2/p) := by
  rw [integral_exp_mul_Ioi (a := -(p/2)) (by linarith) 1, mul_one, neg_div_neg_eq]; field_simp

-- === main: IntBound from kernel decay ===
private theorem intbound_of_decay (F : ℝ → ℂ) (C₀ p : ℝ) (hp : 0 < p) (hC₀ : 0 ≤ C₀)
    (hdtop : ∀ t : ℝ, 1 ≤ t → ‖F t‖ ≤ C₀ * Real.exp (-(p*t)))
    (hdhead : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖F t‖ ≤ C₀ * t ^ (-(1:ℝ)/2) * Real.exp (-(p/t))) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ,
      ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * ‖F t‖
        ≤ Real.exp (C * (1 + |σ|) * Real.log (2 + |σ|)) := by
  set Kp : ℝ := 1 + |Real.log (1 + 2/p)| / Real.log 2 with hKpdef
  have hKp0 : 0 < Kp := by rw [hKpdef]; positivity
  set c2 : ℝ := (5/2) * (1 + Real.log (7/4) / Real.log 2) with hc2def
  have hc20 : 0 < c2 := by rw [hc2def]; positivity
  set Kbig : ℝ := Kp * c2 with hKbigdef
  have hKbig0 : 0 < Kbig := mul_pos hKp0 hc20
  set Cpre : ℝ := max 1 (C₀ * (1 + 2/p)) with hCpredef
  have hCpre1 : 1 ≤ Cpre := le_max_left _ _
  have hCpre0 : 0 < Cpre := lt_of_lt_of_le one_pos hCpre1
  have hlogCpre0 : 0 ≤ Real.log Cpre := Real.log_nonneg hCpre1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := Real.log Cpre / Real.log 2 + Kbig with hCdef
  have hC0 : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, hC0, fun σ => ?_⟩
  set E : ℝ := (1 + |σ|) * Real.log (2 + |σ|) with hEdef
  have hσabs : 0 ≤ |σ| := abs_nonneg σ
  have hElb : Real.log 2 ≤ E := by
    rw [hEdef]
    have h2 : Real.log 2 ≤ Real.log (2 + |σ|) := Real.log_le_log (by norm_num) (by linarith)
    have h3 : 0 ≤ Real.log (2 + |σ|) := Real.log_nonneg (by linarith)
    nlinarith [h2, h3]
  set A_h : ℝ := C₀ * Real.exp (Dco p (3/2 - σ)) with hAhdef
  set A_t : ℝ := C₀ * Real.exp (Dco p (σ - 1)) with hAtdef
  have hAh0 : 0 ≤ A_h := by rw [hAhdef]; positivity
  have hAt0 : 0 ≤ A_t := by rw [hAtdef]; positivity
  set M : ℝ → ℝ := fun t => if t ≤ 1 then A_h * Real.exp (-(p/2)*(1/t)) else A_t * Real.exp (-(p/2)*t) with hMdef
  have hgM : ∀ t : ℝ, t ∈ Ioi (0:ℝ) → t ^ (σ - 1) * ‖F t‖ ≤ M t := by
    intro t ht
    have ht0 : 0 < t := ht
    have htrpow0 : 0 ≤ t ^ (σ - 1) := Real.rpow_nonneg ht0.le _
    rcases le_or_gt t 1 with hle | hgt
    · rw [hMdef]; simp only [if_pos hle]
      have hF := hdhead t ht0 hle
      have step1 : t ^ (σ - 1) * ‖F t‖ ≤ t ^ (σ - 1) * (C₀ * t ^ (-(1:ℝ)/2) * Real.exp (-(p/t))) :=
        mul_le_mul_of_nonneg_left hF htrpow0
      have hrw : t ^ (σ - 1) * (C₀ * t ^ (-(1:ℝ)/2) * Real.exp (-(p/t)))
          = C₀ * (t ^ (-(3/2 - σ)) * Real.exp (-(p/t))) := by
        rw [show (-(3/2 - σ) : ℝ) = (σ - 1) + (-(1:ℝ)/2) by ring, Real.rpow_add ht0]; ring
      rw [hrw] at step1
      have hpt := head_pt p (3/2 - σ) t hp ht0 hle
      calc t ^ (σ - 1) * ‖F t‖ ≤ C₀ * (t ^ (-(3/2 - σ)) * Real.exp (-(p/t))) := step1
        _ ≤ C₀ * (Real.exp (Dco p (3/2 - σ)) * Real.exp (-(p/2)*(1/t))) :=
            mul_le_mul_of_nonneg_left hpt hC₀
        _ = A_h * Real.exp (-(p/2)*(1/t)) := by rw [hAhdef]; ring
    · rw [hMdef]; simp only [if_neg (not_le.mpr hgt)]
      have hF := hdtop t hgt.le
      have step1 : t ^ (σ - 1) * ‖F t‖ ≤ t ^ (σ - 1) * (C₀ * Real.exp (-(p*t))) :=
        mul_le_mul_of_nonneg_left hF htrpow0
      have hpt := tail_pt p (σ - 1) t hp hgt.le
      calc t ^ (σ - 1) * ‖F t‖ ≤ t ^ (σ - 1) * (C₀ * Real.exp (-(p*t))) := step1
        _ = C₀ * (t ^ (σ - 1) * Real.exp (-(p*t))) := by ring
        _ ≤ C₀ * (Real.exp (Dco p (σ - 1)) * Real.exp (-(p/2)*t)) :=
            mul_le_mul_of_nonneg_left hpt hC₀
        _ = A_t * Real.exp (-(p/2)*t) := by rw [hAtdef]; ring
  have hMh : IntegrableOn M (Ioc (0:ℝ) 1) := by
    have hbase : IntegrableOn (fun t => A_h * Real.exp (-(p/2)*(1/t))) (Ioc (0:ℝ) 1) :=
      (exp_head_int p hp).const_mul A_h
    apply hbase.congr_fun _ measurableSet_Ioc
    intro t ht; rw [hMdef]; simp only [if_pos (mem_Ioc.mp ht).2]
  have hMt : IntegrableOn M (Ioi (1:ℝ)) := by
    have hbase : IntegrableOn (fun t => A_t * Real.exp (-(p/2)*t)) (Ioi (1:ℝ)) :=
      (integrableOn_exp_mul_Ioi (a := -(p/2)) (by linarith) 1).const_mul A_t
    apply hbase.congr_fun _ measurableSet_Ioi
    intro t ht; rw [hMdef]; simp only [if_neg (not_le.mpr (mem_Ioi.mp ht))]
  have hMint : IntegrableOn M (Ioi (0:ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one)]
    exact integrableOn_union.mpr ⟨hMh, hMt⟩
  have hbound : ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * ‖F t‖ ≤ ∫ t in Ioi (0:ℝ), M t := by
    apply integral_mono_of_nonneg
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have : 0 < t := ht; positivity
    · exact hMint
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hgM t ht
  have hsplit : ∫ t in Ioi (0:ℝ), M t = (∫ t in Ioc (0:ℝ) 1, M t) + ∫ t in Ioi (1:ℝ), M t := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one)]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hMh hMt
  have hpiece_h : ∫ t in Ioc (0:ℝ) 1, M t ≤ A_h := by
    have hcongr : ∫ t in Ioc (0:ℝ) 1, M t = ∫ t in Ioc (0:ℝ) 1, A_h * Real.exp (-(p/2)*(1/t)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht; rw [hMdef]; simp only [if_pos (mem_Ioc.mp ht).2]
    rw [hcongr, integral_const_mul]
    calc A_h * ∫ t in Ioc (0:ℝ) 1, Real.exp (-(p/2)*(1/t))
        ≤ A_h * 1 := mul_le_mul_of_nonneg_left (exp_head_le p hp) hAh0
      _ = A_h := mul_one A_h
  have hpiece_t : ∫ t in Ioi (1:ℝ), M t ≤ A_t * (2/p) := by
    have hcongr : ∫ t in Ioi (1:ℝ), M t = ∫ t in Ioi (1:ℝ), A_t * Real.exp (-(p/2)*t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht; rw [hMdef]; simp only [if_neg (not_le.mpr (mem_Ioi.mp ht))]
    rw [hcongr, integral_const_mul, exp_tail_val p hp]
    calc A_t * (Real.exp (-(p/2)) * (2/p))
        ≤ A_t * (1 * (2/p)) := by
          apply mul_le_mul_of_nonneg_left _ hAt0
          apply mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith)) (by positivity)
      _ = A_t * (2/p) := by ring
  have hcombine : ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * ‖F t‖ ≤ A_h + A_t * (2/p) := by
    calc ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * ‖F t‖ ≤ ∫ t in Ioi (0:ℝ), M t := hbound
      _ = (∫ t in Ioc (0:ℝ) 1, M t) + ∫ t in Ioi (1:ℝ), M t := hsplit
      _ ≤ A_h + A_t * (2/p) := by linarith [hpiece_h, hpiece_t]
  have hDco_h : Dco p (3/2 - σ) ≤ Kbig * E := by
    have h1 := Dco_le p (3/2 - σ) hp
    have h2 := shift_env_le σ (-(3/2)) (by rw [abs_neg]; norm_num)
    have habs : |(3/2 : ℝ) - σ| = |σ + -(3/2)| := by rw [abs_sub_comm]; ring_nf
    rw [habs] at h1
    calc Dco p (3/2 - σ) ≤ Kp * ((1 + |σ + -(3/2)|) * Real.log (2 + |σ + -(3/2)|)) := h1
      _ ≤ Kp * (c2 * E) := by
          apply mul_le_mul_of_nonneg_left _ hKp0.le; rw [hEdef, hc2def]; exact h2
      _ = Kbig * E := by rw [hKbigdef]; ring
  have hDco_t : Dco p (σ - 1) ≤ Kbig * E := by
    have h1 := Dco_le p (σ - 1) hp
    have h2 := shift_env_le σ (-1) (by rw [abs_neg]; norm_num)
    have habs : |σ - 1| = |σ + -1| := by ring_nf
    rw [habs] at h1
    calc Dco p (σ - 1) ≤ Kp * ((1 + |σ + -1|) * Real.log (2 + |σ + -1|)) := h1
      _ ≤ Kp * (c2 * E) := by
          apply mul_le_mul_of_nonneg_left _ hKp0.le; rw [hEdef, hc2def]; exact h2
      _ = Kbig * E := by rw [hKbigdef]; ring
  have hexpAh : A_h ≤ C₀ * Real.exp (Kbig * E) := by
    rw [hAhdef]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hDco_h) hC₀
  have hexpAt : A_t ≤ C₀ * Real.exp (Kbig * E) := by
    rw [hAtdef]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hDco_t) hC₀
  have hpre : C₀ * (1 + 2/p) ≤ Real.exp (Real.log Cpre / Real.log 2 * E) := by
    have hstep : Real.log Cpre ≤ Real.log Cpre / Real.log 2 * E := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith [mul_le_mul_of_nonneg_left hElb hlogCpre0]
    calc C₀ * (1 + 2/p) ≤ Cpre := le_max_right _ _
      _ = Real.exp (Real.log Cpre) := (Real.exp_log hCpre0).symm
      _ ≤ Real.exp (Real.log Cpre / Real.log 2 * E) := Real.exp_le_exp.mpr hstep
  have hfinal : A_h + A_t * (2/p) ≤ Real.exp (C * E) := by
    have h2p0 : 0 ≤ 2/p := by positivity
    have hsum : A_h + A_t * (2/p) ≤ (C₀ * (1 + 2/p)) * Real.exp (Kbig * E) := by
      have e1 : A_t * (2/p) ≤ (C₀ * Real.exp (Kbig * E)) * (2/p) :=
        mul_le_mul_of_nonneg_right hexpAt h2p0
      nlinarith [hexpAh, e1, Real.exp_pos (Kbig * E), h2p0, hC₀]
    calc A_h + A_t * (2/p) ≤ (C₀ * (1 + 2/p)) * Real.exp (Kbig * E) := hsum
      _ ≤ Real.exp (Real.log Cpre / Real.log 2 * E) * Real.exp (Kbig * E) :=
          mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le
      _ = Real.exp (C * E) := by rw [← Real.exp_add, hCdef]; ring_nf
  calc ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * ‖F t‖ ≤ A_h + A_t * (2/p) := hcombine
    _ ≤ Real.exp (C * E) := hfinal
    _ = Real.exp (C * (1 + |σ|) * Real.log (2 + |σ|)) := by rw [hEdef]; ring_nf

private theorem global_exp_bound (g : ℝ → ℝ) (L p : ℝ)
    (hcont : ContinuousOn g (Ioi 0))
    (hO : (fun t => g t - L) =O[atTop] (fun t => Real.exp (-p * t))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → |g t - L| ≤ C * Real.exp (-p * t) := by
  obtain ⟨K, hK⟩ := hO.isBigOWith
  have hKb := hK.bound
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hKb
  set N : ℝ := max N₀ 1 with hN
  have hIccsub : Icc (1:ℝ) N ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le one_pos ht.1
  have hφcont : ContinuousOn (fun t => |g t - L| * Real.exp (p * t)) (Icc 1 N) := by
    apply ContinuousOn.mul
    · exact ((hcont.mono hIccsub).sub continuousOn_const).abs
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hφcont
  refine ⟨|K| + |M|, by positivity, fun t ht => ?_⟩
  have hexp0 : 0 < Real.exp (-p * t) := Real.exp_pos _
  rcases le_or_gt t N with hle | hgt
  · have hφ := hM t ⟨ht, hle⟩
    rw [Real.norm_eq_abs] at hφ
    have hφ2 : |g t - L| * Real.exp (p * t) ≤ M := le_trans (le_abs_self _) hφ
    have key : |g t - L| ≤ M * Real.exp (-p * t) := by
      have hmul := mul_le_mul_of_nonneg_right hφ2 hexp0.le
      rwa [mul_assoc, ← Real.exp_add, show p * t + -p * t = 0 by ring, Real.exp_zero, mul_one] at hmul
    calc |g t - L| ≤ M * Real.exp (-p * t) := key
      _ ≤ (|K| + |M|) * Real.exp (-p * t) := by
          apply mul_le_mul_of_nonneg_right _ hexp0.le
          have := abs_nonneg K; have := le_abs_self M; linarith
  · have htN₀ : N₀ ≤ t := le_trans (le_max_left N₀ 1) hgt.le
    have hb := hN₀ t htN₀
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hexp0] at hb
    calc |g t - L| ≤ K * Real.exp (-p * t) := hb
      _ ≤ (|K| + |M|) * Real.exp (-p * t) := by
          apply mul_le_mul_of_nonneg_right _ hexp0.le
          have := abs_nonneg M; have := le_abs_self K; linarith

private theorem f0_eq : (hurwitzEvenFEPair 0).f₀ = 1 := by
  show (if (0:UnitAddCircle) = 0 then (1:ℂ) else 0) = 1; rw [if_pos rfl]

private theorem fmodif_tail (t : ℝ) (ht : 1 < t) :
    (hurwitzEvenFEPair 0).f_modif t = (↑(evenKernel 0 t) : ℂ) - 1 := by
  unfold WeakFEPair.f_modif
  rw [Pi.add_apply, indicator_of_mem (mem_Ioi.mpr ht),
    indicator_of_notMem (notMem_Ioo_of_ge ht.le), add_zero, f0_eq]; rfl

private theorem fmodif_one : (hurwitzEvenFEPair 0).f_modif 1 = 0 := by
  unfold WeakFEPair.f_modif
  rw [Pi.add_apply, indicator_of_notMem (by simp), indicator_of_notMem (by simp), add_zero]

private theorem tail_decay : ∃ p : ℝ, 0 < p ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ t : ℝ, 1 ≤ t → ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤ C₀ * Real.exp (-(p*t)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub 0
  have hOsimp : (fun t => evenKernel 0 t - 1) =O[atTop] (fun t => Real.exp (-p * t)) := by
    have he : (if (0:UnitAddCircle) = 0 then (1:ℝ) else 0) = 1 := by rw [if_pos rfl]
    simpa [he] using hO
  obtain ⟨C, hC0, hCb⟩ := global_exp_bound (evenKernel 0) 1 p (continuousOn_evenKernel 0) hOsimp
  refine ⟨p, hp, C, hC0, fun t ht => ?_⟩
  rcases eq_or_lt_of_le ht with h1 | h1
  · rw [← h1, fmodif_one, norm_zero]; positivity
  · rw [fmodif_tail t h1]
    have hnorm : ‖(↑(evenKernel 0 t):ℂ) - 1‖ = |evenKernel 0 t - 1| := by
      rw [show (↑(evenKernel 0 t):ℂ) - 1 = ↑(evenKernel 0 t - 1) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm, show -(p*t) = -p*t by ring]
    exact hCb t ht

private theorem gmodif_eval (y : ℝ) (hy : 1 < y) :
    (hurwitzEvenFEPair 0).g_modif y = (↑(cosKernel 0 y) : ℂ) - 1 := by
  unfold WeakFEPair.g_modif
  rw [Pi.add_apply, indicator_of_mem (mem_Ioi.mpr hy),
    indicator_of_notMem (notMem_Ioo_of_ge hy.le), add_zero]
  show (↑(cosKernel 0 y):ℂ) - (hurwitzEvenFEPair 0).g₀ = ↑(cosKernel 0 y) - 1
  rw [show (hurwitzEvenFEPair 0).g₀ = 1 from rfl]

private theorem head_decay : ∃ p : ℝ, 0 < p ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤ C₀ * t ^ (-(1:ℝ)/2) * Real.exp (-(p/t)) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_cosKernel_sub 0
  obtain ⟨C, hC0, hCb⟩ := global_exp_bound (cosKernel 0) 1 p (continuousOn_cosKernel 0) hO
  refine ⟨p, hp, C, hC0, fun t ht0 ht1 => ?_⟩
  rcases eq_or_lt_of_le ht1 with heq | hlt
  · rw [heq, fmodif_one, norm_zero]; positivity
  · set x : ℝ := 1/t with hx
    have hxpos : 0 < x := by rw [hx]; positivity
    have hx1 : 1 < x := by rw [hx, lt_div_iff₀ ht0]; linarith
    have h1x : 1/x = t := by rw [hx, one_div_one_div]
    have hFE := (hurwitzEvenFEPair 0).hf_modif_FE x hxpos
    rw [h1x, gmodif_eval x hx1, show (hurwitzEvenFEPair 0).ε = 1 from rfl,
      show (hurwitzEvenFEPair 0).k = (1/2 : ℝ) from rfl, one_mul, smul_eq_mul] at hFE
    rw [hFE]
    have hxk0 : 0 ≤ x ^ (1/2 : ℝ) := by positivity
    have hnorm : ‖(↑(x ^ (1/2:ℝ)) : ℂ) * ((↑(cosKernel 0 x) : ℂ) - 1)‖
        = x ^ (1/2:ℝ) * |cosKernel 0 x - 1| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxk0,
        show (↑(cosKernel 0 x):ℂ) - 1 = ↑(cosKernel 0 x - 1) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    have hxrw : x ^ (1/2:ℝ) = t ^ (-(1:ℝ)/2) := by
      rw [hx, one_div t, Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le]
      norm_num
    have hexprw : Real.exp (-p * x) = Real.exp (-(p/t)) := by
      rw [hx]; congr 1; rw [mul_one_div]; ring
    calc x ^ (1/2:ℝ) * |cosKernel 0 x - 1|
        ≤ x ^ (1/2:ℝ) * (C * Real.exp (-p * x)) :=
          mul_le_mul_of_nonneg_left (hCb x hx1.le) hxk0
      _ = C * t ^ (-(1:ℝ)/2) * Real.exp (-(p/t)) := by rw [hxrw, hexprw]; ring

private theorem decay_holds : ∃ C₀ p : ℝ, 0 < p ∧ 0 ≤ C₀ ∧
    (∀ t : ℝ, 1 ≤ t → ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤ C₀ * Real.exp (-(p*t))) ∧
    (∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤ C₀ * t ^ (-(1:ℝ)/2) * Real.exp (-(p/t))) := by
  obtain ⟨p₁, hp₁, C₁, hC₁, htop⟩ := tail_decay
  obtain ⟨p₂, hp₂, C₂, hC₂, hhead⟩ := head_decay
  refine ⟨max C₁ C₂, min p₁ p₂, lt_min hp₁ hp₂, le_trans hC₁ (le_max_left _ _), ?_, ?_⟩
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
    calc ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤ C₁ * Real.exp (-(p₁*t)) := htop t ht
      _ ≤ max C₁ C₂ * Real.exp (-(min p₁ p₂ * t)) := by
          apply mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
            (le_trans hC₁ (le_max_left _ _))
          have : min p₁ p₂ * t ≤ p₁ * t := mul_le_mul_of_nonneg_right (min_le_left _ _) ht0.le
          linarith
  · intro t ht0 ht1
    have hxk0 : 0 ≤ t ^ (-(1:ℝ)/2) := by positivity
    calc ‖(hurwitzEvenFEPair 0).f_modif t‖ ≤ C₂ * t ^ (-(1:ℝ)/2) * Real.exp (-(p₂/t)) := hhead t ht0 ht1
      _ ≤ max C₁ C₂ * t ^ (-(1:ℝ)/2) * Real.exp (-(min p₁ p₂ / t)) := by
          have hexp : Real.exp (-(p₂/t)) ≤ Real.exp (-(min p₁ p₂ / t)) := by
            apply Real.exp_le_exp.mpr
            have hmm : min p₁ p₂ / t ≤ p₂ / t := by
              gcongr
              exact min_le_right _ _
            linarith
          have hCle : C₂ ≤ max C₁ C₂ := le_max_right _ _
          have e1 : C₂ * t ^ (-(1:ℝ)/2) ≤ max C₁ C₂ * t ^ (-(1:ℝ)/2) :=
            mul_le_mul_of_nonneg_right hCle hxk0
          have e2 : 0 ≤ max C₁ C₂ * t ^ (-(1:ℝ)/2) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hexp e2,
            mul_le_mul_of_nonneg_right e1 (Real.exp_pos (-(p₂/t))).le]


/-- The modified even theta kernel underlying `Λ₀`: `F = (hurwitzEvenFEPair 0).f_modif`, the
piecewise correction of the Jacobi theta kernel whose Mellin transform is `Λ₀(2·)`. -/
noncomputable def modifiedEvenKernel : ℝ → ℂ := (HurwitzZeta.hurwitzEvenFEPair 0).f_modif

/-- **Exponential decay of the modified even theta kernel** `F = modifiedEvenKernel` at both ends:
for some rate `p > 0` and constant `C₀ ≥ 0`, `‖F t‖ ≤ C₀ exp (-(p t))` for `t ≥ 1` and
`‖F t‖ ≤ C₀ t^{-1/2} exp (-(p/t))` for `0 < t ≤ 1`.  These are the Jacobi theta bounds
`isBigO_atTop_evenKernel_sub`/`isBigO_atTop_cosKernel_sub`, globalised to pointwise estimates via
compactness and the kernel functional equation; `modifiedEvenKernelDecay_holds` proves them. -/
def ModifiedEvenKernelDecay : Prop :=
  ∃ C₀ p : ℝ, 0 < p ∧ 0 ≤ C₀ ∧
    (∀ t : ℝ, 1 ≤ t → ‖modifiedEvenKernel t‖ ≤ C₀ * Real.exp (-(p*t))) ∧
    (∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖modifiedEvenKernel t‖ ≤ C₀ * t ^ (-(1:ℝ)/2) * Real.exp (-(p/t)))

/-- The modified even theta kernel decays exponentially at both ends: the Jacobi theta asymptotics
`isBigO_atTop_evenKernel_sub` (for `t → ∞`) and `isBigO_atTop_cosKernel_sub` together with the
kernel functional equation `hf_modif_FE` (for `t → 0`), globalised from `atTop` bounds to pointwise
estimates by compactness of the intervening compact interval. -/
theorem modifiedEvenKernelDecay_holds : ModifiedEvenKernelDecay := decay_holds

/-- **The entire completed zeta `Λ₀` has order ≤ 1** (unconditional).  The entire completion
`Λ₀ = completedRiemannZeta₀` obeys the Hadamard order-one bound
`‖Λ₀ s‖ ≤ exp (C · (1 + ‖s‖) · log (2 + ‖s‖))`.

Mechanism: `Λ₀ s = mellin F (s/2) / 2` with `F = modifiedEvenKernel`, so
`‖Λ₀ s‖ ≤ (1/2) ∫₀^∞ t ^ (Re (s/2) - 1) ‖F t‖ dt` by `‖(t:ℂ)^(w-1)‖ = t ^ (Re w - 1)` and the
triangle inequality for integrals.  The Mellin-modulus estimate `intbound_of_decay`, fed the
exponential decay `modifiedEvenKernelDecay_holds`, bounds that real integral at `σ = Re s / 2` by an
order-one envelope in `|σ|`, and `|Re s| ≤ ‖s‖` with monotonicity of `exp`, `log`, and the `/2 ≤ 1`
prefactor give the claimed bound in `‖s‖`. -/
theorem completedZeta0_order_le_one :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      ‖completedRiemannZeta₀ s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C₀, p, hp, hC₀, hdtop, hdhead⟩ := modifiedEvenKernelDecay_holds
  obtain ⟨C, hC, hb⟩ := intbound_of_decay modifiedEvenKernel C₀ p hp hC₀ hdtop hdhead
  refine ⟨C, hC, fun s => ?_⟩
  have hz : completedRiemannZeta₀ s = mellin modifiedEvenKernel (s / 2) / 2 := rfl
  rw [hz, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hstep1 : ‖mellin modifiedEvenKernel (s / 2)‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s / 2 - 1) • modifiedEvenKernel t‖ := by
    rw [mellin]; exact norm_integral_le_integral_norm _
  have hcongr : (∫ t in Set.Ioi (0 : ℝ), ‖(t : ℂ) ^ (s / 2 - 1) • modifiedEvenKernel t‖)
      = ∫ t in Set.Ioi (0 : ℝ), t ^ ((s / 2).re - 1) * ‖modifiedEvenKernel t‖ := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := ht
    show ‖(t : ℂ) ^ (s / 2 - 1) • modifiedEvenKernel t‖
        = t ^ ((s / 2).re - 1) * ‖modifiedEvenKernel t‖
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, sub_re, one_re]
  rw [hcongr] at hstep1
  set σ : ℝ := (s / 2).re with hσ
  have hchain : ‖mellin modifiedEvenKernel (s / 2)‖
      ≤ Real.exp (C * (1 + |σ|) * Real.log (2 + |σ|)) := le_trans hstep1 (hb σ)
  have hσle : |σ| ≤ ‖s‖ := by
    rw [hσ]
    have hre : (s / 2).re = s.re / 2 := by rw [div_re]; simp; ring
    rw [hre, abs_div, show |(2 : ℝ)| = 2 by norm_num]
    have h1 : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
    linarith [norm_nonneg s, abs_nonneg s.re]
  have hmono : Real.exp (C * (1 + |σ|) * Real.log (2 + |σ|))
      ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    apply Real.exp_le_exp.mpr
    have hσnn : 0 ≤ |σ| := abs_nonneg _
    have hsnn : 0 ≤ ‖s‖ := norm_nonneg _
    have hlog : Real.log (2 + |σ|) ≤ Real.log (2 + ‖s‖) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlognn : 0 ≤ Real.log (2 + |σ|) := Real.log_nonneg (by linarith)
    nlinarith [mul_le_mul (by linarith : (1 : ℝ) + |σ| ≤ 1 + ‖s‖) hlog hlognn
      (by linarith : (0 : ℝ) ≤ 1 + ‖s‖), hC.le,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + |σ|) hlognn]
  have hfinal : ‖mellin modifiedEvenKernel (s / 2)‖
      ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := le_trans hchain hmono
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [hfinal, Real.exp_pos (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)),
    norm_nonneg (mellin modifiedEvenKernel (s / 2))]

/-- The order-one growth of `Λ₀` in the form `CompletedZeta0OrderOne`, discharging the analytic input
to the completed-`ξ` growth reduction. -/
theorem completedZeta0OrderOne_holds : CompletedZeta0OrderOne :=
  completedZeta0_order_le_one

/-- **The completed ξ is entire of order ≤ 1, unconditionally.**  Combining the reduction
`xi_growth_order_le_one_of_completedZeta0OrderOne` (all transcendental growth of `ξ` lives in `Λ₀`)
with the discharged growth bound `completedZeta0OrderOne_holds`, the completed zeta satisfies a global
order-one growth envelope with no analytic debt — a native invariant of the completion `Λ = Γ·ζ` and
the growth input Hadamard-type factorization and zero-counting arguments over `ξ` require. -/
theorem xi_growth_order_le_one :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖xi s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) :=
  xi_growth_order_le_one_of_completedZeta0OrderOne completedZeta0OrderOne_holds

end RHTower
