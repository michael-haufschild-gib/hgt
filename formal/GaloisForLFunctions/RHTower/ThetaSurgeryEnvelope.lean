import GaloisForLFunctions.RHTower.ThetaAnalyticStripZeroEngineering
import GaloisForLFunctions.RHTower.ThetaRenewalDenominatorOrder

/-!
# The doubly exponential surgery envelope

The perturbations `ψ(t)(ε₀ + ε₁ cos(Tt) + ε₂ t sin(Tt))`, `ψ(t) = t^{2N+2} exp(-e^{2t} - e^{-2t})`,
are even, real analytic and vanish to order `2N + 2` at the seam. Cauchy estimates on discs of
radius `1/8` bound every derivative by `k! 8^k Σ|ε_j| (|t| + 1)^{2N+3} e^{T/8} ϖ(t)` with
`ϖ(t) = exp(-e^{2|t|}/(2e^{1/4}))`. This profile is dominated by every exponential weight, by the
theta renewal increment `ν` and the arithmetic tail `R` on `t ≥ 0`, and — after the logarithmic
shifts of any finite literal prime deletion — by the first theta atom, uniformly in the prime set.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ContDiff

namespace RHTower

noncomputable section

/-! ## The doubly exponential envelope -/

/-- The decay profile `ϖ(t) = exp(-e^{2|t|}/(2 e^{1/4}))`. -/
def surgeryDecay (t : ℝ) : ℝ := Real.exp (-(Real.exp (2 * |t|) / (2 * Real.exp (1 / 4))))

theorem surgeryDecay_pos (t : ℝ) : 0 < surgeryDecay t := Real.exp_pos _

/-- The three-direction perturbation `ψ(t)(ε₀ + ε₁ cos(Tt) + ε₂ t sin(Tt))`,
`ψ(t) = t^{2N+2} exp(-e^{2t} - e^{-2t})`. -/
def surgeryPerturbation (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  t ^ (2 * N + 2) * Real.exp (-(Real.exp (2 * t) + Real.exp (-(2 * t)))) *
    (ε 0 + ε 1 * Real.cos (T * t) + ε 2 * (t * Real.sin (T * t)))

/-- Its entire extension. -/
def surgeryPerturbationC (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (z : ℂ) : ℂ :=
  z ^ (2 * N + 2) * cexp (-(cexp (2 * z) + cexp (-(2 * z)))) *
    ((ε 0 : ℂ) + (ε 1 : ℂ) * Complex.cos (T * z) + (ε 2 : ℂ) * (z * Complex.sin (T * z)))

theorem surgeryPerturbationC_ofReal (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (x : ℝ) :
    surgeryPerturbationC N T ε x = (surgeryPerturbation N T ε x : ℂ) := by
  simp only [surgeryPerturbationC, surgeryPerturbation]
  push_cast
  rfl

theorem differentiable_surgeryPerturbationC (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) :
    Differentiable ℂ (surgeryPerturbationC N T ε) := by
  unfold surgeryPerturbationC; fun_prop

theorem surgeryPerturbation_eq_re (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) :
    surgeryPerturbation N T ε = fun x : ℝ => (surgeryPerturbationC N T ε (x : ℂ)).re := by
  funext x; rw [surgeryPerturbationC_ofReal, Complex.ofReal_re]

theorem contDiff_surgeryPerturbation (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (surgeryPerturbation N T ε) := by
  unfold surgeryPerturbation; fun_prop

theorem analyticAt_surgeryPerturbation (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (x : ℝ) :
    AnalyticAt ℝ (surgeryPerturbation N T ε) x := by
  rw [surgeryPerturbation_eq_re]
  exact ((differentiable_surgeryPerturbationC N T ε).analyticAt _).re_ofReal

theorem surgeryPerturbation_neg (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) :
    surgeryPerturbation N T ε (-t) = surgeryPerturbation N T ε t := by
  simp only [surgeryPerturbation, mul_neg, neg_neg, Real.cos_neg, Real.sin_neg]
  rw [show (-t) ^ (2 * N + 2) = t ^ (2 * N + 2) by rw [Even.neg_pow ⟨N + 1, by ring⟩]]
  ring_nf

theorem surgeryPerturbation_zero_arg (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) :
    surgeryPerturbation N T ε 0 = 0 := by
  simp [surgeryPerturbation]

/-- **Seam jets.** All derivatives of order `≤ 2N + 1` vanish at `0`. -/
theorem iteratedDeriv_surgeryPerturbation_zero (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) {k : ℕ}
    (hk : k ≤ 2 * N + 1) : iteratedDeriv k (surgeryPerturbation N T ε) 0 = 0 := by
  set h : ℝ → ℝ := fun t => Real.exp (-(Real.exp (2 * t) + Real.exp (-(2 * t)))) *
    (ε 0 + ε 1 * Real.cos (T * t) + ε 2 * (t * Real.sin (T * t)))
  have hh : ContDiff ℝ ∞ h := by fun_prop
  have hp : ContDiff ℝ ∞ fun t : ℝ => t ^ (2 * N + 2) := by fun_prop
  have hfun : surgeryPerturbation N T ε = (fun t : ℝ => t ^ (2 * N + 2)) * h := by
    funext t; simp only [surgeryPerturbation, Pi.mul_apply, h]; ring
  rw [hfun, iteratedDeriv_mul (hp.contDiffAt.of_le (mod_cast le_top))
    (hh.contDiffAt.of_le (mod_cast le_top))]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi' : i < 2 * N + 2 := by have := Finset.mem_range.mp hi; omega
  rw [iteratedDeriv_eq_iterate, iter_deriv_pow]
  simp [zero_pow (by omega : 2 * N + 2 - i ≠ 0)]

/-! ## Bounds on thin strips -/

theorem norm_cexp_envelope_le {z : ℂ} {t : ℝ} (hz : ‖z - t‖ ≤ 1 / 8) :
    ‖cexp (-(cexp (2 * z) + cexp (-(2 * z))))‖ ≤ surgeryDecay t := by
  rw [Complex.norm_exp, surgeryDecay]
  refine Real.exp_le_exp.mpr ?_
  have hb : |z.im| ≤ 1 / 8 := by
    have := Complex.abs_im_le_norm (z - t); simp only [sub_im, ofReal_im, sub_zero] at this; linarith
  have ha : |z.re - t| ≤ 1 / 8 := by
    have := Complex.abs_re_le_norm (z - t); simp only [sub_re, ofReal_re] at this; linarith
  have hcos : 1 / 2 ≤ Real.cos (2 * z.im) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := 2 * z.im)
    have : (2 * z.im) ^ 2 ≤ 1 / 16 := by
      have := sq_abs z.im; nlinarith [abs_nonneg z.im]
    linarith
  have hre : (-(cexp (2 * z) + cexp (-(2 * z)))).re =
      -((Real.exp (2 * z.re) + Real.exp (-(2 * z.re))) * Real.cos (2 * z.im)) := by
    simp only [neg_re, add_re, Complex.exp_re, mul_re, mul_im]
    norm_num
    ring
  rw [hre, neg_le_neg_iff]
  have habs : |t| - 1 / 8 ≤ |z.re| := by
    have := abs_sub_abs_le_abs_sub t z.re; rw [abs_sub_comm] at this; linarith
  have hmax : Real.exp (2 * |t|) / Real.exp (1 / 4) ≤ Real.exp (2 * z.re) + Real.exp (-(2 * z.re)) := by
    rw [← Real.exp_sub]
    rcases le_total 0 z.re with h | h
    · rw [abs_of_nonneg h] at habs
      exact le_add_of_le_of_nonneg (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
    · rw [abs_of_nonpos h] at habs
      exact le_add_of_nonneg_of_le (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith))
  have hE : 0 ≤ Real.exp (2 * z.re) + Real.exp (-(2 * z.re)) := by positivity
  calc Real.exp (2 * |t|) / (2 * Real.exp (1 / 4)) = (Real.exp (2 * |t|) / Real.exp (1 / 4)) * (1 / 2) := by
        field_simp
    _ ≤ (Real.exp (2 * z.re) + Real.exp (-(2 * z.re))) * Real.cos (2 * z.im) :=
        mul_le_mul hmax hcos (by norm_num) hE

theorem norm_surgeryPerturbationC_le (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) {z : ℂ} {t : ℝ}
    (hz : ‖z - t‖ ≤ 1 / 8) :
    ‖surgeryPerturbationC N T ε z‖ ≤ (|ε 0| + |ε 1| + |ε 2|) *
      ((|t| + 1) ^ (2 * N + 3) * Real.exp (T / 8) * surgeryDecay t) := by
  have hzn : ‖z‖ ≤ |t| + 1 := by
    have := norm_sub_norm_le z t; rw [Complex.norm_real, Real.norm_eq_abs] at this; linarith
  have hb : |z.im| ≤ 1 / 8 := by
    have := Complex.abs_im_le_norm (z - t); simp only [sub_im, ofReal_im, sub_zero] at this; linarith
  have hE : Real.exp |((T : ℂ) * z).im| ≤ Real.exp (T / 8) := by
    refine Real.exp_le_exp.mpr ?_
    rw [show ((T : ℂ) * z).im = T * z.im by simp, abs_mul, abs_of_nonneg hT]
    nlinarith
  have hc := (GaloisForLFunctions.HTGeometry.norm_ccos_le_exp_abs_im ((T : ℂ) * z)).trans hE
  have hs := (GaloisForLFunctions.HTGeometry.norm_csin_le_exp_abs_im ((T : ℂ) * z)).trans hE
  have hT8 : 1 ≤ Real.exp (T / 8) := Real.one_le_exp (by positivity)
  have ht1 : 1 ≤ |t| + 1 := by linarith [abs_nonneg t]
  have hinner : ‖(ε 0 : ℂ) + (ε 1 : ℂ) * Complex.cos (T * z) + (ε 2 : ℂ) * (z * Complex.sin (T * z))‖ ≤
      (|ε 0| + |ε 1| + |ε 2|) * ((|t| + 1) * Real.exp (T / 8)) := by
    have n1 := norm_add_le ((ε 0 : ℂ) + (ε 1 : ℂ) * Complex.cos (T * z))
      ((ε 2 : ℂ) * (z * Complex.sin (T * z)))
    have n2 := norm_add_le (ε 0 : ℂ) ((ε 1 : ℂ) * Complex.cos (T * z))
    have e0 : ‖(ε 0 : ℂ)‖ ≤ |ε 0| * ((|t| + 1) * Real.exp (T / 8)) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_mul_of_one_le_right (abs_nonneg _) (by nlinarith)
    have e1 : ‖(ε 1 : ℂ) * Complex.cos (T * z)‖ ≤ |ε 1| * ((|t| + 1) * Real.exp (T / 8)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hc.trans (le_mul_of_one_le_left (Real.exp_pos _).le ht1))
        (abs_nonneg _)
    have e2 : ‖(ε 2 : ℂ) * (z * Complex.sin (T * z))‖ ≤ |ε 2| * ((|t| + 1) * Real.exp (T / 8)) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hzn hs (norm_nonneg _) (by linarith))
        (abs_nonneg _)
    nlinarith
  have hpow : ‖z ^ (2 * N + 2)‖ ≤ (|t| + 1) ^ (2 * N + 2) := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hzn _
  rw [surgeryPerturbationC, norm_mul, norm_mul]
  calc ‖z ^ (2 * N + 2)‖ * ‖cexp (-(cexp (2 * z) + cexp (-(2 * z))))‖ *
        ‖(ε 0 : ℂ) + (ε 1 : ℂ) * Complex.cos (T * z) + (ε 2 : ℂ) * (z * Complex.sin (T * z))‖
      ≤ (|t| + 1) ^ (2 * N + 2) * surgeryDecay t *
          ((|ε 0| + |ε 1| + |ε 2|) * ((|t| + 1) * Real.exp (T / 8))) :=
        mul_le_mul (mul_le_mul hpow (norm_cexp_envelope_le hz) (norm_nonneg _) (by positivity))
          hinner (norm_nonneg _) (by have := surgeryDecay_pos t; positivity)
    _ = _ := by ring

/-- **Cauchy bound** for the perturbation and all its derivatives. -/
theorem abs_iteratedDeriv_surgeryPerturbation_le (N k : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ)
    (t : ℝ) : |iteratedDeriv k (surgeryPerturbation N T ε) t| ≤
      k.factorial * 8 ^ k * ((|ε 0| + |ε 1| + |ε 2|) *
        ((|t| + 1) ^ (2 * N + 3) * Real.exp (T / 8) * surgeryDecay t)) := by
  rw [surgeryPerturbation_eq_re, iteratedDeriv_re_ofReal (differentiable_surgeryPerturbationC N T ε)]
  refine (Complex.abs_re_le_norm _).trans ?_
  have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num : (0 : ℝ) < 1 / 8)
    (differentiable_surgeryPerturbationC N T ε).diffContOnCl (c := (t : ℂ)) fun z hz =>
      norm_surgeryPerturbationC_le N hT ε (t := t) (le_of_eq (mem_sphere_iff_norm.mp hz))
  refine h.trans (le_of_eq ?_)
  have h8 : (8 : ℝ) ^ k * (1 / 8) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [div_eq_iff (by positivity)]
  field_simp
  rw [mul_assoc ((|ε 0| + |ε 1| + |ε 2|) * surgeryDecay t), h8, mul_one]

/-- A quadratic bound: `κ y - y²/(2w) ≤ κ² w / 2`. -/
theorem mul_sub_sq_div_le {κ y w : ℝ} (hw : 0 < w) :
    κ * y - y ^ 2 / (2 * w) ≤ κ ^ 2 * w / 2 := by
  have key : κ * y - y ^ 2 / (2 * w) = κ ^ 2 * w / 2 - (y - κ * w) ^ 2 / (2 * w) := by
    field_simp; ring
  rw [key]
  have : 0 ≤ (y - κ * w) ^ 2 / (2 * w) := by positivity
  linarith

theorem exp_two_mul_abs (t : ℝ) : Real.exp (2 * |t|) = Real.exp |t| ^ 2 := by
  rw [← Real.exp_nat_mul]; norm_num

/-- `e^{B|t|} (|t| + 1)^m ϖ(t)` is bounded uniformly in `t`. -/
theorem exp_mul_pow_mul_surgeryDecay_le (B : ℝ) (m : ℕ) (t : ℝ) :
    Real.exp (B * |t|) * ((|t| + 1) ^ m * surgeryDecay t) ≤
      m.factorial * Real.exp (1 + (|B| + 1) ^ 2 * Real.exp (1 / 4) / 2) := by
  set y := Real.exp |t|
  set w := Real.exp (1 / 4)
  have hw : 0 < w := Real.exp_pos _
  have hy : |t| + 1 ≤ y := Real.add_one_le_exp _
  have h1 := pow_le_factorial_mul_exp (by positivity : (0 : ℝ) ≤ |t| + 1) m
  have hB : B * |t| ≤ |B| * y := by
    have h1' : |t| ≤ y := by linarith
    calc B * |t| ≤ |B| * |t| := mul_le_mul_of_nonneg_right (le_abs_self B) (abs_nonneg t)
      _ ≤ |B| * y := mul_le_mul_of_nonneg_left h1' (abs_nonneg B)
  have hq := mul_sub_sq_div_le (κ := |B| + 1) (y := y) hw
  have hexp : B * |t| + (|t| + 1) - y ^ 2 / (2 * w) ≤ 1 + (|B| + 1) ^ 2 * w / 2 := by nlinarith
  rw [surgeryDecay, exp_two_mul_abs]
  calc Real.exp (B * |t|) * ((|t| + 1) ^ m * Real.exp (-(y ^ 2 / (2 * w))))
      ≤ Real.exp (B * |t|) * ((m.factorial * Real.exp (|t| + 1)) * Real.exp (-(y ^ 2 / (2 * w)))) := by
        gcongr
    _ = m.factorial * (Real.exp (B * |t|) * Real.exp (|t| + 1) * Real.exp (-(y ^ 2 / (2 * w)))) := by
        ring
    _ = m.factorial * Real.exp (B * |t| + (|t| + 1) + -(y ^ 2 / (2 * w))) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)

/-- **Ratio to the renewal increment.** `(t + 1)^m ϖ(t) ≤ K ν(t)` on `t ≥ 0`. -/
theorem pow_mul_surgeryDecay_le_increment (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (t + 1) ^ m * surgeryDecay t ≤
      m.factorial * Real.exp (1 + Real.pi ^ 2 * Real.exp (1 / 4) / 2) / (2 * Real.pi) *
        thetaRenewalIncrement t := by
  set y := Real.exp t
  set w := Real.exp (1 / 4)
  have hw : 0 < w := Real.exp_pos _
  have hν := thetaRenewalIncrement_ge t
  have h1 := pow_le_factorial_mul_exp (by positivity : (0 : ℝ) ≤ t + 1) m
  have hq := mul_sub_sq_div_le (κ := Real.pi) (y := y) hw
  have hexp : (t + 1) - y ^ 2 / (2 * w) ≤ 1 + Real.pi ^ 2 * w / 2 + (5 / 4 * t - Real.pi * y) := by
    nlinarith
  have hpi := Real.pi_pos
  rw [surgeryDecay, abs_of_nonneg ht, show Real.exp (2 * t) = y ^ 2 by
    rw [← Real.exp_nat_mul]; norm_num]
  calc (t + 1) ^ m * Real.exp (-(y ^ 2 / (2 * w)))
      ≤ (m.factorial * Real.exp (t + 1)) * Real.exp (-(y ^ 2 / (2 * w))) := by gcongr
    _ = m.factorial * Real.exp ((t + 1) + -(y ^ 2 / (2 * w))) := by
        rw [Real.exp_add (t + 1) (-(y ^ 2 / (2 * w)))]; ring
    _ ≤ m.factorial * Real.exp (1 + Real.pi ^ 2 * w / 2 + (5 / 4 * t - Real.pi * y)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    _ = m.factorial * Real.exp (1 + Real.pi ^ 2 * w / 2) / (2 * Real.pi) *
          (2 * Real.pi * Real.exp (5 / 4 * t - Real.pi * y)) := by
        rw [Real.exp_add]; field_simp
    _ ≤ _ := by gcongr

/-- `R(t) ≥ 2 e^{t/4 - π e^t}`. -/
theorem thetaLogTail_ge (t : ℝ) : 2 * Real.exp (t / 4 - Real.pi * Real.exp t) ≤ thetaLogTail t := by
  have h := hasSum_thetaLogTail t
  have := h.summable.le_tsum 0 (fun j _ => by positivity)
  rw [h.tsum_eq] at this
  simpa using this

/-- **Ratio to the arithmetic tail.** `(t + 1)^m ϖ(t) ≤ K R(t)` on `t ≥ 0`. -/
theorem pow_mul_surgeryDecay_le_thetaLogTail (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (t + 1) ^ m * surgeryDecay t ≤
      m.factorial * Real.exp (1 + (Real.pi + 1) ^ 2 * Real.exp (1 / 4) / 2) / 2 * thetaLogTail t := by
  set y := Real.exp t
  set w := Real.exp (1 / 4)
  have hw : 0 < w := Real.exp_pos _
  have hR := thetaLogTail_ge t
  have hy : t + 1 ≤ y := Real.add_one_le_exp _
  have h1 := pow_le_factorial_mul_exp (by positivity : (0 : ℝ) ≤ t + 1) m
  have hq := mul_sub_sq_div_le (κ := Real.pi + 1) (y := y) hw
  have hexp : (t + 1) - y ^ 2 / (2 * w) ≤
      1 + (Real.pi + 1) ^ 2 * w / 2 + (t / 4 - Real.pi * y) := by nlinarith
  rw [surgeryDecay, abs_of_nonneg ht, show Real.exp (2 * t) = y ^ 2 by
    rw [← Real.exp_nat_mul]; norm_num]
  calc (t + 1) ^ m * Real.exp (-(y ^ 2 / (2 * w)))
      ≤ (m.factorial * Real.exp (t + 1)) * Real.exp (-(y ^ 2 / (2 * w))) := by gcongr
    _ = m.factorial * Real.exp ((t + 1) + -(y ^ 2 / (2 * w))) := by
        rw [Real.exp_add (t + 1) (-(y ^ 2 / (2 * w)))]; ring
    _ ≤ m.factorial * Real.exp (1 + (Real.pi + 1) ^ 2 * w / 2 + (t / 4 - Real.pi * y)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    _ = m.factorial * Real.exp (1 + (Real.pi + 1) ^ 2 * w / 2) / 2 *
          (2 * Real.exp (t / 4 - Real.pi * y)) := by
        rw [Real.exp_add]; ring
    _ ≤ _ := by gcongr

/-! ## Deletion shifts -/

/-- The first atom dominates `2π(2π - 3) e^{-π e^{2x}}` on `x ≥ 0`. -/
theorem thetaCuspSourceTerm_one_ge {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.pi * (2 * Real.pi - 3) * Real.exp (-(Real.pi * Real.exp (2 * x))) ≤
      thetaCuspSourceTerm x 1 := by
  rw [thetaCuspSourceTerm, thetaCuspSeed]
  simp only [Nat.cast_one, one_mul]
  set u := Real.exp x
  have hu : 1 ≤ u := Real.one_le_exp hx
  have hu2 : Real.exp (2 * x) = u ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have he : 1 ≤ Real.exp (x / 2) := Real.one_le_exp (by linarith)
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hcore : 2 * Real.pi - 3 ≤ 2 * Real.pi * u ^ 4 - 3 * u ^ 2 := by
    have h1 : 1 ≤ u ^ 2 := by nlinarith
    nlinarith [mul_le_mul h1 h1 zero_le_one (by linarith)]
  rw [hu2, show -Real.pi * u ^ 2 = -(Real.pi * u ^ 2) by ring]
  have hE := Real.exp_pos (-(Real.pi * u ^ 2))
  calc 2 * Real.pi * (2 * Real.pi - 3) * Real.exp (-(Real.pi * u ^ 2))
      ≤ 1 * (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2) * Real.exp (-(Real.pi * u ^ 2))) := by
        rw [one_mul]; gcongr
    _ ≤ _ := by
        gcongr
        have : 0 ≤ 2 * Real.pi * u ^ 4 - 3 * u ^ 2 := by linarith
        positivity

/-- `(2x + 1)^m ϖ(2x) ≤ K a₁(x)` on `x ≥ 0`. -/
theorem pow_mul_surgeryDecay_two_mul_le (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (2 * x + 1) ^ m * Real.exp (-(Real.exp (4 * x) / (2 * Real.exp (1 / 4)))) ≤
      m.factorial * Real.exp (1 + (Real.pi + 1) ^ 2 * Real.exp (1 / 4) / 2) /
        (2 * Real.pi * (2 * Real.pi - 3)) * thetaCuspSourceTerm x 1 := by
  set Y := Real.exp (2 * x)
  set w := Real.exp (1 / 4)
  have hw : 0 < w := Real.exp_pos _
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have ha := thetaCuspSourceTerm_one_ge hx
  have hY : 2 * x + 1 ≤ Y := Real.add_one_le_exp _
  have h1 := pow_le_factorial_mul_exp (by positivity : (0 : ℝ) ≤ 2 * x + 1) m
  have hY4 : Real.exp (4 * x) = Y ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hq := mul_sub_sq_div_le (κ := Real.pi + 1) (y := Y) hw
  have hexp : (2 * x + 1) + -(Y ^ 2 / (2 * w)) ≤ 1 + (Real.pi + 1) ^ 2 * w / 2 + -(Real.pi * Y) := by
    nlinarith
  have hc : 0 < 2 * Real.pi * (2 * Real.pi - 3) := by nlinarith
  have hc3 : (2 * Real.pi - 3) ≠ 0 := by linarith
  rw [hY4]
  calc (2 * x + 1) ^ m * Real.exp (-(Y ^ 2 / (2 * w)))
      ≤ (m.factorial * Real.exp (2 * x + 1)) * Real.exp (-(Y ^ 2 / (2 * w))) := by gcongr
    _ = m.factorial * Real.exp ((2 * x + 1) + -(Y ^ 2 / (2 * w))) := by
        rw [Real.exp_add (2 * x + 1) (-(Y ^ 2 / (2 * w)))]; ring
    _ ≤ m.factorial * Real.exp (1 + (Real.pi + 1) ^ 2 * w / 2 + -(Real.pi * Y)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = m.factorial * Real.exp (1 + (Real.pi + 1) ^ 2 * w / 2) / (2 * Real.pi * (2 * Real.pi - 3)) *
          (2 * Real.pi * (2 * Real.pi - 3) * Real.exp (-(Real.pi * Y))) := by
        rw [Real.exp_add]; field_simp; rw [div_self (by linarith)]
    _ ≤ _ := by gcongr

/-- The summable weight `G(n) = (3n)^m e^{-(n-1)/(2w)}` of the deletion shifts. -/
def deletionShiftWeight (m : ℕ) (n : ℕ) : ℝ :=
  (3 * n) ^ m * Real.exp (-(((n : ℝ) - 1) / (2 * Real.exp (1 / 4))))

theorem deletionShiftWeight_nonneg (m n : ℕ) : 0 ≤ deletionShiftWeight m n := by
  unfold deletionShiftWeight; positivity

theorem summable_deletionShiftWeight (m : ℕ) : Summable (deletionShiftWeight m) := by
  set w := Real.exp (1 / 4)
  set r := Real.exp (-(1 / (2 * w)))
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_zero]
    have : 0 < w := Real.exp_pos _
    exact Real.exp_lt_exp.mpr (by simp only [neg_lt_zero]; positivity)
  have h := (summable_pow_mul_geometric_of_norm_lt_one m hr).mul_left (3 ^ m * Real.exp (1 / (2 * w)))
  refine h.congr fun n => ?_
  rw [deletionShiftWeight, mul_pow, show r ^ n = Real.exp (n * -(1 / (2 * w))) by
    rw [← Real.exp_nat_mul]]
  rw [show -(((n : ℝ) - 1) / (2 * w)) = n * -(1 / (2 * w)) + 1 / (2 * w) by ring, Real.exp_add]
  ring

/-- **Uniform deletion bound.** For every finite prime set and `x ≥ 0`, the shifted envelope sum
`Σ_{T ⊆ S} (2(x + log ∏T) + 1)^m ϖ(2(x + log ∏T))` is at most `K a₁(x)`. -/
theorem sum_deletionShift_le (m : ℕ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {x : ℝ} (hx : 0 ≤ x) :
    ∑ T ∈ S.powerset, (2 * (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ)) + 1) ^ m *
        surgeryDecay (2 * (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ))) ≤
      (∑' n, deletionShiftWeight m n) * (m.factorial *
        Real.exp (1 + (Real.pi + 1) ^ 2 * Real.exp (1 / 4) / 2) /
          (2 * Real.pi * (2 * Real.pi - 3))) * thetaCuspSourceTerm x 1 := by
  classical
  set w := Real.exp (1 / 4)
  have hw : 0 < w := Real.exp_pos _
  set A := (2 * x + 1) ^ m * Real.exp (-(Real.exp (4 * x) / (2 * w)))
  have hterm : ∀ T ∈ S.powerset, (2 * (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ)) + 1) ^ m *
      surgeryDecay (2 * (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ))) ≤
        A * deletionShiftWeight m (∏ p ∈ T, p) := by
    intro T hT
    set d : ℕ := ∏ p ∈ T, p
    have hd1 : (1 : ℝ) ≤ d := by
      have : 0 < d := Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
      exact_mod_cast this
    have hlog0 : 0 ≤ Real.log d := Real.log_nonneg hd1
    have hlog1 : Real.log d ≤ d := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hy0 : 0 ≤ 2 * (x + Real.log d) := by positivity
    have hpow : (2 * (x + Real.log d) + 1) ^ m ≤ (2 * x + 1) ^ m * (3 * d) ^ m := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ m
      nlinarith
    have hdec : surgeryDecay (2 * (x + Real.log d)) ≤ Real.exp (-(Real.exp (4 * x) / (2 * w))) *
        Real.exp (-(((d : ℝ) - 1) / (2 * w))) := by
      rw [surgeryDecay, abs_of_nonneg hy0, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have he4 : Real.exp (2 * (2 * (x + Real.log d))) = Real.exp (4 * x) * (d : ℝ) ^ 4 := by
        rw [show 2 * (2 * (x + Real.log d)) = 4 * x + 4 * Real.log d by ring, Real.exp_add,
          show 4 * Real.log (d : ℝ) = (4 : ℕ) * Real.log d by norm_num, ← Real.log_pow,
          Real.exp_log (by positivity)]
      rw [he4]
      have hx4 : 1 ≤ Real.exp (4 * x) := Real.one_le_exp (by linarith)
      have hd4 : (d : ℝ) ≤ (d : ℝ) ^ 4 := by
        calc (d : ℝ) = (d : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (d : ℝ) ^ 4 := pow_le_pow_right₀ hd1 (by norm_num)
      have key : Real.exp (4 * x) + ((d : ℝ) - 1) ≤ Real.exp (4 * x) * (d : ℝ) ^ 4 := by nlinarith
      have key2 := div_le_div_of_nonneg_right key (by positivity : (0 : ℝ) ≤ 2 * Real.exp (1 / 4))
      rw [add_div] at key2
      simp only [w] at *
      linarith
    calc (2 * (x + Real.log d) + 1) ^ m * surgeryDecay (2 * (x + Real.log d))
        ≤ ((2 * x + 1) ^ m * (3 * d) ^ m) * (Real.exp (-(Real.exp (4 * x) / (2 * w))) *
            Real.exp (-(((d : ℝ) - 1) / (2 * w)))) :=
          mul_le_mul hpow hdec (surgeryDecay_pos _).le (by positivity)
      _ = A * deletionShiftWeight m d := by simp only [A, deletionShiftWeight]; ring
  have hsum : ∑ T ∈ S.powerset, deletionShiftWeight m (∏ p ∈ T, p) ≤ ∑' n, deletionShiftWeight m n := by
    rw [← Finset.sum_image (f := deletionShiftWeight m) (g := fun T : Finset ℕ => ∏ p ∈ T, p)
      (Sieve.prod_injOn_powerset hS)]
    exact (summable_deletionShiftWeight m).sum_le_tsum _ fun n _ => deletionShiftWeight_nonneg m n
  have hA := pow_mul_surgeryDecay_two_mul_le m hx
  have hA0 : 0 ≤ A := by positivity
  calc _ ≤ ∑ T ∈ S.powerset, A * deletionShiftWeight m (∏ p ∈ T, p) := Finset.sum_le_sum hterm
    _ = A * ∑ T ∈ S.powerset, deletionShiftWeight m (∏ p ∈ T, p) := by rw [Finset.mul_sum]
    _ ≤ A * ∑' n, deletionShiftWeight m n := mul_le_mul_of_nonneg_left hsum hA0
    _ ≤ _ := by
        rw [mul_comm A, mul_assoc]
        exact mul_le_mul_of_nonneg_left hA (tsum_nonneg fun n => deletionShiftWeight_nonneg m n)

end

end RHTower
