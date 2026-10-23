import GaloisForLFunctions.TransHorizonIncidenceMechanics.OscillatingPrimePatternsArePaidExactlyAtTheCriticalZeros
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheQuarterLawOfResidueFlips
import GaloisForLFunctions.RHTower.ZetaEulerLogarithmOnBoxes

/-!
# The phase law of oscillating prime patterns

For `|a| ≤ 1` and `t₀, φ ∈ ℝ` let `f(p) = a cos(t₀ log p + φ)` (`phasePattern`, completely
multiplicative) and `c(d) = f(d) d^{-1/2}` (`phaseWeight`). For `t₀ ≠ 0`
(`receiverBounded_phaseWeight_iff`):

  `c` is paid  ⇔  `a cos φ < 1`  or  `ζ(1/2 + it₀) = 0`.

Only the real part `Re(a e^{iφ}) = a cos φ` of the complex amplitude decides the receiver.

**Mechanism.** `f(p) p^{-w} = b p^{-(w − it₀)} + b̄ p^{-(w + it₀)}` with `b = (a/2) e^{iφ}`, so with
`ℓ` the Euler logarithm of `ζ`, `log|F(w)| = Re(b ℓ(w − it₀) + b̄ ℓ(w + it₀)) + O(1)`
(`abs_log_norm_phaseSeries_sub_le`). `Re ℓ = log|ζ|` carries the factor `a cos φ`; `Im ℓ = arg ζ`
carries `a sin φ`. The argument stays bounded at the pole (`RHTower.exists_abs_im_zetaEulerLog_le`)
and is `O(log log t)` at height `t`, so the line integrand has the singularity
`|t − t₀|^{-(a cos φ)⁺}` and polylogarithmic growth: integrable iff `a cos φ < 1`. At `a cos φ = 1`
the pattern is `cos(t₀ log p)`, decided by `receiverBounded_oscWeight_iff`.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The phase pattern -/

/-- The phase-shifted oscillating prime pattern `f(p) = a cos(t₀ log p + φ)`. -/
def phasePattern (a t₀ φ : ℝ) : ℕ →*₀ ℝ :=
  primeValueHom fun p => a * Real.cos (t₀ * Real.log p + φ)

theorem phasePattern_prime (a t₀ φ : ℝ) {p : ℕ} (hp : p.Prime) :
    phasePattern a t₀ φ p = a * Real.cos (t₀ * Real.log p + φ) :=
  primeValueHom_prime _ hp

theorem abs_phasePattern_le {a : ℝ} (ha : |a| ≤ 1) (t₀ φ : ℝ) (n : ℕ) :
    |phasePattern a t₀ φ n| ≤ 1 :=
  abs_patternHom_le_one _ (fun p hp => by
    rw [phasePattern_prime a t₀ φ hp, abs_mul]
    exact mul_le_one₀ ha (abs_nonneg _) (Real.abs_cos_le_one _)) n

/-- Reflecting the frequency reflects the phase. -/
theorem phasePattern_neg (a t₀ φ : ℝ) : phasePattern a (-t₀) φ = phasePattern a t₀ (-φ) := by
  unfold phasePattern
  congr 1
  funext p
  rw [show -t₀ * Real.log p + φ = -(t₀ * Real.log p + -φ) by ring, Real.cos_neg]

/-- At full real amplitude `a cos φ = 1` the pattern is `cos(t₀ log p)`. -/
theorem phasePattern_eq_oscPattern_one {a φ : ℝ} (ha : |a| ≤ 1) (h : a * Real.cos φ = 1)
    (t₀ : ℝ) : phasePattern a t₀ φ = oscPattern 1 t₀ := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [abs_nonneg a, sq_abs a]
  have hsq : (a * Real.sin φ) ^ 2 = a ^ 2 - (a * Real.cos φ) ^ 2 := by
    linear_combination a ^ 2 * Real.sin_sq_add_cos_sq φ
  have hsin : a * Real.sin φ = 0 := by
    rw [h] at hsq
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      (le_antisymm (by rw [hsq]; linarith) (sq_nonneg _))
  unfold phasePattern oscPattern
  congr 1
  funext p
  rw [Real.cos_add]
  linear_combination Real.cos (t₀ * Real.log p) * h - Real.sin (t₀ * Real.log p) * hsin

/-- The half-damped phase weight `f(d) d^{-1/2}`. -/
def phaseWeight (a t₀ φ : ℝ) (d : ℕ) : ℝ := phasePattern a t₀ φ d * (d : ℝ) ^ (-(1 / 2 : ℝ))

theorem phaseWeight_neg (a t₀ φ : ℝ) : phaseWeight a (-t₀) φ = phaseWeight a t₀ (-φ) := by
  funext d; simp only [phaseWeight, phasePattern_neg]

/-! ### The Euler comparison with the Euler logarithm of `ζ` -/

/-- `cos(t₀ log p + φ) p^{-w} = (e^{iφ} p^{-(w − it₀)} + e^{-iφ} p^{-(w + it₀)})/2`. -/
theorem cos_add_mul_cpow_eq {p : ℕ} (hp : 0 < p) (t₀ φ : ℝ) (w : ℂ) :
    ((Real.cos (t₀ * Real.log p + φ) : ℝ) : ℂ) * (p : ℂ) ^ (-w) =
      (Complex.exp (φ * I) * (p : ℂ) ^ (-(w - t₀ * I)) +
        Complex.exp (((-φ : ℝ) : ℂ) * I) * (p : ℂ) ^ (-(w + t₀ * I))) / 2 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p)]
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hp0,
    Complex.cpow_def_of_ne_zero hp0, hlog, Complex.ofReal_cos, Complex.cos, div_mul_eq_mul_div,
    add_mul, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  congr 1 <;> (congr 1; push_cast; ring)

/-- `|Σ_p p^{-v} − ℓ(v)| ≤ Σ_p p^{-2}` on `Re v > 1`. -/
theorem norm_tsum_prime_cpow_sub_zetaEulerLog_le {v : ℂ} (hv : 1 < v.re) :
    ‖∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-v) - RHTower.zetaEulerLog v‖ ≤ primeSquareMass := by
  have h := norm_tsum_char_sub_eulerLog_le (1 : DirichletCharacter ℂ 1) hv
  have h1 : ∀ x : ZMod 1, (1 : DirichletCharacter ℂ 1) x = 1 := fun x =>
    MulChar.one_apply (isUnit_of_subsingleton x)
  simp only [h1, one_mul] at h
  exact h

/-- `‖(a/2) e^{iθ}‖ ≤ 1/2` for `|a| ≤ 1`. -/
theorem norm_half_mul_exp_le {a : ℝ} (ha : |a| ≤ 1) (θ : ℝ) :
    ‖((a / 2 : ℝ) : ℂ) * Complex.exp (θ * I)‖ ≤ 1 / 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one,
    abs_div, abs_two]
  linarith

/-- **The Euler comparison.** On `Re w > 1`,
`|log|F(w)| − Re((a/2)e^{iφ} ℓ(w − it₀) + (a/2)e^{-iφ} ℓ(w + it₀))| ≤ 2S`. -/
theorem abs_log_norm_phaseSeries_sub_le {a : ℝ} (ha : |a| ≤ 1) (t₀ φ : ℝ) {w : ℂ}
    (hw : 1 < w.re) :
    |Real.log ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ -
      (((a / 2 : ℝ) : ℂ) * Complex.exp (φ * I) * RHTower.zetaEulerLog (w - t₀ * I) +
        ((a / 2 : ℝ) : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * I) *
          RHTower.zetaEulerLog (w + t₀ * I)).re| ≤ 2 * primeSquareMass := by
  have hwm : 1 < (w - t₀ * I).re := by simpa using hw
  have hwp : 1 < (w + t₀ * I).re := by simpa using hw
  have hF := abs_log_norm_tsum_sub_re_le (cweightedPatternHom (phasePattern a t₀ φ) w) hw
    fun n => by
      simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_natCast]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_phasePattern_le ha t₀ φ n)
  have hFn : ∑' n, cweightedPatternHom (phasePattern a t₀ φ) w n =
      ∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) := tsum_congr fun n => rfl
  have hsm := summable_prime_cpow_neg hwm
  have hsp := summable_prime_cpow_neg hwp
  have hFp : ∑' p : Nat.Primes, cweightedPatternHom (phasePattern a t₀ φ) w p =
      ((a / 2 : ℝ) : ℂ) * Complex.exp (φ * I) * ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(w - t₀ * I)) +
        ((a / 2 : ℝ) : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * I) *
          ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(w + t₀ * I)) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hsm.mul_left _).tsum_add (hsp.mul_left _)]
    refine tsum_congr fun p => ?_
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      Complex.ofReal_natCast, phasePattern_prime a t₀ φ p.2]
    rw [Complex.ofReal_mul, mul_assoc, cos_add_mul_cpow_eq p.2.pos]
    push_cast
    ring
  rw [hFn, hFp] at hF
  have hS : ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) = primeSquareMass := rfl
  rw [hS] at hF
  set bm : ℂ := ((a / 2 : ℝ) : ℂ) * Complex.exp (φ * I)
  set bp : ℂ := ((a / 2 : ℝ) : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * I)
  set Pm := ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(w - t₀ * I))
  set Pp := ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(w + t₀ * I))
  set L := Real.log ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
  have hdiff : |(bm * Pm + bp * Pp).re -
      (bm * RHTower.zetaEulerLog (w - t₀ * I) + bp * RHTower.zetaEulerLog (w + t₀ * I)).re| ≤
        primeSquareMass := by
    rw [← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ?_
    have heq : bm * Pm + bp * Pp - (bm * RHTower.zetaEulerLog (w - t₀ * I) +
        bp * RHTower.zetaEulerLog (w + t₀ * I)) =
          bm * (Pm - RHTower.zetaEulerLog (w - t₀ * I)) +
            bp * (Pp - RHTower.zetaEulerLog (w + t₀ * I)) := by ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul bm, norm_mul bp]
    have h1 : ‖bm‖ * ‖Pm - RHTower.zetaEulerLog (w - t₀ * I)‖ ≤ 1 / 2 * primeSquareMass :=
      mul_le_mul (norm_half_mul_exp_le ha φ) (norm_tsum_prime_cpow_sub_zetaEulerLog_le hwm)
        (norm_nonneg _) (by norm_num)
    have h2 : ‖bp‖ * ‖Pp - RHTower.zetaEulerLog (w + t₀ * I)‖ ≤ 1 / 2 * primeSquareMass :=
      mul_le_mul (norm_half_mul_exp_le ha (-φ)) (norm_tsum_prime_cpow_sub_zetaEulerLog_le hwp)
        (norm_nonneg _) (by norm_num)
    linarith
  have h3 := abs_sub_le L (bm * Pm + bp * Pp).re
    (bm * RHTower.zetaEulerLog (w - t₀ * I) + bp * RHTower.zetaEulerLog (w + t₀ * I)).re
  linarith

/-- `Re((r e^{iθ}) z) = r (cos θ Re z − sin θ Im z)`. -/
theorem re_mul_exp_mul_I (r θ : ℝ) (z : ℂ) :
    ((r : ℂ) * Complex.exp (θ * I) * z).re = r * (Real.cos θ * z.re - Real.sin θ * z.im) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- `(a/2)(cos θ x − sin θ y) ≤ (a cos θ/2) x + |y|/2` for `|a| ≤ 1`. -/
theorem half_mul_cos_sub_sin_le {a : ℝ} (ha : |a| ≤ 1) (θ x y : ℝ) :
    a / 2 * (Real.cos θ * x - Real.sin θ * y) ≤ a * Real.cos θ / 2 * x + |y| / 2 := by
  have h1 : |a * Real.sin θ| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) (Real.abs_sin_le_one θ)
  have h2 : -(a * Real.sin θ * y) ≤ |y| :=
    calc -(a * Real.sin θ * y) ≤ |a * Real.sin θ * y| := neg_le_abs _
      _ = |a * Real.sin θ| * |y| := abs_mul _ _
      _ ≤ 1 * |y| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |y| := one_mul _
  have heq : a / 2 * (Real.cos θ * x - Real.sin θ * y) =
      a * Real.cos θ / 2 * x + -(a * Real.sin θ * y) / 2 := by ring
  rw [heq]
  linarith

/-- **The phase bound.** On `Re w > 1`, with `Z = |ζ(w − it₀)| |ζ(w + it₀)|`,
`|F(w)| ≤ exp(2S + (|arg-part at w − it₀| + |arg-part at w + it₀|)/2) Z^{(a cos φ)/2}`. -/
theorem norm_phaseSeries_le {a : ℝ} (ha : |a| ≤ 1) (t₀ φ : ℝ) {w : ℂ} (hw : 1 < w.re) :
    ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
      Real.exp (2 * primeSquareMass + (|(RHTower.zetaEulerLog (w - t₀ * I)).im| +
        |(RHTower.zetaEulerLog (w + t₀ * I)).im|) / 2) *
          (‖riemannZeta (w - t₀ * I)‖ * ‖riemannZeta (w + t₀ * I)‖) ^ (a * Real.cos φ / 2) := by
  have hwm : 1 < (w - t₀ * I).re := by simpa using hw
  have hwp : 1 < (w + t₀ * I).re := by simpa using hw
  have hm := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hwm.le)
  have hp := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hwp.le)
  set F := ∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)
  rcases (norm_nonneg F).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  have h := (abs_le.mp (abs_log_norm_phaseSeries_sub_le ha t₀ φ hw)).2
  rw [Complex.add_re, re_mul_exp_mul_I, re_mul_exp_mul_I, RHTower.re_zetaEulerLog hwm,
    RHTower.re_zetaEulerLog hwp] at h
  have hb1 := half_mul_cos_sub_sin_le ha φ (Real.log ‖riemannZeta (w - t₀ * I)‖)
    (RHTower.zetaEulerLog (w - t₀ * I)).im
  have hb2 := half_mul_cos_sub_sin_le ha (-φ) (Real.log ‖riemannZeta (w + t₀ * I)‖)
    (RHTower.zetaEulerLog (w + t₀ * I)).im
  rw [Real.cos_neg] at hb2 h
  rw [← Real.exp_log hpos, Real.rpow_def_of_pos (mul_pos hm hp), ← Real.exp_add,
    Real.log_mul hm.ne' hp.ne']
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- **The phase bound at large heights**: `|F(w)| ≤ exp(2S + (|ℓ(w − it₀)| + |ℓ(w + it₀)|)/2)`. -/
theorem norm_phaseSeries_le_exp {a : ℝ} (ha : |a| ≤ 1) (t₀ φ : ℝ) {w : ℂ} (hw : 1 < w.re) :
    ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
      Real.exp (2 * primeSquareMass + (‖RHTower.zetaEulerLog (w - t₀ * I)‖ +
        ‖RHTower.zetaEulerLog (w + t₀ * I)‖) / 2) := by
  set F := ∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)
  rcases (norm_nonneg F).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  have h := (abs_le.mp (abs_log_norm_phaseSeries_sub_le ha t₀ φ hw)).2
  have hre := Complex.re_le_norm (((a / 2 : ℝ) : ℂ) * Complex.exp (φ * I) *
      RHTower.zetaEulerLog (w - t₀ * I) + ((a / 2 : ℝ) : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * I) *
        RHTower.zetaEulerLog (w + t₀ * I))
  have hn := norm_add_le (((a / 2 : ℝ) : ℂ) * Complex.exp (φ * I) *
      RHTower.zetaEulerLog (w - t₀ * I)) (((a / 2 : ℝ) : ℂ) * Complex.exp (((-φ : ℝ) : ℂ) * I) *
        RHTower.zetaEulerLog (w + t₀ * I))
  rw [norm_mul _ (RHTower.zetaEulerLog (w - t₀ * I)),
    norm_mul _ (RHTower.zetaEulerLog (w + t₀ * I))] at hn
  have h1 := mul_le_mul_of_nonneg_right (norm_half_mul_exp_le ha φ)
    (norm_nonneg (RHTower.zetaEulerLog (w - t₀ * I)))
  have h2 := mul_le_mul_of_nonneg_right (norm_half_mul_exp_le ha (-φ))
    (norm_nonneg (RHTower.zetaEulerLog (w + t₀ * I)))
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr (by linarith)

/-! ### Strip bounds -/

/-- `d^{-α/2} ≤ D^{1/2} (x^{-α⁺/2} + 1)` for `0 < x ≤ d ≤ D`, `1 ≤ D`, `|α| ≤ 1`. -/
theorem rpow_neg_half_le {x d D α : ℝ} (hx : 0 < x) (hxd : x ≤ d) (hdD : d ≤ D) (hD : 1 ≤ D)
    (hα : |α| ≤ 1) :
    d ^ (-(α / 2)) ≤ D ^ (1 / 2 : ℝ) * (x ^ (-(max α 0 / 2)) + 1) := by
  have hd : 0 < d := lt_of_lt_of_le hx hxd
  have hD1 : 1 ≤ D ^ (1 / 2 : ℝ) := Real.one_le_rpow hD (by norm_num)
  have hα' := abs_le.mp hα
  rcases le_total 0 α with h0 | h0
  · rw [max_eq_left h0]
    have h1 : d ^ (-(α / 2)) ≤ x ^ (-(α / 2)) := Real.rpow_le_rpow_of_nonpos hx hxd (by linarith)
    have h2 : 0 ≤ x ^ (-(α / 2)) := Real.rpow_nonneg hx.le _
    nlinarith
  · rw [max_eq_right h0, zero_div, neg_zero, Real.rpow_zero]
    have h1 : d ^ (-(α / 2)) ≤ D ^ (-(α / 2)) := Real.rpow_le_rpow hd.le hdD (by linarith)
    have h2 : D ^ (-(α / 2)) ≤ D ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
    nlinarith

/-- `w ∓ it₀` in the form `(1 + u) + iτ`. -/
theorem sub_mul_I_eq (w : ℂ) (t₀ : ℝ) :
    w - t₀ * I = (((1 + (w.re - 1)) : ℝ) : ℂ) + ((w.im - t₀ : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

theorem add_mul_I_eq (w : ℂ) (t₀ : ℝ) :
    w + t₀ * I = (((1 + (w.re - 1)) : ℝ) : ℂ) + ((w.im + t₀ : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-- **The small-height bound** (`t₀ > 0`): on `1 < Re w ≤ 2`, `0 < Im w ≤ 2t₀ + 18`, `Im w ≠ t₀`,
`|F(w)| ≤ A(|Im w − t₀|^{-(a cos φ)⁺/2} + 1)`. -/
theorem exists_norm_phaseSeries_le_small {a t₀ : ℝ} (ha : |a| ≤ 1) (ht₀ : 0 < t₀) (φ : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 0 < w.im → w.im ≤ 2 * t₀ + 18 →
      w.im ≠ t₀ → ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        A * (|w.im - t₀| ^ (-(max (a * Real.cos φ) 0 / 2)) + 1) := by
  set H : ℝ := 3 * t₀ + 18
  set D : ℝ := 1 + H
  have hD : 1 ≤ D := by simp only [D, H]; linarith
  obtain ⟨C, hC⟩ := RHTower.exists_abs_im_zetaEulerLog_le H
  obtain ⟨m, K, hm, hmK⟩ := RHTower.exists_norm_zeta_mul_sub_one_bounds H
  set α : ℝ := a * Real.cos φ
  have hα : |α| ≤ 1 := by
    rw [abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) (Real.abs_cos_le_one φ)
  set Λ : ℝ := max (max (K ^ 2 / t₀) (D / m ^ 2)) 1
  have hΛ : 1 ≤ Λ := le_max_right _ _
  refine ⟨Real.exp (2 * primeSquareMass + C) * Λ ^ 2 * D ^ (1 / 2 : ℝ), by positivity,
    fun w hw hw2 ht htT hne => ?_⟩
  have hu : 0 < w.re - 1 := by linarith
  have hu1 : w.re - 1 ≤ 1 := by linarith
  have hτm : |w.im - t₀| ≤ H := by rw [abs_le]; constructor <;> linarith
  have hτp : |w.im + t₀| ≤ H := by rw [abs_le]; constructor <;> linarith
  have hwm : 1 < (w - t₀ * I).re := by simpa using hw
  have hwp : 1 < (w + t₀ * I).re := by simpa using hw
  -- the arguments are bounded on the box
  have hCm := hC _ _ hu hu1 hτm
  have hCp := hC _ _ hu hu1 hτp
  rw [← sub_mul_I_eq] at hCm
  rw [← add_mul_I_eq] at hCp
  have hexp : Real.exp (2 * primeSquareMass + (|(RHTower.zetaEulerLog (w - t₀ * I)).im| +
      |(RHTower.zetaEulerLog (w + t₀ * I)).im|) / 2) ≤ Real.exp (2 * primeSquareMass + C) :=
    Real.exp_le_exp.mpr (by linarith)
  -- the pole factor
  have hvm_im : |(w - t₀ * I).im| ≤ H := by simpa using hτm
  have hvp_im : |(w + t₀ * I).im| ≤ H := by simpa using hτp
  obtain ⟨hm1, hK1⟩ := hmK _ hwm (by simpa using hw2) hvm_im
  obtain ⟨hm2, hK2⟩ := hmK _ hwp (by simpa using hw2) hvp_im
  set zm := ‖riemannZeta (w - t₀ * I)‖
  set zp := ‖riemannZeta (w + t₀ * I)‖
  set dm := ‖w - t₀ * I - 1‖
  set dp := ‖w + t₀ * I - 1‖
  have hnorm_le : ∀ v : ℂ, 1 < v.re → v.re ≤ 2 → |v.im| ≤ H → ‖v - 1‖ ≤ D := fun v hv hv2 hvH =>
    calc ‖v - 1‖ ≤ |(v - 1).re| + |(v - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + H := by
        rw [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero,
          abs_of_pos (by linarith)]
        linarith
  have hdmD : dm ≤ D := hnorm_le _ hwm (by simpa using hw2) hvm_im
  have hdpD : dp ≤ D := hnorm_le _ hwp (by simpa using hw2) hvp_im
  have hx : 0 < |w.im - t₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hxdm : |w.im - t₀| ≤ dm := by
    have := Complex.abs_im_le_norm (w - t₀ * I - 1)
    simpa using this
  have hdpt : t₀ ≤ dp := by
    have := Complex.abs_im_le_norm (w + t₀ * I - 1)
    have him : (w + t₀ * I - 1).im = w.im + t₀ := by simp
    rw [him, abs_of_pos (by linarith)] at this
    linarith
  have hdm0 : 0 < dm := lt_of_lt_of_le hx hxdm
  have hdp0 : 0 < dp := lt_of_lt_of_le ht₀ hdpt
  have hzm0 : 0 < zm := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hwm.le)
  have hzp0 : 0 < zp := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hwp.le)
  -- `Z = Y/dm` with `m²/D ≤ Y ≤ K²/t₀`
  set Y : ℝ := zm * dm * zp
  have hY0 : 0 < Y := by positivity
  have hzpK : zp ≤ K / t₀ := by
    rw [le_div_iff₀ ht₀]
    exact (mul_le_mul_of_nonneg_left hdpt hzp0.le).trans hK2
  have hzpm : m / D ≤ zp := by
    rw [div_le_iff₀ (by linarith)]
    exact hm2.trans (mul_le_mul_of_nonneg_left hdpD hzp0.le)
  have hK0 : 0 ≤ K := hm.le.trans (hm1.trans hK1)
  have hYup : Y ≤ Λ := by
    have : Y ≤ K * (K / t₀) := mul_le_mul hK1 hzpK hzp0.le hK0
    refine this.trans ((le_of_eq ?_).trans ((le_max_left _ _).trans (le_max_left _ _)))
    ring
  have hYlow : Y⁻¹ ≤ Λ := by
    have hlow : m * (m / D) ≤ Y := mul_le_mul hm1 hzpm (by positivity) (by positivity)
    have hinv : Y⁻¹ ≤ (m * (m / D))⁻¹ := inv_anti₀ (by positivity) hlow
    refine hinv.trans ((le_of_eq ?_).trans ((le_max_right _ _).trans (le_max_left _ _)))
    field_simp
  have hYpow : Y ^ (α / 2) ≤ Λ ^ 2 :=
    rpow_le_sq_of_bounds hY0 hΛ hYup hYlow (by rw [abs_div, abs_two]; linarith)
  have hZ : zm * zp = Y / dm := by simp only [Y]; field_simp
  have hZpow : (zm * zp) ^ (α / 2) = Y ^ (α / 2) * dm ^ (-(α / 2)) := by
    rw [hZ, Real.div_rpow hY0.le hdm0.le, Real.rpow_neg hdm0.le, div_eq_mul_inv]
  have hdpow := rpow_neg_half_le hx hxdm hdmD hD hα
  calc ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
      ≤ Real.exp (2 * primeSquareMass + (|(RHTower.zetaEulerLog (w - t₀ * I)).im| +
          |(RHTower.zetaEulerLog (w + t₀ * I)).im|) / 2) * (zm * zp) ^ (α / 2) :=
        norm_phaseSeries_le ha t₀ φ hw
    _ ≤ Real.exp (2 * primeSquareMass + C) * (Λ ^ 2 * (D ^ (1 / 2 : ℝ) *
          (|w.im - t₀| ^ (-(max α 0 / 2)) + 1))) := by
        refine mul_le_mul hexp ?_ (by positivity) (by positivity)
        rw [hZpow]
        exact mul_le_mul hYpow hdpow (by positivity) (by positivity)
    _ = Real.exp (2 * primeSquareMass + C) * Λ ^ 2 * D ^ (1 / 2 : ℝ) *
          (|w.im - t₀| ^ (-(max α 0 / 2)) + 1) := by ring

/-- **The large-height bound** (`t₀ > 0`): for `Im w > 2t₀ + 18`, `|F(w)| ≤ B₁ (Im w)^{1/4}`. -/
theorem exists_norm_phaseSeries_le_large {a t₀ : ℝ} (ha : |a| ≤ 1) (ht₀ : 0 < t₀) (φ : ℝ) :
    ∃ B₁ : ℝ, ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 2 * t₀ + 18 < w.im →
      ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        B₁ * w.im ^ (1 / 4 : ℝ) := by
  obtain ⟨CL, hCL⟩ := RHTower.exists_norm_zetaEulerLog_le_large
  refine ⟨Real.exp (2 * primeSquareMass + CL) * 2 ^ 9 * (4 * (((9 : ℕ) : ℝ) + 1)) ^ (9 : ℕ),
    fun w hw hw2 ht => ?_⟩
  set y := w.im
  have hy : 18 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hvm : w - t₀ * I = (w.re : ℂ) + ((y - t₀ : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [y]
  have hvp : w + t₀ * I = (w.re : ℂ) + ((y + t₀ : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [y]
  have hm := hCL w.re (y - t₀) hw hw2 (by rw [abs_of_pos (by linarith)]; linarith)
  have hp := hCL w.re (y + t₀) hw hw2 (by rw [abs_of_pos (by linarith)]; linarith)
  rw [← hvm, abs_of_pos (by linarith)] at hm
  rw [← hvp, abs_of_pos (by linarith)] at hp
  -- `log log(y ± t₀) ≤ log(2 log y)`
  have h2log : Real.log (y + t₀) ≤ 2 * Real.log y := by
    rw [← Real.log_rpow (by linarith), Real.rpow_two]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hLm : Real.log (Real.log (y - t₀)) ≤ Real.log (2 * Real.log y) :=
    Real.log_le_log (Real.log_pos (by linarith))
      ((Real.log_le_log (by linarith) (by linarith)).trans h2log)
  have hLp : Real.log (Real.log (y + t₀)) ≤ Real.log (2 * Real.log y) :=
    Real.log_le_log (Real.log_pos (by linarith)) h2log
  have hexp9 : Real.exp (9 * Real.log (2 * Real.log y)) = (2 * Real.log y) ^ 9 := by
    rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hq := log_pow_le_rpow_quarter (show 1 ≤ y by linarith) 9
  calc ‖∑' n : ℕ, (phasePattern a t₀ φ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
      ≤ Real.exp (2 * primeSquareMass + (‖RHTower.zetaEulerLog (w - t₀ * I)‖ +
          ‖RHTower.zetaEulerLog (w + t₀ * I)‖) / 2) := norm_phaseSeries_le_exp ha t₀ φ hw
    _ ≤ Real.exp (2 * primeSquareMass + CL + 9 * Real.log (2 * Real.log y)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (2 * primeSquareMass + CL) * 2 ^ 9 * Real.log y ^ 9 := by
        rw [Real.exp_add, hexp9]; ring
    _ ≤ Real.exp (2 * primeSquareMass + CL) * 2 ^ 9 *
          ((4 * (((9 : ℕ) : ℝ) + 1)) ^ (9 : ℕ) * y ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

/-! ### Payment -/

/-- **Strip bounds pay a half-damped pattern.** Let `|f| ≤ 1` be completely multiplicative. If
`|F(w)| ≤ A(|Im w − t₁|^{-a₀} + 1)` on `1 < Re w ≤ 2`, `0 < Im w ≤ T`, `Im w ≠ t₁`, with `2a₀ < 1`,
and `|F(w)| ≤ B₁ (Im w)^{1/4}` for `Im w > T ≥ 2`, then `f(d) d^{-1/2}` is paid. -/
theorem receiverBounded_pattern_half_of_bounds {f : ℕ →*₀ ℝ} (hf : ∀ n, |f n| ≤ 1)
    {t₁ T a₀ A B₁ : ℝ} (hT : 2 ≤ T) (ha₀1 : 2 * a₀ < 1)
    (hsmall : ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 0 < w.im → w.im ≤ T → w.im ≠ t₁ →
      ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤ A * (|w.im - t₁| ^ (-a₀) + 1))
    (hlarge : ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → T < w.im →
      ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤ B₁ * w.im ^ (1 / 4 : ℝ)) :
    ReceiverBounded (fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
  set c : ℕ → ℝ := fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))
  have hc : DampedClass 1 (1 / 2) c := fun d => by
    simp only [c]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (hf d)
  set P : ℝ := ∑' d : ℕ, c d / d
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_tall_box T
  have hAint : 0 ≤ 4 * Z₀ ^ 2 * (4 * A ^ 2 + 2 * P ^ 2) := by positivity
  set Aint := 4 * Z₀ ^ 2 * (4 * A ^ 2 + 2 * P ^ 2)
  have hwre : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).re = σ + 1 / 2 := fun σ t => by simp
  have hwim : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).im = t := fun σ t => by simp
  have hg : IntegrableOn (fun t : ℝ => Aint * (|t - t₁| ^ (-(2 * a₀)) + 1)) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      (((intervalIntegrable_abs_sub_rpow (by linarith) t₁ 0 T).add
        intervalIntegrable_const).const_mul Aint)
  have hsmall' : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < t → t ≤ T → t ≠ t₁ →
      lineIntegrand c P σ t ≤ Aint * (|t - t₁| ^ (-(2 * a₀)) + 1) := by
    intro σ t hσ hσ' ht htT hne
    have hF := hsmall ((σ : ℂ) + t * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; exact ht) (by rw [hwim]; exact htT) (by rw [hwim]; exact hne)
    rw [hwim] at hF
    set x := |t - t₁|
    have hx0 : 0 ≤ x := abs_nonneg _
    have hC : ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤
        A * (x ^ (-a₀) + 1) + |P| := by
      rw [weightDirichletSeries_pattern]
      refine (norm_sub_le _ _).trans (add_le_add hF (by rw [Complex.norm_real, Real.norm_eq_abs]))
    have hpw : (x ^ (-a₀)) ^ 2 = x ^ (-(2 * a₀)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; congr 1; push_cast; ring
    have hX0 : 0 ≤ x ^ (-(2 * a₀)) := Real.rpow_nonneg hx0 _
    have hsq : ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 ≤
        (4 * A ^ 2 + 2 * P ^ 2) * (x ^ (-(2 * a₀)) + 1) := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hC 2
      have hab : ∀ u v : ℝ, (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := fun u v => by
        nlinarith [sq_nonneg (u - v)]
      have h1 : (A * (x ^ (-a₀) + 1)) ^ 2 ≤ 2 * A ^ 2 * (x ^ (-(2 * a₀)) + 1) := by
        rw [mul_pow]
        have := hab (x ^ (-a₀)) 1
        rw [hpw] at this
        nlinarith [sq_nonneg A]
      refine h.trans ((hab _ _).trans ?_)
      rw [sq_abs]
      nlinarith [sq_nonneg P]
    have hζs := hZ σ t hσ.le hσ'.le (by rw [abs_of_pos ht]; exact htT)
    have hsn : σ ≤ ‖(σ : ℂ) + t * I‖ := by
      have := Complex.abs_re_le_norm ((σ : ℂ) + t * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith [le_abs_self σ]
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hden : 0 < ‖(σ : ℂ) + t * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    have hzsq : ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hζs 2
    simp only [lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
    rw [div_le_iff₀ hden]
    calc ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
          ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2
        ≤ Z₀ ^ 2 * ((4 * A ^ 2 + 2 * P ^ 2) * (x ^ (-(2 * a₀)) + 1)) :=
          mul_le_mul hzsq hsq (sq_nonneg _) (sq_nonneg _)
      _ = Aint * (x ^ (-(2 * a₀)) + 1) * (1 / 2) ^ 2 := by simp only [Aint]; ring
      _ ≤ Aint * (x ^ (-(2 * a₀)) + 1) * ‖(σ : ℂ) + t * I‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (mul_nonneg hAint (by positivity))
  have hlarge' : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < t →
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤ (|B₁| + |P|) * t ^ (1 / 4 : ℝ) := by
    intro σ t hσ hσ' ht
    have hF := hlarge ((σ : ℂ) + t * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; exact ht)
    rw [hwim] at hF
    rw [weightDirichletSeries_pattern]
    refine (norm_sub_le _ _).trans ?_
    have h1 : 1 ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [le_abs_self B₁, abs_nonneg P, abs_nonneg B₁,
      mul_le_mul_of_nonneg_right (le_abs_self B₁) (by positivity : (0 : ℝ) ≤ t ^ (1 / 4 : ℝ))]
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_majorant (c := c) hT hg hsmall' hlarge'
  exact ⟨3 * M / (4 * Real.pi), weightPronicEnergy_le_of_lineEnergy_le hc hM⟩

/-- **Below full real amplitude the phase weight is paid**: for `|a| ≤ 1`, `a cos φ < 1` and
`t₀ ≠ 0`, `f(d) d^{-1/2}` with `f(p) = a cos(t₀ log p + φ)` has bounded receiver. -/
theorem receiverBounded_phaseWeight_of_lt_one {a t₀ φ : ℝ} (ha : |a| ≤ 1)
    (hα : a * Real.cos φ < 1) (ht₀ : t₀ ≠ 0) : ReceiverBounded (phaseWeight a t₀ φ) := by
  have hpos : ∀ {t₀ φ : ℝ}, 0 < t₀ → a * Real.cos φ < 1 →
      ReceiverBounded (phaseWeight a t₀ φ) := by
    intro t₀ φ ht₀ hα
    obtain ⟨A, -, hsmall⟩ := exists_norm_phaseSeries_le_small ha ht₀ φ
    obtain ⟨B₁, hlarge⟩ := exists_norm_phaseSeries_le_large ha ht₀ φ
    have ha₀1 : 2 * (max (a * Real.cos φ) 0 / 2) < 1 := by
      have := max_lt hα (show (0 : ℝ) < 1 by norm_num)
      linarith
    exact receiverBounded_pattern_half_of_bounds (abs_phasePattern_le ha t₀ φ)
      (by linarith) ha₀1 hsmall (fun w hw hw2 ht => hlarge w hw hw2 ht)
  rcases lt_or_gt_of_ne ht₀ with hneg | hpos'
  · rw [show t₀ = -(-t₀) by ring, phaseWeight_neg]
    exact hpos (by linarith) (by rwa [Real.cos_neg])
  · exact hpos hpos' hα

/-- **The phase law.** For `|a| ≤ 1`, `t₀ ≠ 0` and every phase `φ`, the half-damped weight of
`f(p) = a cos(t₀ log p + φ)` is paid iff `a cos φ < 1` or `ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_phaseWeight_iff {a t₀ φ : ℝ} (ha : |a| ≤ 1) (ht₀ : t₀ ≠ 0) :
    ReceiverBounded (phaseWeight a t₀ φ) ↔
      a * Real.cos φ < 1 ∨ riemannZeta (1 / 2 + (t₀ : ℂ) * I) = 0 := by
  by_cases hα : a * Real.cos φ < 1
  · exact ⟨fun _ => Or.inl hα, fun _ => receiverBounded_phaseWeight_of_lt_one ha hα ht₀⟩
  have h1 : a * Real.cos φ = 1 := by
    have : |a * Real.cos φ| ≤ 1 := by
      rw [abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) (Real.abs_cos_le_one φ)
    linarith [le_abs_self (a * Real.cos φ)]
  have hw : phaseWeight a t₀ φ = oscWeight 1 t₀ := by
    funext d; simp only [phaseWeight, oscWeight, phasePattern_eq_oscPattern_one ha h1]
  rw [hw, receiverBounded_oscWeight_iff (by norm_num) le_rfl]
  simp only [ht₀, false_and, false_or, ne_eq, not_false_eq_true, true_and, hα, lt_irrefl]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
