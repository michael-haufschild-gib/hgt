import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Order.Round

/-!
# The theta surface: Riemann–Roch with characteristic and the free polarization

The theta `h⁰` of `Spec ℤ` counts the lattice `ℤ ⊂ ℝ` with Gaussian weight. Translating the lattice
by a **characteristic** `a ∈ ℝ/ℤ` gives a second variable, and the count becomes a function on the
surface of (characteristic, degree):

    h⁰(a, d) = log Σ_{n ∈ ℤ} e^{−π (n + a)² e^{−2d}}        (Mathlib's `evenKernel a`).

* **Riemann–Roch with characteristic** (`thetaH0_riemannRoch`). Poisson summation exchanges the
  translation for a modulation: `h⁰(a, d) − h⁰∨(a, −d) = d`, where
  `h⁰∨(a, d) = log Σ_n e^{−π n² e^{−2d}} cos(2π n a)` is positive (`cosKernel_pos`). At `a = 0` both
  are the theta `h⁰` of `Spec ℤ`. The Euler characteristic is linear in the degree on every fibre.
* **The free polarization** (`hasSum_thetaChar`, `abs_log_thetaChar_sub_le`). With a real exponential
  characteristic `J` the count `ϑ(J, t) = Σ_n e^{−π n² t + 2π n J}` is `e^{π J²/t}` times a shifted
  count, so `log ϑ(J, t) = π J²/t + O_t(1)` uniformly in `J`, with
  `−π t / 4 ≤ log ϑ(J, t) − π J²/t ≤ h⁰-type bound` (`exp_neg_le_evenKernel`,
  `evenKernel_le_evenKernel_zero`). The count is `≥ 1`, so `J ↦ log ϑ(J, t)` is a nonnegative naive
  height whose Tate limit is the positive definite form `π J²/t`: a polarization from counting. It
  satisfies the theorem of the square exactly in the period direction,
  `ϑ(J + t, t) = e^{π t + 2π J} ϑ(J, t)` (`thetaChar_add_period`).
* **The polarization is soft** (`hasSum_shifted_thetaChar`). Translating the lattice by any `b`
  changes only the bounded part: the quadratic term `π J²/t` is the same on every fibre. It carries
  no arithmetic of the fibre.
* **The fibres** (`completedHurwitzZetaEven_zero`). The Mellin transform in the degree of the fibre
  at `a` is the completed even Hurwitz zeta function; at `a = 0` it is `Λ(s)`.

So the theta surface has a Riemann–Roch proved without any sign and a positive polarization that
is a count — and both hold for every characteristic. The positivity a proof of RH needs must be
selective on the fibre at `0`; the polarization of the theta surface is not.
-/

noncomputable section

open Real HurwitzZeta Filter

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The theta `h⁰` at characteristic `a` and degree `d`. -/
def thetaH0 (a d : ℝ) : ℝ := Real.log (evenKernel a (Real.exp (-2 * d)))

/-- The dual (modulated) count `log Σ_n e^{−π n² e^{−2d}} cos(2π n a)`. -/
def thetaH0Dual (a d : ℝ) : ℝ := Real.log (cosKernel a (Real.exp (-2 * d)))

/-- The shifted count dominates its nearest term: `e^{−π t/4} ≤ Σ_n e^{−π(n+a)² t}`. -/
theorem exp_neg_le_evenKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-π * t / 4) ≤ evenKernel a t := by
  have h := hasSum_int_evenKernel a ht
  have hle := h.summable.le_tsum (-round a) fun j _ => (Real.exp_pos _).le
  rw [h.tsum_eq] at hle
  refine le_trans (Real.exp_le_exp.mpr ?_) hle
  have hr : |a - round a| ≤ 1 / 2 := abs_sub_round a
  have hsq : ((-round a : ℤ) + a : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [Int.cast_neg, neg_add_eq_sub]
    nlinarith [abs_nonneg (a - round a), sq_abs (a - round a)]
  have := mul_nonneg (mul_pos Real.pi_pos ht).le (sub_nonneg.mpr hsq)
  nlinarith [this]

theorem evenKernel_pos (a : ℝ) {t : ℝ} (ht : 0 < t) : 0 < evenKernel a t :=
  (Real.exp_pos _).trans_le (exp_neg_le_evenKernel a ht)

/-- The modulated count is positive: by Poisson it is a positive multiple of a shifted count. -/
theorem cosKernel_pos (a : ℝ) {s : ℝ} (hs : 0 < s) : 0 < cosKernel a s := by
  have h := evenKernel_functional_equation a (1 / s)
  rw [one_div_one_div] at h
  have hpos := evenKernel_pos a (one_div_pos.mpr hs)
  rw [h] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)

/-- **Riemann–Roch with characteristic**: `h⁰(a, d) − h⁰∨(a, −d) = d`. -/
theorem thetaH0_riemannRoch (a d : ℝ) : thetaH0 a d - thetaH0Dual a (-d) = d := by
  have h := evenKernel_functional_equation a (Real.exp (-2 * d))
  have hroot : 1 / Real.exp (-2 * d) ^ (1 / 2 : ℝ) = Real.exp d := by
    rw [← Real.exp_mul, one_div, ← Real.exp_neg]; congr 1; ring
  have hinv : 1 / Real.exp (-2 * d) = Real.exp (-2 * -d) := by
    rw [one_div, ← Real.exp_neg]; congr 1; ring
  rw [hroot, hinv] at h
  rw [thetaH0, thetaH0Dual, h, Real.log_mul (Real.exp_pos d).ne'
    (cosKernel_pos a (Real.exp_pos _)).ne', Real.log_exp]
  ring

/-- The modulated count is at most the unmodulated one: `|e^{2πi a n}| = 1`. -/
theorem cosKernel_le_evenKernel_zero (a : ℝ) {s : ℝ} (hs : 0 < s) :
    cosKernel a s ≤ evenKernel 0 s := by
  have hc := Complex.hasSum_re (hasSum_int_cosKernel a hs)
  have h0 := hasSum_int_evenKernel 0 hs
  simp only [Complex.ofReal_re] at hc
  refine hasSum_le (fun n => ?_) hc h0
  refine (Complex.re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  simp

/-- **The fibre at `0` maximizes the count**: `Σ_n e^{−π(n+a)² t} ≤ Σ_n e^{−π n² t}`. -/
theorem evenKernel_le_evenKernel_zero (a : ℝ) {t : ℝ} (ht : 0 < t) :
    evenKernel a t ≤ evenKernel 0 t := by
  rw [evenKernel_functional_equation a t, evenKernel_functional_equation 0 t]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← evenKernel_eq_cosKernel_of_zero]
  exact cosKernel_le_evenKernel_zero a (one_div_pos.mpr ht)

/-- The count with a real exponential characteristic `J`. -/
def thetaChar (J t : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-π * (n : ℝ) ^ 2 * t + 2 * π * n * J)

/-- **Completing the square**: `ϑ(J, t) = e^{π J²/t} · Σ_n e^{−π(n − J/t)² t}`. -/
theorem hasSum_thetaChar (J : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => Real.exp (-π * (n : ℝ) ^ 2 * t + 2 * π * n * J))
      (Real.exp (π * J ^ 2 / t) * evenKernel (-J / t) t) := by
  refine ((hasSum_int_evenKernel (-J / t) ht).mul_left (Real.exp (π * J ^ 2 / t))).congr_fun
    fun n => ?_
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

theorem thetaChar_eq (J : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaChar J t = Real.exp (π * J ^ 2 / t) * evenKernel (-J / t) t :=
  (hasSum_thetaChar J ht).tsum_eq

/-- The count is at least its zero term. -/
theorem one_le_thetaChar (J : ℝ) {t : ℝ} (ht : 0 < t) : 1 ≤ thetaChar J t := by
  have h := (hasSum_thetaChar J ht).summable.le_tsum 0 fun j _ => (Real.exp_pos _).le
  simpa [thetaChar] using h

/-- **The free polarization.** `log ϑ(J, t) = π J²/t + O_t(1)` uniformly in the characteristic. -/
theorem abs_log_thetaChar_sub_le (J : ℝ) {t : ℝ} (ht : 0 < t) :
    |Real.log (thetaChar J t) - π * J ^ 2 / t| ≤ max (π * t / 4) (Real.log (evenKernel 0 t)) := by
  have hk := evenKernel_pos (-J / t) ht
  rw [thetaChar_eq J ht, Real.log_mul (Real.exp_pos _).ne' hk.ne', Real.log_exp, add_sub_cancel_left]
  have hlo : -(π * t / 4) ≤ Real.log (evenKernel (-J / t) t) := by
    have := Real.log_le_log (Real.exp_pos _) (exp_neg_le_evenKernel (-J / t) ht)
    rw [Real.log_exp] at this; linarith
  have hhi : Real.log (evenKernel (-J / t) t) ≤ Real.log (evenKernel 0 t) :=
    Real.log_le_log hk (evenKernel_le_evenKernel_zero _ ht)
  rw [abs_le]
  constructor <;> [linarith [le_max_left (π * t / 4) (Real.log (evenKernel 0 t))];
    linarith [le_max_right (π * t / 4) (Real.log (evenKernel 0 t))]]

/-- The polarization is a nonnegative naive height for the form `π J²/t`. -/
theorem log_thetaChar_nonneg (J : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ Real.log (thetaChar J t) :=
  Real.log_nonneg (one_le_thetaChar J ht)

/-- **Quasi-periodicity** (the theorem of the square in the period direction):
`ϑ(J + t, t) = e^{π t + 2π J} ϑ(J, t)`. -/
theorem thetaChar_add_period (J : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaChar (J + t) t = Real.exp (π * t + 2 * π * J) * thetaChar J t := by
  rw [thetaChar_eq _ ht, thetaChar_eq _ ht, ← mul_assoc, ← Real.exp_add]
  have hshift : -(J + t) / t = -J / t + (-1 : ℤ) := by push_cast; field_simp; ring
  have hper : evenKernel (-(J + t) / t) t = evenKernel (-J / t) t := by
    rw [hshift]
    congr 1
    simp
  rw [hper]
  congr 2
  field_simp
  ring

/-- **The polarization is soft.** Translating the lattice by `b` keeps the quadratic part:
`Σ_n e^{−π(n+b)² t + 2π(n+b)J} = e^{π J²/t} · Σ_n e^{−π(n + b − J/t)² t}`. -/
theorem hasSum_shifted_thetaChar (b J : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => Real.exp (-π * ((n : ℝ) + b) ^ 2 * t + 2 * π * ((n : ℝ) + b) * J))
      (Real.exp (π * J ^ 2 / t) * evenKernel ((b - J / t : ℝ) : UnitAddCircle) t) := by
  refine ((hasSum_int_evenKernel (b - J / t) ht).mul_left (Real.exp (π * J ^ 2 / t))).congr_fun
    fun n => ?_
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **The fibre at characteristic `0` is `Λ(s)`.** -/
theorem completedHurwitzZetaEven_zero : completedHurwitzZetaEven 0 = completedRiemannZeta := rfl

end GaloisForLFunctions.ArithmeticEffectivityTheory
