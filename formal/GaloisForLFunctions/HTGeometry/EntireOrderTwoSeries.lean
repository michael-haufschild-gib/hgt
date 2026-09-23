/-
# Taylor coefficients and entire functions of order two

A power series `∑ aₙ zⁿ` whose coefficients obey the Carleman-type bound

  `‖aₙ‖ ≤ exp(R²c/2) / Rⁿ`   for every `R > 0`

converges everywhere and defines an entire function.  The proof needs no optimisation of `R`: at a
point `z ≠ 0` the choice `R = 2‖z‖` already turns the bound into the geometric series `2⁻ⁿ` times a
constant.  This is exactly the shape produced by Cauchy's estimate applied to a function of order
two, in particular to the regularized determinant `det₂(1 + zM)` of a matrix, whose growth is
governed by the Hilbert–Schmidt norm alone.

Main results:
* `taylorCoeff`, `hasSum_taylorCoeff` — the Taylor coefficients of an entire function.
* `norm_taylorCoeff_le` — Cauchy's estimate in coefficient form.
* `summable_of_orderTwo_bound`, `differentiable_entireOfCoeffs` — such coefficients define an
  entire function.
* `norm_taylorCoeff_finiteDet2_le` — the Carleman coefficient bound of a matrix determinant.
-/
import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries

namespace GaloisForLFunctions.HTGeometry

open Metric

/-- The `n`-th Taylor coefficient of `f` at the origin. -/
noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  ((Nat.factorial n : ℕ) : ℂ)⁻¹ * iteratedDeriv n f 0

/-- An entire function is the sum of its Taylor series at the origin. -/
theorem hasSum_taylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    HasSum (fun n => taylorCoeff f n * z ^ n) (f z) := by
  have h := Complex.hasSum_taylorSeries_of_entire hf 0 z
  refine h.congr_fun fun n => ?_
  simp only [taylorCoeff, sub_zero, smul_eq_mul]
  ring

/-- **Cauchy's estimate, coefficient form.**  If `‖f‖ ≤ C` on the circle of radius `R`, the `n`-th
Taylor coefficient of the entire function `f` is at most `C/Rⁿ`. -/
theorem norm_taylorCoeff_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R C : ℝ} (hR : 0 < R)
    (hC : ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ C) (n : ℕ) :
    ‖taylorCoeff f n‖ ≤ C / R ^ n := by
  have hsphere : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C := by
    intro z hz
    exact hC z (by simpa using mem_sphere_iff_norm.mp hz)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := (0 : ℂ)) (C := C)
    n hR hf.diffContOnCl hsphere
  have hfac : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by exact_mod_cast n.factorial_pos
  rw [taylorCoeff, norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hfac]
  calc ‖iteratedDeriv n f 0‖ ≤ ((Nat.factorial n : ℕ) : ℝ) * C / R ^ n := h
    _ = ((Nat.factorial n : ℕ) : ℝ) * (C / R ^ n) := by ring

/-- **Cauchy's estimate on a disc.**  The same bound for a function only analytic on `ball 0 R`
and continuous on its closure. -/
theorem norm_taylorCoeff_le' {f : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball (0 : ℂ) R)) (hC : ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ C) (n : ℕ) :
    ‖taylorCoeff f n‖ ≤ C / R ^ n := by
  have hsphere : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C := by
    intro z hz
    exact hC z (by simpa using mem_sphere_iff_norm.mp hz)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := (0 : ℂ)) (C := C)
    n hR hf hsphere
  have hfac : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) := by exact_mod_cast n.factorial_pos
  rw [taylorCoeff, norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hfac]
  calc ‖iteratedDeriv n f 0‖ ≤ ((Nat.factorial n : ℕ) : ℝ) * C / R ^ n := h
    _ = ((Nat.factorial n : ℕ) : ℝ) * (C / R ^ n) := by ring

/-! ## Order-two coefficient bounds -/

/-- The coefficient bound of an entire function of order two makes every power series value
absolutely convergent: at `z ≠ 0` the radius `R = 2‖z‖` turns the bound into a geometric series. -/
theorem summable_of_orderTwo_bound {a : ℕ → ℂ} {c : ℝ}
    (h : ∀ R : ℝ, 0 < R → ∀ n, ‖a n‖ ≤ Real.exp (R ^ (2 : ℕ) * c / 2) / R ^ n) (z : ℂ) :
    Summable (fun n => a n * z ^ n) := by
  rcases eq_or_ne z 0 with rfl | hz
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hn0 : n ≠ 0 := by simpa using hn
    simp [zero_pow hn0]
  · have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    set R : ℝ := 2 * ‖z‖ with hRdef
    have hR : 0 < R := by positivity
    refine Summable.of_norm_bounded (g := fun n : ℕ => Real.exp (R ^ (2 : ℕ) * c / 2) * (1 / 2) ^ n) ?_ ?_
    · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    · intro n
      rw [norm_mul, norm_pow]
      have hbound := h R hR n
      have hzn : ‖z‖ ^ n ≠ 0 := by positivity
      have hkey : (Real.exp (R ^ (2 : ℕ) * c / 2) / R ^ n) * ‖z‖ ^ n
          = Real.exp (R ^ (2 : ℕ) * c / 2) * (1 / 2) ^ n := by
        have hRn : R ^ n = 2 ^ n * ‖z‖ ^ n := by rw [hRdef, mul_pow]
        rw [hRn, div_pow, one_pow]
        field_simp
      calc ‖a n‖ * ‖z‖ ^ n ≤ (Real.exp (R ^ (2 : ℕ) * c / 2) / R ^ n) * ‖z‖ ^ n :=
            mul_le_mul_of_nonneg_right hbound (by positivity)
        _ = Real.exp (R ^ (2 : ℕ) * c / 2) * (1 / 2) ^ n := hkey

/-- The entire function attached to a coefficient sequence. -/
noncomputable def entireOfCoeffs (a : ℕ → ℂ) : ℂ → ℂ := fun z => ∑' n, a n * z ^ n

theorem hasDerivAt_entireOfCoeffs {a : ℕ → ℂ} {c : ℝ}
    (h : ∀ R : ℝ, 0 < R → ∀ n, ‖a n‖ ≤ Real.exp (R ^ (2 : ℕ) * c / 2) / R ^ n) (z : ℂ) :
    HasDerivAt (entireOfCoeffs a) (∑' n : ℕ, (n : ℂ) * a n * z ^ (n - 1)) z := by
  obtain ⟨r, hr, hzr⟩ : ∃ r : ℝ, 0 < r ∧ ‖z‖ < r := ⟨‖z‖ + 1, by positivity, by linarith⟩
  set R : ℝ := 2 * r with hRdef
  have hR : 0 < R := by positivity
  set E : ℝ := R ^ (2 : ℕ) * c / 2 with hE
  have hu : Summable (fun n : ℕ => Real.exp E / r * ((n : ℝ) * (1 / 2) ^ n)) := by
    refine Summable.mul_left _ ?_
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (1 / 2 : ℝ))
      (by rw [Real.norm_eq_abs]; norm_num)
    simpa using this
  have hterm : ∀ (n : ℕ) (y : ℂ), y ∈ ball (0 : ℂ) r →
      HasDerivAt (fun w : ℂ => a n * w ^ n) ((n : ℂ) * a n * y ^ (n - 1)) y := by
    intro n y _
    refine ((hasDerivAt_pow n y).const_mul (a n)).congr_deriv ?_
    ring
  have hbound : ∀ (n : ℕ) (y : ℂ), y ∈ ball (0 : ℂ) r →
      ‖(n : ℂ) * a n * y ^ (n - 1)‖ ≤ Real.exp E / r * ((n : ℝ) * (1 / 2) ^ n) := by
    intro n y hy
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hyr : ‖y‖ < r := by rwa [mem_ball_zero_iff] at hy
    have han := h R hR n
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
    have hy1 : ‖y‖ ^ (n - 1) ≤ r ^ (n - 1) :=
      pow_le_pow_left₀ (norm_nonneg y) hyr.le _
    have hmul : ‖a n‖ * ‖y‖ ^ (n - 1) ≤ (Real.exp E / R ^ n) * r ^ (n - 1) :=
      mul_le_mul han hy1 (by positivity) (by positivity)
    have hkey : (Real.exp E / R ^ n) * r ^ (n - 1) = Real.exp E / r * (1 / 2) ^ n := by
      have hn1 : r ^ n = r ^ (n - 1) * r := by
        rw [← pow_succ]
        congr 1
        omega
      have hRn : R ^ n = 2 ^ n * r ^ n := by rw [hRdef, mul_pow]
      have hrne : r ^ (n - 1) ≠ 0 := by positivity
      rw [hRn, hn1, div_pow, one_pow]
      field_simp
    calc (n : ℝ) * ‖a n‖ * ‖y‖ ^ (n - 1) = (n : ℝ) * (‖a n‖ * ‖y‖ ^ (n - 1)) := by ring
      _ ≤ (n : ℝ) * (Real.exp E / r * (1 / 2) ^ n) :=
          mul_le_mul_of_nonneg_left (hmul.trans_eq hkey) (Nat.cast_nonneg n)
      _ = Real.exp E / r * ((n : ℝ) * (1 / 2) ^ n) := by ring
  have hz0 : z ∈ ball (0 : ℂ) r := by rwa [mem_ball_zero_iff]
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball 0 r).isPreconnected
    hterm hbound hz0 (summable_of_orderTwo_bound h z) hz0

theorem differentiable_entireOfCoeffs {a : ℕ → ℂ} {c : ℝ}
    (h : ∀ R : ℝ, 0 < R → ∀ n, ‖a n‖ ≤ Real.exp (R ^ (2 : ℕ) * c / 2) / R ^ n) :
    Differentiable ℂ (entireOfCoeffs a) :=
  fun z => (hasDerivAt_entireOfCoeffs h z).differentiableAt

/-! ## The Carleman coefficient bound of a matrix determinant -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **The Carleman coefficient bound.**  Every Taylor coefficient of `det₂(1 + zM)` obeys the
order-two bound with constant the Hilbert–Schmidt energy of `M`, uniformly in the size of `M`. -/
theorem norm_taylorCoeff_finiteDet2_le (M : Matrix m m ℂ) {R : ℝ} (hR : 0 < R) (k : ℕ) :
    ‖taylorCoeff (finiteDet2 M) k‖ ≤ Real.exp (R ^ (2 : ℕ) * matHSNormSq M / 2) / R ^ k := by
  refine norm_taylorCoeff_le (differentiable_finiteDet2 M) hR (fun z hz => ?_) k
  have := norm_finiteDet2_le M z
  rwa [hz] at this

end GaloisForLFunctions.HTGeometry
