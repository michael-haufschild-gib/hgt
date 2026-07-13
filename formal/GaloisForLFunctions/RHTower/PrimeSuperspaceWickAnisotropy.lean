import GaloisForLFunctions.RHTower.PrimeClockFiniteScaling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Wick anisotropy of finite-prime superspace

Radial reflection and vertical clock displacement have the same Fisher quadratic form at the
critical state, but their global energies use hyperbolic and trigonometric functions respectively.
The clock energy lies below the quadratic form; the radial energy lies above it.  This is the
finite-dimensional core of the failure of a global Wick-symmetric prime superspace.
-/

noncomputable section

namespace RHTower

/-- Finite critical-line clock-separation energy. -/
def primeClockVerticalEnergy (N : ℕ) (h : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, 4 * Real.sin (h * Real.log p / 2) ^ 2 / p

/-- Cosine form of finite clock separation. -/
theorem primeClockVerticalEnergy_eq_cos (N : ℕ) (h : ℝ) :
    primeClockVerticalEnergy N h =
      ∑ p ∈ Nat.primesLE N, 2 * (1 - Real.cos (h * Real.log p)) / p := by
  apply Finset.sum_congr rfl
  intro p hp
  let x : ℝ := h * Real.log p / 2
  have htrig :
      4 * Real.sin (h * Real.log p / 2) ^ 2 =
        2 * (1 - Real.cos (h * Real.log p)) := by
    have hx : h * Real.log p = 2 * x := by dsimp [x]; ring
    have hxhalf : h * Real.log p / 2 = x := rfl
    rw [hxhalf, hx, Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [htrig]

@[simp] theorem primeClockVerticalEnergy_zero (N : ℕ) :
    primeClockVerticalEnergy N 0 = 0 := by
  simp [primeClockVerticalEnergy]

theorem primeClockVerticalEnergy_neg (N : ℕ) (h : ℝ) :
    primeClockVerticalEnergy N (-h) = primeClockVerticalEnergy N h := by
  simp only [primeClockVerticalEnergy, neg_mul, Real.sin_neg, neg_div, neg_sq]

theorem primeClockVerticalEnergy_nonneg (N : ℕ) (h : ℝ) :
    0 ≤ primeClockVerticalEnergy N h := by
  rw [primeClockVerticalEnergy]
  positivity

/-- The vertical clock energy is bounded above by its Fisher susceptibility. -/
theorem primeClockVerticalEnergy_quadratic_upper (N : ℕ) (h : ℝ) :
    primeClockVerticalEnergy N h ≤ h ^ 2 * primeClockSusceptibility N := by
  rw [primeClockVerticalEnergy, primeClockSusceptibility, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpprime : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hs := Real.sin_sq_le_sq (x := h * Real.log p / 2)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hinv : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr hp0.le
  calc
    4 * Real.sin (h * Real.log p / 2) ^ 2 * (p : ℝ)⁻¹ ≤
        4 * (h * Real.log p / 2) ^ 2 * (p : ℝ)⁻¹ := by
      gcongr
    _ = h ^ 2 * (Real.log p ^ 2 * (p : ℝ)⁻¹) := by ring

/-- **Wick anisotropy.** At equal coordinate displacement, trigonometric clock distance lies below
the common Fisher quadratic form, while hyperbolic radial distance lies above it. -/
theorem primeClock_wick_anisotropy (N : ℕ) (r : ℝ) :
    primeClockVerticalEnergy N r ≤ r ^ 2 * primeClockSusceptibility N ∧
      r ^ 2 * primeClockSusceptibility N ≤ primeClockCutoffEnergy N (r / 2) := by
  constructor
  · exact primeClockVerticalEnergy_quadratic_upper N r
  · have h := primeClockCutoffEnergy_quadratic_lower N (r / 2)
    calc
      r ^ 2 * primeClockSusceptibility N =
          4 * (r / 2) ^ 2 * primeClockSusceptibility N := by ring
      _ ≤ primeClockCutoffEnergy N (r / 2) := h

lemma sixteen_div_pi_sq_mul_sq_le_four_sin_sq {x : ℝ}
    (hx : |x| ≤ Real.pi / 2) :
    16 / Real.pi ^ 2 * x ^ 2 ≤ 4 * Real.sin x ^ 2 := by
  have hsin := Real.mul_abs_le_abs_sin hx
  have hnonneg : 0 ≤ 2 / Real.pi * |x| :=
    mul_nonneg (div_nonneg (by norm_num) Real.pi_pos.le) (abs_nonneg x)
  have hsq := (sq_le_sq₀ hnonneg (abs_nonneg (Real.sin x))).2 hsin
  rw [sq_abs, mul_pow, sq_abs] at hsq
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at hsq ⊢
  nlinarith [Real.pi_pos]

/-- Inside the first non-wrapping clock window, vertical energy has the same quadratic scale as
the radial reflected energy. -/
theorem primeClockVerticalEnergy_quadratic_lower
    (N : ℕ) (h : ℝ) (hwindow : |h| * Real.log N ≤ Real.pi) :
    4 / Real.pi ^ 2 * h ^ 2 * primeClockSusceptibility N ≤
      primeClockVerticalEnergy N h := by
  rw [primeClockVerticalEnergy, primeClockSusceptibility, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpdata := Nat.mem_primesLE.mp hp
  have hpprime : p.Prime := hpdata.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
  have hlogle : Real.log p ≤ Real.log N :=
    Real.log_le_log hp0 (by exact_mod_cast hpdata.1)
  have harg : |h * Real.log p / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hlogp0]
    norm_num
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
    exact (mul_le_mul_of_nonneg_left hlogle (abs_nonneg h)).trans hwindow
  have hs := sixteen_div_pi_sq_mul_sq_le_four_sin_sq harg
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hinv : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr hp0.le
  calc
    4 / Real.pi ^ 2 * h ^ 2 * (Real.log p ^ 2 * (p : ℝ)⁻¹) =
        (16 / Real.pi ^ 2 * (h * Real.log p / 2) ^ 2) * (p : ℝ)⁻¹ := by ring
    _ ≤ (4 * Real.sin (h * Real.log p / 2) ^ 2) * (p : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hs hinv
    _ = 4 * Real.sin (h * Real.log p / 2) ^ 2 * (p : ℝ)⁻¹ := rfl

/-- Nondegenerate vertical clock separation throughout the first critical window. -/
theorem primeClockVerticalEnergy_critical_scaled_sandwich
    (N : ℕ) (c : ℝ) (hN : 2 ≤ N) (hc : |c| ≤ Real.pi) :
    4 / Real.pi ^ 2 * c ^ 2 *
          (primeClockSusceptibility N / Real.log N ^ 2) ≤
        primeClockVerticalEnergy N (c / Real.log N) ∧
      primeClockVerticalEnergy N (c / Real.log N) ≤
        c ^ 2 * (primeClockSusceptibility N / Real.log N ^ 2) := by
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hlogne : Real.log N ≠ 0 := hlogpos.ne'
  have hwindow : |c / Real.log N| * Real.log N ≤ Real.pi := by
    rw [abs_div, abs_of_pos hlogpos]
    field_simp
    exact hc
  constructor
  · have h := primeClockVerticalEnergy_quadratic_lower N (c / Real.log N) hwindow
    calc
      4 / Real.pi ^ 2 * c ^ 2 *
          (primeClockSusceptibility N / Real.log N ^ 2) =
          4 / Real.pi ^ 2 * (c / Real.log N) ^ 2 *
            primeClockSusceptibility N := by field_simp
      _ ≤ primeClockVerticalEnergy N (c / Real.log N) := h
  · have h := primeClockVerticalEnergy_quadratic_upper N (c / Real.log N)
    calc
      primeClockVerticalEnergy N (c / Real.log N) ≤
          (c / Real.log N) ^ 2 * primeClockSusceptibility N := h
      _ = c ^ 2 * (primeClockSusceptibility N / Real.log N ^ 2) := by
        field_simp

end RHTower
