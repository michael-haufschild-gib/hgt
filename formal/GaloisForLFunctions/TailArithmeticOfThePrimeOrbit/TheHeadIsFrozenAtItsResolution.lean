import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheTailOfAReturnCarriesTheZero
import GaloisForLFunctions.RHTower.Sieve.MertensIntervalShell

/-!
# The head is frozen at its resolution

The head `E_y` cannot see features of `ζ` finer than its resolution. Moving vertically by `v` changes each factor by
`|p^{−s}| |1 − p^{−iv}| ≤ p^{−σ} |v| log p`, so (`abs_log_norm_eulerMollifier_sub_le`)

`|log|E_y(s + iv)| − log|E_y(s)|| ≤ |v| Σ_{p≤y} log p · p^{−σ}/(1 − p^{−σ})`.

On `Re s ≥ 1` the sum is at most `2(log y + log 4)` (`abs_log_norm_eulerHead_sub_le_of_one_le`): within `|v| ≤ ε/log y`
the head moves by a factor `e^{O(ε)}`. Inside the strip the sum is `≍ y^{1−σ}/(1 − σ)` and the resolution is `y^{σ−1}`.

Since `|ζ| = |E_y| · |ζ M_y|` on `Re s > 0` (`norm_zeta_eq_head_mul_tail`), every variation of `|ζ|` at scales finer than
the resolution is a variation of the tail. This is the sense in which a zero is a tail event at resolution `1/log y`: the
head is a smooth nonvanishing function at that scale, and the zero is a feature of the tail.
-/

open Complex Finset Real

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-- The resolution sum `Σ_{p≤y} log p · p^{−σ}/(1 − p^{−σ})`. -/
def resolutionSum (y : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ headPrimes y, Real.log p * (p : ℝ) ^ (-σ) / (1 - (p : ℝ) ^ (-σ))

theorem norm_natCast_cpow_neg {p : ℕ} (hp : 0 < p) (s : ℂ) : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]

theorem rpow_neg_lt_one {p : ℕ} (hp : 2 ≤ p) {σ : ℝ} (hσ : 0 < σ) : (p : ℝ) ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < p)) (by linarith)

/-- `|1 − p^{−iv}| ≤ |v| log p`. -/
theorem norm_one_sub_cpow_I_le {p : ℕ} (hp : 0 < p) (v : ℝ) :
    ‖1 - (p : ℂ) ^ (-((v : ℂ) * I))‖ ≤ |v| * Real.log p := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have e : (p : ℂ) ^ (-((v : ℂ) * I)) = Complex.exp (I * ((-(v * Real.log p) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p)]
    congr 1
    push_cast
    ring
  rw [e, norm_sub_rev]
  refine norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]

/-- One factor: `|1 − p^{−s−iv}| ≤ |1 − p^{−s}| (1 + e_p)`, `e_p = |v| log p · p^{−σ}/(1 − p^{−σ})`. -/
theorem norm_factor_shift_le {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    ‖1 - (p : ℂ) ^ (-(s + v * I))‖ ≤
      ‖1 - (p : ℂ) ^ (-s)‖ * (1 + |v| * (Real.log p * (p : ℝ) ^ (-s.re) / (1 - (p : ℝ) ^ (-s.re)))) := by
  have hp0 : 0 < p := by omega
  have hlt := rpow_neg_lt_one hp hs
  have hlow : 1 - (p : ℝ) ^ (-s.re) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one, norm_natCast_cpow_neg hp0] at h
    exact h
  have hpos : 0 < 1 - (p : ℝ) ^ (-s.re) := by linarith
  have hsplit : 1 - (p : ℂ) ^ (-(s + v * I)) =
      (1 - (p : ℂ) ^ (-s)) + (p : ℂ) ^ (-s) * (1 - (p : ℂ) ^ (-((v : ℂ) * I))) := by
    rw [cpow_neg_add_mul_I (by omega) s v]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_natCast_cpow_neg hp0]
  have h1 := norm_one_sub_cpow_I_le hp0 v
  have hr0 : 0 ≤ (p : ℝ) ^ (-s.re) := by positivity
  have hkey : (p : ℝ) ^ (-s.re) * (|v| * Real.log p) ≤
      ‖1 - (p : ℂ) ^ (-s)‖ * (|v| * (Real.log p * (p : ℝ) ^ (-s.re) / (1 - (p : ℝ) ^ (-s.re)))) := by
    have e : ‖1 - (p : ℂ) ^ (-s)‖ * (|v| * (Real.log p * (p : ℝ) ^ (-s.re) / (1 - (p : ℝ) ^ (-s.re)))) =
        (|v| * Real.log p * (p : ℝ) ^ (-s.re)) * (‖1 - (p : ℂ) ^ (-s)‖ / (1 - (p : ℝ) ^ (-s.re))) := by
      field_simp
    rw [e]
    have hratio : 1 ≤ ‖1 - (p : ℂ) ^ (-s)‖ / (1 - (p : ℝ) ^ (-s.re)) := by
      rw [le_div_iff₀ hpos, one_mul]
      exact hlow
    have h0 : 0 ≤ |v| * Real.log p * (p : ℝ) ^ (-s.re) := by
      have := Real.log_natCast_nonneg p
      positivity
    nlinarith
  calc ‖1 - (p : ℂ) ^ (-s)‖ + (p : ℝ) ^ (-s.re) * ‖1 - (p : ℂ) ^ (-((v : ℂ) * I))‖
      ≤ ‖1 - (p : ℂ) ^ (-s)‖ + (p : ℝ) ^ (-s.re) * (|v| * Real.log p) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 hr0)
    _ ≤ _ := by linarith

theorem abs_log_norm_factor_shift_le {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    |Real.log ‖1 - (p : ℂ) ^ (-(s + v * I))‖ - Real.log ‖1 - (p : ℂ) ^ (-s)‖| ≤
      |v| * (Real.log p * (p : ℝ) ^ (-s.re) / (1 - (p : ℝ) ^ (-s.re))) := by
  have hs' : 0 < (s + v * I).re := by simpa using hs
  have hre : (s + v * I).re = s.re := by simp
  have hA := norm_factor_shift_le hp hs v
  have hB := norm_factor_shift_le hp hs' (-v)
  rw [hre, abs_neg, show s + v * I + ((-v : ℝ) : ℂ) * I = s by push_cast; ring] at hB
  have hn1 : 0 < ‖1 - (p : ℂ) ^ (-(s + v * I))‖ := norm_pos_iff.mpr (one_sub_cpow_ne_zero hp hs')
  have hn2 : 0 < ‖1 - (p : ℂ) ^ (-s)‖ := norm_pos_iff.mpr (one_sub_cpow_ne_zero hp hs)
  set e := |v| * (Real.log p * (p : ℝ) ^ (-s.re) / (1 - (p : ℝ) ^ (-s.re))) with he
  have he0 : 0 ≤ e := by
    have := rpow_neg_lt_one hp hs
    have := Real.log_natCast_nonneg p
    have : 0 ≤ (p : ℝ) ^ (-s.re) := by positivity
    rw [he]
    refine mul_nonneg (abs_nonneg v) (div_nonneg (by positivity) (by linarith))
  have hlog : Real.log (1 + e) ≤ e := by
    have := Real.log_le_sub_one_of_pos (x := 1 + e) (by linarith)
    linarith
  have h1 : Real.log ‖1 - (p : ℂ) ^ (-(s + v * I))‖ ≤ Real.log ‖1 - (p : ℂ) ^ (-s)‖ + e := by
    have := Real.log_le_log hn1 hA
    rw [Real.log_mul hn2.ne' (by linarith)] at this
    linarith
  have h2 : Real.log ‖1 - (p : ℂ) ^ (-s)‖ ≤ Real.log ‖1 - (p : ℂ) ^ (-(s + v * I))‖ + e := by
    have := Real.log_le_log hn2 hB
    rw [Real.log_mul hn1.ne' (by linarith)] at this
    linarith
  rw [abs_le]
  constructor <;> linarith

theorem log_norm_eulerMollifier_eq (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Real.log ‖eulerMollifier y s‖ = ∑ p ∈ headPrimes y, Real.log ‖1 - (p : ℂ) ^ (-s)‖ := by
  rw [eulerMollifier, norm_prod, Real.log_prod]
  intro p hp
  exact (norm_pos_iff.mpr (one_sub_cpow_ne_zero (Finset.mem_filter.mp hp).2.two_le hs)).ne'

/-- **The head is frozen at its resolution.** -/
theorem abs_log_norm_eulerMollifier_sub_le (y : ℕ) {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    |Real.log ‖eulerMollifier y (s + v * I)‖ - Real.log ‖eulerMollifier y s‖| ≤ |v| * resolutionSum y s.re := by
  have hs' : 0 < (s + v * I).re := by simpa using hs
  rw [log_norm_eulerMollifier_eq y hs', log_norm_eulerMollifier_eq y hs, ← Finset.sum_sub_distrib,
    resolutionSum, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp =>
    abs_log_norm_factor_shift_le (Finset.mem_filter.mp hp).2.two_le hs v)

/-- The head itself: `log|E_y| = −log|M_y|`. -/
theorem abs_log_norm_eulerHead_sub_le (y : ℕ) {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    |Real.log ‖RHTower.eulerHead y (s + v * I)‖ - Real.log ‖RHTower.eulerHead y s‖| ≤ |v| * resolutionSum y s.re := by
  rw [eulerHead_eq_inv, eulerHead_eq_inv, norm_inv, norm_inv, Real.log_inv, Real.log_inv, neg_sub_neg, abs_sub_comm]
  exact abs_log_norm_eulerMollifier_sub_le y hs v

/-- On `Re s ≥ 1` the resolution sum is at most `2(log y + log 4)`. -/
theorem resolutionSum_le_of_one_le {y : ℕ} (hy : 1 ≤ y) {σ : ℝ} (hσ : 1 ≤ σ) :
    resolutionSum y σ ≤ 2 * (Real.log y + Real.log 4) := by
  have h := RHTower.Sieve.sum_log_div_prime_le hy
  have hset : headPrimes y = Nat.primesLE y := by
    ext p
    simp [headPrimes, Nat.primesLE, Nat.primesBelow]
  rw [resolutionSum, hset]
  have hterm : ∀ p ∈ Nat.primesLE y,
      Real.log p * (p : ℝ) ^ (-σ) / (1 - (p : ℝ) ^ (-σ)) ≤ 2 * (Real.log p / p) := by
    intro p hp
    rw [Nat.primesLE, Nat.mem_primesBelow] at hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hr : (p : ℝ) ^ (-σ) ≤ 1 / p := by
      rw [Real.rpow_neg hp0.le, one_div]
      exact inv_anti₀ hp0 (by simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ p) hσ)
    have hr2 : (p : ℝ) ^ (-σ) ≤ 1 / 2 := hr.trans (by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith)
    have hr0 : 0 ≤ (p : ℝ) ^ (-σ) := by positivity
    have hlog := Real.log_natCast_nonneg p
    rw [div_le_iff₀ (by linarith)]
    have : Real.log p * (p : ℝ) ^ (-σ) ≤ Real.log p * (1 / p) := mul_le_mul_of_nonneg_left hr hlog
    have h3 : 2 * (Real.log p / p) * (1 - (p : ℝ) ^ (-σ)) ≥ Real.log p / p := by
      have : Real.log p / p ≥ 0 := by positivity
      nlinarith
    rw [mul_one_div] at this
    linarith
  calc ∑ p ∈ Nat.primesLE y, Real.log p * (p : ℝ) ^ (-σ) / (1 - (p : ℝ) ^ (-σ))
      ≤ ∑ p ∈ Nat.primesLE y, 2 * (Real.log p / p) := Finset.sum_le_sum hterm
    _ = 2 * ∑ p ∈ Nat.primesLE y, Real.log p / p := by rw [Finset.mul_sum]
    _ ≤ 2 * (Real.log y + Real.log 4) := by linarith

/-- **On `Re s ≥ 1` the head is frozen at resolution `1/log y`.** -/
theorem abs_log_norm_eulerHead_sub_le_of_one_le {y : ℕ} (hy : 1 ≤ y) {s : ℂ} (hs : 1 ≤ s.re) (v : ℝ) :
    |Real.log ‖RHTower.eulerHead y (s + v * I)‖ - Real.log ‖RHTower.eulerHead y s‖| ≤
      2 * |v| * (Real.log y + Real.log 4) := by
  have h := abs_log_norm_eulerHead_sub_le y (by linarith) v
  have h2 := resolutionSum_le_of_one_le hy hs
  have := mul_le_mul_of_nonneg_left h2 (abs_nonneg v)
  linarith

/-- `|ζ| = |E_y| · |ζ M_y|` on `Re s > 0`: the head times the tail. -/
theorem norm_zeta_eq_head_mul_tail (y : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta s‖ = ‖RHTower.eulerHead y s‖ * ‖eulerTail y s‖ := by
  rw [eulerHead_eq_inv, eulerTail, norm_inv, norm_mul]
  have h := norm_pos_iff.mpr (eulerMollifier_ne_zero y hs)
  field_simp

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
