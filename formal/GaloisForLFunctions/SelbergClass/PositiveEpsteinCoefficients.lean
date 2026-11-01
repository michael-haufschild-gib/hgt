import GaloisForLFunctions.RHTower.EisensteinHeckeFactorizationAtI
import GaloisForLFunctions.RHTower.Sieve.DivisorBound

/-!
# Positive coefficients of the rectangular Epstein series

The form `m² + 64n²` is the Gaussian norm restricted to imaginary parts divisible
by eight. Its representation fibers give nonnegative normalized Dirichlet
coefficients. The fibers at five and thirteen are empty, while sixty-five is
represented, so the coefficient stream is not multiplicative.
-/

noncomputable section

open Complex Finset
open RHTower.GaussianTwoSquares

namespace GaloisForLFunctions.SelbergClass.PositiveEpstein

/-- Gaussian integers of norm `n` whose imaginary part is divisible by eight. -/
def normFiber (n : ℕ) : Finset GaussianInt :=
  (normSet n).filter fun z => (8 : ℤ) ∣ z.im

theorem mem_normFiber {n : ℕ} {z : GaussianInt} :
    z ∈ normFiber n ↔ z.norm = n ∧ (8 : ℤ) ∣ z.im := by
  simp only [normFiber, Finset.mem_filter, mem_normSet]

/-- Half the representation count, with the zero Dirichlet coefficient suppressed. -/
def coeff (n : ℕ) : ℝ := if n = 0 then 0 else (normFiber n).card / 2

@[simp] theorem coeff_zero : coeff 0 = 0 := by simp only [coeff, if_pos rfl]

theorem coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  by_cases hn : n = 0
  · simp only [coeff, if_pos hn, le_refl]
  · simp only [coeff, if_neg hn]
    positivity

/-- Below norm sixty-four, a represented Gaussian integer lies on the real axis. -/
theorem im_eq_zero_of_mem_normFiber {n : ℕ} {z : GaussianInt}
    (hn : n < 64) (hz : z ∈ normFiber n) : z.im = 0 := by
  obtain ⟨hz, v, hv⟩ := mem_normFiber.mp hz
  rw [norm_eq, hv] at hz
  have hn' : (n : ℤ) < 64 := by exact_mod_cast hn
  have hvbound : 64 * v ^ 2 ≤ (n : ℤ) := by nlinarith only [hz, sq_nonneg z.re]
  have hv2 : v ^ 2 = 0 := by have := sq_nonneg v; omega
  have hv0 : v = 0 := by
    rw [pow_two] at hv2
    rcases mul_eq_zero.mp hv2 with h | h <;> exact h
  simpa only [hv0, mul_zero] using hv

theorem normFiber_one : normFiber 1 = {⟨1, 0⟩, ⟨-1, 0⟩} := by
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    have him := im_eq_zero_of_mem_normFiber (by norm_num : 1 < 64) hz
    have hnorm := (mem_normFiber.mp hz).1
    rw [norm_eq, him] at hnorm
    have hfactor : (z.re - 1) * (z.re + 1) = 0 := by nlinarith only [hnorm]
    rcases mul_eq_zero.mp hfactor with h | h
    · left
      have hre : z.re = 1 := by linarith only [h]
      cases z
      simp_all
    · right
      have hre : z.re = -1 := by linarith only [h]
      cases z
      simp_all
  · rintro (rfl | rfl) <;> norm_num [mem_normFiber, norm_eq]

@[simp] theorem coeff_one : coeff 1 = 1 := by
  norm_num [coeff, normFiber_one]

private theorem not_square_five (m : ℤ) : m ^ 2 ≠ 5 := by
  intro hm
  have hlo : -3 < m := by nlinarith only [hm, sq_nonneg (m + 3)]
  have hhi : m < 3 := by nlinarith only [hm, sq_nonneg (m - 3)]
  have hmlo : 0 ≤ m + 2 := by omega
  have hmhi : 0 ≤ 2 - m := by omega
  nlinarith only [hm, mul_nonneg hmlo hmhi]

private theorem not_square_thirteen (m : ℤ) : m ^ 2 ≠ 13 := by
  intro hm
  have hlo : -4 < m := by nlinarith only [hm, sq_nonneg (m + 4)]
  have hhi : m < 4 := by nlinarith only [hm, sq_nonneg (m - 4)]
  have hmlo : 0 ≤ m + 3 := by omega
  have hmhi : 0 ≤ 3 - m := by omega
  nlinarith only [hm, mul_nonneg hmlo hmhi]

theorem normFiber_five : normFiber 5 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have him := im_eq_zero_of_mem_normFiber (by norm_num : 5 < 64) hz
  have hnorm := (mem_normFiber.mp hz).1
  apply not_square_five z.re
  simpa only [norm_eq, him, zero_pow (by norm_num : 2 ≠ 0), add_zero] using hnorm

theorem normFiber_thirteen : normFiber 13 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have him := im_eq_zero_of_mem_normFiber (by norm_num : 13 < 64) hz
  have hnorm := (mem_normFiber.mp hz).1
  apply not_square_thirteen z.re
  simpa only [norm_eq, him, zero_pow (by norm_num : 2 ≠ 0), add_zero] using hnorm

@[simp] theorem coeff_five : coeff 5 = 0 := by simp [coeff, normFiber_five]

@[simp] theorem coeff_thirteen : coeff 13 = 0 := by simp [coeff, normFiber_thirteen]

theorem coeff_sixtyfive_pos : 0 < coeff 65 := by
  have hmem : (⟨1, 8⟩ : GaussianInt) ∈ normFiber 65 := by
    norm_num [mem_normFiber, norm_eq]
  have hcard : 0 < (normFiber 65).card := Finset.card_pos.mpr ⟨_, hmem⟩
  simp only [coeff, show (65 : ℕ) ≠ 0 by norm_num, if_false]
  positivity

/-- The normalized positive coefficient stream fails multiplicativity at `5 · 13`. -/
theorem coeff_not_multiplicative :
    Nat.Coprime 5 13 ∧ coeff (5 * 13) ≠ coeff 5 * coeff 13 := by
  refine ⟨by norm_num, ?_⟩
  rw [coeff_five, coeff_thirteen, zero_mul]
  exact coeff_sixtyfive_pos.ne'

end GaloisForLFunctions.SelbergClass.PositiveEpstein
