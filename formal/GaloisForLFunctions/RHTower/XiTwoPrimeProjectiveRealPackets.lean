import GaloisForLFunctions.HTGeometry.FourPowerGeneralizedCircle
import GaloisForLFunctions.HTGeometry.WeldClassTable
import GaloisForLFunctions.RHTower.Deninger.DeningerSteinbergKummerSuccessorNormalTransgression
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Two prime-power packets and the critical line

The four-power packets of the rational Kummer character at `2` and `3` each lie
on a generalized circle exactly when the parameter is critical or real. At Xi
zeros, real-axis nonvanishing removes the second branch and gives an RH criterion.
-/

open Complex GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open scoped ComplexConjugate

namespace RHTower.TwoPrimeProjectiveReal

/-- Half-shifted rational character at a natural-number scale. -/
noncomputable def primeMarking (s : ℂ) (p : ℕ) : ℂ :=
  Complex.exp ((1 / 2 - s) * (Real.log p : ℂ))

/-- Exponential markings never vanish. -/
theorem primeMarking_ne_zero (s : ℂ) (p : ℕ) : primeMarking s p ≠ 0 :=
  Complex.exp_ne_zero _

/-- The marking is the existing Kummer character on a positive rational basis element. -/
theorem primeMarking_eq_source (s : ℂ) {p : ℕ} (hp : 0 < p) :
    primeMarking s p =
      deningerKummerCharacter (1 / 2 - s)
        (deningerSteinbergBasis
          (deningerScalingOfPositiveRational (p : ℚ) (by exact_mod_cast hp))) := by
  rw [deningerKummerCharacter_basis]
  simp only [deningerScalingOfPositiveRational_val, Rat.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne')]
  rw [← Complex.ofReal_log (by exact_mod_cast hp.le)]
  simp only [primeMarking, mul_comm]

/-- Every power marking comes from the corresponding power of the source basis element. -/
theorem primeMarking_pow_eq_source (s : ℂ) {p : ℕ} (hp : 0 < p) (k : ℕ) :
    primeMarking s p ^ k =
      deningerKummerCharacter (1 / 2 - s)
        ((deningerSteinbergBasis
          (deningerScalingOfPositiveRational (p : ℚ) (by exact_mod_cast hp))) ^ k) := by
  rw [map_pow, ← primeMarking_eq_source s hp]

/-- Product with the conjugate records the real displacement from the critical line. -/
theorem primeMarking_mul_conj (s : ℂ) (p : ℕ) :
    primeMarking s p * conj (primeMarking s p) =
      (Real.exp ((1 - 2 * s.re) * Real.log p) : ℂ) := by
  rw [primeMarking, ← Complex.exp_conj, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re]
    norm_num
    ring_nf
  · simp only [Complex.add_im, Complex.conj_im, Complex.ofReal_im, add_neg_cancel]

/-- At every scale greater than one, the unit-circle branch is exactly the critical line. -/
theorem primeMarking_mul_conj_eq_one_iff (s : ℂ) {p : ℕ} (hp : 1 < p) :
    primeMarking s p * conj (primeMarking s p) = 1 ↔ s.re = 1 / 2 := by
  rw [primeMarking_mul_conj, ← Complex.ofReal_one, Complex.ofReal_inj,
    Real.exp_eq_one_iff]
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp)).ne'
  rw [mul_eq_zero, or_iff_left hlog]
  constructor <;> intro h <;> linarith

/-- The real branch is an integral phase resonance. -/
theorem primeMarking_real_iff (s : ℂ) (p : ℕ) :
    primeMarking s p = conj (primeMarking s p) ↔
      ∃ k : ℤ, (k : ℝ) * Real.pi = -s.im * Real.log p := by
  have hre (a : ℂ) : a = conj a ↔ a.im = 0 := by
    constructor
    · intro h
      have hi := congrArg Complex.im h
      simp only [Complex.conj_im] at hi
      linarith
    · intro h
      apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im, h, neg_zero]
  rw [hre, primeMarking, Complex.exp_im]
  rw [mul_eq_zero, or_iff_right (Real.exp_ne_zero _)]
  have him : ((1 / 2 - s) * (Real.log p : ℂ)).im = -s.im * Real.log p := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, Complex.sub_im]
    norm_num
  rw [him, Real.sin_eq_zero_iff]

/-- Independence of the two prime logarithms removes every nonzero common resonance. -/
theorem two_primeMarkings_real_iff (s : ℂ) :
    (primeMarking s 2 = conj (primeMarking s 2) ∧
      primeMarking s 3 = conj (primeMarking s 3)) ↔ s.im = 0 := by
  simp only [primeMarking_real_iff]
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    have hrel : (l : ℝ) * Real.log 2 + ((-k : ℤ) : ℝ) * Real.log 3 = 0 := by
      have he : ((l : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3) * Real.pi = 0 := by
        calc
          _ = ((l : ℝ) * Real.pi) * Real.log 2 -
              ((k : ℝ) * Real.pi) * Real.log 3 := by ring_nf
          _ = 0 := by rw [hk, hl]; ring_nf
      have := (mul_eq_zero.mp he).resolve_right Real.pi_ne_zero
      simpa only [Int.cast_neg, neg_mul, sub_eq_add_neg] using this
    have hz := two_prime_log_indep (p := 2) (q := 3)
      (by norm_num) (by norm_num) (by norm_num) l (-k) hrel
    have hl0 : l = 0 := hz.1
    rw [hl0, Int.cast_zero, zero_mul] at hl
    have hlog : Real.log (3 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
    exact neg_eq_zero.mp ((mul_eq_zero.mp hl.symm).resolve_right hlog)
  · intro h
    constructor <;> exact ⟨0, by simp [h]⟩

/-- Each prime packet may have its own generalized circle. -/
def TwoPrimeRealPackets (s : ℂ) : Prop :=
  FourPowerGeneralizedCircle (primeMarking s 2) ∧
    FourPowerGeneralizedCircle (primeMarking s 3)

/-- Complete classification, including the real-axis branch and all repeated markings. -/
theorem twoPrimeRealPackets_iff (s : ℂ) :
    TwoPrimeRealPackets s ↔ s.re = 1 / 2 ∨ s.im = 0 := by
  rw [TwoPrimeRealPackets,
    fourPowerGeneralizedCircle_iff (primeMarking_ne_zero s 2),
    fourPowerGeneralizedCircle_iff (primeMarking_ne_zero s 3),
    primeMarking_mul_conj_eq_one_iff s (by norm_num : 1 < (2 : ℕ)),
    primeMarking_mul_conj_eq_one_iff s (by norm_num : 1 < (3 : ℕ)),
    ← two_primeMarkings_real_iff s]
  tauto

/-- Away from the real axis, the finite packet condition is precisely critical-line membership. -/
theorem twoPrimeRealPackets_iff_of_nonreal {s : ℂ} (hs : s.im ≠ 0) :
    TwoPrimeRealPackets s ↔ s.re = 1 / 2 := by
  rw [twoPrimeRealPackets_iff, or_iff_left hs]

/-- Real-strip nonvanishing removes the extra branch at nontrivial zeta zeros. -/
theorem twoPrimeRealPackets_iff_at_zeta_zero {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    TwoPrimeRealPackets s ↔ s.re = 1 / 2 := by
  apply twoPrimeRealPackets_iff_of_nonreal
  intro hi
  have hs : s = (s.re : ℂ) := by apply Complex.ext <;> simp only [ofReal_re, ofReal_im, hi]
  rw [hs] at hz
  exact riemannZeta_real_strip_ne_zero h0 h1 hz

/-- The packet criterion at every Xi zero, with no strip hypothesis. -/
theorem twoPrimeRealPackets_iff_at_xi_zero {s : ℂ} (hz : xi s = 0) :
    TwoPrimeRealPackets s ↔ s.re = 1 / 2 := by
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hz
  exact twoPrimeRealPackets_iff_at_zeta_zero h0 h1
    (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hz).1

/-- The universal packet condition is equivalent to mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_iff_twoPrimeRealPackets :
    RiemannHypothesis ↔ ∀ s : ℂ, xi s = 0 → TwoPrimeRealPackets s := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  exact forall_congr' fun s => imp_congr_right fun hs =>
    (twoPrimeRealPackets_iff_at_xi_zero hs).symm

end RHTower.TwoPrimeProjectiveReal
