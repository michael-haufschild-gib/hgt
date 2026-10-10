import GaloisForLFunctions.RHTower.PrimeWinningFaceUnit
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Exact half-plane range of the prime Euler exponential

A canonical logarithmic preimage gives every nonzero value. Norms classify
its open and closed half-plane ranges, including the boundary. This supplies
the exact nonvanishing parameter domain of the transported Euler factor.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A canonical preimage of any nonzero Euler value. -/
def paperPrimeExponentialPreimage (p : Nat.Primes) (z : {z : ℂ // z ≠ 0}) : ℂ :=
  -Complex.log (z : ℂ) / (Real.log (p : ℕ) : ℂ)

/-- The logarithmic preimage realizes the literal complex prime power. -/
theorem paperPrimeExponentialPreimage_cpow (p : Nat.Primes) (z : {z : ℂ // z ≠ 0}) :
    ((p : ℕ) : ℂ) ^ (-paperPrimeExponentialPreimage p z) = (z : ℂ) := by
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hlogR : Real.log (p : ℕ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast p.property.one_lt))
  have hlog : (Real.log (p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hlogR
  rw [paperPrimeExponentialPreimage, Complex.cpow_def_of_ne_zero hp,
    ← Complex.natCast_log]
  have he : (Real.log (p : ℕ) : ℂ) *
      -(-Complex.log (z : ℂ) / (Real.log (p : ℕ) : ℂ)) = Complex.log (z : ℂ) := by
    field_simp
  rw [he, Complex.exp_log z.property]

/-- The preimage's real part is the exact logarithmic modulus slope. -/
theorem paperPrimeExponentialPreimage_re (p : Nat.Primes) (z : {z : ℂ // z ≠ 0}) :
    (paperPrimeExponentialPreimage p z).re =
      -Real.log ‖(z : ℂ)‖ / Real.log (p : ℕ) := by
  rw [paperPrimeExponentialPreimage, Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]

/-- An open right half-plane maps onto exactly the punctured open Euler disk. -/
theorem paperPrimeExponential_openHalfPlane_range (p : Nat.Primes) (σ : ℝ) (z : ℂ) :
    (∃ s : ℂ, σ < s.re ∧ ((p : ℕ) : ℂ) ^ (-s) = z) ↔
      z ≠ 0 ∧ ‖z‖ < (p : ℝ) ^ (-σ) := by
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  constructor
  · rintro ⟨s, hs, hz⟩
    refine ⟨fun h => RHTower.primeCpow_neg_ne_zero (-s) p (hz.trans h), ?_⟩
    rw [← hz, Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
    exact (Real.rpow_lt_rpow_left_iff hp).mpr (neg_lt_neg hs)
  · rintro ⟨hz, hnorm⟩
    refine ⟨paperPrimeExponentialPreimage p ⟨z, hz⟩, ?_,
      paperPrimeExponentialPreimage_cpow p ⟨z, hz⟩⟩
    rw [paperPrimeExponentialPreimage_re]
    have hlog := Real.log_lt_log (norm_pos_iff.mpr hz) hnorm
    rw [Real.log_rpow (lt_trans zero_lt_one hp)] at hlog
    apply (lt_div_iff₀ (Real.log_pos hp)).mpr
    linarith

/-- A closed right half-plane retains exactly the boundary circle as well. -/
theorem paperPrimeExponential_closedHalfPlane_range (p : Nat.Primes) (σ : ℝ) (z : ℂ) :
    (∃ s : ℂ, σ ≤ s.re ∧ ((p : ℕ) : ℂ) ^ (-s) = z) ↔
      z ≠ 0 ∧ ‖z‖ ≤ (p : ℝ) ^ (-σ) := by
  have hp : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.property.one_lt
  constructor
  · rintro ⟨s, hs, hz⟩
    refine ⟨fun h => RHTower.primeCpow_neg_ne_zero (-s) p (hz.trans h), ?_⟩
    rw [← hz, Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
    exact (Real.rpow_le_rpow_left_iff hp).mpr (neg_le_neg hs)
  · rintro ⟨hz, hnorm⟩
    refine ⟨paperPrimeExponentialPreimage p ⟨z, hz⟩, ?_,
      paperPrimeExponentialPreimage_cpow p ⟨z, hz⟩⟩
    rw [paperPrimeExponentialPreimage_re]
    have hlog := Real.log_le_log (norm_pos_iff.mpr hz) hnorm
    rw [Real.log_rpow (lt_trans zero_lt_one hp)] at hlog
    apply (le_div_iff₀ (Real.log_pos hp)).mpr
    linarith

/-- All parameters with a nonvanishing denominator on an open half-plane are classified. -/
theorem paperPrimeTransport_openHalfPlane_nonvanishing_iff (p : Nat.Primes) (σ : ℝ) (t : ℂ) :
    (∀ s : ℂ, σ < s.re → 1 - t - ((p : ℕ) : ℂ) ^ (-s) ≠ 0) ↔
      t = 1 ∨ (p : ℝ) ^ (-σ) ≤ ‖1 - t‖ := by
  constructor
  · intro h
    by_cases ht : t = 1
    · exact Or.inl ht
    · right
      by_contra hnorm
      have hz : 1 - t ≠ 0 := fun he => ht (sub_eq_zero.mp he).symm
      obtain ⟨s, hs, he⟩ := (paperPrimeExponential_openHalfPlane_range p σ (1 - t)).mpr
        ⟨hz, lt_of_not_ge hnorm⟩
      exact h s hs (by rw [he, sub_self])
  · rintro (rfl | hnorm) s hs
    · simpa only [sub_self, zero_sub, neg_ne_zero] using
        RHTower.primeCpow_neg_ne_zero (-s) p
    · intro he
      have hsmall := (paperPrimeExponential_openHalfPlane_range p σ (1 - t)).mp
        ⟨s, hs, (sub_eq_zero.mp he).symm⟩
      exact (not_lt_of_ge hnorm) hsmall.2

/-- Preserving the boundary as well requires strict separation from the Euler disk. -/
theorem paperPrimeTransport_closedHalfPlane_nonvanishing_iff (p : Nat.Primes) (σ : ℝ) (t : ℂ) :
    (∀ s : ℂ, σ ≤ s.re → 1 - t - ((p : ℕ) : ℂ) ^ (-s) ≠ 0) ↔
      t = 1 ∨ (p : ℝ) ^ (-σ) < ‖1 - t‖ := by
  constructor
  · intro h
    by_cases ht : t = 1
    · exact Or.inl ht
    · right
      by_contra hnorm
      have hz : 1 - t ≠ 0 := fun he => ht (sub_eq_zero.mp he).symm
      obtain ⟨s, hs, he⟩ := (paperPrimeExponential_closedHalfPlane_range p σ (1 - t)).mpr
        ⟨hz, le_of_not_gt hnorm⟩
      exact h s hs (by rw [he, sub_self])
  · rintro (rfl | hnorm) s hs
    · simpa only [sub_self, zero_sub, neg_ne_zero] using
        RHTower.primeCpow_neg_ne_zero (-s) p
    · intro he
      have hsmall := (paperPrimeExponential_closedHalfPlane_range p σ (1 - t)).mp
        ⟨s, hs, (sub_eq_zero.mp he).symm⟩
      exact (not_le_of_gt hnorm) hsmall.2

end

end GaloisForLFunctions.HTGeometry
