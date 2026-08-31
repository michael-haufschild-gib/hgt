import GaloisForLFunctions.RHTower.Sieve.KloostermanSum
import GaloisForLFunctions.RHTower.Sieve.FinitePowerSumFourier

/-!
# Kloosterman additive-frequency second moment

Additive-character orthogonality gives the exact complete second moment
`sum_n |S(m,n;q)|^2 = q * φ(q)`.  This is average square-root cancellation for every nonzero
modulus.  It is the finite Plancherel layer beneath later spectral large-sieve estimates; it does
not replace the pointwise Weil bound.
-/

open scoped BigOperators

noncomputable section

namespace RHTower.Sieve

/-- Equality of inverse unit residues detects equality of the units. -/
private theorem coe_inv_eq_coe_inv_iff
    (q : ℕ) [NeZero q] (x y : (ZMod q)ˣ) :
    (((x⁻¹ : (ZMod q)ˣ) : ZMod q) = ((y⁻¹ : (ZMod q)ˣ) : ZMod q)) ↔ x = y := by
  constructor
  · intro h
    have hi : x⁻¹ = y⁻¹ := Units.ext h
    simpa using congrArg Inv.inv hi
  · rintro rfl
    rfl

/-- Complete Kloosterman sums have exact additive-frequency second moment `q φ(q)`. -/
theorem sum_normSq_kloostermanSum
    (q : ℕ) [NeZero q] (m : ZMod q) :
    ∑ n : ZMod q, Complex.normSq (kloostermanSum q m n) =
      (q : ℝ) * Nat.totient q := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  simp only [kloostermanSum, map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ x : (ZMod q)ˣ, ∑ n : ZMod q, ∑ y : (ZMod q)ˣ,
        star (kloostermanPhase q m n x) * kloostermanPhase q m n y) =
        ∑ x : (ZMod q)ˣ, ∑ y : (ZMod q)ˣ, ∑ n : ZMod q,
          star (kloostermanPhase q m n x) * kloostermanPhase q m n y := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ x : (ZMod q)ˣ, ∑ y : (ZMod q)ˣ,
          ZMod.stdAddChar (m * ((y : (ZMod q)ˣ) : ZMod q) -
            m * ((x : (ZMod q)ˣ) : ZMod q)) *
          (∑ n : ZMod q, ZMod.stdAddChar
            (n * (((y⁻¹ : (ZMod q)ˣ) : ZMod q) -
              ((x⁻¹ : (ZMod q)ˣ) : ZMod q)))) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      change (starRingEnd ℂ)
          (ZMod.stdAddChar (m * (x : ZMod q) +
            n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) *
          ZMod.stdAddChar (m * (y : ZMod q) +
            n * ((y⁻¹ : (ZMod q)ˣ) : ZMod q)) = _
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
        ← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ x : (ZMod q)ˣ, ∑ y : (ZMod q)ˣ,
          ZMod.stdAddChar (m * ((y : (ZMod q)ˣ) : ZMod q) -
            m * ((x : (ZMod q)ˣ) : ZMod q)) *
          (if x = y then (q : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [sum_stdAddChar_mul]
      by_cases hxy : x = y
      · subst y
        simp
      · have hinv :
            ((y⁻¹ : (ZMod q)ˣ) : ZMod q) -
                ((x⁻¹ : (ZMod q)ˣ) : ZMod q) ≠ 0 := by
          rw [sub_ne_zero]
          intro hinv
          exact hxy ((coe_inv_eq_coe_inv_iff q y x).mp hinv).symm
        simp [hxy, hinv]
    _ = ∑ x : (ZMod q)ˣ, (q : ℂ) := by
      apply Finset.sum_congr rfl
      intro x _
      simp
    _ = (q : ℂ) * Nat.totient q := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        ZMod.card_units_eq_totient]
      ring

/-- Norm-square form of the exact Kloosterman second moment. -/
theorem sum_norm_kloostermanSum_sq
    (q : ℕ) [NeZero q] (m : ZMod q) :
    ∑ n : ZMod q, ‖kloostermanSum q m n‖ ^ 2 =
      (q : ℝ) * Nat.totient q := by
  simpa only [Complex.normSq_eq_norm_sq] using sum_normSq_kloostermanSum q m

end RHTower.Sieve
