import GaloisForLFunctions.RHTower.Sieve.KloostermanCrossModulusCorrelation

/-!
# Complete equal-modulus Kloosterman column correlation

Additive-character orthogonality evaluates the complete correlation of two Kloosterman columns as
the modulus times one zero-frequency Kloosterman sum.  Thus the equal-modulus complete-period
piece is elementary; incomplete windows and distinct moduli contain the remaining cancellation.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Complete inner product of two Kloosterman columns modulo `q`. -/
def kloostermanCompleteColumnCorrelation
    (q : ℕ) [NeZero q] (n k : ZMod q) : ℂ :=
  ∑ m : ZMod q, star (kloostermanSum q m n) * kloostermanSum q m k

/-- Exact complete-column correlation: `q S(0,k-n;q)`. -/
theorem kloostermanCompleteColumnCorrelation_eq
    (q : ℕ) [NeZero q] (n k : ZMod q) :
    kloostermanCompleteColumnCorrelation q n k =
      (q : ℂ) * kloostermanSum q 0 (k - n) := by
  unfold kloostermanCompleteColumnCorrelation
  simp_rw [star_kloostermanSum]
  unfold kloostermanSum kloostermanPhase
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.sum_comm]
  have hpair (y : (ZMod q)ˣ) :
      (∑ m : ZMod q,
        ZMod.stdAddChar (-m * (x : ZMod q) + -n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) *
          ZMod.stdAddChar (m * (y : ZMod q) + k * ((y⁻¹ : (ZMod q)ˣ) : ZMod q))) =
        ZMod.stdAddChar
            (k * ((y⁻¹ : (ZMod q)ˣ) : ZMod q) -
              n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) *
          ∑ m : ZMod q,
            ZMod.stdAddChar (m * ((y : ZMod q) - (x : ZMod q))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _hm
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  calc
    (∑ y : (ZMod q)ˣ, ∑ m : ZMod q,
        ZMod.stdAddChar (-m * (x : ZMod q) + -n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) *
          ZMod.stdAddChar (m * (y : ZMod q) + k * ((y⁻¹ : (ZMod q)ˣ) : ZMod q))) =
        ∑ m : ZMod q,
          ZMod.stdAddChar (-m * (x : ZMod q) + -n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) *
            ZMod.stdAddChar (m * (x : ZMod q) + k * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
      apply Fintype.sum_eq_single x
      intro y hy
      have hres : (y : ZMod q) - (x : ZMod q) ≠ 0 := by
        intro h
        apply hy
        apply Units.ext
        exact sub_eq_zero.mp h
      rw [hpair]
      simp [sum_stdAddChar_mul, hres]
    _ = _ := by
      rw [hpair]
      simp
      rw [show k * ((x⁻¹ : (ZMod q)ˣ) : ZMod q) -
        n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q) =
        (k - n) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q) by ring]
      ring

/-- Diagonal complete-column energy is exactly `q * phi(q)`. -/
theorem kloostermanCompleteColumnCorrelation_diagonal
    (q : ℕ) [NeZero q] (n : ZMod q) :
    kloostermanCompleteColumnCorrelation q n n =
      (q : ℂ) * (Nat.totient q : ℂ) := by
  rw [kloostermanCompleteColumnCorrelation_eq]
  simp

end

end RHTower.Sieve
