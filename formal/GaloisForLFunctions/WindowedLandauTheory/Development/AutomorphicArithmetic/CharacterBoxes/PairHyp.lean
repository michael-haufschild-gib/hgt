import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

/-! The congruences of a prime pair give the required quadratic splitting conditions. -/

open WindowedLandauTheory.HC WindowedLandauTheory.FrobeniusOrbits UpperTheory.Top

private theorem jac_neg_of_dvd {p d : ℕ} (h : p ∣ d + 1) : jacobiSym (-(d : ℤ)) p = 1 := by
  have h1 : (-(d : ℤ)) ≡ 1 [ZMOD (p : ℤ)] := by
    apply Int.modEq_iff_dvd.2
    have h2 := Int.natCast_dvd_natCast.2 h
    push_cast at h2
    have h3 : (1 : ℤ) - -(d : ℤ) = (d : ℤ) + 1 := by ring
    rw [h3]
    exact h2
  rw [jacobiSym.mod_left' h1, jacobiSym.one_left]

theorem UpperTheory.Top.pairHyp :
    ∀ (eps Y : ℝ) (q d : ℕ), WinPair eps Y q d → HostHyp q d ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ Y ^ (eps / 5) → jacobiSym (-(d : ℤ)) p = 1) ∧
      (∀ a : ℕ, Odd a → jacobiSym (-(q : ℤ)) a = jacobiSym (a : ℤ) q ∧ jacobiSym (-(d : ℤ)) a = jacobiSym (a : ℤ) d) := by
  intro eps Y q d hw
  have hq4 : q % 4 = 3 := by have := hw.q_mod; omega
  have hd4 : d % 4 = 3 := by have := hw.d_mod; omega
  refine ⟨⟨hw.q_prime, hw.d_prime, hw.q_mod, hw.d_mod, jac_neg_of_dvd hw.d_q⟩, ?_, ?_⟩
  · intro p hp hp2 hpY
    exact jac_neg_of_dvd (hw.d_small p hp hp2 hpY)
  · intro a ha
    exact ⟨jacobi_neg_recip hq4 (Nat.odd_iff.mp ha), jacobi_neg_recip hd4 (Nat.odd_iff.mp ha)⟩
