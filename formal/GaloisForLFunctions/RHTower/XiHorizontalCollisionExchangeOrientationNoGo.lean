import GaloisForLFunctions.RHTower.EulerShiftPairIncidenceCurrent

/-!
# Exchange orientation at a horizontal collision

The literal Poincare--Lelong thin slice orders equal-height divisor pairs by positive real
shift.  This file tests the most direct signed extension: weight an unordered collision by its
oriented real displacement.  It fails identically, because exchanging the pair reverses that
displacement while preserving both the collision carrier and multiplicity product.

The exact positive survivor is the multiplicity-weighted squared displacement.  It is twice its
positive-order half, so it retains orientation magnitude but cannot choose an orientation sign.
Thus an HC source comparison with nonzero signed cancellation must preserve data beyond an
unlabelled zero pair: an external source label, a non-exchange-stable domain, or another
order-breaking structure.
-/

open Complex Set Filter Topology

namespace RHTower.EulerShiftPairIncidenceCurrent

noncomputable section

/-- The multiplicity-weighted first real-shift displacement cancels on every complete collision
pair carrier. -/
theorem sum_collisionPairs_multiplicity_signed_displacement_eq_zero
    (S : Finset ℂ) (m : ℂ → ℕ) (lo hi : ℝ) :
    (∑ p ∈ collisionPairs S lo hi,
      (m p.1 : ℝ) * (m p.2 : ℝ) * (p.2.re - p.1.re)) = 0 := by
  classical
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p _
    ring
  · intro p hp _ hfix
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.2.2.2
    apply hpne
    exact congrArg Prod.fst hfix.symm
  · intro p hp
    rw [collisionPairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    rcases hp with ⟨⟨hp₁, hp₂⟩, hlo, hhi, him, hne⟩
    exact ⟨⟨hp₂, hp₁⟩, him ▸ hlo, him ▸ hhi, him.symm, fun h => hne h.symm⟩
  · intro p _
    rfl

/-- Specialization of the exchange cancellation to the literal finite Xi collision carrier. -/
theorem xiHorizontalCollisionPairs_signed_displacement_eq_zero (T : ℝ) :
    (∑ p ∈ xiHorizontalCollisionPairs T,
      ((analyticOrderAt xi p.1).toNat : ℝ) *
        ((analyticOrderAt xi p.2).toNat : ℝ) * (p.2.re - p.1.re)) = 0 := by
  rw [← collisionPairs_xiRelevant_eq]
  exact sum_collisionPairs_multiplicity_signed_displacement_eq_zero
    (xiThinSliceRelevantZeros T) (fun rho => (analyticOrderAt xi rho).toNat) 0 T

/-- Every exchange-symmetric weight on collision pairs is twice its positive-order part. -/
theorem sum_collisionPairs_eq_two_mul_orientedPairs_of_swap
    (S : Finset ℂ) (lo hi : ℝ) (f : ℂ × ℂ → ℝ)
    (hswap : ∀ p : ℂ × ℂ, f p.swap = f p) :
    (∑ p ∈ collisionPairs S lo hi, f p) =
      2 * ∑ p ∈ orientedPairs S lo hi, f p := by
  let P := collisionPairs S lo hi
  let Q := orientedPairs S lo hi
  have hpos : P.filter (fun p => p.1.re < p.2.re) = Q := by
    ext p
    simp only [P, Q, collisionPairs, orientedPairs, Finset.mem_filter,
      Finset.mem_product]
    constructor
    · rintro ⟨⟨hS, hlo, hhi, him, _hne⟩, hlt⟩
      exact ⟨hS, hlo, hhi, him, hlt⟩
    · rintro ⟨hS, hlo, hhi, him, hlt⟩
      refine ⟨⟨hS, hlo, hhi, him, ?_⟩, hlt⟩
      intro heq
      exact (ne_of_lt hlt) (congrArg Complex.re heq)
  have hneg :
      ∑ p ∈ P.filter (fun p => ¬ p.1.re < p.2.re), f p = ∑ p ∈ Q, f p := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp
      rcases hp with ⟨hpP, hnlt⟩
      simp only [P, collisionPairs, Finset.mem_filter, Finset.mem_product] at hpP
      rcases hpP with ⟨⟨hpS, hqS⟩, hlo, hhi, him, hne⟩
      have hreNe : p.2.re ≠ p.1.re := by
        intro hre
        apply hne
        apply Complex.ext
        · exact hre.symm
        · exact him
      have hlt : p.2.re < p.1.re :=
        lt_of_le_of_ne (not_lt.mp hnlt) hreNe
      simp only [Q, orientedPairs, Finset.mem_filter, Finset.mem_product,
        Prod.fst_swap, Prod.snd_swap]
      exact ⟨⟨hqS, hpS⟩, him ▸ hlo, him ▸ hhi, him.symm, hlt⟩
    · intro p hp
      simp only [Q, orientedPairs, Finset.mem_filter, Finset.mem_product] at hp
      rcases hp with ⟨⟨hpS, hqS⟩, hlo, hhi, him, hlt⟩
      simp only [Finset.mem_filter, P, collisionPairs, Finset.mem_product,
        Prod.fst_swap, Prod.snd_swap]
      refine ⟨⟨⟨hqS, hpS⟩, him ▸ hlo, him ▸ hhi, him.symm, ?_⟩, ?_⟩
      · intro heq
        have hre := congrArg Complex.re heq
        exact (ne_of_lt hlt) hre.symm
      · exact not_lt.mpr (le_of_lt hlt)
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      exact (hswap p).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not P
    (fun p => p.1.re < p.2.re) f
  calc
    (∑ p ∈ collisionPairs S lo hi, f p) = ∑ p ∈ P, f p := rfl
    _ = (∑ p ∈ P.filter (fun p => p.1.re < p.2.re), f p) +
        ∑ p ∈ P.filter (fun p => ¬ p.1.re < p.2.re), f p := hsplit.symm
    _ = (∑ p ∈ Q, f p) + ∑ p ∈ Q, f p := by rw [hpos, hneg]
    _ = 2 * ∑ p ∈ orientedPairs S lo hi, f p := by
      simp only [Q]
      ring

/-- Exchange-invariant squared real-shift orientation retained by a collision carrier. -/
def collisionPairOrientationSquare
    (S : Finset ℂ) (m : ℂ → ℕ) (lo hi : ℝ) : ℝ :=
  ∑ p ∈ collisionPairs S lo hi,
    (m p.1 : ℝ) * (m p.2 : ℝ) * (p.2.re - p.1.re) ^ (2 : ℕ)

theorem collisionPairOrientationSquare_nonneg
    (S : Finset ℂ) (m : ℂ → ℕ) (lo hi : ℝ) :
    0 ≤ collisionPairOrientationSquare S m lo hi := by
  unfold collisionPairOrientationSquare
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)

/-- The orientation-square survivor is exactly the doubled positive-order collision sum. -/
theorem collisionPairOrientationSquare_eq_two_mul_oriented
    (S : Finset ℂ) (m : ℂ → ℕ) (lo hi : ℝ) :
    collisionPairOrientationSquare S m lo hi =
      2 * ∑ p ∈ orientedPairs S lo hi,
        (m p.1 : ℝ) * (m p.2 : ℝ) * (p.2.re - p.1.re) ^ (2 : ℕ) := by
  unfold collisionPairOrientationSquare
  apply sum_collisionPairs_eq_two_mul_orientedPairs_of_swap
  intro p
  rcases p with ⟨rho, sigma⟩
  dsimp
  ring

end

end RHTower.EulerShiftPairIncidenceCurrent
