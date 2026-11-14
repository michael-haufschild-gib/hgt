import GaloisForLFunctions.GaloisTheoryOfZeros.TheHermiteMonodromyOfACollision

/-!
# The explicit permutation of a double collision

The two Hermite labels are `√2` and `−√2`. A half-turn in the square-root
time parameter interchanges their actual analytic sheets, which remain
distinct off the collision. This specifies the local permutation on the
domain of double collisions; it makes no collision-existence assertion.
-/

noncomputable section
open Complex Filter Topology
open RHTower RHTower.DeBruijn
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- The exact complex root labels of the double-collision profile. -/
theorem heatModelFwd_two_roots (ρ : ℂ) :
    heatModelFwd 2 ρ = 0 ↔ ρ = (Real.sqrt 2 : ℂ) ∨ ρ = -(Real.sqrt 2 : ℂ) := by
  rw [heatModelFwd_eq_zero_iff, profileRoots_two]
  constructor
  · rintro ⟨r, hr, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Complex.ofReal_neg _)
  · rintro (rfl | rfl)
    · exact ⟨Real.sqrt 2, Finset.mem_insert_self _ _, rfl⟩
    · exact ⟨-Real.sqrt 2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        Complex.ofReal_neg _⟩

/-- The actual local monodromy is the transposition of the two specified Hermite sheets. -/
theorem eventually_doubleCollision_transposition {τ ζ : ℂ} (hc : IsCollision τ ζ 2) :
    ∀ᶠ s : ℂ in 𝓝[≠] 0,
      collisionZero τ ζ 2 (Real.sqrt 2 : ℂ) (-s) =
        collisionZero τ ζ 2 (-(Real.sqrt 2 : ℂ)) s ∧
      collisionZero τ ζ 2 (-(Real.sqrt 2 : ℂ)) (-s) =
        collisionZero τ ζ 2 (Real.sqrt 2 : ℂ) s ∧
      collisionZero τ ζ 2 (Real.sqrt 2 : ℂ) s ≠
        collisionZero τ ζ 2 (-(Real.sqrt 2 : ℂ)) s := by
  have hp := (heatModelFwd_two_roots (Real.sqrt 2 : ℂ)).mpr (Or.inl rfl)
  have hn := (heatModelFwd_two_roots (-(Real.sqrt 2 : ℂ))).mpr (Or.inr rfl)
  have hne : (Real.sqrt 2 : ℂ) ≠ -(Real.sqrt 2 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re] at hre
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    linarith only [hre, hpos]
  filter_upwards [(collisionZero_neg hc hp).filter_mono nhdsWithin_le_nhds,
    (collisionZero_neg hc hn).filter_mono nhdsWithin_le_nhds,
    collisionZero_ne hc hp hn hne] with s hp' hn' hne'
  exact ⟨hp', by simpa only [neg_neg] using hn', hne'⟩

#print axioms heatModelFwd_two_roots
#print axioms eventually_doubleCollision_transposition

end GaloisForLFunctions.GaloisTheoryOfZeros
