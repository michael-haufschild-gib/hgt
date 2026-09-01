import GaloisForLFunctions.HTGeometry.RangeDeterminantFormation

/-!
# Rank-jump relative determinant creation

For an injective refinement from rank `d` to rank `d+1`, old oriented volume survives faithfully in
exterior degree `d`, but new top volume cannot come from the old stage in exterior degree `d+1`.
This is the exact finite-dimensional obstruction that forces a relative determinant increment in a
rank-changing formation history.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

noncomputable section

variable {K U V : Type*} [Field K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Old source top exterior degree is a line. -/
theorem finrank_exteriorPower_oldSource_of_rankJump
    (d : ℕ) (hU : finrank K U = d) :
    finrank K (⋀[K]^d U) = 1 := by
  rw [exteriorPower.finrank_eq, hU, Nat.choose_self]

/-- At old top degree, the one-rank-larger target has `d+1` exterior coordinates. -/
theorem finrank_exteriorPower_oldDegree_newTarget_of_rankJump
    (d : ℕ) (hV : finrank K V = d + 1) :
    finrank K (⋀[K]^d V) = d + 1 := by
  rw [exteriorPower.finrank_eq, hV]
  have hs := Nat.choose_symm (n := d + 1) (k := 1) (by omega)
  have hsub : d + 1 - 1 = d := by omega
  rw [hsub] at hs
  rw [Nat.choose_one_right] at hs
  exact hs

/-- At new top degree, old source exterior power vanishes. -/
theorem finrank_exteriorPower_newDegree_oldSource_of_rankJump
    (d : ℕ) (hU : finrank K U = d) :
    finrank K (⋀[K]^(d + 1) U) = 0 := by
  rw [exteriorPower.finrank_eq, hU, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self d)]

/-- New target top exterior degree is a line. -/
theorem finrank_exteriorPower_newTarget_of_rankJump
    (d : ℕ) (hV : finrank K V = d + 1) :
    finrank K (⋀[K]^(d + 1) V) = 1 := by
  rw [exteriorPower.finrank_eq, hV, Nat.choose_self]

omit [FiniteDimensional K U] [FiniteDimensional K V] in
/-- Old oriented volume survives injectively across a rank jump. -/
theorem exteriorPower_oldDegree_injective_of_rankJump
    (d : ℕ) (i : U →ₗ[K] V) (hi : Function.Injective i) :
    Function.Injective (exteriorPower.map d i) :=
  exteriorPower_map_injective d hi

omit [FiniteDimensional K V] in
/-- Image of old oriented volume remains exactly one-dimensional in the larger old-degree
carrier. -/
theorem finrank_range_exteriorPower_oldDegree_of_rankJump
    (d : ℕ) (i : U →ₗ[K] V) (hi : Function.Injective i)
    (hU : finrank K U = d) :
    finrank K (LinearMap.range (exteriorPower.map d i)) = 1 := by
  rw [LinearMap.finrank_range_of_inj
    (exteriorPower_oldDegree_injective_of_rankJump d i hi),
    finrank_exteriorPower_oldSource_of_rankJump d hU]

/-- New top volume cannot be transported from the old stage by exterior functoriality. -/
theorem not_surjective_exteriorPower_newDegree_of_rankJump
    (d : ℕ) (i : U →ₗ[K] V)
    (hU : finrank K U = d) (hV : finrank K V = d + 1) :
    ¬ Function.Surjective (exteriorPower.map (d + 1) i) := by
  intro hsurj
  have hle := LinearMap.finrank_le_finrank_of_surjective hsurj
  rw [finrank_exteriorPower_newTarget_of_rankJump d hV,
    finrank_exteriorPower_newDegree_oldSource_of_rankJump d hU] at hle
  omega

end

end GaloisForLFunctions.HTGeometry
