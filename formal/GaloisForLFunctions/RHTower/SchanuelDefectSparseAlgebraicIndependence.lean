import GaloisForLFunctions.RHTower.SchanuelDefectSingletonAlgebraicIndependence

/-!
# Sparse algebraic-coefficient independence of Schanuel defects

The one-variable algebraic-closure result rules out every relation supported on at most one
coordinate of an arbitrary rationally independent tuple.  This packages that exact sparse floor
without imposing a bound on the tuple's dimension.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- An algebraic-coefficient relation among defects of a rationally independent tuple is trivial
whenever at most one coefficient is nonzero. -/
theorem schanuelDefect_algebraic_relation_of_support_card_le_one
    {n : ℕ} (x : Fin n → ℂ) (hx : LinearIndependent ℚ x)
    (c : Fin n → algebraicClosure ℚ ℂ)
    (hc : (Finset.univ.filter fun i => c i ≠ 0).card ≤ 1)
    (hrel : ∑ i, c i • schanuelDefect (x i) = 0) :
    c = 0 := by
  classical
  funext i
  change c i = 0
  by_contra hci
  have hi : i ∈ Finset.univ.filter fun j => c j ≠ 0 := by
    simp [hci]
  have hsingle : ∑ j, c j • schanuelDefect (x j) =
      c i • schanuelDefect (x i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hcj : c j = 0 := by
        by_contra hcj
        have hj : j ∈ Finset.univ.filter fun k => c k ≠ 0 := by
          simp [hcj]
        exact hji ((Finset.card_le_one.mp hc) j hj i hi)
      simp [hcj]
    · simp
  have hzero : c i • schanuelDefect (x i) = 0 := by
    rw [← hsingle]
    exact hrel
  exact hci ((smul_eq_zero.mp hzero).resolve_right
    (schanuelDefect_ne_zero_of_ne_zero (x i) (hx.ne_zero i)))

end


end GaloisForLFunctions.RHTower
