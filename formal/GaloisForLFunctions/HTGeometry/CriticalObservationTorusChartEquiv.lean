import GaloisForLFunctions.HTGeometry.CriticalObservationChartRing
import GaloisForLFunctions.HTGeometry.LocalizationTwoPrimeUnits
import GaloisForLFunctions.HTGeometry.LocalizationAwayRingEquiv

/-!
# The critical observation chart is a standard two-torus chart

The observation coordinates consist of two nonempty finite blocks.  Reindex them so that the
distinguished coordinate in each block is first, and then transport localization away from their
product.  This gives the exact coordinate-ring identification with `(G_m)^2 x A^(m+n-2)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

private theorem equivCast_fin_val {a b : ℕ} (h : a = b) (x : Fin a) :
    ((Equiv.cast (congrArg Fin h)) x).val = x.val := by
  subst h
  rfl

/-- Reindex the two observation-coordinate blocks with their marked coordinates first. -/
noncomputable def criticalObservationTorusIndexEquiv (m n : ℕ)
    [Fact (0 < m)] [Fact (0 < n)] :
    Fin n ⊕ Fin m ≃ Fin ((n + m - 2) + 2) := by
  have hm : 0 < m := Fact.out
  have hn : 0 < n := Fact.out
  have hnle : n < n + m := by omega
  have htotal : n + m = (n + m - 2) + 2 := by omega
  exact finSumFinEquiv.trans
    ((Equiv.swap (⟨n, hnle⟩ : Fin (n + m)) (⟨1, by omega⟩ : Fin (n + m))).trans
      (Equiv.cast (congrArg Fin htotal)))

theorem criticalObservationTorusIndexEquiv_inl_zero (m n : ℕ)
    [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationTorusIndexEquiv m n (Sum.inl (⟨0, Fact.out⟩ : Fin n)) =
      (⟨0, by omega⟩ : Fin ((n + m - 2) + 2)) := by
  apply Fin.ext
  have hm : 0 < m := Fact.out
  have hn : 0 < n := Fact.out
  simp only [criticalObservationTorusIndexEquiv, Equiv.trans_apply,
    finSumFinEquiv_apply_left]
  rw [equivCast_fin_val, Equiv.swap_apply_def]
  have h0n : Fin.castAdd m (⟨0, hn⟩ : Fin n) ≠ (⟨n, by omega⟩ : Fin (n + m)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have h01 : Fin.castAdd m (⟨0, hn⟩ : Fin n) ≠ (⟨1, by omega⟩ : Fin (n + m)) := by
    intro h
    have := congrArg Fin.val h
    simp at this
  rw [if_neg h0n, if_neg h01]
  simp
  all_goals omega

theorem criticalObservationTorusIndexEquiv_inr_zero (m n : ℕ)
    [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationTorusIndexEquiv m n (Sum.inr (⟨0, Fact.out⟩ : Fin m)) =
      (⟨1, by omega⟩ : Fin ((n + m - 2) + 2)) := by
  apply Fin.ext
  have hm : 0 < m := Fact.out
  have hn : 0 < n := Fact.out
  simp only [criticalObservationTorusIndexEquiv, Equiv.trans_apply,
    finSumFinEquiv_apply_right]
  rw [equivCast_fin_val]
  have hnat : Fin.natAdd n (⟨0, hm⟩ : Fin m) = (⟨n, by omega⟩ : Fin (n + m)) :=
    Fin.ext (by simp)
  rw [hnat, Equiv.swap_apply_left]
  all_goals omega

/-- Polynomial-coordinate equivalence underlying the chart identification. -/
noncomputable def criticalObservationPolynomialTorusEquiv
    (K : Type*) [Field K] (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationRing K m n ≃+*
      MvPolynomial (Fin ((n + m - 2) + 2)) K :=
  (MvPolynomial.renameEquiv K (criticalObservationTorusIndexEquiv m n)).toRingEquiv

theorem criticalObservationPolynomialTorusEquiv_marked
    (K : Type*) [Field K] (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationPolynomialTorusEquiv K m n
        (criticalObservationMarked K (m := m) (n := n)) =
      (X 0 * X 1 : MvPolynomial (Fin ((n + m - 2) + 2)) K) := by
  simp [criticalObservationPolynomialTorusEquiv, criticalObservationMarked,
    criticalObservationTorusIndexEquiv_inl_zero,
    criticalObservationTorusIndexEquiv_inr_zero]

/-- **The critical observation chart is the standard two-torus affine chart.** -/
noncomputable def criticalObservationChartTorusEquiv
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) [Fact (0 < m)] [Fact (0 < n)] :
    criticalObservationChartRing K m n ≃+* TorusChart K (n + m - 2) :=
  awayRingEquiv (criticalObservationPolynomialTorusEquiv K m n)
    (criticalObservationPolynomialTorusEquiv_marked K m n)

end GaloisForLFunctions.HTGeometry
