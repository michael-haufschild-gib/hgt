import GaloisForLFunctions.HTGeometry.DyadicWalshCompactLevel
import GaloisForLFunctions.HTGeometry.LpInjectionCoordinates

/-! # Exact coefficients of the compact Walsh levels -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open RHTower QuantumAlg.WalshHadamard

theorem dyadicWalshLevel_apply_left (k m : ℕ) (r : Fin (2 ^ k))
    (x : lp (fun _ : ℕ => ℂ) 2) :
    dyadicWalshLevel k x (dyadicChild k 0 (m, r)) =
      ∑ s : Fin (2 ^ k), walshSign r s *
        dyadicColumnWeight k (dyadicChild k 1 (m, s)) * x (dyadicChild k 1 (m, s)) := by
  change (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) *
    lpScalarInjection (dyadicChild k 0) (dyadicChild_injective k 0)
      (walshBlockIsometry ℕ k
        (lpCoordinatePullback (E := ℂ) (dyadicChild k 1) (dyadicChild_injective k 1)
          (dyadicColumnOperator k x))) (dyadicChild k 0 (m, r)) = _
  rw [lpScalarInjection_coordinate, sqrt_mul_walshBlockIsometry_apply]
  apply Finset.sum_congr rfl
  intro s _
  change _ * (_ * _) = _
  ring

theorem dyadicWalshLevel_apply_of_not_left (k n : ℕ)
    (hn : n / 2 ^ k % 2 ≠ 0) (x : lp (fun _ : ℕ => ℂ) 2) :
    dyadicWalshLevel k x n = 0 := by
  have hni : n ∉ Set.range (dyadicChild k 0) := by
    rintro ⟨p, rfl⟩
    simp only [dyadicChild_div, Fin.val_zero, Nat.add_zero] at hn
    omega
  change (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) *
    lpScalarInjection (dyadicChild k 0) (dyadicChild_injective k 0) _ n = 0
  rw [lpScalarInjection_coordinate_of_not_mem _ _ _ _ hni, mul_zero]

def dyadicWalshEntry (k n j : ℕ) : ℂ :=
  if DyadicSibling k n j then
    walshSign ⟨n % 2 ^ k, Nat.mod_lt _ (by positivity)⟩
      ⟨j % 2 ^ k, Nat.mod_lt _ (by positivity)⟩ *
        ((2 * ((j : ℕ) : ℝ) + 2)⁻¹ : ℝ) else 0

theorem dyadicWalshLevel_single (k n j : ℕ) :
    dyadicWalshLevel k (lp.single 2 j 1) n = dyadicWalshEntry k n j := by
  classical
  by_cases hs : DyadicSibling k n j
  · obtain ⟨m, r, s, rfl, rfl⟩ := hs.coordinates
    rw [dyadicWalshLevel_apply_left]
    have he (u : Fin (2 ^ k)) : dyadicChild k 1 (m, u) = dyadicChild k 1 (m, s) ↔ u = s := by
      constructor
      · intro h
        exact congrArg Prod.snd (dyadicChild_injective k 1 h)
      · rintro rfl; rfl
    simp only [lp.single_apply, Pi.single_apply, he, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [dyadicColumnWeight_right, dyadicWalshEntry, if_pos hs]
    congr 2 <;> apply Fin.ext <;> simp
  · rw [dyadicWalshEntry, if_neg hs]
    by_cases hn : n / 2 ^ k % 2 = 0
    · let r : Fin (2 ^ k) := ⟨n % 2 ^ k, Nat.mod_lt _ (by positivity)⟩
      have he : dyadicChild k 0 (n / 2 ^ k / 2, r) = n := dyadicChild_eq_of_div hn
      rw [← he, dyadicWalshLevel_apply_left]
      apply Finset.sum_eq_zero
      intro s _
      have hj : dyadicChild k 1 (n / 2 ^ k / 2, s) ≠ j := by
        intro h
        apply hs
        rw [← he, ← h]
        exact dyadicChild_sibling k _ r s
      simp [lp.single_apply, hj]
    · exact dyadicWalshLevel_apply_of_not_left k n hn _

end
end GaloisForLFunctions.HTGeometry
