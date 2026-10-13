import GaloisForLFunctions.HTGeometry.WalshPowerLevels
import GaloisForLFunctions.HTGeometry.DyadicWalshSeries

/-! # Exact signed coefficients of the power-weighted Walsh levels -/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open RHTower QuantumAlg.WalshHadamard

namespace WalshPowerKernel

theorem level_apply_left (D : WalshPowerKernel) (k m : ℕ) (r : Fin (2 ^ k))
    (x : lp (fun _ : ℕ => ℂ) 2) :
    D.level k x (dyadicChild k 0 (m, r)) =
      D.leftWeight k (dyadicChild k 0 (m, r)) *
        ∑ s : Fin (2 ^ k), walshSign r s *
          D.rightWeight k (dyadicChild k 1 (m, s)) * x (dyadicChild k 1 (m, s)) := by
  change (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) *
    (D.leftWeight k (dyadicChild k 0 (m, r)) *
      lpScalarInjection (dyadicChild k 0) (dyadicChild_injective k 0)
        (walshBlockIsometry ℕ k
          (lpCoordinatePullback (E := ℂ) (dyadicChild k 1) (dyadicChild_injective k 1)
            (D.rightOperator k x))) (dyadicChild k 0 (m, r))) = _
  rw [lpScalarInjection_coordinate, mul_left_comm, sqrt_mul_walshBlockIsometry_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  change _ * (_ * _) = _
  ring

theorem level_apply_of_not_left (D : WalshPowerKernel) (k n : ℕ)
    (hn : n / 2 ^ k % 2 ≠ 0) (x : lp (fun _ : ℕ => ℂ) 2) : D.level k x n = 0 := by
  have hni : n ∉ Set.range (dyadicChild k 0) := by
    rintro ⟨p, rfl⟩
    simp only [dyadicChild_div, Fin.val_zero, Nat.add_zero] at hn
    omega
  change (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) *
    (D.leftWeight k n * lpScalarInjection (dyadicChild k 0) (dyadicChild_injective k 0) _ n) = 0
  rw [lpScalarInjection_coordinate_of_not_mem _ _ _ _ hni, mul_zero, mul_zero]

def levelEntry (D : WalshPowerKernel) (k n j : ℕ) : ℂ :=
  if DyadicSibling k n j then
    walshSign ⟨n % 2 ^ k, Nat.mod_lt _ (by positivity)⟩
      ⟨j % 2 ^ k, Nat.mod_lt _ (by positivity)⟩ * (D.row n * D.column j) else 0

theorem level_single (D : WalshPowerKernel) (k n j : ℕ) :
    D.level k (lp.single 2 j 1) n = D.levelEntry k n j := by
  classical
  by_cases hs : DyadicSibling k n j
  · obtain ⟨m, r, s, rfl, rfl⟩ := hs.coordinates
    rw [D.level_apply_left]
    have he (u : Fin (2 ^ k)) : dyadicChild k 1 (m, u) = dyadicChild k 1 (m, s) ↔ u = s := by
      constructor
      · intro h
        exact congrArg Prod.snd (dyadicChild_injective k 1 h)
      · rintro rfl; rfl
    simp only [lp.single_apply, Pi.single_apply, he, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [levelEntry, if_pos hs, mul_left_comm, D.leftWeight_mul_rightWeight hs]
    congr 2 <;> apply Fin.ext <;> simp
  · rw [levelEntry, if_neg hs]
    by_cases hn : n / 2 ^ k % 2 = 0
    · let r : Fin (2 ^ k) := ⟨n % 2 ^ k, Nat.mod_lt _ (by positivity)⟩
      have he : dyadicChild k 0 (n / 2 ^ k / 2, r) = n := dyadicChild_eq_of_div hn
      rw [← he, D.level_apply_left]
      have hz : (∑ s : Fin (2 ^ k), walshSign r s *
          D.rightWeight k (dyadicChild k 1 (n / 2 ^ k / 2, s)) *
            (lp.single 2 j (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)
              (dyadicChild k 1 (n / 2 ^ k / 2, s))) = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        have hj : dyadicChild k 1 (n / 2 ^ k / 2, s) ≠ j := by
          intro h
          apply hs
          rw [← he, ← h]
          exact dyadicChild_sibling k _ r s
        simp [lp.single_apply, hj]
      rw [hz, mul_zero]
    · exact D.level_apply_of_not_left k n hn _

end WalshPowerKernel
end
end GaloisForLFunctions.HTGeometry
