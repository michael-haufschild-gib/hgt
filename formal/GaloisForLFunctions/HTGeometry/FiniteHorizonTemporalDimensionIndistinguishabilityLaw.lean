import GaloisForLFunctions.HTGeometry.ProjectiveRecurrenceDenseStratificationLaw

/-!
# Finite-horizon indistinguishability of quantum temporal dimension

For every finite spectral packet, every positive admissible projective
temporal rank can be imposed by an arbitrarily small spectral perturbation.
The perturbation can simultaneously be made invisible, below any prescribed
tolerance, to every normalized Heisenberg probe throughout any prescribed
finite observation horizon.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open NormedSpace

/-- Every positive temporal dimension is compatible with every finite-horizon
normalized-probe record up to arbitrary positive tolerance. -/
theorem exists_finiteHorizonIndistinguishable_exactProjectiveTemporalRank
    {d k : ℕ} (hk : 0 < k) (hkd : k ≤ d)
    (energy : Fin (d + 1) → ℝ)
    (H η : ℝ) (hH : 0 ≤ H) (hη : 0 < η) :
    ∃ perturbed : Fin (d + 1) → ℝ,
      projectiveTemporalRank perturbed = k ∧
      (∀ i, dist (perturbed i) (energy i) < η / (2 * (H + 1))) ∧
      ∀ (O : RHTower.FiniteIndexClockSpace (Fin (d + 1)) →L[ℂ]
            RHTower.FiniteIndexClockSpace (Fin (d + 1)))
          (t : ℝ),
        ‖O‖ ≤ 1 → |t| ≤ H →
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian perturbed)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian perturbed))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian energy)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian energy)))‖ < η := by
  let δ : ℝ := η / (2 * (H + 1))
  have hH1 : 0 < H + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨perturbed, hrank, hclose⟩ :=
    exists_exactProjectiveTemporalRank_close hk hkd energy δ hδ
  refine ⟨perturbed, hrank, hclose, ?_⟩
  intro O t hO ht
  have hwindowNorm :
      ‖RHTower.finiteIndexDiagonalHamiltonian perturbed -
          RHTower.finiteIndexDiagonalHamiltonian energy‖ ≤ δ := by
    apply finiteIndexDiagonalHamiltonian_norm_sub_le
      perturbed energy δ hδ.le
    intro i
    rw [← Real.dist_eq]
    exact (hclose i).le
  calc
    _ ≤ 2 * |t| *
          ‖RHTower.finiteIndexDiagonalHamiltonian perturbed -
            RHTower.finiteIndexDiagonalHamiltonian energy‖ * ‖O‖ :=
      selfAdjoint_heisenbergEvolution_norm_sub_le
        (RHTower.finiteIndexDiagonalHamiltonian perturbed)
        (RHTower.finiteIndexDiagonalHamiltonian energy) O
        (finiteIndexDiagonalHamiltonian_isSelfAdjoint perturbed)
        (finiteIndexDiagonalHamiltonian_isSelfAdjoint energy) t
    _ ≤ 2 * H * δ * 1 := by gcongr
    _ < η := by
      dsimp [δ]
      field_simp
      nlinarith

/-- From three levels onward, no bounded-time normalized-probe experiment can
certify the exact completed temporal dimension within any positive tolerance. -/
theorem exists_finiteHorizonIndistinguishable_differentTemporalDimension
    {d : ℕ} (hd : 2 ≤ d)
    (energy : Fin (d + 1) → ℝ)
    (H η : ℝ) (hH : 0 ≤ H) (hη : 0 < η) :
    ∃ perturbed : Fin (d + 1) → ℝ,
      projectiveTemporalRank perturbed ≠ projectiveTemporalRank energy ∧
      ∀ (O : RHTower.FiniteIndexClockSpace (Fin (d + 1)) →L[ℂ]
            RHTower.FiniteIndexClockSpace (Fin (d + 1)))
          (t : ℝ),
        ‖O‖ ≤ 1 → |t| ≤ H →
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian perturbed)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian perturbed))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian energy)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian energy)))‖ < η := by
  let k : ℕ := if projectiveTemporalRank energy = 1 then 2 else 1
  have hkpos : 0 < k := by
    dsimp [k]
    split <;> omega
  have hkle : k ≤ d := by
    dsimp [k]
    split <;> omega
  have hkne : k ≠ projectiveTemporalRank energy := by
    dsimp [k]
    split <;> omega
  obtain ⟨perturbed, hrank, _, hprobe⟩ :=
    exists_finiteHorizonIndistinguishable_exactProjectiveTemporalRank
      hkpos hkle energy H η hH hη
  refine ⟨perturbed, ?_, hprobe⟩
  intro heq
  exact hkne (hrank.symm.trans heq)

end
end GaloisForLFunctions.HTGeometry
