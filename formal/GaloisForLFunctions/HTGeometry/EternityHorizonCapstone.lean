import GaloisForLFunctions.HTGeometry.ProjectiveExactReturnRankOne
import GaloisForLFunctions.HTGeometry.ObserverProfileStability

/-!
# Uniform bounded-horizon indistinguishability of the eternities

A commuting Hermitian perturbation of prescribed temporal dimension can be chosen small enough that
the two unitary evolutions stay within any prescribed error for any prescribed horizon: the
perturbation radius `η / T` turns the Duhamel bound `‖U_H(t) - U_K(t)‖ ≤ |t| ‖H - K‖` into a
uniform bound on `|t| ≤ T`.

Consequently, from three levels onward, every Hamiltonian has both an exactly returning and a never
exactly returning commuting neighbour whose evolutions are uniformly indistinguishable on a horizon
fixed before the perturbation is chosen.  Exact eternal recurrence is therefore invisible to every
bounded-time operator-norm observation.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

/-- The Duhamel bound below the horizon: a perturbation of radius `η / T` is uniformly
`η`-indistinguishable on `[-T, T]`. -/
theorem norm_unitaryEvolution_sub_lt_of_le_horizon {H K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K) {T η : ℝ} (hT : 0 < T)
    (hnorm : ‖K - H‖ < η / T) {t : ℝ} (ht : |t| ≤ T) :
    ‖unitaryEvolution K t - unitaryEvolution H t‖ < η := by
  have hbase := norm_unitaryEvolution_sub_le K H hK hH t
  have hnn : (0 : ℝ) ≤ ‖K - H‖ := norm_nonneg _
  have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hmul : |t| * ‖K - H‖ ≤ T * ‖K - H‖ := mul_le_mul_of_nonneg_right ht hnn
  have hlt : T * ‖K - H‖ < T * (η / T) := by
    exact mul_lt_mul_of_pos_left hnorm hT
  have hval : T * (η / T) = η := by field_simp
  rw [hval] at hlt
  exact lt_of_le_of_lt (le_trans hbase hmul) hlt

/-- **Theorem C `(2)`: uniform bounded-horizon indistinguishability at every temporal
dimension.**  Every Hermitian matrix has, for every horizon `T`, every error `η` and every
prescribed temporal dimension `k`, a commuting simple-spectrum Hermitian neighbour of exactly that
dimension whose unitary evolution stays within `η` of its own throughout `|t| ≤ T`. -/
theorem exists_isHermitian_commuting_gapRank_uniform_horizon {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ} (hT : 0 < T)
    (hη : 0 < η) :
    ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ),
      B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧
        B = (Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) hA.eigenvectorUnitary)
              (Matrix.diagonal (RCLike.ofReal ∘ E')) ∧
        rationalCoordinateRank (fun j : Fin n => E' j.succ - E' 0) = k ∧
        ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η := by
  obtain ⟨B, E', hherm, hcomm, hinj, hnorm, hconj, hrank⟩ :=
    exists_isHermitian_commuting_close_gapRank hk hkn A hA (div_pos hη hT)
  refine ⟨B, E', hherm, hcomm, hinj, hconj, hrank, fun t ht => ?_⟩
  exact norm_unitaryEvolution_sub_lt_of_le_horizon hA hherm hT hnorm ht

/-- **Corollary 1 with a horizon fixed in advance.**  From three levels onward every Hermitian
matrix has, inside every uniform bounded-horizon indistinguishability tube, both a commuting
simple-spectrum neighbour that returns exactly and one that never returns exactly. -/
theorem exists_isHermitian_commuting_periodic_and_aperiodic_uniform_horizon (hn : 2 ≤ n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) {T η : ℝ} (hT : 0 < T)
    (hη : 0 < η) :
    (∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ),
        B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧
          HasPositiveProjectiveReturn E' ∧
          B = (Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
                hA.eigenvectorUnitary) (Matrix.diagonal (RCLike.ofReal ∘ E')) ∧
          ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η) ∧
      ∃ (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (E' : Fin (n + 1) → ℝ),
        B.IsHermitian ∧ B * A = A * B ∧ Function.Injective E' ∧
          ¬ HasPositiveProjectiveReturn E' ∧
          B = (Unitary.conjStarAlgAut ℂ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
                hA.eigenvectorUnitary) (Matrix.diagonal (RCLike.ofReal ∘ E')) ∧
          ∀ t : ℝ, |t| ≤ T → ‖unitaryEvolution B t - unitaryEvolution A t‖ < η := by
  constructor
  · obtain ⟨B, E', hherm, hcomm, hinj, hconj, hrank, hclose⟩ :=
      exists_isHermitian_commuting_gapRank_uniform_horizon (k := 1) one_pos (by omega) A hA hT hη
    exact ⟨B, E', hherm, hcomm, hinj,
      (hasPositiveProjectiveReturn_iff_gapRank_le_one E').mpr (le_of_eq hrank), hconj, hclose⟩
  · obtain ⟨B, E', hherm, hcomm, hinj, hconj, hrank, hclose⟩ :=
      exists_isHermitian_commuting_gapRank_uniform_horizon (k := 2) two_pos hn A hA hT hη
    refine ⟨B, E', hherm, hcomm, hinj, ?_, hconj, hclose⟩
    intro hret
    have hle := (hasPositiveProjectiveReturn_iff_gapRank_le_one E').mp hret
    rw [hrank] at hle
    omega

end

end GaloisForLFunctions.HTGeometry
