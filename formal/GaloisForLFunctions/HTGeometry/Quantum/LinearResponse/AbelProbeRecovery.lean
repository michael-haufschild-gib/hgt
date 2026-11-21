import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelDephasingInverse

/-!
# Two inverse probes recover a Hamiltonian modulo scalars

The commutator with a numbered diagonal probe recovers all off-diagonal
entries. The commutator with the all-ones probe recovers diagonal
differences from row and column sums. These formulas give explicit
reconstruction from the preimages of two fixed Hermitian targets.
-/

open Matrix Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The diagonal probe separates the numbered basis positions. -/
def abelDiagonalProbe (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i : Fin d => (i.val : ℂ))

/-- The all-ones probe couples every pair of numbered positions. -/
def abelSumProbe (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun _ _ => 1

theorem abelDiagonalProbe_isHermitian (d : ℕ) : (abelDiagonalProbe d).IsHermitian := by
  change (abelDiagonalProbe d)ᴴ = abelDiagonalProbe d
  rw [abelDiagonalProbe, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  change (starRingEnd ℂ) (i.val : ℂ) = (i.val : ℂ)
  exact Complex.conj_natCast _

theorem abelSumProbe_isHermitian (d : ℕ) : (abelSumProbe d).IsHermitian := by
  change (abelSumProbe d)ᴴ = abelSumProbe d
  ext i j
  simp only [abelSumProbe, Matrix.conjTranspose_apply, Matrix.of_apply, star_one]

variable {d : ℕ}

private def abelOffDiagonalFromReadout (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if i = j then 0 else M i j / ((j.val : ℂ) - (i.val : ℂ))

private theorem abelOffDiagonalFromReadout_eq (H : Matrix (Fin d) (Fin d) ℂ) :
    abelOffDiagonalFromReadout (H * abelDiagonalProbe d - abelDiagonalProbe d * H) =
      H - Matrix.diagonal (fun i => H i i) := by
  ext i j
  simp only [abelOffDiagonalFromReadout, Matrix.of_apply, Matrix.sub_apply]
  by_cases hij : i = j
  · subst j
    simp only [if_true, Matrix.diagonal_apply_eq, sub_self]
  · rw [if_neg hij, abelDiagonalProbe, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.diagonal_apply_ne _ hij, sub_zero]
    have hd : (j.val : ℂ) - (i.val : ℂ) ≠ 0 := by
      intro h
      exact hij (Fin.ext (Nat.cast_injective (sub_eq_zero.mp h)).symm)
    rw [show H i j * (j.val : ℂ) - (i.val : ℂ) * H i j =
      H i j * ((j.val : ℂ) - (i.val : ℂ)) from by ring, mul_div_cancel_right₀ _ hd]

/-- Reconstruct the Hamiltonian relative to its diagonal entry at the
chosen anchor. The two data matrices are the forcings for the two probes. -/
def abelRelativeRecovery (o : Fin d) (ε : Ioi (0 : ℝ))
    (forcingD forcingJ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  let A := abelOffDiagonalFromReadout (abelCommutatorReadout ε (abelDiagonalProbe d) forcingD)
  let B := abelCommutatorReadout ε (abelSumProbe d) forcingJ
  Matrix.of fun i j => if i = j then B i o - (∑ k, A i k) + ∑ k, A k o else A i j

theorem abelRelativeRecovery_apply_ne (o : Fin d) (ε : Ioi (0 : ℝ))
    (forcingD forcingJ : Matrix (Fin d) (Fin d) ℂ) {i j : Fin d} (hij : i ≠ j) :
    abelRelativeRecovery o ε forcingD forcingJ i j =
      abelCommutatorReadout ε (abelDiagonalProbe d) forcingD i j /
        ((j.val : ℂ) - (i.val : ℂ)) := by
  simp only [abelRelativeRecovery, abelOffDiagonalFromReadout, Matrix.of_apply, if_neg hij]

theorem abelRelativeRecovery_diag (o : Fin d) (ε : Ioi (0 : ℝ))
    (forcingD forcingJ : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    abelRelativeRecovery o ε forcingD forcingJ i i =
      abelCommutatorReadout ε (abelSumProbe d) forcingJ i o -
        (∑ k, if i = k then 0 else abelRelativeRecovery o ε forcingD forcingJ i k) +
        ∑ k, if k = o then 0 else abelRelativeRecovery o ε forcingD forcingJ k o := by
  let A := abelOffDiagonalFromReadout (abelCommutatorReadout ε (abelDiagonalProbe d) forcingD)
  have hoff (v w : Fin d) :
      A v w = if v = w then 0 else abelRelativeRecovery o ε forcingD forcingJ v w := by
    by_cases h : v = w
    · simp only [A, abelOffDiagonalFromReadout, Matrix.of_apply, if_pos h]
    · simp only [A, abelRelativeRecovery, Matrix.of_apply, if_neg h]
  change (if i = i then abelCommutatorReadout ε (abelSumProbe d) forcingJ i o -
    (∑ k, A i k) + ∑ k, A k o else A i i) = _
  rw [if_pos rfl]
  simp only [hoff]

theorem abelRelativeRecovery_exact (o : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (ε : Ioi (0 : ℝ)) :
    abelRelativeRecovery o ε (hamiltonianAbelInverse H ε (abelDiagonalProbe d))
      (hamiltonianAbelInverse H ε (abelSumProbe d)) = H - (H o o) • 1 := by
  let A := abelOffDiagonalFromReadout (H * abelDiagonalProbe d - abelDiagonalProbe d * H)
  have hA : A = H - Matrix.diagonal (fun i => H i i) := abelOffDiagonalFromReadout_eq H
  have hrow (i : Fin d) : (∑ k, A i k) = (∑ k, H i k) - H i i := by
    rw [hA]
    simp only [Matrix.sub_apply, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single i]
    · exact Matrix.diagonal_apply_eq _ _
    · intro k _ hk
      exact Matrix.diagonal_apply_ne _ (Ne.symm hk)
    · exact fun h => (h (Finset.mem_univ i)).elim
  have hcol : (∑ k, A k o) = (∑ k, H k o) - H o o := by
    rw [hA]
    simp only [Matrix.sub_apply, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single o]
    · exact Matrix.diagonal_apply_eq _ _
    · intro k _ hk
      exact Matrix.diagonal_apply_ne _ hk
    · exact fun h => (h (Finset.mem_univ o)).elim
  unfold abelRelativeRecovery
  rw [abelCommutatorReadout_inverse, abelCommutatorReadout_inverse]
  ext i j
  change (if i = j then (H * abelSumProbe d - abelSumProbe d * H) i o -
    (∑ k, A i k) + ∑ k, A k o else A i j) =
      H i j - (H o o) * (1 : Matrix (Fin d) (Fin d) ℂ) i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Matrix.one_apply_eq, mul_one, hrow, hcol]
    simp only [abelSumProbe, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, one_mul, mul_one]
    abel
  · rw [if_neg hij, Matrix.one_apply_ne hij, mul_zero, sub_zero, hA, Matrix.sub_apply,
      Matrix.diagonal_apply_ne _ hij, sub_zero]

/-- Center the reconstruction by its normalized trace. -/
def abelTracelessRecovery (o : Fin d) (ε : Ioi (0 : ℝ))
    (forcingD forcingJ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  let B := abelRelativeRecovery o ε forcingD forcingJ
  B - (B.trace / (d : ℂ)) • 1

theorem abelTracelessRecovery_exact (o : Fin d) (H : Matrix (Fin d) (Fin d) ℂ)
    (ε : Ioi (0 : ℝ)) :
    abelTracelessRecovery o ε (hamiltonianAbelInverse H ε (abelDiagonalProbe d))
      (hamiltonianAbelInverse H ε (abelSumProbe d)) = H - (H.trace / (d : ℂ)) • 1 := by
  have hd : d ≠ 0 := by
    intro h
    subst d
    exact Fin.elim0 o
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  unfold abelTracelessRecovery
  rw [abelRelativeRecovery_exact]
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  rw [sub_div, mul_div_cancel_right₀ _ hdC, sub_smul]
  abel

private theorem commutator_eq_of_scalarDifference {H K : Matrix (Fin d) (Fin d) ℂ}
    {c : ℂ} (hc : H - K = c • 1) (Y : Matrix (Fin d) (Fin d) ℂ) :
    H * Y - Y * H = K * Y - Y * K := by
  have he : H = K + c • 1 := by
    calc
      H = K + (H - K) := by abel
      _ = _ := by rw [hc]
  rw [he, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  abel

/-- The two prescribed inverse probes distinguish Hamiltonians exactly
up to their scalar part. -/
theorem abelProbeReadings_eq_iff_scalarDifference (o : Fin d) (H K : Matrix (Fin d) (Fin d) ℂ)
    (ε : Ioi (0 : ℝ)) :
    (hamiltonianAbelInverse H ε (abelDiagonalProbe d) =
        hamiltonianAbelInverse K ε (abelDiagonalProbe d) ∧
      hamiltonianAbelInverse H ε (abelSumProbe d) = hamiltonianAbelInverse K ε (abelSumProbe d)) ↔
      ∃ c : ℂ, H - K = c • 1 := by
  constructor
  · rintro ⟨hD, hJ⟩
    have he : H - (H o o) • 1 = K - (K o o) • 1 := by
      rw [← abelRelativeRecovery_exact o H ε, ← abelRelativeRecovery_exact o K ε, hD, hJ]
    refine ⟨H o o - K o o, ?_⟩
    rw [sub_smul]
    calc
      _ = (H - (H o o) • 1) - (K - (K o o) • 1) + ((H o o) • 1 - (K o o) • 1) := by abel
      _ = _ := by rw [he, sub_self, zero_add]
  · rintro ⟨c, hc⟩
    exact ⟨(hamiltonianAbelInverse_eq_iff_commutators H K ε _).mpr (commutator_eq_of_scalarDifference hc _),
      (hamiltonianAbelInverse_eq_iff_commutators H K ε _).mpr (commutator_eq_of_scalarDifference hc _)⟩

/-- Equality of forward filters has the same scalar ambiguity as equality
of the two selected inverse readings. -/
theorem hamiltonianDampedGapResponse_zero_eq_iff_scalarDifference (o : Fin d)
    {H K : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (hK : K.IsHermitian) (ε : Ioi (0 : ℝ)) :
    hamiltonianDampedGapResponse hH 0 ε = hamiltonianDampedGapResponse hK 0 ε ↔
      ∃ c : ℂ, H - K = c • 1 := by
  rw [← hamiltonianAbelInverse_eq_iff_response_eq hH hK]
  constructor
  · intro he
    exact (abelProbeReadings_eq_iff_scalarDifference o H K ε).mp
      ⟨congrFun he (abelDiagonalProbe d), congrFun he (abelSumProbe d)⟩
  · rintro ⟨c, hc⟩
    funext Y
    exact (hamiltonianAbelInverse_eq_iff_commutators H K ε Y).mpr (commutator_eq_of_scalarDifference hc Y)

#print axioms abelRelativeRecovery_exact
#print axioms abelTracelessRecovery_exact
#print axioms abelProbeReadings_eq_iff_scalarDifference
#print axioms hamiltonianDampedGapResponse_zero_eq_iff_scalarDifference

end

end GaloisForLFunctions.HTGeometry
