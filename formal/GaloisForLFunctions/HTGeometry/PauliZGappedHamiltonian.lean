import GaloisForLFunctions.HTGeometry.PauliZSetLabels
import GaloisForLFunctions.HTGeometry.PauliCountOrderBounds
import GaloisForLFunctions.HTGeometry.EuclideanDiagonalGappedForm

/-!
# The diagonal centre of a fixed-locality Pauli ensemble is gapped

Summing the `Z` strings of every nonempty support of size at most the locality budget gives a
diagonal Hamiltonian whose top computational configuration is the all-zero one.  Every other
configuration has some occupied site, and the singleton `Z` string there flips sign while no term
can exceed one, so the diagonal value drops by at least two.

After the ensemble normalisation the spectral gap above every other configuration is therefore
`2 m^{-1/2}`, which is the gap hypothesis of a gapped-eigenline stability statement.
-/

open scoped BigOperators
open HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n q : ℕ}

/-- The supports of the diagonal centre: nonempty, of size at most the locality budget. -/
def zSupports (n q : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S => S.Nonempty ∧ S.card ≤ q

theorem mem_zSupports {S : Finset (Fin n)} :
    S ∈ zSupports n q ↔ S.Nonempty ∧ S.card ≤ q := by
  simp [zSupports]

/-- The ensemble normalisation `m^{-1/2}`. -/
def pauliNormalization (n q : ℕ) : ℝ :=
  (Real.sqrt (Quantum.nonidentityPauliWeightCount n q : ℝ))⁻¹

theorem pauliNormalization_nonneg (n q : ℕ) : 0 ≤ pauliNormalization n q := by
  rw [pauliNormalization]
  positivity

theorem pauliNormalization_pos (hn : 1 ≤ n) (hq : 1 ≤ q) : 0 < pauliNormalization n q := by
  rw [pauliNormalization, inv_pos, Real.sqrt_pos]
  exact_mod_cast Quantum.one_le_nonidentityPauliWeightCount hn hq

/-- The diagonal symbol of the centre Hamiltonian. -/
def zProfile (n q : ℕ) (x : Fin n → Bool) : ℝ :=
  pauliNormalization n q * ∑ S ∈ zSupports n q, zSetSign S x

/-- **The centre Hamiltonian is the normalised sum of the diagonal `Z` strings.** -/
theorem diagCLM_zProfile_eq (n q : ℕ) :
    diagCLM (zProfile n q)
      = Matrix.toEuclideanCLM (𝕜 := ℂ)
          (((pauliNormalization n q : ℝ) : ℂ) •
            ∑ S ∈ zSupports n q, finitePauliMatrix (pauliZSetLabel S)) := by
  rw [diagCLM]
  congr 1
  ext x y
  rw [Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply]
  simp_rw [finitePauliMatrix_pauliZSetLabel]
  by_cases hxy : x = y
  · subst hxy
    simp [zProfile, Complex.ofReal_sum]
  · rw [if_neg hxy]
    simp [hxy]

/-- The top configuration has diagonal value the number of centre terms, normalised. -/
theorem zProfile_bot (n q : ℕ) :
    zProfile n q (fun _ => false) = pauliNormalization n q * (zSupports n q).card := by
  rw [zProfile]
  congr 1
  rw [Finset.sum_congr rfl fun S _ => zSetSign_eq_one_of_forall_false (fun _ => rfl) S]
  simp

/-- **Every other configuration lies two normalised units below the top.** -/
theorem zProfile_le_of_ne (hq : 1 ≤ q) {x : Fin n → Bool} (hx : x ≠ fun _ => false) :
    zProfile n q x ≤ zProfile n q (fun _ => false) - 2 * pauliNormalization n q := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ false := by
    by_contra hcon
    exact hx (funext fun s => by simpa using not_not.mp (fun h => hcon ⟨s, h⟩))
  have hxi : x i = true := by
    cases hxv : x i
    · exact absurd hxv hi
    · rfl
  have hmem : ({i} : Finset (Fin n)) ∈ zSupports n q := by
    rw [mem_zSupports, Finset.card_singleton]
    exact ⟨Finset.singleton_nonempty i, hq⟩
  have hcard : 1 ≤ (zSupports n q).card := Finset.card_pos.mpr ⟨_, hmem⟩
  have herase : (((zSupports n q).erase {i}).card : ℝ) = ((zSupports n q).card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hmem]
    have : (1 : ℕ) ≤ (zSupports n q).card := hcard
    push_cast [Nat.cast_sub this]
    ring
  have htail : ∑ S ∈ (zSupports n q).erase {i}, zSetSign S x
      ≤ ((zSupports n q).card : ℝ) - 1 := by
    calc ∑ S ∈ (zSupports n q).erase {i}, zSetSign S x
        ≤ ∑ _S ∈ (zSupports n q).erase {i}, (1 : ℝ) :=
          Finset.sum_le_sum fun S _ => zSetSign_le_one S x
      _ = (((zSupports n q).erase {i}).card : ℝ) := by simp
      _ = ((zSupports n q).card : ℝ) - 1 := herase
  have hsingle : zSetSign ({i} : Finset (Fin n)) x = -1 := by
    rw [zSetSign_singleton, if_pos hxi]
  have hsum : ∑ S ∈ zSupports n q, zSetSign S x ≤ ((zSupports n q).card : ℝ) - 2 := by
    rw [← Finset.add_sum_erase _ _ hmem, hsingle]
    linarith [htail]
  rw [zProfile, zProfile_bot]
  have := mul_le_mul_of_nonneg_left hsum (pauliNormalization_nonneg n q)
  linarith [this]

/-- The top configuration is an eigenvector of the centre Hamiltonian. -/
theorem diagCLM_zProfile_single (n q : ℕ) :
    diagCLM (zProfile n q) (EuclideanSpace.single (fun _ => false) (1 : ℂ))
      = ((zProfile n q (fun _ => false) : ℝ) : ℂ) •
        EuclideanSpace.single (fun _ => false) (1 : ℂ) :=
  diagCLM_single _ _

set_option maxHeartbeats 1000000 in
/-- **The gap hypothesis at the centre Hamiltonian**, with gap `2 m^{-1/2}`. -/
theorem reApplyInnerSelf_zProfile_le (hq : 1 ≤ q) (x : EuclideanSpace ℂ (Fin n → Bool)) :
    (diagCLM (zProfile n q)).reApplyInnerSelf x
      ≤ zProfile n q (fun _ => false) * ‖x‖ ^ (2 : ℕ)
        - (2 * pauliNormalization n q) *
          (‖x‖ ^ (2 : ℕ) -
            ‖(inner ℂ (EuclideanSpace.single (fun _ => false) (1 : ℂ)) x : ℂ)‖ ^ (2 : ℕ)) := by
  refine reApplyInnerSelf_diagCLM_le (ι := Fin n → Bool) (zProfile n q) (fun _ => false)
    (2 * pauliNormalization n q) (fun i hi => ?_) x
  exact zProfile_le_of_ne hq hi

end

end GaloisForLFunctions.HTGeometry
