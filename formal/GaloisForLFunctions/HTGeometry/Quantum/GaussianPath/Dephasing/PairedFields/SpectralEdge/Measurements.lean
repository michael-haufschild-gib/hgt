import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.CutDeficit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
import Mathlib.Order.Interval.Finset.Fin

/-! # Affine phase measurements in ranked energy states -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open _root_.RiemannGaussian.HermitianRankTrace
open private diagonalEnergy_spectral wave from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
open private phase_lipschitz from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.PhaseStability
open private from_mean from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.EnergySpread
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Fixed rank labelling used by the Hermitian spectral theorem. -/
abbrev eigenIndex (I : Type*) [Fintype I] : Fin (Fintype.card I) ≃ I :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

/-- Indices of energies strictly earlier in the descending eigenvalue list.
Equal eigenvalues may be placed on either side of the cut. -/
def preceding (j : I) : Finset I :=
  (Iio ((eigenIndex I).symm j)).map (eigenIndex I).toEmbedding

/-- The test records one complex diagonal entry of the true evolution in
the base frame and compares it with the phase of the diagonal energy. -/
def phaseError (U : unitaryGroup I ℂ) (B : selfAdjoint (Mat I)) (t : ℝ) (j : I) : ℝ :=
  ‖(U.valᴴ*unitaryEvolution B.val t*U.val) j j-wave t (diagonalEnergy U B.val j)‖

private theorem diag_wave (U : unitaryGroup I ℂ) (B : selfAdjoint (Mat I)) (t : ℝ) (j : I) :
    let h := B.2.isHermitian
    let W := U⁻¹*h.eigenvectorUnitary
    (U.valᴴ*unitaryEvolution B.val t*U.val) j j =
      ∑ i, ((normSqMatrix W.val j i:ℝ):ℂ)*wave t (h.eigenvalues i) := by
  intro h W
  have he : U.valᴴ*unitaryEvolution B.val t*U.val =
      W.val*diagonal (fun i => wave t (h.eigenvalues i))*W.valᴴ := by
    rw [unitaryEvolution_spectral h]
    change _=(U.valᴴ*h.eigenvectorUnitary.val)*_*(U.valᴴ*h.eigenvectorUnitary.val)ᴴ
    rw [conjTranspose_mul,conjTranspose_conjTranspose]
    simp only [mul_assoc,wave,Matrix.star_eq_conjTranspose]
  rw [he,Matrix.mul_apply]
  apply sum_congr rfl
  intro i _
  rw [mul_diagonal,conjTranspose_apply]
  change W.val j i * _ * star (W.val j i)=((‖W.val j i‖^2:ℝ):ℂ)*_
  rw [mul_right_comm,Complex.star_def,Complex.mul_conj']
  push_cast
  ring

omit [DecidableEq I] in
private theorem phase_deviation {p : I → I → ℝ} (hn : ∀ k i, 0≤p k i) (hr : ∀ k, ∑ i, p k i=1)
    (v : I → ℝ) (t : ℝ) (j : I) :
    ‖(∑ i, (p j i:ℂ)*wave t (v i))-wave t (rowMean p v j)‖ ≤
      2*|t| *rowMean p (fun i => |v i-v j|) j := by
  let d := rowMean p v j
  have hw : ∑ i, (p j i:ℂ)*wave t d=wave t d := by
    rw [←sum_mul,←Complex.ofReal_sum,hr,Complex.ofReal_one,one_mul]
  have hg := from_mean hn hr v j (v j)
  have hgap : rowMean p (fun i => |v i-d|) j ≤ 2*rowMean p (fun i => |v i-v j|) j := by
    apply (sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (abs_sub_le (v i) (v j) d) (hn j i)).trans
    simp only [mul_add,sum_add_distrib,←sum_mul,hr,one_mul]
    simp_rw [abs_sub_comm (v j) (v _)] at hg
    change |v j-d| ≤ rowMean p (fun i => |v i-v j|) j at hg
    change rowMean p (fun i => |v i-v j|) j+|v j-d| ≤ 2*rowMean p (fun i => |v i-v j|) j
    linarith only [hg]
  change ‖_-wave t d‖ ≤ _
  conv_lhs => rw [←hw,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ |t| *rowMean p (fun i => |v i-d|) j := by
      simp only [rowMean,mul_sum]
      apply sum_le_sum
      intro i _
      rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn j i)]
      have h := phase_lipschitz t (v i) d
      rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at h
      exact (mul_le_mul_of_nonneg_left h (hn j i)).trans_eq (by ring)
    _ ≤ _ := (mul_le_mul_of_nonneg_left hgap (abs_nonneg _)).trans_eq (by ring)

/-- Each ranked measurement costs the two neighboring Ky Fan deficits,
independently of total dimension. -/
theorem phaseError_le (U : unitaryGroup I ℂ) (B : selfAdjoint (Mat I)) (t : ℝ) (j : I) :
    let e := B.2.isHermitian.eigenvalues
    let p := normSqMatrix (U⁻¹*B.2.isHermitian.eigenvectorUnitary).val
    let S := preceding j
    phaseError U B t j ≤ 2*|t| *(cutDeficit p e S+cutDeficit p e (insert j S)) := by
  intro e p S
  let r := (eigenIndex I).symm
  have hS (i : I) : i∈S ↔ r i < r j := mem_map_equiv.trans mem_Iio
  obtain ⟨hn,hr,hc⟩ := mem_doublyStochastic_iff_sum.mp
    (normSqMatrix_mem_doublyStochastic_of_unitary (U⁻¹*B.2.isHermitian.eigenvectorUnitary).2)
  have hcut := row_gap_le_adjacent_cuts (p:=p) hn hr hc e S j (fun hj => lt_irrefl _ ((hS j).mp hj))
    (fun i hi => B.2.isHermitian.eigenvalues₀_antitone ((hS i).mp hi).le)
    (fun i hi => B.2.isHermitian.eigenvalues₀_antitone (le_of_not_gt (fun h => hi ((hS i).mpr h))))
  rw [phaseError,diag_wave,diagonalEnergy_spectral U B.2.isHermitian]
  exact (phase_deviation (p:=p) hn hr e t j).trans (mul_le_mul_of_nonneg_left hcut (by positivity))

#print axioms phaseError_le
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
