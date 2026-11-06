import GaloisForLFunctions.RHTower.Representation.PositiveEndpointCharacter
import GaloisForLFunctions.RHTower.XiResolventHankelMatrixLadder
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.ReplicatedKernel

/-!+# The endpoint cycle-moment receiver

The normalized endpoint moments form a positive diagonal congruence of the resolvent Hankel
matrix at shift `1/4`. Their positivity is therefore exactly RH. Replicating the normalized
matrix does not weaken this condition: its unit-diagonal completion is positive at every
replication number exactly under RH.
-/

noncomputable section
open scoped BigOperators

namespace RHTower
open GaloisForLFunctions.SymmetricCharacters

theorem xiResolventPoint_endpoint (q : XiZeroCopy) :
    xiResolventPoint (1 / 4) q = xiStripEdgeWeight q := by
  rw [xiResolventPoint, xiStripEdgeWeight_eq_spectral, add_comm]
  norm_cast

theorem xiEndpointSourceCycle_eq_resolvent (n : ℕ) :
    xiEndpointSourceCycle n =
      (xiResolventMoment n (1 / 4)).re / xiEndpointColorMass ^ (n + 1) := by
  simp only [xiEndpointSourceCycle, xiResolventMoment, xiResolventPoint_endpoint]

/-- Hankel matrix of normalized nonempty cycle values. -/
def xiEndpointHankel (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => xiEndpointSourceCycle (i.val + j.val)

private theorem posSemidef_diagonalScale {I : Type*} [Fintype I]
    {H : Matrix I I ℝ} (hH : H.PosSemidef) (d : I → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    Matrix.PosSemidef (fun i j => a * (d i * H i j * d j)) := by
  classical
  convert (hH.mul_mul_conjTranspose_same (Matrix.diagonal d)).smul ha using 1
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_conjTranspose,
    star_trivial, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- Normalization changes the positive cone by an invertible positive diagonal congruence. -/
theorem xiEndpointHankel_posSemidef_iff (N : ℕ) :
    (xiEndpointHankel N).PosSemidef ↔ (xiResolventHankelMatrix N (1 / 4)).PosSemidef := by
  have hM := xiEndpointColorMass_pos
  constructor
  · intro h
    convert posSemidef_diagonalScale h (fun i => xiEndpointColorMass ^ i.val) hM.le using 1
    ext i j
    change (xiResolventMoment (i.val + j.val) (1 / 4)).re =
      xiEndpointColorMass * (xiEndpointColorMass ^ i.val *
        xiEndpointSourceCycle (i.val + j.val) * xiEndpointColorMass ^ j.val)
    rw [xiEndpointSourceCycle_eq_resolvent, pow_add, pow_add, pow_one]
    field_simp [hM.ne']
  · intro h
    convert posSemidef_diagonalScale h (fun i => 1 / xiEndpointColorMass ^ i.val)
      (one_div_nonneg.mpr hM.le) using 1
    ext i j
    change xiEndpointSourceCycle (i.val + j.val) =
      (1 / xiEndpointColorMass) * ((1 / xiEndpointColorMass ^ i.val) *
        (xiResolventMoment (i.val + j.val) (1 / 4)).re *
        (1 / xiEndpointColorMass ^ j.val))
    rw [xiEndpointSourceCycle_eq_resolvent, pow_add, pow_add, pow_one]
    field_simp [hM.ne']

/-- The full endpoint Hankel positivity condition is precisely RH. -/
theorem forall_xiEndpointHankel_posSemidef_iff_rh :
    (∀ N, (xiEndpointHankel N).PosSemidef) ↔ RiemannHypothesis := by
  simp_rw [xiEndpointHankel_posSemidef_iff]
  exact (riemannHypothesis_iff_forall_xiResolventHankelMatrix_posSemidef
    (by positivity : (0 : ℝ) ≤ 1 / 4)).symm

end RHTower
