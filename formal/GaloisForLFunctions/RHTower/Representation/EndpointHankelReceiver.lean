import GaloisForLFunctions.RHTower.Representation.EndpointArithmeticMoments
import GaloisForLFunctions.RHTower.XiResolventHankelMatrixLadder
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CycleCharacterIdentification

/-!
# The endpoint cycle-moment receiver

The normalized endpoint moments form a positive diagonal congruence of the resolvent Hankel
matrix at shift `1/4`. Their positivity is therefore exactly RH. Replicating the normalized
matrix does not weaken this condition: its unit-diagonal completion is positive at every
replication number exactly under RH.
-/

noncomputable section
open scoped BigOperators

namespace RHTower
open GaloisForLFunctions.SymmetricCharacters

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

/-- Positive probability frequencies have every nonempty power sum at most one. -/
theorem xiEndpointSourceCycle_le_one_of_rh (hRH : RiemannHypothesis) (n : ℕ) :
    xiEndpointSourceCycle n ≤ 1 := by
  have hle (q : XiZeroCopy) : (xiEndpointColor q : ℝ) ^ (n + 1) ≤ xiEndpointColor q := by
    have h0 := (xiEndpointColor q).coe_nonneg
    have h1 := summable_xiEndpointColor.le_tsum q (fun j _ => (xiEndpointColor j).coe_nonneg)
    rw [tsum_xiEndpointColor] at h1
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ h0 h1) h0
  have hs : Summable (fun q => (xiEndpointColor q : ℝ) ^ (n + 1)) :=
    Summable.of_nonneg_of_le (fun q => pow_nonneg (xiEndpointColor q).coe_nonneg _) hle
      summable_xiEndpointColor
  have hsum := Summable.tsum_le_tsum hle hs summable_xiEndpointColor
  rw [tsum_xiEndpointColor] at hsum
  rw [← xiEndpointCharacter_all_cycles_eq_source_iff_rh.mpr hRH n,
    xiEndpointCharacter, wordCharacter_finRotate]
  exact hsum

/-- The common-pivot tests of the prescribed arithmetic cycle function are exactly RH. -/
theorem forall_xiEndpointPivotGram_posSemidef_iff_rh :
    (∀ N n, (pivotGram xiEndpointSourceCycle (fun i : Fin N => i.val) n).PosSemidef) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply forall_xiEndpointHankel_posSemidef_iff_rh.mp
    intro N
    exact ((forall_pivotGram_posSemidef_iff xiEndpointSourceCycle xiEndpointSourceCycle_zero
      (fun i : Fin N => i.val)).mp (h N)).1
  · intro hRH N
    apply (forall_pivotGram_posSemidef_iff xiEndpointSourceCycle xiEndpointSourceCycle_zero
      (fun i : Fin N => i.val)).mpr
    exact ⟨forall_xiEndpointHankel_posSemidef_iff_rh.mpr hRH N,
      fun i => xiEndpointSourceCycle_le_one_of_rh hRH (i.val + i.val)⟩

/-- Positivity of the literal arithmetic cycle class functions forces RH. -/
theorem positive_xiEndpointCycleFamily_implies_rh :
    PositiveCycleFamily xiEndpointSourceCycle → RiemannHypothesis := by
  intro h
  exact forall_xiEndpointHankel_posSemidef_iff_rh.mp
    (fun N => h.hankel xiEndpointSourceCycle_zero N)

/-- The literal source cycle-product function is positive exactly when RH holds. -/
theorem positive_xiEndpointCycleFamily_iff_rh :
    PositiveCycleFamily xiEndpointSourceCycle ↔ RiemannHypothesis := by
  refine ⟨positive_xiEndpointCycleFamily_implies_rh, ?_⟩
  intro hRH
  have he (n : ℕ) : xiEndpointSourceCycle n =
      ∑' q, (xiEndpointColor q : ℝ) ^ (n + 1) := by
    rw [← xiEndpointCharacter_all_cycles_eq_source_iff_rh.mpr hRH n,
      xiEndpointCharacter, wordCharacter_finRotate]
  simpa only [he] using wordCharacter_positiveCycleFamily xiEndpointColor
    summable_xiEndpointColor tsum_xiEndpointColor

/-- The arithmetic response jets prescribe a positive cycle family exactly under RH. -/
theorem positive_xiEndpointArithmeticCycleFamily_iff_rh :
    PositiveCycleFamily xiEndpointArithmeticCycle ↔ RiemannHypothesis := by
  have he : xiEndpointArithmeticCycle = xiEndpointSourceCycle :=
    funext xiEndpointArithmeticCycle_eq_source
  rw [he]
  exact positive_xiEndpointCycleFamily_iff_rh

end RHTower
