import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CountableColoring
import GaloisForLFunctions.RHTower.Representation.EndpointCharacterDefect

/-!
# A coherent positive Xi character and its exact arithmetic discrepancy

Normalize the positive real parts of the reciprocal endpoint weights to obtain a probability
alphabet. Independent coloring gives a normalized positive-definite class function at every
finite rank, compatible with restriction and disjoint support. Its transposition agrees with
the completed arithmetic endpoint jet exactly when RH holds.
-/

noncomputable section
open scoped ComplexOrder

namespace RHTower

open GaloisForLFunctions.SymmetricCharacters

/-- The unconditional probability alphabet obtained by real projection of the Xi divisor. -/
def xiEndpointColor (q : XiZeroCopy) : NNReal :=
  ⟨(xiStripEdgeWeight q).re / xiEndpointColorMass,
    div_nonneg (xiStripEdgeWeight_re_pos q).le xiEndpointColorMass_pos.le⟩

theorem summable_xiEndpointColor : Summable (fun q => (xiEndpointColor q : ℝ)) :=
  (Complex.reCLM.summable summable_xiStripEdgeWeight).div_const xiEndpointColorMass

theorem tsum_xiEndpointColor : (∑' q, (xiEndpointColor q : ℝ)) = 1 := by
  change (∑' q, (xiStripEdgeWeight q).re / xiEndpointColorMass) = 1
  rw [tsum_div_const]
  exact div_self xiEndpointColorMass_pos.ne'

variable {X Y J : Type*} [Fintype X] [Fintype Y]

/-- A positive coherent character family built from the real endpoint alphabet. -/
def xiEndpointCharacter (σ : Equiv.Perm X) : ℝ := wordCharacter xiEndpointColor σ

theorem xiEndpointCharacter_one : xiEndpointCharacter (1 : Equiv.Perm X) = 1 := by
  rw [xiEndpointCharacter, wordCharacter_one xiEndpointColor summable_xiEndpointColor,
    tsum_xiEndpointColor, one_pow]

theorem xiEndpointCharacter_restrict (σ : Equiv.Perm X) :
    xiEndpointCharacter (Equiv.optionCongr σ) = xiEndpointCharacter σ := by
  rw [xiEndpointCharacter, wordCharacter_optionCongr xiEndpointColor summable_xiEndpointColor,
    tsum_xiEndpointColor, one_mul]
  rfl

theorem xiEndpointCharacter_conj (σ τ : Equiv.Perm X) :
    xiEndpointCharacter (τ * σ * τ⁻¹) = xiEndpointCharacter σ :=
  wordCharacter_conj xiEndpointColor σ τ

theorem xiEndpointCharacter_sumCongr (σ : Equiv.Perm X) (τ : Equiv.Perm Y) :
    xiEndpointCharacter (Equiv.sumCongr σ τ) = xiEndpointCharacter σ * xiEndpointCharacter τ :=
  wordCharacter_sumCongr xiEndpointColor summable_xiEndpointColor σ τ

theorem xiEndpointCharacter_posSemidef [Fintype J] (g : J → Equiv.Perm X) :
    Matrix.PosSemidef (fun i j => (xiEndpointCharacter ((g i)⁻¹ * g j) : ℂ)) :=
  wordCharacter_posSemidef xiEndpointColor summable_xiEndpointColor g

/-- Exact values on arbitrary finite lists of cyclic blocks. -/
theorem xiEndpointCharacter_cycles (ns : List ℕ) :
    xiEndpointCharacter (cyclePermutation ns) =
      (ns.map fun n => ∑' q, ((xiStripEdgeWeight q).re / xiEndpointColorMass) ^ (n + 1)).prod :=
  wordCharacter_cyclePermutation xiEndpointColor summable_xiEndpointColor ns

/-- Its first nontrivial cycle value is the positive second moment divided by total mass squared. -/
theorem xiEndpointCharacter_transposition :
    xiEndpointCharacter (finRotate 2) = xiEndpointPositiveTransposition := by
  change wordCharacter xiEndpointColor (finRotate (1 + 1)) = _
  rw [wordCharacter_finRotate]
  change (∑' q, ((xiStripEdgeWeight q).re / xiEndpointColorMass) ^ 2) = _
  simp only [div_pow, tsum_div_const]
  rfl

/-- The positive character's precise discrepancy from the prescribed arithmetic transposition. -/
theorem xiEndpointCharacter_transposition_gap :
    xiEndpointCharacter (finRotate 2) - xiEndpointSourceTransposition =
      xiEndpointOrientationEnergy / xiEndpointColorMass ^ 2 := by
  rw [xiEndpointCharacter_transposition, xiEndpointTransposition_gap]

/-- Positivity and coherence are unconditional; the required arithmetic value identity is RH. -/
theorem xiEndpointCharacter_transposition_eq_source_iff_rh :
    xiEndpointCharacter (finRotate 2) = xiEndpointSourceTransposition ↔ RiemannHypothesis := by
  rw [xiEndpointCharacter_transposition, xiEndpointTransposition_eq_source_iff_rh]

/-- The endpoint power sum prescribed for a nonempty cycle. -/
def xiEndpointSourceCycle (n : ℕ) : ℝ :=
  (∑' q, xiStripEdgeWeight q ^ (n + 1)).re / xiEndpointColorMass ^ (n + 1)

theorem xiEndpointSourceCycle_zero : xiEndpointSourceCycle 0 = 1 := by
  simp only [xiEndpointSourceCycle, zero_add, pow_one]
  rw [Complex.re_tsum summable_xiStripEdgeWeight]
  exact div_self xiEndpointColorMass_pos.ne'

theorem xiEndpointSourceCycle_one : xiEndpointSourceCycle 1 = xiEndpointSourceTransposition := by
  unfold xiEndpointSourceCycle
  rw [hasSum_xiStripEdgeWeight_sq.tsum_eq]
  rfl

/-- Exactness on all cycles has precisely the same obstruction as exactness on a transposition. -/
theorem xiEndpointCharacter_all_cycles_eq_source_iff_rh :
    (∀ n, xiEndpointCharacter (finRotate (n + 1)) = xiEndpointSourceCycle n) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply xiEndpointCharacter_transposition_eq_source_iff_rh.mp
    simpa only [xiEndpointSourceCycle_one] using h 1
  · intro hRH n
    have hreal (q : XiZeroCopy) :
        xiStripEdgeWeight q = ((xiStripEdgeWeight q).re : ℂ) := by
      apply Complex.ext
      · rfl
      · exact (xiStripEdgeWeight_im_eq_zero_iff q).mpr
          (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q)
    rw [xiEndpointCharacter, wordCharacter_finRotate, xiEndpointSourceCycle]
    have hp (q : XiZeroCopy) : xiStripEdgeWeight q ^ (n + 1) =
        (((xiStripEdgeWeight q).re ^ (n + 1) : ℝ) : ℂ) := by
      conv_lhs => rw [hreal q]
      exact (Complex.ofReal_pow _ _).symm
    rw [tsum_congr hp, ← Complex.ofReal_tsum, Complex.ofReal_re]
    change (∑' q, ((xiStripEdgeWeight q).re / xiEndpointColorMass) ^ (n + 1)) = _
    simp only [div_pow, tsum_div_const]

end RHTower
