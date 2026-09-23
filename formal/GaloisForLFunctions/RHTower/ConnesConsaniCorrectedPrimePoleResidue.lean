import GaloisForLFunctions.RHTower.ConnesConsaniLemma33NormalizationCorrection
import GaloisForLFunctions.RHTower.GaussOnePrimeActualCriticalResidue
import GaloisForLFunctions.RHTower.GaussOnePrimeCriticalResidue
import GaloisForLFunctions.RHTower.GaussDiagonalWeakSchatten
import GaloisForLFunctions.RHTower.SchattenLogResidueScalar

/-!
# Corrected Connes--Consani distinguished prime-pole residue

The exact Fourier integral in `ConnesConsaniLemma33NormalizationCorrection` shows that the source
feature Gram matrix is `(p-1)` times the Gram matrix printed in Lemma 3.3.  Thus the isometry from
the normalized source features to the paper's Hardy features satisfies

`V = (p-1)⁻¹ᐟ² U B`,

not `V = U B`.  Substitution into the literal distinguished block removes one factor `p-1` from
the reduced operator.  Its energy is therefore `(p-1)⁻²` times the raw channel energy, and its
measurable logarithmic residue is

`2 (p-1)² / (p² log p)`.

This file formalizes the strongest corrected positive survivor: exact operator energy, weak trace
ideal membership, measurable residue, positivity, and exclusion from trace class.  No premise is
added to repair the false printed normalization.
-/

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

/-- Energy renormalization forced by the missing `p-1` in Connes--Consani Lemma 3.3. -/
def connesConsaniCorrectedPrimeEnergyScale (p : Nat.Primes) : ℝ :=
  ((p : ℝ) - 1)⁻¹ ^ (2 : ℕ)

/-- Correctly normalized reduced distinguished prime-pole block. -/
def connesConsaniCorrectedReducedPrimePoleDefect (p : Nat.Primes) :
    GaussCircleL2 →L[ℂ] GaussCircleL2 :=
  (((((p : ℝ) - 1)⁻¹ : ℝ) : ℂ)) • gaussOnePrimeReducedDefect p

/-- The corrected distinguished block is self-adjoint. -/
theorem connesConsaniCorrectedReducedPrimePoleDefect_inner
    (p : Nat.Primes) (u v : GaussCircleL2) :
    inner ℂ (connesConsaniCorrectedReducedPrimePoleDefect p u) v =
      inner ℂ u (connesConsaniCorrectedReducedPrimePoleDefect p v) := by
  rw [connesConsaniCorrectedReducedPrimePoleDefect, smul_apply, smul_apply,
    inner_smul_left, inner_smul_right, gaussOnePrimeReducedDefect_inner]
  simp

/-- Hilbert adjoint of the corrected distinguished block. -/
theorem adjoint_connesConsaniCorrectedReducedPrimePoleDefect (p : Nat.Primes) :
    ContinuousLinearMap.adjoint (connesConsaniCorrectedReducedPrimePoleDefect p) =
      connesConsaniCorrectedReducedPrimePoleDefect p := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact connesConsaniCorrectedReducedPrimePoleDefect_inner p u v

/-- Exact corrected energy: the printed energy is too large by `(p-1)^(2 : ℕ)`. -/
theorem connesConsaniCorrectedReducedPrimePoleDefect_modulusSq (p : Nat.Primes) :
    ContinuousLinearMap.adjoint (connesConsaniCorrectedReducedPrimePoleDefect p) ∘L
        connesConsaniCorrectedReducedPrimePoleDefect p =
      (connesConsaniCorrectedPrimeEnergyScale p : ℂ) •
        gaussChannelOperator (le_refl 1) (0 : Fin 1) p := by
  rw [adjoint_connesConsaniCorrectedReducedPrimePoleDefect,
    connesConsaniCorrectedReducedPrimePoleDefect]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, smul_apply,
    map_smul, smul_smul]
  rw [show gaussOnePrimeReducedDefect p (gaussOnePrimeReducedDefect p u) =
      gaussChannelOperator (le_refl 1) (0 : Fin 1) p u by
    have h := congrArg (fun T : GaussCircleL2 →L[ℂ] GaussCircleL2 => T u)
      (gaussOnePrimeReducedDefect_modulusSq p)
    simpa only [adjoint_gaussOnePrimeReducedDefect,
      ContinuousLinearMap.coe_comp, Function.comp_apply] using h]
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    linarith
  rw [connesConsaniCorrectedPrimeEnergyScale]
  push_cast
  field_simp

/-- Corrected measurable residue of the distinguished prime-pole energy. -/
def connesConsaniCorrectedPrimePoleResidue (p : Nat.Primes) : ℝ :=
  2 * ((p : ℝ) - 1) ^ (2 : ℕ) / ((p : ℝ) ^ (2 : ℕ) * Real.log (p : ℝ))

/-- The corrected residue is the corrected energy scale times the old raw-channel residue. -/
theorem connesConsaniCorrectedPrimeEnergyScale_mul_gaussChannelResidue (p : Nat.Primes) :
    connesConsaniCorrectedPrimeEnergyScale p * gaussChannelResidue 1 p =
      connesConsaniCorrectedPrimePoleResidue p := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    linarith
  rw [gaussChannelResidue_one]
  simp only [connesConsaniCorrectedPrimeEnergyScale,
    connesConsaniCorrectedPrimePoleResidue]
  field_simp

/-- The corrected residue is strictly positive at every rational prime. -/
theorem connesConsaniCorrectedPrimePoleResidue_pos (p : Nat.Primes) :
    0 < connesConsaniCorrectedPrimePoleResidue p := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  rw [connesConsaniCorrectedPrimePoleResidue]
  exact div_pos (mul_pos (by positivity) (sq_pos_of_pos (sub_pos.mpr hp)))
    (mul_pos (sq_pos_of_pos (lt_trans zero_lt_one hp)) hlog)

/-- The corrected distinguished energy is weak trace class. -/
theorem memWeakSchattenClass_connesConsaniCorrectedReducedPrimePoleDefect_modulusSq
    (p : Nat.Primes) :
    MemWeakSchattenClass 1
      (ContinuousLinearMap.adjoint (connesConsaniCorrectedReducedPrimePoleDefect p) ∘L
        connesConsaniCorrectedReducedPrimePoleDefect p) := by
  rw [connesConsaniCorrectedReducedPrimePoleDefect_modulusSq]
  have hweak : MemWeakSchattenClass 1
      (gaussChannelOperator (le_refl 1) (0 : Fin 1) p) := by
    have hraw : MemWeakSchattenClass 1
        (gaussQuasiInnerGFull (le_refl 1) (0 : Fin 1) p) := by
      simpa using memWeakSchattenClass_gaussQuasiInnerGFull
        (m := 1) (le_refl 1) (0 : Fin 1) p
    rw [gaussChannelOperator]
    exact hraw.smul_one _
  exact hweak.smul_one _

/-- The corrected distinguished energy has the exact corrected logarithmic residue. -/
theorem hasSchattenLogResidue_connesConsaniCorrectedReducedPrimePoleDefect_modulusSq
    (p : Nat.Primes) :
    HasSchattenLogResidue 1
      (ContinuousLinearMap.adjoint (connesConsaniCorrectedReducedPrimePoleDefect p) ∘L
        connesConsaniCorrectedReducedPrimePoleDefect p)
      (connesConsaniCorrectedPrimePoleResidue p) := by
  rw [connesConsaniCorrectedReducedPrimePoleDefect_modulusSq]
  have h := (hasSchattenLogResidue_gaussChannelOperator_one (0 : Fin 1) p).smul_one
    ((connesConsaniCorrectedPrimeEnergyScale p : ℝ) : ℂ)
  have hscale : 0 ≤ connesConsaniCorrectedPrimeEnergyScale p := by
    rw [connesConsaniCorrectedPrimeEnergyScale]
    positivity
  simpa [Complex.norm_real, abs_of_nonneg hscale,
    connesConsaniCorrectedPrimeEnergyScale_mul_gaussChannelResidue] using h

/-- Positive corrected residue excludes trace class. -/
theorem connesConsaniCorrectedReducedPrimePoleDefect_modulusSq_not_memSchattenClass
    (p : Nat.Primes) :
    ¬ MemSchattenClass 1
      (ContinuousLinearMap.adjoint (connesConsaniCorrectedReducedPrimePoleDefect p) ∘L
        connesConsaniCorrectedReducedPrimePoleDefect p) := by
  exact
    (hasSchattenLogResidue_connesConsaniCorrectedReducedPrimePoleDefect_modulusSq p).not_memSchattenClass
      (connesConsaniCorrectedPrimePoleResidue_pos p)

end

end RHTower
