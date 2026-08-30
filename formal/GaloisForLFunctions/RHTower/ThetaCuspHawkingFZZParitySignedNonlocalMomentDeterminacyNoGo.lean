import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZParityPositiveNonlocalFEReflectionCollapse
import GaloisForLFunctions.HTGeometry.LocalExponentialTestClosure

/-!
# Analytically tempered signed nonlocal FZZ reflection is still singular

The positive-kernel classification leaves a sharp loophole: a signed nonlocal kernel can hide
finite collections of reflected Mellin rows through cancellation.  This module closes the whole
finite-measure class once the reflection implements every integer grade and its Jordan parts have
one common bilateral exponential window.

For positive delay `t`, write the signed Fermi-weighted output as `ν₊ - ν₋`, put `a=t⁻¹`, and put
`c=a F(t)`.  All-grade reflection says that `ν₊` and `ν₋ + c δ_a` have identical moments.
Local-exponential moment determinacy therefore gives the exact measure identity

`ν₊ = ν₋ + c δ_a`.

Undressing by reciprocal Fermi density `exp(x)+1` then fixes the net kernel mass as

`a (exp(a)+1)/(exp(t)+1)`,

the same singular local reflection weight found in the positive classification.  Total variation
dominates this net mass, so no polynomially tempered signed finite-measure implementation exists.

Thus signed cancellation does not rescue an analytically tempered nonlocal FZZ-P producer.  A
survivor must be genuinely distributional, lack every local exponential moment window, or retain
the forced essential singularity.

Moment determinacy is classical and imported from the corpus.  Candidate novelty is its exact
assembly with the Fermi source, Jordan cancellation, reciprocal undressing, and the FZZ-P route
consequence.

`[FZZ-P ROUTE KILL] [SIGNED NONLOCAL] [MOMENT DETERMINACY] [CANDIDATE NEW KNOWLEDGE]`
-/

open Filter Topology Asymptotics MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Reciprocal Fermi density used to recover an undressed kernel mass. -/
def fzzCigarParityUndressingDensity (x : ℝ) : ℝ := Real.exp x + 1

/-- Fermi-weighted reflected target: mass `t⁻¹ F(t)` at reciprocal delay. -/
def fzzCigarParitySignedTargetMeasure (t : FZZCigarPositiveDelay) : Measure ℝ :=
  ENNReal.ofReal ((t : ℝ)⁻¹ * fzzCigarPositiveDelayDensity t) •
    Measure.dirac ((t : ℝ)⁻¹)

private theorem fzzCigarPositiveDelayDensity_pos_signed
    (t : FZZCigarPositiveDelay) : 0 < fzzCigarPositiveDelayDensity t := by
  rw [fzzCigarPositiveDelayDensity, fzzCigarParityDelay_eq_fermi t.property]
  positivity

/-- Jordan data for an all-grade signed nonlocal reflection of the literal FZZ source.  The
exponential-window field is analytic tempering; reciprocal-Fermi integrability makes undressed
total variation finite. -/
structure FZZCigarParitySignedNonlocalFEReflectionData where
  positivePart : FZZCigarPositiveDelay → Measure ℝ
  negativePart : FZZCigarPositiveDelay → Measure ℝ
  positive_finite : ∀ t, IsFiniteMeasure (positivePart t)
  negative_finite : ∀ t, IsFiniteMeasure (negativePart t)
  undressing_positive_integrable : ∀ t,
    Integrable fzzCigarParityUndressingDensity (positivePart t)
  undressing_negative_integrable : ∀ t,
    Integrable fzzCigarParityUndressingDensity (negativePart t)
  common_window : ∀ t, ∃ b : ℝ, 0 < b ∧
    Set.Ioo (-b) b ⊆ integrableExpSet id (positivePart t) ∧
    Set.Ioo (-b) b ⊆ integrableExpSet id
      (negativePart t + fzzCigarParitySignedTargetMeasure t)
  all_grades : ∀ t n,
    ∫ x : ℝ, x ^ n ∂positivePart t =
      ∫ x : ℝ, x ^ n ∂(negativePart t + fzzCigarParitySignedTargetMeasure t)

/-- **All-grade signed collapse.**  One common exponential window turns equality of every
integer Mellin row into equality of the complete Fermi-weighted measures. -/
theorem FZZCigarParitySignedNonlocalFEReflectionData.fermiWeightedMeasure_eq
    (D : FZZCigarParitySignedNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    D.positivePart t = D.negativePart t + fzzCigarParitySignedTargetMeasure t := by
  letI : IsFiniteMeasure (D.positivePart t) := D.positive_finite t
  letI : IsFiniteMeasure (D.negativePart t) := D.negative_finite t
  letI : IsFiniteMeasure
      (D.negativePart t + fzzCigarParitySignedTargetMeasure t) := by
    refine IsFiniteMeasure.mk ?_
    simp [fzzCigarParitySignedTargetMeasure,
      measure_lt_top (D.negativePart t) Set.univ]
  obtain ⟨b, hb, hpos, hneg⟩ := D.common_window t
  exact HTGeometry.measure_eq_of_forall_real_moment_eq hb hpos hneg (D.all_grades t)

private theorem integrable_fzzCigarParityUndressingDensity_signedTarget
    (t : FZZCigarPositiveDelay) :
    Integrable fzzCigarParityUndressingDensity
      (fzzCigarParitySignedTargetMeasure t) := by
  have hcpos : 0 < (t : ℝ)⁻¹ * fzzCigarPositiveDelayDensity t :=
    mul_pos (inv_pos.mpr t.property) (fzzCigarPositiveDelayDensity_pos_signed t)
  rw [fzzCigarParitySignedTargetMeasure]
  apply (integrable_smul_measure (ENNReal.ofReal_pos.mpr hcpos).ne' (by simp)).mpr
  apply integrable_dirac
  simp [fzzCigarParityUndressingDensity]

/-- Reciprocal-Fermi undressing of the Jordan identity recovers exactly the forced singular local
mass. -/
theorem FZZCigarParitySignedNonlocalFEReflectionData.undressedNetMass_eq
    (D : FZZCigarParitySignedNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    (∫ x : ℝ, fzzCigarParityUndressingDensity x ∂D.positivePart t) -
        (∫ x : ℝ, fzzCigarParityUndressingDensity x ∂D.negativePart t) =
      (t : ℝ)⁻¹ * (Real.exp (t : ℝ)⁻¹ + 1) /
        (Real.exp (t : ℝ) + 1) := by
  have heq := congrArg
    (fun μ : Measure ℝ => ∫ x : ℝ, fzzCigarParityUndressingDensity x ∂μ)
    (D.fermiWeightedMeasure_eq t)
  rw [integral_add_measure (D.undressing_negative_integrable t)
    (integrable_fzzCigarParityUndressingDensity_signedTarget t)] at heq
  rw [fzzCigarParitySignedTargetMeasure, integral_smul_measure,
    integral_dirac] at heq
  have hcpos : 0 < (t : ℝ)⁻¹ * fzzCigarPositiveDelayDensity t :=
    mul_pos (inv_pos.mpr t.property) (fzzCigarPositiveDelayDensity_pos_signed t)
  rw [ENNReal.toReal_ofReal hcpos.le] at heq
  simp only [smul_eq_mul] at heq
  rw [fzzCigarParityUndressingDensity] at heq
  rw [fzzCigarPositiveDelayDensity,
    fzzCigarParityDelay_eq_fermi t.property] at heq
  have hden : Real.exp (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden] at heq ⊢
  linarith

/-- Reciprocal-Fermi-weighted Jordan total variation. -/
def FZZCigarParitySignedNonlocalFEReflectionData.undressedVariation
    (D : FZZCigarParitySignedNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) : ℝ :=
  (∫ x : ℝ, fzzCigarParityUndressingDensity x ∂D.positivePart t) +
    (∫ x : ℝ, fzzCigarParityUndressingDensity x ∂D.negativePart t)

/-- Signed total variation must pay at least the singular local reflection weight. -/
theorem FZZCigarParitySignedNonlocalFEReflectionData.forcedWeight_le_undressedVariation
    (D : FZZCigarParitySignedNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    (t : ℝ)⁻¹ * (Real.exp (t : ℝ)⁻¹ + 1) /
          (Real.exp (t : ℝ) + 1) ≤
      D.undressedVariation t := by
  have hnet := D.undressedNetMass_eq t
  have hneg : 0 ≤
      ∫ x : ℝ, fzzCigarParityUndressingDensity x ∂D.negativePart t := by
    apply integral_nonneg
    intro x
    rw [fzzCigarParityUndressingDensity]
    positivity
  rw [FZZCigarParitySignedNonlocalFEReflectionData.undressedVariation]
  linarith

theorem FZZCigarParitySignedNonlocalFEReflectionData.undressedVariation_nonneg
    (D : FZZCigarParitySignedNonlocalFEReflectionData)
    (t : FZZCigarPositiveDelay) :
    0 ≤ D.undressedVariation t := by
  have hpos : 0 ≤
      ∫ x : ℝ, fzzCigarParityUndressingDensity x ∂D.positivePart t := by
    apply integral_nonneg
    intro x
    rw [fzzCigarParityUndressingDensity]
    positivity
  have hneg : 0 ≤
      ∫ x : ℝ, fzzCigarParityUndressingDensity x ∂D.negativePart t := by
    apply integral_nonneg
    intro x
    rw [fzzCigarParityUndressingDensity]
    positivity
  rw [FZZCigarParitySignedNonlocalFEReflectionData.undressedVariation]
  exact add_nonneg hpos hneg

/-- Signed undressed variation on the reciprocal-depth ultraviolet ray. -/
def FZZCigarParitySignedNonlocalFEReflectionData.uvUndressedVariation
    (D : FZZCigarParitySignedNonlocalFEReflectionData) (n : ℕ) : ℝ :=
  D.undressedVariation (fzzCigarParityPositiveNonlocalUVDelay n)

theorem FZZCigarParitySignedNonlocalFEReflectionData.forcedLocal_uvWeight_le
    (D : FZZCigarParitySignedNonlocalFEReflectionData) (n : ℕ) :
    fzzCigarParityForcedLocalFEReflectionData.uvWeight n ≤
      D.uvUndressedVariation n := by
  rw [fzzCigarParityForcedLocalFEReflectionData.uvWeight_eq]
  simpa only [FZZCigarParitySignedNonlocalFEReflectionData.uvUndressedVariation,
    fzzCigarParityPositiveNonlocalUVDelay, Subtype.coe_mk, inv_inv] using
      D.forcedWeight_le_undressedVariation
        (fzzCigarParityPositiveNonlocalUVDelay n)

/-- Polynomial tempering of signed transport means polynomial reciprocal-Fermi-weighted total
variation on the ultraviolet ray. -/
def FZZCigarParitySignedNonlocalFEReflectionData.PolynomiallyTempered
    (D : FZZCigarParitySignedNonlocalFEReflectionData) : Prop :=
  ∃ K : ℕ, D.uvUndressedVariation =O[atTop]
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ K)

/-- Analytic signed nonlocal transport inherits the same beyond-polynomial singularity as local
reciprocal reflection. -/
theorem FZZCigarParitySignedNonlocalFEReflectionData.not_polynomiallyTempered
    (D : FZZCigarParitySignedNonlocalFEReflectionData) :
    ¬ D.PolynomiallyTempered := by
  rintro ⟨K, hK⟩
  have hdom : fzzCigarParityForcedLocalFEReflectionData.uvWeight =O[atTop]
      D.uvUndressedVariation := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, Eventually.of_forall fun n => ?_⟩
    have huvnonneg : 0 ≤ D.uvUndressedVariation n := by
      exact D.undressedVariation_nonneg
        (fzzCigarParityPositiveNonlocalUVDelay n)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (fzzCigarParityForcedLocalFEReflectionData.uvWeight_pos n),
      abs_of_nonneg huvnonneg]
    simpa only [one_mul] using D.forcedLocal_uvWeight_le n
  have hforced : fzzCigarParityForcedLocalFEReflectionData.PolynomiallyTempered :=
    ⟨K, hdom.trans hK⟩
  exact fzzCigarParityForcedLocalFEReflectionData.not_polynomiallyTempered hforced

/-- **[FZZ-P SIGNED NONLOCAL ROUTE KILL].**  No polynomially tempered signed finite-measure
reflection with one analytic moment window can implement every integer reflected Mellin row of
the literal FZZ parity source. -/
theorem no_polynomiallyTempered_FZZCigarParitySignedNonlocalFEReflectionData :
    ¬ ∃ D : FZZCigarParitySignedNonlocalFEReflectionData,
      D.PolynomiallyTempered := by
  rintro ⟨D, hD⟩
  exact D.not_polynomiallyTempered hD

end

end RHTower
