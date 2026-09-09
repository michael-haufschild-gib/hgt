import GaloisForLFunctions.HTGeometry.GomesPolynomialMomentGerm

/-!
# A canonical normalized log-profile

Every finite polynomial density has a unique representative with total mass one
inside its constant-log-amplitude class. The representative retains degree and the
shared connection, while realizing the normalized law as an actual raw exponential
measure. This allows finite raw reconstruction to transfer to normalized observations.
-/

noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- The exact additive log-amplitude needed to normalize a finite profile. -/
def gomesPolynomialNormalizationShift (P : GomesFinitePolynomialProfile) : ℝ :=
  Real.log ((gomesDilatonMeasure P.val Set.univ)⁻¹).toReal

/-- The canonical mass-one representative of a finite polynomial profile. -/
def gomesFinitePolynomialNormalizedProfile (P : GomesFinitePolynomialProfile) :
    GomesFinitePolynomialProfile :=
  gomesFinitePolynomialTilt P 0 (gomesPolynomialNormalizationShift P)

/-- Canonical normalization changes only the constant coefficient. -/
theorem gomesFinitePolynomialNormalizedProfile_val (P : GomesFinitePolynomialProfile) :
    (gomesFinitePolynomialNormalizedProfile P).val = P.val + C (gomesPolynomialNormalizationShift P) := by
  change P.val + (C (0 : ℝ) * X + C (gomesPolynomialNormalizationShift P)) = _
  rw [map_zero, zero_mul, zero_add]

/-- The exponential of the normalization shift equals the exact reciprocal mass. -/
theorem gomesPolynomialNormalizationShift_exp (P : GomesFinitePolynomialProfile) :
    ENNReal.ofReal (Real.exp (gomesPolynomialNormalizationShift P)) =
      (gomesDilatonMeasure P.val Set.univ)⁻¹ := by
  have hm : gomesDilatonMeasure P.val Set.univ ≠ ∞ :=
    lt_top_iff_ne_top.mp ((isFiniteMeasure_iff _).mp P.property)
  have hi : (gomesDilatonMeasure P.val Set.univ)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (gomesDilatonMeasure_mass_ne_zero P.val)
  rw [gomesPolynomialNormalizationShift,
    Real.exp_log (ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hm) hi), ENNReal.ofReal_toReal hi]

/-- Its raw exponential measure is precisely the original normalized probability law. -/
theorem gomesFinitePolynomialNormalizedProfile_measure (P : GomesFinitePolynomialProfile) :
    gomesDilatonMeasure (gomesFinitePolynomialNormalizedProfile P).val =
      gomesDilatonMassNormalized P.val := by
  rw [gomesFinitePolynomialNormalizedProfile_val, gomesDilatonMeasure_constant,
    gomesPolynomialNormalizationShift_exp]
  rfl

/-- Canonical normalization preserves polynomial degree exactly. -/
theorem gomesFinitePolynomialNormalizedProfile_natDegree (P : GomesFinitePolynomialProfile) :
    (gomesFinitePolynomialNormalizedProfile P).val.natDegree = P.val.natDegree := by
  rw [gomesFinitePolynomialNormalizedProfile_val, natDegree_add_C]

/-- The canonical representative has total raw mass one. -/
theorem gomesFinitePolynomialNormalizedProfile_mass (P : GomesFinitePolynomialProfile) :
    gomesDilatonMeasure (gomesFinitePolynomialNormalizedProfile P).val Set.univ = 1 := by
  rw [gomesFinitePolynomialNormalizedProfile_measure]
  letI : IsProbabilityMeasure (gomesDilatonMassNormalized P.val) :=
    gomesFinitePolynomialProfile_probability P
  exact measure_univ

/-- Normalizing a canonical representative requires no further log-amplitude change. -/
theorem gomesPolynomialNormalizationShift_normalized (P : GomesFinitePolynomialProfile) :
    gomesPolynomialNormalizationShift (gomesFinitePolynomialNormalizedProfile P) = 0 := by
  rw [gomesPolynomialNormalizationShift, gomesFinitePolynomialNormalizedProfile_mass]
  simp only [inv_one, ENNReal.toReal_one, Real.log_one]

/-- The canonical normalization map is idempotent. -/
theorem gomesFinitePolynomialNormalizedProfile_idempotent (P : GomesFinitePolynomialProfile) :
    gomesFinitePolynomialNormalizedProfile (gomesFinitePolynomialNormalizedProfile P) =
      gomesFinitePolynomialNormalizedProfile P := by
  apply Subtype.ext
  rw [gomesFinitePolynomialNormalizedProfile_val, gomesPolynomialNormalizationShift_normalized,
    map_zero, add_zero]

/-- Equality of canonical profiles is exactly equality of normalized measures. -/
theorem gomesFinitePolynomialNormalizedProfile_eq_iff (P Q : GomesFinitePolynomialProfile) :
    gomesFinitePolynomialNormalizedProfile P = gomesFinitePolynomialNormalizedProfile Q ↔
      gomesDilatonMassNormalized P.val = gomesDilatonMassNormalized Q.val := by
  constructor
  · intro h
    rw [← gomesFinitePolynomialNormalizedProfile_measure P,
      ← gomesFinitePolynomialNormalizedProfile_measure Q, h]
  · intro h
    apply Subtype.ext
    apply gomesDilatonMeasure_injective
    rwa [gomesFinitePolynomialNormalizedProfile_measure, gomesFinitePolynomialNormalizedProfile_measure]

/-- Canonical normalization leaves the induced first-order connection unchanged. -/
theorem gomesFinitePolynomialNormalizedProfile_connection (P : GomesFinitePolynomialProfile) :
    dilatonSuperchargeCLM (gomesFinitePolynomialNormalizedProfile P).val = dilatonSuperchargeCLM P.val := by
  rw [gomesFinitePolynomialNormalizedProfile_val]
  exact gomesDilatonConnection_constant P.val (gomesPolynomialNormalizationShift P)

end GaloisForLFunctions.HTGeometry
