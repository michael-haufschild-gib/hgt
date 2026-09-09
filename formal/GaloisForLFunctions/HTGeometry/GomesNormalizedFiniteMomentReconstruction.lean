import GaloisForLFunctions.HTGeometry.GomesPolynomialFiniteMomentReconstruction
import GaloisForLFunctions.HTGeometry.GomesFinitePolynomialNormalizedProfile

/-!
# Finite normalized observations recover the shared connection

Canonical mass-one log-profiles transfer finite raw reconstruction to normalized
laws. Moments one through the degree cutoff suffice: the mass coordinate is already
fixed. Thus every bounded-degree connection class has an exact finite moment record,
and common finite tensor factors can be cancelled from these observations.
-/

noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology NNReal ENNReal SchwartzMap

namespace GaloisForLFunctions.HTGeometry

/-- A finite normalized moment prefix determines the complete probability law. -/
theorem gomesFinitePolynomialProfile_finite_moments_eq_iff (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, n ≤ max P.val.natDegree Q.val.natDegree →
      (∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val)) =
        ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val)) ↔
      gomesDilatonMassNormalized P.val = gomesDilatonMassNormalized Q.val := by
  rw [← gomesFinitePolynomialNormalizedProfile_eq_iff]
  simpa only [gomesFinitePolynomialNormalizedProfile_natDegree,
    gomesFinitePolynomialNormalizedProfile_measure] using
    gomesPolynomialMeasure_finite_moments_reconstruct
      (gomesFinitePolynomialNormalizedProfile P) (gomesFinitePolynomialNormalizedProfile Q)

/-- Finitely many normalized moments recover precisely the shared polynomial connection. -/
theorem gomesFinitePolynomialProfile_finite_moments_connection_iff (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, n ≤ max P.val.natDegree Q.val.natDegree →
      (∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val)) =
        ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val)) ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM Q.val := by
  rw [gomesFinitePolynomialProfile_finite_moments_eq_iff,
    gomesFinitePolynomialProfile_normalized_eq_iff, gomesDilatonConnection_constant_iff]

/-- The same finite observations recover the canonical ground field up to a nonzero scalar. -/
theorem gomesFinitePolynomialProfile_finite_moments_ground_iff (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, n ≤ max P.val.natDegree Q.val.natDegree →
      (∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val)) =
        ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val)) ↔
      ∃ c : ℂ, c ≠ 0 ∧ gomesPolynomialGroundState P = c • gomesPolynomialGroundState Q := by
  rw [gomesFinitePolynomialProfile_finite_moments_eq_iff,
    gomesPolynomialGroundState_projective_probability_iff]

/-- Positive-order moments alone suffice because normalized mass is fixed. -/
theorem gomesFinitePolynomialProfile_positive_finite_moments_connection_iff
    (P Q : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, 0 < n → n ≤ max P.val.natDegree Q.val.natDegree →
      (∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val)) =
        ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val)) ↔
      dilatonSuperchargeCLM P.val = dilatonSuperchargeCLM Q.val := by
  constructor
  · intro h
    apply (gomesFinitePolynomialProfile_finite_moments_connection_iff P Q).mp
    intro n hn
    cases n with
    | zero =>
      letI : IsProbabilityMeasure (gomesDilatonMassNormalized P.val) :=
        gomesFinitePolynomialProfile_probability P
      letI : IsProbabilityMeasure (gomesDilatonMassNormalized Q.val) :=
        gomesFinitePolynomialProfile_probability Q
      simp
    | succ n => exact h (n + 1) (Nat.succ_pos n) hn
  · intro h n _ hn
    exact (gomesFinitePolynomialProfile_finite_moments_connection_iff P Q).mpr h n hn

/-- The d positive-order moments of a bounded-degree normalized profile. -/
def gomesBoundedPolynomialNormalizedRecord (d : ℕ) (P : GomesBoundedPolynomialProfile d) :
    Fin d → ℝ :=
  fun n => ∫ x : ℝ, x ^ (n.val + 1) ∂(gomesDilatonMassNormalized P.val.val)

/-- The finite normalized record has exactly the shared-connection equivalence kernel. -/
theorem gomesBoundedPolynomialNormalizedRecord_eq_iff (d : ℕ) (P Q : GomesBoundedPolynomialProfile d) :
    gomesBoundedPolynomialNormalizedRecord d P = gomesBoundedPolynomialNormalizedRecord d Q ↔
      dilatonSuperchargeCLM P.val.val = dilatonSuperchargeCLM Q.val.val := by
  constructor
  · intro h
    apply (gomesFinitePolynomialProfile_positive_finite_moments_connection_iff P.val Q.val).mp
    intro n hpos hn
    cases n with
    | zero => exact False.elim ((lt_irrefl 0) hpos)
    | succ n =>
      have hd : n < d := Nat.lt_of_succ_le (hn.trans (max_le P.property Q.property))
      exact congrFun h ⟨n, hd⟩
  · intro h
    have hm : gomesDilatonMassNormalized P.val.val = gomesDilatonMassNormalized Q.val.val := by
      rw [gomesFinitePolynomialProfile_normalized_eq_iff, ← gomesDilatonConnection_constant_iff]
      exact h
    funext n
    change (∫ x : ℝ, x ^ (n.val + 1) ∂(gomesDilatonMassNormalized P.val.val)) =
      ∫ x : ℝ, x ^ (n.val + 1) ∂(gomesDilatonMassNormalized Q.val.val)
    rw [hm]

/-- The finite normalized record determines the canonical mass-one representative exactly. -/
theorem gomesBoundedPolynomialNormalizedRecord_canonical_iff
    (d : ℕ) (P Q : GomesBoundedPolynomialProfile d) :
    gomesBoundedPolynomialNormalizedRecord d P = gomesBoundedPolynomialNormalizedRecord d Q ↔
      gomesFinitePolynomialNormalizedProfile P.val = gomesFinitePolynomialNormalizedProfile Q.val := by
  rw [gomesBoundedPolynomialNormalizedRecord_eq_iff,
    gomesFinitePolynomialNormalizedProfile_eq_iff, gomesFinitePolynomialProfile_normalized_eq_iff,
    gomesDilatonConnection_constant_iff]

/-- Common finite tensor factors cancel from the finite normalized observation test. -/
theorem gomesFinitePolynomialProfile_finite_moments_tensor_cancel (P Q R : GomesFinitePolynomialProfile) :
    (∀ n : ℕ, n ≤ max (P + R).val.natDegree (Q + R).val.natDegree →
      (∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized (P + R).val)) =
        ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized (Q + R).val)) ↔
      ∀ n : ℕ, n ≤ max P.val.natDegree Q.val.natDegree →
        (∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized P.val)) =
          ∫ x : ℝ, x ^ n ∂(gomesDilatonMassNormalized Q.val) := by
  rw [gomesFinitePolynomialProfile_finite_moments_eq_iff,
    gomesFinitePolynomialProfile_finite_moments_eq_iff]
  exact gomesFinitePolynomialProfile_tensor_cancel P Q R

end GaloisForLFunctions.HTGeometry
