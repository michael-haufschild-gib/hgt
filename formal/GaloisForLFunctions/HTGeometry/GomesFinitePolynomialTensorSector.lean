import GaloisForLFunctions.HTGeometry.GomesPolynomialExponentialIntegrability

/-!
# The full finite polynomial tensor sector

The finite survivor of the normalization obstruction is an additive subsemigroup of
polynomial log-densities. Tensor multiplication stays finite; normalized observations
admit cancellation; no finite tensor unit or dual pair exists. This extends the scalar
integer-charge experiment to mixtures of arbitrary polynomial degrees.
-/

noncomputable section
open Polynomial MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- All finite polynomial densities form a tensor-closed additive subsemigroup. -/
def gomesFinitePolynomialProfiles : AddSubsemigroup ℝ[X] where
  carrier := {P | IsFiniteMeasure (gomesDilatonMeasure P)}
  add_mem' := by
    intro P Q hP hQ
    change IsFiniteMeasure (gomesDilatonMeasure P) at hP
    change IsFiniteMeasure (gomesDilatonMeasure Q) at hQ
    change IsFiniteMeasure (gomesDilatonMeasure (P + Q))
    rw [gomesDilatonMeasure_finite_iff_integrable,
      gomesPolynomialExponential_integrable_decay_iff] at hP hQ ⊢
    exact ⟨by simpa only [eval_add] using hP.1.atBot_add_atBot hQ.1,
      by simpa only [eval_add] using hP.2.atBot_add_atBot hQ.2⟩

/-- A polynomial profile belonging to the exact finite tensor sector. -/
abbrev GomesFinitePolynomialProfile := ↥gomesFinitePolynomialProfiles

/-- Membership has a complete coefficient-level test. -/
theorem gomesFinitePolynomialProfiles_mem_iff (P : ℝ[X]) :
    P ∈ gomesFinitePolynomialProfiles ↔
      0 < P.natDegree ∧ Even P.natDegree ∧ P.leadingCoeff < 0 :=
  gomesDilatonMeasure_finite_polynomial_iff P

/-- The tensor unit is excluded from the full finite sector. -/
theorem gomesFinitePolynomialProfiles_zero_not_mem : (0 : ℝ[X]) ∉ gomesFinitePolynomialProfiles := by
  rw [gomesFinitePolynomialProfiles_mem_iff]
  simp only [natDegree_zero, lt_self_iff_false, false_and, not_false_eq_true]

/-- No finite profile and its dual can both belong to this sector. -/
theorem gomesFinitePolynomialProfiles_no_dual (P : ℝ[X]) :
    ¬ (P ∈ gomesFinitePolynomialProfiles ∧ -P ∈ gomesFinitePolynomialProfiles) := by
  rintro ⟨hP, hN⟩
  have h := gomesFinitePolynomialProfiles.add_mem hP hN
  rw [add_neg_cancel] at h
  exact gomesFinitePolynomialProfiles_zero_not_mem h

/-- No pair of finite polynomial densities can fail under tensor addition. -/
theorem gomesFinitePolynomialProfiles_no_tensor_failure :
    ¬ ∃ P Q : ℝ[X], IsFiniteMeasure (gomesDilatonMeasure P) ∧
      IsFiniteMeasure (gomesDilatonMeasure Q) ∧ ¬ IsFiniteMeasure (gomesDilatonMeasure (P + Q)) := by
  rintro ⟨P, Q, hP, hQ, hPQ⟩
  exact hPQ (gomesFinitePolynomialProfiles.add_mem hP hQ)

/-- Every finite profile yields an actual probability measure after normalization. -/
theorem gomesFinitePolynomialProfile_probability (P : GomesFinitePolynomialProfile) :
    IsProbabilityMeasure (gomesDilatonMassNormalized P.val) :=
  (gomesDilatonMassNormalized_probability_iff P.val).mpr P.property

/-- Normalizing before a second finite factor gives exactly the correct tensor probability law. -/
theorem gomesFinitePolynomialProfile_normalized_tensor (P Q : GomesFinitePolynomialProfile) :
    gomesDilatonRenormalizedReweight P.val Q.val = gomesDilatonMassNormalized (P.val + Q.val) :=
  (gomesDilatonRenormalizedReweight_commutes_iff P.val Q.val).mpr (Or.inl P.property)

/-- The actual two-stage tensor operation remains a probability law for all finite profiles. -/
theorem gomesFinitePolynomialProfile_tensor_probability (P Q : GomesFinitePolynomialProfile) :
    IsProbabilityMeasure (gomesDilatonRenormalizedReweight P.val Q.val) :=
  (gomesDilatonRenormalizedReweight_probability_iff P.val Q.val).mpr
    ⟨P.property, gomesFinitePolynomialProfiles.add_mem P.property Q.property⟩

/-- Finite-sector observation equality has only the constant log-amplitude kernel. -/
theorem gomesFinitePolynomialProfile_normalized_eq_iff (P Q : GomesFinitePolynomialProfile) :
    gomesDilatonMassNormalized P.val = gomesDilatonMassNormalized Q.val ↔
      ∃ c : ℝ, P.val = Q.val + C c := by
  rw [gomesDilatonMassNormalized_eq_iff]
  have hn : gomesDilatonMeasure P.val Set.univ ≠ ∞ :=
    (lt_top_iff_ne_top.mp ((isFiniteMeasure_iff _).mp P.property))
  simp only [hn, false_and, or_false]

/-- Tensoring by a common finite profile preserves and reflects equality of normalized laws. -/
theorem gomesFinitePolynomialProfile_tensor_cancel (P Q R : GomesFinitePolynomialProfile) :
    gomesDilatonMassNormalized (P.val + R.val) = gomesDilatonMassNormalized (Q.val + R.val) ↔
      gomesDilatonMassNormalized P.val = gomesDilatonMassNormalized Q.val := by
  let PR : GomesFinitePolynomialProfile := ⟨P.val + R.val,
    gomesFinitePolynomialProfiles.add_mem P.property R.property⟩
  let QR : GomesFinitePolynomialProfile := ⟨Q.val + R.val,
    gomesFinitePolynomialProfiles.add_mem Q.property R.property⟩
  change gomesDilatonMassNormalized PR.val = gomesDilatonMassNormalized QR.val ↔ _
  rw [gomesFinitePolynomialProfile_normalized_eq_iff,
    gomesFinitePolynomialProfile_normalized_eq_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    change P.val + R.val = Q.val + R.val + C c at hc
    linear_combination hc
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    change P.val + R.val = Q.val + R.val + C c
    linear_combination hc

/-- Every finite tensor factor changes every finite normalized law: there is no finite identity. -/
theorem gomesFinitePolynomialProfile_tensor_changes_law (P Q : GomesFinitePolynomialProfile) :
    gomesDilatonMassNormalized (P.val + Q.val) ≠ gomesDilatonMassNormalized P.val := by
  let PQ : GomesFinitePolynomialProfile := ⟨P.val + Q.val,
    gomesFinitePolynomialProfiles.add_mem P.property Q.property⟩
  intro h
  obtain ⟨c, hc⟩ := (gomesFinitePolynomialProfile_normalized_eq_iff PQ P).mp h
  have he : Q.val = C c := by
    change P.val + Q.val = P.val + C c at hc
    exact add_left_cancel hc
  have hd := (gomesFinitePolynomialProfiles_mem_iff Q.val).mp Q.property
  rw [he, natDegree_C] at hd
  exact (lt_irrefl 0) hd.1

/-- Bracketing does not change the finite three-factor normalized observation. -/
theorem gomesFinitePolynomialProfile_tensor_associative (P Q R : GomesFinitePolynomialProfile) :
    gomesDilatonRenormalizedReweight (P.val + Q.val) R.val =
      gomesDilatonRenormalizedReweight P.val (Q.val + R.val) := by
  rw [(gomesDilatonRenormalizedReweight_commutes_iff _ _).mpr
    (Or.inl (gomesFinitePolynomialProfiles.add_mem P.property Q.property)),
    (gomesDilatonRenormalizedReweight_commutes_iff _ _).mpr (Or.inl P.property), add_assoc]

end GaloisForLFunctions.HTGeometry
