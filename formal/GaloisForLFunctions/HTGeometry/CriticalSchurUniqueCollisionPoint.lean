import GaloisForLFunctions.HTGeometry.CriticalSheetCollisionTangent
import GaloisForLFunctions.HTGeometry.CriticalSchurTangentConstantTerm
import GaloisForLFunctions.HTGeometry.CriticalFibreSharedTangentRigidity
import GaloisForLFunctions.HTGeometry.CriticalSchurMarkedReduction
import GaloisForLFunctions.HTGeometry.LowTangentJacobianKernel

/-!
# `(D-f)`: all collisions happen at one point of the reduced fibre

Collision tangents at two singular sheets are proportional, because both conormal vectors span the
same line as the fixed branch conormal.  Rescaling gives one common tangent, which is coprime
because its constant terms do not vanish and the low pair is unique up to scale.  The corpus's
shared-tangent rigidity then identifies the two reduced states.

This is `f_{Q₀} = 1` in the form the collision count consumes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial IsLocalRing

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- Ground-field constants make the residue field of the normal-closure Schur place characteristic
zero. -/
noncomputable instance criticalNormalClosureSchurResidue_charZero :
    CharZero (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n))) :=
  (RingHom.charZero_iff
    (((IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n))).comp
      ((criticalSchurObservationValuationToNormalClosure K (Fact.out : 0 < m)
        (Fact.out : 0 < n)).comp
        (criticalObservationSchurConstantBaseMap K (Fact.out : 0 < m)
          (Fact.out : 0 < n)))).injective)).mp inferInstance

/-- **Collision tangents at two singular sheets are proportional.** -/
theorem criticalSheet_tangent_smul [DecidableEq K]
    (σ σ' : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
    (hsing' : criticalSheetChartToNormalSchur K σ'
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
    {U V U' V' : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]}
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ)) (hUV : U ≠ 0 ∨ V ≠ 0)
    (htan : (X : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]) ^ (m + n)
      ∣ U * criticalSheetReducedRecipPolynomial K σ
        + criticalSheetReducedRawPolynomial K σ * V)
    (hU' : U'.degree < (m : ℕ)) (hV' : V'.degree < (n : ℕ))
    (htan' : (X : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]) ^ (m + n)
      ∣ U' * criticalSheetReducedRecipPolynomial K σ'
        + criticalSheetReducedRawPolynomial K σ' * V') :
    ∃ c : IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)),
      U' = Polynomial.C c * U ∧ V' = Polynomial.C c * V := by
  obtain ⟨a, ha⟩ := criticalSheet_exists_smul_of_tangent K σ hsing hU hV htan
  obtain ⟨b, hb⟩ := criticalSheet_exists_smul_of_tangent K σ' hsing' hU' hV' htan'
  have hane : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ha
    exact horizonConormalVector_ne_zero hU hV hUV ha
  refine ⟨b * a⁻¹, tangent_smul_of_conormal_smul hU hV hU' hV' ?_⟩
  rw [hb, ha, smul_smul]
  congr 1
  field_simp

/-- The reciprocal component of a collision tangent has a nonzero constant term. -/
theorem criticalSheet_tangent_recip_coeff_zero_ne_zero (σ : criticalGeometricSheet K m n)
    {U V : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]}
    (htan : (X : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]) ^ (m + n)
      ∣ U * criticalSheetReducedRecipPolynomial K σ
        + criticalSheetReducedRawPolynomial K σ * V)
    (hU0 : U.coeff 0 ≠ 0) :
    V.coeff 0 ≠ 0 := by
  have hfm : 0 < m := Fact.out
  obtain ⟨w, hw⟩ := dvd_reciprocal_of_low_tangent (criticalSheet_reduced_inv K σ) htan
  have hzero : (V + criticalSheetReducedRecipPolynomial K σ *
      criticalSheetReducedRecipPolynomial K σ * U).coeff 0 = 0 := by
    rw [hw, Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow,
      if_neg (by have := hfm; omega), zero_mul]
  rw [Polynomial.coeff_add, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero] at hzero
  intro hV0
  rw [hV0, zero_add] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact criticalSheetReducedRecipPolynomial_coeff_zero_ne_zero K σ h'
    · exact criticalSheetReducedRecipPolynomial_coeff_zero_ne_zero K σ h'
  · exact hU0 h

/-- The collision tangent at a singular sheet is a coprime pair. -/
theorem criticalSheet_tangent_isCoprime [DecidableEq K] (σ : criticalGeometricSheet K m n)
    (hsing : criticalSheetChartToNormalSchur K σ
        (criticalSchurRamificationChartElement K (m := m) (n := n))
      ∈ maximalIdeal (criticalNormalClosureSchurValuationSubring K (Fact.out : 0 < m)
        (Fact.out : 0 < n)))
    {U V : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]}
    (hU : U.degree < (m : ℕ)) (hV : V.degree < (n : ℕ)) (hUV : U ≠ 0 ∨ V ≠ 0)
    (htan : (X : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]) ^ (m + n)
      ∣ U * criticalSheetReducedRecipPolynomial K σ
        + criticalSheetReducedRawPolynomial K σ * V) :
    IsCoprime U V := by
  have hU0 := criticalSheet_tangent_coeff_zero_ne_zero K σ hsing hU hV hUV htan
  refine isCoprime_of_low_tangent_unique hU0
    (criticalSheet_tangent_recip_coeff_zero_ne_zero K σ htan hU0) htan ?_
  intro U'' V'' hU''deg hV''deg htan''
  obtain ⟨c, hc, _⟩ := criticalSheet_tangent_smul K σ σ hsing hsing hU hV hUV htan
    (lt_of_le_of_lt hU''deg hU) (lt_of_le_of_lt hV''deg hV) htan''
  exact ⟨c, hc⟩

/-- The collision tangent, stated against the reduced jets. -/
theorem criticalSchur_exists_reduced_tangent_of_collision'
    (σ τ : criticalGeometricSheet K m n) (hne : σ ≠ τ)
    (hr : criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ
      = criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) τ) :
    ∃ U V : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      (Fact.out : 0 < m) (Fact.out : 0 < n)))[X],
      (U ≠ 0 ∨ V ≠ 0) ∧ U.degree < (m : ℕ) ∧ V.degree < (n : ℕ) ∧
      (X : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
        (Fact.out : 0 < m) (Fact.out : 0 < n)))[X]) ^ (m + n)
        ∣ U * criticalSheetReducedRecipPolynomial K σ
          + criticalSheetReducedRawPolynomial K σ * V := by
  obtain ⟨U, V, h1, h2, h3, h4⟩ := criticalSchur_exists_reduced_tangent_of_collision K
    (Fact.out : 1 < m) (Fact.out : 1 < n) σ τ hne hr
  refine ⟨U, V, h1, h2, h3, ?_⟩
  rw [criticalSheetReducedRecipPolynomial_eq', criticalSheetReducedRawPolynomial_eq']
  exact h4

/-- **`(D-f)`.  All collisions of the Schur reduction happen at one point of the reduced fibre.** -/
theorem criticalSchur_reducedFibre_eq_of_collisions [DecidableEq K]
    (σ τ σ' τ' : criticalGeometricSheet K m n) (hne : σ ≠ τ)
    (hr : criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ
      = criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) τ)
    (hne' : σ' ≠ τ')
    (hr' : criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ'
      = criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) τ') :
    criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ
      = criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ' := by
  have hfm : 0 < m := Fact.out
  have hfn : 0 < n := Fact.out
  classical
  obtain ⟨U, V, hUV, hU, hV, htan⟩ :=
    criticalSchur_exists_reduced_tangent_of_collision' K σ τ hne hr
  obtain ⟨U', V', hUV', hU', hV', htan'⟩ :=
    criticalSchur_exists_reduced_tangent_of_collision' K σ' τ' hne' hr'
  have hsing := criticalSheet_singular_of_tangent K σ hU hV hUV htan
  have hsing' := criticalSheet_singular_of_tangent K σ' hU' hV' hUV' htan'
  obtain ⟨c, hUc, hVc⟩ := criticalSheet_tangent_smul K σ σ' hsing hsing' hU hV hUV htan
    hU' hV' htan'
  have hcne : c ≠ 0 := by
    intro h0
    rcases hUV' with h | h
    · exact h (by rw [hUc, h0, map_zero, zero_mul])
    · exact h (by rw [hVc, h0, map_zero, zero_mul])
  have htanσ' : (X : (IsLocalRing.ResidueField (criticalNormalClosureSchurValuationSubring K
      hfm hfn))[X]) ^ (m + n)
      ∣ U * criticalSheetReducedRecipPolynomial K σ'
        + criticalSheetReducedRawPolynomial K σ' * V := by
    have hfac : U' * criticalSheetReducedRecipPolynomial K σ'
        + criticalSheetReducedRawPolynomial K σ' * V'
        = Polynomial.C c * (U * criticalSheetReducedRecipPolynomial K σ'
          + criticalSheetReducedRawPolynomial K σ' * V) := by
      rw [hUc, hVc]; ring
    rw [hfac] at htan'
    exact (IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcne))).mp htan'
  have hU0 := criticalSheet_tangent_coeff_zero_ne_zero K σ hsing hU hV hUV htan
  refine criticalFibre_eq_of_shared_coprime_tangent hfm
    (X_pow_dvd_reduced_criticalNormalClosureSchurRawTailIntegral K hfm
      hfn)
    (X_pow_dvd_reduced_criticalNormalClosureSchurReciprocalTailIntegral K hfm
      hfn)
    (reduced_criticalNormalClosureSchurReciprocalTailIntegral_coeff_marked_ne_zero K
      (Fact.out : 1 < m) (Fact.out : 1 < n))
    _ _ hU hV (fun h => hU0 (by rw [h, Polynomial.coeff_zero]))
    (criticalSheet_tangent_isCoprime K σ hsing hU hV hUV htan) ?_ ?_
  · simpa only [criticalSheetReducedRecipPolynomial_eq, criticalSheetReducedRawPolynomial_eq]
      using htan
  · simpa only [criticalSheetReducedRecipPolynomial_eq, criticalSheetReducedRawPolynomial_eq]
      using htanσ'

end

end GaloisForLFunctions.HTGeometry
