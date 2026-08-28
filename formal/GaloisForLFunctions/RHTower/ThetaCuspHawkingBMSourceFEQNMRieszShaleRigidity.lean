import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEQNMShaleStinespringObstruction
import GaloisForLFunctions.RHTower.GaussHodgeWeilDeviationMoment
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import GaloisForLFunctions.HTGeometry.HellmannFeynmanRCLike

/-!
# Source-FE QNM Riesz--Shale rigidity

HC80 leaves a physical realization fork: damped Birmingham--Mokhtari resonances need not be an
orthonormal one-particle basis, so could a nonorthogonal realization evade the repeated source-FE
beta obstruction?

This module first closes the naive positive-Hilbert fork. Both exact BM branches have strictly
negative imaginary frequency on every actual Xi copy and at every overtone. Even symmetry only at
one normalized eigenvector forces its eigenvalue to be real, so neither branch can be an ordinary
symmetric Hilbert eigenmode.

The positive survivor is basis robust. Hilbert--Schmidt membership is invariant under every bounded
invertible similarity between complete complex Hilbert spaces. Consequently any Riesz synthesis
transport of the literal scalar beta block is Hilbert--Schmidt exactly when its source-FE partner
occupation vanishes, hence exactly on the critical wall; arbitrary Xi-dependent transports satisfy
the condition universally exactly under RH. Pointwise equivalences identify the same endpoint with
the HB, Deninger/FZZ-P, PW-B, and canonical-copy RBH receivers.

This does not prove that physical QNM resonances form a Riesz basis, identify their actual Green
operator beta block, cover unbounded/non-Riesz rigged synthesis, or internalize the external
Shale--Stinespring Fock theorem.

`[NEW] [QNM NO-GO] [RIESZ RIGIDITY] [SHALE ENDPOINT] [LEAN-PROVED]`
-/

open Complex Real
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A normalized eigenmode for an operator symmetric against that eigenvector. -/
def IsNormalizedPointSymmetricEigenmode (frequency : ℂ) : Prop :=
  ∃ (A : E → E) (ψ : E),
    inner ℂ ψ ψ = 1 ∧
      inner ℂ ψ (A ψ) = inner ℂ (A ψ) ψ ∧
        A ψ = frequency • ψ

/-- Every positive-branch BM frequency attached to an actual Xi copy is strictly damped. -/
theorem thetaCuspHawkingTopologicalBlackHoleQNMPlus_xi_im_lt_zero
    (n : ℕ) (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)).im < 0 := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMPlus_im,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  have hstrip := abs_xiSpectralPoint_im_lt_half q
  rw [abs_lt] at hstrip
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  norm_num at hstrip ⊢
  linarith

/-- Every negative-branch BM frequency attached to an actual Xi copy is strictly damped. -/
theorem thetaCuspHawkingTopologicalBlackHoleQNMMinus_xi_im_lt_zero
    (n : ℕ) (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)).im < 0 := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMMinus_im,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  have hstrip := abs_xiSpectralPoint_im_lt_half q
  rw [abs_lt] at hstrip
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  norm_num at hstrip ⊢
  linarith

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- A damped positive-branch BM resonance cannot be a positive-Hilbert symmetric eigenmode. -/
theorem not_isNormalizedPointSymmetricEigenmode_qnmPlus_xi
    (n : ℕ) (q : XiZeroCopy) :
    ¬ IsNormalizedPointSymmetricEigenmode (E := E)
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) := by
  rintro ⟨A, ψ, hnorm, hsymm, heigen⟩
  have hconj :=
    GaloisForLFunctions.HTGeometry.eigenvalue_conj_eq_self_of_symmetric_at
      hnorm hsymm heigen
  have him := congrArg Complex.im hconj
  rw [Complex.conj_im] at him
  linarith [thetaCuspHawkingTopologicalBlackHoleQNMPlus_xi_im_lt_zero n q]

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] in
/-- A damped negative-branch BM resonance cannot be a positive-Hilbert symmetric eigenmode. -/
theorem not_isNormalizedPointSymmetricEigenmode_qnmMinus_xi
    (n : ℕ) (q : XiZeroCopy) :
    ¬ IsNormalizedPointSymmetricEigenmode (E := E)
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) := by
  rintro ⟨A, ψ, hnorm, hsymm, heigen⟩
  have hconj :=
    GaloisForLFunctions.HTGeometry.eigenvalue_conj_eq_self_of_symmetric_at
      hnorm hsymm heigen
  have him := congrArg Complex.im hconj
  rw [Complex.conj_im] at him
  linarith [thetaCuspHawkingTopologicalBlackHoleQNMMinus_xi_im_lt_zero n q]

/-- Hilbert--Schmidt membership is invariant under every bounded invertible similarity transport. -/
theorem isHilbertSchmidt_similarity_iff
    (U : E ≃L[ℂ] F) (T : E →L[ℂ] E) :
    ContinuousLinearMap.IsHilbertSchmidt
        (U.toContinuousLinearMap ∘L T ∘L U.symm.toContinuousLinearMap) ↔
      ContinuousLinearMap.IsHilbertSchmidt T := by
  constructor
  · intro h
    have h' := (h.comp_left U.symm.toContinuousLinearMap).comp_right
      U.toContinuousLinearMap
    have heq :
        (U.symm.toContinuousLinearMap ∘L U.toContinuousLinearMap ∘L T ∘L
              U.symm.toContinuousLinearMap) ∘L U.toContinuousLinearMap = T := by
      ext x
      simp
    rw [heq] at h'
    exact h'
  · intro h
    exact (h.comp_left U.toContinuousLinearMap).comp_right
      U.symm.toContinuousLinearMap

/-- On a Hilbert space with an infinite overtone basis, a scalar identity block is
Hilbert--Schmidt exactly when its scalar vanishes. -/
theorem isHilbertSchmidt_smul_id_iff
    (b : HilbertBasis ℕ ℂ E) (c : ℂ) :
    ContinuousLinearMap.IsHilbertSchmidt
        (c • ContinuousLinearMap.id ℂ E) ↔ c = 0 := by
  rw [ContinuousLinearMap.isHilbertSchmidt_iff_summable b]
  simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul,
    b.orthonormal.norm_eq_one, mul_one]
  rw [summable_const_iff]
  exact sq_eq_zero_iff.trans norm_eq_zero

/-- The literal source-FE pair coefficient vanishes exactly in partner vacuum. -/
theorem hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_eq_zero_iff_partnerNumber_eq_zero
    (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q = 0 ↔
      hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 := by
  constructor
  · intro hpair
    have hs := norm_hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_sq q
    rw [hpair, norm_zero] at hs
    norm_num at hs
    exact hs.symm
  · intro hpartner
    apply norm_eq_zero.mp
    have hs := norm_hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_sq q
    rw [hpartner] at hs
    nlinarith [norm_nonneg (hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q)]

/-- Literal overtone beta block after an arbitrary bounded invertible Riesz synthesis transport. -/
def hbXiPeierlsUnitSourceFERieszTransportedBetaBlock
    (q : XiZeroCopy) (U : E ≃L[ℂ] F) : F →L[ℂ] F :=
  U.toContinuousLinearMap ∘L
    (hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q • ContinuousLinearMap.id ℂ E) ∘L
      U.symm.toContinuousLinearMap

/-- Riesz transport cannot change the exact partner-vacuum Hilbert--Schmidt classification. -/
theorem hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_partnerNumber_eq_zero
    (b : HilbertBasis ℕ ℂ E) (q : XiZeroCopy) (U : E ≃L[ℂ] F) :
    ContinuousLinearMap.IsHilbertSchmidt
        (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock q U) ↔
      hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 := by
  rw [hbXiPeierlsUnitSourceFERieszTransportedBetaBlock,
    isHilbertSchmidt_similarity_iff, isHilbertSchmidt_smul_id_iff b,
    hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_eq_zero_iff_partnerNumber_eq_zero]

/-- Every bounded Riesz realization is Hilbert--Schmidt exactly on the critical wall. -/
theorem hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_re_eq_half
    (b : HilbertBasis ℕ ℂ E) (q : XiZeroCopy) (U : E ≃L[ℂ] F) :
    ContinuousLinearMap.IsHilbertSchmidt
        (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock q U) ↔
      (q.1 : ℂ).re = 1 / 2 :=
  (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_partnerNumber_eq_zero
      b q U).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q)

/-- No bounded Riesz change of basis hides an off-wall source-FE beta obstruction. -/
theorem not_hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_of_offWall
    (b : HilbertBasis ℕ ℂ E) (q : XiZeroCopy) (U : E ≃L[ℂ] F)
    (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ ContinuousLinearMap.IsHilbertSchmidt
        (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock q U) :=
  (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_re_eq_half
    b q U).not.mpr hq

/-- Even an arbitrary Xi-dependent family of bounded Riesz transports is globally
Hilbert--Schmidt exactly under RH. -/
theorem forall_hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_rh
    (b : HilbertBasis ℕ ℂ E) (U : XiZeroCopy → E ≃L[ℂ] F) :
    (∀ q : XiZeroCopy,
      ContinuousLinearMap.IsHilbertSchmidt
        (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock q (U q))) ↔
      RiemannHypothesis := by
  rw [← forall_hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_rh]
  exact forall_congr' fun q =>
    hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_partnerNumber_eq_zero
      b q (U q)

/-- The Riesz-robust local Shale endpoint is HB canonical optical darkness. -/
theorem hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_opticalPower_zero
    (b : HilbertBasis ℕ ℂ E) (U : E ≃L[ℂ] F) (n : ℕ) (q : XiZeroCopy) :
    ContinuousLinearMap.IsHilbertSchmidt
        (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock q U) ↔
      hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 :=
  (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_partnerNumber_eq_zero
    b q U).trans
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_opticalPower_zero n q)

/-- The Riesz-robust local Shale endpoint is Deninger reflect-gauge Ward cancellation. -/
theorem hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_sharedWardCharge_zero
    (b : HilbertBasis ℕ ℂ E) (U : E ≃L[ℂ] F) (n : ℕ) (q : XiZeroCopy) :
    ContinuousLinearMap.IsHilbertSchmidt
        (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock q U) ↔
      fzzCigarParityDeningerReflectGaugeWardCharge q = 0 :=
  (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_partnerNumber_eq_zero
    b q U).trans
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_sharedWardCharge_zero n q)

/-- The Riesz-robust local Shale endpoint is FZZ-P information equilibrium. -/
theorem hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_informationForce_zero
    (b : HilbertBasis ℕ ℂ E) (U : E ≃L[ℂ] F) (n : ℕ) (q : XiZeroCopy) :
    ContinuousLinearMap.IsHilbertSchmidt
        (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock q U) ↔
      fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re = 0 :=
  (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_partnerNumber_eq_zero
    b q U).trans
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_informationForce_zero n q)

/-- The Riesz-robust local Shale endpoint is every-grade PW-B balance. -/
theorem hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_pwBalance_zero
    (b : HilbertBasis ℕ ℂ E) (U : E ≃L[ℂ] F) (n : ℕ) (q : XiZeroCopy) (k : ℕ) :
    ContinuousLinearMap.IsHilbertSchmidt
        (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock q U) ↔
      schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k = 0 :=
  (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_partnerNumber_eq_zero
    b q U).trans
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_pwBalance_zero n q k)

/-- On the canonical divisor copy, the Riesz-robust Shale endpoint is RBH leading balance. -/
theorem hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_firstCopy_isHilbertSchmidt_iff_rbhBalance_zero
    (b : HilbertBasis ℕ ℂ E) (U : E ≃L[ℂ] F) (n : ℕ) (rho : XiDivisorSupport) :
    ContinuousLinearMap.IsHilbertSchmidt
        (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock
          (reflectedBiHeatFirstDivisorCopy rho) U) ↔
      reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 :=
  (hbXiPeierlsUnitSourceFERieszTransportedBetaBlock_isHilbertSchmidt_iff_partnerNumber_eq_zero
    b (reflectedBiHeatFirstDivisorCopy rho) U).trans
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_firstCopy_eq_zero_iff_rbhBalance_zero n rho)

end

end RHTower

