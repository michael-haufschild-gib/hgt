import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTBranchChargeNoGo
import GaloisForLFunctions.RHTower.FZZCigarParityFixedSupportQuillenReplicaNoGo

/-!
# FZZ separation-kinematic support radial blindness

Hikida--Schomerus' higher-genus separation of variables, arXiv:0805.3931,
(C.11)--(C.13), determines the moving zeros and Abel--Jacobi twist from
`μ,z,λ,ϖ,u,y,E,σ,ξ,S,g`; radial spin `j` is absent.  The complete change-of-variables
Jacobian (4.18)/(C.18) is likewise a prime-form function of those kinematic data and
contains no `j`.  Radial spin first returns through the Liouville vertex weights in (4.17).

We encode the entire pre-correlator support path and its full Jacobian/prime-form signature,
not a finite sample.  Every postprocessing of that complete record is constant along the
physical radial family `j(P)=-1/2+iP`, so no predicate of it can select `P=0`.  This kills

`pre-correlator support motion/Jacobian → replica-area Ward law → divisor-mode passivity
  → Mellin completeness → RH`.

The positive survivor is exact: adjoining the charge-even external-BRST log-modulus from
`FZZCigarParityExternalBRSTBranchChargeNoGo` makes the signature injective in `P` for every
physical level `k>2`.  Thus a viable FZZ-P producer must use correlator/modulus weighting,
not separation kinematics alone.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Complete pre-correlator separation record along a replica/twist path.  The first field
contains the whole moving divisor, not fixed support; the second may contain the complete
prime-form, theta, ghost-determinant, and Jacobian output of (4.18)/(C.18). -/
structure FZZTorusPreCorrelatorSeparationKinematics where
  supportMotion : ℂ → FZZTorusReplicaAbelData
  jacobianPrimeFormSignature : ℂ → ℂ

/-- The (C.11)--(C.18) separation signature has no radial-spin argument. -/
def fzzTorusPreCorrelatorSeparationSignature
    (K : FZZTorusPreCorrelatorSeparationKinematics) (_radialMomentum : ℝ) :
    FZZTorusPreCorrelatorSeparationKinematics :=
  K

@[simp]
theorem fzzTorusPreCorrelatorSeparationSignature_eq
    (K : FZZTorusPreCorrelatorSeparationKinematics) (radialMomentum : ℝ) :
    fzzTorusPreCorrelatorSeparationSignature K radialMomentum = K := by
  rfl

/-- Every postprocessing of the complete separation record is radial-spin blind. -/
theorem fzzTorusPreCorrelatorSeparation_postprocess_constant
    {A : Type*} (K : FZZTorusPreCorrelatorSeparationKinematics)
    (observable : FZZTorusPreCorrelatorSeparationKinematics → A)
    (P Q : ℝ) :
    observable (fzzTorusPreCorrelatorSeparationSignature K P) =
      observable (fzzTorusPreCorrelatorSeparationSignature K Q) := by
  rfl

/-- No predicate of any postprocessing of complete separation kinematics selects `P=0`. -/
theorem not_fzzTorusPreCorrelatorSeparation_postprocess_radialSelector
    {A : Type*} (K : FZZTorusPreCorrelatorSeparationKinematics)
    (observable : FZZTorusPreCorrelatorSeparationKinematics → A)
    (predicate : A → Prop) :
    ¬ ∀ radialMomentum : ℝ,
      predicate (observable
        (fzzTorusPreCorrelatorSeparationSignature K radialMomentum)) ↔
          radialMomentum = 0 := by
  intro h
  have h0 : predicate (observable
      (fzzTorusPreCorrelatorSeparationSignature K 0)) :=
    (h 0).mpr rfl
  have h1 : predicate (observable
      (fzzTorusPreCorrelatorSeparationSignature K 1)) := by
    rw [fzzTorusPreCorrelatorSeparation_postprocess_constant K observable 1 0]
    exact h0
  exact one_ne_zero ((h 1).mp h1)

/-- Physical radial spin `j=-1/2+iP`. -/
def fzzCigarPhysicalRadialLabel (radialMomentum : ℝ) : ℂ :=
  -(1 : ℂ) / 2 + (radialMomentum : ℂ) * I

/-- Kinematic record enriched by the source-exact charge-even external-BRST modulus. -/
def fzzTorusSeparationKinematicModulusSignature
    (k : ℝ) (p ν : ℤ) (K : FZZTorusPreCorrelatorSeparationKinematics)
    (radialMomentum : ℝ) :
    FZZTorusPreCorrelatorSeparationKinematics × ℂ :=
  (K, fzzCigarExternalBRSTEvenLogModulusMean k
    (fzzCigarPhysicalRadialLabel radialMomentum) p ν)

/-- The modulus-enriched signature reconstructs and separates physical radial momentum. -/
theorem fzzTorusSeparationKinematicModulusSignature_injective
    {k : ℝ} (hk : 2 < k) (p ν : ℤ)
    (K : FZZTorusPreCorrelatorSeparationKinematics) :
    Function.Injective
      (fzzTorusSeparationKinematicModulusSignature k p ν K) := by
  intro P Q hPQ
  have hmod :
      fzzCigarExternalBRSTEvenLogModulusMean k
          (fzzCigarPhysicalRadialLabel P) p ν =
        fzzCigarExternalBRSTEvenLogModulusMean k
          (fzzCigarPhysicalRadialLabel Q) p ν :=
    congrArg Prod.snd hPQ
  have hj : fzzCigarPhysicalRadialLabel P =
      fzzCigarPhysicalRadialLabel Q := by
    calc
      fzzCigarPhysicalRadialLabel P =
          -(fzzCigarReplicaRadialDenominator k / 2) *
            fzzCigarExternalBRSTEvenLogModulusMean k
              (fzzCigarPhysicalRadialLabel P) p ν :=
        (fzzCigarExternalBRSTEvenLogModulusMean_reconstructs_radialLabel
          hk (fzzCigarPhysicalRadialLabel P) p ν).symm
      _ = -(fzzCigarReplicaRadialDenominator k / 2) *
            fzzCigarExternalBRSTEvenLogModulusMean k
              (fzzCigarPhysicalRadialLabel Q) p ν := by rw [hmod]
      _ = fzzCigarPhysicalRadialLabel Q :=
        fzzCigarExternalBRSTEvenLogModulusMean_reconstructs_radialLabel
          hk (fzzCigarPhysicalRadialLabel Q) p ν
  have him := congrArg Complex.im hj
  simpa [fzzCigarPhysicalRadialLabel] using him

/-- Closed class-level route kill and its sharp radial-sensitive survivor. -/
def FZZTorusSeparationKinematicSupportRadialBlindnessNoGo : Prop :=
  (∀ (K : FZZTorusPreCorrelatorSeparationKinematics) (P Q : ℝ),
      fzzTorusPreCorrelatorSeparationSignature K P =
        fzzTorusPreCorrelatorSeparationSignature K Q) ∧
    (∀ {A : Type*} (K : FZZTorusPreCorrelatorSeparationKinematics)
        (observable : FZZTorusPreCorrelatorSeparationKinematics → A)
        (predicate : A → Prop),
      ¬ ∀ radialMomentum : ℝ,
        predicate (observable
          (fzzTorusPreCorrelatorSeparationSignature K radialMomentum)) ↔
            radialMomentum = 0) ∧
    ∀ (k : ℝ), 2 < k → ∀ (p ν : ℤ)
      (K : FZZTorusPreCorrelatorSeparationKinematics),
      Function.Injective
        (fzzTorusSeparationKinematicModulusSignature k p ν K)

theorem fzzTorusSeparationKinematicSupportRadialBlindness_noGo :
    FZZTorusSeparationKinematicSupportRadialBlindnessNoGo := by
  refine ⟨?_, ?_, ?_⟩
  · intro K P Q
    rfl
  · intro A K observable predicate
    exact not_fzzTorusPreCorrelatorSeparation_postprocess_radialSelector
      K observable predicate
  · intro k hk p ν K
    exact fzzTorusSeparationKinematicModulusSignature_injective hk p ν K

end

end GaloisForLFunctions.RHTower
