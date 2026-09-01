import GaloisForLFunctions.HTGeometry.FZZCigarWorldsheetDivisorGenusLock

/-!
# FZZ fixed-support Abel--Jacobi/Quillen replica no-go

The remaining FZZ-P source edge asks the literal fractional-winding replica-area response to be
passive on every parity-Mellin divisor mode.  That premise is already equivalent to RH in
`FZZCigarParityLinearReplicaAreaHolonomySelector`.

This file closes the proposed fixed-support Quillen branch of that edge.  Two source formulas are
decisive:

* Hikida--Schomerus, arXiv:0805.3931, (C.12), makes the genus-one `βγ` holonomy an Abel--Jacobi
  function of divisor **support**.
* Halder--Jafferis, arXiv:2402.00932v3, (3.29)--(3.33), obtains the area insertion by changing the
  winding **charge** at fixed insertion support.

Hence the replica direction does not move the Abel--Jacobi holonomy.  If a torus amplitude is a
separated sum `replicaLog δ + quillenLog λ`, replica subtraction cancels the entire Quillen term.
If it is a separated product `replicaFactor δ * quillenFactor λ`, replica division cancels the
entire Quillen factor.  Both statements hold for arbitrary functions; no regularity, theta-product
formula, or determinant evaluation is used.

Every complex holonomy is realized by explicit neutral genus-one divisor data.  Therefore no
predicate of either normalized response can select `Im λ = 0`.  Fixed-support log-circle averages,
Quillen norms, determinant ratios, and universal replica counterterms are receivers, not the
missing FZZ-P producer.

The strongest positive survivor is a sharp mixed-coupling requirement: any viable torus producer
must make the replica deformation move divisor support or enter a nonseparable prime-form/OPE
branch term before Jacobian integration.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Genus-one FZZ divisor support together with the fractional-winding replica deficit. -/
structure FZZTorusReplicaAbelData where
  spectralFlowMultiplicity : ℕ
  spectralFlowPoint : ℂ
  residualZeros : List ℂ
  radiationPoles : List ℂ
  riemannConstant : ℂ
  replicaDeficit : ℂ

/-- Torus divisor neutrality `M + S = N`. -/
def FZZTorusReplicaAbelData.Neutral (d : FZZTorusReplicaAbelData) : Prop :=
  d.residualZeros.length + d.spectralFlowMultiplicity = d.radiationPoles.length

/-- Change only winding charge, represented by the replica deficit, while keeping divisor support
fixed. -/
def FZZTorusReplicaAbelData.withReplicaDeficit
    (d : FZZTorusReplicaAbelData) (replicaDeficit : ℂ) : FZZTorusReplicaAbelData :=
  { d with replicaDeficit := replicaDeficit }

/-- Genus-one specialization of the Abel--Jacobi constraint (Hikida--Schomerus C.12), after
torus neutrality cancels the base-point coefficient. -/
def fzzTorusAbelJacobiTwist (d : FZZTorusReplicaAbelData) : ℂ :=
  (d.spectralFlowMultiplicity : ℂ) * d.spectralFlowPoint + d.residualZeros.sum -
    d.radiationPoles.sum - 2 * d.riemannConstant

@[simp]
theorem FZZTorusReplicaAbelData.neutral_withReplicaDeficit
    (d : FZZTorusReplicaAbelData) (replicaDeficit : ℂ) :
    (d.withReplicaDeficit replicaDeficit).Neutral ↔ d.Neutral := by
  rfl

/-- **Charge/support separation.** Fractional-winding deformation at fixed support leaves the
genus-one Abel--Jacobi holonomy exactly fixed. -/
@[simp]
theorem fzzTorusAbelJacobiTwist_withReplicaDeficit
    (d : FZZTorusReplicaAbelData) (replicaDeficit : ℂ) :
    fzzTorusAbelJacobiTwist (d.withReplicaDeficit replicaDeficit) =
      fzzTorusAbelJacobiTwist d := by
  rfl

/-- Every complex torus twist is represented by neutral fixed-support divisor data: one residual
zero at the twist and one radiation pole at the origin. -/
def fzzCanonicalNeutralAbelData (twist replicaDeficit : ℂ) : FZZTorusReplicaAbelData where
  spectralFlowMultiplicity := 0
  spectralFlowPoint := 0
  residualZeros := [twist]
  radiationPoles := [0]
  riemannConstant := 0
  replicaDeficit := replicaDeficit

@[simp]
theorem fzzCanonicalNeutralAbelData_neutral (twist replicaDeficit : ℂ) :
    (fzzCanonicalNeutralAbelData twist replicaDeficit).Neutral := by
  simp [FZZTorusReplicaAbelData.Neutral, fzzCanonicalNeutralAbelData]

@[simp]
theorem fzzTorusAbelJacobiTwist_canonical (twist replicaDeficit : ℂ) :
    fzzTorusAbelJacobiTwist (fzzCanonicalNeutralAbelData twist replicaDeficit) = twist := by
  simp [fzzTorusAbelJacobiTwist, fzzCanonicalNeutralAbelData]

/-- Additively separated logarithmic determinant/free-energy amplitude. -/
def fzzFixedSupportQuillenLogAmplitude
    (replicaLog quillenLog : ℂ → ℂ) (d : FZZTorusReplicaAbelData) : ℂ :=
  replicaLog d.replicaDeficit + quillenLog (fzzTorusAbelJacobiTwist d)

/-- Replica-normalized logarithmic response at fixed divisor support. -/
def fzzFixedSupportQuillenLogNormalizedResponse
    (replicaLog quillenLog : ℂ → ℂ) (d : FZZTorusReplicaAbelData)
    (replicaDeficit : ℂ) : ℂ :=
  fzzFixedSupportQuillenLogAmplitude replicaLog quillenLog
      (d.withReplicaDeficit replicaDeficit) -
    fzzFixedSupportQuillenLogAmplitude replicaLog quillenLog
      (d.withReplicaDeficit 0)

/-- **Additive cancellation law.** Fixed-support replica normalization removes every Abel--Jacobi
log-circle/Quillen term. -/
theorem fzzFixedSupportQuillenLogNormalizedResponse_eq
    (replicaLog quillenLog : ℂ → ℂ) (d : FZZTorusReplicaAbelData)
    (replicaDeficit : ℂ) :
    fzzFixedSupportQuillenLogNormalizedResponse replicaLog quillenLog d replicaDeficit =
      replicaLog replicaDeficit - replicaLog 0 := by
  unfold fzzFixedSupportQuillenLogNormalizedResponse
  unfold fzzFixedSupportQuillenLogAmplitude
  rw [fzzTorusAbelJacobiTwist_withReplicaDeficit,
    fzzTorusAbelJacobiTwist_withReplicaDeficit]
  simp [FZZTorusReplicaAbelData.withReplicaDeficit]

/-- No predicate of a fixed-support separated log-Quillen response selects zero radial twist. -/
theorem not_fzzFixedSupportQuillenLogNormalizedResponse_value_selector
    (replicaLog quillenLog : ℂ → ℂ) (replicaDeficit : ℂ) (P : ℂ → Prop) :
    ¬ ∀ twist : ℂ,
      P (fzzFixedSupportQuillenLogNormalizedResponse replicaLog quillenLog
          (fzzCanonicalNeutralAbelData twist 0) replicaDeficit) ↔ twist.im = 0 := by
  intro h
  have hzero := (h 0).mpr (by norm_num)
  have hI : P (fzzFixedSupportQuillenLogNormalizedResponse replicaLog quillenLog
      (fzzCanonicalNeutralAbelData Complex.I 0) replicaDeficit) := by
    rw [fzzFixedSupportQuillenLogNormalizedResponse_eq]
    rw [fzzFixedSupportQuillenLogNormalizedResponse_eq] at hzero
    exact hzero
  have := (h Complex.I).mp hI
  norm_num at this

/-- No choice of replica point and no scalar predicate repairs the separated log-Quillen branch. -/
theorem not_exists_fzzFixedSupportQuillenLogNormalizedResponse_value_selector
    (replicaLog quillenLog : ℂ → ℂ) :
    ¬ ∃ (replicaDeficit : ℂ) (P : ℂ → Prop), ∀ twist : ℂ,
      P (fzzFixedSupportQuillenLogNormalizedResponse replicaLog quillenLog
          (fzzCanonicalNeutralAbelData twist 0) replicaDeficit) ↔ twist.im = 0 := by
  rintro ⟨replicaDeficit, P, h⟩
  exact not_fzzFixedSupportQuillenLogNormalizedResponse_value_selector
    replicaLog quillenLog replicaDeficit P h

/-- Multiplicatively separated determinant amplitude in an arbitrary group.  A group-valued
formulation makes nonvanishing intrinsic and avoids analytic side conditions on determinant ratios. -/
def fzzFixedSupportQuillenRatioAmplitude {G : Type*} [Group G]
    (replicaFactor : ℂ → G) (quillenFactor : ℂ → G)
    (d : FZZTorusReplicaAbelData) : G :=
  replicaFactor d.replicaDeficit * quillenFactor (fzzTorusAbelJacobiTwist d)

/-- Replica-normalized determinant ratio at fixed divisor support. -/
def fzzFixedSupportQuillenRatioNormalizedResponse {G : Type*} [Group G]
    (replicaFactor : ℂ → G) (quillenFactor : ℂ → G)
    (d : FZZTorusReplicaAbelData) (replicaDeficit : ℂ) : G :=
  fzzFixedSupportQuillenRatioAmplitude replicaFactor quillenFactor
      (d.withReplicaDeficit replicaDeficit) *
    (fzzFixedSupportQuillenRatioAmplitude replicaFactor quillenFactor
      (d.withReplicaDeficit 0))⁻¹

/-- **Multiplicative cancellation law.** Fixed-support replica division removes every
Abel--Jacobi Quillen factor. -/
theorem fzzFixedSupportQuillenRatioNormalizedResponse_eq {G : Type*} [Group G]
    (replicaFactor : ℂ → G) (quillenFactor : ℂ → G)
    (d : FZZTorusReplicaAbelData) (replicaDeficit : ℂ) :
    fzzFixedSupportQuillenRatioNormalizedResponse replicaFactor quillenFactor d
        replicaDeficit =
      replicaFactor replicaDeficit * (replicaFactor 0)⁻¹ := by
  unfold fzzFixedSupportQuillenRatioNormalizedResponse
  unfold fzzFixedSupportQuillenRatioAmplitude
  rw [fzzTorusAbelJacobiTwist_withReplicaDeficit,
    fzzTorusAbelJacobiTwist_withReplicaDeficit]
  simp [FZZTorusReplicaAbelData.withReplicaDeficit]

/-- No predicate of a fixed-support separated Quillen ratio selects zero radial twist. -/
theorem not_fzzFixedSupportQuillenRatioNormalizedResponse_value_selector
    {G : Type*} [Group G]
    (replicaFactor : ℂ → G) (quillenFactor : ℂ → G)
    (replicaDeficit : ℂ) (P : G → Prop) :
    ¬ ∀ twist : ℂ,
      P (fzzFixedSupportQuillenRatioNormalizedResponse replicaFactor quillenFactor
          (fzzCanonicalNeutralAbelData twist 0) replicaDeficit) ↔ twist.im = 0 := by
  intro h
  have hzero := (h 0).mpr (by norm_num)
  have hI : P (fzzFixedSupportQuillenRatioNormalizedResponse replicaFactor quillenFactor
      (fzzCanonicalNeutralAbelData Complex.I 0) replicaDeficit) := by
    rw [fzzFixedSupportQuillenRatioNormalizedResponse_eq]
    rw [fzzFixedSupportQuillenRatioNormalizedResponse_eq] at hzero
    exact hzero
  have := (h Complex.I).mp hI
  norm_num at this

/-- No replica point or scalar predicate repairs the separated determinant-ratio branch. -/
theorem not_exists_fzzFixedSupportQuillenRatioNormalizedResponse_value_selector
    {G : Type*} [Group G]
    (replicaFactor : ℂ → G) (quillenFactor : ℂ → G) :
    ¬ ∃ (replicaDeficit : ℂ) (P : G → Prop), ∀ twist : ℂ,
      P (fzzFixedSupportQuillenRatioNormalizedResponse replicaFactor quillenFactor
          (fzzCanonicalNeutralAbelData twist 0) replicaDeficit) ↔ twist.im = 0 := by
  rintro ⟨replicaDeficit, P, h⟩
  exact not_fzzFixedSupportQuillenRatioNormalizedResponse_value_selector
    replicaFactor quillenFactor replicaDeficit P h

end

end GaloisForLFunctions.RHTower
