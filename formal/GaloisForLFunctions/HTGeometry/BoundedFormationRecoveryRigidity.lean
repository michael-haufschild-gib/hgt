import GaloisForLFunctions.HTGeometry.CanonicalFormationGraphCodiagonalFracture

/-!
# Bounded formation--recovery rigidity

Every algebraic response that factors through bounded formation and bounded recovery is
sequentially closable. A constant codiagonal therefore cannot admit such a factorization on any
complex normed space unless its coefficient vanishes. This closes the graph-gauge loophole
sharply: the existing `(n+1)` formation loading can regularize a nonzero codiagonal only because
that load is unbounded in the base `ell^(2 : ℕ)` gauge.

No Xi zero, RH assumption, numerical computation, or project axiom is used.
-/

open Filter Topology
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Bounded factorization law.** Any algebraic response recovered through bounded ingress and
bounded egress is sequentially closable in the source topology. -/
theorem isSequentiallyClosableBetween_of_bounded_factorization
    {D E F K : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (T : D →ₗ[ℝ] K) (j : D →ₗ[ℝ] E)
    (load : E →L[ℝ] F) (recover : F →L[ℝ] K)
    (hfactor : ∀ x : D, recover (load (j x)) = T x) :
    RHTower.IsSequentiallyClosableBetween T j := by
  intro u hu y hy
  have hzero : Tendsto (fun n => recover (load (j (u n)))) atTop (nhds 0) := by
    have hcontinuous := ((recover.comp load).continuous.tendsto 0).comp hu
    convert hcontinuous using 1
    · funext n
      rfl
    · simp
  have hresponse : Tendsto (fun n => T (u n)) atTop (nhds 0) := by
    convert hzero using 1
    funext n
    exact (hfactor (u n)).symm
  exact tendsto_nhds_unique hy hresponse

/-- **Bounded-coboundary invariance.** Adding any bounded response of the completed source does not
change the sequential-closability class of an algebraic response. -/
theorem isSequentiallyClosableBetween_add_boundedFactor_iff
    {D E K : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (T : D →ₗ[ℝ] K) (j : D →ₗ[ℝ] E) (B : E →L[ℝ] K) :
    RHTower.IsSequentiallyClosableBetween (T + B.toLinearMap.comp j) j ↔
      RHTower.IsSequentiallyClosableBetween T j := by
  constructor
  · intro hclose u hu y hy
    have hbounded : Tendsto (fun n => B (j (u n))) atTop (nhds 0) := by
      have hcontinuous := (B.continuous.tendsto 0).comp hu
      convert hcontinuous using 1
      · funext n
        rfl
      · simp
    have hsum : Tendsto
        (fun n => (T + B.toLinearMap.comp j) (u n)) atTop (nhds y) := by
      convert hy.add hbounded using 1
      · funext n
        rfl
      · simp
    exact hclose u hu y hsum
  · intro hclose u hu y hy
    have hbounded : Tendsto (fun n => B (j (u n))) atTop (nhds 0) := by
      have hcontinuous := (B.continuous.tendsto 0).comp hu
      convert hcontinuous using 1
      · funext n
        rfl
      · simp
    have hT : Tendsto (fun n => T (u n)) atTop (nhds y) := by
      have hdiff := hy.sub hbounded
      convert hdiff using 1
      · funext n
        simp
      · simp
    exact hclose u hu y hT

/-- A constant codiagonal that factors through bounded formation and bounded recovery has zero
coefficient. The intermediate formation space is arbitrary. -/
theorem boundedFormationRecovery_constantCodiagonal_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (load : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E)
    (recover : E →L[ℂ] ℂ)
    (c : ℂ)
    (hrec : ∀ x : ℕ →₀ ℂ,
      recover (load (RHTower.codiagEmbed x)) =
        RHTower.codiag (fun _ : ℕ => c) x) :
    c = 0 := by
  apply (constantCodiagonal_closable_iff c).1
  intro u hu y hy
  change Tendsto (fun n => RHTower.codiagEmbed (u n)) atTop (nhds 0) at hu
  have hzero : Tendsto
      (fun n => recover (load (RHTower.codiagEmbed (u n))))
      atTop (nhds 0) := by
    have hcontinuous := ((recover.comp load).continuous.tendsto 0).comp hu
    convert hcontinuous using 1
    · funext n
      rfl
    · simp
  have hresponse : Tendsto
      (fun n => ((RHTower.codiag (H := ℂ) (fun _ => c)).restrictScalars ℝ) (u n))
      atTop (nhds 0) := by
    convert hzero using 1
    funext n
    exact (hrec (u n)).symm
  exact tendsto_nhds_unique hy hresponse

/-- Closed formulation of the bounded formation--recovery rigidity law. -/
def BoundedFormationRecoveryRigidityLaw : Prop :=
  ∀ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℂ E)
    (load : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E)
    (recover : E →L[ℂ] ℂ) (c : ℂ),
    (∀ x : ℕ →₀ ℂ,
      recover (load (RHTower.codiagEmbed x)) =
        RHTower.codiag (fun _ : ℕ => c) x) →
      c = 0

/-- Zero-argument certificate: bounded ingress and bounded egress cannot transport a nonzero
constant cofinal anomaly. -/
theorem boundedFormationRecoveryRigidityLaw :
    BoundedFormationRecoveryRigidityLaw := by
  intro E instNormed instSpace
  letI : NormedAddCommGroup E := instNormed
  letI : NormedSpace ℂ E := instSpace
  intro load recover c hrec
  exact boundedFormationRecovery_constantCodiagonal_eq_zero load recover c hrec

end

end GaloisForLFunctions.HTGeometry
