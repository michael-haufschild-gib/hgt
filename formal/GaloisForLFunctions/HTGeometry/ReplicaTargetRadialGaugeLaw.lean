import GaloisForLFunctions.HTGeometry.ReturnExcisedMinimalIncidenceRankLaw
import GaloisForLFunctions.HTGeometry.ReplicaReturnShellCoareaIncidenceLaw

/-!
# Radial gauge of replica incidence

Nonzero rescaling of each occupied target changes neither its replica span
nor the return-excised incidence number and pair action. This holds at every
replica order, for arbitrary target families and source measures; excision
and all surviving source-sheet multiplicities are kept fixed.

Capture retains the missing radial information: fidelity scales by the
squared norm of the scalar. The existing return-shell reporter retains this
factor explicitly in its weights, raised to replica order. An exact
singleton example has incidence number and action one for every nonzero
scalar, including arbitrarily small target norms.

Thus residual norm suppression cannot be assigned to the unweighted
projection action. Direction changes, zero residuals, norm-weighted reporters
and changes to the source measure are distinct mechanisms. These projection
identities do not supply an ordinary-Hamiltonian incidence suppression bound.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry
noncomputable section


/-- Replica lifting is homogeneous of exactly the replica degree. -/
theorem finitePureTensorPowerEuclidean_smul
    {α : Type*} [Fintype α] (r : ℕ) (z : ℂ) (ψ : α → ℂ) :
    finitePureTensorPowerEuclidean r (z • ψ) =
      z ^ r • finitePureTensorPowerEuclidean r ψ := by
  ext x
  change (∏ j : Fin r, z * ψ (x j)) = z ^ r * ∏ j : Fin r, ψ (x j)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Arbitrary nonzero targetwise radial changes preserve the replica span,
including order zero and empty target families. -/
theorem replicaTargetSpan_units_smul
    {C α : Type*} [Fintype α] (r : ℕ)
    (target : C → α → ℂ) (a : C → ℂˣ) :
    replicaTargetSpan r (fun c => (a c : ℂ) • target c) =
      replicaTargetSpan r target := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨c, rfl⟩
    change finitePureTensorPowerEuclidean r ((a c : ℂ) • target c) ∈ _
    rw [finitePureTensorPowerEuclidean_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self c))
  · apply Submodule.span_le.mpr
    rintro v ⟨c, rfl⟩
    have hmem : finitePureTensorPowerEuclidean r ((a c : ℂ) • target c) ∈
        replicaTargetSpan r (fun c => (a c : ℂ) • target c) :=
      Submodule.subset_span (Set.mem_range_self c)
    have h := (replicaTargetSpan r (fun c => (a c : ℂ) • target c)).smul_mem
      (((a c : ℂ) ^ r)⁻¹) hmem
    rw [finitePureTensorPowerEuclidean_smul, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero r (a c).ne_zero), one_smul] at h
    exact h

/-- Projection action is projective in each occupied target, not sensitive
to its nonzero radial norm. -/
theorem replicaTargetProjectionMass_units_smul
    {C α : Type*} [Fintype α] (r : ℕ)
    (target : C → α → ℂ) (a : C → ℂˣ) (ψ : α → ℂ) :
    replicaTargetProjectionMass r (fun c => (a c : ℂ) • target c) ψ =
      replicaTargetProjectionMass r target ψ := by
  exact congrArg (fun S => replicaSubspaceProjectionMass r S ψ)
    (replicaTargetSpan_units_smul r target a)

/-- Source excision does not restore radial information lost by the target
span. All source points and fibre-sheet multiplicities stay fixed. -/
theorem returnExcisedReplicaIncidenceSpan_units_smul
    {X C α : Type*} [Fintype α] (r : ℕ)
    (target : C → α → ℂ) (a : C → ℂˣ) (state : X → α → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceSpan r (fun c => (a c : ℂ) • target c)
        state returnSet =
      returnExcisedReplicaIncidenceSpan r target state returnSet :=
  returnExcisedReplicaIncidenceSpan_eq_of_targetSpan_eq r _ _ state returnSet
    (replicaTargetSpan_units_smul r target a)

/-- Both factors of the incidence-normalized action are invariant under
nonzero targetwise scaling, for every replica order and every source measure. -/
theorem returnExcisedReplicaIncidence_radialGauge
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ) (a : C → ℂˣ)
    (state : X → α → ℂ) (returnSet : Set X) :
    returnExcisedReplicaIncidenceNumber r (fun c => (a c : ℂ) • target c)
        state returnSet =
      returnExcisedReplicaIncidenceNumber r target state returnSet ∧
    returnExcisedReplicaIncidenceAction μ r (fun c => (a c : ℂ) • target c)
        state returnSet =
      returnExcisedReplicaIncidenceAction μ r target state returnSet := by
  constructor
  · unfold returnExcisedReplicaIncidenceNumber
    rw [returnExcisedReplicaIncidenceSpan_units_smul r target a state returnSet]
  · unfold returnExcisedReplicaIncidenceAction
    rw [replicaTargetPairIncidenceKernel_eq_of_span_eq r _ target state
      (replicaTargetSpan_units_smul r target a)]

/-- Fidelity retains the radial factor that the occupied-span projection
forgets. No normalization of source or target is assumed. -/
theorem finitePureStateFidelity_radial_smul
    {α : Type*} [Fintype α] (ψ φ : α → ℂ) (z : ℂ) :
    finitePureStateFidelity ψ (z • φ) =
      ‖z‖ ^ (2 : ℕ) * finitePureStateFidelity ψ φ := by
  have hinner : finiteComplexInner ψ (z • φ) = z * finiteComplexInner ψ φ := by
    simp only [finiteComplexInner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_left_comm _ _ _
  simp only [finitePureStateFidelity, hinner, norm_mul, mul_pow]

/-- Transporting targetwise thresholds by the squared radial factors
compensates nonzero rescaling of the complete capture event exactly. -/
theorem completePureStateCapture_radialGauge
    {X C α : Type*} [Fintype α]
    (target : C → α → ℂ) (a : C → ℂˣ) (state : X → α → ℂ)
    (threshold : C → ℝ) :
    {x | ∃ c, ‖(a c : ℂ)‖ ^ (2 : ℕ) * threshold c ≤
        finitePureStateFidelity (state x) ((a c : ℂ) • target c)} =
      {x | ∃ c, threshold c ≤ finitePureStateFidelity (state x) (target c)} := by
  ext x
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, ?_⟩
  · rw [finitePureStateFidelity_radial_smul] at hc
    exact le_of_mul_le_mul_left hc (sq_pos_of_pos (norm_pos_iff.mpr (a c).ne_zero))
  · rw [finitePureStateFidelity_radial_smul]
    exact mul_le_mul_of_nonneg_left hc (sq_nonneg _)

/-- The existing shell reporter keeps radial suppression explicitly in its
weights. Its projection factors alone are invariant under the same scaling. -/
theorem replicaReturnShellProjectionMass_radialGauge
    {B α : Type*} [Fintype B] [Fintype α]
    (r : ℕ) (C : B → Type*) (target : ∀ b, C b → α → ℂ)
    (a : B → ℂˣ) (radius : B → ℝ) (ψ : α → ℂ) :
    replicaReturnShellProjectionMass r C
        (fun b c => (a b : ℂ) • target b c)
        (fun b => ‖(a b : ℂ)‖ ^ (2 : ℕ) * radius b) ψ =
      ∑ b, (‖(a b : ℂ)‖ ^ (2 : ℕ)) ^ r *
        (radius b ^ r * replicaTargetProjectionMass r (target b) ψ) := by
  simp only [replicaReturnShellProjectionMass, replicaTargetProjectionMass_units_smul,
    mul_pow, mul_assoc]

/-- A nondegenerate test of the distinction: for every nonzero scalar and
every replica order, a singleton source has incidence number and action one.
The target can have arbitrarily small nonzero norm without reducing either. -/
theorem singleton_returnExcisedReplicaIncidence_radialGauge
    (r : ℕ) (a : ℂˣ) :
    returnExcisedReplicaIncidenceNumber r
        (fun (_ : Unit) (_ : Unit) => (a : ℂ))
        (fun (_ : Unit) (_ : Unit) => (1 : ℂ)) ∅ = 1 ∧
    returnExcisedReplicaIncidenceAction (Measure.dirac ()) r
        (fun (_ : Unit) (_ : Unit) => (a : ℂ))
        (fun (_ : Unit) (_ : Unit) => (1 : ℂ)) ∅ = 1 := by
  classical
  let ψ : Unit → ℂ := fun _ => 1
  let target : Unit → Unit → ℂ := fun _ => ψ
  let state : Unit → Unit → ℂ := fun _ => ψ
  let v := finitePureTensorPowerEuclidean r ψ
  have hproj : (replicaTargetSpan r target).starProjection v = v :=
    Submodule.starProjection_eq_self_iff.mpr
      (Submodule.subset_span (Set.mem_range_self ()))
  have hnorm : ‖v‖ = 1 := norm_finitePureTensorPowerEuclidean_eq_one r ψ
    (by simp [ψ, finiteComplexInner])
  have hv : v ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hspan : returnExcisedReplicaIncidenceSpan r target state ∅ =
      Submodule.span ℂ {v} := by
    unfold returnExcisedReplicaIncidenceSpan
    congr 1
    ext w
    simp only [Set.mem_setOf_eq, Set.compl_empty, Set.mem_univ, true_and]
    change (∃ _ : Unit, w = (replicaTargetSpan r target).starProjection v) ↔ w ∈ {v}
    simp only [hproj, exists_const, Set.mem_singleton_iff]
  have hn : returnExcisedReplicaIncidenceNumber r target state ∅ = 1 := by
    rw [returnExcisedReplicaIncidenceNumber, hspan, finrank_span_singleton hv]
  have hk : replicaTargetPairIncidenceKernel r target state ((), ()) = 1 := by
    rw [replicaTargetPairIncidenceKernel,
      replicaSubspacePairIncidenceKernel_eq_norm_inner_projection]
    change ‖inner ℂ ((replicaTargetSpan r target).starProjection v)
      ((replicaTargetSpan r target).starProjection v)‖ ^ (2 : ℕ) = 1
    rw [hproj]
    change ‖inner ℂ (finitePureTensorPowerEuclidean r ψ)
      (finitePureTensorPowerEuclidean r ψ)‖ ^ (2 : ℕ) = 1
    rw [inner_finitePureTensorPowerEuclidean]
    simp [ψ, finiteComplexInner]
  have ha : returnExcisedReplicaIncidenceAction (Measure.dirac ()) r
      target state ∅ = 1 := by
    unfold returnExcisedReplicaIncidenceAction
    rw [Measure.dirac_prod_dirac]
    simpa only [Set.compl_empty, Set.univ_prod_univ, Measure.restrict_univ,
      integral_dirac] using hk
  have hg := returnExcisedReplicaIncidence_radialGauge
    (Measure.dirac ()) r target (fun _ => a) state ∅
  have hscaled : (fun c : Unit => (a : ℂ) • target c) =
      (fun (_ : Unit) (_ : Unit) => (a : ℂ)) := by
    funext c x
    exact mul_one (a : ℂ)
  rw [hscaled] at hg
  constructor
  · exact hg.1.trans hn
  · exact hg.2.trans ha

end
end GaloisForLFunctions.HTGeometry
