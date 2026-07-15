import GaloisForLFunctions.HTGeometry.UniversalProjectiveConstraintRealization
import Mathlib.Topology.ClusterPt

/-!
# Compact tail-dense constraint kernels

A profile is tail-dense on a constraint set when its range lies in that set and every constraint
point is a cluster point after deleting an arbitrary finite set of coordinates. For continuous
observables, finite-support vanishing along such a profile is exactly vanishing on the full
constraint set.

This removes the exact repeated-fibre hypothesis from the static valuation--Hilbert theorem. The
profile may be injective: topological recurrence alone makes its finite-support quotient recover
the prescribed reduced constraint geometry.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology MvPolynomial

noncomputable section

/-- The profile lies in `K`, and every point of `K` remains a cluster point after every finite
deletion of coordinates. On an infinite ordered coordinate set this says that every tail is dense
in `K`. -/
def CofiniteTailDenseOn {P V : Type*} [TopologicalSpace V]
    (x : P → V) (K : Set V) : Prop :=
  Set.range x ⊆ K ∧ ∀ v ∈ K, MapClusterPt v cofinite x

/-- A convergent map into a Hausdorff space has no cluster point other than its limit. -/
theorem mapClusterPt_eq_of_tendsto
    {P V : Type*} [TopologicalSpace V] [T2Space V]
    {F : Filter P} {x : P → V} {a b : V}
    (ha : MapClusterPt a F x) (hb : Tendsto x F (𝓝 b)) : a = b := by
  let G : Filter V := 𝓝 a ⊓ Filter.map x F
  haveI : NeBot G := ha.clusterPt
  exact tendsto_nhds_unique (f := id) (l := G)
    (tendsto_id.mono_left inf_le_left)
    (tendsto_id.mono_left (inf_le_right.trans hb))

/-- **Continuous tail-detection law.** Along a cofinally tail-dense profile, a continuous complex
observable is nonzero at only finitely many coordinates exactly when it vanishes on the complete
constraint set. -/
theorem cofiniteTailDenseOn_continuous_support_finite_iff
    {P V : Type*} [TopologicalSpace V]
    (x : P → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : V → ℂ) (hf : Continuous f) :
    {p | f (x p) ≠ 0}.Finite ↔ ∀ v ∈ K, f v = 0 := by
  constructor
  · intro hsupp v hv
    have heq : (f ∘ x) =ᶠ[cofinite] (fun _ : P => 0) := by
      filter_upwards [hsupp.eventually_cofinite_notMem] with p hp
      exact not_ne_iff.mp hp
    have hlim : Tendsto (f ∘ x) cofinite (𝓝 0) :=
      tendsto_const_nhds.congr' heq.symm
    have hcluster : MapClusterPt (f v) cofinite (f ∘ x) :=
      (hx.2 v hv).continuousAt_comp hf.continuousAt
    exact mapClusterPt_eq_of_tendsto hcluster hlim
  · intro hvanish
    have hzero : ∀ p, f (x p) = 0 := by
      intro p
      exact hvanish (x p) (hx.1 ⟨p, rfl⟩)
    simp [hzero]

/-- Polynomial specialization of continuous tail detection. -/
theorem cofiniteTailDenseOn_mvPolynomial_eval_support_finite_iff
    {P σ : Type*} [Fintype σ]
    (x : P → σ → ℂ) (K : Set (σ → ℂ)) (hx : CofiniteTailDenseOn x K)
    (Q : MvPolynomial σ ℂ) :
    {p | eval (x p) Q ≠ 0}.Finite ↔ ∀ v ∈ K, eval v Q = 0 := by
  exact cofiniteTailDenseOn_continuous_support_finite_iff x K hx
    (fun v => eval v Q) (MvPolynomial.continuous_eval Q)

/-- **Tail-dense homogeneous kernel.** Exact repeated coefficient fibres are unnecessary: every
homogeneous finite-support relation of a tail-dense profile is precisely a polynomial relation of
the full constraint geometry. -/
theorem homogeneousTailRelationSubmodule_eq_constraintVanishing_of_cofiniteTailDenseOn
    {P σ : Type*} [Fintype σ]
    (x : P → σ → ℂ) (K : Set (σ → ℂ)) (hx : CofiniteTailDenseOn x K) (m : ℕ) :
    homogeneousTailRelationSubmodule x m =
      homogeneousConstraintVanishingSubmodule K m := by
  ext Q
  exact cofiniteTailDenseOn_mvPolynomial_eval_support_finite_iff x K hx Q.1

/-- The valuation-tail Hilbert function of a tail-dense profile is exactly the homogeneous
coordinate Hilbert function of its constraint set. -/
theorem valuationTailHilbertFunction_eq_constraintHomogeneousHilbertFunction_of_cofiniteTailDenseOn
    {P σ : Type*} [Fintype σ]
    (x : P → σ → ℂ) (K : Set (σ → ℂ)) (hx : CofiniteTailDenseOn x K) (m : ℕ) :
    valuationTailHilbertFunction x m = constraintHomogeneousHilbertFunction K m := by
  unfold valuationTailHilbertFunction constraintHomogeneousHilbertFunction
  rw [homogeneousTailRelationSubmodule_eq_constraintVanishing_of_cofiniteTailDenseOn x K hx m]

/-- **Continuous corona-rank law.** A finite family of continuous observables is independent
modulo finite coordinate support exactly when its restrictions to the tail-dense constraint set
are linearly independent. -/
theorem cofiniteTailDenseOn_tailCoefficientIndependent_iff
    {P V J : Type*} [TopologicalSpace V] [Fintype J]
    (x : P → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j)) :
    TailCoefficientIndependent (fun j p => f j (x p)) ↔
      LinearIndependent ℂ (fun j => fun v : K => f j v.1) := by
  classical
  constructor
  · intro htail
    rw [Fintype.linearIndependent_iff]
    intro c hsum
    have hsupp : {p | ∑ j, c j * f j (x p) ≠ 0}.Finite := by
      have hzero : ∀ p, ∑ j, c j * f j (x p) = 0 := by
        intro p
        have hp := congrFun hsum ⟨x p, hx.1 ⟨p, rfl⟩⟩
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hp
      simp [hzero]
    have hc := htail c hsupp
    intro j
    exact congrFun hc j
  · intro hlinear c hsupp
    rw [Fintype.linearIndependent_iff] at hlinear
    let F : V → ℂ := fun v => ∑ j, c j * f j v
    have hF : Continuous F := by
      fun_prop
    have hvanish : ∀ v ∈ K, F v = 0 :=
      (cofiniteTailDenseOn_continuous_support_finite_iff x K hx F hF).mp hsupp
    have hsum : (∑ j, c j • (fun v : K => f j v.1)) = 0 := by
      funext v
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, F] using hvanish v.1 v.2
    have hc := hlinear c hsum
    funext j
    exact hc j

end

end GaloisForLFunctions.HTGeometry
