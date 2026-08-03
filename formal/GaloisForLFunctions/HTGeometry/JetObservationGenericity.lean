import GaloisForLFunctions.HTGeometry.PolynomialJetEscape
import GaloisForLFunctions.HTGeometry.SmallPerturbationReach

/-!
# Locally surjective observations make polynomial constraints generic

An observation of a parameter by finitely many complex coordinates which is continuous and carries
every neighbourhood onto a neighbourhood cannot be trapped in the zero set of a nonzero polynomial:
that zero set is closed and nowhere dense in coordinate space, and a neighbourhood of the observed
point escapes it.

Countably many such constraints therefore fail simultaneously on a residual set of parameters.  This
is the parameter-space half of a transversality argument, with the analytic work isolated in the
local surjectivity hypothesis.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An observation which carries neighbourhoods to neighbourhoods. -/
def LocallySurjectiveObservation {P : Type*} [TopologicalSpace P] {σ : Type*}
    (J : P → (σ → ℂ)) : Prop :=
  ∀ p : P, ∀ N ∈ nhds p, J '' N ∈ nhds (J p)

/-- **A locally surjective observation escapes every polynomial constraint.**  The parameters whose
observation lies on a fixed nonzero hypersurface form a closed nowhere dense set. -/
theorem isNowhereDense_setOf_eval_observation_eq_zero {P : Type*} [TopologicalSpace P]
    {σ : Type*} [Fintype σ] {J : P → (σ → ℂ)} (hJ : Continuous J)
    (hreach : LocallySurjectiveObservation J)
    {Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0) :
    IsNowhereDense {p : P | MvPolynomial.eval (J p) Q = 0} := by
  have hclosed : IsClosed {p : P | MvPolynomial.eval (J p) Q = 0} :=
    isClosed_singleton.preimage (Q.continuous_eval.comp hJ)
  rw [hclosed.isNowhereDense_iff, Set.eq_empty_iff_forall_notMem]
  intro p hp
  have hN : interior {p : P | MvPolynomial.eval (J p) Q = 0} ∈ nhds p :=
    isOpen_interior.mem_nhds hp
  have himg := hreach p _ hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himg
  obtain ⟨y, hyne, hyball⟩ := (mvPolynomial_nonzero_eval_dense Q hQ).exists_mem_open
    Metric.isOpen_ball ⟨J p, Metric.mem_ball_self hε⟩
  obtain ⟨p', hp', rfl⟩ := hball hyball
  have hmem : p' ∈ {p : P | MvPolynomial.eval (J p) Q = 0} := interior_subset hp'
  exact hyne hmem

/-- **Countably many polynomial constraints fail on a residual set.** -/
theorem residual_setOf_forall_eval_observation_ne_zero {P : Type*} [TopologicalSpace P]
    [BaireSpace P] {σ : Type*} [Fintype σ] {J : P → (σ → ℂ)} (hJ : Continuous J)
    (hreach : LocallySurjectiveObservation J) {ι : Type*} [Countable ι]
    (Q : ι → MvPolynomial σ ℂ) (hQ : ∀ i, Q i ≠ 0) :
    {p : P | ∀ i, MvPolynomial.eval (J p) (Q i) ≠ 0} ∈ residual P := by
  classical
  have hcompl : {p : P | ∀ i, MvPolynomial.eval (J p) (Q i) ≠ 0}ᶜ
      = ⋃ i, {p : P | MvPolynomial.eval (J p) (Q i) = 0} := by
    ext p
    simp [not_forall]
  have hmeagre : IsMeagre {p : P | ∀ i, MvPolynomial.eval (J p) (Q i) ≠ 0}ᶜ := by
    rw [hcompl]
    refine isMeagre_iUnion fun i => ?_
    exact (isNowhereDense_setOf_eval_observation_eq_zero hJ hreach (hQ i)).isMeagre
  rwa [IsMeagre, compl_compl] at hmeagre

/-- **The residual set is dense.**  A residual subset of a Baire space is dense. -/
theorem dense_setOf_forall_eval_observation_ne_zero {P : Type*} [TopologicalSpace P]
    [BaireSpace P] {σ : Type*} [Fintype σ] {J : P → (σ → ℂ)} (hJ : Continuous J)
    (hreach : LocallySurjectiveObservation J) {ι : Type*} [Countable ι]
    (Q : ι → MvPolynomial σ ℂ) (hQ : ∀ i, Q i ≠ 0) :
    Dense {p : P | ∀ i, MvPolynomial.eval (J p) (Q i) ≠ 0} :=
  dense_of_mem_residual
    (residual_setOf_forall_eval_observation_ne_zero hJ hreach Q hQ)

/-! ## Products of observations -/

/-- **A finite product of neighbourhood-preserving maps preserves neighbourhoods.**  On a finite
index every neighbourhood contains a box, and the product of the images of the box factors is again
a neighbourhood. -/
theorem pi_image_mem_nhds {ι : Type*} [Fintype ι] {X Y : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)] {f : ∀ i, X i → Y i}
    (x : ∀ i, X i) (hf : ∀ i, ∀ N ∈ nhds (x i), f i '' N ∈ nhds (f i (x i)))
    {N : Set (∀ i, X i)} (hN : N ∈ nhds x) :
    (fun v => fun i => f i (v i)) '' N ∈ nhds fun i => f i (x i) := by
  classical
  obtain ⟨W, hWN, hWopen, hxW⟩ := mem_nhds_iff.mp hN
  obtain ⟨U, hU, hUW⟩ := isOpen_pi_iff'.mp hWopen x hxW
  have hbox : (Set.univ.pi fun i => f i '' U i) ∈ nhds fun i => f i (x i) := by
    refine set_pi_mem_nhds Set.finite_univ fun i _ => ?_
    exact hf i (U i) ((hU i).1.mem_nhds (hU i).2)
  refine Filter.mem_of_superset hbox ?_
  intro y hy
  choose g hg hgy using fun i => hy i (Set.mem_univ i)
  refine ⟨g, hWN (hUW ?_), ?_⟩
  · intro i _
    exact hg i
  · funext i
    exact hgy i

end

end GaloisForLFunctions.HTGeometry
