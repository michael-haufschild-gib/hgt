import GaloisForLFunctions.HTGeometry.PairGroupoidBidescentLaw

/-!
# Universal observation descent law

Observations on a fixed source are classified, up to retained information, by
their kernel equivalence relations.  Serial postprocessing can only enlarge a
kernel, while a heterogeneous parallel record intersects the kernels of all
its channels.  Target recovery is exactly kernel refinement.

This file adds the symmetry and two-directional consequences needed by the
Riemann source problem.  Reflection-invariant observations are closed under
arbitrary parallel records and arbitrary serial postprocessing.  Therefore no
family of such observations, regardless of size or codomains, can recover a
nonzero reflection-odd target.  Exact gluing in an independent direction only
transports a horizontal kernel pair; it cannot improve it.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Serial postprocessing preserves invariance under a source symmetry. -/
theorem invariantUnder_postprocess
    {X Q R : Type*} (sigma : X -> X) (pi : X -> Q) (post : Q -> R)
    (hpi : InvariantUnder sigma pi) :
    InvariantUnder sigma (post ∘ pi) := by
  intro x
  exact congrArg post (hpi x)

/-- An arbitrary heterogeneous parallel record of invariant observations is
again invariant.  Thus adding more invariant channels never creates an odd
orientation channel. -/
theorem invariantUnder_observationRecord
    {J X : Type*} {Y : J -> Type*}
    (sigma : X -> X) (obs : forall j, X -> Y j)
    (hobs : forall j, InvariantUnder sigma (obs j)) :
    InvariantUnder sigma (observationRecord obs) := by
  intro x
  funext j
  exact hobs j x

/-- **Invariant-family odd-target law.**  If a reflection-odd real target is
recoverable from the attained range of an arbitrary family of invariant
observations, then the target vanishes.  No topology, linearity, boundedness,
finiteness, or common observation codomain is assumed. -/
theorem oddTarget_eq_zero_of_factorsThroughRange_invariantObservationFamily
    {J X : Type*} {Y : J -> Type*}
    {sigma : X -> X} {obs : forall j, X -> Y j} {chi : X -> ℝ}
    (hobs : forall j, InvariantUnder sigma (obs j))
    (hchi : OddUnder X sigma chi)
    (hfactor : FactorsThroughRange (observationRecord obs) chi) :
    forall x, chi x = 0 := by
  have hrefine : KernelRefines (observationRecord obs) chi :=
    (factorsThroughRange_iff_kernelRefines (observationRecord obs) chi).1 hfactor
  intro x
  have hrecord :
      MapKernelPair (observationRecord obs) (sigma x) x := by
    exact invariantUnder_observationRecord sigma obs hobs x
  have hsame : chi (sigma x) = chi x := hrefine (sigma x) x hrecord
  linarith [hchi x]

/-- An invariant observation family cannot recover a reflection-odd target
which is nonzero at even one source point. -/
theorem not_observationFamilyRecovers_oddTarget_of_invariant_of_ne
    {J X : Type*} {Y : J -> Type*}
    {sigma : X -> X} {obs : forall j, X -> Y j} {chi : X -> ℝ}
    (hobs : forall j, InvariantUnder sigma (obs j))
    (hchi : OddUnder X sigma chi) {x : X} (hx : chi x ≠ 0) :
    ¬ ObservationFamilyRecovers obs chi := by
  intro hrecover
  have hfactor : FactorsThroughRange (observationRecord obs) chi :=
    (observationFamilyRecovers_iff_factorsThroughRecordRange obs chi).1 hrecover
  exact hx
    (oddTarget_eq_zero_of_factorsThroughRange_invariantObservationFamily
      hobs hchi hfactor x)

/-- Every family which does recover a nonzero odd target must contain a
channel separating that point from its reflection.  This is the exact
horizontal-channel obligation. -/
theorem exists_transverse_channel_of_observationFamilyRecovers_oddTarget
    {J X : Type*} {Y : J -> Type*}
    {sigma : X -> X} {obs : forall j, X -> Y j} {chi : X -> ℝ}
    (hchi : OddUnder X sigma chi)
    (hrecover : ObservationFamilyRecovers obs chi)
    {x : X} (hx : chi x ≠ 0) :
    exists j, obs j (sigma x) ≠ obs j x := by
  by_contra hnone
  push Not at hnone
  have hsame : chi (sigma x) = chi x :=
    hrecover (sigma x) x hnone
  apply hx
  linarith [hchi x, hsame]

/-- Set-level bidescent conservation.  Exact gluing between two vertical
levels at both horizontal endpoints preserves the complete horizontal kernel
pair, not merely an additive difference. -/
theorem horizontal_mapKernelPair_iff_of_vertical_gluing
    {A B C : Type*} (F : A -> B -> C)
    (a0 a1 : A) (b0 b1 : B)
    (hv0 : F a0 b0 = F a1 b0)
    (hv1 : F a0 b1 = F a1 b1) :
    MapKernelPair (F a0) b0 b1 ↔ MapKernelPair (F a1) b0 b1 := by
  change (F a0 b0 = F a0 b1) ↔ (F a1 b0 = F a1 b1)
  rw [hv0, hv1]

/-- Vertical gluing alone permits every horizontal kernel relation: a field
constant in the vertical coordinate realizes an arbitrary horizontal
observation. -/
theorem vertical_gluing_realizes_arbitrary_horizontal_observation
    {A B C : Type*} (h : B -> C) (a0 a1 : A) :
    (forall b, (fun _ b' => h b') a0 b = (fun _ b' => h b') a1 b) ∧
      (fun b => (fun _ b' => h b') a1 b) = h := by
  exact ⟨fun _ => rfl, rfl⟩

/-- **Complete observation-descent law.**  Recovery, serial loss, and
parallel resolution are three faces of the kernel-equivalence lattice. -/
theorem completeObservationDescentLaw
    {J X Q R C : Type*} {Y : J -> Type*}
    (pi : X -> Q) (post : Q -> R) (obs : forall j, X -> Y j)
    (chi : X -> C) :
    (FactorsThroughRange pi chi ↔
      ObservationKernelSetoid pi ≤ ObservationKernelSetoid chi) ∧
    ObservationRefines pi (post ∘ pi) ∧
    ObservationKernelSetoid (observationRecord obs) =
      ⨅ j, ObservationKernelSetoid (obs j) := by
  constructor
  · exact factorsThroughRange_iff_kernelRefines pi chi
  constructor
  · exact observationRefines_postprocess pi post
  · exact observationKernelSetoid_record obs

end

end GaloisForLFunctions.HTGeometry
