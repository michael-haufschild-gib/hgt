import GaloisForLFunctions.HTGeometry.RelativeAdmissionSpectrumNaturalityLaw

/-!
# Exact kernel law for relative admission spectra

Admission is the zero locus of a pointed obstruction class.  Under a natural
transport, the target obstruction is the image of the source obstruction.
Consequently the target admission spectrum is exactly the disjoint union of
the source admission spectrum and the parameters whose nonzero source class
is killed by the induced quotient map.

This sharpens admission-spectrum naturality: regular transport can never
remove an admitted parameter, and every newly admitted parameter has one
precise cause---loss of a nonzero obstruction class in the transport kernel.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A0 A1 B0 B1 P : Type*}
variable [Field R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup B0] [Module R B0]
variable [AddCommGroup B1] [Module R B1]

/-- Parameters at which a map kills a nonzero pointed class. -/
def killedPointedLocus
    {V W P : Type*} [Zero V] [Zero W]
    (T : V → W) (x : P → V) : Set P :=
  {p | x p ≠ 0 ∧ T (x p) = 0}

/-- The zero locus after a zero-preserving map is exactly the old zero locus
plus the nonzero pointed classes killed by the map. -/
theorem mapped_zeroLocus_eq_union_killedPointedLocus
    {V W P : Type*} [Zero V] [Zero W]
    (T : V → W) (x : P → V) (hzero : T 0 = 0) :
    {p | T (x p) = 0} =
      {p | x p = 0} ∪ killedPointedLocus T x := by
  ext p
  constructor
  · intro hTx
    by_cases hx : x p = 0
    · exact Or.inl hx
    · exact Or.inr ⟨hx, hTx⟩
  · rintro (hx | ⟨_hx, hTx⟩)
    · change T (x p) = 0
      rw [hx, hzero]
    · exact hTx

/-- The inherited zero locus and the newly killed locus are disjoint. -/
theorem zeroLocus_disjoint_killedPointedLocus
    {V W P : Type*} [Zero V] [Zero W]
    (T : V → W) (x : P → V) :
    Disjoint {p | x p = 0} (killedPointedLocus T x) := by
  rw [Set.disjoint_left]
  intro p hx hkilled
  exact hkilled.1 hx

/--
**Exact relative-admission kernel law.**  Under a sector-preserving chain
transport, the target admission spectrum is the disjoint union of the source
spectrum and the locus of nonzero source obstruction classes killed by the
induced quotient map.
-/
theorem relativeAdmissionSpectrum_target_eq_source_union_killed
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (h : A1 →ₗ[R] A0) (k : B1 →ₗ[R] B0)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U)
    (x : P → A1)
    (hsource : ∀ p, d (h (x p)) = x p)
    (htarget : ∀ p, e (k (T1 (x p))) = T1 (x p)) :
    relativeAdmissionSpectrum U e k (fun p => T1 (x p)) =
      relativeAdmissionSpectrum S d h x ∪
        killedPointedLocus
          (relativeAdmissionQuotientMap
            S U d e T0 T1 hchain hsector)
          (fun p => relativePrimitiveObstruction S d h (x p)) := by
  ext p
  change
    relativePrimitiveObstruction U e k (T1 (x p)) = 0 ↔
      relativePrimitiveObstruction S d h (x p) = 0 ∨
        (relativePrimitiveObstruction S d h (x p) ≠ 0 ∧
          relativeAdmissionQuotientMap
              S U d e T0 T1 hchain hsector
              (relativePrimitiveObstruction S d h (x p)) = 0)
  rw [← relativePrimitiveObstruction_natural
    S U d e h k T0 T1 hchain hsector (x p)
      (hsource p) (htarget p)]
  by_cases hx : relativePrimitiveObstruction S d h (x p) = 0
  · simp [hx]
  · simp [hx]

/-- Regular relative-admission transport can only enlarge the admission
spectrum. -/
theorem relativeAdmissionSpectrum_source_subset_target
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (h : A1 →ₗ[R] A0) (k : B1 →ₗ[R] B0)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U)
    (x : P → A1)
    (hsource : ∀ p, d (h (x p)) = x p)
    (htarget : ∀ p, e (k (T1 (x p))) = T1 (x p)) :
    relativeAdmissionSpectrum S d h x ⊆
      relativeAdmissionSpectrum U e k (fun p => T1 (x p)) := by
  rw [relativeAdmissionSpectrum_target_eq_source_union_killed
    S U d e h k T0 T1 hchain hsector x hsource htarget]
  exact Set.subset_union_left

/-- Every strict enlargement of admission is witnessed by a nonzero source
obstruction class in the transport kernel. -/
theorem mem_killedPointedLocus_of_target_admitted_source_not
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (h : A1 →ₗ[R] A0) (k : B1 →ₗ[R] B0)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U)
    (x : P → A1)
    (hsource : ∀ p, d (h (x p)) = x p)
    (htarget : ∀ p, e (k (T1 (x p))) = T1 (x p))
    {p : P}
    (hpTarget : p ∈
      relativeAdmissionSpectrum U e k (fun q => T1 (x q)))
    (hpSource : p ∉ relativeAdmissionSpectrum S d h x) :
    p ∈ killedPointedLocus
      (relativeAdmissionQuotientMap
        S U d e T0 T1 hchain hsector)
      (fun q => relativePrimitiveObstruction S d h (x q)) := by
  rw [relativeAdmissionSpectrum_target_eq_source_union_killed
    S U d e h k T0 T1 hchain hsector x hsource htarget] at hpTarget
  exact hpTarget.resolve_left hpSource

end

end GaloisForLFunctions.HTGeometry
