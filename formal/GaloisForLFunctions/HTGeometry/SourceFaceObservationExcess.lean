import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Source-face observation excess

Let `f : M → N` be a linear observation, and let `P ⊆ M`, `Q ⊆ N` be source and
target layers discarded at a boundary face.  If `f(P) ⊆ Q`, then `f` descends to

```text
M/P → N/Q.
```

The kernel of the descended observation is the image of `f⁻¹(Q)` in `M/P`; hence it is
injective exactly when `f⁻¹(Q) ⊆ P`.  More strongly, after quotienting the new kernel by
the inherited generic kernel and the discarded source layer, the remaining born ambiguity is
canonically equivalent to the excess intersection

```text
(range(f) ∩ Q) / f(P).
```

This is the linear-algebraic core of the source-face conservativity law.  It says that a
boundary cannot create arbitrary invisible gauges: every genuinely new gauge is the image of a
generic observation which has fallen into the forgotten target layer.  In a one-parameter module
family with `P = xM` and `Q = xN`, the right side is the standard representative of the
`Tor₁(coker(f), R/(x))` base-change defect.

The quotient and excess-intersection theorems are classical linear algebra.  Their role in the
HT project is to couple the common-kernel reconstruction theorem to the independently computed
source-face derived restriction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {𝕜 : Type u} {M : Type v} {N : Type w}
variable [Field 𝕜] [AddCommGroup M] [Module 𝕜 M]
variable [AddCommGroup N] [Module 𝕜 N]

/-- Observation induced after quotienting a source layer `P` and a target layer `Q`. -/
def sourceFaceQuotientObservation
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N)
    (hPQ : P ≤ Q.comap f) :
    (M ⧸ P) →ₗ[𝕜] (N ⧸ Q) :=
  P.mapQ Q f hPQ

@[simp]
theorem sourceFaceQuotientObservation_mkQ
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N)
    (hPQ : P ≤ Q.comap f) (x : M) :
    sourceFaceQuotientObservation f P Q hPQ (P.mkQ x) = Q.mkQ (f x) :=
  rfl

/-- The boundary kernel is exactly the image of the inverse image of the forgotten target
layer. -/
theorem ker_sourceFaceQuotientObservation
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N)
    (hPQ : P ≤ Q.comap f) :
    LinearMap.ker (sourceFaceQuotientObservation f P Q hPQ) =
      (Q.comap f).map P.mkQ := by
  exact Submodule.ker_mapQ P Q f hPQ

/-- **Maximal quotient reconstruction law.**  The observation on the face is injective exactly
when every source element whose observation falls into the forgotten target layer was already in
the forgotten source layer. -/
theorem sourceFaceQuotientObservation_injective_iff
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N)
    (hPQ : P ≤ Q.comap f) :
    Function.Injective (sourceFaceQuotientObservation f P Q hPQ) ↔
      Q.comap f ≤ P := by
  constructor
  · intro hinjective x hx
    have hzero : sourceFaceQuotientObservation f P Q hPQ (P.mkQ x) = 0 := by
      rw [sourceFaceQuotientObservation_mkQ]
      exact Submodule.Quotient.mk_eq_zero Q |>.2 hx
    have hclass : P.mkQ x = 0 := hinjective (by simpa using hzero)
    exact Submodule.Quotient.mk_eq_zero P |>.1 hclass
  · intro hpreimage
    rw [← LinearMap.ker_eq_bot, ker_sourceFaceQuotientObservation]
    rw [eq_bot_iff]
    rintro y ⟨x, hx, rfl⟩
    exact Submodule.Quotient.mk_eq_zero P |>.2 (hpreimage hx)

/-! ## Joint reporters on a normalized source-fixed gauge -/

section JointSourceObservation

variable {ι : Type*} {Nᵢ : ι → Type w}
variable [∀ i, AddCommGroup (Nᵢ i)] [∀ i, Module 𝕜 (Nᵢ i)]

/-- The joint observation of a normalized source-fixed gauge `K` by a reporter family `R`.
The reporters may have different target spaces. -/
def sourceFixedJointObservation (K : Submodule 𝕜 M)
    (R : ∀ i, M →ₗ[𝕜] Nᵢ i) : K →ₗ[𝕜] (∀ i, Nᵢ i) where
  toFun x i := R i x.1
  map_add' x y := by
    funext i
    exact map_add (R i) x.1 y.1
  map_smul' c x := by
    funext i
    exact map_smul (R i) c x.1

/-- The exact obstruction to reconstruction from the reporter family: normalized source-fixed
gauges invisible to every reporter. -/
def sourceFixedJointInvisibleGauge (K : Submodule 𝕜 M)
    (R : ∀ i, M →ₗ[𝕜] Nᵢ i) : Submodule 𝕜 M :=
  K ⊓ ⨅ i, LinearMap.ker (R i)

theorem mem_sourceFixedJointInvisibleGauge (K : Submodule 𝕜 M)
    (R : ∀ i, M →ₗ[𝕜] Nᵢ i) (x : M) :
    x ∈ sourceFixedJointInvisibleGauge K R ↔ x ∈ K ∧ ∀ i, R i x = 0 := by
  simp [sourceFixedJointInvisibleGauge]

/-- The joint observation kernel is precisely the common invisible gauge, restricted to the
normalized source-fixed stratum. -/
theorem ker_sourceFixedJointObservation (K : Submodule 𝕜 M)
    (R : ∀ i, M →ₗ[𝕜] Nᵢ i) :
    LinearMap.ker (sourceFixedJointObservation K R) =
      (sourceFixedJointInvisibleGauge K R).comap K.subtype := by
  ext x
  constructor
  · intro hx
    have hobs : sourceFixedJointObservation K R x = 0 := LinearMap.mem_ker.1 hx
    change (x : M) ∈ sourceFixedJointInvisibleGauge K R
    rw [mem_sourceFixedJointInvisibleGauge]
    refine ⟨x.property, ?_⟩
    intro i
    simpa [sourceFixedJointObservation] using congrFun hobs i
  · intro hx
    rw [LinearMap.mem_ker]
    funext i
    change R i x.1 = 0
    exact ((mem_sourceFixedJointInvisibleGauge K R x.1).1 hx).2 i

/-- **Maximal joint reconstruction law.**  A reporter family reconstructs every normalized
source-fixed gauge exactly when its joint fixed kernel is zero:

```text
Obs_R injective  ↔  K^S ∩ ⋂_r ker(R_r) = 0.
```

This criterion is unconditional and permits heterogeneous reporter codomains. -/
theorem sourceFixedJointObservation_injective_iff (K : Submodule 𝕜 M)
    (R : ∀ i, M →ₗ[𝕜] Nᵢ i) :
    Function.Injective (sourceFixedJointObservation K R) ↔
      sourceFixedJointInvisibleGauge K R = ⊥ := by
  constructor
  · intro hinjective
    apply eq_bot_iff.2
    intro x hx
    let xK : K := ⟨x, hx.1⟩
    have hobs : sourceFixedJointObservation K R xK = 0 := by
      funext i
      exact ((mem_sourceFixedJointInvisibleGauge K R x).1 hx).2 i
    have hxK0 : xK = 0 := hinjective (by simpa using hobs)
    have hx0 := congrArg (fun y : K => (y : M)) hxK0
    change x = 0 at hx0
    exact hx0
  · intro htrivial x y hxy
    apply Subtype.ext
    have hd : (x.1 - y.1) ∈ sourceFixedJointInvisibleGauge K R := by
      rw [mem_sourceFixedJointInvisibleGauge]
      refine ⟨K.sub_mem x.2 y.2, ?_⟩
      intro i
      have hi : R i x.1 = R i y.1 := by
        simpa [sourceFixedJointObservation] using congrFun hxy i
      rw [map_sub, hi, sub_self]
    rw [htrivial] at hd
    exact sub_eq_zero.mp (by simpa using hd)

/-- **Maximal positive successor to joint nonconservativity.**  After quotienting the normalized
source-fixed stratum by the exact common invisible gauge, the joint observation becomes a
canonical linear equivalence onto its range. -/
noncomputable def sourceFixedJointObservableQuotientEquivRange (K : Submodule 𝕜 M)
    (R : ∀ i, M →ₗ[𝕜] Nᵢ i) :
    (K ⧸ (sourceFixedJointInvisibleGauge K R).comap K.subtype) ≃ₗ[𝕜]
      LinearMap.range (sourceFixedJointObservation K R) := by
  rw [← ker_sourceFixedJointObservation K R]
  exact LinearMap.quotKerEquivRange (sourceFixedJointObservation K R)

end JointSourceObservation

/-- The part of the source which can become invisible after quotienting the target by `Q`. -/
abbrev sourceFaceObservationPreimage
    (f : M →ₗ[𝕜] N) (Q : Submodule 𝕜 N) : Submodule 𝕜 M :=
  Q.comap f

/-- The observations which both occur generically and fall into the forgotten target layer. -/
abbrev sourceFaceRangeIntersection
    (f : M →ₗ[𝕜] N) (Q : Submodule 𝕜 N) : Submodule 𝕜 N :=
  LinearMap.range f ⊓ Q

/-- Restrict `f` from the source preimage of `Q` onto `range(f) ∩ Q`. -/
def sourceFaceRestrictedRangeMap
    (f : M →ₗ[𝕜] N) (Q : Submodule 𝕜 N) :
    sourceFaceObservationPreimage f Q →ₗ[𝕜] sourceFaceRangeIntersection f Q :=
  (f.domRestrict (sourceFaceObservationPreimage f Q)).codRestrict
    (sourceFaceRangeIntersection f Q) fun x =>
      ⟨⟨x.1, rfl⟩, x.2⟩

/-- The restricted range map is onto: every point of `range(f) ∩ Q` has a preimage whose
observation lies in `Q`. -/
theorem sourceFaceRestrictedRangeMap_surjective
    (f : M →ₗ[𝕜] N) (Q : Submodule 𝕜 N) :
    Function.Surjective (sourceFaceRestrictedRangeMap f Q) := by
  rintro ⟨y, hyRange, hyQ⟩
  rcases hyRange with ⟨x, rfl⟩
  exact ⟨⟨x, hyQ⟩, rfl⟩

/-- The inherited part of the boundary kernel: the discarded source layer together with the
generic observation kernel, both restricted to `f⁻¹(Q)`. -/
def sourceFaceInheritedGauge
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) :
    Submodule 𝕜 (sourceFaceObservationPreimage f Q) :=
  P.comap (sourceFaceObservationPreimage f Q).subtype ⊔
    LinearMap.ker (sourceFaceRestrictedRangeMap f Q)

/-- The generic range already forced into the forgotten target layer by the discarded source
layer. -/
def sourceFaceAttainmentLayer
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) :
    Submodule 𝕜 (sourceFaceRangeIntersection f Q) :=
  (P.map f).comap (sourceFaceRangeIntersection f Q).subtype

/-- Preimage of the inherited attainment layer is exactly the inherited source gauge. -/
theorem sourceFaceRestrictedRangeMap_comap_attainmentLayer
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N)
    (hPQ : P ≤ Q.comap f) :
    (sourceFaceAttainmentLayer f P Q).comap (sourceFaceRestrictedRangeMap f Q) =
      sourceFaceInheritedGauge f P Q := by
  apply le_antisymm
  · intro x hx
    change f x.1 ∈ P.map f at hx
    rcases hx with ⟨p, hp, hfp⟩
    let pFace : sourceFaceObservationPreimage f Q := ⟨p, hPQ hp⟩
    have hpFace : pFace ∈ P.comap (sourceFaceObservationPreimage f Q).subtype := hp
    have hker : x - pFace ∈ LinearMap.ker (sourceFaceRestrictedRangeMap f Q) := by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      simp only [sourceFaceRestrictedRangeMap, LinearMap.codRestrict_apply,
        LinearMap.domRestrict_apply, Submodule.coe_sub]
      rw [map_sub]
      change f x.1 - f p = 0
      rw [hfp]
      simp
    exact Submodule.mem_sup.2 ⟨pFace, hpFace, x - pFace, hker, by
      rw [add_comm, sub_add_cancel]⟩
  · intro x hx
    rcases Submodule.mem_sup.1 hx with ⟨pFace, hpFace, z, hz, hsum⟩
    change f x.1 ∈ P.map f
    refine ⟨pFace.1, hpFace, ?_⟩
    have hz0 : sourceFaceRestrictedRangeMap f Q z = 0 :=
      LinearMap.mem_ker.1 hz
    have hmap := congrArg (fun y : sourceFaceRangeIntersection f Q => (y : N))
      (congrArg (sourceFaceRestrictedRangeMap f Q) hsum)
    simp only [map_add, Submodule.coe_add, sourceFaceRestrictedRangeMap,
      LinearMap.codRestrict_apply, LinearMap.domRestrict_apply] at hmap
    have hzval : f z.1 = 0 := by
      exact congrArg (fun y : sourceFaceRangeIntersection f Q => (y : N)) hz0
    simpa [hzval] using hmap

/-- The canonical map from genuinely born boundary gauges to the excess intersection of the
generic observation range with the forgotten target layer. -/
def sourceFaceBornGaugeToRangeExcess
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N)
    (hPQ : P ≤ Q.comap f) :
    (sourceFaceObservationPreimage f Q ⧸ sourceFaceInheritedGauge f P Q) →ₗ[𝕜]
      (sourceFaceRangeIntersection f Q ⧸ sourceFaceAttainmentLayer f P Q) :=
  (sourceFaceInheritedGauge f P Q).mapQ
    (sourceFaceAttainmentLayer f P Q)
    (sourceFaceRestrictedRangeMap f Q)
    (sourceFaceRestrictedRangeMap_comap_attainmentLayer f P Q hPQ).ge

/-- The born-gauge map has no kernel. -/
theorem sourceFaceBornGaugeToRangeExcess_injective
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N)
    (hPQ : P ≤ Q.comap f) :
    Function.Injective (sourceFaceBornGaugeToRangeExcess f P Q hPQ) := by
  rw [← LinearMap.ker_eq_bot]
  rw [sourceFaceBornGaugeToRangeExcess, Submodule.ker_mapQ]
  rw [sourceFaceRestrictedRangeMap_comap_attainmentLayer f P Q hPQ]
  exact Submodule.mkQ_map_self (sourceFaceInheritedGauge f P Q)

/-- Every excess-intersection class is represented by a born boundary gauge. -/
theorem sourceFaceBornGaugeToRangeExcess_surjective
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N)
    (hPQ : P ≤ Q.comap f) :
    Function.Surjective (sourceFaceBornGaugeToRangeExcess f P Q hPQ) := by
  intro y
  induction y using Quotient.inductionOn with
  | _ y =>
      obtain ⟨x, hx⟩ := sourceFaceRestrictedRangeMap_surjective f Q y
      refine ⟨(sourceFaceInheritedGauge f P Q).mkQ x, ?_⟩
      change (sourceFaceAttainmentLayer f P Q).mkQ
          (sourceFaceRestrictedRangeMap f Q x) =
        (sourceFaceAttainmentLayer f P Q).mkQ y
      exact congrArg (sourceFaceAttainmentLayer f P Q).mkQ hx

/-- **Born-gauge/excess-intersection equivalence.**  Modulo the generic kernel and the discarded
source layer, boundary-born invisible gauges are canonically the excess intersection of the
generic observation range with the forgotten target layer, modulo observations already produced
by the discarded source layer. -/
noncomputable def sourceFaceBornGaugeEquivRangeExcess
    (f : M →ₗ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N)
    (hPQ : P ≤ Q.comap f) :
    (sourceFaceObservationPreimage f Q ⧸ sourceFaceInheritedGauge f P Q) ≃ₗ[𝕜]
      (sourceFaceRangeIntersection f Q ⧸ sourceFaceAttainmentLayer f P Q) :=
  LinearEquiv.ofBijective (sourceFaceBornGaugeToRangeExcess f P Q hPQ)
    ⟨sourceFaceBornGaugeToRangeExcess_injective f P Q hPQ,
      sourceFaceBornGaugeToRangeExcess_surjective f P Q hPQ⟩

/-! ## Algebraic shadow of the Tate--Barnes localization comparison -/

section FactorChainMap

variable {A : Type*} [CommRing A]

/-- The one-factor Koszul differential attached to the selected source face. -/
def selectedFaceFactorObservation (x : A) : A →ₗ[A] A :=
  LinearMap.mulLeft A x

/-- The product-factor differential in the Barnes normal-crossing presentation. -/
def productFaceFactorObservation (p x : A) : A →ₗ[A] A :=
  LinearMap.mulLeft A (p * x)

/-- The degree-zero part of the canonical map from `K(x)` to `K(p*x)`.  Its degree-one part is
the identity. -/
def selectedToProductFaceDegreeZero (p : A) : A →ₗ[A] A :=
  LinearMap.mulLeft A p

/-- **Selected-face/Barnes chain square.**  Identity in degree one and multiplication by the
complementary factor `p` in degree zero define a canonical chain map
`[A --x→ A] → [A --p*x→ A]`.  After restriction to `x=0`, the induced degree-one map is still the
identity, so the selected Koszul generator maps to the product-face `Tor₁` generator whenever
both presentations live in this same ring.  This theorem does not identify a nodal gauge
coordinate with a source operator from a different algebra. -/
theorem selectedToProductFace_chainMap_square (p x : A) :
    (productFaceFactorObservation p x).comp LinearMap.id =
      (selectedToProductFaceDegreeZero p).comp (selectedFaceFactorObservation x) := by
  apply LinearMap.ext
  intro a
  simp [productFaceFactorObservation, selectedToProductFaceDegreeZero,
    selectedFaceFactorObservation, LinearMap.mulLeft_apply]

end FactorChainMap

end

end GaloisForLFunctions.HTGeometry
