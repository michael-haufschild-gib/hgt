import GaloisForLFunctions.HTGeometry.RelativeContractionTransgressionLaw

/-!
# Naturality of the relative admission spectrum

Fix linear maps `d : A₀ → A₁`, a candidate primitive map `h : A₁ → A₀` and an admitted sector
`S ≤ A₀`. The relative primitive obstruction of `x ∈ A₁` is the class of `h x` in
`A₀ / (S + ker d)`; for a family `x : P → A₁` the relative admission spectrum is the set of
parameters `p` where this class vanishes, i.e. (when `h (x p)` is a primitive) where `x p` has a
primitive in `S`. A chain map `(T₀, T₁)` from `d` to `e : B₀ → B₁` carrying `S` into `U` induces a
linear map of quotients that sends obstruction classes to obstruction classes. The spectrum is
therefore preserved when this quotient map is injective, and a nonzero source class with zero
target class forces the quotient map to be non-injective.

## Main results

- `relativeAdmissionQuotientMap`: the induced map `A₀ / (S + ker d) → B₀ / (U + ker e)`.
- `relativePrimitiveObstruction_eq_of_primitives`: the obstruction class does not depend on the
  choice of primitive.
- `relativePrimitiveObstruction_natural`: the induced map sends the obstruction of `x` to the
  obstruction of `T₁ x`.
- `relativeAdmissionSpectrum_natural_eq_of_injective`: if the induced quotient map is injective,
  the admission spectra of `x` and `T₁ ∘ x` coincide.
- `relativeAdmissionTransport_information_loss`: a nonzero source obstruction that becomes zero in
  the target lies in the kernel of the induced map, which is then not injective.

## Hypotheses

Unconditional linear algebra over a field. Statements take as explicit inputs the chain-map
identity `e ∘ T₀ = T₁ ∘ d`, the sector condition `T₀(S) ≤ U`, and the primitive identities
`d (h x) = x`, `e (k (T₁ x)) = T₁ x`; the spectrum equality also assumes injectivity of the
induced quotient map.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R A0 A1 B0 B1 P : Type*}
variable [Field R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup B0] [Module R B0]
variable [AddCommGroup B1] [Module R B1]

/-- The parameters `p` at which the relative primitive obstruction of `x p` vanishes. -/
def relativeAdmissionSpectrum
    (S : Submodule R A0) (d : A0 →ₗ[R] A1) (h : A1 →ₗ[R] A0)
    (x : P → A1) : Set P :=
  {p | relativePrimitiveObstruction S d h (x p) = 0}

/-- A chain map `(T₀, T₁)` with `T₀(S) ≤ U` maps `S + ker d` into `U + ker e`. -/
theorem relativeAdmissionTransport_le_comap
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U) :
    S ⊔ LinearMap.ker d ≤ (U ⊔ LinearMap.ker e).comap T0 := by
  rw [sup_le_iff]
  constructor
  · intro a ha
    exact (show T0 a ∈ U ⊔ LinearMap.ker e from
      (le_sup_left : U ≤ U ⊔ LinearMap.ker e)
        (hsector (Submodule.mem_map_of_mem ha)))
  · intro a ha
    apply (le_sup_right : LinearMap.ker e ≤ U ⊔ LinearMap.ker e)
    change e (T0 a) = 0
    have h := LinearMap.congr_fun hchain a
    simp only [LinearMap.comp_apply] at h
    rw [h, show d a = 0 from ha, map_zero]

/-- The linear map `A₀ / (S + ker d) → B₀ / (U + ker e)` induced by `T₀`. -/
def relativeAdmissionQuotientMap
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U) :
    (A0 ⧸ (S ⊔ LinearMap.ker d)) →ₗ[R]
      (B0 ⧸ (U ⊔ LinearMap.ker e)) :=
  Submodule.mapQ (S ⊔ LinearMap.ker d) (U ⊔ LinearMap.ker e) T0
    (relativeAdmissionTransport_le_comap S U d e T0 T1 hchain hsector)

/-- Assuming `h (x p)` is a primitive of `x p`, `p` lies in the admission spectrum iff `x p = d b`
for some `b ∈ S`. -/
theorem relativeAdmissionSpectrum_mem_iff
    (S : Submodule R A0) (d : A0 →ₗ[R] A1) (h : A1 →ₗ[R] A0)
    (x : P → A1) (p : P) (hprimitive : d (h (x p)) = x p) :
    p ∈ relativeAdmissionSpectrum S d h x ↔
      ∃ b : A0, b ∈ S ∧ d b = x p := by
  exact relativePrimitiveObstruction_eq_zero_iff S d h (x p) hprimitive

/-- Any two primitives `h x`, `h' x` of `x` give the same relative obstruction class. -/
theorem relativePrimitiveObstruction_eq_of_primitives
    (S : Submodule R A0) (d : A0 →ₗ[R] A1)
    (h h' : A1 →ₗ[R] A0) (x : A1)
    (hh : d (h x) = x) (hh' : d (h' x) = x) :
    relativePrimitiveObstruction S d h x =
      relativePrimitiveObstruction S d h' x := by
  apply (Submodule.Quotient.eq (S ⊔ LinearMap.ker d)).2
  apply (le_sup_right : LinearMap.ker d ≤ S ⊔ LinearMap.ker d)
  change d (h x - h' x) = 0
  rw [map_sub, hh, hh', sub_self]

/-- Naturality: assuming `h x` and `k (T₁ x)` are primitives, the induced quotient map sends the
obstruction of `x` to the obstruction of `T₁ x`. -/
theorem relativePrimitiveObstruction_natural
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (h : A1 →ₗ[R] A0) (k : B1 →ₗ[R] B0)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U)
    (x : A1) (hsource : d (h x) = x)
    (htarget : e (k (T1 x)) = T1 x) :
    relativeAdmissionQuotientMap S U d e T0 T1 hchain hsector
        (relativePrimitiveObstruction S d h x) =
      relativePrimitiveObstruction U e k (T1 x) := by
  apply (Submodule.Quotient.eq (U ⊔ LinearMap.ker e)).2
  apply (le_sup_right : LinearMap.ker e ≤ U ⊔ LinearMap.ker e)
  change e (T0 (h x) - k (T1 x)) = 0
  rw [map_sub, htarget]
  have hcomm := LinearMap.congr_fun hchain (h x)
  simp only [LinearMap.comp_apply] at hcomm
  rw [hcomm, hsource, sub_self]

/-- If the induced quotient map is injective and primitives are chosen on both sides, the
admission spectrum of `x` equals that of `T₁ ∘ x`. -/
theorem relativeAdmissionSpectrum_natural_eq_of_injective
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (h : A1 →ₗ[R] A0) (k : B1 →ₗ[R] B0)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U)
    (x : P → A1)
    (hsource : ∀ p, d (h (x p)) = x p)
    (htarget : ∀ p, e (k (T1 (x p))) = T1 (x p))
    (hinjective : Function.Injective
      (relativeAdmissionQuotientMap S U d e T0 T1 hchain hsector)) :
    relativeAdmissionSpectrum S d h x =
      relativeAdmissionSpectrum U e k (fun p => T1 (x p)) := by
  ext p
  change relativePrimitiveObstruction S d h (x p) = 0 ↔
    relativePrimitiveObstruction U e k (T1 (x p)) = 0
  have hnat := relativePrimitiveObstruction_natural S U d e h k T0 T1
    hchain hsector (x p) (hsource p) (htarget p)
  constructor
  · intro hz
    rw [← hnat, hz, map_zero]
  · intro hz
    apply hinjective
    rw [hnat, hz, map_zero]

/-- If the source obstruction of `x` is nonzero but that of `T₁ x` vanishes, then the induced
quotient map kills the source class and is not injective. -/
theorem relativeAdmissionTransport_information_loss
    (S : Submodule R A0) (U : Submodule R B0)
    (d : A0 →ₗ[R] A1) (e : B0 →ₗ[R] B1)
    (h : A1 →ₗ[R] A0) (k : B1 →ₗ[R] B0)
    (T0 : A0 →ₗ[R] B0) (T1 : A1 →ₗ[R] B1)
    (hchain : e.comp T0 = T1.comp d)
    (hsector : S.map T0 ≤ U)
    (x : A1) (hsourcePrimitive : d (h x) = x)
    (htargetPrimitive : e (k (T1 x)) = T1 x)
    (hsource : relativePrimitiveObstruction S d h x ≠ 0)
    (htarget : relativePrimitiveObstruction U e k (T1 x) = 0) :
    ¬ Function.Injective
        (relativeAdmissionQuotientMap S U d e T0 T1 hchain hsector) ∧
      relativePrimitiveObstruction S d h x ∈
        LinearMap.ker
          (relativeAdmissionQuotientMap S U d e T0 T1 hchain hsector) := by
  have hnat := relativePrimitiveObstruction_natural S U d e h k T0 T1
    hchain hsector x hsourcePrimitive htargetPrimitive
  have hker :
      relativeAdmissionQuotientMap S U d e T0 T1 hchain hsector
          (relativePrimitiveObstruction S d h x) = 0 := by
    rw [hnat, htarget]
  constructor
  · intro hinj
    apply hsource
    apply hinj
    rw [hker, map_zero]
  · exact hker

end

end GaloisForLFunctions.HTGeometry

