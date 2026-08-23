import GaloisForLFunctions.HTGeometry.SpecDimOneSections

/-!
# The two-point base map of a specialisation

A specialisation `x ⤳ y` in a scheme `X` and a one-dimensional local domain `𝒪` give the
continuous map `Spec 𝒪 → X` sending the generic point to `x` and the closed point to `y`.  The
preimage of an open set is the whole spectrum if it contains `y`, the open generic point if it
contains `x` but not `y`, and empty otherwise.
-/

namespace HTGeometry

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry PrimeSpectrum IsLocalRing

universe u

variable {X : Scheme.{u}} (x y : X)
variable (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
variable (hdim : ∀ P : Ideal R, P.IsPrime → P = ⊥ ∨ P = maximalIdeal R) (hfield : ¬ IsField R)

open scoped Classical in
/-- The map `Spec 𝒪 → X` sending the generic point to `x` and the closed point to `y`. -/
noncomputable def specBaseFun (q : Spec R) : X :=
  if q = specGeneric (R : Type u) then x else y

theorem specBaseFun_generic : specBaseFun x y R (specGeneric (R : Type u)) = x := by
  classical
  rw [specBaseFun, if_pos rfl]

include hfield in
theorem specBaseFun_closed : specBaseFun x y R (specClosed (R : Type u)) = y := by
  classical
  rw [specBaseFun, if_neg (fun h => specGeneric_ne_specClosed hfield h.symm)]

include hdim hfield in
theorem specBaseFun_preimage (hspec : x ⤳ y) (U : X.Opens) :
    (specBaseFun x y R ⁻¹' (U : Set X)) = (⊤ : Set (Spec R)) ∨
      (specBaseFun x y R ⁻¹' (U : Set X)) = {specGeneric (R : Type u)} ∨
      (specBaseFun x y R ⁻¹' (U : Set X)) = (∅ : Set (Spec R)) := by
  classical
  by_cases hy : y ∈ U
  · have hx : x ∈ U := hspec.mem_open U.2 hy
    refine Or.inl ?_
    ext q
    simp only [Set.mem_preimage, Set.top_eq_univ, Set.mem_univ, iff_true]
    rcases spec_eq_generic_or_closed hdim q with h | h
    · rw [h, specBaseFun_generic]; exact hx
    · rw [h, specBaseFun_closed x y R hfield]; exact hy
  · by_cases hx : x ∈ U
    · refine Or.inr (Or.inl ?_)
      ext q
      simp only [Set.mem_preimage]
      constructor
      · intro hq
        rcases spec_eq_generic_or_closed hdim q with h | h
        · exact h
        · rw [h, specBaseFun_closed x y R hfield] at hq
          exact absurd hq hy
      · rintro rfl
        rw [specBaseFun_generic]
        exact hx
    · refine Or.inr (Or.inr ?_)
      ext q
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rcases spec_eq_generic_or_closed hdim q with h | h
      · rw [h, specBaseFun_generic]; exact hx
      · rw [h, specBaseFun_closed x y R hfield]; exact hy

include hdim hfield in
theorem continuous_specBaseFun (hspec : x ⤳ y) : Continuous (specBaseFun x y R) := by
  refine continuous_def.2 fun U hU => ?_
  have h := specBaseFun_preimage x y R hdim hfield hspec ⟨U, hU⟩
  rcases h with h | h | h
  · rw [show (specBaseFun x y R ⁻¹' U) = (Set.univ : Set (Spec R)) from h]
    exact isOpen_univ
  · rw [show (specBaseFun x y R ⁻¹' U) = {specGeneric (R : Type u)} from h]
    exact isOpen_specGeneric hdim hfield
  · rw [show (specBaseFun x y R ⁻¹' U) = (∅ : Set (Spec R)) from h]
    exact isOpen_empty

/-- The continuous map `Spec 𝒪 → X` attached to a specialisation. -/
noncomputable def specBase (hspec : x ⤳ y) : (Spec R : TopCat.{u}) ⟶ (X : TopCat.{u}) :=
  TopCat.ofHom ⟨specBaseFun x y R, continuous_specBaseFun x y R hdim hfield hspec⟩

variable (hspec : x ⤳ y)

include hdim hfield in
theorem specBase_preimage_eq_top (U : X.Opens) (hy : y ∈ U) :
    (Opens.map (specBase x y R hdim hfield hspec)).obj U = ⊤ := by
  have hx : x ∈ U := hspec.mem_open U.2 hy
  refine Opens.ext ?_
  ext q
  simp only [Opens.coe_top, Set.mem_univ, iff_true]
  show specBaseFun x y R q ∈ (U : Set X)
  rcases spec_eq_generic_or_closed hdim q with h | h
  · rw [h, specBaseFun_generic]; exact hx
  · rw [h, specBaseFun_closed x y R hfield]; exact hy

include hdim hfield in
theorem specBase_preimage_eq_generic (U : X.Opens) (hx : x ∈ U) (hy : y ∉ U) :
    (Opens.map (specBase x y R hdim hfield hspec)).obj U = specGenericOpen R hdim hfield := by
  refine Opens.ext ?_
  ext q
  constructor
  · intro hq
    have hq' : specBaseFun x y R q ∈ (U : Set X) := hq
    rcases spec_eq_generic_or_closed hdim q with h | h
    · exact h
    · rw [h, specBaseFun_closed x y R hfield] at hq'
      exact absurd hq' hy
  · intro hq
    have hq' : q = specGeneric (R : Type u) := hq
    show specBaseFun x y R q ∈ (U : Set X)
    rw [hq', specBaseFun_generic]
    exact hx

include hdim hfield in
theorem specBase_preimage_eq_bot (U : X.Opens) (hx : x ∉ U) :
    (Opens.map (specBase x y R hdim hfield hspec)).obj U = ⊥ := by
  have hy : y ∉ U := fun hy => hx (hspec.mem_open U.2 hy)
  refine Opens.ext ?_
  ext q
  simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  show specBaseFun x y R q ∉ (U : Set X)
  rcases spec_eq_generic_or_closed hdim q with h | h
  · rw [h, specBaseFun_generic]; exact hx
  · rw [h, specBaseFun_closed x y R hfield]; exact hy

end HTGeometry
