import GaloisForLFunctions.RHTower.DeningerArithmeticCauchyCohomologyDescent
import GaloisForLFunctions.RHTower.DeningerSkewAdjointGraphCore

/-!
# Flow-equivariant Cauchy descent on arithmetic graph cores

This module closes the formal assembly step between the source two-column
Rost--Schmid/signature totalization and a graph-domain completion.

* `DeningerArithmeticThreeTermFlowChainMap` packages a chain map commuting with the
  transverse generator in all three degrees.
* Its induced maps on `H⁰`, `H¹`, and `H²` commute with the induced generators.
* `deningerTwoColumnComponentMap_intertwines` assembles the two product-column flow squares.
* `DeningerGraphIntertwining` transports common domains and ambient norm estimates across
  two different families of partially defined graph monomials.

No closed-range, splitting, positivity, spectral, or Xi-divisor premise is used.  Actual
arithmetic residue/corestriction maps must still discharge the explicit domain-preservation
and boundedness hypotheses.
-/

namespace RHTower

section FlowEquivariantChainMap

variable {R A0 A1 A2 B0 B1 B2 : Type*}
variable [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable [AddCommGroup B0] [Module R B0]
variable [AddCommGroup B1] [Module R B1]
variable [AddCommGroup B2] [Module R B2]

/-- A chain map that also intertwines the transverse generators in every degree. -/
structure DeningerArithmeticThreeTermFlowChainMap
    (C : DeningerArithmeticThreeTermFlow R A0 A1 A2)
    (D : DeningerArithmeticThreeTermFlow R B0 B1 B2)
    extends DeningerArithmeticThreeTermChainMap C.complex D.complex where
  commutes_theta0 : map0.comp C.theta0 = D.theta0.comp map0
  commutes_theta1 : map1.comp C.theta1 = D.theta1.comp map1
  commutes_theta2 : map2.comp C.theta2 = D.theta2.comp map2

namespace DeningerArithmeticThreeTermFlowChainMap

variable
  {C : DeningerArithmeticThreeTermFlow R A0 A1 A2}
  {D : DeningerArithmeticThreeTermFlow R B0 B1 B2}

/-- Upgrade a chain map after proving the three flow-intertwining squares. -/
def ofChainMap
    (F : DeningerArithmeticThreeTermChainMap C.complex D.complex)
    (h0 : F.map0.comp C.theta0 = D.theta0.comp F.map0)
    (h1 : F.map1.comp C.theta1 = D.theta1.comp F.map1)
    (h2 : F.map2.comp C.theta2 = D.theta2.comp F.map2) :
    DeningerArithmeticThreeTermFlowChainMap C D where
  toDeningerArithmeticThreeTermChainMap := F
  commutes_theta0 := h0
  commutes_theta1 := h1
  commutes_theta2 := h2

variable (F : DeningerArithmeticThreeTermFlowChainMap C D)

/-- The induced degree-zero map intertwines the cohomological generators. -/
theorem mapH0_comp_thetaH0 :
    F.toDeningerArithmeticThreeTermChainMap.mapH0.comp C.thetaH0 =
      D.thetaH0.comp F.toDeningerArithmeticThreeTermChainMap.mapH0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun F.commutes_theta0 (x : A0)

/-- The induced middle-cohomology map intertwines the cohomological generators. -/
theorem mapH1_comp_thetaH1 :
    F.toDeningerArithmeticThreeTermChainMap.mapH1.comp C.thetaH1 =
      D.thetaH1.comp F.toDeningerArithmeticThreeTermChainMap.mapH1 := by
  apply LinearMap.ext
  intro q
  let BA := C.complex.boundaries1.comap C.complex.cycles1.subtype
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective BA q
  simp only [LinearMap.comp_apply,
    DeningerArithmeticThreeTermFlow.thetaH1_mk,
    DeningerArithmeticThreeTermChainMap.mapH1_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact LinearMap.congr_fun F.commutes_theta1 (x : A1)

/-- The induced degree-two map intertwines the cohomological generators. -/
theorem mapH2_comp_thetaH2 :
    F.toDeningerArithmeticThreeTermChainMap.mapH2.comp C.thetaH2 =
      D.thetaH2.comp F.toDeningerArithmeticThreeTermChainMap.mapH2 := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ :=
    Submodule.Quotient.mk_surjective C.complex.boundaries2 q
  simp only [LinearMap.comp_apply,
    DeningerArithmeticThreeTermFlow.thetaH2_mk,
    DeningerArithmeticThreeTermChainMap.mapH2_mk]
  apply congrArg Submodule.Quotient.mk
  exact LinearMap.congr_fun F.commutes_theta2 x

end DeningerArithmeticThreeTermFlowChainMap

end FlowEquivariantChainMap

section TwoColumnFlowNaturality

variable {R A A' B B' : Type*}
variable [CommRing R]
variable [AddCommGroup A] [Module R A]
variable [AddCommGroup A'] [Module R A']
variable [AddCommGroup B] [Module R B]
variable [AddCommGroup B'] [Module R B']

/-- Two component flow squares assemble to the product-column flow square. -/
theorem deningerTwoColumnComponentMap_intertwines
    (left : A →ₗ[R] B)
    (right : A' →ₗ[R] B')
    (thetaA : Module.End R A)
    (thetaA' : Module.End R A')
    (thetaB : Module.End R B)
    (thetaB' : Module.End R B')
    (hleft : left.comp thetaA = thetaB.comp left)
    (hright : right.comp thetaA' = thetaB'.comp right) :
    (deningerTwoColumnComponentMap left right).comp
        (deningerTwoColumnProductEnd thetaA thetaA') =
      (deningerTwoColumnProductEnd thetaB thetaB').comp
        (deningerTwoColumnComponentMap left right) := by
  apply LinearMap.ext
  rintro ⟨a, a'⟩
  apply Prod.ext
  · exact LinearMap.congr_fun hleft a
  · exact LinearMap.congr_fun hright a'

end TwoColumnFlowNaturality

section GraphIntertwining

variable {E F ι : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- A cross-space linear map intertwining two families of partially defined graph monomials. -/
structure DeningerGraphIntertwining
    (P : ι → (E →ₗ.[ℂ] E))
    (Q : ι → (F →ₗ.[ℂ] F))
    (T : E →ₗ[ℂ] F) : Prop where
  /-- Every source monomial domain maps into the corresponding target domain. -/
  mapsTo : ∀ (i : ι) (x : E), x ∈ (P i).domain → T x ∈ (Q i).domain
  /-- Target and source monomial actions agree after applying the map. -/
  intertwines : ∀ (i : ι) (x : E) (hx : x ∈ (P i).domain),
    (Q i) ⟨T x, mapsTo i x hx⟩ = T ((P i) ⟨x, hx⟩)

variable
  {P : ι → (E →ₗ.[ℂ] E)}
  {Q : ι → (F →ₗ.[ℂ] F)}
  {T : E →ₗ[ℂ] F}

/-- A partial-operator intertwiner maps the source common graph core into the target core. -/
theorem deningerGraphCore_map_mem_of_intertwining
    (h : DeningerGraphIntertwining P Q T)
    {x : E} (hx : x ∈ deningerGraphCore P) :
    T x ∈ deningerGraphCore Q :=
  mem_deningerGraphCore.mpr fun i =>
    h.mapsTo i x (mem_deningerGraphCore.mp hx i)

/-- An ambient norm bound transfers, with the same constant, to every intertwined graph seminorm. -/
theorem deningerGraphSeminorm_map_le
    (h : DeningerGraphIntertwining P Q T)
    {c : ℝ} (hc : ∀ y : E, ‖T y‖ ≤ c * ‖y‖)
    (i : ι) {x : E} (hx : x ∈ deningerGraphCore P) :
    deningerGraphSeminorm Q i
        (deningerGraphCore_map_mem_of_intertwining h hx) ≤
      c * deningerGraphSeminorm P i hx := by
  have hxi : x ∈ (P i).domain := mem_deningerGraphCore.mp hx i
  have hintertwines :
      (Q i) ⟨T x, h.mapsTo i x hxi⟩ = T ((P i) ⟨x, hxi⟩) :=
    h.intertwines i x hxi
  show ‖(Q i) ⟨T x, _⟩‖ ≤ c * ‖(P i) ⟨x, _⟩‖
  rw [hintertwines]
  exact hc _

end GraphIntertwining

end RHTower
