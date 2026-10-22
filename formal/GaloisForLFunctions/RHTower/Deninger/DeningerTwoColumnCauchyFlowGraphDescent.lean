import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCauchyCohomologyDescent
import GaloisForLFunctions.RHTower.Deninger.DeningerSkewAdjointGraphCore

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

/-- The linear map induced on common graph cores by a partial-operator intertwiner. -/
def deningerGraphCoreMap
    (h : DeningerGraphIntertwining P Q T) :
    deningerGraphCore P →ₗ[ℂ] deningerGraphCore Q where
  toFun x := ⟨T x, deningerGraphCore_map_mem_of_intertwining h x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add T x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul T c x.1

@[simp]
theorem deningerGraphCoreMap_coe
    (h : DeningerGraphIntertwining P Q T)
    (x : deningerGraphCore P) :
    ((deningerGraphCoreMap h x : deningerGraphCore Q) : F) = T (x : E) :=
  rfl

/-- Intertwining right inverses remain right inverses after restriction to graph cores. -/
theorem deningerGraphCoreMap_comp_rightInverse
    {S : F →ₗ[ℂ] E}
    (hT : DeningerGraphIntertwining P Q T)
    (hS : DeningerGraphIntertwining Q P S)
    (hTS : T.comp S = LinearMap.id) :
    (deningerGraphCoreMap hT).comp (deningerGraphCoreMap hS) =
      LinearMap.id := by
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  exact LinearMap.congr_fun hTS (y : F)

/-- A split partial-operator intertwiner is surjective on the common graph core. -/
theorem deningerGraphCoreMap_surjective_of_rightInverse
    {S : F →ₗ[ℂ] E}
    (hT : DeningerGraphIntertwining P Q T)
    (hS : DeningerGraphIntertwining Q P S)
    (hTS : T.comp S = LinearMap.id) :
    Function.Surjective (deningerGraphCoreMap hT) := by
  intro y
  refine ⟨deningerGraphCoreMap hS y, ?_⟩
  exact LinearMap.congr_fun
    (deningerGraphCoreMap_comp_rightInverse hT hS hTS) y

end GraphIntertwining

section TwoColumnSignatureFlowData

variable (R G00 G10 G01 G11 S : Type*)
variable [CommRing R]
variable [AddCommGroup G00] [Module R G00]
variable [AddCommGroup G10] [Module R G10]
variable [AddCommGroup G01] [Module R G01]
variable [AddCommGroup G11] [Module R G11]
variable [AddCommGroup S] [Module R S]

/-- A two-column Rost--Schmid/signature column together with its five component transverse
generators and the six squares that make them a flow on the three-term totalization. -/
structure DeningerTwoColumnSignatureFlowData where
  horizontal0 : G00 →ₗ[R] G10
  horizontal1 : G01 →ₗ[R] G11
  vertical0 : G00 →ₗ[R] G01
  vertical1 : G10 →ₗ[R] G11
  signature10 : G10 →ₗ[R] S
  signature01 : G01 →ₗ[R] S
  square : vertical1.comp horizontal0 = horizontal1.comp vertical0
  signatureRelation : signature10.comp horizontal0 + signature01.comp vertical0 = 0
  theta00 : Module.End R G00
  theta10 : Module.End R G10
  theta01 : Module.End R G01
  theta11 : Module.End R G11
  thetaS : Module.End R S
  flowHorizontal0 : horizontal0.comp theta00 = theta10.comp horizontal0
  flowVertical0 : vertical0.comp theta00 = theta01.comp vertical0
  flowHorizontal1 : horizontal1.comp theta01 = theta11.comp horizontal1
  flowVertical1 : vertical1.comp theta10 = theta11.comp vertical1
  flowSignature10 : signature10.comp theta10 = thetaS.comp signature10
  flowSignature01 : signature01.comp theta01 = thetaS.comp signature01

namespace DeningerTwoColumnSignatureFlowData

variable {R G00 G10 G01 G11 S}

/-- The three-term flow totalization of a two-column signature column. -/
def flow (F : DeningerTwoColumnSignatureFlowData R G00 G10 G01 G11 S) :
    DeningerArithmeticThreeTermFlow R G00 (G10 × G01) (G11 × S) :=
  deningerTwoColumnSignatureFlow F.horizontal0 F.horizontal1 F.vertical0 F.vertical1
    F.signature10 F.signature01 F.square F.signatureRelation
    F.theta00 F.theta10 F.theta01 F.theta11 F.thetaS
    F.flowHorizontal0 F.flowVertical0 F.flowHorizontal1 F.flowVertical1
    F.flowSignature10 F.flowSignature01

end DeningerTwoColumnSignatureFlowData

end TwoColumnSignatureFlowData

section TwoColumnCauchyFlowAssembly

variable {R A00 A10 A01 A11 AS B00 B10 B01 B11 BS : Type*}
variable [CommRing R]
variable [AddCommGroup A00] [Module R A00]
variable [AddCommGroup A10] [Module R A10]
variable [AddCommGroup A01] [Module R A01]
variable [AddCommGroup A11] [Module R A11]
variable [AddCommGroup AS] [Module R AS]
variable [AddCommGroup B00] [Module R B00]
variable [AddCommGroup B10] [Module R B10]
variable [AddCommGroup B01] [Module R B01]
variable [AddCommGroup B11] [Module R B11]
variable [AddCommGroup BS] [Module R BS]

/-- Five componentwise Cauchy restrictions between two two-column signature columns, subject to
the six Rost--Schmid/signature naturality squares and the five component flow squares. -/
structure DeningerTwoColumnCauchyFlowRestriction
    (A : DeningerTwoColumnSignatureFlowData R A00 A10 A01 A11 AS)
    (B : DeningerTwoColumnSignatureFlowData R B00 B10 B01 B11 BS) where
  restrict00 : A00 →ₗ[R] B00
  restrict10 : A10 →ₗ[R] B10
  restrict01 : A01 →ₗ[R] B01
  restrict11 : A11 →ₗ[R] B11
  restrictS : AS →ₗ[R] BS
  naturalHorizontal0 : restrict10.comp A.horizontal0 = B.horizontal0.comp restrict00
  naturalVertical0 : restrict01.comp A.vertical0 = B.vertical0.comp restrict00
  naturalHorizontal1 : restrict11.comp A.horizontal1 = B.horizontal1.comp restrict01
  naturalVertical1 : restrict11.comp A.vertical1 = B.vertical1.comp restrict10
  naturalSignature10 : restrictS.comp A.signature10 = B.signature10.comp restrict10
  naturalSignature01 : restrictS.comp A.signature01 = B.signature01.comp restrict01
  flow00 : restrict00.comp A.theta00 = B.theta00.comp restrict00
  flow10 : restrict10.comp A.theta10 = B.theta10.comp restrict10
  flow01 : restrict01.comp A.theta01 = B.theta01.comp restrict01
  flow11 : restrict11.comp A.theta11 = B.theta11.comp restrict11
  flowS : restrictS.comp A.thetaS = B.thetaS.comp restrictS

namespace DeningerTwoColumnCauchyFlowRestriction

variable
  {A : DeningerTwoColumnSignatureFlowData R A00 A10 A01 A11 AS}
  {B : DeningerTwoColumnSignatureFlowData R B00 B10 B01 B11 BS}
  (F : DeningerTwoColumnCauchyFlowRestriction A B)

/-- The six naturality squares assemble the five restrictions to a chain map of the three-term
totalizations. -/
def chainMap : DeningerArithmeticThreeTermChainMap A.flow.complex B.flow.complex :=
  deningerTwoColumnSignatureCauchyChainMap
    A.horizontal0 A.horizontal1 A.vertical0 A.vertical1 A.signature10 A.signature01
    A.square A.signatureRelation
    B.horizontal0 B.horizontal1 B.vertical0 B.vertical1 B.signature10 B.signature01
    B.square B.signatureRelation
    F.restrict00 F.restrict10 F.restrict01 F.restrict11 F.restrictS
    F.naturalHorizontal0 F.naturalVertical0 F.naturalHorizontal1 F.naturalVertical1
    F.naturalSignature10 F.naturalSignature01

/-- The five component flow squares upgrade the assembled chain map to a flow-equivariant one:
`R^q Θ_A^q = Θ_B^q R^q` in all three degrees, with `Θ^(1 : ℕ) = θ_{10} ⊕ θ_{01}` and
`Θ^(2 : ℕ) = θ_{11} ⊕ θ_S`. -/
def flowChainMap : DeningerArithmeticThreeTermFlowChainMap A.flow B.flow :=
  DeningerArithmeticThreeTermFlowChainMap.ofChainMap F.chainMap F.flow00
    (deningerTwoColumnComponentMap_intertwines F.restrict10 F.restrict01
      A.theta10 A.theta01 B.theta10 B.theta01 F.flow10 F.flow01)
    (deningerTwoColumnComponentMap_intertwines F.restrict11 F.restrictS
      A.theta11 A.thetaS B.theta11 B.thetaS F.flow11 F.flowS)

/-- Flow equivariance descends to `H⁰`. -/
theorem flowChainMap_mapH0_comp_thetaH0 :
    F.flowChainMap.toDeningerArithmeticThreeTermChainMap.mapH0.comp A.flow.thetaH0 =
      B.flow.thetaH0.comp
        F.flowChainMap.toDeningerArithmeticThreeTermChainMap.mapH0 :=
  DeningerArithmeticThreeTermFlowChainMap.mapH0_comp_thetaH0 F.flowChainMap

/-- Flow equivariance descends to `H¹`. -/
theorem flowChainMap_mapH1_comp_thetaH1 :
    F.flowChainMap.toDeningerArithmeticThreeTermChainMap.mapH1.comp A.flow.thetaH1 =
      B.flow.thetaH1.comp
        F.flowChainMap.toDeningerArithmeticThreeTermChainMap.mapH1 :=
  DeningerArithmeticThreeTermFlowChainMap.mapH1_comp_thetaH1 F.flowChainMap

/-- Flow equivariance descends to `H²`. -/
theorem flowChainMap_mapH2_comp_thetaH2 :
    F.flowChainMap.toDeningerArithmeticThreeTermChainMap.mapH2.comp A.flow.thetaH2 =
      B.flow.thetaH2.comp
        F.flowChainMap.toDeningerArithmeticThreeTermChainMap.mapH2 :=
  DeningerArithmeticThreeTermFlowChainMap.mapH2_comp_thetaH2 F.flowChainMap

end DeningerTwoColumnCauchyFlowRestriction

end TwoColumnCauchyFlowAssembly

end RHTower
