import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticTwoColumnSignatureTotalization

/-!
# Cauchy restriction descent to arithmetic cohomology

This module isolates the quotient argument behind the local-to-global
Green-energy radical.  Once full Cauchy restriction carries global
boundaries to local boundaries, it descends to cohomology.  If local
boundary membership jointly classifies global boundaries, then the
descended restrictions jointly detect every nonzero cohomology class.

No analytic zero set, positivity premise, or Riemann hypothesis is
used.
-/

namespace RHTower

section CauchyCohomologyDescent

variable {R V W ι : Type*}
variable [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/--
Full Cauchy restriction descended from cocycles modulo boundaries to
local harmonic classes modulo local boundaries.
-/
def deningerCauchyQuotientRestriction
    (globalBoundaries : Submodule R V)
    (localBoundaries : Submodule R W)
    (restriction : ι → V →ₗ[R] W)
    (hboundary :
      ∀ i x, x ∈ globalBoundaries →
        restriction i x ∈ localBoundaries)
    (i : ι) :
    (V ⧸ globalBoundaries) →ₗ[R] (W ⧸ localBoundaries) :=
  Submodule.mapQ globalBoundaries localBoundaries
    (restriction i) (hboundary i)

@[simp]
theorem deningerCauchyQuotientRestriction_mk
    (globalBoundaries : Submodule R V)
    (localBoundaries : Submodule R W)
    (restriction : ι → V →ₗ[R] W)
    (hboundary :
      ∀ i x, x ∈ globalBoundaries →
        restriction i x ∈ localBoundaries)
    (i : ι) (x : V) :
    deningerCauchyQuotientRestriction
        globalBoundaries localBoundaries restriction hboundary i
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (restriction i x) :=
  rfl

/--
If simultaneous local boundary membership classifies global
boundaries, the descended Cauchy restrictions jointly detect zero.
-/
theorem deningerCauchyQuotientRestrictions_eq_zero_iff
    (globalBoundaries : Submodule R V)
    (localBoundaries : Submodule R W)
    (restriction : ι → V →ₗ[R] W)
    (hboundary :
      ∀ i x, x ∈ globalBoundaries →
        restriction i x ∈ localBoundaries)
    (hlocal_boundary_classifies :
      ∀ x : V,
        (∀ i, restriction i x ∈ localBoundaries) →
          x ∈ globalBoundaries)
    (q : V ⧸ globalBoundaries) :
    (∀ i,
      deningerCauchyQuotientRestriction
        globalBoundaries localBoundaries restriction hboundary i q = 0) ↔
      q = 0 := by
  obtain ⟨x, rfl⟩ :=
    Submodule.Quotient.mk_surjective globalBoundaries q
  constructor
  · intro hlocal
    apply (Submodule.Quotient.mk_eq_zero globalBoundaries).2
    apply hlocal_boundary_classifies x
    intro i
    apply (Submodule.Quotient.mk_eq_zero localBoundaries).1
    exact hlocal i
  · intro hzero i
    simp only [hzero, map_zero]

/--
Local positive energies jointly detect global cohomology once their
zero classes are exactly local boundaries and Cauchy restrictions
classify the global boundary quotient.
-/
theorem deningerLocalCauchyEnergy_zero_iff_globalClass_zero
    (globalBoundaries : Submodule R V)
    (localBoundaries : Submodule R W)
    (restriction : ι → V →ₗ[R] W)
    (hboundary :
      ∀ i x, x ∈ globalBoundaries →
        restriction i x ∈ localBoundaries)
    (hlocal_boundary_classifies :
      ∀ x : V,
        (∀ i, restriction i x ∈ localBoundaries) →
          x ∈ globalBoundaries)
    (localEnergy : ι → (W ⧸ localBoundaries) → ℝ)
    (hlocal_detects :
      ∀ i q, localEnergy i q = 0 ↔ q = 0)
    (q : V ⧸ globalBoundaries) :
    (∀ i,
      localEnergy i
        (deningerCauchyQuotientRestriction
          globalBoundaries localBoundaries restriction hboundary i q) = 0) ↔
      q = 0 := by
  rw [← deningerCauchyQuotientRestrictions_eq_zero_iff
    globalBoundaries localBoundaries restriction hboundary
    hlocal_boundary_classifies q]
  exact forall_congr' fun i => hlocal_detects i _

end CauchyCohomologyDescent

section ThreeTermChainMap

variable {R A0 A1 A2 B0 B1 B2 : Type*}
variable [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]
variable [AddCommGroup B0] [Module R B0]
variable [AddCommGroup B1] [Module R B1]
variable [AddCommGroup B2] [Module R B2]

/--
A morphism of source three-term arithmetic cochain complexes.
Full Cauchy restriction must instantiate this structure: its two
fields are exactly commutation with the degree-zero and degree-one
Rost--Schmid/Milnor differentials.
-/
structure DeningerArithmeticThreeTermChainMap
    (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)
    (D : DeningerArithmeticThreeTermComplex R B0 B1 B2) where
  map0 : A0 →ₗ[R] B0
  map1 : A1 →ₗ[R] B1
  map2 : A2 →ₗ[R] B2
  commutes_d0 : map1.comp C.d0 = D.d0.comp map0
  commutes_d1 : map2.comp C.d1 = D.d1.comp map1

namespace DeningerArithmeticThreeTermChainMap

variable
  {C : DeningerArithmeticThreeTermComplex R A0 A1 A2}
  {D : DeningerArithmeticThreeTermComplex R B0 B1 B2}
  (F : DeningerArithmeticThreeTermChainMap C D)

/-- A three-term chain map preserves degree-zero cocycles. -/
def mapH0 : C.H0 →ₗ[R] D.H0 where
  toFun x := ⟨F.map0 x, by
    change D.d0 (F.map0 (x : A0)) = 0
    have h := LinearMap.congr_fun F.commutes_d0 (x : A0)
    change F.map1 (C.d0 (x : A0)) =
      D.d0 (F.map0 (x : A0)) at h
    rw [x.2, map_zero] at h
    exact h.symm⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add F.map0 x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul F.map0 c x.1

/-- Degree-one cocycles map to degree-one cocycles. -/
def mapCycles1 : C.cycles1 →ₗ[R] D.cycles1 where
  toFun x := ⟨F.map1 x, by
    change D.d1 (F.map1 (x : A1)) = 0
    have h := LinearMap.congr_fun F.commutes_d1 (x : A1)
    change F.map2 (C.d1 (x : A1)) =
      D.d1 (F.map1 (x : A1)) at h
    rw [x.2, map_zero] at h
    exact h.symm⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add F.map1 x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul F.map1 c x.1

/-- Degree-one boundaries map to degree-one boundaries. -/
theorem mapCycles1_mem_boundaries
    (x : C.cycles1)
    (hx : x ∈ C.boundaries1.comap C.cycles1.subtype) :
    F.mapCycles1 x ∈
      D.boundaries1.comap D.cycles1.subtype := by
  change F.map1 (x : A1) ∈ D.boundaries1
  change (x : A1) ∈ C.boundaries1 at hx
  obtain ⟨a, ha⟩ := hx
  refine ⟨F.map0 a, ?_⟩
  rw [← ha]
  exact (LinearMap.congr_fun F.commutes_d0 a).symm

/-- The induced map on arithmetic middle cohomology. -/
def mapH1 : C.H1 →ₗ[R] D.H1 :=
  Submodule.mapQ
    (C.boundaries1.comap C.cycles1.subtype)
    (D.boundaries1.comap D.cycles1.subtype)
    F.mapCycles1
    F.mapCycles1_mem_boundaries

@[simp]
theorem mapH1_mk (x : C.cycles1) :
    F.mapH1 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.mapCycles1 x) :=
  rfl

/--
**Middle conservativity from exact homotopy fibre.**  A class in the
kernel of `H¹(F)` is represented by a source cocycle `x` whose image
has a target primitive `y`.  If every such fibre cocycle `(x,y)`
lifts from one source degree-zero cochain, then the induced map on
middle cohomology is injective.

This is the three-term, elementwise form of
`H¹(Fib F) = 0 → Function.Injective H¹(F)`.  The paired lifting
hypothesis includes the degree-zero compatibility; no separate
surjectivity assumption on `F.map0` is hidden.
-/
theorem mapH1_injective_of_fiberH1_exact
    (hfiber : ∀ (x : A1) (y : B0),
      C.d1 x = 0 →
      F.map1 x = D.d0 y →
      ∃ a : A0, C.d0 a = x ∧ F.map0 a = y) :
    Function.Injective F.mapH1 := by
  have hkernel : ∀ q : C.H1, F.mapH1 q = 0 → q = 0 := by
    intro q hq
    let BC := C.boundaries1.comap C.cycles1.subtype
    let BD := D.boundaries1.comap D.cycles1.subtype
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective BC q
    rw [mapH1_mk] at hq
    have hlocal : F.mapCycles1 x ∈ BD :=
      (Submodule.Quotient.mk_eq_zero BD).1 hq
    change F.map1 (x : A1) ∈ D.boundaries1 at hlocal
    obtain ⟨y, hy⟩ := hlocal
    obtain ⟨a, ha, _⟩ := hfiber (x : A1) y x.2 hy.symm
    apply (Submodule.Quotient.mk_eq_zero BC).2
    change (x : A1) ∈ C.boundaries1
    exact ⟨a, ha⟩
  intro q r hqr
  apply sub_eq_zero.mp
  apply hkernel (q - r)
  rw [map_sub, hqr, sub_self]

/-- Degree-two boundaries map to degree-two boundaries. -/
theorem map2_mem_boundaries
    (x : A2) (hx : x ∈ C.boundaries2) :
    F.map2 x ∈ D.boundaries2 := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨F.map1 a, ?_⟩
  exact (LinearMap.congr_fun F.commutes_d1 a).symm

/-- The induced map on arithmetic top cohomology. -/
def mapH2 : C.H2 →ₗ[R] D.H2 :=
  Submodule.mapQ C.boundaries2 D.boundaries2
    F.map2 F.map2_mem_boundaries

@[simp]
theorem mapH2_mk (x : A2) :
    F.mapH2 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.map2 x) :=
  rfl

end DeningerArithmeticThreeTermChainMap

end ThreeTermChainMap

section TwoColumnCauchyFunctoriality

variable
  {R A00 A10 A01 A11 AS B00 B10 B01 B11 BS : Type*}
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

/-- Componentwise linear map between two product columns. -/
def deningerTwoColumnComponentMap
    (left : A10 →ₗ[R] B10)
    (right : A01 →ₗ[R] B01) :
    (A10 × A01) →ₗ[R] (B10 × B01) where
  toFun x := (left x.1, right x.2)
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

@[simp]
theorem deningerTwoColumnComponentMap_apply
    (left : A10 →ₗ[R] B10)
    (right : A01 →ₗ[R] B01)
    (x : A10 × A01) :
    deningerTwoColumnComponentMap left right x =
      (left x.1, right x.2) :=
  rfl

/--
Componentwise full-Cauchy maps commuting with the two Rost--Schmid
arrows and both real-signature arrows assemble to a chain map of the
three-term arithmetic totalizations.
-/
def deningerTwoColumnSignatureCauchyChainMap
    (aHorizontal0 : A00 →ₗ[R] A10)
    (aHorizontal1 : A01 →ₗ[R] A11)
    (aVertical0 : A00 →ₗ[R] A01)
    (aVertical1 : A10 →ₗ[R] A11)
    (aSignature10 : A10 →ₗ[R] AS)
    (aSignature01 : A01 →ₗ[R] AS)
    (aSquare :
      aVertical1.comp aHorizontal0 =
        aHorizontal1.comp aVertical0)
    (aSignature :
      aSignature10.comp aHorizontal0 +
        aSignature01.comp aVertical0 = 0)
    (bHorizontal0 : B00 →ₗ[R] B10)
    (bHorizontal1 : B01 →ₗ[R] B11)
    (bVertical0 : B00 →ₗ[R] B01)
    (bVertical1 : B10 →ₗ[R] B11)
    (bSignature10 : B10 →ₗ[R] BS)
    (bSignature01 : B01 →ₗ[R] BS)
    (bSquare :
      bVertical1.comp bHorizontal0 =
        bHorizontal1.comp bVertical0)
    (bSignature :
      bSignature10.comp bHorizontal0 +
        bSignature01.comp bVertical0 = 0)
    (restrict00 : A00 →ₗ[R] B00)
    (restrict10 : A10 →ₗ[R] B10)
    (restrict01 : A01 →ₗ[R] B01)
    (restrict11 : A11 →ₗ[R] B11)
    (restrictS : AS →ₗ[R] BS)
    (hHorizontal0 :
      restrict10.comp aHorizontal0 =
        bHorizontal0.comp restrict00)
    (hVertical0 :
      restrict01.comp aVertical0 =
        bVertical0.comp restrict00)
    (hHorizontal1 :
      restrict11.comp aHorizontal1 =
        bHorizontal1.comp restrict01)
    (hVertical1 :
      restrict11.comp aVertical1 =
        bVertical1.comp restrict10)
    (hSignature10 :
      restrictS.comp aSignature10 =
        bSignature10.comp restrict10)
    (hSignature01 :
      restrictS.comp aSignature01 =
        bSignature01.comp restrict01) :
    DeningerArithmeticThreeTermChainMap
      (deningerTwoColumnSignatureComplex
        aHorizontal0 aHorizontal1 aVertical0 aVertical1
        aSignature10 aSignature01 aSquare aSignature)
      (deningerTwoColumnSignatureComplex
        bHorizontal0 bHorizontal1 bVertical0 bVertical1
        bSignature10 bSignature01 bSquare bSignature) where
  map0 := restrict00
  map1 :=
    deningerTwoColumnComponentMap restrict10 restrict01
  map2 :=
    deningerTwoColumnComponentMap restrict11 restrictS
  commutes_d0 := by
    apply LinearMap.ext
    intro a
    apply Prod.ext
    · exact LinearMap.congr_fun hHorizontal0 a
    · exact LinearMap.congr_fun hVertical0 a
  commutes_d1 := by
    apply LinearMap.ext
    rintro ⟨c, b⟩
    apply Prod.ext
    · have hc := LinearMap.congr_fun hVertical1 c
      have hb := LinearMap.congr_fun hHorizontal1 b
      change restrict11 (aVertical1 c) =
        bVertical1 (restrict10 c) at hc
      change restrict11 (aHorizontal1 b) =
        bHorizontal1 (restrict01 b) at hb
      change
        restrict11 (aVertical1 c - aHorizontal1 b) =
          bVertical1 (restrict10 c) -
            bHorizontal1 (restrict01 b)
      rw [map_sub, hc, hb]
    · have hc := LinearMap.congr_fun hSignature10 c
      have hb := LinearMap.congr_fun hSignature01 b
      change restrictS (aSignature10 c) =
        bSignature10 (restrict10 c) at hc
      change restrictS (aSignature01 b) =
        bSignature01 (restrict01 b) at hb
      change
        restrictS (aSignature10 c + aSignature01 b) =
          bSignature10 (restrict10 c) +
            bSignature01 (restrict01 b)
      rw [map_add, hc, hb]

end TwoColumnCauchyFunctoriality

end RHTower
