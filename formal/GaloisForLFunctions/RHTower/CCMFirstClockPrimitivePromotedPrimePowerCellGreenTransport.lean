import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedGammaCoPoissonGreenTransport
import GaloisForLFunctions.RHTower.DeningerCalderonWittSingularGammaTransgression

/-!
# Prime-power-cell Calderón--Witt Green transport

Route J requires independent Euler prime-power cells, including distinct
depths at one prime.  Existing all-prime Calderón--Witt source retains prime
labels but not Euler depth labels.  This module constructs required
finite-support source over `Nat.Primes × ℕ`.

It proves:

* componentwise vector-valued cup and exterior cup;
* every cross-cell pair is exact Milnor incidence;
* arbitrary diagonal packet-leg transport is a cup chain map;
* Gamma/co-Poisson interval cells define canonical diagonal transport;
* cell-labelled exterior cup has explicit Koszul--Green splitting;
* Green retraction is natural for diagonal transport;
* cross-cell Euler carriers are their own Green primitives.

Thus remaining analytic frontier is no longer source existence: it is
cofinal preservation and Hodge positivity of explicit incidence transport.
-/

open Complex
open scoped DirectSum

namespace RHTower

noncomputable section

/-! ## Prime-power-cell-labelled Calderón--Witt source -/

/-- Euler source cell: prime together with zero-based prime-power depth. -/
abbrev XiGammaEulerCalderonWittCell := Nat.Primes × ℕ

/--
Degree one with independent finite support in prime-power cells.  Retaining
the depth label prevents premature identification of different Euler powers
at the same prime.
-/
abbrev XiGammaEulerCalderonWittCellDegreeOne : Type :=
  ⨁ pe : XiGammaEulerCalderonWittCell,
    DeningerCalderonWittAlgebraicDegreeOne pe.1

/-- Cell-labelled algebraic suspension center. -/
abbrev XiGammaEulerCalderonWittCellDegreeTwo : Type :=
  ⨁ pe : XiGammaEulerCalderonWittCell,
    DeningerCalderonWittAlgebraicDegreeTwo pe.1

/-- Contribution of one labelled Euler cell to componentwise cup. -/
def xiGammaEulerCalderonWittCellCupContribution
    (pe : XiGammaEulerCalderonWittCell) :
    DeningerCalderonWittAlgebraicDegreeOne pe.1 →ₗ[ℂ]
      XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
        XiGammaEulerCalderonWittCellDegreeTwo where
  toFun x :=
    (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
      (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe).comp
      ((deningerCalderonWittAlgebraicCup pe.1 x).comp
        (DirectSum.component ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe))
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    simp

/-- Componentwise cup before any completion or orientation trace. -/
def xiGammaEulerCalderonWittCellCup :
    XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
      XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
        XiGammaEulerCalderonWittCellDegreeTwo :=
  DirectSum.toModule ℂ XiGammaEulerCalderonWittCell
    (XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
      XiGammaEulerCalderonWittCellDegreeTwo)
    xiGammaEulerCalderonWittCellCupContribution

@[simp]
theorem xiGammaEulerCalderonWittCellCup_lof_left
    (pe : XiGammaEulerCalderonWittCell)
    (x : DeningerCalderonWittAlgebraicDegreeOne pe.1)
    (y : XiGammaEulerCalderonWittCellDegreeOne) :
    xiGammaEulerCalderonWittCellCup
        (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe x) y =
      DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe
        (deningerCalderonWittAlgebraicCup pe.1 x
          (DirectSum.component ℂ XiGammaEulerCalderonWittCell
            (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe y)) := by
  rw [xiGammaEulerCalderonWittCellCup, DirectSum.toModule_lof]
  rfl

@[simp]
theorem xiGammaEulerCalderonWittCellCup_lof_same
    (pe : XiGammaEulerCalderonWittCell)
    (x y : DeningerCalderonWittAlgebraicDegreeOne pe.1) :
    xiGammaEulerCalderonWittCellCup
        (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe x)
        (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe y) =
      DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe
        (deningerCalderonWittAlgebraicCup pe.1 x y) := by
  rw [xiGammaEulerCalderonWittCellCup_lof_left,
    DirectSum.component.lof_self]

@[simp]
theorem xiGammaEulerCalderonWittCellCup_lof_ne
    {pe qe : XiGammaEulerCalderonWittCell}
    (hne : pe ≠ qe)
    (x : DeningerCalderonWittAlgebraicDegreeOne pe.1)
    (y : DeningerCalderonWittAlgebraicDegreeOne qe.1) :
    xiGammaEulerCalderonWittCellCup
        (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) pe x)
        (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) qe y) =
      0 := by
  rw [xiGammaEulerCalderonWittCellCup_lof_left,
    DirectSum.component.of]
  simp [hne.symm]

/-- Output cell is exactly local cup of matching input components. -/
theorem xiGammaEulerCalderonWittCellCup_component
    (pe : XiGammaEulerCalderonWittCell)
    (x y : XiGammaEulerCalderonWittCellDegreeOne) :
    DirectSum.component ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe
        (xiGammaEulerCalderonWittCellCup x y) =
      deningerCalderonWittAlgebraicCup pe.1
        (DirectSum.component ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe x)
        (DirectSum.component ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe y) := by
  induction x using DirectSum.induction_on with
  | zero =>
      simp
  | of qe x =>
      rw [← DirectSum.lof_eq_of
        (R := ℂ) (ι := XiGammaEulerCalderonWittCell)
        (M := fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) qe x]
      by_cases h : qe = pe
      · subst qe
        simp
      · rw [xiGammaEulerCalderonWittCellCup_lof_left,
          DirectSum.component.of, DirectSum.component.of]
        simp [h]
  | add x z hx hz =>
      simp only [map_add, LinearMap.add_apply]
      rw [hx, hz]

@[simp]
theorem xiGammaEulerCalderonWittCellCup_self
    (x : XiGammaEulerCalderonWittCellDegreeOne) :
    xiGammaEulerCalderonWittCellCup x x = 0 := by
  apply DirectSum.ext_component ℂ
  intro pe
  rw [xiGammaEulerCalderonWittCellCup_component]
  exact deningerCalderonWittAlgebraicCup_self pe.1 _

/-- Alternating form defining cell-labelled exterior cup. -/
def xiGammaEulerCalderonWittCellCupAlternating :
    XiGammaEulerCalderonWittCellDegreeOne [⋀^Fin 2]→ₗ[ℂ]
      XiGammaEulerCalderonWittCellDegreeTwo where
  toFun v := xiGammaEulerCalderonWittCellCup (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have hij' : v 0 = v 1 := by simpa using hij
      rw [hij', xiGammaEulerCalderonWittCellCup_self]
    · have hij' : v 1 = v 0 := by simpa using hij
      rw [hij', xiGammaEulerCalderonWittCellCup_self]
    · exact (hne rfl).elim

/-- Exterior-square cell cup. -/
def xiGammaEulerCalderonWittCellExteriorCup :
    (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) →ₗ[ℂ]
      XiGammaEulerCalderonWittCellDegreeTwo :=
  exteriorPower.alternatingMapLinearEquiv
    xiGammaEulerCalderonWittCellCupAlternating

@[simp]
theorem xiGammaEulerCalderonWittCellExteriorCup_ιMulti
    (v : Fin 2 → XiGammaEulerCalderonWittCellDegreeOne) :
    xiGammaEulerCalderonWittCellExteriorCup
        (exteriorPower.ιMulti ℂ 2 v) =
      xiGammaEulerCalderonWittCellCup (v 0) (v 1) := by
  change
    exteriorPower.alternatingMapLinearEquiv
        xiGammaEulerCalderonWittCellCupAlternating
        (exteriorPower.ιMulti ℂ 2 v) =
      xiGammaEulerCalderonWittCellCup (v 0) (v 1)
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Cellwise exact Milnor-incidence sector. -/
def xiGammaEulerCalderonWittCellMilnorIncidence :
    Submodule ℂ (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) :=
  LinearMap.ker xiGammaEulerCalderonWittCellExteriorCup

/--
Every cross-cell exterior product is an exact incidence class, including
different prime-power depths of the same prime.
-/
theorem xiGammaEulerCalderonWittCrossCell_mem_milnorIncidence
    {pe qe : XiGammaEulerCalderonWittCell}
    (hne : pe ≠ qe)
    (x : DeningerCalderonWittAlgebraicDegreeOne pe.1)
    (y : DeningerCalderonWittAlgebraicDegreeOne qe.1) :
    exteriorPower.ιMulti ℂ 2
        ![
          DirectSum.lof ℂ XiGammaEulerCalderonWittCell
            (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) pe x,
          DirectSum.lof ℂ XiGammaEulerCalderonWittCell
            (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) qe y] ∈
      xiGammaEulerCalderonWittCellMilnorIncidence := by
  change
    xiGammaEulerCalderonWittCellExteriorCup
      (exteriorPower.ιMulti ℂ 2
        ![
          DirectSum.lof ℂ XiGammaEulerCalderonWittCell
            (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) pe x,
          DirectSum.lof ℂ XiGammaEulerCalderonWittCell
            (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) qe y]) = 0
  rw [xiGammaEulerCalderonWittCellExteriorCup_ιMulti]
  exact xiGammaEulerCalderonWittCellCup_lof_ne hne x y

/-! ## Diagonal packet transport on labelled cells -/

/-- Diagonal packet-leg transport with one coefficient per Euler cell. -/
def xiGammaEulerCalderonWittCellDegreeOneTransport
    (c : XiGammaEulerCalderonWittCell → ℂ) :
    XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
      XiGammaEulerCalderonWittCellDegreeOne :=
  DirectSum.toModule ℂ XiGammaEulerCalderonWittCell
    XiGammaEulerCalderonWittCellDegreeOne
    (fun pe =>
      (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe).comp
      (deningerCalderonWittPacketLegTransport pe.1 (c pe)))

@[simp]
theorem xiGammaEulerCalderonWittCellDegreeOneTransport_lof
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (pe : XiGammaEulerCalderonWittCell)
    (x : DeningerCalderonWittAlgebraicDegreeOne pe.1) :
    xiGammaEulerCalderonWittCellDegreeOneTransport c
        (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe x) =
      DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe
        (deningerCalderonWittPacketLegTransport pe.1 (c pe) x) := by
  rw [xiGammaEulerCalderonWittCellDegreeOneTransport,
    DirectSum.toModule_lof]
  rfl

/-- Component formula for diagonal degree-one transport. -/
theorem xiGammaEulerCalderonWittCellDegreeOneTransport_component
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (pe : XiGammaEulerCalderonWittCell)
    (x : XiGammaEulerCalderonWittCellDegreeOne) :
    DirectSum.component ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe
        (xiGammaEulerCalderonWittCellDegreeOneTransport c x) =
      deningerCalderonWittPacketLegTransport pe.1 (c pe)
        (DirectSum.component ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe x) := by
  induction x using DirectSum.induction_on with
  | zero =>
      exact
        (map_zero
          (deningerCalderonWittPacketLegTransport pe.1 (c pe))).symm
  | of qe x =>
      rw [← DirectSum.lof_eq_of
        (R := ℂ) (ι := XiGammaEulerCalderonWittCell)
        (M := fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) qe x]
      by_cases h : qe = pe
      · subst qe
        simp
      · rw [xiGammaEulerCalderonWittCellDegreeOneTransport_lof,
          DirectSum.component.of, DirectSum.component.of]
        rw [dif_neg h, dif_neg h]
        exact
          (map_zero
            (deningerCalderonWittPacketLegTransport pe.1 (c pe))).symm
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]

/-- Diagonal boundary multiplier on labelled suspension centers. -/
def xiGammaEulerCalderonWittCellDegreeTwoTransport
    (c : XiGammaEulerCalderonWittCell → ℂ) :
    XiGammaEulerCalderonWittCellDegreeTwo →ₗ[ℂ]
      XiGammaEulerCalderonWittCellDegreeTwo :=
  DirectSum.toModule ℂ XiGammaEulerCalderonWittCell
    XiGammaEulerCalderonWittCellDegreeTwo
    (fun pe =>
      (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe).comp
      (deningerCalderonWittDegreeTwoBoundaryTransport pe.1 (c pe)))

@[simp]
theorem xiGammaEulerCalderonWittCellDegreeTwoTransport_lof
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (pe : XiGammaEulerCalderonWittCell)
    (z : DeningerCalderonWittAlgebraicDegreeTwo pe.1) :
    xiGammaEulerCalderonWittCellDegreeTwoTransport c
        (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe z) =
      DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe
        (deningerCalderonWittDegreeTwoBoundaryTransport pe.1 (c pe) z) := by
  rw [xiGammaEulerCalderonWittCellDegreeTwoTransport,
    DirectSum.toModule_lof]
  rfl

/-- Component formula for diagonal degree-two boundary transport. -/
theorem xiGammaEulerCalderonWittCellDegreeTwoTransport_component
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (pe : XiGammaEulerCalderonWittCell)
    (z : XiGammaEulerCalderonWittCellDegreeTwo) :
    DirectSum.component ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe
        (xiGammaEulerCalderonWittCellDegreeTwoTransport c z) =
      deningerCalderonWittDegreeTwoBoundaryTransport pe.1 (c pe)
        (DirectSum.component ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe z) := by
  induction z using DirectSum.induction_on with
  | zero =>
      simp
  | of qe z =>
      rw [← DirectSum.lof_eq_of
        (R := ℂ) (ι := XiGammaEulerCalderonWittCell)
        (M := fun re => DeningerCalderonWittAlgebraicDegreeTwo re.1) qe z]
      by_cases h : qe = pe
      · subst qe
        simp
      · rw [xiGammaEulerCalderonWittCellDegreeTwoTransport_lof,
          DirectSum.component.of, DirectSum.component.of]
        simp [h]
  | add z u hz hu =>
      simp only [map_add]
      rw [hz, hu]

/--
Cell-labelled cup is natural for arbitrary diagonal packet coefficients.
Each matching local cup sees exactly one transported rational-Witt leg.
-/
theorem xiGammaEulerCalderonWittCellCup_transport
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (x y : XiGammaEulerCalderonWittCellDegreeOne) :
    xiGammaEulerCalderonWittCellCup
        (xiGammaEulerCalderonWittCellDegreeOneTransport c x)
        (xiGammaEulerCalderonWittCellDegreeOneTransport c y) =
      xiGammaEulerCalderonWittCellDegreeTwoTransport c
        (xiGammaEulerCalderonWittCellCup x y) := by
  apply DirectSum.ext_component ℂ
  intro pe
  rw [xiGammaEulerCalderonWittCellCup_component,
    xiGammaEulerCalderonWittCellDegreeOneTransport_component,
    xiGammaEulerCalderonWittCellDegreeOneTransport_component,
    xiGammaEulerCalderonWittCellDegreeTwoTransport_component,
    xiGammaEulerCalderonWittCellCup_component]
  exact deningerCalderonWittAlgebraicCup_packetLegTransport pe.1
    (c pe)
    (DirectSum.component ℂ XiGammaEulerCalderonWittCell
      (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe x)
    (DirectSum.component ℂ XiGammaEulerCalderonWittCell
      (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe y)

/-- Exterior transport induced from cell-labelled degree one. -/
def xiGammaEulerCalderonWittCellExteriorTransport
    (c : XiGammaEulerCalderonWittCell → ℂ) :
    (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) →ₗ[ℂ]
      (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) :=
  exteriorPower.map 2
    (xiGammaEulerCalderonWittCellDegreeOneTransport c)

/--
Prime-power-cell transport is a chain map: vector-valued exterior cup is
formed before the diagonal Gamma/co-Poisson boundary is fused.
-/
theorem xiGammaEulerCalderonWittCellExteriorTransport_cup
    (c : XiGammaEulerCalderonWittCell → ℂ) :
    xiGammaEulerCalderonWittCellExteriorCup.comp
        (xiGammaEulerCalderonWittCellExteriorTransport c) =
      (xiGammaEulerCalderonWittCellDegreeTwoTransport c).comp
        xiGammaEulerCalderonWittCellExteriorCup := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro f
  unfold xiGammaEulerCalderonWittCellExteriorTransport
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
  rw [exteriorPower.map_apply_ιMulti,
    xiGammaEulerCalderonWittCellExteriorCup_ιMulti,
    xiGammaEulerCalderonWittCellExteriorCup_ιMulti]
  exact xiGammaEulerCalderonWittCellCup_transport c (f 0) (f 1)

/-- Canonical Gamma/co-Poisson coefficient family on Euler cells. -/
def xiGammaEulerCalderonWittGammaCoPoissonCoefficient
    (z w : ℂ) (pe : XiGammaEulerCalderonWittCell) : ℂ :=
  xiGammaEulerPrimitiveGammaCoPoissonCell pe z w

/--
Actual source-pointed Gamma/co-Poisson transport on all finitely supported
prime-power cells.
-/
def xiGammaEulerCalderonWittGammaCoPoissonExteriorTransport
    (z w : ℂ) :
    (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) →ₗ[ℂ]
      (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) :=
  xiGammaEulerCalderonWittCellExteriorTransport
    (xiGammaEulerCalderonWittGammaCoPoissonCoefficient z w)

/--
Gamma/co-Poisson cell family supplies exact cellwise boundary of full
labelled exterior source.
-/
theorem xiGammaEulerCalderonWittGammaCoPoissonExteriorTransport_cup
    (z w : ℂ) :
    xiGammaEulerCalderonWittCellExteriorCup.comp
        (xiGammaEulerCalderonWittGammaCoPoissonExteriorTransport z w) =
      (xiGammaEulerCalderonWittCellDegreeTwoTransport
        (xiGammaEulerCalderonWittGammaCoPoissonCoefficient z w)).comp
          xiGammaEulerCalderonWittCellExteriorCup := by
  exact xiGammaEulerCalderonWittCellExteriorTransport_cup
    (xiGammaEulerCalderonWittGammaCoPoissonCoefficient z w)

/-- Diagonal exterior transport preserves the exact cell incidence sector. -/
theorem xiGammaEulerCalderonWittCellExteriorTransport_mem_incidence
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (i : xiGammaEulerCalderonWittCellMilnorIncidence) :
    xiGammaEulerCalderonWittCellExteriorTransport c i.1 ∈
      xiGammaEulerCalderonWittCellMilnorIncidence := by
  change
    xiGammaEulerCalderonWittCellExteriorCup
        (xiGammaEulerCalderonWittCellExteriorTransport c i.1) = 0
  have hchain := LinearMap.congr_fun
    (xiGammaEulerCalderonWittCellExteriorTransport_cup c) i.1
  change
    xiGammaEulerCalderonWittCellExteriorCup
        (xiGammaEulerCalderonWittCellExteriorTransport c i.1) =
      xiGammaEulerCalderonWittCellDegreeTwoTransport c
        (xiGammaEulerCalderonWittCellExteriorCup i.1) at hchain
  rw [hchain, i.2, map_zero]

/-! ## Cell-labelled Koszul--Green splitting -/

/-- Cell exterior cup is onto every finite-support suspension center. -/
theorem xiGammaEulerCalderonWittCellExteriorCup_surjective :
    Function.Surjective xiGammaEulerCalderonWittCellExteriorCup := by
  intro z
  induction z using DirectSum.induction_on with
  | zero =>
      exact ⟨0, map_zero _⟩
  | of pe z =>
      rw [← DirectSum.lof_eq_of
        (R := ℂ) (ι := XiGammaEulerCalderonWittCell)
        (M := fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe z]
      obtain ⟨x, y, hxy⟩ :=
        deningerCalderonWittAlgebraicCup_exists_eq pe.1 z
      let v : Fin 2 → XiGammaEulerCalderonWittCellDegreeOne :=
        ![
          DirectSum.lof ℂ XiGammaEulerCalderonWittCell
            (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe x,
          DirectSum.lof ℂ XiGammaEulerCalderonWittCell
            (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe y]
      refine ⟨exteriorPower.ιMulti ℂ 2 v, ?_⟩
      rw [xiGammaEulerCalderonWittCellExteriorCup_ιMulti]
      simp [v, hxy]
  | add z u hz hu =>
      obtain ⟨a, ha⟩ := hz
      obtain ⟨b, hb⟩ := hu
      refine ⟨a + b, ?_⟩
      rw [map_add, ha, hb]

/-- Exterior multiplication on left in cell-labelled degree one. -/
def xiGammaEulerCalderonWittCellExteriorWedgeLeft
    (x : XiGammaEulerCalderonWittCellDegreeOne) :
    XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
      (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) :=
  (AlternatingMap.ofSubsingleton ℂ
      XiGammaEulerCalderonWittCellDegreeOne
      (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne)
      (0 : Fin 1)).symm
    ((exteriorPower.ιMulti ℂ 2).curryLeft x)

@[simp]
theorem xiGammaEulerCalderonWittCellExteriorWedgeLeft_apply
    (x y : XiGammaEulerCalderonWittCellDegreeOne) :
    xiGammaEulerCalderonWittCellExteriorWedgeLeft x y =
      exteriorPower.ιMulti ℂ 2 ![x, y] :=
  rfl

/-- One-cell canonical Green section into global labelled exterior square. -/
def xiGammaEulerCalderonWittOneCellExteriorCupSection
    (pe : XiGammaEulerCalderonWittCell) :
    DeningerCalderonWittAlgebraicDegreeTwo pe.1 →ₗ[ℂ]
      (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) :=
  (xiGammaEulerCalderonWittCellExteriorWedgeLeft
      (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe
        (deningerCalderonWittUnitDefect pe.1, 0))).comp
    ((DirectSum.lof ℂ XiGammaEulerCalderonWittCell
      (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe).comp
        (deningerCalderonWittCenterToDegreeOne pe.1))

/-- One-cell Green section retracts through cell exterior cup exactly. -/
theorem xiGammaEulerCalderonWittCellExteriorCup_oneCellSection
    (pe : XiGammaEulerCalderonWittCell) :
    xiGammaEulerCalderonWittCellExteriorCup.comp
        (xiGammaEulerCalderonWittOneCellExteriorCupSection pe) =
      DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply,
    xiGammaEulerCalderonWittOneCellExteriorCupSection,
    LinearMap.comp_apply, LinearMap.comp_apply,
    xiGammaEulerCalderonWittCellExteriorWedgeLeft_apply,
    xiGammaEulerCalderonWittCellExteriorCup_ιMulti]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [xiGammaEulerCalderonWittCellCup_lof_same]
  apply congrArg
    (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
      (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe)
  have hz := LinearMap.congr_fun
    (deningerCalderonWittExteriorCup_section pe.1) z
  simpa [LinearMap.comp_apply,
    deningerCalderonWittExteriorCupSection,
    deningerCalderonWittExteriorWedgeLeft_apply] using hz

/-- Canonical finite-support Green section over all prime-power cells. -/
def xiGammaEulerCalderonWittCellExteriorCupSection :
    XiGammaEulerCalderonWittCellDegreeTwo →ₗ[ℂ]
      (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) :=
  DirectSum.toModule ℂ XiGammaEulerCalderonWittCell
    (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne)
    xiGammaEulerCalderonWittOneCellExteriorCupSection

@[simp]
theorem xiGammaEulerCalderonWittCellExteriorCupSection_lof
    (pe : XiGammaEulerCalderonWittCell)
    (z : DeningerCalderonWittAlgebraicDegreeTwo pe.1) :
    xiGammaEulerCalderonWittCellExteriorCupSection
        (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeTwo qe.1) pe z) =
      xiGammaEulerCalderonWittOneCellExteriorCupSection pe z := by
  rw [xiGammaEulerCalderonWittCellExteriorCupSection,
    DirectSum.toModule_lof]

/-- Complete cell-labelled Koszul--Green section law. -/
theorem xiGammaEulerCalderonWittCellExteriorCup_section :
    xiGammaEulerCalderonWittCellExteriorCup.comp
        xiGammaEulerCalderonWittCellExteriorCupSection =
      LinearMap.id := by
  apply DirectSum.linearMap_ext ℂ
  intro pe
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [xiGammaEulerCalderonWittCellExteriorCupSection_lof]
  exact LinearMap.congr_fun
    (xiGammaEulerCalderonWittCellExteriorCup_oneCellSection pe) z

/-- Green retraction onto exact cell-labelled incidence relations. -/
def xiGammaEulerCalderonWittCellMilnorGreenRetraction :
    (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) →ₗ[ℂ]
      xiGammaEulerCalderonWittCellMilnorIncidence :=
  ((LinearMap.id -
      xiGammaEulerCalderonWittCellExteriorCupSection.comp
        xiGammaEulerCalderonWittCellExteriorCup)).codRestrict
    xiGammaEulerCalderonWittCellMilnorIncidence (fun w => by
      change
        xiGammaEulerCalderonWittCellExteriorCup
            (w -
              xiGammaEulerCalderonWittCellExteriorCupSection
                (xiGammaEulerCalderonWittCellExteriorCup w)) = 0
      rw [map_sub]
      have hw := LinearMap.congr_fun
        xiGammaEulerCalderonWittCellExteriorCup_section
        (xiGammaEulerCalderonWittCellExteriorCup w)
      simpa [LinearMap.comp_apply] using sub_eq_zero.mpr hw.symm)

@[simp]
theorem xiGammaEulerCalderonWittCellMilnorGreenRetraction_coe
    (w : ⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) :
    (xiGammaEulerCalderonWittCellMilnorGreenRetraction w :
        ⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) =
      w -
        xiGammaEulerCalderonWittCellExteriorCupSection
          (xiGammaEulerCalderonWittCellExteriorCup w) := by
  change
    ((LinearMap.id :
        (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) →ₗ[ℂ]
          (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne)) -
      xiGammaEulerCalderonWittCellExteriorCupSection.comp
        xiGammaEulerCalderonWittCellExteriorCup) w =
      w -
        xiGammaEulerCalderonWittCellExteriorCupSection
          (xiGammaEulerCalderonWittCellExteriorCup w)
  rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]

/--
One-cell Green section is natural for diagonal packet transport.  This is
the labelled global version of local source-before-boundary compatibility.
-/
theorem xiGammaEulerCalderonWittCellExteriorTransport_oneCellSection
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (pe : XiGammaEulerCalderonWittCell)
    (z : DeningerCalderonWittAlgebraicDegreeTwo pe.1) :
    xiGammaEulerCalderonWittCellExteriorTransport c
        (xiGammaEulerCalderonWittOneCellExteriorCupSection pe z) =
      xiGammaEulerCalderonWittOneCellExteriorCupSection pe
        (deningerCalderonWittDegreeTwoBoundaryTransport pe.1 (c pe) z) := by
  unfold xiGammaEulerCalderonWittCellExteriorTransport
    deningerCalderonWittDegreeTwoBoundaryTransport
  rw [xiGammaEulerCalderonWittOneCellExteriorCupSection,
    LinearMap.comp_apply, LinearMap.comp_apply,
    xiGammaEulerCalderonWittCellExteriorWedgeLeft_apply,
    exteriorPower.map_apply_ιMulti]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  apply congrArg
    (fun f : Fin 2 → XiGammaEulerCalderonWittCellDegreeOne =>
      exteriorPower.ιMulti ℂ 2 f)
  funext i
  fin_cases i
  · change
      xiGammaEulerCalderonWittCellDegreeOneTransport c
          (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
            (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe
            (deningerCalderonWittUnitDefect pe.1, 0)) =
        DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe
          (deningerCalderonWittUnitDefect pe.1, 0)
    rw [xiGammaEulerCalderonWittCellDegreeOneTransport_lof]
    simp [deningerCalderonWittPacketLegTransport]
  · change
      xiGammaEulerCalderonWittCellDegreeOneTransport c
          (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
            (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe
            (deningerCalderonWittCenterToDegreeOne pe.1 z)) =
        DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe
          (deningerCalderonWittCenterToDegreeOne pe.1 (c pe • z))
    rw [xiGammaEulerCalderonWittCellDegreeOneTransport_lof]
    apply congrArg
      (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
        (fun qe => DeningerCalderonWittAlgebraicDegreeOne qe.1) pe)
    exact
      deningerCalderonWittPacketLegTransport_centerToDegreeOne
        pe.1 (c pe) z

/-- Full cell-labelled Green section commutes with diagonal transport. -/
theorem xiGammaEulerCalderonWittCellExteriorTransport_section
    (c : XiGammaEulerCalderonWittCell → ℂ) :
    (xiGammaEulerCalderonWittCellExteriorTransport c).comp
        xiGammaEulerCalderonWittCellExteriorCupSection =
      xiGammaEulerCalderonWittCellExteriorCupSection.comp
        (xiGammaEulerCalderonWittCellDegreeTwoTransport c) := by
  apply DirectSum.linearMap_ext ℂ
  intro pe
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [xiGammaEulerCalderonWittCellExteriorCupSection_lof,
    xiGammaEulerCalderonWittCellDegreeTwoTransport_lof,
    xiGammaEulerCalderonWittCellExteriorCupSection_lof]
  exact
    xiGammaEulerCalderonWittCellExteriorTransport_oneCellSection c pe z

/-- Incidence restriction of diagonal cell transport. -/
def xiGammaEulerCalderonWittCellMilnorIncidenceTransport
    (c : XiGammaEulerCalderonWittCell → ℂ) :
    xiGammaEulerCalderonWittCellMilnorIncidence →ₗ[ℂ]
      xiGammaEulerCalderonWittCellMilnorIncidence where
  toFun i :=
    ⟨xiGammaEulerCalderonWittCellExteriorTransport c i.1,
      xiGammaEulerCalderonWittCellExteriorTransport_mem_incidence c i⟩
  map_add' i j := by
    apply Subtype.ext
    exact map_add (xiGammaEulerCalderonWittCellExteriorTransport c) i.1 j.1
  map_smul' a i := by
    apply Subtype.ext
    exact map_smul (xiGammaEulerCalderonWittCellExteriorTransport c) a i.1

@[simp]
theorem xiGammaEulerCalderonWittCellMilnorIncidenceTransport_coe
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (i : xiGammaEulerCalderonWittCellMilnorIncidence) :
    (xiGammaEulerCalderonWittCellMilnorIncidenceTransport c i :
        ⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) =
      xiGammaEulerCalderonWittCellExteriorTransport c i.1 :=
  rfl

/--
Cell-labelled Green retraction is natural for arbitrary diagonal
coefficients.  Remaining Route J problem is now exactly preservation of
cofinal admitted sector by this explicit incidence endomorphism.
-/
theorem xiGammaEulerCalderonWittCellMilnorGreenRetraction_transport
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (w : ⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) :
    xiGammaEulerCalderonWittCellMilnorGreenRetraction
        (xiGammaEulerCalderonWittCellExteriorTransport c w) =
      xiGammaEulerCalderonWittCellMilnorIncidenceTransport c
        (xiGammaEulerCalderonWittCellMilnorGreenRetraction w) := by
  apply Subtype.ext
  rw [xiGammaEulerCalderonWittCellMilnorGreenRetraction_coe,
    xiGammaEulerCalderonWittCellMilnorIncidenceTransport_coe,
    xiGammaEulerCalderonWittCellMilnorGreenRetraction_coe, map_sub]
  have hchain := LinearMap.congr_fun
    (xiGammaEulerCalderonWittCellExteriorTransport_cup c) w
  change
    xiGammaEulerCalderonWittCellExteriorCup
        (xiGammaEulerCalderonWittCellExteriorTransport c w) =
      xiGammaEulerCalderonWittCellDegreeTwoTransport c
        (xiGammaEulerCalderonWittCellExteriorCup w) at hchain
  rw [hchain]
  have hsection := LinearMap.congr_fun
    (xiGammaEulerCalderonWittCellExteriorTransport_section c)
    (xiGammaEulerCalderonWittCellExteriorCup w)
  change
    xiGammaEulerCalderonWittCellExteriorTransport c
        (xiGammaEulerCalderonWittCellExteriorCupSection
          (xiGammaEulerCalderonWittCellExteriorCup w)) =
      xiGammaEulerCalderonWittCellExteriorCupSection
        (xiGammaEulerCalderonWittCellDegreeTwoTransport c
          (xiGammaEulerCalderonWittCellExteriorCup w)) at hsection
  rw [← hsection]

/--
Cross-cell Euler carrier is its own Green primitive: no quotient or
orientation trace sees it.  This includes equal-prime, unequal-depth pairs.
-/
theorem xiGammaEulerCalderonWittCrossCell_greenRetraction_coe
    {pe qe : XiGammaEulerCalderonWittCell}
    (hne : pe ≠ qe)
    (x : DeningerCalderonWittAlgebraicDegreeOne pe.1)
    (y : DeningerCalderonWittAlgebraicDegreeOne qe.1) :
    (xiGammaEulerCalderonWittCellMilnorGreenRetraction
        (exteriorPower.ιMulti ℂ 2
          ![
            DirectSum.lof ℂ XiGammaEulerCalderonWittCell
              (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) pe x,
            DirectSum.lof ℂ XiGammaEulerCalderonWittCell
              (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) qe y]) :
      ⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) =
        exteriorPower.ιMulti ℂ 2
          ![
            DirectSum.lof ℂ XiGammaEulerCalderonWittCell
              (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) pe x,
            DirectSum.lof ℂ XiGammaEulerCalderonWittCell
              (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) qe y] := by
  rw [xiGammaEulerCalderonWittCellMilnorGreenRetraction_coe]
  have hcup :
      xiGammaEulerCalderonWittCellExteriorCup
          (exteriorPower.ιMulti ℂ 2
            ![
              DirectSum.lof ℂ XiGammaEulerCalderonWittCell
                (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) pe x,
              DirectSum.lof ℂ XiGammaEulerCalderonWittCell
                (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) qe y]) =
        0 :=
    xiGammaEulerCalderonWittCrossCell_mem_milnorIncidence hne x y
  rw [hcup, map_zero, sub_zero]

/-! ## Same-prime depth escape -/

/--
Unequal Euler depths at one prime have unequal source heights.  This fact
was invisible in the old all-prime source because it had no independent
depth labels.
-/
theorem xiGammaEulerBoundaryHalfHeight_samePrime_ne_of_depth_ne
    (p : Nat.Primes) {e f : ℕ} (hef : e ≠ f) :
    xiGammaEulerBoundaryHalfHeight p e ≠
      xiGammaEulerBoundaryHalfHeight p f := by
  intro hheight
  unfold xiGammaEulerBoundaryHalfHeight at hheight
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hefR : (e : ℝ) ≠ (f : ℝ) := by
    exact_mod_cast hef
  apply hefR
  nlinarith

/--
**Same-prime depth-escape theorem.**  The canonical defect/packet carrier
between unequal depths at one prime is exact incidence and is its own Green
primitive, yet every nonzero modular displacement gives it nonzero
reflection-odd Gamma coefficient.

Therefore any sector-preserving completion must carry a genuinely
depth-nonlocal countertransport even within each single prime.  Cross-prime
sewing alone cannot close Route J.
-/
theorem xiGammaEulerCalderonWittSamePrimeDepthCarrier_escape
    (p : Nat.Primes) {e f : ℕ} (hef : e ≠ f)
    {a : ℝ} (ha : a ≠ 0) :
    let pe : XiGammaEulerCalderonWittCell := (p, e)
    let qe : XiGammaEulerCalderonWittCell := (p, f)
    let carrier :=
      exteriorPower.ιMulti ℂ 2
        ![
          DirectSum.lof ℂ XiGammaEulerCalderonWittCell
            (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) pe
            (deningerCalderonWittUnitDefect p, 0),
          DirectSum.lof ℂ XiGammaEulerCalderonWittCell
            (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) qe
            (0, deningerCalderonWittAlgebraicUnitPacket p)]
    carrier ∈ xiGammaEulerCalderonWittCellMilnorIncidence ∧
      (xiGammaEulerCalderonWittCellMilnorGreenRetraction carrier :
          ⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) = carrier ∧
      xiGammaEulerPrimitiveReflectionOddExterior a pe qe ≠ 0 := by
  dsimp only
  have hcell : (p, e) ≠ (p, f) := by
    intro h
    exact hef (Prod.mk.inj h).2
  refine
    ⟨xiGammaEulerCalderonWittCrossCell_mem_milnorIncidence hcell
        (deningerCalderonWittUnitDefect p, 0)
        (0, deningerCalderonWittAlgebraicUnitPacket p),
      xiGammaEulerCalderonWittCrossCell_greenRetraction_coe hcell
        (deningerCalderonWittUnitDefect p, 0)
        (0, deningerCalderonWittAlgebraicUnitPacket p),
      ?_⟩
  exact xiGammaEulerPrimitiveReflectionOddExterior_ne_zero
    ha (p, e) (p, f)
      (xiGammaEulerBoundaryHalfHeight_samePrime_ne_of_depth_ne p hef)

end

end RHTower
