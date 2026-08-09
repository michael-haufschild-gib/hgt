import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedCofinalDepthCountertransport
import GaloisForLFunctions.RHTower.DeningerCalderonWittGammaCoPoissonHodgeBoundaryComparison

/-!
# Prime-power-cell Hodge-boundary diagonal rigidity

The cofinal depth countertransport has a bounded landed coefficient profile
fixed by a compensated reflection of its finite depth indices.  Actual
Gamma/Hardy Hodge admission is stronger: its reflection defect is evaluated
before scalar fusion and retains every ordered prime/depth coordinate.

This module constructs that cell-labelled boundary map.  On the canonical
defect-at-`i`, packet-at-`j` exterior carrier, its `(i,j)` coordinate is
exactly the source reflection-odd Gamma coefficient.  Distinct ordered
coordinates do not cancel.  Consequently every nonzero finite canonical
depth spread escapes the actual admitted sector at nonzero modular
displacement.  The positive survivor is diagonal rigidity: an admitted
Route-J carrier must leave the finite canonical defect--packet span and
be genuinely relation-valued at completion.
-/

open Complex
open scoped DirectSum

namespace RHTower

noncomputable section

namespace PrimitivePromotedCellHodgeRigidity

/-- Extract the normalized Calderón defect coordinate from one labelled
prime-power cell. -/
def cellDefectCoordinate
    (pe : XiGammaEulerCalderonWittCell) :
    XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ] ℂ :=
  (deningerCalderonWittLocalDefectCoordinate pe.1).comp
    (DirectSum.component ℂ XiGammaEulerCalderonWittCell
      (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) pe)

/-- Extract and suspend the rational-Witt packet coordinate from one
labelled prime-power cell. -/
def cellPacketFirstMode
    (qe : XiGammaEulerCalderonWittCell) :
    XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeTwo qe.1 :=
  (deningerCalderonWittLocalPacketFirstMode qe.1).comp
    (DirectSum.component ℂ XiGammaEulerCalderonWittCell
      (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1) qe)

/--
Ordered cell cross-effect: defect at `pe` acts on the packet suspension at
`qe`.  Both cell labels survive exterior multiplication.
-/
def cellNonlocalCrossEffect
    (pe qe : XiGammaEulerCalderonWittCell) :
    XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
      XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
        DeningerCalderonWittAlgebraicDegreeTwo qe.1 where
  toFun x :=
    { toFun := fun y =>
        cellDefectCoordinate pe x • cellPacketFirstMode qe y -
          cellDefectCoordinate pe y • cellPacketFirstMode qe x
      map_add' := by
        intro y z
        simp only [map_add, smul_add, add_smul]
        module
      map_smul' := by
        intro c y
        simp only [map_smul, RingHom.id_apply, smul_sub, smul_smul]
        module }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change
      cellDefectCoordinate pe (x + z) •
            cellPacketFirstMode qe y -
          cellDefectCoordinate pe y •
            cellPacketFirstMode qe (x + z) =
        (cellDefectCoordinate pe x •
              cellPacketFirstMode qe y -
            cellDefectCoordinate pe y •
              cellPacketFirstMode qe x) +
          (cellDefectCoordinate pe z •
              cellPacketFirstMode qe y -
            cellDefectCoordinate pe y •
              cellPacketFirstMode qe z)
    rw [map_add, map_add, add_smul, smul_add]
    abel
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    change
      cellDefectCoordinate pe (c • x) •
            cellPacketFirstMode qe y -
          cellDefectCoordinate pe y •
            cellPacketFirstMode qe (c • x) =
        c •
          (cellDefectCoordinate pe x •
              cellPacketFirstMode qe y -
            cellDefectCoordinate pe y •
              cellPacketFirstMode qe x)
    rw [map_smul, map_smul, smul_sub, smul_smul, smul_smul]
    module

@[simp]
theorem cellNonlocalCrossEffect_self
    (pe qe : XiGammaEulerCalderonWittCell)
    (x : XiGammaEulerCalderonWittCellDegreeOne) :
    cellNonlocalCrossEffect pe qe x x = 0 := by
  simp [cellNonlocalCrossEffect]

/-- Scalar multiplication is applied only after the vector-valued
cross-effect. -/
def cellWeightedNonlocalCrossEffect
    (c : ℂ) (pe qe : XiGammaEulerCalderonWittCell) :
    XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
      XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ]
        DeningerCalderonWittAlgebraicDegreeTwo qe.1 :=
  c • cellNonlocalCrossEffect pe qe

/-- Alternating map underlying the weighted ordered-cell cross-effect. -/
def cellWeightedNonlocalAlternating
    (c : ℂ) (pe qe : XiGammaEulerCalderonWittCell) :
    XiGammaEulerCalderonWittCellDegreeOne [⋀^Fin 2]→ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeTwo qe.1 where
  toFun v := cellWeightedNonlocalCrossEffect c pe qe (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp [cellWeightedNonlocalCrossEffect]
  map_update_smul' v i c' x := by
    fin_cases i <;> simp [cellWeightedNonlocalCrossEffect]
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have hij' : v 0 = v 1 := by simpa using hij
      rw [hij']
      simp [cellWeightedNonlocalCrossEffect]
    · have hij' : v 1 = v 0 := by simpa using hij
      rw [hij']
      simp [cellWeightedNonlocalCrossEffect]
    · exact (hne rfl).elim

/-- Exterior linearization of the ordered-cell cross-effect. -/
def cellWeightedNonlocalExterior
    (c : ℂ) (pe qe : XiGammaEulerCalderonWittCell) :
    (⋀[ℂ]^2 XiGammaEulerCalderonWittCellDegreeOne) →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeTwo qe.1 :=
  exteriorPower.alternatingMapLinearEquiv
    (cellWeightedNonlocalAlternating c pe qe)

@[simp]
theorem cellWeightedNonlocalExterior_ιMulti
    (c : ℂ) (pe qe : XiGammaEulerCalderonWittCell)
    (v : Fin 2 → XiGammaEulerCalderonWittCellDegreeOne) :
    cellWeightedNonlocalExterior c pe qe
        (exteriorPower.ιMulti ℂ 2 v) =
      cellWeightedNonlocalCrossEffect c pe qe (v 0) (v 1) := by
  rw [cellWeightedNonlocalExterior,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/--
One ordered coordinate of the actual cell-labelled Gamma/Hardy reflection
defect.  The coefficient is the same reflection-odd primitive Gamma
coefficient identified by the polarized boundary comparison.
-/
def cellReflectionOddBoundaryCoordinate
    (a : ℝ) (pe qe : XiGammaEulerCalderonWittCell) :
    (⋀[ℂ]^2 XiGammaEulerCalderonWittCellDegreeOne) →ₗ[ℂ] ℂ :=
  (deningerCalderonWittAlgebraicCenterTrace qe.1).comp
    (cellWeightedNonlocalExterior
      (xiGammaEulerPrimitiveReflectionOddExterior a pe qe : ℂ) pe qe)

/-- The coefficient used by the cell boundary is literally the value of the
actual Gamma/Hardy boundary reflection defect on the global canonical
cross-prime witness. -/
theorem reflectionOddCoefficient_eq_actualGammaHardyBoundary
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (e f : ℕ) :
    deningerCalderonWittGammaPolarizedBoundaryReflectionDefect a
        (deningerCalderonWittCrossPrimeGammaWitness hpq) p q e f =
      (xiGammaEulerPrimitiveReflectionOddExterior
        a (p, e) (q, f) : ℂ) := by
  rw [deningerCalderonWittGammaPolarizedBoundaryReflectionDefect_eq]
  exact
    deningerCalderonWittGammaReflectionOddScalarTransport_crossPrimeWitness
      hpq a e f

theorem cellNonlocalCrossEffect_shiftedCarrier
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f r s : ℕ) :
    cellNonlocalCrossEffect (p, e + r) (q, f + s)
        (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1)
          (p, e + r) (deningerCalderonWittUnitDefect p, 0))
        (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
          (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1)
          (q, f + s) (0, deningerCalderonWittAlgebraicUnitPacket q)) =
      deningerPrimeFinitePacketGaugeAlgebraicFirstMode q
        (deningerCalderonWittAlgebraicUnitPacket q) := by
  have hcell : (p, e + r) ≠ (q, f + s) := by
    intro h
    exact hpq (Prod.mk.inj h).1
  simp [cellNonlocalCrossEffect, cellDefectCoordinate,
    cellPacketFirstMode,
    deningerCalderonWittLocalDefectCoordinate,
    deningerCalderonWittLocalPacketFirstMode,
    DirectSum.component.of, hcell]

/--
Kronecker value on the matching canonical shifted carrier: actual boundary
defect recovers the reflection-odd Gamma coefficient exactly.
-/
theorem cellReflectionOddBoundaryCoordinate_shiftedCarrier
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (e f r s : ℕ) :
    cellReflectionOddBoundaryCoordinate a (p, e + r) (q, f + s)
        (PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier
          hpq e f r s) =
      (xiGammaEulerPrimitiveReflectionOddExterior
        a (p, e + r) (q, f + s) : ℂ) := by
  have htrace :
      deningerCalderonWittAlgebraicCenterTrace q
          (deningerPrimeFinitePacketGaugeAlgebraicFirstMode q
            (deningerCalderonWittAlgebraicUnitPacket q)) =
        1 := by
    change
      deningerCalderonWittAlgebraicPacketTrace q
          ((deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv q).symm
            ((deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv q)
              (deningerCalderonWittAlgebraicUnitPacket q))) =
        1
    rw [(deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv q).symm_apply_apply,
      deningerCalderonWittAlgebraicPacketTrace_unit]
  rw [cellReflectionOddBoundaryCoordinate, LinearMap.comp_apply,
    PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier,
    cellWeightedNonlocalExterior_ιMulti]
  change
    deningerCalderonWittAlgebraicCenterTrace q
        ((xiGammaEulerPrimitiveReflectionOddExterior
            a (p, e + r) (q, f + s) : ℂ) •
          cellNonlocalCrossEffect (p, e + r) (q, f + s)
            (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
              (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1)
              (p, e + r) (deningerCalderonWittUnitDefect p, 0))
            (DirectSum.lof ℂ XiGammaEulerCalderonWittCell
              (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1)
              (q, f + s) (0, deningerCalderonWittAlgebraicUnitPacket q))) =
      (xiGammaEulerPrimitiveReflectionOddExterior
        a (p, e + r) (q, f + s) : ℂ)
  rw [cellNonlocalCrossEffect_shiftedCarrier hpq, map_smul, htrace,
    smul_eq_mul, mul_one]

/-- Scalar boundary profile indexed by every ordered prime/depth pair. -/
abbrev XiGammaEulerCalderonWittCellGammaScalarProfile :=
  XiGammaEulerCalderonWittCell →
    XiGammaEulerCalderonWittCell → ℂ

/-- Actual cell-labelled reflection defect before any coordinate fusion. -/
def cellReflectionOddBoundaryDefect
    (a : ℝ) :
    xiGammaEulerCalderonWittCellMilnorIncidence →ₗ[ℂ]
      XiGammaEulerCalderonWittCellGammaScalarProfile where
  toFun x pe qe :=
    cellReflectionOddBoundaryCoordinate a pe qe x.1
  map_add' x y := by
    funext pe qe
    exact map_add (cellReflectionOddBoundaryCoordinate a pe qe) x.1 y.1
  map_smul' c x := by
    funext pe qe
    exact map_smul (cellReflectionOddBoundaryCoordinate a pe qe) c x.1

/-- Concrete actual admitted sector on the independent prime-power-cell
source. -/
def actualCellGammaAdmittedHodgeSector
    (a : ℝ) :
    Submodule ℂ xiGammaEulerCalderonWittCellMilnorIncidence :=
  LinearMap.ker (cellReflectionOddBoundaryDefect a)

theorem cellReflectionOddBoundaryDefect_shiftedCarrier
    {p q : Nat.Primes} (hpq : p ≠ q)
    (a : ℝ) (e f r s : ℕ) :
    cellReflectionOddBoundaryDefect a
        ⟨PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier
            hpq e f r s,
          PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier_mem_incidence
            hpq e f r s⟩
        (p, e + r) (q, f + s) =
      (xiGammaEulerPrimitiveReflectionOddExterior
        a (p, e + r) (q, f + s) : ℂ) := by
  exact cellReflectionOddBoundaryCoordinate_shiftedCarrier
    hpq a e f r s

theorem shiftedCarrier_not_mem_actualCellGammaAdmittedHodgeSector
    {p q : Nat.Primes} (hpq : p ≠ q)
    {a : ℝ} (ha : a ≠ 0) :
    (⟨PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier
          hpq 0 0 0 0,
        PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier_mem_incidence
          hpq 0 0 0 0⟩ :
      xiGammaEulerCalderonWittCellMilnorIncidence) ∉
        actualCellGammaAdmittedHodgeSector a := by
  intro hmem
  have hzero :
      cellReflectionOddBoundaryDefect a
          (⟨PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier
              hpq 0 0 0 0,
            PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier_mem_incidence
              hpq 0 0 0 0⟩ :
            xiGammaEulerCalderonWittCellMilnorIncidence) = 0 :=
    (LinearMap.mem_ker).mp hmem
  have heval :
      cellReflectionOddBoundaryDefect a
          (⟨PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier
              hpq 0 0 0 0,
            PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier_mem_incidence
              hpq 0 0 0 0⟩ :
            xiGammaEulerCalderonWittCellMilnorIncidence)
          (p, 0) (q, 0) = 0 := by
    rw [hzero]
    rfl
  rw [cellReflectionOddBoundaryDefect_shiftedCarrier] at heval
  have hgamma :
      xiGammaEulerPrimitiveReflectionOddExterior
          a (p, 0) (q, 0) ≠ 0 :=
    xiGammaEulerPrimitiveReflectionOddExterior_ne_zero
      ha (p, 0) (q, 0)
        (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth hpq 0)
  norm_num at heval
  have hreal :
      xiGammaEulerPrimitiveReflectionOddExterior
          a (p, 0) (q, 0) = 0 := by
    exact_mod_cast heval
  exact hgamma hreal

/-! ## Complete finite-cell diagonal rigidity -/

/-- Ordered pair of distinct prime-power cells. -/
abbrev XiGammaEulerCalderonWittOrderedDistinctCellPair :=
  {ij : XiGammaEulerCalderonWittCell × XiGammaEulerCalderonWittCell //
    ij.1 ≠ ij.2}

/-- Normalized defect generator in one labelled prime-power cell. -/
def canonicalCellDefectGenerator
    (pe : XiGammaEulerCalderonWittCell) :
    XiGammaEulerCalderonWittCellDegreeOne :=
  DirectSum.lof ℂ XiGammaEulerCalderonWittCell
    (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1)
    pe (deningerCalderonWittUnitDefect pe.1, 0)

/-- Normalized packet generator in one labelled prime-power cell. -/
def canonicalCellPacketGenerator
    (qe : XiGammaEulerCalderonWittCell) :
    XiGammaEulerCalderonWittCellDegreeOne :=
  DirectSum.lof ℂ XiGammaEulerCalderonWittCell
    (fun re => DeningerCalderonWittAlgebraicDegreeOne re.1)
    qe (0, deningerCalderonWittAlgebraicUnitPacket qe.1)

/-- Canonical defect-at-`i`, packet-at-`j` exterior carrier. -/
def canonicalDistinctCellCarrier
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    ⋀[ℂ]^2 XiGammaEulerCalderonWittCellDegreeOne :=
  exteriorPower.ιMulti ℂ 2
    ![canonicalCellDefectGenerator ij.1.1,
      canonicalCellPacketGenerator ij.1.2]

theorem canonicalDistinctCellCarrier_mem_incidence
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    canonicalDistinctCellCarrier ij ∈
      xiGammaEulerCalderonWittCellMilnorIncidence := by
  unfold canonicalDistinctCellCarrier canonicalCellDefectGenerator
    canonicalCellPacketGenerator
  exact xiGammaEulerCalderonWittCrossCell_mem_milnorIncidence
    ij.2 _ _

/-- Canonical distinct-cell carrier as an exact incidence vector. -/
def canonicalDistinctCellIncidenceCarrier
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  ⟨canonicalDistinctCellCarrier ij,
    canonicalDistinctCellCarrier_mem_incidence ij⟩

/-- Normalized scalar packet coordinate after vector-valued suspension. -/
def cellPacketCoordinate
    (qe : XiGammaEulerCalderonWittCell) :
    XiGammaEulerCalderonWittCellDegreeOne →ₗ[ℂ] ℂ :=
  (deningerCalderonWittAlgebraicCenterTrace qe.1).comp
    (cellPacketFirstMode qe)

/-- Unweighted scalar cell exterior.  This is packet orientation applied
after the vector-valued nonlocal cross-effect. -/
def cellScalarExterior
    (pe qe : XiGammaEulerCalderonWittCell) :
    (⋀[ℂ]^2 XiGammaEulerCalderonWittCellDegreeOne) →ₗ[ℂ] ℂ :=
  (deningerCalderonWittAlgebraicCenterTrace qe.1).comp
    (cellWeightedNonlocalExterior 1 pe qe)

@[simp]
theorem cellScalarExterior_ιMulti
    (pe qe : XiGammaEulerCalderonWittCell)
    (v : Fin 2 → XiGammaEulerCalderonWittCellDegreeOne) :
    cellScalarExterior pe qe (exteriorPower.ιMulti ℂ 2 v) =
      deningerCalderonWittAlgebraicCenterTrace qe.1
        (cellNonlocalCrossEffect pe qe (v 0) (v 1)) := by
  rw [cellScalarExterior, LinearMap.comp_apply,
    cellWeightedNonlocalExterior_ιMulti]
  simp [cellWeightedNonlocalCrossEffect]

theorem cellDefectCoordinate_canonicalDefectGenerator
    (pe k : XiGammaEulerCalderonWittCell) :
    cellDefectCoordinate pe (canonicalCellDefectGenerator k) =
      if k = pe then 1 else 0 := by
  by_cases h : k = pe
  · subst k
    simp [cellDefectCoordinate, canonicalCellDefectGenerator,
      deningerCalderonWittLocalDefectCoordinate]
  · simp [cellDefectCoordinate, canonicalCellDefectGenerator,
      deningerCalderonWittLocalDefectCoordinate,
      DirectSum.component.of, h]

theorem cellDefectCoordinate_canonicalPacketGenerator
    (pe l : XiGammaEulerCalderonWittCell) :
    cellDefectCoordinate pe (canonicalCellPacketGenerator l) = 0 := by
  by_cases h : l = pe
  · subst l
    simp [cellDefectCoordinate, canonicalCellPacketGenerator,
      deningerCalderonWittLocalDefectCoordinate]
  · simp [cellDefectCoordinate, canonicalCellPacketGenerator,
      deningerCalderonWittLocalDefectCoordinate,
      DirectSum.component.of, h]

theorem cellPacketCoordinate_canonicalPacketGenerator
    (qe l : XiGammaEulerCalderonWittCell) :
    cellPacketCoordinate qe (canonicalCellPacketGenerator l) =
      if l = qe then 1 else 0 := by
  by_cases h : l = qe
  · subst l
    rw [if_pos rfl]
    rw [cellPacketCoordinate, LinearMap.comp_apply,
      cellPacketFirstMode, LinearMap.comp_apply,
      canonicalCellPacketGenerator, DirectSum.component.lof_self,
      deningerCalderonWittLocalPacketFirstMode]
    change
      deningerCalderonWittAlgebraicPacketTrace qe.1
          ((deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv qe.1).symm
            ((deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv qe.1)
              (deningerCalderonWittAlgebraicUnitPacket qe.1))) =
        1
    rw [(deningerPrimeFinitePacketGaugeAlgebraicFirstModeEquiv qe.1).symm_apply_apply,
      deningerCalderonWittAlgebraicPacketTrace_unit]
  · simp [cellPacketCoordinate, cellPacketFirstMode,
      canonicalCellPacketGenerator,
      deningerCalderonWittLocalPacketFirstMode,
      DirectSum.component.of, h]

theorem cellPacketCoordinate_canonicalDefectGenerator
    (qe k : XiGammaEulerCalderonWittCell) :
    cellPacketCoordinate qe (canonicalCellDefectGenerator k) = 0 := by
  by_cases h : k = qe
  · subst k
    simp [cellPacketCoordinate, cellPacketFirstMode,
      canonicalCellDefectGenerator,
      deningerCalderonWittLocalPacketFirstMode]
  · simp [cellPacketCoordinate, cellPacketFirstMode,
      canonicalCellDefectGenerator,
      deningerCalderonWittLocalPacketFirstMode,
      DirectSum.component.of, h]

/--
Unweighted Kronecker law: packet orientation of the `(pe,qe)` cross-effect
extracts exactly the matching canonical ordered carrier coefficient.
-/
theorem cellScalarExterior_canonicalDistinctCellCarrier
    (pe qe : XiGammaEulerCalderonWittCell)
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    cellScalarExterior pe qe (canonicalDistinctCellCarrier ij) =
      if pe = ij.1.1 ∧ qe = ij.1.2 then 1 else 0 := by
  rw [canonicalDistinctCellCarrier, cellScalarExterior_ιMulti]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change
    deningerCalderonWittAlgebraicCenterTrace qe.1
        (cellDefectCoordinate pe (canonicalCellDefectGenerator ij.1.1) •
            cellPacketFirstMode qe (canonicalCellPacketGenerator ij.1.2) -
          cellDefectCoordinate pe (canonicalCellPacketGenerator ij.1.2) •
            cellPacketFirstMode qe (canonicalCellDefectGenerator ij.1.1)) =
      if pe = ij.1.1 ∧ qe = ij.1.2 then 1 else 0
  rw [map_sub, map_smul, map_smul]
  change
    cellDefectCoordinate pe (canonicalCellDefectGenerator ij.1.1) *
          cellPacketCoordinate qe (canonicalCellPacketGenerator ij.1.2) -
        cellDefectCoordinate pe (canonicalCellPacketGenerator ij.1.2) *
          cellPacketCoordinate qe (canonicalCellDefectGenerator ij.1.1) =
      if pe = ij.1.1 ∧ qe = ij.1.2 then 1 else 0
  rw [cellDefectCoordinate_canonicalDefectGenerator,
    cellPacketCoordinate_canonicalPacketGenerator,
    cellDefectCoordinate_canonicalPacketGenerator,
    cellPacketCoordinate_canonicalDefectGenerator]
  by_cases h : pe = ij.1.1 ∧ qe = ij.1.2
  · rw [if_pos h, if_pos h.1.symm, if_pos h.2.symm]
    norm_num
  · rw [if_neg h]
    by_cases hpi : pe = ij.1.1
    · have hqj : qe ≠ ij.1.2 := fun hq => h ⟨hpi, hq⟩
      have hqj' : ij.1.2 ≠ qe := fun hq => hqj hq.symm
      rw [if_pos hpi.symm, if_neg hqj']
      norm_num
    · have hpi' : ij.1.1 ≠ pe := fun hp => hpi hp.symm
      rw [if_neg hpi']
      norm_num

/--
Actual Gamma/Hardy boundary Kronecker law.  Distinct ordered coordinates
remain distinct until after the reflection coefficient is applied.
-/
theorem cellReflectionOddBoundaryCoordinate_canonicalDistinctCellCarrier
    (a : ℝ) (pe qe : XiGammaEulerCalderonWittCell)
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    cellReflectionOddBoundaryCoordinate a pe qe
        (canonicalDistinctCellCarrier ij) =
      if pe = ij.1.1 ∧ qe = ij.1.2 then
        (xiGammaEulerPrimitiveReflectionOddExterior a pe qe : ℂ)
      else 0 := by
  rw [cellReflectionOddBoundaryCoordinate, LinearMap.comp_apply,
    canonicalDistinctCellCarrier, cellWeightedNonlocalExterior_ιMulti]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change
    deningerCalderonWittAlgebraicCenterTrace qe.1
        ((xiGammaEulerPrimitiveReflectionOddExterior a pe qe : ℂ) •
          cellNonlocalCrossEffect pe qe
            (canonicalCellDefectGenerator ij.1.1)
            (canonicalCellPacketGenerator ij.1.2)) =
      if pe = ij.1.1 ∧ qe = ij.1.2 then
        (xiGammaEulerPrimitiveReflectionOddExterior a pe qe : ℂ)
      else 0
  rw [map_smul, smul_eq_mul]
  have hscalar :=
    cellScalarExterior_canonicalDistinctCellCarrier pe qe ij
  rw [cellScalarExterior, LinearMap.comp_apply,
    canonicalDistinctCellCarrier,
    cellWeightedNonlocalExterior_ιMulti] at hscalar
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    cellWeightedNonlocalCrossEffect, one_smul] at hscalar
  rw [hscalar]
  by_cases h : pe = ij.1.1 ∧ qe = ij.1.2
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- Finite canonical distinct-cell coefficient family realized in exact
incidence. -/
def canonicalDistinctCellCarrierCombination :
    (XiGammaEulerCalderonWittOrderedDistinctCellPair →₀ ℂ) →ₗ[ℂ]
      xiGammaEulerCalderonWittCellMilnorIncidence :=
  Finsupp.linearCombination ℂ canonicalDistinctCellIncidenceCarrier

/-- Every boundary coordinate recovers its matching finite carrier
coefficient multiplied by the actual reflection-odd Gamma coefficient. -/
theorem cellReflectionOddBoundaryDefect_carrierCombination_eval
    (a : ℝ)
    (c : XiGammaEulerCalderonWittOrderedDistinctCellPair →₀ ℂ)
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    cellReflectionOddBoundaryDefect a
        (canonicalDistinctCellCarrierCombination c) ij.1.1 ij.1.2 =
      (xiGammaEulerPrimitiveReflectionOddExterior
        a ij.1.1 ij.1.2 : ℂ) * c ij := by
  induction c using Finsupp.induction_linear with
  | zero =>
      simp [canonicalDistinctCellCarrierCombination,
        cellReflectionOddBoundaryDefect]
  | add f g hf hg =>
      rw [map_add, map_add]
      change
        cellReflectionOddBoundaryDefect a
              (canonicalDistinctCellCarrierCombination f) ij.1.1 ij.1.2 +
            cellReflectionOddBoundaryDefect a
              (canonicalDistinctCellCarrierCombination g) ij.1.1 ij.1.2 =
          (xiGammaEulerPrimitiveReflectionOddExterior
            a ij.1.1 ij.1.2 : ℂ) * (f ij + g ij)
      rw [hf, hg]
      ring
  | single kl b =>
      by_cases h : ij = kl
      · subst kl
        change
          cellReflectionOddBoundaryDefect a
                ((Finsupp.linearCombination ℂ
                  canonicalDistinctCellIncidenceCarrier)
                    (Finsupp.single ij b)) ij.1.1 ij.1.2 =
            (xiGammaEulerPrimitiveReflectionOddExterior
              a ij.1.1 ij.1.2 : ℂ) * Finsupp.single ij b ij
        rw [Finsupp.linearCombination_single, map_smul]
        change
          b * cellReflectionOddBoundaryCoordinate a ij.1.1 ij.1.2
                (canonicalDistinctCellCarrier ij) =
            (xiGammaEulerPrimitiveReflectionOddExterior
              a ij.1.1 ij.1.2 : ℂ) * Finsupp.single ij b ij
        rw [cellReflectionOddBoundaryCoordinate_canonicalDistinctCellCarrier,
          Finsupp.single_eq_same]
        simp
        ring
      · change
          cellReflectionOddBoundaryDefect a
                ((Finsupp.linearCombination ℂ
                  canonicalDistinctCellIncidenceCarrier)
                    (Finsupp.single kl b)) ij.1.1 ij.1.2 =
            (xiGammaEulerPrimitiveReflectionOddExterior
              a ij.1.1 ij.1.2 : ℂ) * Finsupp.single kl b ij
        rw [Finsupp.linearCombination_single, map_smul]
        change
          b * cellReflectionOddBoundaryCoordinate a ij.1.1 ij.1.2
                (canonicalDistinctCellCarrier kl) =
            (xiGammaEulerPrimitiveReflectionOddExterior
              a ij.1.1 ij.1.2 : ℂ) * Finsupp.single kl b ij
        rw [cellReflectionOddBoundaryCoordinate_canonicalDistinctCellCarrier]
        have hpair :
            ¬(ij.1.1 = kl.1.1 ∧ ij.1.2 = kl.1.2) := by
          intro hp
          apply h
          apply Subtype.ext
          exact Prod.ext hp.1 hp.2
        rw [if_neg hpair, mul_zero]
        rw [Finsupp.single_eq_of_ne h]
        ring

/-- Prime-power physical half-height is injective on labelled cells. -/
theorem xiGammaEulerBoundaryHalfHeight_cell_injective :
    Function.Injective
      (fun pe : XiGammaEulerCalderonWittCell =>
        xiGammaEulerBoundaryHalfHeight pe.1 pe.2) := by
  rintro ⟨p, e⟩ ⟨q, f⟩ hheight
  change
    xiGammaEulerBoundaryHalfHeight p e =
      xiGammaEulerBoundaryHalfHeight q f at hheight
  rw [xiGammaEulerBoundaryHalfHeight_eq_half_log_valuation,
    xiGammaEulerBoundaryHalfHeight_eq_half_log_valuation] at hheight
  have hlog :
      Real.log (xiGammaEulerValuationNat (p, e) : ℝ) =
        Real.log (xiGammaEulerValuationNat (q, f) : ℝ) := by
    linarith
  have hpVal :
      (0 : ℝ) < (xiGammaEulerValuationNat (p, e) : ℝ) := by
    unfold xiGammaEulerValuationNat
    exact_mod_cast pow_pos p.property.pos (e + 1)
  have hqVal :
      (0 : ℝ) < (xiGammaEulerValuationNat (q, f) : ℝ) := by
    unfold xiGammaEulerValuationNat
    exact_mod_cast pow_pos q.property.pos (f + 1)
  have hvalR :
      (xiGammaEulerValuationNat (p, e) : ℝ) =
        (xiGammaEulerValuationNat (q, f) : ℝ) := by
    have hexp := congrArg Real.exp hlog
    rwa [Real.exp_log hpVal, Real.exp_log hqVal] at hexp
  have hpow :
      (p : ℕ) ^ (e + 1) = (q : ℕ) ^ (f + 1) := by
    exact_mod_cast hvalR
  obtain ⟨hpq, hef⟩ := Nat.Prime.pow_inj p.property q.property hpow
  apply Prod.ext
  · exact Subtype.ext hpq
  · exact hef

/--
Finite-cell diagonal rigidity: at nonzero modular displacement, actual
Gamma/Hardy boundary defect is injective on every finite canonical
distinct-cell coefficient family.
-/
theorem cellReflectionOddBoundaryDefect_carrierCombination_injective
    {a : ℝ} (ha : a ≠ 0) :
    Function.Injective
      (fun c :
          XiGammaEulerCalderonWittOrderedDistinctCellPair →₀ ℂ =>
        cellReflectionOddBoundaryDefect a
          (canonicalDistinctCellCarrierCombination c)) := by
  intro c d hcd
  apply Finsupp.ext
  intro ij
  have heval :
      cellReflectionOddBoundaryDefect a
          (canonicalDistinctCellCarrierCombination c) ij.1.1 ij.1.2 =
        cellReflectionOddBoundaryDefect a
          (canonicalDistinctCellCarrierCombination d) ij.1.1 ij.1.2 := by
    exact congrFun (congrFun hcd ij.1.1) ij.1.2
  rw [cellReflectionOddBoundaryDefect_carrierCombination_eval,
    cellReflectionOddBoundaryDefect_carrierCombination_eval] at heval
  have hheight :
      xiGammaEulerBoundaryHalfHeight ij.1.1.1 ij.1.1.2 ≠
        xiGammaEulerBoundaryHalfHeight ij.1.2.1 ij.1.2.2 := by
    intro hh
    exact ij.2 (xiGammaEulerBoundaryHalfHeight_cell_injective hh)
  have hgamma :
      xiGammaEulerPrimitiveReflectionOddExterior
          a ij.1.1 ij.1.2 ≠ 0 :=
    xiGammaEulerPrimitiveReflectionOddExterior_ne_zero
      ha ij.1.1 ij.1.2 hheight
  have hgammaC :
      (xiGammaEulerPrimitiveReflectionOddExterior
        a ij.1.1 ij.1.2 : ℂ) ≠ 0 := by
    exact_mod_cast hgamma
  exact mul_left_cancel₀ hgammaC heval

theorem canonicalDistinctCellCarrierCombination_injective :
    Function.Injective canonicalDistinctCellCarrierCombination := by
  intro c d hcd
  apply cellReflectionOddBoundaryDefect_carrierCombination_injective
    (a := 1) (by norm_num)
  exact congrArg (cellReflectionOddBoundaryDefect 1) hcd

theorem canonicalCarrierCombination_not_mem_actualCellGammaAdmittedHodgeSector
    {a : ℝ} (ha : a ≠ 0)
    {c : XiGammaEulerCalderonWittOrderedDistinctCellPair →₀ ℂ}
    (hc : c ≠ 0) :
    canonicalDistinctCellCarrierCombination c ∉
      actualCellGammaAdmittedHodgeSector a := by
  intro hmem
  have hzero :
      cellReflectionOddBoundaryDefect a
          (canonicalDistinctCellCarrierCombination c) = 0 :=
    (LinearMap.mem_ker).mp hmem
  have hzeroCombination :
      cellReflectionOddBoundaryDefect a
          (canonicalDistinctCellCarrierCombination c) =
        cellReflectionOddBoundaryDefect a
          (canonicalDistinctCellCarrierCombination 0) := by
    simpa using hzero
  have hc0 :=
    cellReflectionOddBoundaryDefect_carrierCombination_injective
      ha hzeroCombination
  exact hc hc0

/-! ## Existing cofinal spread lies in the rigid finite-cell span -/

def shiftedCrossPrimeOrderedDistinctCellPair
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f r s : ℕ) :
    XiGammaEulerCalderonWittOrderedDistinctCellPair :=
  ⟨((p, e + r), (q, f + s)), by
    intro hcell
    exact hpq (Prod.mk.inj hcell).1⟩

theorem canonicalCarrier_shiftedCrossPrime
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f r s : ℕ) :
    canonicalDistinctCellIncidenceCarrier
        (shiftedCrossPrimeOrderedDistinctCellPair hpq e f r s) =
      ⟨PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier
          hpq e f r s,
        PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier_mem_incidence
          hpq e f r s⟩ := by
  apply Subtype.ext
  rfl

def sourceNormalDepthSpreadCoefficients
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f : ℕ) (N M : ℕ) (w : ℂ) :
    XiGammaEulerCalderonWittOrderedDistinctCellPair →₀ ℂ :=
  ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range M,
    Finsupp.single
      (shiftedCrossPrimeOrderedDistinctCellPair hpq e f r s)
      (((PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, e) r *
          PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, f) s : ℝ) : ℂ) *
        (w / ((N : ℂ) * (M : ℂ))))

theorem canonicalCombination_sourceNormalDepthSpread
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f : ℕ) (N M : ℕ) (w : ℂ) :
    canonicalDistinctCellCarrierCombination
        (sourceNormalDepthSpreadCoefficients hpq e f N M w) =
      PrimitivePromotedCofinalDepth.sourceNormalDepthSpreadCarrier
        hpq e f N M w := by
  rw [sourceNormalDepthSpreadCoefficients,
    PrimitivePromotedCofinalDepth.sourceNormalDepthSpreadCarrier]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  change
    (Finsupp.linearCombination ℂ canonicalDistinctCellIncidenceCarrier)
        (Finsupp.single
          (shiftedCrossPrimeOrderedDistinctCellPair hpq e f r s)
          (((PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, e) r *
              PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, f) s : ℝ) : ℂ) *
            (w / ((N : ℂ) * (M : ℂ))))) =
      (((PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, e) r *
          PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, f) s : ℝ) : ℂ) *
        (w / ((N : ℂ) * (M : ℂ)))) •
        ⟨PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier
            hpq e f r s,
          PrimitivePromotedCofinalDepth.shiftedCrossPrimeDepthCarrier_mem_incidence
            hpq e f r s⟩
  rw [Finsupp.linearCombination_single,
    canonicalCarrier_shiftedCrossPrime]

theorem shiftedCrossPrimeOrderedDistinctCellPair_eq_iff
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f r s r' s' : ℕ) :
    shiftedCrossPrimeOrderedDistinctCellPair hpq e f r s =
        shiftedCrossPrimeOrderedDistinctCellPair hpq e f r' s' ↔
      r = r' ∧ s = s' := by
  constructor
  · intro h
    have hpairs := congrArg Subtype.val h
    have hcells := Prod.mk.inj hpairs
    exact
      ⟨Nat.add_left_cancel (Prod.mk.inj hcells.1).2,
        Nat.add_left_cancel (Prod.mk.inj hcells.2).2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem sourceNormalDepthSpreadCoefficients_base
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f : ℕ) {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (w : ℂ) :
    sourceNormalDepthSpreadCoefficients hpq e f N M w
        (shiftedCrossPrimeOrderedDistinctCellPair hpq e f 0 0) =
      (((PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, e) 0 *
          PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, f) 0 : ℝ) : ℂ) *
        (w / ((N : ℂ) * (M : ℂ)))) := by
  classical
  rw [sourceNormalDepthSpreadCoefficients, Finset.sum_apply']
  simp_rw [Finset.sum_apply']
  change
    (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range M,
      Finsupp.single
          (shiftedCrossPrimeOrderedDistinctCellPair hpq e f r s)
          (((PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, e) r *
              PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, f) s : ℝ) : ℂ) *
            (w / ((N : ℂ) * (M : ℂ))))
        (shiftedCrossPrimeOrderedDistinctCellPair hpq e f 0 0)) =
      (((PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, e) 0 *
          PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, f) 0 : ℝ) : ℂ) *
        (w / ((N : ℂ) * (M : ℂ))))
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · rw [Finsupp.single_eq_same]
    · intro s hs hs0
      rw [Finsupp.single_apply, if_neg]
      intro hpair
      have hrs :=
        (shiftedCrossPrimeOrderedDistinctCellPair_eq_iff
          hpq e f 0 s 0 0).mp hpair
      exact hs0 hrs.2
    · intro hzero
      exact (hzero (Finset.mem_range.mpr hM)).elim
  · intro r hr hr0
    apply Finset.sum_eq_zero
    intro s hs
    rw [Finsupp.single_apply, if_neg]
    intro hpair
    have hrs :=
      (shiftedCrossPrimeOrderedDistinctCellPair_eq_iff
        hpq e f r s 0 0).mp hpair
    exact hr0 hrs.1
  · intro hzero
    exact (hzero (Finset.mem_range.mpr hN)).elim

theorem sourceNormalDepthSpreadCoefficients_ne_zero
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f : ℕ) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {w : ℂ} (hw : w ≠ 0) :
    sourceNormalDepthSpreadCoefficients hpq e f N M w ≠ 0 := by
  intro hzero
  have heval :=
    congrArg
      (fun c : XiGammaEulerCalderonWittOrderedDistinctCellPair →₀ ℂ =>
        c (shiftedCrossPrimeOrderedDistinctCellPair hpq e f 0 0))
      hzero
  rw [sourceNormalDepthSpreadCoefficients_base
    hpq e f hN hM w] at heval
  have hdepthR :
      PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, e) 0 *
          PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, f) 0 ≠
        0 :=
    mul_ne_zero
      (PrimitivePromotedCofinalDepth.criticalDepthDeattenuation_pos
        (p, e) 0).ne'
      (PrimitivePromotedCofinalDepth.criticalDepthDeattenuation_pos
        (q, f) 0).ne'
  have hdepthC :
      ((PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, e) 0 *
          PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, f) 0 :
        ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hdepthR
  have hNC : (N : ℂ) ≠ 0 := by
    exact_mod_cast hN.ne'
  have hMC : (M : ℂ) ≠ 0 := by
    exact_mod_cast hM.ne'
  have hquot : w / ((N : ℂ) * (M : ℂ)) ≠ 0 :=
    div_ne_zero hw (mul_ne_zero hNC hMC)
  exact (mul_ne_zero hdepthC hquot) heval

/--
The complete finite source-normal depth spread is never in the actual
Gamma/Hardy admitted sector at nonzero displacement.  Its compensated
finite-index Hodge symmetry therefore cannot be promoted to actual
boundary-kernel membership.
-/
theorem sourceNormalDepthSpreadCarrier_not_mem_actualCellGammaAdmittedHodgeSector
    {p q : Nat.Primes} (hpq : p ≠ q)
    (e f : ℕ) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {w : ℂ} (hw : w ≠ 0)
    {a : ℝ} (ha : a ≠ 0) :
    PrimitivePromotedCofinalDepth.sourceNormalDepthSpreadCarrier
        hpq e f N M w ∉
      actualCellGammaAdmittedHodgeSector a := by
  rw [← canonicalCombination_sourceNormalDepthSpread]
  exact
    canonicalCarrierCombination_not_mem_actualCellGammaAdmittedHodgeSector
      ha
      (sourceNormalDepthSpreadCoefficients_ne_zero
        hpq e f hN hM hw)

end PrimitivePromotedCellHodgeRigidity

end
end RHTower
