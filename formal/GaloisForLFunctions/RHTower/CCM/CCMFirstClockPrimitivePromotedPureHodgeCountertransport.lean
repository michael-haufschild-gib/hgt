import GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimitivePromotedCellHodgeBoundaryRigidity

/-!
# Pure-incidence Hodge countertransport

Actual cell-boundary coordinates pair one Calderon defect leg with one
rational-Witt packet leg.  This module classifies the complementary pure
incidence sectors.  For distinct cells `i,j`, both `d_i wedge d_j` and
`w_i wedge w_j` are nonzero exact incidences annihilated by every actual
Gamma/Hardy reflection coordinate.  Their normalized sum is therefore an
actual admitted pure Hodge pair at every modular displacement.

Packet-leg Gamma transport acts on the packet--packet carrier by the
product of both cell coefficients.  Critical depth deattenuation then gives
the two-leg primitive landing internally, rather than inserting a scalar
after mixed cup.  The complete finite two-scale pure carrier is actual
admitted incidence, is fixed by Green retraction, retains exact codiagonal
readout, and has uniform source-normal capacity.

The final theorem records the hostile boundary: any scalar readout bounded
by that capacity still has gain growing linearly with aperture.  Thus this
module constructs the requested admitted countertransport but does not
silently identify its singular codiagonal with a bounded completed output.
-/

open Complex
open scoped DirectSum

namespace RHTower

noncomputable section

namespace PrimitivePromotedPureHodgeCountertransport

open PrimitivePromotedCellHodgeRigidity

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def cellCoordinateAlternating
    (φ ψ : V →ₗ[ℂ] ℂ) :
    V [⋀^Fin 2]→ₗ[ℂ] ℂ where
  toFun v := φ (v 0) * ψ (v 1) - φ (v 1) * ψ (v 0)
  map_update_add' v i x y := by
    fin_cases i <;> simp [mul_add, add_mul] <;> ring
  map_update_smul' v i c x := by
    fin_cases i <;> simp [smul_eq_mul] <;> ring
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · have h : v 0 = v 1 := by simpa using hij
      simp [h]
    · have h : v 1 = v 0 := by simpa using hij
      simp [h]
    · exact (hne rfl).elim

def cellCoordinateExterior
    (φ ψ : V →ₗ[ℂ] ℂ) :
    (⋀[ℂ]^(2 : ℕ) V) →ₗ[ℂ] ℂ :=
  exteriorPower.alternatingMapLinearEquiv
    (cellCoordinateAlternating φ ψ)

@[simp]
theorem cellCoordinateExterior_ιMulti
    (φ ψ : V →ₗ[ℂ] ℂ) (v : Fin 2 → V) :
    cellCoordinateExterior φ ψ (exteriorPower.ιMulti ℂ 2 v) =
      φ (v 0) * ψ (v 1) - φ (v 1) * ψ (v 0) := by
  rw [cellCoordinateExterior,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

def canonicalDefectDefectCellCarrier
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    ⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne :=
  exteriorPower.ιMulti ℂ 2
    ![canonicalCellDefectGenerator ij.1.1,
      canonicalCellDefectGenerator ij.1.2]

def canonicalPacketPacketCellCarrier
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    ⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne :=
  exteriorPower.ιMulti ℂ 2
    ![canonicalCellPacketGenerator ij.1.1,
      canonicalCellPacketGenerator ij.1.2]

theorem canonicalDefectDefectCellCarrier_mem_incidence
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    canonicalDefectDefectCellCarrier ij ∈
      xiGammaEulerCalderonWittCellMilnorIncidence := by
  unfold canonicalDefectDefectCellCarrier canonicalCellDefectGenerator
  exact xiGammaEulerCalderonWittCrossCell_mem_milnorIncidence ij.2 _ _

theorem canonicalPacketPacketCellCarrier_mem_incidence
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    canonicalPacketPacketCellCarrier ij ∈
      xiGammaEulerCalderonWittCellMilnorIncidence := by
  unfold canonicalPacketPacketCellCarrier canonicalCellPacketGenerator
  exact xiGammaEulerCalderonWittCrossCell_mem_milnorIncidence ij.2 _ _

def cellDefectDefectExterior
    (pe qe : XiGammaEulerCalderonWittCell) :
    (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) →ₗ[ℂ] ℂ :=
  cellCoordinateExterior
    (cellDefectCoordinate pe) (cellDefectCoordinate qe)

def cellPacketPacketExterior
    (pe qe : XiGammaEulerCalderonWittCell) :
    (⋀[ℂ]^(2 : ℕ) XiGammaEulerCalderonWittCellDegreeOne) →ₗ[ℂ] ℂ :=
  cellCoordinateExterior
    (cellPacketCoordinate pe) (cellPacketCoordinate qe)

theorem cellDefectDefectExterior_canonical
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    cellDefectDefectExterior ij.1.1 ij.1.2
        (canonicalDefectDefectCellCarrier ij) = 1 := by
  rw [cellDefectDefectExterior, canonicalDefectDefectCellCarrier,
    cellCoordinateExterior_ιMulti]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp [cellDefectCoordinate_canonicalDefectGenerator,
    ij.2, ij.2.symm]

theorem cellPacketPacketExterior_canonical
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    cellPacketPacketExterior ij.1.1 ij.1.2
        (canonicalPacketPacketCellCarrier ij) = 1 := by
  rw [cellPacketPacketExterior, canonicalPacketPacketCellCarrier,
    cellCoordinateExterior_ιMulti]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp [cellPacketCoordinate_canonicalPacketGenerator,
    ij.2, ij.2.symm]

theorem canonicalDefectDefectCellCarrier_ne_zero
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    canonicalDefectDefectCellCarrier ij ≠ 0 := by
  intro h
  have := congrArg (cellDefectDefectExterior ij.1.1 ij.1.2) h
  rw [cellDefectDefectExterior_canonical, map_zero] at this
  norm_num at this

theorem canonicalPacketPacketCellCarrier_ne_zero
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    canonicalPacketPacketCellCarrier ij ≠ 0 := by
  intro h
  have := congrArg (cellPacketPacketExterior ij.1.1 ij.1.2) h
  rw [cellPacketPacketExterior_canonical, map_zero] at this
  norm_num at this

theorem cellScalarExterior_eq_coordinateExterior
    (pe qe : XiGammaEulerCalderonWittCell) :
    cellScalarExterior pe qe =
      cellCoordinateExterior
        (cellDefectCoordinate pe) (cellPacketCoordinate qe) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change
    cellScalarExterior pe qe (exteriorPower.ιMulti ℂ 2 v) =
      cellCoordinateExterior
        (cellDefectCoordinate pe) (cellPacketCoordinate qe)
        (exteriorPower.ιMulti ℂ 2 v)
  rw [cellScalarExterior_ιMulti, cellCoordinateExterior_ιMulti]
  change
    deningerCalderonWittAlgebraicCenterTrace qe.1
        (cellDefectCoordinate pe (v 0) • cellPacketFirstMode qe (v 1) -
          cellDefectCoordinate pe (v 1) • cellPacketFirstMode qe (v 0)) =
      cellDefectCoordinate pe (v 0) * cellPacketCoordinate qe (v 1) -
        cellDefectCoordinate pe (v 1) * cellPacketCoordinate qe (v 0)
  rw [map_sub, map_smul, map_smul]
  rfl

theorem cellReflectionOddBoundaryCoordinate_eq_scalar
    (a : ℝ) (pe qe : XiGammaEulerCalderonWittCell) :
    cellReflectionOddBoundaryCoordinate a pe qe =
      (xiGammaEulerPrimitiveReflectionOddExterior a pe qe : ℂ) •
        cellScalarExterior pe qe := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change
    cellReflectionOddBoundaryCoordinate a pe qe
        (exteriorPower.ιMulti ℂ 2 v) =
      ((xiGammaEulerPrimitiveReflectionOddExterior a pe qe : ℂ) •
        cellScalarExterior pe qe) (exteriorPower.ιMulti ℂ 2 v)
  rw [LinearMap.smul_apply]
  rw [cellReflectionOddBoundaryCoordinate, LinearMap.comp_apply,
    cellWeightedNonlocalExterior_ιMulti,
    cellScalarExterior_ιMulti]
  simp only [cellWeightedNonlocalCrossEffect, LinearMap.smul_apply]
  rw [map_smul]

theorem cellReflectionOddBoundaryCoordinate_defectDefect
    (a : ℝ) (pe qe : XiGammaEulerCalderonWittCell)
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    cellReflectionOddBoundaryCoordinate a pe qe
        (canonicalDefectDefectCellCarrier ij) = 0 := by
  rw [cellReflectionOddBoundaryCoordinate_eq_scalar,
    LinearMap.smul_apply, cellScalarExterior_eq_coordinateExterior,
    canonicalDefectDefectCellCarrier, cellCoordinateExterior_ιMulti]
  simp [cellPacketCoordinate_canonicalDefectGenerator]

theorem cellReflectionOddBoundaryCoordinate_packetPacket
    (a : ℝ) (pe qe : XiGammaEulerCalderonWittCell)
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    cellReflectionOddBoundaryCoordinate a pe qe
        (canonicalPacketPacketCellCarrier ij) = 0 := by
  rw [cellReflectionOddBoundaryCoordinate_eq_scalar,
    LinearMap.smul_apply, cellScalarExterior_eq_coordinateExterior,
    canonicalPacketPacketCellCarrier, cellCoordinateExterior_ιMulti]
  simp [cellDefectCoordinate_canonicalPacketGenerator]

def canonicalDefectDefectIncidenceCarrier
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  ⟨canonicalDefectDefectCellCarrier ij,
    canonicalDefectDefectCellCarrier_mem_incidence ij⟩

def canonicalPacketPacketIncidenceCarrier
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  ⟨canonicalPacketPacketCellCarrier ij,
    canonicalPacketPacketCellCarrier_mem_incidence ij⟩

theorem canonicalDefectDefectIncidenceCarrier_mem_actual
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    canonicalDefectDefectIncidenceCarrier ij ∈
      actualCellGammaAdmittedHodgeSector a := by
  rw [actualCellGammaAdmittedHodgeSector, LinearMap.mem_ker]
  funext pe qe
  exact cellReflectionOddBoundaryCoordinate_defectDefect a pe qe ij

theorem canonicalPacketPacketIncidenceCarrier_mem_actual
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    canonicalPacketPacketIncidenceCarrier ij ∈
      actualCellGammaAdmittedHodgeSector a := by
  rw [actualCellGammaAdmittedHodgeSector, LinearMap.mem_ker]
  funext pe qe
  exact cellReflectionOddBoundaryCoordinate_packetPacket a pe qe ij

def canonicalPureHodgeCellCarrier
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  canonicalDefectDefectIncidenceCarrier ij +
    canonicalPacketPacketIncidenceCarrier ij

theorem canonicalPureHodgeCellCarrier_mem_actual
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    canonicalPureHodgeCellCarrier ij ∈
      actualCellGammaAdmittedHodgeSector a := by
  exact Submodule.add_mem _
    (canonicalDefectDefectIncidenceCarrier_mem_actual a ij)
    (canonicalPacketPacketIncidenceCarrier_mem_actual a ij)

theorem canonicalPureHodgeCellCarrier_ne_zero
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    canonicalPureHodgeCellCarrier ij ≠ 0 := by
  intro h
  have hcoe := congrArg Subtype.val h
  change
    canonicalDefectDefectCellCarrier ij +
        canonicalPacketPacketCellCarrier ij = 0 at hcoe
  have hc := congrArg
    (cellDefectDefectExterior ij.1.1 ij.1.2) hcoe
  rw [map_add, cellDefectDefectExterior_canonical, map_zero] at hc
  have hpacket :
      cellDefectDefectExterior ij.1.1 ij.1.2
          (canonicalPacketPacketCellCarrier ij) = 0 := by
    rw [cellDefectDefectExterior, canonicalPacketPacketCellCarrier,
      cellCoordinateExterior_ιMulti]
    simp [cellDefectCoordinate_canonicalPacketGenerator]
  rw [hpacket] at hc
  norm_num at hc

theorem cellDegreeOneTransport_canonicalDefectGenerator
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (pe : XiGammaEulerCalderonWittCell) :
    xiGammaEulerCalderonWittCellDegreeOneTransport c
        (canonicalCellDefectGenerator pe) =
      canonicalCellDefectGenerator pe := by
  rw [canonicalCellDefectGenerator,
    xiGammaEulerCalderonWittCellDegreeOneTransport_lof]
  congr 1
  ext <;> simp [deningerCalderonWittPacketLegTransport]

theorem cellDegreeOneTransport_canonicalPacketGenerator
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (pe : XiGammaEulerCalderonWittCell) :
    xiGammaEulerCalderonWittCellDegreeOneTransport c
        (canonicalCellPacketGenerator pe) =
      c pe • canonicalCellPacketGenerator pe := by
  rw [canonicalCellPacketGenerator,
    xiGammaEulerCalderonWittCellDegreeOneTransport_lof]
  rw [← map_smul]
  congr 1
  ext <;> simp [deningerCalderonWittPacketLegTransport]

theorem cellExteriorTransport_defectDefect
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    xiGammaEulerCalderonWittCellExteriorTransport c
        (canonicalDefectDefectCellCarrier ij) =
      canonicalDefectDefectCellCarrier ij := by
  rw [xiGammaEulerCalderonWittCellExteriorTransport,
    canonicalDefectDefectCellCarrier,
    exteriorPower.map_apply_ιMulti]
  apply congrArg
    (fun f : Fin 2 → XiGammaEulerCalderonWittCellDegreeOne =>
      exteriorPower.ιMulti ℂ 2 f)
  funext k
  fin_cases k
  · exact cellDegreeOneTransport_canonicalDefectGenerator c ij.1.1
  · exact cellDegreeOneTransport_canonicalDefectGenerator c ij.1.2

theorem cellExteriorTransport_packetPacket
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    xiGammaEulerCalderonWittCellExteriorTransport c
        (canonicalPacketPacketCellCarrier ij) =
      (c ij.1.1 * c ij.1.2) •
        canonicalPacketPacketCellCarrier ij := by
  rw [xiGammaEulerCalderonWittCellExteriorTransport,
    canonicalPacketPacketCellCarrier,
    exteriorPower.map_apply_ιMulti]
  have hscale :=
    (exteriorPower.ιMulti ℂ 2
      (M := XiGammaEulerCalderonWittCellDegreeOne)).map_smul_univ
        ![c ij.1.1, c ij.1.2]
        ![canonicalCellPacketGenerator ij.1.1,
          canonicalCellPacketGenerator ij.1.2]
  calc
    exteriorPower.ιMulti ℂ 2
        (xiGammaEulerCalderonWittCellDegreeOneTransport c ∘
          ![canonicalCellPacketGenerator ij.1.1,
            canonicalCellPacketGenerator ij.1.2]) =
      exteriorPower.ιMulti ℂ 2
        ![c ij.1.1 • canonicalCellPacketGenerator ij.1.1,
          c ij.1.2 • canonicalCellPacketGenerator ij.1.2] := by
        apply congrArg
        funext k
        fin_cases k
        · exact cellDegreeOneTransport_canonicalPacketGenerator c ij.1.1
        · exact cellDegreeOneTransport_canonicalPacketGenerator c ij.1.2
    _ = _ := by
      have hf :
          (fun k : Fin 2 =>
            ![c ij.1.1, c ij.1.2] k •
              ![canonicalCellPacketGenerator ij.1.1,
                canonicalCellPacketGenerator ij.1.2] k) =
            ![c ij.1.1 • canonicalCellPacketGenerator ij.1.1,
              c ij.1.2 • canonicalCellPacketGenerator ij.1.2] := by
        funext k
        fin_cases k <;> rfl
      rw [← hf]
      simpa only [Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one] using hscale

theorem cellExteriorTransport_pureHodge
    (c : XiGammaEulerCalderonWittCell → ℂ)
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    xiGammaEulerCalderonWittCellExteriorTransport c
        (canonicalPureHodgeCellCarrier ij).1 =
      canonicalDefectDefectCellCarrier ij +
        (c ij.1.1 * c ij.1.2) •
          canonicalPacketPacketCellCarrier ij := by
  rw [canonicalPureHodgeCellCarrier]
  change
    xiGammaEulerCalderonWittCellExteriorTransport c
        (canonicalDefectDefectCellCarrier ij +
          canonicalPacketPacketCellCarrier ij) = _
  rw [map_add, cellExteriorTransport_defectDefect,
    cellExteriorTransport_packetPacket]

/-! Source-level two-packet landing. -/

def primitiveCriticalAmplitudeCoefficient
    (pe : XiGammaEulerCalderonWittCell) : ℂ :=
  (xiGammaEulerPrimitiveBoundaryAmplitude 0 pe : ℂ)

def anchoredPureKernel (n p q : ℕ) : ℝ :=
  (PrimitivePromotedTwoScale.relativeHeight n q ^ (2 : ℕ) -
      PrimitivePromotedTwoScale.relativeHeight n p ^ (2 : ℕ)) *
    Real.sin (PrimitivePromotedTwoScale.twoScalePhase *
      (PrimitivePromotedTwoScale.relativeHeight n q -
        PrimitivePromotedTwoScale.relativeHeight n p))

theorem anchoredCrossPair_eq_amplitudes_mul_pureKernel
    (n p q : ℕ) :
    PrimitivePromotedTwoScale.anchoredCrossPair n p q =
      xiGammaEulerPrimitiveDepthZeroAmplitude p *
        xiGammaEulerPrimitiveDepthZeroAmplitude q *
          anchoredPureKernel n p q := by
  unfold PrimitivePromotedTwoScale.anchoredCrossPair anchoredPureKernel
  ring

theorem primitiveBoundaryAmplitude_depthZero
    (p : Nat.Primes) :
    xiGammaEulerPrimitiveBoundaryAmplitude 0 (p, 0) =
      xiGammaEulerPrimitiveDepthZeroAmplitude p := by
  rw [xiGammaEulerPrimitiveBoundaryAmplitude_zero_eq_primitiveFibreCriticalCurrent]
  simp [primitiveFibreCriticalCurrent,
    xiGammaEulerPrimitiveDepthZeroAmplitude]

def purePacketPrelandingCoefficient
    (n : ℕ) (p q : Nat.Primes) (r s : ℕ) : ℝ :=
  2 * anchoredPureKernel n p q *
      PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, 0) r *
      PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, 0) s /
    ((PrimitivePromotedCofinalDepth.primeDepthMultiplicity p : ℝ) *
      (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q : ℝ))

theorem purePacketPrelandingCoefficient_mul_landing
    (n : ℕ) (p q : Nat.Primes) (r s : ℕ) :
    purePacketPrelandingCoefficient n p q r s *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 (p, r) *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 (q, s) =
      PrimitivePromotedCofinalDepth.landedDepthPairProfile n p q
        ⟨r % PrimitivePromotedCofinalDepth.primeDepthMultiplicity p,
          Nat.mod_lt _
            (PrimitivePromotedCofinalDepth.primeDepthMultiplicity_pos
              p.property.one_lt)⟩
        ⟨s % PrimitivePromotedCofinalDepth.primeDepthMultiplicity q,
          Nat.mod_lt _
            (PrimitivePromotedCofinalDepth.primeDepthMultiplicity_pos
              q.property.one_lt)⟩ := by
  have hp :=
    PrimitivePromotedCofinalDepth.criticalDepthDeattenuation_mul_landing
      (p, 0) r
  have hq :=
    PrimitivePromotedCofinalDepth.criticalDepthDeattenuation_mul_landing
      (q, 0) s
  have hp' :
      PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, 0) r *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 (p, r) =
        xiGammaEulerPrimitiveBoundaryAmplitude 0 (p, 0) := by
    simpa using hp
  have hq' :
      PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, 0) s *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 (q, s) =
        xiGammaEulerPrimitiveBoundaryAmplitude 0 (q, 0) := by
    simpa using hq
  unfold purePacketPrelandingCoefficient
    PrimitivePromotedCofinalDepth.landedDepthPairProfile
  let den : ℝ :=
    (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p : ℝ) *
      (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q : ℝ)
  calc
    _ = 2 * anchoredPureKernel n p q *
          (PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (p, 0) r *
            xiGammaEulerPrimitiveBoundaryAmplitude 0 (p, r)) *
          (PrimitivePromotedCofinalDepth.criticalDepthDeattenuation (q, 0) s *
            xiGammaEulerPrimitiveBoundaryAmplitude 0 (q, s)) / den := by
      dsimp only [den]
      ring
    _ = 2 * anchoredPureKernel n p q *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 (p, 0) *
          xiGammaEulerPrimitiveBoundaryAmplitude 0 (q, 0) / den := by
      rw [hp', hq']
    _ = _ := by
      dsimp only [den]
      rw [primitiveBoundaryAmplitude_depthZero,
        primitiveBoundaryAmplitude_depthZero,
        anchoredCrossPair_eq_amplitudes_mul_pureKernel]
      ring

def shiftedPureOrderedDistinctCellPair
    {p q : Nat.Primes} (hpq : p ≠ q) (r s : ℕ) :
    XiGammaEulerCalderonWittOrderedDistinctCellPair :=
  ⟨((p, r), (q, s)), by
    intro h
    exact hpq (Prod.mk.inj h).1⟩

theorem purePacket_prelanding_exteriorTransport
    {p q : Nat.Primes} (hpq : p ≠ q)
    (n r s : ℕ) :
    xiGammaEulerCalderonWittCellExteriorTransport
        primitiveCriticalAmplitudeCoefficient
        ((purePacketPrelandingCoefficient n p q r s : ℂ) •
          canonicalPacketPacketCellCarrier
            (shiftedPureOrderedDistinctCellPair hpq r s)) =
      (PrimitivePromotedCofinalDepth.landedDepthPairProfile n p q
          ⟨r % PrimitivePromotedCofinalDepth.primeDepthMultiplicity p,
            Nat.mod_lt _
              (PrimitivePromotedCofinalDepth.primeDepthMultiplicity_pos
                p.property.one_lt)⟩
          ⟨s % PrimitivePromotedCofinalDepth.primeDepthMultiplicity q,
            Nat.mod_lt _
              (PrimitivePromotedCofinalDepth.primeDepthMultiplicity_pos
                q.property.one_lt)⟩ : ℂ) •
        canonicalPacketPacketCellCarrier
          (shiftedPureOrderedDistinctCellPair hpq r s) := by
  rw [map_smul, cellExteriorTransport_packetPacket]
  rw [smul_smul]
  apply congrArg
    (fun z : ℂ => z •
      canonicalPacketPacketCellCarrier
        (shiftedPureOrderedDistinctCellPair hpq r s))
  change
    (purePacketPrelandingCoefficient n p q r s : ℂ) *
      ((xiGammaEulerPrimitiveBoundaryAmplitude 0 (p, r) : ℂ) *
        (xiGammaEulerPrimitiveBoundaryAmplitude 0 (q, s) : ℂ)) = _
  norm_cast
  rw [← mul_assoc]
  exact purePacketPrelandingCoefficient_mul_landing n p q r s

theorem purePacket_prelanding_exteriorTransport_fin
    {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ)
    (r : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p))
    (s : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q)) :
    xiGammaEulerCalderonWittCellExteriorTransport
        primitiveCriticalAmplitudeCoefficient
        ((purePacketPrelandingCoefficient n p q r.1 s.1 : ℂ) •
          canonicalPacketPacketCellCarrier
            (shiftedPureOrderedDistinctCellPair hpq r.1 s.1)) =
      (PrimitivePromotedCofinalDepth.landedDepthPairProfile n p q r s : ℂ) •
        canonicalPacketPacketCellCarrier
          (shiftedPureOrderedDistinctCellPair hpq r.1 s.1) := by
  simpa [Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt s.2] using
    purePacket_prelanding_exteriorTransport hpq n r.1 s.1

abbrev PureHodgeDepthPairProfileSpace (p q : ℕ) :=
  PrimitivePromotedCofinalDepth.LandedDepthPairProfileSpace p q ×
    PrimitivePromotedCofinalDepth.LandedDepthPairProfileSpace p q

def pureHodgeExchange
    {p q : ℕ} (x : PureHodgeDepthPairProfileSpace p q) :
    PureHodgeDepthPairProfileSpace p q :=
  (x.2, x.1)

theorem pureHodgeExchange_sq
    {p q : ℕ} (x : PureHodgeDepthPairProfileSpace p q) :
    pureHodgeExchange (pureHodgeExchange x) = x := by
  rcases x with ⟨x, y⟩
  rfl

def pureHodgeLandedDepthPairProfile (n p q : ℕ) :
    PureHodgeDepthPairProfileSpace p q :=
  (PrimitivePromotedCofinalDepth.landedDepthPairProfile n p q,
    PrimitivePromotedCofinalDepth.landedDepthPairProfile n p q)

theorem pureHodgeLandedDepthPairProfile_fixed
    (n p q : ℕ) :
    pureHodgeExchange (pureHodgeLandedDepthPairProfile n p q) =
      pureHodgeLandedDepthPairProfile n p q := by
  rfl

def pureHodgeCountertransportCapacity (n : ℕ) : ℝ :=
  2 * PrimitivePromotedCofinalDepth.cofinalDepthCountertransportCapacity n

theorem pureHodgeCountertransportCapacity_eq_reflected
    {n : ℕ} (hn : 0 < n) :
    pureHodgeCountertransportCapacity n =
      PrimitivePromotedCofinalDepth.reflectedHodgeCountertransportCapacity n := by
  rw [PrimitivePromotedCofinalDepth.reflectedHodgeCountertransportCapacity_eq hn]
  rfl

theorem pureHodgeCountertransportCapacity_le
    {n : ℕ} (hn : 0 < n) :
    pureHodgeCountertransportCapacity n ≤ 200 * 289 ^ (2 : ℕ) := by
  rw [pureHodgeCountertransportCapacity_eq_reflected hn]
  exact
    PrimitivePromotedCofinalDepth.reflectedHodgeCountertransportCapacity_le hn

/-! Complete cofinal two-scale pure-Hodge carrier. -/

def fivePrimeBlockPrime
    (n : ℕ) (p : {p // p ∈ suzukiMangoldtFivePrimeBlock n}) :
    Nat.Primes :=
  ⟨p.1, (mem_suzukiMangoldtFivePrimeBlock.mp p.2).1⟩

theorem lowHighFivePrimeBlockPrime_ne
    {n : ℕ} (_hn : 0 < n)
    (p : {p // p ∈ suzukiMangoldtFivePrimeBlock n})
    (q : {q // q ∈ suzukiMangoldtFivePrimeBlock
      (PrimitivePromotedTwoScale.sourceDilation * n)}) :
    fivePrimeBlockPrime n p ≠
      fivePrimeBlockPrime
        (PrimitivePromotedTwoScale.sourceDilation * n) q := by
  intro hpq
  have hpqNat : p.1 = q.1 := congrArg Subtype.val hpq
  have hpUpper := (mem_suzukiMangoldtFivePrimeBlock.mp p.2).2.2
  have hqLower := (mem_suzukiMangoldtFivePrimeBlock.mp q.2).2.1
  rw [← hpqNat] at hqLower
  norm_num [PrimitivePromotedTwoScale.sourceDilation] at hqLower
  omega

def lowHighDepthOrderedDistinctCellPair
    {n : ℕ} (hn : 0 < n)
    (p : {p // p ∈ suzukiMangoldtFivePrimeBlock n})
    (q : {q // q ∈ suzukiMangoldtFivePrimeBlock
      (PrimitivePromotedTwoScale.sourceDilation * n)})
    (r : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p.1))
    (s : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q.1)) :
    XiGammaEulerCalderonWittOrderedDistinctCellPair :=
  shiftedPureOrderedDistinctCellPair
    (lowHighFivePrimeBlockPrime_ne hn p q) r.1 s.1

def landedPureHodgeCellCarrier
    {n : ℕ} (hn : 0 < n)
    (p : {p // p ∈ suzukiMangoldtFivePrimeBlock n})
    (q : {q // q ∈ suzukiMangoldtFivePrimeBlock
      (PrimitivePromotedTwoScale.sourceDilation * n)})
    (r : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p.1))
    (s : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q.1)) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  (PrimitivePromotedCofinalDepth.landedDepthPairProfile
      n p.1 q.1 r s : ℂ) •
    canonicalPureHodgeCellCarrier
      (lowHighDepthOrderedDistinctCellPair hn p q r s)

def prelandingPureHodgeCellCarrier
    {n : ℕ} (hn : 0 < n)
    (p : {p // p ∈ suzukiMangoldtFivePrimeBlock n})
    (q : {q // q ∈ suzukiMangoldtFivePrimeBlock
      (PrimitivePromotedTwoScale.sourceDilation * n)})
    (r : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p.1))
    (s : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q.1)) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  let ij := lowHighDepthOrderedDistinctCellPair hn p q r s
  (PrimitivePromotedCofinalDepth.landedDepthPairProfile
      n p.1 q.1 r s : ℂ) •
      canonicalDefectDefectIncidenceCarrier ij +
    (purePacketPrelandingCoefficient n
      (fivePrimeBlockPrime n p)
      (fivePrimeBlockPrime
        (PrimitivePromotedTwoScale.sourceDilation * n) q)
      r.1 s.1 : ℂ) •
      canonicalPacketPacketIncidenceCarrier ij

theorem prelandingPureHodgeCellCarrier_mem_actual
    {n : ℕ} (hn : 0 < n) (a : ℝ)
    (p : {p // p ∈ suzukiMangoldtFivePrimeBlock n})
    (q : {q // q ∈ suzukiMangoldtFivePrimeBlock
      (PrimitivePromotedTwoScale.sourceDilation * n)})
    (r : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p.1))
    (s : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q.1)) :
    prelandingPureHodgeCellCarrier hn p q r s ∈
      actualCellGammaAdmittedHodgeSector a := by
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _
      (canonicalDefectDefectIncidenceCarrier_mem_actual a
        (lowHighDepthOrderedDistinctCellPair hn p q r s)))
    (Submodule.smul_mem _ _
      (canonicalPacketPacketIncidenceCarrier_mem_actual a
        (lowHighDepthOrderedDistinctCellPair hn p q r s)))

theorem prelandingPureHodgeCellCarrier_transport
    {n : ℕ} (hn : 0 < n)
    (p : {p // p ∈ suzukiMangoldtFivePrimeBlock n})
    (q : {q // q ∈ suzukiMangoldtFivePrimeBlock
      (PrimitivePromotedTwoScale.sourceDilation * n)})
    (r : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p.1))
    (s : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q.1)) :
    xiGammaEulerCalderonWittCellMilnorIncidenceTransport
        primitiveCriticalAmplitudeCoefficient
        (prelandingPureHodgeCellCarrier hn p q r s) =
      landedPureHodgeCellCarrier hn p q r s := by
  apply Subtype.ext
  let pp : Nat.Primes := fivePrimeBlockPrime n p
  let qq : Nat.Primes := fivePrimeBlockPrime
    (PrimitivePromotedTwoScale.sourceDilation * n) q
  have hpq : pp ≠ qq := lowHighFivePrimeBlockPrime_ne hn p q
  change
    xiGammaEulerCalderonWittCellExteriorTransport
        primitiveCriticalAmplitudeCoefficient
        ((PrimitivePromotedCofinalDepth.landedDepthPairProfile
            n p.1 q.1 r s : ℂ) •
              canonicalDefectDefectCellCarrier
                (shiftedPureOrderedDistinctCellPair hpq r.1 s.1) +
          (purePacketPrelandingCoefficient n pp qq r.1 s.1 : ℂ) •
            canonicalPacketPacketCellCarrier
              (shiftedPureOrderedDistinctCellPair hpq r.1 s.1)) =
      (PrimitivePromotedCofinalDepth.landedDepthPairProfile
          n p.1 q.1 r s : ℂ) •
        (canonicalDefectDefectCellCarrier
            (shiftedPureOrderedDistinctCellPair hpq r.1 s.1) +
          canonicalPacketPacketCellCarrier
            (shiftedPureOrderedDistinctCellPair hpq r.1 s.1))
  rw [map_add, map_smul, cellExteriorTransport_defectDefect,
    purePacket_prelanding_exteriorTransport_fin hpq n r s]
  dsimp only [pp, qq, fivePrimeBlockPrime]
  module

theorem landedPureHodgeCellCarrier_mem_actual
    {n : ℕ} (hn : 0 < n) (a : ℝ)
    (p : {p // p ∈ suzukiMangoldtFivePrimeBlock n})
    (q : {q // q ∈ suzukiMangoldtFivePrimeBlock
      (PrimitivePromotedTwoScale.sourceDilation * n)})
    (r : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p.1))
    (s : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q.1)) :
    landedPureHodgeCellCarrier hn p q r s ∈
      actualCellGammaAdmittedHodgeSector a := by
  exact Submodule.smul_mem _ _
    (canonicalPureHodgeCellCarrier_mem_actual a
      (lowHighDepthOrderedDistinctCellPair hn p q r s))

def cofinalPureHodgeLandedCarrier
    (n : ℕ) (hn : 0 < n) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  ∑ p ∈ (suzukiMangoldtFivePrimeBlock n).attach,
    ∑ q ∈ (suzukiMangoldtFivePrimeBlock
        (PrimitivePromotedTwoScale.sourceDilation * n)).attach,
      ∑ r : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p.1),
        ∑ s : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q.1),
          landedPureHodgeCellCarrier hn p q r s

def cofinalPureHodgePrelandingCarrier
    (n : ℕ) (hn : 0 < n) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  ∑ p ∈ (suzukiMangoldtFivePrimeBlock n).attach,
    ∑ q ∈ (suzukiMangoldtFivePrimeBlock
        (PrimitivePromotedTwoScale.sourceDilation * n)).attach,
      ∑ r : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p.1),
        ∑ s : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q.1),
          prelandingPureHodgeCellCarrier hn p q r s

theorem cofinalPureHodgePrelandingCarrier_mem_actual
    (n : ℕ) (hn : 0 < n) (a : ℝ) :
    cofinalPureHodgePrelandingCarrier n hn ∈
      actualCellGammaAdmittedHodgeSector a := by
  unfold cofinalPureHodgePrelandingCarrier
  apply Submodule.sum_mem
  intro p hp
  apply Submodule.sum_mem
  intro q hq
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.sum_mem
  intro s hs
  exact prelandingPureHodgeCellCarrier_mem_actual hn a p q r s

theorem cofinalPureHodgePrelandingCarrier_transport
    (n : ℕ) (hn : 0 < n) :
    xiGammaEulerCalderonWittCellMilnorIncidenceTransport
        primitiveCriticalAmplitudeCoefficient
        (cofinalPureHodgePrelandingCarrier n hn) =
      cofinalPureHodgeLandedCarrier n hn := by
  unfold cofinalPureHodgePrelandingCarrier
    cofinalPureHodgeLandedCarrier
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact prelandingPureHodgeCellCarrier_transport hn p q r s

theorem cofinalPureHodgeLandedCarrier_mem_actual
    (n : ℕ) (hn : 0 < n) (a : ℝ) :
    cofinalPureHodgeLandedCarrier n hn ∈
      actualCellGammaAdmittedHodgeSector a := by
  unfold cofinalPureHodgeLandedCarrier
  apply Submodule.sum_mem
  intro p hp
  apply Submodule.sum_mem
  intro q hq
  apply Submodule.sum_mem
  intro r hr
  apply Submodule.sum_mem
  intro s hs
  exact landedPureHodgeCellCarrier_mem_actual hn a p q r s

theorem cellMilnorGreenRetraction_incidence
    (i : xiGammaEulerCalderonWittCellMilnorIncidence) :
    xiGammaEulerCalderonWittCellMilnorGreenRetraction i.1 = i := by
  apply Subtype.ext
  rw [xiGammaEulerCalderonWittCellMilnorGreenRetraction_coe,
    i.2, map_zero, sub_zero]

theorem cofinalPureHodgeLandedCarrier_green
    (n : ℕ) (hn : 0 < n) :
    xiGammaEulerCalderonWittCellMilnorGreenRetraction
        (cofinalPureHodgeLandedCarrier n hn).1 =
      cofinalPureHodgeLandedCarrier n hn :=
  cellMilnorGreenRetraction_incidence _

theorem pureHodgeCountertransport_readout_eq
    {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        ∑ q ∈ suzukiMangoldtFivePrimeBlock
            (PrimitivePromotedTwoScale.sourceDilation * n),
          ∑ r : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity p),
            ∑ s : Fin (PrimitivePromotedCofinalDepth.primeDepthMultiplicity q),
              PrimitivePromotedCofinalDepth.landedDepthPairProfile n p q r s =
      PrimitivePromotedTwoScale.anchoredTwoScaleEnergy n :=
  PrimitivePromotedCofinalDepth.cofinalDepthCountertransport_readout_eq hn

theorem pureScalarReadoutGain_linear_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ))
    {gain : ℝ} (hgain : 0 ≤ gain)
    (hreadout :
      PrimitivePromotedTwoScale.anchoredTwoScaleEnergy n ≤
        gain * Real.sqrt (pureHodgeCountertransportCapacity n)) :
    (5 / 289 : ℝ) * n ≤ gain := by
  have hnPos : 0 < n := by
    have : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
    exact_mod_cast this
  have hcapNonneg :
      0 ≤ pureHodgeCountertransportCapacity n := by
    unfold pureHodgeCountertransportCapacity
    exact mul_nonneg (by norm_num)
      (PrimitivePromotedCofinalDepth.cofinalDepthCountertransportCapacity_nonneg n)
  have hcapUpper := pureHodgeCountertransportCapacity_le hnPos
  have hsqrtSq :
      Real.sqrt (pureHodgeCountertransportCapacity n) ^ (2 : ℕ) =
        pureHodgeCountertransportCapacity n :=
    Real.sq_sqrt hcapNonneg
  have hsqrtUpper :
      Real.sqrt (pureHodgeCountertransportCapacity n) ≤
        20 * 289 := by
    nlinarith [Real.sqrt_nonneg (pureHodgeCountertransportCapacity n)]
  have henergy :=
    PrimitivePromotedTwoScale.anchoredTwoScaleEnergy_linear_lower hn
  have hmul :
      gain * Real.sqrt (pureHodgeCountertransportCapacity n) ≤
        gain * (20 * 289) :=
    mul_le_mul_of_nonneg_left hsqrtUpper hgain
  nlinarith

/-- No aperture-independent bounded scalar consumer can extend all finite
pure-Hodge codiagonals while respecting the proved source-normal capacity. -/
theorem no_uniform_bounded_pureScalarReadout
    (gain : ℝ) (hgain : 0 ≤ gain)
    (hreadout : ∀ n : ℕ, Real.exp 20 ≤ (n : ℝ) →
      PrimitivePromotedTwoScale.anchoredTwoScaleEnergy n ≤
        gain * Real.sqrt (pureHodgeCountertransportCapacity n)) :
    False := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt
    (max (Real.exp 20) ((289 / 5 : ℝ) * gain))
  have hnExp : Real.exp 20 ≤ (n : ℝ) :=
    (le_max_left _ _).trans hn.le
  have hnGain : (289 / 5 : ℝ) * gain < (n : ℝ) :=
    (le_max_right _ _).trans_lt hn
  have hlower :=
    pureScalarReadoutGain_linear_lower hnExp hgain
      (hreadout n hnExp)
  have hstrict : gain < (5 / 289 : ℝ) * n := by
    nlinarith
  exact (not_lt_of_ge hlower) hstrict

/-- Class-complete continuous-linear version of the pure codiagonal no-go.
Any single normed completion retaining the uniform carrier norm makes the
finite readout sequence impossible for one bounded scalar functional. -/
theorem no_continuousLinearMap_pureHodgeReadout
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (carrier : ℕ → E) (reader : E →L[ℂ] ℂ)
    (hcarrier : ∀ n : ℕ, Real.exp 20 ≤ (n : ℝ) →
      ‖carrier n‖ ≤ Real.sqrt (pureHodgeCountertransportCapacity n))
    (hreadout : ∀ n : ℕ, Real.exp 20 ≤ (n : ℝ) →
      reader (carrier n) =
        (PrimitivePromotedTwoScale.anchoredTwoScaleEnergy n : ℂ)) :
    False := by
  apply no_uniform_bounded_pureScalarReadout ‖reader‖ (norm_nonneg reader)
  intro n hn
  have hop := reader.le_opNorm (carrier n)
  rw [hreadout n hn, Complex.norm_real, Real.norm_eq_abs] at hop
  have henergy :=
    PrimitivePromotedTwoScale.anchoredTwoScaleEnergy_linear_lower hn
  have hnNonneg : (0 : ℝ) ≤ n := by positivity
  have henergyNonneg :
      0 ≤ PrimitivePromotedTwoScale.anchoredTwoScaleEnergy n := by
    nlinarith
  rw [abs_of_nonneg henergyNonneg] at hop
  exact hop.trans (mul_le_mul_of_nonneg_left
    (hcarrier n hn) (norm_nonneg reader))

end PrimitivePromotedPureHodgeCountertransport
end
end RHTower
