import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedPureHodgeCountertransport

/-!
# Pure-Hodge modular transgression

The primary Gamma/Hardy boundary annihilates both pure cell incidences
\`d_i wedge d_j\` and \`w_i wedge w_j\`.  Nevertheless, their Hodge exchange
retains the actual unsquared mixed boundary as a secondary operation.

This module constructs the balanced modular orbit on the canonical pure
Hodge plane.  Hodge exchange conjugates displacement \`a\` to \`-a\`; hence its
reflection-odd part is Hodge-anti-fixed and remains actual-admitted
incidence.  Pairing its packet--packet coordinate against the dual
defect--defect leg with the source half-height weight recovers exactly the
actual mixed Gamma/Hardy boundary coefficient, including sign and scale.

The final classification supplies the topology forced by this trace.  At
fixed distinct prime clocks, the two-component balanced graph capacity is
the sum of reciprocal Gamma sewing costs.  It is uniformly bounded over
cofinal valuation depth exactly at zero modular displacement; otherwise it
diverges to infinity.  Thus pure admission preserves the missing unsquared
charge, but only through a singular secondary transgression.
-/

open Complex Set Finset Filter Topology
open scoped DirectSum BigOperators

namespace RHTower

noncomputable section

namespace PrimitivePromotedPureHodgeModularTransgression

open PrimitivePromotedCellHodgeRigidity
open PrimitivePromotedPureHodgeCountertransport

abbrev PureHodgeCellPlane := ℂ × ℂ

def pureHodgeCellExchange :
    PureHodgeCellPlane →ₗ[ℂ] PureHodgeCellPlane where
  toFun z := (z.2, z.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pureHodgeCellModularRate
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) : ℝ :=
  xiGammaEulerPrimitiveModularRate ij.1.1 +
    xiGammaEulerPrimitiveModularRate ij.1.2

def pureHodgeCellBalancedModularTransport
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    PureHodgeCellPlane →ₗ[ℂ] PureHodgeCellPlane where
  toFun z :=
    ((Real.exp (-a * pureHodgeCellModularRate ij) : ℂ) * z.1,
      (Real.exp (a * pureHodgeCellModularRate ij) : ℂ) * z.2)
  map_add' x y := by
    ext <;> simp [mul_add]
  map_smul' c x := by
    ext <;> simp [smul_eq_mul] <;> ring

theorem pureHodgeCellExchange_balanced
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair)
    (z : PureHodgeCellPlane) :
    pureHodgeCellExchange
        (pureHodgeCellBalancedModularTransport a ij z) =
      pureHodgeCellBalancedModularTransport (-a) ij
        (pureHodgeCellExchange z) := by
  ext <;> simp [pureHodgeCellExchange,
    pureHodgeCellBalancedModularTransport]

def pureHodgeCellFixedCoefficients : PureHodgeCellPlane := (1, 1)

def pureHodgeCellOddTransgressionCoefficients
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    PureHodgeCellPlane :=
  (1 / 2 : ℂ) •
    (pureHodgeCellBalancedModularTransport a ij
        pureHodgeCellFixedCoefficients -
      pureHodgeCellBalancedModularTransport (-a) ij
        pureHodgeCellFixedCoefficients)

theorem pureHodgeCellOddTransgressionCoefficients_antiFixed
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    pureHodgeCellExchange
        (pureHodgeCellOddTransgressionCoefficients a ij) =
      -pureHodgeCellOddTransgressionCoefficients a ij := by
  ext <;> simp [pureHodgeCellExchange,
    pureHodgeCellOddTransgressionCoefficients,
    pureHodgeCellBalancedModularTransport,
    pureHodgeCellFixedCoefficients] <;> ring

def pureHodgeCellPlaneEmbedding
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    PureHodgeCellPlane →ₗ[ℂ]
      xiGammaEulerCalderonWittCellMilnorIncidence where
  toFun z :=
    z.1 • canonicalDefectDefectIncidenceCarrier ij +
      z.2 • canonicalPacketPacketIncidenceCarrier ij
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    abel
  map_smul' c x := by
    rcases x with ⟨x, y⟩
    change
      (c * x) • canonicalDefectDefectIncidenceCarrier ij +
          (c * y) • canonicalPacketPacketIncidenceCarrier ij =
        c • (x • canonicalDefectDefectIncidenceCarrier ij +
          y • canonicalPacketPacketIncidenceCarrier ij)
    module

theorem pureHodgeCellPlaneEmbedding_mem_actual
    (b : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair)
    (z : PureHodgeCellPlane) :
    pureHodgeCellPlaneEmbedding ij z ∈
      actualCellGammaAdmittedHodgeSector b := by
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _
      (canonicalDefectDefectIncidenceCarrier_mem_actual b ij))
    (Submodule.smul_mem _ _
      (canonicalPacketPacketIncidenceCarrier_mem_actual b ij))

def pureHodgeCellOddTransgression
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  pureHodgeCellPlaneEmbedding ij
    (pureHodgeCellOddTransgressionCoefficients a ij)

theorem pureHodgeCellOddTransgression_mem_actual
    (a b : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    pureHodgeCellOddTransgression a ij ∈
      actualCellGammaAdmittedHodgeSector b :=
  pureHodgeCellPlaneEmbedding_mem_actual b ij _

theorem cellPacketPacketExterior_defectDefect
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    cellPacketPacketExterior ij.1.1 ij.1.2
        (canonicalDefectDefectCellCarrier ij) = 0 := by
  rw [cellPacketPacketExterior, canonicalDefectDefectCellCarrier,
    cellCoordinateExterior_ιMulti]
  simp [cellPacketCoordinate_canonicalDefectGenerator]

def pureHodgeCellPoincareWeight
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude 0 ij.1.1 *
    xiGammaEulerPrimitiveBoundaryAmplitude 0 ij.1.2 *
      (xiGammaEulerBoundaryHalfHeight ij.1.1.1 ij.1.1.2 -
        xiGammaEulerBoundaryHalfHeight ij.1.2.1 ij.1.2.2)

def pureHodgeCellPoincareTrace
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    xiGammaEulerCalderonWittCellMilnorIncidence →ₗ[ℂ] ℂ where
  toFun x :=
    (pureHodgeCellPoincareWeight ij : ℂ) *
      cellPacketPacketExterior ij.1.1 ij.1.2 x.1
  map_add' x y := by
    rw [Submodule.coe_add, map_add]
    ring
  map_smul' c x := by
    rw [Submodule.coe_smul, map_smul]
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

theorem pureHodgeCellPoincareTrace_planeEmbedding
    (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair)
    (z : PureHodgeCellPlane) :
    pureHodgeCellPoincareTrace ij
        (pureHodgeCellPlaneEmbedding ij z) =
      (pureHodgeCellPoincareWeight ij : ℂ) * z.2 := by
  change
    (pureHodgeCellPoincareWeight ij : ℂ) *
        cellPacketPacketExterior ij.1.1 ij.1.2
          (z.1 • canonicalDefectDefectCellCarrier ij +
            z.2 • canonicalPacketPacketCellCarrier ij) = _
  rw [map_add, map_smul, map_smul,
    cellPacketPacketExterior_defectDefect,
    cellPacketPacketExterior_canonical]
  simp

theorem reflectionOddExterior_eq_pureHodgePoincareFactor
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    xiGammaEulerPrimitiveReflectionOddExterior a ij.1.1 ij.1.2 =
      pureHodgeCellPoincareWeight ij *
        ((Real.exp (a * pureHodgeCellModularRate ij) -
          Real.exp (-a * pureHodgeCellModularRate ij)) / 2) := by
  rw [xiGammaEulerPrimitiveReflectionOddExterior,
    xiGammaEulerPrimitiveModularExterior_eq,
    xiGammaEulerPrimitiveModularExterior_eq]
  unfold pureHodgeCellPoincareWeight pureHodgeCellModularRate
  ring

theorem pureHodgeCellOddTransgressionCoefficients_snd
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    (pureHodgeCellOddTransgressionCoefficients a ij).2 =
      (1 / 2 : ℂ) *
        ((Real.exp (a * pureHodgeCellModularRate ij) : ℂ) -
          (Real.exp (-a * pureHodgeCellModularRate ij) : ℂ)) := by
  simp [pureHodgeCellOddTransgressionCoefficients,
    pureHodgeCellBalancedModularTransport,
    pureHodgeCellFixedCoefficients, smul_eq_mul]

theorem pureHodgeCellPoincareTrace_oddTransgression_eq_reflectionOddExterior
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    pureHodgeCellPoincareTrace ij
        (pureHodgeCellOddTransgression a ij) =
      (xiGammaEulerPrimitiveReflectionOddExterior
        a ij.1.1 ij.1.2 : ℂ) := by
  rw [pureHodgeCellOddTransgression,
    pureHodgeCellPoincareTrace_planeEmbedding,
    pureHodgeCellOddTransgressionCoefficients_snd]
  have hreal :
      pureHodgeCellPoincareWeight ij *
          ((1 / 2 : ℝ) *
            (Real.exp (a * pureHodgeCellModularRate ij) -
              Real.exp (-a * pureHodgeCellModularRate ij))) =
        xiGammaEulerPrimitiveReflectionOddExterior
          a ij.1.1 ij.1.2 := by
    rw [reflectionOddExterior_eq_pureHodgePoincareFactor]
    ring
  calc
    (pureHodgeCellPoincareWeight ij : ℂ) *
          ((1 / 2 : ℂ) *
            ((Real.exp (a * pureHodgeCellModularRate ij) : ℂ) -
              (Real.exp (-a * pureHodgeCellModularRate ij) : ℂ))) =
        (pureHodgeCellPoincareWeight ij *
          ((1 / 2 : ℝ) *
            (Real.exp (a * pureHodgeCellModularRate ij) -
              Real.exp (-a * pureHodgeCellModularRate ij))) : ℝ) := by
          push_cast
          rfl
    _ = (xiGammaEulerPrimitiveReflectionOddExterior
          a ij.1.1 ij.1.2 : ℂ) := by exact_mod_cast hreal

theorem pureHodgeCellPoincareTrace_eq_actualMixedBoundary
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    pureHodgeCellPoincareTrace ij
        (pureHodgeCellOddTransgression a ij) =
      cellReflectionOddBoundaryCoordinate a ij.1.1 ij.1.2
        (canonicalDistinctCellCarrier ij) := by
  rw [pureHodgeCellPoincareTrace_oddTransgression_eq_reflectionOddExterior,
    cellReflectionOddBoundaryCoordinate_canonicalDistinctCellCarrier,
    if_pos ⟨rfl, rfl⟩]

theorem pureHodgeCellPoincareTrace_oddTransgression_eq_zero_iff
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    pureHodgeCellPoincareTrace ij
        (pureHodgeCellOddTransgression a ij) = 0 ↔
      a = 0 := by
  rw [pureHodgeCellPoincareTrace_oddTransgression_eq_reflectionOddExterior]
  have hheight :
      xiGammaEulerBoundaryHalfHeight ij.1.1.1 ij.1.1.2 ≠
        xiGammaEulerBoundaryHalfHeight ij.1.2.1 ij.1.2.2 := by
    intro h
    exact ij.2 (xiGammaEulerBoundaryHalfHeight_cell_injective h)
  exact_mod_cast
    xiGammaEulerPrimitiveReflectionOddExterior_eq_zero_iff
      a ij.1.1 ij.1.2 hheight

def pureHodgeCellBalancedCapacity
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) : ℝ :=
  Real.exp (-a * pureHodgeCellModularRate ij) ^ 2 +
    Real.exp (a * pureHodgeCellModularRate ij) ^ 2

theorem pureHodgeCellBalancedCapacity_sub_two
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    pureHodgeCellBalancedCapacity a ij - 2 =
      (Real.exp (a * pureHodgeCellModularRate ij) -
        Real.exp (-a * pureHodgeCellModularRate ij)) ^ 2 := by
  have hmul :
      Real.exp (a * pureHodgeCellModularRate ij) *
          Real.exp (-a * pureHodgeCellModularRate ij) = 1 := by
    rw [← Real.exp_add]
    have hzero :
        a * pureHodgeCellModularRate ij +
            -a * pureHodgeCellModularRate ij = 0 := by ring
    rw [hzero, Real.exp_zero]
  unfold pureHodgeCellBalancedCapacity
  nlinarith

/-- Source-side purity defect: positive graph-capacity excess is exactly
the square of the unsquared secondary Poincare/Gamma trace. -/
theorem pureHodgeCellPoincareTrace_sq_eq_capacityDefect
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    4 * xiGammaEulerPrimitiveReflectionOddExterior
          a ij.1.1 ij.1.2 ^ 2 =
      pureHodgeCellPoincareWeight ij ^ 2 *
        (pureHodgeCellBalancedCapacity a ij - 2) := by
  rw [reflectionOddExterior_eq_pureHodgePoincareFactor,
    pureHodgeCellBalancedCapacity_sub_two]
  ring

theorem pureHodgeCellBalancedCapacity_two_le
    (a : ℝ) (ij : XiGammaEulerCalderonWittOrderedDistinctCellPair) :
    2 ≤ pureHodgeCellBalancedCapacity a ij := by
  rw [← sub_nonneg]
  rw [pureHodgeCellBalancedCapacity_sub_two]
  positivity

/-! Cofinal graph-capacity classification. -/

def pureHodgeBalancedGraphCapacity
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) : ℝ :=
  Real.exp
      (-a * (xiGammaEulerPrimitiveModularRate (p, n) +
        xiGammaEulerPrimitiveModularRate (q, n))) ^ 2 +
    Real.exp
      (a * (xiGammaEulerPrimitiveModularRate (p, n) +
        xiGammaEulerPrimitiveModularRate (q, n))) ^ 2

theorem pureHodgeBalancedGraphCapacity_eq_sewing_add_reflection
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    pureHodgeBalancedGraphCapacity a p q n =
      deningerCalderonWittGammaReflectionSewingCost a p q n +
        deningerCalderonWittGammaReflectionSewingCost (-a) p q n := by
  unfold pureHodgeBalancedGraphCapacity
    deningerCalderonWittGammaReflectionSewingCost
  rw [pow_two, pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1 <;> ring

theorem pureHodgeBalancedGraphCapacity_zero
    (p q : Nat.Primes) (n : ℕ) :
    pureHodgeBalancedGraphCapacity 0 p q n = 2 := by
  norm_num [pureHodgeBalancedGraphCapacity]

theorem gammaReflectionSewingCost_tendsto_atTop_of_pos
    {a : ℝ} (ha : 0 < a) (p q : Nat.Primes) :
    Tendsto
      (fun n : ℕ =>
        deningerCalderonWittGammaReflectionSewingCost a p q n)
      atTop atTop := by
  let c : ℝ :=
    2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))
  have hc : 0 < c := by
    dsimp only [c]
    have hp : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.property.one_lt)
    have hq : 0 < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast q.property.one_lt)
    positivity
  have hlinear :
      Tendsto (fun n : ℕ => c * ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add
      tendsto_const_nhds).const_mul_atTop hc
  apply (Real.tendsto_exp_atTop.comp hlinear).congr'
  filter_upwards with n
  rw [deningerCalderonWittGammaReflectionSewingCost_eq_exp]
  rfl

theorem gammaReflectionSewingCost_pos
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    0 < deningerCalderonWittGammaReflectionSewingCost a p q n := by
  unfold deningerCalderonWittGammaReflectionSewingCost
  exact Real.exp_pos _

theorem pureHodgeBalancedGraphCapacity_tendsto_atTop
    {a : ℝ} (ha : a ≠ 0) (p q : Nat.Primes) :
    Tendsto (fun n : ℕ => pureHodgeBalancedGraphCapacity a p q n)
      atTop atTop := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · have hreflect : 0 < -a := neg_pos.mpr haNeg
    refine tendsto_atTop_mono' atTop ?_
      (gammaReflectionSewingCost_tendsto_atTop_of_pos hreflect p q)
    filter_upwards with n
    rw [pureHodgeBalancedGraphCapacity_eq_sewing_add_reflection]
    exact le_add_of_nonneg_left
      (gammaReflectionSewingCost_pos a p q n).le
  · refine tendsto_atTop_mono' atTop ?_
      (gammaReflectionSewingCost_tendsto_atTop_of_pos haPos p q)
    filter_upwards with n
    rw [pureHodgeBalancedGraphCapacity_eq_sewing_add_reflection]
    exact le_add_of_nonneg_right
      (gammaReflectionSewingCost_pos (-a) p q n).le

theorem pureHodgeBalancedGraphCapacity_uniform_iff
    (a : ℝ) (p q : Nat.Primes) :
    (∃ C : ℝ, ∀ n : ℕ,
      pureHodgeBalancedGraphCapacity a p q n ≤ C) ↔
      a = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra ha
    have hdiv := pureHodgeBalancedGraphCapacity_tendsto_atTop ha p q
    have hev : ∀ᶠ n : ℕ in atTop,
        C + 1 ≤ pureHodgeBalancedGraphCapacity a p q n :=
      (tendsto_atTop.1 hdiv) (C + 1)
    obtain ⟨n, hn⟩ := Filter.Eventually.exists hev
    linarith [hC n]
  · rintro rfl
    exact ⟨2, fun n => by rw [pureHodgeBalancedGraphCapacity_zero]⟩

end PrimitivePromotedPureHodgeModularTransgression
end
end RHTower
