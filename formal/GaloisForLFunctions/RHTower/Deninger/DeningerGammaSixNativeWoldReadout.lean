import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixAdjacentDepthPhysicalReader

/-!
# Native Wold products and the nonlinear physical readout

For the original complete source tail, the Abel readings of the native products
`V₆ (T U₆)`, `(T U₆) V₆`, and their additive commutator have exact nonzero scalar
factors relative to the projected reading at every positive regulator.
Those factors cancel between adjacent depths at a common regulator. All three
trace quotients therefore recover the same fixed physical BV boundary value.

The original multiplicity-top Xi sources are admitted without spectral premises.
Their nonlinear readout is invariant under the native cyclic swap, but the
subtraction discrepancy recovers the same physical value. Vanishing of any of
the three readouts is exactly critical-line placement. Reflected sources retain
the existing Burnol conormal, and finite diagonal repairs disappear before limits.
This does not establish commutator annihilation or the Riemann Hypothesis.
-/

open Complex Real Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

/-- Literal native products and their additive commutator on the original carrier. -/
inductive DeningerGammaSixNativeFace
  | compression | projection | commutator

def deningerGammaSixNativeFaceOperator (face : DeningerGammaSixNativeFace)
    (T : DeningerOrdinaryIntegerEnd) : DeningerOrdinaryIntegerEnd :=
  match face with
  | .compression => deningerOrdinaryIntegerWoldBackward 6 * (T * deningerOrdinaryIntegerWoldShift 6)
  | .projection => T * deningerOrdinaryIntegerDivisibilityProjection 6
  | .commutator =>
      deningerOrdinaryIntegerWoldBackward 6 * (T * deningerOrdinaryIntegerWoldShift 6) -
        T * deningerOrdinaryIntegerDivisibilityProjection 6

theorem deningerGammaSixNativeFaceOperator_projection_eq_swapped
    (T : DeningerOrdinaryIntegerEnd) :
    deningerGammaSixNativeFaceOperator .projection T =
      (T * deningerOrdinaryIntegerWoldShift 6) * deningerOrdinaryIntegerWoldBackward 6 := by
  rw [mul_assoc, deningerOrdinaryIntegerWoldShift_comp_WoldBackward]
  rfl

theorem deningerGammaSixNativeFaceOperator_commutator_eq
    (T : DeningerOrdinaryIntegerEnd) :
    deningerGammaSixNativeFaceOperator .commutator T =
      deningerOrdinaryIntegerWoldBackward 6 * (T * deningerOrdinaryIntegerWoldShift 6) -
        (T * deningerOrdinaryIntegerWoldShift 6) * deningerOrdinaryIntegerWoldBackward 6 := by
  rw [mul_assoc, deningerOrdinaryIntegerWoldShift_comp_WoldBackward]
  rfl

theorem deningerGammaSixNativeFaceOperator_mem_gibbsDomain
    (face : DeningerGammaSixNativeFace) {sigma : ℝ}
    (T : deningerOrdinaryIntegerGibbsDomain sigma) :
    deningerGammaSixNativeFaceOperator face T.val ∈ deningerOrdinaryIntegerGibbsDomain sigma := by
  cases face with
  | compression => exact deningerOrdinaryIntegerGibbsDomain_compression T 6
  | projection => exact deningerOrdinaryIntegerGibbsDomain_rightProjection T 6
  | commutator =>
      exact (deningerOrdinaryIntegerGibbsDomain sigma).sub_mem
        (deningerOrdinaryIntegerGibbsDomain_compression T 6)
        (deningerOrdinaryIntegerGibbsDomain_rightProjection T 6)

def deningerGammaSixNativeFaceFactor (face : DeningerGammaSixNativeFace) (ε : ℝ) : ℂ :=
  match face with
  | .compression => Complex.ofReal ((6 : ℝ) ^ ε)
  | .projection => 1
  | .commutator => Complex.ofReal ((6 : ℝ) ^ ε - 1)

theorem deningerGammaSixNativeFaceFactor_ne_zero
    (face : DeningerGammaSixNativeFace) {ε : ℝ} (hε : 0 < ε) :
    deningerGammaSixNativeFaceFactor face ε ≠ 0 := by
  cases face with
  | compression => exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne'
  | projection => exact one_ne_zero
  | commutator => exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr
      (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 6) hε)).ne'

theorem deningerGammaSixNativeFaceOperator_abel_factor
    (face : DeningerGammaSixNativeFace) {ε : ℝ}
    (T : deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2)) :
    deningerOrdinaryIntegerAbelReader ε (deningerGammaSixNativeFaceOperator face T.val) =
      deningerGammaSixNativeFaceFactor face ε *
        deningerOrdinaryIntegerAbelReader ε (T.val * deningerOrdinaryIntegerDivisibilityProjection 6) := by
  cases face with
  | compression => exact deningerOrdinaryIntegerAbelReader_compression_exchange T 6
  | projection => simp only [deningerGammaSixNativeFaceOperator, deningerGammaSixNativeFaceFactor, one_mul]
  | commutator =>
    change deningerOrdinaryIntegerAbelReader ε (_ - _) = _
    rw [deningerOrdinaryIntegerAbelReader_sub
      ⟨_, deningerOrdinaryIntegerGibbsDomain_compression T 6⟩
      ⟨_, deningerOrdinaryIntegerGibbsDomain_rightProjection T 6⟩]
    exact deningerOrdinaryIntegerAbelDefect_eq T 6

/-- All three adjacent trace quotients equal the actual adjacent defect quotient. -/
theorem deningerGammaSixNativeFaceOperator_abel_quotient_eq
    (face : DeningerGammaSixNativeFace) {ε : ℝ} (hε : 0 < ε)
    (T U : deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2)) :
    deningerOrdinaryIntegerAbelReader ε (deningerGammaSixNativeFaceOperator face U.val) /
      deningerOrdinaryIntegerAbelReader ε (deningerGammaSixNativeFaceOperator face T.val) =
        deningerGammaSixAdjacentDefectQuotient ε T.val U.val := by
  rw [deningerGammaSixNativeFaceOperator_abel_factor face U,
    deningerGammaSixNativeFaceOperator_abel_factor face T,
    mul_div_mul_left _ _ (deningerGammaSixNativeFaceFactor_ne_zero face hε)]
  unfold deningerGammaSixAdjacentDefectQuotient
  rw [deningerOrdinaryIntegerAbelDefect_eq U 6, deningerOrdinaryIntegerAbelDefect_eq T 6]
  exact (mul_div_mul_left _ _ (deningerGammaSixNativeFaceFactor_ne_zero .commutator hε)).symm

def deningerGammaSixNativeAdjacentReadout (face : DeningerGammaSixNativeFace)
    (ε : ℝ) (T U : DeningerOrdinaryIntegerEnd) : ℝ :=
  deningerGammaSixPhysicalDecoder
    (deningerOrdinaryIntegerAbelReader ε (deningerGammaSixNativeFaceOperator face U) /
      deningerOrdinaryIntegerAbelReader ε (deningerGammaSixNativeFaceOperator face T))

theorem eventually_deningerGammaSixIntegralTailOperator_gibbsDomain
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re) :
    ∀ᶠ M : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      deningerGammaSixIntegralTailOperator k l M w ∈
        deningerOrdinaryIntegerGibbsDomain ((1 + ε) / 2) := by
  filter_upwards [eventually_deningerGammaSixSourceDepth_admitted hrw hrw] with M hM
  intro ε hε
  exact deningerOrdinaryIntegerSummableDiagonal_mem_gibbsDomain (by linarith) _
    (deningerGammaSixIntegralTailOperator_summable_of_admitted k l M hw hrw
      (fun m hm => (hM.2 m hm).1))

/-- Source admission is uniform in the positive regulator and in the three native faces. -/
theorem eventually_deningerGammaSixNativeAdjacentReadout_eq
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re) :
    ∀ᶠ M : ℕ in atTop, ∀ (face : DeningerGammaSixNativeFace) (ε : ℝ), 0 < ε →
      deningerGammaSixNativeAdjacentReadout face ε
        (deningerGammaSixIntegralTailOperator k l M w)
        (deningerGammaSixIntegralTailOperator k l (M+1) w) =
      deningerGammaSixPhysicalDecoder (deningerGammaSixAdjacentDefectQuotient ε
        (deningerGammaSixIntegralTailOperator k l M w)
        (deningerGammaSixIntegralTailOperator k l (M+1) w)) := by
  have h := eventually_deningerGammaSixIntegralTailOperator_gibbsDomain k l hw hrw
  filter_upwards [h, (tendsto_add_atTop_nat 1).eventually h] with M hM hS
  intro face ε hε
  unfold deningerGammaSixNativeAdjacentReadout
  rw [deningerGammaSixNativeFaceOperator_abel_quotient_eq face hε ⟨_, hM ε hε⟩ ⟨_, hS ε hε⟩]

/-- The native products and their actual commutator all recover the same original physical value. -/
theorem tendsto_deningerGammaSixNativeAdjacentReadout_physicalBV
    (face : DeningerGammaSixNativeFace) (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixNativeAdjacentReadout face (ε M)
      (deningerGammaSixIntegralTailOperator k l M w)
      (deningerGammaSixIntegralTailOperator k l (M+1) w)) atTop
      (𝓝 (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (mobiusThetaCenteredParameter w))) := by
  apply (tendsto_deningerGammaSixAdjacentDefect_physicalBV k l hw hrw hc ε hε hpos).congr'
  filter_upwards [eventually_deningerGammaSixNativeAdjacentReadout_eq k l hw hrw, hpos] with M hM hp
  exact (hM face (ε M) hp).symm

/-- The complete original multiplicity-top source, without selecting or moving its Xi divisor. -/
def deningerGammaSixXiNativeReadout (face : DeningerGammaSixNativeFace)
    (rho : XiDivisorSupport) (ε : ℝ) (M : ℕ) : ℝ :=
  deningerGammaSixNativeAdjacentReadout face ε
    (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) M
      (xiSpectralPointSupport rho))
    (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) (M+1)
      (xiSpectralPointSupport rho))

theorem eventually_deningerGammaSixXiNativeReadout_eq
    (rho : XiDivisorSupport) :
    ∀ᶠ M : ℕ in atTop, ∀ (face : DeningerGammaSixNativeFace) (ε : ℝ), 0 < ε →
      deningerGammaSixXiNativeReadout face rho ε M =
        deningerGammaSixXiAdjacentPhysicalReadout rho ε M := by
  have hrw : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  exact eventually_deningerGammaSixNativeAdjacentReadout_eq _ _
    (abs_im_xiSpectralPointSupport_lt_one rho) hrw

/-- Cyclic swap invariance holds exactly at every sufficiently admitted original cutoff. -/
theorem eventually_deningerGammaSixXiNativeReadout_cyclic
    (rho : XiDivisorSupport) :
    ∀ᶠ M : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      deningerGammaSixXiNativeReadout .compression rho ε M =
        deningerGammaSixXiNativeReadout .projection rho ε M := by
  filter_upwards [eventually_deningerGammaSixXiNativeReadout_eq rho] with M hM
  intro ε hε
  rw [hM .compression ε hε, hM .projection ε hε]

/-- A native commutator recovers the fixed physical value, just as either product does. -/
theorem tendsto_deningerGammaSixXiNativeReadout
    (face : DeningerGammaSixNativeFace) (rho : XiDivisorSupport)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixXiNativeReadout face rho (ε M) M) atTop
      (𝓝 (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (rho : ℂ))) := by
  apply (tendsto_deningerGammaSixXiAdjacentPhysicalReadout rho ε hε hpos).congr'
  filter_upwards [eventually_deningerGammaSixXiNativeReadout_eq rho, hpos] with M hM hp
  exact (hM face (ε M) hp).symm

/-- The two original reflected sources retain the actual conormal, with independent native faces. -/
theorem tendsto_deningerGammaSixXiNativeReadout_reflected
    (face reflectedFace : DeningerGammaSixNativeFace) (rho : XiDivisorSupport)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => (6 : ℝ) *
      (deningerGammaSixXiNativeReadout face rho (ε M) M -
        deningerGammaSixXiNativeReadout reflectedFace (xiZeroLineConjEquiv rho) (ε M) M)) atTop
      (𝓝 (deningerBurnolActualConormalRadialReflectionDefect 6 rho)) := by
  have h := ((tendsto_deningerGammaSixXiNativeReadout face rho ε hε hpos).sub
    (tendsto_deningerGammaSixXiNativeReadout reflectedFace (xiZeroLineConjEquiv rho) ε hε hpos)).const_mul 6
  rw [deningerBurnolActualConormalRadialReflectionDefect_eq_bvGreenStokes (by omega : 2 ≤ 6)]
  simpa only [xiZeroLineConjEquiv_apply, starRingEnd_apply, Nat.cast_ofNat] using h

/-- Subtraction after decoding loses exactly the retained commutator readout. -/
theorem eventually_deningerGammaSixXiNativeReadout_subtraction_discrepancy
    (rho : XiDivisorSupport) :
    ∀ᶠ M : ℕ in atTop, ∀ ε : ℝ, 0 < ε →
      deningerGammaSixXiNativeReadout .commutator rho ε M -
        (deningerGammaSixXiNativeReadout .compression rho ε M -
          deningerGammaSixXiNativeReadout .projection rho ε M) =
        deningerGammaSixXiAdjacentPhysicalReadout rho ε M := by
  filter_upwards [eventually_deningerGammaSixXiNativeReadout_eq rho] with M hM
  intro ε hε
  rw [hM .commutator ε hε, hM .compression ε hε, hM .projection ε hε, sub_self, sub_zero]

/-- The nonlinear subtraction discrepancy tends to the original physical boundary. -/
theorem tendsto_deningerGammaSixXiNativeReadout_subtraction_discrepancy
    (rho : XiDivisorSupport) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixXiNativeReadout .commutator rho (ε M) M -
      (deningerGammaSixXiNativeReadout .compression rho (ε M) M -
        deningerGammaSixXiNativeReadout .projection rho (ε M) M)) atTop
      (𝓝 (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (rho : ℂ))) := by
  apply (tendsto_deningerGammaSixXiAdjacentPhysicalReadout rho ε hε hpos).congr'
  filter_upwards [eventually_deningerGammaSixXiNativeReadout_subtraction_discrepancy rho, hpos]
    with M hM hp
  exact (hM (ε M) hp).symm

/-- Native commutatorhood and nonlinear cyclic invariance do not discharge this remaining condition. -/
theorem tendsto_deningerGammaSixXiNativeReadout_zero_iff
    (face : DeningerGammaSixNativeFace) (rho : XiDivisorSupport)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixXiNativeReadout face rho (ε M) M) atTop (𝓝 0) ↔
      (rho : ℂ).re = 1 / 2 := by
  have hp := tendsto_deningerGammaSixXiNativeReadout face rho ε hε hpos
  have hz := deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_eq_zero_iff (by omega : 2 ≤ 6)
    (rho : ℂ)
  constructor
  · intro h
    exact hz.mp (tendsto_nhds_unique hp h)
  · intro h
    rw [hz.mpr h] at hp
    exact hp

theorem deningerGammaSixNativeFaceOperator_abel_congr_diagonal
    (face : DeningerGammaSixNativeFace) (T S : DeningerOrdinaryIntegerEnd)
    (h : ∀ a : PNat, deningerOrdinaryIntegerDiagonalCoefficient a T =
      deningerOrdinaryIntegerDiagonalCoefficient a S) (ε : ℝ) :
    deningerOrdinaryIntegerAbelReader ε (deningerGammaSixNativeFaceOperator face T) =
      deningerOrdinaryIntegerAbelReader ε (deningerGammaSixNativeFaceOperator face S) := by
  cases face <;>
    simp only [deningerGammaSixNativeFaceOperator, deningerOrdinaryIntegerAbelReader,
      deningerOrdinaryIntegerGibbsDiagonal_abel, map_sub,
      deningerOrdinaryIntegerDiagonalCoefficient_compression,
      deningerOrdinaryIntegerDiagonalCoefficient_rightProjection, h]

/-- Finite diagonal repairs disappear from all three actual trace quotients before taking limits. -/
theorem eventually_deningerGammaSixNativeAdjacentReadout_finite_tail_repair
    (T F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    ∀ᶠ M : ℕ in atTop, ∀ (face : DeningerGammaSixNativeFace) (ε : ℝ),
      deningerGammaSixNativeAdjacentReadout face ε
        (deningerOrdinaryIntegerTailProjection (6 ^ M) * (T + F))
        (deningerOrdinaryIntegerTailProjection (6 ^ (M+1)) * (T + F)) =
      deningerGammaSixNativeAdjacentReadout face ε
        (deningerOrdinaryIntegerTailProjection (6 ^ M) * T)
        (deningerOrdinaryIntegerTailProjection (6 ^ (M+1)) * T) := by
  have h := eventually_deningerOrdinaryInteger_finite_tail_diagonal_zero F hF
  have he : ∀ᶠ M : ℕ in atTop, ∀ a : PNat,
      deningerOrdinaryIntegerDiagonalCoefficient a
        (deningerOrdinaryIntegerTailProjection (6 ^ M) * (T + F)) =
      deningerOrdinaryIntegerDiagonalCoefficient a
        (deningerOrdinaryIntegerTailProjection (6 ^ M) * T) := by
    filter_upwards [h] with M hM
    intro a
    rw [mul_add, map_add, hM, add_zero]
  filter_upwards [he, (tendsto_add_atTop_nat 1).eventually he] with M hM hS
  intro face ε
  unfold deningerGammaSixNativeAdjacentReadout
  rw [deningerGammaSixNativeFaceOperator_abel_congr_diagonal face _ _ hM ε,
    deningerGammaSixNativeFaceOperator_abel_congr_diagonal face _ _ hS ε]

theorem tendsto_deningerGammaSixNativeAdjacentReadout_finite_repair_physicalBV
    (face : DeningerGammaSixNativeFace) (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => deningerGammaSixNativeAdjacentReadout face (ε M)
      (deningerOrdinaryIntegerTailProjection (6 ^ M) *
        ((deningerGammaSixIntegralOperator k l w w + F) -
          (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen))
      (deningerOrdinaryIntegerTailProjection (6 ^ (M+1)) *
        ((deningerGammaSixIntegralOperator k l w w + F) -
          (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen))) atTop
      (𝓝 (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation 6 (mobiusThetaCenteredParameter w))) := by
  have he := eventually_deningerGammaSixNativeAdjacentReadout_finite_tail_repair
    (deningerGammaSixIntegralOperator k l w w -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) F hF
  apply (tendsto_deningerGammaSixNativeAdjacentReadout_physicalBV face k l hw hrw hc ε hε hpos).congr'
  filter_upwards [he] with M hM
  rw [show (deningerGammaSixIntegralOperator k l w w + F) -
    (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen =
      (deningerGammaSixIntegralOperator k l w w -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) + F by abel,
    hM]
  rfl

end
end RHTower
