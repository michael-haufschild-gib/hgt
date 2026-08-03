import GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential
import GaloisForLFunctions.RHTower.MobiusThetaInternalJetCofinalComplexLanding

/-!
# Resolved BV--Wold source-frame annihilation on the actual Xi landing

The alternating BV--Wold coefficient is genuinely non-coboundary before
source normalization.  It is nevertheless the off-diagonal entry of a
canonical determinant-one triangular source frame.  The diagonal entries
retain the endpoint Wold--Gamma clocks, and their mixed contribution makes
the resolved transport flat.

This file constructs that source frame, its inverse, and the corresponding
resolved covariant differential.  It then lands the first nonzero Xi
conormal through the existing cofinal physical Möbius--theta source and
proves `D1 D0 = 0` on that nonzero actual landing without RH.

The result does not prove flatness of the earlier scalar transport
`exp ((2 Re rho - 1) theta)`.  The final theorems make the distinction exact:
the resolved differential always squares to zero, while its unnormalized
scalar reporter squares to zero on the same nonzero conormal exactly on the
critical line.  Thus dropping the diagonal clock ratios is the scalar
descent obstruction, not an arithmetic annihilation theorem.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Source normalization -/

/-- Every prime/depth Wold--Gamma clock is strictly positive. -/
theorem xiGammaEulerPrimitivePrimeDepthLogClock_pos
    (i : PrimeDepthBVWoldCell) :
    0 < xiGammaEulerPrimitivePrimeDepthLogClock i := by
  rcases i with ⟨p, e⟩
  rw [xiGammaEulerPrimitivePrimeDepthLogClock_apply]
  exact mul_pos (by positivity)
    (Real.log_pos (by exact_mod_cast p.2.one_lt))

theorem xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero
    (i : PrimeDepthBVWoldCell) :
    xiGammaEulerPrimitivePrimeDepthLogClock i ≠ 0 :=
  ne_of_gt (xiGammaEulerPrimitivePrimeDepthLogClock_pos i)

/-- Vertex potential forced by source-frame normalization. -/
def primeDepthBVWoldNormalizedPotential
    (i : PrimeDepthBVWoldCell) : ℝ :=
  primeDepthBVFirstTraceDepthWeight i /
    xiGammaEulerPrimitivePrimeDepthLogClock i

/-- Source-normalized version of the alternating coefficient. -/
def primeDepthBVWoldNormalizedConnection
    (i j : PrimeDepthBVWoldCell) : ℝ :=
  primeDepthBVWoldConnection i j /
    (xiGammaEulerPrimitivePrimeDepthLogClock i *
      xiGammaEulerPrimitivePrimeDepthLogClock j)

/-- **Normalization law.**  Retaining both endpoint clock factors turns the
alternating BV--Wold coefficient into a vertex coboundary. -/
theorem primeDepthBVWoldNormalizedConnection_eq_potential_sub
    (i j : PrimeDepthBVWoldCell) :
    primeDepthBVWoldNormalizedConnection i j =
      primeDepthBVWoldNormalizedPotential i -
        primeDepthBVWoldNormalizedPotential j := by
  rw [primeDepthBVWoldNormalizedConnection,
    primeDepthBVWoldConnection,
    primeDepthBVWoldNormalizedPotential,
    primeDepthBVWoldNormalizedPotential]
  field_simp [xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero]

/-- Weighted cocycle identity which supplies the mixed cancellation in the
resolved source frame. -/
theorem primeDepthBVWoldConnection_weighted_cocycle
    (i j k : PrimeDepthBVWoldCell) :
    xiGammaEulerPrimitivePrimeDepthLogClock i *
          primeDepthBVWoldConnection j k +
        xiGammaEulerPrimitivePrimeDepthLogClock k *
          primeDepthBVWoldConnection i j =
      xiGammaEulerPrimitivePrimeDepthLogClock j *
        primeDepthBVWoldConnection i k := by
  rw [primeDepthBVWoldConnection, primeDepthBVWoldConnection,
    primeDepthBVWoldConnection]
  ring

/-! ## Determinant-one triangular source frames -/

/-- Triangular frame carrying the regular clock on its diagonal and the
singular BV mass in its off-diagonal entry. -/
def primeDepthBVWoldResolvedSourceFrame
    (a : ℝ) (i : PrimeDepthBVWoldCell) :
    (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun z :=
    ((((1 / xiGammaEulerPrimitivePrimeDepthLogClock i : ℝ) : ℂ) * z.1 +
      ((a * primeDepthBVFirstTraceDepthWeight i : ℝ) : ℂ) * z.2),
      (xiGammaEulerPrimitivePrimeDepthLogClock i : ℂ) * z.2)
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' c x := by
    ext <;> simp <;> ring

/-- Explicit inverse of the triangular source frame. -/
def primeDepthBVWoldResolvedSourceFrameInv
    (a : ℝ) (i : PrimeDepthBVWoldCell) :
    (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun z :=
    (((xiGammaEulerPrimitivePrimeDepthLogClock i : ℂ) * z.1 -
      ((a * primeDepthBVFirstTraceDepthWeight i : ℝ) : ℂ) * z.2),
      (((1 / xiGammaEulerPrimitivePrimeDepthLogClock i : ℝ) : ℂ) * z.2))
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' c x := by
    ext <;> simp <;> ring

theorem primeDepthBVWoldResolvedSourceFrameInv_frame
    (a : ℝ) (i : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldResolvedSourceFrameInv a i
        (primeDepthBVWoldResolvedSourceFrame a i z) = z := by
  have hi := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero i
  ext <;> simp only [primeDepthBVWoldResolvedSourceFrame,
    primeDepthBVWoldResolvedSourceFrameInv, LinearMap.coe_mk,
    AddHom.coe_mk]
  · push_cast
    field_simp [hi]
    ring
  · push_cast
    field_simp [hi]

theorem primeDepthBVWoldResolvedSourceFrame_frameInv
    (a : ℝ) (i : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldResolvedSourceFrame a i
        (primeDepthBVWoldResolvedSourceFrameInv a i z) = z := by
  have hi := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero i
  ext <;> simp only [primeDepthBVWoldResolvedSourceFrame,
    primeDepthBVWoldResolvedSourceFrameInv, LinearMap.coe_mk,
    AddHom.coe_mk]
  · push_cast
    field_simp [hi]
    ring
  · push_cast
    field_simp [hi]

/-- Resolved transition between two literal source frames.  Its
off-diagonal entry is exactly the unnormalized BV--Wold connection. -/
def primeDepthBVWoldResolvedTransport
    (a : ℝ) (i j : PrimeDepthBVWoldCell) :
    (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun z :=
    ((((xiGammaEulerPrimitivePrimeDepthLogClock i /
          xiGammaEulerPrimitivePrimeDepthLogClock j : ℝ) : ℂ) * z.1 -
        ((a * primeDepthBVWoldConnection i j : ℝ) : ℂ) * z.2),
      (((xiGammaEulerPrimitivePrimeDepthLogClock j /
          xiGammaEulerPrimitivePrimeDepthLogClock i : ℝ) : ℂ) * z.2))
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' c x := by
    ext <;> simp <;> ring

/-- The displayed transition is literally `G_i⁻¹ G_j`; no connection
coefficient was inserted after scalarization. -/
theorem primeDepthBVWoldResolvedTransport_eq_frameTransition
    (a : ℝ) (i j : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldResolvedTransport a i j z =
      primeDepthBVWoldResolvedSourceFrameInv a i
        (primeDepthBVWoldResolvedSourceFrame a j z) := by
  have hi := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero i
  have hj := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero j
  ext <;> simp only [primeDepthBVWoldResolvedTransport,
    primeDepthBVWoldResolvedSourceFrame,
    primeDepthBVWoldResolvedSourceFrameInv, LinearMap.coe_mk,
    AddHom.coe_mk]
  · push_cast
    rw [primeDepthBVWoldConnection]
    push_cast
    field_simp [hi, hj]
    ring
  · push_cast
    field_simp [hi, hj]

/-- **Resolved source flatness.**  The two diagonal clock characters supply
the exact mixed term needed to compose the nonseparable off-diagonal
coefficient. -/
theorem primeDepthBVWoldResolvedTransport_comp
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) (z : ℂ × ℂ) :
    primeDepthBVWoldResolvedTransport a i j
        (primeDepthBVWoldResolvedTransport a j k z) =
      primeDepthBVWoldResolvedTransport a i k z := by
  have hi := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero i
  have hj := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero j
  have hk := xiGammaEulerPrimitivePrimeDepthLogClock_ne_zero k
  have hw := primeDepthBVWoldConnection_weighted_cocycle i j k
  have hdiag :
      xiGammaEulerPrimitivePrimeDepthLogClock i /
          xiGammaEulerPrimitivePrimeDepthLogClock j *
        (xiGammaEulerPrimitivePrimeDepthLogClock j /
          xiGammaEulerPrimitivePrimeDepthLogClock k) =
      xiGammaEulerPrimitivePrimeDepthLogClock i /
        xiGammaEulerPrimitivePrimeDepthLogClock k := by
    field_simp [hi, hj, hk]
  have hdiag' :
      xiGammaEulerPrimitivePrimeDepthLogClock j /
          xiGammaEulerPrimitivePrimeDepthLogClock i *
        (xiGammaEulerPrimitivePrimeDepthLogClock k /
          xiGammaEulerPrimitivePrimeDepthLogClock j) =
      xiGammaEulerPrimitivePrimeDepthLogClock k /
        xiGammaEulerPrimitivePrimeDepthLogClock i := by
    field_simp [hi, hj, hk]
  have hoff :
      xiGammaEulerPrimitivePrimeDepthLogClock i /
            xiGammaEulerPrimitivePrimeDepthLogClock j *
          primeDepthBVWoldConnection j k +
        primeDepthBVWoldConnection i j *
          (xiGammaEulerPrimitivePrimeDepthLogClock k /
            xiGammaEulerPrimitivePrimeDepthLogClock j) =
      primeDepthBVWoldConnection i k := by
    field_simp [hj]
    linear_combination hw
  have hdiagc := congrArg (fun x : ℝ => (x : ℂ)) hdiag
  have hdiagc' := congrArg (fun x : ℝ => (x : ℂ)) hdiag'
  have hoffc := congrArg (fun x : ℝ => (x : ℂ)) hoff
  push_cast at hdiagc hdiagc' hoffc
  ext
  · simp only [primeDepthBVWoldResolvedTransport, LinearMap.coe_mk,
      AddHom.coe_mk]
    push_cast
    rw [mul_sub]
    rw [← mul_assoc, hdiagc]
    linear_combination -(a : ℂ) * hoffc * z.2
  · simp only [primeDepthBVWoldResolvedTransport, LinearMap.coe_mk,
      AddHom.coe_mk]
    push_cast
    rw [← mul_assoc, hdiagc']

/-! ## Resolved covariant differential -/

abbrev PrimeDepthBVWoldResolvedZeroCochain :=
  PrimeDepthBVWoldCell → ℂ × ℂ
abbrev PrimeDepthBVWoldResolvedOneCochain :=
  PrimeDepthBVWoldCell → PrimeDepthBVWoldCell → ℂ × ℂ
abbrev PrimeDepthBVWoldResolvedTwoCochain :=
  PrimeDepthBVWoldCell → PrimeDepthBVWoldCell →
    PrimeDepthBVWoldCell → ℂ × ℂ

def primeDepthBVWoldResolvedCovariantD0 (a : ℝ) :
    PrimeDepthBVWoldResolvedZeroCochain →ₗ[ℂ]
      PrimeDepthBVWoldResolvedOneCochain where
  toFun f i j := primeDepthBVWoldResolvedTransport a i j (f j) - f i
  map_add' f g := by
    funext i j
    simp only [Pi.add_apply, map_add]
    module
  map_smul' c f := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]
    module

def primeDepthBVWoldResolvedCovariantD1 (a : ℝ) :
    PrimeDepthBVWoldResolvedOneCochain →ₗ[ℂ]
      PrimeDepthBVWoldResolvedTwoCochain where
  toFun omega i j k :=
    primeDepthBVWoldResolvedTransport a i j (omega j k) -
      omega i k + omega i j
  map_add' omega eta := by
    funext i j k
    simp only [Pi.add_apply, map_add]
    module
  map_smul' c omega := by
    funext i j k
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]
    module

/-- **Unconditional resolved annihilation.**  Source-frame composition,
not a critical-line premise, forces the resolved square to vanish. -/
theorem primeDepthBVWoldResolvedCovariantD1_comp_D0_apply
    (a : ℝ) (f : PrimeDepthBVWoldResolvedZeroCochain)
    (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldResolvedCovariantD1 a
        (primeDepthBVWoldResolvedCovariantD0 a f) i j k = 0 := by
  change
    primeDepthBVWoldResolvedTransport a i j
          (primeDepthBVWoldResolvedTransport a j k (f k) - f j) -
        (primeDepthBVWoldResolvedTransport a i k (f k) - f i) +
      (primeDepthBVWoldResolvedTransport a i j (f j) - f i) = 0
  rw [map_sub, primeDepthBVWoldResolvedTransport_comp]
  module

/-! ## Divisor resolution and actual leading Xi conormal -/

abbrev PrimeDepthBVWoldXiResolvedZeroCochain :=
  XiDivisorSupport → PrimeDepthBVWoldResolvedZeroCochain
abbrev PrimeDepthBVWoldXiResolvedOneCochain :=
  XiDivisorSupport → PrimeDepthBVWoldResolvedOneCochain
abbrev PrimeDepthBVWoldXiResolvedTwoCochain :=
  XiDivisorSupport → PrimeDepthBVWoldResolvedTwoCochain

def primeDepthBVWoldXiResolvedCovariantD0 :
    PrimeDepthBVWoldXiResolvedZeroCochain →ₗ[ℂ]
      PrimeDepthBVWoldXiResolvedOneCochain where
  toFun f rho := primeDepthBVWoldResolvedCovariantD0
    (primeDepthBVWoldXiCenteredRate rho) (f rho)
  map_add' f g := by
    funext rho i j
    simp only [Pi.add_apply, map_add]
  map_smul' c f := by
    funext rho i j
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]

def primeDepthBVWoldXiResolvedCovariantD1 :
    PrimeDepthBVWoldXiResolvedOneCochain →ₗ[ℂ]
      PrimeDepthBVWoldXiResolvedTwoCochain where
  toFun omega rho := primeDepthBVWoldResolvedCovariantD1
    (primeDepthBVWoldXiCenteredRate rho) (omega rho)
  map_add' omega eta := by
    funext rho i j k
    simp only [Pi.add_apply, map_add]
  map_smul' c omega := by
    funext rho i j k
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]

/-- First nonzero Xi conormal, retained as the vertical coordinate of every
resolved prime/depth frame. -/
def primeDepthBVWoldXiResolvedLeadingConormal :
    PrimeDepthBVWoldXiResolvedZeroCochain :=
  fun rho _ =>
    (0, iteratedDeriv (xiSupportMultiplicity rho) XiC
      (xiSpectralPointSupport rho))

/-- The actual leading landing is nonzero on every divisor copy and every
prime/depth frame. -/
theorem primeDepthBVWoldXiResolvedLeadingConormal_ne_zero
    (rho : XiDivisorSupport) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiResolvedLeadingConormal rho i ≠ 0 := by
  intro h
  have hsnd := congrArg Prod.snd h
  simpa [primeDepthBVWoldXiResolvedLeadingConormal] using
    (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho hsnd)

/-- Finite codiagonal of the internally promoted physical Möbius--theta
coface, placed in the same resolved conormal coordinate. -/
def primeDepthBVWoldXiResolvedLeadingConormalApproximation
    (K N : ℕ) : PrimeDepthBVWoldXiResolvedZeroCochain :=
  fun rho _ =>
    (0, ∑ j ∈ Finset.range (N + 1),
      mobiusThetaInternalJetCompleteChannelFourierLaplace
        (xiSupportMultiplicity rho) K j
        (xiSpectralPointSupport rho))

/-- **Actual source landing.**  The resolved leading conormal is the
cofinal limit of target-free physical source cofaces at every retained
prime/depth label. -/
theorem tendsto_primeDepthBVWoldXiResolvedLeadingConormalApproximation
    (K : ℕ) (rho : XiDivisorSupport) (i : PrimeDepthBVWoldCell) :
    Tendsto
      (fun N =>
        primeDepthBVWoldXiResolvedLeadingConormalApproximation K N rho i)
      atTop
      (nhds (primeDepthBVWoldXiResolvedLeadingConormal rho i)) := by
  have h :=
    tendsto_sum_range_mobiusThetaInternalJetCompleteChannelFourierLaplace_at_divisor
      (xiSupportMultiplicity rho) K rho
  exact tendsto_const_nhds.prodMk_nhds h

/-- **Source-derived annihilation on the actual Xi landing.**  This is the
resolved statement: all prime, depth, divisor, and conormal coordinates
remain present. -/
theorem primeDepthBVWoldXiResolvedCovariantD1_comp_D0_leadingConormal
    (rho : XiDivisorSupport) (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiResolvedCovariantD1
        (primeDepthBVWoldXiResolvedCovariantD0
          primeDepthBVWoldXiResolvedLeadingConormal) rho i j k = 0 := by
  exact primeDepthBVWoldResolvedCovariantD1_comp_D0_apply _ _ _ _ _

/-! ## Exact scalar-descent obstruction -/

/-- The same actual nonzero leading conormal after forgetting its resolved
vertical coordinate. -/
def primeDepthBVWoldXiScalarLeadingConormal :
    PrimeDepthBVWoldXiZeroCochain :=
  fun rho _ => iteratedDeriv (xiSupportMultiplicity rho) XiC
    (xiSpectralPointSupport rho)

theorem primeDepthBVWoldXiScalarLeadingConormal_ne_zero
    (rho : XiDivisorSupport) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiScalarLeadingConormal rho i ≠ 0 :=
  iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho

/-- The unnormalized scalar reporter does not inherit resolved nilpotence.
On the same actual nonzero Xi conormal, its witness square vanishes exactly
on the critical line. -/
theorem primeDepthBVWoldXiCovariant_square_scalarLeadingConormal_eq_zero_iff
    (rho : XiDivisorSupport) :
    primeDepthBVWoldXiCovariantD1
        (primeDepthBVWoldXiCovariantD0
          primeDepthBVWoldXiScalarLeadingConormal)
          rho primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [primeDepthBVWoldXiCovariantD1_comp_D0_apply]
  rw [mul_eq_zero]
  simp only [primeDepthBVWoldXiScalarLeadingConormal_ne_zero, or_false,
    Complex.ofReal_sub, sub_eq_zero]
  norm_cast
  exact primeDepthBVWoldXiTransport_witness_flat_iff rho

/-- Global scalar annihilation on the actual leading Xi conormal is still
exactly RH.  This theorem prevents resolved source nilpotence from being
used as a circular scalar descent. -/
def PrimeDepthBVWoldXiScalarLeadingConormalAnnihilated : Prop :=
  ∀ rho : XiDivisorSupport,
    primeDepthBVWoldXiCovariantD1
        (primeDepthBVWoldXiCovariantD0
          primeDepthBVWoldXiScalarLeadingConormal)
          rho primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo = 0

theorem primeDepthBVWoldXiScalarLeadingConormalAnnihilated_iff_riemannHypothesis :
    PrimeDepthBVWoldXiScalarLeadingConormalAnnihilated ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply rh_iff_xi_ne_zero_right.mpr
    intro z hz hzero
    let rho : XiDivisorSupport :=
      ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hline : z.re = 1 / 2 :=
      (primeDepthBVWoldXiCovariant_square_scalarLeadingConormal_eq_zero_iff
        rho).1 (h rho)
    have hzgt : 1 / 2 < z.re := mem_rightHalf.mp hz
    linarith
  · intro hRH rho
    exact
      (primeDepthBVWoldXiCovariant_square_scalarLeadingConormal_eq_zero_iff
        rho).2 (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
