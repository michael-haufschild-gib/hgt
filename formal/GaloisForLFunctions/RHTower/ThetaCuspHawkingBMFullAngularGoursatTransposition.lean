import GaloisForLFunctions.HTGeometry.VolterraRectangleTransposition
import GaloisForLFunctions.HTGeometry.VolterraRectangleNonseparableTransposition
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursat
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGeneralTemporalTransposition

/-!
# Literal full-angular Goursat transposition

This is compact-null transposition for the actual branch-dependent full angular
Riemann kernel.  The forcing retains the full kernel, the native theta kernel,
the original vertex, and the original hyperbolic weight.

Proof-chain role:
`full angular kernel transposition -> literal seed-cap weak realization ->
QNM-cutoff/contact comparison -> HB B2`.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace RHTower.D4BMFullAngularGoursatTransposition

open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMNativeCircle D4BMCausalKernel
open D4BMFullAngularCircle D4BMFullAngularCircleAction D4BMFullAngularGoursat
open D4BMFullAngularReconstruction
open D4BMGeneralTemporalTransposition

noncomputable section
set_option autoImplicit false

private def nullInvariant (y : ℝ) (p : ℝ × ℝ) : ℝ :=
  invariant ((p.1 + p.2) / 2) (y + (p.1 - p.2) / 2) y

private theorem nullInvariant_continuous (y : ℝ) :
    Continuous (nullInvariant y) := by
  unfold nullInvariant invariant
  apply Continuous.div <;> try fun_prop
  intro p
  exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'

private theorem nullInvariant_causal (y u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    1 ≤ nullInvariant y (u, v) := by
  exact invariant_causal ⟨(u + v) / 2, y + (u - v) / 2, y, by
    rw [abs_le]
    constructor <;> linarith⟩

private def closedFullKernel (q : XiZeroCopy) (branch : Bool) (y X k : ℝ)
    (p : ℝ × ℝ) : ℂ :=
  angularMean q branch (Real.arcosh (max 1 (nullInvariant y p))) X k

private def closedNativeKernel (q : XiZeroCopy) (y X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  D4BMNativeCircle.mean q (Real.arcosh (max 1 (nullInvariant y p))) X k

private theorem closedRadius_continuous (y : ℝ) :
    Continuous (fun p : ℝ × ℝ => Real.arcosh (max 1 (nullInvariant y p))) :=
  Real.continuousOn_arcosh.comp_continuous
    (continuous_const.max (nullInvariant_continuous y))
    (fun p => le_max_left 1 (nullInvariant y p))

private theorem closedFullKernel_continuous (q : XiZeroCopy) (branch : Bool) (y X k : ℝ) :
    Continuous (closedFullKernel q branch y X k) :=
  (angularMean_smooth q branch X k).continuous.comp (closedRadius_continuous y)

private theorem closedNativeKernel_continuous (q : XiZeroCopy) (y X k : ℝ) :
    Continuous (closedNativeKernel q y X k) :=
  (D4BMNativeCircle.mean_radial_smooth q X k).continuous.comp (closedRadius_continuous y)

private theorem closedFullKernel_eq_actual (q : XiZeroCopy) (branch : Bool)
    (y u v X k : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    closedFullKernel q branch y X k (u, v) =
      fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k := by
  exact (fullAngularRiemannKernel_null_closed q branch y u v X k hu hv).symm

private theorem closedNativeKernel_eq_actual (q : XiZeroCopy) (y u v X k : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    closedNativeKernel q y X k (u, v) =
      D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2) (y + (u - v) / 2) y X k := by
  exact (nativeRiemannKernel_null_closed q y u v X k hu hv).symm

private def fullForcing (q : XiZeroCopy) (branch : Bool) (y X k : ℝ)
    (p : ℝ × ℝ) : ℂ :=
  parameter q branch *
      (closedFullKernel q branch y X k p + closedNativeKernel q y X k p) /
    (4 * (Real.cosh (y + (p.1 - p.2) / 2) : ℂ) ^ (2 : ℕ))

private theorem fullForcing_continuous (q : XiZeroCopy) (branch : Bool) (y X k : ℝ) :
    Continuous (fullForcing q branch y X k) := by
  apply Continuous.div
  · exact continuous_const.mul
      ((closedFullKernel_continuous q branch y X k).add (closedNativeKernel_continuous q y X k))
  · fun_prop
  · intro p
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'))

private theorem closedFullKernel_goursat (q : XiZeroCopy) (branch : Bool)
    (y u v X k : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    closedFullKernel q branch y X k (u, v) =
      fullAngularField q branch ![X, Real.exp k] +
        ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, fullForcing q branch y X k (a, b) := by
  have hinside : |(y + (u - v) / 2) - y| ≤ (u + v) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  calc
    closedFullKernel q branch y X k (u, v) =
        fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k :=
      closedFullKernel_eq_actual q branch y u v X k hu hv
    _ = fullAngularField q branch ![X, Real.exp k] +
        ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v,
          parameter q branch *
            (fullAngularRiemannKernel q branch ((a + b) / 2) (y + (a - b) / 2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((a + b) / 2) (y + (a - b) / 2) y X k) /
            (4 * (Real.cosh (y + (a - b) / 2) : ℂ) ^ (2 : ℕ)) := by
      simpa only [show (u + v) / 2 + (y + (u - v) / 2) - y = u by ring,
        show (u + v) / 2 - (y + (u - v) / 2) + y = v by ring] using
        (fullAngularRiemannKernel_goursat q branch
          ⟨(u + v) / 2, y + (u - v) / 2, y, hinside⟩ X k)
    _ = fullAngularField q branch ![X, Real.exp k] +
        ∫ a in (0 : ℝ)..u, ∫ b in (0 : ℝ)..v, fullForcing q branch y X k (a, b) := by
      apply congrArg (fun z : ℂ => fullAngularField q branch ![X, Real.exp k] + z)
      apply intervalIntegral.integral_congr
      intro a ha
      apply intervalIntegral.integral_congr
      intro b hb
      have ha0 : 0 ≤ a := (show a ∈ Icc 0 u by simpa [uIcc_of_le hu] using ha).1
      have hb0 : 0 ≤ b := (show b ∈ Icc 0 v by simpa [uIcc_of_le hv] using hb).1
      unfold fullForcing
      change parameter q branch *
          (fullAngularRiemannKernel q branch ((a + b) / 2) (y + (a - b) / 2) y X k +
            D4BMNativeCircle.nativeRiemannKernel q ((a + b) / 2) (y + (a - b) / 2) y X k) /
          (4 * (Real.cosh (y + (a - b) / 2) : ℂ) ^ (2 : ℕ)) =
        parameter q branch *
          (closedFullKernel q branch y X k (a, b) + closedNativeKernel q y X k (a, b)) /
          (4 * (Real.cosh (y + (a - b) / 2) : ℂ) ^ (2 : ℕ))
      rw [closedFullKernel_eq_actual q branch y a b X k ha0 hb0,
        closedNativeKernel_eq_actual q y a b X k ha0 hb0]

/-- Compact-null transposition of the literal branch-dependent full angular
Riemann kernel.  This is an exact weak Goursat identity, not a native-kernel
surrogate: both full and native channels remain on the right. -/
theorem fullAngularRiemannKernel_transposition (q : XiZeroCopy) (branch : Bool)
    (y X k U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (phi phip psi psip : ℝ → ℂ)
    (hp : Continuous phi) (hpd : Continuous phip) (hs : Continuous psi) (hsd : Continuous psip)
    (hphi : ∀ u, HasDerivAt phi (phip u) u)
    (hpsi : ∀ v, HasDerivAt psi (psip v) v) (hpU : phi U = 0) (hsV : psi V = 0) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
      fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k * phip u * psip v) =
      fullAngularField q branch ![X, Real.exp k] * phi 0 * psi 0 +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          parameter q branch *
            (fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2) (y + (u - v) / 2) y X k) /
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) * phi u * psi v := by
  have h := rectangle_volterra_transposition
    (closedFullKernel q branch y X k) (fullForcing q branch y X k)
    (fullAngularField q branch ![X, Real.exp k]) U V hU hV
    (fullForcing_continuous q branch y X k)
    (fun u v hu hv => closedFullKernel_goursat q branch y u v X k hu hv)
    phi phip psi psip hp hpd hs hsd hphi hpsi hpU hsV
  calc
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
      fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k * phip u * psip v) =
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          closedFullKernel q branch y X k (u, v) * phip u * psip v := by
      apply intervalIntegral.integral_congr
      intro u hu
      apply intervalIntegral.integral_congr
      intro v hv
      have hu0 : 0 ≤ u := (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
      have hv0 : 0 ≤ v := (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1
      change fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k *
          phip u * psip v =
        closedFullKernel q branch y X k (u, v) * phip u * psip v
      rw [closedFullKernel_eq_actual q branch y u v X k hu0 hv0]
    _ = fullAngularField q branch ![X, Real.exp k] * phi 0 * psi 0 +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          fullForcing q branch y X k (u, v) * phi u * psi v := h
    _ = fullAngularField q branch ![X, Real.exp k] * phi 0 * psi 0 +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          parameter q branch *
            (fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2) (y + (u - v) / 2) y X k) /
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) * phi u * psi v := by
      apply congrArg (fun z : ℂ => fullAngularField q branch ![X, Real.exp k] * phi 0 * psi 0 + z)
      apply intervalIntegral.integral_congr
      intro u hu
      apply intervalIntegral.integral_congr
      intro v hv
      have hu0 : 0 ≤ u := (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
      have hv0 : 0 ≤ v := (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1
      change fullForcing q branch y X k (u, v) * phi u * psi v =
        parameter q branch *
            (fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2) (y + (u - v) / 2) y X k) /
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) * phi u * psi v
      unfold fullForcing
      rw [closedFullKernel_eq_actual q branch y u v X k hu0 hv0,
        closedNativeKernel_eq_actual q y u v X k hu0 hv0]

/-- Compact-null transposition of the literal full angular kernel against an
arbitrary continuous mixed test.  Unlike the product-test theorem above, this
retains source couplings across both null variables. -/
theorem fullAngularRiemannKernel_continuous_test_transposition (q : XiZeroCopy) (branch : Bool)
    (y X k U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V) (H : ℝ × ℝ → ℂ) (hH : Continuous H) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
      fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k * H (u, v)) =
      fullAngularField q branch ![X, Real.exp k] * backwardRectanglePrimitive H U V (0, 0) +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          parameter q branch *
            (fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2) (y + (u - v) / 2) y X k) /
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) *
              backwardRectanglePrimitive H U V (u, v) := by
  have h := rectangle_volterra_continuous_test_transposition
    (closedFullKernel q branch y X k) (fullForcing q branch y X k)
    (fullAngularField q branch ![X, Real.exp k]) U V hU hV
    (fullForcing_continuous q branch y X k)
    (fun u v hu hv => closedFullKernel_goursat q branch y u v X k hu hv) H hH
  calc
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
      fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k * H (u, v)) =
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          closedFullKernel q branch y X k (u, v) * H (u, v) := by
      apply intervalIntegral.integral_congr
      intro u hu
      apply intervalIntegral.integral_congr
      intro v hv
      have hu0 : 0 ≤ u := (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
      have hv0 : 0 ≤ v := (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1
      change fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k * H (u, v) =
        closedFullKernel q branch y X k (u, v) * H (u, v)
      rw [closedFullKernel_eq_actual q branch y u v X k hu0 hv0]
    _ = fullAngularField q branch ![X, Real.exp k] * backwardRectanglePrimitive H U V (0, 0) +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          fullForcing q branch y X k (u, v) * backwardRectanglePrimitive H U V (u, v) := h
    _ = fullAngularField q branch ![X, Real.exp k] * backwardRectanglePrimitive H U V (0, 0) +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          parameter q branch *
            (fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2) (y + (u - v) / 2) y X k) /
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) *
              backwardRectanglePrimitive H U V (u, v) := by
      apply congrArg (fun z : ℂ =>
        fullAngularField q branch ![X, Real.exp k] * backwardRectanglePrimitive H U V (0, 0) + z)
      apply intervalIntegral.integral_congr
      intro u hu
      apply intervalIntegral.integral_congr
      intro v hv
      have hu0 : 0 ≤ u := (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
      have hv0 : 0 ≤ v := (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1
      unfold fullForcing
      change parameter q branch *
          (closedFullKernel q branch y X k (u, v) + closedNativeKernel q y X k (u, v)) /
          (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) *
            backwardRectanglePrimitive H U V (u, v) =
        parameter q branch *
            (fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2) (y + (u - v) / 2) y X k) /
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) *
              backwardRectanglePrimitive H U V (u, v)
      rw [closedFullKernel_eq_actual q branch y u v X k hu0 hv0,
        closedNativeKernel_eq_actual q y u v X k hu0 hv0]

/-- The literal full-angular null kernel satisfies the mixed-derivative Green
identity for an arbitrary nonseparable test with outgoing-face zero data.
The source vertex is the full branch field; the bulk retains its native-channel
coupling. This is the finite kernel-level contact law, before any source-event
integration or noncompact current limit. -/
theorem fullAngularRiemannKernel_mixed_green (q : XiZeroCopy) (branch : Bool)
    (y X k U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (H W Wv : ℝ × ℝ → ℂ)
    (hH : Continuous H) (hW : Continuous W) (hWv : Continuous Wv)
    (hWv_u : ∀ u v, HasDerivAt (fun a => Wv (a, v)) (H (u, v)) u)
    (hW_v : ∀ u v, HasDerivAt (fun b => W (u, b)) (Wv (u, v)) v)
    (hWvU : ∀ v, Wv (U, v) = 0) (hWV : ∀ u, W (u, V) = 0) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
      fullAngularRiemannKernel q branch ((u + v) / 2)
        (y + (u - v) / 2) y X k * H (u, v)) =
      fullAngularField q branch ![X, Real.exp k] * W (0, 0) +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          parameter q branch *
            (fullAngularRiemannKernel q branch ((u + v) / 2)
              (y + (u - v) / 2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2)
                (y + (u - v) / 2) y X k) /
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) * W (u, v) := by
  have h := rectangle_volterra_nonseparable_transposition
    (closedFullKernel q branch y X k) (fullForcing q branch y X k)
    (fullAngularField q branch ![X, Real.exp k]) U V hU hV
    (fullForcing_continuous q branch y X k)
    (fun u v hu hv => closedFullKernel_goursat q branch y u v X k hu hv)
    H W Wv hH hW hWv hWv_u hW_v hWvU hWV
  calc
    _ = ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          closedFullKernel q branch y X k (u, v) * H (u, v) := by
      apply intervalIntegral.integral_congr
      intro u hu
      apply intervalIntegral.integral_congr
      intro v hv
      have hu0 : 0 ≤ u := (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
      have hv0 : 0 ≤ v := (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1
      change fullAngularRiemannKernel q branch ((u + v) / 2)
          (y + (u - v) / 2) y X k * H (u, v) =
        closedFullKernel q branch y X k (u, v) * H (u, v)
      rw [closedFullKernel_eq_actual q branch y u v X k hu0 hv0]
    _ = fullAngularField q branch ![X, Real.exp k] * W (0, 0) +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          fullForcing q branch y X k (u, v) * W (u, v) := h
    _ = _ := by
      apply congrArg (fun z : ℂ => fullAngularField q branch ![X, Real.exp k] * W (0, 0) + z)
      apply intervalIntegral.integral_congr
      intro u hu
      apply intervalIntegral.integral_congr
      intro v hv
      have hu0 : 0 ≤ u := (show u ∈ Icc 0 U by simpa [uIcc_of_le hU] using hu).1
      have hv0 : 0 ≤ v := (show v ∈ Icc 0 V by simpa [uIcc_of_le hV] using hv).1
      unfold fullForcing
      change parameter q branch *
          (closedFullKernel q branch y X k (u, v) + closedNativeKernel q y X k (u, v)) /
          (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) * W (u, v) =
        parameter q branch *
          (fullAngularRiemannKernel q branch ((u + v) / 2) (y + (u - v) / 2) y X k +
            D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2)
              (y + (u - v) / 2) y X k) /
          (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) * W (u, v)
      rw [closedFullKernel_eq_actual q branch y u v X k hu0 hv0,
        closedNativeKernel_eq_actual q y u v X k hu0 hv0]

private theorem physicalEventDir_smooth {phi : ℝ × ℝ → ℂ}
    (hp : ContDiff ℝ ∞ phi) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (eventDir v phi) :=
  _root_.RHTower.D4BMGeneralTemporalTransposition.eventDir_smooth hp v

private theorem physicalEventWave_smooth {phi : ℝ × ℝ → ℂ}
    (hp : ContDiff ℝ ∞ phi) : ContDiff ℝ ∞ (eventWave phi) :=
  (physicalEventDir_smooth (physicalEventDir_smooth hp (1,0)) (1,0)).sub
    (physicalEventDir_smooth (physicalEventDir_smooth hp (0,1)) (0,1))

private theorem physicalEventDir_second {phi : ℝ × ℝ → ℂ}
    (hp : ContDiff ℝ ∞ phi) (v w p : ℝ × ℝ) :
    eventDir v (eventDir w phi) p = fderiv ℝ (fderiv ℝ phi) p v w :=
  _root_.RHTower.D4BMGeneralTemporalTransposition.eventDir_second hp v w p

private theorem physicalPast_u (s y u v : ℝ) :
    HasDerivAt (fun a => pastVertex s y (a,v)) (-1/2,1/2) u :=
  _root_.RHTower.D4BMGeneralTemporalTransposition.pastVertex_u s y u v

private theorem physicalPast_v (s y u v : ℝ) :
    HasDerivAt (fun b => pastVertex s y (u,b)) (-1/2,-1/2) v :=
  _root_.RHTower.D4BMGeneralTemporalTransposition.pastVertex_v s y u v

private theorem physicalPast_mixed_wave {phi : ℝ × ℝ → ℂ}
    (hp : ContDiff ℝ ∞ phi) (p : ℝ × ℝ) :
    eventDir (-1/2,1/2) (eventDir (-1/2,-1/2) phi) p =
      eventWave phi p/4 := by
  rw [physicalEventDir_second hp]
  unfold eventWave
  rw [physicalEventDir_second hp,physicalEventDir_second hp]
  have hs := (hp.contDiffAt (x := p)).isSymmSndFDerivAt
    (by norm_num; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) (1,0) (0,1)
  have hv : ((-1/2,1/2) : ℝ × ℝ) = (-1/2:ℝ) • (1,0)+(1/2:ℝ) • (0,1) := by
    ext <;> norm_num
  have hw : ((-1/2,-1/2) : ℝ × ℝ) = (-1/2:ℝ) • (1,0)+(-1/2:ℝ) • (0,1) := by
    ext <;> norm_num
  rw [hv,hw]
  simp only [map_add,map_smul,add_apply,smul_apply,
    Complex.real_smul,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,
    Complex.ofReal_ofNat]
  rw [hs]
  ring

/-- Full angular kernel contact for a smooth, nonseparable physical target test
on any null rectangle whose two outgoing faces miss the test and its normal jet.
The temporal wave has its actual source vertex and its full-plus-native bulk
angular action; no scalar square-contact substitution is made. -/
theorem fullAngularRiemannKernel_physical_null_green (q : XiZeroCopy) (branch : Bool)
    (s y X k U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (phi : ℝ × ℝ → ℂ) (hp : ContDiff ℝ ∞ phi)
    (hfaceU : ∀ v, eventDir (-1/2,-1/2) phi (pastVertex s y (U,v)) = 0)
    (hfaceV : ∀ u, phi (pastVertex s y (u,V)) = 0) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
      fullAngularRiemannKernel q branch ((u + v) / 2)
        (y + (u - v) / 2) y X k *
          (eventWave phi (pastVertex s y (u,v))/4)) =
      fullAngularField q branch ![X, Real.exp k] * phi (s,y) +
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V,
          parameter q branch *
            (fullAngularRiemannKernel q branch ((u + v) / 2)
              (y + (u - v) / 2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2)
                (y + (u - v) / 2) y X k) /
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) *
              phi (pastVertex s y (u,v)) := by
  let W : ℝ × ℝ → ℂ := fun p => phi (pastVertex s y p)
  let Wv : ℝ × ℝ → ℂ := fun p => eventDir (-1/2,-1/2) phi (pastVertex s y p)
  let H : ℝ × ℝ → ℂ := fun p => eventWave phi (pastVertex s y p)/4
  have hmap : Continuous (pastVertex s y) := by unfold pastVertex; fun_prop
  have hW : Continuous W := hp.continuous.comp hmap
  have hWv : Continuous Wv := (physicalEventDir_smooth hp _).continuous.comp hmap
  have hH : Continuous H := ((physicalEventWave_smooth hp).continuous.comp hmap).div_const 4
  have hW_v (u v : ℝ) : HasDerivAt (fun b => W (u,b)) (Wv (u,v)) v :=
    ((hp.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt v
      (physicalPast_v s y u v))
  have hWv_u (u v : ℝ) : HasDerivAt (fun a => Wv (a,v)) (H (u,v)) u := by
    have h := (((physicalEventDir_smooth hp (-1/2,-1/2)).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt
      u (physicalPast_u s y u v))
    change HasDerivAt _ (eventDir (-1/2,1/2) (eventDir (-1/2,-1/2) phi) _) u at h
    rw [physicalPast_mixed_wave hp] at h
    exact h
  have h := fullAngularRiemannKernel_mixed_green q branch y X k U V hU hV
    H W Wv hH hW hWv hWv_u hW_v hfaceU hfaceV
  simpa only [H,W,Wv,pastVertex,zero_add,add_zero,zero_div,sub_zero] using h

private def physicalPastChart (s y : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := pastVertex s y
  invFun := fun p => (s-p.1+p.2-y,s-p.1-p.2+y)
  left_inv p := by ext <;> simp only [pastVertex] <;> ring
  right_inv p := by ext <;> simp only [pastVertex] <;> ring
  continuous_toFun := by unfold pastVertex; fun_prop
  continuous_invFun := by fun_prop

/-- Every smooth compact physical target test admits a finite null square on
which the literal full-angular kernel has its exact branch-field source
vertex and coupled full/native bulk action. No truncation premise is left for
the test: a sufficiently large square is constructed from its actual support. -/
theorem fullAngularRiemannKernel_compact_physical_null_green (q : XiZeroCopy)
    (branch : Bool) (s y X k : ℝ) (phi : ℝ × ℝ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∫ u in (0 : ℝ)..R, ∫ v in (0 : ℝ)..R,
        fullAngularRiemannKernel q branch ((u + v) / 2)
          (y + (u - v) / 2) y X k *
            (eventWave phi (pastVertex s y (u,v))/4)) =
        fullAngularField q branch ![X, Real.exp k] * phi (s,y) +
          ∫ u in (0 : ℝ)..R, ∫ v in (0 : ℝ)..R,
            parameter q branch *
              (fullAngularRiemannKernel q branch ((u + v) / 2)
                (y + (u - v) / 2) y X k +
                D4BMNativeCircle.nativeRiemannKernel q ((u + v) / 2)
                  (y + (u - v) / 2) y X k) /
              (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ (2 : ℕ)) *
                phi (pastVertex s y (u,v)) := by
  have hc0 : HasCompactSupport (fun p => phi (pastVertex s y p)) :=
    hc.comp_homeomorph (physicalPastChart s y)
  have hc1 : HasCompactSupport
      (fun p => eventDir (-1/2,-1/2) phi (pastVertex s y p)) :=
    (hc.fderiv_apply ℝ (-1/2,-1/2)).comp_homeomorph (physicalPastChart s y)
  obtain ⟨R0,hR0,h0⟩ := hc0.exists_pos_le_norm
  obtain ⟨R1,hR1,h1⟩ := hc1.exists_pos_le_norm
  let R := max R0 R1
  have hR0le : R0 ≤ R := le_max_left _ _
  have hR1le : R1 ≤ R := le_max_right _ _
  have hR : 0 ≤ R := hR0.le.trans hR0le
  refine ⟨R,hR,?_⟩
  apply fullAngularRiemannKernel_physical_null_green q branch s y X k R R hR hR phi hp
  · intro v
    exact h1 (R,v) (hR1le.trans ((le_abs_self R).trans (norm_fst_le (R,v))))
  · intro u
    exact h0 (u,R) (hR0le.trans ((le_abs_self R).trans (norm_snd_le (u,R))))

private def fullNullTestResidual (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  closedFullKernel q branch y X k p *
      (eventWave phi (pastVertex s y p) / 4) -
    fullForcing q branch y X k p * phi (pastVertex s y p)

private theorem fullNullTestResidual_regular (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : ℝ × ℝ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Continuous (fullNullTestResidual q branch s y X k phi) ∧
      HasCompactSupport (fullNullTestResidual q branch s y X k phi) := by
  have hw : ContDiff ℝ ∞ (eventWave phi) := physicalEventWave_smooth hp
  have hcw : HasCompactSupport (eventWave phi) := by
    unfold eventWave
    exact ((hc.fderiv_apply ℝ (1,0)).fderiv_apply ℝ (1,0)).sub
      ((hc.fderiv_apply ℝ (0,1)).fderiv_apply ℝ (0,1))
  have hmap : Continuous (pastVertex s y) := by unfold pastVertex; fun_prop
  constructor
  · exact ((closedFullKernel_continuous q branch y X k).mul
      ((hw.continuous.comp hmap).div_const 4)).sub
      ((fullForcing_continuous q branch y X k).mul (hp.continuous.comp hmap))
  · have hdiv : HasCompactSupport
        (fun p => eventWave phi (pastVertex s y p) / 4) := by
      simp only [div_eq_mul_inv]
      exact (hcw.comp_homeomorph (physicalPastChart s y)).mul_right
    exact hdiv.mul_left.sub
      ((hc.comp_homeomorph (physicalPastChart s y)).mul_left)

private theorem fullQuadrant_eq_box (F : ℝ × ℝ → ℂ)
    (hF : Continuous F) (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ p : ℝ × ℝ, R ≤ ‖p‖ → F p = 0) :
    (∫ p in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ), F p) =
      ∫ u in (0 : ℝ)..R, ∫ v in (0 : ℝ)..R, F (u,v) := by
  have he : (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)).indicator F =
      (Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R).indicator F := by
    funext p
    by_cases hq : p ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)
    · by_cases hb : p ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R
      · simp only [Set.indicator_of_mem hq, Set.indicator_of_mem hb]
      · have hn : R ≤ ‖p‖ := by
          have hh : R < p.1 ∨ R < p.2 := by
            by_contra! hh
            exact hb ⟨⟨hq.1,hh.1⟩,⟨hq.2,hh.2⟩⟩
          rcases hh with hh | hh
          · exact hh.le.trans ((le_abs_self _).trans (norm_fst_le p))
          · exact hh.le.trans ((le_abs_self _).trans (norm_snd_le p))
        simp only [Set.indicator_of_mem hq, Set.indicator_of_notMem hb, hzero p hn]
    · have hb : p ∉ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R :=
        fun h => hq ⟨h.1.1,h.2.1⟩
      simp only [Set.indicator_of_notMem hq, Set.indicator_of_notMem hb]
  rw [← integral_indicator (measurableSet_Ici.prod measurableSet_Ici), he,
    integral_indicator (measurableSet_Icc.prod measurableSet_Icc), Measure.volume_eq_prod]
  rw [setIntegral_prod F
    (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))]
  simp_rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hR]

private theorem fullRectangle_sub (F G : ℝ × ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G) (U V : ℝ) :
    (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, F (u,v)-G (u,v)) =
      (∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, F (u,v)) -
        ∫ u in (0 : ℝ)..U, ∫ v in (0 : ℝ)..V, G (u,v) := by
  have hi (u : ℝ) :
      (∫ v in (0 : ℝ)..V, F (u,v)-G (u,v)) =
        (∫ v in (0 : ℝ)..V, F (u,v)) -
          ∫ v in (0 : ℝ)..V, G (u,v) :=
    intervalIntegral.integral_sub
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V)
      ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 V)
  simp_rw [hi]
  exact intervalIntegral.integral_sub
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ => F (u,v)) hF 0 V).intervalIntegrable 0 U)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun u v : ℝ => G (u,v)) hG 0 V).intervalIntegrable 0 U)

private theorem fullNullTestResidual_integral (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : ℝ × ℝ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ p in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ),
      fullNullTestResidual q branch s y X k phi p) =
        fullAngularField q branch ![X, Real.exp k] * phi (s,y) := by
  have hc0 : HasCompactSupport (fun p => phi (pastVertex s y p)) :=
    hc.comp_homeomorph (physicalPastChart s y)
  have hc1 : HasCompactSupport
      (fun p => eventDir (-1/2,-1/2) phi (pastVertex s y p)) :=
    (hc.fderiv_apply ℝ (-1/2,-1/2)).comp_homeomorph (physicalPastChart s y)
  obtain ⟨R0,hR0,h0⟩ := hc0.exists_pos_le_norm
  obtain ⟨R1,hR1,h1⟩ := hc1.exists_pos_le_norm
  have hr := fullNullTestResidual_regular q branch s y X k phi hp hc
  obtain ⟨R2,hR2,h2⟩ := hr.2.exists_pos_le_norm
  let R := max (max R0 R1) R2
  have hb0 : R0 ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hb1 : R1 ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hb2 : R2 ≤ R := le_max_right _ _
  have hR : 0 ≤ R := hR0.le.trans hb0
  rw [fullQuadrant_eq_box _ hr.1 R hR (fun p hp' => h2 p (hb2.trans hp'))]
  have hmap : Continuous (pastVertex s y) := by unfold pastVertex; fun_prop
  have hA : Continuous (fun p : ℝ × ℝ =>
      closedFullKernel q branch y X k p *
        (eventWave phi (pastVertex s y p)/4)) :=
    (closedFullKernel_continuous q branch y X k).mul
      (((physicalEventWave_smooth hp).continuous.comp hmap).div_const 4)
  have hB : Continuous (fun p : ℝ × ℝ =>
      fullForcing q branch y X k p * phi (pastVertex s y p)) :=
    (fullForcing_continuous q branch y X k).mul (hp.continuous.comp hmap)
  change (∫ u in (0 : ℝ)..R, ∫ v in (0 : ℝ)..R,
      (closedFullKernel q branch y X k (u,v) *
        (eventWave phi (pastVertex s y (u,v))/4) -
        fullForcing q branch y X k (u,v) * phi (pastVertex s y (u,v)))) = _
  rw [fullRectangle_sub _ _ hA hB R R]
  have hgreen := fullAngularRiemannKernel_physical_null_green q branch
    s y X k R R hR hR phi hp
    (fun v => h1 (R,v) (hb1.trans ((le_abs_self R).trans (norm_fst_le (R,v)))))
    (fun u => h0 (u,R) (hb0.trans ((le_abs_self R).trans (norm_snd_le (u,R)))))
  have hleft :
      (∫ u in (0 : ℝ)..R, ∫ v in (0 : ℝ)..R,
        closedFullKernel q branch y X k (u,v) *
          (eventWave phi (pastVertex s y (u,v))/4)) =
        ∫ u in (0 : ℝ)..R, ∫ v in (0 : ℝ)..R,
          fullAngularRiemannKernel q branch ((u+v)/2)
            (y+(u-v)/2) y X k *
              (eventWave phi (pastVertex s y (u,v))/4) := by
    apply intervalIntegral.integral_congr
    intro u hu
    apply intervalIntegral.integral_congr
    intro v hv
    have hu0 : 0 ≤ u := (show u ∈ Icc 0 R by simpa [uIcc_of_le hR] using hu).1
    have hv0 : 0 ≤ v := (show v ∈ Icc 0 R by simpa [uIcc_of_le hR] using hv).1
    change closedFullKernel q branch y X k (u,v) * _ = _
    rw [closedFullKernel_eq_actual q branch y u v X k hu0 hv0]
  have hright :
      (∫ u in (0 : ℝ)..R, ∫ v in (0 : ℝ)..R,
        fullForcing q branch y X k (u,v) * phi (pastVertex s y (u,v))) =
        ∫ u in (0 : ℝ)..R, ∫ v in (0 : ℝ)..R,
          parameter q branch *
            (fullAngularRiemannKernel q branch ((u+v)/2)
              (y+(u-v)/2) y X k +
              D4BMNativeCircle.nativeRiemannKernel q ((u+v)/2)
                (y+(u-v)/2) y X k) /
            (4*(Real.cosh (y+(u-v)/2) : ℂ)^(2 : ℕ)) *
              phi (pastVertex s y (u,v)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    apply intervalIntegral.integral_congr
    intro v hv
    have hu0 : 0 ≤ u := (show u ∈ Icc 0 R by simpa [uIcc_of_le hR] using hu).1
    have hv0 : 0 ≤ v := (show v ∈ Icc 0 R by simpa [uIcc_of_le hR] using hv).1
    unfold fullForcing
    change parameter q branch *
        (closedFullKernel q branch y X k (u,v) + closedNativeKernel q y X k (u,v)) /
        (4*(Real.cosh (y+(u-v)/2) : ℂ)^(2 : ℕ)) *
          phi (pastVertex s y (u,v)) = _
    rw [closedFullKernel_eq_actual q branch y u v X k hu0 hv0,
      closedNativeKernel_eq_actual q y u v X k hu0 hv0]
  rw [hleft, hright, hgreen]
  ring

/-- One literal full-angular causal cone tested by the physical time/radial
wave operator, with its complete full-plus-native angular action. -/
def fullTemporalConeResidual (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if |p.2-y| ≤ s-p.1 then
    fullAngularRiemannKernel q branch (s-p.1) p.2 y X k * eventWave phi p -
      parameter q branch *
        (fullAngularRiemannKernel q branch (s-p.1) p.2 y X k +
          D4BMNativeCircle.nativeRiemannKernel q (s-p.1) p.2 y X k) /
        (Real.cosh p.2 : ℂ)^(2 : ℕ) * phi p
  else 0

private theorem fullPast_causal (s y : ℝ) (p : ℝ × ℝ) :
    |(pastVertex s y p).2-y| ≤ s-(pastVertex s y p).1 ↔
      p ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) := by
  simp only [pastVertex, mem_prod, mem_Ici, abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

private theorem fullTemporalConeResidual_pullback (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    fullTemporalConeResidual q branch s y X k phi (pastVertex s y p) =
      4 * (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)).indicator
        (fullNullTestResidual q branch s y X k phi) p := by
  by_cases hp : p ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)
  · rw [fullTemporalConeResidual, if_pos ((fullPast_causal s y p).mpr hp),
      Set.indicator_of_mem hp, fullNullTestResidual]
    have hK := closedFullKernel_eq_actual q branch y p.1 p.2 X k hp.1 hp.2
    have hN := closedNativeKernel_eq_actual q y p.1 p.2 X k hp.1 hp.2
    dsimp only [fullForcing]
    rw [hK,hN]
    simp only [pastVertex]
    rw [show s-(s-(p.1+p.2)/2)=(p.1+p.2)/2 by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · rw [fullTemporalConeResidual,
      if_neg (fun h => hp ((fullPast_causal s y p).mp h)),
      Set.indicator_of_notMem hp, mul_zero]

theorem fullTemporalConeResidual_integrable (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : ℝ × ℝ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Integrable (fullTemporalConeResidual q branch s y X k phi) := by
  have hr := fullNullTestResidual_regular q branch s y X k phi hp hc
  have hi : Integrable (fun p =>
      fullTemporalConeResidual q branch s y X k phi (pastVertex s y p)) := by
    simp_rw [fullTemporalConeResidual_pullback]
    exact ((hr.1.integrable_of_hasCompactSupport hr.2).indicator
      (measurableSet_Ici.prod measurableSet_Ici)).const_mul 4
  have h := ((physicalPastChart s y).toMeasurableEquiv.measurableEmbedding.integrable_map_iff
    (μ := volume) (g := fullTemporalConeResidual q branch s y X k phi)).mpr hi
  change Integrable (fullTemporalConeResidual q branch s y X k phi)
    (Measure.map (pastVertex s y) volume) at h
  rw [pastVertex_volume, integrable_smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)] at h
  exact h

/-- Exact physical-cone distributional contact of the branch-dependent full
angular kernel. The full/native angular action is retained pointwise; its
integral cancels the temporal wave except at the full-field vertex. -/
theorem fullTemporalConeResidual_integral (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : ℝ × ℝ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ p : ℝ × ℝ, fullTemporalConeResidual q branch s y X k phi p) =
      2 * (fullAngularField q branch ![X, Real.exp k] * phi (s,y)) := by
  have h := integral_pastVertex s y
    (fullTemporalConeResidual q branch s y X k phi)
  simp_rw [fullTemporalConeResidual_pullback] at h
  rw [integral_const_mul,
    integral_indicator (measurableSet_Ici.prod measurableSet_Ici),
    fullNullTestResidual_integral q branch s y X k phi hp hc] at h
  linear_combination -(1/2 : ℂ) * h

/-- Literal full-angular direct-minus-image temporal weak action. -/
def fullDirichletTemporalResidual (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (fullTemporalConeResidual q branch s y X k phi p -
    fullTemporalConeResidual q branch s (-y) X k phi p) / 2

/-- The weak action is exactly the original full-circle direct-minus-image
kernel and its native companion, not an auxiliary cone residual. -/
theorem fullDirichletTemporalResidual_kernel (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    fullDirichletTemporalResidual q branch s y X k phi p =
      angularDirichletKernel q branch (s-p.1) p.2 y X k * eventWave phi p -
        parameter q branch *
          (angularDirichletKernel q branch (s-p.1) p.2 y X k +
            D4BMNativeCircle.nativeDirichletCausalKernel q (s-p.1) p.2 y X k) /
          (Real.cosh p.2 : ℂ)^(2 : ℕ) * phi p := by
  have hkernel (h x z : ℝ) :
      fullAngularRiemannKernel q branch h x z X k =
        angularMean q branch (Real.arcosh (invariant h x z)) X k := rfl
  unfold fullDirichletTemporalResidual fullTemporalConeResidual angularDirichletKernel
    D4BMNativeCircle.nativeDirichletCausalKernel
  simp only [sub_neg_eq_add, hkernel]
  split_ifs <;> simp only [div_eq_mul_inv] <;> ring

/-- Both causal gates and the original image factor produce the exact
source-minus-image full-field contact. -/
theorem fullDirichletTemporalResidual_integral (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : ℝ × ℝ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ p : ℝ × ℝ, fullDirichletTemporalResidual q branch s y X k phi p) =
      fullAngularField q branch ![X, Real.exp k] *
        (phi (s,y)-phi (s,-y)) := by
  simp_rw [fullDirichletTemporalResidual]
  rw [integral_div, integral_sub
    (fullTemporalConeResidual_integrable q branch s y X k phi hp hc)
    (fullTemporalConeResidual_integrable q branch s (-y) X k phi hp hc),
    fullTemporalConeResidual_integral q branch s y X k phi hp hc,
    fullTemporalConeResidual_integral q branch s (-y) X k phi hp hc]
  ring

/-- The reflected source vertex is absent for a test compactly supported in
the physical negative-radial half-plane. -/
theorem fullDirichletTemporalResidual_physical (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (hy : y < 0) (phi : ℝ × ℝ → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hphysical : tsupport phi ⊆ {p : ℝ × ℝ | p.2 < 0}) :
    (∫ p : ℝ × ℝ, fullDirichletTemporalResidual q branch s y X k phi p) =
      fullAngularField q branch ![X, Real.exp k] * phi (s,y) := by
  have hz : phi (s,-y) = 0 := by
    by_contra hn
    have h := hphysical (subset_tsupport phi
      (show (s,-y) ∈ Function.support phi from hn))
    change -y < 0 at h
    linarith
  rw [fullDirichletTemporalResidual_integral q branch s y X k phi hp hc,
    hz, sub_zero]

end

end RHTower.D4BMFullAngularGoursatTransposition
