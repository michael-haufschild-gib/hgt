import GaloisForLFunctions.HTGeometry.VolterraRectangleTransposition
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursat

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

namespace RHTower.D4BMFullAngularGoursatTransposition

open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMNativeCircle D4BMCausalKernel
open D4BMFullAngularCircle D4BMFullAngularCircleAction D4BMFullAngularGoursat

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
    (4 * (Real.cosh (y + (p.1 - p.2) / 2) : ℂ) ^ 2)

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
            (4 * (Real.cosh (y + (a - b) / 2) : ℂ) ^ 2) := by
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
          (4 * (Real.cosh (y + (a - b) / 2) : ℂ) ^ 2) =
        parameter q branch *
          (closedFullKernel q branch y X k (a, b) + closedNativeKernel q y X k (a, b)) /
          (4 * (Real.cosh (y + (a - b) / 2) : ℂ) ^ 2)
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
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ 2) * phi u * psi v := by
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
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ 2) * phi u * psi v := by
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
            (4 * (Real.cosh (y + (u - v) / 2) : ℂ) ^ 2) * phi u * psi v
      unfold fullForcing
      rw [closedFullKernel_eq_actual q branch y u v X k hu0 hv0,
        closedNativeKernel_eq_actual q y u v X k hu0 hv0]

end

end RHTower.D4BMFullAngularGoursatTransposition
