import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCircleMean
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalRiemannKernel
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! A Riemann kernel acting on the complete original theta half-square. -/
namespace RHTower.D4BMNativeCircle
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMCausalKernel
open Set Filter Topology
open scoped ContDiff
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def angularKernel (q : XiZeroCopy) (z X k : ℝ) : ℂ := mean q (Real.arcosh z) X k
def argumentFirst (q : XiZeroCopy) (z X k : ℝ) : ℂ :=
  deriv (fun r => mean q r X k) (Real.arcosh z)/(Real.sinh (Real.arcosh z):ℂ)
def argumentSecond (q : XiZeroCopy) (z X k : ℝ) : ℂ :=
  deriv (deriv (fun r => mean q r X k)) (Real.arcosh z)/(Real.sinh (Real.arcosh z):ℂ)^2-
    (Real.cosh (Real.arcosh z):ℂ)*deriv (fun r => mean q r X k) (Real.arcosh z)/
      (Real.sinh (Real.arcosh z):ℂ)^3
def angularAction (q : XiZeroCopy) (z X k : ℝ) : ℂ :=
  (Real.exp k:ℂ)^2*deriv (deriv (fun r => angularKernel q z r k)) X+
    deriv (deriv (fun r => angularKernel q z X r)) k-deriv (fun r => angularKernel q z X r) k

private theorem radius_derivative {z : ℝ} (hz : 1 < z) :
    HasDerivAt Real.arcosh (1/Real.sinh (Real.arcosh z)) z := by
  simpa only [one_div,Real.sinh_arcosh hz.le] using Real.hasDerivAt_arcosh hz

private theorem angular_derivatives (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    HasDerivAt (fun y => angularKernel q y X k) (argumentFirst q z X k) z ∧
    HasDerivAt (fun y => argumentFirst q y X k) (argumentSecond q z X k) z := by
  have hs := mean_radial_smooth q X k
  have hs1 := (contDiff_infty_iff_deriv.mp hs).2
  have hm := ((hs.contDiffAt (x := Real.arcosh z)).differentiableAt (by simp)).hasDerivAt
  have hm1 := ((hs1.contDiffAt (x := Real.arcosh z)).differentiableAt (by simp)).hasDerivAt
  have hd := radius_derivative hz
  have hn : Real.sinh (Real.arcosh z) ≠ 0 := (Real.sinh_pos_iff.mpr (Real.arcosh_pos hz)).ne'
  have hnC : (Real.sinh (Real.arcosh z):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  have hr := ((Real.hasDerivAt_sinh (Real.arcosh z)).comp z hd).ofReal_comp
  constructor
  · apply (hm.scomp z hd).congr_deriv
    simp only [argumentFirst,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one]
    ring
  · apply ((hm1.scomp z hd).div hr hnC).congr_deriv
    dsimp [argumentSecond]
    simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one]
    field_simp [hnC]

private theorem angular_equation (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    ((z:ℂ)^2-1)*argumentSecond q z X k+2*(z:ℂ)*argumentFirst q z X k=angularAction q z X k := by
  have hn : (Real.sinh (Real.arcosh z):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr (Real.arcosh_pos hz)).ne'
  have he : (z:ℂ)^2-1=(Real.sinh (Real.arcosh z):ℂ)^2 := by
    have h := Real.cosh_sq_sub_sinh_sq (Real.arcosh z)
    rw [Real.cosh_arcosh hz.le] at h
    exact_mod_cast (by linarith : z^2-1=Real.sinh (Real.arcosh z)^2)
  have h := mean_darboux q (Real.arcosh z) X k
  change _ = (Real.sinh (Real.arcosh z):ℂ)^2*angularAction q z X k at h
  rw [Real.cosh_arcosh hz.le] at h
  rw [he]
  dsimp [argumentSecond,argumentFirst]
  rw [Real.cosh_arcosh hz.le]
  linear_combination (norm := (field_simp [hn]; ring)) h/(Real.sinh (Real.arcosh z):ℂ)^2

def nativeRiemannKernel (q : XiZeroCopy) (h x y X k : ℝ) : ℂ :=
  angularKernel q (invariant h x y) X k
def nativeTimeFirst (q : XiZeroCopy) (h x y X k : ℝ) : ℂ :=
  argumentFirst q (invariant h x y) X k*(invariantTimeFirst h x y:ℂ)
def nativeTimeSecond (q : XiZeroCopy) (h x y X k : ℝ) : ℂ :=
  argumentSecond q (invariant h x y) X k*(invariantTimeFirst h x y:ℂ)^2+
    argumentFirst q (invariant h x y) X k*(invariantTimeSecond h x y:ℂ)
def nativeSpaceFirst (q : XiZeroCopy) (h x y X k : ℝ) : ℂ :=
  argumentFirst q (invariant h x y) X k*(invariantSpaceFirst h x y:ℂ)
def nativeSpaceSecond (q : XiZeroCopy) (h x y X k : ℝ) : ℂ :=
  argumentSecond q (invariant h x y) X k*(invariantSpaceFirst h x y:ℂ)^2+
    argumentFirst q (invariant h x y) X k*(invariantSpaceSecond h x y:ℂ)

private theorem time_derivatives (q : XiZeroCopy) (h x y X k : ℝ) (hz : 1 < invariant h x y) :
    HasDerivAt (fun t => nativeRiemannKernel q t x y X k) (nativeTimeFirst q h x y X k) h ∧
    HasDerivAt (fun t => nativeTimeFirst q t x y X k) (nativeTimeSecond q h x y X k) h := by
  obtain ⟨hA,hB⟩ := angular_derivatives q X k hz
  obtain ⟨hz1,hz2⟩ := invariant_time_derivatives h x y
  constructor
  · apply (hA.scomp h hz1).congr_deriv
    simp only [nativeTimeFirst,Complex.real_smul]
    ring
  · apply ((hB.scomp h hz1).mul hz2.ofReal_comp).congr_deriv
    simp only [nativeTimeSecond,Complex.real_smul,Function.comp_def]
    ring

private theorem space_derivatives (q : XiZeroCopy) (h x y X k : ℝ) (hz : 1 < invariant h x y) :
    HasDerivAt (fun t => nativeRiemannKernel q h t y X k) (nativeSpaceFirst q h x y X k) x ∧
    HasDerivAt (fun t => nativeSpaceFirst q h t y X k) (nativeSpaceSecond q h x y X k) x := by
  obtain ⟨hA,hB⟩ := angular_derivatives q X k hz
  obtain ⟨hz1,hz2⟩ := invariant_space_derivatives h x y
  constructor
  · apply (hA.scomp x hz1).congr_deriv
    simp only [nativeSpaceFirst,Complex.real_smul]
    ring
  · apply ((hB.scomp x hz1).mul hz2.ofReal_comp).congr_deriv
    simp only [nativeSpaceSecond,Complex.real_smul,Function.comp_def]
    ring

/-- Interior of the original forward characteristic cone in the native angular chart. -/
abbrev InteriorPoint := {p : CausalPoint // 1 < invariant p.time p.target p.source}

/-- The complete theta-source Riemann kernel satisfies the original time/tortoise wave equation
with the actual hyperbolic Laplacian in horizontal and logarithmic-height coordinates. -/
theorem nativeRiemannKernel_wave (q : XiZeroCopy) (p : InteriorPoint) (X k : ℝ) :
    deriv (deriv (fun h => nativeRiemannKernel q h p.val.target p.val.source X k)) p.val.time-
      deriv (deriv (fun x => nativeRiemannKernel q p.val.time x p.val.source X k)) p.val.target-
      ((Real.exp k:ℂ)^2*deriv (deriv (fun a => nativeRiemannKernel q p.val.time p.val.target p.val.source a k)) X+
        deriv (deriv (fun a => nativeRiemannKernel q p.val.time p.val.target p.val.source X a)) k-
        deriv (fun a => nativeRiemannKernel q p.val.time p.val.target p.val.source X a) k)/
          (Real.cosh p.val.target:ℂ)^2=0 := by
  obtain ⟨ht,htt⟩ := time_derivatives q p.val.time p.val.target p.val.source X k p.property
  obtain ⟨hx,hxx⟩ := space_derivatives q p.val.time p.val.target p.val.source X k p.property
  have et : deriv (fun h => nativeRiemannKernel q h p.val.target p.val.source X k) =ᶠ[𝓝 p.val.time]
      fun h => nativeTimeFirst q h p.val.target p.val.source X k := by
    filter_upwards [(invariant_time_derivatives p.val.time p.val.target p.val.source).1.continuousAt.eventually_const_lt p.property] with h hh
    exact (time_derivatives q h p.val.target p.val.source X k hh).1.deriv
  have ex : deriv (fun x => nativeRiemannKernel q p.val.time x p.val.source X k) =ᶠ[𝓝 p.val.target]
      fun x => nativeSpaceFirst q p.val.time x p.val.source X k := by
    filter_upwards [(invariant_space_derivatives p.val.time p.val.target p.val.source).1.continuousAt.eventually_const_lt p.property] with x hh
    exact (space_derivatives q p.val.time x p.val.source X k hh).1.deriv
  rw [et.deriv_eq,ex.deriv_eq,htt.deriv,hxx.deriv]
  have h1 : (invariantTimeFirst p.val.time p.val.target p.val.source:ℂ)^2-
      (invariantSpaceFirst p.val.time p.val.target p.val.source:ℂ)^2=
      ((invariant p.val.time p.val.target p.val.source:ℂ)^2-1)/(Real.cosh p.val.target:ℂ)^2 := by
    exact_mod_cast (invariant_wave_geometry p.val.time p.val.target p.val.source).1
  have h2 : (invariantTimeSecond p.val.time p.val.target p.val.source:ℂ)-
      (invariantSpaceSecond p.val.time p.val.target p.val.source:ℂ)=
      2*(invariant p.val.time p.val.target p.val.source:ℂ)/(Real.cosh p.val.target:ℂ)^2 := by
    exact_mod_cast (invariant_wave_geometry p.val.time p.val.target p.val.source).2
  have h := angular_equation q X k p.property
  change _-_ - angularAction q (invariant p.val.time p.val.target p.val.source) X k/(Real.cosh p.val.target:ℂ)^2=0
  dsimp [nativeTimeSecond,nativeSpaceSecond]
  linear_combination
    argumentSecond q (invariant p.val.time p.val.target p.val.source) X k*h1+
    argumentFirst q (invariant p.val.time p.val.target p.val.source) X k*h2+
    h/(Real.cosh p.val.target:ℂ)^2

/-- The characteristic value is the literal original source, without a spectral projection. -/
theorem nativeRiemannKernel_characteristic (q : XiZeroCopy) (x y X k : ℝ) :
    nativeRiemannKernel q (x-y) x y X k=fullSquarePotential q ![X,Real.exp k] := by
  rw [nativeRiemannKernel,invariant_characteristic,angularKernel,Real.arcosh_zero,mean_zero]

/-- The actual full-source kernel and its image agree at the original AdS endpoint. -/
theorem nativeRiemannKernel_AdS (q : XiZeroCopy) (h y X k : ℝ) :
    nativeRiemannKernel q h 0 y X k-nativeRiemannKernel q h 0 (-y) X k=0 := by
  rw [nativeRiemannKernel,nativeRiemannKernel,invariant_AdS,sub_self]

end
end RHTower.D4BMNativeCircle
