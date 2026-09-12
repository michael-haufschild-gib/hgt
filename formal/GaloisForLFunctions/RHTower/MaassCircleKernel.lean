import GaloisForLFunctions.RHTower.MaassCircleMean
import GaloisForLFunctions.HTGeometry.SmoothCylinderIntegral
import GaloisForLFunctions.RHTower.SoninAnnulusBump
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Compact reproducing kernels for Maass eigenforms

A smooth annular bump divided by the circular mean multiplier reproduces the
original Maass eigenform. Continuity and the value one at radius zero provide
a positive annulus on which the divisor is nonzero.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.MaassCircle
open MaassSmooth HTGeometry.SmoothCylinder
noncomputable section

def kernelAverage {a b : ℝ} (k : Kernel a b) (f : FunctionSpace) (z : ℍ) : ℂ :=
  boxIntegral a b (fun p => k p * f (circlePoint p.1 p.2 z))

private theorem bump_normed_zero {a b : ℝ} (hab : a < b) {r : ℝ}
    (hr : r ∉ Icc a b) : (_root_.RHTower.soninAnnulusBumpData a b hab).normed volume r = 0 := by
  have hz : _root_.RHTower.soninAnnulusBumpData a b hab r = 0 := by
    by_contra h
    have hh := _root_.RHTower.soninAnnulusBumpData_support_subset a b hab h
    exact hr ⟨hh.1.le,hh.2.le⟩
  simp only [ContDiffBump.normed_def, hz, zero_div]

def radialBumpKernel (a b : ℝ) (hab : a < b) : Kernel a b where
  toFun p := (((_root_.RHTower.soninAnnulusBumpData a b hab).normed volume p.1 : ℝ) : ℂ) /
    (2*Real.pi : ℂ)
  smooth := (Complex.ofRealCLM.contDiff.comp
    ((_root_.RHTower.soninAnnulusBumpData a b hab).contDiff_normed.comp contDiff_fst)).div_const _
  periodic _ _ := rfl
  vanish p hp := by simp only [bump_normed_zero hab hp, Complex.ofReal_zero, zero_div]

/-- A compact smooth annular kernel reproduces the specified original Maass form. -/
theorem exists_reproducing_kernel {Γ : Subgroup SL2R} {lam : ℝ} (hlam : 0 < lam)
    (f : MaassCuspEigenform Γ lam) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ k : Kernel a b,
      ∀ z : ℍ, kernelAverage k (ofMaass f) z = f.1.1 z := by
  obtain ⟨phi,hphi,hphi0,haction⟩ := exists_mean_multiplier hlam f
  have hn0 : phi 0 ≠ 0 := by rw [hphi0]; exact one_ne_zero
  obtain ⟨delta,hdelta,hd⟩ := Metric.eventually_nhds_iff.mp
    ((hphi.continuous.continuousAt : ContinuousAt phi 0).eventually_ne hn0)
  let a : ℝ := delta/4
  let b : ℝ := delta/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hab : a < b := by dsimp [a,b]; linarith
  have hn : ∀ r ∈ Icc a b, phi r ≠ 0 := by
    intro r hr
    apply hd
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha.le.trans hr.1)]
    exact hr.2.trans_lt (by dsimp [b]; linarith)
  let k := (radialBumpKernel a b hab).divRadial phi hphi hn
  refine ⟨a,b,ha,hab,k,?_⟩
  intro z
  have hT : 0 ≤ 2*Real.pi := by positivity
  have hTne : (2*Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  let psi : ℝ → ℝ := (_root_.RHTower.soninAnnulusBumpData a b hab).normed volume
  have hmass : (∫ r in a..b, psi r) = 1 := by
    rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => bump_normed_zero hab hr)]
    exact (_root_.RHTower.soninAnnulusBumpData a b hab).integral_normed
  have htheta (r : ℝ) (hr : r ∈ Icc a b) :
      (∫ theta in 0..2*Real.pi, k (r,theta) * f.1.1 (circlePoint r theta z)) =
      (psi r : ℂ) * f.1.1 z := by
    have hm := haction z r (ha.le.trans hr.1)
    change (1/(2*Real.pi : ℂ)) *
      (∫ theta in Ioc 0 (2*Real.pi), f.1.1 (circlePoint r theta z)) = phi r * f.1.1 z at hm
    rw [← intervalIntegral.integral_of_le hT] at hm
    have hi : (∫ theta in 0..2*Real.pi, f.1.1 (circlePoint r theta z)) =
        (2*Real.pi : ℂ) * phi r * f.1.1 z := by
      calc
        _ = (2*Real.pi : ℂ) * ((1/(2*Real.pi : ℂ)) *
            (∫ theta in 0..2*Real.pi, f.1.1 (circlePoint r theta z))) := by field_simp
        _ = _ := by rw [hm]; ring
    change (∫ theta in 0..2*Real.pi,
      ((psi r : ℂ)/(2*Real.pi : ℂ)/phi r) * f.1.1 (circlePoint r theta z)) = _
    rw [intervalIntegral.integral_const_mul, hi]
    field_simp [hn r hr]
  change boxIntegral a b (fun p => k p * f.1.1 (circlePoint p.1 p.2 z)) = _
  rw [boxIntegral_eq_iterated (F := fun p => k p * f.1.1 (circlePoint p.1 p.2 z)) hab.le
    (k.smooth.continuous.mul (circle_source_smooth (ofMaass f) z).continuous)]
  have he : (∫ r in a..b, ∫ theta in 0..2*Real.pi, k (r,theta) * f.1.1 (circlePoint r theta z)) =
      ∫ r in a..b, (psi r : ℂ)*f.1.1 z := by
    apply intervalIntegral.integral_congr
    intro r hr
    exact htheta r (by simpa only [uIcc_of_le hab.le] using hr)
  rw [he, intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, hmass,
    Complex.ofReal_one, one_mul]

end
end GaloisForLFunctions.RHTower.MaassCircle
