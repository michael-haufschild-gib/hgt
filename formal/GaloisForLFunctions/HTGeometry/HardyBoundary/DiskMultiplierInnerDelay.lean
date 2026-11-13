import GaloisForLFunctions.HTGeometry.HardyBoundary.DiskMultiplierInnerSingularSupport
import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness

/-!
# The single-point inner factor is a pure delay

The Poisson kernel at `1` is the real part of the inverse Cayley map.
Removing the corresponding exponential from an inner factor leaves an analytic
function of constant modulus, hence a unimodular constant.
-/

noncomputable section
open Complex MeasureTheory Metric Set Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.HTGeometry

theorem poissonKernel_at_one_eq_re_diskToRight (z : ℂ) :
    poissonKernel 0 z 1 = (diskToRight z).re := by
  simp only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
    herglotzRieszKernel, sub_zero, diskToRight]

/-- A single Poisson kernel for the inner log defect determines the entire inner factor. -/
theorem innerFactor_eq_unit_mul_delay_of_defect (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0) (d : ℝ)
    (hdef : ∀ z ∈ ball (0 : ℂ) 1,
      diskMultiplierInnerDefect φ hφ z = d * poissonKernel 0 z 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1,
      (diskMultiplierInnerFactor φ hφ).fn z =
        c * Complex.exp (-((d : ℂ) * diskToRight z)) := by
  let g : ℂ → ℂ := fun z => (diskMultiplierInnerFactor φ hφ).fn z *
    Complex.exp ((d : ℂ) * diskToRight z)
  have hnorm (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : ‖g z‖ = 1 := by
    have hpos : 0 < ‖(diskMultiplierInnerFactor φ hφ).fn z‖ :=
      norm_pos_iff.mpr (diskMultiplierInnerFactor_ne_zero φ hφ hz (hne z hz))
    have hlog : Real.log ‖(diskMultiplierInnerFactor φ hφ).fn z‖ =
        -(d * (diskToRight z).re) := by
      have he := hdef z hz
      rw [diskMultiplierInnerDefect, poissonKernel_at_one_eq_re_diskToRight] at he
      linarith only [he]
    change ‖(diskMultiplierInnerFactor φ hφ).fn z *
      Complex.exp ((d : ℂ) * diskToRight z)‖ = 1
    rw [norm_mul, norm_exp, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      ← Real.exp_log hpos, hlog, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hdiff : DifferentiableOn ℂ g (ball (0 : ℂ) 1) := by
    intro z hz
    have hconst : DifferentiableAt ℂ (fun _ : ℂ => (d : ℂ)) z := differentiableAt_const _
    have hmap : DifferentiableAt ℂ diskToRight z := (diskToRight_analyticAt hz).differentiableAt
    have he : DifferentiableAt ℂ (fun w => Complex.exp ((d : ℂ) * diskToRight w)) z :=
      Complex.differentiable_exp.differentiableAt.comp z (hconst.mul hmap)
    exact ((diskMultiplierInnerFactor φ hφ).diff z hz).mul he.differentiableWithinAt
  have hz0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have heq : EqOn g (fun _ => g 0) (ball (0 : ℂ) 1) := by
    apply eqOn_of_isPreconnected_of_isMaxOn_norm
      (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball hdiff hz0
    intro z hz
    change ‖g z‖ ≤ ‖g 0‖
    rw [hnorm z hz, hnorm 0 hz0]
  refine ⟨g 0, hnorm 0 hz0, ?_⟩
  intro z hz
  calc
    _ = (diskMultiplierInnerFactor φ hφ).fn z *
        (Complex.exp ((d : ℂ) * diskToRight z) *
          Complex.exp (-((d : ℂ) * diskToRight z))) := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    _ = g z * Complex.exp (-((d : ℂ) * diskToRight z)) := by rw [← mul_assoc]
    _ = g 0 * Complex.exp (-((d : ℂ) * diskToRight z)) := by rw [heq hz]

/-- Boundary continuity and nonvanishing leave only a nonnegative delay in the inner factor. -/
theorem exists_innerFactor_eq_unit_mul_delay (φ : DiskMultiplier)
    (hφ : ∃ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0)
    (hc : ContinuousOn φ.fn {z : ℂ | ‖z‖ ≤ 1 ∧ z ≠ 1})
    (hne : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → φ.fn z ≠ 0) :
    ∃ d : ℝ, 0 ≤ d ∧ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1,
      (diskMultiplierInnerFactor φ hφ).fn z =
        c * Complex.exp (-((d : ℂ) * diskToRight z)) := by
  have hne' : ∀ z ∈ ball (0 : ℂ) 1, φ.fn z ≠ 0 := by
    intro z hz
    have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    apply hne z hn.le
    intro he
    rw [he, norm_one] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  obtain ⟨ν, hfinite, hrep⟩ := exists_poissonRepresentation
    (harmonicOnNhd_diskMultiplierInnerDefect φ hφ hne')
    (fun z hz => diskMultiplierInnerDefect_nonneg φ hφ hz)
  letI : IsFiniteMeasure ν := hfinite
  refine ⟨ν.real univ, measureReal_nonneg, ?_⟩
  apply innerFactor_eq_unit_mul_delay_of_defect φ hφ hne' (ν.real univ)
  intro z hz
  exact innerDefect_eq_mass_mul_poissonKernel_of_rep φ hφ hc hne hrep hz

#print axioms exists_innerFactor_eq_unit_mul_delay

end GaloisForLFunctions.HTGeometry
