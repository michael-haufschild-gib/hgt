import GaloisForLFunctions.RHTower.XiRationalHurwitzDyadicRefinement
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Complete Hurwitz power-energy regularization

The literal native energy on the prescribed dyadic ray is a hyperbolic square. Its reciprocal
regularization stays between zero and one. Its depth limit is one exactly on the critical line
and zero elsewhere; no statement about the location of Xi zeros is assumed.
-/

namespace RHTower

noncomputable section
open Filter Classical
open scoped Topology

/-- The complete dyadic history of the native normalized reflection energy. -/
def paperHurwitzPowerEnergy (rho : ℂ) (k : ℕ) : ℝ :=
  normalizedScaleSeamEnergy (2 ^ k) rho

theorem paperHurwitzPowerEnergy_eq_sinh (rho : ℂ) (k : ℕ) :
    paperHurwitzPowerEnergy rho k =
      Real.sinh ((k : ℝ) * ((rho.re - 1 / 2) * Real.log 2)) ^ 2 := by
  simpa only [paperHurwitzPowerEnergy, Nat.cast_ofNat] using
    normalizedScaleSeamEnergy_pow_eq_sinh rho 2 k

/-- Every actual Xi fibre retains its original finite rational-Hurwitz packet energy. -/
theorem paperHurwitzPowerEnergy_eq_source (rho : XiDivisorSupport) (k : ℕ) :
    paperHurwitzPowerEnergy (rho : ℂ) k =
      normalizedRationalHurwitzReflectionEnergy (2 ^ k) (rho : ℂ) :=
  (normalizedRationalHurwitzReflectionEnergy_eq_scale
    (xi_divisor_support_re_mem_open_unit rho) _).symm

theorem paperHurwitzPowerEnergy_nonneg (rho : ℂ) (k : ℕ) :
    0 ≤ paperHurwitzPowerEnergy rho k :=
  normalizedScaleSeamEnergy_nonneg rho _

theorem paperHurwitzPowerEnergy_zero (rho : ℂ) : paperHurwitzPowerEnergy rho 0 = 0 := by
  simp [paperHurwitzPowerEnergy_eq_sinh]

theorem paperHurwitzPowerEnergy_eq_zero_of_wall {rho : ℂ} (hr : rho.re = 1 / 2) (k : ℕ) :
    paperHurwitzPowerEnergy rho k = 0 := by
  simp [paperHurwitzPowerEnergy_eq_sinh, hr]

/-- The native all-power lower bound pays divergence of every off-wall energy ray. -/
theorem tendsto_paperHurwitzPowerEnergy_atTop {rho : ℂ} (hr : rho.re ≠ 1 / 2) :
    Tendsto (paperHurwitzPowerEnergy rho) atTop atTop := by
  have he : 0 < normalizedScaleSeamEnergy 2 rho :=
    (normalizedScaleSeamEnergy_pos_iff rho 2 (by norm_num)).mpr hr
  have hk : Tendsto (fun k : ℕ => (k : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono (fun k => normalizedScaleSeamEnergy_pow_linear_le rho 2 k)
    (Filter.Tendsto.atTop_mul_const he hk)

/-- Bounded regularization of the actual complete power-energy history. -/
def paperHurwitzRegularizer (rho : ℂ) (k : ℕ) : ℝ :=
  (1 + paperHurwitzPowerEnergy rho k)⁻¹

theorem paperHurwitzRegularizer_pos (rho : ℂ) (k : ℕ) :
    0 < paperHurwitzRegularizer rho k :=
  inv_pos.mpr (by linarith [paperHurwitzPowerEnergy_nonneg rho k])

theorem paperHurwitzRegularizer_le_one (rho : ℂ) (k : ℕ) :
    paperHurwitzRegularizer rho k ≤ 1 := by
  apply (inv_le_one₀ (by linarith [paperHurwitzPowerEnergy_nonneg rho k])).mpr
  linarith [paperHurwitzPowerEnergy_nonneg rho k]

theorem paperHurwitzRegularizer_zero (rho : ℂ) : paperHurwitzRegularizer rho 0 = 1 := by
  simp [paperHurwitzRegularizer, paperHurwitzPowerEnergy_zero]

theorem paperHurwitzRegularizer_of_wall {rho : ℂ} (hr : rho.re = 1 / 2) (k : ℕ) :
    paperHurwitzRegularizer rho k = 1 := by
  simp [paperHurwitzRegularizer, paperHurwitzPowerEnergy_eq_zero_of_wall hr]

/-- The complete depth limit distinguishes the line from its complement. -/
theorem tendsto_paperHurwitzRegularizer (rho : ℂ) :
    Tendsto (paperHurwitzRegularizer rho) atTop (𝓝 (if rho.re = 1 / 2 then 1 else 0)) := by
  by_cases hr : rho.re = 1 / 2
  · simp only [if_pos hr]
    have heq : paperHurwitzRegularizer rho = fun _ => 1 :=
      funext (paperHurwitzRegularizer_of_wall hr)
    rw [heq]
    exact tendsto_const_nhds
  · simp only [if_neg hr]
    have he := (tendsto_paperHurwitzPowerEnergy_atTop hr).atTop_add
      (tendsto_const_nhds (x := (1 : ℝ)))
    change Tendsto (fun k => (1 + paperHurwitzPowerEnergy rho k)⁻¹) atTop (𝓝 0)
    simpa only [Function.comp_def, add_comm] using
      tendsto_inv_atTop_zero.comp he

/-- Every finite-depth coefficient varies continuously with the source point. -/
theorem continuous_paperHurwitzRegularizer (k : ℕ) :
    Continuous (fun rho : ℂ => paperHurwitzRegularizer rho k) := by
  have he : Continuous (fun rho : ℂ => paperHurwitzPowerEnergy rho k) := by
    simp only [paperHurwitzPowerEnergy_eq_sinh]
    fun_prop
  apply (continuous_const.add he).inv₀
  intro rho
  change 1 + paperHurwitzPowerEnergy rho k ≠ 0
  exact ne_of_gt (by linarith [paperHurwitzPowerEnergy_nonneg rho k])

/-- The wall character in the complex scalar field of the history space. -/
def paperHurwitzWallCharacter (rho : ℂ) : ℂ := if rho.re = 1 / 2 then 1 else 0

theorem tendsto_paperHurwitzRegularizer_complex (rho : ℂ) :
    Tendsto (fun k => (paperHurwitzRegularizer rho k : ℂ)) atTop
      (𝓝 (paperHurwitzWallCharacter rho)) := by
  simpa only [paperHurwitzWallCharacter, apply_ite, Complex.ofReal_one, Complex.ofReal_zero,
    Function.comp_def] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_paperHurwitzRegularizer rho)

end
end RHTower
