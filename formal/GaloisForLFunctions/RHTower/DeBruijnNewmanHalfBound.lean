import GaloisForLFunctions.RHTower.DeBruijnHeatFlowRealZeros
import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity
import GaloisForLFunctions.RHTower.ThetaThresholdXiDivisibleUniqueness
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# The de Bruijn–Newman deformation of `Ξ` has only real zeros from heat time `1/8` on

Riemann's kernel `Φ` (`riemannKernelReal`) is even, positive and decays like `exp(−3 e^{2|x|})`,
and its transform is `Ξ(z) = ξ(1/2 + iz) = ∫ Φ(x) e^{izx} dx`. Put

`H_t(z) = ∫ Φ(x) e^{t x²} e^{izx} dx`,

so that `H_0 = Ξ` (`riemannHeat_zero`). Every zero of `Ξ` has `|Im z| < 1/2`, because every zero of
`ξ` lies in the open critical strip. The heat contraction of the zero strip
(`cosTransform_heat_zeros_im_sq_le`) then gives, unconditionally:

* every zero of `H_t` satisfies `(Im z)² ≤ max(1/4 − 2t, 0)` for `t > 0`;
* for every `t ≥ 1/8` all zeros of `H_t` are real (`riemannHeat_zeros_real`);
* the Riemann hypothesis is the statement that all zeros of `H_0` are real
  (`riemannHypothesis_iff_riemannHeat_zero_real`).

In Newman's normalization `∫₀^∞ e^{s u²} Φ_N(u) cos(zu) du` with `Φ_N(u) = Φ(u/2)` and the variable
`z/2`, the heat time is `s = 4t`, so the statement is de Bruijn's bound `Λ ≤ 1/2` on the
de Bruijn–Newman constant. RH is `Λ ≤ 0`; the gap `(0, 1/2]` is not touched here.
-/

open Complex

namespace RHTower.DeBruijn

noncomputable section

/-- Riemann's kernel belongs to the super-exponential class. -/
theorem riemannKernel_superExp : SuperExpKernel riemannKernelReal where
  continuous := continuous_riemannKernelReal
  even x := by simp [riemannKernelReal, abs_neg]
  nonneg x := (riemannKernelReal_pos x).le
  pos_zero := riemannKernelReal_pos 0
  decay := by
    obtain ⟨C, hC⟩ := riemannPhiKernel_decay_below_theta (c := 3) (by norm_num)
      (by linarith [Real.pi_gt_three])
    have hnorm : ∀ x, ‖riemannPhiKernel x‖ = riemannKernelReal x := fun x => by
      rw [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (riemannKernelReal_pos x)]
    have hC0 : 0 ≤ C := by
      have h := hC 0
      rw [hnorm] at h
      have hpos := riemannKernelReal_pos 0
      by_contra hneg
      push Not at hneg
      have : C * Real.exp (-(3 * Real.exp (2 * |(0 : ℝ)|))) < 0 :=
        mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
      linarith
    refine ⟨C, 3, 2, 0, hC0, by norm_num, by norm_num, le_rfl, fun x => ?_⟩
    have h := hC x
    rw [hnorm] at h
    simpa using h

/-- The transform of Riemann's kernel is `Ξ(z) = ξ(1/2 + iz)`. -/
theorem cosTransform_riemannKernel (z : ℂ) :
    cosTransform riemannKernelReal z = xi (1 / 2 + I * z) := by
  rw [← riemannPhiTransform_eq_xi]
  unfold cosTransform riemannPhiTransform
  congr 1
  funext x
  rw [riemannPhiKernel_eq_ofReal, mul_comm]
  ring_nf

/-- Every zero of `Ξ` has `|Im z| < 1/2`. -/
theorem riemannKernel_zeros_im_sq_le (w : ℂ) (hw : cosTransform riemannKernelReal w = 0) :
    w.im ^ 2 ≤ 1 / 4 := by
  rw [cosTransform_riemannKernel] at hw
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hw
  have hre : (1 / 2 + I * w).re = 1 / 2 - w.im := by simp; ring
  rw [hre] at h0 h1
  nlinarith

/-- The de Bruijn–Newman deformation `H_t(z) = ∫ Φ(x) e^{t x²} e^{izx} dx` of `Ξ`. -/
def riemannHeat (t : ℝ) (z : ℂ) : ℂ :=
  cosTransform (fun x => riemannKernelReal x * Real.exp (t * x ^ 2)) z

theorem riemannHeat_zero (z : ℂ) : riemannHeat 0 z = xi (1 / 2 + I * z) := by
  unfold riemannHeat
  simp only [zero_mul, Real.exp_zero, mul_one]
  exact cosTransform_riemannKernel z

/-- **Contraction of the zero strip along the flow.** -/
theorem riemannHeat_zeros_im_sq_le {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : riemannHeat t z = 0) :
    z.im ^ 2 ≤ max (1 / 4 - 2 * t) 0 :=
  cosTransform_heat_zeros_im_sq_le riemannKernel_superExp riemannKernel_zeros_im_sq_le ht z hz

/-- **de Bruijn's bound (`Λ ≤ 1/2`).** For every heat time `t ≥ 1/8` all zeros of the
de Bruijn–Newman deformation of `Ξ` are real. -/
theorem riemannHeat_zeros_real {t : ℝ} (ht : 1 / 8 ≤ t) {z : ℂ} (hz : riemannHeat t z = 0) :
    z.im = 0 :=
  cosTransform_heat_zeros_real riemannKernel_superExp riemannKernel_zeros_im_sq_le
    (by linarith) (by linarith) z hz

/-- The Riemann hypothesis is the reality of the zeros of `H_0 = Ξ`. -/
theorem riemannHypothesis_iff_riemannHeat_zero_real :
    RiemannHypothesis ↔ ∀ z : ℂ, riemannHeat 0 z = 0 → z.im = 0 := by
  constructor
  · intro hRH z hz
    rw [riemannHeat_zero] at hz
    have h := xi_zero_re_eq_half_of_RH hRH hz
    have hre : (1 / 2 + I * z).re = 1 / 2 - z.im := by simp; ring
    rw [hre] at h
    linarith
  · intro hreal
    refine rh_iff_xi_ne_zero_right.mpr fun s hs hxi => ?_
    have hs' := mem_rightHalf.mp hs
    have hz : riemannHeat 0 (-I * (s - 1 / 2)) = 0 := by
      rw [riemannHeat_zero]
      have : (1 / 2 : ℂ) + I * (-I * (s - 1 / 2)) = s := by
        ring_nf; rw [Complex.I_sq]; ring
      rw [this]
      exact hxi
    have him := hreal _ hz
    have : (-I * (s - 1 / 2)).im = -(s.re - 1 / 2) := by simp
    rw [this] at him
    linarith

end

end RHTower.DeBruijn
