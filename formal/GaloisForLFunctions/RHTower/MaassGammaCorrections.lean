import GaloisForLFunctions.HTGeometry.MellinGammaNegativeStrip
import GaloisForLFunctions.HTGeometry.GaussianMellinMoments

/-!
# Gamma-type polar corrections with double poles

Let `γ₀(s) = (2π)^{−s} Γ(s)` (simple pole at `0`) and `γ₁ = γ₀'` (double pole at `0`).  Their
Mellin pre-images are elementary on both sides of the pole:

* `Re s > 0`: `e^{−2πy} ↦ γ₀(s)` and `log y · e^{−2πy} ↦ γ₁(s)`;
* `−1 < Re s < 0`: `e^{−2πy} − 1 ↦ γ₀(s)` and `log y · (e^{−2πy} − 1) ↦ γ₁(s)`.

The `log` versions are the derivatives of the Mellin transforms (`mellin_hasDerivAt_of_isBigO_rpow`).
The dual `y^{−1} f(1/y)` has Mellin transform `M f(1 − s)` (`hasMellin_dual_inv`), which handles the
reflected corrections `γ₀(1 − s)`, `γ₁(1 − s)` with their double pole at `s = 1`.
-/

open Complex Set Filter Asymptotics Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.MaassGammaCorrections

/-- `γ₀(s) = (2π)^{−s} Γ(s)`. -/
def gam0 (s : ℂ) : ℂ := ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s

/-- `γ₁ = γ₀'`. -/
def gam1 (s : ℂ) : ℂ := deriv gam0 s

/-- `e^{−2πy}`. -/
def eTwo (y : ℝ) : ℂ := ((Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ)

theorem continuous_eTwo : Continuous eTwo := by unfold eTwo; fun_prop

theorem two_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity

theorem hasMellin_eTwo {s : ℂ} (hs : 0 < s.re) : HasMellin eTwo s (gam0 s) := by
  have hbase : MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s := by
    refine (Complex.GammaIntegral_convergent hs).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    ring
  have hconv : MellinConvergent eTwo s :=
    (MellinConvergent.comp_mul_left (f := fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) two_pi_pos).mpr
      hbase
  refine ⟨hconv, ?_⟩
  have h := mellin_comp_mul_left (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ)) s two_pi_pos
  rw [mellin_exp_neg hs, smul_eq_mul] at h
  exact h

theorem eTwo_sub_one_eq (y : ℝ) : eTwo y - 1 = expNegSubOne (2 * Real.pi * y) := by
  simp [eTwo, expNegSubOne]

theorem hasMellin_eTwo_sub_one {s : ℂ} (h1 : -1 < s.re) (h2 : s.re < 0) :
    HasMellin (fun y : ℝ => eTwo y - 1) s (gam0 s) := by
  have hfun : (fun y : ℝ => eTwo y - 1) = fun y : ℝ => expNegSubOne (2 * Real.pi * y) := by
    funext y; exact eTwo_sub_one_eq y
  rw [hfun]
  refine ⟨(MellinConvergent.comp_mul_left (f := expNegSubOne) two_pi_pos).mpr
    (mellinConvergent_expNegSubOne h1 h2), ?_⟩
  rw [mellin_comp_mul_left expNegSubOne s two_pi_pos, mellin_expNegSubOne h1 h2, smul_eq_mul]
  rfl

/-! ## Asymptotics -/

theorem norm_eTwo_le_one (y : ℝ) (hy : 0 ≤ y) : ‖eTwo y‖ ≤ 1 := by
  unfold eTwo
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])

theorem eTwo_isBigO_top (a : ℝ) : eTwo =O[atTop] (fun t : ℝ => t ^ (-a)) := by
  have h := isLittleO_exp_neg_mul_rpow_atTop two_pi_pos (-a)
  refine IsBigO.of_norm_left (h.isBigO.congr_left fun t => ?_)
  rw [eTwo, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_mul]

theorem eTwo_isBigO_bot : eTwo =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [neg_zero, Real.rpow_zero, norm_one, one_mul]
  exact norm_eTwo_le_one t ht0.le

theorem eTwo_sub_one_isBigO_top : (fun y : ℝ => eTwo y - 1) =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [neg_zero, Real.rpow_zero, norm_one, one_mul, eTwo_sub_one_eq]
  exact norm_expNegSubOne_le_one (by positivity)

theorem eTwo_sub_one_isBigO_bot :
    (fun y : ℝ => eTwo y - 1) =O[𝓝[>] 0] (fun t : ℝ => t ^ (-(-1 : ℝ))) := by
  refine IsBigO.of_bound (2 * Real.pi) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [neg_neg, Real.rpow_one, eTwo_sub_one_eq, Real.norm_eq_abs, abs_of_pos ht0]
  exact norm_expNegSubOne_le_self (by positivity)

/-! ## The logarithmic corrections -/

theorem differentiableAt_gam0_of_re_pos {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ gam0 s := by
  unfold gam0
  refine DifferentiableAt.mul ?_ (Complex.differentiableAt_Gamma _ fun m h => ?_)
  · exact (differentiableAt_id.neg).const_cpow (Or.inl (by exact_mod_cast two_pi_pos.ne'))
  · have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- `log y · e^{−2πy}` has Mellin transform `γ₁(s)` for `Re s > 0`. -/
theorem hasMellin_log_eTwo {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun y : ℝ => Real.log y • eTwo y) s (gam1 s) := by
  have hloc : LocallyIntegrableOn eTwo (Ioi 0) :=
    continuous_eTwo.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have h := mellin_hasDerivAt_of_isBigO_rpow (a := s.re + 1) (b := 0) hloc (eTwo_isBigO_top _)
    (by linarith) eTwo_isBigO_bot hs
  refine ⟨h.1, ?_⟩
  -- `mellin eTwo = γ₀` near `s`
  have hev : mellin eTwo =ᶠ[𝓝 s] gam0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact (hasMellin_eTwo hw).2
  have hd : HasDerivAt gam0 (mellin (fun t => Real.log t • eTwo t) s) s := h.2.congr_of_eventuallyEq
    hev.symm
  rw [gam1, hd.deriv]

/-- `log y · (e^{−2πy} − 1)` has Mellin transform `γ₁(s)` for `−1 < Re s < 0`. -/
theorem hasMellin_log_eTwo_sub_one {s : ℂ} (h1 : -1 < s.re) (h2 : s.re < 0) :
    HasMellin (fun y : ℝ => Real.log y • (eTwo y - 1)) s (gam1 s) := by
  have hloc : LocallyIntegrableOn (fun y : ℝ => eTwo y - 1) (Ioi 0) :=
    (continuous_eTwo.sub continuous_const).continuousOn.locallyIntegrableOn measurableSet_Ioi
  have h := mellin_hasDerivAt_of_isBigO_rpow (a := 0) (b := -1) hloc eTwo_sub_one_isBigO_top h2
    eTwo_sub_one_isBigO_bot h1
  refine ⟨h.1, ?_⟩
  have hopen : IsOpen {w : ℂ | -1 < w.re ∧ w.re < 0} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : mellin (fun y : ℝ => eTwo y - 1) =ᶠ[𝓝 s] gam0 := by
    filter_upwards [hopen.mem_nhds ⟨h1, h2⟩] with w hw
    exact (hasMellin_eTwo_sub_one hw.1 hw.2).2
  have hd : HasDerivAt gam0 (mellin (fun t => Real.log t • (eTwo t - 1)) s) s :=
    h.2.congr_of_eventuallyEq hev.symm
  rw [gam1, hd.deriv]

/-! ## The dual transform -/

/-- `y^{−1} f(1/y)` has Mellin transform `M f(1 − s)`. -/
theorem hasMellin_dual_inv {f : ℝ → ℂ} {s m : ℂ} (h : HasMellin f (1 - s) m) :
    HasMellin (fun y : ℝ => (y : ℂ) ^ (-1 : ℂ) * f y⁻¹) s m := by
  have hinv : (fun t : ℝ => f t⁻¹) = fun t : ℝ => f (t ^ (-1 : ℝ)) := by
    funext t; rw [Real.rpow_neg_one]
  have hconv : MellinConvergent (fun t : ℝ => f t⁻¹) (s + (-1 : ℂ)) := by
    rw [hinv, MellinConvergent.comp_rpow (by norm_num : (-1 : ℝ) ≠ 0),
      show (s + (-1 : ℂ)) / ((-1 : ℝ) : ℂ) = 1 - s by push_cast; ring]
    exact h.1
  refine ⟨MellinConvergent.cpow_smul.mpr hconv, ?_⟩
  show mellin (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ) • f t⁻¹) s = m
  rw [mellin_cpow_smul, mellin_comp_inv, show -(s + -1) = 1 - s by ring]
  exact h.2

end RHTower.MaassGammaCorrections
