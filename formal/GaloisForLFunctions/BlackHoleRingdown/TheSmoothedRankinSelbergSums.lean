import GaloisForLFunctions.BlackHoleRingdown.TheGrowthOfTheRankinSelbergLFunction
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateIsTheZeroFreeRegion
import GaloisForLFunctions.RHTower.SmoothAFELogGaussianMoment
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelKernelInversion
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinFaithful
import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversionGeneralLine

/-!
# Smoothed Rankin–Selberg sums with a power saving

For a cusp form `g` with Whittaker coefficients `ρ(n)` let `f(m) = |ρ(m)|² + |ρ(-m)|²`, `A = (24/π²) cosh(πt)‖g‖²`
the mean-square constant, and `φ_Δ(u) = G(log u/Δ)/Δ` the log-Gaussian of width `Δ`
(`G(y) = e^{-y²/4}/(2√π)`, so `φ̃_Δ(w) = e^{Δ² w²}`). The smoothed sum `S_Δ(y) = Σ_m f(m) φ_Δ(m y)` satisfies,
for all `0 < Δ ≤ 1` and `y > 0` (`norm_smSum_sub_le`),

  `|S_Δ(y) - A e^{Δ²} y⁻¹ e^{-y}| ≤ K Δ^{-(N+1)} y^{-3/4}`,

with `K, N` depending only on `g`. With `X = 1/y`: `Σ_m f(m) φ_Δ(m/X) = A e^{Δ²} X e^{-1/X} + O(Δ^{-N-1} X^{3/4})`, a
power saving in `X` with polynomial dependence on the width.

**Proof.** Mellin inversion of `φ_Δ` termwise and Fubini give `S_Δ = 𝓜⁻¹_{9/8}(L_f · e^{Δ²w²})`, and
`y⁻¹e^{-y} = 𝓜⁻¹_{9/8}Γ(w-1)`. With `L_f = φ_g/(w-1)` and `Γ(w) = (w-1)Γ(w-1)` the difference is `𝓜⁻¹_{9/8}Ψ_Δ`,
`Ψ_Δ = dslope(φ_g e^{Δ²w²} - A e^{Δ²} Γ) 1`, holomorphic on `Re w > ½` and rapidly decaying (polynomial growth of
`φ_g`, Gaussian decay of `e^{Δ²w²}`, exponential decay of `Γ`). Shift to `Re w = 3/4`: on that line
`|Ψ_Δ| ≤ 4e(C(1+|t|)^N e^{-Δ²t²} + A|Γ(¾+it)|)` and `∫(1+|t|)^N e^{-Δ²t²} dt ≤ Δ^{-N-1}∫(1+|v|)^N e^{-v²} dv`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair

namespace CuspSRS

open HeckeCusp CuspL CuspRSC CuspMS CuspRSV CuspRSL

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-! ### The log-Gaussian weight -/

/-- `φ_Δ(u) = G(log u / Δ)/Δ`, `G(y) = e^{-y²/4}/(2√π)`. -/
def lgW (Δ : ℝ) (u : ℝ) : ℂ := ((smoothAFELogGaussian (Real.log u / Δ) / Δ : ℝ) : ℂ)

theorem lgW_exp (Δ t : ℝ) : lgW Δ (Real.exp t) = ((smoothAFELogGaussian (t / Δ) / Δ : ℝ) : ℂ) := by
  simp [lgW, Real.log_exp]

theorem smoothAFELogGaussian_nonneg (y : ℝ) : 0 ≤ smoothAFELogGaussian y := by
  unfold smoothAFELogGaussian; positivity

theorem continuous_smoothAFELogGaussian : Continuous smoothAFELogGaussian := by
  unfold smoothAFELogGaussian; fun_prop

theorem integrable_exp_mul_lgW {Δ : ℝ} (hΔ : 0 < Δ) (w : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (w * t) * lgW Δ (Real.exp t)) := by
  have h := (integrable_smoothAFELogGaussian_mul_exp (w * Δ)).comp_div hΔ.ne'
  refine (h.div_const (Δ : ℂ)).congr (Eventually.of_forall fun t => ?_)
  have hΔC : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ.ne'
  simp only [lgW_exp]
  rw [show w * (Δ : ℂ) * ((t / Δ : ℝ) : ℂ) = w * t by push_cast; field_simp]
  push_cast
  ring_nf

theorem mellinConvergent_lgW {Δ : ℝ} (hΔ : 0 < Δ) (w : ℂ) : MellinConvergent (lgW Δ) w := by
  unfold MellinConvergent
  rw [integrableOn_Ioi_iff_integrable_exp_smul]
  refine (integrable_exp_mul_lgW hΔ w).congr (Eventually.of_forall fun u => ?_)
  simp only [Complex.real_smul, smul_eq_mul]
  rw [RHTower.ofReal_rexp_cpow_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem mellin_lgW {Δ : ℝ} (hΔ : 0 < Δ) (w : ℂ) :
    mellin (lgW Δ) w = Complex.exp (Δ ^ 2 * w ^ 2) := by
  have hΔC : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hΔ.ne'
  rw [mellin_eq_integral_exp_mul_log]
  have hsub := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => Complex.exp (w * t) * lgW Δ (Real.exp t)) Δ
  rw [abs_inv, abs_of_pos hΔ, Complex.real_smul] at hsub
  have e : ∫ t : ℝ, Complex.exp (w * t) * lgW Δ (Real.exp t) =
      (Δ : ℂ) * ∫ y : ℝ, Complex.exp (w * ((Δ * y : ℝ) : ℂ)) * lgW Δ (Real.exp (Δ * y)) := by
    rw [hsub]; push_cast; field_simp
  have e2 : ∀ y : ℝ, Complex.exp (w * ((Δ * y : ℝ) : ℂ)) * lgW Δ (Real.exp (Δ * y)) =
      (smoothAFELogGaussian y : ℂ) * Complex.exp (w * Δ * y) / Δ := by
    intro y
    rw [lgW_exp, mul_div_cancel_left₀ y hΔ.ne']
    push_cast
    ring_nf
  rw [e]
  simp_rw [e2]
  rw [integral_div, integral_smoothAFELogGaussian_mul_exp,
    show (Δ : ℂ) * (Complex.exp ((w * Δ) ^ 2) / Δ) = Complex.exp ((w * Δ) ^ 2) by field_simp]
  congr 1
  ring

theorem continuousAt_lgW {Δ u : ℝ} (hu : 0 < u) : ContinuousAt (lgW Δ) u := by
  unfold lgW
  refine Complex.continuous_ofReal.continuousAt.comp ?_
  exact ((continuous_smoothAFELogGaussian.continuousAt.comp
    ((Real.continuousAt_log hu.ne').div_const Δ)).div_const Δ)

theorem norm_exp_sq {Δ : ℝ} (w : ℂ) :
    ‖Complex.exp (Δ ^ 2 * w ^ 2)‖ = Real.exp (Δ ^ 2 * (w.re ^ 2 - w.im ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [sq, Complex.mul_re]

theorem verticalIntegrable_exp_sq {Δ : ℝ} (hΔ : 0 < Δ) (c : ℝ) :
    Complex.VerticalIntegrable (fun w => Complex.exp (Δ ^ 2 * w ^ 2)) c := by
  unfold Complex.VerticalIntegrable
  have hb : 0 < Δ ^ 2 := by positivity
  refine ((integrable_exp_neg_mul_sq hb).const_mul (Real.exp (Δ ^ 2 * c ^ 2))).mono' (by fun_prop)
    (Eventually.of_forall fun t => ?_)
  rw [norm_exp_sq]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
    add_im, mul_im, zero_add]
  rw [← Real.exp_add]
  apply le_of_eq; congr 1; ring

/-- **Mellin inversion of the weight**: `φ_Δ(u) = 𝓜⁻¹_c e^{Δ² w²}(u)` for `u > 0`. -/
theorem lgW_eq_mellinInv {Δ : ℝ} (hΔ : 0 < Δ) (c : ℝ) {u : ℝ} (hu : 0 < u) :
    lgW Δ u = mellinInv c (fun w => Complex.exp (Δ ^ 2 * w ^ 2)) u := by
  have hfun : mellin (lgW Δ) = fun w => Complex.exp (Δ ^ 2 * w ^ 2) := funext (mellin_lgW hΔ)
  have h := mellinInv_mellin_eq c (lgW Δ) hu (mellinConvergent_lgW hΔ c)
    (by rw [hfun]; exact verticalIntegrable_exp_sq hΔ c) (continuousAt_lgW hu)
  rw [hfun] at h
  exact h.symm

/-! ### The smoothed sum as a Mellin inverse -/

/-- `S_Δ(y) = Σ_m f(m) φ_Δ(m y)`. -/
def smSum (ρ : ℤ → ℂ) (Δ y : ℝ) : ℂ := ∑' m : ℕ, ((rsCoeff ρ m : ℝ) : ℂ) * lgW Δ (m * y)

theorem rsCoeff_nonneg (m : ℕ) : 0 ≤ rsCoeff ρ m := by unfold rsCoeff; positivity

theorem rsCoeff_zero (hρ0 : ρ 0 = 0) : rsCoeff ρ 0 = 0 := by simp [rsCoeff, hρ0]

/-- `S_Δ(y) = 𝓜⁻¹_c (L_f · e^{Δ²w²})(y)` for `c > 1`. -/
theorem smSum_eq_mellinInv (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {Δ : ℝ} (hΔ : 0 < Δ) {c : ℝ}
    (hc : 1 < c) {y : ℝ} (hy : 0 < y) :
    smSum ρ Δ y = mellinInv c (fun w => LSeries (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) w *
      Complex.exp (Δ ^ 2 * w ^ 2)) y := by
  set F : ℕ → ℝ → ℂ := fun m t => ((rsCoeff ρ m : ℝ) : ℂ) *
    ((((m : ℝ) * y : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) * Complex.exp (Δ ^ 2 * ((c : ℂ) + t * I) ^ 2))
    with hF
  have hterm : ∀ m : ℕ, ((rsCoeff ρ m : ℝ) : ℂ) * lgW Δ (m * y) =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, F m t := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, rsCoeff_zero hρ0]
    · have hmy : 0 < (m : ℝ) * y := mul_pos (by exact_mod_cast hm) hy
      rw [lgW_eq_mellinInv hΔ c hmy, mellinInv, mul_smul_comm, ← integral_const_mul]
      congr 1
  have hGauss : Integrable (fun t : ℝ => Real.exp (Δ ^ 2 * (c ^ 2 - t ^ 2))) := by
    have hb : 0 < Δ ^ 2 := by positivity
    refine ((integrable_exp_neg_mul_sq hb).const_mul (Real.exp (Δ ^ 2 * c ^ 2))).congr
      (Eventually.of_forall fun t => ?_)
    simp only; rw [← Real.exp_add]; congr 1; ring
  have hnormF : ∀ m : ℕ, ∀ t : ℝ, ‖F m t‖ = rsCoeff ρ m * ((m : ℝ) * y) ^ (-c) *
      Real.exp (Δ ^ 2 * (c ^ 2 - t ^ 2)) := by
    intro m t
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, rsCoeff_zero hρ0]
    · have hmy : 0 < (m : ℝ) * y := mul_pos (by exact_mod_cast hm) hy
      simp only [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (rsCoeff_nonneg m),
        norm_cpow_eq_rpow_re_of_pos hmy, norm_exp_sq]
      simp
      ring
  have hFint : ∀ m : ℕ, Integrable (F m) := by
    intro m
    refine (hGauss.const_mul (rsCoeff ρ m * ((m : ℝ) * y) ^ (-c))).mono' ?_
      (Eventually.of_forall fun t => le_of_eq (by rw [hnormF]))
    have : Continuous (F m) := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have h0 : F 0 = fun _ => 0 := by funext t; simp [hF, rsCoeff_zero hρ0]
        rw [h0]; exact continuous_const
      · have hmy : 0 < (m : ℝ) * y := mul_pos (by exact_mod_cast hm) hy
        refine continuous_const.mul ((continuous_const.cpow (by fun_prop) fun _ =>
          ofReal_mem_slitPlane.2 hmy).mul (by fun_prop))
    exact this.aestronglyMeasurable
  have hsumm : Summable fun m : ℕ => ∫ t : ℝ, ‖F m t‖ := by
    have hS := summable_nterm hg hρ0 hρ hc
    have heq : ∀ m : ℕ, ∫ t : ℝ, ‖F m t‖ = (y ^ (-c) * ∫ t : ℝ, Real.exp (Δ ^ 2 * (c ^ 2 - t ^ 2))) *
        nterm (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) c m := by
      intro m
      simp_rw [hnormF]
      rw [integral_const_mul]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [nterm, rsCoeff_zero hρ0]
      · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
        simp only [nterm, hm.ne', if_false, Complex.norm_real, Real.norm_of_nonneg (rsCoeff_nonneg m)]
        rw [Real.mul_rpow (Nat.cast_nonneg _) hy.le, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
        ring
    exact (hS.mul_left _).congr fun m => (heq m).symm
  have hint := integral_tsum_of_summable_integral_norm hFint hsumm
  unfold smSum mellinInv
  simp_rw [hterm]
  rw [tsum_const_smul'' (1 / (2 * Real.pi) : ℝ), hint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [hF, smul_eq_mul]
  -- `Σ_m f(m) (m y)^{-w} = y^{-w} L_f(w)`
  have h1 : ∀ i : ℕ, ((rsCoeff ρ i : ℝ) : ℂ) * ((((i : ℝ) * y : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) *
      Complex.exp (Δ ^ 2 * ((c : ℂ) + t * I) ^ 2)) = ((y : ℂ) ^ (-((c : ℂ) + t * I)) *
        Complex.exp (Δ ^ 2 * ((c : ℂ) + t * I) ^ 2)) *
        LSeries.term (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) ((c : ℂ) + t * I) i := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [rsCoeff_zero hρ0]
    · rw [LSeries.term_of_ne_zero hi.ne', ofReal_mul, mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) hy.le,
        cpow_neg, cpow_neg, div_eq_mul_inv]
      push_cast
      ring
  rw [tsum_congr h1, tsum_mul_left, LSeries]
  ring

/-- `y⁻¹ e^{-y} = 𝓜⁻¹_c Γ(w - 1)(y)` for `c > 1`. -/
theorem mellinInv_gamma_sub_one {c y : ℝ} (hc : 1 < c) (hy : 0 < y) :
    mellinInv c (fun w => Gamma (w - 1)) y = (y : ℂ)⁻¹ * Complex.exp (-(y : ℂ)) := by
  have h := GaloisForLFunctions.SelbergClass.mellinInv_line_Gamma_eq_exp_neg (c := c - 1)
    (by linarith) hy
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  have key : ∫ t : ℝ, (y : ℂ) ^ (-((c : ℂ) + t * I)) • Gamma ((c : ℂ) + t * I - 1) =
      (y : ℂ)⁻¹ * ∫ t : ℝ, (y : ℂ) ^ (-(((c - 1 : ℝ) : ℂ) + t * I)) • Gamma (((c - 1 : ℝ) : ℂ) + t * I) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    rw [show (((c - 1 : ℝ) : ℂ) + t * I) = (c : ℂ) + t * I - 1 by push_cast; ring,
      show -((c : ℂ) + t * I) = -1 + -((c : ℂ) + t * I - 1) by ring, cpow_add _ _ hy0, cpow_neg_one]
    ring
  calc mellinInv c (fun w => Gamma (w - 1)) y
      = (1 / (2 * Real.pi) : ℝ) • ((y : ℂ)⁻¹ * ∫ t : ℝ, (y : ℂ) ^ (-(((c - 1 : ℝ) : ℂ) + t * I)) •
          Gamma (((c - 1 : ℝ) : ℂ) + t * I)) := by
        unfold mellinInv; rw [key]
    _ = (y : ℂ)⁻¹ * mellinInv (c - 1) Gamma y := by unfold mellinInv; rw [mul_smul_comm]
    _ = (y : ℂ)⁻¹ * Complex.exp (-(y : ℂ)) := by rw [h]


/-! ### The regular part -/

/-- `N_Δ(w) = φ_g(w) e^{Δ²w²} - A e^{Δ²} Γ(w)`; `N_Δ(1) = 0`. -/
def numR (lamE : ℝ) (g : UpperHalfPlane → ℂ) (Δ : ℝ) (w : ℂ) : ℂ :=
  rsPhi lamE g w * Complex.exp (Δ ^ 2 * w ^ 2) - (msConst lamE g : ℂ) * Complex.exp (Δ ^ 2) * Gamma w

/-- `Ψ_Δ = dslope N_Δ 1`. -/
def regR (lamE : ℝ) (g : UpperHalfPlane → ℂ) (Δ : ℝ) (w : ℂ) : ℂ := dslope (numR lamE g Δ) 1 w

theorem numR_one {Δ : ℝ} : numR lamE g Δ 1 = 0 := by
  simp [numR, rsPhi_one, Complex.Gamma_one]

theorem regR_eq {Δ : ℝ} {w : ℂ} (hw : w ≠ 1) : regR lamE g Δ w = numR lamE g Δ w / (w - 1) := by
  rw [regR, dslope_of_ne _ hw, slope_def_field, numR_one, sub_zero]

theorem differentiableOn_numR (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) (Δ : ℝ) :
    DifferentiableOn ℂ (numR lamE g Δ) {w : ℂ | 1 / 2 < w.re} := by
  intro w hw
  have hw' : (1 : ℝ) / 2 < w.re := hw
  have hΓ : DifferentiableAt ℂ Gamma w := Complex.differentiableAt_Gamma w fun m hm => by
    have := congrArg Complex.re hm; simp at this; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold numR
  exact ((differentiableAt_rsPhi hg hρ0 hρ hw').mul (by fun_prop)).sub (hΓ.const_mul _)

theorem differentiableAt_regR (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) (Δ : ℝ) {w : ℂ} (hw : 1 / 2 < w.re) :
    DifferentiableAt ℂ (regR lamE g Δ) w := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) := hU.mem_nhds (by simp; norm_num)
  have hd := (Complex.differentiableOn_dslope h1).2 (differentiableOn_numR hg hρ0 hρ Δ)
  exact (hd w hw).differentiableAt (hU.mem_nhds hw)

/-- On `Re w > 1`: `Ψ_Δ(w) = L_f(w) e^{Δ²w²} - A e^{Δ²} Γ(w - 1)`. -/
theorem regR_eq_sub (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) (Δ : ℝ) {w : ℂ} (hw : 1 < w.re) :
    regR lamE g Δ w = LSeries (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) w * Complex.exp (Δ ^ 2 * w ^ 2) -
      (msConst lamE g : ℂ) * Complex.exp (Δ ^ 2) * Gamma (w - 1) := by
  have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
  have hw0 : w - 1 ≠ 0 := sub_ne_zero.2 hw1
  have hx : (w - 1) * (w - 1)⁻¹ = 1 := mul_inv_cancel₀ hw0
  rw [regR_eq hw1, numR, ← rsPhi_div_eq_LSeries hg hρ0 hρ hw,
    show Gamma w = (w - 1) * Gamma (w - 1) by rw [← Complex.Gamma_add_one (w - 1) hw0, sub_add_cancel]]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  linear_combination (-((msConst lamE g : ℂ) * Complex.exp (Δ ^ 2) * Gamma (w - 1))) * hx

theorem gauss_le_exp {Δ : ℝ} (hΔ : 0 < Δ) (t : ℝ) :
    -(Δ ^ 2 * t ^ 2) ≤ Real.pi ^ 2 / (16 * Δ ^ 2) - Real.pi * |t| / 2 := by
  have hsq : 0 ≤ (Δ * |t| - Real.pi / (4 * Δ)) ^ 2 := sq_nonneg _
  have e : (Δ * |t| - Real.pi / (4 * Δ)) ^ 2 =
      Δ ^ 2 * t ^ 2 - Real.pi * |t| / 2 + Real.pi ^ 2 / (16 * Δ ^ 2) := by
    rw [sub_sq, mul_pow, sq_abs]; field_simp; ring
  linarith

/-- **`Ψ_Δ` is regular** on `½ < Re w < 5/4`. -/
theorem mellinRegularStrip_regR (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {Δ : ℝ} (hΔ : 0 < Δ) :
    MellinRegularStrip (regR lamE g Δ) (1 / 2) (5 / 4) := by
  refine ⟨fun w hw _ => differentiableAt_regR hg hρ0 hρ Δ hw, fun a' b' ha' hb' K => ?_⟩
  have hbox : IsCompact (Icc a' b' ×ℂ Icc (-1 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hbox.exists_bound_of_continuousOn (f := regR lamE g Δ) (fun w hw =>
    (differentiableAt_regR hg hρ0 hρ Δ (by have := hw.1.1; linarith)).continuousAt.continuousWithinAt)
  obtain ⟨CR, NR, hCR, hR⟩ := exists_rsPhi_poly hg hρ0 hρ (a := a') ha'
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := GaloisForLFunctions.HTGeometry.exists_sharp_bound_norm_Gamma_strip a' b'
  set A := msConst lamE g
  set E₀ := Real.exp (Δ ^ 2 * (5 / 4) ^ 2) * Real.exp (Real.pi ^ 2 / (16 * Δ ^ 2))
  set Nn := NR + NΓ
  set Cn := CR * E₀ + ‖(A : ℂ) * Complex.exp (Δ ^ 2)‖ * CΓ
  obtain ⟨Ce, hCe, hCe'⟩ := exists_pow_mul_exp_le Nn K
  have hgauss : ∀ w : ℂ, a' ≤ w.re → w.re ≤ b' →
      ‖Complex.exp (Δ ^ 2 * w ^ 2)‖ ≤ E₀ * Real.exp (-(Real.pi * |w.im| / 2)) := by
    intro w h1 h2
    rw [norm_exp_sq]
    have e : E₀ * Real.exp (-(Real.pi * |w.im| / 2)) = Real.exp (Δ ^ 2 * (5 / 4) ^ 2 +
        Real.pi ^ 2 / (16 * Δ ^ 2) + -(Real.pi * |w.im| / 2)) := by
      simp only [E₀]; rw [Real.exp_add, Real.exp_add]
    rw [e]
    apply Real.exp_le_exp.2
    have hσ : w.re ^ 2 ≤ (5 / 4) ^ 2 := by nlinarith
    have hΔ2 : 0 ≤ Δ ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left hσ hΔ2
    have h4 := gauss_le_exp hΔ w.im
    nlinarith
  have hN : ∀ w : ℂ, a' ≤ w.re → w.re ≤ b' → 1 ≤ |w.im| →
      ‖numR lamE g Δ w‖ ≤ Cn * (1 + |w.im|) ^ Nn * Real.exp (-(Real.pi * |w.im| / 2)) := by
    intro w h1 h2 ht
    have hX : 1 ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
    have hR' := hR w h1 (by linarith)
    have hΓ' := hΓ w h1 h2 ht
    have hg' := hgauss w h1 h2
    have hp1 : (1 + |w.im|) ^ NR ≤ (1 + |w.im|) ^ Nn := pow_le_pow_right₀ hX (Nat.le_add_right _ _)
    have hp2 : |w.im| ^ NΓ ≤ (1 + |w.im|) ^ Nn :=
      (pow_le_pow_left₀ (abs_nonneg _) (by linarith) _).trans (pow_le_pow_right₀ hX (Nat.le_add_left _ _))
    unfold numR
    calc ‖rsPhi lamE g w * Complex.exp (Δ ^ 2 * w ^ 2) - (A : ℂ) * Complex.exp (Δ ^ 2) * Gamma w‖
        ≤ ‖rsPhi lamE g w‖ * ‖Complex.exp (Δ ^ 2 * w ^ 2)‖ +
          ‖(A : ℂ) * Complex.exp (Δ ^ 2)‖ * ‖Gamma w‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul (_ * _)]
      _ ≤ (CR * (1 + |w.im|) ^ NR) * (E₀ * Real.exp (-(Real.pi * |w.im| / 2))) +
          ‖(A : ℂ) * Complex.exp (Δ ^ 2)‖ * (CΓ * |w.im| ^ NΓ * Real.exp (-(Real.pi * |w.im| / 2))) := by
          gcongr
      _ ≤ (CR * (1 + |w.im|) ^ Nn) * (E₀ * Real.exp (-(Real.pi * |w.im| / 2))) +
          ‖(A : ℂ) * Complex.exp (Δ ^ 2)‖ * (CΓ * (1 + |w.im|) ^ Nn * Real.exp (-(Real.pi * |w.im| / 2))) := by
          gcongr
      _ = Cn * (1 + |w.im|) ^ Nn * Real.exp (-(Real.pi * |w.im| / 2)) := by simp only [Cn]; ring
  refine ⟨max (B * 2 ^ K) (Cn * 2 ^ Nn * Ce), fun w h1 h2 => ?_⟩
  have hden : 0 < (1 + w.im ^ 2) ^ K := by positivity
  rcases le_or_gt |w.im| 1 with ht | ht
  · have hmem : w ∈ Icc a' b' ×ℂ Icc (-1 : ℝ) 1 := by
      rw [mem_reProdIm]
      exact ⟨⟨h1, h2⟩, ⟨by linarith [neg_abs_le w.im], by linarith [le_abs_self w.im]⟩⟩
    have hpow : (1 + w.im ^ 2) ^ K ≤ 2 ^ K := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [abs_nonneg w.im, sq_abs w.im]
    rw [le_div_iff₀ hden]
    calc ‖regR lamE g Δ w‖ * (1 + w.im ^ 2) ^ K ≤ max B 0 * 2 ^ K := by
          gcongr
          · exact le_max_right _ _
          · exact (hB w hmem).trans (le_max_left _ _)
      _ ≤ max (B * 2 ^ K) (Cn * 2 ^ Nn * Ce) := by
          rcases le_total B 0 with hB0 | hB0
          · rw [max_eq_right hB0, zero_mul]
            exact le_max_of_le_left (by
              have : (0 : ℝ) ≤ 2 ^ K := by positivity
              nlinarith [(norm_nonneg _).trans (hB w hmem)])
          · rw [max_eq_left hB0]; exact le_max_left _ _
  · have hw0 : w ≠ 1 := fun h => by rw [h] at ht; simp at ht; linarith
    have hwn : 1 ≤ ‖w - 1‖ := by
      have := Complex.abs_im_le_norm (w - 1); simp at this; linarith
    have hNb := hN w h1 h2 ht.le
    have hX : 1 + |w.im| ≤ 2 * |w.im| := by linarith
    have hCn : 0 ≤ Cn := by positivity
    have hstep : (1 + |w.im|) ^ Nn ≤ 2 ^ Nn * |w.im| ^ Nn := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hX _
    have hfin := hCe' w.im ht.le
    rw [regR_eq hw0, norm_div]
    calc ‖numR lamE g Δ w‖ / ‖w - 1‖ ≤ ‖numR lamE g Δ w‖ := div_le_self (norm_nonneg _) hwn
      _ ≤ Cn * (1 + |w.im|) ^ Nn * Real.exp (-(Real.pi * |w.im| / 2)) := hNb
      _ ≤ Cn * (2 ^ Nn * |w.im| ^ Nn) * Real.exp (-(Real.pi * |w.im| / 2)) := by gcongr
      _ = Cn * 2 ^ Nn * (|w.im| ^ Nn * Real.exp (-(Real.pi * |w.im| / 2))) := by ring
      _ ≤ Cn * 2 ^ Nn * (Ce / (1 + w.im ^ 2) ^ K) := by gcongr
      _ = Cn * 2 ^ Nn * Ce / (1 + w.im ^ 2) ^ K := by ring
      _ ≤ max (B * 2 ^ K) (Cn * 2 ^ Nn * Ce) / (1 + w.im ^ 2) ^ K := by
          gcongr; exact le_max_right _ _

end CuspSRS

end GaloisForLFunctions.BlackHoleRingdown
