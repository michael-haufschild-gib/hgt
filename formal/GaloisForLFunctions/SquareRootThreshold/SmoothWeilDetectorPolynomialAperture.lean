import GaloisForLFunctions.SquareRootThreshold.VisibilityTradeoffAndExcludedDepthLaw
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# Smooth Weil detection at a polynomial aperture

The cluster horizon yields a negative finite-regularity source. Complete-form
mollification makes it smooth with aperture enlargement at most one. A coarse
quadratic radius pays the logarithmic horizon condition uniformly in the zero.
-/

open MeasureTheory Set Filter Topology Complex
open scoped CompactlySupported
open Zeta23
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.CHMDDoobGraph RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower
noncomputable section
set_option autoImplicit false

/-- A failed Hodge index has a smooth negative witness after enlarging the aperture by one. -/
theorem exists_smooth_weil_negative_of_not_hodgeIndex {a : ℝ}
    (h : ¬ HodgeIndexAtLevel zetaZeroConfig a) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Icc (-(a + 1)) (a + 1) ∧ (zetaZeroConfig.W f f).re < 0 := by
  classical
  have hn : ¬ ZetaWindowPositive a := fun hpos => h (hodgeIndexAtLevel_of_zetaWindowPositive hpos)
  unfold ZetaWindowPositive at hn
  push Not at hn
  obtain ⟨F, hF, hFc, hv, hneg⟩ := hn
  let fc : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  have hJ : IntegrableOn (fun x => (autocorr fc 0-autocorr fc x) * archLevySinhWeight x)
      (Ioi 0) := integrableOn_biScaleLevyIntegrand hF hFc
  have hsm := contDiff_top_smooth hF.continuous hFc
  have hsc := smooth_compact hFc
  have hlim := re_weilFullFunctional_smooth_tendsto fc hJ
  have hZ : Tendsto (fun k => fullZeroForm (smooth F k)) atTop (𝓝 (fullZeroForm F)) := by
    rw [fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc]
    refine hlim.congr fun k => ?_
    exact (fullZeroForm_eq_re_weilFullFunctional (hsm k).continuous (hsc k)).symm
  obtain ⟨k, hk⟩ := (hZ.eventually (Iio_mem_nhds hneg)).exists
  let f : ℝ → ℂ := fun x => (smooth F k x : ℂ)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := Complex.ofRealCLM.contDiff.comp (hsm k)
  have hfc : HasCompactSupport f := (hsc k).comp_left Complex.ofReal_zero
  refine ⟨f, hf, hfc, ?_, ?_⟩
  · refine closure_minimal (fun x hx => ?_) isClosed_Icc
    have hr : 1 / (4 * ((k : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith only [Nat.cast_nonneg (α := ℝ) k]
    apply abs_le.mp
    by_contra hh
    have ha : a + 1 < |x| := lt_of_not_ge hh
    have hz := smooth_eq_zero_of_radius_lt_abs hv k (by linarith only [ha, hr])
    exact hx (by simp only [f, hz, Complex.ofReal_zero])
  · rw [zeta_W_eq_weilFullFunctional (hf.of_le (by norm_cast)) hfc]
    rw [← fullZeroForm_eq_re_weilFullFunctional (hsm k).continuous (hsc k)]
    exact hk

private theorem log_sq_le_sixteen_sqrt {u : ℝ} (hu : 1 ≤ u) :
    Real.log (u ^ 2) ^ 2 ≤ 16 * u := by
  have hu0 : 0 < u := by linarith only [hu]
  have ha : 0 < u ^ 2 := by positivity
  have hl0 : 0 ≤ Real.log (u ^ 2) := Real.log_nonneg (by nlinarith only [hu])
  have hl : Real.log (u ^ 2) ≤ 4 * (u ^ 2) ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div ha.le (show (0 : ℝ) < 1 / 4 by norm_num)
    linarith only [h]
  have hsq := pow_le_pow_left₀ hl0 hl 2
  have hp : ((u ^ 2) ^ (1 / 4 : ℝ)) ^ 2 = u := by
    rw [← Real.rpow_natCast ((u ^ 2) ^ (1 / 4 : ℝ)) 2,
      ← Real.rpow_mul ha.le,
      show (1 / 4 : ℝ) * (2 : ℕ) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hu0.le]
  rw [mul_pow, hp] at hsq
  nlinarith only [hsq]

private theorem polynomial_radius_conditions {A K δ γ : ℝ} (hA : 1 ≤ A)
    (hK : Real.exp 6 + 1000000000 * (A + 1) ≤ K)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let u := K * (4 + |γ|) / δ
    Real.exp 6 ≤ u ^ 2 ∧ 1 / δ ≤ u ^ 2 ∧
      10 ^ 5 * A * Real.log (|γ| + 306) * Real.log (u ^ 2) ^ 2 ≤ u ^ 2 := by
  dsimp only
  have hA0 : 0 ≤ A := by linarith only [hA]
  have he : 1 ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
  have hK1 : 1 ≤ K := by linarith only [hK, hA, he]
  have hK0 : 0 ≤ K := by linarith only [hK1]
  have hH : 4 ≤ 4 + |γ| := by linarith only [abs_nonneg γ]
  have hKH : 1 ≤ K * (4 + |γ|) := by nlinarith only [hK1, hH]
  have huKH : K * (4 + |γ|) ≤ K * (4 + |γ|) / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith only [mul_nonneg (show 0 ≤ K * (4 + |γ|) by positivity)
      (sub_nonneg.mpr hδ1)]
  have hu1 : 1 ≤ K * (4 + |γ|) / δ := hKH.trans huKH
  have huK : K ≤ K * (4 + |γ|) / δ := by
    have hx := mul_nonneg hK0 (show 0 ≤ 4 + |γ| - 1 by linarith only [hH])
    nlinarith only [huKH, hx]
  have husq : K * (4 + |γ|) / δ ≤ (K * (4 + |γ|) / δ) ^ 2 := by
    nlinarith only [hu1]
  have hd : 1 / δ ≤ K * (4 + |γ|) / δ := div_le_div_of_nonneg_right hKH hδ.le
  have hlog : Real.log (|γ| + 306) ≤ 77 * (4 + |γ|) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < |γ| + 306 by positivity)
    linarith only [h, abs_nonneg γ]
  have hlog0 : 0 ≤ Real.log (|γ| + 306) := Real.log_nonneg (by linarith only [abs_nonneg γ])
  have hAK : 16 * 10 ^ 5 * A * 77 ≤ K := by linarith only [hK, hA, he]
  have hpay : 16 * 10 ^ 5 * A * Real.log (|γ| + 306) ≤ K * (4 + |γ|) / δ := by
    have h₁ := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 16 * 10 ^ 5 * A by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hAK (show 0 ≤ 4 + |γ| by positivity)
    nlinarith only [h₁, h₂, huKH]
  have hlsq := log_sq_le_sixteen_sqrt hu1
  have hmul := mul_le_mul_of_nonneg_left hlsq
    (show 0 ≤ 10 ^ 5 * A * Real.log (|γ| + 306) by positivity)
  have hpaymul := mul_le_mul_of_nonneg_right hpay
    (show 0 ≤ K * (4 + |γ|) / δ by positivity)
  exact ⟨by linarith only [hK, hA, huK, husq], hd.trans husq,
    by nlinarith only [hmul, hpaymul]⟩

/-- The cluster horizon gives a smooth negative witness with quadratic depth and height cost. -/
theorem exists_smooth_weil_negative_quadratic_aperture :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      ∃ a : ℝ, 0 < a ∧ a ≤ C / |ρ.re - 1 / 2| ^ 2 * (4 + |ρ.im|) ^ 2 ∧
        ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
          tsupport f ⊆ Icc (-a) a ∧ (zetaZeroConfig.W f f).re < 0 := by
  obtain ⟨A, hA, hhorizon⟩ := zeta_hodge_index_cluster_horizon
  let K := Real.exp 6 + 1000000000 * (A + 1)
  have hK : 1 ≤ K := by
    have he := Real.one_le_exp (show (0 : ℝ) ≤ 6 by norm_num)
    dsimp [K]
    linarith only [hA, he]
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨2 * K ^ 2, by positivity, fun ρ hρ hne => ?_⟩
  have hδ : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hδ1 : |ρ.re - 1 / 2| ≤ 1 := abs_le.mpr ⟨by linarith [hρ.2.1], by linarith [hρ.2.2]⟩
  have hheight : 2 ≤ |ρ.im| := by
    by_contra h
    have hs : ρ.im ^ 2 ≤ 32 := by
      have hh : |ρ.im| ≤ 2 := (lt_of_not_ge h).le
      have hp := pow_le_pow_left₀ (abs_nonneg ρ.im) hh 2
      rw [sq_abs] at hp
      linarith only [hp]
    have hρ1 : ρ ≠ 1 := fun he => (ne_of_lt hρ.2.2) (congrArg Complex.re he)
    exact riemannZeta_ne_zero_of_im_sq_le hρ1 hρ.2.1 hs hρ.1
  let u := K * (4 + |ρ.im|) / |ρ.re - 1 / 2|
  have hu : 0 < u := by dsimp [u]; positivity
  obtain ⟨h6, hd, hsize⟩ := polynomial_radius_conditions hA
    (show Real.exp 6 + 1000000000 * (A + 1) ≤ K from le_rfl) hδ hδ1
  have hfail := hhorizon _ hδ ρ hρ le_rfl hheight (u ^ 2) h6 hd hsize
  obtain ⟨f, hf, hfc, hfs, hn⟩ := exists_smooth_weil_negative_of_not_hodgeIndex hfail
  refine ⟨u ^ 2 + 1, by positivity, ?_, f, hf, hfc, hfs, hn⟩
  have hu1 : 1 ≤ u ^ 2 := (Real.one_le_exp (show (0 : ℝ) ≤ 6 by norm_num)).trans h6
  calc
    u ^ 2 + 1 ≤ 2 * u ^ 2 := by linarith only [hu1]
    _ = (2 * K ^ 2 / |ρ.re - 1 / 2| ^ 2) * (4 + |ρ.im|) ^ 2 := by
      dsimp [u]
      rw [div_pow, mul_pow]
      ring

/-- In particular the smooth detector satisfies the degree-thirty-eight aperture bound. -/
theorem exists_smooth_weil_negative_polynomial_aperture :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      ∃ a : ℝ, 0 < a ∧ a ≤ C / |ρ.re - 1 / 2| ^ 2 * (4 + |ρ.im|) ^ 38 ∧
        ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
          tsupport f ⊆ Icc (-a) a ∧ (zetaZeroConfig.W f f).re < 0 := by
  obtain ⟨C,hC,hdet⟩ := exists_smooth_weil_negative_quadratic_aperture
  refine ⟨C,hC,fun ρ hρ hne => ?_⟩
  obtain ⟨a,ha,hbound,f,hf,hfc,hfs,hneg⟩ := hdet ρ hρ hne
  refine ⟨a,ha,hbound.trans ?_,f,hf,hfc,hfs,hneg⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_right₀ (by linarith only [abs_nonneg ρ.im]) (by norm_num)

end
end RHTower
