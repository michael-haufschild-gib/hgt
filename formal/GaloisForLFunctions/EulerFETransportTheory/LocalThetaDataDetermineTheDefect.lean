import GaloisForLFunctions.RHTower.HamburgerStabilityCriticalLine
import GaloisForLFunctions.RHTower.ExpDecayFourierAnalytic

/-!
# Local theta data determine the uncompleted functional-equation defect

Gamma damping makes every polynomially bounded defect exponentially integrable.
The actual Hamburger theta kernel, in logarithmic scale, is its Fourier transform.
Analytic continuation and Fourier injectivity therefore recover the whole defect
from any open interval of positive scales. No unweighted integrability is needed.
-/

open Complex Filter Topology Set MeasureTheory
open RHTower RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- The integrable source of the theta defect in logarithmic coordinates. -/
def gammaWeightedDefect (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * g t

private theorem polynomial_exponential_bound (n : ℕ) (t : ℝ) :
    (1 + |t|) ^ n * Real.exp (-|t|) ≤
      (2 ^ n * (n.factorial : ℝ) * Real.exp (1 / 2)) * Real.exp (-(|t| / 2)) := by
  have h := pow_abs_mul_exp_neg_le (by norm_num : (0 : ℝ) < 1) n (1 + |t|)
  rw [abs_of_pos (by positivity : 0 < 1 + |t|)] at h
  norm_num only [div_one, one_mul] at h
  have he : Real.exp (-(1 + |t|)) * Real.exp 1 = Real.exp (-|t|) := by
    rw [← Real.exp_add]; congr 1; ring
  have he' : Real.exp (-(1 / 2 * (1 + |t|))) * Real.exp 1 =
      Real.exp (1 / 2) * Real.exp (-(|t| / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_nonneg 1)
  simpa only [mul_assoc, he, he'] using hh

/-- Polynomial growth is absorbed by Gamma decay before the theta transform. -/
theorem gammaWeightedDefect_exponential_bound {g : ℝ → ℂ} {C : ℝ} {N : ℕ}
    (hgb : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t, ‖gammaWeightedDefect g t‖ ≤
      K * Real.exp (-((1 / 2 : ℝ) * |t|)) := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hgb 0)
  obtain ⟨A, M, hA, hΓ⟩ := exists_bound_Gammaℝ_quarter_line
  refine ⟨A * C * (2 ^ (M + N) * ((M + N).factorial : ℝ) * Real.exp (1 / 2)),
    by positivity, fun t => ?_⟩
  calc ‖gammaWeightedDefect g t‖
      ≤ (A * (1 + |t|) ^ M * Real.exp (-(1 * |t|))) * (C * (1 + |t|) ^ N) := by
        rw [gammaWeightedDefect, norm_mul]
        exact mul_le_mul (hΓ t) (hgb t) (norm_nonneg _) (by positivity)
    _ = A * C * ((1 + |t|) ^ (M + N) * Real.exp (-|t|)) := by
        rw [pow_add]; ring
    _ ≤ A * C * ((2 ^ (M + N) * ((M + N).factorial : ℝ) * Real.exp (1 / 2)) *
        Real.exp (-(|t| / 2))) :=
      mul_le_mul_of_nonneg_left (polynomial_exponential_bound (M + N) t) (by positivity)
    _ = _ := by rw [show |t| / 2 = (1 / 2 : ℝ) * |t| by ring]; ring

/-- Exact Fourier normalization of the actual theta kernel. -/
theorem defectKernel_exp_eq_fourier (g : ℝ → ℂ) (u : ℝ) :
    defectKernel g (Real.exp u) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      Complex.exp (-(u : ℂ) / 4) * expFourier (gammaWeightedDefect g) u := by
  have hp (t : ℝ) : ((Real.exp u : ℝ) : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) =
      Complex.exp (-(u : ℂ) / 4) * Complex.exp (-(I * (u : ℂ) * t)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
      ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [defectKernel, hp, expFourier]
  conv_rhs => rw [mul_assoc, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp only [gammaWeightedDefect]
  ring

private theorem real_interval_frequently {a b : ℝ} (hab : a < b)
    {P : ℂ → Prop} (hP : ∀ u ∈ Ioo a b, P (u : ℂ)) :
    ∃ c : ℝ, ∃ᶠ z in 𝓝[≠] (c : ℂ), P z := by
  let c : ℝ := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp [c]; constructor <;> linarith
  have he : ∀ᶠ (u : ℝ) in 𝓝[≠] c, P (u : ℂ) :=
    (eventually_nhdsWithin_of_eventually_nhds (Ioo_mem_nhds hc.1 hc.2)).mono
      (fun u hu => hP u hu)
  have ht : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[≠] c) (𝓝[≠] (c : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_ofReal.tendsto c).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj] using hu
  exact ⟨c, ht.frequently he.frequently⟩

private theorem ae_eq_zero_of_expFourier_local {f : ℝ → ℂ}
    (hfm : AEStronglyMeasurable f volume) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ t, ‖f t‖ ≤ K * Real.exp (-((1 / 2 : ℝ) * |t|)))
    {a b : ℝ} (hab : a < b) (hz : ∀ u ∈ Ioo a b, expFourier f u = 0) :
    f =ᵐ[volume] 0 := by
  obtain ⟨c, hc⟩ := real_interval_frequently (P := fun z => expFourier f z = 0) hab hz
  have ha := analyticOnNhd_expFourier hfm hK hb
  have he := ha.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_imStrip (1 / 2)).isPreconnected (by simp : |(c : ℂ).im| < (1 / 2 : ℝ)) hc
  apply integrable_ae_eq_zero_of_fourier_eq_zero
    (integrable_of_expDecay hfm (by norm_num) hb)
  intro w
  have hh : expFourier f ((2 * Real.pi * w : ℝ) : ℂ) = 0 :=
    he (by simp)
  rw [Real.fourier_real_eq_integral_exp_smul, ← hh, expFourier]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

/-- Vanishing on one open scale interval annihilates the entire polynomial-growth
defect, even when its unweighted mass and energy are infinite. -/
theorem ae_eq_zero_of_defectKernel_eq_zero_on_interval {g : ℝ → ℂ} {C : ℝ} {N : ℕ}
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ N)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hz : ∀ x ∈ Ioo a b, defectKernel g x = 0) : g =ᵐ[volume] 0 := by
  obtain ⟨K, hK, hb⟩ := gammaWeightedDefect_exponential_bound hgb
  have hfm : AEStronglyMeasurable (gammaWeightedDefect g) volume :=
    continuous_Gammaℝ_quarter_line.aestronglyMeasurable.mul hgm.aestronglyMeasurable
  have hlog : Real.log a < Real.log b := Real.log_lt_log ha hab
  have hF : gammaWeightedDefect g =ᵐ[volume] 0 :=
    ae_eq_zero_of_expFourier_local hfm hK hb hlog (fun u hu => by
      have hx : Real.exp u ∈ Ioo a b := ⟨(Real.log_lt_iff_lt_exp ha).mp hu.1,
        by simpa only [Real.exp_log (ha.trans hab)] using Real.exp_lt_exp.mpr hu.2⟩
      have hh := hz _ hx
      rw [defectKernel_exp_eq_fourier] at hh
      exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero
        (by exact_mod_cast (one_div_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
          Real.pi_ne_zero))) (Complex.exp_ne_zero _)))
  filter_upwards [hF] with t ht
  exact (mul_eq_zero.mp ht).resolve_left
    (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))

/-- The actual theta kernel depends only on the almost-everywhere defect class. -/
theorem defectKernel_congr_ae {g h : ℝ → ℂ} (he : g =ᵐ[volume] h) (x : ℝ) :
    defectKernel g x = defectKernel h x := by
  unfold defectKernel
  congr 1
  apply integral_congr_ae
  filter_upwards [he] with t ht
  rw [ht]

/-- An open interval of actual theta data identifies any two polynomially bounded
defects. This is injectivity of the local measurement, with no finite-cost premise. -/
theorem ae_eq_of_defectKernel_eq_on_interval {g h : ℝ → ℂ} {Cg Ch : ℝ} {Ng Nh : ℕ}
    (hgm : Measurable g) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ Ng)
    (hhm : Measurable h) (hhb : ∀ t, ‖h t‖ ≤ Ch * (1 + |t|) ^ Nh)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (he : ∀ x ∈ Ioo a b, defectKernel g x = defectKernel h x) :
    g =ᵐ[volume] h := by
  obtain ⟨Kg, hKg, hBg⟩ := gammaWeightedDefect_exponential_bound hgb
  obtain ⟨Kh, hKh, hBh⟩ := gammaWeightedDefect_exponential_bound hhb
  have hGm : AEStronglyMeasurable (gammaWeightedDefect g) volume :=
    continuous_Gammaℝ_quarter_line.aestronglyMeasurable.mul hgm.aestronglyMeasurable
  have hHm : AEStronglyMeasurable (gammaWeightedDefect h) volume :=
    continuous_Gammaℝ_quarter_line.aestronglyMeasurable.mul hhm.aestronglyMeasurable
  have hbound (t : ℝ) : ‖gammaWeightedDefect g t - gammaWeightedDefect h t‖ ≤
      (Kg + Kh) * Real.exp (-((1 / 2 : ℝ) * |t|)) :=
    (norm_sub_le _ _).trans ((add_le_add (hBg t) (hBh t)).trans_eq (by ring))
  have hzero : (fun t => gammaWeightedDefect g t - gammaWeightedDefect h t) =ᵐ[volume] 0 :=
    ae_eq_zero_of_expFourier_local (hGm.sub hHm) (add_nonneg hKg hKh) hbound
      (Real.log_lt_log ha hab) (fun u hu => by
        have hx : Real.exp u ∈ Ioo a b := ⟨(Real.log_lt_iff_lt_exp ha).mp hu.1,
          by simpa only [Real.exp_log (ha.trans hab)] using Real.exp_lt_exp.mpr hu.2⟩
        have hh := he _ hx
        rw [defectKernel_exp_eq_fourier, defectKernel_exp_eq_fourier] at hh
        have hc : ((1 / (2 * Real.pi) : ℝ) : ℂ) * Complex.exp (-(u : ℂ) / 4) ≠ 0 :=
          mul_ne_zero (by exact_mod_cast (one_div_ne_zero
            (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))) (Complex.exp_ne_zero _)
        have hEq := mul_left_cancel₀ hc hh
        have hIg := integrable_expFourier_kernel hGm hKg hBg (w := (u : ℂ)) (by simp)
        have hIh := integrable_expFourier_kernel hHm hKh hBh (w := (u : ℂ)) (by simp)
        unfold expFourier
        simp_rw [sub_mul]
        rw [integral_sub hIg hIh]
        exact sub_eq_zero.mpr hEq)
  filter_upwards [hzero] with t ht
  have ht' : gammaWeightedDefect g t = gammaWeightedDefect h t := sub_eq_zero.mp ht
  exact mul_left_cancel₀ (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)) ht'

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.gammaWeightedDefect_exponential_bound
#print axioms GaloisForLFunctions.EulerFETransportTheory.defectKernel_exp_eq_fourier
#print axioms GaloisForLFunctions.EulerFETransportTheory.ae_eq_zero_of_defectKernel_eq_zero_on_interval
#print axioms GaloisForLFunctions.EulerFETransportTheory.ae_eq_of_defectKernel_eq_on_interval
