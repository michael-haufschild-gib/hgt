import GaloisForLFunctions.RHTower.DivisorContinuousUnitMoment
import GaloisForLFunctions.RHTower.ZetaPoleSplit
import GaloisForLFunctions.RHTower.RetainedPrimeDivisorConvolution
import GaloisForLFunctions.RHTower.ZetaChiLineSharp
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfLeftEdge

/-!
# Entire continuation and vertical bounds of the literal divisor source

The two Laurent poles cancel in the actual log-minus-divisor coefficient.
An entire divided-difference formula agrees with its full absolute L-series
and its existing conditional Dirichlet sum. On the reflected negative-half
line the source has quadratic growth; on the companion absolute half-plane
it is uniformly bounded. These are unconditional inputs for the paired
Mellin contour, not a claim of a physical signed mean asymptotic.
-/

noncomputable section
open Complex Filter Set Topology
namespace RHTower

/-- Entire continuation of the literal log-minus-divisor coefficient source. -/
def divisorSourceEntire (w : ℂ) : ℂ :=
  -deriv zetaRegularized w - zetaRegularized w ^ (2 : ℕ) - 2 * dslope zetaRegularized 1 w +
    2 * (Real.eulerMascheroniConstant : ℂ) * zetaRegularized w

/-- The two apparent Laurent poles of the literal source cancel completely. -/
theorem differentiable_divisorSourceEntire : Differentiable ℂ divisorSourceEntire := by
  have hds : Differentiable ℂ (dslope zetaRegularized 1) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 (1:ℂ))).mpr
      differentiable_zetaRegularized.differentiableOn
  exact (((differentiable_zetaRegularized.deriv.neg).sub
    (differentiable_zetaRegularized.pow 2)).sub (hds.const_mul 2)).add
      (differentiable_zetaRegularized.const_mul (2 * (Real.eulerMascheroniConstant : ℂ)))

private lemma regularized_deriv {w : ℂ} (hw : w≠1) :
    deriv zetaRegularized w = deriv riemannZeta w + 1/(w-1)^(2 : ℕ) := by
  have he : zetaRegularized =ᶠ[𝓝 w] (fun z => riemannZeta z-1/(z-1)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hw] with z hz
    exact zetaRegularized_of_ne hz
  rw [he.deriv_eq]
  have h := (differentiableAt_riemannZeta hw).hasDerivAt.sub
    ((hasDerivAt_const w (1:ℂ)).div ((hasDerivAt_id w).sub_const 1) (sub_ne_zero.mpr hw))
  simpa only [Pi.sub_def, Pi.div_def, id_eq, zero_mul, one_mul, zero_sub, neg_div, sub_neg_eq_add] using h.deriv

/-- Away from the filled pole this entire function is the literal zeta expression,
with no inverse zeta factor and no zero-free-region premise. -/
theorem divisorSourceEntire_eq {w : ℂ} (hw : w≠1) :
    divisorSourceEntire w = -deriv riemannZeta w-riemannZeta w^(2 : ℕ)+
      2*(Real.eulerMascheroniConstant:ℂ)*riemannZeta w := by
  rw [divisorSourceEntire, regularized_deriv hw, dslope_of_ne _ hw,
    slope_def_field, zetaRegularized_of_ne hw]
  have h1 : zetaRegularized 1=(Real.eulerMascheroniConstant:ℂ) := by
    simp [zetaRegularized]
  rw [h1]
  field_simp
  ring

/-- The exact completed source agrees with the original coefficient series
on its half-plane of absolute convergence. -/
theorem divisorSourceEntire_eq_LSeries {w : ℂ} (hw : 1<w.re) :
    divisorSourceEntire w = LSeries (fun n => (primeFreeDivisorIncrement n : ℂ)) w := by
  have hlog : LSeriesSummable (LSeries.logMul (1 : ℕ→ℂ)) w :=
    LSeriesSummable_logMul_of_lt_re (by
      rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hw)
  have hone : LSeriesSummable (1 : ℕ→ℂ) w := LSeriesSummable_one_iff.mpr hw
  have hdiv := Sieve.LSeriesSummable_card_divisors hw
  have hfun : (fun n => (primeFreeDivisorIncrement n : ℂ)) =
      LSeries.logMul (1 : ℕ→ℂ) - (fun n => (n.divisors.card : ℂ)) +
        (2*(Real.eulerMascheroniConstant:ℂ)) • (1 : ℕ→ℂ) := by
    ext n
    simp [primeFreeDivisorIncrement,LSeries.logMul,Complex.natCast_log]
  have he : LSeries (1 : ℕ→ℂ) =ᶠ[𝓝 w] riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with s hs
    exact LSeries_one_eq_riemannZeta hs
  have hd := LSeries_deriv (f := (1 : ℕ→ℂ)) (s := w) (by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hw)
  rw [he.deriv_eq] at hd
  rw [divisorSourceEntire_eq (by intro h; simp [h] at hw), hfun,
    LSeries_add (hlog.sub hdiv) (hone.smul _), LSeries_sub hlog hdiv,
    LSeries_smul, LSeries_one_eq_riemannZeta hw,
    Sieve.LSeries_card_divisors_eq_riemannZeta_sq hw]
  rw [hd]
  ring

/-- The entire source continues the already constructed divisor Dirichlet sum
throughout its original conditional-convergence half-plane. -/
theorem divisorSourceEntire_eq_divisorSourceDirichlet {w : ℂ} (hw : 1/2<w.re) :
    divisorSourceEntire w = divisorSourceDirichlet w := by
  have ha : AnalyticOnNhd ℂ divisorSourceEntire {s : ℂ | 1/2<s.re} :=
    fun s _ => differentiable_divisorSourceEntire.analyticAt s
  have he : divisorSourceEntire =ᶠ[𝓝 (2:ℂ)] divisorSourceDirichlet := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (3/2:ℝ)<(2:ℂ).re)] with s hs
    rw [divisorSourceEntire_eq_LSeries (by linarith), divisorSourceDirichlet_eq_LSeries hs]
  exact ha.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_divisorSourceDirichlet
    (convex_halfSpace_re_gt (1/2)).isPreconnected (by norm_num : (2:ℂ)∈{s : ℂ | 1/2<s.re})
    he hw

/-- Uniform boundedness of the actual source throughout the closed absolute
half-plane used by the companion Mellin factor. -/
theorem exists_bound_divisorSourceEntire_right :
    ∃ C : ℝ, 0≤C ∧ ∀w : ℂ, 3/2≤w.re → ‖divisorSourceEntire w‖≤C := by
  let b : ℕ→ℂ := fun n => (primeFreeDivisorIncrement n : ℂ)
  have hbase := (LSeriesSummable_primeFreeDivisorIncrement_right
    (s := 3/2) (by norm_num)).norm
  refine ⟨∑'n, ‖LSeries.term b (3/2) n‖, tsum_nonneg (fun n => norm_nonneg _), ?_⟩
  intro w hw
  rw [divisorSourceEntire_eq_LSeries (by linarith), LSeries]
  exact (norm_tsum_le_tsum_norm
    (LSeriesSummable_primeFreeDivisorIncrement_right (by linarith)).norm).trans
      (Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re b
        (by simpa using hw) n)
        (LSeriesSummable_primeFreeDivisorIncrement_right (by linarith)).norm hbase)

/-- The reflected literal source has only quadratic vertical growth on
Re(w)=-1/2, including its zeta derivative contribution. -/
theorem exists_bound_divisorSourceEntire_negative_half :
    ∃ C : ℝ, 0≤C ∧ ∀t : ℝ, 3≤|t| →
      ‖divisorSourceEntire ((-1/2:ℂ)+(t:ℂ)*I)‖ ≤ C*(1+|t|)^(2 : ℕ) := by
  obtain ⟨K,hK,hchi⟩ := exists_norm_zetaChi_line_le (σ := -1/2) (by norm_num)
  let C : ℝ := 160*Real.exp 4+(3*K)^(2 : ℕ)+6*|Real.eulerMascheroniConstant| *K
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  let w : ℂ := (-1/2:ℂ)+(t:ℂ)*I
  have hz : ‖riemannZeta w‖≤3*K*(1+|t|) := by
    have hc := hchi t (by linarith)
    norm_num at hc
    have hr := Sieve.norm_riemannZeta_le (s := 1-w) (by norm_num [w])
    norm_num [w] at hr
    have hw0 : w≠0 := by intro h; have := congrArg Complex.re h; norm_num [w] at this
    have hw1 : w≠1 := by intro h; have := congrArg Complex.re h; norm_num [w] at this
    rw [zeta_eq_zetaChi_mul hw0 hw1 (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num [w])), norm_mul]
    calc
      _ ≤ (K*|t|)*3 := mul_le_mul (by convert hc using 1 <;> first | rfl | norm_num [w])
        (by convert hr using 1 <;> first | rfl | norm_num [w]) (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith [abs_nonneg t]
  have hd := Sieve.norm_deriv_riemannZeta_negative_half_le ht
  have hw1 : w≠1 := by intro h; have := congrArg Complex.re h; norm_num [w] at this
  rw [divisorSourceEntire_eq hw1]
  have hnorm : ‖-deriv riemannZeta w-riemannZeta w^(2 : ℕ)+
      2*(Real.eulerMascheroniConstant:ℂ)*riemannZeta w‖ ≤
      ‖deriv riemannZeta w‖+‖riemannZeta w‖^(2 : ℕ)+
        2*|Real.eulerMascheroniConstant| *‖riemannZeta w‖ := by
    calc
      _ ≤ ‖-deriv riemannZeta w-riemannZeta w^(2 : ℕ)‖+
          ‖2*(Real.eulerMascheroniConstant:ℂ)*riemannZeta w‖ := norm_add_le _ _
      _ ≤ _ := by
        have h := norm_sub_le (-deriv riemannZeta w) (riemannZeta w^(2 : ℕ))
        simp only [norm_neg,norm_pow] at h
        simp only [norm_mul, Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
        linarith
  apply hnorm.trans
  have hsq : ‖riemannZeta w‖^(2 : ℕ)≤(3*K*(1+|t|))^(2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hlin := mul_le_mul_of_nonneg_left hz (show 0≤2*|Real.eulerMascheroniConstant| by positivity)
  have ht1 : 1≤1+|t| := by linarith [abs_nonneg t]
  have hlast : 6*|Real.eulerMascheroniConstant| *K*(1+|t|) ≤
      6*|Real.eulerMascheroniConstant| *K*(1+|t|)^(2 : ℕ) := by
    gcongr
    nlinarith
  dsimp [C]
  dsimp [w] at *
  nlinarith

end RHTower
