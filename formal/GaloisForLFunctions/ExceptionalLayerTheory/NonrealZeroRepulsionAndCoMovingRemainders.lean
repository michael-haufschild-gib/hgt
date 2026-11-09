import GaloisForLFunctions.ExceptionalLayerTheory.TheExceptionalLayerAtEscapingHeights
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiRealReciprocalField
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros

/-!
# Nonreal zero repulsion, absence of the Siegel regime, and co-moving remainder modes

Two analytic mechanisms govern how a top zero layer of `ζ` interacts with a strictly lower
infinite remainder:

* **Multiplicity-exact 5-point repulsion and absence of the Siegel regime.** Expanding `-Re (ζ'/ζ)`
  against `2 (1 + cos(γ₁ log n)) (1 + cos(γ₂ log n)) ≥ 0` on `1 < σ ≤ 2` and retaining the full
  multiplicity fibres of `q₁, q₂ : XiZeroCopy` (`4 ≤ Im q₁`, `Im q₁ + 4 ≤ Im q₂`) gives
  `2 m₁ / (σ - β₁) + 2 m₂ / (σ - β₂) ≤ 2 / (σ - 1) + log γ₁ + log γ₂ + (log(γ₂ + γ₁) + log(γ₂ - γ₁))/2 + 13/5`.
  For a simple zero (`m₁ = 1`), `2 / (σ - 1) - 2 / (σ - β₁) > 0` for every `σ > 1`. Moreover, every
  pair of nontrivial zeros `ρ₁, ρ₂` of `ζ` satisfies `(1 - Re ρ₁) log(|Im ρ₁| · |Im ρ₂|) ≥ 1/58`,
  and for any fixed `β < 1`, `(1 - β) log |Im ρ₂| → +∞` as `|Im ρ₂| → ∞`; hence `ζ` admits no
  Siegel Deuring–Heilbronn regime.
* **Exact speed phase transition of co-moving remainder modes.** At observation point `σ + i t`
  and damping `y = e^{-a t}`, a fixed top zero `ρ_top` (`Re ρ_top = β`) has exponential rate
  `a (β - σ) / 2 - π / 4`, whereas a co-moving remainder mode at `β_r + i t` (`σ < β_r < β`) has
  zero imaginary Gamma offset and exact rate `a (β_r - σ) / 2`. The observation abscissa `σ`
  cancels from their rate difference `a (β - β_r) / 2 - π / 4`: throughout the nonempty
  supercritical window `π / (2 (β - σ)) < a < π / (2 (β - β_r))`, the top mode diverges yet is
  exponentially dominated by the co-moving remainder mode, while for `a > π / (2 (β - β_r))` the
  top mode exponentially masks the co-moving remainder mode.
-/

set_option autoImplicit false

open Complex Filter Finset Set Topology RHTower XiAtlasFinitePart
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open GaloisForLFunctions.EulerFETransportTheory

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ### Multiplicity-exact 5-point repulsion and absence of the Siegel regime -/

/-- Two-phase trigonometric positivity `2 + 2 cos u + 2 cos v + cos(v + u) + cos(v - u) ≥ 0`. -/
theorem zero_le_two_phase_cosine_scalar {a E u v : ℝ} (ha : 0 ≤ a) (hE : 0 ≤ E) :
    0 ≤ 2 * (a * (E * 1)) + 2 * (a * (E * Real.cos u)) + 2 * (a * (E * Real.cos v)) +
      a * (E * Real.cos (v + u)) + a * (E * Real.cos (v - u)) := by
  have htrig : 2 + 2 * Real.cos u + 2 * Real.cos v + Real.cos (v + u) + Real.cos (v - u) =
      2 * (1 + Real.cos u) * (1 + Real.cos v) := by
    rw [Real.cos_add, Real.cos_sub]
    ring
  have hfac : 2 * (a * (E * 1)) + 2 * (a * (E * Real.cos u)) + 2 * (a * (E * Real.cos v)) +
      a * (E * Real.cos (v + u)) + a * (E * Real.cos (v - u)) =
      a * E * (2 + 2 * Real.cos u + 2 * Real.cos v + Real.cos (v + u) + Real.cos (v - u)) := by
    ring
  have hu : 0 ≤ 1 + Real.cos u := by linarith [Real.neg_one_le_cos u]
  have hv : 0 ≤ 1 + Real.cos v := by linarith [Real.neg_one_le_cos v]
  rw [hfac, htrig]
  positivity

private theorem zero_le_two_phase_vonMangoldt_term (n : ℕ) (σ γ₁ γ₂ : ℝ) :
    0 ≤ 2 * (LSeries.term (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)) (σ : ℂ) n).re +
      2 * (LSeries.term (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
        ((σ : ℂ) + (γ₁ : ℂ) * I) n).re +
      2 * (LSeries.term (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
        ((σ : ℂ) + (γ₂ : ℂ) * I) n).re +
      (LSeries.term (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
        ((σ : ℂ) + ((γ₂ + γ₁ : ℝ) : ℂ) * I) n).re +
      (LSeries.term (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
        ((σ : ℂ) + ((γ₂ - γ₁ : ℝ) : ℂ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [RHTower.Sieve.re_lseries_term_vonMangoldt hn, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_self, add_zero, zero_add]
    have hz : Real.log (n : ℝ) * 0 = 0 := mul_zero _
    have hp : Real.log (n : ℝ) * (γ₂ + γ₁) = Real.log (n : ℝ) * γ₂ + Real.log (n : ℝ) * γ₁ := by
      ring
    have hm : Real.log (n : ℝ) * (γ₂ - γ₁) = Real.log (n : ℝ) * γ₂ - Real.log (n : ℝ) * γ₁ := by
      ring
    rw [hz, Real.cos_zero, hp, hm]
    exact zero_le_two_phase_cosine_scalar ArithmeticFunction.vonMangoldt_nonneg (Real.exp_nonneg _)

/-- **Nonnegative 5-point von Mangoldt inequality for `-Re (ζ'/ζ)` on `1 < σ`.** -/
theorem zero_le_five_point_neg_re_logDeriv_riemannZeta {σ : ℝ} (hσ : 1 < σ) (γ₁ γ₂ : ℝ) :
    0 ≤ 2 * (-(logDeriv riemannZeta (σ : ℂ)).re) +
      2 * (-(logDeriv riemannZeta ((σ : ℂ) + (γ₁ : ℂ) * I)).re) +
      2 * (-(logDeriv riemannZeta ((σ : ℂ) + (γ₂ : ℂ) * I)).re) +
      (-(logDeriv riemannZeta ((σ : ℂ) + ((γ₂ + γ₁ : ℝ) : ℂ) * I)).re) +
      (-(logDeriv riemannZeta ((σ : ℂ) + ((γ₂ - γ₁ : ℝ) : ℂ) * I)).re) := by
  let pt : ℝ → ℂ := fun t => (σ : ℂ) + (t : ℂ) * I
  have hre : ∀ t : ℝ, 1 < (pt t).re := fun t => by simp [pt, hσ]
  have hval : ∀ t : ℝ, -(logDeriv riemannZeta (pt t)).re =
      ∑' n : ℕ, (LSeries.term (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
        (pt t) n).re := by
    intro t
    rw [← RHTower.Sieve.neg_div_re_eq_neg_logDeriv_re,
      ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div (hre t),
      RHTower.Sieve.re_lseries_vonMangoldt (hre t)]
  have hp0 : (σ : ℂ) = pt 0 := by simp [pt]
  rw [hp0, hval 0, hval γ₁, hval γ₂, hval (γ₂ + γ₁), hval (γ₂ - γ₁)]
  have s0 := RHTower.Sieve.summable_re_lseries_term_vonMangoldt (hre 0)
  have s1 := RHTower.Sieve.summable_re_lseries_term_vonMangoldt (hre γ₁)
  have s2 := RHTower.Sieve.summable_re_lseries_term_vonMangoldt (hre γ₂)
  have s3 := RHTower.Sieve.summable_re_lseries_term_vonMangoldt (hre (γ₂ + γ₁))
  have s4 := RHTower.Sieve.summable_re_lseries_term_vonMangoldt (hre (γ₂ - γ₁))
  rw [← s0.tsum_mul_left, ← s1.tsum_mul_left, ← s2.tsum_mul_left,
    ← (s0.mul_left 2).tsum_add (s1.mul_left 2),
    ← ((s0.mul_left 2).add (s1.mul_left 2)).tsum_add (s2.mul_left 2),
    ← (((s0.mul_left 2).add (s1.mul_left 2)).add (s2.mul_left 2)).tsum_add s3,
    ← ((((s0.mul_left 2).add (s1.mul_left 2)).add (s2.mul_left 2)).add s3).tsum_add s4]
  refine tsum_nonneg fun n => ?_
  simpa only [← hp0, pt] using zero_le_two_phase_vonMangoldt_term n σ γ₁ γ₂

/-- On `1 ≤ s.re` away from `ξ`-zeros, `Re (ξ'/ξ)(s)` dominates the full multiplicity fibre of any
zero copy `q₀`. -/
theorem fiber_resolvent_le_re_logDeriv_xi {s : ℂ} (hs : xi s ≠ 0) (h1 : 1 ≤ s.re)
    (q₀ : XiZeroCopy) :
    ((xiZeroCopyFiber q₀.1).card : ℝ) *
        ((s.re - (q₀.1 : ℂ).re) / Complex.normSq (s - (q₀.1 : ℂ))) ≤
      (logDeriv xi s).re := by
  rw [re_logDeriv_xi_eq_realReciprocal_tsum hs]
  have hsum := xiRealReciprocal_summable s (h := 0) (by norm_num)
  have hnn : ∀ q : XiZeroCopy, 0 ≤ xiRealReciprocal s 0 q := by
    intro q
    have hq1 := xiZeroCopy_re_lt_one q
    simp only [xiRealReciprocal, Complex.ofReal_zero, add_zero, Complex.inv_re, Complex.sub_re]
    exact div_nonneg (by linarith) (Complex.normSq_nonneg _)
  have hle := hsum.sum_le_tsum (xiZeroCopyFiber q₀.1) (fun q _ => hnn q)
  have hconst : ∀ q ∈ xiZeroCopyFiber q₀.1,
      xiRealReciprocal s 0 q = (s.re - (q₀.1 : ℂ).re) / Complex.normSq (s - (q₀.1 : ℂ)) := by
    intro q hq
    have hpt : (q.1 : ℂ) = (q₀.1 : ℂ) := congrArg Subtype.val (xiZeroCopyFiber_point hq)
    simp [xiRealReciprocal, Complex.inv_re, hpt]
  rwa [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hle

/-- Multiplicity-exact Landau bound on `1 < σ ≤ 2`, `t ≥ 4`, retaining the full fibre at `q₀`. -/
theorem neg_re_logDeriv_riemannZeta_le_half_sub_fiber {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (q₀ : XiZeroCopy) (hγ : 4 ≤ (q₀.1 : ℂ).im) :
    -(logDeriv riemannZeta ((σ : ℂ) + ((q₀.1 : ℂ).im : ℂ) * I)).re ≤
      Real.log (q₀.1 : ℂ).im / 2 + 1 / 2 -
        ((xiZeroCopyFiber q₀.1).card : ℝ) / (σ - (q₀.1 : ℂ).re) := by
  set β : ℝ := (q₀.1 : ℂ).re with hβ
  set γ : ℝ := (q₀.1 : ℂ).im with hγdef
  set s : ℂ := (σ : ℂ) + (γ : ℂ) * I with hsdef
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = γ := by simp [s]
  have h1 : 1 < s.re := by simpa [hsre] using hσ1
  have hxine : xi s ≠ 0 := xi_ne_zero_of_one_le_re h1.le
  have hβ1 : β < 1 := xiZeroCopy_re_lt_one q₀
  have hσβ : 0 < σ - β := by linarith
  have hfib := fiber_resolvent_le_re_logDeriv_xi hxine h1.le q₀
  have hnsq : Complex.normSq (s - (q₀.1 : ℂ)) = (σ - β) ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [hsre, hsim, Complex.sub_re, Complex.sub_im, ← hβ, ← hγdef, sub_self]
    ring
  rw [hsre, hnsq] at hfib
  have hsimp : ((xiZeroCopyFiber q₀.1).card : ℝ) * ((σ - β) / (σ - β) ^ 2) =
      ((xiZeroCopyFiber q₀.1).card : ℝ) / (σ - β) := by
    field_simp
  rw [hsimp] at hfib
  have hfour := logDeriv_xi_fourFactor h1
  have hzeta : logDeriv riemannZeta s =
      logDeriv xi s - 1 / s - 1 / (s - 1) - logDeriv Complex.Gammaℝ s := by
    rw [hfour]; ring
  rw [hzeta]
  simp only [Complex.sub_re]
  have hnormSq : Complex.normSq s = σ ^ 2 + γ ^ 2 := by
    rw [Complex.normSq_apply, hsre, hsim]; ring
  have hnormSq1 : Complex.normSq (s - 1) = (σ - 1) ^ 2 + γ ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hsre, hsim,
      Complex.one_re, Complex.one_im, sub_zero]
    ring
  have hA : (1 / s).re ≤ 2 / 17 := by
    rw [one_div, Complex.inv_re, hsre, hnormSq, div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [hγ, hσ1, hσ2]
  have hB : (1 / (s - 1)).re ≤ 1 / 16 := by
    rw [one_div, Complex.inv_re, Complex.sub_re, hsre, Complex.one_re, hnormSq1,
      div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [hγ, hσ1, hσ2]
  have hC : (logDeriv Complex.Gammaℝ s).re ≤ Real.log γ / 2 + 1 / 4 :=
    re_logDeriv_Gammaℝ_le_half_log hσ1.le hσ2 hγ
  linarith [hfib, hA, hB, hC]

/-- **Explicit multiplicity-weighted 5-point repulsion inequality for two nonreal `ζ`-zeros.**
For any `1 < σ ≤ 2` and `q₁, q₂ : XiZeroCopy` with `4 ≤ Im q₁` and `Im q₁ + 4 ≤ Im q₂`,
retaining the full multiplicity fibres `m₁ = card (xiZeroCopyFiber q₁.1)` and
`m₂ = card (xiZeroCopyFiber q₂.1)` yields an explicit pole-vs-zero balance with logarithmic
height growth. -/
theorem two_zero_five_point_repulsion_inequality {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (q₁ q₂ : XiZeroCopy) (hγ₁ : 4 ≤ (q₁.1 : ℂ).im)
    (hgap : (q₁.1 : ℂ).im + 4 ≤ (q₂.1 : ℂ).im) :
    2 * ((xiZeroCopyFiber q₁.1).card : ℝ) / (σ - (q₁.1 : ℂ).re) +
      2 * ((xiZeroCopyFiber q₂.1).card : ℝ) / (σ - (q₂.1 : ℂ).re) ≤
      2 / (σ - 1) + Real.log (q₁.1 : ℂ).im + Real.log (q₂.1 : ℂ).im +
        (Real.log ((q₂.1 : ℂ).im + (q₁.1 : ℂ).im) +
          Real.log ((q₂.1 : ℂ).im - (q₁.1 : ℂ).im)) / 2 + 13 / 5 := by
  set γ₁ : ℝ := (q₁.1 : ℂ).im
  set γ₂ : ℝ := (q₂.1 : ℂ).im
  have hbase := zero_le_five_point_neg_re_logDeriv_riemannZeta hσ1 γ₁ γ₂
  have hb0 : -(logDeriv riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) - 1 / 5 := by
    have h := neg_re_logDeriv_riemannZeta_real_le_neg hσ1 hσ2
    rw [RHTower.Sieve.neg_div_re_eq_neg_logDeriv_re] at h
    linarith
  have hb1 := neg_re_logDeriv_riemannZeta_le_half_sub_fiber hσ1 hσ2 q₁ hγ₁
  have hb2 := neg_re_logDeriv_riemannZeta_le_half_sub_fiber hσ1 hσ2 q₂ (by linarith)
  have hb3 := neg_re_logDeriv_riemannZeta_le_half (σ := σ) (t := γ₂ + γ₁) hσ1 hσ2 (by linarith)
  have hb4 := neg_re_logDeriv_riemannZeta_le_half (σ := σ) (t := γ₂ - γ₁) hσ1 hσ2 (by linarith)
  linarith [hbase, hb0, hb1, hb2, hb3, hb4]

/-- For a simple top zero (`m₁ = 1`), the pole main term `2 / (σ - 1)` strictly exceeds the
top-zero main term `2 / (σ - β₁)` at every `σ > 1`. -/
theorem pole_mainTerm_sub_simple_zero_pos {β₁ σ : ℝ} (hβ₁ : β₁ < 1) (hσ : 1 < σ) :
    0 < 2 / (σ - 1) - 2 / (σ - β₁) := by
  have h1 : 0 < σ - 1 := by linarith
  have h2 : 0 < σ - β₁ := by linarith
  have heq : 2 / (σ - 1) - 2 / (σ - β₁) = 2 * (1 - β₁) / ((σ - 1) * (σ - β₁)) := by
    field_simp
    ring
  rw [heq]
  exact div_pos (by linarith) (mul_pos h1 h2)

/-- **Absence of the Siegel Deuring–Heilbronn regime for `ζ`.** Every pair of nontrivial zeros
`ρ₁, ρ₂` of `ζ` satisfies `(1 - Re ρ₁) log(|Im ρ₁| · |Im ρ₂|) ≥ 1/58` (`> 1/58` strictly since
`log |Im ρ₂| > 0`), and for any fixed `β < 1`, `(1 - β) log t → +∞` as `t → +∞`. -/
theorem zeta_no_siegel_regime {ρ₁ ρ₂ : ℂ}
    (h0₁ : 0 < ρ₁.re) (h1₁ : ρ₁.re < 1) (hz₁ : riemannZeta ρ₁ = 0)
    (h0₂ : 0 < ρ₂.re) (h1₂ : ρ₂.re < 1) (hz₂ : riemannZeta ρ₂ = 0) :
    1 / 58 < (1 - ρ₁.re) * Real.log (|ρ₁.im| * |ρ₂.im|) := by
  have hγ₁ := four_le_abs_im_of_zeta_zero h0₁ h1₁ hz₁
  have hγ₂ := four_le_abs_im_of_zeta_zero h0₂ h1₂ hz₂
  have hreg := re_le_one_sub_of_zeta_zero h0₁ h1₁ hz₁
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog4 : (1.38 : ℝ) < Real.log 4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    linarith
  have hL₁ : 0 < Real.log |ρ₁.im| := lt_of_lt_of_le (by linarith)
    (Real.log_le_log (by norm_num) hγ₁)
  have hL₂ : 0 < Real.log |ρ₂.im| := lt_of_lt_of_le (by linarith)
    (Real.log_le_log (by norm_num) hγ₂)
  have hprod₁ : 1 / 58 ≤ (1 - ρ₁.re) * Real.log |ρ₁.im| := by
    have hdiv : 1 / 58 / Real.log |ρ₁.im| ≤ 1 - ρ₁.re := by linarith
    rwa [div_le_iff₀ hL₁] at hdiv
  have hmul : Real.log (|ρ₁.im| * |ρ₂.im|) = Real.log |ρ₁.im| + Real.log |ρ₂.im| :=
    Real.log_mul (by linarith) (by linarith)
  have hpos : 0 < (1 - ρ₁.re) * Real.log |ρ₂.im| := mul_pos (by linarith) hL₂
  rw [hmul, mul_add]
  linarith

theorem tendsto_fixed_gap_mul_log_atTop {β : ℝ} (hβ : β < 1) :
    Tendsto (fun t : ℝ => (1 - β) * Real.log t) atTop atTop :=
  Filter.Tendsto.const_mul_atTop (by linarith) Real.tendsto_log_atTop

/-! ### Co-moving remainder modes and the `exp(-a t)` observation phase transition -/

/-- Exact evaluation of a Gaussian Mellin–Barnes mode for a co-moving zero `β_r + i t` observed at
`σ + i t` (`σ < β_r`): the imaginary offset vanishes, removing Stirling's `e^{-π t / 4}` damping. -/
theorem gaussianMBKernel_coMoving_eq {β_r σ : ℝ} (hσ : σ < β_r) (a t : ℝ) :
    gaussianMBKernel (Real.exp (-a * t)) (((β_r : ℂ) + t * I) - ((σ : ℂ) + t * I)) =
      (((1 / 2 : ℝ) * Real.Gamma ((β_r - σ) / 2) *
        Real.exp (a * (β_r - σ) / 2 * t) : ℝ) : ℂ) := by
  have hsub : ((β_r : ℂ) + t * I) - ((σ : ℂ) + t * I) = ((β_r - σ : ℝ) : ℂ) := by
    push_cast; ring
  have hdiv : (((β_r - σ : ℝ) : ℂ) / 2) = (((β_r - σ) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have hy : (Real.exp (-a * t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  rw [hsub, gaussianMBKernel, hdiv, ← Complex.ofReal_gamma,
    Complex.cpow_def_of_ne_zero hy, ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  have hexp : Complex.exp (((-a * t : ℝ) : ℂ) * -(((β_r - σ) / 2 : ℝ) : ℂ)) =
      (Real.exp (a * (β_r - σ) / 2 * t) : ℂ) := by
    rw [← Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp]
  push_cast
  ring

theorem norm_gaussianMBKernel_coMoving {β_r σ : ℝ} (hσ : σ < β_r) (a t : ℝ) :
    ‖gaussianMBKernel (Real.exp (-a * t)) (((β_r : ℂ) + t * I) - ((σ : ℂ) + t * I))‖ =
      (1 / 2 : ℝ) * Real.Gamma ((β_r - σ) / 2) * Real.exp (a * (β_r - σ) / 2 * t) := by
  have hΓ : 0 < Real.Gamma ((β_r - σ) / 2) := Real.Gamma_pos_of_pos (by linarith)
  rw [gaussianMBKernel_coMoving_eq hσ, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

/-- The observation abscissa `σ` cancels identically from the exponential rate difference between a
fixed top-layer mode `ρ_top` and a co-moving remainder mode at `β_r + i t`. -/
theorem gaussianObservationRate_sub_coMovingRate (ρ_top : ℂ) (β_r σ a : ℝ) :
    gaussianObservationRate ρ_top σ a - a * (β_r - σ) / 2 =
      a * (ρ_top.re - β_r) / 2 - Real.pi / 4 := by
  unfold gaussianObservationRate
  ring

/-- Whenever `σ < β_r < β`, the supercritical co-moving dominance window
`(π / (2 (β - σ)), π / (2 (β - β_r)))` is nonempty. -/
theorem coMoving_supercritical_window_nonempty {σ β_r β : ℝ} (hσ : σ < β_r) (hβ : β_r < β) :
    Real.pi / (2 * (β - σ)) < Real.pi / (2 * (β - β_r)) :=
  div_lt_div_of_pos_left Real.pi_pos (by linarith) (by linarith)

/-- **Supercritical co-moving remainder dominance.** For `σ < β_r < ρ_top.re` and any damping speed
`a` in the nonempty supercritical window `π / (2 (ρ_top.re - σ)) < a < π / (2 (ρ_top.re - β_r))`,
the fixed top-layer mode diverges (`→ +∞`), yet its ratio to a co-moving remainder mode at
`β_r + i t` decays exponentially to `0`. -/
theorem tendsto_top_div_coMoving_zero_in_supercritical_window {ρ_top : ℂ} {σ β_r a : ℝ}
    (hσ : σ < β_r) (hβ : β_r < ρ_top.re)
    (hsuper : Real.pi / (2 * (ρ_top.re - σ)) < a)
    (hsub : a < Real.pi / (2 * (ρ_top.re - β_r))) :
    Tendsto (fun t : ℝ =>
        ‖gaussianMBKernel (Real.exp (-a * t)) (ρ_top - ((σ : ℂ) + t * I))‖) atTop atTop ∧
      Tendsto (fun t : ℝ =>
        gaussianMBKernel (Real.exp (-a * t)) (ρ_top - ((σ : ℂ) + t * I)) /
          gaussianMBKernel (Real.exp (-a * t)) (((β_r : ℂ) + t * I) - ((σ : ℂ) + t * I)))
        atTop (𝓝 0) := by
  have hden1 : 0 < 2 * (ρ_top.re - σ) := by linarith
  have hden2 : 0 < 2 * (ρ_top.re - β_r) := by linarith
  have hrate_pos : 0 < gaussianObservationRate ρ_top σ a := by
    have hm := (div_lt_iff₀ hden1).mp hsuper
    unfold gaussianObservationRate
    linarith
  refine ⟨tendsto_norm_gaussianMode_atTop_of_positive_rate ρ_top σ a hrate_pos, ?_⟩
  obtain ⟨C, _, N, _, hC, _, hb⟩ := exists_gaussianMode_exponential_bounds ρ_top σ
  have hΓ : 0 < Real.Gamma ((β_r - σ) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hδ : 0 < Real.pi / 4 - a * (ρ_top.re - β_r) / 2 := by
    have hm := (lt_div_iff₀ hden2).mp hsub
    linarith
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (C := 2 * C / Real.Gamma ((β_r - σ) / 2)) (N := N) hδ
  filter_upwards [eventually_ge_atTop (|ρ_top.im| + 2)] with t ht
  have hnum := (hb t ht a).1
  rw [norm_div, norm_gaussianMBKernel_coMoving hσ]
  have hco_pos : 0 < (1 / 2 : ℝ) * Real.Gamma ((β_r - σ) / 2) *
      Real.exp (a * (β_r - σ) / 2 * t) := by positivity
  calc
    ‖gaussianMBKernel (Real.exp (-a * t)) (ρ_top - ((σ : ℂ) + t * I))‖ /
        ((1 / 2 : ℝ) * Real.Gamma ((β_r - σ) / 2) * Real.exp (a * (β_r - σ) / 2 * t)) ≤
      (C * t ^ N * Real.exp (gaussianObservationRate ρ_top σ a * t)) /
        ((1 / 2 : ℝ) * Real.Gamma ((β_r - σ) / 2) * Real.exp (a * (β_r - σ) / 2 * t)) :=
      div_le_div_of_nonneg_right hnum hco_pos.le
    _ = (2 * C / Real.Gamma ((β_r - σ) / 2)) * t ^ N *
        Real.exp (-((Real.pi / 4 - a * (ρ_top.re - β_r) / 2) * t)) := by
      have hex : gaussianObservationRate ρ_top σ a * t - a * (β_r - σ) / 2 * t =
          -((Real.pi / 4 - a * (ρ_top.re - β_r) / 2) * t) := by
        unfold gaussianObservationRate; ring
      rw [← hex, Real.exp_sub]
      field_simp

/-- **Ultra-supercritical top-layer masking.** Above the `σ`-independent threshold
`a > π / (2 (ρ_top.re - β_r))`, a fixed top-layer mode exponentially masks even co-moving
remainder modes at `β_r + i t`. -/
theorem tendsto_coMoving_div_top_zero_above_masking_threshold {ρ_top : ℂ} {σ β_r a : ℝ}
    (hσ : σ < β_r) (hβ : β_r < ρ_top.re)
    (hmask : Real.pi / (2 * (ρ_top.re - β_r)) < a) :
    Tendsto (fun t : ℝ =>
      gaussianMBKernel (Real.exp (-a * t)) (((β_r : ℂ) + t * I) - ((σ : ℂ) + t * I)) /
        gaussianMBKernel (Real.exp (-a * t)) (ρ_top - ((σ : ℂ) + t * I)))
      atTop (𝓝 0) := by
  obtain ⟨_, D, _, M, _, hD, hb⟩ := exists_gaussianMode_exponential_bounds ρ_top σ
  have hΓ : 0 < Real.Gamma ((β_r - σ) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hden : 0 < 2 * (ρ_top.re - β_r) := by linarith
  have hδ : 0 < a * (ρ_top.re - β_r) / 2 - Real.pi / 4 := by
    have hm := (div_lt_iff₀ hden).mp hmask
    linarith
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
    (C := (1 / 2 : ℝ) * Real.Gamma ((β_r - σ) / 2) * D) (N := M) hδ
  filter_upwards [eventually_ge_atTop (|ρ_top.im| + 2)] with t ht
  have hinv := (hb t ht a).2
  rw [div_eq_mul_inv, norm_mul, norm_gaussianMBKernel_coMoving hσ]
  calc
    (1 / 2 : ℝ) * Real.Gamma ((β_r - σ) / 2) * Real.exp (a * (β_r - σ) / 2 * t) *
        ‖(gaussianMBKernel (Real.exp (-a * t)) (ρ_top - ((σ : ℂ) + t * I)))⁻¹‖ ≤
      (1 / 2 : ℝ) * Real.Gamma ((β_r - σ) / 2) * Real.exp (a * (β_r - σ) / 2 * t) *
        (D * t ^ M * Real.exp (-(gaussianObservationRate ρ_top σ a * t))) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = ((1 / 2 : ℝ) * Real.Gamma ((β_r - σ) / 2) * D) * t ^ M *
        Real.exp (-((a * (ρ_top.re - β_r) / 2 - Real.pi / 4) * t)) := by
      have hex : a * (β_r - σ) / 2 * t + -(gaussianObservationRate ρ_top σ a * t) =
          -((a * (ρ_top.re - β_r) / 2 - Real.pi / 4) * t) := by
        unfold gaussianObservationRate; ring
      rw [← hex, Real.exp_add]
      ring

end GaloisForLFunctions.ExceptionalLayerTheory
