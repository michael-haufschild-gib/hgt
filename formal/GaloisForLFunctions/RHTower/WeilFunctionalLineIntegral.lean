import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import Zeta23.WeilEF.Main

/-!
# The Weil functional as a line integral of the Weil function

For real weights `lam` with `Σ |lam(n)| n^{−σ} < ∞` for `σ > 1`, a `C²` compactly supported test `k`
and `1 < c ≤ 3/2`,

`W_lam(k) = (1/2π) ∫ (H(c + it) + H(1 − c − it)) Φ_lam(c + it) dt`
(`weilFullFunctional_eq_line_integral`),

where `H(s) = k̂((s − ½)/i)` and `Φ_lam(s) = Γ_ℝ'/Γ_ℝ(s) + 1/s + 1/(s − 1) − Σ_{n≥2} lam(n) n^{−s}` is
the Weil function.

* The prime part is a Fourier inversion on the line `Re s = c`, for any absolutely convergent
  Dirichlet series (`prime_side_line_gen`).
* The archimedean part moves to the critical line (`Zeta23.WeilEF.gamma_line_shift`).
* The pole part is the two-line residue identity `two_line_pair` at `z₀ = 0`: for
  `g_{z₀}(s) = 1/(s − z₀) + 1/(s − 1 + z₀)` and `1 − c < Re z₀ < c`,
  `(1/2π) ∫ (H(c + it) + H(1 − c − it)) g_{z₀}(c + it) dt = H(z₀) + H(1 − z₀)`.
  The same identity at `z₀ = ½ + iγ` evaluates every atom of an atomic Weil function.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Interval
open Zeta23 Zeta23.WeilEF

noncomputable section

namespace RHTower.WeilLineIntegral

/-! ## The prime side for any absolutely convergent Dirichlet series -/

theorem line_integral_term {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (c : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, paperFT (tilt k (c - 1 / 2)) t * LSeries.term a (c + t * I) n
      = a n / Real.sqrt n * k (Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hterm : ∀ t : ℝ, LSeries.term a (c + t * I) n
        = a n * (((n : ℝ) ^ (-c) : ℝ) : ℂ) * cexp (-I * t * Real.log n) := by
      intro t
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg]
      have hsplit : (-((c : ℂ) + t * I)) = (-(c : ℂ)) + (-(I * t)) := by ring
      rw [hsplit, Complex.cpow_add _ _ hnC]
      have h1 : (n : ℂ) ^ (-(c : ℂ)) = (((n : ℝ) ^ (-c) : ℝ) : ℂ) := by
        rw [show ((n : ℂ)) = (((n : ℝ) : ℂ)) by push_cast; rfl,
          show (-(c : ℂ)) = ((-c : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hn0.le]
      have h2 : (n : ℂ) ^ (-(I * t)) = cexp (-I * t * Real.log n) := by
        rw [Complex.cpow_def_of_ne_zero hnC]
        congr 1
        rw [show ((n : ℂ)) = (((n : ℝ) : ℂ)) by push_cast; rfl, ← Complex.ofReal_log hn0.le]
        ring
      rw [h1, h2]
      ring
    simp_rw [hterm]
    have hre : (fun t : ℝ => paperFT (tilt k (c - 1 / 2)) t
        * (a n * (((n : ℝ) ^ (-c) : ℝ) : ℂ) * cexp (-I * t * Real.log n)))
        = fun t : ℝ => (a n * (((n : ℝ) ^ (-c) : ℝ) : ℂ))
          * (paperFT (tilt k (c - 1 / 2)) t * cexp (-I * t * Real.log n)) := by
      funext t
      ring
    rw [hre, Zeta23.EF.cintegral_const_mul]
    rw [show (1 / (2 * (Real.pi : ℂ))) * ((a n * (((n : ℝ) ^ (-c) : ℝ) : ℂ))
        * ∫ t : ℝ, paperFT (tilt k (c - 1 / 2)) t * cexp (-I * t * Real.log n))
        = (a n * (((n : ℝ) ^ (-c) : ℝ) : ℂ))
          * ((1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, paperFT (tilt k (c - 1 / 2)) t
            * cexp (-I * t * Real.log n)) from by ring]
    rw [tilted_inversion hk hkc (c - 1 / 2) (Real.log n)]
    have hexp : Real.exp ((c - 1 / 2) * Real.log n) = (n : ℝ) ^ (c - 1 / 2) := by
      rw [Real.rpow_def_of_pos hn0]
      ring_nf
    have hpow : ((n : ℝ) ^ (-c) : ℝ) * ((n : ℝ) ^ (c - 1 / 2) : ℝ) = 1 / Real.sqrt n := by
      rw [← Real.rpow_add hn0, show -c + (c - 1 / 2) = -(1 / 2) by ring, Real.rpow_neg hn0.le,
        Real.sqrt_eq_rpow]
      exact (one_div _).symm
    rw [hexp]
    calc a n * (((n : ℝ) ^ (-c) : ℝ) : ℂ) * (k (Real.log n) * (((n : ℝ) ^ (c - 1 / 2) : ℝ) : ℂ))
        = a n * ((((n : ℝ) ^ (-c) * (n : ℝ) ^ (c - 1 / 2) : ℝ)) : ℂ) * k (Real.log n) := by
          push_cast
          ring
      _ = a n / Real.sqrt n * k (Real.log n) := by
          rw [hpow]
          push_cast
          ring

/-- **The prime side on a line of absolute convergence.**
`(1/2π) ∫ H(c + it) L(c + it) dt = Σ_n a(n) n^{−1/2} k(log n)`. -/
theorem hasSum_prime_side_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {a : ℕ → ℂ} {c : ℝ} (ha : LSeriesSummable a c) :
    HasSum (fun n : ℕ => a n / Real.sqrt n * k (Real.log n))
      ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (c + t * I) * LSeries a (c + t * I)) := by
  have hkb2 : ContDiff ℝ 2 (tilt k (c - 1 / 2)) := tilt_contDiff hk _
  have hkbc : HasCompactSupport (tilt k (c - 1 / 2)) := tilt_hasCompactSupport hkc _
  have hpfi : Integrable (fun t : ℝ => paperFT (tilt k (c - 1 / 2)) t) :=
    Zeta23.EF.integrable_paperFT_ofReal (Zeta23.EF.integrable_fourier_of_contDiff_two hkb2 hkbc)
  have hnorm : ∀ (n : ℕ) (t : ℝ), ‖LSeries.term a ((c : ℂ) + t * I) n‖ = ‖LSeries.term a c n‖ := by
    intro n t
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hcont : ∀ n : ℕ, Continuous (fun t : ℝ => LSeries.term a ((c : ℂ) + t * I) n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simpa [LSeries.term_zero] using continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div ?_ (fun t => ?_)
      · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn))
      · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => paperFT (tilt k (c - 1 / 2)) t
      * LSeries.term a ((c : ℂ) + t * I) n) := by
    intro n
    refine hpfi.mul_bdd (c := ‖LSeries.term a c n‖) (hcont n).aestronglyMeasurable ?_
    filter_upwards with t
    rw [hnorm n t]
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖paperFT (tilt k (c - 1 / 2)) t
      * LSeries.term a ((c : ℂ) + t * I) n‖) := by
    have heval : ∀ n : ℕ, (∫ t : ℝ, ‖paperFT (tilt k (c - 1 / 2)) t
        * LSeries.term a ((c : ℂ) + t * I) n‖)
        = (∫ t : ℝ, ‖paperFT (tilt k (c - 1 / 2)) t‖) * ‖LSeries.term a c n‖ := by
      intro n
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [norm_mul, hnorm n t]
    exact (ha.norm.mul_left _).congr fun n => (heval n).symm
  have hHS := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum
  have hline : ∀ t : ℝ, Hfn k (c + t * I) * LSeries a (c + t * I)
      = ∑' n : ℕ, paperFT (tilt k (c - 1 / 2)) t * LSeries.term a (c + t * I) n := by
    intro t
    rw [Hfn_line, LSeries, ← tsum_mul_left]
  rw [integral_congr_ae (Filter.Eventually.of_forall hline), ← hHS.tsum_eq,
    ← tsum_mul_left]
  have hterm : ∀ n : ℕ, (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, paperFT (tilt k (c - 1 / 2)) t
      * LSeries.term a ((c : ℂ) + t * I) n = a n / Real.sqrt n * k (Real.log n) :=
    line_integral_term hk hkc c a
  have hS : Summable fun n : ℕ => (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      paperFT (tilt k (c - 1 / 2)) t * LSeries.term a ((c : ℂ) + t * I) n :=
    hHS.summable.mul_left _
  rw [show (fun n : ℕ => a n / Real.sqrt n * k (Real.log n)) = fun n => (1 / (2 * Real.pi) : ℂ) *
    ∫ t : ℝ, paperFT (tilt k (c - 1 / 2)) t * LSeries.term a ((c : ℂ) + t * I) n
    from funext fun n => (hterm n).symm]
  exact hS.hasSum

/-! ## Two vertical lines and a simple pole -/

/-- On a vertical line off the pole, `H(σ + it)/(σ + it − p)` is integrable. -/
theorem integrable_line_div {H : ℂ → ℂ} (hH : Differentiable ℂ H) {a b C : ℝ}
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖H (σ + t * I)‖ ≤ C / (1 + t ^ 2)) {σ : ℝ} (h1 : a ≤ σ)
    (h2 : σ ≤ b) {p : ℂ} (hne : σ ≠ p.re) :
    Integrable (fun t : ℝ => H (σ + t * I) / (σ + t * I - p)) := by
  have hC0 : 0 ≤ C := by
    have := hC σ 0 h1 h2
    simp at this
    exact (norm_nonneg _).trans this
  have hd : 0 < |σ - p.re| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hne' : ∀ t : ℝ, (σ : ℂ) + t * I - p ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    exact hne (by linarith)
  have hcont : Continuous (fun t : ℝ => H (σ + t * I) / (σ + t * I - p)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hl : ContinuousAt (fun t : ℝ => (σ : ℂ) + t * I) t := by fun_prop
    exact ((hH _).continuousAt.comp hl).div (hl.sub continuousAt_const) (hne' t)
  have hdom : Integrable (fun t : ℝ => C / |σ - p.re| * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_div]
  have hden : |σ - p.re| ≤ ‖(σ : ℂ) + t * I - p‖ := by
    have := Complex.abs_re_le_norm ((σ : ℂ) + t * I - p)
    simpa using this
  rw [div_le_iff₀ (lt_of_lt_of_le hd hden)]
  calc ‖H (σ + t * I)‖ ≤ C / (1 + t ^ 2) := hC σ t h1 h2
    _ = C / |σ - p.re| * (1 + t ^ 2)⁻¹ * |σ - p.re| := by field_simp
    _ ≤ C / |σ - p.re| * (1 + t ^ 2)⁻¹ * ‖(σ : ℂ) + t * I - p‖ := by gcongr

/-- **Two vertical lines and one simple pole.**  If `H` is entire and `‖H(σ + it)‖ ≤ C/(1 + t²)` on
the strip `a ≤ σ ≤ b`, then for `a < Re p < b`
`∫ H(b + it)/(b + it − p) dt − ∫ H(a + it)/(a + it − p) dt = 2π H(p)`. -/
theorem two_line_simple_pole {H : ℂ → ℂ} (hH : Differentiable ℂ H) {a b C : ℝ}
    (hC : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ‖H (σ + t * I)‖ ≤ C / (1 + t ^ 2)) {p : ℂ}
    (hp1 : a < p.re) (hp2 : p.re < b) :
    (∫ t : ℝ, H (b + t * I) / (b + t * I - p)) - (∫ t : ℝ, H (a + t * I) / (a + t * I - p)) =
      2 * Real.pi * H p := by
  set f : ℂ → ℂ := fun s => H s / (s - p) with hf
  have hab : a ≤ b := by linarith
  have hC0 : 0 ≤ C := by
    have := hC a 0 le_rfl hab
    simp at this
    exact (norm_nonneg _).trans this
  -- the residue at `p`
  have hres : ∀ R : ℝ, |p.im| < R →
      RectangleIntegral' f ((a : ℂ) + (-R : ℝ) * I) ((b : ℂ) + (R : ℝ) * I) = H p := by
    intro R hR
    have hRp : 0 < R := lt_of_le_of_lt (abs_nonneg _) hR
    refine ResidueTheoremOnRectangleWithSimplePole' (p := p) (by simp; linarith) (by simp; linarith)
      ?_ ?_ ?_
    · rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_zero, add_im, mul_im, zero_add]
      rw [Set.uIoo_of_le hab, Set.uIoo_of_le (by linarith)]
      exact ⟨⟨hp1, hp2⟩, ⟨by linarith [neg_abs_le p.im], by linarith [le_abs_self p.im]⟩⟩
    · intro s hs
      exact ((hH s).div (differentiableAt_id.sub_const p)
        (sub_ne_zero.mpr hs.2)).differentiableWithinAt
    · have hO : (fun s => H s - H p) =O[𝓝[≠] p] (fun s => s - p) :=
        ((hH p).hasDerivAt.isBigO_sub).mono nhdsWithin_le_nhds
      have h2 := hO.mul (Asymptotics.isBigO_refl (fun s : ℂ => (s - p)⁻¹) (𝓝[≠] p))
      refine (h2.congr' ?_ ?_)
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [hf, Pi.sub_apply]
        ring
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_inv_cancel₀ (sub_ne_zero.mpr hs)
  have hline : ∀ σ : ℝ, a ≤ σ → σ ≤ b → σ ≠ p.re →
      Integrable (fun t : ℝ => f (σ + t * I)) := fun σ h1 h2 hne =>
    integrable_line_div hH hC h1 h2 hne
  have hib := hline b hab le_rfl hp2.ne'
  have hia := hline a le_rfl hab hp1.ne
  -- the horizontal sides vanish
  have hhor : ∀ s₀ : ℝ, Tendsto (fun R : ℝ => HIntegral f a b (s₀ * R)) atTop (𝓝 0) →
      True := fun _ _ => trivial
  clear hhor
  have hbound : ∀ R : ℝ, |p.im| + 1 ≤ |R| → ∀ x ∈ Set.uIcc a b,
      ‖f (x + R * I)‖ ≤ C / (1 + R ^ 2) := by
    intro R hR x hx
    rw [Set.uIcc_of_le hab] at hx
    simp only [hf, norm_div]
    have hden : 1 ≤ ‖(x : ℂ) + R * I - p‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + R * I - p)
      simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add] at this
      have h' : |p.im| + 1 ≤ |R - p.im| + |p.im| := by
        have := abs_sub_abs_le_abs_sub R p.im
        linarith
      linarith
    calc ‖H (x + R * I)‖ / ‖(x : ℂ) + R * I - p‖ ≤ ‖H (x + R * I)‖ / 1 :=
          div_le_div_of_nonneg_left (norm_nonneg _) one_pos hden
      _ ≤ C / (1 + R ^ 2) := by rw [div_one]; exact hC x R hx.1 hx.2
  have htop : Tendsto (fun R : ℝ => HIntegral f a b R) atTop (𝓝 0) := by
    have hlim : Tendsto (fun R : ℝ => C / (1 + R ^ 2) * |b - a|) atTop (𝓝 0) := by
      have : Tendsto (fun R : ℝ => C / (1 + R ^ 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1
          (tendsto_pow_atTop (by norm_num)))
      simpa using this.mul_const |b - a|
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (|p.im| + 1)] with R hR
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hbound R (by rw [abs_of_nonneg (show (0 : ℝ) ≤ R by linarith [abs_nonneg p.im])]; exact hR) x
        (Set.uIoc_subset_uIcc hx)
  have hbot : Tendsto (fun R : ℝ => HIntegral f a b (-R)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun R : ℝ => C / (1 + R ^ 2) * |b - a|) atTop (𝓝 0) := by
      have : Tendsto (fun R : ℝ => C / (1 + R ^ 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1
          (tendsto_pow_atTop (by norm_num)))
      simpa using this.mul_const |b - a|
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (|p.im| + 1)] with R hR
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have h := hbound (-R)
      (by rw [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ R by linarith [abs_nonneg p.im])]; exact hR)
      x (Set.uIoc_subset_uIcc hx)
    simpa using h
  -- the vertical sides converge
  have hvb : Tendsto (fun R : ℝ => ∫ t in (-R)..R, f (b + t * I)) atTop
      (𝓝 (∫ t : ℝ, f (b + t * I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have hva : Tendsto (fun R : ℝ => ∫ t in (-R)..R, f (a + t * I)) atTop
      (𝓝 (∫ t : ℝ, f (a + t * I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  -- assemble
  have hdec : ∀ R : ℝ, RectangleIntegral' f ((a : ℂ) + (-R : ℝ) * I) ((b : ℂ) + (R : ℝ) * I) =
      (1 / (2 * Real.pi * I)) * (HIntegral f a b (-R) - HIntegral f a b R +
        I * (∫ t in (-R)..R, f (b + t * I)) - I * (∫ t in (-R)..R, f (a + t * I))) := by
    intro R
    simp only [RectangleIntegral', RectangleIntegral, VIntegral, smul_eq_mul]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero, add_im, mul_im, zero_add]
  have hlimit : Tendsto (fun R : ℝ => RectangleIntegral' f ((a : ℂ) + (-R : ℝ) * I)
      ((b : ℂ) + (R : ℝ) * I)) atTop
      (𝓝 ((1 / (2 * Real.pi * I)) * (0 - 0 + I * (∫ t : ℝ, f (b + t * I)) -
        I * (∫ t : ℝ, f (a + t * I))))) := by
    simp_rw [hdec]
    exact (((hbot.sub htop).add (hvb.const_mul I)).sub (hva.const_mul I)).const_mul _
  have hconst : Tendsto (fun R : ℝ => RectangleIntegral' f ((a : ℂ) + (-R : ℝ) * I)
      ((b : ℂ) + (R : ℝ) * I)) atTop (𝓝 (H p)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop |p.im|] with R hR
    exact (hres R hR).symm
  have heq := tendsto_nhds_unique hconst hlimit
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have e1 : (∫ t : ℝ, f (b + t * I)) = ∫ t : ℝ, H (b + t * I) / (b + t * I - p) := rfl
  have e2 : (∫ t : ℝ, f (a + t * I)) = ∫ t : ℝ, H (a + t * I) / (a + t * I - p) := rfl
  rw [← e1, ← e2, heq]
  have hk : (2 * Real.pi : ℂ) * (1 / (2 * Real.pi * I)) * I = 1 := by field_simp
  linear_combination (-(∫ t : ℝ, f (b + t * I)) + ∫ t : ℝ, f (a + t * I)) * hk

/-- The test transform on the lines: `H(s) = k̂((s − ½)/i)` is entire and `O(1/(1 + t²))` on
`−1 ≤ Re s ≤ 2`. -/
theorem differentiable_Hfn {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Differentiable ℂ (Hfn k) := by
  have h := differentiable_paperFT hk.continuous hkc
  show Differentiable ℂ (fun s => paperFT k ((s - 1 / 2) / I))
  exact h.comp ((differentiable_id.sub_const _).div_const I)

/-- `g_{z₀}(s) = 1/(s − z₀) + 1/(s − (1 − z₀))`, odd under `s ↦ 1 − s`. -/
def gPair (z₀ s : ℂ) : ℂ := 1 / (s - z₀) + 1 / (s - (1 - z₀))

theorem gPair_one_sub (z₀ s : ℂ) : gPair z₀ (1 - s) = -gPair z₀ s := by
  unfold gPair
  rw [show 1 - s - z₀ = -(s - (1 - z₀)) by ring, show 1 - s - (1 - z₀) = -(s - z₀) by ring,
    div_neg, div_neg]
  ring

/-- **The two-line identity for a symmetric pair of simple poles.**  For `1 − c < Re z₀ < c`,
`(1/2π) ∫ (H(c + it) + H(1 − c − it)) g_{z₀}(c + it) dt = H(z₀) + H(1 − z₀)`. -/
theorem two_line_pair {H : ℂ → ℂ} (hH : Differentiable ℂ H) {c C : ℝ}
    (hC : ∀ σ t : ℝ, 1 - c ≤ σ → σ ≤ c → ‖H (σ + t * I)‖ ≤ C / (1 + t ^ 2)) {z₀ : ℂ}
    (h1 : 1 - c < z₀.re) (h2 : z₀.re < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (H (c + t * I) + H (1 - c - t * I)) * gPair z₀ (c + t * I) =
      H z₀ + H (1 - z₀) := by
  have hle : 1 - c ≤ c := by linarith
  have h1' : 1 - c < (1 - z₀).re := by simp; linarith
  have h2' : (1 - z₀).re < c := by simp; linarith
  have hc0 : c ≠ z₀.re := (ne_of_gt h2)
  have hc1 : c ≠ (1 - z₀).re := (ne_of_gt h2')
  have ha0 : 1 - c ≠ z₀.re := (ne_of_lt h1)
  have ha1 : 1 - c ≠ (1 - z₀).re := (ne_of_lt h1')
  have iR0 := integrable_line_div hH hC hle le_rfl hc0
  have iR1 := integrable_line_div hH hC hle le_rfl hc1
  have iL0 := integrable_line_div hH hC le_rfl hle ha0
  have iL1 := integrable_line_div hH hC le_rfl hle ha1
  have e0 := two_line_simple_pole hH hC h1 h2
  have e1 := two_line_simple_pole hH hC h1' h2'
  -- the right line
  have hR : (∫ t : ℝ, H (c + t * I) * gPair z₀ (c + t * I)) =
      (∫ t : ℝ, H (c + t * I) / (c + t * I - z₀)) +
        ∫ t : ℝ, H (c + t * I) / (c + t * I - (1 - z₀)) := by
    rw [← integral_add iR0 iR1]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [gPair]
    ring
  -- the reflected line
  have hL : (∫ t : ℝ, H (1 - c - t * I) * gPair z₀ (c + t * I)) =
      -((∫ t : ℝ, H (((1 - c : ℝ) : ℂ) + t * I) / (((1 - c : ℝ) : ℂ) + t * I - z₀)) +
        ∫ t : ℝ, H (((1 - c : ℝ) : ℂ) + t * I) / (((1 - c : ℝ) : ℂ) + t * I - (1 - z₀))) := by
    rw [← integral_add iL0 iL1, ← integral_neg,
      ← integral_neg_eq_self (fun t : ℝ => H (1 - c - t * I) * gPair z₀ (c + t * I))]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    have hs : (c : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - (((1 - c : ℝ) : ℂ) + t * I) := by
      push_cast; ring
    have hs' : (1 : ℂ) - c - ((-t : ℝ) : ℂ) * I = ((1 - c : ℝ) : ℂ) + t * I := by
      push_cast; ring
    rw [hs, hs', gPair_one_sub]
    simp only [gPair]
    ring
  have hiR : Integrable (fun t : ℝ => H (c + t * I) * gPair z₀ (c + t * I)) :=
    (iR0.add iR1).congr (Eventually.of_forall fun t => by simp only [Pi.add_apply, gPair]; ring)
  have hiL : Integrable (fun t : ℝ => H (1 - c - t * I) * gPair z₀ (c + t * I)) := by
    have h := (iL0.add iL1).neg.comp_neg
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.neg_apply, Pi.add_apply]
    have hs : (c : ℂ) + t * I = 1 - (((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      push_cast; ring
    have hs' : (1 : ℂ) - c - t * I = ((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hs, hs', gPair_one_sub]
    simp only [gPair]
    ring
  have hsplit : (∫ t : ℝ, (H (c + t * I) + H (1 - c - t * I)) * gPair z₀ (c + t * I)) =
      (∫ t : ℝ, H (c + t * I) * gPair z₀ (c + t * I)) +
        ∫ t : ℝ, H (1 - c - t * I) * gPair z₀ (c + t * I) := by
    rw [← integral_add hiR hiL]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    ring
  rw [hsplit, hR, hL]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key := congrArg (fun x => (1 / (2 * Real.pi) : ℂ) * x) (show
    ((∫ t : ℝ, H (c + t * I) / (c + t * I - z₀)) +
        ∫ t : ℝ, H (c + t * I) / (c + t * I - (1 - z₀))) +
      -((∫ t : ℝ, H (((1 - c : ℝ) : ℂ) + t * I) / (((1 - c : ℝ) : ℂ) + t * I - z₀)) +
        ∫ t : ℝ, H (((1 - c : ℝ) : ℂ) + t * I) / (((1 - c : ℝ) : ℂ) + t * I - (1 - z₀))) =
      2 * Real.pi * H z₀ + 2 * Real.pi * H (1 - z₀) by linear_combination e0 + e1)
  rw [key]
  field_simp

/-! ## The Weil functional as a line integral -/

theorem lseriesSummable_lamC {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {c : ℝ} (hc : 1 < c) :
    LSeriesSummable (WeilHerglotz.lamC lam) c := by
  refine Summable.of_norm_bounded (hsl c hc) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with h
  · positivity
  · rw [show ((c : ℂ)).re = c from Complex.ofReal_re c]
    gcongr
    unfold WeilHerglotz.lamC
    rw [Complex.norm_real, Real.norm_eq_abs]
    split_ifs <;> simp

theorem Hfn_zero (k : ℝ → ℂ) : Hfn k 0 = paperFT k (I / 2) := by
  unfold Hfn
  congr 1
  rw [div_I]
  ring

theorem Hfn_one (k : ℝ → ℂ) : Hfn k 1 = paperFT k (-I / 2) := by
  unfold Hfn
  congr 1
  rw [div_I]
  ring

theorem weilFunction_eq (lam : ℕ → ℝ) {s : ℂ} (hs : 0 < s.re) :
    WeilHerglotz.weilFunction lam s = logDeriv Complex.Gammaℝ s + gPair 0 s -
      LSeries (WeilHerglotz.lamC lam) s := by
  rw [logDeriv_Gammaℝ hs, WeilHerglotz.weilFunction, gPair]
  ring

/-- **The Weil functional is the line integral of the Weil function.** -/
theorem weilFullFunctional_eq_line_integral {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    weilFullFunctional lam k = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, (Hfn k (c + t * I) + Hfn k (1 - c - t * I)) *
        WeilHerglotz.weilFunction lam (c + t * I) := by
  set kn : ℝ → ℂ := fun u => k (-u) with hkn
  have hkn2 : ContDiff ℝ 2 kn := hk.comp contDiff_neg
  have hknc : HasCompactSupport kn := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  obtain ⟨Cn, hCn0, hCn⟩ := norm_Hfn_le hkn2 hknc
  set F : ℝ → ℂ := fun t => Hfn k (c + t * I) + Hfn k (1 - c - t * I) with hF
  have hFm : ∀ t : ℝ, Hfn k (1 - c - t * I) = Hfn kn (c + t * I) := fun t => Hfn_mirror k c t
  have hFc : Continuous F := by
    simp only [hF, hFm]
    exact (continuous_Hfn_line hk hkc c).add (continuous_Hfn_line hkn2 hknc c)
  have hFb : ∀ t : ℝ, ‖F t‖ ≤ (C + Cn) / (1 + t ^ 2) := by
    intro t
    simp only [hF, hFm]
    refine (norm_add_le _ _).trans ?_
    rw [add_div]
    exact add_le_add (hC c t (by linarith) (by linarith)) (hCn c t (by linarith) (by linarith))
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  -- integrability of the three pieces
  have hiG : Integrable (fun t : ℝ => F t * logDeriv Complex.Gammaℝ (c + t * I)) := by
    have h1 := integrable_Hfn_mul_logDeriv_Gammaℝ hk hkc (σ := c) (by linarith) hc2
    have h2 := integrable_Hfn_mul_logDeriv_Gammaℝ hkn2 hknc (σ := c) (by linarith) hc2
    refine (h1.add h2).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply, hF, hFm]
    ring
  have hdomF : Integrable (fun t : ℝ => (C + Cn) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hig : Integrable (fun t : ℝ => F t * gPair 0 (c + t * I)) := by
    have hcont : Continuous (fun t : ℝ => gPair 0 ((c : ℂ) + t * I)) := by
      unfold gPair
      refine Continuous.add ?_ ?_
      · refine continuous_const.div (by fun_prop) fun t h => ?_
        have := congrArg Complex.re h; simp at this; linarith
      · refine continuous_const.div (by fun_prop) fun t h => ?_
        have := congrArg Complex.re h; simp at this; linarith
    have hbd : ∀ t : ℝ, ‖gPair 0 ((c : ℂ) + t * I)‖ ≤ 1 / c + 1 / (c - 1) := by
      intro t
      unfold gPair
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_div, norm_one, sub_zero]
        refine div_le_div_of_nonneg_left zero_le_one (by linarith) ?_
        have := Complex.abs_re_le_norm ((c : ℂ) + t * I)
        rw [hre, abs_of_pos (by linarith)] at this
        exact this
      · rw [norm_div, norm_one]
        refine div_le_div_of_nonneg_left zero_le_one (by linarith) ?_
        have := Complex.abs_re_le_norm ((c : ℂ) + t * I - (1 - 0))
        have hre' : ((c : ℂ) + t * I - (1 - 0)).re = c - 1 := by simp
        rw [hre', abs_of_pos (show (0 : ℝ) < c - 1 by linarith)] at this
        exact this
    refine (hdomF.mul_const (1 / c + 1 / (c - 1))).mono'
      (hFc.mul hcont).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    calc ‖F t‖ * ‖gPair 0 ((c : ℂ) + t * I)‖ ≤ ((C + Cn) / (1 + t ^ 2)) * (1 / c + 1 / (c - 1)) :=
          mul_le_mul (hFb t) (hbd t) (norm_nonneg _) (by positivity)
      _ = (C + Cn) * (1 + t ^ 2)⁻¹ * (1 / c + 1 / (c - 1)) := by rw [div_eq_mul_inv]
  have hsumL := lseriesSummable_lamC hsl hc1
  have hLb : ∀ t : ℝ, ‖LSeries (WeilHerglotz.lamC lam) ((c : ℂ) + t * I)‖ ≤
      ∑' n, ‖LSeries.term (WeilHerglotz.lamC lam) c n‖ := by
    intro t
    have hs : LSeriesSummable (WeilHerglotz.lamC lam) ((c : ℂ) + t * I) :=
      (LSeriesSummable_iff_of_re_eq_re (by simp)).mpr hsumL
    unfold LSeries
    refine (norm_tsum_le_tsum_norm hs.norm).trans (le_of_eq (tsum_congr fun n => ?_))
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hLc : Continuous (fun t : ℝ => LSeries (WeilHerglotz.lamC lam) ((c : ℂ) + t * I)) := by
    have hcont : ∀ n : ℕ, Continuous (fun t : ℝ =>
        LSeries.term (WeilHerglotz.lamC lam) ((c : ℂ) + t * I) n) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simpa [LSeries.term_zero] using continuous_const
      · simp only [LSeries.term_of_ne_zero hn]
        refine continuous_const.div ?_ (fun t => ?_)
        · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn))
        · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
    exact continuous_tsum hcont hsumL.norm fun n t => by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]; simp
  set S : ℝ := ∑' n, ‖LSeries.term (WeilHerglotz.lamC lam) c n‖ with hS
  have hiL1 : ∀ {j : ℝ → ℂ} (Cj : ℝ), (∀ t : ℝ, ‖Hfn j (c + t * I)‖ ≤ Cj / (1 + t ^ 2)) →
      Continuous (fun t : ℝ => Hfn j (c + t * I)) →
      Integrable (fun t : ℝ => Hfn j (c + t * I) * LSeries (WeilHerglotz.lamC lam) (c + t * I)) := by
    intro j Cj hb hcj
    refine ((integrable_inv_one_add_sq.const_mul Cj).mul_const S).mono'
      (hcj.mul hLc).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    calc ‖Hfn j (c + t * I)‖ * ‖LSeries (WeilHerglotz.lamC lam) (c + t * I)‖
        ≤ (Cj / (1 + t ^ 2)) * S := mul_le_mul (hb t) (hLb t) (norm_nonneg _)
          ((norm_nonneg _).trans (hb t))
      _ = Cj * (1 + t ^ 2)⁻¹ * S := by rw [div_eq_mul_inv]
  have hiLk := hiL1 C (fun t => hC c t (by linarith) (by linarith)) (continuous_Hfn_line hk hkc c)
  have hiLn := hiL1 Cn (fun t => hCn c t (by linarith) (by linarith))
    (continuous_Hfn_line hkn2 hknc c)
  have hiL : Integrable (fun t : ℝ => F t * LSeries (WeilHerglotz.lamC lam) (c + t * I)) :=
    (hiLk.add hiLn).congr (Eventually.of_forall fun t => by
      simp only [Pi.add_apply, hF, hFm]; ring)
  -- the integral splits
  have hsplit : (∫ t : ℝ, F t * WeilHerglotz.weilFunction lam (c + t * I)) =
      (∫ t : ℝ, F t * logDeriv Complex.Gammaℝ (c + t * I)) +
        (∫ t : ℝ, F t * gPair 0 (c + t * I)) -
          ∫ t : ℝ, F t * LSeries (WeilHerglotz.lamC lam) (c + t * I) := by
    have hGg : Integrable (fun t : ℝ => F t * logDeriv Complex.Gammaℝ (c + t * I) +
        F t * gPair 0 (c + t * I)) := hiG.add hig
    rw [← integral_add hiG hig, ← integral_sub hGg hiL]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [weilFunction_eq lam (by rw [hre]; linarith)]
    ring
  -- the archimedean part
  have hG : (∫ t : ℝ, F t * logDeriv Complex.Gammaℝ (c + t * I)) =
      ∫ r : ℝ, paperFT k r * (Zeta23.EF.gammaBracket r : ℂ) := by
    rw [gamma_line_shift hk hkc hc1 hc2]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [gammaR_bracket t, Zeta23.EF.gammaBracket]
    congr 4
    ring
  -- the pole part
  have hpole : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, F t * gPair 0 (c + t * I)) =
      paperFT k (I / 2) + paperFT k (-I / 2) := by
    have h := two_line_pair (differentiable_Hfn hk hkc) (c := c) (C := C)
      (fun σ t h1 h2 => hC σ t (by linarith) (by linarith)) (z₀ := 0)
      (by simp; linarith) (by simp; linarith)
    rw [sub_zero, Hfn_zero, Hfn_one] at h
    exact h
  -- the prime part
  have hP1 := hasSum_prime_side_line hk hkc hsumL
  have hP2 := hasSum_prime_side_line hkn2 hknc hsumL
  have hprime : HasSum (fun n : ℕ => ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n)))
      ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, F t * LSeries (WeilHerglotz.lamC lam) (c + t * I)) := by
    have hint : (∫ t : ℝ, F t * LSeries (WeilHerglotz.lamC lam) (c + t * I)) =
        (∫ t : ℝ, Hfn k (c + t * I) * LSeries (WeilHerglotz.lamC lam) (c + t * I)) +
          ∫ t : ℝ, Hfn kn (c + t * I) * LSeries (WeilHerglotz.lamC lam) (c + t * I) := by
      rw [← integral_add hiLk hiLn]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [hF, hFm]
      ring
    rw [hint, mul_add]
    refine (hP1.add hP2).congr_fun fun n => ?_
    simp only [hkn, WeilHerglotz.lamC]
    split_ifs with h
    · push_cast; ring
    · simp
  rw [weilFullFunctional, hprime.tsum_eq, hsplit, hG]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [mul_sub, mul_add, hpole]
  ring

end RHTower.WeilLineIntegral
