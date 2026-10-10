import GaloisForLFunctions.RHTower.SquarefreeExponentialOneSided
import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyQuarterOmega
import GaloisForLFunctions.RHTower.MertensFrontierOneSidedOmega
import GaloisForLFunctions.RHTower.ZetaDilationCascade

/-!
# The exponentially weighted squarefree error is `Ω±(t^{-1/4})`

Let `e(t) = Σ_{n ≥ 1} μ(n)² e^{-nt} - (6/π²)/t`.

**Theorem** (`exists_sqfError_omega_pm`). There is `c₀ > 0` such that for both signs `η = ±1`,
every `C₀ < c₀` and every `t₀ > 0`, some `t ∈ (0, t₀]` has `η e(t) > C₀ t^{-1/4}`. So `e(t)` is
`Ω±(t^{-1/4})` as `t ↓ 0`, unconditionally.

**Proof.** If RH fails, a one-sided bound at `t^{-1/4}` already contradicts the receiver
`riemannHypothesis_of_sqfError_oneSided`. Assume RH and take a critical zero `ρ` of order `m`;
put `s₀ = ρ/2`, so `Re s₀ = 1/4` and `ζ(s₀) ≠ 0`. A bound `η e ≤ C₀ t^{-1/4} + K` gives, for
`C > C₀`, a nonnegative Landau measure whose transform `G` continues to `Re z > 1/4` and satisfies
`F·E = H` with `F = G + 𝓜P`, `E(z) = (z - 1)Z(2z)` and `H(z) = (2z-1)Γ(z)Z(z) - cZ(2z)`. Here
`H(s₀) = (ρ - 1)Γ(s₀)Z(s₀) ≠ 0` and `E` vanishes to order `m` at `s₀`. Positivity gives
`‖G(s₀ + r)‖ ≤ C/r + O(1)`, since `|𝓛ν(s₀+r)| ≤ 𝓛ν(1/4+r)` and the real values `G(1/4 + r)` stay
bounded. The ray lemma then forces `m = 1` and `‖H(s₀)‖ ≤ C ‖p(s₀)‖`, where `E = (z - s₀)p`.
Hence `C₀ ≥ c₀ := ‖H(s₀)‖/‖p(s₀)‖`.
-/

open Filter Topology MeasureTheory Set Complex
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
open scoped ArithmeticFunction.Moebius

namespace RHTower.SquarefreeExponential

noncomputable section

/-- Under RH the half-plane `Re z > 1/4` lies in the continuation region. -/
theorem mem_contRegion_of_riemannHypothesis (hRH : RiemannHypothesis) {z : ℂ}
    (hz : 1 / 4 < z.re) : z ∈ contRegion := by
  refine ⟨by linarith, ?_⟩
  by_cases h2 : 2 * z = 1
  · rw [h2, zetaResidueUnit_one]; exact one_ne_zero
  · rw [zetaResidueUnit, Function.update_of_ne h2]
    refine mul_ne_zero (sub_ne_zero.mpr h2) ?_
    exact (riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH) _
      (by simp only [Complex.mul_re]; norm_num; linarith)

/-- **One-sided Ω± bound at a critical zero.** Under RH, with a critical zero of order `m` written as
`ζ(z) = (z - ρ)^m g(z)`, a global one-sided bound `η e(t) ≤ C₀ t^{-1/4} + K` forces `m = 1` and
`‖H(ρ/2)‖ ≤ C₀ ‖p(ρ/2)‖`. -/
theorem norm_H_le_of_oneSided (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hz : riemannZeta ρ = 0) {m : ℕ} {g : ℂ → ℂ} (hg : ContinuousAt g ρ)
    (hfac : ∀ᶠ w in 𝓝 ρ, riemannZeta w = (w - ρ) ^ m • g w) (hm : m ≠ 0)
    {η C₀ K : ℝ} (hη : |η| = 1) (hC₀ : 0 ≤ C₀) (hK : 0 ≤ K)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, η * sqfError t ≤ C₀ * t ^ (-(1 / 4 : ℝ)) + K) :
    m = 1 ∧
      ‖(2 * (ρ / 2) - 1) * Complex.Gamma (ρ / 2) * zetaResidueUnit (ρ / 2) -
          density * zetaResidueUnit (2 * (ρ / 2))‖ ≤
        C₀ * ‖(ρ / 2 - 1) * ((2 * (ρ / 2) - 1) * (2 ^ m * g (2 * (ρ / 2))))‖ := by
  set s₀ : ℂ := ρ / 2 with hs₀
  have hs₀re : s₀.re = 1 / 4 := by rw [hs₀, Complex.div_re]; simp [hρ]; ring
  have hρ1 : ρ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hρ; norm_num at hρ
  have hs₀1 : s₀ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hs₀re; norm_num at hs₀re
  have h2s₀ : 2 * s₀ = ρ := by rw [hs₀]; ring
  have hγ : s₀.im ≠ 0 := by
    intro him
    have hreal : s₀ = ((1 / 4 : ℝ) : ℂ) := Complex.ext (by simp [hs₀re]) (by simp [him])
    have : riemannZeta ((1 / 2 : ℝ) : ℂ) = 0 := by
      rw [show ((1 / 2 : ℝ) : ℂ) = ρ by rw [← h2s₀, hreal]; push_cast; ring]; exact hz
    exact DilationCascade.riemannZeta_ofReal_ne_zero (by norm_num) (by norm_num) this
  -- the log-variable bound
  have hgK : ∀ u, 0 < u → η * logError u ≤ C₀ * Real.exp ((1 / 4 : ℝ) * u) + K := by
    intro u hu
    have hmem : Real.exp (-u) ∈ Ioc (0 : ℝ) 1 :=
      ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith)⟩
    have h := hB _ hmem
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
    rw [logError]
    convert h using 3
    ring
  -- for every `C > C₀` the conclusion holds with `C`; let `C ↓ C₀`
  have hmain : ∀ C : ℝ, C₀ < C →
      m = 1 ∧ ‖(2 * s₀ - 1) * Complex.Gamma s₀ * zetaResidueUnit s₀ -
          density * zetaResidueUnit (2 * s₀)‖ ≤
        C * ‖(s₀ - 1) * ((2 * s₀ - 1) * (2 ^ m * g (2 * s₀)))‖ := by
    intro C hC
    have hC0 : 0 < C := by linarith
    have hc := abscissa_osMeasure_eq hη (by norm_num) (by norm_num) hK hC hgK
    -- `G` agrees with the continuation on `Re z > 1/4`
    set U : Set ℂ := {z : ℂ | 1 / 4 < z.re} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hGan : AnalyticOnNhd ℂ (osTransform η C (1 / 4) K) U := by
      refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
      have hw' : (1 / 4 : ℝ) < w.re := hw
      have hwα : w - ((1 / 4 : ℝ) : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      have hw0 : w ≠ 0 := by intro h; rw [h, Complex.zero_re] at hw'; linarith
      have h1a : DifferentiableAt ℂ (fun z : ℂ => (C : ℂ) / (z - ((1 / 4 : ℝ) : ℂ))) w :=
        (differentiableAt_const _).div (differentiableAt_id.sub_const _) hwα
      have h1b : DifferentiableAt ℂ (fun z : ℂ => (K : ℂ) / z) w :=
        (differentiableAt_const _).div differentiableAt_id hw0
      have h2 := (hasDerivAt_complexLaplace hc hw').differentiableAt
      exact (((h1a.add h1b).sub h2).const_mul (η : ℂ)).differentiableWithinAt
    have hCan : AnalyticOnNhd ℂ errorCont U := fun z hz =>
      analyticOnNhd_errorCont z (mem_contRegion_of_riemannHypothesis hRH hz)
    have hagree : Set.EqOn (osTransform η C (1 / 4) K) errorCont U := by
      refine hGan.eqOn_of_preconnected_of_eventuallyEq hCan
        (convex_halfSpace_re_gt (1 / 4 : ℝ)).isPreconnected (show (2 : ℂ) ∈ U by simp [hU]; norm_num) ?_
      have hgt : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
      filter_upwards [hgt] with z hz1
      rw [osTransform_eq_mellin hη hC.le (by norm_num) hgK hz1, errorCont_eq_mellin hz1]
    -- the real values near `1/4` are bounded
    have hq : (((1 / 4 : ℝ)) : ℂ) ∈ contRegion := ofReal_mem_contRegion (by norm_num)
    have hcontC : ContinuousAt errorCont (((1 / 4 : ℝ)) : ℂ) :=
      (analyticOnNhd_errorCont _ hq).continuousAt
    have hrayR : Tendsto (fun r : ℝ => (((1 / 4 + r : ℝ)) : ℂ)) (𝓝[>] 0) (𝓝 (((1 / 4 : ℝ)) : ℂ)) := by
      have h : Tendsto (fun r : ℝ => (((1 / 4 + r : ℝ)) : ℂ)) (𝓝 0)
          (𝓝 (((1 / 4 + 0 : ℝ)) : ℂ)) :=
        (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
      rw [add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    set B₁ : ℝ := ‖errorCont (((1 / 4 : ℝ)) : ℂ)‖ + 1 with hB₁
    have hrealB : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖errorCont (((1 / 4 + r : ℝ)) : ℂ)‖ ≤ B₁ :=
      ((hcontC.tendsto.comp hrayR).norm.eventually (gt_mem_nhds (lt_add_one _))).mono
        fun r hr => hr.le
    -- the complex ray from `s₀`
    have hrayC : Tendsto (fun r : ℝ => s₀ + (r : ℂ)) (𝓝[>] 0) (𝓝 s₀) := by
      have h : Tendsto (fun r : ℝ => s₀ + (r : ℂ)) (𝓝 0) (𝓝 (s₀ + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      rw [Complex.ofReal_zero, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    set B₂ : ℝ := ‖mellin tailPiece s₀‖ + 1 with hB₂
    have htailB : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖mellin tailPiece (s₀ + r)‖ ≤ B₂ :=
      ((((differentiableAt_mellin_tailPiece s₀).continuousAt).tendsto.comp hrayC).norm.eventually
        (gt_mem_nhds (lt_add_one _))).mono fun r hr => hr.le
    -- the bound on `F = G + 𝓜P` along the ray
    set F : ℂ → ℂ := fun z => osTransform η C (1 / 4) K z + mellin tailPiece z with hF
    have hη2 : (η : ℂ) * η = 1 := by
      have := sq_abs η
      rw [hη] at this
      exact_mod_cast (by nlinarith : η * η = 1)
    have hFbound : ∀ᶠ r : ℝ in 𝓝[>] 0,
        ‖F (s₀ + r)‖ ≤ C * r ^ (-((1 : ℕ) : ℝ)) +
          (2 * C / |s₀.im| + 8 * K + B₁ + B₂) := by
      filter_upwards [hrealB, htailB, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr1 hr2 hrI
      have hr0 : 0 < r := hrI.1
      have hzre : (s₀ + (r : ℂ)).re = 1 / 4 + r := by simp [hs₀re]
      have hzim : (s₀ + (r : ℂ)).im = s₀.im := by simp
      -- the Laplace transform is dominated by its real values
      have hLap : ‖complexLaplace (osMeasure η C (1 / 4) K) (s₀ + r)‖ ≤
          laplaceReal (osMeasure η C (1 / 4) K) (1 / 4 + r) := by
        have h := norm_complexLaplace_le (osMeasure η C (1 / 4) K) (s₀ + r)
        rw [hzre] at h
        exact h
      have hrealmem : (((1 / 4 + r : ℝ)) : ℂ) ∈ U := by simp [hU]; linarith
      have hLapReal : laplaceReal (osMeasure η C (1 / 4) K) (1 / 4 + r) ≤ C / r + 4 * K + B₁ := by
        have hcl := RHTower.complexLaplace_ofReal (osMeasure η C (1 / 4) K) (1 / 4 + r)
        have hdef : complexLaplace (osMeasure η C (1 / 4) K) (((1 / 4 + r : ℝ)) : ℂ) =
            (C : ℂ) / ((((1 / 4 + r : ℝ)) : ℂ) - ((1 / 4 : ℝ) : ℂ)) +
              (K : ℂ) / (((1 / 4 + r : ℝ)) : ℂ) -
              η * osTransform η C (1 / 4) K (((1 / 4 + r : ℝ)) : ℂ) := by
          rw [osTransform]
          linear_combination (-(complexLaplace (osMeasure η C (1 / 4) K)
            (((1 / 4 + r : ℝ)) : ℂ)) + (C : ℂ) / ((((1 / 4 + r : ℝ)) : ℂ) - ((1 / 4 : ℝ) : ℂ)) +
              (K : ℂ) / (((1 / 4 + r : ℝ)) : ℂ)) * hη2
        rw [hagree hrealmem] at hdef
        have hnorm := congrArg norm hcl
        rw [Complex.norm_real, Real.norm_eq_abs, hdef] at hnorm
        have hlap0 : laplaceReal (osMeasure η C (1 / 4) K) (1 / 4 + r) ≤
            |laplaceReal (osMeasure η C (1 / 4) K) (1 / 4 + r)| := le_abs_self _
        rw [← hnorm] at hlap0
        refine hlap0.trans ?_
        have e1 : ‖(C : ℂ) / ((((1 / 4 + r : ℝ)) : ℂ) - ((1 / 4 : ℝ) : ℂ))‖ = C / r := by
          rw [show (((1 / 4 + r : ℝ)) : ℂ) - ((1 / 4 : ℝ) : ℂ) = ((r : ℝ) : ℂ) by push_cast; ring,
            norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hC0.le,
            Real.norm_of_nonneg hr0.le]
        have e2 : ‖(K : ℂ) / (((1 / 4 + r : ℝ)) : ℂ)‖ ≤ 4 * K := by
          rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hK,
            Real.norm_of_nonneg (by linarith), div_le_iff₀ (by linarith)]
          nlinarith
        have e3 : ‖(η : ℂ) * errorCont (((1 / 4 + r : ℝ)) : ℂ)‖ ≤ B₁ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul]; exact hr1
        calc ‖(C : ℂ) / ((((1 / 4 + r : ℝ)) : ℂ) - ((1 / 4 : ℝ) : ℂ)) +
              (K : ℂ) / (((1 / 4 + r : ℝ)) : ℂ) - η * errorCont (((1 / 4 + r : ℝ)) : ℂ)‖
            ≤ ‖(C : ℂ) / ((((1 / 4 + r : ℝ)) : ℂ) - ((1 / 4 : ℝ) : ℂ))‖ +
                ‖(K : ℂ) / (((1 / 4 + r : ℝ)) : ℂ)‖ +
                ‖(η : ℂ) * errorCont (((1 / 4 + r : ℝ)) : ℂ)‖ := norm_sub_le_of_le
                  (norm_add_le _ _) le_rfl
          _ ≤ C / r + 4 * K + B₁ := by rw [e1]; linarith
      -- the two rational terms at the complex point
      have hd1 : ‖(C : ℂ) / (s₀ + r - ((1 / 4 : ℝ) : ℂ))‖ ≤ 2 * C / |s₀.im| := by
        have hlow : |s₀.im| ≤ ‖s₀ + r - ((1 / 4 : ℝ) : ℂ)‖ := by
          have := Complex.abs_im_le_norm (s₀ + r - ((1 / 4 : ℝ) : ℂ))
          simpa using this
        have hpos : 0 < |s₀.im| := abs_pos.mpr hγ
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hC0.le]
        calc C / ‖s₀ + r - ((1 / 4 : ℝ) : ℂ)‖ ≤ C / |s₀.im| :=
              div_le_div_of_nonneg_left hC0.le hpos hlow
          _ ≤ 2 * C / |s₀.im| := by
              apply div_le_div_of_nonneg_right _ hpos.le; linarith
      have hd2 : ‖(K : ℂ) / (s₀ + r)‖ ≤ 4 * K := by
        have hlow : 1 / 4 ≤ ‖s₀ + (r : ℂ)‖ := by
          have := Complex.re_le_norm (s₀ + (r : ℂ))
          rw [hzre] at this
          linarith
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hK,
          div_le_iff₀ (by linarith)]
        nlinarith
      have hG : ‖osTransform η C (1 / 4) K (s₀ + r)‖ ≤ C / r + (2 * C / |s₀.im| + 8 * K + B₁) := by
        rw [osTransform, norm_mul, Complex.norm_real, Real.norm_eq_abs, hη, one_mul]
        calc ‖(C : ℂ) / (s₀ + r - ((1 / 4 : ℝ) : ℂ)) + (K : ℂ) / (s₀ + r) -
              complexLaplace (osMeasure η C (1 / 4) K) (s₀ + r)‖
            ≤ ‖(C : ℂ) / (s₀ + r - ((1 / 4 : ℝ) : ℂ))‖ + ‖(K : ℂ) / (s₀ + r)‖ +
                ‖complexLaplace (osMeasure η C (1 / 4) K) (s₀ + r)‖ :=
              norm_sub_le_of_le (norm_add_le _ _) le_rfl
          _ ≤ 2 * C / |s₀.im| + 4 * K + (C / r + 4 * K + B₁) := by
              gcongr
              exact hLap.trans hLapReal
          _ = C / r + (2 * C / |s₀.im| + 8 * K + B₁) := by ring
      have hpow : r ^ (-((1 : ℕ) : ℝ)) = 1 / r := by
        rw [Nat.cast_one, Real.rpow_neg_one, one_div]
      calc ‖F (s₀ + r)‖ ≤ ‖osTransform η C (1 / 4) K (s₀ + r)‖ + ‖mellin tailPiece (s₀ + r)‖ :=
            norm_add_le _ _
        _ ≤ C / r + (2 * C / |s₀.im| + 8 * K + B₁) + B₂ := add_le_add hG hr2
        _ = C * r ^ (-((1 : ℕ) : ℝ)) + (2 * C / |s₀.im| + 8 * K + B₁ + B₂) := by
            rw [hpow]; ring
    -- the factorisation and the identity along the ray
    set P : ℂ → ℂ := fun z => (z - 1) * ((2 * z - 1) * (2 ^ m * g (2 * z))) with hP
    have hdouble : Tendsto (fun z : ℂ => 2 * z) (𝓝 s₀) (𝓝 ρ) := by
      have := (continuous_const_mul (2 : ℂ)).tendsto s₀
      rwa [h2s₀] at this
    have hPc : ContinuousAt P s₀ := by
      have hgc : ContinuousAt (fun z : ℂ => g (2 * z)) s₀ := by
        rw [ContinuousAt, h2s₀]; exact hg.tendsto.comp hdouble
      exact (continuousAt_id.sub continuousAt_const).mul
        (((continuousAt_const.mul continuousAt_id).sub continuousAt_const).mul
          (continuousAt_const.mul hgc))
    have hEfac : ∀ᶠ z in 𝓝 s₀,
        (z - 1) * zetaResidueUnit (2 * z) = (z - s₀) ^ m * P z := by
      have hne : ∀ᶠ z in 𝓝 s₀, 2 * z ≠ 1 :=
        hdouble.eventually (isOpen_compl_singleton.mem_nhds hρ1)
      filter_upwards [hdouble.eventually hfac, hne] with z hz1 hz2
      rw [zetaResidueUnit, Function.update_of_ne hz2, hz1, smul_eq_mul, hP]
      have : 2 * z - ρ = 2 * (z - s₀) := by rw [← h2s₀]; ring
      rw [this, mul_pow]
      ring
    set H : ℂ → ℂ := fun z => (2 * z - 1) * Complex.Gamma z * zetaResidueUnit z -
      density * zetaResidueUnit (2 * z) with hHdef
    have hHc : ContinuousAt H s₀ := by
      have hΓ : ContinuousAt Complex.Gamma s₀ :=
        (Complex.differentiableAt_Gamma s₀ fun k hk => by
          have hre := congrArg Complex.re hk
          simp only [Complex.neg_re, Complex.natCast_re] at hre
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith [hs₀re]).continuousAt
      exact ((((continuousAt_const.mul continuousAt_id).sub continuousAt_const).mul hΓ).mul
        (analyticAt_zetaResidueUnit s₀).continuousAt).sub
        (continuousAt_const.mul ((analyticAt_zetaResidueUnit (2 * s₀)).continuousAt.comp
          (continuous_const.mul continuous_id).continuousAt))
    have hFE : ∀ᶠ r : ℝ in 𝓝[>] 0,
        F (s₀ + r) * ((s₀ + r - 1) * zetaResidueUnit (2 * (s₀ + r))) = H (s₀ + r) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : (0 : ℝ) < r := hr
      have hid := os_pole_cleared_identity hη (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num) hK hC
        hgK (s := s₀ + r) (by simp [hs₀re]; linarith)
      simp only [hF, hHdef]
      linear_combination hid
    have hHs₀ : H s₀ ≠ 0 := by
      have hZρ : zetaResidueUnit (2 * s₀) = 0 := by
        rw [h2s₀, zetaResidueUnit, Function.update_of_ne hρ1, hz, mul_zero]
      simp only [hHdef, hZρ, mul_zero, sub_zero]
      have hΓ : Complex.Gamma s₀ ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hs₀re]; norm_num)
      have hζ : riemannZeta s₀ ≠ 0 :=
        SquarefreeDiscrepancy.riemannZeta_ne_zero_of_re_quarter hRH hs₀re
      rw [zetaResidueUnit, Function.update_of_ne hs₀1, h2s₀]
      exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hρ1) hΓ)
        (mul_ne_zero (sub_ne_zero.mpr hs₀1) hζ)
    -- the order must be `1`
    have hm1 : m = 1 := by
      by_contra hne
      have hlt : ((1 : ℕ) : ℝ) < m := by
        have : 2 ≤ m := by omega
        exact_mod_cast (show 1 < m by omega)
      exact hHs₀ (eq_zero_of_ray_bigO_lt (E := fun z => (z - 1) * zetaResidueUnit (2 * z))
        (F := F) (H := H) (p := P) hm hlt hPc hEfac hHc hFE hFbound)
    refine ⟨hm1, ?_⟩
    subst hm1
    have h := norm_le_of_ray_bigO (E := fun z => (z - 1) * zetaResidueUnit (2 * z))
      (F := F) (H := H) (p := P) one_ne_zero hPc hEfac hHc hFE hFbound
    simpa [hHdef, hP] using h
  -- pass to the limit `C ↓ C₀`
  obtain ⟨hm1, -⟩ := hmain (C₀ + 1) (by linarith)
  refine ⟨hm1, ?_⟩
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  set Pn : ℝ := ‖(s₀ - 1) * ((2 * s₀ - 1) * (2 ^ m * g (2 * s₀)))‖ with hPn
  have hPn0 : 0 ≤ Pn := norm_nonneg _
  set C : ℝ := C₀ + δ / (Pn + 1) with hCdef
  have hC : C₀ < C := by rw [hCdef]; have : 0 < δ / (Pn + 1) := by positivity
                         linarith
  have h := (hmain C hC).2
  calc _ ≤ C * Pn := h
    _ = C₀ * Pn + δ * (Pn / (Pn + 1)) := by rw [hCdef]; ring
    _ < C₀ * Pn + δ := by
        have : Pn / (Pn + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        nlinarith

/-- **`e(t) = Ω±(t^{-1/4})`**, unconditionally. -/
theorem exists_sqfError_omega_pm :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ η C₀ : ℝ, |η| = 1 → C₀ < c₀ → ∀ t₀ : ℝ, 0 < t₀ →
      ∃ t ∈ Ioc (0 : ℝ) t₀, C₀ * t ^ (-(1 / 4 : ℝ)) < η * sqfError t := by
  -- a local bound on `(0, t₀]` is a global bound with an additive constant
  have hglobal : ∀ η C₀ t₀ : ℝ, |η| = 1 → 0 < t₀ →
      (∀ t ∈ Ioc (0 : ℝ) t₀, η * sqfError t ≤ C₀ * t ^ (-(1 / 4 : ℝ))) →
      ∀ t ∈ Ioc (0 : ℝ) 1, η * sqfError t ≤ max C₀ 0 * t ^ (-(1 / 4 : ℝ)) + 1 / t₀ := by
    intro η C₀ t₀ hη ht₀ hloc t ht
    have hpow : 0 ≤ t ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg ht.1.le _
    have hmax : C₀ * t ^ (-(1 / 4 : ℝ)) ≤ max C₀ 0 * t ^ (-(1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
    have hmax0 : 0 ≤ max C₀ 0 * t ^ (-(1 / 4 : ℝ)) := mul_nonneg (le_max_right _ _) hpow
    have hinv : 0 ≤ 1 / t₀ := by positivity
    rcases le_or_gt t t₀ with htt | htt
    · linarith [hloc t ⟨ht.1, htt⟩]
    · have habs : η * sqfError t ≤ 1 / t := by
        calc η * sqfError t ≤ |η * sqfError t| := le_abs_self _
          _ = |sqfError t| := by rw [abs_mul, hη, one_mul]
          _ ≤ 1 / t := abs_sqfError_le ht.1
      have : 1 / t ≤ 1 / t₀ := one_div_le_one_div_of_le ht₀ htt.le
      linarith
  by_cases hRH : RiemannHypothesis
  · obtain ⟨ρ, hρ, hz⟩ := ZetaMultiple.exists_riemannZeta_zero_re_half
    have hρ1 : ρ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hρ; norm_num at hρ
    have hρpos : 0 < ρ.re := by rw [hρ]; norm_num
    have hρlt : ρ.re < 1 := by rw [hρ]; norm_num
    have hfin : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
      rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hρpos, hρlt⟩]
      exact xi_orderAt_ne_top ρ
    set m : ℕ := (analyticOrderAt riemannZeta ρ).toNat with hm
    have hcoe : (m : ℕ∞) = analyticOrderAt riemannZeta ρ := ENat.coe_toNat hfin
    obtain ⟨g, hg, hgρ, hfac⟩ :=
      ((analyticOn_riemannZeta ρ hρ1).analyticOrderAt_eq_natCast).mp hcoe.symm
    have hm0 : m ≠ 0 := by
      intro h
      have hzero : analyticOrderAt riemannZeta ρ = 0 := by rw [← hcoe, h]; rfl
      rw [analyticOrderAt_eq_zero] at hzero
      rcases hzero with h' | h'
      exacts [h' (analyticOn_riemannZeta ρ hρ1), h' hz]
    set s₀ : ℂ := ρ / 2 with hs₀
    set Hn : ℝ := ‖(2 * s₀ - 1) * Complex.Gamma s₀ * zetaResidueUnit s₀ -
        density * zetaResidueUnit (2 * s₀)‖ with hHn
    set Pn : ℝ := ‖(s₀ - 1) * ((2 * s₀ - 1) * (2 ^ m * g (2 * s₀)))‖ with hPn
    have hs₀re : s₀.re = 1 / 4 := by rw [hs₀, Complex.div_re]; simp [hρ]; ring
    have hs₀1 : s₀ ≠ 1 := by intro h1; rw [h1, Complex.one_re] at hs₀re; norm_num at hs₀re
    have h2s₀ : 2 * s₀ = ρ := by rw [hs₀]; ring
    have hHn0 : 0 < Hn := by
      rw [hHn, norm_pos_iff]
      have hZρ : zetaResidueUnit (2 * s₀) = 0 := by
        rw [h2s₀, zetaResidueUnit, Function.update_of_ne hρ1, hz, mul_zero]
      rw [hZρ, mul_zero, sub_zero]
      have hΓ : Complex.Gamma s₀ ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hs₀re]; norm_num)
      have hζ : riemannZeta s₀ ≠ 0 :=
        SquarefreeDiscrepancy.riemannZeta_ne_zero_of_re_quarter hRH hs₀re
      rw [zetaResidueUnit, Function.update_of_ne hs₀1, h2s₀]
      exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hρ1) hΓ)
        (mul_ne_zero (sub_ne_zero.mpr hs₀1) hζ)
    have hPn0 : 0 < Pn := by
      rw [hPn, norm_pos_iff, h2s₀]
      refine mul_ne_zero (sub_ne_zero.mpr hs₀1) (mul_ne_zero (sub_ne_zero.mpr hρ1)
        (mul_ne_zero (pow_ne_zero _ two_ne_zero) hgρ))
    refine ⟨Hn / Pn, div_pos hHn0 hPn0, fun η C₀ hη hC₀ t₀ ht₀ => ?_⟩
    by_contra hall
    simp only [not_exists, not_and, not_lt] at hall
    have hB := hglobal η C₀ t₀ hη ht₀ hall
    have h := (norm_H_le_of_oneSided hRH hρ hz hg.continuousAt hfac hm0 hη (le_max_right C₀ 0)
      (by positivity) hB).2
    rw [← hs₀] at h
    have hlt : max C₀ 0 < Hn / Pn := max_lt hC₀ (div_pos hHn0 hPn0)
    have : max C₀ 0 * Pn < Hn := by rwa [lt_div_iff₀ hPn0] at hlt
    linarith
  · refine ⟨1, one_pos, fun η C₀ hη _ t₀ ht₀ => ?_⟩
    by_contra hall
    simp only [not_exists, not_and, not_lt] at hall
    apply hRH
    have hB := hglobal η C₀ t₀ hη ht₀ hall
    refine riemannHypothesis_of_sqfError_oneSided hη fun ε hε => ⟨max C₀ 0 + 1 / t₀, fun t ht => ?_⟩
    have hp1 : t ^ (-(1 / 4 : ℝ)) ≤ t ^ (-(1 / 4 + ε)) :=
      Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by linarith)
    have hp0 : 1 ≤ t ^ (-(1 / 4 + ε)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 (by linarith)
    have hinv : 0 ≤ 1 / t₀ := by positivity
    calc η * sqfError t ≤ max C₀ 0 * t ^ (-(1 / 4 : ℝ)) + 1 / t₀ := hB t ht
      _ ≤ max C₀ 0 * t ^ (-(1 / 4 + ε)) + 1 / t₀ * t ^ (-(1 / 4 + ε)) :=
          add_le_add (mul_le_mul_of_nonneg_left hp1 (le_max_right _ _))
            (le_mul_of_one_le_right hinv hp0)
      _ = (max C₀ 0 + 1 / t₀) * t ^ (-(1 / 4 + ε)) := by ring

end

end RHTower.SquarefreeExponential
