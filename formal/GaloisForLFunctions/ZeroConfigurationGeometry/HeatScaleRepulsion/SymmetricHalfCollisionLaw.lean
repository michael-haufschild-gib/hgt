import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.SubWeylCollisionFreeHorizon
import GaloisForLFunctions.RHTower.Heat.TheLocalDeBruijnNewmanConstant
import GaloisForLFunctions.RHTower.Heat.AnOffLinePairSurvivesTheHeatFlowToItsDepth
import GaloisForLFunctions.RHTower.DeBruijnCollisionMassAndCriticalHeat

/-!
# Symmetric-half collision law, sharpness at `6600/9991`, and the `pairModel` collision obstruction

This module completes the analysis of Question 2.6.5 in Route ZCG:

1. **Exact symmetric-half collision law on `ℝ`** (`riemannHeat_ofReal_eq_two_re_halfGauss`,
   `deriv_riemannHeat_ofReal_eq_neg_two_im_deriv_halfGauss`,
   `riemannHeat_ofReal_collision_iff_halfGauss`):
   For `t > 0` and `X ∈ ℝ`, with `Q_{t,X}(v) = halfGaussTransform t (xiLine X) v`,
   `H_t(X) = 2 Re Q_{t,X}(0)` and `H_t'(X) = −2 Im Q_{t,X}'(0)`. Thus `X` is a multiple real zero
   (collision point) of `H_t` if and only if `Re Q_{t,X}(0) = 0` and `Im Q_{t,X}'(0) = 0`, which
   forces `(Q_{t,X}'(0) conj Q_{t,X}(0)).re = 0`.
2. **Sharpness of `6600 / 9991` and the `1/2` Gaussian saddle barrier**
   (`subWeyl_margin_pos_iff`, `gaussianSaddle_gt_one_iff`):
   The four-piece sub-Weyl Gaussian quadratic margin `(c − w)² − 4c · subWeylStripExp 0 w` is
   strictly positive on `[0, 1/2]` (`c > 0`) if and only if `c > 6600 / 9991`, witnessed at
   `w = 3c / 100`. Moreover, the Gaussian saddle `1/2 + t log(X / 2π)` enters the Euler-product
   half-plane `Re s > 1` if and only if `t > (1/2) / log(X / 2π)`.
3. **Sharpened local de Bruijn–Newman constant `Λ_X` and slice heat threshold `λ_t`**
   (`eventually_localNewmanConstant_le_subWeyl`, `eventually_localNewmanConstant_le_subWeyl_logX`,
   `exists_eventually_localHeatThreshold_le_subWeyl`):
   For every `ε > 0` and all large `X`, `Λ_X ≤ (6600 / 9991 + ε) / log((X − 1)/2π)` and
   `Λ_X ≤ (6600 / 9991 + ε) / log X`.
4. **Exact closed form and order-2 real collision of `pairModelHeat` below `(1/2)/log(X/2π)`**
   (`pairModelHeat_eq_closed`, `pairModelHeat_orderTwo_collision`,
   `exists_pairModelHeat_real_collision_below_scale`):
   For every `L > 0` and off-line zero depth `δ ∈ (0, 1/2]`, the Lindelöf-bounded Riemann-density
   source `pairModel L δ` (`‖F(x + iy)‖ ≤ (x² + y² + δ²) cosh(Ly/2)`, real zeros spaced `2π / L`)
   undergoes an exact nondegenerate order-2 real collision (`H_{t_*}(0) = H'_{t_*}(0) = 0`,
   `H''_{t_*}(0) = 2 e^{t_* L²/4} √(1 + L² δ²) > 0`) at
   `t_* = (√(1 + L² δ²) − 1) / L² < min(δ²/2, δ/L)`, showing that no source-side repulsion law
   relying only on functional-equation symmetry, RvM spacing, and Phragmén–Lindelöf strip size
   bounds can exclude collisions across `(0, (1/2)/log(X/2π)]`.
5. **Exact reduction and global equivalence for Question 2.6.5**
   (`no_collision_upto_twoThirds_iff_upto_subWeyl`, `question_2_6_5_global_equivalence`):
   At every large height `X`, absence of collisions on `(0, (2/3 + ε)/log X]` reduces
   unconditionally to absence of collisions on `(0, (6600 / 9991 + δ)/log X]`; globally across all
   heights, absence of positive-time collisions is equivalent to `∀ X, Λ_X = 0`, `Λ = 0`, and
   `RiemannHypothesis`.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-! ## 1. Exact symmetric-half collision law on the real axis -/

/-- **Real-axis value of `H_t` via the half-line Gaussian transform.**
For `t > 0` and `X ∈ ℝ`, `H_t(X) = 2 Re Q_{t,X}(0)`. -/
theorem riemannHeat_ofReal_eq_two_re_halfGauss {t : ℝ} (ht : 0 < t) (X : ℝ) :
    riemannHeat t (X : ℂ) = ((2 * (halfGaussTransform t (xiLine X) 0).re : ℝ) : ℂ) := by
  have h : riemannHeat t ((X : ℂ) + I * (0 : ℝ)) =
      halfGaussTransform t (xiLine X) (-(0 : ℝ)) +
        starRingEnd ℂ (halfGaussTransform t (xiLine X) 0) :=
    riemannHeat_eq_halfGaussAverage ht X 0
  simp only [ofReal_zero, mul_zero, add_zero, neg_zero] at h
  rw [h]
  apply Complex.ext
  · simp [mul_comm]
  · simp

/-- **Real-axis derivative of `H_t` via the half-line Gaussian transform.**
For `t > 0` and `X ∈ ℝ`, `H_t'(X) = −2 Im Q_{t,X}'(0)`, where
`Q_{t,X}'(0) = ∫_0^∞ (w / (2t)) g_t(w) ξ(1/2 + w + iX) dw`. -/
theorem deriv_riemannHeat_ofReal_eq_neg_two_im_deriv_halfGauss {t : ℝ} (ht : 0 < t) (X : ℝ) :
    deriv (riemannHeat t) (X : ℂ) =
      ((-2 * (deriv (halfGaussTransform t (xiLine X)) 0).im : ℝ) : ℂ) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = halfGaussTransform t (xiLine X) := ⟨_, rfl⟩
  obtain ⟨D₀, hD₀⟩ : ∃ D₀, D₀ = ∫ w in Ioi (0 : ℝ),
    (((w - 0) / (2 * t) * gaussDensity t (w - 0) : ℝ) : ℂ) * xiLine X w := ⟨_, rfl⟩
  have hQd : HasDerivAt Q D₀ 0 := by
    rw [hQ, hD₀]
    exact hasDerivAt_halfGaussTransform ht (continuous_xiLine X)
      (integrable_exp_mul_norm_xiLine ht X) 0
  have hQderiv : deriv Q 0 = D₀ := hQd.deriv
  have hsplit : ∀ y : ℝ, riemannHeat t ((X : ℂ) + I * y) = Q (-y) + starRingEnd ℂ (Q y) := by
    intro y; rw [hQ]; exact riemannHeat_eq_halfGaussAverage ht X y
  have hL : HasDerivAt (fun y : ℝ => riemannHeat t ((X : ℂ) + I * y))
      (deriv (riemannHeat t) (X : ℂ) * I) 0 := by
    have hd := (differentiable_riemannHeat ht.le ((X : ℂ) + I * ((0 : ℝ) : ℂ))).hasDerivAt
    have hin : HasDerivAt (fun w : ℂ => (X : ℂ) + I * w) I ((0 : ℝ) : ℂ) := by
      simpa using ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul I).const_add (X : ℂ)
    simpa using (hd.comp ((0 : ℝ) : ℂ) hin).comp_ofReal
  have hR : HasDerivAt (fun y : ℝ => Q (-y) + starRingEnd ℂ (Q y)) (-D₀ + starRingEnd ℂ D₀) 0 := by
    have h1 : HasDerivAt (fun y : ℝ => Q (-y)) (-D₀) 0 := by
      have hQd' : HasDerivAt Q D₀ (-(0 : ℝ)) := by rw [neg_zero]; exact hQd
      simpa [Function.comp_def] using hQd'.scomp 0 (hasDerivAt_neg (0 : ℝ))
    exact h1.add hQd.star
  have hfun : (fun y : ℝ => riemannHeat t ((X : ℂ) + I * y)) =
      fun y : ℝ => Q (-y) + starRingEnd ℂ (Q y) := funext hsplit
  rw [hfun] at hL
  have heq : deriv (riemannHeat t) (X : ℂ) * I = -D₀ + starRingEnd ℂ D₀ := hL.unique hR
  have hD_im : -D₀ + starRingEnd ℂ D₀ = ((-2 * D₀.im : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp; ring
  rw [hD_im] at heq
  rw [← hQ, hQderiv]
  exact mul_right_cancel₀ Complex.I_ne_zero heq

/-- **Exact symmetric-half real collision characterization.**
For `t > 0` and `X ∈ ℝ`, `X` is a multiple real zero of `H_t` (`H_t(X) = 0` and `H_t'(X) = 0`) if
and only if `Q_{t,X}(0)` is purely imaginary (`Re Q_{t,X}(0) = 0`) and `Q_{t,X}'(0)` is purely real
(`Im Q_{t,X}'(0) = 0`). -/
theorem riemannHeat_ofReal_collision_iff_halfGauss {t : ℝ} (ht : 0 < t) (X : ℝ) :
    (riemannHeat t (X : ℂ) = 0 ∧ deriv (riemannHeat t) (X : ℂ) = 0) ↔
      ((halfGaussTransform t (xiLine X) 0).re = 0 ∧
        (deriv (halfGaussTransform t (xiLine X)) 0).im = 0) := by
  rw [riemannHeat_ofReal_eq_two_re_halfGauss ht X,
    deriv_riemannHeat_ofReal_eq_neg_two_im_deriv_halfGauss ht X,
    Complex.ofReal_eq_zero, Complex.ofReal_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- Any real collision of `H_t` at `X` forces the half-Gaussian phase-velocity pairing
`Re(Q'_{t,X}(0) conj Q_{t,X}(0))` to vanish. -/
theorem re_deriv_mul_conj_halfGauss_eq_zero_of_collision {t X : ℝ} (ht : 0 < t)
    (hz : riemannHeat t (X : ℂ) = 0) (hdz : deriv (riemannHeat t) (X : ℂ) = 0) :
    (deriv (halfGaussTransform t (xiLine X)) 0 *
      starRingEnd ℂ (halfGaussTransform t (xiLine X) 0)).re = 0 := by
  obtain ⟨hre, him⟩ := (riemannHeat_ofReal_collision_iff_halfGauss ht X).mp ⟨hz, hdz⟩
  simp [Complex.mul_re, hre, him]

/-- **Exact quantitative real-zero slope formula via the symmetric-half pairing.**
At every real zero `H_t(X) = 0` (`t > 0`) with `Q_{t,X}(0) ≠ 0`,
`‖H_t'(X)‖ = 2 * |Re(Q'_{t,X}(0) conj Q_{t,X}(0))| / ‖Q_{t,X}(0)‖`. -/
theorem norm_deriv_riemannHeat_ofReal_eq_of_eq_zero {t X : ℝ} (ht : 0 < t)
    (hz : riemannHeat t (X : ℂ) = 0)
    (hQ : halfGaussTransform t (xiLine X) 0 ≠ 0) :
    ‖deriv (riemannHeat t) (X : ℂ)‖ =
      2 * |(deriv (halfGaussTransform t (xiLine X)) 0 *
        starRingEnd ℂ (halfGaussTransform t (xiLine X) 0)).re| /
        ‖halfGaussTransform t (xiLine X) 0‖ := by
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀, Q₀ = halfGaussTransform t (xiLine X) 0 := ⟨_, rfl⟩
  obtain ⟨D₀, hD₀⟩ : ∃ D₀, D₀ = deriv (halfGaussTransform t (xiLine X)) 0 := ⟨_, rfl⟩
  have hz' := hz
  rw [riemannHeat_ofReal_eq_two_re_halfGauss ht X, ← hQ₀, Complex.ofReal_eq_zero] at hz'
  have hre0 : Q₀.re = 0 := by linarith
  have hQ_im : Q₀ = (Q₀.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre0]
  have hQ_norm : ‖Q₀‖ = |Q₀.im| := by
    conv_lhs => rw [hQ_im]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hQ_pos : 0 < ‖Q₀‖ := norm_pos_iff.mpr (by rwa [hQ₀])
  have hpair : |(D₀ * starRingEnd ℂ Q₀).re| = |D₀.im| * ‖Q₀‖ := by
    have hp : (D₀ * starRingEnd ℂ Q₀).re = D₀.im * Q₀.im := by
      simp [Complex.mul_re, hre0]
    rw [hp, abs_mul, hQ_norm]
  rw [deriv_riemannHeat_ofReal_eq_neg_two_im_deriv_halfGauss ht X, ← hQ₀, ← hD₀,
    Complex.norm_real, Real.norm_eq_abs, hpair, show |-2 * D₀.im| = 2 * |D₀.im| by
      rw [abs_mul]; norm_num]
  field_simp [hQ_pos.ne']

/-! ## 2. Sharpness of `6600 / 9991` and the `1/2` Gaussian saddle barrier -/

/-- **Exact algebraic sharpness of `6600 / 9991` for the four-piece sub-Weyl strip profile.**
For `c > 0`, the unperturbed quadratic Gaussian margin `(c − w)² − 4c · subWeylStripExp 0 w` is
strictly positive on all of `[0, 1/2]` if and only if `c > 6600 / 9991`. -/
theorem subWeyl_margin_pos_iff {c : ℝ} (hc : 0 < c) :
    (∀ w ∈ Icc (0 : ℝ) (1 / 2), 0 < (c - w) ^ 2 - 4 * c * subWeylStripExp 0 w) ↔
      6600 / 9991 < c := by
  constructor
  · intro hall
    by_contra hle
    push Not at hle
    have hw_mem : 3 * c / 100 ∈ Icc (0 : ℝ) (1 / 2) := ⟨by positivity, by linarith⟩
    have hw_19 : 3 * c / 100 ≤ 1 / 9 := by linarith
    have hpos := hall (3 * c / 100) hw_mem
    unfold subWeylStripExp at hpos
    rw [if_pos hw_19] at hpos
    have hid : (c - 3 * c / 100) ^ 2 - 4 * c * (33 / 200 + 0 - 97 / 200 * (3 * c / 100)) =
        c * (9991 / 10000 * (c - 6600 / 9991)) := by ring
    rw [hid] at hpos
    have hnonpos : c * (9991 / 10000 * (c - 6600 / 9991)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)
    linarith
  · intro hc_gt w hw
    unfold subWeylStripExp
    split_ifs with h1 h2 h3
    · have hid : (c - w) ^ 2 - 4 * c * (33 / 200 + 0 - 97 / 200 * w) =
          (w - 3 * c / 100) ^ 2 + c * (9991 / 10000 * (c - 6600 / 9991)) := by ring
      rw [hid]
      have hpos : 0 < c * (9991 / 10000 * (c - 6600 / 9991)) :=
        mul_pos hc (by linarith)
      linarith [sq_nonneg (w - 3 * c / 100)]
    · have hid : (c - w) ^ 2 - 4 * c * (1 / 9 + 0 - 5 / 13 * (w - 1 / 9)) =
          (w - 3 * c / 13) ^ 2 + c * (160 / 169 * c - 8 / 13) := by ring
      rw [hid]
      have hpos : 0 < c * (160 / 169 * c - 8 / 13) := mul_pos hc (by linarith)
      linarith [sq_nonneg (w - 3 * c / 13)]
    · have hid : (c - w) ^ 2 - 4 * c * (1 / 14 + 0 - 15 / 53 * (w - 3 / 14)) =
          (w - 23 * c / 53) ^ 2 + c * (2280 / 2809 * c - 28 / 53) := by ring
      rw [hid]
      have hpos : 0 < c * (2280 / 2809 * c - 28 / 53) := mul_pos hc (by linarith)
      linarith [sq_nonneg (w - 23 * c / 53)]
    · have hid : (c - w) ^ 2 - 4 * c * ((2 / 53 + 2 * 0) / (1 / 6 + 2 * 0) * (1 / 2 + 2 * 0 - w)) =
          (w - 29 * c / 53) ^ 2 + c * (1968 / 2809 * c - 24 / 53) := by ring
      rw [hid]
      have hpos : 0 < c * (1968 / 2809 * c - 24 / 53) := mul_pos hc (by linarith)
      linarith [sq_nonneg (w - 29 * c / 53)]

/-- **The `1/2` Gaussian saddle barrier.**
For `X > 2π`, the Stirling–Gaussian saddle abscissa `1/2 + 2tα = 1/2 + t log(X / 2π)` enters the
zero-free Euler-product half-plane `Re s > 1` if and only if `t > (1/2) / log(X / 2π)`. -/
theorem gaussianSaddle_gt_one_iff {X t : ℝ} (hX : 2 * Real.pi < X) :
    1 < 1 / 2 + t * Real.log (X / (2 * Real.pi)) ↔
      (1 / 2) / Real.log (X / (2 * Real.pi)) < t := by
  have h2π : 0 < 2 * Real.pi := by positivity
  have hdiv : 1 < X / (2 * Real.pi) := (one_lt_div h2π).mpr hX
  have hL : 0 < Real.log (X / (2 * Real.pi)) := Real.log_pos hdiv
  rw [div_lt_iff₀ hL]
  constructor <;> intro h <;> linarith

/-! ## 3. Sharpened bounds on `localNewmanConstant` and `localHeatThreshold` -/

/-- **Sharpened asymptotic bound on the local de Bruijn–Newman constant `Λ_X`.**
For every `ε > 0` and all sufficiently large `X`,
`Λ_X ≤ (6600 / 9991 + ε) / log((X − 1) / 2π)`. -/
theorem eventually_localNewmanConstant_le_subWeyl {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, localNewmanConstant X ≤ (6600 / 9991 + ε) / Real.log ((X - 1) / (2 * Real.pi)) := by
  obtain ⟨X₀, hX₀⟩ := riemannHeat_zeros_real_subWeyl hε
  have hlog : Tendsto (fun X : ℝ => Real.log ((X - 1) / (2 * Real.pi))) atTop atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    refine Tendsto.atTop_div_const (by positivity) ?_
    exact tendsto_atTop_add_const_right _ (-1) tendsto_id
  filter_upwards [hlog.eventually_ge_atTop (8 * (6600 / 9991 + ε) + 1),
    eventually_ge_atTop (|X₀| + 3)] with X hL hX
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log ((X - 1) / (2 * Real.pi)) := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hLdef]; linarith
  obtain ⟨s, hs⟩ : ∃ s, s = (6600 / 9991 + ε) / L := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  have hs8 : s ≤ 1 / 8 := by rw [hs, div_le_iff₀ hL0]; linarith [hLdef]
  rw [← hLdef, ← hs]
  refine localNewmanConstant_le ⟨hs0.le, fun s' hss' z hz hre => ?_⟩
  rcases le_or_gt (1 / 8) s' with h8 | h8
  · exact ((mem_realRootedTimes_iff (by linarith)).mpr
      ((newmanConstant_lt_eighth.le).trans h8)).2 z hz
  · have hzre : X - 1 ≤ |z.re| := by
      have := abs_le.mp hre
      rw [abs_of_pos (by linarith [abs_nonneg X₀])]
      linarith
    refine hX₀ s' (hs0.trans_le hss') h8.le z hz (by linarith [le_abs_self X₀]) ?_
    have hexp : Real.exp ((6600 / 9991 + ε) / s') ≤ Real.exp ((6600 / 9991 + ε) / s) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hs0 hss')
    have hval : Real.exp ((6600 / 9991 + ε) / s) = (X - 1) / (2 * Real.pi) := by
      rw [hs, div_div_cancel₀ (by positivity : (6600 / 9991 + ε : ℝ) ≠ 0), hLdef,
        Real.exp_log (by
          have : (1 : ℝ) < X - 1 := by linarith [abs_nonneg X₀]
          positivity)]
    have hπ : 0 < 2 * Real.pi := by positivity
    calc 2 * Real.pi * Real.exp ((6600 / 9991 + ε) / s')
        ≤ 2 * Real.pi * ((X - 1) / (2 * Real.pi)) := by
          rw [← hval]; exact mul_le_mul_of_nonneg_left hexp hπ.le
      _ = X - 1 := by field_simp
      _ ≤ |z.re| := hzre

/-- **`log X`-normalized upper bound on `Λ_X` at exponent `6600 / 9991`.** -/
theorem eventually_localNewmanConstant_le_subWeyl_logX {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, localNewmanConstant X ≤ (6600 / 9991 + ε) / Real.log X := by
  have hev := eventually_localNewmanConstant_le_subWeyl (ε := ε / 2) (by positivity)
  obtain ⟨A, hAdef⟩ : ∃ A, A = (2 / ε) * (6600 / 9991 + ε) * Real.log (4 * Real.pi) + 4 := ⟨_, rfl⟩
  filter_upwards [hev, eventually_ge_atTop (max 30 (Real.exp A))] with X hΛ hX
  have hX30 : 30 ≤ X := (le_max_left _ _).trans hX
  have hXA : Real.exp A ≤ X := (le_max_right _ _).trans hX
  have h4π_pos : 0 < 4 * Real.pi := by positivity
  have hX4π_gt1 : 1 < X / (4 * Real.pi) := by
    rw [one_lt_div h4π_pos]; linarith [Real.pi_lt_four]
  have hdiv_le : X / (4 * Real.pi) ≤ (X - 1) / (2 * Real.pi) := by
    have h2π : 0 < 2 * Real.pi := by positivity
    rw [show X / (4 * Real.pi) = (X / 2) / (2 * Real.pi) by ring]
    exact div_le_div_of_nonneg_right (by linarith) h2π.le
  have hlog_sub : Real.log X - Real.log (4 * Real.pi) ≤ Real.log ((X - 1) / (2 * Real.pi)) := by
    rw [← Real.log_div (by linarith) h4π_pos.ne']
    exact Real.log_le_log (by positivity) hdiv_le
  have hL_pos : 0 < Real.log ((X - 1) / (2 * Real.pi)) :=
    lt_of_lt_of_le (Real.log_pos hX4π_gt1) (Real.log_le_log (by positivity) hdiv_le)
  have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
  have hA_le : A ≤ Real.log X := by
    rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos A) hXA
  refine hΛ.trans ?_
  rw [div_le_div_iff₀ hL_pos hlogX_pos]
  have h1 : (2 / ε) * (6600 / 9991 + ε) * Real.log (4 * Real.pi) ≤ Real.log X := by
    rw [hAdef] at hA_le; linarith
  have h2 : (6600 / 9991 + ε) * Real.log (4 * Real.pi) ≤ (ε / 2) * Real.log X := by
    have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ ε / 2)
    have heq : (ε / 2) * ((2 / ε) * (6600 / 9991 + ε) * Real.log (4 * Real.pi)) =
        (6600 / 9991 + ε) * Real.log (4 * Real.pi) := by field_simp
    linarith
  have h3 : (6600 / 9991 + ε) * (Real.log X - Real.log (4 * Real.pi)) ≤
      (6600 / 9991 + ε) * Real.log ((X - 1) / (2 * Real.pi)) :=
    mul_le_mul_of_nonneg_left hlog_sub (by positivity)
  linarith

/-- **Sharpened asymptotic bound on the slice heat threshold `λ_t` via `Λ_X`.** -/
theorem exists_eventually_localHeatThreshold_le_subWeyl {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t in atTop,
      localHeatThreshold t ≤ (6600 / 9991 + ε) / (3 * c) := by
  obtain ⟨c, hc, X₀, hbridge⟩ := exists_localHeatThreshold_le_localNewmanConstant
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (eventually_localNewmanConstant_le_subWeyl_logX (ε := ε / 2) (by positivity))
  obtain ⟨B, hBdef⟩ : ∃ B, B = (2 / ε) * (6600 / 9991 + ε) * Real.log 2 + 4 := ⟨_, rfl⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (max (X₀ + 2) (max (X₁ + 2) (Real.exp B + 1)))] with t ht
  have htX₀ : X₀ + 1 ≤ t := by
    have : X₀ + 2 ≤ t := (le_max_left _ _).trans ht
    linarith
  have htX₁ : X₁ + 2 ≤ t := ((le_max_left _ _).trans (le_max_right _ _)).trans ht
  have htB : Real.exp B + 1 ≤ t := ((le_max_right _ _).trans (le_max_right _ _)).trans ht
  have hB4 : 4 ≤ B := by
    rw [hBdef]
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hterm : 0 ≤ (2 / ε) * (6600 / 9991 + ε) * Real.log 2 := by positivity
    linarith
  have h5_le_exp : 5 ≤ Real.exp B := by
    have := Real.add_one_le_exp B
    linarith
  have htm1_gt1 : 1 < t - 1 := by linarith
  have hlog_tm1_pos : 0 < Real.log (t - 1) := Real.log_pos htm1_gt1
  have hM0 : 0 ≤ (6600 / 9991 + ε / 2) / Real.log (t - 1) := by positivity
  have hloc : ∀ X : ℝ, |X - t| ≤ 1 →
      localNewmanConstant X ≤ (6600 / 9991 + ε / 2) / Real.log (t - 1) := by
    intro X hXt
    have hX_ge : t - 1 ≤ X := by linarith [(abs_le.mp hXt).1]
    have hX_pos : 1 < X := lt_of_lt_of_le htm1_gt1 hX_ge
    have hlog_mono : Real.log (t - 1) ≤ Real.log X :=
      Real.log_le_log (by linarith) hX_ge
    exact (hX₁ X (by linarith)).trans
      (div_le_div_of_nonneg_left (by positivity) hlog_tm1_pos hlog_mono)
  have hstep := hbridge t ((6600 / 9991 + ε / 2) / Real.log (t - 1)) htX₀ hM0 hloc
  refine hstep.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  suffices h : Real.log (t + 1) * ((6600 / 9991 + ε / 2) / Real.log (t - 1)) ≤ 6600 / 9991 + ε by
    exact mul_le_mul_of_nonneg_right h (by positivity)
  rw [mul_div_assoc', div_le_iff₀ hlog_tm1_pos]
  have htp1_le : t + 1 ≤ 2 * (t - 1) := by linarith
  have hlog_tp1 : Real.log (t + 1) ≤ Real.log 2 + Real.log (t - 1) := by
    rw [← Real.log_mul two_ne_zero (by linarith)]
    exact Real.log_le_log (by linarith) htp1_le
  have hB_le : B ≤ Real.log (t - 1) := by
    rw [← Real.log_exp B]; exact Real.log_le_log (Real.exp_pos B) (by linarith)
  have h1 : (2 / ε) * (6600 / 9991 + ε) * Real.log 2 ≤ Real.log (t - 1) := by
    rw [hBdef] at hB_le; linarith
  have h2 : (6600 / 9991 + ε) * Real.log 2 ≤ (ε / 2) * Real.log (t - 1) := by
    have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ ε / 2)
    have heq : (ε / 2) * ((2 / ε) * (6600 / 9991 + ε) * Real.log 2) =
        (6600 / 9991 + ε) * Real.log 2 := by field_simp
    linarith
  have h2_sub : (6600 / 9991 + ε / 2) * Real.log 2 ≤ (6600 / 9991 + ε) * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.log_nonneg (by norm_num))
  calc Real.log (t + 1) * (6600 / 9991 + ε / 2)
      = (6600 / 9991 + ε / 2) * Real.log (t + 1) := mul_comm _ _
    _ ≤ (6600 / 9991 + ε / 2) * (Real.log 2 + Real.log (t - 1)) :=
        mul_le_mul_of_nonneg_left hlog_tp1 (by positivity)
    _ = (6600 / 9991 + ε / 2) * Real.log 2 + (6600 / 9991 + ε / 2) * Real.log (t - 1) :=
        mul_add _ _ _
    _ ≤ (ε / 2) * Real.log (t - 1) + (6600 / 9991 + ε / 2) * Real.log (t - 1) := by linarith
    _ = (6600 / 9991 + ε) * Real.log (t - 1) := by ring

/-! ## 4. Exact closed form and order-2 real collision of `pairModelHeat` -/

private theorem forwardPolyHeat_one (s : ℝ) : forwardPolyHeat s (1 : Polynomial ℝ) = 1 := by
  rw [forwardPolyHeat_eq_sum (N := 1) (by simp)]
  simp

private theorem forwardPolyHeat_X (s : ℝ) :
    forwardPolyHeat s (Polynomial.X : Polynomial ℝ) = Polynomial.X := by
  rw [forwardPolyHeat_eq_sum (N := 1) (by simp)]
  simp

private theorem integrable_and_integral_gaussDensity_tilt_quad {t : ℝ} (ht : 0 < t)
    (a δ : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ =>
      ((gaussDensity t u * Real.exp (a * u) : ℝ) : ℂ) * ((z + (u : ℂ) * I) ^ 2 + (δ : ℂ) ^ 2)) ∧
    (∫ u : ℝ, ((gaussDensity t u * Real.exp (a * u) : ℝ) : ℂ) *
        ((z + (u : ℂ) * I) ^ 2 + (δ : ℂ) ^ 2)) =
      ((Real.exp (t * a ^ 2) : ℝ) : ℂ) *
        ((z + I * ((2 * t * a : ℝ) : ℂ)) ^ 2 + (δ : ℂ) ^ 2 - 2 * (t : ℂ)) := by
  have h2t : 0 < 2 * t := by positivity
  obtain ⟨i0, v0⟩ := integrable_and_integral_gaussDensity_tilt_poly h2t (1 : Polynomial ℝ) a 0
  obtain ⟨i1, v1⟩ := integrable_and_integral_gaussDensity_tilt_poly h2t
    (Polynomial.X : Polynomial ℝ) a 0
  obtain ⟨i2, v2⟩ := integrable_and_integral_gaussDensity_tilt_poly h2t
    (Polynomial.C (δ ^ 2) - Polynomial.X ^ 2) a 0
  rw [show 2 * t / 2 = t by ring] at i0 v0 i1 v1 i2 v2
  have hpt : ∀ u : ℝ,
      ((gaussDensity t u * Real.exp (a * u) : ℝ) : ℂ) * ((z + (u : ℂ) * I) ^ 2 + (δ : ℂ) ^ 2) =
      z ^ 2 * ((gaussDensity t u * (Real.exp (a * u) * (1 : Polynomial ℝ).eval (0 + u)) : ℝ) : ℂ) +
      (2 * z * I) * ((gaussDensity t u *
        (Real.exp (a * u) * (Polynomial.X : Polynomial ℝ).eval (0 + u)) : ℝ) : ℂ) +
      ((gaussDensity t u *
        (Real.exp (a * u) * (Polynomial.C (δ ^ 2) - Polynomial.X ^ 2).eval (0 + u)) : ℝ) : ℂ) := by
    intro u
    simp only [Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_pow, zero_add, mul_one]
    have hc1 : ((gaussDensity t u * (Real.exp (a * u) * u) : ℝ) : ℂ) =
        ((gaussDensity t u * Real.exp (a * u) : ℝ) : ℂ) * (u : ℂ) := by
      rw [← mul_assoc, Complex.ofReal_mul]
    have hc2 : ((gaussDensity t u * (Real.exp (a * u) * (δ ^ 2 - u ^ 2)) : ℝ) : ℂ) =
        ((gaussDensity t u * Real.exp (a * u) : ℝ) : ℂ) * ((δ : ℂ) ^ 2 - (u : ℂ) ^ 2) := by
      rw [← mul_assoc, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow,
        Complex.ofReal_pow]
    rw [hc1, hc2]
    have hI2 : ((u : ℂ) * I) ^ 2 = -(u : ℂ) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
    linear_combination ((gaussDensity t u * Real.exp (a * u) : ℝ) : ℂ) * hI2
  have ic0 : Integrable (fun u : ℝ =>
      z ^ 2 * ((gaussDensity t u * (Real.exp (a * u) * (1 : Polynomial ℝ).eval (0 + u)) : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.integrable_comp i0).const_mul (z ^ 2)
  have ic1 : Integrable (fun u : ℝ => (2 * z * I) *
      ((gaussDensity t u *
        (Real.exp (a * u) * (Polynomial.X : Polynomial ℝ).eval (0 + u)) : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.integrable_comp i1).const_mul (2 * z * I)
  have ic01 : Integrable (fun u : ℝ =>
      z ^ 2 * ((gaussDensity t u * (Real.exp (a * u) * (1 : Polynomial ℝ).eval (0 + u)) : ℝ) : ℂ) +
      (2 * z * I) * ((gaussDensity t u *
        (Real.exp (a * u) * (Polynomial.X : Polynomial ℝ).eval (0 + u)) : ℝ) : ℂ)) :=
    ic0.add ic1
  have ic2 : Integrable (fun u : ℝ =>
      ((gaussDensity t u *
        (Real.exp (a * u) * (Polynomial.C (δ ^ 2) - Polynomial.X ^ 2).eval (0 + u)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.integrable_comp i2
  refine ⟨(ic01.add ic2).congr (Eventually.of_forall fun u => (hpt u).symm), ?_⟩
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add ic01 ic2,
    integral_add ic0 ic1, integral_const_mul, integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal,
    v0, v1, v2, forwardPolyHeat_one, forwardPolyHeat_X, forwardPolyHeat_C_sub_X_sq]
  simp only [Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_pow, zero_add, show 2 * t * a ^ 2 / 2 = t * a ^ 2 by ring, mul_one]
  have hd1 : ((Real.exp (t * a ^ 2) * (2 * t * a) : ℝ) : ℂ) =
      ((Real.exp (t * a ^ 2) : ℝ) : ℂ) * ((2 * t * a : ℝ) : ℂ) := Complex.ofReal_mul _ _
  have hd2 : ((Real.exp (t * a ^ 2) * (δ ^ 2 - 2 * t - (2 * t * a) ^ 2) : ℝ) : ℂ) =
      ((Real.exp (t * a ^ 2) : ℝ) : ℂ) *
        ((δ : ℂ) ^ 2 - 2 * (t : ℂ) - ((2 * t * a : ℝ) : ℂ) ^ 2) := by
    rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_sub, Complex.ofReal_pow,
      Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [hd1, hd2]
  have hI2 : (I * ((2 * t * a : ℝ) : ℂ)) ^ 2 = -((2 * t * a : ℝ) : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]; ring
  linear_combination -(((Real.exp (t * a ^ 2) : ℝ) : ℂ) * hI2)

/-- Half-branch building block for the closed form of `pairModelHeat`:
`pairBranch L δ t z = e^{iLz/2} ((z − iLt)² + δ² − 2t)`. -/
def pairBranch (L δ t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((L : ℂ) * z / 2 * I) *
    ((z - I * (L : ℂ) * (t : ℂ)) ^ 2 + (δ : ℂ) ^ 2 - 2 * (t : ℂ))

/-- Derivative of `pairBranch L δ t` on `ℂ`. -/
def pairBranchDeriv (L δ t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((L : ℂ) * z / 2 * I) *
    (((L : ℂ) / 2 * I) * ((z - I * (L : ℂ) * (t : ℂ)) ^ 2 + (δ : ℂ) ^ 2 - 2 * (t : ℂ)) +
      2 * (z - I * (L : ℂ) * (t : ℂ)))

/-- **Exact closed form of `pairModelHeat` on all of `ℂ`.**
For `t > 0` and `z ∈ ℂ`,
`pairModelHeat L δ t z = (e^{tL²/4} / 2) * (pairBranch L δ t z + pairBranch L δ t (−z))`. -/
theorem pairModelHeat_eq_closed {L δ t : ℝ} (ht : 0 < t) (z : ℂ) :
    pairModelHeat L δ t z =
      ((Real.exp (t * L ^ 2 / 4) / 2 : ℝ) : ℂ) * (pairBranch L δ t z + pairBranch L δ t (-z)) := by
  obtain ⟨im, vm⟩ := integrable_and_integral_gaussDensity_tilt_quad ht (-(L / 2)) δ z
  obtain ⟨ip, vp⟩ := integrable_and_integral_gaussDensity_tilt_quad ht (L / 2) δ z
  have hpt : ∀ u : ℝ, (gaussDensity t u : ℂ) * pairModel L δ (z + (u : ℂ) * I) =
      (Complex.exp ((L : ℂ) * z / 2 * I) / 2) *
        (((gaussDensity t u * Real.exp (-(L / 2) * u) : ℝ) : ℂ) *
          ((z + (u : ℂ) * I) ^ 2 + (δ : ℂ) ^ 2)) +
      (Complex.exp (-((L : ℂ) * z / 2 * I)) / 2) *
        (((gaussDensity t u * Real.exp ((L / 2) * u) : ℝ) : ℂ) *
          ((z + (u : ℂ) * I) ^ 2 + (δ : ℂ) ^ 2)) := by
    intro u
    unfold pairModel
    rw [Complex.cos]
    have e1 : (L : ℂ) * (z + (u : ℂ) * I) / 2 * I =
        (L : ℂ) * z / 2 * I + ((-(L / 2) * u : ℝ) : ℂ) := by
      push_cast
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination ((L : ℂ) * (u : ℂ) / 2) * hI2
    have e2 : -((L : ℂ) * (z + (u : ℂ) * I) / 2) * I =
        -((L : ℂ) * z / 2 * I) + (((L / 2) * u : ℝ) : ℂ) := by
      push_cast
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination (-((L : ℂ) * (u : ℂ) / 2)) * hI2
    rw [e1, e2, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
    push_cast
    ring
  unfold pairModelHeat
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (im.const_mul _) (ip.const_mul _),
    integral_const_mul, integral_const_mul, vm, vp]
  have ha1 : t * (-(L / 2)) ^ 2 = t * L ^ 2 / 4 := by ring
  have ha2 : t * (L / 2) ^ 2 = t * L ^ 2 / 4 := by ring
  rw [ha1, ha2]
  unfold pairBranch
  push_cast
  ring

private theorem hasDerivAt_pairBranch (L δ t : ℝ) (z : ℂ) :
    HasDerivAt (pairBranch L δ t) (pairBranchDeriv L δ t z) z := by
  have hlin : HasDerivAt (fun w : ℂ => (L : ℂ) * w / 2 * I) ((L : ℂ) / 2 * I) z := by
    have h := (hasDerivAt_id z).const_mul ((L : ℂ) / 2 * I)
    simpa [show (fun w : ℂ => (L : ℂ) / 2 * I * w) = fun w => (L : ℂ) * w / 2 * I by
      funext w; ring] using h
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp ((L : ℂ) * w / 2 * I))
      (Complex.exp ((L : ℂ) * z / 2 * I) * ((L : ℂ) / 2 * I)) z := hlin.cexp
  have hsub : HasDerivAt (fun w : ℂ => w - I * (L : ℂ) * (t : ℂ)) 1 z :=
    (hasDerivAt_id z).sub_const _
  have hsq : HasDerivAt (fun w : ℂ => (w - I * (L : ℂ) * (t : ℂ)) ^ 2 + (δ : ℂ) ^ 2 - 2 * (t : ℂ))
      (2 * (z - I * (L : ℂ) * (t : ℂ))) z := by
    have h1 := (hsub.pow 2).add_const ((δ : ℂ) ^ 2) |>.sub_const (2 * (t : ℂ))
    simpa using h1
  have hmul := hexp.mul hsq
  unfold pairBranch pairBranchDeriv
  refine hmul.congr_deriv ?_
  ring

private theorem deriv_pairModelHeat_eq {L δ t : ℝ} (ht : 0 < t) (z : ℂ) :
    deriv (pairModelHeat L δ t) z =
      ((Real.exp (t * L ^ 2 / 4) / 2 : ℝ) : ℂ) *
        (pairBranchDeriv L δ t z - pairBranchDeriv L δ t (-z)) := by
  have hfun : pairModelHeat L δ t = fun w =>
      ((Real.exp (t * L ^ 2 / 4) / 2 : ℝ) : ℂ) * (pairBranch L δ t w + pairBranch L δ t (-w)) :=
    funext (pairModelHeat_eq_closed ht)
  rw [hfun]
  have hd1 := hasDerivAt_pairBranch L δ t z
  have hd2 : HasDerivAt (fun w : ℂ => pairBranch L δ t (-w)) (-pairBranchDeriv L δ t (-z)) z := by
    have h := (hasDerivAt_pairBranch L δ t (-z)).comp z (hasDerivAt_neg z)
    simpa [Function.comp_def] using h
  have hsum : HasDerivAt (fun w =>
      ((Real.exp (t * L ^ 2 / 4) / 2 : ℝ) : ℂ) * (pairBranch L δ t w + pairBranch L δ t (-w)))
      (((Real.exp (t * L ^ 2 / 4) / 2 : ℝ) : ℂ) *
        (pairBranchDeriv L δ t z + -pairBranchDeriv L δ t (-z))) z :=
    (hd1.add hd2).const_mul ((Real.exp (t * L ^ 2 / 4) / 2 : ℝ) : ℂ)
  rw [hsum.deriv]
  ring

/-- Critical collision time `t_* = (√(1 + L² δ²) − 1) / L²` at which the off-line pair `±iδ` of
`pairModel L δ` collides on the real axis at `z = 0`. -/
def pairCriticalHeat (L δ : ℝ) : ℝ := (Real.sqrt (1 + L ^ 2 * δ ^ 2) - 1) / L ^ 2

/-- Positivity, exact quadratic equation `(L t_*)² + 2 t_* = δ²`, and sharp upper bounds
`t_* < δ² / 2` and `t_* < δ / L` for `pairCriticalHeat L δ`. -/
theorem pairCriticalHeat_pos_and_bounds {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    0 < pairCriticalHeat L δ ∧
      (L * pairCriticalHeat L δ) ^ 2 + 2 * pairCriticalHeat L δ = δ ^ 2 ∧
      pairCriticalHeat L δ < δ ^ 2 / 2 ∧
      pairCriticalHeat L δ < δ / L := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (1 + L ^ 2 * δ ^ 2) := ⟨_, rfl⟩
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
  have hs_sq : s ^ 2 = 1 + L ^ 2 * δ ^ 2 := by
    rw [hs]; exact Real.sq_sqrt (by positivity)
  have hs1 : 1 < s := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ < Real.sqrt (1 + L ^ 2 * δ ^ 2) :=
          Real.sqrt_lt_sqrt (by norm_num) (by linarith [mul_pos hL2 (sq_pos_of_pos hδ)])
      _ = s := hs.symm
  have ht_pos : 0 < pairCriticalHeat L δ := by
    unfold pairCriticalHeat; rw [← hs]; exact div_pos (by linarith) hL2
  have hquad : (L * pairCriticalHeat L δ) ^ 2 + 2 * pairCriticalHeat L δ = δ ^ 2 := by
    unfold pairCriticalHeat
    rw [← hs]
    have hLne : L ≠ 0 := hL.ne'
    calc (L * ((s - 1) / L ^ 2)) ^ 2 + 2 * ((s - 1) / L ^ 2)
        = (s ^ 2 - 1) / L ^ 2 := by field_simp; ring
      _ = δ ^ 2 := by rw [hs_sq]; field_simp; ring
  have hLt_pos : 0 < (L * pairCriticalHeat L δ) ^ 2 := sq_pos_of_pos (mul_pos hL ht_pos)
  have hlt_sq : pairCriticalHeat L δ < δ ^ 2 / 2 := by linarith
  have hLt_lt : L * pairCriticalHeat L δ < δ := by
    have hsq_lt : (L * pairCriticalHeat L δ) ^ 2 < δ ^ 2 := by linarith
    nlinarith [mul_pos hL ht_pos]
  exact ⟨ht_pos, hquad, hlt_sq, (lt_div_iff₀ hL).mpr (by linarith)⟩

/-- **Exact nondegenerate order-2 real collision of `pairModelHeat` at `z = 0, t = t_*`.**
For every `L > 0` and `δ > 0`, at `t_* = pairCriticalHeat L δ > 0`:
1. `pairModelHeat L δ t_* 0 = 0`,
2. `deriv (pairModelHeat L δ t_*) 0 = 0`,
3. `deriv (deriv (pairModelHeat L δ t_*)) 0 = 2 e^{t_* L²/4} √(1 + L² δ²) ≠ 0`. -/
theorem pairModelHeat_orderTwo_collision {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    pairModelHeat L δ (pairCriticalHeat L δ) 0 = 0 ∧
    deriv (pairModelHeat L δ (pairCriticalHeat L δ)) 0 = 0 ∧
    deriv (deriv (pairModelHeat L δ (pairCriticalHeat L δ))) 0 =
      ((2 * Real.exp (pairCriticalHeat L δ * L ^ 2 / 4) *
        Real.sqrt (1 + L ^ 2 * δ ^ 2) : ℝ) : ℂ) ∧
    deriv (deriv (pairModelHeat L δ (pairCriticalHeat L δ))) 0 ≠ 0 := by
  obtain ⟨ht, hquad, _, _⟩ := pairCriticalHeat_pos_and_bounds hL hδ
  obtain ⟨t, htdef⟩ : ∃ t, t = pairCriticalHeat L δ := ⟨_, rfl⟩
  rw [← htdef] at ht hquad ⊢
  have h1p : 1 + L ^ 2 * t = Real.sqrt (1 + L ^ 2 * δ ^ 2) := by
    rw [htdef, pairCriticalHeat, mul_div_cancel₀ _ (sq_pos_of_pos hL).ne']
    ring
  have hval : pairModelHeat L δ t 0 = 0 := by
    have hI0 := pairModelHeat_mul_I (L := L) (δ := δ) ht 0
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, zero_div, neg_zero, Real.exp_zero,
      one_mul, zero_add, zero_sub, neg_sq] at hI0
    rw [hI0]
    have h0 : δ ^ 2 - 2 * t - (L * t) ^ 2 = 0 := by linarith
    simp [h0]
  have hd1 : deriv (pairModelHeat L δ t) 0 = 0 := by
    rw [deriv_pairModelHeat_eq ht 0, neg_zero, sub_self, mul_zero]
  have hd_fun : deriv (pairModelHeat L δ t) = fun w =>
      ((Real.exp (t * L ^ 2 / 4) / 2 : ℝ) : ℂ) *
        (pairBranchDeriv L δ t w - pairBranchDeriv L δ t (-w)) :=
    funext (deriv_pairModelHeat_eq ht)
  -- Differentiate `pairBranchDeriv L δ t` at `0`.
  have hlin0 : HasDerivAt (fun w : ℂ => (L : ℂ) * w / 2 * I) ((L : ℂ) / 2 * I) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).const_mul ((L : ℂ) / 2 * I)
    simpa [show (fun w : ℂ => (L : ℂ) / 2 * I * w) = fun w => (L : ℂ) * w / 2 * I by
      funext w; ring] using h
  have hexp0 : HasDerivAt (fun w : ℂ => Complex.exp ((L : ℂ) * w / 2 * I))
      (Complex.exp ((L : ℂ) * 0 / 2 * I) * ((L : ℂ) / 2 * I)) 0 := hlin0.cexp
  have hsub0 : HasDerivAt (fun w : ℂ => w - I * (L : ℂ) * (t : ℂ)) 1 0 :=
    (hasDerivAt_id (0 : ℂ)).sub_const _
  have hsq0 : HasDerivAt
      (fun w : ℂ => (w - I * (L : ℂ) * (t : ℂ)) ^ 2 + (δ : ℂ) ^ 2 - 2 * (t : ℂ))
      (2 * ((0 : ℂ) - I * (L : ℂ) * (t : ℂ))) 0 := by
    have h1 := (hsub0.pow 2).add_const ((δ : ℂ) ^ 2) |>.sub_const (2 * (t : ℂ))
    simpa using h1
  have hr0 : HasDerivAt
      (fun w : ℂ => ((L : ℂ) / 2 * I) *
          ((w - I * (L : ℂ) * (t : ℂ)) ^ 2 + (δ : ℂ) ^ 2 - 2 * (t : ℂ)) +
        2 * (w - I * (L : ℂ) * (t : ℂ)))
      (((L : ℂ) / 2 * I) * (2 * ((0 : ℂ) - I * (L : ℂ) * (t : ℂ))) + 2 * 1) 0 :=
    (hsq0.const_mul ((L : ℂ) / 2 * I)).add (hsub0.const_mul 2)
  obtain ⟨d₂, hd₂def⟩ : ∃ d₂ : ℂ, d₂ =
      Complex.exp ((L : ℂ) * 0 / 2 * I) * ((L : ℂ) / 2 * I) *
        (((L : ℂ) / 2 * I) * (((0 : ℂ) - I * (L : ℂ) * (t : ℂ)) ^ 2 + (δ : ℂ) ^ 2 - 2 * (t : ℂ)) +
          2 * ((0 : ℂ) - I * (L : ℂ) * (t : ℂ))) +
      Complex.exp ((L : ℂ) * 0 / 2 * I) *
        (((L : ℂ) / 2 * I) * (2 * ((0 : ℂ) - I * (L : ℂ) * (t : ℂ))) + 2 * 1) := ⟨_, rfl⟩
  have hbd0 : HasDerivAt (pairBranchDeriv L δ t) d₂ 0 := by
    rw [hd₂def]
    exact hexp0.mul hr0
  have hbd_neg0 : HasDerivAt (fun w : ℂ => pairBranchDeriv L δ t (-w)) (-d₂) 0 := by
    have hbd0' : HasDerivAt (pairBranchDeriv L δ t) d₂ (-(0 : ℂ)) := by
      rw [neg_zero]; exact hbd0
    simpa [Function.comp_def] using hbd0'.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  have hd2_at : HasDerivAt (deriv (pairModelHeat L δ t))
      (((Real.exp (t * L ^ 2 / 4) / 2 : ℝ) : ℂ) * (d₂ - (-d₂))) 0 := by
    rw [hd_fun]
    exact (hbd0.sub hbd_neg0).const_mul _
  have hd₂_simp : d₂ = ((2 * (1 + L ^ 2 * t) : ℝ) : ℂ) := by
    rw [hd₂def]
    simp only [mul_zero, zero_div, zero_mul, Complex.exp_zero, one_mul, zero_sub]
    have hq0 : (-(I * (L : ℂ) * (t : ℂ))) ^ 2 + (δ : ℂ) ^ 2 - 2 * (t : ℂ) = 0 := by
      have hI2 : (-(I * (L : ℂ) * (t : ℂ))) ^ 2 = -(((L * t) ^ 2 : ℝ) : ℂ) := by
        rw [neg_sq, mul_pow, mul_pow, Complex.I_sq]; push_cast; ring
      rw [hI2]
      have hreal : -((L * t) ^ 2) + δ ^ 2 - 2 * t = 0 := by linarith
      exact_mod_cast hreal
    rw [hq0, mul_zero, zero_add]
    push_cast
    have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
    linear_combination (-2 * (L : ℂ) ^ 2 * (t : ℂ)) * hI2
  have hd2_val : deriv (deriv (pairModelHeat L δ t)) 0 =
      ((2 * Real.exp (t * L ^ 2 / 4) * Real.sqrt (1 + L ^ 2 * δ ^ 2) : ℝ) : ℂ) := by
    rw [hd2_at.deriv, hd₂_simp, h1p]
    push_cast
    ring
  have hd2_ne : deriv (deriv (pairModelHeat L δ t)) 0 ≠ 0 := by
    rw [hd2_val, Complex.ofReal_ne_zero]
    positivity
  exact ⟨hval, hd1, hd2_val, hd2_ne⟩

/-- **Arbitrarily small-heat collision obstruction for Lindelöf-bounded Riemann-density sources.**
For every density `L > 0` (e.g., `L = log X`) and every positive heat threshold `τ > 0` (in
particular `τ = (2/3 + ε) / log X` or `τ = (1/2) / log(X / 2π)`), there exist an off-line depth
`δ ∈ (0, 1/2]` and a collision time `t_* ∈ (0, τ)` such that `pairModel L δ`:
* obeys the Lindelöf-level slice bound `‖pairModel L δ (x + iy)‖ ≤ (x² + y² + δ²) cosh(Ly/2)`;
* carries nonreal zeros throughout `(0, t_*)`; and
* undergoes an exact nondegenerate order-2 real collision at `z = 0, t = t_*`. -/
theorem exists_pairModelHeat_real_collision_below_scale {L τ : ℝ} (hL : 0 < L) (hτ : 0 < τ) :
    ∃ δ t_star : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < t_star ∧ t_star < τ ∧
      (∀ x y : ℝ, ‖pairModel L δ (x + y * I)‖ ≤ (x ^ 2 + y ^ 2 + δ ^ 2) * Real.cosh (L * y / 2)) ∧
      (∀ t : ℝ, 0 < t → t < t_star → ∃ y : ℝ, 0 < y ∧ pairModelHeat L δ t (y * I) = 0) ∧
      pairModelHeat L δ t_star 0 = 0 ∧
      deriv (pairModelHeat L δ t_star) 0 = 0 ∧
      deriv (deriv (pairModelHeat L δ t_star)) 0 ≠ 0 := by
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = min (1 / 2) (Real.sqrt τ) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min (by norm_num) (Real.sqrt_pos.mpr hτ)
  have hδ2 : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδ_sq : δ ^ 2 ≤ τ := by
    have hle : δ ≤ Real.sqrt τ := by rw [hδdef]; exact min_le_right _ _
    calc δ ^ 2 ≤ (Real.sqrt τ) ^ 2 := pow_le_pow_left₀ hδ0.le hle 2
      _ = τ := Real.sq_sqrt hτ.le
  obtain ⟨ht_pos, hquad, hlt_sq, _⟩ := pairCriticalHeat_pos_and_bounds hL hδ0
  obtain ⟨hv, hd1, _, hd2_ne⟩ := pairModelHeat_orderTwo_collision hL hδ0
  refine ⟨δ, pairCriticalHeat L δ, hδ0, hδ2, ht_pos, ?_, norm_pairModel_le L δ, ?_,
    hv, hd1, hd2_ne⟩
  · linarith
  · intro t ht0 htt
    refine exists_pos_pairModelHeat_mul_I_eq_zero ht0 hL.le hδ0 (by linarith) ?_
    have hsq_lt : (L * t) ^ 2 < (L * pairCriticalHeat L δ) ^ 2 :=
      pow_lt_pow_left₀ (mul_lt_mul_of_pos_left htt hL) (by positivity) (by omega)
    linarith

/-! ## 5. Exact heightwise reduction and global equivalence for Question 2.6.5 -/

/-- **Heightwise reduction of Question 2.6.5 from `2/3` to `6600 / 9991`.**
For every `δ > 0` and `ε ≥ 0` with `6600 / 9991 + δ ≤ 2 / 3 + ε`, there exists `X₁ ≥ 30` such that
at EVERY individual height `X ≥ X₁`, absence of collisions of `riemannHeat t` in `|Re z − X| ≤ 1`
across `t ∈ (0, (2 / 3 + ε) / log X]` is unconditionally equivalent to absence of collisions across
the strictly narrower sub-Weyl interval `t ∈ (0, (6600 / 9991 + δ) / log X]`. -/
theorem no_collision_upto_twoThirds_iff_upto_subWeyl {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hle : 6600 / 9991 + δ ≤ 2 / 3 + ε) :
    ∃ X₁ : ℝ, 30 ≤ X₁ ∧ ∀ X : ℝ, X₁ ≤ X →
      ((∀ t : ℝ, 0 < t → t ≤ (2 / 3 + ε) / Real.log X →
          ∀ z : ℂ, riemannHeat t z = 0 → |z.re - X| ≤ 1 →
            z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0) ↔
        (∀ t : ℝ, 0 < t → t ≤ (6600 / 9991 + δ) / Real.log X →
          ∀ z : ℂ, riemannHeat t z = 0 → |z.re - X| ≤ 1 →
            z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0)) := by
  obtain ⟨X₁, hX₁30, hband⟩ := riemannHeat_no_collision_near_height_subWeyl_logX hδ hε
  refine ⟨X₁, hX₁30, fun X hX => ?_⟩
  have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
  have hdiv_le : (6600 / 9991 + δ) / Real.log X ≤ (2 / 3 + ε) / Real.log X :=
    div_le_div_of_nonneg_right hle hlogX_pos.le
  constructor
  · intro hall t ht0 ht_le z hz hre
    exact hall t ht0 (ht_le.trans hdiv_le) z hz hre
  · intro hsub t ht0 ht_le z hz hre
    rcases le_or_gt t ((6600 / 9991 + δ) / Real.log X) with hlo | hhi
    · exact hsub t ht0 hlo z hz hre
    · exact hband X hX t hhi.le ht_le z hz hre

/-- **Global equivalence for Question 2.6.5 (`Λ_X = 0` at every height).**
For every `δ > 0` and `ε ≥ 0` with `6600 / 9991 + δ ≤ 2 / 3 + ε`, there exists `X₁ ≥ 30` such that
the following are unconditionally equivalent:
1. `∀ X : ℝ, localNewmanConstant X = 0` (`Λ_X = 0` at every height);
2. `∀ t : ℝ, 0 < t → ∀ x : ℝ, riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0`
   (zeros of `H_t` never collide on `ℝ` at any `t > 0`);
3. `(∀ t ∈ Ioc (0 : ℝ) (1 / 8), ∀ x : ℝ, |x| ≤ X₁ → riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0)`
   and `∀ X ≥ X₁, ∀ t ∈ Ioc (0 : ℝ) ((2 / 3 + ε) / Real.log X), riemannHeat t X = 0 → deriv (riemannHeat t) X ≠ 0`;
4. `(∀ t ∈ Ioc (0 : ℝ) (1 / 8), ∀ x : ℝ, |x| ≤ X₁ → riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0)`
   and `∀ X ≥ X₁, ∀ t ∈ Ioc (0 : ℝ) ((6600 / 9991 + δ) / Real.log X), (halfGaussTransform t (xiLine X) 0).re = 0 → (deriv (halfGaussTransform t (xiLine X)) 0).im ≠ 0`;
5. `RiemannHypothesis`. -/
theorem question_2_6_5_global_equivalence {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hle : 6600 / 9991 + δ ≤ 2 / 3 + ε) :
    ∃ X₁ : ℝ, 30 ≤ X₁ ∧
      (((∀ X : ℝ, localNewmanConstant X = 0) ↔
          (∀ t : ℝ, 0 < t → ∀ x : ℝ, riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0)) ∧
        ((∀ X : ℝ, localNewmanConstant X = 0) ↔
          ((∀ t ∈ Ioc (0 : ℝ) (1 / 8), ∀ x : ℝ, |x| ≤ X₁ →
              riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0) ∧
            (∀ X ≥ X₁, ∀ t ∈ Ioc (0 : ℝ) ((2 / 3 + ε) / Real.log X),
              riemannHeat t X = 0 → deriv (riemannHeat t) X ≠ 0))) ∧
        ((∀ X : ℝ, localNewmanConstant X = 0) ↔
          ((∀ t ∈ Ioc (0 : ℝ) (1 / 8), ∀ x : ℝ, |x| ≤ X₁ →
              riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0) ∧
            (∀ X ≥ X₁, ∀ t ∈ Ioc (0 : ℝ) ((6600 / 9991 + δ) / Real.log X),
              (halfGaussTransform t (xiLine X) 0).re = 0 →
                (deriv (halfGaussTransform t (xiLine X)) 0).im ≠ 0))) ∧
        ((∀ X : ℝ, localNewmanConstant X = 0) ↔ RiemannHypothesis)) := by
  obtain ⟨X_b, _, hband⟩ := riemannHeat_no_collision_near_height_subWeyl_band (δ := δ / 2)
    (by positivity)
  obtain ⟨A, hAdef⟩ : ∃ A, A = (2 / δ) * (6600 / 9991 + δ) * Real.log (4 * Real.pi) + 4 := ⟨_, rfl⟩
  obtain ⟨X₁, hX₁def⟩ : ∃ X₁, X₁ = max 30 (max X_b (Real.exp A)) := ⟨_, rfl⟩
  have hX₁30 : 30 ≤ X₁ := by rw [hX₁def]; exact le_max_left _ _
  refine ⟨X₁, hX₁30, ?_⟩
  have h1_to_2 : (∀ X : ℝ, localNewmanConstant X = 0) →
      ∀ t : ℝ, 0 < t → ∀ x : ℝ, riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0 := by
    intro hloc t ht
    have hΛ0 : newmanConstant = 0 := by
      rw [newmanConstant_eq_iSup_localNewmanConstant]
      simp [hloc]
    have hcm0 : collisionMass t = 0 :=
      collisionMass_eq_zero_of_newmanConstant_lt (by linarith)
    exact (collisionMass_eq_zero_iff_simple ht).mp hcm0
  have h2_to_3 : (∀ t : ℝ, 0 < t → ∀ x : ℝ, riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0) →
      (∀ t ∈ Ioc (0 : ℝ) (1 / 8), ∀ x : ℝ, |x| ≤ X₁ →
          riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0) ∧
        (∀ X ≥ X₁, ∀ t ∈ Ioc (0 : ℝ) ((2 / 3 + ε) / Real.log X),
          riemannHeat t X = 0 → deriv (riemannHeat t) X ≠ 0) :=
    fun h2 => ⟨fun t ht x _ hx => h2 t ht.1 x hx, fun X _ t ht hX => h2 t ht.1 X hX⟩
  have h3_to_4 : ((∀ t ∈ Ioc (0 : ℝ) (1 / 8), ∀ x : ℝ, |x| ≤ X₁ →
          riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0) ∧
        (∀ X ≥ X₁, ∀ t ∈ Ioc (0 : ℝ) ((2 / 3 + ε) / Real.log X),
          riemannHeat t X = 0 → deriv (riemannHeat t) X ≠ 0)) →
      (∀ t ∈ Ioc (0 : ℝ) (1 / 8), ∀ x : ℝ, |x| ≤ X₁ →
          riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0) ∧
        (∀ X ≥ X₁, ∀ t ∈ Ioc (0 : ℝ) ((6600 / 9991 + δ) / Real.log X),
          (halfGaussTransform t (xiLine X) 0).re = 0 →
            (deriv (halfGaussTransform t (xiLine X)) 0).im ≠ 0) := by
    rintro ⟨hbox, hhi⟩
    refine ⟨hbox, fun X hX t ht hre him => ?_⟩
    have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
    have ht_hi : t ≤ (2 / 3 + ε) / Real.log X :=
      ht.2.trans (div_le_div_of_nonneg_right hle hlogX_pos.le)
    obtain ⟨hz, hdz⟩ := (riemannHeat_ofReal_collision_iff_halfGauss ht.1 X).mpr ⟨hre, him⟩
    exact hhi X hX t ⟨ht.1, ht_hi⟩ hz hdz
  have h4_to_1 : ((∀ t ∈ Ioc (0 : ℝ) (1 / 8), ∀ x : ℝ, |x| ≤ X₁ →
          riemannHeat t x = 0 → deriv (riemannHeat t) x ≠ 0) ∧
        (∀ X ≥ X₁, ∀ t ∈ Ioc (0 : ℝ) ((6600 / 9991 + δ) / Real.log X),
          (halfGaussTransform t (xiLine X) 0).re = 0 →
            (deriv (halfGaussTransform t (xiLine X)) 0).im ≠ 0)) →
      ∀ X : ℝ, localNewmanConstant X = 0 := by
    rintro ⟨hbox, hsub⟩
    suffices hΛ0 : newmanConstant = 0 by
      intro X
      exact le_antisymm (hΛ0 ▸ localNewmanConstant_le_newmanConstant X)
        (localNewmanConstant_nonneg X)
    rcases eq_or_lt_of_le newmanConstant_nonneg with h0 | hpos
    · exact h0.symm
    · exfalso
      have hne := collisionMass_newmanConstant_ne_zero hpos
      have ht8 : newmanConstant ≤ 1 / 8 := newmanConstant_lt_eighth.le
      have hnot_simple : ¬ ∀ x : ℝ, riemannHeat newmanConstant x = 0 →
          deriv (riemannHeat newmanConstant) x ≠ 0 :=
        fun hs => hne ((collisionMass_eq_zero_iff_simple hpos).mpr hs)
      push Not at hnot_simple
      obtain ⟨x, hx0, hdx0⟩ := hnot_simple
      -- Symmetrize to `|x| ≥ 0`.
      have habs_col : riemannHeat newmanConstant ((|x| : ℝ) : ℂ) = 0 ∧
          deriv (riemannHeat newmanConstant) ((|x| : ℝ) : ℂ) = 0 := by
        rcases le_or_gt 0 x with hnonneg | hneg
        · rwa [abs_of_nonneg hnonneg]
        · rw [abs_of_neg hneg, ofReal_neg, riemannHeat_neg hpos.le,
            deriv_riemannHeat_neg hpos.le, hx0, hdx0, neg_zero]
          exact ⟨rfl, rfl⟩
      rcases le_or_gt |x| X₁ with hle_X₁ | hgt_X₁
      · exact hbox newmanConstant ⟨hpos, ht8⟩ x hle_X₁ hx0 hdx0
      · obtain ⟨X, hXdef⟩ : ∃ X, X = |x| := ⟨_, rfl⟩
        have hXX₁ : X₁ ≤ X := by rw [hXdef]; exact hgt_X₁.le
        rw [← hXdef] at habs_col
        have hX30 : 30 ≤ X := hX₁30.trans hXX₁
        have hXb : X_b ≤ X := by
          have : X_b ≤ X₁ := by rw [hX₁def]; exact (le_max_left _ _).trans (le_max_right _ _)
          exact this.trans hXX₁
        have hXA : Real.exp A ≤ X := by
          have : Real.exp A ≤ X₁ := by
            rw [hX₁def]; exact (le_max_right _ _).trans (le_max_right _ _)
          exact this.trans hXX₁
        have h4π_pos : 0 < 4 * Real.pi := by positivity
        have hX4π_gt1 : 1 < X / (4 * Real.pi) := by
          rw [one_lt_div h4π_pos]; linarith [Real.pi_lt_four]
        have hdiv_le : X / (4 * Real.pi) ≤ (X - 1) / (2 * Real.pi) := by
          have h2π : 0 < 2 * Real.pi := by positivity
          rw [show X / (4 * Real.pi) = (X / 2) / (2 * Real.pi) by ring]
          exact div_le_div_of_nonneg_right (by linarith) h2π.le
        have hlog_sub : Real.log X - Real.log (4 * Real.pi) ≤
            Real.log ((X - 1) / (2 * Real.pi)) := by
          rw [← Real.log_div (by linarith) h4π_pos.ne']
          exact Real.log_le_log (by positivity) hdiv_le
        have hL_pos : 0 < Real.log ((X - 1) / (2 * Real.pi)) :=
          lt_of_lt_of_le (Real.log_pos hX4π_gt1) (Real.log_le_log (by positivity) hdiv_le)
        have hlogX_pos : 0 < Real.log X := Real.log_pos (by linarith)
        have hA_le : A ≤ Real.log X := by
          rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos A) hXA
        have hband_lo : (6600 / 9991 + δ / 2) / Real.log ((X - 1) / (2 * Real.pi)) ≤
            (6600 / 9991 + δ) / Real.log X := by
          rw [div_le_div_iff₀ hL_pos hlogX_pos]
          have h1 : (2 / δ) * (6600 / 9991 + δ) * Real.log (4 * Real.pi) ≤ Real.log X := by
            rw [hAdef] at hA_le; linarith
          have h2 : (6600 / 9991 + δ) * Real.log (4 * Real.pi) ≤ (δ / 2) * Real.log X := by
            have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ δ / 2)
            have heq : (δ / 2) * ((2 / δ) * (6600 / 9991 + δ) * Real.log (4 * Real.pi)) =
                (6600 / 9991 + δ) * Real.log (4 * Real.pi) := by field_simp
            linarith
          have h3 : (6600 / 9991 + δ) * (Real.log X - Real.log (4 * Real.pi)) ≤
              (6600 / 9991 + δ) * Real.log ((X - 1) / (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hlog_sub (by positivity)
          linarith
        rcases le_or_gt newmanConstant ((6600 / 9991 + δ) / Real.log X) with hΛ_le | hΛ_gt
        · obtain ⟨hre, him⟩ :=
            (riemannHeat_ofReal_collision_iff_halfGauss hpos X).mp habs_col
          exact hsub X hXX₁ newmanConstant ⟨hpos, hΛ_le⟩ hre him
        · have hsimple := hband X hXb newmanConstant (hband_lo.trans hΛ_gt.le) ht8 (X : ℂ)
            habs_col.1 (by simp)
          exact hsimple.2 habs_col.2
  refine ⟨⟨h1_to_2, fun h2 => h4_to_1 (h3_to_4 (h2_to_3 h2))⟩,
    ⟨fun h1 => h2_to_3 (h1_to_2 h1), fun h3 => h4_to_1 (h3_to_4 h3)⟩,
    ⟨fun h1 => h3_to_4 (h2_to_3 (h1_to_2 h1)), h4_to_1⟩,
    riemannHypothesis_iff_forall_localNewmanConstant_eq_zero.symm⟩

end

end GaloisForLFunctions.ZeroConfigurationGeometry
