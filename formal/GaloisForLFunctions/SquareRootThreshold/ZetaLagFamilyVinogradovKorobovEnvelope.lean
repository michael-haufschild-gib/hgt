import GaloisForLFunctions.SquareRootThreshold.ZetaLagFamilyUnconditionalEnvelope
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovZeroFree

/-!
# The lag envelope of `ζ` at Vinogradov–Korobov strength

The window functional of the difference test at lag `v` is `P_v = φ(0) − φ(v)`,
`φ(v) = 2 Re S(v) = Σ_z D(z) e^{zv}`, and a zero-free region of `ζ` bounds `φ` through the
tradeoff `|φ(v)| ≤ e^{v/2}(W e^{−ηv} + S₂/(1 + G)²)` between the zero-free width `η` of the
exponents of height `≤ G` and the decay of the bump (`abs_two_re_lagStructure_le_of_zeroFree`).
`ZetaLagFamilyUnconditionalEnvelope` feeds the de la Vallée Poussin region and obtains
`P_v ≥ −|φ(0)| − (W + S₂) e^{v/2 − √v/10}`. This module feeds the Vinogradov–Korobov region
`Re ρ ≤ 1 − (log γ)^{−2/3} (log log γ)^{−5/3}/10⁸` for large heights
(`RHTower.Sieve.riemannZeta_ne_zero_vinogradovKorobov`) through the same tradeoff.

**The zero-free profile** (`exists_vk_zeroFree_profile`). There is a height `G₀ ≥ exp(e³⁰)` and a
width `η₁ > 0` such that for every `G ≥ G₀` every exponent of height `≤ G` has
`Re z ≤ ½ − min(η₁, vkZeroFreeWidth G)`: below `G₀` the de la Vallée Poussin profile supplies the
constant width `η₁`, above it the Vinogradov–Korobov width, which decreases in the height
(`vkZeroFreeWidth_antitone`), is read at the cut `G`.

**The envelope** (`zeta_lag_envelope_vinogradovKorobov`). For `0 < ex < 3/5` take the cut
`G = exp(v^θ)` with `θ = (ex + 3/5)/2`, so that `ex < θ` and `r = 1 − 2θ/3 − ex > 0`. Then
`(1 + G)^{−2} ≤ e^{−v^θ} ≤ e^{−v^ex}`, and `η v ≥ v^ex` since
`vkZeroFreeWidth(G)·v ≥ v^{ex} · v^{r}/(10⁸ (log v)²) ≥ v^ex` for large `v`. Hence for every width
`w ∈ (0, ½ log 2)` and all large lags,

`P_v ≥ −|φ(0)| − (W + S₂) e^{v/2 − v^ex}`.

The lag envelope carries exactly the strength of the zero-free region that enters; RH needs
`P_v ≥ 0`, a quasi-RH half-plane needs `P_v ≥ −C e^{σv}`, and `e^{v/2 − v^ex}` is `O(e^{σv})` for
no `σ < 1/2`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The Vinogradov–Korobov zero-free profile of `ζ` -/

/-- The Vinogradov–Korobov zero-free width at height `G`:
`(log G)^{−2/3} (log log G)^{−5/3} / 10⁸`. -/
def vkZeroFreeWidth (G : ℝ) : ℝ :=
  Real.log G ^ (-(2 : ℝ) / 3) * Real.log (Real.log G) ^ (-(5 : ℝ) / 3) / 10 ^ 8

/-- The width decreases in the height above `exp(e³⁰)`. -/
theorem vkZeroFreeWidth_antitone {γ G : ℝ} (hγ : Real.exp (Real.exp 30) ≤ γ) (hγG : γ ≤ G) :
    vkZeroFreeWidth G ≤ vkZeroFreeWidth γ := by
  unfold vkZeroFreeWidth
  have hγ0 : 0 < γ := lt_of_lt_of_le (Real.exp_pos _) hγ
  have hlγ : Real.exp 30 ≤ Real.log γ := by rw [Real.le_log_iff_exp_le hγ0]; exact hγ
  have hlγ0 : 0 < Real.log γ := lt_of_lt_of_le (Real.exp_pos _) hlγ
  have hllγ : 30 ≤ Real.log (Real.log γ) := by
    rw [← Real.log_exp 30]; exact Real.log_le_log (Real.exp_pos _) hlγ
  have hllγ0 : 0 < Real.log (Real.log γ) := by linarith
  have hlG : Real.log γ ≤ Real.log G := Real.log_le_log hγ0 hγG
  have hllG : Real.log (Real.log γ) ≤ Real.log (Real.log G) := Real.log_le_log hlγ0 hlG
  have h1 : Real.log G ^ (-(2 : ℝ) / 3) ≤ Real.log γ ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hlγ0 hlG (by norm_num)
  have h2 : Real.log (Real.log G) ^ (-(5 : ℝ) / 3) ≤ Real.log (Real.log γ) ^ (-(5 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hllγ0 hllG (by norm_num)
  exact div_le_div_of_nonneg_right
    (mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hlγ0.le _))
    (by norm_num)

/-- **The Vinogradov–Korobov region on the carrier.** There is a height `γ₀ ≥ exp(e³⁰)` such that
every nontrivial zero with `|γ| ≥ γ₀` has `Re ρ ≤ 1 − vkZeroFreeWidth |γ|`. -/
theorem exists_re_le_of_mem_zetaCarrier_vk :
    ∃ γ₀ : ℝ, Real.exp (Real.exp 30) ≤ γ₀ ∧ ∀ ρ ∈ zetaZeroConfig.carrier, γ₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - vkZeroFreeWidth |ρ.im| := by
  obtain ⟨γ₀, hγ₀⟩ := Sieve.riemannZeta_ne_zero_vinogradovKorobov
  refine ⟨max γ₀ (Real.exp (Real.exp 30)), le_max_right _ _, fun ρ hρ him => ?_⟩
  have hγ : γ₀ ≤ |ρ.im| := le_trans (le_max_left _ _) him
  have hzero : riemannZeta ρ = 0 := hρ.1
  by_contra hgt
  have hgt' := not_le.mp hgt
  unfold vkZeroFreeWidth at hgt'
  rcases le_or_gt 0 ρ.im with hpos | hneg
  · rw [abs_of_nonneg hpos] at hγ hgt'
    have hne := hγ₀ ρ.re ρ.im hγ hgt'
    rw [Complex.re_add_im] at hne
    exact hne hzero
  · rw [abs_of_neg hneg] at hγ hgt'
    have hc := conj_mem_zetaZeroConfig hρ
    have hne := hγ₀ ρ.re (-ρ.im) hγ hgt'
    have hconj : ((ρ.re : ℂ) + ((-ρ.im : ℝ) : ℂ) * I) = conj ρ := by
      apply Complex.ext <;> simp
    rw [hconj] at hne
    exact hne hc.1

/-- **The zero-free profile at Vinogradov–Korobov strength.** There are `G₀ ≥ exp(e³⁰)` and
`η₁ > 0` such that for every `G ≥ G₀` every exponent `z` of the lag function of `ζ` with
`|Im z| ≤ G` has `Re z ≤ ½ − min(η₁, vkZeroFreeWidth G)`. Below `G₀` the de la Vallée Poussin
profile gives the constant width `η₁ = min(η₀, 1/(100 log G₀))`; above it the Vinogradov–Korobov
width at the height of the exponent is at least the width at the cut `G`. -/
theorem exists_vk_zeroFree_profile (b : ℝ → ℂ) :
    ∃ G₀ η₁ : ℝ, Real.exp (Real.exp 30) ≤ G₀ ∧ 0 < η₁ ∧ ∀ G, G₀ ≤ G → ∀ z : ℂ,
      evenCoeff zetaZeroConfig b z ≠ 0 → |z.im| ≤ G →
        z.re ≤ 1 / 2 - min η₁ (vkZeroFreeWidth G) := by
  obtain ⟨γ₀, hγ₀e, hvk⟩ := exists_re_le_of_mem_zetaCarrier_vk
  have hγ₀pos : 0 < γ₀ := lt_of_lt_of_le (Real.exp_pos _) hγ₀e
  have hlogγ₀ : Real.exp 30 ≤ Real.log γ₀ := by
    rw [Real.le_log_iff_exp_le hγ₀pos]; exact hγ₀e
  have hlogγ₀pos : 0 < Real.log γ₀ := lt_of_lt_of_le (Real.exp_pos _) hlogγ₀
  have h23 : Real.exp 23 ≤ γ₀ := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hγ₀e
    linarith [Real.add_one_le_exp (30 : ℝ)]
  set η₁ : ℝ := min lowZeroFreeWidth (1 / (100 * Real.log γ₀)) with hη₁
  refine ⟨γ₀, η₁, hγ₀e, lt_min lowZeroFreeWidth_pos (by positivity), fun G hG z hz him => ?_⟩
  rcases le_or_gt |z.im| γ₀ with hlow | hhigh
  · -- below `γ₀`: the de la Vallée Poussin profile at height `γ₀`
    have := re_le_of_evenCoeff_zeta h23 hz hlow
    linarith [min_le_left η₁ (vkZeroFreeWidth G)]
  · -- above `γ₀`: the Vinogradov–Korobov region, read at the cut `G` by antitonicity
    have key : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2 + z.re → |ρ.im| = |z.im| →
        z.re ≤ 1 / 2 - min η₁ (vkZeroFreeWidth G) := by
      intro ρ hρ hre him'
      have h1 := hvk ρ hρ (by rw [him']; exact hhigh.le)
      have h2 : vkZeroFreeWidth G ≤ vkZeroFreeWidth |ρ.im| :=
        vkZeroFreeWidth_antitone (by rw [him']; exact hγ₀e.trans hhigh.le) (by rw [him']; exact him)
      have := min_le_right η₁ (vkZeroFreeWidth G)
      linarith
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · exact key _ h (by simp) (by simp)
    · exact key _ h (by simp) (by simp)

/-! ### Eventual inequalities for the power saving -/

/-- `1 ≤ η v^{1−ex}` for all large `v` when `η > 0` and `ex < 1`. -/
theorem eventually_one_le_mul_rpow {η ex : ℝ} (hη : 0 < η) (hex : ex < 1) :
    ∀ᶠ v : ℝ in atTop, 1 ≤ η * v ^ (1 - ex) := by
  have ht := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ex)).eventually
    (eventually_ge_atTop (1 / η))
  filter_upwards [ht] with v hv
  rw [div_le_iff₀ hη] at hv
  linarith

/-- `10⁸ (log v)² ≤ v^r` for all large `v` when `r > 0`. -/
theorem eventually_log_sq_le_rpow {r : ℝ} (hr : 0 < r) :
    ∀ᶠ v : ℝ in atTop, 10 ^ 8 * Real.log v ^ 2 ≤ v ^ r := by
  have hlo := (isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < r / 2)).bound
    (show (0 : ℝ) < 1 / 10 ^ 4 by positivity)
  filter_upwards [hlo, eventually_ge_atTop (1 : ℝ)] with v h1 hv1
  have hv0 : 0 < v := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hv1),
    abs_of_nonneg (Real.rpow_nonneg hv0.le _)] at h1
  have hsq : Real.log v ^ 2 ≤ (1 / 10 ^ 4 * v ^ (r / 2)) ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg hv1) h1 2
  have hvr : (v ^ (r / 2)) ^ 2 = v ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv0.le]; congr 1; push_cast; ring
  rw [mul_pow, hvr] at hsq
  norm_num at hsq
  linarith

/-! ### The envelope -/

/-- **The lag envelope of `ζ` at Vinogradov–Korobov strength.** For every `0 < ex < 3/5` and
every width `w ∈ (0, ½ log 2)`, for all large lags `v` the window functional of the difference
test satisfies `P_v ≥ −|M| − (W + S₂) e^{v/2 − v^ex}`, with `M = 2 Re S(0)`, `W = Σ_z |D(z)|`,
`S₂ = Σ_z |D(z)| (1 + |Im z|)²`. -/
theorem zeta_lag_envelope_vinogradovKorobov_eventually {ex : ℝ} (hex0 : 0 < ex)
    (hex : ex < 3 / 5) {w : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) :
    ∀ᶠ v : ℝ in atTop,
      -|2 * (lagStructure zetaZeroConfig (modScaledBump w 0) 0).re| -
        ((∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖) +
          ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * (1 + |z.im|) ^ 2) *
          Real.exp (v / 2 - v ^ ex) ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs : ∀ u, b u ≠ 0 → |u| ≤ w := modScaledBump_support hw 0
  obtain ⟨G₀, η₁, hG₀, hη₁, hprof⟩ := exists_vk_zeroFree_profile b
  have hG₀pos : 0 < G₀ := lt_of_lt_of_le (Real.exp_pos _) hG₀
  -- the auxiliary exponent `θ` of the height cut and the power gap `r`
  set θ : ℝ := (ex + 3 / 5) / 2 with hθdef
  have hθex : ex < θ := by rw [hθdef]; linarith
  have hθ1 : θ < 1 := by rw [hθdef]; linarith
  have hθ0 : 0 < θ := by linarith
  set r : ℝ := 1 - 2 * θ / 3 - ex with hrdef
  have hr : 0 < r := by rw [hrdef, hθdef]; linarith
  have hsum : ex + r + 2 * θ / 3 = 1 := by rw [hrdef]; ring
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    (tendsto_rpow_atTop hθ0).eventually (eventually_ge_atTop (Real.log G₀)),
    eventually_one_le_mul_rpow hη₁ (by linarith : ex < 1),
    eventually_log_sq_le_rpow hr] with v hve hvG hvη hvlog
  have hv1 : 1 ≤ v := le_trans (Real.one_le_exp zero_le_one) hve
  have hv0 : 0 < v := by linarith
  have hlogv : 1 ≤ Real.log v := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hve
  have hP : (lagPrimeWindowRHS v w (EF.weilTest (twoBump b v (-1)) (twoBump b v (-1)))).re =
      2 * (lagStructure zetaZeroConfig b 0).re - 2 * (lagStructure zetaZeroConfig b v).re := by
    rw [hbdef, ← literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv0.le,
      ← zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
        (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
        (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
          (modScaledBump_support hw 0)) v (-1)),
      re_W_lag_eq zetaZeroConfig temperedConfig_zetaZeroConfig hb hbs v]
  rw [hP]
  -- the height cut `G = e^{v^θ}` and the zero-free width `η` at the cut
  set G : ℝ := Real.exp (v ^ θ) with hGdef
  have hGG₀ : G₀ ≤ G :=
    calc G₀ = Real.exp (Real.log G₀) := (Real.exp_log hG₀pos).symm
      _ ≤ G := Real.exp_le_exp.mpr hvG
  set η : ℝ := min η₁ (vkZeroFreeWidth G) with hηdef
  have hfree : ∀ z, evenCoeff zetaZeroConfig b z ≠ 0 → |z.im| ≤ G → z.re ≤ 1 / 2 - η :=
    fun z hz him => hprof G hGG₀ z hz him
  have henv := abs_two_re_lagStructure_le_of_zeroFree zetaZeroConfig temperedConfig_zetaZeroConfig
    hb hw.le hbs hv0.le (Real.exp_pos _).le hfree
  -- `ηv ≥ v^ex`
  have hvex : 0 ≤ v ^ ex := Real.rpow_nonneg hv0.le ex
  have hηv : v ^ ex ≤ η * v := by
    rw [hηdef]
    rcases le_total η₁ (vkZeroFreeWidth G) with h | h
    · rw [min_eq_left h]
      calc v ^ ex = 1 * v ^ ex := (one_mul _).symm
        _ ≤ (η₁ * v ^ (1 - ex)) * v ^ ex := mul_le_mul_of_nonneg_right hvη hvex
        _ = η₁ * (v ^ (1 - ex) * v ^ ex) := by ring
        _ = η₁ * v := by
            rw [← Real.rpow_add hv0, show 1 - ex + ex = (1 : ℝ) by ring, Real.rpow_one]
    · rw [min_eq_right h]
      -- `width(G) ≥ v^{−2θ/3} (log v)^{−2}/10⁸` and `v = v^ex v^r v^{2θ/3}`
      have hlogG : Real.log G = v ^ θ := by rw [hGdef, Real.log_exp]
      have hloglogG : Real.log (Real.log G) = θ * Real.log v := by
        rw [hlogG, Real.log_rpow hv0]
      have hw1 : (v ^ θ) ^ (-(2 : ℝ) / 3) = (v ^ (2 * θ / 3))⁻¹ := by
        rw [← Real.rpow_mul hv0.le, ← Real.rpow_neg hv0.le]; congr 1; ring
      have hw2 : Real.log v ^ (-(2 : ℝ)) ≤ (θ * Real.log v) ^ (-(5 : ℝ) / 3) := by
        have hθl : 0 < θ * Real.log v := by positivity
        have h1 : Real.log v ^ (-(5 : ℝ) / 3) ≤ (θ * Real.log v) ^ (-(5 : ℝ) / 3) :=
          Real.rpow_le_rpow_of_nonpos hθl (by nlinarith) (by norm_num)
        have h2 : Real.log v ^ (-(2 : ℝ)) ≤ Real.log v ^ (-(5 : ℝ) / 3) :=
          Real.rpow_le_rpow_of_exponent_le hlogv (by norm_num)
        exact h2.trans h1
      have hw3 : Real.log v ^ (-(2 : ℝ)) = (Real.log v ^ 2)⁻¹ := by
        rw [Real.rpow_neg (by linarith), Real.rpow_two]
      have hpos1 : 0 < v ^ (2 * θ / 3) := Real.rpow_pos_of_pos hv0 _
      have hpos2 : 0 < Real.log v ^ 2 := by positivity
      have hwidth : (v ^ (2 * θ / 3))⁻¹ * (Real.log v ^ 2)⁻¹ / 10 ^ 8 ≤ vkZeroFreeWidth G := by
        unfold vkZeroFreeWidth
        rw [hloglogG, hlogG, hw1, ← hw3]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hw2 (by positivity)) (by norm_num)
      have hvdecomp : v = v ^ ex * v ^ r * v ^ (2 * θ / 3) := by
        rw [← Real.rpow_add hv0, ← Real.rpow_add hv0, hsum, Real.rpow_one]
      calc v ^ ex = v ^ ex * 1 := (mul_one _).symm
        _ ≤ v ^ ex * (v ^ r / (10 ^ 8 * Real.log v ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hvex
            rw [le_div_iff₀ (by positivity)]; linarith
        _ = (v ^ ex * v ^ r * (Real.log v ^ 2)⁻¹ / 10 ^ 8) *
              ((v ^ (2 * θ / 3))⁻¹ * v ^ (2 * θ / 3)) := by
            rw [inv_mul_cancel₀ hpos1.ne', mul_one]; ring
        _ = ((v ^ (2 * θ / 3))⁻¹ * (Real.log v ^ 2)⁻¹ / 10 ^ 8) *
              (v ^ ex * v ^ r * v ^ (2 * θ / 3)) := by ring
        _ = ((v ^ (2 * θ / 3))⁻¹ * (Real.log v ^ 2)⁻¹ / 10 ^ 8) * v := by rw [← hvdecomp]
        _ ≤ vkZeroFreeWidth G * v := mul_le_mul_of_nonneg_right hwidth hv0.le
  -- `e^{−ηv} ≤ e^{−v^ex}` and `(1 + G)^{−2} ≤ e^{−v^ex}`
  have hE1 : Real.exp (-η * v) ≤ Real.exp (-(v ^ ex)) := Real.exp_le_exp.mpr (by linarith)
  have hE2 : 1 / (1 + G) ^ 2 ≤ Real.exp (-(v ^ ex)) := by
    have hG0 : 0 < G := Real.exp_pos _
    have hθv : v ^ ex ≤ v ^ θ := Real.rpow_le_rpow_of_exponent_le hv1 hθex.le
    have hG2 : Real.exp (v ^ ex) ≤ (1 + G) ^ 2 := by
      calc Real.exp (v ^ ex) ≤ Real.exp (v ^ θ) := Real.exp_le_exp.mpr hθv
        _ = G := by rw [hGdef]
        _ ≤ (1 + G) ^ 2 := by nlinarith
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos _) hG2
  set W : ℝ := ∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖ with hW
  set S₂ : ℝ := ∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖ * (1 + |z.im|) ^ 2 with hS₂
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hS0 : 0 ≤ S₂ := tsum_nonneg fun z => by positivity
  have hphi : |2 * (lagStructure zetaZeroConfig b v).re| ≤
      (W + S₂) * Real.exp (v / 2 - v ^ ex) := by
    refine henv.trans ?_
    have h1 : W * Real.exp (-η * v) ≤ W * Real.exp (-(v ^ ex)) :=
      mul_le_mul_of_nonneg_left hE1 hW0
    have h2 : S₂ / (1 + G) ^ 2 ≤ S₂ * Real.exp (-(v ^ ex)) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hE2 hS0
    calc Real.exp (v / 2) * (W * Real.exp (-η * v) + S₂ / (1 + G) ^ 2)
        ≤ Real.exp (v / 2) * (W * Real.exp (-(v ^ ex)) + S₂ * Real.exp (-(v ^ ex))) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Real.exp_pos _).le
      _ = (W + S₂) * Real.exp (v / 2 - v ^ ex) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
  have hM := neg_abs_le (2 * (lagStructure zetaZeroConfig b 0).re)
  have hphi' := (abs_le.mp hphi).2
  linarith

/-- **The lag envelope of `ζ` at Vinogradov–Korobov strength, with a lag threshold.** For every
`0 < ex < 3/5` and every width `w ∈ (0, ½ log 2)` there is a lag `V₀` such that for every
`v ≥ V₀`: `P_v ≥ −|M| − (W + S₂) e^{v/2 − v^ex}`. -/
theorem zeta_lag_envelope_vinogradovKorobov {ex : ℝ} (hex0 : 0 < ex) (hex : ex < 3 / 5)
    {w : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) :
    ∃ V₀ : ℝ, ∀ v : ℝ, V₀ ≤ v →
      -|2 * (lagStructure zetaZeroConfig (modScaledBump w 0) 0).re| -
        ((∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖) +
          ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * (1 + |z.im|) ^ 2) *
          Real.exp (v / 2 - v ^ ex) ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re :=
  eventually_atTop.1 (zeta_lag_envelope_vinogradovKorobov_eventually hex0 hex hw hw2)

end GaloisForLFunctions.SquareRootThreshold
