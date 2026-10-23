import GaloisForLFunctions.TransHorizonIncidenceMechanics.OscillatingPrimePatternsArePaidExactlyAtTheCriticalZeros
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ThePhaseDiagramOfTheConstantSignPattern
import GaloisForLFunctions.RHTower.XiHorizontalSliceDensityFromMeanSquare

/-!
# The prime mean is quantized height by height

Below half damping a paid receiver continues `ζ(s)(C(s) − m)` holomorphically to `Re s > 1/2`
(`differentiableOn_complexMellinPairing`), so `C = (Φ + mζ)/ζ` is meromorphic at every point
`s₁ = 1 − ε + it₀` of the abscissa line. Along the ray `s₁ + u` its modulus therefore behaves like an
integral power `u^{p − q}` (`exists_ray_bounds_of_order`, from the factorizations of `Φ + mζ` and `ζ` at
`s₁`). The corpus law `not_receiverBounded_of_primeMean` is the case `t₀ = 0`. Here the prime mean is
read at every height:

* the complex pairing identity `Φ(s) = ζ(s)(C(s) − m)` holds off the real axis
  (`complexMellinPairing_eq_zeta_mul_of_summable`);
* the oscillating pattern `f(p) = a cos(t₀ log p)`, `t₀ ≠ 0`, has local prime mean `a/2` at the height
  `t₀`: `|Σ f(n) n^{-(1 + u + it₀)}| ≍ u^{-a/2}` (`exists_norm_oscSeries_rpow_bounds`).

Its real-axis prime mean is `0` for every amplitude, which the real-axis law allows. The height-local
law forces `−a/2 ∈ ℤ`: for `0 < ε < 1/2` and `t₀ ≠ 0` the weight `f_{a,t₀}(d) d^{-ε}` is paid iff `a = 0`
(`receiverBounded_oscPattern_damped_iff`).
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The complex pairing identity -/

/-- `|c(d) δ_d(n) Δ_n(s)| ≤ |s| n^{θ − σ − 1} · |c(d)| d^{-θ}` for `0 < θ ≤ 1`, `σ = Re s > 0`. -/
theorem norm_cpairingFamily_le {c : ℕ → ℝ} {θ : ℝ} {s : ℂ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hs : 0 < s.re) (n d : ℕ) :
    ‖(c d : ℂ) * (modulusDefect d n : ℂ) * complexMellinCell s n‖ ≤
      (‖s‖ * (n : ℝ) ^ (θ - s.re - 1)) * (|c d| * (d : ℝ) ^ (-θ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [modulusDefect_zero_right, Complex.ofReal_zero, mul_zero, zero_mul, norm_zero]
    positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [modulusDefect_zero_left, Complex.ofReal_zero, mul_zero, zero_mul, norm_zero]
    positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hα := abs_modulusDefect_le_rpow hθ0 hθ1 d n
  rw [Real.div_rpow hn0.le hd0.le] at hα
  have hcell : ‖complexMellinCell s n‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
    calc ‖complexMellinCell s n‖ = ‖cmellinCell s n‖ := rfl
      _ ≤ ‖s‖ / s.re * mellinCell s.re n := norm_cmellinCell_le hs hn
      _ ≤ ‖s‖ / s.re * (s.re * (n : ℝ) ^ (-s.re - 1)) :=
          mul_le_mul_of_nonneg_left (mellinCell_bounds hs hn).2 (by positivity)
      _ = ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by field_simp
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  calc |c d| * |modulusDefect d n| * ‖complexMellinCell s n‖
      ≤ |c d| * ((n : ℝ) ^ θ / (d : ℝ) ^ θ) * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hα (abs_nonneg _)) hcell (norm_nonneg _)
          (by positivity)
    _ = (‖s‖ * (n : ℝ) ^ (θ - s.re - 1)) * (|c d| * (d : ℝ) ^ (-θ)) := by
        rw [show θ - s.re - 1 = θ + (-s.re - 1) by ring, Real.rpow_add hn0,
          Real.rpow_neg hd0.le θ, div_eq_mul_inv]
        ring

/-- **The complex Mellin pairing identity.** If `Σ_d |c(d)| d^{-θ} < ∞` with `0 < θ < Re s < 1`, then
`Φ(s) = ζ(s)(C(s) − m)`. -/
theorem complexMellinPairing_eq_zeta_mul_of_summable {c : ℕ → ℝ} {θ : ℝ} {s : ℂ} (hθ0 : 0 < θ)
    (hθs : θ < s.re) (hs1 : s.re < 1) (hc : Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-θ))) :
    complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d)) s =
      riemannZeta s * (weightDirichletSeries c s - ((∑' d : ℕ, c d / d : ℝ) : ℂ)) := by
  have hsne : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  have hσ0 : 0 < s.re := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hσ0; linarith
  have hcomp : ∀ τ : ℝ, θ ≤ τ → Summable (fun d : ℕ => |c d| * (d : ℝ) ^ (-τ)) := fun τ hτ =>
    hc.of_nonneg_of_le (fun d => by positivity) fun d => by
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp [Real.zero_rpow (show -τ ≠ 0 by intro h; linarith),
          Real.zero_rpow (show -θ ≠ 0 by intro h; linarith)]
      · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd) (by linarith)
  have hs : Summable (fun d : ℕ => c d / d) := (hcomp 1 hθ1).of_norm_bounded fun d =>
    le_of_eq (by rw [Real.norm_eq_abs, abs_div, Nat.abs_cast, Real.rpow_neg_one, div_eq_mul_inv])
  have hS1 : Summable (fun d : ℕ => (c d : ℂ) * ((d : ℝ) : ℂ) ^ (-s)) := by
    refine (hcomp s.re hθs.le).of_norm_bounded fun d => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [Nat.cast_zero, Complex.ofReal_zero, Complex.zero_cpow hs0, norm_zero, mul_zero]
      positivity
    · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hd0, Complex.neg_re]
  have hS2 : Summable (fun d : ℕ => (c d : ℂ) / d) := by
    refine (Complex.summable_ofReal.mpr hs).congr fun d => ?_
    push_cast; ring
  -- the double family over `(n, d)`
  set F : ℕ → ℕ → ℂ := fun n d => (c d : ℂ) * (modulusDefect d n : ℂ) * complexMellinCell s n
    with hF
  set g : ℕ → ℝ := fun n => ‖s‖ * (n : ℝ) ^ (θ - s.re - 1)
  set h : ℕ → ℝ := fun d => |c d| * (d : ℝ) ^ (-θ)
  have hg : Summable g :=
    (Real.summable_nat_rpow.mpr (show θ - s.re - 1 < -1 by linarith)).mul_left _
  have hg0 : 0 ≤ g := fun n => by positivity
  have hh0 : 0 ≤ h := fun d => by positivity
  have hbound : ∀ n d, ‖F n d‖ ≤ g n * h d := fun n d => norm_cpairingFamily_le hθ0 hθ1 hσ0 n d
  have hFsum : Summable (Function.uncurry F) :=
    (Summable.mul_of_nonneg hg hc hg0 hh0).of_norm_bounded fun p => hbound p.1 p.2
  have hrow : ∀ n, Summable (F n) := fun n =>
    (hc.mul_left (g n)).of_norm_bounded fun d => hbound n d
  have hcol : ∀ d, Summable (fun n => F n d) := fun d =>
    (hg.mul_right (h d)).of_norm_bounded fun n => hbound n d
  have hleft : complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d)) s =
      ∑' n, ∑' d, F n d := by
    unfold complexMellinPairing
    refine tsum_congr fun n => ?_
    rw [weightCenteredPrefix_eq_tsum_modulusDefect c hs n, Complex.ofReal_tsum, ← tsum_mul_right]
    refine tsum_congr fun d => ?_
    simp only [hF]
    push_cast
    ring
  have hcomm : ∑' n, ∑' d, F n d = ∑' d, ∑' n, F n d := (hFsum.tsum_comm' hrow hcol).symm
  have hinner : ∀ d, ∑' n, F n d =
      (c d : ℂ) * (riemannZeta s * (((d : ℝ) : ℂ) ^ (-s) - 1 / d)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp only [hF, modulusDefect_zero_left, Complex.ofReal_zero, mul_zero, zero_mul, tsum_zero,
        Nat.cast_zero, Complex.zero_cpow hs0, div_zero, sub_zero]
    have hcd : ∀ n, F n d = (c d : ℂ) * ((modulusDefect d n : ℂ) * cmellinCell s n) := fun n => by
      simp only [hF]
      rw [show complexMellinCell s n = cmellinCell s n from rfl]
      ring
    simp_rw [hcd]
    rw [tsum_mul_left, (hasSum_modulusDefect_mul_cmellinCell hσ0 hsne hd).tsum_eq]
  rw [hleft, hcomm]
  simp_rw [hinner]
  have hsplit : ∀ d : ℕ, (c d : ℂ) * (riemannZeta s * (((d : ℝ) : ℂ) ^ (-s) - 1 / d)) =
      riemannZeta s * ((c d : ℂ) * ((d : ℝ) : ℂ) ^ (-s) - (c d : ℂ) / d) := fun d => by ring
  simp_rw [hsplit]
  rw [tsum_mul_left, hS1.tsum_sub hS2, weightDirichletSeries, Complex.ofReal_tsum]
  congr 2
  refine tsum_congr fun d => ?_
  push_cast
  ring

/-! ### Orders along a horizontal ray -/

/-- **Along a horizontal ray an analytic function behaves like an integral power.** If `f` is analytic
at `z₀` and not identically zero near it, then `A u^n ≤ |f(z₀ + u)| ≤ B u^n` as `u ↓ 0`, with `n ∈ ℕ`
the order of `f` at `z₀`. -/
theorem exists_ray_bounds_of_order {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hf0 : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) :
    ∃ n : ℕ, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      A * u ^ (n : ℝ) ≤ ‖f (z₀ + (u : ℂ))‖ ∧ ‖f (z₀ + (u : ℂ))‖ ≤ B * u ^ (n : ℝ) := by
  obtain ⟨n, g, hg, hga, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hf0
  have hgpos : 0 < ‖g z₀‖ := norm_pos_iff.mpr hga
  have hgnear : ∀ᶠ z in 𝓝 z₀, ‖g z₀‖ / 2 ≤ ‖g z‖ ∧ ‖g z‖ ≤ 2 * ‖g z₀‖ := by
    have hball := Metric.ball_mem_nhds (g z₀) (half_pos hgpos)
    filter_upwards [hg.continuousAt.preimage_mem_nhds hball] with z hz
    have hz' : ‖g z - g z₀‖ < ‖g z₀‖ / 2 := by simpa [dist_eq_norm] using hz
    have h1 := norm_sub_norm_le (g z₀) (g z)
    have h2 := norm_sub_norm_le (g z) (g z₀)
    rw [norm_sub_rev] at h1
    constructor <;> linarith
  have hpath : Tendsto (fun u : ℝ => z₀ + (u : ℂ)) (𝓝[>] 0) (𝓝 z₀) := by
    have hcont : Continuous (fun u : ℝ => z₀ + (u : ℂ)) :=
      continuous_const.add Complex.continuous_ofReal
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [Complex.ofReal_zero, add_zero] at h
  refine ⟨n, ‖g z₀‖ / 2, 2 * ‖g z₀‖, half_pos hgpos, by positivity, ?_⟩
  filter_upwards [hpath.eventually hfg, hpath.eventually hgnear, self_mem_nhdsWithin]
    with u hfu hgu hu
  have hu0 : 0 < u := hu
  have hnorm : ‖f (z₀ + u)‖ = u ^ (n : ℝ) * ‖g (z₀ + u)‖ := by
    rw [hfu, norm_smul, norm_pow, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hu0, ← Real.rpow_natCast]
  rw [hnorm]
  have hun : 0 ≤ u ^ (n : ℝ) := Real.rpow_nonneg hu0.le _
  constructor
  · calc ‖g z₀‖ / 2 * u ^ (n : ℝ) = u ^ (n : ℝ) * (‖g z₀‖ / 2) := by ring
      _ ≤ u ^ (n : ℝ) * ‖g (z₀ + u)‖ := mul_le_mul_of_nonneg_left hgu.1 hun
  · calc u ^ (n : ℝ) * ‖g (z₀ + u)‖ ≤ u ^ (n : ℝ) * (2 * ‖g z₀‖) :=
          mul_le_mul_of_nonneg_left hgu.2 hun
      _ = 2 * ‖g z₀‖ * u ^ (n : ℝ) := by ring

/-! ### The local power law of the oscillating pattern -/

/-- Near a point `q ≠ 1` with `ζ(q) ≠ 0`, `|ζ(q)|/2 < |ζ| < 2|ζ(q)|`. -/
theorem exists_norm_zeta_near_bounds {q : ℂ} (hq : q ≠ 1) (hz : riemannZeta q ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z - q‖ < r →
      ‖riemannZeta q‖ / 2 < ‖riemannZeta z‖ ∧ ‖riemannZeta z‖ < 2 * ‖riemannZeta q‖ := by
  have hc : ContinuousAt riemannZeta q := (differentiableAt_riemannZeta hq).continuousAt
  have hpos := norm_pos_iff.mpr hz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((Filter.Tendsto.eventually hc.norm (lt_mem_nhds (show ‖riemannZeta q‖ / 2 <
      ‖riemannZeta q‖ by linarith))).and
     (Filter.Tendsto.eventually hc.norm (gt_mem_nhds (show ‖riemannZeta q‖ <
      2 * ‖riemannZeta q‖ by linarith))))
  exact ⟨r, hr, fun z hz => hball (by rwa [dist_eq_norm])⟩

/-- `α ≤ Y u ≤ β` with `α > 0` gives `Y^b ≍ u^{-b}`, with the constants `min/max(α^b, β^b)`. -/
theorem rpow_bounds_of_mul_bounds {Y u α β b : ℝ} (hu : 0 < u) (hα : 0 < α)
    (h1 : α ≤ Y * u) (h2 : Y * u ≤ β) :
    min (α ^ b) (β ^ b) * u ^ (-b) ≤ Y ^ b ∧ Y ^ b ≤ max (α ^ b) (β ^ b) * u ^ (-b) := by
  have hY0 : 0 < Y * u := lt_of_lt_of_le hα h1
  have hsplit : Y ^ b = (Y * u) ^ b * u ^ (-b) := by
    have hYeq : Y = (Y * u) * u⁻¹ := by field_simp
    calc Y ^ b = ((Y * u) * u⁻¹) ^ b := by rw [← hYeq]
      _ = (Y * u) ^ b * (u⁻¹) ^ b := Real.mul_rpow hY0.le (inv_nonneg.mpr hu.le)
      _ = (Y * u) ^ b * u ^ (-b) := by rw [Real.inv_rpow hu.le, Real.rpow_neg hu.le]
  have hbr : min (α ^ b) (β ^ b) ≤ (Y * u) ^ b ∧ (Y * u) ^ b ≤ max (α ^ b) (β ^ b) := by
    rcases le_total 0 b with hb | hb
    · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow hα.le h1 hb),
        (Real.rpow_le_rpow hY0.le h2 hb).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos hY0 h2 hb),
        (Real.rpow_le_rpow_of_nonpos hα h1 hb).trans (le_max_left _ _)⟩
  have hupos : 0 < u ^ (-b) := Real.rpow_pos_of_pos hu _
  rw [hsplit]
  exact ⟨mul_le_mul_of_nonneg_right hbr.1 hupos.le, mul_le_mul_of_nonneg_right hbr.2 hupos.le⟩

/-- **The local prime mean of the oscillating pattern at the height `t₀` is `a/2`**: for `|a| ≤ 1`,
`t₀ ≠ 0`, `κ u^{-a/2} ≤ |F(1 + u + it₀)| ≤ K u^{-a/2}` for small `u > 0`, since
`|ζ(1 + u)| ≍ 1/u` and `|ζ(1 + u + 2it₀)| ≍ 1`. -/
theorem exists_norm_oscSeries_rpow_bounds {a t₀ : ℝ} (ha : |a| ≤ 1) (ht₀ : t₀ ≠ 0) :
    ∃ κ K u₀ : ℝ, 0 < κ ∧ 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u < u₀ →
      κ * u ^ (-(a / 2)) ≤
        ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + t₀ * I))‖ ∧
      ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + t₀ * I))‖ ≤
        K * u ^ (-(a / 2)) := by
  obtain ⟨ρ, hρ, hζ1⟩ := exists_norm_zeta_ge_near_one
  obtain ⟨K₀, hK₀, hpole⟩ := exists_norm_zeta_mul_sub_one_le
  have hq1 : (1 + 2 * t₀ * I : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.im h; norm_num at this; exact ht₀ this
  have hqz : riemannZeta (1 + 2 * t₀ * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
  obtain ⟨rq, hrq, hζq⟩ := exists_norm_zeta_near_bounds hq1 hqz
  have hcq : 0 < ‖riemannZeta (1 + 2 * t₀ * I)‖ := norm_pos_iff.mpr hqz
  set cq : ℝ := ‖riemannZeta (1 + 2 * t₀ * I)‖
  have hα : 0 < cq / 4 := by positivity
  have hβ : 0 < 2 * cq * K₀ := by positivity
  refine ⟨Real.exp (-(2 * primeSquareMass)) * min ((cq / 4) ^ (a / 2)) ((2 * cq * K₀) ^ (a / 2)),
    Real.exp (2 * primeSquareMass) * max ((cq / 4) ^ (a / 2)) ((2 * cq * K₀) ^ (a / 2)),
    min (min ρ rq) 1,
    mul_pos (Real.exp_pos _) (lt_min (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos hβ _)),
    lt_min (lt_min hρ hrq) one_pos, fun u hu hu₀ => ?_⟩
  have huρ : u < ρ := lt_of_lt_of_le hu₀ ((min_le_left _ _).trans (min_le_left _ _))
  have huq : u < rq := lt_of_lt_of_le hu₀ ((min_le_left _ _).trans (min_le_right _ _))
  have hu1 : u < 1 := lt_of_lt_of_le hu₀ (min_le_right _ _)
  set w : ℂ := ((1 + u : ℝ) : ℂ) + t₀ * I
  have hwre : 1 < w.re := by simp [w]; linarith
  have hwm : w - t₀ * I = ((1 + u : ℝ) : ℂ) := by simp only [w]; ring
  have hwp : w + t₀ * I - (1 + 2 * t₀ * I) = (u : ℂ) := by simp only [w]; push_cast; ring
  have hne1 : ((1 + u : ℝ) : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h
    rw [Complex.ofReal_re, Complex.one_re] at this; linarith
  have hsub : ((1 + u : ℝ) : ℂ) - 1 = (u : ℂ) := by push_cast; ring
  have hun : ‖(u : ℂ)‖ = u := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  -- `|ζ(1 + u)| u ∈ [1/2, K₀]` and `|ζ(1 + u + 2it₀)| ∈ (c_q/2, 2c_q)`
  have hlo1 : 1 / 2 ≤ ‖riemannZeta ((1 + u : ℝ) : ℂ)‖ * u := by
    have h := hζ1 _ hne1 (by rw [hsub, hun]; exact huρ)
    rw [hsub, hun, div_le_iff₀ (by positivity)] at h
    linarith
  have hhi1 : ‖riemannZeta ((1 + u : ℝ) : ℂ)‖ * u ≤ K₀ := by
    have h := hpole ((1 + u : ℝ) : ℂ) (by rw [Complex.ofReal_re]; linarith)
      (by rw [Complex.ofReal_re]; linarith) (by rw [Complex.ofReal_im, abs_zero]; norm_num)
    rwa [hsub, hun] at h
  have hq := hζq (w + t₀ * I) (by rw [hwp, hun]; exact huq)
  have hYu : cq / 4 ≤ ‖riemannZeta ((1 + u : ℝ) : ℂ)‖ * ‖riemannZeta (w + t₀ * I)‖ * u ∧
      ‖riemannZeta ((1 + u : ℝ) : ℂ)‖ * ‖riemannZeta (w + t₀ * I)‖ * u ≤ 2 * cq * K₀ := by
    constructor
    · calc cq / 4 = 1 / 2 * (cq / 2) := by ring
        _ ≤ (‖riemannZeta ((1 + u : ℝ) : ℂ)‖ * u) * ‖riemannZeta (w + t₀ * I)‖ :=
            mul_le_mul hlo1 hq.1.le (by positivity) (by positivity)
        _ = _ := by ring
    · calc _ = (‖riemannZeta ((1 + u : ℝ) : ℂ)‖ * u) * ‖riemannZeta (w + t₀ * I)‖ := by ring
        _ ≤ K₀ * (2 * cq) := mul_le_mul hhi1 hq.2.le (norm_nonneg _) hK₀.le
        _ = 2 * cq * K₀ := by ring
  have hb := rpow_bounds_of_mul_bounds (b := a / 2) hu hα hYu.1 hYu.2
  obtain ⟨hup, hlow⟩ := norm_oscSeries_le_ge ha t₀ hwre
  rw [hwm] at hup hlow
  constructor
  · calc Real.exp (-(2 * primeSquareMass)) * min ((cq / 4) ^ (a / 2)) ((2 * cq * K₀) ^ (a / 2)) *
          u ^ (-(a / 2))
        = Real.exp (-(2 * primeSquareMass)) *
            (min ((cq / 4) ^ (a / 2)) ((2 * cq * K₀) ^ (a / 2)) * u ^ (-(a / 2))) := mul_assoc _ _ _
      _ ≤ Real.exp (-(2 * primeSquareMass)) *
            (‖riemannZeta ((1 + u : ℝ) : ℂ)‖ * ‖riemannZeta (w + t₀ * I)‖) ^ (a / 2) :=
          mul_le_mul_of_nonneg_left hb.1 (Real.exp_pos _).le
      _ ≤ _ := hlow
  · calc _ ≤ Real.exp (2 * primeSquareMass) *
            (‖riemannZeta ((1 + u : ℝ) : ℂ)‖ * ‖riemannZeta (w + t₀ * I)‖) ^ (a / 2) := hup
      _ ≤ Real.exp (2 * primeSquareMass) *
            (max ((cq / 4) ^ (a / 2)) ((2 * cq * K₀) ^ (a / 2)) * u ^ (-(a / 2))) :=
          mul_le_mul_of_nonneg_left hb.2 (Real.exp_pos _).le
      _ = _ := (mul_assoc _ _ _).symm

/-! ### The height-local quantization -/

theorem weightDirichletSeries_dampedSignWeight (f : ℕ →*₀ ℝ) (ε : ℝ) (s : ℂ) :
    weightDirichletSeries (dampedSignWeight f ε) s =
      ∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(s + ε)) := by
  refine tsum_congr fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [dampedSignWeight]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [dampedSignWeight, Complex.ofReal_mul, Complex.ofReal_cpow hd0.le, mul_assoc,
    ← Complex.cpow_add _ _ hdC]
  congr 2
  push_cast
  ring

/-- **Below half damping an oscillating pattern is paid only at amplitude `0`.** For `0 < ε < 1/2`,
`t₀ ≠ 0` and `0 < |a| ≤ 1`, the weight `f_{a,t₀}(d) d^{-ε}` has unbounded receiver: a paid receiver
makes `|C(1 − ε + it₀ + u)|` an integral power of `u`, while the local prime mean `a/2` makes it
`≍ u^{-a/2}`. -/
theorem not_receiverBounded_oscPattern_damped {a t₀ ε : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0)
    (ht₀ : t₀ ≠ 0) (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ¬ ReceiverBounded (dampedSignWeight (oscPattern a t₀) ε) := by
  rintro ⟨E, hE⟩
  set c := dampedSignWeight (oscPattern a t₀) ε
  have hc : DampedClass 1 ε c := fun d => by
    simp only [c, dampedSignWeight]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (abs_oscPattern_le ha t₀ d)
  set s₁ : ℂ := ((1 - ε : ℝ) : ℂ) + t₀ * I
  have hs₁1 : s₁ ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp [s₁] at this; exact ht₀ this
  have hs₁re : s₁.re = 1 - ε := by simp [s₁]
  -- the analytic numerator `Q = Φ + mζ` and the denominator `ζ` at `s₁`
  have hΦ : AnalyticAt ℂ (complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d))) s₁ :=
    (differentiableOn_complexMellinPairing (weightCenteredPrefix_zero _ _) fun T => hE T).analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) / 2 < s₁.re by rw [hs₁re]; linarith))
  have hζ : AnalyticAt ℂ riemannZeta s₁ := analyticOn_riemannZeta s₁ hs₁1
  set Q : ℂ → ℂ := fun z => complexMellinPairing (weightCenteredPrefix c (∑' d : ℕ, c d / d)) z +
    ((∑' d : ℕ, c d / d : ℝ) : ℂ) * riemannZeta z
  have hQ : AnalyticAt ℂ Q s₁ := hΦ.add (analyticAt_const.mul hζ)
  -- on the ray `s₁ + u`: `C ζ = Q`, and `|C| ≍ u^{-a/2}`
  have hray : ∀ u : ℝ, 0 < u → u < ε →
      weightDirichletSeries c (s₁ + u) * riemannZeta (s₁ + u) = Q (s₁ + u) := by
    intro u hu huε
    have hre : (s₁ + u).re = 1 - ε + u := by rw [Complex.add_re, hs₁re, Complex.ofReal_re]
    have hid := complexMellinPairing_eq_zeta_mul_of_summable (c := c) (θ := 1 - ε + u / 2)
      (s := s₁ + u) (by linarith) (by rw [hre]; linarith) (by rw [hre]; linarith)
      (summable_abs_mul_rpow_of_dampedClass hε hc (by linarith))
    simp only [Q]
    rw [hid]
    ring
  obtain ⟨κ, K, u₀, hκ, hu₀, hbd⟩ := exists_norm_oscSeries_rpow_bounds ha ht₀
  have hCeq : ∀ u : ℝ, weightDirichletSeries c (s₁ + u) =
      ∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + t₀ * I)) := by
    intro u
    rw [weightDirichletSeries_dampedSignWeight,
      show s₁ + (u : ℂ) + (ε : ℂ) = ((1 + u : ℝ) : ℂ) + t₀ * I by simp only [s₁]; push_cast; ring]
  have hIoo : Set.Ioo (0 : ℝ) (min u₀ ε) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (lt_min hu₀ hε)
  -- the order of `ζ` at `s₁`
  have hζ0 : ¬ ∀ᶠ z in 𝓝 s₁, riemannZeta z = 0 := fun h =>
    RHTower.analyticOrderAt_riemannZeta_ne_top_of_ne_one hs₁1 (analyticOrderAt_eq_top.mpr h)
  obtain ⟨q, Aζ, Bζ, hAζ, hBζ, hζray⟩ := exists_ray_bounds_of_order hζ hζ0
  by_cases hQ0 : ∀ᶠ z in 𝓝 s₁, Q z = 0
  · -- `Q ≡ 0` near `s₁`, against `|C| |ζ| > 0`
    have hpath : Tendsto (fun u : ℝ => s₁ + (u : ℂ)) (𝓝[>] 0) (𝓝 s₁) := by
      have hcont : Continuous (fun u : ℝ => s₁ + (u : ℂ)) :=
        continuous_const.add Complex.continuous_ofReal
      have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [Complex.ofReal_zero, add_zero] at h
    obtain ⟨u, hQu, hζu, hu⟩ := ((hpath.eventually hQ0).and (hζray.and hIoo)).exists
    have hCu := (hbd u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _))).1
    have hprod := hray u hu.1 (lt_of_lt_of_le hu.2 (min_le_right _ _))
    rw [hQu, hCeq] at hprod
    have h1 : 0 < κ * u ^ (-(a / 2)) := mul_pos hκ (Real.rpow_pos_of_pos hu.1 _)
    have h2 : 0 < Aζ * u ^ (q : ℝ) := mul_pos hAζ (Real.rpow_pos_of_pos hu.1 _)
    have hpos := mul_pos (lt_of_lt_of_le h1 hCu) (lt_of_lt_of_le h2 hζu.1)
    rw [← norm_mul, hprod, norm_zero] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨p, AQ, BQ, hAQ, hBQ, hQray⟩ := exists_ray_bounds_of_order hQ hQ0
  -- `|C| = |Q|/|ζ| ≍ u^{p − q}`
  have hup : ∀ᶠ u in 𝓝[>] (0 : ℝ), κ * u ^ (-(a / 2)) ≤ (BQ / Aζ) * u ^ ((p : ℝ) - q) := by
    filter_upwards [hζray, hQray, hIoo] with u hζu hQu hu
    have hCu := (hbd u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _))).1
    have hprod := hray u hu.1 (lt_of_lt_of_le hu.2 (min_le_right _ _))
    rw [hCeq] at hprod
    have hζpos : 0 < Aζ * u ^ (q : ℝ) := mul_pos hAζ (Real.rpow_pos_of_pos hu.1 _)
    have hnorm := congrArg norm hprod
    rw [norm_mul] at hnorm
    rw [Real.rpow_sub hu.1, div_mul_div_comm, le_div_iff₀ hζpos]
    calc κ * u ^ (-(a / 2)) * (Aζ * u ^ (q : ℝ))
        ≤ ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + t₀ * I))‖ *
            ‖riemannZeta (s₁ + u)‖ :=
          mul_le_mul hCu hζu.1 hζpos.le (norm_nonneg _)
      _ = ‖Q (s₁ + u)‖ := hnorm
      _ ≤ BQ * u ^ (p : ℝ) := hQu.2
  have hlow : ∀ᶠ u in 𝓝[>] (0 : ℝ), (AQ / Bζ) * u ^ ((p : ℝ) - q) ≤ K * u ^ (-(a / 2)) := by
    filter_upwards [hζray, hQray, hIoo] with u hζu hQu hu
    have hCu := (hbd u hu.1 (lt_of_lt_of_le hu.2 (min_le_left _ _))).2
    have hprod := hray u hu.1 (lt_of_lt_of_le hu.2 (min_le_right _ _))
    rw [hCeq] at hprod
    have hζpos : 0 < Bζ * u ^ (q : ℝ) := mul_pos hBζ (Real.rpow_pos_of_pos hu.1 _)
    have hnorm := congrArg norm hprod
    rw [norm_mul] at hnorm
    rw [Real.rpow_sub hu.1, div_mul_div_comm, div_le_iff₀ hζpos]
    have hKpos : 0 ≤ K * u ^ (-(a / 2)) := (norm_nonneg _).trans hCu
    calc AQ * u ^ (p : ℝ) ≤ ‖Q (s₁ + u)‖ := hQu.1
      _ = ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-(((1 + u : ℝ) : ℂ) + t₀ * I))‖ *
            ‖riemannZeta (s₁ + u)‖ := hnorm.symm
      _ ≤ K * u ^ (-(a / 2)) * (Bζ * u ^ (q : ℝ)) :=
          mul_le_mul hCu hζu.2 (norm_nonneg _) hKpos
  have heq := eq_of_rpow_le_rpow_nhdsGT hκ (div_pos hAQ hBζ) hup hlow
  -- `−a/2 = p − q` with `0 < |a| ≤ 1` is impossible
  have habs := abs_le.mp ha
  rcases lt_trichotomy p q with hpq | hpq | hpq
  · have : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
    linarith
  · subst hpq; exact ha0 (by linarith)
  · have : (q : ℝ) + 1 ≤ p := by exact_mod_cast hpq
    linarith

/-- At amplitude `0` the pattern is the unit mass at `1`. -/
theorem oscPattern_zero_amplitude (t₀ : ℝ) : oscPattern 0 t₀ = constantSignHom 0 := by
  refine DFunLike.ext _ _ fun n => ?_
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => rw [oscPattern_prime 0 t₀ hp, constantSignHom_prime 0 hp, zero_mul]
  | mul m n hm hn => rw [map_mul, map_mul, hm, hn]

/-- **The oscillating patterns below half damping.** For `0 < ε < 1/2`, `t₀ ≠ 0` and `|a| ≤ 1`, the
weight `f_{a,t₀}(d) d^{-ε}`, `f(p) = a cos(t₀ log p)`, is paid iff `a = 0`. -/
theorem receiverBounded_oscPattern_damped_iff {a t₀ ε : ℝ} (ha : |a| ≤ 1) (ht₀ : t₀ ≠ 0)
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ReceiverBounded (dampedSignWeight (oscPattern a t₀) ε) ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha0
    exact not_receiverBounded_oscPattern_damped ha ha0 ht₀ hε hε2 h
  · rintro rfl
    rw [oscPattern_zero_amplitude]
    exact receiverBounded_constantSign_zero ε

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
