import GaloisForLFunctions.GaloisTheoryOfZeros.ForEachSignALoopOfSaddlesTurnsTheRatioOfTheTwoTerms
import GaloisForLFunctions.GaloisTheoryOfZeros.AZeroOfAStripStaysInItsStripWhereTheCosineTermDominates

/-!
# A signed loop of saddles exchanges the zeros of two adjacent strips

On a signed loop `2S₀ cos ξ₀(s) = εB₀` up to `|B₀|/4096`, `ξ₀(s) = e^{iπs}/4`. For `θ ∈ πℤ` with
`cos θ = −ε` the model `B₀ + 2S₀ cos ζ` nearly vanishes at `ζ = θ + ξ₀(s)`: its zero near
`θ + 1/4`, in the strip of `θ`, is carried around the half circle to the zero near `θ − 1/4`, in
the strip of `θ − π`.

**Theorem** (`exists_exchange`). Far out, the zero of `H_{τ(a(0))}` near `θ + 1/4` is joined
through simple zeros, along the loop, to the zero near `θ − 1/4`.

Proof. The moving disc `|az − θ − ξ₀(s)| ≤ 1/8` holds no zero on the annulus of inner radius
`1/16`, and a zero at `s = 0`. On the disc `sin ζ = cos θ sin(ζ − θ)` and
`Re(e^{−iπs} sin(ζ − θ)) ≥ 1/9`, so the function is injective there with nonvanishing derivative:
the zero is alone in the moving disc and simple.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The sine on a disc off the centre -/

/-- `Re(u sin ξ) ≥ 1/9` on the disc of radius `1/8` around a point `ξ₀` with `uξ₀ = 1/4`,
`|u| = 1`. -/
theorem le_re_mul_sin_of_mem_disc {u ξ₀ ξ : ℂ} (hu : ‖u‖ = 1) (hξ₀ : u * ξ₀ = 1 / 4)
    (hξ : ‖ξ - ξ₀‖ ≤ 1 / 8) : 1 / 9 ≤ (u * Complex.sin ξ).re := by
  have hq : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
  have hξ₀n : ‖ξ₀‖ = 1 / 4 := by
    have h := congrArg norm hξ₀
    rw [norm_mul, hu, one_mul, hq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num)] at h
    exact h
  have hξn : ‖ξ‖ ≤ 3 / 8 := by
    have h := norm_add_le (ξ - ξ₀) ξ₀
    rw [sub_add_cancel] at h
    linarith
  have hsin := Complex.sin_bound (x := ξ) (by linarith)
  have h3 : ‖ξ‖ ^ 3 ≤ 27 / 512 := by
    have h := pow_le_pow_left₀ (norm_nonneg ξ) hξn 3
    norm_num at h
    exact h
  have h5 : ‖ξ‖ ^ 5 ≤ 243 / 32768 := by
    have h := pow_le_pow_left₀ (norm_nonneg ξ) hξn 5
    norm_num at h
    exact h
  have hdiff : ‖Complex.sin ξ - ξ‖ ≤ 1 / 100 := by
    have e : Complex.sin ξ - ξ = Complex.sin ξ - (ξ - ξ ^ 3 / 6) - ξ ^ 3 / 6 := by ring
    have h6 : ‖ξ ^ 3 / 6‖ = ‖ξ‖ ^ 3 / 6 := by rw [norm_div, norm_pow, Complex.norm_ofNat]
    have h7 := norm_sub_le (Complex.sin ξ - (ξ - ξ ^ 3 / 6)) (ξ ^ 3 / 6)
    rw [h6] at h7
    rw [e]
    linarith
  have e : u * Complex.sin ξ = 1 / 4 + u * (ξ - ξ₀) + u * (Complex.sin ξ - ξ) := by
    rw [← hξ₀]
    ring
  have h8 : ‖u * (ξ - ξ₀)‖ ≤ 1 / 8 := by
    rw [norm_mul, hu, one_mul]
    exact hξ
  have h9 : ‖u * (Complex.sin ξ - ξ)‖ ≤ 1 / 100 := by
    rw [norm_mul, hu, one_mul]
    exact hdiff
  have h10 := (abs_le.mp ((Complex.abs_re_le_norm _).trans h8)).1
  have h11 := (abs_le.mp ((Complex.abs_re_le_norm _).trans h9)).1
  rw [e, Complex.add_re, Complex.add_re, hq, Complex.ofReal_re]
  linarith

/-- A disc around `θ + c` of radius `r` lies in the strip of `θ` if
`1/8 ≤ c − r`, `c + r ≤ π − 1/8`, `r ≤ 1`. -/
theorem mem_cosStrip_of_norm_sub_le {θ c r : ℝ} {ζ : ℂ} (h : ‖ζ - θ - c‖ ≤ r)
    (h1 : 1 / 8 ≤ c - r) (h2 : c + r ≤ π - 1 / 8) (h3 : r ≤ 1) : ζ ∈ cosStrip θ := by
  have hre := abs_le.mp ((Complex.abs_re_le_norm _).trans h)
  have him := abs_le.mp ((Complex.abs_im_le_norm _).trans h)
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero] at hre him
  exact ⟨by linarith [hre.1], by linarith [hre.2], by linarith [him.1], by linarith [him.2]⟩

/-! ## The base of a signed loop -/

theorem norm_cos_quarter_le : ‖Complex.cos (1 / 4 : ℂ)‖ ≤ 969 / 1000 := by
  have e : Complex.cos (1 / 4 : ℂ) = ((Real.cos (1 / 4) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos]
    norm_num
  have hpos : 0 < Real.cos (1 / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  have h := (abs_le.mp (Real.cos_bound (x := 1 / 4) (by rw [abs_of_pos] <;> norm_num))).2
  have e2 : (1 : ℝ) - (1 / 4) ^ 2 / 2 = 31 / 32 := by norm_num
  have e3 : (1 / 4 : ℝ) ^ 4 * (5 / 96) = 5 / 24576 := by norm_num
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), e2, e3] at h
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  linarith

/-- At the base of a signed loop the cosine term dominates. -/
theorem IsSignedLoop.cosineSide {ε : ℂ} {a : ℝ → ℂ} (h : IsSignedLoop ε a) (hε : ‖ε‖ = 1) :
    CosineSide (a 0) := by
  have h1 := h.signed 0 ⟨le_rfl, zero_le_one⟩
  rw [turnPoint_zero] at h1
  have h2 := norm_sub_norm_le (ε * bulkTerm (a 0)) (2 * saddleTerm (a 0) * Complex.cos (1 / 4))
  rw [norm_sub_rev, norm_mul ε, hε, one_mul, norm_mul (2 * saddleTerm (a 0))] at h2
  have h3 : ‖2 * saddleTerm (a 0)‖ * ‖Complex.cos (1 / 4 : ℂ)‖ ≤
      ‖2 * saddleTerm (a 0)‖ * (969 / 1000) :=
    mul_le_mul_of_nonneg_left norm_cos_quarter_le (norm_nonneg _)
  unfold CosineSide
  linarith [norm_nonneg (2 * saddleTerm (a 0))]

/-! ## The exchange -/

/-- **A signed loop exchanges the zeros of two adjacent strips.** For every window `R` there is
`σ₀` such that on a signed loop of sign `ε` beyond `σ₀` and for `θ ∈ πℤ` with `cos θ = −ε` in the
window: a zero of `H_{τ(a(0))}` in the strip of `θ` is joined through simple zeros to a zero in
the strip of `θ − π`. -/
theorem exists_exchange (R : ℝ) : ∃ σ₀ : ℝ, ∀ {ε : ℂ} {a : ℝ → ℂ}, IsSignedLoop ε a →
    (ε = 1 ∨ ε = -1) → (∀ s, σ₀ ≤ (a s).re) → ∀ θ : ℝ, Real.sin θ = 0 →
    (Real.cos θ : ℂ) = -ε → |θ| + π + 2 ≤ R →
    ∃ z₀ z₁ : ℂ, complexHeat (saddleTime (a 0)) z₀ = 0 ∧ a 0 * z₀ ∈ cosStrip θ ∧
      complexHeat (saddleTime (a 0)) z₁ = 0 ∧ a 0 * z₁ ∈ cosStrip (θ - π) ∧
      SimplyJoined (saddleTime (a 0)) z₀ (saddleTime (a 0)) z₁ := by
  obtain ⟨σ₀, hσ₀⟩ := exists_forall_norm_complexHeat_sub_wide_model_le R (ε := 1 / 16384)
    (by norm_num)
  refine ⟨σ₀, fun {ε a} h hε hfar θ hθ hcos hθR => ?_⟩
  have hπ := Real.pi_gt_three
  have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hsinθ : Complex.sin (θ : ℂ) = 0 := by rw [← Complex.ofReal_sin, hθ, Complex.ofReal_zero]
  have hcosθ : Complex.cos (θ : ℂ) = -ε := by rw [← Complex.ofReal_cos, hcos]
  have hθn : ‖(θ : ℂ)‖ = |θ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hBpos : ∀ s, 0 < ‖bulkTerm (a s)‖ := fun s =>
    norm_pos_iff.mpr (h.region s).bulkTerm_ne_zero
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- the two terms on the loop
  have hE : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖2 * saddleTerm (a s) * Complex.cos (θ : ℂ) * Complex.cos (turnPoint s) +
        bulkTerm (a s)‖ ≤ ‖bulkTerm (a s)‖ / 4096 := by
    intro s hs
    have e : 2 * saddleTerm (a s) * Complex.cos (θ : ℂ) * Complex.cos (turnPoint s) +
        bulkTerm (a s) =
        -ε * (2 * saddleTerm (a s) * Complex.cos (turnPoint s) - ε * bulkTerm (a s)) := by
      rw [hcosθ]
      linear_combination (-(bulkTerm (a s))) * hεsq
    rw [e, norm_mul, norm_neg, hεn, one_mul]
    linarith [h.signed s hs]
  have hSB : ∀ s ∈ Icc (0 : ℝ) 1, ‖saddleTerm (a s)‖ ≤ ‖bulkTerm (a s)‖ ∧
      ‖bulkTerm (a s)‖ ≤ 3 * ‖saddleTerm (a s)‖ := by
    intro s hs
    have h1 := h.signed s hs
    obtain ⟨hc1, hc2⟩ := norm_cos_turnPoint_bounds s
    have h2 := norm_sub_norm_le (2 * saddleTerm (a s) * Complex.cos (turnPoint s))
      (ε * bulkTerm (a s))
    have h3 := norm_sub_norm_le (ε * bulkTerm (a s))
      (2 * saddleTerm (a s) * Complex.cos (turnPoint s))
    rw [norm_sub_rev] at h3
    simp only [norm_mul, Complex.norm_ofNat, hεn, one_mul] at h2 h3
    have h4 : 2 * ‖saddleTerm (a s)‖ * (15 / 16) ≤
        2 * ‖saddleTerm (a s)‖ * ‖Complex.cos (turnPoint s)‖ :=
      mul_le_mul_of_nonneg_left hc1 (by positivity)
    have h5 : 2 * ‖saddleTerm (a s)‖ * ‖Complex.cos (turnPoint s)‖ ≤
        2 * ‖saddleTerm (a s)‖ * (17 / 16) :=
      mul_le_mul_of_nonneg_left hc2 (by positivity)
    have hB := (hBpos s).le
    have hS := norm_nonneg (saddleTerm (a s))
    constructor <;> linarith
  have hmodel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ ζ : ℂ, ‖ζ‖ ≤ R →
      ‖complexHeat (saddleTime (a s)) (ζ / a s) - bulkTerm (a s) -
        2 * saddleTerm (a s) * Complex.cos ζ‖ ≤ ‖bulkTerm (a s)‖ / 8192 := by
    intro s hs ζ hζ
    have h1 := hσ₀ (a s) (h.region s).wide (hfar s) ζ hζ
    linarith [(hSB s hs).1]
  have hwin : ∀ s (ξ : ℂ), ‖ξ - turnPoint s‖ ≤ 1 / 8 → ‖(θ : ℂ) + ξ‖ ≤ R - 1 := by
    intro s ξ hξ
    have h1 := norm_add_le (θ : ℂ) ξ
    have h2 := norm_add_le (ξ - turnPoint s) (turnPoint s)
    rw [sub_add_cancel, norm_turnPoint] at h2
    rw [hθn] at h1
    linarith
  have hscale : ∀ s (z : ℂ), a s * z / a s = z := fun s z =>
    mul_div_cancel_left₀ z (h.region s).ne_zero
  -- no zero on the annulus of the moving disc
  have hann : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, complexHeat (saddleTime (a s)) z = 0 →
      ‖a s * z - θ - turnPoint s‖ ≤ 1 / 8 → ‖a s * z - θ - turnPoint s‖ < 1 / 16 := by
    intro s hs z hz hd
    by_contra hcon
    push Not at hcon
    have e : ((θ : ℂ) + (a s * z - θ)) / a s = z := by rw [add_sub_cancel, hscale]
    have h1 := le_norm_of_mem_annulus (ξ := a s * z - θ) hsinθ (norm_turnPoint s) (hE s hs)
      (hmodel s hs _ (by linarith [hwin s (a s * z - θ) hd])) hcon hd
    rw [e, hz, norm_zero] at h1
    linarith [hBpos s]
  -- on the moving disc the function is injective with nonvanishing derivative
  have hdisc : ∀ s ∈ Icc (0 : ℝ) 1,
      InjOn (fun ζ : ℂ => complexHeat (saddleTime (a s)) (ζ / a s))
          (Metric.closedBall ((θ : ℂ) + turnPoint s) (1 / 8)) ∧
        ∀ ζ ∈ Metric.closedBall ((θ : ℂ) + turnPoint s) (1 / 8),
          deriv (fun ζ : ℂ => complexHeat (saddleTime (a s)) (ζ / a s)) ζ ≠ 0 := by
    intro s hs
    obtain ⟨u, hun, hut⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ u * turnPoint s = 1 / 4 := by
      refine ⟨cexp (-(((π * s : ℝ) : ℂ) * I)), ?_, ?_⟩
      · rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
      · rw [turnPoint, mul_left_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
          mul_one]
    have hc : ‖-ε * u‖ = 1 := by rw [norm_mul, norm_neg, hεn, hun, one_mul]
    refine injOn_and_deriv_ne_zero (differentiable_scaledHeat (a s)) (convex_closedBall _ _)
      (c := -ε * u) (m := 1 / 9) (δ := ‖bulkTerm (a s)‖ / 8192) hc (fun ζ hζ => ?_) ?_
      (fun ζ hζ => ?_)
    · rw [Metric.mem_closedBall, dist_eq_norm, ← sub_sub] at hζ
      have hsin : Complex.sin ζ = -ε * Complex.sin (ζ - θ) := by
        have e : ζ = (θ : ℂ) + (ζ - θ) := by ring
        conv_lhs => rw [e]
        rw [Complex.sin_add, hsinθ, zero_mul, zero_add, hcosθ]
      have e2 : -ε * u * Complex.sin ζ = u * Complex.sin (ζ - θ) := by
        rw [hsin]
        linear_combination (u * Complex.sin (ζ - θ)) * hεsq
      rw [e2]
      exact le_re_mul_sin_of_mem_disc hun hut hζ
    · linarith [(hSB s hs).2, hBpos s]
    · rw [Metric.mem_closedBall, dist_eq_norm, ← sub_sub] at hζ
      have h1 := hwin s (ζ - θ) hζ
      rw [add_sub_cancel] at h1
      exact norm_deriv_add_sin_le (differentiable_scaledHeat (a s)) (hmodel s hs) h1
  -- a zero in the first disc
  have ha0 := (h.region 0).ne_zero
  have han : 0 < ‖a 0‖ := norm_pos_iff.mpr ha0
  obtain ⟨z₀, hz₀d, hz₀⟩ : ∃ z₀ : ℂ, ‖a 0 * z₀ - θ - turnPoint 0‖ < 1 / 16 ∧
      complexHeat (saddleTime (a 0)) z₀ = 0 := by
    have hζ0 : ‖(θ : ℂ) + turnPoint 0‖ ≤ R := by
      linarith [hwin 0 (turnPoint 0) (by rw [sub_self, norm_zero]; norm_num)]
    have hcen : ‖complexHeat (saddleTime (a 0)) (((θ : ℂ) + turnPoint 0) / a 0)‖ <
        ‖bulkTerm (a 0)‖ * (9 / 8192) := by
      have h1 := norm_le_at_turnPoint hsinθ (hE 0 h01) (hmodel 0 h01 _ hζ0)
      linarith [hBpos 0]
    have hshift : ∀ z : ℂ, a 0 * z - θ - turnPoint 0 =
        a 0 * (z - ((θ : ℂ) + turnPoint 0) / a 0) := by
      intro z
      rw [mul_sub, mul_div_cancel₀ _ ha0]
      ring
    obtain ⟨z₀, hz₀r, hz₀⟩ := RigidArithmeticOfCuts.exists_zero_of_norm_center_lt
      (differentiable_complexHeat (saddleTime (a 0))) (c := ((θ : ℂ) + turnPoint 0) / a 0)
      (r := 1 / 16 / ‖a 0‖) (μ := ‖bulkTerm (a 0)‖ * (9 / 8192))
      (div_pos (by norm_num) han) (mul_pos (hBpos 0) (by norm_num)) hcen (by
        intro z hz
        have hξ : ‖a 0 * z - θ - turnPoint 0‖ = 1 / 16 := by
          rw [hshift, norm_mul, hz, mul_div_cancel₀ _ han.ne']
        have e : ((θ : ℂ) + (a 0 * z - θ)) / a 0 = z := by rw [add_sub_cancel, hscale]
        have h1 := le_norm_of_mem_annulus (ξ := a 0 * z - θ) hsinθ (norm_turnPoint 0)
          (hE 0 h01)
          (hmodel 0 h01 _ (by linarith [hwin 0 (a 0 * z - θ) (by rw [hξ]; norm_num)]))
          hξ.ge (by rw [hξ]; norm_num)
        rwa [e] at h1)
    refine ⟨z₀, ?_, hz₀⟩
    rw [hshift, norm_mul]
    rw [lt_div_iff₀ han] at hz₀r
    linarith [mul_comm ‖a 0‖ ‖z₀ - ((θ : ℂ) + turnPoint 0) / a 0‖]
  -- the zero follows the moving disc
  have hnorm : ∀ s, 1 ≤ ‖a s‖ := fun s => by
    have h1 := (le_abs_self _).trans (Complex.abs_re_le_norm (a s))
    linarith [(h.region s).1]
  have hdc : Continuous fun p : ℝ × ℂ => ‖a p.1 * p.2 - θ - turnPoint p.1‖ - 1 / 8 :=
    ((((h.continuous.comp continuous_fst).mul continuous_snd).sub continuous_const).sub
      (continuous_turnPoint.comp continuous_fst)).norm.sub continuous_const
  have hball : ∀ s (z : ℂ), ‖a s * z - θ - turnPoint s‖ - 1 / 8 ≤ 0 →
      a s * z ∈ Metric.closedBall ((θ : ℂ) + turnPoint s) (1 / 8) := by
    intro s z hd
    rw [Metric.mem_closedBall, dist_eq_norm, ← sub_sub]
    linarith
  obtain ⟨z₁, hj, hz₁, hd₁⟩ := exists_simplyJoined_of_alone (γ := fun s => saddleTime (a s))
    (d := fun s z => ‖a s * z - θ - turnPoint s‖ - 1 / 8) (M := |θ| + 1)
    (continuous_saddleTime_comp h.continuous h.region).continuousOn
    (fun s _ => (h.region s).time_re_pos) hdc.continuousOn
    (fun s _ z hd => by
      have h1 := norm_add_le (a s * z - θ - turnPoint s) ((θ : ℂ) + turnPoint s)
      have e : a s * z - θ - turnPoint s + ((θ : ℂ) + turnPoint s) = a s * z := by ring
      have h2 := norm_add_le (θ : ℂ) (turnPoint s)
      rw [e, norm_mul] at h1
      rw [hθn, norm_turnPoint] at h2
      have h3 : 1 * ‖z‖ ≤ ‖a s‖ * ‖z‖ := mul_le_mul_of_nonneg_right (hnorm s) (norm_nonneg z)
      linarith)
    (fun s hs z hz hd => by linarith [hann s hs z hz (by linarith)])
    (fun s hs z z' hz hd hz' hd' => mul_left_cancel₀ (h.region s).ne_zero
      ((hdisc s hs).1 (hball s z hd) (hball s z' hd') (by
        show complexHeat (saddleTime (a s)) (a s * z / a s) =
          complexHeat (saddleTime (a s)) (a s * z' / a s)
        rw [hscale, hscale, hz, hz'])))
    (fun s hs z _ hd h0 => (hdisc s hs).2 (a s * z) (hball s z hd)
      (by rw [deriv_scaledHeat, hscale, h0, zero_div]))
    hz₀ (by linarith)
  have hj' : SimplyJoined (saddleTime (a 0)) z₀ (saddleTime (a 1)) z₁ := hj
  have hz₁' : complexHeat (saddleTime (a 1)) z₁ = 0 := hz₁
  have hd₁' : ‖a 1 * z₁ - θ - turnPoint 1‖ - 1 / 8 < 0 := hd₁
  rw [h.closed] at hj' hz₁' hd₁'
  rw [turnPoint_one] at hd₁'
  rw [turnPoint_zero] at hz₀d
  have hq : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
  refine ⟨z₀, z₁, hz₀, ?_, hz₁', ?_, hj'⟩
  · rw [hq] at hz₀d
    exact mem_cosStrip_of_norm_sub_le (c := 1 / 4) (r := 1 / 16) hz₀d.le (by norm_num)
      (by linarith) (by norm_num)
  · have e : a 0 * z₁ - ((θ - π : ℝ) : ℂ) - ((π - 1 / 4 : ℝ) : ℂ) =
        a 0 * z₁ - θ - -(1 / 4) := by
      push_cast
      ring
    refine mem_cosStrip_of_norm_sub_le (c := π - 1 / 4) (r := 1 / 8) ?_ (by linarith)
      (by linarith) (by norm_num)
    rw [e]
    linarith

end

end GaloisForLFunctions.GaloisTheoryOfZeros
