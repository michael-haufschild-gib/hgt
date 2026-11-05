import GaloisForLFunctions.ArithmeticDiscreteness.ANearCoincidenceFlattensZeta
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The depth of an FE pair is read on the line

The functional-equation form of collide-or-repel. An off-line zero `ρ = ½ + δ + iγ` comes with its
partner `1 − ρ̄ = ½ − δ + iγ`; the two are a near-coincidence of size `2|δ|` centred on the critical
line, so a depth gap for `ζ` (B54 restricted to FE pairs) is a statement about `ζ` on the line.

* **Two symmetric zeros flatten the centre** (`norm_le_of_two_symmetric_zeros`). If `f` is
  holomorphic and bounded by `M` on `‖z − c‖ ≤ 2R` and vanishes at `c ± h`, `‖h‖ ≤ R/8`, then
  `‖f(c)‖ ≤ (24M/R²) ‖h‖²`: the derivative at `c − h` is `≤ 16M‖h‖/R²`
  (`norm_deriv_mul_le_of_two_zeros`), and the Taylor remainder from `c − h` to `c` is
  `≤ 8M‖h‖²/R²` (`norm_sub_taylor_le`).
* **An FE pair flattens zeta on the line** (`norm_zeta_center_le_of_offline_zero`). For a zero `ρ`
  of the strip with `|γ| ≥ 3` and `|β − ½| ≤ 1/16`,
  `|ζ(½ + iγ)| ≤ 480 e² (|γ| + 2)(|γ| + 5) (β − ½)²`.
* **A depth gap from the line** (`depth_ge_of_norm_zeta_center_ge`). If `|ζ(½ + iγ)| ≥ c` then
  `|β − ½| ≥ min(1/16, √(c / (480 e² (|γ| + 2)(|γ| + 5))))`.

* **An interval of flatness** (`norm_zeta_line_le_of_offline_zero`). If `0 < |β − ½| ≤ η ≤ 1/16`,
  then `|ζ(½ + it)| ≤ 1280 e² (|γ| + 2)(|γ| + 5) η²` for all `|t − γ| ≤ η`.
* **A depth gap from a small-value measure** (`depth_gt_of_small_value_measure`). If that sublevel
  set has measure `< 2η` in `[γ − η, γ + η]`, the zero is on the line or deeper than `η`.

* **The depth is at least the derivative** (`depth_ge_of_norm_deriv`).
  `|β − ½| ≥ min(1/16, |ζ'(ρ)| / (320 e² (|γ| + 2)(|γ| + 5)))` for an off-line zero.

So off-line zeros of small depth sit exactly where `|ζ(½ + it)|` is quadratically small on a whole
interval, and a lower bound for `|ζ|` on the line, or a measure bound for its small values, is a
depth gap.
-/

open Complex Metric

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- **Two symmetric zeros flatten the centre.** -/
theorem norm_le_of_two_symmetric_zeros {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c h : ℂ} {R M : ℝ} (hR : 0 < R)
    (hsub : closedBall c (2 * R) ⊆ U) (hM : ∀ z ∈ closedBall c (2 * R), ‖f z‖ ≤ M)
    (hh : ‖h‖ ≤ R / 8) (h1 : f (c - h) = 0) (h2 : f (c + h) = 0) :
    ‖f c‖ ≤ 24 * M / R ^ 2 * ‖h‖ ^ 2 := by
  have hball : closedBall (c - h) R ⊆ closedBall c (2 * R) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - c‖ = ‖(w - (c - h)) - h‖ := by ring_nf
      _ ≤ ‖w - (c - h)‖ + ‖h‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hM' : ∀ z ∈ closedBall (c - h) R, ‖f z‖ ≤ M := fun z hz => hM z (hball hz)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_closedBall_self (by linarith)))
  have hK : 0 ≤ 8 * M / R ^ 2 := by positivity
  by_cases h0 : h = 0
  · subst h0; simp at h1; rw [h1, norm_zero]; positivity
  have hhpos : 0 < ‖h‖ := norm_pos_iff.mpr h0
  -- the derivative at `c − h`
  have hdist : ‖(c + h) - (c - h)‖ = 2 * ‖h‖ := by
    rw [show (c + h) - (c - h) = 2 * h by ring, norm_mul]; norm_num
  have hder := norm_deriv_mul_le_of_two_zeros hU hf hR (hball.trans hsub) hM'
    (by rw [hdist]; linarith) h1 h2
  rw [hdist] at hder
  have hder' : ‖deriv f (c - h)‖ ≤ 8 * M / R ^ 2 * (2 * ‖h‖) := by
    have h2h : 0 < 2 * ‖h‖ := by positivity
    have h3 : ‖deriv f (c - h)‖ * (2 * ‖h‖) ≤ (8 * M / R ^ 2 * (2 * ‖h‖)) * (2 * ‖h‖) := by
      calc _ ≤ 8 * M / R ^ 2 * (2 * ‖h‖) ^ 2 := hder
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 h2h
  -- the Taylor remainder from `c − h` to `c`
  have hca : ‖c - (c - h)‖ = ‖h‖ := by rw [sub_sub_cancel]
  have htay := norm_sub_taylor_le hU hf hR (hball.trans hsub) hM' (by rw [hca]; linarith)
  rw [hca, h1, sub_zero, sub_sub_cancel] at htay
  calc ‖f c‖ = ‖(f c - deriv f (c - h) * h) + deriv f (c - h) * h‖ := by ring_nf
    _ ≤ ‖f c - deriv f (c - h) * h‖ + ‖deriv f (c - h)‖ * ‖h‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ 8 * M / R ^ 2 * ‖h‖ ^ 2 + 8 * M / R ^ 2 * (2 * ‖h‖) * ‖h‖ :=
        add_le_add htay (mul_le_mul_of_nonneg_right hder' (norm_nonneg _))
    _ = 24 * M / R ^ 2 * ‖h‖ ^ 2 := by ring

/-- The zeta bound on the unit disc around a point of the critical line at height `≥ 3`. -/
theorem norm_riemannZeta_le_on_line_disc {γ : ℝ} (hγ : 3 ≤ |γ|) :
    ∀ z ∈ closedBall ((1 / 2 : ℂ) + γ * I) 1,
      ‖riemannZeta z‖ ≤ 5 * Real.exp 2 * (|γ| + 2) * (|γ| + 5) := by
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := (abs_re_le_norm _).trans hz
  have him := (abs_im_le_norm _).trans hz
  simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
    mul_one, sub_im, add_im, mul_im, add_zero] at hre him
  norm_num at hre him
  have ht2 : 2 ≤ |z.im| := by
    have := abs_sub_abs_le_abs_sub γ z.im
    rw [abs_sub_comm] at this
    linarith
  have htle : |z.im| ≤ |γ| + 1 := by
    have := abs_sub_abs_le_abs_sub z.im γ
    linarith
  have hb := RHTower.norm_riemannZeta_le_smoothAFE_strip (σ := z.re) (t := z.im)
    (by linarith [(abs_le.mp hre).1]) (by linarith [(abs_le.mp hre).2]) ht2
  rw [re_add_im] at hb
  refine hb.trans ?_
  have he : 0 < 5 * Real.exp 2 := by positivity
  have h3 : (1 + |z.im|) * (4 + |z.im|) ≤ (|γ| + 2) * (|γ| + 5) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have h4 := mul_le_mul_of_nonneg_left h3 he.le
  linarith [h4, show 5 * Real.exp 2 * (1 + |z.im|) * (4 + |z.im|) =
    5 * Real.exp 2 * ((1 + |z.im|) * (4 + |z.im|)) by ring,
    show 5 * Real.exp 2 * (|γ| + 2) * (|γ| + 5) = 5 * Real.exp 2 * ((|γ| + 2) * (|γ| + 5)) by ring]

/-- **An FE pair flattens zeta on the line.** -/
theorem norm_zeta_center_le_of_offline_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hγ : 3 ≤ |ρ.im|) (hδ : |ρ.re - 1 / 2| ≤ 1 / 16) :
    ‖riemannZeta ((1 / 2 : ℂ) + ρ.im * I)‖ ≤
      480 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) * (ρ.re - 1 / 2) ^ 2 := by
  set c : ℂ := (1 / 2 : ℂ) + ρ.im * I with hc
  set h : ℂ := ((ρ.re - 1 / 2 : ℝ) : ℂ) with hh
  have hplus : c + h = ρ := by
    apply Complex.ext <;> simp [hc, hh]
  have hminus : c - h = 1 - (starRingEnd ℂ) ρ := by
    apply Complex.ext <;> simp [hc, hh]; ring
  have hpartner : riemannZeta (c - h) = 0 := by
    rw [hminus, show (1 : ℂ) - (starRingEnd ℂ) ρ = (starRingEnd ℂ) (1 - ρ) by simp,
      riemannZeta_conj, RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hρ h0 h1, map_zero]
  set U : Set ℂ := {s | s ≠ 1} with hU
  have hfU : DifferentiableOn ℂ riemannZeta U := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hsub : closedBall c (2 * (1 / 2)) ⊆ U := by
    intro z hz h1'
    rw [mem_closedBall, dist_eq_norm] at hz
    have him := (abs_im_le_norm (z - c)).trans hz
    rw [sub_im, h1', one_im, hc] at him
    simp at him
    linarith
  have hhn : ‖h‖ = |ρ.re - 1 / 2| := by rw [hh, norm_real, Real.norm_eq_abs]
  have hbound := norm_riemannZeta_le_on_line_disc (γ := ρ.im) hγ
  have key := norm_le_of_two_symmetric_zeros isOpen_ne hfU (by norm_num : (0 : ℝ) < 1 / 2) hsub
    (fun z hz => hbound z (by rw [← hc]; simpa using hz)) (by rw [hhn]; linarith) hpartner
    (by rw [hplus]; exact hρ)
  rw [hhn, sq_abs] at key
  calc ‖riemannZeta c‖ ≤ 24 * (5 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5)) / (1 / 2) ^ 2 *
        (ρ.re - 1 / 2) ^ 2 := key
    _ = 480 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) * (ρ.re - 1 / 2) ^ 2 := by ring

/-- **A depth gap from the line.** If `|ζ(½ + iγ)| ≥ c` at the ordinate of a zero `ρ` of the strip
with `|γ| ≥ 3`, then `|β − ½| ≥ min(1/16, √(c / (480 e² (|γ| + 2)(|γ| + 5))))`. -/
theorem depth_ge_of_norm_zeta_center_ge {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hγ : 3 ≤ |ρ.im|) {c : ℝ}
    (hc : c ≤ ‖riemannZeta ((1 / 2 : ℂ) + ρ.im * I)‖) :
    min (1 / 16) (Real.sqrt (c / (480 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5)))) ≤
      |ρ.re - 1 / 2| := by
  by_cases hfar : 1 / 16 < |ρ.re - 1 / 2|
  · exact (min_le_left _ _).trans hfar.le
  push Not at hfar
  have hK : 0 < 480 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) := by positivity
  have h := norm_zeta_center_le_of_offline_zero hρ h0 h1 hγ hfar
  refine (min_le_right _ _).trans ?_
  rw [← Real.sqrt_sq (abs_nonneg (ρ.re - 1 / 2)), sq_abs]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_iff₀ hK]
  linarith

/-! ### The depth from a small-value measure -/

/-- **An FE pair flattens zeta on a whole interval of the line.** For an off-line zero `ρ` of the
strip with `|γ| ≥ 3` and `0 < |β − ½| ≤ η ≤ 1/16`, every `|u| ≤ η` has
`|ζ(½ + i(γ + u))| ≤ 1280 e² (|γ| + 2)(|γ| + 5) η²`. (For an on-line simple zero the flatness is
only linear in `u`.) -/
theorem norm_zeta_line_le_of_offline_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hoff : ρ.re ≠ 1 / 2) (hγ : 3 ≤ |ρ.im|) {η : ℝ}
    (hδη : |ρ.re - 1 / 2| ≤ η) (hη : η ≤ 1 / 16) {u : ℝ} (hu : |u| ≤ η) :
    ‖riemannZeta ((1 / 2 : ℂ) + (ρ.im + u) * I)‖ ≤
      1280 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) * η ^ 2 := by
  set c : ℂ := (1 / 2 : ℂ) + ρ.im * I with hc
  set h : ℂ := ((ρ.re - 1 / 2 : ℝ) : ℂ) with hh
  set M : ℝ := 5 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) with hM
  have hpartner : riemannZeta (c - h) = 0 := by
    have hminus : c - h = 1 - (starRingEnd ℂ) ρ := by
      apply Complex.ext <;> simp [hc, hh]; ring
    rw [hminus, show (1 : ℂ) - (starRingEnd ℂ) ρ = (starRingEnd ℂ) (1 - ρ) by simp,
      riemannZeta_conj, RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hρ h0 h1, map_zero]
  have hplus : c + h = ρ := by apply Complex.ext <;> simp [hc, hh]
  set U : Set ℂ := {s | s ≠ 1} with hU
  have hfU : DifferentiableOn ℂ riemannZeta U := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hbound := norm_riemannZeta_le_on_line_disc (γ := ρ.im) hγ
  have hhn : ‖h‖ = |ρ.re - 1 / 2| := by rw [hh, norm_real, Real.norm_eq_abs]
  have hball : closedBall (c - h) (1 / 2) ⊆ closedBall c 1 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - c‖ = ‖(w - (c - h)) - h‖ := by ring_nf
      _ ≤ ‖w - (c - h)‖ + ‖h‖ := norm_sub_le _ _
      _ ≤ 1 := by rw [hhn]; linarith
  have hsub : closedBall (c - h) (1 / 2) ⊆ U := by
    intro z hz h1'
    have hz' := hball hz
    rw [mem_closedBall, dist_eq_norm] at hz'
    have him := (abs_im_le_norm (z - c)).trans hz'
    rw [sub_im, h1', one_im, hc] at him
    simp at him
    linarith
  have hM' : ∀ z ∈ closedBall (c - h) (1 / 2), ‖riemannZeta z‖ ≤ M := fun z hz =>
    hbound z (by rw [← hc]; exact hball hz)
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  -- the derivative at the partner: `≤ 64 M |β − ½|`
  have hpair : ‖(c + h) - (c - h)‖ = 2 * |ρ.re - 1 / 2| := by
    rw [show (c + h) - (c - h) = 2 * h by ring, norm_mul, hhn]; norm_num
  have hpos : 0 < 2 * |ρ.re - 1 / 2| := by
    have : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
    linarith
  have hder' : ‖deriv riemannZeta (c - h)‖ ≤ 32 * M * (2 * η) := by
    have hd := norm_deriv_mul_le_of_two_zeros isOpen_ne hfU (by norm_num : (0 : ℝ) < 1 / 2)
      hsub hM' (by rw [hpair]; linarith) hpartner (by rw [hplus]; exact hρ)
    rw [hpair] at hd
    have h3 : ‖deriv riemannZeta (c - h)‖ * (2 * |ρ.re - 1 / 2|) ≤
        (32 * M * (2 * |ρ.re - 1 / 2|)) * (2 * |ρ.re - 1 / 2|) := by
      calc _ ≤ 8 * M / (1 / 2) ^ 2 * (2 * |ρ.re - 1 / 2|) ^ 2 := hd
        _ = _ := by ring
    have := le_of_mul_le_mul_right h3 hpos
    exact this.trans (by nlinarith)
  -- Taylor from `c − h` to `c + iu`
  set b : ℂ := c + (u : ℂ) * I with hbdef
  have hbeq : (1 / 2 : ℂ) + (ρ.im + u) * I = b := by rw [hbdef, hc]; ring
  have hba : ‖b - (c - h)‖ ≤ 2 * η := by
    rw [show b - (c - h) = h + (u : ℂ) * I by rw [hbdef]; ring]
    calc ‖h + (u : ℂ) * I‖ ≤ ‖h‖ + ‖(u : ℂ) * I‖ := norm_add_le _ _
      _ = |ρ.re - 1 / 2| + |u| := by rw [hhn, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
      _ ≤ 2 * η := by linarith
  have htay := norm_sub_taylor_le isOpen_ne hfU (by norm_num : (0 : ℝ) < 1 / 2) hsub hM'
    (b := b) (by linarith)
  rw [hpartner, sub_zero] at htay
  rw [hbeq]
  have hη0 : 0 ≤ η := (abs_nonneg _).trans hδη
  calc ‖riemannZeta b‖ = ‖(riemannZeta b - deriv riemannZeta (c - h) * (b - (c - h))) +
        deriv riemannZeta (c - h) * (b - (c - h))‖ := by ring_nf
    _ ≤ ‖riemannZeta b - deriv riemannZeta (c - h) * (b - (c - h))‖ +
        ‖deriv riemannZeta (c - h)‖ * ‖b - (c - h)‖ := by rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ 8 * M / (1 / 2) ^ 2 * (2 * η) ^ 2 + 32 * M * (2 * η) * (2 * η) := by
        refine add_le_add (htay.trans ?_) (mul_le_mul hder' hba (norm_nonneg _) (by positivity))
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hba 2) (by positivity)
    _ = 1280 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) * η ^ 2 := by rw [hM]; ring

/-- **A depth gap from a small-value measure.** For a zero `ρ` of the strip with `|γ| ≥ 3` and
`η ≤ 1/16`: if the set of `t ∈ [γ − η, γ + η]` with
`|ζ(½ + it)| ≤ 1280 e² (|γ| + 2)(|γ| + 5) η²` has measure `< 2η`, then `ρ` is on the line or
`|β − ½| > η`. -/
theorem depth_gt_of_small_value_measure {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hγ : 3 ≤ |ρ.im|) {η : ℝ} (hη : η ≤ 1 / 16)
    (hmeas : MeasureTheory.volume {t : ℝ | t ∈ Set.Icc (ρ.im - η) (ρ.im + η) ∧
        ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
          1280 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) * η ^ 2} < ENNReal.ofReal (2 * η)) :
    ρ.re = 1 / 2 ∨ η < |ρ.re - 1 / 2| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hoff, hδ⟩ := hcon
  have hset : Set.Icc (ρ.im - η) (ρ.im + η) ⊆ {t : ℝ | t ∈ Set.Icc (ρ.im - η) (ρ.im + η) ∧
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤
        1280 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) * η ^ 2} := by
    intro t ht
    refine ⟨ht, ?_⟩
    have hu : |t - ρ.im| ≤ η := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := norm_zeta_line_le_of_offline_zero hρ h0 h1 hoff hγ hδ hη hu
    rwa [show (ρ.im : ℂ) + ((t - ρ.im : ℝ) : ℂ) = t by push_cast; ring] at this
  have hvol := MeasureTheory.measure_mono (μ := MeasureTheory.volume) hset
  rw [Real.volume_Icc, show ρ.im + η - (ρ.im - η) = 2 * η by ring] at hvol
  exact absurd hmeas (not_lt.mpr hvol)

/-- **The depth is at least the derivative.** An off-line zero `ρ` of the strip with `|γ| ≥ 3` has
`|β − ½| ≥ min(1/16, |ζ'(ρ)| / (320 e² (|γ| + 2)(|γ| + 5)))`: its partner `1 − ρ̄` is a second zero
at distance `2|β − ½|` (`separation_of_norm_deriv_riemannZeta_ge`). -/
theorem depth_ge_of_norm_deriv {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hoff : ρ.re ≠ 1 / 2) (hγ : 3 ≤ |ρ.im|) :
    min (1 / 16) (‖deriv riemannZeta ρ‖ / (320 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5))) ≤
      |ρ.re - 1 / 2| := by
  set ρ' : ℂ := 1 - (starRingEnd ℂ) ρ with hρ'
  have hz' : riemannZeta ρ' = 0 := by
    rw [hρ', show (1 : ℂ) - (starRingEnd ℂ) ρ = (starRingEnd ℂ) (1 - ρ) by simp,
      riemannZeta_conj, RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hρ h0 h1, map_zero]
  have hdist : ‖ρ' - ρ‖ = 2 * |ρ.re - 1 / 2| := by
    have : ρ' - ρ = ((1 - 2 * ρ.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hρ']; ring
    rw [this, norm_real, Real.norm_eq_abs, show 1 - 2 * ρ.re = -(2 * (ρ.re - 1 / 2)) by ring,
      abs_neg, abs_mul, abs_two]
  have hne : ρ' ≠ ρ := by
    intro h
    have : ‖ρ' - ρ‖ = 0 := by rw [h, sub_self, norm_zero]
    rw [hdist] at this
    exact hoff (by have := abs_eq_zero.mp (by linarith : |ρ.re - 1 / 2| = 0); linarith)
  have h := separation_of_norm_deriv_riemannZeta_ge hρ hz' hne h0.le h1.le hγ le_rfl
  rw [hdist] at h
  have hK : 0 < 160 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) := by positivity
  have hsplit : min (1 / 16) (‖deriv riemannZeta ρ‖ /
      (320 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5))) =
      min (1 / 8) (‖deriv riemannZeta ρ‖ / (160 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5))) / 2 := by
    rw [← min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    · norm_num
    · rw [div_div]; ring_nf
  rw [hsplit]
  linarith

end GaloisForLFunctions.ArithmeticDiscreteness
