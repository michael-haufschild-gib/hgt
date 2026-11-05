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

So off-line zeros of small depth sit exactly where `|ζ(½ + it)|` has a small positive local
minimum, and a lower bound for `|ζ|` on the line at those ordinates is a depth gap.
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

end GaloisForLFunctions.ArithmeticDiscreteness
