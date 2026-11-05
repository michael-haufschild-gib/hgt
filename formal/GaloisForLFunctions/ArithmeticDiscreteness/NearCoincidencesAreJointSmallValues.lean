import GaloisForLFunctions.ArithmeticDiscreteness.TheDepthOfAnFEPairIsReadOnTheLine

/-!
# Near-coincidences are joint small values

Over `𝔽_q` a near-double root of an integral polynomial `P` is a point where `P` and `P'` are
simultaneously small, and integrality (the discriminant) bounds how small they can jointly be. The
same picture holds for `ζ` without integrality: every near-coincidence is a joint small value of
`(ζ, ζ')`.

* **Two zeros make `f` and `f'` small at their midpoint** (`norm_deriv_le_of_two_symmetric_zeros`).
  If `f` is holomorphic and bounded by `M` on `‖z − c‖ ≤ 2R` and vanishes at `c ± h`, `‖h‖ ≤ R/8`,
  then `‖f'(c)‖ ≤ (24M/R²)‖h‖`; together with `norm_le_of_two_symmetric_zeros`,
  `‖f(c)‖ ≤ (24M/R²)‖h‖²`.
* **For zeta** (`joint_small_values_of_close_zeros`). Two zeros `ρ ≠ ρ'` of `ζ` within `1/16` of
  each other, with midpoint `c` in the strip and `|Im c| ≥ 3`, give
  `|ζ(c)| ≤ K‖h‖²` and `|ζ'(c)| ≤ K‖h‖`, `h = (ρ' − ρ)/2`, `K = 1920 e² (|Im c|+2)(|Im c|+5)`.
  Contrapositively, if no point `c` of the strip has both `|ζ(c)| ≤ K‖h‖²` and `|ζ'(c)| ≤ K‖h‖`,
  no two zeros are at distance `2‖h‖`.

So collide-or-repel for `ζ` is the statement that `(ζ, ζ')` has no joint small values at the
corresponding scales; over `𝔽_q` integrality supplies this, over `ℤ` it is open.
-/

open Complex Metric

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- **Two zeros make the derivative small at their midpoint.** -/
theorem norm_deriv_le_of_two_symmetric_zeros {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {c h : ℂ} {R M : ℝ} (hR : 0 < R)
    (hsub : closedBall c (2 * R) ⊆ U) (hM : ∀ z ∈ closedBall c (2 * R), ‖f z‖ ≤ M)
    (hh : ‖h‖ ≤ R / 8) (hh0 : h ≠ 0) (h1 : f (c - h) = 0) (h2 : f (c + h) = 0) :
    ‖deriv f c‖ ≤ 24 * M / R ^ 2 * ‖h‖ := by
  have hball : closedBall (c - h) R ⊆ closedBall c (2 * R) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - c‖ = ‖(w - (c - h)) - h‖ := by ring_nf
      _ ≤ ‖w - (c - h)‖ + ‖h‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hM' : ∀ z ∈ closedBall (c - h) R, ‖f z‖ ≤ M := fun z hz => hM z (hball hz)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_closedBall_self (by linarith)))
  have hhpos : 0 < ‖h‖ := norm_pos_iff.mpr hh0
  -- the derivative at `c − h`
  have hdist : ‖(c + h) - (c - h)‖ = 2 * ‖h‖ := by
    rw [show (c + h) - (c - h) = 2 * h by ring, norm_mul]; norm_num
  have hder := norm_deriv_mul_le_of_two_zeros hU hf hR (hball.trans hsub) hM'
    (by rw [hdist]; linarith) h1 h2
  rw [hdist] at hder
  have hder' : ‖deriv f (c - h)‖ ≤ 16 * M / R ^ 2 * ‖h‖ := by
    have h2h : 0 < 2 * ‖h‖ := by positivity
    have h3 : ‖deriv f (c - h)‖ * (2 * ‖h‖) ≤ (16 * M / R ^ 2 * ‖h‖) * (2 * ‖h‖) := by
      calc _ ≤ 8 * M / R ^ 2 * (2 * ‖h‖) ^ 2 := hder
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 h2h
  -- the derivative moves by at most `(8M/R²)‖h‖` from `c − h` to `c`
  have hdd := norm_deriv_deriv_le hU hf hR (hball.trans hsub) hM'
  have hsmall : closedBall (c - h) (R / 4) ⊆ U :=
    ((closedBall_subset_closedBall (by linarith)).trans hball).trans hsub
  have hdiff : ∀ z ∈ closedBall (c - h) (R / 4), DifferentiableAt ℂ (deriv f) z := fun z hz =>
    (hf.deriv hU).differentiableAt (hU.mem_nhds (hsmall hz))
  have hcmem : c ∈ closedBall (c - h) (R / 4) := by
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel]; linarith
  have hmv := (convex_closedBall (c - h) (R / 4)).norm_image_sub_le_of_norm_deriv_le hdiff hdd
    (mem_closedBall_self (by positivity)) hcmem
  rw [sub_sub_cancel] at hmv
  calc ‖deriv f c‖ = ‖(deriv f c - deriv f (c - h)) + deriv f (c - h)‖ := by ring_nf
    _ ≤ ‖deriv f c - deriv f (c - h)‖ + ‖deriv f (c - h)‖ := norm_add_le _ _
    _ ≤ 8 * M / R ^ 2 * ‖h‖ + 16 * M / R ^ 2 * ‖h‖ := add_le_add hmv hder'
    _ = 24 * M / R ^ 2 * ‖h‖ := by ring

/-- **For zeta: close zeros are joint small values.** Two distinct zeros `ρ, ρ'` with
`‖ρ' − ρ‖ ≤ 1/16` whose midpoint `c` lies in the strip with `|Im c| ≥ 3` satisfy, with
`h = (ρ' − ρ)/2` and `K = 1920 e² (|Im c| + 2)(|Im c| + 5)`,
`|ζ(c)| ≤ K‖h‖²` and `|ζ'(c)| ≤ K‖h‖`. -/
theorem joint_small_values_of_close_zeros {ρ ρ' : ℂ} (hρ : riemannZeta ρ = 0)
    (hρ' : riemannZeta ρ' = 0) (hne : ρ ≠ ρ') (hclose : ‖ρ' - ρ‖ ≤ 1 / 16)
    (hre0 : 0 ≤ ((ρ + ρ') / 2).re) (hre1 : ((ρ + ρ') / 2).re ≤ 1)
    (hγ : 3 ≤ |((ρ + ρ') / 2).im|) :
    ‖riemannZeta ((ρ + ρ') / 2)‖ ≤
        1920 * Real.exp 2 * (|((ρ + ρ') / 2).im| + 2) * (|((ρ + ρ') / 2).im| + 5) *
          ‖(ρ' - ρ) / 2‖ ^ 2 ∧
      ‖deriv riemannZeta ((ρ + ρ') / 2)‖ ≤
        1920 * Real.exp 2 * (|((ρ + ρ') / 2).im| + 2) * (|((ρ + ρ') / 2).im| + 5) *
          ‖(ρ' - ρ) / 2‖ := by
  set c : ℂ := (ρ + ρ') / 2 with hc
  set h : ℂ := (ρ' - ρ) / 2 with hh
  have hcm : c - h = ρ := by rw [hc, hh]; ring
  have hcp : c + h = ρ' := by rw [hc, hh]; ring
  have hh0 : h ≠ 0 := by
    rw [hh]; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) two_ne_zero
  have hhn : ‖h‖ ≤ (1 / 4) / 8 := by
    rw [hh, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
  set U : Set ℂ := {s | s ≠ 1} with hU
  have hfU : DifferentiableOn ℂ riemannZeta U := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hsub : closedBall c (2 * (1 / 4)) ⊆ U := by
    intro z hz h1'
    rw [mem_closedBall, dist_eq_norm] at hz
    have him := (abs_im_le_norm (z - c)).trans hz
    rw [sub_im, h1', one_im] at him
    rw [abs_sub_comm] at him
    simp only [sub_zero] at him
    linarith
  have hbound : ∀ z ∈ closedBall c (2 * (1 / 4)), ‖riemannZeta z‖ ≤
      5 * Real.exp 2 * (|c.im| + 2) * (|c.im| + 5) := fun z hz =>
    norm_riemannZeta_le_on_disc hre0 hre1 hγ z (by
      rw [mem_closedBall] at hz ⊢; linarith)
  have h1 : riemannZeta (c - h) = 0 := by rw [hcm]; exact hρ
  have h2 : riemannZeta (c + h) = 0 := by rw [hcp]; exact hρ'
  have hv := norm_le_of_two_symmetric_zeros isOpen_ne hfU (by norm_num : (0 : ℝ) < 1 / 4) hsub
    hbound hhn h1 h2
  have hd := norm_deriv_le_of_two_symmetric_zeros isOpen_ne hfU (by norm_num : (0 : ℝ) < 1 / 4)
    hsub hbound hhn hh0 h1 h2
  constructor
  · calc ‖riemannZeta c‖ ≤ 24 * (5 * Real.exp 2 * (|c.im| + 2) * (|c.im| + 5)) / (1 / 4) ^ 2 *
          ‖h‖ ^ 2 := hv
      _ = 1920 * Real.exp 2 * (|c.im| + 2) * (|c.im| + 5) * ‖h‖ ^ 2 := by ring
  · calc ‖deriv riemannZeta c‖ ≤ 24 * (5 * Real.exp 2 * (|c.im| + 2) * (|c.im| + 5)) /
          (1 / 4) ^ 2 * ‖h‖ := hd
      _ = 1920 * Real.exp 2 * (|c.im| + 2) * (|c.im| + 5) * ‖h‖ := by ring

end GaloisForLFunctions.ArithmeticDiscreteness
