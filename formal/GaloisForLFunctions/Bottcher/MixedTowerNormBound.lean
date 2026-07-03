/-
# The mixed-tower norm bound from Green band-avoidance (task B8)

The mixed q62 capstone `q62_phiMero_mixed_of_normBoundedTower` consumes a `c₁` radical tower whose
extension domain stays in `{2 < ‖z‖}` (so `bottcherCoord c₂` extends single-valued there).  That
norm bound is NOT derivable from the tower's Green control alone: the tower's non-section pieces
satisfy only `G_c(z) < 2·G_c(0)`, and the deep lobes descend through the Green band `G_c(0) ± 1/8`
that `closedBall 0 2` occupies (the pinch `abs_greenFunctionDyn_sub_crit_le`).

The route here is **Green band-avoidance**.  Every tower point reaches the section image in `j`
iterates (`hreach`), and `G_c(f_c^{[j]} z) = 2ʲ·G_c(z)` while the section image has Green value
`log‖w‖ ∈ (log rlo, log R₀)`; hence `G_c(z) ∈ (log rlo/2ʲ, log R₀/2ʲ)` — a *scaled band*.  If the
section annulus `(rlo, R₀)` is chosen so that no scaled band `(log rlo/2ʲ, log R₀/2ʲ)` meets the
pinch band `[G_c(0) − 1/8, G_c(0) + 1/8]`, then every tower point is Green-far from `G_c(0)`, so
`2 < ‖z‖` by the pinch contrapositives `two_lt_norm_of_greenFunctionDyn_gt/_lt`.

* `two_lt_norm_of_tower_bandAvoid` — the reduction: tower reach + band-avoidance ⟹ `∀ z ∈ Ext, 2 < ‖z‖`.

This reduces the tower norm bound (hence the whole mixed case, via the capstone) to the numeric
band-avoidance condition on the section annulus — achievable for `‖c‖ ≥ 100`, where the gaps between
consecutive geometric bands have width `≈ G_c(0)/2 ≫ 1/4`, so `G_c(0)` can be placed `1/8`-clear in a
gap by choosing `log rlo`.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.GreenBallPinch
import GaloisForLFunctions.Bottcher.GreenSublevel
import GaloisForLFunctions.Bottcher.SectionTower
import GaloisForLFunctions.Bottcher.AnnulusRoot

open Set
open scoped Topology

namespace Bottcher

/-- **Tower norm bound from Green band-avoidance.**  For `‖c‖ ≥ 100`, if every point of a tower
domain `Ext` reaches the section image `S.T '' annulusSet rlo R₀` within `k` iterates, and if every
scaled Green band `(log rlo / 2ʲ, log R₀ / 2ʲ)` avoids the pinch band `[G_c(0) − 1/8, G_c(0) + 1/8]`,
then every point of `Ext` has norm `> 2` (avoids `closedBall 0 2 ⊇ K_{c₂}` for connected `c₂`).  This
discharges the mixed-tower norm bound from a numeric condition on the section annulus. -/
theorem two_lt_norm_of_tower_bandAvoid
    {c : ℂ} (hc : (100:ℝ) ≤ ‖c‖) {rlo R₀ : ℝ} (hrlo : 1 < rlo)
    (S : TowerSection c rlo R₀) {Ext : Set ℂ} {k : ℕ}
    (hreach : ∀ z ∈ Ext, ∃ j : ℕ, j ≤ k ∧ (quadratic c)^[j] z ∈ S.T '' annulusSet rlo R₀)
    (hband : ∀ j : ℕ, Real.log R₀ / (2:ℝ)^j ≤ greenFunctionDyn c 0 - 1/8
                    ∨ greenFunctionDyn c 0 + 1/8 ≤ Real.log rlo / (2:ℝ)^j) :
    ∀ z ∈ Ext, 2 < ‖z‖ := by
  intro z hz
  obtain ⟨j, _hjk, w, hw, hwT⟩ := hreach z hz
  obtain ⟨hwlo, hwhi⟩ := hw
  have h2jpos : (0:ℝ) < (2:ℝ)^j := by positivity
  have hwpos : (0:ℝ) < ‖w‖ := lt_trans (by linarith) hwlo
  have hgj : greenFunctionDyn c ((quadratic c)^[j] z) = Real.log ‖w‖ := by
    rw [← hwT]; exact S.level w ⟨hwlo, hwhi⟩
  have hit : greenFunctionDyn c ((quadratic c)^[j] z) = (2:ℝ)^j * greenFunctionDyn c z :=
    greenFunctionDyn_iterate c z j
  have hgz : greenFunctionDyn c z = Real.log ‖w‖ / (2:ℝ)^j := by
    rw [eq_div_iff (ne_of_gt h2jpos)]
    have : (2:ℝ)^j * greenFunctionDyn c z = Real.log ‖w‖ := hit ▸ hgj
    linarith
  rcases hband j with hb | hb
  · apply two_lt_norm_of_greenFunctionDyn_lt hc
    rw [hgz]
    have hlogw : Real.log ‖w‖ < Real.log R₀ := Real.log_lt_log hwpos hwhi
    have : Real.log ‖w‖ / (2:ℝ)^j < Real.log R₀ / (2:ℝ)^j :=
      (div_lt_div_iff_of_pos_right h2jpos).mpr hlogw
    linarith
  · apply two_lt_norm_of_greenFunctionDyn_gt hc
    rw [hgz]
    have hlogw : Real.log rlo < Real.log ‖w‖ :=
      Real.log_lt_log (lt_trans one_pos hrlo) hwlo
    have : Real.log rlo / (2:ℝ)^j < Real.log ‖w‖ / (2:ℝ)^j :=
      (div_lt_div_iff_of_pos_right h2jpos).mpr hlogw
    linarith

end Bottcher

namespace Bottcher

/-- **Preimage norm from separation.**  If `f_c(z) = w` and `‖w − c‖ > 4`, then `2 < ‖z‖`
(`‖z‖² = ‖z²‖ = ‖w − c‖ > 4`).  The clean preimage step of the mixed-tower norm floor: an outer
`f_c`-preimage of a point separated from `c` stays outside `closedBall 0 2`. -/
theorem two_lt_norm_of_quadratic_eq {c z w : ℂ} (hzw : quadratic c z = w)
    (hsep : 4 < ‖w - c‖) : 2 < ‖z‖ := by
  have hz2 : z ^ 2 = w - c := by
    have : quadratic c z = z ^ 2 + c := by rw [quadratic_apply]
    rw [this] at hzw; linear_combination hzw
  have hnz2 : ‖z‖ ^ 2 = ‖w - c‖ := by rw [← hz2, norm_pow]
  nlinarith [norm_nonneg z, hnz2, hsep]

/-- **Separation from a radial gap (outer side).**  `‖c‖ + 4 < ‖w‖ ⟹ 4 < ‖w − c‖` (reverse
triangle): a tower point beyond `‖c‖ + 4` yields preimages of norm `> 2`. -/
theorem four_lt_norm_sub_of_gt {c w : ℂ} (h : ‖c‖ + 4 < ‖w‖) : 4 < ‖w - c‖ := by
  have h1 : ‖w‖ - ‖c‖ ≤ ‖w - c‖ := by have := norm_sub_norm_le w c; linarith
  linarith

/-- **Separation from a radial gap (inner side).**  `‖w‖ + 4 < ‖c‖ ⟹ 4 < ‖w − c‖`. -/
theorem four_lt_norm_sub_of_lt {c w : ℂ} (h : ‖w‖ + 4 < ‖c‖) : 4 < ‖w - c‖ := by
  have h1 : ‖c‖ - ‖w‖ ≤ ‖w - c‖ := by
    rw [norm_sub_rev]; have := norm_sub_norm_le c w; linarith
  linarith

end Bottcher

namespace Bottcher

/-- **Escape growth from `closedBall 0 2`.**  For `‖c‖ ≥ 100`, two iterates of a norm-`≤ 2` point
land past `9000`: `‖f_c(z)‖ ≥ ‖c‖ − ‖z‖² ≥ 96`, then `‖f_c²(z)‖ ≥ ‖f_c(z)‖² − ‖c‖ ≥ 96² − ‖c‖`.
So a norm-`≤ 2` tower point cannot reach the bounded section (radius `< e^{4·G_c(0)} ≈ ‖c‖²`) in
`≥ 3` iterates — the deep tower pieces are `> 2` automatically, reducing the residual `#131` norm
bound to the shallow `j ∈ {1,2}` pieces near the section. -/
theorem norm_iterate_two_ge_of_norm_le_two {c z : ℂ} (hc : (100:ℝ) ≤ ‖c‖) (hz : ‖z‖ ≤ 2) :
    9000 ≤ ‖(quadratic c)^[2] z‖ := by
  have hz2 : ‖z‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg z]
  have hw1 : ‖c‖ - 4 ≤ ‖quadratic c z‖ := by
    have heq : quadratic c z = z ^ 2 + c := by rw [quadratic_apply]
    have h1 : ‖c‖ ≤ ‖quadratic c z‖ + ‖z‖ ^ 2 := by
      calc ‖c‖ = ‖(z ^ 2 + c) - z ^ 2‖ := by rw [show (z ^ 2 + c) - z ^ 2 = c by ring]
        _ ≤ ‖z ^ 2 + c‖ + ‖z ^ 2‖ := norm_sub_le _ _
        _ = ‖quadratic c z‖ + ‖z‖ ^ 2 := by rw [← heq, norm_pow]
    nlinarith [h1, hz2]
  have hw1nn : (0:ℝ) ≤ ‖c‖ - 4 := by linarith
  have hw1sq : (‖c‖ - 4) ^ 2 ≤ ‖quadratic c z‖ ^ 2 := by nlinarith [hw1, hw1nn]
  have hiter : (quadratic c)^[2] z = quadratic c (quadratic c z) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; rfl
  rw [hiter]
  have heq2 : quadratic c (quadratic c z) = (quadratic c z) ^ 2 + c := by rw [quadratic_apply]
  have h2 : ‖quadratic c z‖ ^ 2 ≤ ‖quadratic c (quadratic c z)‖ + ‖c‖ := by
    calc ‖quadratic c z‖ ^ 2 = ‖(quadratic c z) ^ 2‖ := (norm_pow _ _).symm
      _ = ‖((quadratic c z) ^ 2 + c) - c‖ := by rw [show ((quadratic c z) ^ 2 + c) - c
            = (quadratic c z) ^ 2 by ring]
      _ ≤ ‖(quadratic c z) ^ 2 + c‖ + ‖c‖ := norm_sub_le _ _
      _ = ‖quadratic c (quadratic c z)‖ + ‖c‖ := by rw [← heq2]
  nlinarith [h2, hw1sq, hc]

end Bottcher

namespace Bottcher

/-- **The preimage invariant `(2, ‖c‖−4)`.**  For `‖c‖ ≥ 100`, if `‖w‖ < ‖c‖ − 4` and `w'² = w − c`,
then `‖w'‖ ∈ (2, ‖c‖−4)`: `‖w'‖² = ‖w−c‖ ∈ (4, 2‖c‖−4)` and `2‖c‖−4 < (‖c‖−4)²`.  The band
`(2, ‖c‖−4)` is closed under `f_c`-preimages — no thin-annulus collapse.  Induction step of the
`#131` mixed-tower norm bound. -/
theorem norm_mem_Ioo_of_preimage {c w w' : ℂ} (hc : (100:ℝ) ≤ ‖c‖)
    (hhi : ‖w‖ < ‖c‖ - 4) (heq : w' ^ 2 = w - c) :
    2 < ‖w'‖ ∧ ‖w'‖ < ‖c‖ - 4 := by
  have hsep : 4 < ‖w - c‖ := four_lt_norm_sub_of_lt (by linarith)
  have hnw' : ‖w'‖ ^ 2 = ‖w - c‖ := by rw [← heq, norm_pow]
  have hub : ‖w - c‖ < 2 * ‖c‖ - 4 := by have := norm_sub_le w c; linarith
  exact ⟨by nlinarith [hnw', hsep, norm_nonneg w'],
    by nlinarith [hnw', hub, norm_nonneg w', hc]⟩

/-- **Section base step.**  The far section point (`‖c‖ + 4 < ‖w‖`, and `‖w − c‖ < (‖c‖−4)²` from
the far-field radius `R₀ < (‖c‖−4)²`) has its first `f_c`-preimage in the invariant band
`(2, ‖c‖−4)`.  From here `norm_mem_Ioo_of_preimage` carries the whole scaffold/lobe chain `> 2`. -/
theorem norm_mem_Ioo_of_preimage_of_far {c w w' : ℂ} (hc : (100:ℝ) ≤ ‖c‖)
    (hfar : ‖c‖ + 4 < ‖w‖) (hub : ‖w - c‖ < (‖c‖ - 4) ^ 2) (heq : w' ^ 2 = w - c) :
    2 < ‖w'‖ ∧ ‖w'‖ < ‖c‖ - 4 := by
  have hsep : 4 < ‖w - c‖ := four_lt_norm_sub_of_gt hfar
  have hnw' : ‖w'‖ ^ 2 = ‖w - c‖ := by rw [← heq, norm_pow]
  exact ⟨by nlinarith [hnw', hsep, norm_nonneg w'],
    by nlinarith [hnw', hub, norm_nonneg w', hc]⟩

end Bottcher

namespace Bottcher

/-- **Scaffold/lobe chain stays in the band `(2, ‖c‖−4)`.**  Given a preimage chain `σ`
(`σ(j+1)² = σj − c` on `A`) with a far section (`‖c‖+4 < ‖σ0 v‖`, `‖σ0 v − c‖ < (‖c‖−4)²`), every
generation `σ(j+1)` lies in `(2, ‖c‖−4)`.  Chains the `#131` base + step over the
`exists_matched_lobes`/`exists_scaffold_chain` families. -/
theorem preimageChain_norm_band {c : ℂ} (hc : (100:ℝ) ≤ ‖c‖) {A : Set ℂ} {σ : ℕ → ℂ → ℂ}
    (hfar : ∀ v ∈ A, ‖c‖ + 4 < ‖σ 0 v‖)
    (hub : ∀ v ∈ A, ‖σ 0 v - c‖ < (‖c‖ - 4) ^ 2)
    (hrec : ∀ j, ∀ v ∈ A, σ (j + 1) v ^ 2 = σ j v - c) :
    ∀ j : ℕ, ∀ v ∈ A, 2 < ‖σ (j + 1) v‖ ∧ ‖σ (j + 1) v‖ < ‖c‖ - 4 := by
  intro j
  induction j with
  | zero => intro v hv; exact norm_mem_Ioo_of_preimage_of_far hc (hfar v hv) (hub v hv) (hrec 0 v hv)
  | succ n ih => intro v hv; exact norm_mem_Ioo_of_preimage hc (ih v hv).2 (hrec (n + 1) v hv)

/-- **Every generation exceeds `2`.**  The far section and all its preimages avoid `closedBall 0 2`. -/
theorem preimageChain_two_lt {c : ℂ} (hc : (100:ℝ) ≤ ‖c‖) {A : Set ℂ} {σ : ℕ → ℂ → ℂ}
    (hfar : ∀ v ∈ A, ‖c‖ + 4 < ‖σ 0 v‖)
    (hub : ∀ v ∈ A, ‖σ 0 v - c‖ < (‖c‖ - 4) ^ 2)
    (hrec : ∀ j, ∀ v ∈ A, σ (j + 1) v ^ 2 = σ j v - c) :
    ∀ j : ℕ, ∀ v ∈ A, 2 < ‖σ j v‖ := by
  intro j v hv
  cases j with
  | zero => linarith [hfar v hv]
  | succ n => exact (preimageChain_norm_band hc hfar hub hrec n v hv).1

end Bottcher

namespace Bottcher

/-- **Escape is monotone past `9000`.**  For `‖c‖ ≤ 9000`, once an orbit reaches norm `≥ 9000` it
stays there: `‖f_c w‖ ≥ ‖w‖² − ‖c‖ ≥ 9000² − 9000 ≥ 9000`. -/
theorem le_norm_iterate_of_ge {c : ℂ} (hcU : ‖c‖ ≤ 9000) {w : ℂ} (hw : 9000 ≤ ‖w‖) (i : ℕ) :
    9000 ≤ ‖(quadratic c)^[i] w‖ := by
  induction i with
  | zero => simpa using hw
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have heq : quadratic c ((quadratic c)^[n] w) = ((quadratic c)^[n] w) ^ 2 + c := by
      rw [quadratic_apply]
    rw [heq]
    have h1 : ‖((quadratic c)^[n] w) ^ 2‖ ≤ ‖((quadratic c)^[n] w) ^ 2 + c‖ + ‖c‖ := by
      have := norm_sub_le (((quadratic c)^[n] w) ^ 2 + c) c
      rwa [show (((quadratic c)^[n] w) ^ 2 + c) - c = ((quadratic c)^[n] w) ^ 2 by ring] at this
    rw [norm_pow] at h1
    nlinarith [h1, ih, hcU]

/-- **Mixed-tower norm bound from reach + section bounds — the direct `#131` closure.**  For
`‖c‖ ≥ 100`, if the section image has norm in `(‖c‖+4, 9000)` and `z` reaches it in `j` iterates,
then `2 < ‖z‖`.  Proof by orbit growth, *no preimage-branch information*: `‖z‖ ≤ 2 ⟹ ‖f z‖ ≤ ‖c‖+4`
(kills `j=1`, since the section is `> ‖c‖+4`) and `‖f² z‖ ≥ 9000` with later iterates staying
`≥ 9000` (kills `j ≥ 2`, since the section is `< 9000`); `j=0` is `‖z‖ > ‖c‖+4`.  So the tower norm
bound needs only `exists_tower_ext`'s `hreach` plus the section's `Rinj`/`ψ≈id` bounds — no change to
the scaffold/lobe construction. -/
theorem two_lt_norm_of_reach {c : ℂ} (hc : (100:ℝ) ≤ ‖c‖) {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hsec_lo : ∀ w ∈ annulusSet rlo R₀, ‖c‖ + 4 < ‖S.T w‖)
    (hsec_hi : ∀ w ∈ annulusSet rlo R₀, ‖S.T w‖ < 9000)
    {z : ℂ} {k : ℕ}
    (hreach : ∃ j, j ≤ k ∧ (quadratic c)^[j] z ∈ S.T '' annulusSet rlo R₀) :
    2 < ‖z‖ := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨j, _hjk, w, hw, hwT⟩ := hreach
  have hlo := hsec_lo w hw
  have hhi := hsec_hi w hw
  have hcU : ‖c‖ ≤ 9000 := by linarith
  rcases j with _ | _ | m
  · simp only [Function.iterate_zero, id_eq] at hwT
    rw [hwT] at hlo; linarith
  · simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at hwT
    rw [hwT, quadratic_apply] at hlo
    have h1 : ‖z ^ 2 + c‖ ≤ ‖z ^ 2‖ + ‖c‖ := norm_add_le _ _
    rw [norm_pow] at h1
    nlinarith [h1, norm_nonneg z, hle, hlo]
  · have hf2 : (9000:ℝ) ≤ ‖(quadratic c)^[2] z‖ := norm_iterate_two_ge_of_norm_le_two hc hle
    have hsplit : (quadratic c)^[m + 1 + 1] z = (quadratic c)^[m] ((quadratic c)^[2] z) := by
      rw [show m + 1 + 1 = m + 2 from rfl]
      exact Function.iterate_add_apply (quadratic c) m 2 z
    rw [hsplit] at hwT
    have hge : (9000:ℝ) ≤ ‖(quadratic c)^[m] ((quadratic c)^[2] z)‖ :=
      le_norm_iterate_of_ge hcU hf2 m
    rw [← hwT] at hge; linarith

end Bottcher

namespace Bottcher

/-- **Sharp two-iterate escape.**  `‖c‖ ≥ 100 ∧ ‖z‖ ≤ 2 ⟹ (‖c‖−4)² − ‖c‖ ≤ ‖f²z‖` — the
`‖c‖`-scaled escape floor (the fixed `9000` version is the `‖c‖ = 100` special case). -/
theorem norm_iterate_two_ge_sharp {c z : ℂ} (hc : (100:ℝ) ≤ ‖c‖) (hz : ‖z‖ ≤ 2) :
    (‖c‖ - 4) ^ 2 - ‖c‖ ≤ ‖(quadratic c)^[2] z‖ := by
  have hz2 : ‖z‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg z]
  have hw1 : ‖c‖ - 4 ≤ ‖quadratic c z‖ := by
    have heq : quadratic c z = z ^ 2 + c := by rw [quadratic_apply]
    have h1 : ‖c‖ ≤ ‖quadratic c z‖ + ‖z‖ ^ 2 := by
      calc ‖c‖ = ‖(z ^ 2 + c) - z ^ 2‖ := by rw [show (z ^ 2 + c) - z ^ 2 = c by ring]
        _ ≤ ‖z ^ 2 + c‖ + ‖z ^ 2‖ := norm_sub_le _ _
        _ = ‖quadratic c z‖ + ‖z‖ ^ 2 := by rw [← heq, norm_pow]
    nlinarith [h1, hz2]
  have hw1nn : (0:ℝ) ≤ ‖c‖ - 4 := by linarith
  have hw1sq : (‖c‖ - 4) ^ 2 ≤ ‖quadratic c z‖ ^ 2 := by nlinarith [hw1, hw1nn]
  have hiter : (quadratic c)^[2] z = quadratic c (quadratic c z) := by
    rw [show (2:ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]; rfl
  rw [hiter]
  have heq2 : quadratic c (quadratic c z) = (quadratic c z) ^ 2 + c := by rw [quadratic_apply]
  have h2 : ‖quadratic c z‖ ^ 2 ≤ ‖quadratic c (quadratic c z)‖ + ‖c‖ := by
    calc ‖quadratic c z‖ ^ 2 = ‖(quadratic c z) ^ 2‖ := (norm_pow _ _).symm
      _ = ‖((quadratic c z) ^ 2 + c) - c‖ := by rw [show ((quadratic c z) ^ 2 + c) - c
            = (quadratic c z) ^ 2 by ring]
      _ ≤ ‖(quadratic c z) ^ 2 + c‖ + ‖c‖ := norm_sub_le _ _
      _ = ‖quadratic c (quadratic c z)‖ + ‖c‖ := by rw [← heq2]
  nlinarith [h2, hw1sq]

/-- **Escape monotone past a threshold** `T ≥ 2` with `‖c‖ ≤ T`. -/
theorem le_norm_iterate_of_ge_thresh {c : ℂ} {T : ℝ} (hT : 2 ≤ T) (hcT : ‖c‖ ≤ T)
    {w : ℂ} (hw : T ≤ ‖w‖) (i : ℕ) : T ≤ ‖(quadratic c)^[i] w‖ := by
  induction i with
  | zero => simpa using hw
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have heq : quadratic c ((quadratic c)^[n] w) = ((quadratic c)^[n] w) ^ 2 + c := by
      rw [quadratic_apply]
    rw [heq]
    have h1 : ‖((quadratic c)^[n] w) ^ 2‖ ≤ ‖((quadratic c)^[n] w) ^ 2 + c‖ + ‖c‖ := by
      have := norm_sub_le (((quadratic c)^[n] w) ^ 2 + c) c
      rwa [show (((quadratic c)^[n] w) ^ 2 + c) - c = ((quadratic c)^[n] w) ^ 2 by ring] at this
    rw [norm_pow] at h1
    nlinarith [h1, ih, hcT, hT]

/-- **Mixed-tower norm bound from reach — threshold form, all `‖c‖ ≥ 100`.**  If the section image is
confined to `(‖c‖+4, T)` with `‖c‖ ≤ T ≤ (‖c‖−4)² − ‖c‖`, a point reaching it has norm `> 2`. -/
theorem two_lt_norm_of_reach_thresh {c : ℂ} (hc : (100:ℝ) ≤ ‖c‖) {T : ℝ}
    (hcT : ‖c‖ ≤ T) (hTle : T ≤ (‖c‖ - 4) ^ 2 - ‖c‖)
    {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    (hsec_lo : ∀ w ∈ annulusSet rlo R₀, ‖c‖ + 4 < ‖S.T w‖)
    (hsec_hi : ∀ w ∈ annulusSet rlo R₀, ‖S.T w‖ < T)
    {z : ℂ} {k : ℕ}
    (hreach : ∃ j, j ≤ k ∧ (quadratic c)^[j] z ∈ S.T '' annulusSet rlo R₀) :
    2 < ‖z‖ := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨j, _hjk, w, hw, hwT⟩ := hreach
  have hlo := hsec_lo w hw
  have hhi := hsec_hi w hw
  have hTge2 : (2:ℝ) ≤ T := by linarith
  rcases j with _ | _ | m
  · simp only [Function.iterate_zero, id_eq] at hwT
    rw [hwT] at hlo; linarith
  · simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at hwT
    rw [hwT, quadratic_apply] at hlo
    have h1 : ‖z ^ 2 + c‖ ≤ ‖z ^ 2‖ + ‖c‖ := norm_add_le _ _
    rw [norm_pow] at h1
    nlinarith [h1, norm_nonneg z, hle, hlo]
  · have hf2 : T ≤ ‖(quadratic c)^[2] z‖ := le_trans hTle (norm_iterate_two_ge_sharp hc hle)
    have hsplit : (quadratic c)^[m + 1 + 1] z = (quadratic c)^[m] ((quadratic c)^[2] z) := by
      rw [show m + 1 + 1 = m + 2 from rfl]
      exact Function.iterate_add_apply (quadratic c) m 2 z
    rw [hsplit] at hwT
    have hge : T ≤ ‖(quadratic c)^[m] ((quadratic c)^[2] z)‖ :=
      le_norm_iterate_of_ge_thresh hTge2 hcT hf2 m
    rw [← hwT] at hge; linarith

end Bottcher
