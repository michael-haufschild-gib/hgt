/-
The seam cocycle (MWM lane, OC2 of 15-conservation-program.md — task #122).

The u-plane carrier (UPlaneDescent.lean): the critical line is the slit, and around an
on-seam point `a` the two open half-disks `overlapU`/`overlapD` are the two banks. A
root of `f` on a bank glues across the RIGHT seam segment against the chart root `G₁`
(analytic across it) with a constant ratio, and across the LEFT segment against `G₂`;
the two gluing constants are the SEAM CLASSES

  σ_R := (GU qP / G₁ qP) / (GD qM / G₁ qM),   σ_L := (GU qP / G₂ qP) / (GD qM / G₂ qM).

* `deckClass_basepoint_indep` — the deck class of chart roots is the same at every
  basepoint pair in `overlapU × overlapD` where `f` does not vanish.
* `seam_jump` — **the seam ledger**: crossing an on-seam zero of multiplicity `m`
  multiplies the seam class by `exp(2πi·m/n)`:  σ_L = exp(2πi·m/n)·σ_R. The identity is
  VALUE-LEVEL (only the four root values enter); the interpretation of σ as a gluing
  constant is supplied by `pow_root_ratio` on the preconnected banks.
* `xiDescent_seam_jump` — the instance on the actual descended completed zeta: at every
  point of the u-plane (on-slit points = on-line ξ-zeros), the seam class jumps by
  exp(2πi·ord/n).

Reading: the whole-plane tower obstruction of ξ splits as OFF-LINE deck classes (the
RH content, `xi_deckClass_eq_one_iff_ladder_dvd`) plus the SEAM LEDGER of on-line
multiplicities (present unconditionally) — this module is the second account.
-/
import GaloisForLFunctions.RHTower.UPlaneDescent

namespace RHTower

open Complex Metric Set

/-- The deck class of chart roots does not depend on the choice of basepoints in the
two overlap banks, as long as `f` does not vanish there. -/
theorem deckClass_basepoint_indep {f G₁ G₂ : ℂ → ℂ} {a : ℂ} {R : ℝ}
    {n : ℕ} (hn : 0 < n)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = f z)
    {qP qP' qM qM' : ℂ}
    (hqP : qP ∈ overlapU a R) (hqP' : qP' ∈ overlapU a R)
    (hqM : qM ∈ overlapD a R) (hqM' : qM' ∈ overlapD a R)
    (hfP : f qP ≠ 0) (hfP' : f qP' ≠ 0) (hfM : f qM ≠ 0) (hfM' : f qM' ≠ 0) :
    deckClass G₁ G₂ qP qM = deckClass G₁ G₂ qP' qM' := by
  have hUsub : overlapU a R ⊆ chartR a R ∩ chartL a R := by
    rw [chart_inter_eq]
    exact Set.subset_union_left
  have hDsub : overlapD a R ⊆ chartR a R ∩ chartL a R := by
    rw [chart_inter_eq]
    exact Set.subset_union_right
  obtain ⟨-, hEqU⟩ := pow_root_ratio hn (isOpen_overlapU a R) (isPreconnected_overlapU a R)
    (fun z hz => hG₁ z (hUsub hz).1) (fun z hz => hG₂ z (hUsub hz).2)
    (fun z hz => hpG₁ z (hUsub hz).1) (fun z hz => hpG₂ z (hUsub hz).2) hqP hfP
  obtain ⟨-, hEqD⟩ := pow_root_ratio hn (isOpen_overlapD a R) (isPreconnected_overlapD a R)
    (fun z hz => hG₁ z (hDsub hz).1) (fun z hz => hG₂ z (hDsub hz).2)
    (fun z hz => hpG₁ z (hDsub hz).1) (fun z hz => hpG₂ z (hDsub hz).2) hqM hfM
  have h1P : G₁ qP ≠ 0 :=
    fun h0 => hfP (by rw [← hpG₁ qP (hUsub hqP).1, h0, zero_pow hn.ne'])
  have h2P : G₂ qP ≠ 0 :=
    fun h0 => hfP (by rw [← hpG₂ qP (hUsub hqP).2, h0, zero_pow hn.ne'])
  have h1M : G₁ qM ≠ 0 :=
    fun h0 => hfM (by rw [← hpG₁ qM (hDsub hqM).1, h0, zero_pow hn.ne'])
  have h2M : G₂ qM ≠ 0 :=
    fun h0 => hfM (by rw [← hpG₂ qM (hDsub hqM).2, h0, zero_pow hn.ne'])
  have h2P' : G₂ qP' ≠ 0 :=
    fun h0 => hfP' (by rw [← hpG₂ qP' (hUsub hqP').2, h0, zero_pow hn.ne'])
  have h2M' : G₂ qM' ≠ 0 :=
    fun h0 => hfM' (by rw [← hpG₂ qM' (hDsub hqM').2, h0, zero_pow hn.ne'])
  have eP := hEqU hqP'
  have eM := hEqD hqM'
  simp only at eP eM
  rw [deckClass, deckClass, eP, eM]
  field_simp

/-- **The seam ledger.** Around an on-seam zero `f = (z−a)^m·h`, the left seam class of
any bank roots equals the right seam class times `exp(2πi·m/n)`:

  (GU qP / G₂ qP) / (GD qM / G₂ qM)
    = exp(2πi·m/n) · (GU qP / G₁ qP) / (GD qM / G₁ qM).

Crossing an on-seam zero multiplies the seam gluing constant by the zero's root of
unity. Value-level: only the root property AT the two basepoints enters. -/
theorem seam_jump {f h GU GD G₁ G₂ : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    {m n : ℕ} (hn : 0 < n)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (z - a) ^ m * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = f z)
    {qP qM : ℂ} (hqP : qP ∈ overlapU a R) (hqM : qM ∈ overlapD a R)
    (hpGU : GU qP ^ n = f qP) (hpGD : GD qM ^ n = f qM) :
    (GU qP / G₂ qP) / (GD qM / G₂ qM) =
      exp (2 * (Real.pi : ℂ) * I * (m : ℂ) / n) *
        ((GU qP / G₁ qP) / (GD qM / G₁ qM)) := by
  have hR2 : (0 : ℝ) < R / 2 := by positivity
  -- nonvanishing of f on the banks
  have hf_ne : ∀ q : ℂ, q ∈ ball a R → (q - a).im ≠ 0 → f q ≠ 0 := by
    intro q hq him
    rw [hfact q hq]
    refine mul_ne_zero (pow_ne_zero _ ?_) (hh0 q hq)
    intro h0
    rw [h0] at him
    simp at him
  have hfqP : f qP ≠ 0 := hf_ne qP hqP.2 (ne_of_gt hqP.1)
  have hfqM : f qM ≠ 0 := hf_ne qM hqM.2 (ne_of_lt hqM.1)
  -- the standard basepoints lie on the banks
  have hPsub : a + ((R / 2 : ℝ) : ℂ) * I - a = ((R / 2 : ℝ) : ℂ) * I := by ring
  have hMsub : a - ((R / 2 : ℝ) : ℂ) * I - a = -(((R / 2 : ℝ) : ℂ) * I) := by ring
  have hnormP : ‖a + ((R / 2 : ℝ) : ℂ) * I - a‖ = R / 2 := by
    rw [hPsub, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hR2]
  have hnormM : ‖a - ((R / 2 : ℝ) : ℂ) * I - a‖ = R / 2 := by
    rw [hMsub, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hR2]
  have hballP : a + ((R / 2 : ℝ) : ℂ) * I ∈ ball a R := by
    rw [mem_ball, Complex.dist_eq, hnormP]
    linarith
  have hballM : a - ((R / 2 : ℝ) : ℂ) * I ∈ ball a R := by
    rw [mem_ball, Complex.dist_eq, hnormM]
    linarith
  have himP : (a + ((R / 2 : ℝ) : ℂ) * I - a).im = R / 2 := by
    rw [hPsub]
    simp
  have himM : (a - ((R / 2 : ℝ) : ℂ) * I - a).im = -(R / 2) := by
    rw [hMsub]
    simp
  have hbP : a + ((R / 2 : ℝ) : ℂ) * I ∈ overlapU a R :=
    ⟨by rw [Set.mem_setOf_eq, himP]; exact hR2, hballP⟩
  have hbM : a - ((R / 2 : ℝ) : ℂ) * I ∈ overlapD a R :=
    ⟨by rw [Set.mem_setOf_eq, himM]; linarith, hballM⟩
  have hfbP : f (a + ((R / 2 : ℝ) : ℂ) * I) ≠ 0 :=
    hf_ne _ hballP (by rw [himP]; exact hR2.ne')
  have hfbM : f (a - ((R / 2 : ℝ) : ℂ) * I) ≠ 0 :=
    hf_ne _ hballM (by rw [himM]; simpa using hR2.ne')
  -- the deck class value at the given basepoints
  have hdeck : deckClass G₁ G₂ qP qM =
      exp (2 * (Real.pi : ℂ) * I * (m : ℂ) / n) := by
    rw [deckClass_basepoint_indep hn hG₁ hG₂ hpG₁ hpG₂ hqP hbP hqM hbM
      hfqP hfbP hfqM hfbM]
    exact deckClass_single_zero hR hn hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂
  -- chart memberships and nonvanishing of the four roots at the basepoints
  have hUsub : overlapU a R ⊆ chartR a R ∩ chartL a R := by
    rw [chart_inter_eq]
    exact Set.subset_union_left
  have hDsub : overlapD a R ⊆ chartR a R ∩ chartL a R := by
    rw [chart_inter_eq]
    exact Set.subset_union_right
  have hGUq : GU qP ≠ 0 := fun h0 => hfqP (by rw [← hpGU, h0, zero_pow hn.ne'])
  have hGDq : GD qM ≠ 0 := fun h0 => hfqM (by rw [← hpGD, h0, zero_pow hn.ne'])
  have hG₁P : G₁ qP ≠ 0 :=
    fun h0 => hfqP (by rw [← hpG₁ qP (hUsub hqP).1, h0, zero_pow hn.ne'])
  have hG₁M : G₁ qM ≠ 0 :=
    fun h0 => hfqM (by rw [← hpG₁ qM (hDsub hqM).1, h0, zero_pow hn.ne'])
  have hG₂P : G₂ qP ≠ 0 :=
    fun h0 => hfqP (by rw [← hpG₂ qP (hUsub hqP).2, h0, zero_pow hn.ne'])
  have hG₂M : G₂ qM ≠ 0 :=
    fun h0 => hfqM (by rw [← hpG₂ qM (hDsub hqM).2, h0, zero_pow hn.ne'])
  -- the algebra: σ_L / σ_R = deckClass G₁ G₂ qP qM
  rw [← hdeck, deckClass]
  field_simp

/-- xiDescent has finite vanishing order everywhere (witness: `xiDescent (9/4) ≠ 0`). -/
theorem xiDescent_orderAt_ne_top (w : ℂ) : analyticOrderAt xiDescent w ≠ ⊤ := by
  intro htop
  have hne : xiDescent ((9 : ℂ) / 4) ≠ 0 := by
    rw [show ((9 : ℂ) / 4) = ((2 : ℂ) - 1 / 2) ^ (2 : ℕ) from by norm_num, ← xi_eq_xiDescent]
    exact xi_two_ne_zero
  have hev0 : xiDescent =ᶠ[nhds w] (0 : ℂ → ℂ) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  exact hne
    (xiDescent_analyticOnNhd_univ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ w) hev0 (Set.mem_univ _))

/-- Around any point, xiDescent peels on a small ball with a nonvanishing cofactor. -/
theorem xiDescent_peel_ball (w₀ : ℂ) :
    ∃ R₀ > 0, ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball w₀ R₀) ∧
      (∀ z ∈ ball w₀ R₀, h z ≠ 0) ∧
      ∀ z ∈ ball w₀ R₀, xiDescent z =
        (z - w₀) ^ (analyticOrderAt xiDescent w₀).toNat * h z := by
  have hm : analyticOrderAt xiDescent w₀ =
      ((analyticOrderAt xiDescent w₀).toNat : ℕ∞) :=
    (ENat.coe_toNat (xiDescent_orderAt_ne_top w₀)).symm
  obtain ⟨h, hhan, hh0, hfact, -⟩ :=
    exists_peel isOpen_univ xiDescent_analyticOnNhd_univ (Set.mem_univ w₀) hm
  have hcont : ContinuousAt h w₀ := (hhan w₀ (Set.mem_univ w₀)).continuousAt
  have hev : ∀ᶠ z in nhds w₀, h z ≠ 0 := hcont.eventually_ne hh0
  obtain ⟨R₀, hR₀, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨R₀, hR₀, h, fun z _ => hhan z (Set.mem_univ z), ?_, ?_⟩
  · intro z hz
    exact hball (by rwa [mem_ball] at hz)
  · intro z _
    exact hfact z (Set.mem_univ z)

/-- **The seam ledger of the descended completed zeta.** Around any u-plane point
(on-slit points are the on-line ξ-zeros), the seam class of any bank roots of
`xiDescent` jumps by `exp(2πi·ord/n)` across the point. -/
theorem xiDescent_seam_jump (x₀ : ℂ) :
    ∃ R₀ > 0, ∀ {R : ℝ}, 0 < R → R ≤ R₀ → ∀ {n : ℕ}, 0 < n →
      ∀ {GU GD G₁ G₂ : ℂ → ℂ},
      AnalyticOnNhd ℂ G₁ (chartR x₀ R) → AnalyticOnNhd ℂ G₂ (chartL x₀ R) →
      (∀ z ∈ chartR x₀ R, G₁ z ^ n = xiDescent z) →
      (∀ z ∈ chartL x₀ R, G₂ z ^ n = xiDescent z) →
      ∀ {qP qM : ℂ}, qP ∈ overlapU x₀ R → qM ∈ overlapD x₀ R →
      GU qP ^ n = xiDescent qP → GD qM ^ n = xiDescent qM →
      (GU qP / G₂ qP) / (GD qM / G₂ qM) =
        exp (2 * (Real.pi : ℂ) * I *
            ((analyticOrderAt xiDescent x₀).toNat : ℂ) / n) *
          ((GU qP / G₁ qP) / (GD qM / G₁ qM)) := by
  obtain ⟨R₀, hR₀, h, hhan, hh0, hfact⟩ := xiDescent_peel_ball x₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR hRle n hn GU GD G₁ G₂ hG₁ hG₂ hpG₁ hpG₂ qP qM hqP hqM hpGU hpGD
  have hsub : ball x₀ R ⊆ ball x₀ R₀ := ball_subset_ball hRle
  exact seam_jump hR hn (fun z hz => hhan z (hsub hz)) (fun z hz => hh0 z (hsub hz))
    (fun z hz => hfact z (hsub hz)) hG₁ hG₂ hpG₁ hpG₂ hqP hqM hpGU hpGD

end RHTower
