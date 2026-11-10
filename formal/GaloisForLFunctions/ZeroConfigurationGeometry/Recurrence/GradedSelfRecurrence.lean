import GaloisForLFunctions.ZeroConfigurationGeometry.Recurrence.GradedZeroCounts
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.RHTower.ZetaOrbitApproachesEveryAnalyticTargetWithTheHurwitzThreshold
import GaloisForLFunctions.RHTower.XiWindowZeroCount

/-!
# Graded self-recurrence excludes zeros

A sufficiently small self-return disc about a zero transports that zero by
Rouché. One-separated shifts produce distinct zero copies. The Guth–Maynard
count therefore bounds separated returns in the whole interval `[0,T]` by
every power strictly above `(30/13)(1−σ)`.
-/

open Complex Filter Topology Metric RHTower

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry.Recurrence

/-- A small disc within a prescribed strip has a positive zeta boundary floor. -/
theorem exists_small_zeta_disc {σ : ℝ} {ρ : ℂ} (hσρ : σ < ρ.re) (hρ1 : ρ.re < 1) :
    ∃ r > 0, r ≤ 1 / 4 ∧ (∀ s ∈ closedBall ρ r, σ < s.re ∧ s.re < 1) ∧
      ∃ m > 0, ∀ z ∈ sphere ρ r, m ≤ ‖riemannZeta z‖ := by
  have hne1 : ρ ≠ 1 := by intro h; rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
  have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have han : AnalyticAt ℂ riemannZeta ρ := hdiff.analyticAt (isOpen_ne.mem_nhds hne1)
  have hne : ¬ ∀ᶠ z in 𝓝 ρ, riemannZeta z = 0 := fun h =>
    analyticOrderAt_riemannZeta_ne_top_of_ne_one hne1 (analyticOrderAt_eq_top.mpr h)
  set δ : ℝ := min (1 / 4) (min ((ρ.re - σ) / 2) ((1 - ρ.re) / 2))
  have hδ : 0 < δ := lt_min (by norm_num)
    (lt_min (by linarith only [hσρ]) (by linarith only [hρ1]))
  obtain ⟨r, hr, hrδ, m, hm, hfloor⟩ :=
    exists_sphere_norm_ge_of_analyticAt_of_not_eventually_zero han hne hδ
  have hr4 : r ≤ 1 / 4 := hrδ.trans (min_le_left _ _)
  have hrσ : r ≤ (ρ.re - σ) / 2 :=
    hrδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr1 : r ≤ (1 - ρ.re) / 2 :=
    hrδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r, hr, hr4, ?_, m, hm, hfloor⟩
  intro s hs
  have habs := abs_le.mp ((abs_re_le_norm (s - ρ)).trans (mem_closedBall_iff_norm.mp hs))
  rw [sub_re] at habs
  constructor <;> linarith only [habs.1, habs.2, hrσ, hr1, hσρ, hρ1]

/-- Separated returns inject into a fixed low-height census and a cumulative tail census. -/
theorem card_separated_zeta_returns_le {σ r m T₀ T : ℝ} {ρ : ℂ}
    (hσ : 0 < σ) (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    (hstrip : ∀ s ∈ closedBall ρ r, σ < s.re ∧ s.re < 1)
    (hzero : riemannZeta ρ = 0) (hfloor : ∀ z ∈ sphere ρ r, m ≤ ‖riemannZeta z‖)
    (hT₀ : 1 ≤ T₀) (W : Finset ℝ)
    (hW : ∀ τ ∈ W, 0 ≤ τ ∧ τ ≤ T ∧ τ ∈ zetaReturnSet (closedBall ρ r) (m / 2))
    (hsep : ∀ τ ∈ W, ∀ υ ∈ W, τ ≠ υ → 1 ≤ |τ - υ|) :
    W.card ≤ (xiOrdinateWindow (T₀ + |ρ.im| + 1) 0).ncard +
      (zeroCopyRange σ T₀ (T + |ρ.im| + 1)).ncard := by
  classical
  have hchoose : ∀ τ ∈ W, ∃ q : XiZeroCopy,
      σ ≤ (q.1 : ℂ).re ∧ |(q.1 : ℂ).im - ρ.im - τ| < r := by
    intro τ hτ
    obtain ⟨z, hz, hz0⟩ := exists_zero_of_mem_zetaReturnSet hr
      (fun s hs => (hstrip s hs).2) hzero hfloor (hW τ hτ).2.2
    have hzstrip := hstrip z (ball_subset_closedBall hz)
    have hzre : (z + τ * I).re = z.re := by simp
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hz0
      (by rw [hzre]; exact hσ.trans hzstrip.1) (by rw [hzre]; exact hzstrip.2)
    refine ⟨q, ?_, ?_⟩
    · rw [hq, hzre]; exact hzstrip.1.le
    · have him := (abs_im_le_norm (z - ρ)).trans_lt (mem_ball_iff_norm.mp hz)
      rw [sub_im] at him
      simpa [hq, sub_sub] using him
  choose! q hq using hchoose
  have hinj : Set.InjOn q (W : Set ℝ) := by
    intro τ hτ υ hυ heq
    by_contra hne
    have hτim := abs_lt.mp (hq τ hτ).2
    have hυim := abs_lt.mp (hq υ hυ).2
    rw [← heq] at hυim
    have hdist : |τ - υ| < 1 := abs_lt.mpr
      ⟨by linarith only [hτim.2, hυim.1, hr4],
       by linarith only [hυim.2, hτim.1, hr4]⟩
    exact (not_lt_of_ge (hsep τ hτ υ hυ hne)) hdist
  let F₀ := (finite_xiOrdinateWindow (T₀ + |ρ.im| + 1) 0).toFinset
  have hT₀0 : 0 < T₀ := by linarith only [hT₀]
  let F₁ := (zeroCopyRange_finite σ T₀ (T + |ρ.im| + 1)
    hT₀0).toFinset
  have hsub : W.image q ⊆ F₀ ∪ F₁ := by
    intro v hv
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hτ0, hτT, _⟩ := hW τ hτ
    have him := abs_lt.mp (hq τ hτ).2
    by_cases hlo : T₀ ≤ ((q τ).1 : ℂ).im
    · apply Finset.mem_union.mpr; right
      change q τ ∈ (zeroCopyRange_finite σ T₀ (T + |ρ.im| + 1) hT₀0).toFinset
      rw [Set.Finite.mem_toFinset]
      exact ⟨(hq τ hτ).1, hlo, by linarith only [him.2, hτT, hr4, le_abs_self ρ.im]⟩
    · apply Finset.mem_union.mpr; left
      change q τ ∈ (finite_xiOrdinateWindow (T₀ + |ρ.im| + 1) 0).toFinset
      rw [Set.Finite.mem_toFinset, mem_xiOrdinateWindow_iff, sub_zero]
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith only [him.1, hτ0, hr4, hT₀, neg_abs_le ρ.im]
      · linarith only [not_le.mp hlo, abs_nonneg ρ.im]
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le F₀ F₁)
  rw [Finset.card_image_of_injOn hinj] at hcard
  simpa only [F₀, F₁, ← Set.ncard_eq_toFinset_card] using hcard

/-- At a zero, separated self-returns are eventually fewer than any power above
the Guth–Maynard density exponent. The interval starts at zero. -/
theorem exists_eventually_card_zeta_returns_lt_rpow {σ c : ℝ} {ρ : ℂ}
    (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 6) (hc : (30 / 13) * (1 - σ) < c)
    (hσρ : σ < ρ.re) (hρ1 : ρ.re < 1) (hzero : riemannZeta ρ = 0) :
    ∃ r > 0, (∀ s ∈ closedBall ρ r, σ < s.re ∧ s.re < 1) ∧ ∃ ε > 0,
      ∀ᶠ T : ℝ in atTop, ∀ W : Finset ℝ,
        (∀ τ ∈ W, 0 ≤ τ ∧ τ ≤ T ∧ τ ∈ zetaReturnSet (closedBall ρ r) ε) →
        (∀ τ ∈ W, ∀ υ ∈ W, τ ≠ υ → 1 ≤ |τ - υ|) → (W.card : ℝ) < T ^ c := by
  obtain ⟨r, hr, hr4, hstrip, m, hm, hfloor⟩ := exists_small_zeta_disc hσρ hρ1
  refine ⟨r, hr, hstrip, m / 2, by positivity, ?_⟩
  set a : ℝ := (30 / 13) * (1 - σ)
  change a < c at hc
  set d : ℝ := (a + c) / 2
  have had : a < d := by dsimp [d]; linarith only [hc]
  have hdc : d < c := by dsimp [d]; linarith only [hc]
  have hd0 : 0 ≤ d := by
    have ha0 : 0 ≤ a := by dsimp [a]; linarith only [hσ1]
    exact ha0.trans had.le
  obtain ⟨T₀, hT₀, hcount⟩ := exists_zeroCopyRange_le_rpow_guthMaynard hσ0 hσ1 had
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hcount
  set L : ℝ := ((xiOrdinateWindow (T₀ + |ρ.im| + 1) 0).ncard : ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hmargin := (tendsto_rpow_atTop (sub_pos.mpr hdc)).eventually_gt_atTop (L + 2 ^ d)
  filter_upwards [hmargin, eventually_ge_atTop Y₀, eventually_ge_atTop (|ρ.im| + 1)]
    with T hmarginT hTY hT
  intro W hW hsep
  have hT1 : 1 ≤ T := by linarith only [hT, abs_nonneg ρ.im]
  have hT0 : 0 < T := by linarith only [hT1]
  have hTd : 1 ≤ T ^ d := Real.one_le_rpow hT1 hd0
  have hY : Y₀ ≤ T + |ρ.im| + 1 := by linarith only [hTY, abs_nonneg ρ.im]
  have hYbound : (T + |ρ.im| + 1) ^ d ≤ (2 * T) ^ d := by gcongr; linarith only [hT]
  have hWcount := card_separated_zeta_returns_le
    (show 0 < σ by linarith only [hσ0]) hr hr4 hstrip hzero hfloor hT₀ W hW hsep
  calc (W.card : ℝ) ≤ L + ((zeroCopyRange σ T₀ (T + |ρ.im| + 1)).ncard : ℝ) :=
      by dsimp only [L]; exact_mod_cast hWcount
    _ ≤ L + (T + |ρ.im| + 1) ^ d := by linarith only [hY₀ _ hY]
    _ ≤ L + (2 * T) ^ d := by linarith only [hYbound]
    _ ≤ (L + 2 ^ d) * T ^ d := by
      rw [Real.mul_rpow (by norm_num) hT0.le]
      nlinarith only [mul_le_mul_of_nonneg_left hTd hL]
    _ < T ^ (c - d) * T ^ d := mul_lt_mul_of_pos_right hmarginT (Real.rpow_pos_of_pos hT0 _)
    _ = T ^ c := by rw [← Real.rpow_add hT0]; congr 1; ring

/-- Frequent power-many separated self-returns exclude a zero at the disc centre. -/
theorem zeta_ne_zero_of_graded_disc_returns {σ c : ℝ} {ρ : ℂ}
    (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 6) (hc : (30 / 13) * (1 - σ) < c)
    (hσρ : σ < ρ.re) (hρ1 : ρ.re < 1)
    (hreturns : ∀ r > 0, (∀ s ∈ closedBall ρ r, σ < s.re ∧ s.re < 1) → ∀ ε > 0,
      ∃ᶠ T : ℝ in atTop, ∃ W : Finset ℝ,
        (∀ τ ∈ W, 0 ≤ τ ∧ τ ≤ T ∧ τ ∈ zetaReturnSet (closedBall ρ r) ε) ∧
        (∀ τ ∈ W, ∀ υ ∈ W, τ ≠ υ → 1 ≤ |τ - υ|) ∧ T ^ c ≤ (W.card : ℝ)) :
    riemannZeta ρ ≠ 0 := by
  intro hzero
  obtain ⟨r, hr, hstrip, ε, hε, hbound⟩ :=
    exists_eventually_card_zeta_returns_lt_rpow hσ0 hσ1 hc hσρ hρ1 hzero
  obtain ⟨T, ⟨W, hW, hsep, hcard⟩, hT⟩ :=
    ((hreturns r hr hstrip ε hε).and_eventually hbound).exists
  exact (not_lt_of_ge hcard) (hT W hW hsep)

#print axioms exists_eventually_card_zeta_returns_lt_rpow
#print axioms zeta_ne_zero_of_graded_disc_returns

end GaloisForLFunctions.ZeroConfigurationGeometry.Recurrence
