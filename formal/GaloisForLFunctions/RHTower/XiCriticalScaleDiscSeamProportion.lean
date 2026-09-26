import GaloisForLFunctions.RHTower.XiZeroFreeRegionDiscSeamContraction
import GaloisForLFunctions.RHTower.LamzouriMontgomeryTaylorXiDensity

/-!
# Seam contraction on all but a third of the right discs next to the critical line

Fix `0 < r ≤ 1/8` and consider the closed discs of radius `r` centred at `1/2 + 2r + 3rk·i`,
`k = 1, …, K`.  They lie strictly right of the critical line (`Re ≥ 1/2 + r`), inside
`Re < 1`, and they are pairwise disjoint.  A disc containing a zero of `xi` contains an
*off-line* zero, and different discs contain different zeros.  Hence
(`card_badCriticalScaleDiscs_le_offLine`) the number of exceptional discs is at most the number
`O(T)` of off-line zeros with `0 < Im ρ ≤ T`.  That number is at most
`xiPosZeroCount T − xiSimpleCriticalZeroCount T` (`card_offLine_le`).

With the unconditional Montgomery–Taylor proportion of simple critical zeros
(`lamzouri_montgomeryTaylor_simpleCritical_epsilon`, `HD(1) ≈ 0.6725`), for every `ε > 0` and all
large `T` (`card_badCriticalScaleDiscs_le`):

`#{k ≤ K : the k-th disc contains a zero} ≤ (1 − HD(1) + ε) · N(T)`.

On every other disc the adjoint seam of the `xi` phase is a strict contraction.  At the
zero-spacing scale `r ≍ 1/log T` the family has `K ≍ T log T/(3r log T)` members, so a fixed
positive proportion of the discs adjacent to the critical line satisfies route 1's criterion.
-/

noncomputable section

open Complex Metric

namespace RHTower

/-- Centre of the `k`-th critical-scale disc. -/
def criticalScaleCenter (r : ℝ) (k : ℕ) : ℂ :=
  ((1 / 2 + 2 * r : ℝ) : ℂ) + ((3 * r * k : ℝ) : ℂ) * I

/-- The exceptional discs among the first `K`. -/
def badCriticalScaleDiscs (r : ℝ) (K : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 K).filter
    (fun k => ∃ z ∈ closedBall (criticalScaleCenter r k) r, xi z = 0)

/-- The off-line zeros with `0 < Im ρ ≤ T`. -/
def offLineZeroFinset (T : ℝ) : Finset ℂ := by
  classical
  exact (stripFinsetPos T).filter (fun z => z.re ≠ 1 / 2)

theorem re_im_of_mem_criticalScaleDisc {r : ℝ} {k : ℕ} {z : ℂ}
    (hz : z ∈ closedBall (criticalScaleCenter r k) r) :
    1 / 2 + r ≤ z.re ∧ z.re ≤ 1 / 2 + 3 * r ∧ 3 * r * k - r ≤ z.im ∧ z.im ≤ 3 * r * k + r := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h1 : |(z - criticalScaleCenter r k).re| ≤ ‖z - criticalScaleCenter r k‖ :=
    Complex.abs_re_le_norm _
  have h2 : |(z - criticalScaleCenter r k).im| ≤ ‖z - criticalScaleCenter r k‖ :=
    Complex.abs_im_le_norm _
  have hre : (criticalScaleCenter r k).re = 1 / 2 + 2 * r := by simp [criticalScaleCenter]
  have him : (criticalScaleCenter r k).im = 3 * r * k := by simp [criticalScaleCenter]
  rw [Complex.sub_re, hre] at h1
  rw [Complex.sub_im, him] at h2
  have a1 := abs_le.mp (le_trans h1 hz)
  have a2 := abs_le.mp (le_trans h2 hz)
  exact ⟨by linarith [a1.1], by linarith [a1.2], by linarith [a2.1], by linarith [a2.2]⟩

/-- **Exceptional discs are at most the off-line zeros.** -/
theorem card_badCriticalScaleDiscs_le_offLine {r T : ℝ} (hr : 0 < r) (hr8 : r ≤ 1 / 8)
    {K : ℕ} (hK : 3 * r * K + r ≤ T) :
    (badCriticalScaleDiscs r K).card ≤ (offLineZeroFinset T).card := by
  classical
  have hchoose : ∀ k ∈ badCriticalScaleDiscs r K,
      ∃ z ∈ closedBall (criticalScaleCenter r k) r, xi z = 0 := by
    intro k hk
    unfold badCriticalScaleDiscs at hk
    exact (Finset.mem_filter.mp hk).2
  choose! w hwball hwzero using hchoose
  have hmaps : ∀ k ∈ badCriticalScaleDiscs r K, w k ∈ offLineZeroFinset T := by
    intro k hk
    have hkI : k ∈ Finset.Icc 1 K := by
      unfold badCriticalScaleDiscs at hk; exact (Finset.mem_filter.mp hk).1
    rw [Finset.mem_Icc] at hkI
    obtain ⟨h1, h2, h3, h4⟩ := re_im_of_mem_criticalScaleDisc (hwball k hk)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkI.1
    have hkK : (k : ℝ) ≤ K := by exact_mod_cast hkI.2
    unfold offLineZeroFinset
    rw [Finset.mem_filter, mem_stripFinsetPos]
    refine ⟨⟨by linarith, by linarith, by nlinarith, by nlinarith, hwzero k hk⟩, ?_⟩
    intro hre; linarith
  have hinj : Set.InjOn w (badCriticalScaleDiscs r K : Set ℕ) := by
    intro k hk l hl hkl
    obtain ⟨-, -, hk1, hk2⟩ := re_im_of_mem_criticalScaleDisc (hwball k hk)
    obtain ⟨-, -, hl1, hl2⟩ := re_im_of_mem_criticalScaleDisc (hwball l hl)
    rw [hkl] at hk1 hk2
    have e1 : 3 * r * ((k : ℝ) - l) < 3 * r := by nlinarith
    have e2 : 3 * r * ((l : ℝ) - k) < 3 * r := by nlinarith
    have f1 : (k : ℝ) - l < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have f2 : (l : ℝ) - k < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have g1 : (k : ℤ) - l < 1 := by exact_mod_cast f1
    have g2 : (l : ℤ) - k < 1 := by exact_mod_cast f2
    omega
  exact Finset.card_le_card_of_injOn w hmaps hinj

/-- **Off-line zeros are at most `N(T)` minus the simple critical zeros.** -/
theorem card_offLine_le (T : ℝ) :
    (offLineZeroFinset T).card + xiSimpleCriticalZeroCount T ≤ xiPosZeroCount T := by
  classical
  unfold offLineZeroFinset xiSimpleCriticalZeroCount xiPosZeroCount
  set S := stripFinsetPos T
  have hdisj : Disjoint (S.filter (fun z => z.re ≠ 1 / 2))
      (S.filter (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)) := by
    rw [Finset.disjoint_filter]
    intro z _ h1 h2
    exact h1 h2.1
  rw [← Finset.card_union_of_disjoint hdisj]
  have hsub : S.filter (fun z => z.re ≠ 1 / 2) ∪
      S.filter (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) ⊆ S := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  calc (S.filter (fun z => z.re ≠ 1 / 2) ∪
        S.filter (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)).card
      ≤ S.card := Finset.card_le_card hsub
    _ = ∑ z ∈ S, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ z ∈ S, (analyticOrderAt xi z).toNat := by
        apply Finset.sum_le_sum
        intro z hz
        have hxi : xi z = 0 := (mem_stripFinsetPos.mp hz).2.2.2.2
        exact one_le_zeroMult_xi hxi

/-- **A third of the critical-scale discs at most are exceptional.** -/
theorem card_badCriticalScaleDiscs_le :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ {r : ℝ}, 0 < r → r ≤ 1 / 8 → ∀ {K : ℕ},
      3 * r * K + r ≤ T →
      ((badCriticalScaleDiscs r K).card : ℝ) ≤
        (1 - Zeta23.ThmD.HD 1 + ε) * (xiPosZeroCount T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := lamzouri_montgomeryTaylor_simpleCritical_epsilon ε hε
  refine ⟨T₀, fun T hT r hr hr8 K hK => ?_⟩
  have h1 := card_badCriticalScaleDiscs_le_offLine hr hr8 hK
  have h2 := card_offLine_le T
  have h3 := hT₀ T hT
  have h1' : ((badCriticalScaleDiscs r K).card : ℝ) ≤ (offLineZeroFinset T).card := by
    exact_mod_cast h1
  have h2' : ((offLineZeroFinset T).card : ℝ) + xiSimpleCriticalZeroCount T ≤
      xiPosZeroCount T := by exact_mod_cast h2
  nlinarith

/-- Off the exceptional set the seam contracts. -/
theorem criticalScaleDisc_adjointSeam_lt_one {r : ℝ} (hr : 0 < r) {k : ℕ}
    (hk : ∀ z ∈ closedBall (criticalScaleCenter r k) r, xi z ≠ 0) :
    ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter r k) r, xi ζ ≠ 0,
      ‖(xiDiscDatum (criticalScaleCenter r k) r hr hne).circlePhase.datum.adjointHankelSeam‖
        < 1 :=
  ⟨fun ζ hζ => hk ζ (sphere_subset_closedBall hζ),
    xiDisc_adjointSeam_lt_one_of_ne_zero _ _ _ _ hk⟩

/-! ## Halving by the reflection `ρ ↦ 1 − conj ρ` -/

/-- The off-line zeros right of the critical line. -/
def offLineRightZeroFinset (T : ℝ) : Finset ℂ := by
  classical
  exact (stripFinsetPos T).filter (fun z => 1 / 2 < z.re)

theorem mem_offLineRightZeroFinset {T : ℝ} {z : ℂ} :
    z ∈ offLineRightZeroFinset T ↔ z ∈ stripFinsetPos T ∧ 1 / 2 < z.re := by
  classical
  unfold offLineRightZeroFinset
  rw [Finset.mem_filter]

theorem mem_offLineZeroFinset {T : ℝ} {z : ℂ} :
    z ∈ offLineZeroFinset T ↔ z ∈ stripFinsetPos T ∧ z.re ≠ 1 / 2 := by
  classical
  unfold offLineZeroFinset
  rw [Finset.mem_filter]

theorem mem_stripFinsetPos_reflect {T : ℝ} {z : ℂ} (hz : z ∈ stripFinsetPos T) :
    1 - starRingEnd ℂ z ∈ stripFinsetPos T := by
  rw [mem_stripFinsetPos] at hz ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hz
  have hre : (1 - starRingEnd ℂ z).re = 1 - z.re := by simp
  have him : (1 - starRingEnd ℂ z).im = z.im := by simp
  refine ⟨by rw [hre]; linarith, by rw [hre]; linarith, by rw [him]; exact h3,
    by rw [him]; exact h4, ?_⟩
  rw [xi_one_sub, xi_conj, h5, map_zero]

/-- **Off-line zeros pair up:** twice the right-hand ones is at most all of them. -/
theorem two_mul_card_offLineRight_le (T : ℝ) :
    2 * (offLineRightZeroFinset T).card ≤ (offLineZeroFinset T).card := by
  classical
  set R := offLineRightZeroFinset T
  set O := offLineZeroFinset T
  set L := R.image (fun z => 1 - starRingEnd ℂ z) with hL
  have hinj : Set.InjOn (fun z : ℂ => 1 - starRingEnd ℂ z) (R : Set ℂ) := by
    intro a _ b _ hab
    have := congrArg (fun w : ℂ => starRingEnd ℂ (1 - w)) hab
    simpa using this
  have hLcard : L.card = R.card := Finset.card_image_of_injOn hinj
  have hdisj : Disjoint R L := by
    rw [Finset.disjoint_left]
    intro z hzR hzL
    rw [hL, Finset.mem_image] at hzL
    obtain ⟨w, hwR, rfl⟩ := hzL
    have h1 : 1 / 2 < (1 - starRingEnd ℂ w).re := (mem_offLineRightZeroFinset.mp hzR).2
    have h2 : 1 / 2 < w.re := (mem_offLineRightZeroFinset.mp hwR).2
    simp at h1
    linarith
  have hRO : R ⊆ O := by
    intro z hz
    have hz' := mem_offLineRightZeroFinset.mp hz
    exact mem_offLineZeroFinset.mpr ⟨hz'.1, fun h => by rw [h] at hz'; exact lt_irrefl _ hz'.2⟩
  have hLO : L ⊆ O := by
    intro z hz
    rw [hL, Finset.mem_image] at hz
    obtain ⟨w, hwR, rfl⟩ := hz
    have hwR := mem_offLineRightZeroFinset.mp hwR
    refine mem_offLineZeroFinset.mpr ⟨mem_stripFinsetPos_reflect hwR.1, ?_⟩
    intro h
    simp at h
    linarith [hwR.2]
  calc 2 * R.card = (R ∪ L).card := by rw [Finset.card_union_of_disjoint hdisj, hLcard]; ring
    _ ≤ O.card := Finset.card_le_card (Finset.union_subset hRO hLO)

theorem card_badCriticalScaleDiscs_le_offLineRight {r T : ℝ} (hr : 0 < r) (hr8 : r ≤ 1 / 8)
    {K : ℕ} (hK : 3 * r * K + r ≤ T) :
    (badCriticalScaleDiscs r K).card ≤ (offLineRightZeroFinset T).card := by
  classical
  have hchoose : ∀ k ∈ badCriticalScaleDiscs r K,
      ∃ z ∈ closedBall (criticalScaleCenter r k) r, xi z = 0 := by
    intro k hk
    unfold badCriticalScaleDiscs at hk
    exact (Finset.mem_filter.mp hk).2
  choose! w hwball hwzero using hchoose
  have hmaps : ∀ k ∈ badCriticalScaleDiscs r K, w k ∈ offLineRightZeroFinset T := by
    intro k hk
    have hkI : k ∈ Finset.Icc 1 K := by
      unfold badCriticalScaleDiscs at hk; exact (Finset.mem_filter.mp hk).1
    rw [Finset.mem_Icc] at hkI
    obtain ⟨h1, h2, h3, h4⟩ := re_im_of_mem_criticalScaleDisc (hwball k hk)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkI.1
    have hkK : (k : ℝ) ≤ K := by exact_mod_cast hkI.2
    rw [mem_offLineRightZeroFinset, mem_stripFinsetPos]
    exact ⟨⟨by linarith, by linarith, by nlinarith, by nlinarith, hwzero k hk⟩, by linarith⟩
  have hinj : Set.InjOn w (badCriticalScaleDiscs r K : Set ℕ) := by
    intro k hk l hl hkl
    obtain ⟨-, -, hk1, hk2⟩ := re_im_of_mem_criticalScaleDisc (hwball k hk)
    obtain ⟨-, -, hl1, hl2⟩ := re_im_of_mem_criticalScaleDisc (hwball l hl)
    rw [hkl] at hk1 hk2
    have f1 : (k : ℝ) - l < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have f2 : (l : ℝ) - k < 1 := by
      by_contra hc; push Not at hc; nlinarith
    have g1 : (k : ℤ) - l < 1 := by exact_mod_cast f1
    have g2 : (l : ℤ) - k < 1 := by exact_mod_cast f2
    omega
  exact Finset.card_le_card_of_injOn w hmaps hinj

/-- **At most a sixth of `N(T)` exceptional discs.** -/
theorem card_badCriticalScaleDiscs_le_half :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ {r : ℝ}, 0 < r → r ≤ 1 / 8 → ∀ {K : ℕ},
      3 * r * K + r ≤ T →
      2 * ((badCriticalScaleDiscs r K).card : ℝ) ≤
        (1 - Zeta23.ThmD.HD 1 + ε) * (xiPosZeroCount T : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := lamzouri_montgomeryTaylor_simpleCritical_epsilon ε hε
  refine ⟨T₀, fun T hT r hr hr8 K hK => ?_⟩
  have h1 := card_badCriticalScaleDiscs_le_offLineRight hr hr8 hK
  have h2 := two_mul_card_offLineRight_le T
  have h3 := card_offLine_le T
  have h4 := hT₀ T hT
  have h1' : ((badCriticalScaleDiscs r K).card : ℝ) ≤ (offLineRightZeroFinset T).card := by
    exact_mod_cast h1
  have h2' : 2 * ((offLineRightZeroFinset T).card : ℝ) ≤ (offLineZeroFinset T).card := by
    exact_mod_cast h2
  have h3' : ((offLineZeroFinset T).card : ℝ) + xiSimpleCriticalZeroCount T ≤
      xiPosZeroCount T := by exact_mod_cast h3
  nlinarith


end RHTower
