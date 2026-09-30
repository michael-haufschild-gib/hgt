import GaloisForLFunctions.RHTower.ZetaStrongRecurrenceReceiver
import GaloisForLFunctions.RHTower.XiCriticalScaleDiscSeamExplicitDensity

/-!
# Contracting seams on almost all right discs of every fixed radius

For `σ > ½` and `ℓ > 0` let `N(σ, ℓ)` be the set of heights within `ℓ` of the ordinate of a zero of
`ζ` with real part `≥ σ`.  On a Littlewood window, the part of `N(σ, ℓ)` away from the window ends
is covered by the intervals `[Im w − ℓ, Im w + ℓ]` of the zeros `w` counted by
`eventually_zeroCount_fixedSigma_le`, so it has measure `2ℓ · o(T)`; dyadic summation gives

  `|N(σ, ℓ) ∩ [0, V]| = o(V)`   (`eventually_volume_zetaZeroShadow_le`).

An exceptional right disc `D_k` of radius `r` (centre `½ + 2r + 3rk·i`) contains a zero of `ξ` with
real part `≥ ½ + r`, so its height interval `[3rk − r, 3rk + r]` lies in `N(½ + r, 2r)`, and these
intervals are pairwise disjoint.  Hence at every fixed radius the exceptional discs among
`D_1, …, D_K` number `o(K)`, and the adjoint Hankel seam of the `ξ` phase is a strict contraction on
all the others (`eventually_card_goodCriticalScaleDiscs_ge`).  The proportion `37%` of
`exists_card_goodCriticalScaleDiscs_ge` is uniform in the radius; at a fixed radius it is one.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-- Heights within `ℓ` of the ordinate of a zero of `ζ` with real part `≥ σ`. -/
def zetaZeroShadow (σ ℓ : ℝ) : Set ℝ :=
  {τ : ℝ | ∃ w : ℂ, riemannZeta w = 0 ∧ σ ≤ w.re ∧ |w.im - τ| ≤ ℓ}

/-- **The zero shadow on one window.** For every `δ > 0`, for all large `V` the part of `N(σ, ℓ)`
in `[V/2, V]` has measure at most `δ V`. -/
theorem eventually_volume_zetaZeroShadow_window_le {σ ℓ δ : ℝ} (hσ : 1 / 2 < σ) (hℓ : 0 < ℓ)
    (hδ : 0 < δ) :
    ∀ᶠ V in atTop,
      volume (zetaZeroShadow σ ℓ ∩ Icc ((V - 0) / 2) V) ≤ ENNReal.ofReal (δ * V) := by
  classical
  set E := zetaZeroShadow σ ℓ
  have hlin : Tendsto (fun V : ℝ => 2 * V) atTop atTop := tendsto_id.const_mul_atTop two_pos
  have hε' : 0 < δ / (2 * ℓ) := by positivity
  filter_upwards [hlin.eventually (eventually_zeroCount_fixedSigma_le hσ hε'),
    hlin.eventually (eventually_ge_atTop (100 : ℝ)),
    eventually_ge_atTop ((2 + 2 * ℓ) / (δ / 2))] with V hV hV100 hVbig
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hV
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  set Zσ := Z.filter (fun w => σ ≤ w.re)
  have hcover : Icc ((V - 0) / 2) V ⊆ (Icc ((V - 0) / 2) (T₁ + ℓ) ∪ Icc (T₁ + ℓ) (T₂ - ℓ)) ∪
      Icc (T₂ - ℓ) V := by
    intro x hx
    rcases le_total x (T₁ + ℓ) with h | h
    · exact Or.inl (Or.inl ⟨hx.1, h⟩)
    rcases le_total x (T₂ - ℓ) with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr ⟨h', hx.2⟩
  have hmid : E ∩ Icc (T₁ + ℓ) (T₂ - ℓ) ⊆ ⋃ w ∈ Zσ, Icc (w.im - ℓ) (w.im + ℓ) := by
    rintro τ ⟨⟨w, hw0, hwσ, hwτ⟩, hτ⟩
    have hwτ' := abs_le.mp hwτ
    have hw1 : w.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hw0
    have hwZ : w ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩, hw0⟩
    exact mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨hwZ, hwσ⟩, ⟨by linarith, by linarith⟩⟩
  have hcard : (Zσ.card : ℝ) ≤ ∑ w ∈ Zσ, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨hwZ, -⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0
  have hvmid : volume (E ∩ Icc (T₁ + ℓ) (T₂ - ℓ)) ≤
      ENNReal.ofReal (2 * ℓ * (δ / (2 * ℓ) * (T₂ - T₁))) :=
    calc volume (E ∩ Icc (T₁ + ℓ) (T₂ - ℓ))
        ≤ volume (⋃ w ∈ Zσ, Icc (w.im - ℓ) (w.im + ℓ)) := measure_mono hmid
      _ ≤ ∑ w ∈ Zσ, volume (Icc (w.im - ℓ) (w.im + ℓ)) := measure_biUnion_finset_le _ _
      _ = ∑ w ∈ Zσ, ENNReal.ofReal (2 * ℓ) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Real.volume_Icc]
          congr 1
          ring
      _ = ENNReal.ofReal (2 * ℓ * Zσ.card) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), mul_comm]
      _ ≤ ENNReal.ofReal (2 * ℓ * (δ / (2 * ℓ) * (T₂ - T₁))) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (hcard.trans (hc Z hZ)) (by positivity))
  have hlo : volume (Icc ((V - 0) / 2) (T₁ + ℓ)) ≤ ENNReal.ofReal (1 + ℓ) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith [hT₁.2])
  have hhi : volume (Icc (T₂ - ℓ) V) ≤ ENNReal.ofReal (1 + ℓ) := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by linarith [hT₂.1])
  have hmid' : 2 * ℓ * (δ / (2 * ℓ) * (T₂ - T₁)) = δ * (T₂ - T₁) := by
    field_simp
  have hlen : T₂ - T₁ ≤ V / 2 := by linarith [hT₁.1, hT₂.2]
  have hVbig' : 2 + 2 * ℓ ≤ δ / 2 * V := by
    rw [div_le_iff₀ (by positivity)] at hVbig
    linarith
  calc volume (E ∩ Icc ((V - 0) / 2) V)
      ≤ volume ((E ∩ Icc ((V - 0) / 2) (T₁ + ℓ) ∪ E ∩ Icc (T₁ + ℓ) (T₂ - ℓ)) ∪
          E ∩ Icc (T₂ - ℓ) V) := by
        refine measure_mono ?_
        rw [← inter_union_distrib_left, ← inter_union_distrib_left]
        exact inter_subset_inter_right _ hcover
    _ ≤ (volume (Icc ((V - 0) / 2) (T₁ + ℓ)) + volume (E ∩ Icc (T₁ + ℓ) (T₂ - ℓ))) +
          volume (Icc (T₂ - ℓ) V) :=
        (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
          (add_le_add (measure_mono inter_subset_right) le_rfl)) (measure_mono inter_subset_right))
    _ ≤ (ENNReal.ofReal (1 + ℓ) + ENNReal.ofReal (δ * (T₂ - T₁))) + ENNReal.ofReal (1 + ℓ) :=
        add_le_add (add_le_add hlo (hmid' ▸ hvmid)) hhi
    _ = ENNReal.ofReal ((1 + ℓ) + δ * (T₂ - T₁) + (1 + ℓ)) := by
        have hmid0 : 0 ≤ δ * (T₂ - T₁) := mul_nonneg hδ.le (by linarith)
        rw [← ENNReal.ofReal_add (by positivity) hmid0, ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal (δ * V) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := mul_le_mul_of_nonneg_left hlen hδ.le
        linarith

/-- **The zero shadow has density zero.** For `σ > ½` and `ℓ > 0`, the heights in `[0, V]` within
`ℓ` of the ordinate of a zero of `ζ` with real part `≥ σ` have measure `o(V)`. -/
theorem eventually_volume_zetaZeroShadow_le {σ ℓ κ : ℝ} (hσ : 1 / 2 < σ) (hℓ : 0 < ℓ)
    (hκ : 0 < κ) :
    ∀ᶠ V in atTop, volume (zetaZeroShadow σ ℓ ∩ Icc 0 V) ≤ ENNReal.ofReal (κ * V) :=
  eventually_volume_inter_Icc_le_of_window
    (fun _ hδ => eventually_volume_zetaZeroShadow_window_le hσ hℓ hδ) hκ

/-- **Exceptional discs against the zero shadow.** The height intervals `[3rk − r, 3rk + r]` of
the exceptional right discs are disjoint and lie in `N(½ + r, 2r) ∩ [0, 3rK + r]`. -/
theorem ofReal_mul_card_badCriticalScaleDiscs_le {r : ℝ} (hr : 0 < r) (K : ℕ) :
    ENNReal.ofReal (2 * r * (badCriticalScaleDiscs r K).card) ≤
      volume (zetaZeroShadow (1 / 2 + r) (2 * r) ∩ Icc 0 (3 * r * K + r)) := by
  classical
  have hsub : (⋃ k ∈ badCriticalScaleDiscs r K, Icc (3 * r * k - r) (3 * r * k + r)) ⊆
      zetaZeroShadow (1 / 2 + r) (2 * r) ∩ Icc 0 (3 * r * K + r) := by
    intro τ hτ
    obtain ⟨k, hk, hτk⟩ := mem_iUnion₂.mp hτ
    unfold badCriticalScaleDiscs at hk
    obtain ⟨hkI, z, hz, hz0⟩ := Finset.mem_filter.mp hk
    obtain ⟨h1, -, h3, h4⟩ := re_im_of_mem_criticalScaleDisc hz
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hkI).1
    have hkK : (k : ℝ) ≤ K := by exact_mod_cast (Finset.mem_Icc.mp hkI).2
    have hzre1 := xi_zero_re_lt_one hz0
    have hz1 : z ≠ 1 := by intro h; rw [h] at hzre1; simp at hzre1
    have hζ : riemannZeta z = 0 := (xi_eq_zero_iff (by linarith) hz1).mp hz0
    refine ⟨⟨z, hζ, h1, abs_le.mpr ⟨by linarith [hτk.2], by linarith [hτk.1]⟩⟩, ?_, ?_⟩
    · nlinarith [hτk.1]
    · nlinarith [hτk.2]
  have hdisj : Set.PairwiseDisjoint (↑(badCriticalScaleDiscs r K))
      (fun k : ℕ => Icc (3 * r * k - r) (3 * r * k + r)) := by
    intro k _ l _ hkl
    rw [Function.onFun, Set.disjoint_left]
    intro τ hτk hτl
    apply hkl
    have f1 : (k : ℝ) - l < 1 := by nlinarith [hτk.1, hτl.2]
    have f2 : (l : ℝ) - k < 1 := by nlinarith [hτk.2, hτl.1]
    have g1 : (k : ℤ) - l < 1 := by exact_mod_cast f1
    have g2 : (l : ℤ) - k < 1 := by exact_mod_cast f2
    omega
  calc ENNReal.ofReal (2 * r * (badCriticalScaleDiscs r K).card)
      = ∑ k ∈ badCriticalScaleDiscs r K, volume (Icc (3 * r * k - r) (3 * r * k + r)) := by
        rw [Finset.sum_congr rfl fun k _ => by
          rw [Real.volume_Icc, show 3 * r * k + r - (3 * r * k - r) = 2 * r by ring],
          Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), mul_comm]
    _ = volume (⋃ k ∈ badCriticalScaleDiscs r K, Icc (3 * r * k - r) (3 * r * k + r)) :=
        (measure_biUnion_finset hdisj fun k _ => measurableSet_Icc).symm
    _ ≤ _ := measure_mono hsub

/-- **Exceptional discs of a fixed radius are `o(K)`.** -/
theorem eventually_card_badCriticalScaleDiscs_le {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, ((badCriticalScaleDiscs r K).card : ℝ) ≤ ε * K := by
  obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp
    (eventually_volume_zetaZeroShadow_le (σ := 1 / 2 + r) (ℓ := 2 * r) (by linarith)
      (by positivity) (show 0 < ε / 4 by positivity))
  filter_upwards [eventually_ge_atTop (⌈V₀ / (3 * r)⌉₊ + 1)] with K hK
  have hK' : (⌈V₀ / (3 * r)⌉₊ : ℝ) + 1 ≤ K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by linarith [Nat.cast_nonneg (α := ℝ) ⌈V₀ / (3 * r)⌉₊]
  have hVK : V₀ ≤ 3 * r * K + r := by
    have h1 := Nat.le_ceil (V₀ / (3 * r))
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith
  have h1 := (ofReal_mul_card_badCriticalScaleDiscs_le hr K).trans (hV₀ _ hVK)
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  have h2 : 2 * r * ((badCriticalScaleDiscs r K).card : ℝ) ≤ 2 * r * (ε * K) := by
    have h3 := mul_nonneg (mul_nonneg hr.le hε.le) (show (0 : ℝ) ≤ 5 * K - 1 by linarith)
    linarith
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- **Contracting seams on almost all right discs of a fixed radius.** For every radius `r > 0` and
every `ε > 0`, for all large `K` at least `(1 − ε) K` of the right discs `D_1, …, D_K` of radius `r`
are zero-free, and on each of them the adjoint Hankel seam of the `ξ` phase has norm `< 1`. -/
theorem eventually_card_goodCriticalScaleDiscs_ge {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      (1 - ε) * (K : ℝ) ≤ ((Finset.Icc 1 K \ badCriticalScaleDiscs r K).card : ℝ) ∧
      ∀ k ∈ Finset.Icc 1 K \ badCriticalScaleDiscs r K,
        ∃ hne : ∀ ζ ∈ sphere (criticalScaleCenter r k) r, xi ζ ≠ 0,
          ‖(xiDiscDatum (criticalScaleCenter r k) r hr hne).circlePhase.datum.adjointHankelSeam‖
            < 1 := by
  classical
  filter_upwards [eventually_card_badCriticalScaleDiscs_le hr hε] with K hbad
  refine ⟨?_, fun k hk => ?_⟩
  · have hsub : badCriticalScaleDiscs r K ⊆ Finset.Icc 1 K := by
      intro k hk
      unfold badCriticalScaleDiscs at hk
      exact (Finset.mem_filter.mp hk).1
    have e : ((Finset.Icc 1 K \ badCriticalScaleDiscs r K).card : ℝ)
        = ((Finset.Icc 1 K).card : ℝ) - (badCriticalScaleDiscs r K).card := by
      rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    have hK : ((Finset.Icc 1 K).card : ℝ) = K := by simp
    rw [e, hK]
    linarith
  · obtain ⟨hkI, hkb⟩ := Finset.mem_sdiff.mp hk
    apply criticalScaleDisc_adjointSeam_lt_one hr
    intro z hz hz0
    apply hkb
    unfold badCriticalScaleDiscs
    exact Finset.mem_filter.mpr ⟨hkI, z, hz, hz0⟩

end

end RHTower
