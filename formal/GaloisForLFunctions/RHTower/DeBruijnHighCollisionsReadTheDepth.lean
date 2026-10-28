import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit
import GaloisForLFunctions.RHTower.DeBruijnNewmanEnergyTransition
import GaloisForLFunctions.RHTower.LindelofCosineFiniteDefectDepth
import GaloisForLFunctions.RHTower.DeBruijnNewmanStrictBound
import GaloisForLFunctions.RHTower.KiKimLeeLargeHeightReality

/-!
# The high collisions of the de Bruijn–Newman flow read the depth of the zeros

Split the nonreal zeros of `H_t` (`riemannHeat t`) at a height `h > 0`: the **high** zeros have
`Im w ≥ h`, the **near-axis** zeros `0 < |Im w| < h`. The question whether the nonreal count
`N(t)` is bounded uniformly as `t → 0⁺` splits accordingly.

* **Energy–count law** (`highCount_le_of_energy`): below the Gaussian horizon `8St < 1`, the high
  zeros of `H_t` number at most `2K/h²`, where `K` bounds the energy
  `Σ_{Im ρ > 0} ((Im ρ)² − 2t − h²/2)_+` of the zeros of `Ξ`. This is the weak majorization
  `riemannHeat_upper_energy_le` at threshold `h²/2`.
* **Uniform high count under depth finiteness** (`exists_highCount_le_of_zerosApproachLine`): if
  the zeros approach the line, the high zeros of `H_t` are bounded uniformly in `t > 0` by
  `max(2K_h/h², N(t₀))`, `K_h = Σ_{Im ρ > h/2} (Im ρ)²`.
* **Converse** (`zerosApproachLine_of_highCount`): every finite set of zeros of `Ξ` of depth
  `> 2h` survives, with multiplicity, as high zeros of `H_s` for small `s`
  (`eventually_exists_highZeros`), so a uniform high count at every height forces the zeros to
  approach the line.

At bound zero this is RH (`riemannHypothesis_iff_highCount_zero`).

Hence (`zerosApproachLine_iff_highCount`, `lindelof_of_highCount`): a `t`-uniform bound on the high
collisions at every height is exactly the statement that the zeros approach the line, which is
the Lindelöf hypothesis together with finiteness of the nonreal zeros of every cosine shift. A
`t`-uniform bound on all collisions is finite off-line support
(`finite_nonreal_zeros_iff_exists_nonrealZeroCount_le`). What the flow adds beyond the depth
counting of `Ξ` is the near-axis count alone.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.DeBruijn

open RHTower.BacklundConverse RHTower.CosineDefectBudget RHTower.LindelofSparse

/-- The high zeros of `H_t` (`Im w ≥ h`) number at most `B`, with multiplicity. -/
def HighCountLE (t h B : ℝ) : Prop :=
  ∀ Z : Finset ℂ, (∀ w ∈ Z, riemannHeat t w = 0 ∧ h ≤ w.im) →
    (∑ w ∈ Z, (zeroMult (riemannHeat t) w : ℝ)) ≤ B

/-- **Energy–count law.** Below the Gaussian horizon, the high zeros of `H_t` number at most
`2K/h²`, `K` a bound for the energy `Σ_{Im ρ > 0} ((Im ρ)² − 2t − h²/2)_+` of `Ξ`. -/
theorem highCount_le_of_energy {t h K : ℝ} (ht : 0 < t) (htS : 8 * xiApproxGrowth * t < 1)
    (hh : 0 < h)
    (hK : ∀ T : Finset XiZeroCopy,
      ∑ q ∈ T.filter (fun q => 0 < (xiSpectralPoint q).im),
        max ((xiSpectralPoint q).im ^ 2 - 2 * t - h ^ 2 / 2) 0 ≤ K) :
    HighCountLE t h (2 * K / h ^ 2) := by
  intro Z hZ
  have hE := riemannHeat_upper_energy_le ht htS (by positivity : 0 ≤ h ^ 2 / 2) hK Z
  have hterm : ∀ w ∈ Z, (zeroMult (riemannHeat t) w : ℝ) * (h ^ 2 / 2) ≤
      (zeroMult (riemannHeat t) w : ℝ) * max ((max w.im 0) ^ 2 - h ^ 2 / 2) 0 := by
    intro w hw
    have hwim := (hZ w hw).2
    have hm : max w.im 0 = w.im := max_eq_left (hh.le.trans hwim)
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [hm]
    refine le_max_of_le_left ?_
    nlinarith
  have hsum := (Finset.sum_le_sum hterm).trans hE
  rw [← Finset.sum_mul] at hsum
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- A finite set of nonreal zeros of `H_t` is counted by `N(t)`. -/
theorem sum_zeroMult_le_nonrealZeroCount {t : ℝ} (ht : 0 < t) {Z : Finset ℂ}
    (hZ : ∀ w ∈ Z, riemannHeat t w = 0 ∧ w.im ≠ 0) :
    ∑ w ∈ Z, zeroMult (riemannHeat t) w ≤ nonrealZeroCount t := by
  rw [nonrealZeroCount_eq ht]
  exact Finset.sum_le_sum_of_subset fun w hw => by
    rw [Set.Finite.mem_toFinset]; exact hZ w hw

/-- **Zeros approaching the line bound the high collisions uniformly in time.** -/
theorem exists_highCount_le_of_zerosApproachLine (hZ : ZerosApproachLine) {h : ℝ} (hh : 0 < h) :
    ∃ B : ℝ, ∀ t : ℝ, 0 < t → HighCountLE t h B := by
  classical
  have hD := hZ (h / 2) (by positivity)
  set K : ℝ := ∑ q ∈ hD.toFinset, (xiSpectralPoint q).im ^ 2
  set t₀ : ℝ := 1 / (16 * xiApproxGrowth + 16)
  have hS := xiApproxGrowth_nonneg
  have ht₀ : 0 < t₀ := by positivity
  have ht₀S : 8 * xiApproxGrowth * t₀ < 1 := by
    simp only [t₀]
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  refine ⟨max (2 * K / h ^ 2) (nonrealZeroCount t₀), fun t ht Z hZt => ?_⟩
  rcases lt_or_ge t t₀ with htt | htt
  · -- below the horizon: the energy of the zeros deeper than `h/2`
    have htS : 8 * xiApproxGrowth * t < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left htt.le (by positivity)) ht₀S
    refine (highCount_le_of_energy ht htS hh (K := K) (fun T => ?_) Z hZt).trans
      (le_max_left _ _)
    set T' := T.filter (fun q => 0 < (xiSpectralPoint q).im)
    have hoff : ∀ q ∈ T', q ∉ hD.toFinset →
        max ((xiSpectralPoint q).im ^ 2 - 2 * t - h ^ 2 / 2) 0 = 0 := by
      intro q hq hqD
      rw [Set.Finite.mem_toFinset] at hqD
      have hle : (xiSpectralPoint q).im ≤ h / 2 := not_lt.mp hqD
      have hpos : 0 < (xiSpectralPoint q).im := (Finset.mem_filter.mp hq).2
      refine max_eq_right ?_
      nlinarith
    calc ∑ q ∈ T', max ((xiSpectralPoint q).im ^ 2 - 2 * t - h ^ 2 / 2) 0
        = ∑ q ∈ T'.filter (· ∈ hD.toFinset),
            max ((xiSpectralPoint q).im ^ 2 - 2 * t - h ^ 2 / 2) 0 :=
          (Finset.sum_filter_of_ne fun q hq hne => by
            by_contra hqD
            exact hne (hoff q hq hqD)).symm
      _ ≤ ∑ q ∈ T'.filter (· ∈ hD.toFinset), (xiSpectralPoint q).im ^ 2 :=
          Finset.sum_le_sum fun q _ => max_le (by nlinarith [ht]) (sq_nonneg _)
      _ ≤ K := Finset.sum_le_sum_of_subset_of_nonneg
          (fun q hq => (Finset.mem_filter.mp hq).2) fun _ _ _ => sq_nonneg _
  · -- beyond: the count is nonincreasing
    have hnonreal : ∀ w ∈ Z, riemannHeat t w = 0 ∧ w.im ≠ 0 := fun w hw =>
      ⟨(hZt w hw).1, (lt_of_lt_of_le hh (hZt w hw).2).ne'⟩
    have h1 := sum_zeroMult_le_nonrealZeroCount ht hnonreal
    have h2 := nonrealZeroCount_antitoneOn (Set.mem_Ioi.mpr ht₀) (Set.mem_Ioi.mpr ht) htt
    refine le_trans ?_ (le_max_right _ _)
    rw [← Nat.cast_sum]
    exact_mod_cast h1.trans h2

/-- **Deep zeros of `Ξ` survive as high zeros.** For a finite set `E` of zeros of `Ξ` with
`Im e ≥ 2h > 0`, for all small `s > 0` the zeros of `H_s` in disjoint discs around `E` all have
`Im ≥ h`, and they carry the multiplicities of `E`. -/
theorem eventually_exists_highZeros {E : Finset ℂ} {h : ℝ} (hh : 0 < h)
    (hE : ∀ e ∈ E, riemannHeat 0 e = 0 ∧ 2 * h ≤ e.im) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ∃ Z : Finset ℂ, (∀ z ∈ Z, riemannHeat s z = 0 ∧ h ≤ z.im) ∧
      ∑ e ∈ E, zeroMult (riemannHeat 0) e ≤ ∑ z ∈ Z, zeroMult (riemannHeat s) z := by
  classical
  choose ρ₀ hρ₀ hρ₀prop using fun e => exists_radius_zeroSumBall_riemannHeat_eq (le_refl (0 : ℝ)) e
  obtain ⟨d, hd, hdsep⟩ := exists_pos_sep E
  set r : ℂ → ℝ := fun e => min (ρ₀ e) (min (e.im / 2) (d / 3)) with hrdef
  have hrpos : ∀ e ∈ E, 0 < r e := fun e he =>
    lt_min (hρ₀ e) (lt_min (by linarith [(hE e he).2]) (by linarith))
  have hhigh : ∀ e ∈ E, ∀ w ∈ ball e (r e), h ≤ w.im := by
    intro e he w hw
    have h1 : |(w - e).im| ≤ ‖w - e‖ := Complex.abs_im_le_norm _
    rw [mem_ball, dist_eq_norm] at hw
    have hr2 : r e ≤ e.im / 2 := (min_le_right _ _).trans (min_le_left _ _)
    rw [Complex.sub_im] at h1
    have := (abs_le.mp (h1.trans (hw.le.trans hr2))).1
    linarith [(hE e he).2]
  have hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')) := by
    intro e he e' he' hne
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hdsep e he e' he' hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    have h3 : r e ≤ d / 3 := (min_le_right _ _).trans (min_le_right _ _)
    have h4 : r e' ≤ d / 3 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  set F : ℝ → ℂ → ℂ := fun s => riemannHeat (max s 0) with hFdef
  have hF : ∀ s, Differentiable ℂ (F s) := fun s => differentiable_riemannHeat (le_max_right _ _)
  have hdiff0 := differentiable_riemannHeat (le_refl (0 : ℝ))
  have hev : ∀ e ∈ E, ∀ᶠ s in 𝓝[>] (0 : ℝ),
      zeroSumBall (F s) e (r e) = (zeroMult (riemannHeat 0) e : ℂ) ∧
        ∀ w ∈ sphere e (r e), F s w ≠ 0 := by
    intro e he
    obtain ⟨hsph, hcount⟩ := hρ₀prop e (r e) (hrpos e he) (min_le_left _ _)
    have h1 := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hF hdiff0
      tendstoLocallyUniformly_riemannHeat_max_zero (hrpos e he)
      (by linarith [hrpos e he] : r e < 2 * r e) hsph
    have h2 := eventually_ne_zero_on_sphere hdiff0.continuous
      tendstoLocallyUniformly_riemannHeat_max_zero (hrpos e he).le hsph
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨by rw [hs1, hcount], hs2⟩
  filter_upwards [(Filter.eventually_all_finset E).mpr hev, self_mem_nhdsWithin] with s hs hs0
  have hs0' : 0 < s := Set.mem_Ioi.mp hs0
  have hFs : F s = riemannHeat s := by simp only [hFdef, max_eq_left hs0'.le]
  have hdiff := differentiable_riemannHeat hs0'.le
  have hZ : ∀ e ∈ E, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball e (r e)) ∧
      (∀ z ∈ ball e (r e), riemannHeat s z = 0 ↔ z ∈ Z) ∧
      zeroSumBall (riemannHeat s) e (r e) = ∑ ρ ∈ Z, (zeroMult (riemannHeat s) ρ : ℂ) :=
    fun e he => exists_zeroSet_zeroSumBall (hrpos e he) (by linarith [hrpos e he] : r e < 2 * r e)
      isOpen_univ (subset_univ _) hdiff.differentiableOn (by rw [← hFs]; exact (hs e he).2)
  choose! Zs hZball hZzero hZsum using hZ
  have hpd : (E : Set ℂ).PairwiseDisjoint Zs := by
    intro e he e' he' hne
    refine Finset.disjoint_left.mpr fun z hz hz' => ?_
    exact (Set.disjoint_left.mp (hdisj e he e' he' hne)) (hZball e he z hz) (hZball e' he' z hz')
  refine ⟨E.biUnion Zs, fun z hz => ?_, ?_⟩
  · obtain ⟨e, he, hze⟩ := Finset.mem_biUnion.mp hz
    exact ⟨(hZzero e he z (hZball e he z hze)).mpr hze, hhigh e he z (hZball e he z hze)⟩
  · rw [Finset.sum_biUnion hpd]
    refine Finset.sum_le_sum fun e he => le_of_eq ?_
    have h1 := (hs e he).1
    rw [hFs, hZsum e he] at h1
    exact_mod_cast h1.symm

/-- Infinitely many copies of depth `> h` have infinitely many distinct spectral points. -/
theorem infinite_image_deepCopies {h : ℝ} (hinf : (deepCopies h).Infinite) :
    (xiSpectralPoint '' deepCopies h).Infinite := by
  intro hfin
  refine hinf ((hfin.preimage' fun e _ => ?_).subset fun q hq => ⟨q, hq, rfl⟩)
  rcases (xiSpectralPoint ⁻¹' {e}).eq_empty_or_nonempty with h0 | ⟨q₀, hq₀⟩
  · rw [h0]; exact Set.finite_empty
  · refine (Set.finite_range fun i : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q₀.1 : ℂ))) =>
      (⟨q₀.1, i⟩ : XiZeroCopy)).subset fun q hq => ?_
    have hq' : xiSpectralPoint q = e := hq
    have hq₀' : xiSpectralPoint q₀ = e := hq₀
    have h1 : q.1 = q₀.1 := (xiSpectralPoint_eq_iff q q₀).mp (hq'.trans hq₀'.symm)
    obtain ⟨ρ, i⟩ := q
    simp only at h1
    subst h1
    exact ⟨i, rfl⟩

/-- **A uniform high count at every height forces the zeros to approach the line.** -/
theorem zerosApproachLine_of_highCount
    (hB : ∀ h : ℝ, 0 < h → ∃ B : ℝ, ∀ t : ℝ, 0 < t → HighCountLE t h B) :
    ZerosApproachLine := by
  intro h₀ hh₀
  by_contra hinf
  obtain ⟨B, hBt⟩ := hB (h₀ / 2) (by positivity)
  have himg := infinite_image_deepCopies hinf
  obtain ⟨E, hEsub, hEcard⟩ := himg.exists_subset_card_eq (⌈B⌉₊ + 1)
  have hE : ∀ e ∈ E, riemannHeat 0 e = 0 ∧ 2 * (h₀ / 2) ≤ e.im := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := hEsub he
    refine ⟨by rw [riemannHeat_zero_eq_XiC]; exact XiC_xiSpectralPoint_eq_zero q, ?_⟩
    have : h₀ < (xiSpectralPoint q).im := hq
    linarith
  obtain ⟨s, ⟨Z, hZ, hsum⟩, hs0⟩ :=
    ((eventually_exists_highZeros (by positivity) hE).and self_mem_nhdsWithin).exists
  have hle := hBt s hs0 Z hZ
  have hcard : (E.card : ℝ) ≤ ∑ e ∈ E, (zeroMult (riemannHeat 0) e : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun e he => ?_
    exact_mod_cast one_le_zeroMult_riemannHeat le_rfl (hE e he).1
  have hsumR : ∑ e ∈ E, (zeroMult (riemannHeat 0) e : ℝ) ≤
      ∑ z ∈ Z, (zeroMult (riemannHeat s) z : ℝ) := by exact_mod_cast hsum
  rw [hEcard] at hcard
  push_cast at hcard
  have := Nat.le_ceil B
  linarith

/-- **The uniform high count is exactly the approach of the zeros to the line.** -/
theorem zerosApproachLine_iff_highCount :
    ZerosApproachLine ↔ ∀ h : ℝ, 0 < h → ∃ B : ℝ, ∀ t : ℝ, 0 < t → HighCountLE t h B :=
  ⟨fun hZ _ hh => exists_highCount_le_of_zerosApproachLine hZ hh, zerosApproachLine_of_highCount⟩

/-- **A uniform high count is Lindelöf-strength**: it implies the Lindelöf hypothesis and a
zero-free half-plane `Re s > ½ + α`, `α < ½`. -/
theorem lindelof_of_highCount
    (hB : ∀ h : ℝ, 0 < h → ∃ B : ℝ, ∀ t : ℝ, 0 < t → HighCountLE t h B) :
    LindelofCriticalLine ∧ ∃ α : ℝ, α < 1 / 2 ∧ XiZeroHalfPlaneBound α :=
  ⟨lindelofCriticalLine_of_zerosApproachLine (zerosApproachLine_of_highCount hB),
    quasiRH_of_zerosApproachLine (zerosApproachLine_of_highCount hB)⟩

/-- **The uniform high count is LH plus finiteness of every cosine shift.** -/
theorem highCount_iff_lindelof_and_cosShiftXi_finite_nonreal :
    (∀ h : ℝ, 0 < h → ∃ B : ℝ, ∀ t : ℝ, 0 < t → HighCountLE t h B) ↔
      LindelofCriticalLine ∧
        ∀ h : ℝ, 0 < h → {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite := by
  rw [← zerosApproachLine_iff_highCount, zerosApproachLine_iff_lindelof_and_cosShiftXi_finite_nonreal]

/-- **No high collisions at any time and height is RH.** -/
theorem riemannHypothesis_iff_highCount_zero :
    RiemannHypothesis ↔ ∀ h : ℝ, 0 < h → ∀ t : ℝ, 0 < t → HighCountLE t h 0 := by
  constructor
  · intro hRH h hh t ht Z hZ
    have hZe : Z = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by
      have := (riemannHeat_zeros_real_simple_of_riemannHypothesis hRH ht (hZ w hw).1).1
      linarith [(hZ w hw).2]
    simp [hZe]
  · intro h0
    refine riemannHypothesis_iff_riemannHeat_zero_real.mpr fun z hz => ?_
    by_contra hne
    -- move the zero to the upper half-plane by evenness
    obtain ⟨w, hw0, hwim⟩ : ∃ w : ℂ, riemannHeat 0 w = 0 ∧ 0 < w.im := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨-z, by rw [riemannHeat_neg le_rfl]; exact hz, by rw [Complex.neg_im]; linarith⟩
      · exact ⟨z, hz, hgt⟩
    have hE : ∀ e ∈ ({w} : Finset ℂ), riemannHeat 0 e = 0 ∧ 2 * (w.im / 2) ≤ e.im := by
      intro e he
      rw [Finset.mem_singleton.mp he]
      exact ⟨hw0, by linarith⟩
    obtain ⟨s, ⟨Z, hZ, hsum⟩, hs0⟩ :=
      ((eventually_exists_highZeros (by positivity) hE).and self_mem_nhdsWithin).exists
    have hle := h0 (w.im / 2) (by positivity) s hs0 Z hZ
    have h1 := one_le_zeroMult_riemannHeat le_rfl hw0
    rw [Finset.sum_singleton] at hsum
    have hsumR : (1 : ℝ) ≤ ∑ z ∈ Z, (zeroMult (riemannHeat s) z : ℝ) := by
      exact_mod_cast h1.trans hsum
    linarith

end RHTower.DeBruijn
