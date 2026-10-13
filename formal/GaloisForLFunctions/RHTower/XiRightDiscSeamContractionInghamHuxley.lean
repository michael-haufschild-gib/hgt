import GaloisForLFunctions.RHTower.XiCosineShiftDefectZeroDensity
import GaloisForLFunctions.RHTower.XiRightDiscSeamContractionUniformDensity

/-!
# Seam contraction on all but a power-saving set of right discs, at every abscissa

For `0 < c ≤ ½`, `0 < r < ½` and an abscissa `σ₀` with `½ + c ≤ σ₀ − r`, let `D_n(σ₀, r)` be the
closed disc of radius `r` centred at `σ₀ + i n`.  On a zero-free disc the adjoint Hankel seam of the
`xi` boundary phase is a strict contraction, so the cubic relative index of the disc vanishes.

**Theorem** (`exists_card_badUniformDiscs_le_inghamHuxley`).  For every `0 < ε ≤ 1` there are `C`
and `B` such that for all `X ≥ 1`, uniformly in `σ₀` and `r`, the number of `n ≤ X` whose disc
contains a zero of `xi` is at most

`C (1 + log X)^B X^{(A(½ + c) + ε)(½ − c)}`,

where `A` is the Ingham–Huxley exponent.  Since `A(σ)(1 − σ) < 1` for `σ > ½`, there is `θ < 1`
with at most `X^θ` exceptional discs for large `X` (`exists_card_badUniformDiscs_le_rpow_lt_one`).
Near the line the exponent is `1 − 4c/3 + O(c²)`.

**Proof.**  A zero in `D_n(σ₀, r)` has real part `≥ ½ + c` and ordinate within `r < ½` of `n`, so a
chosen zero copy per exceptional disc is injective.  The copies of zeros with real part `≥ σ` and
ordinate in `[T₀, Y]` lie in the dyadic boxes `[T₀ 2^j, T₀ 2^{j+1}]`, `j ≤ log₂(Y/T₀)`
(`ncard_zeroCopyRange_le`), each bounded by the Ingham–Huxley estimate.
-/

noncomputable section

open Complex Metric Filter

namespace RHTower

/-- Zero copies with real part `≥ σ` and ordinate in `[T₀, Y]`. -/
def zeroCopyRange (σ T₀ Y : ℝ) : Set XiZeroCopy :=
  {q | σ ≤ (q.1 : ℂ).re ∧ T₀ ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ Y}

/-- The copies in `[T₀, Y]` lie in the dyadic boxes `[T₀ 2^j, T₀ 2^{j+1}]`, `j ≤ log₂ ⌊Y/T₀⌋`. -/
theorem zeroCopyRange_subset_iUnion {σ T₀ Y : ℝ} (hT₀ : 0 < T₀) :
    zeroCopyRange σ T₀ Y ⊆
      ⋃ j ∈ Finset.range (Nat.log 2 ⌊Y / T₀⌋₊ + 1), zeroHeightBox σ (T₀ * 2 ^ j) := by
  intro q hq
  obtain ⟨hre, hlo, hhi⟩ := hq
  set y : ℝ := (q.1 : ℂ).im with hy
  set m : ℕ := ⌊y / T₀⌋₊ with hm
  have hy1 : 1 ≤ y / T₀ := by rw [le_div_iff₀ hT₀]; linarith
  have hm1 : 1 ≤ m := by rw [hm]; exact Nat.one_le_floor_iff _ |>.mpr hy1
  set j : ℕ := Nat.log 2 m with hj
  have hpow : 2 ^ j ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hlt : m < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hpowR : (2 : ℝ) ^ j ≤ y / T₀ := by
    calc (2 : ℝ) ^ j = ((2 ^ j : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (m : ℝ) := by exact_mod_cast hpow
      _ ≤ y / T₀ := Nat.floor_le (by linarith)
  have hltR : y / T₀ < (2 : ℝ) ^ (j + 1) := by
    have h1 : y / T₀ < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (m : ℝ) + 1 ≤ (2 : ℝ) ^ (j + 1) := by
      have : m + 1 ≤ 2 ^ (j + 1) := hlt
      exact_mod_cast this
    linarith
  have hjJ : j ≤ Nat.log 2 ⌊Y / T₀⌋₊ := by
    refine Nat.log_mono_right (Nat.floor_le_floor ?_)
    exact div_le_div_of_nonneg_right hhi hT₀.le
  refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
  refine ⟨hre, ?_, ?_⟩
  · rw [← hy]
    have := (le_div_iff₀ hT₀).mp hpowR
    linarith
  · rw [← hy]
    have := (div_lt_iff₀ hT₀).mp hltR
    rw [pow_succ] at this
    linarith

theorem zeroCopyRange_finite (σ T₀ Y : ℝ) (hT₀ : 0 < T₀) : (zeroCopyRange σ T₀ Y).Finite :=
  (Set.Finite.biUnion (Finset.range (Nat.log 2 ⌊Y / T₀⌋₊ + 1)).finite_toSet
    fun j _ => zeroHeightBox_finite σ (T₀ * 2 ^ j)).subset (zeroCopyRange_subset_iUnion hT₀)

/-- **Cumulative Ingham–Huxley count.**  For `½ < σ ≤ 1` and `0 < ε ≤ 1` there are `D, B, T₀` such
that for every `Y ≥ T₀` the zero copies with real part `≥ σ` and ordinate in `[T₀, Y]` number at
most `2D (1 + log Y)^{B+1} Y^{(A(σ) + ε)(1 − σ)}`. -/
theorem exists_ncard_zeroCopyRange_le {σ ε : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ B : ℕ, ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ Y : ℝ, T₀ ≤ Y →
      ((zeroCopyRange σ T₀ Y).ncard : ℝ) ≤
        2 * D * (1 + Real.log Y) ^ (B + 1) * Y ^ ((inghamHuxleyExponent σ + ε) * (1 - σ)) := by
  classical
  obtain ⟨D, hD, B, T₀, hT₀, hbox⟩ := exists_zeroHeightBox_ncard_le_ingham_huxley hσ hσ1 hε hε1
  set E : ℝ := (inghamHuxleyExponent σ + ε) * (1 - σ) with hE
  have hE0 : 0 ≤ E := by
    have hA := (inghamHuxleyExponent_mem hσ).1
    rw [hE]; exact mul_nonneg (by linarith) (by linarith)
  refine ⟨D, hD, B, T₀, hT₀, fun Y hY => ?_⟩
  have hT₀0 : 0 < T₀ := by linarith
  have hY1 : 1 ≤ Y := le_trans hT₀ hY
  set J : ℕ := Nat.log 2 ⌊Y / T₀⌋₊ with hJ
  -- each box parameter lies in `[T₀, Y]`
  have hparam : ∀ j ∈ Finset.range (J + 1), T₀ ≤ T₀ * 2 ^ j ∧ T₀ * 2 ^ j ≤ Y := by
    intro j hj
    have hjJ : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    refine ⟨le_mul_of_one_le_right hT₀0.le (one_le_pow₀ (by norm_num)), ?_⟩
    have hfl : 1 ≤ ⌊Y / T₀⌋₊ := Nat.one_le_floor_iff _ |>.mpr ((one_le_div hT₀0).mpr hY)
    have h2J : 2 ^ J ≤ ⌊Y / T₀⌋₊ := Nat.pow_log_le_self 2 (by omega)
    have h2j : (2 : ℝ) ^ j ≤ Y / T₀ := by
      calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J := pow_le_pow_right₀ (by norm_num) hjJ
        _ = ((2 ^ J : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (⌊Y / T₀⌋₊ : ℝ) := by exact_mod_cast h2J
        _ ≤ Y / T₀ := Nat.floor_le (div_nonneg (by linarith) hT₀0.le)
    rw [mul_comm]
    exact (le_div_iff₀ hT₀0).mp h2j
  -- the number of boxes
  have hJlog : (J : ℝ) ≤ 2 * Real.log Y := by
    by_cases hfl : ⌊Y / T₀⌋₊ = 0
    · rw [hJ, hfl, Nat.log_zero_right]
      simp only [Nat.cast_zero]
      exact mul_nonneg (by norm_num) (Real.log_nonneg hY1)
    · have h2J : 2 ^ J ≤ ⌊Y / T₀⌋₊ := Nat.pow_log_le_self 2 hfl
      have h2JY : (2 : ℝ) ^ J ≤ Y := by
        calc (2 : ℝ) ^ J = ((2 ^ J : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (⌊Y / T₀⌋₊ : ℝ) := by exact_mod_cast h2J
          _ ≤ Y / T₀ := Nat.floor_le (div_nonneg (by linarith) hT₀0.le)
          _ ≤ Y := div_le_self (by linarith) hT₀
      have hlog := Real.log_le_log (by positivity) h2JY
      rw [Real.log_pow] at hlog
      have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      nlinarith [Real.log_nonneg hY1]
  -- the box sum
  have hsub := zeroCopyRange_subset_iUnion (σ := σ) (Y := Y) hT₀0
  rw [← hJ] at hsub
  have hfin : ∀ j, (zeroHeightBox σ (T₀ * 2 ^ j)).Finite := fun j => zeroHeightBox_finite σ _
  set F : Finset XiZeroCopy :=
    (Finset.range (J + 1)).biUnion (fun j => (hfin j).toFinset) with hF
  have hsubF : zeroCopyRange σ T₀ Y ⊆ (F : Set XiZeroCopy) := by
    intro q hq
    obtain ⟨j, hj, hqj⟩ := Set.mem_iUnion₂.mp (hsub hq)
    rw [hF, Finset.coe_biUnion]
    exact Set.mem_iUnion₂.mpr ⟨j, hj, (hfin j).mem_toFinset.mpr hqj⟩
  have hncard : (zeroCopyRange σ T₀ Y).ncard ≤ F.card := by
    have := Set.ncard_le_ncard hsubF F.finite_toSet
    rwa [Set.ncard_coe_finset] at this
  have hFcard : (F.card : ℝ) ≤ ∑ j ∈ Finset.range (J + 1), ((zeroHeightBox σ (T₀ * 2 ^ j)).ncard : ℝ) := by
    have h := Finset.card_biUnion_le (s := Finset.range (J + 1)) (t := fun j => (hfin j).toFinset)
    have h' : (F.card : ℝ) ≤ ∑ j ∈ Finset.range (J + 1), (((hfin j).toFinset.card : ℕ) : ℝ) := by
      rw [hF]; exact_mod_cast h
    refine h'.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [Set.ncard_eq_toFinset_card _ (hfin j)]
  -- each box is at most the box at height `Y`
  set P : ℝ := D * (1 + Real.log Y) ^ B * Y ^ E with hP
  have hP0 : 0 ≤ P := by rw [hP]; have := Real.log_nonneg hY1; positivity
  have hterm : ∀ j ∈ Finset.range (J + 1), ((zeroHeightBox σ (T₀ * 2 ^ j)).ncard : ℝ) ≤ P := by
    intro j hj
    obtain ⟨hlo, hhi⟩ := hparam j hj
    have hx0 : 0 < T₀ * 2 ^ j := by positivity
    have hlog : Real.log (T₀ * 2 ^ j) ≤ Real.log Y := Real.log_le_log hx0 hhi
    have hlog0 : 0 ≤ Real.log (T₀ * 2 ^ j) := Real.log_nonneg (le_trans hT₀ hlo)
    calc ((zeroHeightBox σ (T₀ * 2 ^ j)).ncard : ℝ)
        ≤ D * (1 + Real.log (T₀ * 2 ^ j)) ^ B * (T₀ * 2 ^ j) ^ E := hbox _ hlo
      _ ≤ D * (1 + Real.log Y) ^ B * Y ^ E := by
          have hY0 : 0 ≤ D * (1 + Real.log Y) ^ B := by
            have := Real.log_nonneg hY1; positivity
          gcongr
  have hsum : ∑ j ∈ Finset.range (J + 1), ((zeroHeightBox σ (T₀ * 2 ^ j)).ncard : ℝ) ≤
      (J + 1 : ℝ) * P := by
    calc ∑ j ∈ Finset.range (J + 1), ((zeroHeightBox σ (T₀ * 2 ^ j)).ncard : ℝ)
        ≤ ∑ _j ∈ Finset.range (J + 1), P := Finset.sum_le_sum hterm
      _ = (J + 1 : ℝ) * P := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hJ1 : (J + 1 : ℝ) ≤ 2 * (1 + Real.log Y) := by linarith [Real.log_nonneg hY1]
  calc ((zeroCopyRange σ T₀ Y).ncard : ℝ) ≤ F.card := by exact_mod_cast hncard
    _ ≤ (J + 1 : ℝ) * P := hFcard.trans hsum
    _ ≤ 2 * (1 + Real.log Y) * P := mul_le_mul_of_nonneg_right hJ1 hP0
    _ = 2 * D * (1 + Real.log Y) ^ (B + 1) * Y ^ E := by rw [hP]; ring

/-- **Exceptional right discs obey the Ingham–Huxley density bound**, uniformly in the abscissa
and the radius. -/
theorem exists_card_badUniformDiscs_le_inghamHuxley {c ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ B : ℕ, ∀ X : ℕ, 1 ≤ X → ∀ {σ₀ r : ℝ}, 0 < r → r < 1 / 2 →
      1 / 2 + c ≤ σ₀ - r →
      ((badUniformDiscs σ₀ r X).card : ℝ) ≤
        C * (1 + Real.log X) ^ B * (X : ℝ) ^ ((inghamHuxleyExponent (1 / 2 + c) + ε) * (1 / 2 - c)) := by
  classical
  set σ : ℝ := 1 / 2 + c with hσ
  have hσ1 : 1 / 2 < σ := by rw [hσ]; linarith
  have hσ2 : σ ≤ 1 := by rw [hσ]; linarith
  obtain ⟨D, hD, B, T₀, hT₀, hcount⟩ := exists_ncard_zeroCopyRange_le hσ1 hσ2 hε hε1
  set E : ℝ := (inghamHuxleyExponent σ + ε) * (1 - σ) with hE
  have hE' : (inghamHuxleyExponent (1 / 2 + c) + ε) * (1 / 2 - c) = E := by
    rw [hE, hσ]; ring
  rw [hE']
  have hE0 : 0 ≤ E := by
    have hA := (inghamHuxleyExponent_mem hσ1).1
    rw [hE]; exact mul_nonneg (by linarith) (by linarith)
  have hEle : E ≤ 2 := by
    have hA := (inghamHuxleyExponent_mem hσ1).2
    rw [hE]; nlinarith
  set N₀ : ℕ := ⌈T₀⌉₊ + 1 with hN₀
  refine ⟨N₀ + 2 * D * 2 ^ (B + 1) * 4, by positivity, B + 1, fun X hX σ₀ r hr0 hr hlow => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  set S := badUniformDiscs σ₀ r X with hS
  set Slow := S.filter (fun n => n < N₀) with hSlow
  set Shigh := S.filter (fun n => ¬ n < N₀) with hShigh
  have hsplit : S.card = Slow.card + Shigh.card := (Finset.card_filter_add_card_filter_not _).symm
  -- low discs
  have hlow_card : Slow.card ≤ N₀ := by
    calc Slow.card ≤ (Finset.range N₀).card := Finset.card_le_card fun n hn =>
          Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
      _ = N₀ := Finset.card_range _
  -- high discs: one zero copy each
  have hchoose : ∀ n ∈ Shigh, ∃ q : XiZeroCopy, (q.1 : ℂ) ∈ closedBall (uniformDiscCenter σ₀ n) r := by
    intro n hn
    obtain ⟨z, hz, hxz⟩ := (mem_badUniformDiscs.mp (Finset.mem_filter.mp hn).1).2
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxz
    exact ⟨q, hq ▸ hz⟩
  choose! w hw using hchoose
  have hinj : Set.InjOn w (Shigh : Set ℕ) := by
    intro n hn m hm hnm
    obtain ⟨-, -, hn1, hn2⟩ := re_im_of_mem_uniformDisc (hw n hn)
    obtain ⟨-, -, hm1, hm2⟩ := re_im_of_mem_uniformDisc (hw m hm)
    rw [hnm] at hn1 hn2
    have h3 : (n : ℤ) - m < 1 := by
      have : ((n : ℝ) - m) < 1 := by linarith
      exact_mod_cast this
    have h4 : (m : ℤ) - n < 1 := by
      have : ((m : ℝ) - n) < 1 := by linarith
      exact_mod_cast this
    omega
  have hmaps : ∀ n ∈ Shigh, w n ∈ zeroCopyRange σ T₀ (X + 1) := by
    intro n hn
    obtain ⟨hr1, -, hi1, hi2⟩ := re_im_of_mem_uniformDisc (hw n hn)
    have hnX : n ≤ X := (Finset.mem_Icc.mp (mem_badUniformDiscs.mp (Finset.mem_filter.mp hn).1).1).2
    have hnN : N₀ ≤ n := not_lt.mp (Finset.mem_filter.mp hn).2
    have hnN' : (N₀ : ℝ) ≤ n := by exact_mod_cast hnN
    have hT₀N : T₀ + 1 ≤ (N₀ : ℝ) := by
      rw [hN₀]; push_cast; linarith [Nat.le_ceil T₀]
    have hnXR : (n : ℝ) ≤ X := by exact_mod_cast hnX
    refine ⟨by linarith, by linarith, by linarith⟩
  have hhigh_card : (Shigh.card : ℝ) ≤ (zeroCopyRange σ T₀ (X + 1)).ncard := by
    have himg : ((Shigh.image w : Finset XiZeroCopy) : Set XiZeroCopy) ⊆
        zeroCopyRange σ T₀ (X + 1) := by
      intro q hq
      obtain ⟨n, hn, rfl⟩ := Finset.mem_coe.mp hq |> Finset.mem_image.mp
      exact hmaps n hn
    have hfinR := zeroCopyRange_finite σ T₀ (X + 1) (by linarith)
    have h := Set.ncard_le_ncard himg hfinR
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj] at h
    exact_mod_cast h
  -- the cumulative count at height `X + 1`
  set L : ℝ := (1 + Real.log X) ^ (B + 1) * (X : ℝ) ^ E with hL
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith))
      (Real.one_le_rpow hX1 hE0)
  have hR : ((zeroCopyRange σ T₀ (X + 1)).ncard : ℝ) ≤ 2 * D * 2 ^ (B + 1) * 4 * L := by
    by_cases hYT : T₀ ≤ (X : ℝ) + 1
    · have h := hcount _ hYT
      have hXp : (0 : ℝ) < X + 1 := by linarith
      have hlogX1 : 1 + Real.log ((X : ℝ) + 1) ≤ 2 * (1 + Real.log X) := by
        have h2X : (X : ℝ) + 1 ≤ 2 * X := by linarith
        have := Real.log_le_log hXp h2X
        rw [Real.log_mul (by norm_num) (by linarith)] at this
        have hl2 : Real.log 2 ≤ 1 := by
          have := Real.log_two_lt_d9; linarith
        linarith
      have hpowX : ((X : ℝ) + 1) ^ E ≤ 4 * (X : ℝ) ^ E := by
        calc ((X : ℝ) + 1) ^ E ≤ (2 * (X : ℝ)) ^ E := Real.rpow_le_rpow hXp.le (by linarith) hE0
          _ = 2 ^ E * (X : ℝ) ^ E := Real.mul_rpow (by norm_num) (by linarith)
          _ ≤ 4 * (X : ℝ) ^ E := by
              gcongr
              calc (2 : ℝ) ^ E ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hEle
                _ = 4 := by norm_num
      have hlogpos : 0 ≤ 1 + Real.log ((X : ℝ) + 1) := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ X + 1 by linarith); linarith
      calc ((zeroCopyRange σ T₀ (X + 1)).ncard : ℝ)
          ≤ 2 * D * (1 + Real.log ((X : ℝ) + 1)) ^ (B + 1) * ((X : ℝ) + 1) ^ E := h
        _ ≤ 2 * D * (2 * (1 + Real.log X)) ^ (B + 1) * (4 * (X : ℝ) ^ E) := by
            gcongr
        _ = 2 * D * 2 ^ (B + 1) * 4 * L := by rw [hL, mul_pow]; ring
    · have hempty : zeroCopyRange σ T₀ (X + 1) = ∅ := by
        ext q
        simp only [zeroCopyRange, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, h1, h2⟩
        exact hYT (h1.trans h2)
      rw [hempty, Set.ncard_empty, Nat.cast_zero]
      have : 0 ≤ L := by linarith
      positivity
  have hN₀L : (N₀ : ℝ) ≤ N₀ * L := le_mul_of_one_le_right (by positivity) hL1
  calc ((badUniformDiscs σ₀ r X).card : ℝ) = Slow.card + Shigh.card := by
        rw [← hS, hsplit]; push_cast; ring
    _ ≤ N₀ + 2 * D * 2 ^ (B + 1) * 4 * L := by
        have : (Slow.card : ℝ) ≤ N₀ := by exact_mod_cast hlow_card
        linarith [hhigh_card.trans hR]
    _ ≤ (N₀ + 2 * D * 2 ^ (B + 1) * 4) * L := by nlinarith
    _ = (N₀ + 2 * D * 2 ^ (B + 1) * 4) * (1 + Real.log X) ^ (B + 1) * (X : ℝ) ^ E := by
        rw [hL]; ring

/-- **Power saving.**  For every `0 < c ≤ ½` there is `θ < 1` such that, for all large `X` and
uniformly in `σ₀, r` with `0 < r < ½` and `½ + c ≤ σ₀ − r`, at most `X^θ` of the discs
`D_n(σ₀, r)`, `n ≤ X`, contain a zero of `xi`. -/
theorem exists_card_badUniformDiscs_le_rpow_lt_one {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2) :
    ∃ θ : ℝ, θ < 1 ∧ ∀ᶠ X : ℕ in atTop, ∀ {σ₀ r : ℝ}, 0 < r → r < 1 / 2 →
      1 / 2 + c ≤ σ₀ - r → ((badUniformDiscs σ₀ r X).card : ℝ) ≤ (X : ℝ) ^ θ := by
  set σ : ℝ := 1 / 2 + c with hσ
  have hσ1 : 1 / 2 < σ := by rw [hσ]; linarith
  set g : ℝ := 1 - inghamHuxleyExponent σ * (1 - σ) with hg
  have hg0 : 0 < g := by rw [hg]; linarith [inghamHuxleyExponent_mul_lt_one hσ1]
  set ε : ℝ := min 1 g with hε
  have hε0 : 0 < ε := lt_min one_pos hg0
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨C, hC, B, hbound⟩ := exists_card_badUniformDiscs_le_inghamHuxley hc hc1 hε0 hε1
  set E : ℝ := (inghamHuxleyExponent (1 / 2 + c) + ε) * (1 / 2 - c) with hE
  have hEg : E ≤ 1 - g / 2 := by
    have hεg : ε ≤ g := min_le_right _ _
    have h1σ : 1 / 2 - c = 1 - σ := by rw [hσ]; ring
    have h12 : 1 - σ ≤ 1 / 2 := by linarith
    have h0 : 0 ≤ 1 - σ := by rw [hσ]; linarith
    rw [hE, h1σ, ← hσ]
    have : ε * (1 - σ) ≤ g / 2 := by nlinarith
    nlinarith
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (eventually_const_mul_polylog_le_rpow B (c := g / 4) (by positivity) C)
  refine ⟨1 - g / 4, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈T₂⌉₊] with X hX1 hXT
  intro σ₀ r hr0 hr hlow
  have hX1R : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hXT₂ : T₂ ≤ (X : ℝ) := (Nat.le_ceil T₂).trans (by exact_mod_cast hXT)
  have hpoly := hT₂ X hXT₂
  calc ((badUniformDiscs σ₀ r X).card : ℝ) ≤ C * (1 + Real.log X) ^ B * (X : ℝ) ^ E :=
        hbound X hX1 hr0 hr hlow
    _ ≤ (X : ℝ) ^ (g / 4) * (X : ℝ) ^ (1 - g / 2) :=
        mul_le_mul hpoly (Real.rpow_le_rpow_of_exponent_le hX1R hEg) (by positivity)
          (by positivity)
    _ = (X : ℝ) ^ (1 - g / 4) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf

end RHTower
