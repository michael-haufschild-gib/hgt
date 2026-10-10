import GaloisForLFunctions.RHTower.XiRightDiscSeamContractionUniformDensity
import GaloisForLFunctions.RHTower.SelbergExponentialNearLineDensityLong
import GaloisForLFunctions.RHTower.XiHorizontalSliceDensityFromMeanSquare

/-!
# Seam contraction on almost every right disc, at every abscissa right of the line

For `0 < c ≤ 1/4`, `0 < r < 1/2` and an abscissa `σ₀` with `½ + c + r ≤ σ₀` and `σ₀ + r < 1`, let
`D_n(σ₀, r)` be the closed disc of radius `r` centred at `σ₀ + i n`. On a zero-free disc the adjoint
Hankel seam of the `xi` boundary phase is a strict contraction
(`xiDisc_adjointSeam_lt_one_of_ne_zero`). The number of `n ≤ X` whose disc contains a zero of `xi`
is at most `C(c)(X^{1 − c/28} + (1 + log X)²)`, which is `o(X)`
(`exists_card_badUniformDiscs_le_nearLine`).

The input is Selberg's exponential near-line density at the critical scale
(`exists_selberg_exponential_nearLine_zeroDensity_long`): on a window of heights inside
`[U/4, U/2]` the zeros with `Re ρ ≥ ½ + 2a/log U` number at most
`(log U/(2πa))((U/4)Ae^{−a/14} + K log U)`. With `a = (c/2) log U` this is
`(1/(πc))((U/4)AU^{−c/28} + K log U)` (`exists_nearLine_window_card_le`). The heights `n ∈ [2^k, 2^{k+1})`
are covered by the two windows `U = (7/2)2^k` and `U = 5·2^k`. Summing over `k ≤ log₂ X` gives the
geometric bound `Σ (2^k)^{1−c/28} ≤ 4X^{1−c/28}`.
-/

open Complex Metric Filter Set

namespace RHTower

noncomputable section

/-! ## One window -/

/-- **Zeros right of `½ + c` in one window.** For all large `U`, every finite set of zeros of `ζ`
with real part in `[½ + c, 1]` and height in `[U/4 + 1, U/2 − 1]` has at most
`(1/(πc))((U/4)AU^{−c/28} + K log U)` elements. -/
theorem exists_nearLine_window_card_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ U in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 / 4 →
      2 / c ≤ Real.log U → ∀ Z : Finset ℂ,
        (∀ z ∈ Z, riemannZeta z = 0 ∧ 1 / 2 + c ≤ z.re ∧ z.re ≤ 1 ∧
          U / 4 + 1 ≤ z.im ∧ z.im ≤ U / 2 - 1) →
        Real.pi * c * Z.card ≤
          U / 4 * A * Real.exp (-(c / 28 * Real.log U)) + K * Real.log U := by
  classical
  obtain ⟨A, K, hA, hK, hev⟩ := exists_selberg_exponential_nearLine_zeroDensity_long
  refine ⟨A, K, hA, hK, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (Real.exp 8)] with U hU hU8
  intro c hc hc4 hcL Z hZ
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos 8) hU8
  have hU9 : 9 ≤ U := le_trans (by linarith [Real.add_one_le_exp (8 : ℝ)]) hU8
  have hL8 : 8 ≤ Real.log U := by
    rw [Real.le_log_iff_exp_le hU0]; exact hU8
  set L := Real.log U with hLdef
  set a := c * L / 2 with hadef
  have hcL2 : 2 ≤ c * L := by
    rw [div_le_iff₀ hc] at hcL; linarith
  have ha1 : 1 ≤ a := by rw [hadef]; linarith
  have ha2 : 2 * a + 2 ≤ L := by rw [hadef]; nlinarith
  have hL0 : 0 < L := by linarith
  have h2aL : 2 * a / L = c := by rw [hadef]; field_simp
  have haL : a / L = c / 2 := by rw [hadef]; field_simp
  set Zall := Sieve.zetaResidueUnitClosedRectangleZeros
    ((1 / 2 : ℂ) + (T₁ : ℂ) * I) ((15 / 2 : ℂ) + (T₂ : ℂ) * I) with hZall
  have hT₁0 : 0 < T₁ := by linarith [hT₁.1]
  have hmem : ∀ z : ℂ, z ∈ Zall ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
    intro z
    rw [hZall, Sieve.mem_zetaResidueUnitClosedRectangleZeros]
    have hre1 : ((1 / 2 : ℂ) + (T₁ : ℂ) * I).re = 1 / 2 := by simp
    have hre2 : ((15 / 2 : ℂ) + (T₂ : ℂ) * I).re = 15 / 2 := by simp
    have him1 : ((1 / 2 : ℂ) + (T₁ : ℂ) * I).im = T₁ := by simp
    have him2 : ((15 / 2 : ℂ) + (T₂ : ℂ) * I).im = T₂ := by simp
    rw [hre1, hre2, him1, him2]
    constructor
    · rintro ⟨hR, hz⟩
      refine ⟨hR, ?_⟩
      have hne : z ≠ 1 := by
        intro h
        rw [h, Complex.mem_reProdIm] at hR
        have h2 := hR.2
        simp only [Complex.one_im, Set.mem_uIcc] at h2
        rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> linarith [hT₁.1, hT₂.1, hU9]
      rw [zetaResidueUnit, Function.update_of_ne hne] at hz
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact h
    · rintro ⟨hR, hz⟩
      exact ⟨hR, zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero hz⟩
  have h := hbound a ha1 ha2 Zall hmem
  rw [h2aL, haL] at h
  -- `Z` sits inside the filtered zero set
  have hsub : Z ⊆ Zall.filter (fun w => 1 / 2 + c ≤ w.re) := by
    intro z hz
    obtain ⟨hz0, hre1, hre2, him1, him2⟩ := hZ z hz
    rw [Finset.mem_filter, hmem]
    refine ⟨⟨?_, hz0⟩, hre1⟩
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (show (1 / 2 : ℝ) ≤ 15 / 2 by norm_num),
      Set.uIcc_of_le (by linarith [hT₁.2, hT₂.1, hU9] : T₁ ≤ T₂)]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith
    · linarith
    · linarith [hT₁.2]
    · linarith [hT₂.1]
  have hcard : (Z.card : ℝ) ≤ ∑ w ∈ Zall.filter (fun w => 1 / 2 + c ≤ w.re),
      ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
    calc (Z.card : ℝ) = ∑ _w ∈ Z, (1 : ℝ) := by rw [Finset.sum_const, nsmul_one]
      _ ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
          refine Finset.sum_le_sum fun w hw => ?_
          obtain ⟨hz0, -, -, him1, -⟩ := hZ w hw
          have hne : w ≠ 1 := by
            intro h; rw [h, Complex.one_im] at him1; linarith
          exact_mod_cast one_le_analyticOrderAt_riemannZeta_toNat hne hz0
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hT : T₂ - T₁ ≤ U / 4 := by linarith [hT₁.1, hT₂.2]
  have hexp : Real.exp (-(a / 14)) = Real.exp (-(c / 28 * L)) := by
    congr 1; rw [hadef]; ring
  rw [hexp] at h
  have hE : 0 ≤ A * Real.exp (-(c / 28 * L)) := by positivity
  have h3 : (T₂ - T₁) * (A * Real.exp (-(c / 28 * L))) ≤ U / 4 * A * Real.exp (-(c / 28 * L)) := by
    rw [mul_assoc (U / 4)]; exact mul_le_mul_of_nonneg_right hT hE
  have h4 : Real.pi * c * Z.card ≤ 2 * Real.pi * ((c / 2) * ∑ w ∈ Zall.filter
      (fun w => 1 / 2 + c ≤ w.re), ((analyticOrderAt riemannZeta w).toNat : ℝ)) := by
    have : 2 * Real.pi * ((c / 2) * ∑ w ∈ Zall.filter (fun w => 1 / 2 + c ≤ w.re),
        ((analyticOrderAt riemannZeta w).toNat : ℝ))
        = Real.pi * c * ∑ w ∈ Zall.filter (fun w => 1 / 2 + c ≤ w.re),
          ((analyticOrderAt riemannZeta w).toNat : ℝ) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hcard (by positivity)
  linarith

/-! ## Exceptional discs in one height range -/

/-- **Exceptional discs in one height range.** If every set of zeros right of `½ + c` with heights in
`[U/4 + 1, U/2 − 1]` satisfies `πc|Z| ≤ B`, and `[m₁ − ½, m₂ + ½] ⊆ [U/4 + 1, U/2 − 1]`, then the
exceptional discs with `m₁ ≤ n ≤ m₂` satisfy the same bound. Distinct discs are separated by more
than their diameter, so a chosen zero per disc is injective. -/
theorem card_badUniformDiscs_range_le {B U c σ₀ r : ℝ} {X m₁ m₂ : ℕ}
    (hwin : ∀ Z : Finset ℂ, (∀ z ∈ Z, riemannZeta z = 0 ∧ 1 / 2 + c ≤ z.re ∧ z.re ≤ 1 ∧
        U / 4 + 1 ≤ z.im ∧ z.im ≤ U / 2 - 1) → Real.pi * c * Z.card ≤ B)
    (hc : 0 ≤ c) (hr0 : 0 < r) (_hr : r < 1 / 2) (hlow : 1 / 2 + c ≤ σ₀ - r) (hhigh : σ₀ + r < 1)
    (h1 : U / 4 + 1 ≤ (m₁ : ℝ) - 1 / 2) (h2 : (m₂ : ℝ) + 1 / 2 ≤ U / 2 - 1) :
    Real.pi * c * ((badUniformDiscs σ₀ r X).filter (fun n => m₁ ≤ n ∧ n ≤ m₂)).card ≤ B := by
  classical
  set S := (badUniformDiscs σ₀ r X).filter (fun n => m₁ ≤ n ∧ n ≤ m₂) with hS
  have hchoose : ∀ n ∈ S, ∃ z ∈ closedBall (uniformDiscCenter σ₀ n) r, xi z = 0 := fun n hn =>
    (mem_badUniformDiscs.mp (Finset.mem_filter.mp hn).1).2
  choose! w hwball hwzero using hchoose
  have hinj : Set.InjOn w (S : Set ℕ) := by
    intro n hn m hm hnm
    obtain ⟨-, -, hn1, hn2⟩ := re_im_of_mem_uniformDisc (hwball n hn)
    obtain ⟨-, -, hm1, hm2⟩ := re_im_of_mem_uniformDisc (hwball m hm)
    rw [hnm] at hn1 hn2
    have h3 : (n : ℤ) - m < 1 := by
      have : ((n : ℝ) - m) < 1 := by linarith
      exact_mod_cast this
    have h4 : (m : ℤ) - n < 1 := by
      have : ((m : ℝ) - n) < 1 := by linarith
      exact_mod_cast this
    omega
  have hcard : (S.image w).card = S.card := Finset.card_image_of_injOn hinj
  have hZ : ∀ z ∈ S.image w, riemannZeta z = 0 ∧ 1 / 2 + c ≤ z.re ∧ z.re ≤ 1 ∧
      U / 4 + 1 ≤ z.im ∧ z.im ≤ U / 2 - 1 := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hr1, hr2, hi1, hi2⟩ := re_im_of_mem_uniformDisc (hwball n hn)
    have hnm := (Finset.mem_filter.mp hn).2
    have hn1 : (m₁ : ℝ) ≤ n := by exact_mod_cast hnm.1
    have hn2 : (n : ℝ) ≤ m₂ := by exact_mod_cast hnm.2
    have hre0 : 0 < (w n).re := by linarith
    have hne1 : w n ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hr2; linarith
    refine ⟨(xi_eq_zero_iff hre0 hne1).mp (hwzero n hn), by linarith, by linarith,
      by linarith, by linarith⟩
  have := hwin (S.image w) hZ
  rwa [hcard] at this

/-! ## A geometric sum -/

/-- `Σ_{k ≤ m} (2^k)^θ ≤ 4 (2^m)^θ` for `½ ≤ θ`. -/
theorem sum_range_two_pow_rpow_le {θ : ℝ} (hθ : 1 / 2 ≤ θ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), ((2 : ℝ) ^ k) ^ θ ≤ 4 * ((2 : ℝ) ^ m) ^ θ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hsplit : ((2 : ℝ) ^ (m + 1)) ^ θ = (2 : ℝ) ^ θ * ((2 : ℝ) ^ m) ^ θ := by
      rw [pow_succ, mul_comm, Real.mul_rpow (by norm_num) (by positivity)]
    have h2θ : (4 : ℝ) / 3 ≤ (2 : ℝ) ^ θ := by
      have h1 : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ (2 : ℝ) ^ θ :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ
      have h2 : (4 : ℝ) / 3 ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      linarith
    have hP : 0 ≤ ((2 : ℝ) ^ m) ^ θ := by positivity
    rw [hsplit]
    nlinarith

/-! ## Summing the windows -/

/-- The window bound at `U ≤ 5P`, `P ≥ 1`: `(U/4)AU^{−c/28} + K log U ≤ (5/4)AP^{1−c/28} + K log(5P)`. -/
theorem nearLine_window_bound_le {A K c U P : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hc : 0 < c)
    (hc4 : c ≤ 1 / 4) (hU : 0 < U) (hUP : U ≤ 5 * P) (hP : 1 ≤ P) :
    U / 4 * A * Real.exp (-(c / 28 * Real.log U)) + K * Real.log U ≤
      5 / 4 * A * P ^ (1 - c / 28) + K * Real.log (5 * P) := by
  have hθ0 : 0 ≤ 1 - c / 28 := by linarith
  have hθ1 : 1 - c / 28 ≤ 1 := by linarith
  have hpow : U * Real.exp (-(c / 28 * Real.log U)) = U ^ (1 - c / 28) := by
    rw [Real.rpow_def_of_pos hU, show Real.log U * (1 - c / 28)
      = Real.log U + -(c / 28 * Real.log U) by ring, Real.exp_add, Real.exp_log hU]
  have h1 : U ^ (1 - c / 28) ≤ (5 * P) ^ (1 - c / 28) :=
    Real.rpow_le_rpow hU.le hUP hθ0
  have h2 : (5 * P) ^ (1 - c / 28) ≤ 5 * P ^ (1 - c / 28) := by
    rw [Real.mul_rpow (by norm_num) (by linarith)]
    have : (5 : ℝ) ^ (1 - c / 28) ≤ 5 := by
      calc (5 : ℝ) ^ (1 - c / 28) ≤ (5 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
        _ = 5 := Real.rpow_one 5
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hlog : Real.log U ≤ Real.log (5 * P) := Real.log_le_log hU hUP
  have e : U / 4 * A * Real.exp (-(c / 28 * Real.log U))
      = A / 4 * (U * Real.exp (-(c / 28 * Real.log U))) := by ring
  rw [e, hpow]
  have h3 : A / 4 * U ^ (1 - c / 28) ≤ 5 / 4 * A * P ^ (1 - c / 28) := by
    have := mul_le_mul_of_nonneg_left (h1.trans h2) (show 0 ≤ A / 4 by positivity)
    linarith
  have h4 := mul_le_mul_of_nonneg_left hlog hK
  linarith

/-- The lower half `[2^k, 2^k + 2^{k−1}]` of the dyadic block `k`. -/
def dyadicLowerHalf (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  S.filter (fun n => 2 ^ k ≤ n ∧ n ≤ 2 ^ k + 2 ^ (k - 1))

/-- The upper half `[2^k + 2^{k−1} + 1, 2^{k+1} − 1]` of the dyadic block `k`. -/
def dyadicUpperHalf (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  S.filter (fun n => 2 ^ k + 2 ^ (k - 1) + 1 ≤ n ∧ n ≤ 2 ^ (k + 1) - 1)

/-- **Dyadic covering.** A set of positive integers `≤ X` has at most
`2^{k₁} + Σ_{k₁ ≤ k ≤ log₂ X} (|lower half k| + |upper half k|)` elements. -/
theorem card_le_dyadic_halves {S : Finset ℕ} {X : ℕ} (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ X) (k₁ : ℕ) :
    S.card ≤ 2 ^ k₁ + ∑ k ∈ Finset.Icc k₁ (Nat.log 2 X),
      ((dyadicLowerHalf S k).card + (dyadicUpperHalf S k).card) := by
  classical
  have hcover : S ⊆ S.filter (fun n => n < 2 ^ k₁) ∪
      (Finset.Icc k₁ (Nat.log 2 X)).biUnion (fun k => dyadicLowerHalf S k ∪ dyadicUpperHalf S k) := by
    intro n hn
    obtain ⟨hn1, hnX⟩ := hS n hn
    rcases lt_or_ge n (2 ^ k₁) with hlt | hge
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn, hlt⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨Nat.log 2 n, ?_, ?_⟩)
      · rw [Finset.mem_Icc]
        exact ⟨Nat.le_log_of_pow_le (by norm_num) hge, Nat.log_mono_right hnX⟩
      · have hn0 : n ≠ 0 := by omega
        have hlo := Nat.pow_log_le_self 2 hn0
        have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
        set j := Nat.log 2 n
        rcases le_or_gt n (2 ^ j + 2 ^ (j - 1)) with h1 | h1
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn, hlo, h1⟩)
        · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, h1, ?_⟩)
          rw [Nat.succ_eq_add_one] at hhi
          omega
  have h6 : (S.filter (fun n => n < 2 ^ k₁)).card ≤ 2 ^ k₁ := by
    calc (S.filter (fun n => n < 2 ^ k₁)).card ≤ (Finset.range (2 ^ k₁)).card :=
          Finset.card_le_card fun n hn => Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
      _ = 2 ^ k₁ := Finset.card_range _
  calc S.card ≤ _ := Finset.card_le_card hcover
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ 2 ^ k₁ + ∑ k ∈ Finset.Icc k₁ (Nat.log 2 X),
          (dyadicLowerHalf S k ∪ dyadicUpperHalf S k).card :=
        Nat.add_le_add h6 Finset.card_biUnion_le
    _ ≤ _ := Nat.add_le_add_left (Finset.sum_le_sum fun k _ => Finset.card_union_le _ _) _

/-- **One dyadic block near the line.** If the window property holds for every `U ≥ V`, then for
`2^k > max(V, 16)` the exceptional discs in block `k` satisfy
`πc(|lower| + |upper|) ≤ (5/2)A(2^k)^{1−c/28} + 2K log(5·2^k)`. -/
theorem dyadic_block_badUniformDiscs_le {A K c V σ₀ r : ℝ} {X k : ℕ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hc : 0 < c) (hc4 : c ≤ 1 / 4) (hV16 : 16 ≤ V)
    (hwin : ∀ U : ℝ, V ≤ U → ∀ Z : Finset ℂ, (∀ z ∈ Z, riemannZeta z = 0 ∧ 1 / 2 + c ≤ z.re ∧
      z.re ≤ 1 ∧ U / 4 + 1 ≤ z.im ∧ z.im ≤ U / 2 - 1) →
      Real.pi * c * Z.card ≤ U / 4 * A * Real.exp (-(c / 28 * Real.log U)) + K * Real.log U)
    (hr0 : 0 < r) (hr : r < 1 / 2) (hlow : 1 / 2 + c ≤ σ₀ - r) (hhigh : σ₀ + r < 1)
    (hPV : V < (2 : ℝ) ^ k) :
    Real.pi * c * ((dyadicLowerHalf (badUniformDiscs σ₀ r X) k).card : ℝ)
      + Real.pi * c * ((dyadicUpperHalf (badUniformDiscs σ₀ r X) k).card : ℝ)
      ≤ 5 / 2 * A * ((2 : ℝ) ^ k) ^ (1 - c / 28) + 2 * K * Real.log (5 * (2 : ℝ) ^ k) := by
  set P : ℝ := (2 : ℝ) ^ k with hP
  have hP16 : 16 < P := by linarith
  have hk0 : k ≠ 0 := by
    intro h; rw [hP, h, pow_zero] at hP16; norm_num at hP16
  have hhalf : (((2 : ℕ) ^ (k - 1) : ℕ) : ℝ) = P / 2 := by
    have : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    push_cast; rw [hP, this]; ring
  have hcast1 : (((2 : ℕ) ^ k : ℕ) : ℝ) = P := by push_cast; rfl
  have hcast2 : (((2 : ℕ) ^ k + 2 ^ (k - 1) : ℕ) : ℝ) = P + P / 2 := by
    rw [Nat.cast_add, hcast1, hhalf]
  have hcast3 : (((2 : ℕ) ^ k + 2 ^ (k - 1) + 1 : ℕ) : ℝ) = P + P / 2 + 1 := by
    rw [Nat.cast_add, hcast2, Nat.cast_one]
  have hcast4 : (((2 : ℕ) ^ (k + 1) - 1 : ℕ) : ℝ) = 2 * P - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, pow_succ,
      hP]; ring
  have hP1 : 1 ≤ P := by linarith
  have hA1 := card_badUniformDiscs_range_le (B := 7 * P / 2 / 4 * A
      * Real.exp (-(c / 28 * Real.log (7 * P / 2))) + K * Real.log (7 * P / 2))
    (X := X) (m₁ := 2 ^ k) (m₂ := 2 ^ k + 2 ^ (k - 1))
    (hwin (7 * P / 2) (by linarith)) hc.le hr0 hr hlow hhigh
    (by rw [hcast1]; linarith) (by rw [hcast2]; linarith)
  have hA2 := card_badUniformDiscs_range_le (B := 5 * P / 4 * A
      * Real.exp (-(c / 28 * Real.log (5 * P))) + K * Real.log (5 * P))
    (X := X) (m₁ := 2 ^ k + 2 ^ (k - 1) + 1) (m₂ := 2 ^ (k + 1) - 1)
    (hwin (5 * P) (by linarith)) hc.le hr0 hr hlow hhigh
    (by rw [hcast3]; linarith) (by rw [hcast4]; linarith)
  have hb1 := nearLine_window_bound_le hA hK hc hc4 (U := 7 * P / 2) (P := P)
    (by linarith) (by linarith) hP1
  have hb2 := nearLine_window_bound_le hA hK hc hc4 (U := 5 * P) (P := P)
    (by linarith) le_rfl hP1
  unfold dyadicLowerHalf dyadicUpperHalf
  linarith

/-- The two sums over dyadic blocks up to `log₂ X`. -/
theorem dyadic_sums_le {A K θ : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hθ : 1 / 2 ≤ θ) {X : ℕ}
    (hX1 : 1 ≤ X) (k₁ : ℕ) :
    ∑ k ∈ Finset.Icc k₁ (Nat.log 2 X),
        (5 / 2 * A * ((2 : ℝ) ^ k) ^ θ + 2 * K * Real.log (5 * (2 : ℝ) ^ k))
      ≤ 10 * A * (X : ℝ) ^ θ + 8 * K * (1 + Real.log X) ^ 2 := by
  set m := Nat.log 2 X with hm
  have h2m : ((2 : ℝ) ^ m) ≤ X := by
    have := Nat.pow_log_le_self 2 (show X ≠ 0 by omega)
    exact_mod_cast this
  have hLX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX1)
  have hm_le : (m : ℝ) ≤ 2 * Real.log X := by
    have h1 : (m : ℝ) * Real.log 2 ≤ Real.log X := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2m
    have hl2 := Real.log_two_gt_d9
    nlinarith
  have hgeom : ∑ k ∈ Finset.Icc k₁ m, ((2 : ℝ) ^ k) ^ θ ≤ 4 * (X : ℝ) ^ θ := by
    calc ∑ k ∈ Finset.Icc k₁ m, ((2 : ℝ) ^ k) ^ θ
        ≤ ∑ k ∈ Finset.range (m + 1), ((2 : ℝ) ^ k) ^ θ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => by positivity)
          rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
      _ ≤ 4 * ((2 : ℝ) ^ m) ^ θ := sum_range_two_pow_rpow_le hθ m
      _ ≤ 4 * (X : ℝ) ^ θ := by
          have := Real.rpow_le_rpow (by positivity) h2m (by linarith : (0 : ℝ) ≤ θ)
          linarith
  have h5 : Real.log 5 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have hlogsum : ∑ k ∈ Finset.Icc k₁ m, Real.log (5 * (2 : ℝ) ^ k)
      ≤ (m + 1) * (2 + Real.log X) := by
    calc ∑ k ∈ Finset.Icc k₁ m, Real.log (5 * (2 : ℝ) ^ k)
        ≤ ∑ _k ∈ Finset.Icc k₁ m, (2 + Real.log X) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Finset.mem_Icc] at hk
          have hkm : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hk.2
          rw [Real.log_mul (by norm_num) (by positivity)]
          have := Real.log_le_log (by positivity) (hkm.trans h2m)
          linarith
      _ = ((Finset.Icc k₁ m).card : ℝ) * (2 + Real.log X) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m + 1) * (2 + Real.log X) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          rw [Nat.card_Icc]
          have : m + 1 - k₁ ≤ m + 1 := Nat.sub_le _ _
          exact_mod_cast this
  have hq : ((m : ℝ) + 1) * (2 + Real.log X) ≤ 4 * (1 + Real.log X) ^ 2 := by nlinarith
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e1 := mul_le_mul_of_nonneg_left hgeom (show 0 ≤ 5 / 2 * A by positivity)
  have e2 := mul_le_mul_of_nonneg_left (hlogsum.trans hq) (show 0 ≤ 2 * K by positivity)
  linarith

/-- **Exceptional right discs near the line are `o(X)`.** For `0 < c ≤ 1/4` there is `C` such that
for all large `X` and all `0 < r < ½`, `½ + c ≤ σ₀ − r`, `σ₀ + r < 1`, at most
`C(X^{1 − c/28} + (1 + log X)²)` of the discs `D_n(σ₀, r)`, `n ≤ X`, contain a zero of `xi`. -/
theorem exists_card_badUniformDiscs_le_nearLine {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℕ in atTop, ∀ {σ₀ r : ℝ}, 0 < r → r < 1 / 2 →
      1 / 2 + c ≤ σ₀ - r → σ₀ + r < 1 →
      ((badUniformDiscs σ₀ r X).card : ℝ) ≤
        C * ((X : ℝ) ^ (1 - c / 28) + (1 + Real.log X) ^ 2) := by
  classical
  obtain ⟨A, K, hA, hK, hev⟩ := exists_nearLine_window_card_le
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev
  set V : ℝ := max (max U₀ (Real.exp (2 / c))) 16 with hVdef
  obtain ⟨k₁, hk₁⟩ := pow_unbounded_of_one_lt V (by norm_num : (1 : ℝ) < 2)
  have hθ : 1 / 2 ≤ 1 - c / 28 := by linarith
  have hπc : 0 < Real.pi * c := by positivity
  refine ⟨(Real.pi * c * 2 ^ k₁ + 10 * A + 8 * K) / (Real.pi * c), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with X hX1
  intro σ₀ r hr0 hr hlow hhigh
  have hV16 : 16 ≤ V := le_max_right _ _
  have hVU₀ : U₀ ≤ V := le_trans (le_max_left _ _) (le_max_left _ _)
  have hVexp : Real.exp (2 / c) ≤ V := le_trans (le_max_right _ _) (le_max_left _ _)
  have hwin : ∀ U : ℝ, V ≤ U → ∀ Z : Finset ℂ, (∀ z ∈ Z, riemannZeta z = 0 ∧ 1 / 2 + c ≤ z.re ∧
      z.re ≤ 1 ∧ U / 4 + 1 ≤ z.im ∧ z.im ≤ U / 2 - 1) →
      Real.pi * c * Z.card ≤ U / 4 * A * Real.exp (-(c / 28 * Real.log U)) + K * Real.log U := by
    intro U hU Z hZ
    have hU0 : 0 < U := by linarith
    have hlog : 2 / c ≤ Real.log U := by
      rw [Real.le_log_iff_exp_le hU0]; linarith
    exact hU₀ U (le_trans hVU₀ hU) c hc hc4 hlog Z hZ
  have hS : ∀ n ∈ badUniformDiscs σ₀ r X, 1 ≤ n ∧ n ≤ X := fun n hn =>
    Finset.mem_Icc.mp (mem_badUniformDiscs.mp hn).1
  have hcardN := card_le_dyadic_halves hS k₁
  have hcard : ((badUniformDiscs σ₀ r X).card : ℝ) ≤ 2 ^ k₁ +
      ∑ k ∈ Finset.Icc k₁ (Nat.log 2 X),
        (((dyadicLowerHalf (badUniformDiscs σ₀ r X) k).card : ℝ)
          + ((dyadicUpperHalf (badUniformDiscs σ₀ r X) k).card : ℝ)) := by
    exact_mod_cast hcardN
  have hblocks : Real.pi * c * ∑ k ∈ Finset.Icc k₁ (Nat.log 2 X),
        (((dyadicLowerHalf (badUniformDiscs σ₀ r X) k).card : ℝ)
          + ((dyadicUpperHalf (badUniformDiscs σ₀ r X) k).card : ℝ))
      ≤ 10 * A * (X : ℝ) ^ (1 - c / 28) + 8 * K * (1 + Real.log X) ^ 2 := by
    refine le_trans ?_ (dyadic_sums_le hA.le hK hθ hX1 k₁)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hPk : (2 : ℝ) ^ k₁ ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) (Finset.mem_Icc.mp hk).1
    rw [mul_add]
    exact dyadic_block_badUniformDiscs_le hA.le hK hc hc4 hV16 hwin hr0 hr hlow hhigh
      (lt_of_lt_of_le hk₁ hPk)
  have hXθ : 0 ≤ (X : ℝ) ^ (1 - c / 28) := by positivity
  have hL1 : 1 ≤ (1 + Real.log X) ^ 2 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ X by exact_mod_cast hX1)
    nlinarith
  have h2k : (0 : ℝ) ≤ 2 ^ k₁ := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hπc]
  have hmain : ((badUniformDiscs σ₀ r X).card : ℝ) * (Real.pi * c)
      ≤ Real.pi * c * 2 ^ k₁ + (10 * A * (X : ℝ) ^ (1 - c / 28)
        + 8 * K * (1 + Real.log X) ^ 2) := by
    have := mul_le_mul_of_nonneg_right hcard hπc.le
    nlinarith
  nlinarith [mul_nonneg hπc.le h2k, mul_nonneg hA.le hXθ, mul_nonneg hK hXθ,
    mul_le_mul_of_nonneg_left hL1 (mul_nonneg hπc.le h2k)]

end

end RHTower
