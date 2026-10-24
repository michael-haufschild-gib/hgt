import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumSelfDual
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSixOneConstants
import GaloisForLFunctions.RHTower.Sieve.SeparatedCount

/-!
# Heath–Brown's pair-sum estimate at every length

Dilating the positive ratio kernel to a length comparable to
`sqrt T * |W|^(1/4)` before reflection removes the middle-range loss.
The reflected estimate already has constants independent of the input
length, so arbitrarily long polynomials need no separate growth assumption.
-/

set_option autoImplicit false
open Finset

namespace RHTower.Sieve
noncomputable section

private theorem balanced_rpow_identity {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T) :
    R ^ (3 / 2 : ℝ) * T = R * (T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ)) ^ 2 := by
  rw [mul_pow, ← Real.rpow_natCast (T ^ (1 / 2 : ℝ)) 2,
    ← Real.rpow_mul hT, ← Real.rpow_natCast (R ^ (1 / 4 : ℝ)) 2,
    ← Real.rpow_mul hR.le]
  norm_num
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hR, Real.rpow_one]
  ring

private theorem balanced_main_identity {R T : ℝ} (hR : 0 < R) :
    R * (T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ)) = R ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by
  rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hR, Real.rpow_one]
  ring

/-- Above the balanced scale the reflected fourth term is paid by the
ordinary diagonal term, uniformly in the polynomial length. -/
theorem hbPairSum_Ioc_le_above_balanced {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T)
    {N : ℕ} (hN : 1 ≤ N) (hN2 : 2 * T < (N : ℝ) ^ 2)
    (hbal : T ^ (1 / 2 : ℝ) * (W.card : ℝ) ^ (1 / 4 : ℝ) ≤ N)
    {δ : ℝ} (hδ : 0 < δ) {a : ℕ → ℂ}
    (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc N (2 * N)) a ≤
      2 * hbSelfDualConst T δ * GuthMaynard.heathBrownMajorant W.card N T := by
  have hH := hbSelfDualConst_nonneg hT hδ
  have h := hbPairSum_Ioc_le_reflected hW hT hdiam hN hN2 hδ ha
  rcases Nat.eq_zero_or_pos W.card with hR | hR
  · have he : W = ∅ := Finset.card_eq_zero.mp hR
    subst W
    simp [hbPairSum, GuthMaynard.heathBrownMajorant]
  · have hRpos : (0 : ℝ) < W.card := by exact_mod_cast hR
    have hG0 : 0 ≤ T ^ (1 / 2 : ℝ) * (W.card : ℝ) ^ (1 / 4 : ℝ) := by positivity
    have hfourth : (W.card : ℝ) ^ (3 / 2 : ℝ) * T ≤ W.card * (N : ℝ) ^ 2 := by
      rw [balanced_rpow_identity hRpos (by linarith)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hG0 hbal 2) hRpos.le
    have hbase : 0 ≤ (W.card : ℝ) ^ 2 * N +
        (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N := by positivity
    unfold GuthMaynard.heathBrownMajorant
    nlinarith only [h, mul_le_mul_of_nonneg_left hfourth hH,
      mul_nonneg hH hbase]

/-- Weighted reflection on a block within six times the balanced scale. -/
private theorem hbAmp_half_le_balanced_window {W : Finset ℝ}
    (hW : GuthMaynard.IsSeparated 1 W) {T : ℝ} (hT : 1 ≤ T)
    (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) (hR : 0 < (W.card : ℝ))
    {N : ℕ} (hN : 1 ≤ N) (hN2 : 2 * T < (N : ℝ) ^ 2)
    (hlo : T ^ (1 / 2 : ℝ) * (W.card : ℝ) ^ (1 / 4 : ℝ) ≤ N)
    (hhi : (N : ℝ) ≤ 6 * (T ^ (1 / 2 : ℝ) * (W.card : ℝ) ^ (1 / 4 : ℝ)))
    {δ : ℝ} (hδ : 0 < δ) :
    hbAmp W (1 / 2) (Finset.Ioc N (2 * N)) ≤
      hbSelfDualConst T δ * ((W.card : ℝ) ^ 2 +
        13 * ((W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hH := hbSelfDualConst_nonneg hT hδ
  have href := hbPairSum_Ioc_le_reflected hW hT hdiam hN hN2 hδ
    (a := fun _ => (1 : ℂ)) (fun _ _ => by norm_num)
  have hG0 : 0 ≤ T ^ (1 / 2 : ℝ) * (W.card : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hfourth : (W.card : ℝ) ^ (3 / 2 : ℝ) * T ≤ W.card * (N : ℝ) ^ 2 := by
    rw [balanced_rpow_identity hR (by linarith)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hG0 hlo 2) hR.le
  have hRN : (W.card : ℝ) * N ≤
      6 * ((W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hhi hR.le
    rw [← balanced_main_identity hR]
    nlinarith only [hm]
  refine (hbAmp_half_le_hbPairSum_div W hN).trans ?_
  rw [div_le_iff₀ hNpos]
  have hpay := mul_le_mul_of_nonneg_left hfourth hH
  have hmain := mul_le_mul_of_nonneg_right hRN (mul_nonneg hH hNpos.le)
  nlinarith only [href, hpay, hmain]

private theorem balanced_length_bounds {R T : ℝ} (hR : 1 ≤ R) (hRT : R ≤ 2 * T)
    (hT : 1 ≤ T) :
    let G := T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ)
    let L := ⌈2 * G⌉₊
    1 ≤ L ∧ 2 * G ≤ (L : ℝ) ∧ (L : ℝ) ≤ 3 * G ∧
      2 * T < (L : ℝ) ^ 2 ∧ (L : ℝ) ≤ 6 * T ^ 2 := by
  dsimp only
  have hT0 : 0 ≤ T := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hTr : 1 ≤ T ^ (1 / 2 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hRr : 1 ≤ R ^ (1 / 4 : ℝ) := Real.one_le_rpow hR (by norm_num)
  have hG : 1 ≤ T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ) := by nlinarith only [hTr, hRr]
  have hlo := Nat.le_ceil (2 * (T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ)))
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 2 *
    (T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ)) by positivity)
  have hL1 : (1 : ℝ) ≤ (⌈2 * (T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ))⌉₊ : ℕ) := by
    linarith only [hlo, hG]
  have hL3 : ((⌈2 * (T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ))⌉₊ : ℕ) : ℝ) ≤
      3 * (T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ)) := by linarith only [hhi, hG]
  have hsqrt : (T ^ (1 / 2 : ℝ)) ^ 2 = T := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0]
    norm_num
  have hGsq : T ≤ (T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ)) ^ 2 := by
    rw [mul_pow, hsqrt]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (one_le_pow₀ hRr : 1 ≤ (R ^ (1 / 4 : ℝ)) ^ 2) hT0
  have hLsq := pow_le_pow_left₀ (show 0 ≤ 2 *
    (T ^ (1 / 2 : ℝ) * R ^ (1 / 4 : ℝ)) by positivity) hlo 2
  have ht : T ^ (1 / 2 : ℝ) ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hr : R ^ (1 / 4 : ℝ) ≤ R := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hR (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  have hGupper := mul_le_mul ht (hr.trans hRT)
    (show 0 ≤ R ^ (1 / 4 : ℝ) by positivity) hT0
  exact ⟨by exact_mod_cast hL1, hlo, hL3, by nlinarith only [hLsq, hGsq, hT],
    by nlinarith only [hL3, hGupper]⟩

/-- A uniform divisor factor for the two blocks surrounding the balanced scale. -/
def hbBalancedDivisorFactor (T δ : ℝ) : ℝ :=
  divisorBoundConst δ * ((⌈24 * T ^ 2⌉₊ : ℕ) : ℝ) ^ δ

theorem hbBalancedDivisorFactor_nonneg (T : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ hbBalancedDivisorFactor T δ := by
  unfold hbBalancedDivisorFactor
  exact mul_nonneg (divisorBoundConst_pos hδ).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Dilating to the balanced scale removes the fourth term at every length. -/
theorem hbPairSum_Ioc_le_balanced {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T)
    (hcard : (W.card : ℝ) ≤ 2 * T) {M : ℕ} (hM : 1 ≤ M)
    {δ : ℝ} (hδ : 0 < δ) {a : ℕ → ℂ}
    (ha : ∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc M (2 * M)) a ≤
      208 * (hbBalancedDivisorFactor T δ + 1) * hbSelfDualConst T δ *
        GuthMaynard.heathBrownMajorant W.card M T := by
  classical
  rcases Nat.eq_zero_or_pos W.card with hR | hR
  · have he : W = ∅ := Finset.card_eq_zero.mp hR
    subst W
    simp [hbPairSum, GuthMaynard.heathBrownMajorant]
  have hRpos : (0 : ℝ) < W.card := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hR
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  let G := T ^ (1 / 2 : ℝ) * (W.card : ℝ) ^ (1 / 4 : ℝ)
  let L := ⌈2 * G⌉₊
  have hG0 : 0 ≤ G := by dsimp [G]; positivity
  obtain ⟨hL, hLlo, hLhi, hLsq, hLT⟩ := balanced_length_bounds hR1 hcard hT
  change 1 ≤ L at hL
  change 2 * G ≤ (L : ℝ) at hLlo
  change (L : ℝ) ≤ 3 * G at hLhi
  change 2 * T < (L : ℝ) ^ 2 at hLsq
  change (L : ℝ) ≤ 6 * T ^ 2 at hLT
  have hH := hbSelfDualConst_nonneg hT hδ
  have hD := hbBalancedDivisorFactor_nonneg T hδ
  have hmajor := GuthMaynard.heathBrownMajorant_nonneg hRpos.le hMpos.le
    (show 0 ≤ T by linarith)
  by_cases hLM : L ≤ M
  · have hLMr : (L : ℝ) ≤ M := by exact_mod_cast hLM
    have hMsq : 2 * T < (M : ℝ) ^ 2 :=
      hLsq.trans_le (pow_le_pow_left₀ (Nat.cast_nonneg _) hLMr 2)
    have hlarge := hbPairSum_Ioc_le_above_balanced hW hT hdiam hM hMsq
      (show G ≤ (M : ℝ) by linarith only [hG0, hLlo, hLMr]) hδ ha
    refine hlarge.trans ?_
    apply mul_le_mul_of_nonneg_right _ hmajor
    nlinarith only [hH, mul_nonneg hD hH]
  · have hML : M ≤ L := by omega
    have h2L : 1 ≤ 2 * L := by omega
    have h2Lsq : 2 * T < ((2 * L : ℕ) : ℝ) ^ 2 := by
      push_cast
      nlinarith only [hLsq, sq_nonneg (L : ℝ)]
    have h1 := hbAmp_half_le_balanced_window hW hT hdiam hRpos hL hLsq
      (show G ≤ (L : ℝ) by linarith only [hG0, hLlo])
      (show (L : ℝ) ≤ 6 * G by linarith only [hG0, hLhi]) hδ
    have h2 := hbAmp_half_le_balanced_window hW hT hdiam hRpos h2L h2Lsq
      (show G ≤ ((2 * L : ℕ) : ℝ) by push_cast; linarith only [hG0, hLlo])
      (show ((2 * L : ℕ) : ℝ) ≤ 6 * G by push_cast; linarith only [hLhi]) hδ
    have hdiv : ∀ u ∈ Finset.Ioc L (2 * 2 * L),
        (u.divisors.card : ℝ) ≤ hbBalancedDivisorFactor T δ := by
      intro u hu
      obtain ⟨hulo, huhi⟩ := Finset.mem_Ioc.mp hu
      have hu0 : u ≠ 0 := by omega
      refine (card_divisors_le_rpow hδ hu0).trans ?_
      apply mul_le_mul_of_nonneg_left _ (divisorBoundConst_pos hδ).le
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hδ.le
      have hu : (u : ℝ) ≤ 4 * (L : ℝ) := by exact_mod_cast huhi
      exact (show (u : ℝ) ≤ 24 * T ^ 2 by linarith only [hu, hLT]).trans (Nat.le_ceil _)
    have hdilate := hbAmp_half_le_of_le W (A := M) (N := L) (c := 2)
      (by omega) hML (Finset.Subset.refl _) hdiv
    have hdisjoint : Disjoint (Finset.Ioc L (2 * L)) (Finset.Ioc (2 * L) (2 * (2 * L))) := by
      apply Finset.disjoint_left.mpr
      intro u hu hv
      have hu' := (Finset.mem_Ioc.mp hu).2
      have hv' := (Finset.mem_Ioc.mp hv).1
      omega
    have hunion : Finset.Ioc L (2 * 2 * L) =
        Finset.Ioc L (2 * L) ∪ Finset.Ioc (2 * L) (2 * (2 * L)) := by
      ext u
      simp only [Finset.mem_union, Finset.mem_Ioc]
      omega
    have hsplit := hbPairSum_union_le W hdisjoint
      (fun n => (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
    change hbAmp W (1 / 2) (_ ∪ _) ≤
      2 * hbAmp W (1 / 2) (Finset.Ioc L (2 * L)) +
        2 * hbAmp W (1 / 2) (Finset.Ioc (2 * L) (2 * (2 * L))) at hsplit
    rw [← hunion] at hsplit
    have hwide : hbAmp W (1 / 2) (Finset.Ioc L (2 * 2 * L)) ≤
        4 * (hbSelfDualConst T δ * ((W.card : ℝ) ^ 2 +
          13 * ((W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)))) := by
      linarith only [hsplit, h1, h2]
    have hshort := hdilate.trans (mul_le_mul_of_nonneg_left hwide (by positivity))
    have hpair := (hbPairSum_le_two_mul_hbAmp_half W ha).trans
      (mul_le_mul_of_nonneg_left hshort (by positivity))
    have hscalar : (M : ℝ) * ((W.card : ℝ) ^ 2 +
        13 * ((W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ))) ≤
        13 * GuthMaynard.heathBrownMajorant W.card M T := by
      unfold GuthMaynard.heathBrownMajorant
      nlinarith only [mul_nonneg (sq_nonneg (W.card : ℝ)) hMpos.le,
        mul_nonneg hRpos.le (sq_nonneg (M : ℝ))]
    have hscaled := mul_le_mul_of_nonneg_left hscalar
      (show 0 ≤ 16 * hbBalancedDivisorFactor T δ * hbSelfDualConst T δ by positivity)
    nlinarith only [hpair, hscaled, mul_nonneg hH hmajor]

private theorem hbSelfDualConst_le_of_block_bounds {T δ η C : ℝ}
    (hT : 1 ≤ T) (hδ : 0 < δ) (hη : 0 < η) (hC : 0 ≤ C)
    (hblocks : ∀ L : ℕ, (L : ℝ) ≤ 64 * T ^ 2 → hbBlockConst T δ L ≤ C * T ^ η) :
    hbSelfDualConst T δ ≤
      (4 * C + 7200000 * C * (1 + 1 / ((η / 3) * Real.log 2)) ^ 3) * T ^ (2 * η) := by
  have hT0 : 0 < T := by linarith
  have hTpow : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlong : (hbLongBlock T : ℝ) ≤ 64 * T ^ 2 := by
    have hp := Real.rpow_le_rpow_of_exponent_le hT (show (2 / 3 : ℝ) ≤ 2 by norm_num)
    rw [Real.rpow_two] at hp
    have ht := hbLongBlock_le_rpow hT
    nlinarith only [hp, ht, sq_nonneg T]
  have hceil : (⌈2 * T⌉₊ : ℝ) ≤ 3 * T := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2 * T by positivity)
    linarith only [h, hT]
  have hceilSq : ((⌈2 * T⌉₊ ^ 2 : ℕ) : ℝ) ≤ 64 * T ^ 2 := by
    push_cast
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg ⌈2 * T⌉₊) hceil 2
    nlinarith only [hs, sq_nonneg T]
  have hs := hblocks (hbLongBlock T) hlong
  rw [← hbSmallConst_eq_hbBlockConst] at hs
  have hb := hblocks (⌈2 * T⌉₊ ^ 2) hceilSq
  have hz := hblocks 0 (by
    simpa only [Nat.cast_zero] using
      mul_nonneg (show (0 : ℝ) ≤ 64 by norm_num) (sq_nonneg T))
  norm_num [hbBlockConst, Real.zero_rpow hδ.ne'] at hz
  have hdual := hbDualFactor_nonneg T
  have hrefl := one_le_hbReflFactor hT
  have hr : hbReflFactor T ≤ C * T ^ η := by nlinarith only [hz, hdual, hrefl]
  have hL0 : 0 ≤ 1 + Real.logb 2 T := by
    have h := Real.logb_nonneg (b := 2) (by norm_num) hT
    linarith only [h]
  have hLc := GuthMaynard.one_add_logb_two_le_rpow (show 0 < η / 3 by positivity) hT
  have hcube : (1 + Real.logb 2 T) ^ 3 ≤
      (1 + 1 / ((η / 3) * Real.log 2)) ^ 3 * T ^ η := by
    have h := pow_le_pow_left₀ hL0 hLc 3
    rw [mul_pow, ← Real.rpow_natCast (T ^ (η / 3)) 3,
      ← Real.rpow_mul hT0.le] at h
    norm_num only [Nat.cast_ofNat, div_mul_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0)] at h
    exact h
  have hc0 : 0 ≤ (1 + 1 / ((η / 3) * Real.log 2)) ^ 3 := by positivity
  have hsum0 : 0 ≤ hbSmallConst T δ + hbBlockConst T δ (⌈2 * T⌉₊ ^ 2) := by
    have h₁ := one_le_hbSmallConst hT hδ
    have h₂ := hbBlockConst_nonneg (δ := δ) hT (⌈2 * T⌉₊ ^ 2)
    linarith only [h₁, h₂]
  have hproduct := mul_le_mul hcube (show hbSmallConst T δ +
      hbBlockConst T δ (⌈2 * T⌉₊ ^ 2) ≤ 2 * C * T ^ η by linarith only [hs, hb])
      hsum0 (mul_nonneg hc0 (by positivity))
  have hlinear : C * T ^ η ≤ C * (T ^ η * T ^ η) := by
    nlinarith only [hC, hTpow, mul_nonneg hC (mul_nonneg
      (show 0 ≤ T ^ η by positivity) (show 0 ≤ T ^ η - 1 by linarith only [hTpow]))]
  have heq : T ^ (2 * η) = T ^ η * T ^ η := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  rw [hbSelfDualConst, heq]
  nlinarith only [hproduct, hr, hlinear]

/-- The balanced-scale constant is `O(T^ε)`, uniformly in all input data. -/
theorem exists_hbBalancedConst_le {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      208 * (hbBalancedDivisorFactor T δ + 1) * hbSelfDualConst T δ ≤ C * T ^ ε := by
  obtain ⟨δ, hδ, C, hC, hb⟩ := GuthMaynard.exists_blockConst_divisor_le
    (show 0 < ε / 3 by positivity) (show (4 : ℝ) ≤ 64 by norm_num)
    (show (2 / 3 : ℝ) ≤ 2 by norm_num)
  let K := 4 * C + 7200000 * C * (1 + 1 / ((ε / 3 / 3) * Real.log 2)) ^ 3
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨δ, hδ, 208 * (C + 2) * K, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hTpow : 1 ≤ T ^ (ε / 3) := Real.one_le_rpow hT (by positivity)
  have hT2 : 1 ≤ T ^ 2 := by nlinarith only [hT]
  have hindex : (⌈24 * T ^ 2⌉₊ : ℝ) ≤ 64 * T ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    have h := Nat.ceil_lt_add_one (show 0 ≤ 24 * T ^ 2 by positivity)
    linarith only [h, hT2]
  have hDsquare := (hb T hT).2 ⌈24 * T ^ 2⌉₊ hindex
  change hbBalancedDivisorFactor T δ ^ 2 ≤ C * T ^ (ε / 3) at hDsquare
  have hD : hbBalancedDivisorFactor T δ + 1 ≤ (C + 2) * T ^ (ε / 3) := by
    nlinarith only [hDsquare, hTpow, sq_nonneg (hbBalancedDivisorFactor T δ - 1 / 2)]
  have hH : hbSelfDualConst T δ ≤ K * T ^ (2 * (ε / 3)) := by
    apply hbSelfDualConst_le_of_block_bounds hT hδ (by positivity) hC
    intro L hL
    apply (hb T hT).1 L
    simpa only [Real.rpow_two] using hL
  have hH0 := hbSelfDualConst_nonneg hT hδ
  have hD0 := hbBalancedDivisorFactor_nonneg T hδ
  have hprod := mul_le_mul hD hH hH0 (by positivity : 0 ≤ (C + 2) * T ^ (ε / 3))
  have hexp : T ^ (ε / 3) * T ^ (2 * (ε / 3)) = T ^ ε := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  calc
    208 * (hbBalancedDivisorFactor T δ + 1) * hbSelfDualConst T δ
      ≤ 208 * (((C + 2) * T ^ (ε / 3)) * (K * T ^ (2 * (ε / 3)))) := by
        nlinarith only [hprod]
    _ = 208 * (C + 2) * K * T ^ ε := by
      rw [show (C + 2) * T ^ (ε / 3) * (K * T ^ (2 * (ε / 3))) =
        (C + 2) * K * (T ^ (ε / 3) * T ^ (2 * (ε / 3))) by ring, hexp]
      ring

end
end RHTower.Sieve

namespace RHTower.GuthMaynard
noncomputable section
open RHTower.Sieve

/-- Heath–Brown's pair-sum theorem, with no restriction on the block length. -/
theorem heathBrownPairSumBound_holds : HeathBrownPairSumBound := by
  intro ε hε
  obtain ⟨δ, hδ, C, hC, hbound⟩ := exists_hbBalancedConst_le hε
  refine ⟨C, hC, fun W N a T T₀ hT hN ha hin hsep => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T := by
    intro t ht t' ht'
    obtain ⟨htlo, hthi⟩ := hin t ht
    obtain ⟨ht'lo, ht'hi⟩ := hin t' ht'
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hcard : (W.card : ℝ) ≤ 2 * T := by
    have h := card_le_of_separated (s := W) (u := id) (g := 1) (by norm_num)
      (show 0 ≤ T by linarith) hsep hin
    simp only [div_one] at h
    linarith only [h, hT]
  have hpair := hbPairSum_Ioc_le_balanced hsep hT1 hdiam hcard hN hδ (fun n _ => ha n)
  have hmain := hpair.trans (mul_le_mul_of_nonneg_right (hbound T hT1)
    (heathBrownMajorant_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith)))
  rw [hbPairSum_eq_sum_exp] at hmain
  exact hmain

end
end RHTower.GuthMaynard

namespace RHTower.Sieve
noncomputable section
open Finset

/-- A dyadic cover preserves the three-term majorant, at cost `8^m`. -/
theorem hbPairSum_Ioc_two_pow_le_of_blocks {W : Finset ℝ} {T K : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) {a : ℕ → ℂ}
    (hblocks : ∀ N : ℕ, 1 ≤ N → hbPairSum W (Finset.Ioc N (2 * N)) a ≤
      K * GuthMaynard.heathBrownMajorant W.card N T)
    {P : ℕ} (hP : 1 ≤ P) (m : ℕ) :
    hbPairSum W (Finset.Ioc P (2 ^ m * P)) a ≤
      8 ^ m * K * GuthMaynard.heathBrownMajorant W.card P T := by
  have hA : 0 ≤ (W.card : ℝ) ^ 2 * P := by positivity
  have hB : 0 ≤ (W.card : ℝ) * (P : ℝ) ^ 2 := by positivity
  have hC : 0 ≤ (W.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * P := by positivity
  have hmajor : 0 ≤ GuthMaynard.heathBrownMajorant W.card P T :=
    GuthMaynard.heathBrownMajorant_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) hT
  have hblock : ∀ i ∈ Finset.range m,
      hbPairSum W (Finset.Ioc (2 ^ i * P) (2 * (2 ^ i * P))) a ≤
        K * GuthMaynard.heathBrownMajorant W.card P T * 4 ^ i := by
    intro i hi
    have hiP : 1 ≤ 2 ^ i * P := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h := hblocks (2 ^ i * P) hiP
    have h4 : ((2 : ℝ) ^ i) ^ 2 = (4 : ℝ) ^ i := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have h24 := two_pow_le_four_pow i
    have hscale : GuthMaynard.heathBrownMajorant W.card (2 ^ i * (P : ℝ)) T ≤
        GuthMaynard.heathBrownMajorant W.card P T * 4 ^ i := by
      unfold GuthMaynard.heathBrownMajorant
      rw [mul_pow, h4]
      nlinarith only [mul_le_mul_of_nonneg_left h24 hA,
        mul_le_mul_of_nonneg_left h24 hC]
    push_cast at h
    exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_left hscale hK])
  have hsum : ∑ i ∈ Finset.range m,
      hbPairSum W (Finset.Ioc (2 ^ i * P) (2 * (2 ^ i * P))) a ≤
        K * GuthMaynard.heathBrownMajorant W.card P T * 4 ^ m := by
    calc
      _ ≤ ∑ i ∈ Finset.range m, K * GuthMaynard.heathBrownMajorant W.card P T * 4 ^ i :=
        Finset.sum_le_sum hblock
      _ = K * GuthMaynard.heathBrownMajorant W.card P T *
          ∑ i ∈ Finset.range m, (4 : ℝ) ^ i := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_geom_four_le m) (mul_nonneg hK hmajor)
  have h8 : (8 : ℝ) ^ m = 2 ^ m * 4 ^ m := by rw [← mul_pow]; norm_num
  refine (hbPairSum_Ioc_two_pow_le W a P m).trans ?_
  have h := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 ^ m by positivity)
  rw [h8]
  nlinarith only [h]

end
end RHTower.Sieve
