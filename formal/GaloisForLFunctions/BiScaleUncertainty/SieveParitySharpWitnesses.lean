import GaloisForLFunctions.BiScaleUncertainty.SievePhysicalTranslationStability
import GaloisForLFunctions.BiScaleUncertainty.SieveParityFourierBounds
import GaloisForLFunctions.BiScaleUncertainty.SieveParityResonanceCounts

/-! Actual perturbation families with sharp raw cancellation and translation separation. -/

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false

def sharpProfile (A B : ℕ) (t : ℝ) (q : ℕ) : ℝ :=
  if q = 2 then 2 else if q = A ∨ q = B then t else 0

def flipProfile (B : ℕ) (a : ℕ → ℝ) (q : ℕ) : ℝ := if q = B then -a q else a q

def sharpWeights (N A B : ℕ) (t : ℝ) : ℕ → ℝ :=
  _root_.RHTower.pmRamanujanResidueCoeff (sharpProfile A B t) N

def sharpFlippedWeights (N A B : ℕ) (t : ℝ) : ℕ → ℝ :=
  _root_.RHTower.pmRamanujanResidueCoeff (flipProfile B (sharpProfile A B t)) N

theorem coordinate_sharpWeights (N A B : ℕ) (t : ℝ)
    (h2 : 2 ∈ Icc 1 N) (hA : A ∈ Icc 1 N) (hB : B ∈ Icc 1 N) (q : ℕ) :
    selbergMultiplesCoord N (sharpWeights N A B t) q = sharpProfile A B t q := by
  rw [sharpWeights, selbergMultiplesCoord_ramanujan_inverse]
  by_cases hq : q ∈ Icc 1 N
  · simp [hq]
  · have hq2 : q ≠ 2 := fun hh => hq (hh ▸ h2)
    have hqA : q ≠ A := fun hh => hq (hh ▸ hA)
    have hqB : q ≠ B := fun hh => hq (hh ▸ hB)
    simp [hq, sharpProfile, hq2, hqA, hqB]

theorem coordinate_sharpFlippedWeights (N A B : ℕ) (t : ℝ)
    (h2 : 2 ∈ Icc 1 N) (hA : A ∈ Icc 1 N) (hB : B ∈ Icc 1 N) (q : ℕ) :
    selbergMultiplesCoord N (sharpFlippedWeights N A B t) q =
      flipProfile B (sharpProfile A B t) q := by
  rw [sharpFlippedWeights, selbergMultiplesCoord_ramanujan_inverse]
  by_cases hq : q ∈ Icc 1 N
  · simp [hq]
  · have hq2 : q ≠ 2 := fun hh => hq (hh ▸ h2)
    have hqA : q ≠ A := fun hh => hq (hh ▸ hA)
    have hqB : q ≠ B := fun hh => hq (hh ▸ hB)
    simp [hq, flipProfile, sharpProfile, hq2, hqA, hqB]

private theorem product_flip {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (p : ι → Prop) [DecidablePred p] :
    (∏ i, if p i then -a i else a i) =
      (-1 : ℝ)^((univ.filter p).card)*(∏ i, a i) := by
  classical
  have he : (∏ i, if p i then (-1 : ℝ) else 1) = (-1 : ℝ)^((univ.filter p).card) := by
    rw [Finset.prod_ite]
    simp
  calc
    _ = (∏ i, if p i then (-1 : ℝ) else 1)*(∏ i, a i) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      split_ifs <;> ring
    _ = _ := by rw [he]

theorem sharp_product_bound {P m : ℕ} [NeZero P] (r : Fin m → ZMod P)
    (A B : ℕ) (t : ℝ) (d : ℕ) (hm : m ≤ 6) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hdegree : (∀ i, addOrderOf (r i) = 2 ∨ addOrderOf (r i) = A ∨ addOrderOf (r i) = B) →
      Odd (orderCount r B) → d ≤ smallCount r) :
    |(∏ i, sharpProfile A B t (addOrderOf (r i))) -
        (∏ i, flipProfile B (sharpProfile A B t) (addOrderOf (r i)))| ≤ 128*t^d := by
  classical
  by_cases hs : ∀ i, addOrderOf (r i) = 2 ∨ addOrderOf (r i) = A ∨ addOrderOf (r i) = B
  · rcases Nat.even_or_odd (orderCount r B) with ho | ho
    · have he := product_flip (fun i => sharpProfile A B t (addOrderOf (r i)))
        (fun i => addOrderOf (r i) = B)
      change (∏ i, flipProfile B (sharpProfile A B t) (addOrderOf (r i))) =
        (-1 : ℝ)^(orderCount r B)*(∏ i, sharpProfile A B t (addOrderOf (r i))) at he
      rw [ho.neg_one_pow, one_mul] at he
      rw [he, sub_self, abs_zero]
      positivity
    · have hnorm (i : Fin m) : |sharpProfile A B t (addOrderOf (r i))| =
          if addOrderOf (r i) = 2 then 2 else t := by
        by_cases h2 : addOrderOf (r i) = 2
        · simp [sharpProfile, h2]
        · have hab := (hs i).resolve_left h2
          simp [sharpProfile, h2, hab, abs_of_nonneg ht]
      have ha : |∏ i, sharpProfile A B t (addOrderOf (r i))| =
          (2 : ℝ)^(orderCount r 2)*t^(smallCount r) := by
        rw [Finset.abs_prod]
        simp_rw [hnorm]
        rw [Finset.prod_ite]
        simp [orderCount, smallCount]
      have hb : |∏ i, flipProfile B (sharpProfile A B t) (addOrderOf (r i))| =
          |∏ i, sharpProfile A B t (addOrderOf (r i))| := by
        rw [Finset.abs_prod, Finset.abs_prod]
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : addOrderOf (r i) = B <;> simp [flipProfile, hi]
      have hn : orderCount r 2 ≤ m := by
        have hh := Finset.card_le_card (Finset.filter_subset
          (fun i : Fin m => addOrderOf (r i) = 2) (univ : Finset (Fin m)))
        simpa only [orderCount, card_univ, Fintype.card_fin] using hh
      have htwo : (2 : ℝ)^(orderCount r 2) ≤ 64 := by
        calc
          _ ≤ (2 : ℝ)^6 := pow_le_pow_right₀ (by norm_num) (hn.trans hm)
          _ = _ := by norm_num
      have htdeg : t^(smallCount r) ≤ t^d := pow_le_pow_of_le_one ht ht1 (hdegree hs ho)
      have hbound := mul_le_mul htwo htdeg (pow_nonneg ht (smallCount r)) (by norm_num : (0 : ℝ) ≤ 64)
      have htri := abs_sub_le (∏ i, sharpProfile A B t (addOrderOf (r i))) 0
        (∏ i, flipProfile B (sharpProfile A B t) (addOrderOf (r i)))
      rw [sub_zero, zero_sub, abs_neg, hb, ha] at htri
      nlinarith only [hbound, htri]
  · push Not at hs
    obtain ⟨i, hi2, hiA, hiB⟩ := hs
    have ha : sharpProfile A B t (addOrderOf (r i)) = 0 := by simp [sharpProfile, hi2, hiA, hiB]
    have hb : flipProfile B (sharpProfile A B t) (addOrderOf (r i)) = 0 := by simp [flipProfile, hiB, ha]
    rw [Finset.prod_eq_zero (mem_univ i) ha, Finset.prod_eq_zero (mem_univ i) hb, sub_self, abs_zero]
    positivity

local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

theorem sharp_raw_bound (N A B : ℕ) (t : ℝ) (d m : ℕ)
    (h2 : 2 ∈ Icc 1 N) (hA : A ∈ Icc 1 N) (hB : B ∈ Icc 1 N)
    (hm : m ≤ 6) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hdegree : ∀ r : Fin m → ZMod N.factorial, (∑ i, r i) = 0 →
      (∀ i, addOrderOf (r i) = 2 ∨ addOrderOf (r i) = A ∨ addOrderOf (r i) = B) →
      Odd (orderCount r B) → d ≤ smallCount r)
    (v : Fin m → ℕ) :
    |translatedMoment N (sharpWeights N A B t) v-
        translatedMoment N (sharpFlippedWeights N A B t) v| ≤
      128*(N.factorial : ℝ)^6*t^d := by
  have hp (r : Fin m → ZMod N.factorial) (hz : (∑ i, r i) = 0) :
      |(∏ i, selbergMultiplesCoord N (sharpWeights N A B t) (addOrderOf (r i))) -
        (∏ i, selbergMultiplesCoord N (sharpFlippedWeights N A B t) (addOrderOf (r i)))| ≤ 128*t^d := by
    simp_rw [coordinate_sharpWeights N A B t h2 hA hB,
      coordinate_sharpFlippedWeights N A B t h2 hA hB]
    exact sharp_product_bound r A B t d hm ht ht1 (hdegree r hz)
  have hPnat : 1 ≤ N.factorial := Nat.factorial_pos N
  have hP : (1 : ℝ) ≤ N.factorial := by exact_mod_cast hPnat
  have hpow := pow_le_pow_right₀ hP hm
  calc
    _ ≤ (N.factorial : ℝ)^m*(128*t^d) :=
      raw_error_of_resonant_products N _ _ m (128*t^d) (by positivity) hp v
    _ ≤ (N.factorial : ℝ)^6*(128*t^d) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by ring

theorem sharp_raw_three (N : ℕ) (hN : 3 ≤ N) (t : ℝ) (m : ℕ)
    (hm : m ≤ 6) (ht : 0 ≤ t) (ht1 : t ≤ 1) (v : Fin m → ℕ) :
    |translatedMoment N (sharpWeights N 3 3 t) v-
        translatedMoment N (sharpFlippedWeights N 3 3 t) v| ≤
      128*(N.factorial : ℝ)^6*t^3 := by
  apply sharp_raw_bound N 3 3 t 3 m (by simp; omega) (by simp; omega) (by simp; omega) hm ht ht1
  intro r hz hs ho
  exact count_three_lower r hz (fun i => by simpa only [or_self] using hs i) ho

theorem sharp_raw_five (N : ℕ) (hN : 12 ≤ N) (t : ℝ) (m : ℕ)
    (hm : m ≤ 6) (ht : 0 ≤ t) (ht1 : t ≤ 1) (v : Fin m → ℕ) :
    |translatedMoment N (sharpWeights N 8 12 t) v-
        translatedMoment N (sharpFlippedWeights N 8 12 t) v| ≤
      128*(N.factorial : ℝ)^6*t^5 := by
  apply sharp_raw_bound N 8 12 t 5 m (by simp; omega) (by simp; omega) (by simp; omega) hm ht ht1
  intro r hz hs ho
  exact count_five_lower r hz hs ho

theorem sharp_raw_six (N : ℕ) (hN : 20 ≤ N) (t : ℝ) (m : ℕ)
    (hm : m ≤ 6) (ht : 0 ≤ t) (ht1 : t ≤ 1) (v : Fin m → ℕ) :
    |translatedMoment N (sharpWeights N 12 20 t) v-
        translatedMoment N (sharpFlippedWeights N 12 20 t) v| ≤
      128*(N.factorial : ℝ)^6*t^6 := by
  apply sharp_raw_bound N 12 20 t 6 m (by simp; omega) (by simp; omega) (by simp; omega) hm ht ht1
  intro r hz hs ho
  exact count_six_lower r hz hs ho

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

def translationPhase (N q h : ℕ) : ℂ :=
  ZMod.stdAddChar ((h : ZMod N.factorial)*((N.factorial/q : ℕ) : ZMod N.factorial))

theorem translationPhase_norm (N q h : ℕ) : ‖translationPhase N q h‖ = 1 := by
  simp [translationPhase, ZMod.stdAddChar_apply]

theorem translationPhase_order (N q h : ℕ) (hq : q ∈ Icc 1 N) :
    (translationPhase N q h)^q = 1 := by
  let r : ZMod N.factorial := ((N.factorial/q : ℕ) : ZMod N.factorial)
  have hr : addOrderOf r = q := frequency_order hq
  have hqr : q • r = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [hr])
  have hz : q • ((h : ZMod N.factorial)*r) = 0 := by
    rw [nsmul_eq_mul] at hqr ⊢
    calc
      (q : ZMod N.factorial)*((h : ZMod N.factorial)*r) =
          (h : ZMod N.factorial)*((q : ZMod N.factorial)*r) := by ring
      _ = 0 := by rw [hqr, mul_zero]
  change (ZMod.stdAddChar ((h : ZMod N.factorial)*r))^q = 1
  rw [← AddChar.map_nsmul_eq_pow, hz]
  simp

theorem translationPhase_relation (N A B h p q : ℕ)
    (he : p*(N.factorial/A) = q*(N.factorial/B)) :
    (translationPhase N A h)^p = (translationPhase N B h)^q := by
  unfold translationPhase
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul]
  calc
    (p : ZMod N.factorial)*((h : ZMod N.factorial)*(N.factorial/A : ℕ)) =
        (h : ZMod N.factorial)*((p*(N.factorial/A) : ℕ) : ZMod N.factorial) := by push_cast; ring
    _ = (h : ZMod N.factorial)*((q*(N.factorial/B) : ℕ) : ZMod N.factorial) := by rw [he]
    _ = _ := by push_cast; ring

theorem translationPhase_eight_twelve (N : ℕ) (hN : 12 ≤ N) (h : ℕ) :
    (translationPhase N 8 h)^2 = (translationPhase N 12 h)^3 := by
  apply translationPhase_relation
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (by decide : 0 < 8) (by omega : 8 ≤ N)
  obtain ⟨j, hj⟩ := Nat.dvd_factorial (by decide : 0 < 12) hN
  omega

theorem translationPhase_twelve_twenty (N : ℕ) (hN : 20 ≤ N) (h : ℕ) :
    (translationPhase N 12 h)^3 = (translationPhase N 20 h)^5 := by
  apply translationPhase_relation
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (by decide : 0 < 12) (by omega : 12 ≤ N)
  obtain ⟨j, hj⟩ := Nat.dvd_factorial (by decide : 0 < 20) hN
  omega

theorem sharp_unchanged_phase_bound (N A B : ℕ) (t : ℝ)
    (h2 : 2 ∈ Icc 1 N) (hA : A ∈ Icc 1 N) (hB : B ∈ Icc 1 N)
    (hA2 : A ≠ 2) (hAB : A ≠ B) (ht : 0 ≤ t) (h : ℕ) (D : ℝ)
    (herr : ∀ n, |sieveSeq N (sharpFlippedWeights N A B t) n-
      sieveSeq N (sharpWeights N A B t) (n+h)| ≤ D) :
    t*‖1-translationPhase N A h‖ ≤ D := by
  have hb := translated_coordinate_error N (sharpWeights N A B t)
    (sharpFlippedWeights N A B t) h D herr
    ((N.factorial/A : ℕ) : ZMod N.factorial)
  rw [frequency_order hA, coordinate_sharpWeights N A B t h2 hA hB,
    coordinate_sharpFlippedWeights N A B t h2 hA hB] at hb
  have hh : ‖(t : ℂ)-translationPhase N A h*(t : ℂ)‖ ≤ D := by
    simpa [sharpProfile, flipProfile, hA2, hAB, translationPhase] using hb
  rw [show (t : ℂ)-translationPhase N A h*(t : ℂ) = (t : ℂ)*(1-translationPhase N A h) by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht] at hh
  exact hh

theorem sharp_flipped_phase_bound (N A B : ℕ) (t : ℝ)
    (h2 : 2 ∈ Icc 1 N) (hA : A ∈ Icc 1 N) (hB : B ∈ Icc 1 N)
    (hB2 : B ≠ 2) (ht : 0 ≤ t) (h : ℕ) (D : ℝ)
    (herr : ∀ n, |sieveSeq N (sharpFlippedWeights N A B t) n-
      sieveSeq N (sharpWeights N A B t) (n+h)| ≤ D) :
    t*‖1+translationPhase N B h‖ ≤ D := by
  have hb := translated_coordinate_error N (sharpWeights N A B t)
    (sharpFlippedWeights N A B t) h D herr
    ((N.factorial/B : ℕ) : ZMod N.factorial)
  rw [frequency_order hB, coordinate_sharpWeights N A B t h2 hA hB,
    coordinate_sharpFlippedWeights N A B t h2 hA hB] at hb
  have hh : ‖-(t : ℂ)-translationPhase N B h*(t : ℂ)‖ ≤ D := by
    simpa [sharpProfile, flipProfile, hB2, translationPhase] using hb
  rw [show -(t : ℂ)-translationPhase N B h*(t : ℂ) = -(t : ℂ)*(1+translationPhase N B h) by ring,
    norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht] at hh
  exact hh

theorem sharp_separation_three (N : ℕ) (hN : 3 ≤ N) (t : ℝ) (ht : 0 ≤ t) (h : ℕ) (D : ℝ)
    (herr : ∀ n, |sieveSeq N (sharpFlippedWeights N 3 3 t) n-
      sieveSeq N (sharpWeights N 3 3 t) (n+h)| ≤ D) : 2*t ≤ 3*D := by
  have h3 : 3 ∈ Icc 1 N := by simp; omega
  have hb := sharp_flipped_phase_bound N 3 3 t (by simp; omega) h3 h3 (by decide) ht h D herr
  have hp := phase_incompatibility 1 (translationPhase N 3 h) 0 3
    (by norm_num) (by rw [translationPhase_norm]) ⟨1, rfl⟩
    (by simpa using (translationPhase_order N 3 h h3).symm)
  norm_num at hp
  have hh := mul_le_mul_of_nonneg_left hp ht
  nlinarith only [hh, hb]

theorem sharp_separation_five (N : ℕ) (hN : 12 ≤ N) (t : ℝ) (ht : 0 ≤ t) (h : ℕ) (D : ℝ)
    (herr : ∀ n, |sieveSeq N (sharpFlippedWeights N 8 12 t) n-
      sieveSeq N (sharpWeights N 8 12 t) (n+h)| ≤ D) : 2*t ≤ 5*D := by
  have h2 : 2 ∈ Icc 1 N := by simp; omega
  have h8 : 8 ∈ Icc 1 N := by simp; omega
  have h12 : 12 ∈ Icc 1 N := by simp; omega
  have ha := sharp_unchanged_phase_bound N 8 12 t h2 h8 h12 (by decide) (by decide) ht h D herr
  have hb := sharp_flipped_phase_bound N 8 12 t h2 h8 h12 (by decide) ht h D herr
  have hp := phase_incompatibility (translationPhase N 8 h) (translationPhase N 12 h) 2 3
    (by rw [translationPhase_norm]) (by rw [translationPhase_norm]) ⟨1, rfl⟩
    (translationPhase_eight_twelve N hN h)
  norm_num at hp
  have hh := mul_le_mul_of_nonneg_left hp ht
  nlinarith only [hh, ha, hb]

theorem sharp_separation_six (N : ℕ) (hN : 20 ≤ N) (t : ℝ) (ht : 0 ≤ t) (h : ℕ) (D : ℝ)
    (herr : ∀ n, |sieveSeq N (sharpFlippedWeights N 12 20 t) n-
      sieveSeq N (sharpWeights N 12 20 t) (n+h)| ≤ D) : 2*t ≤ 8*D := by
  have h2 : 2 ∈ Icc 1 N := by simp; omega
  have h12 : 12 ∈ Icc 1 N := by simp; omega
  have h20 : 20 ∈ Icc 1 N := by simp; omega
  have ha := sharp_unchanged_phase_bound N 12 20 t h2 h12 h20 (by decide) (by decide) ht h D herr
  have hb := sharp_flipped_phase_bound N 12 20 t h2 h12 h20 (by decide) ht h D herr
  have hp := phase_incompatibility (translationPhase N 12 h) (translationPhase N 20 h) 3 5
    (by rw [translationPhase_norm]) (by rw [translationPhase_norm]) ⟨2, rfl⟩
    (translationPhase_twelve_twenty N hN h)
  norm_num at hp
  have hh := mul_le_mul_of_nonneg_left hp ht
  nlinarith only [hh, ha, hb]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
