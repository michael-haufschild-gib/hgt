import GaloisForLFunctions.BiScaleUncertainty.ZeroDensityFilteredCriticalDeficitLaw
import GaloisForLFunctions.HTGeometry.CountableDivisorConvergenceExponent
import GaloisForLFunctions.RHTower.XiOrdinateCosineMass

/-!
# Subunit ordinate moments in every right substrip

The zero-density deficit pays a reciprocal power strictly below one.
Dyadic buckets retain all multiplicities. This spare power supplies a
polynomial tail rate, beyond qualitative reciprocal summability.
-/

open Complex Filter Topology Set
open _root_.RHTower

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open BiScaleUncertainty.ChebyshevGauge CountableDivisor

private theorem summable_shifted_polynomial_geometric (B : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ B * r ^ n) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (k := B)
    (show ‖r‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hr])
  have hs := ((summable_nat_add_iff 1).mpr h).mul_right r⁻¹
  refine hs.congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one]

private def ordinateBucket (q : XiZeroCopy) : ℕ :=
  ⌊Real.log |xiCopyOrdinate q| / Real.log 2⌋₊

private theorem ordinateBucket_bounds (q : XiZeroCopy) :
    (2 : ℝ) ^ ordinateBucket q ≤ |xiCopyOrdinate q| ∧
      |xiCopyOrdinate q| ≤ 2 * (2 : ℝ) ^ ordinateBucket q := by
  have hγ := four_lt_abs_xiCopyOrdinate q
  have hγ0 : 0 < |xiCopyOrdinate q| := by linarith only [hγ]
  have hγ1 : 1 ≤ |xiCopyOrdinate q| := by linarith only [hγ]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : 0 ≤ Real.log |xiCopyOrdinate q| / Real.log 2 :=
    div_nonneg (Real.log_nonneg hγ1) hlog2.le
  have hlo := (le_div_iff₀ hlog2).mp (Nat.floor_le hnn)
  have hhi := (div_lt_iff₀ hlog2).mp
    (Nat.lt_floor_add_one (Real.log |xiCopyOrdinate q| / Real.log 2))
  have he (n : ℕ) : Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  constructor
  · have hh := Real.exp_le_exp.mpr hlo
    rwa [Real.exp_log hγ0, he] at hh
  · have hh := Real.exp_le_exp.mpr hhi.le
    rw [Real.exp_log hγ0, add_mul, Real.exp_add, one_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), he] at hh
    simpa only [ordinateBucket, mul_comm] using hh

/-- The density deficit allows every reciprocal power above an explicit
threshold strictly below one, with all multiplicity copies retained. -/
theorem summable_rightSubstrip_ordinate_rpow {σ p : ℝ} (hσ : 1 / 2 < σ)
    (hp : 1 - min ((σ - 1 / 2) / 2) (1 / 4) / 3 < p) :
    Summable (fun q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} =>
      |xiCopyOrdinate q.1| ^ (-p)) := by
  classical
  let θ := min ((σ - 1 / 2) / 2) (1 / 4)
  have hθ : 0 < θ := lt_min (by linarith only [hσ]) (by norm_num)
  have hθ4 : θ ≤ 1 / 4 := min_le_right _ _
  have hgap : 1 - θ / 3 < p := hp
  have hp0 : 0 < p := by linarith only [hgap, hθ4]
  have hθσ : 1 / 2 + θ ≤ σ := by
    have hh := min_le_left ((σ - 1 / 2) / 2) (1 / 4)
    linarith only [hh, hσ]
  obtain ⟨D, hD, B, T₀, hT₀, hcount⟩ :=
    exists_zeroHeightBox_ncard_le_one_sub_four_thirds_uniform
      hθ (by linarith only [hθ4]) (δ := 1) zero_lt_one
  let b := fun q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} => ordinateBucket q.1
  have hsub (n : ℕ) :
      Subtype.val '' {q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} | b q = n} ⊆
        foldedHeightBox (1 / 2 + θ) ((2 : ℝ) ^ n) := by
    rintro _ ⟨q, hq, rfl⟩
    have hh := ordinateBucket_bounds q.1
    change ordinateBucket q.1 = n at hq
    rw [hq] at hh
    exact ⟨hθσ.trans (q.2.trans (re_le_foldedRe q.1)), hh⟩
  have hfib (n : ℕ) :
      {q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} | b q = n}.Finite :=
    Set.Finite.of_finite_image ((foldedHeightBox_finite _ _).subset (hsub n))
      Subtype.val_injective.injOn
  have hcard (n : ℕ) :
      {q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} | b q = n}.ncard ≤
        4 * (zeroHeightBox (1 / 2 + θ) ((2 : ℝ) ^ n)).ncard := by
    refine le_trans ?_ (ncard_foldedHeightBox_le _ _)
    exact Set.ncard_le_ncard_of_injOn Subtype.val
      (fun q hq => hsub n ⟨q, hq, rfl⟩)
      (fun _ _ _ _ h => Subtype.ext h) (foldedHeightBox_finite _ _)
  refine summable_of_bucket _ (fun q => Real.rpow_nonneg (abs_nonneg _) _) b hfib
    (fun n => ((2 : ℝ) ^ n) ^ (-p))
    (fun q => Real.rpow_le_rpow_of_nonpos (by positivity)
      (ordinateBucket_bounds q.1).1 (neg_nonpos.mpr hp0.le)) ?_
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let r := Real.exp ((1 - θ / 3 - p) * Real.log 2)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (sub_neg.mpr hgap) hlog2)
  have hmajor : Summable (fun n : ℕ =>
      (4 * D * (1 + Real.log 2) ^ B) * (((n : ℝ) + 1) ^ B * r ^ n)) :=
    (summable_shifted_polynomial_geometric B hr hr1).mul_left _
  let N₀ := ⌈Real.log T₀ / Real.log 2⌉₊
  have hN (n : ℕ) (hn : N₀ ≤ n) : T₀ ≤ (2 : ℝ) ^ n := by
    have hh : Real.log T₀ / Real.log 2 ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have he := Real.exp_le_exp.mpr ((div_le_iff₀ hlog2).mp hh)
    rwa [Real.exp_log (zero_lt_one.trans_le hT₀), Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  have hbound (n : ℕ) (hn : N₀ ≤ n) :
      ({q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} | b q = n}.ncard : ℝ) *
        ((2 : ℝ) ^ n) ^ (-p) ≤
      (4 * D * (1 + Real.log 2) ^ B) * (((n : ℝ) + 1) ^ B * r ^ n) := by
    have hc := hcount ((2 : ℝ) ^ n) (hN n hn) (1 / 2 + θ) le_rfl
      (by linarith only [hθ4])
    have hc' : ((zeroHeightBox (1 / 2 + θ) ((2 : ℝ) ^ n)).ncard : ℝ) ≤
        D * (1 + (n : ℝ) * Real.log 2) ^ B * ((2 : ℝ) ^ n) ^ (1 - θ / 3) := by
      rw [Real.log_pow] at hc
      convert hc using 1 <;> first | rfl | congr 2 <;> ring
    have hpoly : (1 + (n : ℝ) * Real.log 2) ^ B ≤
        (1 + Real.log 2) ^ B * ((n : ℝ) + 1) ^ B := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith only [hlog2, Nat.cast_nonneg (α := ℝ) n]
    have hexp : ((2 : ℝ) ^ n) ^ (1 - θ / 3) * ((2 : ℝ) ^ n) ^ (-p) = r ^ n := by
      dsimp only [r]
      rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
        Real.log_pow, ← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ (4 * (D * (1 + (n : ℝ) * Real.log 2) ^ B *
          ((2 : ℝ) ^ n) ^ (1 - θ / 3))) * ((2 : ℝ) ^ n) ^ (-p) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcR :
            ({q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} | b q = n}.ncard : ℝ) ≤
              4 * ((zeroHeightBox (1 / 2 + θ) ((2 : ℝ) ^ n)).ncard : ℝ) := by
          exact_mod_cast hcard n
        exact hcR.trans (mul_le_mul_of_nonneg_left hc' (by norm_num))
      _ ≤ (4 * D * ((1 + Real.log 2) ^ B * ((n : ℝ) + 1) ^ B)) *
          (((2 : ℝ) ^ n) ^ (1 - θ / 3) * ((2 : ℝ) ^ n) ^ (-p)) := by
        have hm := mul_le_mul_of_nonneg_left hpoly
          (show 0 ≤ 4 * D * (((2 : ℝ) ^ n) ^ (1 - θ / 3) * ((2 : ℝ) ^ n) ^ (-p)) by positivity)
        nlinarith only [hm]
      _ = _ := by rw [hexp]; ring
  rw [← summable_nat_add_iff N₀]
  exact ((summable_nat_add_iff N₀).mpr hmajor).of_nonneg_of_le
    (fun n => by positivity) (fun n => hbound (n + N₀) (by omega))

/-- Every fixed right substrip has a summable ordinate moment of order
strictly between zero and one. -/
theorem exists_summable_rightSubstrip_subunit_moment {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      Summable (fun q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} =>
        |xiCopyOrdinate q.1| ^ (-p)) := by
  let θ := min ((σ - 1 / 2) / 2) (1 / 4)
  have hθ : 0 < θ := lt_min (by linarith only [hσ]) (by norm_num)
  have hθ4 : θ ≤ 1 / 4 := min_le_right _ _
  refine ⟨1 - θ / 6, by linarith only [hθ4], by linarith only [hθ], ?_⟩
  exact summable_rightSubstrip_ordinate_rpow hσ (by
    change 1 - θ / 3 < 1 - θ / 6
    linarith only [hθ])

/-- A subunit moment gives a polynomial bound for every finite reciprocal
tail, uniformly over the choice of exterior zeros. -/
theorem sum_rightSubstrip_inverse_tail_le_moment
    {σ p Y : ℝ} (hp : p ≤ 1) (hY : 0 < Y)
    (hs : Summable (fun q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} =>
      |xiCopyOrdinate q.1| ^ (-p)))
    (F : Finset {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re})
    (hF : ∀ q ∈ F, Y ≤ |xiCopyOrdinate q.1|) :
    (∑ q ∈ F, |xiCopyOrdinate q.1|⁻¹) ≤
      Y ^ (p - 1) * ∑' q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re},
        |xiCopyOrdinate q.1| ^ (-p) := by
  have hterm (q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re}) (hq : q ∈ F) :
      |xiCopyOrdinate q.1|⁻¹ ≤ Y ^ (p - 1) * |xiCopyOrdinate q.1| ^ (-p) := by
    have hx : 0 < |xiCopyOrdinate q.1| := hY.trans_le (hF q hq)
    have he : |xiCopyOrdinate q.1| ^ (p - 1) * |xiCopyOrdinate q.1| ^ (-p) =
        |xiCopyOrdinate q.1|⁻¹ := by
      rw [← Real.rpow_add hx, show p - 1 + -p = -(1 : ℝ) by ring,
        Real.rpow_neg hx.le, Real.rpow_one]
    rw [← he]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hY (hF q hq) (sub_nonpos.mpr hp))
      (Real.rpow_nonneg (abs_nonneg _) _)
  calc
    _ ≤ ∑ q ∈ F, Y ^ (p - 1) * |xiCopyOrdinate q.1| ^ (-p) :=
      Finset.sum_le_sum hterm
    _ = Y ^ (p - 1) * ∑ q ∈ F, |xiCopyOrdinate q.1| ^ (-p) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum F (fun q _ => Real.rpow_nonneg (abs_nonneg _) _))
      (Real.rpow_nonneg hY.le _)

/-- The same moment bounds the number of low zeros, with multiplicities. -/
theorem card_rightSubstrip_le_moment
    {σ p Y : ℝ} (hp : 0 ≤ p) (hY : 0 ≤ Y)
    (hs : Summable (fun q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} =>
      |xiCopyOrdinate q.1| ^ (-p)))
    (F : Finset {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re})
    (hF : ∀ q ∈ F, |xiCopyOrdinate q.1| ≤ Y) :
    (F.card : ℝ) ≤ Y ^ p * ∑' q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re},
      |xiCopyOrdinate q.1| ^ (-p) := by
  have hterm (q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re}) (hq : q ∈ F) :
      (1 : ℝ) ≤ Y ^ p * |xiCopyOrdinate q.1| ^ (-p) := by
    have hx : 0 < |xiCopyOrdinate q.1| := by
      have hh := four_lt_abs_xiCopyOrdinate q.1
      linarith only [hh]
    calc
      _ = |xiCopyOrdinate q.1| ^ p * |xiCopyOrdinate q.1| ^ (-p) := by
        rw [← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hx.le (hF q hq) hp) (Real.rpow_nonneg hx.le _)
  calc
    _ = ∑ _q ∈ F, (1 : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ q ∈ F, Y ^ p * |xiCopyOrdinate q.1| ^ (-p) := Finset.sum_le_sum hterm
    _ = Y ^ p * ∑ q ∈ F, |xiCopyOrdinate q.1| ^ (-p) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum F (fun q _ => Real.rpow_nonneg (abs_nonneg _) _))
      (Real.rpow_nonneg hY _)

/-- Actual right-substrip zeros have a power-saving reciprocal tail and
a sublinear low-height count with one common constant. -/
theorem exists_rightSubstrip_power_tail_and_count {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ p C : ℝ, 0 < p ∧ p < 1 ∧ 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y →
      ∀ F : Finset {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re},
        ((∀ q ∈ F, Y ≤ |xiCopyOrdinate q.1|) →
          (∑ q ∈ F, |xiCopyOrdinate q.1|⁻¹) ≤ C * Y ^ (p - 1)) ∧
        ((∀ q ∈ F, |xiCopyOrdinate q.1| ≤ Y) → (F.card : ℝ) ≤ C * Y ^ p) := by
  obtain ⟨p, hp, hp1, hs⟩ := exists_summable_rightSubstrip_subunit_moment hσ
  refine ⟨p, ∑' q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re},
    |xiCopyOrdinate q.1| ^ (-p), hp, hp1,
    tsum_nonneg (fun q => Real.rpow_nonneg (abs_nonneg _) _), ?_⟩
  intro Y hY F
  constructor
  · intro hF
    simpa only [mul_comm] using sum_rightSubstrip_inverse_tail_le_moment hp1.le hY hs F hF
  · intro hF
    simpa only [mul_comm] using card_rightSubstrip_le_moment hp.le hY.le hs F hF

end GaloisForLFunctions.ZeroConfigurationGeometry
