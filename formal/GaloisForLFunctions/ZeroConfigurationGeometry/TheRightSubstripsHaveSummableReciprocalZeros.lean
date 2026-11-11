import GaloisForLFunctions.BiScaleUncertainty.ZeroDensityFilteredCriticalDeficitLaw
import GaloisForLFunctions.HTGeometry.CountableDivisorConvergenceExponent
import GaloisForLFunctions.RHTower.XiOrdinateCosineMass

/-!
# Reciprocal summability in every right substrip

Ingham's density deficit makes the reciprocal ordinates summable on every
fixed substrip strictly right of the critical line. Dyadic buckets retain
multiplicities and turn the density estimate into a geometric series.
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

/-- Reciprocal ordinates are absolutely summable in every fixed right substrip,
with every multiplicity copy retained. -/
theorem summable_rightSubstrip_inv_abs_ordinate {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} =>
      |xiCopyOrdinate q.1|⁻¹) := by
  classical
  let θ := min ((σ - 1 / 2) / 2) (1 / 4)
  have hθ : 0 < θ := lt_min (by linarith only [hσ]) (by norm_num)
  have hθ4 : θ ≤ 1 / 4 := min_le_right _ _
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
  refine summable_of_bucket _ (fun q => inv_nonneg.mpr (abs_nonneg _)) b hfib
    (fun n => ((2 : ℝ) ^ n)⁻¹)
    (fun q => inv_anti₀ (by positivity) (ordinateBucket_bounds q.1).1) ?_
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let r := Real.exp (-(θ / 3) * Real.log 2)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hθ hlog2])
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
        ((2 : ℝ) ^ n)⁻¹ ≤
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
    have hexp : ((2 : ℝ) ^ n) ^ (1 - θ / 3) * ((2 : ℝ) ^ n)⁻¹ = r ^ n := by
      dsimp only [r]
      rw [Real.rpow_def_of_pos (by positivity), Real.log_pow,
        show ((2 : ℝ) ^ n)⁻¹ = Real.exp (-((n : ℝ) * Real.log 2)) by
          rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)],
        ← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ (4 * (D * (1 + (n : ℝ) * Real.log 2) ^ B *
          ((2 : ℝ) ^ n) ^ (1 - θ / 3))) * ((2 : ℝ) ^ n)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcR :
            ({q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} | b q = n}.ncard : ℝ) ≤
              4 * ((zeroHeightBox (1 / 2 + θ) ((2 : ℝ) ^ n)).ncard : ℝ) := by
          exact_mod_cast hcard n
        exact hcR.trans (mul_le_mul_of_nonneg_left hc' (by norm_num))
      _ ≤ (4 * D * ((1 + Real.log 2) ^ B * ((n : ℝ) + 1) ^ B)) *
          (((2 : ℝ) ^ n) ^ (1 - θ / 3) * ((2 : ℝ) ^ n)⁻¹) := by
        have hm := mul_le_mul_of_nonneg_left hpoly
          (show 0 ≤ 4 * D * (((2 : ℝ) ^ n) ^ (1 - θ / 3) * ((2 : ℝ) ^ n)⁻¹) by positivity)
        nlinarith only [hm]
      _ = _ := by rw [hexp]; ring
  rw [← summable_nat_add_iff N₀]
  exact ((summable_nat_add_iff N₀).mpr hmajor).of_nonneg_of_le
    (fun n => by positivity) (fun n => hbound (n + N₀) (by omega))

/-- The actual reciprocal zeros, not just their ordinates, are absolutely summable
strictly right of the critical line. -/
theorem summable_rightSubstrip_norm_inv {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re} => ‖(q.1.1 : ℂ)‖⁻¹) := by
  refine (summable_rightSubstrip_inv_abs_ordinate hσ).of_nonneg_of_le
    (fun q => inv_nonneg.mpr (norm_nonneg _)) fun q => ?_
  exact inv_anti₀ (by have h := four_lt_abs_xiCopyOrdinate q.1; linarith only [h])
    (Complex.abs_im_le_norm _)

private theorem norm_normalizedZeroTerm_le {β u : ℝ} (hu : 0 ≤ u)
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≤ β) :
    ‖Complex.exp (((q.1 : ℂ) - (β : ℂ)) * (u : ℂ)) / (q.1 : ℂ)‖ ≤
      ‖(q.1 : ℂ)‖⁻¹ := by
  rw [norm_div, Complex.norm_exp]
  have he : (((q.1 : ℂ) - (β : ℂ)) * (u : ℂ)).re ≤ 0 := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hq) hu
  simpa only [one_div] using
    div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr he) (norm_nonneg (q.1 : ℂ))

private theorem tendsto_normalizedZeroTerm_zero {β : ℝ} (q : XiZeroCopy)
    (hq : (q.1 : ℂ).re < β) :
    Tendsto (fun u : ℝ =>
      Complex.exp (((q.1 : ℂ) - (β : ℂ)) * (u : ℂ)) / (q.1 : ℂ)) atTop (𝓝 0) := by
  have hp : 0 < β - (q.1 : ℂ).re := sub_pos.mpr hq
  have hl := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hp tendsto_id))
  have he : Tendsto (fun u : ℝ =>
      Complex.exp (((q.1 : ℂ) - (β : ℂ)) * (u : ℂ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine hl.congr fun u => ?_
    change Real.exp (-((β - (q.1 : ℂ).re) * u)) =
      ‖Complex.exp (((q.1 : ℂ) - (β : ℂ)) * (u : ℂ))‖
    rw [Complex.norm_exp]
    apply congrArg Real.exp
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring
  simpa only [zero_div] using he.div_const (q.1 : ℂ)

/-- In an absolutely summable right substrip, normalization retains precisely the
zeros on the bounding line. No gap below that line is required. -/
theorem tendsto_rightSubstrip_sum_sub_boundary {σ β : ℝ} (hσ : 1 / 2 < σ)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    Tendsto (fun u : ℝ =>
      (∑' q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re},
        Complex.exp (((q.1.1 : ℂ) - (β : ℂ)) * (u : ℂ)) / (q.1.1 : ℂ)) -
      ∑' q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re},
        if (q.1.1 : ℂ).re = β then
          Complex.exp (((q.1.1 : ℂ) - (β : ℂ)) * (u : ℂ)) / (q.1.1 : ℂ)
        else 0) atTop (𝓝 0) := by
  classical
  let term := fun (u : ℝ) (q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re}) =>
    Complex.exp (((q.1.1 : ℂ) - (β : ℂ)) * (u : ℂ)) / (q.1.1 : ℂ)
  let boundary := fun (u : ℝ) (q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re}) =>
    if (q.1.1 : ℂ).re = β then term u q else 0
  have hs := summable_rightSubstrip_norm_inv hσ
  have hterm (u : ℝ) (hu : 0 ≤ u) : Summable (term u) :=
    Summable.of_norm_bounded hs fun q => norm_normalizedZeroTerm_le hu q.1 (hβ q.1)
  have hboundary (u : ℝ) (hu : 0 ≤ u) : Summable (boundary u) := by
    refine Summable.of_norm_bounded hs fun q => ?_
    dsimp [boundary]
    split_ifs
    · exact norm_normalizedZeroTerm_le hu q.1 (hβ q.1)
    · simp only [norm_zero]
      positivity
  have hpt (q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re}) :
      Tendsto (fun u : ℝ => term u q - boundary u q) atTop (𝓝 0) := by
    by_cases hq : (q.1.1 : ℂ).re = β
    · simpa only [boundary, hq, if_true, sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    · simpa only [boundary, hq, if_false, sub_zero, term] using
        tendsto_normalizedZeroTerm_zero q.1 (lt_of_le_of_ne (hβ q.1) hq)
  have hdom : ∀ᶠ u : ℝ in atTop, ∀ q : {q : XiZeroCopy // σ ≤ (q.1 : ℂ).re},
      ‖term u q - boundary u q‖ ≤ ‖(q.1.1 : ℂ)‖⁻¹ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu q
    dsimp [boundary]
    split_ifs
    · simp only [sub_self, norm_zero]
      positivity
    · simpa only [sub_zero] using norm_normalizedZeroTerm_le hu q.1 (hβ q.1)
  have h := tendsto_tsum_of_dominated_convergence hs hpt hdom
  simp only [tsum_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  exact (hterm u hu).tsum_sub (hboundary u hu)

end GaloisForLFunctions.ZeroConfigurationGeometry
