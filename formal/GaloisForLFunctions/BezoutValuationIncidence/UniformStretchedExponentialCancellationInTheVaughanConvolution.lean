import GaloisForLFunctions.BezoutValuationIncidence.UniformCancellationInTheUndampedVaughanConvolution
import GaloisForLFunctions.RHTower.EulerDeletionStretchedEnergy
import GaloisForLFunctions.RHTower.MobiusTwoJetLinearDensity
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
The actual Mertens and harmonic stretched-exponential bounds give a common
Vaughan convolution error for every cutoff pair. A quarter-power split retains
an explicit saving, which controls all logarithmic orders with one threshold.
-/

open Finset Filter RHTower
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem vaughan_saving_pos (x : ℝ) : 0 < DeletionStretchedEnergy.saving x :=
  Real.exp_pos _

private theorem vaughan_saving_le_one {x : ℝ} (hx : 1 ≤ x) :
    DeletionStretchedEnergy.saving x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have h := Real.rpow_nonneg (Real.log_nonneg hx) (1 / 3 : ℝ)
  change -(Real.log x ^ (1 / 3 : ℝ) / 216) ≤ 0
  linarith only [h]

private theorem vaughan_saving_anti {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    DeletionStretchedEnergy.saving y ≤ DeletionStretchedEnergy.saving x := by
  apply Real.exp_le_exp.mpr
  have h := Real.rpow_le_rpow (Real.log_nonneg hx)
    (Real.log_le_log (zero_lt_one.trans_le hx) hxy) (by norm_num : (0 : ℝ) ≤ 1 / 3)
  change -(Real.log y ^ (1 / 3 : ℝ) / 216) ≤ -(Real.log x ^ (1 / 3 : ℝ) / 216)
  linarith only [h]

private theorem vaughan_saving_sq (x : ℝ) :
    DeletionStretchedEnergy.saving x ^ 2 = deningerMertensSaving x := by
  rw [pow_two, DeletionStretchedEnergy.saving, ← Real.exp_add, deningerMertensSaving]
  congr 1
  ring

/-- The actual Mertens and harmonic stretched-exponential rates give one finite convolution bound. -/
theorem exists_uniform_pmUndampedVaughanConvolutionPrefix_stretched_bound :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∃ D₀ : ℕ, 1 ≤ D₀ ∧
      ∀ D n : ℕ, D₀ ≤ D → D ≤ n → ∀ U V : ℕ,
        |pmUndampedVaughanConvolutionPrefix U V n -
          (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
            (D : ℝ) ^ 2 + D +
              (3 * B * n + 2 * B * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 + C * n) *
                DeletionStretchedEnergy.saving D := by
  obtain ⟨B, hB, hM⟩ := deningerMertensM_rate
  obtain ⟨C, hC, hH⟩ := DeletionStretchedEnergy.harmonic_rate
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hM
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp hH
  refine ⟨B, C, hB, hC, max M₀ (max H₀ 1),
    (le_max_right H₀ 1).trans (le_max_right _ _), fun D n hD hDn U V => ?_⟩
  have hD1 : 1 ≤ D := ((le_max_right H₀ 1).trans (le_max_right M₀ _)).trans hD
  have hM' (x : ℕ) (hx : D ≤ x) :
      |∑ d ∈ Icc 1 x, moebiusReal d| ≤ (B * DeletionStretchedEnergy.saving D) * x := by
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hD1.trans hx
    have hs : DeletionStretchedEnergy.saving x ^ 2 ≤ DeletionStretchedEnergy.saving D := by
      calc
        _ ≤ DeletionStretchedEnergy.saving x := by
          have h := mul_le_mul_of_nonneg_left (vaughan_saving_le_one hx1)
            (vaughan_saving_pos (x : ℝ)).le
          simpa only [pow_two, mul_one] using h
        _ ≤ _ := vaughan_saving_anti (by exact_mod_cast hD1) (by exact_mod_cast hx)
    rw [sum_Icc_moebiusReal_eq_mertensM]
    have hmx := hM₀ x (((le_max_left M₀ _).trans hD).trans hx)
    rw [← vaughan_saving_sq] at hmx
    exact hmx.trans ((mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ B * x)).trans_eq (by ring))
  have hH' (x : ℕ) (hx : D ≤ x) :
      |deningerHarmonicPartial x| ≤ C * DeletionStretchedEnergy.saving D :=
    (hH₀ x ((((le_max_left H₀ 1).trans (le_max_right M₀ _)).trans hD).trans hx)).trans
      (mul_le_mul_of_nonneg_left
        (vaughan_saving_anti (by exact_mod_cast hD1) (by exact_mod_cast hx)) hC)
  exact (abs_pmUndampedVaughanConvolutionPrefix_sub_mean_le_uniform
    (mul_nonneg hB (vaughan_saving_pos _).le)
    (mul_nonneg hC (vaughan_saving_pos _).le) hDn hM' hH' U V).trans_eq (by ring)

/-- The stretched-exponential constant retained by a quarter-power Vaughan split. -/
def pmVaughanStretchedConstant : ℝ := (1 / 8 : ℝ) ^ (1 / 3 : ℝ) / 432

private theorem stretched_constant_pos : 0 < pmVaughanStretchedConstant := by
  unfold pmVaughanStretchedConstant
  positivity

private theorem stretched_constant_le : pmVaughanStretchedConstant ≤ 1 / 432 := by
  unfold pmVaughanStretchedConstant
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)) (by norm_num)

private theorem quarter_head_le {n : ℕ} (hn : 1 ≤ n) :
    ((⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ^ 2 +
      (⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊ : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD := Nat.floor_le (Real.rpow_nonneg hn0.le (1 / 4 : ℝ))
  have hsq : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hDsq := pow_le_pow_left₀ (Nat.cast_nonneg ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊) hD 2
  rw [hsq] at hDsq
  have hquarter : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  linarith only [hDsq, hD, hquarter]

private theorem log_square_mul_exp_le {l c : ℝ} (hl : 0 ≤ l) (hc : 0 < c) :
    l ^ 2 * Real.exp (-(2 * (c * l ^ (1 / 3 : ℝ)))) ≤
      (1 / c) ^ 6 * (6.factorial : ℝ) * Real.exp (-(c * l ^ (1 / 3 : ℝ))) := by
  let t := c * l ^ (1 / 3 : ℝ)
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hcube : (l ^ (1 / 3 : ℝ)) ^ 3 = l := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl]
    norm_num
  have hpower : t ^ 6 = c ^ 6 * l ^ 2 := by
    dsimp only [t]
    have hsix : (l ^ (1 / 3 : ℝ)) ^ 6 = l ^ 2 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hcube]
    rw [mul_pow, hsix]
  have hpoly : l ^ 2 ≤ (1 / c) ^ 6 * (6.factorial : ℝ) * Real.exp t := by
    have h := Real.pow_div_factorial_le_exp t ht 6
    rw [hpower] at h
    have hf : (0 : ℝ) < 6.factorial := by positivity
    have hm := (div_le_iff₀ hf).mp h
    have heq : l ^ 2 = (1 / c) ^ 6 * (c ^ 6 * l ^ 2) := by field_simp [hc.ne']
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq (by ring)
  have hexp : Real.exp t * Real.exp (-(2 * t)) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ ((1 / c) ^ 6 * (6.factorial : ℝ) * Real.exp t) * Real.exp (-(2 * t)) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, hexp]

/-- A common stretched-exponential saving holds for every pair of Vaughan cutoffs. -/
theorem exists_uniform_pmUndampedVaughanConvolutionPrefix_stretched_rate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ U V : ℕ,
      |pmUndampedVaughanConvolutionPrefix U V n -
        (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
          C * n * Real.exp (-(pmVaughanStretchedConstant * Real.log (n : ℝ) ^ (1 / 3 : ℝ))) := by
  obtain ⟨B, C, hB, hC, D₀, hD₀, hfinite⟩ :=
    exists_uniform_pmUndampedVaughanConvolutionPrefix_stretched_bound
  let c := pmVaughanStretchedConstant
  have hc : 0 < c := stretched_constant_pos
  let D : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊
  have hDlim : Tendsto D atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop)
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨2 + 3 * B + C + 8 * B * (1 / c) ^ 6 * (6.factorial : ℝ), by positivity, ?_⟩
  filter_upwards [hDlim.eventually_ge_atTop D₀, hloglim.eventually_ge_atTop 1,
    hloglim.eventually_ge_atTop (8 * Real.log 2), eventually_ge_atTop 1]
      with n hD hlog1 hlog8 hn U V
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log (n : ℝ) := zero_le_one.trans hlog1
  let t := c * Real.log (n : ℝ) ^ (1 / 3 : ℝ)
  have ht : 0 ≤ t := mul_nonneg hc.le (Real.rpow_nonneg hl _)
  have hDn : D n ≤ n := by
    apply Nat.floor_le_of_le
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1
      (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hlogD : Real.log (n : ℝ) / 8 ≤ Real.log (D n : ℝ) := by
    have h := CubicGamma.log_floor_rpow_ge hn1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    change 1 / 4 * Real.log (n : ℝ) - Real.log 2 ≤ Real.log (D n : ℝ) at h
    linarith only [h, hlog8]
  have hsD : DeletionStretchedEnergy.saving (D n) ≤ Real.exp (-(2 * t)) := by
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ Real.log (n : ℝ) / 8)
      hlogD (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have heq : (Real.log (n : ℝ) / 8) ^ (1 / 3 : ℝ) =
        (1 / 8 : ℝ) ^ (1 / 3 : ℝ) * Real.log (n : ℝ) ^ (1 / 3 : ℝ) := by
      rw [show Real.log (n : ℝ) / 8 = (1 / 8 : ℝ) * Real.log (n : ℝ) by ring,
        Real.mul_rpow (by norm_num) hl]
    rw [heq] at hpow
    apply Real.exp_le_exp.mpr
    change -(Real.log (D n : ℝ) ^ (1 / 3 : ℝ) / 216) ≤ -(2 * t)
    dsimp only [t, c, pmVaughanStretchedConstant]
    linarith only [hpow]
  have hH : (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 ≤ 4 * Real.log (n : ℝ) ^ 2 := by
    have hsum := Sieve.sum_Icc_one_div_le_one_add_log n
    have hlin : (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
      linarith only [hsum, hlog1]
    have hnonneg : 0 ≤ ∑ k ∈ Icc 1 n, 1 / (k : ℝ) := sum_nonneg fun k _ => by positivity
    simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using pow_le_pow_left₀ hnonneg hlin 2
  have hexp_le : Real.exp (-(2 * t)) ≤ Real.exp (-t) :=
    Real.exp_le_exp.mpr (by linarith only [ht])
  have hplain : (3 * B * n + C * n) * DeletionStretchedEnergy.saving (D n) ≤
      (3 * B + C) * n * Real.exp (-t) :=
    (mul_le_mul_of_nonneg_left (hsD.trans hexp_le) (by positivity)).trans_eq (by ring)
  have hmiddle : (2 * B * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2) *
      DeletionStretchedEnergy.saving (D n) ≤
        (8 * B * (1 / c) ^ 6 * (6.factorial : ℝ)) * n * Real.exp (-t) := by
    calc
      _ ≤ (2 * B * n * (4 * Real.log (n : ℝ) ^ 2)) * Real.exp (-(2 * t)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hH (by positivity)) hsD
          (vaughan_saving_pos _).le (by positivity)
      _ = (8 * B * n) * (Real.log (n : ℝ) ^ 2 * Real.exp (-(2 * t))) := by ring
      _ ≤ (8 * B * n) * ((1 / c) ^ 6 * (6.factorial : ℝ) * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left (log_square_mul_exp_le hl hc) (by positivity)
      _ = _ := by ring
  have htail : (3 * B * n + 2 * B * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 + C * n) *
      DeletionStretchedEnergy.saving (D n) ≤
        (3 * B + C + 8 * B * (1 / c) ^ 6 * (6.factorial : ℝ)) * n * Real.exp (-t) := by
    calc
      _ = (3 * B * n + C * n) * DeletionStretchedEnergy.saving (D n) +
          (2 * B * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2) *
            DeletionStretchedEnergy.saving (D n) := by ring
      _ ≤ (3 * B + C) * n * Real.exp (-t) +
          (8 * B * (1 / c) ^ 6 * (6.factorial : ℝ)) * n * Real.exp (-t) :=
        add_le_add hplain hmiddle
      _ = _ := by ring
  have hu : Real.log (n : ℝ) ^ (1 / 3 : ℝ) ≤ Real.log (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have htlog : t ≤ Real.log (n : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_left hu hc.le
    have hc' : c ≤ 1 / 432 := stretched_constant_le
    have h' := mul_le_mul_of_nonneg_right hc' hl
    dsimp only [t]
    linarith only [h, h', hl]
  have hhalf : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) * Real.exp (-t) := by
    have hexp : Real.exp t ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hn0]
      exact Real.exp_le_exp.mpr (by simpa only [div_eq_mul_inv] using htlog)
    have he : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hsq : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = n := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hn0.le]
    have h := mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hn0.le (1 / 2 : ℝ))
    have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-t)).le
    rw [mul_assoc, he, mul_one, ← pow_two, hsq] at h'
    exact h'
  have hhead : (D n : ℝ) ^ 2 + D n ≤ 2 * n * Real.exp (-t) :=
    (quarter_head_le hn).trans ((mul_le_mul_of_nonneg_left hhalf (by norm_num)).trans_eq (by ring))
  exact (hfinite (D n) n hD hDn U V).trans
    ((add_le_add hhead htail).trans_eq (by ring))

/-- One threshold controls all logarithmic orders, with explicit factorial growth. -/
theorem exists_uniform_pmUndampedVaughanConvolutionPrefix_factorial_rate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ U V q : ℕ,
      |pmUndampedVaughanConvolutionPrefix U V n -
        (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| * Real.log (n : ℝ) ^ q ≤
          C * n * (1 / pmVaughanStretchedConstant) ^ (3 * q) * ((3 * q).factorial : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_pmUndampedVaughanConvolutionPrefix_stretched_rate
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with n hn hn1 U V q
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  let c := pmVaughanStretchedConstant
  have hc : 0 < c := stretched_constant_pos
  let t := c * Real.log (n : ℝ) ^ (1 / 3 : ℝ)
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hcube : (Real.log (n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = Real.log (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl]
    norm_num
  have hp : t ^ (3 * q) = c ^ (3 * q) * Real.log (n : ℝ) ^ q := by
    dsimp only [t]
    simp only [mul_pow, pow_mul, hcube]
  have hs := Real.pow_div_factorial_le_exp t ht (3 * q)
  rw [hp] at hs
  have hf : (0 : ℝ) < (3 * q).factorial := by positivity
  have hm := (div_le_iff₀ hf).mp hs
  have hpoly : Real.log (n : ℝ) ^ q ≤
      ((1 / c) ^ (3 * q) * ((3 * q).factorial : ℝ)) * Real.exp t := by
    have heq : Real.log (n : ℝ) ^ q =
        (1 / c) ^ (3 * q) * (c ^ (3 * q) * Real.log (n : ℝ) ^ q) := by field_simp [hc.ne']
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq (by ring)
  have he : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ ≤ (C * n * Real.exp (-t)) * Real.log (n : ℝ) ^ q :=
      mul_le_mul_of_nonneg_right (hn U V) (pow_nonneg hl q)
    _ ≤ (C * n * Real.exp (-t)) *
        (((1 / c) ^ (3 * q) * ((3 * q).factorial : ℝ)) * Real.exp t) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = C * n * (1 / c) ^ (3 * q) * ((3 * q).factorial : ℝ) *
        (Real.exp (-t) * Real.exp t) := by ring
    _ = _ := by rw [he, mul_one]

#print axioms exists_uniform_pmUndampedVaughanConvolutionPrefix_stretched_bound
#print axioms exists_uniform_pmUndampedVaughanConvolutionPrefix_stretched_rate
#print axioms exists_uniform_pmUndampedVaughanConvolutionPrefix_factorial_rate
end GaloisForLFunctions.BezoutValuationIncidence
