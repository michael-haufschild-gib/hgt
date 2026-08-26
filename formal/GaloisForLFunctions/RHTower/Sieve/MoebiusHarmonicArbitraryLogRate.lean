import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicLogRate
import GaloisForLFunctions.HTGeometry.ReciprocalLogPowerTailGeneral

/-!
# Arbitrary logarithmic decay for the Möbius harmonic sum

The unconditional stretched-exponential Mertens saving beats every fixed power of the logarithm.
Combined with the generic reciprocal-log integral test and the exact Abel tail identity, this gives
arbitrary inverse-log decay for `deningerHarmonicPartial`.  In particular every fixed logarithmic
power times that partial sum tends to zero.
-/

namespace RHTower.Sieve

open ArithmeticFunction Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every fixed logarithmic power is eventually absorbed by the Mertens saving. -/
theorem eventually_deningerMertensSaving_mul_log_pow_le_one (p : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      deningerMertensSaving (N : ℝ) * Real.log (N : ℝ) ^ p ≤ 1 := by
  have hdom : ∀ᶠ u : ℝ in atTop,
      (1 : ℝ) * u ^ (p : ℝ) ≤
        Real.exp (((1 : ℝ) / 108) * u ^ ((1 : ℝ) / 3)) :=
    eventually_mul_rpow_le_exp_rpow 1 (c := (1 : ℝ) / 108)
      (δ := (1 : ℝ) / 3) (p := (p : ℝ)) (by norm_num) (by norm_num)
  have hcomp : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) * Real.log (N : ℝ) ^ (p : ℝ) ≤
        Real.exp (((1 : ℝ) / 108) *
          Real.log (N : ℝ) ^ ((1 : ℝ) / 3)) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hdom
  filter_upwards [hcomp, eventually_gt_atTop 1] with N hdomN hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hexp :
      Real.exp (-(Real.log (N : ℝ) ^ ((1 : ℝ) / 3) / 108)) *
          Real.exp (((1 : ℝ) / 108) *
            Real.log (N : ℝ) ^ ((1 : ℝ) / 3)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hdomN' : Real.log (N : ℝ) ^ p ≤
      Real.exp (((1 : ℝ) / 108) *
        Real.log (N : ℝ) ^ ((1 : ℝ) / 3)) := by
    calc
      Real.log (N : ℝ) ^ p = Real.log (N : ℝ) ^ (p : ℝ) :=
        (Real.rpow_natCast _ p).symm
      _ ≤ _ := by simpa only [one_mul] using hdomN
  rw [deningerMertensSaving]
  calc
    Real.exp (-(Real.log (N : ℝ) ^ ((1 : ℝ) / 3) / 108)) *
        Real.log (N : ℝ) ^ p
      ≤ Real.exp (-(Real.log (N : ℝ) ^ ((1 : ℝ) / 3) / 108)) *
          Real.exp (((1 : ℝ) / 108) *
            Real.log (N : ℝ) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left hdomN' (Real.exp_pos _).le
    _ = 1 := hexp

/-- Mertens summatory bound weakened to any prescribed inverse logarithmic power. -/
theorem deningerMertensM_log_pow_rate (p : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |mertensM N| ≤ B * (N : ℝ) / Real.log (N : ℝ) ^ p := by
  obtain ⟨B, hB, hrate⟩ := RHTower.deningerMertensM_rate
  refine ⟨B, hB, ?_⟩
  filter_upwards [hrate,
    eventually_deningerMertensSaving_mul_log_pow_le_one p,
    eventually_gt_atTop 1] with N hrateN hsave hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hsave' : deningerMertensSaving (N : ℝ) ≤
      1 / Real.log (N : ℝ) ^ p := by
    rw [le_div_iff₀ (pow_pos hlog p)]
    simpa [mul_comm] using hsave
  calc
    |mertensM N| ≤ B * (N : ℝ) * deningerMertensSaving (N : ℝ) := hrateN
    _ ≤ B * (N : ℝ) * (1 / Real.log (N : ℝ) ^ p) := by
      exact mul_le_mul_of_nonneg_left hsave'
        (mul_nonneg hB (Nat.cast_nonneg N))
    _ = B * (N : ℝ) / Real.log (N : ℝ) ^ p := by ring

private theorem abs_mertensHarmonicTerm_le_log_pow
    {B : ℝ} (hB : 0 ≤ B) {p k : ℕ} (hk : 1 < k)
    (hrate : |mertensM k| ≤
      B * (k : ℝ) / Real.log (k : ℝ) ^ p) :
    |mertensM k / ((k : ℝ) * ((k : ℝ) + 1))| ≤
      B * (1 / ((k : ℝ) * Real.log (k : ℝ) ^ p)) := by
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  rw [abs_div, abs_of_pos (mul_pos hk0 (by linarith))]
  rw [div_le_iff₀ (mul_pos hk0 (by linarith))]
  calc
    |mertensM k| ≤ B * (k : ℝ) / Real.log (k : ℝ) ^ p := hrate
    _ ≤ (B * (1 / ((k : ℝ) * Real.log (k : ℝ) ^ p))) *
        ((k : ℝ) * ((k : ℝ) + 1)) := by
      have hden : 0 < Real.log (k : ℝ) ^ p := pow_pos hlog p
      field_simp
      nlinarith [hB]

/-- Arbitrary inverse-log rate for the Möbius harmonic partial sums. -/
theorem exists_abs_deningerHarmonicPartial_log_pow_rate
    (p : ℕ) (hp : 0 < p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |RHTower.deningerHarmonicPartial N| ≤
        2 * B / Real.log (N : ℝ) ^ (p + 1) +
          B / ((p : ℝ) * Real.log (N : ℝ) ^ p) := by
  obtain ⟨B, hB, hrate⟩ := deningerMertensM_log_pow_rate (p + 1)
  rw [Filter.eventually_atTop] at hrate
  obtain ⟨K, hK⟩ := hrate
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop K, eventually_gt_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (Real.exp 1)]
      with N hNK hN1 hNe
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hrateN := hK N hNK
  have hboundary : |mertensM N / (N : ℝ)| ≤
      B / Real.log (N : ℝ) ^ (p + 1) := by
    rw [abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    calc
      |mertensM N| ≤
          B * (N : ℝ) / Real.log (N : ℝ) ^ (p + 1) := hrateN
      _ = (B / Real.log (N : ℝ) ^ (p + 1)) * (N : ℝ) := by ring
  let f : ℕ → ℝ := fun i => mertensM (i + N) /
    (((i + N : ℕ) : ℝ) * (((i + N : ℕ) : ℝ) + 1))
  have hsumm : Summable f := by
    exact (summable_nat_add_iff N).mpr RHTower.deningerMertensHarmonic_summable
  have hsumm_abs : Summable (fun i => |f i|) := hsumm.abs
  have hterm : ∀ i : ℕ, |f i| ≤
      B * (1 / (((i + N : ℕ) : ℝ) *
        Real.log ((i + N : ℕ) : ℝ) ^ (p + 1))) := by
    intro i
    apply abs_mertensHarmonicTerm_le_log_pow hB
    · omega
    · exact hK (i + N) (le_trans hNK (Nat.le_add_left N i))
  have htsum_abs : (∑' i : ℕ, |f i|) ≤
      B * (1 / ((N : ℝ) * Real.log (N : ℝ) ^ (p + 1))) +
        B * (1 / ((p : ℝ) * Real.log (N : ℝ) ^ p)) := by
    refine le_of_tendsto' hsumm_abs.hasSum.tendsto_sum_nat ?_
    intro a
    rcases a with _ | a
    · simp
      positivity
    · rw [Finset.sum_range_succ']
      have hshift : ∑ i ∈ Finset.range a, |f (i + 1)| ≤
          B * (1 / ((p : ℝ) * Real.log (N : ℝ) ^ p)) := by
        calc
          ∑ i ∈ Finset.range a, |f (i + 1)| ≤
              ∑ i ∈ Finset.range a,
                B * (1 / (((N + (i + 1 : ℕ) : ℕ) : ℝ) *
                  Real.log ((N + (i + 1 : ℕ) : ℕ) : ℝ) ^ (p + 1))) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have ht := hterm (i + 1)
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
          _ = B * ∑ i ∈ Finset.range a,
              1 / (((N : ℝ) + ((i : ℝ) + 1)) *
                Real.log ((N : ℝ) + ((i : ℝ) + 1)) ^ (p + 1)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i hi => ?_
            push_cast
            ring
          _ ≤ B * (1 / ((p : ℝ) * Real.log (N : ℝ) ^ p)) := by
            exact mul_le_mul_of_nonneg_left
              (sum_one_div_mul_log_pow_succ_le hp hNe a) hB
      have hzero := hterm 0
      simp only [zero_add] at hzero
      linarith
  have htail : |∑' i : ℕ, f i| ≤
      B * (1 / ((N : ℝ) * Real.log (N : ℝ) ^ (p + 1))) +
        B * (1 / ((p : ℝ) * Real.log (N : ℝ) ^ p)) := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_tsum_le_tsum_norm
      (by simpa [Real.norm_eq_abs] using hsumm_abs))
      (by simpa [Real.norm_eq_abs] using htsum_abs)
  rw [deningerHarmonicPartial_eq_mertens_boundary_sub_tail]
  have hsplit := abs_sub (mertensM N / (N : ℝ)) (∑' i : ℕ, f i)
  have hfirst :
      B * (1 / ((N : ℝ) * Real.log (N : ℝ) ^ (p + 1))) ≤
        B / Real.log (N : ℝ) ^ (p + 1) := by
    have hInvN : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one hN0]
      exact le_of_lt hNR
    have hden : 0 < Real.log (N : ℝ) ^ (p + 1) := pow_pos hlog (p + 1)
    calc
      B * (1 / ((N : ℝ) * Real.log (N : ℝ) ^ (p + 1))) =
          (B / Real.log (N : ℝ) ^ (p + 1)) * (1 / (N : ℝ)) := by ring
      _ ≤ (B / Real.log (N : ℝ) ^ (p + 1)) * 1 := by
        exact mul_le_mul_of_nonneg_left hInvN (div_nonneg hB hden.le)
      _ = B / Real.log (N : ℝ) ^ (p + 1) := by ring
  dsimp only [f] at htail hsplit
  calc
    |mertensM N / (N : ℝ) - ∑' i : ℕ,
        mertensM (i + N) /
          (((i + N : ℕ) : ℝ) * (((i + N : ℕ) : ℝ) + 1))| ≤
        |mertensM N / (N : ℝ)| + |∑' i : ℕ,
          mertensM (i + N) /
            (((i + N : ℕ) : ℝ) * (((i + N : ℕ) : ℝ) + 1))| := hsplit
    _ ≤ B / Real.log (N : ℝ) ^ (p + 1) +
        (B * (1 / ((N : ℝ) * Real.log (N : ℝ) ^ (p + 1))) +
          B * (1 / ((p : ℝ) * Real.log (N : ℝ) ^ p))) :=
      add_le_add hboundary htail
    _ ≤ 2 * B / Real.log (N : ℝ) ^ (p + 1) +
        B / ((p : ℝ) * Real.log (N : ℝ) ^ p) := by
      calc
        B / Real.log (N : ℝ) ^ (p + 1) +
            (B * (1 / ((N : ℝ) * Real.log (N : ℝ) ^ (p + 1))) +
              B * (1 / ((p : ℝ) * Real.log (N : ℝ) ^ p))) ≤
            B / Real.log (N : ℝ) ^ (p + 1) +
              (B / Real.log (N : ℝ) ^ (p + 1) +
                B * (1 / ((p : ℝ) * Real.log (N : ℝ) ^ p))) := by
          linarith
        _ = 2 * B / Real.log (N : ℝ) ^ (p + 1) +
            B / ((p : ℝ) * Real.log (N : ℝ) ^ p) := by ring

/-- The Möbius harmonic partial sums admit an eventual pure inverse-log envelope of every
positive integral order. -/
theorem exists_abs_deningerHarmonicPartial_le_const_div_log_pow
    (p : ℕ) (hp : 0 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |RHTower.deningerHarmonicPartial N| ≤ C / Real.log (N : ℝ) ^ p := by
  obtain ⟨B, hB, hrate⟩ :=
    exists_abs_deningerHarmonicPartial_log_pow_rate p hp
  refine ⟨3 * B, by positivity, ?_⟩
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    have hevent : ∀ᶠ N : ℕ in atTop, Real.exp 1 ≤ (N : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 1)
    filter_upwards [hevent] with N hN
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hN
  filter_upwards [hrate, hlog] with N hrateN hlogN
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogN
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpowpos : 0 < Real.log (N : ℝ) ^ p := pow_pos hlogpos p
  have hpow_le : Real.log (N : ℝ) ^ p ≤ Real.log (N : ℝ) ^ (p + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right hpowpos.le hlogN
  have hfirst : 2 * B / Real.log (N : ℝ) ^ (p + 1) ≤
      2 * B / Real.log (N : ℝ) ^ p := by
    exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hB)
      hpowpos hpow_le
  have hsecond : B / ((p : ℝ) * Real.log (N : ℝ) ^ p) ≤
      B / Real.log (N : ℝ) ^ p := by
    have hden : Real.log (N : ℝ) ^ p ≤
        (p : ℝ) * Real.log (N : ℝ) ^ p := by
      exact le_mul_of_one_le_left hpowpos.le hpR
    exact div_le_div_of_nonneg_left hB hpowpos hden
  calc
    |RHTower.deningerHarmonicPartial N| ≤
        2 * B / Real.log (N : ℝ) ^ (p + 1) +
          B / ((p : ℝ) * Real.log (N : ℝ) ^ p) := hrateN
    _ ≤ 2 * B / Real.log (N : ℝ) ^ p +
          B / Real.log (N : ℝ) ^ p := add_le_add hfirst hsecond
    _ = 3 * B / Real.log (N : ℝ) ^ p := by ring

/-- Every fixed logarithmic power kills the Möbius harmonic partial sum. -/
theorem tendsto_log_pow_mul_deningerHarmonicPartial_zero (q : ℕ) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ q *
      RHTower.deningerHarmonicPartial N) atTop (nhds 0) := by
  obtain ⟨B, hB, hrate⟩ :=
    exists_abs_deningerHarmonicPartial_log_pow_rate (q + 1) (by omega)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => 1 / Real.log (N : ℝ))
      atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).div_atTop hlog)
  have hmajor : Tendsto (fun N : ℕ =>
      2 * B / Real.log (N : ℝ) ^ 2 +
        (B / ((q + 1 : ℕ) : ℝ)) * (1 / Real.log (N : ℝ)))
      atTop (nhds 0) := by
    have hsq := (hinv.pow 2).const_mul (2 * B)
    have hone := hinv.const_mul (B / ((q + 1 : ℕ) : ℝ))
    have hsq' : Tendsto (fun N : ℕ =>
        2 * B / Real.log (N : ℝ) ^ 2) atTop (nhds 0) := by
      convert hsq using 1 <;> simp [div_eq_mul_inv, pow_two, mul_assoc]
    simpa only [mul_zero, add_zero] using hsq'.add hone
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hmajor
  filter_upwards [hrate, eventually_gt_atTop 1] with N hrateN hN1
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hqR : (((q + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hlogN]
  have hmul := mul_le_mul_of_nonneg_left hrateN (pow_nonneg hlogN.le q)
  calc
    Real.log (N : ℝ) ^ q * |RHTower.deningerHarmonicPartial N| ≤
        Real.log (N : ℝ) ^ q *
          (2 * B / Real.log (N : ℝ) ^ (q + 1 + 1) +
            B / (((q + 1 : ℕ) : ℝ) *
              Real.log (N : ℝ) ^ (q + 1))) := hmul
    _ = 2 * B / Real.log (N : ℝ) ^ 2 +
        (B / ((q + 1 : ℕ) : ℝ)) * (1 / Real.log (N : ℝ)) := by
      rw [show q + 1 + 1 = q + 2 by omega, pow_add, pow_succ]
      field_simp [hlogN.ne', hqR]
      ring

end

end RHTower.Sieve
