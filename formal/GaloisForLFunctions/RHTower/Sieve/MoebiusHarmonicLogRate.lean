import GaloisForLFunctions.RHTower.DeningerMertensSummatory
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicTailIdentity
import GaloisForLFunctions.HTGeometry.ReciprocalLogPowerTail
import GaloisForLFunctions.HTGeometry.RpowExpAsymptotics

/-!
# Logarithmic decay of the Möbius harmonic partial sums

The corpus's unconditional Mertens estimate has the zero-free-region saving

`|M(N)| <= B N exp (-(log N)^(1/3) / 108)`.

A stretched exponential beats `(log N)^(4 : ℕ)`.  The exact Abel tail identity and the integral-test
bound for `sum 1/(n (log n)^(4 : ℕ))` then give

`sum_{n <= N} mu(n)/n = O((log N)^(-3))`.

In particular, multiplication by `log N` still leaves a null sequence.  This is the quantitative
Möbius cancellation needed by Graham's Barban--Vehov evaluation.
-/

namespace RHTower.Sieve

open ArithmeticFunction Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Four logarithmic powers are eventually absorbed by the unconditional Mertens saving. -/
theorem eventually_deningerMertensSaving_mul_log_pow_four_le_one :
    ∀ᶠ N : ℕ in atTop,
      deningerMertensSaving (N : ℝ) * (Real.log (N : ℝ)) ^ 4 ≤ 1 := by
  have hdom : ∀ᶠ u : ℝ in atTop,
      (1 : ℝ) * u ^ (4 : ℝ) ≤ Real.exp (((1 : ℝ) / 108) * u ^ ((1 : ℝ) / 3)) :=
    eventually_mul_rpow_le_exp_rpow 1 (c := (1 : ℝ) / 108)
      (δ := (1 : ℝ) / 3) (p := 4) (by norm_num) (by norm_num)
  have hcomp : ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) * (Real.log (N : ℝ)) ^ (4 : ℝ) ≤
        Real.exp (((1 : ℝ) / 108) * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 3)) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hdom
  filter_upwards [hcomp, eventually_gt_atTop 1] with N hdomN hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hexp :
      Real.exp (-((Real.log (N : ℝ)) ^ ((1 : ℝ) / 3) / 108)) *
          Real.exp (((1 : ℝ) / 108) * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 3)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hdomN' : (Real.log (N : ℝ)) ^ 4 ≤
      Real.exp (((1 : ℝ) / 108) * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 3)) := by
    calc
      (Real.log (N : ℝ)) ^ (4 : ℕ) = (Real.log (N : ℝ)) ^ (4 : ℝ) :=
        (Real.rpow_natCast _ 4).symm
      _ ≤ Real.exp (((1 : ℝ) / 108) * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 3)) := by
        simpa only [one_mul] using hdomN
  rw [deningerMertensSaving]
  calc
    Real.exp (-((Real.log (N : ℝ)) ^ ((1 : ℝ) / 3) / 108)) *
        (Real.log (N : ℝ)) ^ 4
      ≤ Real.exp (-((Real.log (N : ℝ)) ^ ((1 : ℝ) / 3) / 108)) *
          Real.exp (((1 : ℝ) / 108) * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left hdomN' (Real.exp_pos _).le
    _ = 1 := hexp

/-- Integer Mertens summatory bound with the saving weakened to four inverse logarithmic powers. -/
theorem deningerMertensM_log_pow_four_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |mertensM N| ≤ B * (N : ℝ) / (Real.log (N : ℝ)) ^ 4 := by
  obtain ⟨B, hB, hrate⟩ := RHTower.deningerMertensM_rate
  refine ⟨B, hB, ?_⟩
  filter_upwards [hrate, eventually_deningerMertensSaving_mul_log_pow_four_le_one,
    eventually_gt_atTop 1] with N hrateN hsave hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
  have hsave' : deningerMertensSaving (N : ℝ) ≤ 1 / (Real.log (N : ℝ)) ^ 4 := by
    rw [le_div_iff₀ (pow_pos hlog 4)]
    simpa [mul_comm] using hsave
  calc
    |mertensM N| ≤ B * (N : ℝ) * deningerMertensSaving (N : ℝ) := hrateN
    _ ≤ B * (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ 4) := by
      exact mul_le_mul_of_nonneg_left hsave' (mul_nonneg hB (Nat.cast_nonneg N))
    _ = B * (N : ℝ) / (Real.log (N : ℝ)) ^ 4 := by ring

private theorem abs_mertensHarmonicTerm_le_log_four {B : ℝ} (hB : 0 ≤ B)
    {k : ℕ} (hk : 1 < k)
    (hrate : |mertensM k| ≤ B * (k : ℝ) / (Real.log (k : ℝ)) ^ 4) :
    |mertensM k / ((k : ℝ) * ((k : ℝ) + 1))|
      ≤ B * (1 / ((k : ℝ) * (Real.log (k : ℝ)) ^ 4)) := by
  have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  rw [abs_div, abs_of_pos (mul_pos hk0 (by linarith))]
  rw [div_le_iff₀ (mul_pos hk0 (by linarith))]
  calc
    |mertensM k| ≤ B * (k : ℝ) / (Real.log (k : ℝ)) ^ 4 := hrate
    _ ≤ (B * (1 / ((k : ℝ) * (Real.log (k : ℝ)) ^ 4))) *
        ((k : ℝ) * ((k : ℝ) + 1)) := by
      have hden : 0 < (Real.log (k : ℝ)) ^ 4 := pow_pos hlog 4
      field_simp
      nlinarith [hB]

/-- Explicit eventual `O((log N)^(-3))` estimate for the Möbius harmonic partial sums. -/
theorem exists_abs_deningerHarmonicPartial_log_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      |RHTower.deningerHarmonicPartial N| ≤
        2 * B / (Real.log (N : ℝ)) ^ 4 +
          B / (3 * (Real.log (N : ℝ)) ^ 3) := by
  obtain ⟨B, hB, hrate⟩ := deningerMertensM_log_pow_four_rate
  rw [Filter.eventually_atTop] at hrate
  obtain ⟨K, hK⟩ := hrate
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop K, eventually_gt_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (Real.exp 1)] with N hNK hN1 hNe
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hrateN := hK N hNK
  have hboundary : |mertensM N / (N : ℝ)| ≤ B / (Real.log (N : ℝ)) ^ 4 := by
    rw [abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    calc
      |mertensM N| ≤ B * (N : ℝ) / (Real.log (N : ℝ)) ^ 4 := hrateN
      _ = (B / (Real.log (N : ℝ)) ^ 4) * (N : ℝ) := by ring
  let f : ℕ → ℝ := fun i => mertensM (i + N) /
    (((i + N : ℕ) : ℝ) * (((i + N : ℕ) : ℝ) + 1))
  have hsumm : Summable f := by
    exact (summable_nat_add_iff N).mpr RHTower.deningerMertensHarmonic_summable
  have hsumm_abs : Summable (fun i => |f i|) := hsumm.abs
  have hterm : ∀ i : ℕ, |f i| ≤
      B * (1 / (((i + N : ℕ) : ℝ) * (Real.log ((i + N : ℕ) : ℝ)) ^ 4)) := by
    intro i
    apply abs_mertensHarmonicTerm_le_log_four hB
    · omega
    · exact hK (i + N) (le_trans hNK (Nat.le_add_left N i))
  have htsum_abs : (∑' i : ℕ, |f i|) ≤
      B * (1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 4)) +
        B * (1 / (3 * (Real.log (N : ℝ)) ^ 3)) := by
    refine le_of_tendsto' hsumm_abs.hasSum.tendsto_sum_nat ?_
    intro a
    rcases a with _ | a
    · simp
      positivity
    · rw [Finset.sum_range_succ']
      have hshift : ∑ i ∈ Finset.range a, |f (i + 1)| ≤
          B * (1 / (3 * (Real.log (N : ℝ)) ^ 3)) := by
        calc
          ∑ i ∈ Finset.range a, |f (i + 1)| ≤
              ∑ i ∈ Finset.range a,
                B * (1 / (((N + (i + 1 : ℕ) : ℕ) : ℝ) *
                  (Real.log ((N + (i + 1 : ℕ) : ℕ) : ℝ)) ^ 4)) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have ht := hterm (i + 1)
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
          _ = B * ∑ i ∈ Finset.range a,
              1 / (((N : ℝ) + ((i : ℝ) + 1)) *
                (Real.log ((N : ℝ) + ((i : ℝ) + 1))) ^ 4) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i hi => ?_
            push_cast
            ring
          _ ≤ B * (1 / (3 * (Real.log (N : ℝ)) ^ 3)) := by
            exact mul_le_mul_of_nonneg_left (sum_one_div_mul_log_four_le hNe a) hB
      have hzero := hterm 0
      simp only [zero_add] at hzero
      linarith
  have htail : |∑' i : ℕ, f i| ≤
      B * (1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 4)) +
        B * (1 / (3 * (Real.log (N : ℝ)) ^ 3)) := by
    rw [← Real.norm_eq_abs]
    exact le_trans (norm_tsum_le_tsum_norm (by simpa [Real.norm_eq_abs] using hsumm_abs))
      (by simpa [Real.norm_eq_abs] using htsum_abs)
  rw [deningerHarmonicPartial_eq_mertens_boundary_sub_tail]
  have hsplit := abs_sub (mertensM N / (N : ℝ)) (∑' i : ℕ, f i)
  have hfirst : B * (1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 4)) ≤
      B / (Real.log (N : ℝ)) ^ 4 := by
    have hInvN : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one hN0]
      exact le_of_lt hNR
    have hden : 0 < (Real.log (N : ℝ)) ^ 4 := pow_pos hlog 4
    calc
      B * (1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 4))
          = (B / (Real.log (N : ℝ)) ^ 4) * (1 / (N : ℝ)) := by ring
      _ ≤ (B / (Real.log (N : ℝ)) ^ 4) * 1 := by
        exact mul_le_mul_of_nonneg_left hInvN (div_nonneg hB hden.le)
      _ = B / (Real.log (N : ℝ)) ^ 4 := by ring
  dsimp only [f] at htail hsplit
  calc
    |mertensM N / (N : ℝ) - ∑' i : ℕ,
        mertensM (i + N) / (((i + N : ℕ) : ℝ) * (((i + N : ℕ) : ℝ) + 1))|
        ≤ |mertensM N / (N : ℝ)| + |∑' i : ℕ,
          mertensM (i + N) / (((i + N : ℕ) : ℝ) * (((i + N : ℕ) : ℝ) + 1))| := hsplit
    _ ≤ B / (Real.log (N : ℝ)) ^ 4 +
        (B * (1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 4)) +
          B * (1 / (3 * (Real.log (N : ℝ)) ^ 3))) :=
      add_le_add hboundary htail
    _ ≤ 2 * B / (Real.log (N : ℝ)) ^ 4 +
        B / (3 * (Real.log (N : ℝ)) ^ 3) := by
      have hlog4 : 0 < (Real.log (N : ℝ)) ^ 4 := pow_pos hlog 4
      calc
        B / (Real.log (N : ℝ)) ^ 4 +
            (B * (1 / ((N : ℝ) * (Real.log (N : ℝ)) ^ 4)) +
              B * (1 / (3 * (Real.log (N : ℝ)) ^ 3)))
            ≤ B / (Real.log (N : ℝ)) ^ 4 +
              (B / (Real.log (N : ℝ)) ^ 4 +
                B * (1 / (3 * (Real.log (N : ℝ)) ^ 3))) := by linarith
        _ = 2 * B / (Real.log (N : ℝ)) ^ 4 +
            B / (3 * (Real.log (N : ℝ)) ^ 3) := by ring

private theorem tendsto_one_div_log_nat_pow_two :
    Tendsto (fun N : ℕ => 1 / (Real.log (N : ℝ)) ^ 2) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ 2) atTop atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ hlog
    filter_upwards [hlog.eventually_ge_atTop (1 : ℝ)] with N hN
    nlinarith [sq_nonneg (Real.log (N : ℝ))]
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop hpow)

private theorem tendsto_one_div_log_nat_pow_three :
    Tendsto (fun N : ℕ => 1 / (Real.log (N : ℝ)) ^ 3) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ 3) atTop atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ hlog
    filter_upwards [hlog.eventually_ge_atTop (1 : ℝ)] with N hN
    nlinarith [sq_nonneg (Real.log (N : ℝ))]
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop hpow)

/-- The Möbius harmonic partial sums decay faster than the inverse logarithm. -/
theorem tendsto_log_mul_deningerHarmonicPartial_zero :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) * RHTower.deningerHarmonicPartial N)
      atTop (𝓝 0) := by
  obtain ⟨B, hB, hpartial⟩ := exists_abs_deningerHarmonicPartial_log_rate
  have hbound : ∀ᶠ N : ℕ in atTop,
      |Real.log (N : ℝ) * RHTower.deningerHarmonicPartial N| ≤
        2 * B / (Real.log (N : ℝ)) ^ 3 + B / (3 * (Real.log (N : ℝ)) ^ 2) := by
    filter_upwards [hpartial, eventually_gt_atTop 1] with N hpart hN1
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
    have hmul := mul_le_mul_of_nonneg_left hpart hlog.le
    rw [abs_mul, abs_of_pos hlog]
    calc
      Real.log (N : ℝ) * |RHTower.deningerHarmonicPartial N| ≤
          Real.log (N : ℝ) *
            (2 * B / (Real.log (N : ℝ)) ^ 4 +
              B / (3 * (Real.log (N : ℝ)) ^ 3)) := hmul
      _ = 2 * B / (Real.log (N : ℝ)) ^ 3 +
          B / (3 * (Real.log (N : ℝ)) ^ 2) := by
        field_simp
  have hmajor : Tendsto (fun N : ℕ =>
      2 * B / (Real.log (N : ℝ)) ^ 3 + B / (3 * (Real.log (N : ℝ)) ^ 2))
      atTop (𝓝 0) := by
    have h3 := tendsto_one_div_log_nat_pow_three.const_mul (2 * B)
    have h2 := tendsto_one_div_log_nat_pow_two.const_mul (B / 3)
    convert h3.add h2 using 1 <;> simp <;> ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hmajor
  filter_upwards [hbound] with N hN
  simpa [Real.norm_eq_abs] using hN

end

end RHTower.Sieve
