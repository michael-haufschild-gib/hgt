import GaloisForLFunctions.RHTower.GaussComponentSampledRatioPrime
import GaloisForLFunctions.RHTower.GaussComponentSampledEnergyBounds

/-!
# The integer frequency lattice of a Gauss component

The Fourier data of the quasi-inner block are indexed by all integer frequencies, with the
reality relation `d_{-i} = conj d_i` and `d_0 = 0`.  This module puts the sampled Gauss component
on that lattice and proves the shifted ratio law at *every* integer shift:

`d_{i+j}/d_i - exp(2π i j δ_i) → 0`  as `i → ∞`,  `δ_i = (log i - log log p)/(m log p)`.

Nonnegative shifts are the forward ratio law; negative shifts come from the backward law after a
shift of the index, together with the fact that the phase moves by `o(1)` over a fixed shift.
-/

namespace RHTower

open Filter Topology

noncomputable section

/-! ## The lattice -/

/-- Height of the integer frequency `i` on the prime logarithmic lattice. -/
def gaussPrimeSampleHeightInt (p : Nat.Primes) (i : ℤ) : ℝ :=
  2 * Real.pi * (i : ℝ) / Real.log (p : ℝ)

theorem gaussPrimeSampleHeightInt_natSucc (p : Nat.Primes) (n : ℕ) :
    gaussPrimeSampleHeightInt p ((n : ℤ) + 1) = gaussPrimeSampleHeight p n := by
  rw [gaussPrimeSampleHeightInt, gaussPrimeSampleHeight]
  push_cast
  ring

theorem gaussPrimeSampleHeightInt_pos (p : Nat.Primes) {i : ℤ} (hi : 0 < i) :
    0 < gaussPrimeSampleHeightInt p i := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [gaussPrimeSampleHeightInt]
  positivity

/-- The sampled Gauss component on the integer frequency lattice, with the reality relation
`d_{-i} = conj d_i` and the vanishing central mode. -/
def gaussSampleValue {m : ℕ} (k : Fin m) (p : Nat.Primes) (i : ℤ) : ℂ :=
  if 0 < i then gaussComponentVerticalValue k (gaussPrimeSampleHeightInt p i)
  else if i < 0 then
    starRingEnd ℂ (gaussComponentVerticalValue k (gaussPrimeSampleHeightInt p (-i)))
  else 0

theorem gaussSampleValue_of_pos {m : ℕ} (k : Fin m) (p : Nat.Primes) {i : ℤ} (hi : 0 < i) :
    gaussSampleValue k p i = gaussComponentVerticalValue k (gaussPrimeSampleHeightInt p i) := by
  rw [gaussSampleValue, if_pos hi]

@[simp] theorem gaussSampleValue_zero {m : ℕ} (k : Fin m) (p : Nat.Primes) :
    gaussSampleValue k p 0 = 0 := by
  rw [gaussSampleValue]
  norm_num

/-- The reality relation on the frequency lattice. -/
theorem gaussSampleValue_neg {m : ℕ} (k : Fin m) (p : Nat.Primes) (i : ℤ) :
    gaussSampleValue k p (-i) = starRingEnd ℂ (gaussSampleValue k p i) := by
  rcases lt_trichotomy i 0 with hi | hi | hi
  · have hpos : 0 < -i := by omega
    rw [gaussSampleValue_of_pos k p hpos, gaussSampleValue, if_neg (by omega), if_pos hi]
    rw [Complex.conj_conj]
  · subst hi
    simp
  · rw [gaussSampleValue, if_neg (by omega), if_pos (by omega), neg_neg,
      gaussSampleValue_of_pos k p hi]

theorem gaussSampleValue_ne_zero {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {i : ℤ} (hi : i ≠ 0) : gaussSampleValue k p i ≠ 0 := by
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · rw [gaussSampleValue, if_neg (by omega), if_pos hneg]
    simpa using
      gaussComponentVerticalValue_ne_zero hm k (gaussPrimeSampleHeightInt_pos p (by omega : 0 < -i))
  · rw [gaussSampleValue_of_pos k p hpos]
    exact gaussComponentVerticalValue_ne_zero hm k (gaussPrimeSampleHeightInt_pos p hpos)

theorem gaussSampleValue_natSucc {m : ℕ} (k : Fin m) (p : Nat.Primes) (n : ℕ) :
    gaussSampleValue k p ((n : ℤ) + 1) =
      gaussComponentVerticalValue k (gaussPrimeSampleHeight p n) := by
  rw [gaussSampleValue_of_pos k p (by omega), gaussPrimeSampleHeightInt_natSucc]

/-! ## The lattice phase -/

/-- The rotation exponent attached to the frequency `i`. -/
def gaussSamplePhase (m : ℕ) (p : Nat.Primes) (i : ℤ) : ℝ :=
  gaussComponentPhaseRate m p * Real.log (i : ℝ) + gaussComponentPhaseOffset m p

theorem gaussSamplePhase_natSucc (m : ℕ) (p : Nat.Primes) (n : ℕ) :
    gaussSamplePhase m p ((n : ℤ) + 1) =
      gaussComponentPhaseRate m p * Real.log ((n : ℝ) + 1) + gaussComponentPhaseOffset m p := by
  rw [gaussSamplePhase]
  push_cast
  ring

/-- Over a fixed shift the lattice phase moves by `o(1)`. -/
theorem tendsto_gaussSamplePhase_shift_sub_zero (m : ℕ) (p : Nat.Primes) (j : ℤ) :
    Tendsto (fun n : ℕ =>
      gaussSamplePhase m p ((n : ℤ) + 1 + j) - gaussSamplePhase m p ((n : ℤ) + 1))
      atTop (nhds 0) := by
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1 + (j : ℝ)) / ((n : ℝ) + 1))
      atTop (nhds 1) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) + (j : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1) := by
      have hinv : Tendsto (fun n : ℕ => (j : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
        have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
        simpa using tendsto_const_nhds.div_atTop hden
      simpa using tendsto_const_nhds.add hinv
    refine hbase.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hden : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have hlog : Tendsto (fun n : ℕ =>
      Real.log (((n : ℝ) + 1 + (j : ℝ)) / ((n : ℝ) + 1))) atTop (nhds 0) := by
    have hc := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
    simpa [Function.comp_def] using hc
  have hdiff : Tendsto (fun n : ℕ =>
      Real.log ((n : ℝ) + 1 + (j : ℝ)) - Real.log ((n : ℝ) + 1)) atTop (nhds 0) := by
    refine hlog.congr' ?_
    filter_upwards [eventually_gt_atTop j.natAbs] with n hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnjZ : (0 : ℤ) < (n : ℤ) + 1 + j := by omega
    have hnj : (0 : ℝ) < (n : ℝ) + 1 + (j : ℝ) := by exact_mod_cast hnjZ
    rw [Real.log_div hnj.ne' hn1.ne']
  have hscaled := hdiff.const_mul (gaussComponentPhaseRate m p)
  rw [mul_zero] at hscaled
  refine hscaled.congr' ?_
  filter_upwards with n
  rw [gaussSamplePhase, gaussSamplePhase]
  push_cast
  ring

/-! ## The shifted ratio law on the lattice -/

/-- Deviation of the shifted lattice ratio from its rotation. -/
def gaussSampleRatioDefect {m : ℕ} (k : Fin m) (p : Nat.Primes) (j i : ℤ) : ℂ :=
  gaussSampleValue k p (i + j) / gaussSampleValue k p i -
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
      ((gaussSamplePhase m p i : ℝ) : ℂ))

/-- **Lattice ratio law.**  At every integer shift the sampled ratio is asymptotically the
rotation prescribed by the lattice phase. -/
theorem tendsto_gaussSampleRatioDefect
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (j : ℤ) :
    Tendsto (fun n : ℕ => gaussSampleRatioDefect k p j ((n : ℤ) + 1)) atTop (nhds 0) := by
  by_cases hj : 0 ≤ j
  · -- forward shift
    obtain ⟨J, rfl⟩ : ∃ J : ℕ, j = (J : ℤ) := ⟨j.toNat, by omega⟩
    have hbase := gaussComponentPrimeSample_ratio_sub_phase_tendsto_zero hm k p J
    refine hbase.congr ?_
    intro n
    rw [gaussSampleRatioDefect, gaussSamplePhase_natSucc,
      show (n : ℤ) + 1 + (J : ℤ) = ((n + J : ℕ) : ℤ) + 1 by push_cast; ring,
      gaussSampleValue_natSucc, gaussSampleValue_natSucc]
    push_cast
    ring_nf
  · -- backward shift
    have hjneg : j < 0 := by omega
    obtain ⟨J, rfl⟩ : ∃ J : ℕ, j = -(J : ℤ) := ⟨(-j).toNat, by omega⟩
    rw [← Filter.tendsto_add_atTop_iff_nat J]
    have hback := gaussComponentPrimeSample_inv_ratio_sub_phase_tendsto_zero hm k p J
    have hshift := tendsto_gaussSamplePhase_shift_sub_zero m p (J : ℤ)
    have hcast : Tendsto (fun n : ℕ =>
        ((gaussSamplePhase m p (((n + J : ℕ) : ℤ) + 1) -
          gaussSamplePhase m p ((n : ℤ) + 1) : ℝ) : ℂ)) atTop (nhds 0) := by
      have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hshift
      simp only [Function.comp_def, Complex.ofReal_zero] at hc
      refine hc.congr ?_
      intro n
      congr 3
      push_cast
      ring
    have hmul := hcast.const_mul (2 * (Real.pi : ℂ) * Complex.I * (J : ℂ))
    rw [mul_zero] at hmul
    have hphase : Tendsto (fun n : ℕ =>
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) *
            ((gaussComponentPhaseRate m p * Real.log ((n : ℝ) + 1) +
              gaussComponentPhaseOffset m p : ℝ) : ℂ))) -
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-(J : ℤ) : ℤ) : ℂ) *
            ((gaussSamplePhase m p (((n + J : ℕ) : ℤ) + 1) : ℝ) : ℂ)))
        atTop (nhds 0) := by
      refine GaloisForLFunctions.tendsto_exp_sub_exp_zero_of_tendsto_sub_zero ?_ ?_
      · intro n
        have hform : (2 * (Real.pi : ℂ) * Complex.I * ((-(J : ℤ) : ℤ) : ℂ) *
            ((gaussSamplePhase m p (((n + J : ℕ) : ℤ) + 1) : ℝ) : ℂ))
            = ((-(2 * Real.pi * (J : ℝ) *
                gaussSamplePhase m p (((n + J : ℕ) : ℤ) + 1)) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [hform]
        simp
      · refine hmul.congr ?_
        intro n
        rw [← gaussSamplePhase_natSucc]
        push_cast
        ring
    have hsum := hback.add hphase
    rw [add_zero] at hsum
    refine hsum.congr ?_
    intro n
    rw [gaussSampleRatioDefect,
      show ((n + J : ℕ) : ℤ) + 1 + -(J : ℤ) = (n : ℤ) + 1 by push_cast; ring,
      gaussSampleValue_natSucc, gaussSampleValue_natSucc]
    ring

/-! ## Reflection of the lattice -/

/-- The lattice phase is even: it depends on the frequency only through its magnitude. -/
theorem gaussSamplePhase_neg (m : ℕ) (p : Nat.Primes) (i : ℤ) :
    gaussSamplePhase m p (-i) = gaussSamplePhase m p i := by
  rw [gaussSamplePhase, gaussSamplePhase]
  congr 2
  rw [Int.cast_neg, Real.log_neg_eq_log]

/-- **Reflection of the shifted ratio.**  Reflecting both the frequency and the shift conjugates
the defect; in particular it preserves its modulus. -/
theorem gaussSampleRatioDefect_neg {m : ℕ} (k : Fin m) (p : Nat.Primes) (j i : ℤ) :
    gaussSampleRatioDefect k p (-j) (-i)
      = starRingEnd ℂ (gaussSampleRatioDefect k p j i) := by
  have hsum : -i + -j = -(i + j) := by ring
  rw [gaussSampleRatioDefect, gaussSampleRatioDefect, hsum, gaussSampleValue_neg,
    gaussSampleValue_neg, gaussSamplePhase_neg, map_sub, map_div₀]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
  push_cast
  ring

end

end RHTower
