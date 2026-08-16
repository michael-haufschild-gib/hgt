import GaloisForLFunctions.RHTower.GaussComponentQuantitativeRatio
import GaloisForLFunctions.RHTower.GaussSampleIntegerLattice

/-!
# Quantitative Gauss ratios on the prime Fourier lattice

This module transports the continuous forward and backward Gamma-ratio bounds
to the exact integer lattice used by the quasi-inner Gauss operator.  With
physical lattice spacing `q_p = 2π / log p`, it proves exact exponential
envelopes for both signs of a shift.

The main central-band laws remove the exponential altogether.  Whenever
`J² ≤ I`, there is a component-dependent constant `D` such that

`‖d_(I+J)/d_I - rotation‖ ≤ D (J+J²)/I`

and the corresponding backward ratio based at `I+J` satisfies the same order.
This identifies quadratic clock curvature as the precise local cost and gives
the rate input missing from all earlier qualitative `L²` translation results.
-/

namespace RHTower

open Complex Filter Topology

noncomputable section

theorem gaussPrimeSampleHeightInt_add_nat
    (p : Nat.Primes) (I J : ℕ) :
    gaussPrimeSampleHeightInt p ((I : ℤ) + (J : ℤ)) =
      gaussPrimeSampleHeightInt p (I : ℤ) + gaussPrimeSampleShift p J := by
  rw [gaussPrimeSampleHeightInt, gaussPrimeSampleHeightInt, gaussPrimeSampleShift]
  push_cast
  ring

theorem gaussPrimeSampleHeightInt_add_nat_sub_shift
    (p : Nat.Primes) (I J : ℕ) :
    gaussPrimeSampleHeightInt p ((I : ℤ) + (J : ℤ)) - gaussPrimeSampleShift p J =
      gaussPrimeSampleHeightInt p (I : ℤ) := by
  rw [gaussPrimeSampleHeightInt_add_nat]
  ring

/-- Physical spacing of the prime logarithmic lattice. -/
def gaussPrimeSampleSpacing (p : Nat.Primes) : ℝ :=
  2 * Real.pi / Real.log (p : ℝ)

theorem gaussPrimeSampleSpacing_pos (p : Nat.Primes) :
    0 < gaussPrimeSampleSpacing p := by
  rw [gaussPrimeSampleSpacing]
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.log_pos hp)

theorem gaussPrimeSampleShift_eq_spacing_mul (p : Nat.Primes) (J : ℕ) :
    gaussPrimeSampleShift p J = gaussPrimeSampleSpacing p * (J : ℝ) := by
  rw [gaussPrimeSampleShift, gaussPrimeSampleSpacing]
  ring

theorem gaussPrimeSampleHeightInt_nat_eq_spacing_mul (p : Nat.Primes) (I : ℕ) :
    gaussPrimeSampleHeightInt p (I : ℤ) = gaussPrimeSampleSpacing p * (I : ℝ) := by
  rw [gaussPrimeSampleHeightInt, gaussPrimeSampleSpacing]
  push_cast
  ring

theorem gaussPrimeSampleShift_mul_clock_int
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) {I : ℕ} (hI : 0 < I) (J : ℕ) :
    ((gaussPrimeSampleShift p J : ℝ) : ℂ) *
        gaussComponentVerticalClock m (gaussPrimeSampleHeightInt p (I : ℤ)) =
      2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) *
        ((gaussSamplePhase m p (I : ℤ) : ℝ) : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : I ≠ 0)
  have h := gaussPrimeSampleShift_mul_clock hm p n J
  have hindex : (n.succ : ℤ) = (n : ℤ) + 1 := by omega
  rw [hindex, gaussPrimeSampleHeightInt_natSucc, gaussSamplePhase_natSucc]
  exact h

/-- Quantitative forward lattice-ratio law with its exact physical envelope. -/
theorem exists_gaussSampleRatioDefect_forward_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ I J : ℕ, 0 < I →
      2 * (m : ℝ) ≤ gaussPrimeSampleHeightInt p (I : ℤ) →
      let h := gaussPrimeSampleShift p J
      let t := gaussPrimeSampleHeightInt p (I : ℤ)
      let B := (C * h + h * h) / t
      ‖gaussSampleRatioDefect k p (J : ℤ) (I : ℤ)‖ ≤ B * Real.exp B := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_gaussComponentVerticalValue_ratio_sub_clock_inv_bound hm k
  refine ⟨C, hC, ?_⟩
  intro I J hI ht
  dsimp only
  have hIZ : (0 : ℤ) < (I : ℤ) := by exact_mod_cast hI
  have hIJZ : (0 : ℤ) < (I : ℤ) + (J : ℤ) := by omega
  have hh := gaussPrimeSampleShift_nonneg p J
  have hmain := hbound (gaussPrimeSampleHeightInt p (I : ℤ))
    (gaussPrimeSampleShift p J) hh ht
  rw [gaussSampleRatioDefect, gaussSampleValue_of_pos k p hIJZ,
    gaussSampleValue_of_pos k p hIZ, gaussPrimeSampleHeightInt_add_nat]
  have hclock := gaussPrimeSampleShift_mul_clock_int hm p hI J
  have hphase :
      2 * (Real.pi : ℂ) * Complex.I * ((J : ℤ) : ℂ) *
          ((gaussSamplePhase m p (I : ℤ) : ℝ) : ℂ) =
        ((gaussPrimeSampleShift p J : ℝ) : ℂ) *
          gaussComponentVerticalClock m (gaussPrimeSampleHeightInt p (I : ℤ)) := by
    calc
      2 * (Real.pi : ℂ) * Complex.I * ((J : ℤ) : ℂ) *
          ((gaussSamplePhase m p (I : ℤ) : ℝ) : ℂ)
        = 2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) *
          ((gaussSamplePhase m p (I : ℤ) : ℝ) : ℂ) := by
            push_cast
            rfl
      _ = ((gaussPrimeSampleShift p J : ℝ) : ℂ) *
          gaussComponentVerticalClock m (gaussPrimeSampleHeightInt p (I : ℤ)) := hclock.symm
  rw [hphase]
  exact hmain

/-- Quantitative backward lattice-ratio law, based at `I+J` and shifted back to
`I`; its envelope is governed by the lower endpoint `I`. -/
theorem exists_gaussSampleRatioDefect_backward_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ I J : ℕ, 0 < I →
      2 * (m : ℝ) ≤ gaussPrimeSampleHeightInt p (I : ℤ) →
      let h := gaussPrimeSampleShift p J
      let t := gaussPrimeSampleHeightInt p ((I + J : ℕ) : ℤ)
      let B := (C * h + 2 * h * h) / (t - h)
      ‖gaussSampleRatioDefect k p (-(J : ℤ)) ((I + J : ℕ) : ℤ)‖ ≤
        B * Real.exp B := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_gaussComponentVerticalValue_sub_ratio_sub_clock_inv_bound hm k
  refine ⟨C, hC, ?_⟩
  intro I J hI ht
  dsimp only
  have hIZ : (0 : ℤ) < (I : ℤ) := by exact_mod_cast hI
  have hIJZ : (0 : ℤ) < ((I + J : ℕ) : ℤ) := by exact_mod_cast (Nat.add_pos_left hI J)
  have hsum : ((I + J : ℕ) : ℤ) + -(J : ℤ) = (I : ℤ) := by push_cast; ring
  have hh := gaussPrimeSampleShift_nonneg p J
  have hheight : gaussPrimeSampleHeightInt p ((I + J : ℕ) : ℤ) -
      gaussPrimeSampleShift p J = gaussPrimeSampleHeightInt p (I : ℤ) := by
    convert gaussPrimeSampleHeightInt_add_nat_sub_shift p I J using 1
    all_goals push_cast
    all_goals rfl
  have hmain := hbound (gaussPrimeSampleHeightInt p ((I + J : ℕ) : ℤ))
    (gaussPrimeSampleShift p J) hh (by
      rw [hheight]
      exact ht)
  rw [gaussSampleRatioDefect, hsum, gaussSampleValue_of_pos k p hIZ,
    gaussSampleValue_of_pos k p hIJZ]
  have hclock := gaussPrimeSampleShift_mul_clock_int hm p (Nat.add_pos_left hI J) J
  have hphase :
      2 * (Real.pi : ℂ) * Complex.I * (-(J : ℂ)) *
          ((gaussSamplePhase m p ((I + J : ℕ) : ℤ) : ℝ) : ℂ) =
        -((gaussPrimeSampleShift p J : ℝ) : ℂ) *
          gaussComponentVerticalClock m
            (gaussPrimeSampleHeightInt p ((I + J : ℕ) : ℤ)) := by
    calc
      2 * (Real.pi : ℂ) * Complex.I * (-(J : ℂ)) *
          ((gaussSamplePhase m p ((I + J : ℕ) : ℤ) : ℝ) : ℂ)
        = -(2 * (Real.pi : ℂ) * Complex.I * (J : ℂ) *
            ((gaussSamplePhase m p ((I + J : ℕ) : ℤ) : ℝ) : ℂ)) := by
              push_cast
              ring
      _ = -(((gaussPrimeSampleShift p J : ℝ) : ℂ) *
          gaussComponentVerticalClock m
            (gaussPrimeSampleHeightInt p ((I + J : ℕ) : ℤ))) := by rw [hclock]
      _ = -((gaussPrimeSampleShift p J : ℝ) : ℂ) *
          gaussComponentVerticalClock m
            (gaussPrimeSampleHeightInt p ((I + J : ℕ) : ℤ)) := by ring
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [hphase]
  rw [hheight] at hmain
  rw [hheight]
  exact hmain

private theorem nat_le_sq_of_pos {J : ℕ} (hJ : 0 < J) : J ≤ J ^ 2 := by
  nlinarith

/-- In the parabolic central band `J² ≤ I`, the forward defect is genuinely
algebraic: the exponential envelope is uniformly bounded and only
`(J+J²)/I` remains. -/
theorem exists_gaussSampleRatioDefect_forward_central_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ∃ D : ℝ, 0 < D ∧ ∀ I J : ℕ, 0 < I →
      2 * (m : ℝ) ≤ gaussPrimeSampleHeightInt p (I : ℤ) → J ^ 2 ≤ I →
      ‖gaussSampleRatioDefect k p (J : ℤ) (I : ℤ)‖ ≤
        D * ((J : ℝ) + (J : ℝ) ^ 2) / (I : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_gaussSampleRatioDefect_forward_bound hm k p
  set q : ℝ := gaussPrimeSampleSpacing p with hq
  have hqpos : 0 < q := by rw [hq]; exact gaussPrimeSampleSpacing_pos p
  set A : ℝ := C + q + 1 with hA
  have hApos : 0 < A := by dsimp [A]; linarith
  set D : ℝ := A * Real.exp (2 * A) with hD
  refine ⟨D, mul_pos hApos (Real.exp_pos _), ?_⟩
  intro I J hI ht hJI
  have hIR : 0 < (I : ℝ) := by exact_mod_cast hI
  have hJR : 0 ≤ (J : ℝ) := by positivity
  have hJ2R : (J : ℝ) ^ 2 ≤ (I : ℝ) := by exact_mod_cast hJI
  have hJleI : J ≤ I := by
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · exact Nat.zero_le _
    · exact le_trans (nat_le_sq_of_pos hJ) hJI
  have hJleIR : (J : ℝ) ≤ (I : ℝ) := by exact_mod_cast hJleI
  set X : ℝ := ((J : ℝ) + (J : ℝ) ^ 2) / (I : ℝ) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hX2 : X ≤ 2 := by
    rw [hX, div_le_iff₀ hIR]
    nlinarith
  set B : ℝ := (C * (J : ℝ) + q * (J : ℝ) ^ 2) / (I : ℝ) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBX : B ≤ A * X := by
    rw [hB, hX, ← mul_div_assoc, div_le_div_iff₀ hIR hIR]
    dsimp [A]
    nlinarith [mul_nonneg hC hJR, mul_nonneg hqpos.le (sq_nonneg (J : ℝ)),
      mul_nonneg hC (sq_nonneg (J : ℝ)), mul_nonneg hqpos.le hJR]
  have hB2A : B ≤ 2 * A := le_trans hBX (by nlinarith [mul_le_mul_of_nonneg_left hX2 hApos.le])
  have hbase := hbound I J hI ht
  dsimp only at hbase
  rw [gaussPrimeSampleShift_eq_spacing_mul,
    gaussPrimeSampleHeightInt_nat_eq_spacing_mul] at hbase
  have henv :
      (C * (q * (J : ℝ)) + q * (J : ℝ) * (q * (J : ℝ))) /
          (q * (I : ℝ)) = B := by
    rw [hB]
    field_simp
  rw [show gaussPrimeSampleSpacing p = q from hq.symm, henv] at hbase
  calc
    ‖gaussSampleRatioDefect k p (J : ℤ) (I : ℤ)‖
      ≤ B * Real.exp B := hbase
    _ ≤ (A * X) * Real.exp (2 * A) :=
      mul_le_mul hBX (Real.exp_le_exp.mpr hB2A) (Real.exp_pos _).le
        (mul_nonneg hApos.le hX0)
    _ = D * ((J : ℝ) + (J : ℝ) ^ 2) / (I : ℝ) := by
      rw [hD, hX]
      ring

/-- Backward central-band defect has the same algebraic order. -/
theorem exists_gaussSampleRatioDefect_backward_central_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ∃ D : ℝ, 0 < D ∧ ∀ I J : ℕ, 0 < I →
      2 * (m : ℝ) ≤ gaussPrimeSampleHeightInt p (I : ℤ) → J ^ 2 ≤ I →
      ‖gaussSampleRatioDefect k p (-(J : ℤ)) ((I + J : ℕ) : ℤ)‖ ≤
        D * ((J : ℝ) + (J : ℝ) ^ 2) / (I : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_gaussSampleRatioDefect_backward_bound hm k p
  set q : ℝ := gaussPrimeSampleSpacing p with hq
  have hqpos : 0 < q := by rw [hq]; exact gaussPrimeSampleSpacing_pos p
  set A : ℝ := C + 2 * q + 1 with hA
  have hApos : 0 < A := by dsimp [A]; linarith
  set D : ℝ := A * Real.exp (2 * A) with hD
  refine ⟨D, mul_pos hApos (Real.exp_pos _), ?_⟩
  intro I J hI ht hJI
  have hIR : 0 < (I : ℝ) := by exact_mod_cast hI
  have hJR : 0 ≤ (J : ℝ) := by positivity
  have hJ2R : (J : ℝ) ^ 2 ≤ (I : ℝ) := by exact_mod_cast hJI
  have hJleI : J ≤ I := by
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · exact Nat.zero_le _
    · exact le_trans (nat_le_sq_of_pos hJ) hJI
  have hJleIR : (J : ℝ) ≤ (I : ℝ) := by exact_mod_cast hJleI
  set X : ℝ := ((J : ℝ) + (J : ℝ) ^ 2) / (I : ℝ) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hX2 : X ≤ 2 := by
    rw [hX, div_le_iff₀ hIR]
    nlinarith
  set B : ℝ := (C * (J : ℝ) + 2 * q * (J : ℝ) ^ 2) / (I : ℝ) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBX : B ≤ A * X := by
    rw [hB, hX, ← mul_div_assoc, div_le_div_iff₀ hIR hIR]
    dsimp [A]
    nlinarith [mul_nonneg hC hJR, mul_nonneg hqpos.le (sq_nonneg (J : ℝ)),
      mul_nonneg hC (sq_nonneg (J : ℝ)), mul_nonneg hqpos.le hJR]
  have hB2A : B ≤ 2 * A := le_trans hBX (by nlinarith [mul_le_mul_of_nonneg_left hX2 hApos.le])
  have hbase := hbound I J hI ht
  dsimp only at hbase
  rw [gaussPrimeSampleShift_eq_spacing_mul] at hbase
  have hheight : gaussPrimeSampleHeightInt p ((I + J : ℕ) : ℤ) -
      q * (J : ℝ) = q * (I : ℝ) := by
    rw [hq, gaussPrimeSampleSpacing, gaussPrimeSampleHeightInt]
    push_cast
    ring
  rw [hheight] at hbase
  have henv :
      (C * (q * (J : ℝ)) + 2 * (q * (J : ℝ)) * (q * (J : ℝ))) /
          (q * (I : ℝ)) = B := by
    rw [hB]
    field_simp
  rw [show gaussPrimeSampleSpacing p = q from hq.symm, henv] at hbase
  calc
    ‖gaussSampleRatioDefect k p (-(J : ℤ)) ((I + J : ℕ) : ℤ)‖
      ≤ B * Real.exp B := hbase
    _ ≤ (A * X) * Real.exp (2 * A) :=
      mul_le_mul hBX (Real.exp_le_exp.mpr hB2A) (Real.exp_pos _).le
        (mul_nonneg hApos.le hX0)
    _ = D * ((J : ℝ) + (J : ℝ) ^ 2) / (I : ℝ) := by
      rw [hD, hX]
      ring

/-- Uniform signed central-band law.  The negative-shift estimate is rebased at
`I - |j|`; the factor `2` in the parabolic band keeps that lower endpoint at
least `I / 2`.  This is the form needed by two-sided Fourier sums. -/
theorem exists_gaussSampleRatioDefect_signed_central_bound
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ∃ D : ℝ, 0 < D ∧ ∀ I : ℕ, ∀ j : ℤ, 0 < I →
      2 * (m : ℝ) ≤ gaussPrimeSampleHeightInt p ((I / 2 : ℕ) : ℤ) →
      2 * j.natAbs ^ 2 ≤ I →
      ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ≤
        D * ((j.natAbs : ℝ) + (j.natAbs : ℝ) ^ 2) / (I : ℝ) := by
  obtain ⟨Df, hDf, hforward⟩ :=
    exists_gaussSampleRatioDefect_forward_central_bound hm k p
  obtain ⟨Db, hDb, hbackward⟩ :=
    exists_gaussSampleRatioDefect_backward_central_bound hm k p
  refine ⟨Df + 2 * Db, by positivity, ?_⟩
  intro I j hI hheight hcentral
  set a : ℕ := j.natAbs with ha
  have hIR : 0 < (I : ℝ) := by exact_mod_cast hI
  have hheight_mono : ∀ {u v : ℕ}, u ≤ v →
      gaussPrimeSampleHeightInt p (u : ℤ) ≤ gaussPrimeSampleHeightInt p (v : ℤ) := by
    intro u v huv
    rw [gaussPrimeSampleHeightInt_nat_eq_spacing_mul,
      gaussPrimeSampleHeightInt_nat_eq_spacing_mul]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast huv)
      (gaussPrimeSampleSpacing_pos p).le
  by_cases hj : 0 ≤ j
  · have hjrepr : (a : ℤ) = j := by
      rw [ha]
      exact Int.natAbs_of_nonneg hj
    have ha2I : a ^ 2 ≤ I := by omega
    have hheightI : 2 * (m : ℝ) ≤ gaussPrimeSampleHeightInt p (I : ℤ) :=
      hheight.trans (hheight_mono (Nat.div_le_self I 2))
    have hbase := hforward I a hI hheightI ha2I
    rw [hjrepr] at hbase
    calc
      ‖gaussSampleRatioDefect k p j (I : ℤ)‖
          ≤ Df * ((a : ℝ) + (a : ℝ) ^ 2) / (I : ℝ) := hbase
      _ ≤ (Df + 2 * Db) * ((a : ℝ) + (a : ℝ) ^ 2) / (I : ℝ) := by
        gcongr
        linarith
  · have hjneg : j < 0 := lt_of_not_ge hj
    have ha0 : 0 < a := by
      rw [ha]
      omega
    have harepr : -(a : ℤ) = j := by
      have h := Int.ofNat_natAbs_of_nonpos hjneg.le
      rw [← ha] at h
      omega
    have ha_le_sq : a ≤ a ^ 2 := by nlinarith
    have haI : a ≤ I := by omega
    set L : ℕ := I - a with hL
    have hLI : L + a = I := by
      rw [hL, Nat.sub_add_cancel haI]
    have ha2L : a ^ 2 ≤ L := by omega
    have hLpos : 0 < L := by omega
    have hhalfL : I / 2 ≤ L := by omega
    have hheightL : 2 * (m : ℝ) ≤ gaussPrimeSampleHeightInt p (L : ℤ) :=
      hheight.trans (hheight_mono hhalfL)
    have hbase := hbackward L a hLpos hheightL ha2L
    rw [hLI, harepr] at hbase
    have hIL : I ≤ 2 * L := by omega
    have hLR : 0 < (L : ℝ) := by exact_mod_cast hLpos
    have hscale :
        Db * ((a : ℝ) + (a : ℝ) ^ 2) / (L : ℝ) ≤
          (2 * Db) * ((a : ℝ) + (a : ℝ) ^ 2) / (I : ℝ) := by
      rw [div_le_div_iff₀ hLR hIR]
      have hILR : (I : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hIL
      nlinarith [mul_nonneg hDb.le
        (add_nonneg (Nat.cast_nonneg a) (sq_nonneg (a : ℝ)))]
    calc
      ‖gaussSampleRatioDefect k p j (I : ℤ)‖
          ≤ Db * ((a : ℝ) + (a : ℝ) ^ 2) / (L : ℝ) := hbase
      _ ≤ (2 * Db) * ((a : ℝ) + (a : ℝ) ^ 2) / (I : ℝ) := hscale
      _ ≤ (Df + 2 * Db) * ((a : ℝ) + (a : ℝ) ^ 2) / (I : ℝ) := by
        gcongr
        linarith

end

end RHTower
