import GaloisForLFunctions.RHTower.GaussTwoPieceInvariance
import GaloisForLFunctions.RHTower.GaussPairingDefect
import GaloisForLFunctions.RHTower.GaussSpikeDefectBand
import GaloisForLFunctions.RHTower.GaussSandwich
import GaloisForLFunctions.RHTower.GaussPrincipalStepBlock
import GaloisForLFunctions.HTGeometry.IntegerPowerSeriesBounds

/-!
# One step of the two-piece class through the principal step

The class the `m`-fold iteration must carry is
`|ĝ(j)| ≤ A/(1+|j|)^θ + (B/(1+I)^θ)·spike(c)`: the spike-height exponent is *tied* to the bulk
exponent.  With that tie the four hypotheses of the pairing estimate collapse to the single
inequality `c_P + c_Q + 1 < θ_P + θ_Q`, and the invariant is maintained by two steps:

* a **symbol step** (multiplication by `B` or `B^(-2)`), which drops `θ` by a fixed `ε` and keeps
  both constants bounded — the logarithm each convolution costs is absorbed by the drop;
* a **multiplier step** (application of `S` or `S*`), which keeps `θ` and raises `c` by `1/(2m)`.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions
open scoped ENNReal NNReal

noncomputable section

/-! ## Monotonicity of the class -/

theorem TwoPieceAmplitude.mono_const {A A' θ B B' c : ℝ} {n : ℕ} {g : ℤ → ℂ}
    (hA : A ≤ A') (hB : B ≤ B') (h : TwoPieceAmplitude A θ B c n g) :
    TwoPieceAmplitude A' θ B' c n g := by
  intro j
  refine le_trans (h j) (add_le_add ?_ ?_)
  · exact div_le_div_of_nonneg_right hA (by positivity)
  · rw [spikeProfile, spikeProfile]
    split_ifs with hband
    · refine mul_le_mul_of_nonneg_right hB ?_
      exact Real.rpow_nonneg (by positivity) c
    · exact le_rfl

/-! ## The convolution constants are beaten by any positive power -/

theorem exists_spikeConvConst_le_rpow {c ε : ℝ} (hc1 : c < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : ℕ,
      spikeConvConst c (bandRadius I) ≤ C * (1 + (I : ℝ)) ^ ε := by
  obtain ⟨C₀, hC₀, hbound⟩ := GaloisForLFunctions.log_div_le_rpow_div
    (θ := 1 - ε) (by linarith) (by linarith)
  have hfac : (0 : ℝ) < 12 + 2 / (1 - c) := by
    have : (0 : ℝ) < 1 - c := by linarith
    positivity
  refine ⟨(12 + 2 / (1 - c)) * (1 + Real.log 2 + C₀), by positivity, fun I => ?_⟩
  have hIn : (bandRadius I : ℝ) ≤ (I : ℝ) := by
    have : bandRadius I ≤ I := by rw [bandRadius]; omega
    exact_mod_cast this
  have hpos : (0 : ℝ) < 2 * (bandRadius I : ℝ) + 2 := by positivity
  have hle : 2 * (bandRadius I : ℝ) + 2 ≤ 2 * (2 + (I : ℝ)) := by linarith
  have hlogmono : Real.log (2 * (bandRadius I : ℝ) + 2) ≤ Real.log (2 * (2 + (I : ℝ))) :=
    Real.log_le_log hpos hle
  have hsplit : Real.log (2 * (2 + (I : ℝ))) = Real.log 2 + Real.log (2 + (I : ℝ)) :=
    Real.log_mul (by norm_num) (by positivity)
  have hkey := hbound (I : ℝ) (Nat.cast_nonneg I)
  have hIpos : (0 : ℝ) < 1 + (I : ℝ) := by positivity
  have hrpow : (0 : ℝ) < (1 + (I : ℝ)) ^ (1 - ε) := Real.rpow_pos_of_pos hIpos _
  have hlogI : Real.log (2 + (I : ℝ)) ≤ C₀ * (1 + (I : ℝ)) ^ ε := by
    rw [div_le_div_iff₀ hIpos hrpow] at hkey
    have hid : (1 + (I : ℝ)) ^ (1 - ε) * (1 + (I : ℝ)) ^ ε = (1 + (I : ℝ)) := by
      rw [← Real.rpow_add hIpos]
      norm_num
    nlinarith [hkey, hid, Real.rpow_pos_of_pos hIpos ε]
  have hIge : (1 : ℝ) ≤ 1 + (I : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) I]
  have hone : (1 : ℝ) ≤ (1 + (I : ℝ)) ^ ε := Real.one_le_rpow hIge hε0.le
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hstep : 1 + (Real.log 2 + C₀ * (1 + (I : ℝ)) ^ ε)
      ≤ (1 + Real.log 2 + C₀) * (1 + (I : ℝ)) ^ ε := by nlinarith [hone, hlog2, hC₀.le]
  rw [spikeConvConst]
  calc (12 + 2 / (1 - c)) * (1 + Real.log (2 * (bandRadius I : ℝ) + 2))
      ≤ (12 + 2 / (1 - c)) * (1 + (Real.log 2 + C₀ * (1 + (I : ℝ)) ^ ε)) := by
        refine mul_le_mul_of_nonneg_left ?_ hfac.le
        linarith [hlogmono, hsplit, hlogI]
    _ ≤ (12 + 2 / (1 - c)) * (1 + Real.log 2 + C₀) * (1 + (I : ℝ)) ^ ε := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hstep hfac.le

theorem exists_spikeConvBulkConst_le_rpow {c ε : ℝ} (hc1 : c < 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : ℕ,
      spikeConvBulkConst c (bandRadius I) ≤ C * (1 + (I : ℝ)) ^ ε := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_spikeConvConst_le_rpow hc1 hε0 hε1
  have hpos : (0 : ℝ) < 6 + 4 / (1 - c) := by
    have : (0 : ℝ) < 1 - c := by linarith
    positivity
  refine ⟨30 * C₀ + (6 + 4 / (1 - c)), by positivity, fun I => ?_⟩
  have hIge : (1 : ℝ) ≤ 1 + (I : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) I]
  have hone : (1 : ℝ) ≤ (1 + (I : ℝ)) ^ ε := Real.one_le_rpow hIge hε0.le
  rw [spikeConvBulkConst]
  nlinarith [hbound I, hone, hpos.le]

/-! ## The symbol step -/

set_option maxHeartbeats 1000000 in
/-- **Multiplication by a bounded real symbol with harmonic coefficients keeps the class**, at the
cost of a fixed drop `ε` in the exponent; the logarithm the convolution costs is absorbed by the
drop, so both constants stay independent of the frequency. -/
theorem exists_gaussClass_symbol_step {θ c ε : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hθ1 : θ ≤ 1) (hε0 : 0 < ε) (hεθ : ε < θ)
    {sym : AddCircle (1 : ℝ) → ℂ} (hsym : Measurable sym) {Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hCb : ∀ x, ‖sym x‖ ≤ Cb) (hreal : ∀ x, starRingEnd ℂ (sym x) = sym x)
    {K : ℝ} (hK : ∀ x : ℤ, ‖fourierCoeff sym x‖ ≤ K / (1 + (x.natAbs : ℝ)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ A' B' : ℝ, 0 ≤ A' ∧ 0 ≤ B' ∧ ∀ (I : ℕ), 1 ≤ I →
      ∀ u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))),
      TwoPieceAmplitude A θ (B / (1 + (I : ℝ)) ^ θ) c I
          (fun j => fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j) →
      TwoPieceAmplitude A' (θ - ε) (B' / (1 + (I : ℝ)) ^ (θ - ε)) c I
        (fun j => fourierCoeff ((MeasureTheory.lpBoundedMulCLM hsym hCb0 hCb u :
          AddCircle (1 : ℝ) → ℂ)) j) := by
  have hε1 : ε < 1 := by linarith
  have hK0 : 0 ≤ K := by
    have h0 := hK 0
    simp only [Int.natAbs_zero, Nat.cast_zero, add_zero, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  obtain ⟨C₁, hC₁, hC₁b⟩ := exists_spikeConvBulkConst_le_rpow (c := c) hc1
    (by linarith : (0 : ℝ) < ε / 2) (by linarith : ε / 2 < 1)
  obtain ⟨C₂, hC₂, hC₂b⟩ := exists_spikeConvConst_le_rpow (c := c) hc1
    (by linarith : (0 : ℝ) < ε / 2) (by linarith : ε / 2 < 1)
  set W : ℝ := (∑' x : ℤ, GaloisForLFunctions.intPowWeight (θ + 1 - (θ - ε)) x).toReal with hW
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  refine ⟨K * A * (2 * (2 * W)) + C₁ * K * B, 3 * K * C₂ * B, by positivity, by positivity,
    fun I hI u hu => ?_⟩
  have hIge : (1 : ℝ) ≤ 1 + (I : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) I]
  have hIpos : (0 : ℝ) < 1 + (I : ℝ) := by linarith
  have hBI : (0 : ℝ) ≤ B / (1 + (I : ℝ)) ^ θ := by positivity
  have hstep := TwoPieceAmplitude.mul_symbol hc0 hc1 hθ1 (by linarith : (0 : ℝ) < θ - ε)
    (by linarith : θ - ε < θ) hA hBI hI hsym hCb0 hCb hreal hK u hu
  refine TwoPieceAmplitude.mono_const ?_ ?_ hstep
  · -- the bulk constant
    have h2γ : (2 : ℝ) ^ (θ - ε) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : θ - ε ≤ 1)
      simpa using h
    have hfirst : K * A * (2 ^ (θ - ε) * (2 * W)) ≤ K * A * (2 * (2 * W)) := by
      have hKA : (0 : ℝ) ≤ K * A := by positivity
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h2γ (by linarith : (0 : ℝ) ≤ 2 * W)) hKA
    have hIγ : (I : ℝ) ^ (θ - ε) ≤ (1 + (I : ℝ)) ^ (θ - ε) :=
      Real.rpow_le_rpow (Nat.cast_nonneg I) (by linarith) (by linarith)
    have hnnb : (0 : ℝ) ≤ B / (1 + (I : ℝ)) ^ θ := by positivity
    have hSB0 : (0 : ℝ) ≤ spikeConvBulkConst c (bandRadius I) := by
      have hone := one_le_spikeConvConst hc1 (bandRadius I)
      have hcc : (0 : ℝ) < 1 - c := by linarith
      rw [spikeConvBulkConst]
      have : (0 : ℝ) < 4 / (1 - c) := by positivity
      linarith
    have hA1 : spikeConvBulkConst c (bandRadius I) * K * (B / (1 + (I : ℝ)) ^ θ) *
          (I : ℝ) ^ (θ - ε)
        ≤ (C₁ * (1 + (I : ℝ)) ^ (ε / 2)) * K * (B / (1 + (I : ℝ)) ^ θ) *
          (1 + (I : ℝ)) ^ (θ - ε) := by
      refine mul_le_mul ?_ hIγ (Real.rpow_nonneg (Nat.cast_nonneg I) _) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC₁b I) hK0) hnnb
    have hθne : ((1 + (I : ℝ)) ^ θ) ≠ 0 := (Real.rpow_pos_of_pos hIpos θ).ne'
    have hfac : (C₁ * (1 + (I : ℝ)) ^ (ε / 2)) * K * (B / (1 + (I : ℝ)) ^ θ) *
          (1 + (I : ℝ)) ^ (θ - ε)
        = C₁ * K * B * ((1 + (I : ℝ)) ^ (ε / 2) * (1 + (I : ℝ)) ^ (θ - ε) /
            (1 + (I : ℝ)) ^ θ) := by
      field_simp
    have hpow : (1 + (I : ℝ)) ^ (ε / 2) * (1 + (I : ℝ)) ^ (θ - ε) / (1 + (I : ℝ)) ^ θ
        = (1 + (I : ℝ)) ^ (-(ε / 2)) := by
      rw [← Real.rpow_add hIpos, ← Real.rpow_sub hIpos]
      congr 1
      ring
    have hid : (C₁ * (1 + (I : ℝ)) ^ (ε / 2)) * K * (B / (1 + (I : ℝ)) ^ θ) *
          (1 + (I : ℝ)) ^ (θ - ε)
        = C₁ * K * B * (1 + (I : ℝ)) ^ (-(ε / 2)) := by
      rw [hfac, hpow]
    rw [hid] at hA1
    have hle1 : (1 + (I : ℝ)) ^ (-(ε / 2)) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le hIge (by linarith : -(ε / 2) ≤ 0)
      simpa using h
    have hsecond : spikeConvBulkConst c (bandRadius I) * K * (B / (1 + (I : ℝ)) ^ θ) *
        (I : ℝ) ^ (θ - ε) ≤ C₁ * K * B := by
      refine le_trans hA1 ?_
      nlinarith [hle1, mul_nonneg (mul_nonneg hC₁.le hK0) hB]
    linarith
  · -- the spike constant
    have hIpos' : (0 : ℝ) < 1 + (I : ℝ) := hIpos
    have hnnb : (0 : ℝ) ≤ B / (1 + (I : ℝ)) ^ θ := by positivity
    have hmono : (1 + (I : ℝ)) ^ (ε / 2) ≤ (1 + (I : ℝ)) ^ ε :=
      Real.rpow_le_rpow_of_exponent_le hIge (by linarith)
    have hsc : spikeConvConst c (bandRadius I) ≤ C₂ * (1 + (I : ℝ)) ^ ε :=
      le_trans (hC₂b I) (mul_le_mul_of_nonneg_left hmono hC₂.le)
    have hstep1 : 3 * K * spikeConvConst c (bandRadius I) * (B / (1 + (I : ℝ)) ^ θ)
        ≤ 3 * K * (C₂ * (1 + (I : ℝ)) ^ ε) * (B / (1 + (I : ℝ)) ^ θ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsc (by positivity : (0 : ℝ) ≤ 3 * K)) hnnb
    have hθne : ((1 + (I : ℝ)) ^ θ) ≠ 0 := (Real.rpow_pos_of_pos hIpos θ).ne'
    have hεne : ((1 + (I : ℝ)) ^ ε) ≠ 0 := (Real.rpow_pos_of_pos hIpos ε).ne'
    have hid2 : 3 * K * (C₂ * (1 + (I : ℝ)) ^ ε) * (B / (1 + (I : ℝ)) ^ θ)
        = 3 * K * C₂ * B / (1 + (I : ℝ)) ^ (θ - ε) := by
      rw [Real.rpow_sub hIpos]
      field_simp
    rw [hid2] at hstep1
    exact hstep1

/-! ## The multiplier step -/

/-- **A Fourier multiplier with the two-regime bound keeps the tied class**, raising the spike
exponent and leaving the bulk exponent alone. -/
theorem gaussClass_multiplier_step {A θ B c c' K₁ K₂ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hc0 : 0 < c)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) {I : ℕ} (hI : 2 ≤ I) {g : ℤ → ℂ}
    (hg : TwoPieceAmplitude A θ (B / (1 + (I : ℝ)) ^ θ) c I g) (ρ : ℤ → ℂ)
    (hρbulk : ∀ j : ℤ, ¬ (2 * ((((I : ℤ) + j).natAbs : ℝ)) < (I : ℝ)) → ‖ρ j‖ ≤ K₁)
    (hρband : ∀ j : ℤ, 2 * ((((I : ℤ) + j).natAbs : ℝ)) < (I : ℝ) →
      ‖ρ j‖ ≤ K₂ * ((I : ℝ) / (1 + (((I : ℤ) + j).natAbs : ℝ))) ^ c') :
    TwoPieceAmplitude (K₁ * A) θ ((K₂ * (2 * A + B)) / (1 + (I : ℝ)) ^ θ) (c + c') I
      (fun j => ρ j * g j) := by
  have hIpos : (0 : ℝ) < 1 + (I : ℝ) := by positivity
  have hIge : (1 : ℝ) ≤ 1 + (I : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) I]
  have hstep := TwoPieceAmplitude.mul_multiplier hA hθ0 hc0 hK₁ hK₂ hI hg ρ hρbulk hρband
  refine TwoPieceAmplitude.mono_const le_rfl ?_ hstep
  have hhalf : A / (1 + (I : ℝ) / 2) ^ θ ≤ 2 * A / (1 + (I : ℝ)) ^ θ := by
    have h := inv_one_add_half_rpow_le hθ0 I
    have h2 : (2 : ℝ) ^ θ ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hθ1
      simpa using this
    have hp2 : (0 : ℝ) < (1 + (I : ℝ)) ^ θ := Real.rpow_pos_of_pos hIpos θ
    have hchain : (1 : ℝ) / (1 + (I : ℝ) / 2) ^ θ ≤ 2 / (1 + (I : ℝ)) ^ θ := by
      refine le_trans h ?_
      exact div_le_div_of_nonneg_right h2 hp2.le
    calc A / (1 + (I : ℝ) / 2) ^ θ = A * (1 / (1 + (I : ℝ) / 2) ^ θ) := by ring
      _ ≤ A * (2 / (1 + (I : ℝ)) ^ θ) := mul_le_mul_of_nonneg_left hchain hA
      _ = 2 * A / (1 + (I : ℝ)) ^ θ := by ring
  have hsum : A / (1 + (I : ℝ) / 2) ^ θ + B / (1 + (I : ℝ)) ^ θ
      ≤ (2 * A + B) / (1 + (I : ℝ)) ^ θ := by
    have : 2 * A / (1 + (I : ℝ)) ^ θ + B / (1 + (I : ℝ)) ^ θ
        = (2 * A + B) / (1 + (I : ℝ)) ^ θ := by ring
    linarith
  calc K₂ * (A / (1 + (I : ℝ) / 2) ^ θ + B / (1 + (I : ℝ)) ^ θ)
      ≤ K₂ * ((2 * A + B) / (1 + (I : ℝ)) ^ θ) := mul_le_mul_of_nonneg_left hsum hK₂
    _ = K₂ * (2 * A + B) / (1 + (I : ℝ)) ^ θ := by ring

/-! ## The two regimes of the shifted symbol -/

variable {m : ℕ}

/-- Off the band the sampled ratio is bounded by a constant. -/
theorem gaussShiftRatio_le_of_not_spike (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ}
    (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (l : ℤ) (hspike : ¬ (2 * ((((I : ℤ) + l).natAbs : ℝ)) < (I : ℝ))) :
    gaussShiftRatio k p (I : ℤ) l ≤ Real.sqrt (1 + 2 * K) := by
  have hN : I ≤ 2 * ((I : ℤ) + l).natAbs := by
    have hR : (I : ℝ) ≤ 2 * ((((I : ℤ) + l).natAbs : ℕ) : ℝ) := not_lt.mp hspike
    exact_mod_cast hR
  have hsq := gaussShiftRatio_sq_le_of_not_spike hm k p hK hKb I l hN
  have h0 : 0 ≤ gaussShiftRatio k p (I : ℤ) l := gaussShiftRatio_nonneg k p (I : ℤ) l
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq h0] at this

/-- On the band the sampled ratio is bounded by the spike profile at exponent `1/(2m)`. -/
theorem gaussShiftRatio_le_of_spike (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ}
    (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    (I : ℕ) (l : ℤ) :
    gaussShiftRatio k p (I : ℤ) l
      ≤ (2 * K) ^ ((1 : ℝ) / (2 * m)) *
        ((I : ℝ) / (1 + (((I : ℤ) + l).natAbs : ℝ))) ^ ((1 : ℝ) / (2 * m)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp : (0 : ℝ) < (1 : ℝ) / (2 * m) := by positivity
  set R : ℝ := gaussShiftRatio k p (I : ℤ) l with hR
  have hR0 : 0 ≤ R := gaussShiftRatio_nonneg k p (I : ℤ) l
  have hbase : R ^ (2 * m) ≤ K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ) :=
    norm_gaussSampleRatio_pow_le hm k p hKb I l
  have hid : (R ^ (2 * m)) ^ ((1 : ℝ) / (2 * m)) = R := by
    rw [← Real.rpow_natCast R (2 * m), ← Real.rpow_mul hR0]
    push_cast
    rw [show (2 : ℝ) * (m : ℝ) * ((1 : ℝ) / (2 * (m : ℝ))) = 1 from by field_simp]
    exact Real.rpow_one R
  have hquot : K * (I : ℝ) / (((I : ℤ) + l).natAbs : ℝ)
      ≤ 2 * K * ((I : ℝ) / (1 + (((I : ℤ) + l).natAbs : ℝ))) := by
    rcases Nat.eq_zero_or_pos ((I : ℤ) + l).natAbs with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, div_zero]
      positivity
    · have h1 : (1 : ℝ) ≤ ((((I : ℤ) + l).natAbs : ℕ) : ℝ) := by exact_mod_cast hpos
      have hden : (0 : ℝ) < ((((I : ℤ) + l).natAbs : ℕ) : ℝ) := by linarith
      have hden2 : (0 : ℝ) < 1 + ((((I : ℤ) + l).natAbs : ℕ) : ℝ) := by linarith
      rw [div_le_iff₀ hden]
      have hInn : (0 : ℝ) ≤ (I : ℝ) := Nat.cast_nonneg I
      have hK2 : (0 : ℝ) ≤ 2 * K := by positivity
      have hstep : 1 + ((((I : ℤ) + l).natAbs : ℕ) : ℝ)
          ≤ 2 * ((((I : ℤ) + l).natAbs : ℕ) : ℝ) := by linarith
      have hfrac : (I : ℝ) / (1 + ((((I : ℤ) + l).natAbs : ℕ) : ℝ)) *
          (2 * ((((I : ℤ) + l).natAbs : ℕ) : ℝ)) ≥ (I : ℝ) := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hden2]
        nlinarith [hInn, hstep]
      nlinarith [hfrac, hK.le, hInn]
  calc R = (R ^ (2 * m)) ^ ((1 : ℝ) / (2 * m)) := hid.symm
    _ ≤ (2 * K * ((I : ℝ) / (1 + (((I : ℤ) + l).natAbs : ℝ)))) ^ ((1 : ℝ) / (2 * m)) :=
        Real.rpow_le_rpow (pow_nonneg hR0 _) (le_trans hbase hquot) hexp.le
    _ = (2 * K) ^ ((1 : ℝ) / (2 * m)) *
        ((I : ℝ) / (1 + (((I : ℤ) + l).natAbs : ℝ))) ^ ((1 : ℝ) / (2 * m)) :=
        Real.mul_rpow (by positivity) (by positivity)

/-! ## The two normalized shifted blocks preserve the class -/

/-- The common multiplier bookkeeping for the two normalized shifted blocks. -/
theorem gaussClass_shifted_step (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {A θ B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hc0 : 0 < c)
    {I : ℕ} (hI : 2 ≤ I) {g h : ℤ → ℂ}
    (hg : TwoPieceAmplitude A θ (B / (1 + (I : ℝ)) ^ θ) c I g)
    (hnorm : ∀ j : ℤ, ‖h j‖ = gaussShiftRatio k p (I : ℤ) j * ‖g j‖) :
    TwoPieceAmplitude (Real.sqrt (1 + 2 * K) * A) θ
      (((2 * K) ^ ((1 : ℝ) / (2 * m)) * (2 * A + B)) / (1 + (I : ℝ)) ^ θ)
      (c + (1 : ℝ) / (2 * m)) I h := by
  have hstep := gaussClass_multiplier_step (K₁ := Real.sqrt (1 + 2 * K))
    (K₂ := (2 * K) ^ ((1 : ℝ) / (2 * m))) (c' := (1 : ℝ) / (2 * m))
    hA hB hθ0 hθ1 hc0 (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _) hI hg
    (fun j => (gaussShiftRatio k p (I : ℤ) j : ℂ))
    (fun j hj => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (gaussShiftRatio_nonneg k p (I : ℤ) j)]
      exact gaussShiftRatio_le_of_not_spike hm k p hK hKb I j hj)
    (fun j _ => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (gaussShiftRatio_nonneg k p (I : ℤ) j)]
      exact gaussShiftRatio_le_of_spike hm k p hK hKb I j)
  intro j
  have hval : ‖h j‖ = ‖(gaussShiftRatio k p (I : ℤ) j : ℂ) * g j‖ := by
    rw [hnorm j, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gaussShiftRatio_nonneg k p (I : ℤ) j)]
  rw [hval]
  exact hstep j

theorem gaussClass_shiftedBlockDiag_step (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ}
    (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {A θ B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hc0 : 0 < c)
    {I : ℕ} (hI : 2 ≤ I) (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
    (hv : TwoPieceAmplitude A θ (B / (1 + (I : ℝ)) ^ θ) c I
      (fun j => fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j)) :
    TwoPieceAmplitude (Real.sqrt (1 + 2 * K) * A) θ
      (((2 * K) ^ ((1 : ℝ) / (2 * m)) * (2 * A + B)) / (1 + (I : ℝ)) ^ θ)
      (c + (1 : ℝ) / (2 * m)) I
      (fun j => fourierCoeff ((gaussShiftedBlockDiag hm k p (I : ℤ) v :
        AddCircle (1 : ℝ) → ℂ)) j) :=
  gaussClass_shifted_step hm k p hK hKb hA hB hθ0 hθ1 hc0 hI hv
    (fun j => norm_fourierCoeff_gaussShiftedBlockDiag hm k p (I : ℤ) v j)

theorem gaussClass_shiftedBlockOf_step (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) {K : ℝ}
    (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {A θ B c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hc0 : 0 < c)
    {I : ℕ} (hI : 2 ≤ I) (v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
    (hv : TwoPieceAmplitude A θ (B / (1 + (I : ℝ)) ^ θ) c I
      (fun j => fourierCoeff ((v : AddCircle (1 : ℝ) → ℂ)) j)) :
    TwoPieceAmplitude (Real.sqrt (1 + 2 * K) * A) θ
      (((2 * K) ^ ((1 : ℝ) / (2 * m)) * (2 * A + B)) / (1 + (I : ℝ)) ^ θ)
      (c + (1 : ℝ) / (2 * m)) I
      (fun j => fourierCoeff ((gaussShiftedBlockOf hm k p (I : ℤ) v :
        AddCircle (1 : ℝ) → ℂ)) j) := by
  refine gaussClass_shifted_step hm k p hK hKb hA hB hθ0 hθ1 hc0 hI hv (fun j => ?_)
  rw [fourierCoeff_gaussShiftedBlockOf, norm_mul, norm_mul, norm_inv, gaussShiftRatio,
    RCLike.norm_conj, RCLike.norm_conj, div_eq_inv_mul, mul_assoc]

/-! ## The two prime-scale symbols -/

theorem norm_fourierCoeff_gaussPrimeScaleCircle_le {p : ℝ} (hp : 1 < p) (x : ℤ) :
    ‖fourierCoeff (gaussPrimeScaleCircle p) x‖
      ≤ (2 * (Real.sqrt p - 1) / min (Real.log p / 2) (2 * Real.pi)) / (1 + (x.natAbs : ℝ)) := by
  have habs : |(x : ℝ)| = (x.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hbase := norm_gaussPrimeScaleFourierCoefficient_le hp x
  rw [habs] at hbase
  rwa [fourierCoeff_gaussPrimeScaleCircle hp]

theorem exists_gaussClass_primeScale_step {p : ℝ} (hp : 1 < p) {θ c ε : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hθ1 : θ ≤ 1) (hε0 : 0 < ε) (hεθ : ε < θ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ A' B' : ℝ, 0 ≤ A' ∧ 0 ≤ B' ∧ ∀ (I : ℕ), 1 ≤ I →
      ∀ u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))),
      TwoPieceAmplitude A θ (B / (1 + (I : ℝ)) ^ θ) c I
          (fun j => fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j) →
      TwoPieceAmplitude A' (θ - ε) (B' / (1 + (I : ℝ)) ^ (θ - ε)) c I
        (fun j => fourierCoeff ((gaussPrimeScaleBlock hp u : AddCircle (1 : ℝ) → ℂ)) j) :=
  exists_gaussClass_symbol_step hc0 hc1 hθ1 hε0 hεθ (measurable_gaussPrimeScaleCircle p)
    (Real.sqrt_nonneg p) (norm_gaussPrimeScaleCircle_le hp) (gaussPrimeScaleCircle_real p)
    (norm_fourierCoeff_gaussPrimeScaleCircle_le hp) A B hA hB

theorem exists_gaussClass_primeScaleInvSq_step {p : ℝ} (hp : 1 < p) {θ c ε : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hθ1 : θ ≤ 1) (hε0 : 0 < ε) (hεθ : ε < θ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ A' B' : ℝ, 0 ≤ A' ∧ 0 ≤ B' ∧ ∀ (I : ℕ), 1 ≤ I →
      ∀ u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))),
      TwoPieceAmplitude A θ (B / (1 + (I : ℝ)) ^ θ) c I
          (fun j => fourierCoeff ((u : AddCircle (1 : ℝ) → ℂ)) j) →
      TwoPieceAmplitude A' (θ - ε) (B' / (1 + (I : ℝ)) ^ (θ - ε)) c I
        (fun j => fourierCoeff ((gaussPrimeScaleInvSqBlock hp u : AddCircle (1 : ℝ) → ℂ)) j) :=
  exists_gaussClass_symbol_step hc0 hc1 hθ1 hε0 hεθ (measurable_gaussPrimeScaleInvSqCircle p)
    zero_le_one (norm_gaussPrimeScaleInvSqCircle_le hp) (gaussPrimeScaleInvSqCircle_real p)
    (norm_fourierCoeff_gaussPrimeScaleInvSqCircle_le hp) A B hA hB

/-! ## One principal step -/

set_option maxHeartbeats 1000000 in
/-- **The principal step keeps the tied class**, dropping the exponent by `3ε` (one drop per
convolution) and raising the spike exponent by `1/m` (one half per normalized shifted block). -/
theorem exists_gaussClass_principalStep (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {θ c ε : ℝ} (hc0 : 0 < c) (hcm : c + 1 / (m : ℝ) < 1) (hθ1 : θ ≤ 1) (hε0 : 0 < ε)
    (h3ε : 3 * ε < θ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ A' B' : ℝ, 0 ≤ A' ∧ 0 ≤ B' ∧ ∀ (I : ℕ), 2 ≤ I →
      ∀ f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))),
      TwoPieceAmplitude A θ (B / (1 + (I : ℝ)) ^ θ) c I
          (fun j => fourierCoeff ((f : AddCircle (1 : ℝ) → ℂ)) j) →
      TwoPieceAmplitude A' (θ - 3 * ε) (B' / (1 + (I : ℝ)) ^ (θ - 3 * ε)) (c + 1 / (m : ℝ)) I
        (fun j => fourierCoeff ((gaussPrincipalStepBlock hm k p hp (I : ℤ) f :
          AddCircle (1 : ℝ) → ℂ)) j) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hhalf : (1 : ℝ) / (2 * (m : ℝ)) + 1 / (2 * (m : ℝ)) = 1 / (m : ℝ) := by field_simp; ring
  have hhalf0 : (0 : ℝ) < 1 / (2 * (m : ℝ)) := by positivity
  have hc1 : c < 1 := by
    have : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    linarith
  set c2 : ℝ := c + 1 / (2 * (m : ℝ)) with hc2def
  have hc20 : 0 < c2 := by rw [hc2def]; linarith
  have hc21 : c2 < 1 := by rw [hc2def]; linarith [hhalf, hhalf0]
  have hc4 : c2 + 1 / (2 * (m : ℝ)) = c + 1 / (m : ℝ) := by rw [hc2def]; linarith [hhalf]
  obtain ⟨A1, B1, hA1, hB1, hstep1⟩ := exists_gaussClass_primeScale_step hp hc0 hc1 hθ1 hε0
    (by linarith : ε < θ) A B hA hB
  set A2 : ℝ := Real.sqrt (1 + 2 * K) * A1 with hA2def
  set B2 : ℝ := (2 * K) ^ ((1 : ℝ) / (2 * (m : ℝ))) * (2 * A1 + B1) with hB2def
  have hA20 : 0 ≤ A2 := by rw [hA2def]; positivity
  have hB20 : 0 ≤ B2 := by
    rw [hB2def]
    have : (0 : ℝ) ≤ (2 * K) ^ ((1 : ℝ) / (2 * (m : ℝ))) := Real.rpow_nonneg (by positivity) _
    positivity
  obtain ⟨A3, B3, hA3, hB3, hstep3⟩ := exists_gaussClass_primeScaleInvSq_step hp hc20 hc21
    (by linarith : θ - ε ≤ 1) hε0 (by linarith : ε < θ - ε) A2 B2 hA20 hB20
  set A4 : ℝ := Real.sqrt (1 + 2 * K) * A3 with hA4def
  set B4 : ℝ := (2 * K) ^ ((1 : ℝ) / (2 * (m : ℝ))) * (2 * A3 + B3) with hB4def
  have hA40 : 0 ≤ A4 := by rw [hA4def]; positivity
  have hB40 : 0 ≤ B4 := by
    rw [hB4def]
    have : (0 : ℝ) ≤ (2 * K) ^ ((1 : ℝ) / (2 * (m : ℝ))) := Real.rpow_nonneg (by positivity) _
    positivity
  obtain ⟨A5, B5, hA5, hB5, hstep5⟩ := exists_gaussClass_primeScale_step (θ := θ - ε - ε) hp
    (by linarith [hhalf0] : (0 : ℝ) < c2 + 1 / (2 * (m : ℝ)))
    (by rw [hc4]; exact hcm) (by linarith : θ - ε - ε ≤ 1) hε0
    (by linarith : ε < θ - ε - ε) A4 B4 hA40 hB40
  refine ⟨A5, B5, hA5, hB5, fun I hI f hf => ?_⟩
  have hI1 : 1 ≤ I := by omega
  have h1 := hstep1 I hI1 f hf
  have h2 := gaussClass_shiftedBlockOf_step hm k p hK hKb hA1 hB1
    (by linarith : (0 : ℝ) ≤ θ - ε) (by linarith : θ - ε ≤ 1) hc0 hI _ h1
  have h3 := hstep3 I hI1 _ h2
  have h4 := gaussClass_shiftedBlockDiag_step hm k p hK hKb hA3 hB3
    (by linarith : (0 : ℝ) ≤ θ - ε - ε) (by linarith : θ - ε - ε ≤ 1) hc20 hI _ h3
  have h5 := hstep5 I hI1 _ h4
  have hθrw : θ - ε - ε - ε = θ - 3 * ε := by ring
  have hcrw : c2 + 1 / (2 * (m : ℝ)) = c + 1 / (m : ℝ) := hc4
  rw [gaussPrincipalStepBlock_apply]
  rw [hθrw, hcrw] at h5
  exact h5

/-! ## The base vector and the iteration -/

theorem norm_fourierCoeff_fourierLp_zero (j : ℤ) :
    ‖fourierCoeff ((fourierLp 2 (0 : ℤ) :
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ) j‖
      = if j = 0 then 1 else 0 := by
  rw [← fourierBasis_repr]
  have hb : (fourierLp 2 (0 : ℤ) : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
      = (fourierBasis (T := (1 : ℝ))) 0 := by rw [coe_fourierBasis]
  rw [hb, HilbertBasis.repr_self]
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem twoPieceAmplitude_fourierLp_zero {θ c : ℝ} (I : ℕ) :
    TwoPieceAmplitude 1 θ 0 c I
      (fun j => fourierCoeff ((fourierLp 2 (0 : ℤ) :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) : AddCircle (1 : ℝ) → ℂ) j) := by
  intro j
  have hspike : spikeProfile 0 c I j = 0 := by
    rw [spikeProfile]
    split_ifs <;> simp
  rw [hspike, add_zero, norm_fourierCoeff_fourierLp_zero]
  split_ifs with h
  · subst h
    simp
  · positivity

set_option maxHeartbeats 1000000 in
/-- **The iterates of the principal step stay in the class.**  Each step costs `3ε` of exponent
and adds `1/m` to the spike exponent; the constants stay independent of the frequency. -/
theorem exists_gaussClass_principalStep_pow (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {c₀ ε : ℝ} (hc₀ : 0 < c₀) (hε0 : 0 < ε) :
    ∀ r : ℕ, c₀ + (r : ℝ) / (m : ℝ) < 1 → 3 * (r : ℝ) * ε < 1 →
      ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ I : ℕ, 2 ≤ I →
        TwoPieceAmplitude A (1 - 3 * (r : ℝ) * ε)
          (B / (1 + (I : ℝ)) ^ (1 - 3 * (r : ℝ) * ε)) (c₀ + (r : ℝ) / (m : ℝ)) I
          (fun j => fourierCoeff (((gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ r)
            (fourierLp 2 (0 : ℤ)) : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
              AddCircle (1 : ℝ) → ℂ) j) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  intro r
  induction r with
  | zero =>
      intro _ _
      refine ⟨1, 0, by norm_num, le_rfl, fun I hI => ?_⟩
      have hz : ((gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ 0) (fourierLp 2 (0 : ℤ)) :
          Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
          = fourierLp 2 (0 : ℤ) := by rw [pow_zero]; rfl
      rw [hz]
      have hzero : (0 : ℝ) / (1 + (I : ℝ)) ^ (1 - 3 * ((0 : ℕ) : ℝ) * ε) = 0 := by simp
      rw [hzero]
      exact twoPieceAmplitude_fourierLp_zero I
  | succ r ih =>
      intro hcr hεr
      have hcr' : c₀ + (r : ℝ) / (m : ℝ) < 1 := by
        have hmono : (r : ℝ) / (m : ℝ) ≤ ((r + 1 : ℕ) : ℝ) / (m : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hm0.le
          push_cast
          linarith
        linarith [hcr, hmono]
      have hεr' : 3 * (r : ℝ) * ε < 1 := by
        push_cast at hεr ⊢
        nlinarith [hε0.le]
      obtain ⟨A, B, hA, hB, hstep⟩ := ih hcr' hεr'
      have hcm : c₀ + (r : ℝ) / (m : ℝ) + 1 / (m : ℝ) < 1 := by
        have hid : c₀ + (r : ℝ) / (m : ℝ) + 1 / (m : ℝ) = c₀ + ((r : ℝ) + 1) / (m : ℝ) := by
          field_simp
          ring
        rw [hid]
        push_cast at hcr
        linarith
      have h3ε : 3 * ε < 1 - 3 * (r : ℝ) * ε := by
        push_cast at hεr
        nlinarith [hε0.le]
      obtain ⟨A', B', hA', hB', hR⟩ := exists_gaussClass_principalStep hm k p hp hK hKb
        (θ := 1 - 3 * (r : ℝ) * ε) (c := c₀ + (r : ℝ) / (m : ℝ))
        (by positivity) hcm (by nlinarith [hε0.le, Nat.cast_nonneg (α := ℝ) r]) hε0 h3ε A B hA hB
      refine ⟨A', B', hA', hB', fun I hI => ?_⟩
      have hpow : ((gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ (r + 1)) (fourierLp 2 (0 : ℤ)) :
          Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
          = gaussPrincipalStepBlock hm k p hp (I : ℤ)
            ((gaussPrincipalStepBlock hm k p hp (I : ℤ) ^ r) (fourierLp 2 (0 : ℤ))) := by
        rw [pow_succ']
        rfl
      have hmain := hR I hI _ (hstep I hI)
      have hθid : 1 - 3 * (r : ℝ) * ε - 3 * ε = 1 - 3 * ((r + 1 : ℕ) : ℝ) * ε := by
        push_cast
        ring
      have hcid : c₀ + (r : ℝ) / (m : ℝ) + 1 / (m : ℝ) = c₀ + ((r + 1 : ℕ) : ℝ) / (m : ℝ) := by
        push_cast
        field_simp
        ring
      rw [hθid, hcid] at hmain
      rw [hpow]
      exact hmain

end

end RHTower
