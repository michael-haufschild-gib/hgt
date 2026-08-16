import GaloisForLFunctions.RHTower.GaussDefectHighModeTail
import GaloisForLFunctions.RHTower.GaussConvolutionCoefficient

/-!
# The low-mode block seen from the spike

The frequencies of the spike `2|n+l| < n` are far from the band `|j| ≤ n/4`: every difference
`|l - j|` exceeds `n/4`.  A convolution kernel with harmonic decay therefore contributes at most
`C/n` to each spike coefficient of the truncated vector, and the truncated vector has `ℓ¹` mass
`O(log n)`, because on the low band the lattice defect is bounded by a constant.

The resulting bound `O(log n / n)` on the spike coefficients is what the linear spike mass can
absorb.
-/

namespace RHTower

open Filter Topology MeasureTheory GaloisForLFunctions

open scoped ENNReal NNReal

noncomputable section

variable {m : ℕ}

/-- The spike is separated from the low band. -/
theorem spike_lowBand_separation {I J : ℕ} (hJ : 4 * J ≤ I) {l j : ℤ}
    (hl : 2 * ((I : ℤ) + l).natAbs < I) (hj : j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ)) :
    I ≤ 4 * (1 + (j - l).natAbs) := by
  rw [Finset.mem_Icc] at hj
  omega

/-- **The kernel bound on the spike.**  A harmonic convolution kernel applied to a vector supported
in the low band has small coefficients at every spike frequency. -/
theorem norm_fourierCoeff_symbol_truncate_le {c : AddCircle (1 : ℝ) → ℂ} (hc : Measurable c)
    {Cb : ℝ} (hC0 : 0 ≤ Cb) (hC : ∀ x, ‖c x‖ ≤ Cb) (hreal : ∀ x, starRingEnd ℂ (c x) = c x)
    {A : ℝ} (hA : ∀ x : ℤ, ‖fourierCoeff c x‖ ≤ A / (1 + (x.natAbs : ℝ)))
    (S : Finset ℤ) (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ j ∈ S, D ≤ (1 : ℝ) + (((j - l).natAbs : ℕ) : ℝ)) :
    ‖fourierCoeff ((MeasureTheory.lpBoundedMulCLM (p := 2)
        (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC (fourierTruncate S w) :
        AddCircle (1 : ℝ) → ℂ)) l‖
      ≤ (A / D) * ∑ j ∈ S, ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ := by
  classical
  have hA0 : 0 ≤ A := by
    have h0 := hA 0
    simp only [Int.natAbs_zero, Nat.cast_zero, add_zero, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hbase := norm_fourierCoeff_lpBoundedMulCLM_le hc hC0 hC hreal hA (fourierTruncate S w) l
  have hzero : ∀ j ∉ S, A / (1 + (((j - l).natAbs : ℕ) : ℝ)) *
      ‖fourierCoeff ((fourierTruncate S w : AddCircle (1 : ℝ) → ℂ)) j‖ = 0 := by
    intro j hj
    rw [fourierCoeff_fourierTruncate, if_neg hj, norm_zero, mul_zero]
  rw [tsum_eq_sum hzero] at hbase
  refine hbase.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [fourierCoeff_fourierTruncate, if_pos hj]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hsepj := hsep j hj
  rw [div_le_div_iff₀ (by positivity) hD]
  nlinarith [hsepj, hA0, hD]

/-- The reciprocal-square specialization of the kernel bound. -/
theorem norm_fourierCoeff_invSq_truncate_le {P : ℝ} (hP : 1 < P) (S : Finset ℤ)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (l : ℤ) {D : ℝ} (hD : 0 < D)
    (hsep : ∀ j ∈ S, D ≤ (1 : ℝ) + (((j - l).natAbs : ℕ) : ℝ)) :
    ‖fourierCoeff ((gaussPrimeScaleInvSqBlock hP (fourierTruncate S w) :
        AddCircle (1 : ℝ) → ℂ)) l‖
      ≤ (2 / D) * ∑ j ∈ S, ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖ :=
  norm_fourierCoeff_symbol_truncate_le (measurable_gaussPrimeScaleInvSqCircle P) zero_le_one
    (norm_gaussPrimeScaleInvSqCircle_le hP) (gaussPrimeScaleInvSqCircle_conj P)
    (norm_fourierCoeff_gaussPrimeScaleInvSqCircle_le hP) S w l hD hsep

/-- On the low band the lattice defect is bounded by a constant. -/
theorem norm_gaussSampleRatioDefect_le_of_lowBand (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {I J : ℕ} (hJ : 4 * J ≤ I) {j : ℤ} (hj : j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ)) :
    ‖gaussSampleRatioDefect k p j (I : ℤ)‖ ≤ 5 + 3 * K := by
  have hdef := norm_gaussSampleRatioDefect_sq_le hm k p hKb I j
  have hnn : (0 : ℝ) ≤ ‖gaussSampleRatioDefect k p j (I : ℤ)‖ := norm_nonneg _
  have hquot : 2 * K * (I : ℝ) / ((((I : ℤ) + j).natAbs : ℕ) : ℝ) ≤ 3 * K := by
    rcases Nat.eq_zero_or_pos ((I : ℤ) + j).natAbs with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, div_zero]
      positivity
    · rw [Finset.mem_Icc] at hj
      have hge : 4 * ((I : ℤ) + j).natAbs ≥ 3 * I := by omega
      have hgeR : 3 * (I : ℝ) ≤ 4 * ((((I : ℤ) + j).natAbs : ℕ) : ℝ) := by exact_mod_cast hge
      have hposR : (0 : ℝ) < ((((I : ℤ) + j).natAbs : ℕ) : ℝ) := by exact_mod_cast hpos
      rw [div_le_iff₀ hposR]
      nlinarith [hK.le]
  nlinarith [hdef, hquot, hnn, sq_nonneg (‖gaussSampleRatioDefect k p j (I : ℤ)‖ - 1)]

/-- **The `ℓ¹` mass of the low band is logarithmic.** -/
theorem sum_norm_fourierCoeff_lowBand_le (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 →
      ‖gaussSampleValue k p a‖ ^ (2 * m) * (a.natAbs : ℝ)
        ≤ K * (‖gaussSampleValue k p b‖ ^ (2 * m) * (b.natAbs : ℝ)))
    {A : ℝ} (hA : 0 ≤ A) {I J : ℕ} (hJ : 4 * J ≤ I)
    {w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))}
    (hw : ∀ j : ℤ, ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖
      ≤ (A / (1 + (j.natAbs : ℝ))) * ‖gaussSampleRatioDefect k p j (I : ℤ)‖) :
    ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖
      ≤ A * (5 + 3 * K) * (2 * (1 + Real.log ((J : ℝ) + 2))) := by
  have hstep : ∀ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ),
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) j‖
        ≤ (A * (5 + 3 * K)) * (1 / (1 + (j.natAbs : ℝ))) := by
    intro j hj
    refine (hw j).trans ?_
    have hd := norm_gaussSampleRatioDefect_le_of_lowBand hm k p hK hKb hJ hj
    have hpos : (0 : ℝ) < 1 + (j.natAbs : ℝ) := by positivity
    rw [div_eq_mul_one_div, mul_comm A (1 / (1 + (j.natAbs : ℝ))), mul_assoc]
    rw [show A * (5 + 3 * K) * (1 / (1 + (j.natAbs : ℝ)))
        = (1 / (1 + (j.natAbs : ℝ))) * (A * (5 + 3 * K)) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hd hA
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  have hharm := sum_Icc_int_inv_one_add_natAbs_le J
  refine mul_le_mul_of_nonneg_left hharm (by positivity)

end

end RHTower
