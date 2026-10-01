import GaloisForLFunctions.RHTower.SmoothAFEReflectedCompactChannel

open Complex Finset
noncomputable section
namespace RHTower

/-- Literal normalized free-prime channel, independent of a chosen coherent mode. -/
def compactGaussianNormalizedPrimeChannel (s : ℂ) (N p tau : ℝ) (L : ℕ)
    (ω : SteinhausModel.Omega) : ℂ :=
  (p : ℂ) ^ ((tau : ℂ) * I) *
    normalizedTruncatedGaussianCofactorChannel (fun _ : Fin 1 => s) (N / p) L ω 0 /
      (Real.sqrt N : ℂ)

/-- Every coherent mode represents the same literal normalized channel. -/
theorem compactGaussianNormalizedPrimeChannel_eq_mode {N p : ℝ}
    (hN : 0 < N) (hp : 0 < p) (s : ℂ) (tau t : ℝ) {A : ℂ} (hA : A ≠ 0)
    (L : ℕ) (ω : SteinhausModel.Omega) :
    compactGaussianNormalizedPrimeChannel s N p tau L ω =
      compactGaussianPrimeAmplitude N p t tau A *
        relativeTruncatedFullGaussianCofactorScalarMode s t A (N / p) L ω := by
  have hR : 0 < N / p := div_pos hN hp
  unfold compactGaussianNormalizedPrimeChannel
  rw [normalizedTruncatedGaussianCofactorChannel_eq_mode _ t hA hR,
    relativeTruncatedFullGaussianCofactorMode_eq_scalar _ t A hR]
  unfold compactGaussianPrimeAmplitude
  ring

/-- Exact common-row factorization of the literal reflected-primal channel. -/
theorem reflectedPrimalChannel_eq_compactGaussianNormalizedPrimeChannel
    (d b tau : ℝ) (N L p : ℕ) (hN : 0 < N) (hp : 0 < p)
    (ω : SteinhausModel.Omega) :
    steinhausLargePrimeChannel
      (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d (tau + b) 1 N) L p ω =
      reflectedCompactGaussianRow (rightDisplacedLinePt d b) N tau *
        compactGaussianNormalizedPrimeChannel (rightDisplacedLinePt d b) N p tau (L / p)
          (steinhausLogPhaseShift ω tau) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hf := reflectedPrimalChannel_eq_compactGaussian_mode d b tau 0 N L p hN hp
    (A := 1) one_ne_zero ω
  rw [mul_assoc, ← compactGaussianNormalizedPrimeChannel_eq_mode hNR hpR _ tau 0 one_ne_zero] at hf
  exact hf

/-- Every finite literal cofactor is entire, at any fixed scale and phase. -/
theorem differentiable_truncatedFullGaussianCofactor (R : ℝ) (L : ℕ)
    (ω : SteinhausModel.Omega) : Differentiable ℂ (fun s => truncatedFullGaussianCofactor s R L ω) := by
  unfold truncatedFullGaussianCofactor
  apply Differentiable.fun_sum
  intro n _
  exact (((differentiable_id.sub_const (1 : ℂ)).const_cpow (c := ((n + 1 : ℕ) : ℂ))
    (Or.inl (by exact_mod_cast Nat.succ_ne_zero n))).const_mul
      (SteinhausModel.X (n + 1) ω)).mul_const
        (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R))

/-- Removing the common row leaves an entire spectral channel. -/
theorem differentiable_compactGaussianNormalizedPrimeChannel {N p : ℝ}
    (hN : 0 < N) (hp : 0 < p) (tau : ℝ) (L : ℕ) (ω : SteinhausModel.Omega) :
    Differentiable ℂ (fun s => compactGaussianNormalizedPrimeChannel s N p tau L ω) := by
  have hR : 0 < N / p := div_pos hN hp
  change Differentiable ℂ (fun s => (p : ℂ) ^ ((tau : ℂ) * I) *
    (((N / p : ℝ) : ℂ) * (truncatedFullGaussianCofactor s (N / p) L ω *
      ((N / p : ℝ) : ℂ) ^ (-s))) / (Real.sqrt N : ℂ))
  exact (((differentiable_truncatedFullGaussianCofactor (N / p) L ω).mul
    (differentiable_id.neg.const_cpow (c := ((N / p : ℝ) : ℂ))
      (Or.inl (Complex.ofReal_ne_zero.mpr hR.ne')))).const_mul
        ((N / p : ℝ) : ℂ) |>.const_mul ((p : ℂ) ^ ((tau : ℂ) * I))).div_const _

/-- Exact normalized-channel size; the height-dependent prime phase has unit norm. -/
theorem norm_compactGaussianNormalizedPrimeChannel {N p : ℝ}
    (hN : 0 < N) (hp : 0 < p) (s : ℂ) (tau : ℝ) (L : ℕ) (ω : SteinhausModel.Omega) :
    ‖compactGaussianNormalizedPrimeChannel s N p tau L ω‖ =
      ((N / p) / Real.sqrt N) *
        ‖truncatedFullGaussianCofactor s (N / p) L ω * ((N / p : ℝ) : ℂ) ^ (-s)‖ := by
  have hR : 0 < N / p := div_pos hN hp
  simp only [compactGaussianNormalizedPrimeChannel, normalizedTruncatedGaussianCofactorChannel,
    norm_div, norm_mul, Complex.norm_of_nonneg hR.le,
    Complex.norm_of_nonneg (Real.sqrt_nonneg N), Complex.norm_cpow_eq_rpow_re_of_pos hp,
    Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, zero_mul, Complex.ofReal_im,
    Complex.I_im, sub_self, Real.rpow_zero, one_mul]
  ring

end RHTower
