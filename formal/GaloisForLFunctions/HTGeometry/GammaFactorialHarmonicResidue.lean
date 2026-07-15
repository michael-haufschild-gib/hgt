import GaloisForLFunctions.HTGeometry.GammaFactorialFirstJetBoundary
import GaloisForLFunctions.HTGeometry.GammaLogDeriv
import GaloisForLFunctions.HTGeometry.GammaWeierstrass

/-!
# The harmonic transverse residue of the Gamma factorial microscope

The leading factorial microscope sends Gamma to the reciprocal germ `M(x) = -1 / x`.  Its first
jet therefore collapses onto the Riccati boundary `M' = M²`.  This file identifies the first
nonzero direction beyond that boundary.

For the Gamma zoom `gₙ(x) = Gamma(-n + sₙ x)`, where `sₙ = (-1)^(n+1) / n!`, the pole-germ
residue of its Riccati defect is exactly

`lim_{x → 0, x ≠ 0} x (gₙ'(x) - gₙ(x)²) = -2 sₙ digamma(n+1)`.

After division by the canonical harmonic scale `sₙ Hₙ`, these residues converge to `-2`.
Thus the Gamma deformation crosses the complete first-jet reciprocal boundary in a canonical,
nonzero arithmetic direction.  The result is extracted from the exact second derivative of the
entire reciprocal Gamma function at its negative-integer zeros; no numerical approximation and no
interchange of moving limits is used.
-/

namespace GaloisForLFunctions

open Complex Filter Topology

noncomputable section

/-- The regular part of digamma at the pole `-n`, expressed at the corresponding positive
integer. -/
def gammaPoleHarmonicParameter (n : ℕ) : ℂ :=
  Complex.digamma ((n : ℂ) + 1)

/-- The pole parameter is exactly the universal constant `digamma(1)` plus the harmonic number. -/
theorem gammaPoleHarmonicParameter_eq (n : ℕ) :
    gammaPoleHarmonicParameter n =
      Complex.digamma 1 + (harmonic n : ℂ) := by
  have hOff : ∀ k : ℕ, (1 : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have h := HTGeometry.digamma_add_nat 1 hOff n
  rw [HilbertSchmidt.harmonic_cast_complex]
  simpa [gammaPoleHarmonicParameter, add_comm] using h

/-- The factorial scale refined by the divergent harmonic pole parameter. -/
def gammaHarmonicMicroscopeScale (n : ℕ) : ℂ :=
  reciprocalGammaFactorialScale n * (harmonic n : ℂ)

theorem tendsto_harmonic_cast_real_atTop :
    Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun n : ℕ => Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun n => log_add_one_le_harmonic n) hlog

theorem tendsto_inv_harmonic_cast_complex_zero :
    Tendsto (fun n : ℕ => ((harmonic n : ℂ)⁻¹)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun n : ℕ => ((harmonic n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_harmonic_cast_real_atTop
  have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have heq : (fun n : ℕ => ((harmonic n : ℂ)⁻¹)) =
      fun n : ℕ => Complex.ofReal ((harmonic n : ℝ)⁻¹) := by
    funext n
    simpa only using (Complex.ofReal_inv (harmonic n : ℝ)).symm
  rw [heq]
  exact hcast

/-- The entire reciprocal-Gamma zoom at the negative integer `-n`. -/
def reciprocalGammaFactorialZoom (n : ℕ) : ℂ → ℂ :=
  factorialBlowUpZoom reciprocalGammaEntire n

theorem reciprocalGammaFactorialZoom_zero (n : ℕ) :
    reciprocalGammaFactorialZoom n 0 = 0 := by
  rw [reciprocalGammaFactorialZoom]
  simp only [factorialBlowUpZoom, mul_zero, add_zero]
  rw [reciprocalGammaEntire, Complex.Gamma_neg_nat_eq_zero]
  simp

/-- The factorial scaling normalizes the derivative of reciprocal Gamma at every pole to `-1`. -/
theorem deriv_reciprocalGammaFactorialZoom_zero (n : ℕ) :
    deriv (reciprocalGammaFactorialZoom n) 0 = -1 := by
  rw [← iteratedDeriv_one]
  rw [reciprocalGammaFactorialZoom, iteratedDeriv_factorialBlowUpZoom]
  simp only [pow_one, mul_zero, add_zero]
  rw [iteratedDeriv_one]
  change reciprocalGammaFactorialScale n *
      deriv (fun z : ℂ => (Complex.Gamma z)⁻¹) (-(n : ℂ)) = -1
  rw [(hasDerivAt_oneDivGamma_neg_nat n).deriv]
  simpa [mul_comm] using reciprocalGammaFactorialScale_cancel n

/-- The exact quadratic pole coefficient.  This is the arithmetic datum that survives after the
leading reciprocal boundary has been removed. -/
theorem iteratedDeriv_two_reciprocalGammaFactorialZoom_zero (n : ℕ) :
    iteratedDeriv 2 (reciprocalGammaFactorialZoom n) 0 =
      2 * reciprocalGammaFactorialScale n *
        Complex.digamma ((n : ℂ) + 1) := by
  rw [reciprocalGammaFactorialZoom, iteratedDeriv_factorialBlowUpZoom]
  simp only [mul_zero, add_zero]
  rw [iteratedDeriv_two_reciprocalGammaEntire_neg_nat]
  have hcancel := reciprocalGammaFactorialScale_cancel n
  calc
    reciprocalGammaFactorialScale n ^ 2 *
        (-2 * ((-1 : ℂ) ^ n * (n.factorial : ℂ)) *
          Complex.digamma ((n : ℂ) + 1)) =
      -2 * (((-1 : ℂ) ^ n * (n.factorial : ℂ)) *
        reciprocalGammaFactorialScale n) * reciprocalGammaFactorialScale n *
          Complex.digamma ((n : ℂ) + 1) := by ring
    _ = _ := by rw [hcancel]; ring

theorem contDiff_reciprocalGammaFactorialZoom (n : ℕ) :
    ContDiff ℂ ⊤ (reciprocalGammaFactorialZoom n) := by
  rw [reciprocalGammaFactorialZoom]
  exact contDiff_reciprocalGammaEntire.comp
    (contDiff_const.neg.add (contDiff_const.mul contDiff_id))

/-- The normalized reciprocal Gamma germ tends to its simple-zero derivative. -/
theorem tendsto_reciprocalGammaFactorialZoom_div (n : ℕ) :
    Tendsto (fun x : ℂ => reciprocalGammaFactorialZoom n x / x)
      (𝓝[≠] 0) (𝓝 (-1)) := by
  have hdiff : Differentiable ℂ (reciprocalGammaFactorialZoom n) :=
    (contDiff_reciprocalGammaFactorialZoom n).differentiable (by simp)
  have hder : HasDerivAt (reciprocalGammaFactorialZoom n) (-1) 0 := by
    have h := (hdiff 0).hasDerivAt
    rwa [deriv_reciprocalGammaFactorialZoom_zero] at h
  have h := hder.tendsto_slope_zero
  simpa [reciprocalGammaFactorialZoom_zero, div_eq_inv_mul] using h

/-- The normalized derivative correction tends to the exact quadratic coefficient. -/
theorem tendsto_deriv_reciprocalGammaFactorialZoom_add_one_div (n : ℕ) :
    Tendsto (fun x : ℂ =>
      (deriv (reciprocalGammaFactorialZoom n) x + 1) / x)
      (𝓝[≠] 0)
      (𝓝 (2 * reciprocalGammaFactorialScale n *
        Complex.digamma ((n : ℂ) + 1))) := by
  have hdiff : Differentiable ℂ (reciprocalGammaFactorialZoom n) :=
    (contDiff_reciprocalGammaFactorialZoom n).differentiable (by simp)
  have han : AnalyticAt ℂ (reciprocalGammaFactorialZoom n) 0 :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff) 0 (Set.mem_univ 0)
  have hder : HasDerivAt (deriv (reciprocalGammaFactorialZoom n))
      (2 * reciprocalGammaFactorialScale n *
        Complex.digamma ((n : ℂ) + 1)) 0 := by
    have h := han.deriv.differentiableAt.hasDerivAt
    convert h using 1
    simpa [show 2 = 1 + 1 by omega, iteratedDeriv_succ', iteratedDeriv_one] using
      (iteratedDeriv_two_reciprocalGammaFactorialZoom_zero n).symm
  have h := hder.tendsto_slope_zero
  rw [deriv_reciprocalGammaFactorialZoom_zero] at h
  simpa [div_eq_inv_mul] using h

theorem factorialBlowUpZoom_Gamma_eq_inv_reciprocalGammaFactorialZoom (n : ℕ) :
    factorialBlowUpZoom Complex.Gamma n =
      fun x => (reciprocalGammaFactorialZoom n x)⁻¹ := by
  funext x
  simp [factorialBlowUpZoom, reciprocalGammaFactorialZoom, reciprocalGammaEntire]

/-- Away from the pole, the Gamma Riccati defect is the reciprocal-Gamma derivative defect divided
by the square of reciprocal Gamma. -/
theorem gammaFactorialFirstJetDefect_eq_reciprocal
    (n : ℕ) (x : ℂ) (hx : reciprocalGammaFactorialZoom n x ≠ 0) :
    gammaFactorialFirstJetDefect n x =
      -(deriv (reciprocalGammaFactorialZoom n) x + 1) /
        reciprocalGammaFactorialZoom n x ^ 2 := by
  rw [gammaFactorialFirstJetDefect, iteratedDeriv_one,
    factorialBlowUpZoom_Gamma_eq_inv_reciprocalGammaFactorialZoom]
  rw [deriv_fun_inv''
    ((contDiff_reciprocalGammaFactorialZoom n).differentiable (by simp) x) hx]
  field_simp [hx]
  ring

/-- **Exact transverse pole residue.**  The Gamma first jet leaves the reciprocal Riccati boundary
in the direction `-2 sₙ digamma(n+1)` at the pole `-n`. -/
theorem tendsto_gammaFactorialFirstJetDefect_pole_residue (n : ℕ) :
    Tendsto (fun x : ℂ => x * gammaFactorialFirstJetDefect n x)
      (𝓝[≠] 0)
      (𝓝 (-2 * reciprocalGammaFactorialScale n *
        Complex.digamma ((n : ℂ) + 1))) := by
  have hA := (tendsto_deriv_reciprocalGammaFactorialZoom_add_one_div n).neg
  have hB := tendsto_reciprocalGammaFactorialZoom_div n
  have hlim := hA.div (hB.pow 2) (by norm_num)
  have hquot_ne : ∀ᶠ x : ℂ in 𝓝[≠] 0,
      reciprocalGammaFactorialZoom n x / x ≠ 0 :=
    hB.eventually (eventually_ne_nhds (by norm_num))
  have hx_ne : ∀ᶠ x : ℂ in 𝓝[≠] 0, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have heq : ∀ᶠ x : ℂ in 𝓝[≠] 0,
      x * gammaFactorialFirstJetDefect n x =
        (-((deriv (reciprocalGammaFactorialZoom n) x + 1) / x)) /
          (reciprocalGammaFactorialZoom n x / x) ^ 2 := by
    filter_upwards [hquot_ne, hx_ne] with x hquot hx
    have hh : reciprocalGammaFactorialZoom n x ≠ 0 := by
      intro hzero
      apply hquot
      simp [hzero]
    rw [gammaFactorialFirstJetDefect_eq_reciprocal n x hh]
    field_simp [hx, hh]
  convert hlim.congr' (heq.mono fun _ h => h.symm) using 1
  ring_nf

/-- The positive-integer digamma value is asymptotic to the harmonic number, over `ℂ`. -/
theorem tendsto_gammaPoleHarmonicParameter_div_harmonic :
    Tendsto (fun n : ℕ =>
      gammaPoleHarmonicParameter n / (harmonic n : ℂ))
      atTop (𝓝 1) := by
  have hsmall := tendsto_inv_harmonic_cast_complex_zero.const_mul
    (Complex.digamma 1)
  have hlim := (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1)).add hsmall
  have heq : ∀ᶠ n : ℕ in atTop,
      gammaPoleHarmonicParameter n / (harmonic n : ℂ) =
        1 + Complex.digamma 1 * (harmonic n : ℂ)⁻¹ := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hH : (harmonic n : ℂ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'
    rw [gammaPoleHarmonicParameter_eq]
    field_simp [hH]
    ring
  simpa using hlim.congr' (heq.mono fun _ h => h.symm)

/-- **Canonical nonzero harmonic direction.**  The exact pole residues, divided by `sₙ Hₙ`,
converge to `-2`.  In particular the harmonic deformation is transverse to the Riccati boundary
and cannot vanish through cancellation in the leading reciprocal first-jet kernel. -/
theorem tendsto_normalized_gammaFactorialFirstJetDefect_pole_residue :
    Tendsto (fun n : ℕ =>
      (-2 * reciprocalGammaFactorialScale n *
        Complex.digamma ((n : ℂ) + 1)) /
          gammaHarmonicMicroscopeScale n)
      atTop (𝓝 (-2)) := by
  have hlim := tendsto_gammaPoleHarmonicParameter_div_harmonic.const_mul (-2)
  have heq : ∀ᶠ n : ℕ in atTop,
      (-2 * reciprocalGammaFactorialScale n *
        Complex.digamma ((n : ℂ) + 1)) /
          gammaHarmonicMicroscopeScale n =
        -2 * (gammaPoleHarmonicParameter n / (harmonic n : ℂ)) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hs : reciprocalGammaFactorialScale n ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.factorial_ne_zero n)
    have hH : (harmonic n : ℂ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : n ≠ 0)).ne'
    rw [gammaHarmonicMicroscopeScale]
    change (-2 * reciprocalGammaFactorialScale n * gammaPoleHarmonicParameter n) /
        (reciprocalGammaFactorialScale n * (harmonic n : ℂ)) = _
    field_simp [hs, hH]
  simpa using hlim.congr' (heq.mono fun _ h => h.symm)

end

end GaloisForLFunctions
