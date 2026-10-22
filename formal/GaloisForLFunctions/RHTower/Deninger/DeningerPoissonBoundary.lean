import GaloisForLFunctions.RHTower.Deninger.DeningerHarmonicMode

/-!
# The Poisson extension of a Kummer phase mode

On the character of frequency `μ` the Poisson extension is the decaying exponential `e^{-|μ| r}`.
Its second radial derivative is `μ²` times itself, which cancels the square of the Kronecker
generator, so the extension is leafwise harmonic; its outward normal derivative at the boundary is
`|μ|`, the absolute value of the generator; and its Dirichlet energy is the same `|μ|`, a positive
boundary form.

The boundary Hodge operator is multiplication by `i` times the sign of the frequency: it squares to
`-1` and has modulus one, and it is the boundary value of the leafwise Hodge star of the harmonic
mode.

* `deningerPoissonProfile_deriv`, `_secondDeriv` : the radial derivatives.
* `deningerPoisson_harmonic` : the extension is harmonic.
* `deningerPoisson_dirichletToNeumann` : the outward normal derivative is `|μ|`.
* `deningerPoisson_energy` : the Dirichlet energy is `|μ|`.
* `deningerBoundaryHodge_sq`, `_norm` : the boundary Hodge operator squares to `-1` and is unitary.
-/

namespace RHTower

open MeasureTheory Set

section PoissonBoundary

/-- **The radial derivative of the Poisson profile.** -/
theorem deningerPoissonProfile_deriv (μ r : ℝ) :
    HasDerivAt (deningerModeProfile μ) (-|μ| * deningerModeProfile μ r) r := by
  have h := deningerModeProfile_hasDerivAt μ r
  rw [show deningerModeProfile μ r * -|μ| = -|μ| * deningerModeProfile μ r from by ring] at h
  exact h

/-- **The second radial derivative of the Poisson profile.**  It is `μ²` times the profile. -/
theorem deningerPoissonProfile_secondDeriv (μ r : ℝ) :
    HasDerivAt (fun s => -|μ| * deningerModeProfile μ s) (μ ^ (2 : ℕ) * deningerModeProfile μ r) r := by
  have h := (deningerPoissonProfile_deriv μ r).const_mul (-|μ|)
  rw [show -|μ| * (-|μ| * deningerModeProfile μ r) = μ ^ (2 : ℕ) * deningerModeProfile μ r from by
    rw [← mul_assoc]
    congr 1
    rw [neg_mul_neg, ← sq_abs, sq]] at h
  exact h

/-- **The Poisson extension is leafwise harmonic.**  The Kronecker generator acts on the character
of frequency `μ` by `i μ`, so its square contributes `-μ²`, which cancels the second radial
derivative. -/
theorem deningerPoisson_harmonic (μ r : ℝ) :
    HasDerivAt (fun s => -|μ| * deningerModeProfile μ s)
      (-(-(μ ^ (2 : ℕ)) * deningerModeProfile μ r)) r := by
  have h := deningerPoissonProfile_secondDeriv μ r
  rw [show -(-(μ ^ (2 : ℕ)) * deningerModeProfile μ r) = μ ^ (2 : ℕ) * deningerModeProfile μ r from by ring]
  exact h

/-- **The Poisson extension attains its boundary value.** -/
@[simp] theorem deningerPoissonProfile_zero (μ : ℝ) : deningerModeProfile μ 0 = 1 := by
  rw [deningerModeProfile, mul_zero, Real.exp_zero]

/-- **The outward Dirichlet-to-Neumann operator is the absolute value of the generator.** -/
theorem deningerPoisson_dirichletToNeumann (μ : ℝ) :
    -(-|μ| * deningerModeProfile μ 0) = |μ| := by
  rw [deningerPoissonProfile_zero, mul_one, neg_neg]

/-- The pointwise Dirichlet energy density of the Poisson extension. -/
theorem deningerPoisson_energyDensity (μ r : ℝ) :
    (-|μ| * deningerModeProfile μ r) ^ (2 : ℕ) + μ ^ (2 : ℕ) * deningerModeProfile μ r ^ (2 : ℕ)
      = 2 * μ ^ (2 : ℕ) * deningerModeProfile μ r ^ (2 : ℕ) := by
  rw [mul_pow, neg_pow, sq_abs]
  ring

/-- **The Dirichlet energy of the Poisson extension is `|μ|`.**  The radial and transverse energies
are equal, and the integral of the squared profile is `1 / (2|μ|)`. -/
theorem deningerPoisson_energy {μ : ℝ} (hμ : μ ≠ 0) :
    ∫ r in Ioi (0 : ℝ), ((-|μ| * deningerModeProfile μ r) ^ (2 : ℕ)
        + μ ^ (2 : ℕ) * deningerModeProfile μ r ^ (2 : ℕ)) = |μ| := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    fun r _ => deningerPoisson_energyDensity μ r]
  rw [show (fun r : ℝ => 2 * μ ^ (2 : ℕ) * deningerModeProfile μ r ^ (2 : ℕ))
      = fun r : ℝ => (2 * μ ^ (2 : ℕ)) * deningerModeProfile μ r ^ (2 : ℕ) from rfl,
    integral_const_mul, deningerModeProfile_integral hμ]
  have habs : |μ| ≠ 0 := abs_ne_zero.mpr hμ
  have hsq : μ ^ (2 : ℕ) = |μ| ^ (2 : ℕ) := (sq_abs μ).symm
  rw [hsq]
  field_simp

/-- The boundary Hodge operator of a mode: `i` times the sign of its frequency. -/
noncomputable def deningerBoundaryHodge (μ : ℝ) : ℂ := Complex.I * (deningerFreqSign μ : ℂ)

/-- **The boundary Hodge operator squares to `-1`.** -/
theorem deningerBoundaryHodge_sq (μ : ℝ) :
    deningerBoundaryHodge μ * deningerBoundaryHodge μ = -1 := by
  have hsq : (deningerFreqSign μ : ℂ) * (deningerFreqSign μ : ℂ) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_sq μ)
  rw [deningerBoundaryHodge]
  calc Complex.I * (deningerFreqSign μ : ℂ) * (Complex.I * (deningerFreqSign μ : ℂ))
      = (Complex.I ^ (2 : ℕ)) * ((deningerFreqSign μ : ℂ) * (deningerFreqSign μ : ℂ)) := by ring
    _ = -1 := by rw [Complex.I_sq, hsq]; ring

/-- **The boundary Hodge operator is unitary.** -/
theorem deningerBoundaryHodge_norm (μ : ℝ) : ‖deningerBoundaryHodge μ‖ = 1 := by
  rw [deningerBoundaryHodge, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, deningerFreqSign]
  split_ifs <;> norm_num

/-- **The boundary Hodge operator is the boundary value of the leafwise Hodge star.**  The star of
the harmonic mode is multiplication by exactly this scalar. -/
theorem deningerBoundaryHodge_eq_star (μ r : ℝ) :
    deningerCxStar (deningerMode μ r) = deningerBoundaryHodge μ • deningerMode μ r :=
  deningerMode_chirality μ r

end PoissonBoundary

end RHTower
