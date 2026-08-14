import GaloisForLFunctions.RHTower.SuzukiFlatPrimitiveFluxAssembly

/-!
# Flat Suzuki primitive flux has no independent terminal charge

The flat primitive-flux argument previously listed vanishing terminal flux as a separate
matching premise.  It is forced by the hypotheses already used in that argument.  If the value
block is superpolynomially flat, its growing `2L` coefficient still tends to zero in block norm;
the localized Gamma remainder and primitive source also tend to zero.  The defining flux equation
therefore makes the flux block norm tend to zero, so any terminal strong limit is necessarily the
zero vector.

This file proves the scalar norm-sequence core.  The first theorem extracts the load-bearing
`n * F n → 0` consequence of superpolynomial flatness.  The second theorem consumes the exact
localized flux upper bound.  No self-adjointness, normality, group bound, spectral assumption, or
Riemann-hypothesis premise occurs.
-/

open Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Multiplication by the linearly growing terminal coefficient still kills a
superpolynomially flat nonnegative block-norm sequence. -/
theorem tendsto_natCast_mul_of_superpolynomiallyFlat
    {q : ℕ → ℝ} (hq0 : ∀ n, 0 ≤ q n) (hflat : SuperpolynomiallyFlat q) :
    Tendsto (fun n : ℕ => (n : ℝ) * q n) atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := hflat 2
  have hupper : ∀ᶠ n : ℕ in atTop, (n : ℝ) * q n ≤ M / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hqn := hM n hn
    calc
      (n : ℝ) * q n ≤ (n : ℝ) * (M / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hqn hn0.le
      _ = M / n := by field_simp
  have hlower : ∀ n : ℕ, 0 ≤ (n : ℝ) * q n :=
    fun n => mul_nonneg (by positivity) (hq0 n)
  have htop : Tendsto (fun n : ℕ => M / (n : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))))
  exact squeeze_zero' (Filter.Eventually.of_forall hlower) hupper htop

/-- **Automatic terminal-charge law.**  Let `F` be the value block norm, `R` a localized
Gamma/envelope remainder, `G` the primitive source norm, and `Y` the flux block norm.  The exact
localized flux equation has the displayed upper-bound shape.  Superpolynomial flatness of `F`
and decay of `R,G` force `Y → 0`; zero terminal charge is a conclusion, not another premise. -/
theorem flat_flux_terminal_charge_automatic
    {F R G Y : ℕ → ℝ} {A C : ℝ}
    (hF0 : ∀ n, 0 ≤ F n) (hY0 : ∀ n, 0 ≤ Y n)
    (hFflat : SuperpolynomiallyFlat F)
    (hR : Tendsto R atTop (nhds 0)) (hG : Tendsto G atTop (nhds 0))
    (hflux : ∀ᶠ n : ℕ in atTop,
      Y n ≤ A * ((n : ℝ) * F n) + C * R n + G n) :
    Tendsto Y atTop (nhds 0) := by
  have hF := tendsto_natCast_mul_of_superpolynomiallyFlat hF0 hFflat
  have hupper : Tendsto
      (fun n : ℕ => A * ((n : ℝ) * F n) + C * R n + G n) atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds.mul hF).add (tendsto_const_nhds.mul hR)).add hG
  exact squeeze_zero' (Filter.Eventually.of_forall hY0) hflux hupper

/-! ## One-sided physical-root indicial coefficients -/

/-- Leading coefficient of Suzuki's one-sided physical-endpoint logarithmic jump on a
`beta * L⁻ᵗᵃᵘ` profile.  The opposite orientation is the literal zero extension. -/
noncomputable def physicalEndpointIndicialCoefficient (tau beta : ℝ) : ℝ :=
  ((1 - 2 * tau) / (1 - tau)) * beta

/-- Away from the borderline `tau = 1`, a nonzero physical-endpoint conormal coefficient can
annihilate its leading jump only at the unique half-log root `tau = 1/2`. -/
theorem physicalEndpointIndicialCoefficient_eq_zero_iff
    {tau beta : ℝ} (htau : tau ≠ 1) (hbeta : beta ≠ 0) :
    physicalEndpointIndicialCoefficient tau beta = 0 ↔ tau = 1 / 2 := by
  constructor
  · intro h
    rw [physicalEndpointIndicialCoefficient] at h
    have hfrac : (1 - 2 * tau) / (1 - tau) = 0 :=
      (mul_eq_zero.mp h).resolve_right hbeta
    have hden : 1 - tau ≠ 0 := sub_ne_zero.mpr (Ne.symm htau)
    field_simp [hden] at hfrac
    linarith
  · intro h
    rw [h, physicalEndpointIndicialCoefficient]
    norm_num

/-- At the borderline physical dipole `beta / L`, the uncancelled logarithmic output has
coefficient `-beta`. -/
def physicalEndpointDipoleLogCoefficient (beta : ℝ) : ℝ := -beta

/-- A bounded literal physical-endpoint source therefore admits no nonzero one-sided
`1 / log` dipole coefficient. -/
theorem physicalEndpointDipoleLogCoefficient_eq_zero_iff (beta : ℝ) :
    physicalEndpointDipoleLogCoefficient beta = 0 ↔ beta = 0 := by
  simp [physicalEndpointDipoleLogCoefficient]

end RHTower
