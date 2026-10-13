import GaloisForLFunctions.RHTower.XiCosineShiftDefectPersistence
import GaloisForLFunctions.RHTower.DeBruijnPolynomialGaussianAverage
import GaloisForLFunctions.RHTower.DeBruijnNewmanConstant
import GaloisForLFunctions.RHTower.KiKimLeeFiniteness

/-!
# Persistence of an off-line pair under the de Bruijn–Newman flow

Let `H_t(z) = ∫ Φ(x) e^{tx²} e^{izx} dx` (`riemannHeat`).  For `t > 0` it is the Gaussian average
`H_t(z) = ∫ g_t(u) Ξ(z − iu) du` with `g_t` the centred Gaussian density of variance `2t`
(`riemannHeat_eq_integral_gaussian_xi`).

**Theorem** (`riemannHeat_exists_nonreal_zero_of_offline_zero`).  Let `ρ = ½ + b + iγ` (`b > 0`) be
a zero of `ξ`, so `Ξ = q·g` with `q(z) = (z − γ)² + b²` and `g = xiPairQuotient γ b` entire.  Let
`0 < 2t < b²`, `c = √(b² − 2t)` and `z₀ = γ − ci`.  If on the circle `|z − z₀| = c/2` the quotient
does not vanish and

  `∫ g_t(u) |q(z − iu)| |g(z − iu) − g(z)| du < (3c²/4) |g(z)|`,

then `H_t` has a zero `z` with `|z − z₀| < c/2`; in particular `Im z < −c/2`.  Consequently
(`lt_newmanConstant_of_offline_zero`) the de Bruijn–Newman constant satisfies `Λ₊ > t`.

So an off-line pair of depth `b` whose cofactor varies little over the Gaussian scale `√(2t)`
survives the flow up to the de Bruijn time `t ≈ b²/2`: the pair `γ ∓ ib` moves to `γ ∓ ic` with
`c² = b² − 2t`, which is the de Bruijn barrier `(Im z)² = b² − 2t`.  For such pairs
`Λ₊ ≥ (b² − c²)/2` is sharp against de Bruijn's bound `Λ₊ ≤ b²/2`.

**Proof.**  The Gaussian moments give `∫ g_t(u) q(z − iu) du = (z − γ)² + c²`
(`integral_gaussDensity_mul_quadratic`), so

  `H_t(z) − g(z)((z − γ)² + c²) = ∫ g_t(u) q(z − iu) (g(z − iu) − g(z)) du`.

On the circle `|(z − γ)² + c²| = |z − z₀||z − z̄₀| ≥ 3c²/4`, and Rouché
(`exists_zero_mem_ball_of_norm_sub_lt`) against `g·((z − γ)² + c²)`, which vanishes at `z₀`, gives
the zero.  This is the Gaussian analogue of the cosine-shift persistence law
(`cosineShift_exists_nonreal_zero_of_quadratic_factor`).
-/

open Complex MeasureTheory Metric Set

namespace RHTower.DeBruijn

noncomputable section

/-! ## Gaussian moments of a quadratic -/

theorem integrable_gaussDensity_mul_ofReal_pow {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * (u : ℂ) ^ k) :=
  ((integrable_gaussDensity_mul_pow ht k).ofReal).congr
    (Filter.Eventually.of_forall fun u => by push_cast; rfl)

theorem integral_gaussDensity_mul_quadratic {t : ℝ} (ht : 0 < t) (γ b : ℝ) (z : ℂ) :
    ∫ u : ℝ, (gaussDensity t u : ℂ) * (((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2)
      = (z - γ) ^ 2 + ((b ^ 2 - 2 * t : ℝ) : ℂ) := by
  have m0 : ∫ u : ℝ, (gaussDensity t u : ℂ) * (u : ℂ) ^ 0 = 1 := by
    rw [integral_gaussDensity_mul_ofReal_pow]
    have := integral_gaussDensity_mul_pow_even ht 0
    norm_num at this ⊢
    exact_mod_cast this
  have m1 : ∫ u : ℝ, (gaussDensity t u : ℂ) * (u : ℂ) ^ 1 = 0 := by
    rw [integral_gaussDensity_mul_ofReal_pow]
    have := integral_gaussDensity_mul_pow_odd t 0
    norm_num at this ⊢
    exact_mod_cast this
  have m2 : ∫ u : ℝ, (gaussDensity t u : ℂ) * (u : ℂ) ^ 2 = ((2 * t : ℝ) : ℂ) := by
    rw [integral_gaussDensity_mul_ofReal_pow]
    have := integral_gaussDensity_mul_pow_even ht 1
    norm_num at this ⊢
    rw [this]; push_cast; ring
  have hpt : ∀ u : ℝ, (gaussDensity t u : ℂ) * (((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2)
      = ((z - γ) ^ 2 + (b : ℂ) ^ 2) * ((gaussDensity t u : ℂ) * (u : ℂ) ^ 0)
        + (-2 * I * (z - γ)) * ((gaussDensity t u : ℂ) * (u : ℂ) ^ 1)
        + (-1) * ((gaussDensity t u : ℂ) * (u : ℂ) ^ 2) := by
    intro u
    ring_nf
    rw [I_sq]
    ring
  simp_rw [hpt]
  have I0 := (integrable_gaussDensity_mul_ofReal_pow ht 0).const_mul ((z - γ) ^ 2 + (b : ℂ) ^ 2)
  have I1 := (integrable_gaussDensity_mul_ofReal_pow ht 1).const_mul (-2 * I * (z - γ))
  have I2 := (integrable_gaussDensity_mul_ofReal_pow ht 2).const_mul (-1 : ℂ)
  rw [integral_add (f := fun u : ℝ => ((z - γ) ^ 2 + (b : ℂ) ^ 2) * ((gaussDensity t u : ℂ) * (u : ℂ) ^ 0)
      + (-2 * I * (z - γ)) * ((gaussDensity t u : ℂ) * (u : ℂ) ^ 1))
      (g := fun u : ℝ => (-1 : ℂ) * ((gaussDensity t u : ℂ) * (u : ℂ) ^ 2)) (I0.add I1) I2,
    integral_add I0 I1, integral_const_mul, integral_const_mul, integral_const_mul, m0, m1, m2]
  push_cast
  ring


theorem integrable_gaussDensity_mul_quadratic {t : ℝ} (ht : 0 < t) (γ b : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * (((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2)) := by
  have I0 := (integrable_gaussDensity_mul_ofReal_pow ht 0).const_mul ((z - γ) ^ 2 + (b : ℂ) ^ 2)
  have I1 := (integrable_gaussDensity_mul_ofReal_pow ht 1).const_mul (-2 * I * (z - γ))
  have I2 := (integrable_gaussDensity_mul_ofReal_pow ht 2).const_mul (-1 : ℂ)
  refine ((I0.add I1).add I2).congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply]
  ring_nf
  rw [I_sq]
  ring

/-! ## The persistence law -/

/-- **Persistence of a defect pair under a Gaussian flow.**  If `f = q·g` with
`q(z) = (z − γ)² + b²`, `A(z) = ∫ g_t(u) f(z − iu) du` and the cofactor `g` has small Gaussian
variation on the circle `|z − z₀| = c/2`, `z₀ = γ − ci`, `c = √(b² − 2t)`, then `A` vanishes within
`c/2` of `z₀`. -/
theorem gaussFlow_exists_nonreal_zero_of_quadratic_factor {f g A : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hA : Differentiable ℂ A) {γ b t : ℝ} (ht : 0 < t)
    (htb : 2 * t < b ^ 2) (hfac : ∀ z, f z = ((z - γ) ^ 2 + (b : ℂ) ^ 2) * g z)
    (hAeq : ∀ z, A z = ∫ u : ℝ, (gaussDensity t u : ℂ) * f (z - I * u))
    (hint : ∀ z, Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * f (z - I * u)))
    (hsph : ∀ z ∈ sphere ((γ : ℂ) - (Real.sqrt (b ^ 2 - 2 * t) : ℂ) * I)
        (Real.sqrt (b ^ 2 - 2 * t) / 2),
      g z ≠ 0 ∧ ∫ u : ℝ, gaussDensity t u * ‖((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2‖
          * ‖g (z - I * u) - g z‖ < 3 * (b ^ 2 - 2 * t) / 4 * ‖g z‖) :
    ∃ z : ℂ, A z = 0 ∧ z.im < -(Real.sqrt (b ^ 2 - 2 * t) / 2) ∧
      |z.re - γ| < Real.sqrt (b ^ 2 - 2 * t) / 2 := by
  set c : ℝ := Real.sqrt (b ^ 2 - 2 * t) with hcdef
  have hbt : 0 < b ^ 2 - 2 * t := by linarith
  have hc : 0 < c := Real.sqrt_pos.mpr hbt
  have hc2 : c ^ 2 = b ^ 2 - 2 * t := Real.sq_sqrt hbt.le
  set z₀ : ℂ := (γ : ℂ) - (c : ℂ) * I with hz₀
  set F : ℂ → ℂ := fun z => g z * ((z - γ) ^ 2 + (c : ℂ) ^ 2) with hFdef
  have hFd : Differentiable ℂ F := hg.mul (by fun_prop)
  have hF0 : F z₀ = 0 := by
    simp only [hFdef, hz₀]
    have : ((γ : ℂ) - (c : ℂ) * I - γ) ^ 2 + (c : ℂ) ^ 2 = 0 := by
      ring_nf; rw [I_sq]; ring
    rw [this, mul_zero]
  have hcC : ((b ^ 2 - 2 * t : ℝ) : ℂ) = (c : ℂ) ^ 2 := by
    rw [← hc2]; push_cast; ring
  -- the comparison identity
  have hid : ∀ z, A z - F z = ∫ u : ℝ, (gaussDensity t u : ℂ) *
      ((((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2) * (g (z - I * u) - g z)) := by
    intro z
    have hq := integral_gaussDensity_mul_quadratic ht γ b z
    rw [hcC] at hq
    have hFz : F z = ∫ u : ℝ, (gaussDensity t u : ℂ) * (((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2)
        * g z := by
      rw [integral_mul_const, hq]; simp only [hFdef]; ring
    rw [hAeq z, hFz, ← integral_sub (hint z)
      ((integrable_gaussDensity_mul_quadratic ht γ b z).mul_const (g z))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hfac]
    ring
  have hbound : ∀ z ∈ sphere z₀ (c / 2), ‖A z - F z‖ < ‖F z‖ := by
    intro z hz
    obtain ⟨hgz, hvar⟩ := hsph z hz
    have hgpos : 0 < ‖g z‖ := norm_pos_iff.mpr hgz
    have hzz : ‖z - z₀‖ = c / 2 := by simpa using hz
    have hnorm : ∀ u : ℝ, ‖(gaussDensity t u : ℂ) *
        ((((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2) * (g (z - I * u) - g z))‖
        = gaussDensity t u * ‖((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2‖ * ‖g (z - I * u) - g z‖ := by
      intro u
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (gaussDensity_pos ht u)]
      ring
    have hle : ‖A z - F z‖ ≤ ∫ u : ℝ, gaussDensity t u * ‖((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2‖
        * ‖g (z - I * u) - g z‖ := by
      rw [hid z]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      exact integral_congr_ae (Filter.Eventually.of_forall hnorm)
    have hP : 3 * c ^ 2 / 4 ≤ ‖(z - γ) ^ 2 + (c : ℂ) ^ 2‖ := by
      have hfac2 : (z - γ) ^ 2 + (c : ℂ) ^ 2 = (z - z₀) * (z - ((γ : ℂ) + c * I)) := by
        simp only [hz₀]; ring_nf; rw [I_sq]; ring
      have hfar : 3 * c / 2 ≤ ‖z - ((γ : ℂ) + c * I)‖ := by
        have e : z - ((γ : ℂ) + c * I) = (z - z₀) - (2 * c : ℝ) * I := by
          simp only [hz₀]; push_cast; ring
        rw [e]
        have h2 : ‖((2 * c : ℝ) : ℂ) * I‖ = 2 * c := by
          rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith)]
        have := norm_sub_norm_le (((2 * c : ℝ) : ℂ) * I) (z - z₀)
        rw [h2, hzz, norm_sub_rev] at this
        linarith
      rw [hfac2, norm_mul, hzz]
      nlinarith
    have hFz : ‖F z‖ = ‖g z‖ * ‖(z - γ) ^ 2 + (c : ℂ) ^ 2‖ := by
      simp only [hFdef, norm_mul]
    rw [hFz]
    calc ‖A z - F z‖ < 3 * (b ^ 2 - 2 * t) / 4 * ‖g z‖ := hle.trans_lt hvar
      _ = ‖g z‖ * (3 * c ^ 2 / 4) := by rw [hc2]; ring
      _ ≤ ‖g z‖ * ‖(z - γ) ^ 2 + (c : ℂ) ^ 2‖ := mul_le_mul_of_nonneg_left hP hgpos.le
  obtain ⟨z, hzball, hAz⟩ := exists_zero_mem_ball_of_norm_sub_lt hFd hA (by linarith) hbound
    (mem_ball_self (by linarith)) hF0
  have hzb : ‖z - z₀‖ < c / 2 := by simpa [dist_eq_norm] using hzball
  refine ⟨z, hAz, ?_, ?_⟩
  · have him : |(z - z₀).im| ≤ ‖z - z₀‖ := abs_im_le_norm _
    have hz0im : z₀.im = -c := by simp [hz₀]
    have : (z - z₀).im = z.im + c := by rw [sub_im, hz0im]; ring
    rw [this] at him
    have := (abs_le.mp him).2
    linarith
  · have hre : |(z - z₀).re| ≤ ‖z - z₀‖ := abs_re_le_norm _
    have hz0re : z₀.re = γ := by simp [hz₀]
    rw [sub_re, hz0re] at hre
    linarith

/-! ## The persistence law for the de Bruijn–Newman flow -/

/-- `H_t(z) = ∫ g_t(u) Ξ(z − iu) du` for `t > 0`. -/
theorem riemannHeat_eq_integral_gaussian_XiC {t : ℝ} (ht : 0 < t) (z : ℂ) :
    riemannHeat t z = ∫ u : ℝ, (gaussDensity t u : ℂ) * XiC (z - I * u) := by
  rw [riemannHeat_eq_integral_gaussian_xi ht]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [XiC]
  congr 2
  ring_nf
  rw [I_sq]
  ring

theorem integrable_gaussDensity_mul_XiC {t : ℝ} (ht : 0 < t) (z : ℂ) :
    Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * XiC (z - I * u)) := by
  refine (integrable_gaussDensity_mul_xi ht z).congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [XiC]
  congr 2
  ring_nf
  rw [I_sq]
  ring

/-- **Persistence of an off-line pair of `Ξ` under the de Bruijn–Newman flow.**  If
`Ξ(γ − ib) = 0` (`ρ = ½ + b + iγ` is a zero of `ξ`), `0 < 2t < b²`, and the cofactor
`g = xiPairQuotient γ b` satisfies the Gaussian variation bound on the circle `|z − z₀| = c/2`,
`z₀ = γ − ci`, `c = √(b² − 2t)`, then `H_t` has a zero `z` with `Im z < −c/2` and `|Re z − γ| < c/2`. -/
theorem riemannHeat_exists_nonreal_zero_of_offline_zero {γ b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (htb : 2 * t < b ^ 2) (hz : XiC ((γ : ℂ) - b * I) = 0)
    (hsph : ∀ z ∈ sphere ((γ : ℂ) - (Real.sqrt (b ^ 2 - 2 * t) : ℂ) * I)
        (Real.sqrt (b ^ 2 - 2 * t) / 2),
      xiPairQuotient γ b z ≠ 0 ∧ ∫ u : ℝ, gaussDensity t u * ‖((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2‖
          * ‖xiPairQuotient γ b (z - I * u) - xiPairQuotient γ b z‖
          < 3 * (b ^ 2 - 2 * t) / 4 * ‖xiPairQuotient γ b z‖) :
    ∃ z : ℂ, riemannHeat t z = 0 ∧ z.im < -(Real.sqrt (b ^ 2 - 2 * t) / 2) ∧
      |z.re - γ| < Real.sqrt (b ^ 2 - 2 * t) / 2 :=
  gaussFlow_exists_nonreal_zero_of_quadratic_factor (differentiable_xiPairQuotient γ b)
    (differentiable_riemannHeat ht.le) ht htb (XiC_eq_quadratic_mul_xiPairQuotient hb hz)
    (riemannHeat_eq_integral_gaussian_XiC ht) (integrable_gaussDensity_mul_XiC ht) hsph

/-- **De Bruijn–Newman lower bound from a persistent off-line pair.**  Under the hypotheses of
`riemannHeat_exists_nonreal_zero_of_offline_zero`, `t < Λ₊`. -/
theorem lt_newmanConstant_of_offline_zero {γ b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (htb : 2 * t < b ^ 2) (hz : XiC ((γ : ℂ) - b * I) = 0)
    (hsph : ∀ z ∈ sphere ((γ : ℂ) - (Real.sqrt (b ^ 2 - 2 * t) : ℂ) * I)
        (Real.sqrt (b ^ 2 - 2 * t) / 2),
      xiPairQuotient γ b z ≠ 0 ∧ ∫ u : ℝ, gaussDensity t u * ‖((z - I * u) - γ) ^ 2 + (b : ℂ) ^ 2‖
          * ‖xiPairQuotient γ b (z - I * u) - xiPairQuotient γ b z‖
          < 3 * (b ^ 2 - 2 * t) / 4 * ‖xiPairQuotient γ b z‖) :
    t < newmanConstant := by
  obtain ⟨z, hz0, him, -⟩ := riemannHeat_exists_nonreal_zero_of_offline_zero hb ht htb hz hsph
  by_contra h
  push Not at h
  have hmem := (mem_realRootedTimes_iff ht.le).mpr h
  have h0 := hmem.2 z hz0
  have hc : 0 < Real.sqrt (b ^ 2 - 2 * t) := Real.sqrt_pos.mpr (by linarith)
  linarith

end

end RHTower.DeBruijn
