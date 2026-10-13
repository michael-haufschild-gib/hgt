import GaloisForLFunctions.RHTower.DeBruijnDefectPairPersistence

/-!
# Persistence of zero clusters under the de Bruijn–Newman flow

Let `H_t(z) = ∫ g_t(u) Ξ(z − iu) du` (`riemannHeat_eq_integral_gaussian_XiC`) and, for a complex
polynomial `P`, let `(e^{−tD²}P)(z) = Σ_m (−t)^m/m! P^{(2m)}(z)` (`polyHeat`), which is the same
Gaussian average `∫ g_t(u) P(z − iu) du` (`integral_gaussDensity_mul_eval_sub`).

**Theorem** (`riemannHeat_exists_zero_of_polynomial_factor`).  Suppose `Ξ = P·g` with `g` entire.  If
`e^{−tD²}P` vanishes at `z₀` and on the circle `|z − z₀| = r`

  `∫ g_t(u) |P(z − iu)| |g(z − iu) − g(z)| du < |g(z)| |(e^{−tD²}P)(z)|`,

then `H_t` vanishes in the disk `|z − z₀| < r`.  If the disk lies off the real axis, `t < Λ₊`
(`lt_newmanConstant_of_polynomial_factor`).

So the zeros of `H_t` near a cluster of zeros of `Ξ` follow the polynomial heat flow of the cluster,
as long as the cofactor varies little on the Gaussian scale `√(2t)`.  The persistence time of a
non-real zero of the cluster is the time at which `e^{−tD²}P` loses that non-real zero.  This is the
cluster form of the pair law (`lt_newmanConstant_of_offline_zero`, `P = (z − γ)² + b²`).

**Mixed triple** (`lt_newmanConstant_of_mixed_triple`).  A critical zero at the ordinate `γ` of an
off-line pair `γ ∓ ib` gives `P = (z − γ)((z − γ)² + b²)`, and `e^{−tD²}P = (z − γ)((z − γ)² + b² − 6t)`
(`polyHeat_mixedTriplePoly`).  The pair now survives up to `t ≈ b²/6`, against `b²/2` for an isolated
pair: the critical zero at the same ordinate pulls the pair to the axis three times faster.

**Proof.**  `H_t(z) − g(z)(e^{−tD²}P)(z) = ∫ g_t(u) P(z − iu)(g(z − iu) − g(z)) du`, and Rouché
(`exists_zero_mem_ball_of_norm_sub_lt`) against `g·e^{−tD²}P`.
-/

open Complex MeasureTheory Metric Set Polynomial

namespace RHTower.DeBruijn

noncomputable section

/-- The polynomial heat flow `(e^{−tD²}P)(z) = Σ_m (−t)^m/m! P^{(2m)}(z)`. -/
def polyHeat (t : ℝ) (P : ℂ[X]) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (P.natDegree + 1),
    ((-t : ℂ) ^ m / (m.factorial : ℂ)) * (derivative^[2 * m] P).eval z

theorem differentiable_polyHeat (t : ℝ) (P : ℂ[X]) : Differentiable ℂ (polyHeat t P) := by
  unfold polyHeat
  fun_prop

theorem integrable_gaussDensity_mul_eval_sub {t : ℝ} (ht : 0 < t) (P : ℂ[X]) (z : ℂ) :
    Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * P.eval (z - I * u)) := by
  have hexp : ∀ u : ℝ, (gaussDensity t u : ℂ) * P.eval (z - I * u) =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        (hasseDeriv j P).eval z * (-I) ^ j * ((gaussDensity t u : ℂ) * (u : ℂ) ^ j) := by
    intro u
    rw [eval_sub_eq_sum_taylor, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show -(I * (u : ℂ)) = (-I) * u by ring, mul_pow]
    ring
  simp_rw [hexp]
  exact integrable_finsetSum _ fun j _ =>
    (integrable_gaussDensity_mul_ofReal_pow ht j).const_mul _

/-- **Rouché transfer of the polynomial heat flow.**  Let `A(z) = ∫ g_t(u) P(z − iu) g(z − iu) du`.
If `e^{−tD²}P` vanishes at `z₀` and on the circle `|z − z₀| = r` the cofactor `g` has Gaussian
variation below `|g(z)| |(e^{−tD²}P)(z)|`, then `A` vanishes in the disk `|z − z₀| < r`. -/
theorem gaussFlow_exists_zero_of_polynomial_factor {g A : ℂ → ℂ} (P : ℂ[X])
    (hg : Differentiable ℂ g) (hA : Differentiable ℂ A) {t r : ℝ} (ht : 0 < t) (hr : 0 < r)
    {z₀ : ℂ} (hP0 : polyHeat t P z₀ = 0)
    (hAeq : ∀ z, A z = ∫ u : ℝ, (gaussDensity t u : ℂ) * (P.eval (z - I * u) * g (z - I * u)))
    (hint : ∀ z, Integrable (fun u : ℝ =>
      (gaussDensity t u : ℂ) * (P.eval (z - I * u) * g (z - I * u))))
    (hsph : ∀ z ∈ sphere z₀ r, ∫ u : ℝ, gaussDensity t u * ‖P.eval (z - I * u)‖ *
        ‖g (z - I * u) - g z‖ < ‖g z‖ * ‖polyHeat t P z‖) :
    ∃ z ∈ ball z₀ r, A z = 0 := by
  set F : ℂ → ℂ := fun z => g z * polyHeat t P z with hFdef
  have hFd : Differentiable ℂ F := hg.mul (differentiable_polyHeat t P)
  have hF0 : F z₀ = 0 := by simp only [hFdef, hP0, mul_zero]
  have hid : ∀ z, A z - F z = ∫ u : ℝ, (gaussDensity t u : ℂ) *
      (P.eval (z - I * u) * (g (z - I * u) - g z)) := by
    intro z
    have hq := integral_gaussDensity_mul_eval_sub ht P z
    have hFz : F z = ∫ u : ℝ, (gaussDensity t u : ℂ) * P.eval (z - I * u) * g z := by
      rw [integral_mul_const, hq]; simp only [hFdef, polyHeat]; ring
    rw [hAeq z, hFz, ← integral_sub (hint z)
      ((integrable_gaussDensity_mul_eval_sub ht P z).mul_const (g z))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    ring
  have hbound : ∀ z ∈ sphere z₀ r, ‖A z - F z‖ < ‖F z‖ := by
    intro z hz
    have hnorm : ∀ u : ℝ, ‖(gaussDensity t u : ℂ) * (P.eval (z - I * u) * (g (z - I * u) - g z))‖
        = gaussDensity t u * ‖P.eval (z - I * u)‖ * ‖g (z - I * u) - g z‖ := by
      intro u
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (gaussDensity_pos ht u)]
      ring
    have hle : ‖A z - F z‖ ≤ ∫ u : ℝ, gaussDensity t u * ‖P.eval (z - I * u)‖ *
        ‖g (z - I * u) - g z‖ := by
      rw [hid z]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      exact integral_congr_ae (Filter.Eventually.of_forall hnorm)
    have hFz : ‖F z‖ = ‖g z‖ * ‖polyHeat t P z‖ := by simp only [hFdef, norm_mul]
    rw [hFz]
    exact hle.trans_lt (hsph z hz)
  exact exists_zero_mem_ball_of_norm_sub_lt hFd hA hr hbound (mem_ball_self hr) hF0

/-- **Cluster persistence for the de Bruijn–Newman flow.**  If `Ξ = P·g` with `g` entire, `t > 0`,
`e^{−tD²}P` vanishes at `z₀`, and the Gaussian variation of `g` on `|z − z₀| = r` is below
`|g(z)||(e^{−tD²}P)(z)|`, then `H_t` vanishes in the disk `|z − z₀| < r`. -/
theorem riemannHeat_exists_zero_of_polynomial_factor {g : ℂ → ℂ} (P : ℂ[X])
    (hg : Differentiable ℂ g) (hfac : ∀ z, XiC z = P.eval z * g z) {t r : ℝ} (ht : 0 < t)
    (hr : 0 < r) {z₀ : ℂ} (hP0 : polyHeat t P z₀ = 0)
    (hsph : ∀ z ∈ sphere z₀ r, ∫ u : ℝ, gaussDensity t u * ‖P.eval (z - I * u)‖ *
        ‖g (z - I * u) - g z‖ < ‖g z‖ * ‖polyHeat t P z‖) :
    ∃ z ∈ ball z₀ r, riemannHeat t z = 0 := by
  refine gaussFlow_exists_zero_of_polynomial_factor P hg (differentiable_riemannHeat ht.le) ht hr
    hP0 (fun z => ?_) (fun z => ?_) hsph
  · rw [riemannHeat_eq_integral_gaussian_XiC ht]
    simp_rw [hfac]
  · simp_rw [← hfac]
    exact integrable_gaussDensity_mul_XiC ht z

/-- **Newman bound from a persistent cluster.**  If moreover the disk `|z − z₀| < r` lies off the
real axis (`r ≤ |Im z₀|`), then `t < Λ₊`. -/
theorem lt_newmanConstant_of_polynomial_factor {g : ℂ → ℂ} (P : ℂ[X])
    (hg : Differentiable ℂ g) (hfac : ∀ z, XiC z = P.eval z * g z) {t r : ℝ} (ht : 0 < t)
    (hr : 0 < r) {z₀ : ℂ} (hP0 : polyHeat t P z₀ = 0) (hoff : r ≤ |z₀.im|)
    (hsph : ∀ z ∈ sphere z₀ r, ∫ u : ℝ, gaussDensity t u * ‖P.eval (z - I * u)‖ *
        ‖g (z - I * u) - g z‖ < ‖g z‖ * ‖polyHeat t P z‖) :
    t < newmanConstant := by
  obtain ⟨z, hz, hz0⟩ := riemannHeat_exists_zero_of_polynomial_factor P hg hfac ht hr hP0 hsph
  by_contra h
  push Not at h
  have hmem := (mem_realRootedTimes_iff ht.le).mpr h
  have him := hmem.2 z hz0
  have hzb : ‖z - z₀‖ < r := by simpa [dist_eq_norm] using hz
  have h1 : |(z - z₀).im| ≤ ‖z - z₀‖ := abs_im_le_norm _
  rw [sub_im, him, zero_sub, abs_neg] at h1
  linarith


/-- The cubic of a mixed triple, a critical zero at `γ` and an off-line pair `γ ∓ ib`. -/
def mixedTriplePoly (γ b : ℝ) : ℂ[X] := (X - C (γ : ℂ)) * ((X - C (γ : ℂ)) ^ 2 + C ((b : ℂ) ^ 2))

theorem eval_mixedTriplePoly (γ b : ℝ) (z : ℂ) :
    (mixedTriplePoly γ b).eval z = (z - γ) * ((z - γ) ^ 2 + (b : ℂ) ^ 2) := by
  simp [mixedTriplePoly]

/-- `e^{−tD²}` moves the pair of a mixed triple to depth `√(b² − 6t)`:
`(e^{−tD²}P)(z) = (z − γ)((z − γ)² + b² − 6t)`. -/
theorem polyHeat_mixedTriplePoly {t : ℝ} (ht : 0 < t) (γ b : ℝ) (z : ℂ) :
    polyHeat t (mixedTriplePoly γ b) z = (z - γ) * ((z - γ) ^ 2 + ((b ^ 2 - 6 * t : ℝ) : ℂ)) := by
  rw [polyHeat, ← integral_gaussDensity_mul_eval_sub ht]
  simp_rw [eval_mixedTriplePoly]
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
  have m3 : ∫ u : ℝ, (gaussDensity t u : ℂ) * (u : ℂ) ^ 3 = 0 := by
    rw [integral_gaussDensity_mul_ofReal_pow]
    have := integral_gaussDensity_mul_pow_odd t 1
    norm_num at this ⊢
    exact_mod_cast this
  set w := z - γ with hw
  set c : ℕ → ℂ := fun j => if j = 0 then w ^ 3 + (b : ℂ) ^ 2 * w else if j = 1 then
    -3 * I * w ^ 2 - I * (b : ℂ) ^ 2 else if j = 2 then -3 * w else I with hc
  have hpt : ∀ u : ℝ, (gaussDensity t u : ℂ) * ((z - I * u - γ) * ((z - I * u - γ) ^ 2 + (b : ℂ) ^ 2))
      = ∑ j ∈ Finset.range 4, c j * ((gaussDensity t u : ℂ) * (u : ℂ) ^ j) := by
    intro u
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc, hw]
    norm_num
    ring_nf
    rw [I_sq, show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun j _ => (integrable_gaussDensity_mul_ofReal_pow ht j).const_mul _)]
  simp_rw [integral_const_mul]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, m0, m1, m2, m3, hc]
  norm_num
  ring

/-- The cofactor of a mixed triple: `Ξ = (z − γ)((z − γ)² + b²) · mixedTripleQuotient γ b`. -/
def mixedTripleQuotient (γ b : ℝ) : ℂ → ℂ := dslope (xiPairQuotient γ b) γ

theorem differentiable_mixedTripleQuotient (γ b : ℝ) :
    Differentiable ℂ (mixedTripleQuotient γ b) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
    (differentiable_xiPairQuotient γ b).differentiableOn

theorem XiC_eq_mixedTriple_mul {γ b : ℝ} (hb : 0 < b) (hz : XiC ((γ : ℂ) - b * I) = 0)
    (hγ : XiC (γ : ℂ) = 0) (z : ℂ) :
    XiC z = (mixedTriplePoly γ b).eval z * mixedTripleQuotient γ b z := by
  have hq := XiC_eq_quadratic_mul_xiPairQuotient hb hz
  have hg0 : xiPairQuotient γ b γ = 0 := by
    have h := hq γ
    rw [hγ, sub_self, zero_pow two_ne_zero, zero_add] at h
    have hb2 : (b : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hb.ne')
    exact (mul_eq_zero.mp h.symm).resolve_left hb2
  have e := sub_smul_dslope_of_zero hg0 z
  rw [smul_eq_mul] at e
  rw [hq z, eval_mixedTriplePoly, mixedTripleQuotient, ← e]
  ring

/-- **Persistence of a mixed triple.**  Let `γ` be a critical ordinate (`Ξ(γ) = 0`) carrying an
off-line pair `γ ∓ ib` (`Ξ(γ − ib) = 0`), `0 < 6t < b²`, `c = √(b² − 6t)`.  If the cofactor varies by
less than `(3c³/8)|g(z)|` in the Gaussian sense on `|z − (γ − ci)| = c/2`, then `t < Λ₊`.  Under
`e^{−tD²}` the cubic becomes `(z − γ)((z − γ)² + b² − 6t)`, so an isolated mixed triple survives the
de Bruijn–Newman flow up to `t ≈ b²/6`. -/
theorem lt_newmanConstant_of_mixed_triple {γ b t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (h6 : 6 * t < b ^ 2) (hz : XiC ((γ : ℂ) - b * I) = 0) (hγ : XiC (γ : ℂ) = 0)
    (hsph : ∀ z ∈ sphere ((γ : ℂ) - (Real.sqrt (b ^ 2 - 6 * t) : ℂ) * I)
        (Real.sqrt (b ^ 2 - 6 * t) / 2),
      ∫ u : ℝ, gaussDensity t u * ‖(mixedTriplePoly γ b).eval (z - I * u)‖ *
          ‖mixedTripleQuotient γ b (z - I * u) - mixedTripleQuotient γ b z‖
        < 3 * Real.sqrt (b ^ 2 - 6 * t) ^ 3 / 8 * ‖mixedTripleQuotient γ b z‖) :
    t < newmanConstant := by
  set c : ℝ := Real.sqrt (b ^ 2 - 6 * t) with hcdef
  have hbt : 0 < b ^ 2 - 6 * t := by linarith
  have hc : 0 < c := Real.sqrt_pos.mpr hbt
  have hc2 : c ^ 2 = b ^ 2 - 6 * t := Real.sq_sqrt hbt.le
  set z₀ : ℂ := (γ : ℂ) - (c : ℂ) * I with hz₀
  have hcC : ((b ^ 2 - 6 * t : ℝ) : ℂ) = (c : ℂ) ^ 2 := by rw [← hc2]; push_cast; ring
  have hheat : ∀ z, polyHeat t (mixedTriplePoly γ b) z = (z - γ) * ((z - γ) ^ 2 + (c : ℂ) ^ 2) := by
    intro z; rw [polyHeat_mixedTriplePoly ht, hcC]
  refine lt_newmanConstant_of_polynomial_factor (mixedTriplePoly γ b)
    (differentiable_mixedTripleQuotient γ b) (XiC_eq_mixedTriple_mul hb hz hγ) ht
    (r := c / 2) (by linarith) (z₀ := z₀) ?_ ?_ ?_
  · rw [hheat]; simp only [hz₀]; ring_nf
    rw [show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]; ring
  · have : z₀.im = -c := by simp [hz₀]
    rw [this, abs_neg, abs_of_pos hc]; linarith
  · intro z hz
    have hzz : ‖z - z₀‖ = c / 2 := by simpa using hz
    have hnear : c / 2 ≤ ‖z - γ‖ := by
      have e : z - γ = (z - z₀) - (c : ℂ) * I := by simp only [hz₀]; ring
      rw [e]
      have h2 : ‖(c : ℂ) * I‖ = c := by
        rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      have := norm_sub_norm_le ((c : ℂ) * I) (z - z₀)
      rw [h2, hzz, norm_sub_rev] at this
      linarith
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
    have hheatn : 3 * c ^ 3 / 8 ≤ ‖polyHeat t (mixedTriplePoly γ b) z‖ := by
      rw [hheat, norm_mul]
      have := mul_le_mul hnear hP (by positivity) (norm_nonneg _)
      nlinarith
    calc _ < 3 * c ^ 3 / 8 * ‖mixedTripleQuotient γ b z‖ := hsph z hz
      _ ≤ ‖mixedTripleQuotient γ b z‖ * ‖polyHeat t (mixedTriplePoly γ b) z‖ := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left hheatn (norm_nonneg _)

end

end RHTower.DeBruijn
