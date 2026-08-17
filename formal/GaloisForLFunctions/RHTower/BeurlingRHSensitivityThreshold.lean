import GaloisForLFunctions.HTGeometry.FrullaniIntegral

/-!
# The RH-sensitivity threshold of a generalized prime measure is `σ = 1/2`

A Beurling generalized prime system adjoined to the rational primes is recorded by a positive
measure `ν` on `(1, ∞)`; in the logarithmic coordinate `t = log u` it is a positive density `g` on
`(0, ∞)`.  The zeta function of the enlarged system is

```
ζ_ν(s) = ζ(s) · exp (∫_0^∞ exp (-s t) g t dt).
```

The `σ`-mass of the adjoined measure is `∫_0^∞ exp (-σ t) g t dt`; the *reciprocal mass* is the
value at `σ = 1`, which is the total mass `∫ u⁻¹ dν(u)` of the adjoined generalized primes and also
controls the shift of the Mertens sum.

Two theorems locate exactly which scale of the prime measure the Riemann hypothesis can see.

* **Stability.**  If every `σ`-mass with `σ > 1/2` is finite, then the Euler factor
  `exp (∫ exp (-s t) g t dt)` is a *convergent* exponential on `Re s > 1/2` and therefore has no
  zeros there: the zeros of `ζ_ν` in `Re s > 1/2` are exactly the zeros of `ζ`.

* **Instability.**  For every `β ∈ (1/2, 1)` and every `γ ≠ 0` the explicit positive density
  `g(t) = 2 e^{β t}(1 - cos γ t)/t` — in the multiplicative coordinate, the adjoined generalized
  primes of density `2 u^{β-1}(1 - cos (γ log u))/log u` — has Laplace transform
  `Log(s-β-iγ) + Log(s-β+iγ) - 2 Log(s-β)`, hence Euler factor `((s-β)² + γ²)/(s-β)²`.  The
  enlarged zeta is `ζ(s)((s-β)²+γ²)/(s-β)²` and **vanishes at `β ± iγ`**, so RH fails for it, while
  its reciprocal mass is `log (1 + γ²/(1-β)²)`, which tends to `0` as `γ → 0`.

So an adjoined prime measure of *arbitrarily small* reciprocal mass can put a zeta zero anywhere in
`1/2 < Re s < 1`, whereas no adjoined measure with abscissa at most `1/2` can move a zero at all.
Every functional of a prime system that is continuous for the reciprocal (Mertens) mass is therefore
incapable of deciding the Riemann hypothesis.

All statements are unconditional.
-/

open MeasureTheory Set Filter Topology Complex GaloisForLFunctions.HTGeometry

namespace RHTower.BeurlingSensitivity

noncomputable section

/-! ## Stability: an adjoined measure with abscissa at most `1/2` moves no zero -/

/-- Absolute convergence of the Laplace transform of a nonnegative density on `Re s > 1/2`, given
finiteness of every `σ`-mass with `σ > 1/2`. -/
theorem integrableOn_cexp_mul_of_masses {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ))))
    (hmass : ∀ σ : ℝ, 1 / 2 < σ →
      IntegrableOn (fun t : ℝ => Real.exp (-σ * t) * g t) (Ioi (0 : ℝ)))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * (g t : ℂ)) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (hmass s.re hs) ?_ ?_
  · exact ((continuous_cexp_neg_mul s).aestronglyMeasurable).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hmeas)
  · filter_upwards with t
    rw [norm_mul, norm_cexp_neg_mul_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hg t)]
    simp [neg_mul]

/-- **Stability below the sensitivity threshold.**  A convergent adjoined Euler factor is nowhere
zero, so on `Re s > 1/2` the enlarged zeta vanishes exactly where `ζ` does. -/
theorem perturbed_eq_zero_iff (z : ℂ) (F : ℂ) :
    z * Complex.exp F = 0 ↔ z = 0 := by
  rw [mul_eq_zero]
  simp [Complex.exp_ne_zero]

/-! ## The adjoined density -/

/-- Logarithmic-coordinate density of the adjoined generalized primes.  In the multiplicative
coordinate `u = e^t` it is `2 u^{β-1}(1 - cos (γ log u)) / log u`. -/
def adjoinedDensity (β γ t : ℝ) : ℝ :=
  2 * Real.exp (β * t) * (1 - Real.cos (γ * t)) / t

theorem adjoinedDensity_nonneg (β γ : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ adjoinedDensity β γ t := by
  refine div_nonneg ?_ ht.le
  have h := Real.cos_le_one (γ * t)
  have h2 : (0 : ℝ) ≤ 1 - Real.cos (γ * t) := by linarith
  positivity

theorem continuousOn_adjoinedDensity (β γ : ℝ) :
    ContinuousOn (adjoinedDensity β γ) (Ioi (0 : ℝ)) := by
  unfold adjoinedDensity
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro t ht
  exact ne_of_gt ht

/-- Pointwise splitting of the weighted density into two Frullani integrands. -/
theorem cexp_mul_adjoinedDensity (β γ : ℝ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    Complex.exp (-(s * t)) * (adjoinedDensity β γ t : ℂ) =
      (Complex.exp (-((s - β) * t)) -
        Complex.exp (-((s - β - γ * I) * t))) / t +
      (Complex.exp (-((s - β) * t)) -
        Complex.exp (-((s - β + γ * I) * t))) / t := by
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have e1 : Complex.exp (-((s - β - γ * I) * t)) =
      Complex.exp (-((s - β) * t)) * Complex.exp (((γ : ℂ) * t) * I) := by
    rw [← Complex.exp_add]
    ring_nf
  have e2 : Complex.exp (-((s - β + γ * I) * t)) =
      Complex.exp (-((s - β) * t)) * Complex.exp (-(((γ : ℂ) * t) * I)) := by
    rw [← Complex.exp_add]
    ring_nf
  have ecos : Complex.exp (((γ : ℂ) * t) * I) + Complex.exp (-(((γ : ℂ) * t) * I)) =
      2 * Complex.cos ((γ : ℂ) * t) := by
    rw [Complex.exp_mul_I, show -(((γ : ℂ) * t) * I) = (-((γ : ℂ) * t)) * I by ring,
      Complex.exp_mul_I]
    simp [Complex.cos_neg, Complex.sin_neg]
    ring
  have hcancel : Complex.exp (-(s * (t : ℂ))) * Complex.exp ((β : ℂ) * (t : ℂ)) =
      Complex.exp (-((s - (β : ℂ)) * (t : ℂ))) := by
    rw [← Complex.exp_add]
    ring_nf
  have elhs : Complex.exp (-(s * t)) * (adjoinedDensity β γ t : ℂ) =
      Complex.exp (-((s - β) * t)) * (2 - 2 * Complex.cos ((γ : ℂ) * t)) / t := by
    unfold adjoinedDensity
    push_cast
    rw [show (2 : ℂ) * Complex.exp ((β : ℂ) * (t : ℂ)) *
          (1 - Complex.cos ((γ : ℂ) * (t : ℂ))) / (t : ℂ)
          = Complex.exp ((β : ℂ) * (t : ℂ)) *
            ((2 - 2 * Complex.cos ((γ : ℂ) * (t : ℂ))) / (t : ℂ)) from by ring,
      ← mul_assoc, hcancel, mul_div_assoc]
  rw [elhs, e1, e2, ← add_div]
  congr 1
  linear_combination (Complex.exp (-((s - (β : ℂ)) * (t : ℂ)))) * ecos

/-! ## The Laplace transform of the adjoined density -/

theorem re_sub_pos {β : ℝ} {s : ℂ} (hs : β < s.re) : 0 < (s - (β : ℂ)).re := by
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

theorem re_sub_sub_pos {β γ : ℝ} {s : ℂ} (hs : β < s.re) :
    0 < (s - (β : ℂ) - (γ : ℂ) * I).re := by
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  linarith

theorem re_sub_add_pos {β γ : ℝ} {s : ℂ} (hs : β < s.re) :
    0 < (s - (β : ℂ) + (γ : ℂ) * I).re := by
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im]
  linarith

/-- **Laplace transform of the adjoined generalized-prime density.** -/
theorem integral_cexp_mul_adjoinedDensity (β γ : ℝ) {s : ℂ} (hs : β < s.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (adjoinedDensity β γ t : ℂ)) =
      Complex.log (s - (β : ℂ) - (γ : ℂ) * I) + Complex.log (s - (β : ℂ) + (γ : ℂ) * I) -
        2 * Complex.log (s - (β : ℂ)) := by
  have h0 := re_sub_pos (β := β) hs
  have h1 := re_sub_sub_pos (β := β) (γ := γ) hs
  have h2 := re_sub_add_pos (β := β) (γ := γ) hs
  have hsplit :
      (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (adjoinedDensity β γ t : ℂ)) =
        ∫ t in Ioi (0 : ℝ),
          ((Complex.exp (-((s - (β : ℂ)) * t)) -
            Complex.exp (-((s - (β : ℂ) - (γ : ℂ) * I) * t))) / t +
          (Complex.exp (-((s - (β : ℂ)) * t)) -
            Complex.exp (-((s - (β : ℂ) + (γ : ℂ) * I) * t))) / t) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    exact cexp_mul_adjoinedDensity β γ s ht
  rw [hsplit, integral_add (integrableOn_frullani h0 h1) (integrableOn_frullani h0 h2),
    integral_frullani h0 h1, integral_frullani h0 h2]
  ring

/-! ## The adjoined Euler factor and the perturbed zeta -/

/-- The Euler factor contributed by the adjoined generalized primes. -/
def adjoinedFactor (β γ : ℝ) (s : ℂ) : ℂ :=
  ((s - (β : ℂ)) ^ 2 + (γ : ℂ) ^ 2) / (s - (β : ℂ)) ^ 2

/-- The adjoined Euler factor is the exponential of the Laplace transform of the adjoined density.
This is what makes the perturbed zeta the zeta function of a genuine Beurling system. -/
theorem cexp_integral_adjoinedDensity (β γ : ℝ) {s : ℂ} (hs : β < s.re) :
    Complex.exp (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (adjoinedDensity β γ t : ℂ)) =
      adjoinedFactor β γ s := by
  have h0 := re_sub_pos (β := β) hs
  have h1 := re_sub_sub_pos (β := β) (γ := γ) hs
  have h2 := re_sub_add_pos (β := β) (γ := γ) hs
  have n0 : s - (β : ℂ) ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  have n1 : s - (β : ℂ) - (γ : ℂ) * I ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have n2 : s - (β : ℂ) + (γ : ℂ) * I ≠ 0 := by
    intro h; rw [h] at h2; simp at h2
  rw [integral_cexp_mul_adjoinedDensity β γ hs, Complex.exp_sub, Complex.exp_add,
    Complex.exp_log n1, Complex.exp_log n2, two_mul, Complex.exp_add, Complex.exp_log n0,
    adjoinedFactor]
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  field_simp
  ring_nf
  rw [hI]
  ring

/-- The zeta function of the rational primes enlarged by the adjoined generalized primes. -/
def perturbedZeta (β γ : ℝ) (s : ℂ) : ℂ := riemannZeta s * adjoinedFactor β γ s

theorem perturbedZeta_eq_zeta_mul_cexp (β γ : ℝ) {s : ℂ} (hs : β < s.re) :
    perturbedZeta β γ s =
      riemannZeta s *
        Complex.exp (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (adjoinedDensity β γ t : ℂ)) := by
  rw [perturbedZeta, cexp_integral_adjoinedDensity β γ hs]

/-- **The enlarged system has a zeta zero at `β ± iγ`.** -/
theorem adjoinedFactor_eq_zero (β : ℝ) {γ : ℝ} (hγ : γ ≠ 0) :
    adjoinedFactor β γ ((β : ℂ) + (γ : ℂ) * I) = 0 := by
  have hγC : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  have hnum : (((β : ℂ) + (γ : ℂ) * I) - (β : ℂ)) ^ 2 + (γ : ℂ) ^ 2 = 0 := by
    have : (((β : ℂ) + (γ : ℂ) * I) - (β : ℂ)) = (γ : ℂ) * I := by ring
    rw [this, mul_pow, Complex.I_sq]
    ring
  rw [adjoinedFactor, hnum, zero_div]

theorem perturbedZeta_eq_zero (β : ℝ) {γ : ℝ} (hγ : γ ≠ 0) :
    perturbedZeta β γ ((β : ℂ) + (γ : ℂ) * I) = 0 := by
  rw [perturbedZeta, adjoinedFactor_eq_zero β hγ, mul_zero]

theorem re_of_zero (β γ : ℝ) : ((β : ℂ) + (γ : ℂ) * I).re = β := by
  simp

/-! ## The masses of the adjoined primes -/

/-- **The `σ`-mass of the adjoined generalized primes**, `∫ u^{-σ} dν(u)`. -/
theorem integral_cexp_mul_adjoinedDensity_ofReal (β γ : ℝ) {σ : ℝ} (hσ : β < σ) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-((σ : ℂ) * t)) * (adjoinedDensity β γ t : ℂ)) =
      ((Real.log (1 + γ ^ 2 / (σ - β) ^ 2) : ℝ) : ℂ) := by
  have hs : β < ((σ : ℂ)).re := by simpa using hσ
  rw [integral_cexp_mul_adjoinedDensity β γ hs]
  have hb : (0 : ℝ) < σ - β := by linarith
  have e0 : (σ : ℂ) - (β : ℂ) = ((σ - β : ℝ) : ℂ) := by push_cast; ring
  have hlog0 : Complex.log ((σ : ℂ) - (β : ℂ)) = ((Real.log (σ - β) : ℝ) : ℂ) := by
    rw [e0, Complex.ofReal_log hb.le]
  have harg : ((σ : ℂ) - (β : ℂ) - (γ : ℂ) * I).arg ≠ Real.pi := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    have hre := h.1
    simp [Complex.sub_re, Complex.mul_re] at hre
    linarith
  have hnorm : ‖(σ : ℂ) - (β : ℂ) - (γ : ℂ) * I‖ = Real.sqrt ((σ - β) ^ 2 + γ ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  have hconj : (starRingEnd ℂ) ((σ : ℂ) - (β : ℂ) - (γ : ℂ) * I) =
      (σ : ℂ) - (β : ℂ) + (γ : ℂ) * I := by
    simp
  have hlogpair : Complex.log ((σ : ℂ) - (β : ℂ) - (γ : ℂ) * I) +
      Complex.log ((σ : ℂ) - (β : ℂ) + (γ : ℂ) * I) =
      ((Real.log ((σ - β) ^ 2 + γ ^ 2) : ℝ) : ℂ) := by
    rw [← hconj, Complex.log_conj _ harg, Complex.add_conj, Complex.log_re, hnorm,
      Real.log_sqrt (by positivity)]
    push_cast
    ring
  have hval : Real.log ((σ - β) ^ 2 + γ ^ 2) - 2 * Real.log (σ - β) =
      Real.log (1 + γ ^ 2 / (σ - β) ^ 2) := by
    have hb2 : (0 : ℝ) < (σ - β) ^ 2 := pow_pos hb 2
    have hsum : (0 : ℝ) < (σ - β) ^ 2 + γ ^ 2 := by positivity
    rw [show (2 : ℝ) * Real.log (σ - β) = Real.log ((σ - β) ^ 2) from by
      rw [Real.log_pow]; norm_num]
    rw [← Real.log_div (ne_of_gt hsum) (ne_of_gt hb2)]
    congr 1
    field_simp
  rw [hlogpair, hlog0, ← hval]
  push_cast
  ring

theorem cexp_ofReal_mul_adjoinedDensity (β γ σ : ℝ) (t : ℝ) :
    Complex.exp (-((σ : ℂ) * t)) * (adjoinedDensity β γ t : ℂ) =
      ((Real.exp (-(σ * t)) * adjoinedDensity β γ t : ℝ) : ℂ) := by
  push_cast
  ring

/-- The real form of the `σ`-mass. -/
theorem integral_adjoinedDensity_mass (β γ : ℝ) {σ : ℝ} (hσ : β < σ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(σ * t)) * adjoinedDensity β γ t) =
      Real.log (1 + γ ^ 2 / (σ - β) ^ 2) := by
  have h := integral_cexp_mul_adjoinedDensity_ofReal β γ hσ
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t _ => cexp_ofReal_mul_adjoinedDensity β γ σ t)] at h
  exact_mod_cast h

/-- **The reciprocal mass** `∫ u⁻¹ dν(u)` of the adjoined generalized primes. -/
theorem integral_adjoinedDensity_reciprocal (β γ : ℝ) (hβ : β < 1) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(1 * t)) * adjoinedDensity β γ t) =
      Real.log (1 + γ ^ 2 / (1 - β) ^ 2) :=
  integral_adjoinedDensity_mass β γ hβ

/-- **The abscissa of the adjoined measure is exactly `β`.**  The `β`-mass diverges, so no
smaller exponent controls the adjoined generalized primes. -/
theorem not_integrableOn_adjoinedDensity_abscissa (β : ℝ) {γ : ℝ} (hγ : γ ≠ 0) :
    ¬ IntegrableOn (fun t : ℝ => Real.exp (-(β * t)) * adjoinedDensity β γ t) (Ioi (0 : ℝ)) := by
  intro hint
  set M : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-(β * t)) * adjoinedDensity β γ t with hM
  have hγ2 : (0 : ℝ) < γ ^ 2 := by positivity
  set δ : ℝ := |γ| / Real.sqrt (Real.exp M + 1) with hδ
  have hroot : (0 : ℝ) < Real.sqrt (Real.exp M + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  have hδpos : 0 < δ := div_pos (abs_pos.mpr hγ) hroot
  set σ : ℝ := β + δ with hσdef
  have hσ : β < σ := by simp [hσdef, hδpos]
  -- the `σ`-mass is dominated by the `β`-mass
  have hdom : ∀ t ∈ Ioi (0 : ℝ),
      Real.exp (-(σ * t)) * adjoinedDensity β γ t ≤
        Real.exp (-(β * t)) * adjoinedDensity β γ t := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    refine mul_le_mul_of_nonneg_right ?_ (adjoinedDensity_nonneg β γ ht')
    apply Real.exp_le_exp.mpr
    nlinarith
  have hnonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ Real.exp (-(σ * t)) * adjoinedDensity β γ t := by
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (adjoinedDensity_nonneg β γ ht)
  have hintσ : IntegrableOn
      (fun t : ℝ => Real.exp (-(σ * t)) * adjoinedDensity β γ t) (Ioi (0 : ℝ)) := by
    refine Integrable.mono hint ?_ ?_
    · exact ((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable).mul
        ((continuousOn_adjoinedDensity β γ).aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnonneg t ht),
        abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (adjoinedDensity_nonneg β γ ht))]
      exact hdom t ht
  have hle : (∫ t in Ioi (0 : ℝ), Real.exp (-(σ * t)) * adjoinedDensity β γ t) ≤ M := by
    rw [hM]
    exact setIntegral_mono_on hintσ hint measurableSet_Ioi hdom
  rw [integral_adjoinedDensity_mass β γ hσ] at hle
  have hsub : σ - β = δ := by simp [hσdef]
  rw [hsub] at hle
  have hδ2 : δ ^ 2 = γ ^ 2 / (Real.exp M + 1) := by
    rw [hδ, div_pow, Real.sq_sqrt (by positivity), sq_abs]
  have hquot : γ ^ 2 / δ ^ 2 = Real.exp M + 1 := by
    rw [hδ2]
    field_simp
  rw [hquot] at hle
  have hgt : M < Real.log (1 + (Real.exp M + 1)) := by
    have h1 : Real.exp M < 1 + (Real.exp M + 1) := by linarith [Real.exp_pos M]
    calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
      _ < Real.log (1 + (Real.exp M + 1)) :=
          Real.log_lt_log (Real.exp_pos M) h1
  linarith

/-- The **Mertens integrand** of the adjoined primes: `log u` times the density. -/
def mertensIntegrand (β γ t : ℝ) : ℝ := 2 * Real.exp (β * t) * (1 - Real.cos (γ * t))

theorem mertensIntegrand_eq (β γ : ℝ) {t : ℝ} (ht : 0 < t) :
    mertensIntegrand β γ t = t * adjoinedDensity β γ t := by
  unfold mertensIntegrand adjoinedDensity
  field_simp

theorem cexp_mul_mertensIntegrand (β γ : ℝ) (s : ℂ) (t : ℝ) :
    Complex.exp (-(s * t)) * (mertensIntegrand β γ t : ℂ) =
      2 * Complex.exp (-((s - β) * t)) -
        Complex.exp (-((s - β - γ * I) * t)) -
        Complex.exp (-((s - β + γ * I) * t)) := by
  have e1 : Complex.exp (-((s - β - γ * I) * t)) =
      Complex.exp (-((s - β) * t)) * Complex.exp (((γ : ℂ) * t) * I) := by
    rw [← Complex.exp_add]; ring_nf
  have e2 : Complex.exp (-((s - β + γ * I) * t)) =
      Complex.exp (-((s - β) * t)) * Complex.exp (-(((γ : ℂ) * t) * I)) := by
    rw [← Complex.exp_add]; ring_nf
  have ecos : Complex.exp (((γ : ℂ) * t) * I) + Complex.exp (-(((γ : ℂ) * t) * I)) =
      2 * Complex.cos ((γ : ℂ) * t) := by
    rw [Complex.exp_mul_I, show -(((γ : ℂ) * t) * I) = (-((γ : ℂ) * t)) * I by ring,
      Complex.exp_mul_I]
    simp [Complex.cos_neg, Complex.sin_neg]
    ring
  have hcancel : Complex.exp (-(s * (t : ℂ))) * Complex.exp ((β : ℂ) * (t : ℂ)) =
      Complex.exp (-((s - (β : ℂ)) * (t : ℂ))) := by
    rw [← Complex.exp_add]; ring_nf
  have elhs : Complex.exp (-(s * t)) * (mertensIntegrand β γ t : ℂ) =
      Complex.exp (-((s - β) * t)) * (2 - 2 * Complex.cos ((γ : ℂ) * t)) := by
    unfold mertensIntegrand
    push_cast
    rw [show (2 : ℂ) * Complex.exp ((β : ℂ) * (t : ℂ)) * (1 - Complex.cos ((γ : ℂ) * (t : ℂ)))
          = Complex.exp ((β : ℂ) * (t : ℂ)) * (2 - 2 * Complex.cos ((γ : ℂ) * (t : ℂ))) from by
        ring, ← mul_assoc, hcancel]
  rw [elhs, e1, e2]
  linear_combination (Complex.exp (-((s - (β : ℂ)) * (t : ℂ)))) * ecos

/-- **The Mertens mass** `∫ u⁻¹ log u dν(u)` of the adjoined generalized primes: the amount by
which the Mertens sum of the enlarged system exceeds the classical one. -/
theorem integral_mertensIntegrand (β γ : ℝ) (hβ : β < 1) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-((1 : ℂ) * t)) * (mertensIntegrand β γ t : ℂ)) =
      2 * (γ : ℂ) ^ 2 / (((1 : ℂ) - β) * (((1 : ℂ) - β) ^ 2 + (γ : ℂ) ^ 2)) := by
  have hs : β < (1 : ℂ).re := by simpa using hβ
  have h0 := re_sub_pos (β := β) hs
  have h1 := re_sub_sub_pos (β := β) (γ := γ) hs
  have h2 := re_sub_add_pos (β := β) (γ := γ) hs
  have n0 : (1 : ℂ) - (β : ℂ) ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have n1 : (1 : ℂ) - (β : ℂ) - (γ : ℂ) * I ≠ 0 := by intro h; rw [h] at h1; simp at h1
  have n2 : (1 : ℂ) - (β : ℂ) + (γ : ℂ) * I ≠ 0 := by intro h; rw [h] at h2; simp at h2
  have hsplit :
      (∫ t in Ioi (0 : ℝ), Complex.exp (-((1 : ℂ) * t)) * (mertensIntegrand β γ t : ℂ)) =
        ∫ t in Ioi (0 : ℝ),
          ((2 : ℂ) * Complex.exp (-(((1 : ℂ) - β) * t)) -
            Complex.exp (-(((1 : ℂ) - β - γ * I) * t)) -
            Complex.exp (-(((1 : ℂ) - β + γ * I) * t))) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    exact cexp_mul_mertensIntegrand β γ 1 t
  rw [hsplit,
    integral_sub
      (f := fun t : ℝ => 2 * Complex.exp (-(((1 : ℂ) - β) * t)) -
        Complex.exp (-(((1 : ℂ) - β - γ * I) * t)))
      (g := fun t : ℝ => Complex.exp (-(((1 : ℂ) - β + γ * I) * t)))
      (((integrableOn_cexp_neg_mul h0).const_mul 2).sub (integrableOn_cexp_neg_mul h1))
      (integrableOn_cexp_neg_mul h2),
    integral_sub
      (f := fun t : ℝ => 2 * Complex.exp (-(((1 : ℂ) - β) * t)))
      (g := fun t : ℝ => Complex.exp (-(((1 : ℂ) - β - γ * I) * t)))
      ((integrableOn_cexp_neg_mul h0).const_mul 2) (integrableOn_cexp_neg_mul h1),
    integral_const_mul, integral_cexp_neg_mul h0, integral_cexp_neg_mul h1,
    integral_cexp_neg_mul h2]
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hfac : ((1 : ℂ) - (β : ℂ)) ^ 2 + (γ : ℂ) ^ 2 =
      ((1 : ℂ) - (β : ℂ) - (γ : ℂ) * I) * ((1 : ℂ) - (β : ℂ) + (γ : ℂ) * I) := by
    linear_combination ((γ : ℂ) ^ 2) * hI
  have hD : ((1 : ℂ) - (β : ℂ)) ^ 2 + (γ : ℂ) ^ 2 ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero n1 n2
  field_simp
  ring_nf
  rw [hI]
  ring

/-- The reciprocal mass tends to `0` as the adjoined oscillation frequency tends to `0`. -/
theorem tendsto_reciprocalMass (β : ℝ) (hβ : β < 1) :
    Tendsto (fun γ : ℝ => Real.log (1 + γ ^ 2 / (1 - β) ^ 2)) (𝓝 0) (𝓝 0) := by
  have hb : (1 - β) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < 1 - β := by linarith
    positivity
  have hcont : ContinuousAt (fun γ : ℝ => Real.log (1 + γ ^ 2 / (1 - β) ^ 2)) 0 := by
    apply ContinuousAt.log
    · fun_prop
    · norm_num
  simpa using hcont.tendsto

/-! ## The threshold theorem -/

/-- **Instability above the sensitivity threshold.**  For every `β` strictly between `1/2` and `1`
and every tolerance `ε > 0` there is an adjoined positive generalized-prime density whose reciprocal
mass is below `ε` and whose enlarged zeta function has a zero with real part `β`. -/
theorem exists_small_reciprocalMass_zero_off_line
    {β : ℝ} (hβ1 : 1 / 2 < β) (hβ2 : β < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧
      Real.log (1 + γ ^ 2 / (1 - β) ^ 2) < ε ∧
      (∀ t : ℝ, 0 < t → 0 ≤ adjoinedDensity β γ t) ∧
      perturbedZeta β γ ((β : ℂ) + (γ : ℂ) * I) = 0 ∧
      1 / 2 < ((β : ℂ) + (γ : ℂ) * I).re := by
  have hlim := tendsto_reciprocalMass β hβ2
  have hev0 : ∀ᶠ γ : ℝ in 𝓝 (0 : ℝ), Real.log (1 + γ ^ 2 / (1 - β) ^ 2) < ε :=
    hlim.eventually (eventually_lt_nhds hε)
  have hev : ∀ᶠ γ : ℝ in 𝓝[>] (0 : ℝ), Real.log (1 + γ ^ 2 / (1 - β) ^ 2) < ε :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hev0
  obtain ⟨γ, hγε, hγpos⟩ := ((hev.and self_mem_nhdsWithin).exists)
  refine ⟨γ, hγpos, hγε, fun t ht => adjoinedDensity_nonneg β γ ht,
    perturbedZeta_eq_zero β (ne_of_gt hγpos), ?_⟩
  rw [re_of_zero]
  exact hβ1

/-- **Stability half of the threshold theorem.**  If the adjoined positive generalized-prime
density has finite `σ`-mass for every `σ > 1/2`, then on `Re s > 1/2` the adjoined Euler factor is
the exponential of a convergent integral and is therefore never zero: the zeros of the enlarged
zeta function in that half plane are exactly the zeros of `ζ`. -/
theorem zeros_unchanged_of_mass_abscissa_le_half {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Ioi (0 : ℝ))))
    (hmass : ∀ σ : ℝ, 1 / 2 < σ →
      IntegrableOn (fun t : ℝ => Real.exp (-σ * t) * g t) (Ioi (0 : ℝ)))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * (g t : ℂ)) (Ioi (0 : ℝ)) ∧
      (riemannZeta s *
          Complex.exp (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (g t : ℂ)) = 0 ↔
        riemannZeta s = 0) :=
  ⟨integrableOn_cexp_mul_of_masses hg hmeas hmass hs, perturbed_eq_zero_iff _ _⟩

/-- **The Riemann hypothesis is a statement at the `σ = 1/2` scale of the prime measure.**

For every `β` strictly between `1/2` and `1` and every `ε > 0` there is a positive
generalized-prime density `g = adjoinedDensity β γ` on `(0, ∞)` such that

* `g ≥ 0`, and its `σ`-mass is `log (1 + γ²/(σ-β)²)` for every `σ > β`;
* its abscissa is exactly `β`: the `β`-mass diverges;
* its reciprocal mass — the total mass `∫ u⁻¹ dν(u)` of the adjoined generalized primes, which also
  bounds the shift of the Mertens sum — is smaller than `ε`;
* the adjoined Euler factor is `((s-β)² + γ²)/(s-β)²` on `Re s > β`;
* the enlarged zeta function `ζ(s)((s-β)²+γ²)/(s-β)²` vanishes at `β + iγ`, a point of the open
  half plane `Re s > 1/2`.

Together with `zeros_unchanged_of_mass_abscissa_le_half` this localizes exactly which scale of a
prime measure the Riemann hypothesis can see: an adjoined measure with abscissa at most `1/2` moves
no zero, while an adjoined measure of arbitrarily small reciprocal mass and abscissa `β > 1/2` puts
a zeta zero on the line `Re s = β`.  No functional of a prime system that is continuous for the
reciprocal (Mertens) mass can therefore decide the Riemann hypothesis. -/
theorem rh_sensitivity_threshold {β : ℝ} (hβ1 : 1 / 2 < β) (hβ2 : β < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧
      (∀ t : ℝ, 0 < t → 0 ≤ adjoinedDensity β γ t) ∧
      (∀ σ : ℝ, β < σ →
        (∫ t in Ioi (0 : ℝ), Real.exp (-(σ * t)) * adjoinedDensity β γ t) =
          Real.log (1 + γ ^ 2 / (σ - β) ^ 2)) ∧
      ¬ IntegrableOn (fun t : ℝ => Real.exp (-(β * t)) * adjoinedDensity β γ t) (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ), Real.exp (-(1 * t)) * adjoinedDensity β γ t) < ε ∧
      (∀ s : ℂ, β < s.re →
        Complex.exp (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (adjoinedDensity β γ t : ℂ)) =
          adjoinedFactor β γ s) ∧
      perturbedZeta β γ ((β : ℂ) + (γ : ℂ) * I) = 0 ∧
      1 / 2 < ((β : ℂ) + (γ : ℂ) * I).re := by
  obtain ⟨γ, hγpos, hγε, hnonneg, hzero, hre⟩ :=
    exists_small_reciprocalMass_zero_off_line hβ1 hβ2 hε
  refine ⟨γ, hγpos, hnonneg, fun σ hσ => integral_adjoinedDensity_mass β γ hσ,
    not_integrableOn_adjoinedDensity_abscissa β (ne_of_gt hγpos), ?_,
    fun s hs => cexp_integral_adjoinedDensity β γ hs, hzero, hre⟩
  rw [integral_adjoinedDensity_reciprocal β γ hβ2]
  exact hγε

end

end RHTower.BeurlingSensitivity
