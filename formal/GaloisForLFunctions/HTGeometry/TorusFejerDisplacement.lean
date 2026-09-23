import Mathlib

/-!
# The Fejér kernel on the circle and its mean displacement

The order-`N` Fejér kernel `F_N(x) = |D_N(x)|²/(N+1)`, built from the Dirichlet sum
`D_N(x) = ∑_{k ≤ N} e^{ikx}`, is nonnegative, has Haar integral one and concentrates at the origin.
The quantitative form of the concentration used by a moving-window estimate is the *mean
displacement*

`(1/2π) ∫_{-π}^{π} |x| F_N(x) dx ≤ 2π/√(N+1)`.

It follows from two elementary facts.  Expanding the square and integrating term by term, only the
`N+1` diagonal modes survive, so the total mass is `2π`.  Away from the origin the geometric sum
gives `|D_N(x)| ≤ 1/|sin(x/2)|`, and Jordan's inequality `sin(x/2) ≥ |x|/π` on `|x| ≤ π` turns this
into `F_N(x) ≤ π²/((N+1)x²)`.  Splitting the integral at `δ = π/√(N+1)` and using the mass bound
inside and the tail bound outside gives the two equal halves `2π²/√(N+1)`.

Convolving a `1/ρ`-Lipschitz function against `F_N` therefore moves it by at most
`2π/(ρ√(N+1))` in the uniform norm.
-/

open Real intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section TorusFejer

/-- The Dirichlet sum `D_N(x) = ∑_{k ≤ N} e^{ikx}`. -/
def dirichletSum (N : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), Complex.exp ((((k : ℝ) * x : ℝ) : ℂ) * Complex.I)

/-- The order-`N` Fejér kernel on the circle, `F_N(x) = |D_N(x)|²/(N+1)`. -/
def torusFejer (N : ℕ) (x : ℝ) : ℝ := ‖dirichletSum N x‖ ^ (2 : ℕ) / ((N : ℝ) + 1)

theorem torusFejer_nonneg (N : ℕ) (x : ℝ) : 0 ≤ torusFejer N x := by
  unfold torusFejer
  positivity

/-- The square of the Dirichlet sum expands into the `(N+1)²` modes of the kernel. -/
theorem dirichletSum_mul_conj (N : ℕ) (x : ℝ) :
    dirichletSum N x * (starRingEnd ℂ) (dirichletSum N x)
      = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          Complex.exp (((((p : ℝ) - (q : ℝ)) * x : ℝ)) * Complex.I) := by
  classical
  rw [dirichletSum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The squared modulus of the Dirichlet sum is a real cosine polynomial. -/
theorem norm_dirichletSum_sq (N : ℕ) (x : ℝ) :
    ‖dirichletSum N x‖ ^ (2 : ℕ)
      = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          Real.cos (((p : ℝ) - (q : ℝ)) * x) := by
  classical
  have hnormSq : (‖dirichletSum N x‖ ^ (2 : ℕ) : ℝ)
      = (dirichletSum N x * (starRingEnd ℂ) (dirichletSum N x)).re := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hnormSq, dirichletSum_mul_conj, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun q _ => Complex.exp_ofReal_mul_I_re _

/-- **The complex form of the kernel.**  It is a trigonometric polynomial whose frequencies are the
`(N+1)²` differences `p - q`. -/
theorem torusFejer_complex (N : ℕ) (x : ℝ) :
    ((torusFejer N x : ℝ) : ℂ)
      = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          ((N : ℂ) + 1)⁻¹ * Complex.exp (((((p : ℝ) - (q : ℝ)) * x : ℝ)) * Complex.I) := by
  classical
  have hNne : ((N : ℂ) + 1) ≠ 0 := by
    have : ((N : ℝ) + 1) ≠ 0 := by positivity
    intro h
    apply this
    exact_mod_cast h
  have hsq : ((‖dirichletSum N x‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = dirichletSum N x * (starRingEnd ℂ) (dirichletSum N x) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcast : (((N : ℝ) + 1 : ℝ) : ℂ) = (N : ℂ) + 1 := by push_cast; ring
  rw [torusFejer, Complex.ofReal_div, hcast, hsq, dirichletSum_mul_conj, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [div_eq_inv_mul]

/-- A single mode integrates to `2π` on the diagonal and to zero off it. -/
theorem integral_cos_mode (p q : ℕ) :
    (∫ x in (-π)..π, Real.cos (((p : ℝ) - (q : ℝ)) * x))
      = if p = q then 2 * π else 0 := by
  by_cases hpq : p = q
  · subst hpq
    simp
    ring
  · rw [if_neg hpq]
    have hm : ((p : ℝ) - (q : ℝ)) = (((p : ℤ) - (q : ℤ) : ℤ) : ℝ) := by push_cast; ring
    have hmne : ((p : ℤ) - (q : ℤ) : ℤ) ≠ 0 := by
      intro h
      exact hpq (by omega)
    have hcne : ((((p : ℤ) - (q : ℤ) : ℤ) : ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hmne
    rw [hm]
    set c : ℝ := (((p : ℤ) - (q : ℤ) : ℤ) : ℝ) with hc
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hcne, integral_cos]
    have h1 : Real.sin (c * π) = 0 := by
      rw [hc]
      exact Real.sin_int_mul_pi _
    have h2 : Real.sin (c * -π) = 0 := by
      have : c * -π = -(c * π) := by ring
      rw [this, Real.sin_neg, h1, neg_zero]
    rw [h1, h2]
    simp

/-- **The Fejér kernel has total mass `2π`,** i.e. Haar mean one. -/
theorem integral_torusFejer (N : ℕ) : (∫ x in (-π)..π, torusFejer N x) = 2 * π := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hNne : ((N : ℝ) + 1) ≠ 0 := ne_of_gt hNpos
  have hexp : ∀ x : ℝ, torusFejer N x
      = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          Real.cos (((p : ℝ) - (q : ℝ)) * x) / ((N : ℝ) + 1) := by
    intro x
    rw [torusFejer, norm_dirichletSum_sq]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_div _ _ _
  have hint : ∀ (p q : ℕ), IntervalIntegrable
      (fun x : ℝ => Real.cos (((p : ℝ) - (q : ℝ)) * x) / ((N : ℝ) + 1)) volume (-π) π := by
    intro p q
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  calc (∫ x in (-π)..π, torusFejer N x)
      = ∫ x in (-π)..π, ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          Real.cos (((p : ℝ) - (q : ℝ)) * x) / ((N : ℝ) + 1) := by
        exact intervalIntegral.integral_congr fun x _ => hexp x
    _ = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          ∫ x in (-π)..π, Real.cos (((p : ℝ) - (q : ℝ)) * x) / ((N : ℝ) + 1) := by
        rw [intervalIntegral.integral_finsetSum]
        · refine Finset.sum_congr rfl fun p _ => ?_
          rw [intervalIntegral.integral_finsetSum]
          exact fun q _ => hint p q
        · intro p _
          exact Continuous.intervalIntegrable (by fun_prop) _ _
    _ = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          (if p = q then (2 * π) / ((N : ℝ) + 1) else 0) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [intervalIntegral.integral_div, integral_cos_mode]
        split <;> simp
    _ = ∑ _p ∈ Finset.range (N + 1), (2 * π) / ((N : ℝ) + 1) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.sum_ite_eq]
        exact if_pos hp
    _ = 2 * π := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

end TorusFejer

section FejerTail

/-- The squared distance of a unimodular character from one. -/
theorem norm_exp_mul_I_sub_one_sq (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ (2 : ℕ) = 4 * Real.sin (θ / 2) ^ (2 : ℕ) := by
  have hre : (Complex.exp ((θ : ℂ) * Complex.I) - 1).re = Real.cos θ - 1 := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re]
  have him : (Complex.exp ((θ : ℂ) * Complex.I) - 1).im = Real.sin θ := by
    rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero]
  have hnorm : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ (2 : ℕ)
      = (Real.cos θ - 1) ^ (2 : ℕ) + Real.sin θ ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    ring
  have hpy : Real.sin θ ^ (2 : ℕ) + Real.cos θ ^ (2 : ℕ) = 1 := Real.sin_sq_add_cos_sq θ
  have hhalf : Real.cos θ = 2 * Real.cos (θ / 2) ^ (2 : ℕ) - 1 := by
    have := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    exact this
  have hpy2 : Real.sin (θ / 2) ^ (2 : ℕ) + Real.cos (θ / 2) ^ (2 : ℕ) = 1 := Real.sin_sq_add_cos_sq (θ / 2)
  rw [hnorm, hhalf]
  nlinarith [hpy, hpy2]

/-- The distance of a unimodular character from one. -/
theorem norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hsq := norm_exp_mul_I_sub_one_sq θ
  have h1 : (0 : ℝ) ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ 2 * |Real.sin (θ / 2)| := by positivity
  nlinarith [sq_abs (Real.sin (θ / 2))]

/-- **Jordan's inequality on the half-angle.**  On `|x| ≤ π` the half-angle sine is at least
`|x|/π`. -/
theorem abs_div_pi_le_abs_sin_half {x : ℝ} (hx : |x| ≤ π) : |x| / π ≤ |Real.sin (x / 2)| := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have habs : |Real.sin (x / 2)| = Real.sin (|x| / 2) := by
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by
        rw [abs_of_nonneg hx0] at hx; linarith)
    · rw [abs_of_neg hx0]
      have hneg : Real.sin (x / 2) ≤ 0 := by
        have : Real.sin (-(x / 2)) = -Real.sin (x / 2) := Real.sin_neg _
        have hnn : 0 ≤ Real.sin (-(x / 2)) := by
          refine Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) ?_
          rw [abs_of_neg hx0] at hx
          linarith
        linarith [this ▸ hnn]
      rw [abs_of_nonpos hneg]
      have : -x / 2 = -(x / 2) := by ring
      rw [this, Real.sin_neg]
  rw [habs]
  have hjordan : 2 / π * (|x| / 2) ≤ Real.sin (|x| / 2) :=
    Real.mul_le_sin (by positivity) (by linarith)
  calc |x| / π = 2 / π * (|x| / 2) := by ring
    _ ≤ Real.sin (|x| / 2) := hjordan

/-- The Dirichlet sum as a geometric sum. -/
theorem dirichletSum_eq_geom (N : ℕ) (x : ℝ) :
    dirichletSum N x = ∑ k ∈ Finset.range (N + 1), (Complex.exp ((x : ℂ) * Complex.I)) ^ k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The Dirichlet-sum bound away from the origin.** -/
theorem norm_dirichletSum_le (N : ℕ) {x : ℝ} (hx : x ≠ 0) (hxπ : |x| ≤ π) :
    ‖dirichletSum N x‖ ≤ π / |x| := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hxabs : (0 : ℝ) < |x| := abs_pos.mpr hx
  have hsin : |x| / π ≤ |Real.sin (x / 2)| := abs_div_pi_le_abs_sin_half hxπ
  have hsinpos : (0 : ℝ) < |Real.sin (x / 2)| := lt_of_lt_of_le (by positivity) hsin
  have hden : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (x / 2)| :=
    norm_exp_mul_I_sub_one x
  have hdenpos : (0 : ℝ) < ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ := by
    rw [hden]; positivity
  have hzne : Complex.exp ((x : ℂ) * Complex.I) ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hdenpos
    exact lt_irrefl 0 hdenpos
  have hgeom : dirichletSum N x
      = ((Complex.exp ((x : ℂ) * Complex.I)) ^ (N + 1) - 1)
        / (Complex.exp ((x : ℂ) * Complex.I) - 1) := by
    rw [dirichletSum_eq_geom]
    exact geom_sum_eq hzne (N + 1)
  have hznorm : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hnum : ‖(Complex.exp ((x : ℂ) * Complex.I)) ^ (N + 1) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, hznorm, one_pow, norm_one]
    norm_num
  have hstep : ‖dirichletSum N x‖ ≤ 2 / (2 * |Real.sin (x / 2)|) := by
    rw [hgeom, norm_div, hden]
    exact div_le_div₀ (by norm_num) hnum (by positivity) le_rfl
  have hfinal : 2 / (2 * |Real.sin (x / 2)|) ≤ π / |x| := by
    rw [div_le_div_iff₀ (by positivity) hxabs]
    have h2 : |x| ≤ |Real.sin (x / 2)| * π := (div_le_iff₀ hpi).mp hsin
    linarith
  linarith

/-- **`(15)`, the Fejér tail bound.**  Away from the origin the kernel decays quadratically. -/
theorem torusFejer_le (N : ℕ) {x : ℝ} (hx : x ≠ 0) (hxπ : |x| ≤ π) :
    torusFejer N x ≤ π ^ (2 : ℕ) / (((N : ℝ) + 1) * x ^ (2 : ℕ)) := by
  have hxabs : (0 : ℝ) < |x| := abs_pos.mpr hx
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hD := norm_dirichletSum_le N hx hxπ
  have hsq : ‖dirichletSum N x‖ ^ (2 : ℕ) ≤ (π / |x|) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hx2 : (π / |x|) ^ (2 : ℕ) = π ^ (2 : ℕ) / x ^ (2 : ℕ) := by
    rw [div_pow, sq_abs]
  rw [torusFejer, div_le_div_iff₀ hNpos (by positivity)]
  rw [hx2] at hsq
  have hxx : (0 : ℝ) < x ^ (2 : ℕ) := by positivity
  calc ‖dirichletSum N x‖ ^ (2 : ℕ) * (((N : ℝ) + 1) * x ^ (2 : ℕ))
      ≤ (π ^ (2 : ℕ) / x ^ (2 : ℕ)) * (((N : ℝ) + 1) * x ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = π ^ (2 : ℕ) * ((N : ℝ) + 1) := by field_simp

end FejerTail

section FejerDisplacement

theorem continuous_dirichletSum (N : ℕ) : Continuous (dirichletSum N) := by
  unfold dirichletSum
  fun_prop

theorem continuous_torusFejer (N : ℕ) : Continuous (torusFejer N) := by
  unfold torusFejer
  exact (((continuous_dirichletSum N).norm).pow 2).div_const _

/-- The antiderivative `-x⁻¹` computes the reciprocal-square integral off the origin. -/
theorem integral_inv_sq {a b : ℝ} (_hab : a ≤ b) (h0 : ∀ x ∈ Set.uIcc a b, x ≠ 0) :
    (∫ x in a..b, (x ^ (2 : ℕ))⁻¹) = a⁻¹ - b⁻¹ := by
  have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ (2 : ℕ))⁻¹) x := by
    intro x hx
    have h : HasDerivAt (fun y : ℝ => -y⁻¹) (-(-(x ^ (2 : ℕ))⁻¹)) x := (hasDerivAt_inv (h0 x hx)).neg
    simpa using h
  have hcontOn : ContinuousOn (fun x : ℝ => (x ^ (2 : ℕ))⁻¹) (Set.uIcc a b) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    exact pow_ne_zero 2 (h0 x hx)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcontOn.intervalIntegrable]
  ring

/-- **`(14)`, the Fejér mean displacement.**  The kernel moves mass by at most `2π/√(N+1)` in
Haar mean. -/
theorem integral_abs_mul_torusFejer_le (N : ℕ) :
    (∫ x in (-π)..π, |x| * torusFejer N x) ≤ 4 * π ^ (2 : ℕ) / Real.sqrt ((N : ℝ) + 1) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set s : ℝ := Real.sqrt ((N : ℝ) + 1) with hsdef
  have hs1 : 1 ≤ s := by
    rw [hsdef, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by simp)
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs1
  have hssq : s ^ (2 : ℕ) = (N : ℝ) + 1 := Real.sq_sqrt (le_of_lt hNpos)
  set δ : ℝ := π / s with hδdef
  have hδpos : (0 : ℝ) < δ := by positivity
  have hδπ : δ ≤ π := by
    rw [hδdef]
    exact div_le_self (le_of_lt hpi) hs1
  set A : ℝ := π ^ (2 : ℕ) / ((N : ℝ) + 1) with hAdef
  have hApos : (0 : ℝ) < A := by positivity
  have hcontF : Continuous (torusFejer N) := continuous_torusFejer N
  have hcont : Continuous fun x : ℝ => |x| * torusFejer N x := continuous_abs.mul hcontF
  -- the three adjacent windows
  have e1 : (∫ x in (-π)..(-δ), |x| * torusFejer N x)
      + (∫ x in (-δ)..δ, |x| * torusFejer N x) = ∫ x in (-π)..δ, |x| * torusFejer N x :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have e2 : (∫ x in (-π)..δ, |x| * torusFejer N x)
      + (∫ x in δ..π, |x| * torusFejer N x) = ∫ x in (-π)..π, |x| * torusFejer N x :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  -- the middle window uses the total mass
  have hmid : (∫ x in (-δ)..δ, |x| * torusFejer N x) ≤ δ * (2 * π) := by
    have hle : (∫ x in (-δ)..δ, |x| * torusFejer N x)
        ≤ ∫ x in (-δ)..δ, δ * torusFejer N x := by
      refine intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
        ((continuous_const.mul hcontF).intervalIntegrable _ _) fun x hx => ?_
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hx.1, hx.2⟩) (torusFejer_nonneg N x)
    have heq : (∫ x in (-δ)..δ, δ * torusFejer N x) = δ * ∫ x in (-δ)..δ, torusFejer N x :=
      intervalIntegral.integral_const_mul _ _
    have f1 : (∫ x in (-π)..(-δ), torusFejer N x) + (∫ x in (-δ)..δ, torusFejer N x)
        = ∫ x in (-π)..δ, torusFejer N x :=
      intervalIntegral.integral_add_adjacent_intervals (hcontF.intervalIntegrable _ _)
        (hcontF.intervalIntegrable _ _)
    have f2 : (∫ x in (-π)..δ, torusFejer N x) + (∫ x in δ..π, torusFejer N x)
        = ∫ x in (-π)..π, torusFejer N x :=
      intervalIntegral.integral_add_adjacent_intervals (hcontF.intervalIntegrable _ _)
        (hcontF.intervalIntegrable _ _)
    have n1 : 0 ≤ ∫ x in (-π)..(-δ), torusFejer N x :=
      intervalIntegral.integral_nonneg (by linarith) fun x _ => torusFejer_nonneg N x
    have n2 : 0 ≤ ∫ x in δ..π, torusFejer N x :=
      intervalIntegral.integral_nonneg hδπ fun x _ => torusFejer_nonneg N x
    have htot := integral_torusFejer N
    have hFint : (∫ x in (-δ)..δ, torusFejer N x) ≤ 2 * π := by linarith
    calc (∫ x in (-δ)..δ, |x| * torusFejer N x) ≤ ∫ x in (-δ)..δ, δ * torusFejer N x := hle
      _ = δ * ∫ x in (-δ)..δ, torusFejer N x := heq
      _ ≤ δ * (2 * π) := mul_le_mul_of_nonneg_left hFint (le_of_lt hδpos)
  -- the two tails use the quadratic decay
  have hmajor : ∀ x : ℝ, x ≠ 0 → |x| ≤ π → |x| * torusFejer N x ≤ π * (A * (x ^ (2 : ℕ))⁻¹) := by
    intro x hx hxπ
    have hx2 : (0 : ℝ) < x ^ (2 : ℕ) := by positivity
    have hF := torusFejer_le N hx hxπ
    have hFA : π ^ (2 : ℕ) / (((N : ℝ) + 1) * x ^ (2 : ℕ)) = A * (x ^ (2 : ℕ))⁻¹ := by
      rw [hAdef]
      field_simp
    rw [hFA] at hF
    calc |x| * torusFejer N x ≤ π * torusFejer N x :=
          mul_le_mul_of_nonneg_right hxπ (torusFejer_nonneg N x)
      _ ≤ π * (A * (x ^ (2 : ℕ))⁻¹) := mul_le_mul_of_nonneg_left hF (le_of_lt hpi)
  have hcontMaj : ∀ {a b : ℝ}, (∀ x ∈ Set.uIcc a b, x ≠ 0) →
      IntervalIntegrable (fun x : ℝ => π * (A * (x ^ (2 : ℕ))⁻¹)) MeasureTheory.volume a b := by
    intro a b h0
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop) ?_))
    exact fun x hx => pow_ne_zero 2 (h0 x hx)
  have htailR : (∫ x in δ..π, |x| * torusFejer N x) ≤ π * A * δ⁻¹ := by
    have h0 : ∀ x ∈ Set.uIcc δ π, x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le hδπ] at hx
      exact ne_of_gt (lt_of_lt_of_le hδpos hx.1)
    have hle : (∫ x in δ..π, |x| * torusFejer N x)
        ≤ ∫ x in δ..π, π * (A * (x ^ (2 : ℕ))⁻¹) := by
      refine intervalIntegral.integral_mono_on hδπ (hcont.intervalIntegrable _ _)
        (hcontMaj h0) fun x hx => ?_
      have hxne : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hδpos hx.1)
      exact hmajor x hxne (by rw [abs_of_pos (lt_of_lt_of_le hδpos hx.1)]; exact hx.2)
    have heval : (∫ x in δ..π, π * (A * (x ^ (2 : ℕ))⁻¹)) = π * A * (δ⁻¹ - π⁻¹) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_inv_sq hδπ h0]
      ring
    have hdrop : π * A * (δ⁻¹ - π⁻¹) ≤ π * A * δ⁻¹ := by
      have hpa : (0 : ℝ) ≤ π * A := by positivity
      have hinvpi : (0 : ℝ) < π⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) hpa
    linarith
  have htailL : (∫ x in (-π)..(-δ), |x| * torusFejer N x) ≤ π * A * δ⁻¹ := by
    have hle' : -π ≤ -δ := by linarith
    have h0 : ∀ x ∈ Set.uIcc (-π) (-δ), x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le hle'] at hx
      exact ne_of_lt (lt_of_le_of_lt hx.2 (by linarith))
    have hle : (∫ x in (-π)..(-δ), |x| * torusFejer N x)
        ≤ ∫ x in (-π)..(-δ), π * (A * (x ^ (2 : ℕ))⁻¹) := by
      refine intervalIntegral.integral_mono_on hle' (hcont.intervalIntegrable _ _)
        (hcontMaj h0) fun x hx => ?_
      have hxneg : x < 0 := lt_of_le_of_lt hx.2 (by linarith)
      refine hmajor x (ne_of_lt hxneg) ?_
      rw [abs_of_neg hxneg]
      linarith [hx.1]
    have heval : (∫ x in (-π)..(-δ), π * (A * (x ^ (2 : ℕ))⁻¹)) = π * A * (δ⁻¹ - π⁻¹) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_inv_sq hle' h0]
      have hneg : (-π : ℝ)⁻¹ - (-δ : ℝ)⁻¹ = δ⁻¹ - π⁻¹ := by
        rw [inv_neg, inv_neg]; ring
      rw [hneg]
      ring
    have hdrop : π * A * (δ⁻¹ - π⁻¹) ≤ π * A * δ⁻¹ := by
      have hpa : (0 : ℝ) ≤ π * A := by positivity
      have hinvpi : (0 : ℝ) < π⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) hpa
    linarith
  -- assemble
  have hsum : (∫ x in (-π)..π, |x| * torusFejer N x)
      ≤ π * A * δ⁻¹ + δ * (2 * π) + π * A * δ⁻¹ := by
    rw [← e2, ← e1]
    linarith
  have hδval : δ * (2 * π) = 2 * π ^ (2 : ℕ) / s := by
    rw [hδdef]
    field_simp
  have hAval : π * A * δ⁻¹ = π ^ (2 : ℕ) / s := by
    rw [hAdef, hδdef, ← hssq]
    field_simp
  rw [hδval, hAval] at hsum
  calc (∫ x in (-π)..π, |x| * torusFejer N x)
      ≤ π ^ (2 : ℕ) / s + 2 * π ^ (2 : ℕ) / s + π ^ (2 : ℕ) / s := hsum
    _ = 4 * π ^ (2 : ℕ) / s := by ring

end FejerDisplacement

section FejerConvolution

/-- The Fejér mean of `f`: its convolution against the order-`N` kernel, in Haar normalization. -/
def fejerConv (N : ℕ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ x in (-π)..π, f (θ - x) * torusFejer N x

theorem fejerConv_sub_eq (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f) (θ : ℝ) :
    fejerConv N f θ - f θ
      = (1 / (2 * π)) * ∫ x in (-π)..π, (f (θ - x) - f θ) * torusFejer N x := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hcontF : Continuous (torusFejer N) := continuous_torusFejer N
  have h1 : Continuous fun x : ℝ => f (θ - x) * torusFejer N x :=
    (hf.comp (continuous_const.sub continuous_id)).mul hcontF
  have h2 : Continuous fun x : ℝ => f θ * torusFejer N x := continuous_const.mul hcontF
  have hsplit : (∫ x in (-π)..π, (f (θ - x) - f θ) * torusFejer N x)
      = (∫ x in (-π)..π, f (θ - x) * torusFejer N x)
        - ∫ x in (-π)..π, f θ * torusFejer N x := by
    rw [← intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun x _ => by ring
  have hconst : (∫ x in (-π)..π, f θ * torusFejer N x) = f θ * (2 * π) := by
    rw [intervalIntegral.integral_const_mul, integral_torusFejer]
  rw [hsplit, hconst, fejerConv, mul_sub]
  have : (1 / (2 * π)) * (f θ * (2 * π)) = f θ := by field_simp
  rw [this]

/-- **`(16)`, the Fejér displacement of a Lipschitz function.**  The Fejér mean of an `L`-Lipschitz
function differs from it by at most `2πL/√(N+1)`, uniformly. -/
theorem abs_fejerConv_sub_le (N : ℕ) {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|) (θ : ℝ) :
    |fejerConv N f θ - f θ| ≤ L * (2 * π / Real.sqrt ((N : ℝ) + 1)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hcontf : Continuous f := by
    refine Metric.continuous_iff.mpr fun u ε hε => ?_
    rcases eq_or_lt_of_le hL with hL0 | hL0
    · refine ⟨1, one_pos, fun v _ => ?_⟩
      have := hf v u
      rw [← hL0, zero_mul] at this
      rw [Real.dist_eq]
      exact lt_of_le_of_lt this hε
    · refine ⟨ε / L, by positivity, fun v hv => ?_⟩
      rw [Real.dist_eq] at hv ⊢
      calc |f v - f u| ≤ L * |v - u| := hf v u
        _ < L * (ε / L) := mul_lt_mul_of_pos_left hv hL0
        _ = ε := by field_simp
  have hcontF : Continuous (torusFejer N) := continuous_torusFejer N
  have hcont1 : Continuous fun x : ℝ => (f (θ - x) - f θ) * torusFejer N x :=
    ((hcontf.comp (continuous_const.sub continuous_id)).sub continuous_const).mul hcontF
  have hcont2 : Continuous fun x : ℝ => L * (|x| * torusFejer N x) :=
    continuous_const.mul (continuous_abs.mul hcontF)
  have hpointwise : ∀ x ∈ Set.Icc (-π) π,
      |(f (θ - x) - f θ) * torusFejer N x| ≤ L * (|x| * torusFejer N x) := by
    intro x _
    rw [abs_mul, abs_of_nonneg (torusFejer_nonneg N x)]
    have h1 : |f (θ - x) - f θ| ≤ L * |x| := by
      have := hf (θ - x) θ
      rwa [show θ - x - θ = -x by ring, abs_neg] at this
    calc |f (θ - x) - f θ| * torusFejer N x ≤ (L * |x|) * torusFejer N x :=
          mul_le_mul_of_nonneg_right h1 (torusFejer_nonneg N x)
      _ = L * (|x| * torusFejer N x) := by ring
  have hbound : |∫ x in (-π)..π, (f (θ - x) - f θ) * torusFejer N x|
      ≤ L * (4 * π ^ (2 : ℕ) / Real.sqrt ((N : ℝ) + 1)) := by
    have hππ : (-π : ℝ) ≤ π := by linarith
    calc |∫ x in (-π)..π, (f (θ - x) - f θ) * torusFejer N x|
        ≤ ∫ x in (-π)..π, |(f (θ - x) - f θ) * torusFejer N x| :=
          intervalIntegral.abs_integral_le_integral_abs hππ
      _ ≤ ∫ x in (-π)..π, L * (|x| * torusFejer N x) := by
          refine intervalIntegral.integral_mono_on hππ
            ((hcont1.abs).intervalIntegrable _ _) (hcont2.intervalIntegrable _ _) hpointwise
      _ = L * ∫ x in (-π)..π, |x| * torusFejer N x :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ L * (4 * π ^ (2 : ℕ) / Real.sqrt ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (integral_abs_mul_torusFejer_le N) hL
  rw [fejerConv_sub_eq N hcontf θ, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * π))]
  calc (1 / (2 * π)) * |∫ x in (-π)..π, (f (θ - x) - f θ) * torusFejer N x|
      ≤ (1 / (2 * π)) * (L * (4 * π ^ (2 : ℕ) / Real.sqrt ((N : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = L * (2 * π / Real.sqrt ((N : ℝ) + 1)) := by
        field_simp
        ring

end FejerConvolution

section Tent

/-- The tent function of width `ρ`, `q_ρ(x) = max(1 - |x|/ρ, 0)`. -/
def torusTent (ρ x : ℝ) : ℝ := max (1 - |x| / ρ) 0

theorem torusTent_nonneg (ρ x : ℝ) : 0 ≤ torusTent ρ x := le_max_right _ _

theorem torusTent_le_one {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) : torusTent ρ x ≤ 1 := by
  refine max_le ?_ zero_le_one
  have : (0 : ℝ) ≤ |x| / ρ := by positivity
  linarith

/-- The positivity set of the tent is the open interval of radius `ρ`. -/
theorem torusTent_pos_iff {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) : 0 < torusTent ρ x ↔ |x| < ρ := by
  rw [torusTent, lt_max_iff]
  constructor
  · rintro (h | h)
    · rw [lt_sub_iff_add_lt, zero_add, div_lt_one hρ] at h
      exact h
    · exact absurd h (lt_irrefl 0)
  · intro h
    left
    rw [lt_sub_iff_add_lt, zero_add, div_lt_one hρ]
    exact h

theorem continuous_torusTent (ρ : ℝ) : Continuous (torusTent ρ) := by
  unfold torusTent
  fun_prop

/-- **The tent is `1/ρ`-Lipschitz.** -/
theorem abs_torusTent_sub_le {ρ : ℝ} (hρ : 0 < ρ) (u v : ℝ) :
    |torusTent ρ u - torusTent ρ v| ≤ (1 / ρ) * |u - v| := by
  have hmax : |torusTent ρ u - torusTent ρ v| ≤ |(1 - |u| / ρ) - (1 - |v| / ρ)| := by
    unfold torusTent
    exact abs_max_sub_max_le_abs _ _ _
  have heq : (1 - |u| / ρ) - (1 - |v| / ρ) = (|v| - |u|) / ρ := by ring
  have habs : |(|v| - |u|)| ≤ |u - v| := by
    have := abs_abs_sub_abs_le_abs_sub v u
    rwa [show v - u = -(u - v) by ring, abs_neg] at this
  calc |torusTent ρ u - torusTent ρ v| ≤ |(1 - |u| / ρ) - (1 - |v| / ρ)| := hmax
    _ = |(|v| - |u|)| / ρ := by rw [heq, abs_div, abs_of_pos hρ]
    _ ≤ |u - v| / ρ := by gcongr
    _ = (1 / ρ) * |u - v| := by ring

/-- The absolute value integrates to `ρ²` over the symmetric window of radius `ρ`. -/
theorem integral_abs_symm {ρ : ℝ} (hρ : 0 < ρ) : (∫ x in (-ρ)..ρ, |x|) = ρ ^ (2 : ℕ) := by
  have hcont : Continuous fun x : ℝ => |x| := continuous_abs
  have hneg : (∫ x in (-ρ)..(0 : ℝ), |x|) = ρ ^ (2 : ℕ) / 2 := by
    have h : (∫ x in (-ρ)..(0 : ℝ), |x|) = ∫ x in (-ρ)..(0 : ℝ), -x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact abs_of_nonpos hx.2
    rw [h, intervalIntegral.integral_neg, integral_id]
    ring
  have hpos : (∫ x in (0 : ℝ)..ρ, |x|) = ρ ^ (2 : ℕ) / 2 := by
    have h : (∫ x in (0 : ℝ)..ρ, |x|) = ∫ x in (0 : ℝ)..ρ, x := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact abs_of_nonneg hx.1
    rw [h, integral_id]
    ring
  have hadd : (∫ x in (-ρ)..(0 : ℝ), |x|) + (∫ x in (0 : ℝ)..ρ, |x|) = ∫ x in (-ρ)..ρ, |x| :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  rw [← hadd, hneg, hpos]
  ring

/-- **`(11)`, the tent mass.**  The tent of width `ρ ≤ π` has Haar mean `ρ/2π`. -/
theorem integral_torusTent {ρ : ℝ} (hρ : 0 < ρ) (hρπ : ρ ≤ π) : (∫ x in (-π)..π, torusTent ρ x) = ρ := by
  have hcont : Continuous (torusTent ρ) := continuous_torusTent ρ
  have hcontA : Continuous fun x : ℝ => |x| := continuous_abs
  have hzeroOut : ∀ {a b : ℝ}, (∀ x ∈ Set.uIcc a b, ρ ≤ |x|) → (∫ x in a..b, torusTent ρ x) = 0 := by
    intro a b h
    have : (∫ x in a..b, torusTent ρ x) = ∫ _x in a..b, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      refine max_eq_right ?_
      have hx' : ρ ≤ |x| := h x hx
      have : (1 : ℝ) ≤ |x| / ρ := (one_le_div hρ).mpr hx'
      linarith
    rw [this, intervalIntegral.integral_const]
    simp
  have h1 : (∫ x in (-π)..(-ρ), torusTent ρ x) = 0 := by
    refine hzeroOut fun x hx => ?_
    rw [Set.uIcc_of_le (by linarith)] at hx
    rw [abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.2]
  have h3 : (∫ x in ρ..π, torusTent ρ x) = 0 := by
    refine hzeroOut fun x hx => ?_
    rw [Set.uIcc_of_le hρπ] at hx
    rw [abs_of_nonneg (by linarith [hx.1])]
    exact hx.1
  have h2 : (∫ x in (-ρ)..ρ, torusTent ρ x) = ρ := by
    have hcongr : (∫ x in (-ρ)..ρ, torusTent ρ x) = ∫ x in (-ρ)..ρ, (1 - |x| / ρ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by linarith)] at hx
      refine max_eq_left ?_
      have hle : |x| ≤ ρ := abs_le.mpr ⟨hx.1, hx.2⟩
      have : |x| / ρ ≤ 1 := (div_le_one hρ).mpr hle
      linarith
    have hsub : (∫ x in (-ρ)..ρ, (1 - |x| / ρ))
        = (∫ _x in (-ρ)..ρ, (1 : ℝ)) - ∫ x in (-ρ)..ρ, |x| / ρ := by
      refine intervalIntegral.integral_sub intervalIntegrable_const ?_
      exact (hcontA.div_const ρ).intervalIntegrable _ _
    have hdiv : (∫ x in (-ρ)..ρ, |x| / ρ) = ρ := by
      rw [intervalIntegral.integral_div, integral_abs_symm hρ]
      field_simp
    rw [hcongr, hsub, hdiv, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
    ring
  have e1 : (∫ x in (-π)..(-ρ), torusTent ρ x) + (∫ x in (-ρ)..ρ, torusTent ρ x)
      = ∫ x in (-π)..ρ, torusTent ρ x :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  have e2 : (∫ x in (-π)..ρ, torusTent ρ x) + (∫ x in ρ..π, torusTent ρ x)
      = ∫ x in (-π)..π, torusTent ρ x :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  rw [← e2, ← e1, h1, h2, h3]
  ring

/-- **`(16)` for the tent.**  The Fejér mean of the tent of width `ρ` is uniformly within
`2π/(ρ√(N+1))` of it. -/
theorem abs_fejerConv_torusTent_sub_le (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    |fejerConv N (torusTent ρ) θ - torusTent ρ θ| ≤ (1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1)) :=
  abs_fejerConv_sub_le N (by positivity) (fun u v => abs_torusTent_sub_le hρ u v) θ

end Tent

section ProductDisplacement

theorem fejerConv_nonneg (N : ℕ) {f : ℝ → ℝ} (hf0 : ∀ y, 0 ≤ f y) (θ : ℝ) :
    0 ≤ fejerConv N f θ := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  refine mul_nonneg (by positivity) ?_
  refine intervalIntegral.integral_nonneg (by linarith) fun x _ => ?_
  exact mul_nonneg (hf0 _) (torusFejer_nonneg N x)

theorem fejerConv_le_one (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f) (hf1 : ∀ y, f y ≤ 1) (θ : ℝ) :
    fejerConv N f θ ≤ 1 := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hcontF : Continuous (torusFejer N) := continuous_torusFejer N
  have hle : (∫ x in (-π)..π, f (θ - x) * torusFejer N x) ≤ ∫ x in (-π)..π, torusFejer N x := by
    refine intervalIntegral.integral_mono_on (by linarith)
      (((hf.comp (continuous_const.sub continuous_id)).mul hcontF).intervalIntegrable _ _)
      (hcontF.intervalIntegrable _ _) fun x _ => ?_
    calc f (θ - x) * torusFejer N x ≤ 1 * torusFejer N x :=
          mul_le_mul_of_nonneg_right (hf1 _) (torusFejer_nonneg N x)
      _ = torusFejer N x := one_mul _
  rw [integral_torusFejer] at hle
  rw [fejerConv]
  calc (1 / (2 * π)) * ∫ x in (-π)..π, f (θ - x) * torusFejer N x
      ≤ (1 / (2 * π)) * (2 * π) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 := by field_simp

/-- A telescoping bound for products of numbers in the unit ball. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      have hax : |a x| ≤ 1 := ha x (Finset.mem_insert_self x s)
      have hbx : |b x| ≤ 1 := hb x (Finset.mem_insert_self x s)
      have has : ∀ i ∈ s, |a i| ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
      have hbs : ∀ i ∈ s, |b i| ≤ 1 := fun i hi => hb i (Finset.mem_insert_of_mem hi)
      have hprodA : |∏ i ∈ s, a i| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun i _ => abs_nonneg _) has
      rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx]
      have key : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i
          = (a x - b x) * (∏ i ∈ s, a i) + b x * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i) := by ring
      rw [key]
      calc |(a x - b x) * (∏ i ∈ s, a i) + b x * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i)|
          ≤ |(a x - b x) * (∏ i ∈ s, a i)| + |b x * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i)| :=
            abs_add_le _ _
        _ = |a x - b x| * |∏ i ∈ s, a i| + |b x| * |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| := by
            rw [abs_mul, abs_mul]
        _ ≤ |a x - b x| * 1 + 1 * ∑ i ∈ s, |a i - b i| := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul_of_nonneg_left hprodA (abs_nonneg _)
            · exact mul_le_mul hbx (ih has hbs) (abs_nonneg _) zero_le_one
        _ = |a x - b x| + ∑ i ∈ s, |a i - b i| := by ring

variable {d : ℕ}

/-- The `d`-fold tent centred at `c`. -/
def productTent (ρ : ℝ) (c θ : Fin d → ℝ) : ℝ := ∏ j, torusTent ρ (θ j - c j)

/-- The Fejér mean of the `d`-fold tent.  Convolving a product function against the product
kernel `F_N^{⊗d}` factorizes, by Fubini, into the one-dimensional Fejér means. -/
def productFejerTent (N : ℕ) (ρ : ℝ) (c θ : Fin d → ℝ) : ℝ :=
  ∏ j, fejerConv N (torusTent ρ) (θ j - c j)

/-- **`(16)` in `d` dimensions.**  The Fejér mean of the product tent is uniformly within
`2πd/(ρ√(N+1))` of it. -/
theorem abs_productFejerTent_sub_le (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (c θ : Fin d → ℝ) :
    |productFejerTent N ρ c θ - productTent ρ c θ|
      ≤ (d : ℝ) * ((1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1))) := by
  classical
  have hcontT : Continuous (torusTent ρ) := continuous_torusTent ρ
  have hb : ∀ j : Fin d, |torusTent ρ (θ j - c j)| ≤ 1 := by
    intro j
    rw [abs_of_nonneg (torusTent_nonneg _ _)]
    exact torusTent_le_one hρ _
  have ha : ∀ j : Fin d, |fejerConv N (torusTent ρ) (θ j - c j)| ≤ 1 := by
    intro j
    rw [abs_of_nonneg (fejerConv_nonneg N (fun y => torusTent_nonneg ρ y) _)]
    exact fejerConv_le_one N hcontT (fun y => torusTent_le_one hρ y) _
  have htele := abs_prod_sub_prod_le (Finset.univ : Finset (Fin d))
    (fun j => fejerConv N (torusTent ρ) (θ j - c j)) (fun j => torusTent ρ (θ j - c j))
    (fun j _ => ha j) (fun j _ => hb j)
  refine le_trans htele ?_
  calc ∑ j : Fin d, |fejerConv N (torusTent ρ) (θ j - c j) - torusTent ρ (θ j - c j)|
      ≤ ∑ _j : Fin d, (1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1)) :=
        Finset.sum_le_sum fun j _ => abs_fejerConv_torusTent_sub_le N hρ _
    _ = (d : ℝ) * ((1 / ρ) * (2 * π / Real.sqrt ((N : ℝ) + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end ProductDisplacement

end

end GaloisForLFunctions.HTGeometry
