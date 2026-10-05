import GaloisForLFunctions.HTGeometry.PrimeShiftScaleMemory

/-!
# The relative-scale defect kernel

For `a, b > 0` the normalized ordered defect of two prime letters has the closed form
`ab ω_t(a,b) = (a - b)/(a + b) · (1 - e^{-(a+b)t}) + e^{-at} - e^{-bt}`, obtained by integrating
the simplex kernel twice.  It yields:

* `(FGP.3)`: `0 < -ab ω_t(a,b) ≤ (b - a)/a` for `0 < a < b`, `t > 0`;
* `(FGP.4)`: `ab ω_t(a,b) → (a - b)/(a + b)` as `t → ∞`;
* `(FGP.4a)`: `∫₀^∞ e^{-zt} ab ω_t(a,b) dt = ab(a - b)/(z(z+a)(z+b)(z+a+b))`, `Re z > 0`;
* `(FGP.4b)`: `sup_{t ≥ 0} |∂_t^k (ab ω_t(a,b))| ≤ C_k a^{k-1} (b - a)` for `a ≤ b ≤ 2a`, with
  `C_k = 3^k + (k+1) 2^k`; the `t`-derivatives are exponential polynomials and the difference
  `a^k e^{-at} - b^k e^{-bt}` is controlled by the mean value theorem in the scale.

The relative factor `a - b` survives every finite time differentiation.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

theorem integral_exp_neg_mul_eq {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    ∫ v in (0 : ℝ)..x, Real.exp (-c * v) = (1 - Real.exp (-c * x)) / c := by
  have hderiv : ∀ v ∈ uIcc (0 : ℝ) x, HasDerivAt (fun v => -Real.exp (-c * v) / c)
      (Real.exp (-c * v)) v := fun v _ => by
    have h := ((hasDerivAt_id' v).const_mul (-c)).exp
    refine (h.neg.div_const c).congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun v : ℝ => Real.exp (-c * v)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- The simplex kernel in closed form. -/
theorem simplexKernel_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) (t : ℝ) :
    simplexKernel a b t =
      ((1 - Real.exp (-(a + b) * t)) / (a + b) - Real.exp (-b * t) *
        ((1 - Real.exp (-a * t)) / a)) / b := by
  have hcongr : ∀ u ∈ uIcc (0 : ℝ) t,
      ∫ v in (0 : ℝ)..(t - u), Real.exp (-(a + b) * u - b * v) =
        (Real.exp (-(a + b) * u) - Real.exp (-b * t) * Real.exp (-a * u)) / b := fun u _ => by
    have he : Real.exp (-(a + b) * u) * Real.exp (-b * (t - u)) =
        Real.exp (-b * t) * Real.exp (-a * u) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    rw [inner_simplex_eq, integral_exp_neg_mul_eq hb, mul_div_assoc', mul_sub, mul_one, he]
  rw [simplexKernel, intervalIntegral.integral_congr hcongr, intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun u : ℝ => Real.exp (-(a + b) * u)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun u : ℝ =>
        Real.exp (-b * t) * Real.exp (-a * u)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_exp_neg_mul_eq ha]
  rw [show -(a + b) = -(a + b) by rfl, integral_exp_neg_mul_eq hab]

/-- **The closed form** `ab ω_t(a,b) = (a-b)/(a+b) (1 - e^{-(a+b)t}) + e^{-at} - e^{-bt}`. -/
theorem defectKernel_closed {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    a * b * defectKernel t a b =
      (a - b) / (a + b) * (1 - Real.exp (-(a + b) * t)) + Real.exp (-a * t) -
        Real.exp (-b * t) := by
  have hab : a + b ≠ 0 := by positivity
  have hba : b + a ≠ 0 := by positivity
  rw [defectKernel, simplexKernel_eq ha.ne' hb.ne' hab, simplexKernel_eq hb.ne' ha.ne' hba,
    add_comm b a]
  field_simp
  ring

/-- **`(FGP.3)`: the universal relative-scale bound** `-ab ω_t(a,b) ≤ (b - a)/a`. -/
theorem neg_defect_le {a b : ℝ} (ha : 0 < a) (hab : a < b) {t : ℝ} (ht : 0 ≤ t) :
    -(a * b * defectKernel t a b) ≤ (b - a) / a := by
  have hb : 0 < b := ha.trans hab
  rw [defectKernel_closed ha hb]
  have he : Real.exp (-b * t) ≤ Real.exp (-a * t) := Real.exp_le_exp.mpr (by nlinarith)
  have hE : 0 ≤ 1 - Real.exp (-(a + b) * t) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
  have hE1 : 1 - Real.exp (-(a + b) * t) ≤ 1 := sub_le_self _ (Real.exp_pos _).le
  have hρ : (b - a) / (a + b) ≤ (b - a) / a :=
    div_le_div_of_nonneg_left (by linarith) ha (by linarith)
  have hρ0 : 0 ≤ (b - a) / (a + b) := div_nonneg (by linarith) (by linarith)
  calc -((a - b) / (a + b) * (1 - Real.exp (-(a + b) * t)) + Real.exp (-a * t) -
        Real.exp (-b * t))
      = (b - a) / (a + b) * (1 - Real.exp (-(a + b) * t)) -
          (Real.exp (-a * t) - Real.exp (-b * t)) := by ring
    _ ≤ (b - a) / (a + b) * 1 - 0 := by
        gcongr
        · linarith
    _ ≤ (b - a) / a := by linarith

/-- **`(FGP.3)`, strict sign**: `0 < -ab ω_t(a,b)` for `0 < a < b`, `t > 0`. -/
theorem neg_defect_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) {t : ℝ} (ht : 0 < t) :
    0 < -(a * b * defectKernel t a b) := by
  have hb : 0 < b := ha.trans hab
  have h := defectKernel_pos ht hab
  rw [defectKernel_swap] at h
  nlinarith [mul_pos ha hb]

/-- **`(FGP.4)`: the infinite-horizon value** `ab ω_t(a,b) → (a - b)/(a + b)`. -/
theorem tendsto_defect_atTop {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun t => a * b * defectKernel t a b) atTop (𝓝 ((a - b) / (a + b))) := by
  have hexp : ∀ c : ℝ, 0 < c → Tendsto (fun t : ℝ => Real.exp (-c * t)) atTop (𝓝 0) :=
    fun c hc => by
      have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
      simpa [Function.comp_def, neg_mul] using this
  have h := ((tendsto_const_nhds (x := (a - b) / (a + b))).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (hexp (a + b) (by positivity)))).add
      (hexp a ha) |>.sub (hexp b hb)
  simp only [sub_zero, mul_one, add_zero] at h
  exact h.congr fun t => (defectKernel_closed ha hb t).symm

/-- **`(FGP.4a)`: the formation-time Laplace transform**
`∫₀^∞ e^{-zt} ab ω_t(a,b) dt = ab(a-b)/(z(z+a)(z+b)(z+a+b))`, `Re z > 0`. -/
theorem laplace_defect {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-z * t) * ((a * b * defectKernel t a b : ℝ) : ℂ) =
      (a * b * (a - b) : ℂ) / (z * (z + a) * (z + b) * (z + a + b)) := by
  have hexp : ∀ c : ℂ, 0 < c.re → IntegrableOn (fun t : ℝ => Complex.exp (-c * t)) (Ioi 0) :=
    fun c hc => integrableOn_exp_mul_complex_Ioi (by simpa using hc) 0
  have hint : ∀ c : ℂ, 0 < c.re → ∫ t in Ioi (0 : ℝ), Complex.exp (-c * t) = 1 / c :=
    fun c hc => by
      rw [integral_exp_mul_complex_Ioi (by simpa using hc) 0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      have hc0 : c ≠ 0 := fun h => by simp [h] at hc
      field_simp
  have hs : 0 < (z + (a + b : ℝ)).re := by simp; linarith [ha, hb]
  have hsa : 0 < (z + (a : ℝ)).re := by simp; linarith
  have hsb : 0 < (z + (b : ℝ)).re := by simp; linarith
  have hpt : ∀ t : ℝ, Complex.exp (-z * t) * ((a * b * defectKernel t a b : ℝ) : ℂ) =
      ((a - b) / (a + b) : ℝ) * Complex.exp (-z * t) -
        ((a - b) / (a + b) : ℝ) * Complex.exp (-(z + (a + b : ℝ)) * t) +
        Complex.exp (-(z + (a : ℝ)) * t) - Complex.exp (-(z + (b : ℝ)) * t) := fun t => by
    rw [defectKernel_closed ha hb]
    push_cast
    rw [show -(z + ((a : ℂ) + b)) * t = -z * t + (-(a + b) * t) by ring,
      show -(z + (a : ℂ)) * t = -z * t + (-a * t) by ring,
      show -(z + (b : ℂ)) * t = -z * t + (-b * t) by ring, Complex.exp_add, Complex.exp_add,
      Complex.exp_add]
    ring
  simp_rw [hpt]
  set ρ : ℂ := (((a - b) / (a + b) : ℝ) : ℂ)
  have i1 := (hexp z hz).const_mul ρ
  have i2 := (hexp _ hs).const_mul ρ
  have i3 := hexp _ hsa
  have i4 := hexp _ hsb
  rw [integral_sub (f := fun t : ℝ => ρ * Complex.exp (-z * t) -
        ρ * Complex.exp (-(z + (a + b : ℝ)) * t) + Complex.exp (-(z + (a : ℝ)) * t))
      (g := fun t : ℝ => Complex.exp (-(z + (b : ℝ)) * t)) ((i1.sub i2).add i3) i4,
    integral_add (f := fun t : ℝ => ρ * Complex.exp (-z * t) -
        ρ * Complex.exp (-(z + (a + b : ℝ)) * t))
      (g := fun t : ℝ => Complex.exp (-(z + (a : ℝ)) * t)) (i1.sub i2) i3,
    integral_sub (f := fun t : ℝ => ρ * Complex.exp (-z * t))
      (g := fun t : ℝ => ρ * Complex.exp (-(z + (a + b : ℝ)) * t)) i1 i2,
    integral_const_mul, integral_const_mul, hint z hz, hint _ hs, hint _ hsa, hint _ hsb]
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h1 : z + (a + b : ℝ) ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have h2 : z + (a : ℝ) ≠ 0 := fun h => by rw [h] at hsa; simp at hsa
  have h3 : z + (b : ℝ) ≠ 0 := fun h => by rw [h] at hsb; simp at hsb
  have hab : (a : ℂ) + b ≠ 0 := by exact_mod_cast (by positivity : a + b ≠ 0)
  simp only [ρ]
  push_cast at h1 h2 h3 ⊢
  have h4 : (a : ℂ) + b + z ≠ 0 := fun h => h1 (by linear_combination h)
  have h5 : z + a + b ≠ 0 := fun h => h1 (by linear_combination h)
  field_simp
  ring

/-! ### Formation-time derivatives -/

/-- The `k`-th formation-time derivative of `ab ω_t(a,b)`, as an exponential polynomial. -/
theorem iteratedDeriv_defect {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (fun t => a * b * defectKernel t a b) t =
      ((if k = 0 then (a - b) / (a + b) else 0) -
        (a - b) / (a + b) * ((-(a + b)) ^ k * Real.exp (-(a + b) * t))) +
        (-a) ^ k * Real.exp (-a * t) - (-b) ^ k * Real.exp (-b * t) := by
  set ρ := (a - b) / (a + b)
  have hfun : (fun t => a * b * defectKernel t a b) =
      ((fun _ : ℝ => ρ) - (fun t => ρ * Real.exp (-(a + b) * t)) +
        (fun t => Real.exp (-a * t))) - fun t => Real.exp (-b * t) := by
    funext t
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [defectKernel_closed ha hb]
    ring
  have h1 : ContDiff ℝ k (fun _ : ℝ => ρ) := contDiff_const
  have h2 : ContDiff ℝ k (fun t : ℝ => ρ * Real.exp (-(a + b) * t)) := by fun_prop
  have h3 : ContDiff ℝ k (fun t : ℝ => Real.exp (-a * t)) := by fun_prop
  have h4 : ContDiff ℝ k (fun t : ℝ => Real.exp (-b * t)) := by fun_prop
  have he : ContDiff ℝ k (fun t : ℝ => Real.exp (-(a + b) * t)) := by fun_prop
  rw [hfun, iteratedDeriv_sub (f := ((fun _ : ℝ => ρ) - fun t => ρ * Real.exp (-(a + b) * t)) +
      fun t => Real.exp (-a * t)) (g := fun t => Real.exp (-b * t))
      ((h1.sub h2).add h3).contDiffAt h4.contDiffAt,
    iteratedDeriv_add (f := (fun _ : ℝ => ρ) - fun t => ρ * Real.exp (-(a + b) * t))
      (g := fun t => Real.exp (-a * t)) (h1.sub h2).contDiffAt h3.contDiffAt,
    iteratedDeriv_sub (f := fun _ : ℝ => ρ) (g := fun t => ρ * Real.exp (-(a + b) * t))
      h1.contDiffAt h2.contDiffAt,
    iteratedDeriv_const, iteratedDeriv_const_mul _ he.contDiffAt, iteratedDeriv_exp_const_mul,
    iteratedDeriv_exp_const_mul, iteratedDeriv_exp_const_mul]

theorem mul_exp_neg_le_one (x : ℝ) : x * Real.exp (-x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have hpos := Real.exp_pos x
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hpos]
  linarith

/-- The scale mean value estimate `|a^k e^{-at} - b^k e^{-bt}| ≤ (k+1) 2^k a^{k-1} (b - a)`. -/
theorem scale_difference_le {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb2 : b ≤ 2 * a)
    (ht : 0 ≤ t) (k : ℕ) :
    |a ^ k * Real.exp (-a * t) - b ^ k * Real.exp (-b * t)| ≤
      (k + 1) * 2 ^ k * a ^ ((k : ℤ) - 1) * (b - a) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst heq
    simp
  set g : ℝ → ℝ := fun c => c ^ k * Real.exp (-c * t)
  set g' : ℝ → ℝ := fun c => ((k : ℝ) * c ^ (k - 1) - t * c ^ k) * Real.exp (-c * t)
  have hg : ∀ c, HasDerivAt g (g' c) c := fun c => by
    have h1 := hasDerivAt_pow k c
    have h2 := ((hasDerivAt_neg c).mul_const t).exp
    refine (h1.mul h2).congr_deriv ?_
    simp only [g']
    ring
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g g' hlt
    (fun c _ => (hg c).continuousAt.continuousWithinAt) (fun c _ => hg c)
  have hc0 : 0 < c := ha.trans hc.1
  have hct : c * t * Real.exp (-c * t) ≤ 1 := by
    have h := mul_exp_neg_le_one (c * t)
    rwa [show -(c * t) = -c * t by ring] at h
  have hgc : |g' c| ≤ (k + 1) * c ^ ((k : ℤ) - 1) := by
    have he : 0 < Real.exp (-c * t) := Real.exp_pos _
    rcases k with _ | k
    · have hg0 : g' c = -(t * Real.exp (-c * t)) := by simp [g']
      rw [hg0, abs_neg, abs_of_nonneg (by positivity)]
      simp only [CharP.cast_eq_zero, zero_add, one_mul, zero_sub, Int.reduceNeg, zpow_neg_one]
      rw [← one_div, le_div_iff₀ hc0]
      nlinarith [hct]
    · have hzk : c ^ (((k + 1 : ℕ) : ℤ) - 1) = c ^ k := by
        rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, zpow_natCast]
      rw [hzk]
      simp only [g', Nat.add_sub_cancel]
      rw [abs_mul, abs_of_pos he]
      have hct' : t * c ^ (k + 1) * Real.exp (-c * t) ≤ c ^ k := by
        have : t * c ^ (k + 1) * Real.exp (-c * t) = c ^ k * (c * t * Real.exp (-c * t)) := by
          ring
        rw [this]
        exact mul_le_of_le_one_right (by positivity) hct
      have hexp1 : Real.exp (-c * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      calc |((k + 1 : ℕ) : ℝ) * c ^ k - t * c ^ (k + 1)| * Real.exp (-c * t)
          ≤ (((k + 1 : ℕ) : ℝ) * c ^ k + t * c ^ (k + 1)) * Real.exp (-c * t) := by
            gcongr
            exact (abs_sub _ _).trans (by
              rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)])
        _ = ((k + 1 : ℕ) : ℝ) * c ^ k * Real.exp (-c * t) +
              t * c ^ (k + 1) * Real.exp (-c * t) := by ring
        _ ≤ ((k + 1 : ℕ) : ℝ) * c ^ k * 1 + c ^ k := by
            gcongr
        _ = ((k + 1 : ℕ) + 1 : ℝ) * c ^ k := by push_cast; ring
  have hcmp : c ^ ((k : ℤ) - 1) ≤ 2 ^ k * a ^ ((k : ℤ) - 1) := by
    rcases k with _ | k
    · simp only [CharP.cast_eq_zero, zero_sub, Int.reduceNeg, zpow_neg_one, pow_zero, one_mul]
      exact inv_anti₀ ha hc.1.le
    · rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast]
      calc c ^ k ≤ (2 * a) ^ k := pow_le_pow_left₀ hc0.le (hc.2.le.trans hb2) k
        _ = 2 ^ k * a ^ k := mul_pow _ _ _
        _ ≤ 2 ^ (k + 1) * a ^ k := by gcongr <;> norm_num
  have hdiff : g b - g a = g' c * (b - a) := by
    rw [hslope]
    field_simp [(sub_pos.mpr hlt).ne']
  calc |a ^ k * Real.exp (-a * t) - b ^ k * Real.exp (-b * t)| = |g b - g a| := by
        rw [abs_sub_comm]
    _ = |g' c| * (b - a) := by rw [hdiff, abs_mul, abs_of_pos (sub_pos.mpr hlt)]
    _ ≤ (k + 1) * (2 ^ k * a ^ ((k : ℤ) - 1)) * (b - a) := by
        gcongr
        exact hgc.trans (mul_le_mul_of_nonneg_left hcmp (by positivity))
    _ = (k + 1) * 2 ^ k * a ^ ((k : ℤ) - 1) * (b - a) := by ring

/-- The constant of `(FGP.4b)`. -/
def derivConst (k : ℕ) : ℝ := 3 ^ k + (k + 1) * 2 ^ k

theorem derivConst_pos (k : ℕ) : 0 < derivConst k := by unfold derivConst; positivity

/-- **`(FGP.4b)`: finite time differentiation keeps the relative factor**:
`|∂_t^k (ab ω_t(a,b))| ≤ C_k a^{k-1} (b - a)` for `0 < a ≤ b ≤ 2a`, `t ≥ 0`. -/
theorem abs_iteratedDeriv_defect_le {a b t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb2 : b ≤ 2 * a)
    (ht : 0 ≤ t) (k : ℕ) :
    |iteratedDeriv k (fun t => a * b * defectKernel t a b) t| ≤
      derivConst k * a ^ ((k : ℤ) - 1) * (b - a) := by
  have hb : 0 < b := ha.trans_le hab
  set ρ := (a - b) / (a + b)
  have hρ : |ρ| = (b - a) / (a + b) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < a + b), abs_sub_comm,
      abs_of_nonneg (by linarith)]
  have hE : 0 < Real.exp (-(a + b) * t) := Real.exp_pos _
  have hE1 : Real.exp (-(a + b) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hB : |(-a) ^ k * Real.exp (-a * t) - (-b) ^ k * Real.exp (-b * t)| ≤
      (k + 1) * 2 ^ k * a ^ ((k : ℤ) - 1) * (b - a) := by
    rw [neg_pow a, neg_pow b, mul_assoc, mul_assoc, ← mul_sub, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul]
    exact scale_difference_le ha hab hb2 ht k
  have hA : |(if k = 0 then ρ else 0) - ρ * ((-(a + b)) ^ k * Real.exp (-(a + b) * t))| ≤
      3 ^ k * a ^ ((k : ℤ) - 1) * (b - a) := by
    rcases k with _ | k
    · simp only [if_true, pow_zero, one_mul, CharP.cast_eq_zero, zero_sub, Int.reduceNeg,
        zpow_neg_one]
      rw [show ρ - ρ * Real.exp (-(a + b) * t) = ρ * (1 - Real.exp (-(a + b) * t)) by ring,
        abs_mul, hρ, abs_of_nonneg (sub_nonneg.mpr hE1)]
      calc (b - a) / (a + b) * (1 - Real.exp (-(a + b) * t)) ≤ (b - a) / (a + b) * 1 := by
            gcongr
            linarith
        _ ≤ (b - a) / a := by
            rw [mul_one]
            exact div_le_div_of_nonneg_left (by linarith) ha (by linarith)
        _ = a⁻¹ * (b - a) := by ring
    · simp only [Nat.succ_ne_zero, if_false, zero_sub, abs_neg]
      rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring, zpow_natCast, abs_mul, abs_mul,
        abs_pow, abs_neg, abs_of_pos (by positivity : 0 < a + b), abs_of_pos hE, hρ]
      calc (b - a) / (a + b) * ((a + b) ^ (k + 1) * Real.exp (-(a + b) * t))
          ≤ (b - a) / (a + b) * ((a + b) ^ (k + 1) * 1) := by
            gcongr
        _ = (b - a) * (a + b) ^ k := by
            field_simp
            ring
        _ ≤ (b - a) * (3 * a) ^ k := by
            gcongr
            linarith
        _ = 3 ^ k * a ^ k * (b - a) := by rw [mul_pow]; ring
        _ ≤ 3 ^ (k + 1) * a ^ k * (b - a) := by
            gcongr
            · norm_num
            · omega
  rw [iteratedDeriv_defect ha hb k t]
  calc |(if k = 0 then ρ else 0) - ρ * ((-(a + b)) ^ k * Real.exp (-(a + b) * t)) +
        (-a) ^ k * Real.exp (-a * t) - (-b) ^ k * Real.exp (-b * t)|
      = |((if k = 0 then ρ else 0) - ρ * ((-(a + b)) ^ k * Real.exp (-(a + b) * t))) +
          ((-a) ^ k * Real.exp (-a * t) - (-b) ^ k * Real.exp (-b * t))| := by ring_nf
    _ ≤ 3 ^ k * a ^ ((k : ℤ) - 1) * (b - a) + (k + 1) * 2 ^ k * a ^ ((k : ℤ) - 1) * (b - a) :=
        (abs_add_le _ _).trans (add_le_add hA hB)
    _ = derivConst k * a ^ ((k : ℤ) - 1) * (b - a) := by unfold derivConst; ring

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
