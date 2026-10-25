import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryPositivity

/-!
# Progression models: one-prime boundary data

The weights `h e^{−(hn+c)x}` on the frequencies `hn + c` (`n ≥ 0`, step `h > 0`, offset `c`) are the
log-derivative coefficients of a single geometric Euler factor. Their boundary divisor is
`D(u) = cos(cu)` on the lattice `(2π/h)ℤ` and `0` off it (`progression_isBoundaryDivisor`).

* On the lattice the frequencies collapse to `cos(cu)`, and the geometric mass `x h e^{−cx}/(1 − e^{−hx})`
  tends to `1` (`tendsto_progression_mass`).
* Off the lattice `e^{−ihu} ≠ 1`, so the closed form `h e^{−cw}/(1 − e^{−hw})`, `w = x + iu`, stays
  bounded as `x ↓ 0` (`tendsto_progression_off`).

Two choices give integer divisors (`lattice_isBoundaryDivisor`, `alternating_isBoundaryDivisor`).
With `c = h` the divisor is the lattice indicator `1_{(2π/h)ℤ}`: the simple periodic poles of
`(1 − e^{−h(s−1)})^{−1}`. With `c = h/2` it alternates: `D(k·2π/h) = (−1)^k`, the poles and zeros of
`(1 + e^{−h(s−1)/2})/(1 − e^{−h(s−1)/2})`. Together with `D_ζ = 1_{0}` these realize all three types
of the boundary trichotomy.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

variable {h c : ℝ}

/-- Weights `h e^{−(hn+c)x}`. -/
noncomputable def progressionWeight (h c x : ℝ) (n : ℕ) : ℝ := h * Real.exp (-((h * n + c) * x))

/-- Frequencies `hn + c`. -/
noncomputable def progressionFrequency (h c : ℝ) (n : ℕ) : ℝ := h * n + c

open Classical in
/-- `cos(cu)` on the lattice `(2π/h)ℤ`, zero off it. -/
noncomputable def progressionDivisor (h c u : ℝ) : ℝ :=
  if ∃ m : ℤ, u = m * (2 * Real.pi / h) then Real.cos (c * u) else 0

/-- Closed form `e^{−cw}/(1 − e^{−hw})` of the complex trace at `w = x + iu`. -/
noncomputable def progressionKernel (h c x u : ℝ) : ℂ :=
  Complex.exp (-(c : ℂ) * ((x : ℂ) + (u : ℂ) * I)) /
    (1 - Complex.exp (-(h : ℂ) * ((x : ℂ) + (u : ℂ) * I)))

theorem progressionWeight_nonneg (hh : 0 < h) (x : ℝ) (n : ℕ) : 0 ≤ progressionWeight h c x n :=
  mul_nonneg hh.le (Real.exp_pos _).le

theorem hasSum_progressionWeight (hh : 0 < h) {x : ℝ} (hx : 0 < x) :
    HasSum (progressionWeight h c x)
      (h * Real.exp (-(c * x)) * (1 - Real.exp (-(h * x)))⁻¹) := by
  have hr0 : 0 ≤ Real.exp (-(h * x)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(h * x)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have heq : progressionWeight h c x =
      fun n : ℕ => h * Real.exp (-(c * x)) * Real.exp (-(h * x)) ^ n := by
    funext n
    unfold progressionWeight
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq]
  exact (hasSum_geometric_of_lt_one hr0 hr1).mul_left _

private theorem re_exp_neg_mul (a x u : ℝ) :
    (Complex.exp (-(a : ℂ) * ((x : ℂ) + (u : ℂ) * I))).re =
      Real.exp (-(a * x)) * Real.cos (a * u) := by
  rw [Complex.exp_re]
  have hre : (-(a : ℂ) * ((x : ℂ) + (u : ℂ) * I)).re = -(a * x) := by simp
  have him : (-(a : ℂ) * ((x : ℂ) + (u : ℂ) * I)).im = -(a * u) := by simp
  rw [hre, him, Real.cos_neg]

theorem hasSum_progression_complex (hh : 0 < h) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    HasSum (fun n : ℕ => Complex.exp (-((h * n + c : ℝ) : ℂ) * ((x : ℂ) + (u : ℂ) * I)))
      (progressionKernel h c x u) := by
  set q := Complex.exp (-(h : ℂ) * ((x : ℂ) + (u : ℂ) * I)) with hq
  have hqn : ‖q‖ < 1 := by
    rw [hq, Complex.norm_exp]
    have : (-(h : ℂ) * ((x : ℂ) + (u : ℂ) * I)).re = -(h * x) := by simp
    rw [this, Real.exp_lt_one_iff]
    nlinarith
  have heq : (fun n : ℕ => Complex.exp (-((h * n + c : ℝ) : ℂ) * ((x : ℂ) + (u : ℂ) * I))) =
      fun n : ℕ => Complex.exp (-(c : ℂ) * ((x : ℂ) + (u : ℂ) * I)) * q ^ n := by
    funext n
    rw [hq, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold progressionKernel
  rw [div_eq_mul_inv, ← hq, heq]
  exact (hasSum_geometric_of_norm_lt_one hqn).mul_left _

/-- The real cosine trace is `h · Re` of the closed form. -/
theorem progression_trace_eq (hh : 0 < h) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    cosineTrace (progressionWeight h c x) (progressionFrequency h c) u =
      h * (progressionKernel h c x u).re := by
  have hre : HasSum (fun n : ℕ => Real.exp (-((h * n + c) * x)) * Real.cos ((h * n + c) * u))
      (progressionKernel h c x u).re := by
    have := Complex.reCLM.hasSum (hasSum_progression_complex (c := c) hh hx u)
    simpa only [Complex.reCLM_apply, re_exp_neg_mul] using this
  unfold cosineTrace progressionWeight progressionFrequency
  rw [← (hre.mul_left h).tsum_eq]
  exact tsum_congr fun n => by ring

/-- On the lattice every frequency gives the same phase `cos(cu)`. -/
theorem progression_trace_lattice (hh : 0 < h) {x : ℝ} (hx : 0 < x) (m : ℤ) :
    cosineTrace (progressionWeight h c x) (progressionFrequency h c) (m * (2 * Real.pi / h)) =
      Real.cos (c * (m * (2 * Real.pi / h))) *
        (h * Real.exp (-(c * x)) * (1 - Real.exp (-(h * x)))⁻¹) := by
  unfold cosineTrace
  rw [← ((hasSum_progressionWeight (c := c) hh hx).mul_left
    (Real.cos (c * (m * (2 * Real.pi / h))))).tsum_eq]
  refine tsum_congr fun n => ?_
  unfold progressionFrequency
  have e : (h * n + c) * (m * (2 * Real.pi / h)) =
      c * (m * (2 * Real.pi / h)) + ((n * m : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp
    ring
  rw [e, Real.cos_add_int_mul_two_pi]
  ring

/-- The geometric mass `x h e^{−cx}/(1 − e^{−hx})` tends to `1` as `x ↓ 0`. -/
theorem tendsto_progression_mass (hh : 0 < h) (c : ℝ) :
    Tendsto (fun x : ℝ => x * (h * Real.exp (-(c * x)) * (1 - Real.exp (-(h * x)))⁻¹))
      (𝓝[>] 0) (𝓝 1) := by
  have hderiv : HasDerivAt (fun x : ℝ => 1 - Real.exp (-(h * x))) h 0 := by
    have h1 : HasDerivAt (fun x : ℝ => -(h * x)) (-(h * 1)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul h).neg
    have h2 := h1.exp.const_sub 1
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, one_mul, neg_neg] at h2
    exact h2
  have hslope : Tendsto (fun x : ℝ => (1 - Real.exp (-(h * x))) / x) (𝓝[≠] 0) (𝓝 h) := by
    refine (hasDerivAt_iff_tendsto_slope.mp hderiv).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x _
    rw [slope_def_field]
    simp
  have hinv : Tendsto (fun x : ℝ => x / (1 - Real.exp (-(h * x)))) (𝓝[≠] 0) (𝓝 h⁻¹) := by
    simpa only [inv_div] using hslope.inv₀ hh.ne'
  have hexp : Tendsto (fun x : ℝ => h * Real.exp (-(c * x))) (𝓝[≠] 0) (𝓝 h) := by
    have hc : Continuous (fun x : ℝ => h * Real.exp (-(c * x))) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hprod := (hexp.mul hinv).mono_left
    (nhdsWithin_mono (0 : ℝ) (fun x (hx : 0 < x) => (ne_of_gt hx : x ≠ 0)))
  rw [mul_inv_cancel₀ hh.ne'] at hprod
  refine hprod.congr' (Eventually.of_forall fun x => ?_)
  ring

/-- Off the lattice the closed form is continuous at `x = 0`, so the boundary limit is `0`. -/
theorem tendsto_progression_off (hh : 0 < h) {u : ℝ}
    (hu : ¬ ∃ m : ℤ, u = m * (2 * Real.pi / h)) :
    Tendsto (fun x => x * cosineTrace (progressionWeight h c x) (progressionFrequency h c) u)
      (𝓝[>] 0) (𝓝 0) := by
  have hden : (1 : ℂ) - Complex.exp (-(h : ℂ) * (((0 : ℝ) : ℂ) + (u : ℂ) * I)) ≠ 0 := by
    intro h0
    have h1 : Complex.exp (-(h : ℂ) * (((0 : ℝ) : ℂ) + (u : ℂ) * I)) = 1 := by
      linear_combination -h0
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    apply hu
    refine ⟨-n, ?_⟩
    have him := congrArg Complex.im hn
    simp at him
    push_cast
    field_simp
    linarith
  have hnum : Continuous (fun x : ℝ => Complex.exp (-(c : ℂ) * ((x : ℂ) + (u : ℂ) * I))) := by
    fun_prop
  have hd : Continuous (fun x : ℝ => (1 : ℂ) - Complex.exp (-(h : ℂ) * ((x : ℂ) + (u : ℂ) * I))) := by
    fun_prop
  have hcont : ContinuousAt (fun x : ℝ => x * (h * (progressionKernel h c x u).re)) 0 := by
    unfold progressionKernel
    exact continuousAt_id.mul (continuousAt_const.mul
      (Complex.continuous_re.continuousAt.comp (hnum.continuousAt.div hd.continuousAt hden)))
  have hlim : Tendsto (fun x : ℝ => x * (h * (progressionKernel h c x u).re)) (𝓝[>] 0) (𝓝 0) := by
    have := hcont.tendsto
    simp only [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [progression_trace_eq hh (Set.mem_Ioi.mp hx) u]

/-- **Progression boundary datum.** -/
theorem progression_isBoundaryDivisor (hh : 0 < h) (c : ℝ) :
    IsBoundaryDivisor (progressionFrequency h c) (progressionWeight h c)
      (progressionDivisor h c) where
  nonneg x _ n := progressionWeight_nonneg hh x n
  summable x hx := (hasSum_progressionWeight hh hx).summable
  tendsto u := by
    by_cases hu : ∃ m : ℤ, u = m * (2 * Real.pi / h)
    · obtain ⟨m, rfl⟩ := hu
      have hD : progressionDivisor h c (m * (2 * Real.pi / h)) =
          Real.cos (c * (m * (2 * Real.pi / h))) := by
        unfold progressionDivisor
        rw [if_pos ⟨m, rfl⟩]
      rw [hD]
      have := (tendsto_progression_mass hh c).const_mul (Real.cos (c * (m * (2 * Real.pi / h))))
      rw [mul_one] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [progression_trace_lattice hh (Set.mem_Ioi.mp hx) m]
      ring
    · have hD : progressionDivisor h c u = 0 := by
        unfold progressionDivisor
        rw [if_neg hu]
      rw [hD]
      exact tendsto_progression_off hh hu

/-! ### The integer progression divisors -/

open Classical in
/-- **Periodic simple poles.** With `c = h` the divisor is the indicator of `(2π/h)ℤ`. -/
theorem lattice_isBoundaryDivisor (hh : 0 < h) :
    IsBoundaryDivisor (progressionFrequency h h) (progressionWeight h h)
      (fun u => if ∃ m : ℤ, u = m * (2 * Real.pi / h) then 1 else 0) := by
  convert progression_isBoundaryDivisor hh h using 1
  funext u
  unfold progressionDivisor
  split_ifs with hu
  · obtain ⟨m, rfl⟩ := hu
    have e : h * (m * (2 * Real.pi / h)) = 0 + (m : ℝ) * (2 * Real.pi) := by field_simp; ring
    rw [e, Real.cos_add_int_mul_two_pi, Real.cos_zero]
  · rfl

/-- **Alternating poles and zeros.** With `c = h/2` the divisor alternates on `(2π/h)ℤ`. -/
theorem alternating_isBoundaryDivisor (hh : 0 < h) :
    IsBoundaryDivisor (progressionFrequency h (h / 2)) (progressionWeight h (h / 2))
      (progressionDivisor h (h / 2)) ∧
    (∀ k : ℤ, progressionDivisor h (h / 2) (k * (2 * Real.pi / h)) = (-1) ^ k.natAbs) ∧
    ∀ u, (¬ ∃ k : ℤ, u = k * (2 * Real.pi / h)) → progressionDivisor h (h / 2) u = 0 := by
  refine ⟨progression_isBoundaryDivisor hh _, fun k => ?_, fun u hu => ?_⟩
  · unfold progressionDivisor
    rw [if_pos ⟨k, rfl⟩]
    have e : h / 2 * (k * (2 * Real.pi / h)) = (k : ℝ) * Real.pi := by field_simp
    rw [e, Real.cos_int_mul_pi]
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · simp
    · simp only [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg,
        zpow_natCast]
      rw [← inv_pow, inv_neg, inv_one]
  · unfold progressionDivisor
    rw [if_neg hu]

end GaloisForLFunctions.MultiplicativePositivityGeometry
