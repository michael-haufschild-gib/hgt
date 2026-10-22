import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninTimeBandKernel

/-!
# The time-band scaling trace is `C²` with unit slope

`T(u) = ∫₀¹∫₀¹ 4 cos(2π x z) e^{u/2} cos(2π e^u x z)` is differentiated twice under the integral
over the unit square (bounded integrands on a finite measure).  At `u = 0` the derivative is an
exact derivative in the inner variable,

`4 cos(2πs)(½ cos(2πs) - 2πs sin(2πs)) = ∂_z (2 z cos²(2π x z))`,  `s = x z`,

so `T'(0) = ∫₀¹ 2 cos²(2πx) dx = 1`.  The second derivative is bounded on bounded sets.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-! ## The scaling profile and its derivatives -/

/-- `e^{u/2} cos(2π e^u s)`. -/
def ccmScalingProfile (u s : ℝ) : ℝ :=
  Real.exp (u / 2) * Real.cos (2 * Real.pi * Real.exp u * s)

/-- `∂_u` of the scaling profile. -/
def ccmScalingProfile' (u s : ℝ) : ℝ :=
  Real.exp (u / 2) * (1 / 2 * Real.cos (2 * Real.pi * Real.exp u * s) -
    2 * Real.pi * s * Real.exp u * Real.sin (2 * Real.pi * Real.exp u * s))

/-- `∂_u²` of the scaling profile. -/
def ccmScalingProfile'' (u s : ℝ) : ℝ :=
  Real.exp (u / 2) * (1 / 4 * Real.cos (2 * Real.pi * Real.exp u * s) -
    4 * Real.pi * s * Real.exp u * Real.sin (2 * Real.pi * Real.exp u * s) -
      4 * Real.pi ^ 2 * s ^ 2 * Real.exp u ^ 2 * Real.cos (2 * Real.pi * Real.exp u * s))

theorem hasDerivAt_ccmScalingProfile (u s : ℝ) :
    HasDerivAt (fun v => ccmScalingProfile v s) (ccmScalingProfile' u s) u := by
  have h1 : HasDerivAt (fun v => Real.exp (v / 2)) (Real.exp (u / 2) * (1 / 2)) u := by
    have := ((hasDerivAt_id u).div_const 2).exp
    simpa using this
  have h2 : HasDerivAt (fun v => 2 * Real.pi * Real.exp v * s) (2 * Real.pi * Real.exp u * s) u := by
    have := ((Real.hasDerivAt_exp u).const_mul (2 * Real.pi)).mul_const s
    simpa using this
  have h3 := h2.cos
  have := h1.mul h3
  unfold ccmScalingProfile ccmScalingProfile'
  exact this.congr_deriv (by ring)

theorem hasDerivAt_ccmScalingProfile' (u s : ℝ) :
    HasDerivAt (fun v => ccmScalingProfile' v s) (ccmScalingProfile'' u s) u := by
  have h1 : HasDerivAt (fun v => Real.exp (v / 2)) (Real.exp (u / 2) * (1 / 2)) u := by
    have := ((hasDerivAt_id u).div_const 2).exp
    simpa using this
  have h2 : HasDerivAt (fun v => 2 * Real.pi * Real.exp v * s) (2 * Real.pi * Real.exp u * s) u := by
    have := ((Real.hasDerivAt_exp u).const_mul (2 * Real.pi)).mul_const s
    simpa using this
  have hc := h2.cos
  have hs := h2.sin
  have he := Real.hasDerivAt_exp u
  have hinner : HasDerivAt (fun v => 1 / 2 * Real.cos (2 * Real.pi * Real.exp v * s) -
      2 * Real.pi * s * Real.exp v * Real.sin (2 * Real.pi * Real.exp v * s))
      (1 / 2 * (-Real.sin (2 * Real.pi * Real.exp u * s) * (2 * Real.pi * Real.exp u * s)) -
        (2 * Real.pi * s * Real.exp u * Real.sin (2 * Real.pi * Real.exp u * s) +
          2 * Real.pi * s * Real.exp u *
            (Real.cos (2 * Real.pi * Real.exp u * s) * (2 * Real.pi * Real.exp u * s)))) u := by
    refine (hc.const_mul (1 / 2)).sub ?_
    have := (he.const_mul (2 * Real.pi * s)).mul hs
    exact this.congr_deriv (by ring)
  have := h1.mul hinner
  unfold ccmScalingProfile' ccmScalingProfile''
  exact this.congr_deriv (by ring)

theorem abs_ccmScalingProfile'_le {u s R : ℝ} (hu : |u| ≤ R) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |ccmScalingProfile' u s| ≤ Real.exp R * (1 + 2 * Real.pi * Real.exp R) := by
  have hR : 0 ≤ R := (abs_nonneg u).trans hu
  have he2 : Real.exp (u / 2) ≤ Real.exp R :=
    Real.exp_le_exp.mpr (by linarith [neg_abs_le u, le_abs_self u])
  have he : Real.exp u ≤ Real.exp R := Real.exp_le_exp.mpr ((le_abs_self u).trans hu)
  have hc := Real.abs_cos_le_one (2 * Real.pi * Real.exp u * s)
  have hsn := Real.abs_sin_le_one (2 * Real.pi * Real.exp u * s)
  unfold ccmScalingProfile'
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hin : |1 / 2 * Real.cos (2 * Real.pi * Real.exp u * s) -
      2 * Real.pi * s * Real.exp u * Real.sin (2 * Real.pi * Real.exp u * s)| ≤
        1 + 2 * Real.pi * Real.exp R := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * s * Real.exp u)]
    have h1 : 2 * Real.pi * s * Real.exp u ≤ 2 * Real.pi * Real.exp R := by
      have := mul_le_mul hs1 he (Real.exp_pos u).le zero_le_one
      nlinarith [Real.pi_pos]
    nlinarith [abs_nonneg (Real.sin (2 * Real.pi * Real.exp u * s)),
      abs_nonneg (Real.cos (2 * Real.pi * Real.exp u * s)), Real.pi_pos,
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) hs0) (Real.exp_pos u).le]
  exact mul_le_mul he2 hin (abs_nonneg _) (Real.exp_pos R).le

theorem abs_ccmScalingProfile''_le {u s R : ℝ} (hu : |u| ≤ R) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |ccmScalingProfile'' u s| ≤
      Real.exp R * (1 + 4 * Real.pi * Real.exp R + 4 * Real.pi ^ 2 * Real.exp R ^ 2) := by
  have hR : 0 ≤ R := (abs_nonneg u).trans hu
  have he2 : Real.exp (u / 2) ≤ Real.exp R :=
    Real.exp_le_exp.mpr (by linarith [neg_abs_le u, le_abs_self u])
  have he : Real.exp u ≤ Real.exp R := Real.exp_le_exp.mpr ((le_abs_self u).trans hu)
  have hc := Real.abs_cos_le_one (2 * Real.pi * Real.exp u * s)
  have hsn := Real.abs_sin_le_one (2 * Real.pi * Real.exp u * s)
  set C := Real.cos (2 * Real.pi * Real.exp u * s)
  set S := Real.sin (2 * Real.pi * Real.exp u * s)
  unfold ccmScalingProfile''
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |4 * Real.pi * s * Real.exp u * S| ≤ 4 * Real.pi * Real.exp R := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * Real.pi * s * Real.exp u)]
    have : 4 * Real.pi * s * Real.exp u ≤ 4 * Real.pi * Real.exp R := by
      have := mul_le_mul hs1 he (Real.exp_pos u).le zero_le_one
      nlinarith [Real.pi_pos]
    calc 4 * Real.pi * s * Real.exp u * |S| ≤ 4 * Real.pi * s * Real.exp u * 1 :=
          mul_le_mul_of_nonneg_left hsn (by positivity)
      _ ≤ _ := by linarith
  have h2 : |4 * Real.pi ^ 2 * s ^ 2 * Real.exp u ^ 2 * C| ≤ 4 * Real.pi ^ 2 * Real.exp R ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * Real.pi ^ 2 * s ^ 2 * Real.exp u ^ 2)]
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    have he2' : Real.exp u ^ 2 ≤ Real.exp R ^ 2 := pow_le_pow_left₀ (Real.exp_pos u).le he 2
    have : 4 * Real.pi ^ 2 * s ^ 2 * Real.exp u ^ 2 ≤ 4 * Real.pi ^ 2 * Real.exp R ^ 2 := by
      have := mul_le_mul hs2 he2' (by positivity) zero_le_one
      nlinarith [Real.pi_pos, sq_nonneg Real.pi]
    calc 4 * Real.pi ^ 2 * s ^ 2 * Real.exp u ^ 2 * |C| ≤
          4 * Real.pi ^ 2 * s ^ 2 * Real.exp u ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ _ := by linarith
  have h0 : |1 / 4 * C| ≤ 1 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]; linarith
  have hin : |1 / 4 * C - 4 * Real.pi * s * Real.exp u * S -
      4 * Real.pi ^ 2 * s ^ 2 * Real.exp u ^ 2 * C| ≤
        1 + 4 * Real.pi * Real.exp R + 4 * Real.pi ^ 2 * Real.exp R ^ 2 := by
    calc _ ≤ |1 / 4 * C - 4 * Real.pi * s * Real.exp u * S| +
          |4 * Real.pi ^ 2 * s ^ 2 * Real.exp u ^ 2 * C| := abs_sub _ _
      _ ≤ (|1 / 4 * C| + |4 * Real.pi * s * Real.exp u * S|) +
          |4 * Real.pi ^ 2 * s ^ 2 * Real.exp u ^ 2 * C| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  exact mul_le_mul he2 hin (abs_nonneg _) (Real.exp_pos R).le

/-! ## Differentiation under the integral over the unit square -/

/-- Lebesgue measure on the unit square `(0, 1]²`. -/
abbrev ccmUnitSquare : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))

instance : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])

theorem ccmUnitSquare_real_univ : ccmUnitSquare.real univ = 1 := by
  rw [Measure.real, ← Set.univ_prod_univ, Measure.prod_prod]
  simp [Real.volume_Ioc]

theorem ae_mem_ccmUnitSquare :
    ∀ᵐ p ∂ccmUnitSquare, p.1 ∈ Ioc (0 : ℝ) 1 ∧ p.2 ∈ Ioc (0 : ℝ) 1 := by
  rw [ccmUnitSquare, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  exact hp

/-- `4 cos(2π x z) · e^{u/2} cos(2π e^u x z)`, the integrand of `T`. -/
def ccmTimeBandIntegrand (u : ℝ) (p : ℝ × ℝ) : ℝ :=
  4 * Real.cos (2 * Real.pi * p.1 * p.2) * ccmScalingProfile u (p.1 * p.2)

def ccmTimeBandIntegrand' (u : ℝ) (p : ℝ × ℝ) : ℝ :=
  4 * Real.cos (2 * Real.pi * p.1 * p.2) * ccmScalingProfile' u (p.1 * p.2)

def ccmTimeBandIntegrand'' (u : ℝ) (p : ℝ × ℝ) : ℝ :=
  4 * Real.cos (2 * Real.pi * p.1 * p.2) * ccmScalingProfile'' u (p.1 * p.2)

/-- Bound for the first `u`-derivative of the integrand on `|v| ≤ |u| + 1`. -/
def ccmTimeBandBound₁ (u : ℝ) : ℝ :=
  4 * (Real.exp (|u| + 1) * (1 + 2 * Real.pi * Real.exp (|u| + 1)))

/-- Bound for the second `u`-derivative of the integrand on `|v| ≤ |u| + 1`. -/
def ccmTimeBandBound₂ (u : ℝ) : ℝ :=
  4 * (Real.exp (|u| + 1) * (1 + 4 * Real.pi * Real.exp (|u| + 1) +
    4 * Real.pi ^ 2 * Real.exp (|u| + 1) ^ 2))

/-- `T'(u)`. -/
def ccmTimeBandTrace' (u : ℝ) : ℝ := ∫ p, ccmTimeBandIntegrand' u p ∂ccmUnitSquare

/-- `T''(u)`. -/
def ccmTimeBandTrace'' (u : ℝ) : ℝ := ∫ p, ccmTimeBandIntegrand'' u p ∂ccmUnitSquare

theorem continuous_ccmTimeBandIntegrand (u : ℝ) : Continuous (ccmTimeBandIntegrand u) := by
  unfold ccmTimeBandIntegrand ccmScalingProfile; fun_prop

theorem continuous_ccmTimeBandIntegrand' (u : ℝ) : Continuous (ccmTimeBandIntegrand' u) := by
  unfold ccmTimeBandIntegrand' ccmScalingProfile'; fun_prop

theorem continuous_ccmTimeBandIntegrand'' (u : ℝ) : Continuous (ccmTimeBandIntegrand'' u) := by
  unfold ccmTimeBandIntegrand'' ccmScalingProfile''; fun_prop

theorem integrable_ccmTimeBandIntegrand (u : ℝ) : Integrable (ccmTimeBandIntegrand u) ccmUnitSquare := by
  refine Integrable.of_bound (continuous_ccmTimeBandIntegrand u).aestronglyMeasurable
    (4 * Real.exp (u / 2)) (Filter.Eventually.of_forall fun p => ?_)
  unfold ccmTimeBandIntegrand ccmScalingProfile
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h1 := Real.abs_cos_le_one (2 * Real.pi * p.1 * p.2)
  have h2 := Real.abs_cos_le_one (2 * Real.pi * Real.exp u * (p.1 * p.2))
  have he := Real.exp_pos (u / 2)
  calc 4 * |Real.cos (2 * Real.pi * p.1 * p.2)| *
        (Real.exp (u / 2) * |Real.cos (2 * Real.pi * Real.exp u * (p.1 * p.2))|)
      ≤ 4 * 1 * (Real.exp (u / 2) * 1) := by gcongr
    _ = _ := by ring

theorem norm_ccmTimeBandIntegrand'_le {u v : ℝ} (hv : |v| ≤ |u| + 1) {p : ℝ × ℝ}
    (hp : p.1 ∈ Ioc (0 : ℝ) 1 ∧ p.2 ∈ Ioc (0 : ℝ) 1) :
    ‖ccmTimeBandIntegrand' v p‖ ≤ ccmTimeBandBound₁ u := by
  have hs0 : 0 ≤ p.1 * p.2 := mul_nonneg hp.1.1.le hp.2.1.le
  have hs1 : p.1 * p.2 ≤ 1 := mul_le_one₀ hp.1.2 hp.2.1.le hp.2.2
  unfold ccmTimeBandIntegrand'
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h1 := Real.abs_cos_le_one (2 * Real.pi * p.1 * p.2)
  have h2 := abs_ccmScalingProfile'_le hv hs0 hs1
  calc 4 * |Real.cos (2 * Real.pi * p.1 * p.2)| * |ccmScalingProfile' v (p.1 * p.2)|
      ≤ 4 * 1 * (Real.exp (|u| + 1) * (1 + 2 * Real.pi * Real.exp (|u| + 1))) := by
        gcongr
    _ = _ := by rw [ccmTimeBandBound₁]; ring

theorem norm_ccmTimeBandIntegrand''_le {u v : ℝ} (hv : |v| ≤ |u| + 1) {p : ℝ × ℝ}
    (hp : p.1 ∈ Ioc (0 : ℝ) 1 ∧ p.2 ∈ Ioc (0 : ℝ) 1) :
    ‖ccmTimeBandIntegrand'' v p‖ ≤ ccmTimeBandBound₂ u := by
  have hs0 : 0 ≤ p.1 * p.2 := mul_nonneg hp.1.1.le hp.2.1.le
  have hs1 : p.1 * p.2 ≤ 1 := mul_le_one₀ hp.1.2 hp.2.1.le hp.2.2
  unfold ccmTimeBandIntegrand''
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have h1 := Real.abs_cos_le_one (2 * Real.pi * p.1 * p.2)
  have h2 := abs_ccmScalingProfile''_le hv hs0 hs1
  calc 4 * |Real.cos (2 * Real.pi * p.1 * p.2)| * |ccmScalingProfile'' v (p.1 * p.2)|
      ≤ 4 * 1 * (Real.exp (|u| + 1) * (1 + 4 * Real.pi * Real.exp (|u| + 1) +
          4 * Real.pi ^ 2 * Real.exp (|u| + 1) ^ 2)) := by gcongr
    _ = _ := by rw [ccmTimeBandBound₂]; ring

theorem abs_le_of_mem_ball {u v : ℝ} (hv : v ∈ Metric.ball u 1) : |v| ≤ |u| + 1 := by
  rw [Metric.mem_ball, Real.dist_eq] at hv
  have := abs_sub_abs_le_abs_sub v u
  linarith

theorem ccmTimeBandTrace_eq_integral (u : ℝ) :
    ccmTimeBandTrace u = ∫ p, ccmTimeBandIntegrand u p ∂ccmUnitSquare := by
  rw [integral_prod _ (integrable_ccmTimeBandIntegrand u)]
  unfold ccmTimeBandTrace
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [ccmTimeBandIntegrand, ccmScalingProfile]
  rw [show 2 * Real.pi * Real.exp u * (x * z) = 2 * Real.pi * Real.exp u * x * z by ring]
  ring

/-- **`T' = ∫ ∂_u`.** -/
theorem hasDerivAt_ccmTimeBandTrace (u : ℝ) :
    HasDerivAt ccmTimeBandTrace (ccmTimeBandTrace' u) u := by
  rw [show ccmTimeBandTrace = fun v => ∫ p, ccmTimeBandIntegrand v p ∂ccmUnitSquare from
    funext ccmTimeBandTrace_eq_integral]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => ccmTimeBandBound₁ u)
    (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall fun v => (continuous_ccmTimeBandIntegrand v).aestronglyMeasurable)
    (integrable_ccmTimeBandIntegrand u) (continuous_ccmTimeBandIntegrand' u).aestronglyMeasurable
    ?_ (integrable_const _) ?_).2
  · filter_upwards [ae_mem_ccmUnitSquare] with p hp v hv
    exact norm_ccmTimeBandIntegrand'_le (abs_le_of_mem_ball hv) hp
  · filter_upwards with p v hv
    exact (hasDerivAt_ccmScalingProfile v (p.1 * p.2)).const_mul _

theorem integrable_ccmTimeBandIntegrand' (u : ℝ) :
    Integrable (ccmTimeBandIntegrand' u) ccmUnitSquare := by
  refine Integrable.of_bound (continuous_ccmTimeBandIntegrand' u).aestronglyMeasurable
    (ccmTimeBandBound₁ u) ?_
  filter_upwards [ae_mem_ccmUnitSquare] with p hp
  exact norm_ccmTimeBandIntegrand'_le (u := u) (le_add_of_nonneg_right zero_le_one) hp

/-- **`T'' = ∫ ∂_u²`.** -/
theorem hasDerivAt_ccmTimeBandTrace' (u : ℝ) :
    HasDerivAt ccmTimeBandTrace' (ccmTimeBandTrace'' u) u := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => ccmTimeBandBound₂ u)
    (Metric.ball_mem_nhds u one_pos)
    (Filter.Eventually.of_forall fun v => (continuous_ccmTimeBandIntegrand' v).aestronglyMeasurable)
    (integrable_ccmTimeBandIntegrand' u) (continuous_ccmTimeBandIntegrand'' u).aestronglyMeasurable
    ?_ (integrable_const _) ?_).2
  · filter_upwards [ae_mem_ccmUnitSquare] with p hp v hv
    exact norm_ccmTimeBandIntegrand''_le (abs_le_of_mem_ball hv) hp
  · filter_upwards with p v hv
    exact (hasDerivAt_ccmScalingProfile' v (p.1 * p.2)).const_mul _

/-- `|T''(v)| ≤ C(u)` for `|v| ≤ |u| + 1`. -/
theorem abs_ccmTimeBandTrace''_le {u v : ℝ} (hv : |v| ≤ |u| + 1) :
    |ccmTimeBandTrace'' v| ≤ ccmTimeBandBound₂ u := by
  have h := norm_integral_le_of_norm_le_const (μ := ccmUnitSquare)
    (f := ccmTimeBandIntegrand'' v) (by
      filter_upwards [ae_mem_ccmUnitSquare] with p hp
      exact norm_ccmTimeBandIntegrand''_le hv hp)
  rw [ccmUnitSquare_real_univ, mul_one, Real.norm_eq_abs] at h
  exact h

theorem continuous_ccmTimeBandTrace'' : Continuous ccmTimeBandTrace'' := by
  rw [continuous_iff_continuousAt]
  intro u
  have hcont : ContinuousOn ccmTimeBandTrace'' (Metric.ball u 1) := by
    refine continuousOn_of_dominated (bound := fun _ => ccmTimeBandBound₂ u)
      (fun v _ => (continuous_ccmTimeBandIntegrand'' v).aestronglyMeasurable)
      (fun v hv => ?_) (integrable_const _) ?_
    · filter_upwards [ae_mem_ccmUnitSquare] with p hp
      exact norm_ccmTimeBandIntegrand''_le (abs_le_of_mem_ball hv) hp
    · filter_upwards with p
      refine Continuous.continuousOn ?_
      unfold ccmTimeBandIntegrand'' ccmScalingProfile''
      fun_prop
  exact hcont.continuousAt (Metric.ball_mem_nhds u one_pos)

/-! ## The unit slope -/

/-- For fixed `x`, the `u = 0` integrand is the `z`-derivative of `2 z cos²(2π x z)`. -/
theorem hasDerivAt_two_mul_cos_sq (x z : ℝ) :
    HasDerivAt (fun z => 2 * z * (Real.cos (2 * Real.pi * x * z) * Real.cos (2 * Real.pi * x * z)))
      (ccmTimeBandIntegrand' 0 (x, z)) z := by
  have hc : HasDerivAt (fun z => Real.cos (2 * Real.pi * x * z))
      (-Real.sin (2 * Real.pi * x * z) * (2 * Real.pi * x)) z := by
    have := ((hasDerivAt_id' z).const_mul (2 * Real.pi * x)).cos
    simpa using this
  have h1 : HasDerivAt (fun z : ℝ => 2 * z) 2 z := by
    simpa using (hasDerivAt_id' z).const_mul (2 : ℝ)
  refine (h1.mul (hc.mul hc)).congr_deriv ?_
  simp only [Pi.mul_apply, ccmTimeBandIntegrand', ccmScalingProfile', Real.exp_zero, zero_div,
    mul_one, one_mul]
  rw [show 2 * Real.pi * (x * z) = 2 * Real.pi * x * z by ring]
  ring

theorem integral_cos_two_pi_sq : ∫ x in Ioc (0 : ℝ) 1, Real.cos (2 * Real.pi * x) ^ 2 = 1 / 2 := by
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2)
      (mul_ne_zero two_ne_zero Real.pi_ne_zero), integral_cos_sq, mul_zero, mul_one,
    Real.sin_two_pi, Real.sin_zero, smul_eq_mul]
  field_simp
  ring

/-- **`T'(0) = 1`.** -/
theorem ccmTimeBandTrace'_zero : ccmTimeBandTrace' 0 = 1 := by
  rw [ccmTimeBandTrace', integral_prod _ (integrable_ccmTimeBandIntegrand' 0)]
  have hin : ∀ x, ∫ z in Ioc (0 : ℝ) 1, ccmTimeBandIntegrand' 0 (x, z) =
      2 * Real.cos (2 * Real.pi * x) ^ 2 := by
    intro x
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hasDerivAt_two_mul_cos_sq x z)
        (((continuous_ccmTimeBandIntegrand' 0).comp (Continuous.prodMk_right x)).intervalIntegrable
          0 1)]
    simp [sq]
  simp_rw [hin]
  rw [integral_const_mul, integral_cos_two_pi_sq]
  norm_num

end RHTower
