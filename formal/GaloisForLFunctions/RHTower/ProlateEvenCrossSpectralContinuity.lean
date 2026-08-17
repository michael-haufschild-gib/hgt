import GaloisForLFunctions.RHTower.ProlateEvenCrossSpectralIdentity

open MeasureTheory Set Filter

noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

namespace RHTower

/-- Integral model of the second derivative of the entire sinc profile. -/
def sincSecondIntegralProfile (c u : ℝ) : ℝ :=
  -(c ^ 3) / (2 * Real.pi) *
    ∫ t in (-1 : ℝ)..1, t ^ 2 * Real.cos (c * u * t)

private theorem sincSmooth_eq_cosIntegral (c u : ℝ) :
    sincSmooth c u = c / (2 * Real.pi) *
      ∫ t in (-1 : ℝ)..1, Real.cos (c * u * t) := by
  by_cases hc : c = 0
  · subst c
    have hz : sincSmooth 0 u = 0 := by
      by_cases hu : u = 0
      · subst u
        simp [sincSmooth_zero]
      · rw [sincSmooth_eq_off hu]
        simp [sincScalar]
    rw [hz]
    simp
  by_cases hu : u = 0
  · subst u
    rw [sincSmooth_zero]
    simp
    ring
  · have hcu : c * u ≠ 0 := mul_ne_zero hc hu
    have hderiv : ∀ t : ℝ,
        HasDerivAt (fun z : ℝ => Real.sin ((c * u) * z) / (c * u))
          (Real.cos ((c * u) * t)) t := by
      intro t
      have hlin : HasDerivAt (fun z : ℝ => (c * u) * z) (c * u) t := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (c * u)
      have hd := hlin.sin.div_const (c * u)
      exact hd.congr_deriv (by field_simp [hcu])
    have hint : (∫ t in (-1 : ℝ)..1, Real.cos (c * u * t)) =
        2 * Real.sin (c * u) / (c * u) := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (-1 : ℝ)) (b := 1)
        (fun t _ => hderiv t)
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable
          (-1 : ℝ) 1)
      simp only [mul_neg, mul_one, Real.sin_neg] at h
      rw [h]
      field_simp [hcu]
      ring
    rw [hint, sincSmooth_eq_off hu]
    simp only [sincScalar]
    field_simp [hc, hu, hcu, Real.pi_ne_zero]

private theorem hasDerivAt_cosIntegral (c u : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ t in (-1 : ℝ)..1, Real.cos (c * x * t))
      (∫ t in (-1 : ℝ)..1, -(c * t) * Real.sin (c * u * t)) u := by
  let F : ℝ → ℝ → ℝ := fun x t => Real.cos ((c * t) * x)
  let F' : ℝ → ℝ → ℝ := fun x t => -(c * t) * Real.sin ((c * t) * x)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (-1 : ℝ)) (b := 1)
    (F := F) (F' := F') (bound := fun _ => |c|) (s := Set.univ)
    (x₀ := u) univ_mem
    (Eventually.of_forall fun x =>
      (by fun_prop : Continuous (fun t : ℝ => F x t)) |>.aestronglyMeasurable)
    ((by fun_prop : Continuous (F u)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (F' u)).aestronglyMeasurable)
    (Eventually.of_forall fun t ht x _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      have ht1 : |t| ≤ 1 := by
        rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        exact abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hs1 : |Real.sin ((c * t) * x)| ≤ 1 := Real.abs_sin_le_one _
      calc
        |c * t| * |Real.sin ((c * t) * x)| ≤ |c * t| * 1 :=
          mul_le_mul_of_nonneg_left hs1 (abs_nonneg _)
        _ = |c| * |t| := by rw [mul_one, abs_mul]
        _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left ht1 (abs_nonneg _)
        _ = |c| := mul_one _)
    (continuous_const.intervalIntegrable _ _)
    (Eventually.of_forall fun t _ x _ => by
      have hlin : HasDerivAt (fun z : ℝ => (c * t) * z) (c * t) x := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (c * t)
      simpa [F, F', mul_comm] using hlin.cos)
  simpa [F, F', mul_assoc, mul_comm, mul_left_comm] using h.2

private theorem hasDerivAt_sinWeightedIntegral (c u : ℝ) :
    HasDerivAt (fun x : ℝ =>
        ∫ t in (-1 : ℝ)..1, -(c * t) * Real.sin (c * x * t))
      (∫ t in (-1 : ℝ)..1, -(c * t) ^ 2 * Real.cos (c * u * t)) u := by
  let F : ℝ → ℝ → ℝ := fun x t => -(c * t) * Real.sin ((c * t) * x)
  let F' : ℝ → ℝ → ℝ := fun x t => -(c * t) ^ 2 * Real.cos ((c * t) * x)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (-1 : ℝ)) (b := 1)
    (F := F) (F' := F') (bound := fun _ => c ^ 2) (s := Set.univ)
    (x₀ := u) univ_mem
    (Eventually.of_forall fun x =>
      (by fun_prop : Continuous (fun t : ℝ => F x t)) |>.aestronglyMeasurable)
    ((by fun_prop : Continuous (F u)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (F' u)).aestronglyMeasurable)
    (Eventually.of_forall fun t ht x _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_pow]
      have ht1 : |t| ≤ 1 := by
        rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        exact abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hct : |c * t| ≤ |c| := by
        rw [abs_mul]
        simpa using mul_le_mul_of_nonneg_left ht1 (abs_nonneg c)
      have hsq : |c * t| ^ 2 ≤ |c| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hct 2
      have hcos : |Real.cos ((c * t) * x)| ≤ 1 := Real.abs_cos_le_one _
      calc
        |c * t| ^ 2 * |Real.cos ((c * t) * x)| ≤ |c * t| ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hcos (sq_nonneg _)
        _ ≤ |c| ^ 2 := by simpa using hsq
        _ = c ^ 2 := sq_abs c)
    (continuous_const.intervalIntegrable _ _)
    (Eventually.of_forall fun t _ x _ => by
      have hlin : HasDerivAt (fun z : ℝ => (c * t) * z) (c * t) x := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (c * t)
      simpa [F, F', mul_comm, mul_left_comm, mul_assoc, pow_two] using
        hlin.sin.const_mul (-(c * t)))
  simpa [F, F', mul_assoc, mul_comm, mul_left_comm] using h.2

/-- Exact integral representation of the second derivative, including the removable diagonal. -/
theorem deriv2_sincSmooth_eq_sincSecondIntegralProfile (c u : ℝ) :
    deriv (deriv (sincSmooth c)) u = sincSecondIntegralProfile c u := by
  have hfun : sincSmooth c = fun x : ℝ => c / (2 * Real.pi) *
      ∫ t in (-1 : ℝ)..1, Real.cos (c * x * t) :=
    funext (sincSmooth_eq_cosIntegral c)
  have hfirst : deriv (sincSmooth c) = fun x : ℝ => c / (2 * Real.pi) *
      ∫ t in (-1 : ℝ)..1, -(c * t) * Real.sin (c * x * t) := by
    funext x
    have h := (hasDerivAt_cosIntegral c x).const_mul (c / (2 * Real.pi))
    rw [← hfun] at h
    exact h.deriv
  have hsecond := (hasDerivAt_sinWeightedIntegral c u).const_mul (c / (2 * Real.pi))
  rw [← hfirst] at hsecond
  rw [hsecond.deriv, sincSecondIntegralProfile]
  have hint : (∫ t in (-1 : ℝ)..1, -(c * t) ^ 2 * Real.cos (c * u * t)) =
      (-c ^ 2) * ∫ t in (-1 : ℝ)..1, t ^ 2 * Real.cos (c * u * t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [hint]
  ring

private theorem continuous_closedInterval_cosMoment (n : ℕ) :
    Continuous (fun p : ℝ × ℝ =>
      ∫ t : ClosedInterval (-1 : ℝ) 1,
        (t : ℝ) ^ n * Real.cos (p.1 * p.2 * (t : ℝ)) ∂volume) := by
  let F : (ℝ × ℝ) → ClosedInterval (-1 : ℝ) 1 → ℝ :=
    fun p t => (t : ℝ) ^ n * Real.cos (p.1 * p.2 * (t : ℝ))
  apply MeasureTheory.continuous_of_dominated
    (F := F) (bound := fun _ => (1 : ℝ))
  · intro p
    exact (by fun_prop : Continuous (F p)).aestronglyMeasurable
  · intro p
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have ht : |(t : ℝ)| ≤ 1 := abs_le.mpr t.2
      have hpow : |(t : ℝ)| ^ n ≤ 1 := by
        simpa using pow_le_one₀ (abs_nonneg (t : ℝ)) ht
      calc
        |(t : ℝ)| ^ n * |Real.cos (p.1 * p.2 * (t : ℝ))| ≤
            |(t : ℝ)| ^ n * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (pow_nonneg (abs_nonneg _) _)
        _ ≤ 1 := by simpa using hpow
  · exact MeasureTheory.integrable_const 1
  · exact Eventually.of_forall fun t => by
      dsimp only [F]
      fun_prop

/-- The entire sinc profile is jointly continuous in aperture and spatial argument. -/
theorem continuous_sincSmooth_joint :
    Continuous (fun p : ℝ × ℝ => sincSmooth p.1 p.2) := by
  have hfun : (fun p : ℝ × ℝ => sincSmooth p.1 p.2) =
      fun p => p.1 / (2 * Real.pi) *
        ∫ t : ClosedInterval (-1 : ℝ) 1,
          Real.cos (p.1 * p.2 * (t : ℝ)) ∂volume := by
    funext p
    rw [sincSmooth_eq_cosIntegral,
      ← GaloisForLFunctions.RHTower.integral_subtype_unit]
  rw [hfun]
  have hc : Continuous (fun p : ℝ × ℝ => p.1 / (2 * Real.pi)) := by fun_prop
  exact hc.mul (by
    simpa only [pow_zero, one_mul] using continuous_closedInterval_cosMoment 0)

/-- The integral second-sinc profile is jointly continuous in aperture and spatial argument. -/
theorem continuous_sincSecondIntegralProfile_joint :
    Continuous (fun p : ℝ × ℝ => sincSecondIntegralProfile p.1 p.2) := by
  have hfun : (fun p : ℝ × ℝ => sincSecondIntegralProfile p.1 p.2) =
      fun p => -(p.1 ^ 3) / (2 * Real.pi) *
        ∫ t : ClosedInterval (-1 : ℝ) 1,
          (t : ℝ) ^ 2 * Real.cos (p.1 * p.2 * (t : ℝ)) ∂volume := by
    funext p
    rw [sincSecondIntegralProfile,
      ← GaloisForLFunctions.RHTower.integral_subtype_unit]
  rw [hfun]
  have hc : Continuous (fun p : ℝ × ℝ => -(p.1 ^ 3) / (2 * Real.pi)) := by fun_prop
  exact hc.mul (continuous_closedInterval_cosMoment 2)

/-- The second derivative of the sinc profile is jointly continuous in aperture and space. -/
theorem continuous_deriv2_sincSmooth_joint :
    Continuous (fun p : ℝ × ℝ => deriv (deriv (sincSmooth p.1)) p.2) := by
  convert continuous_sincSecondIntegralProfile_joint using 1
  funext p
  exact deriv2_sincSmooth_eq_sincSecondIntegralProfile p.1 p.2

/-- Continuous twice-differentiated sinc kernel on the unit square. -/
def bandSecondKernelContinuous (c : ℝ) :
    C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℝ) where
  toFun z := sincSecondIntegralProfile c ((z.1 : ℝ) - (z.2 : ℝ))
  continuous_toFun := by
    have hx : Continuous (fun z : ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1 =>
        (z.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
    have hy : Continuous (fun z : ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1 =>
        (z.2 : ℝ)) := continuous_subtype_val.comp continuous_snd
    exact continuous_sincSecondIntegralProfile_joint.comp
      (continuous_const.prodMk (hx.sub hy))

/-- Twice-differentiated sinc kernel varies continuously in the sup norm. -/
theorem continuous_bandSecondKernelContinuous :
    Continuous bandSecondKernelContinuous := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc : Continuous (fun p : ℝ ×
      (ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1) => p.1) := continuous_fst
  have hx : Continuous (fun p : ℝ ×
      (ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1) => (p.2.1 : ℝ)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hy : Continuous (fun p : ℝ ×
      (ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1) => (p.2.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  exact continuous_sincSecondIntegralProfile_joint.comp (hc.prodMk (hx.sub hy))

theorem bandSecondKernelContinuous_apply (c : ℝ)
    (z : ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1) :
    bandSecondKernelContinuous c z =
      deriv (deriv (sincSmooth c)) ((z.1 : ℝ) - (z.2 : ℝ)) := by
  exact (deriv2_sincSmooth_eq_sincSecondIntegralProfile c _).symm

/-- Bounded `L²[-1,1]` operator obtained from the twice-differentiated sinc kernel. -/
def bandSecondOperatorL2 (c : ℝ) :
    GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
      GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 :=
  GaloisForLFunctions.RHTower.continuousKernelOperator (bandSecondKernelContinuous c)

/-- The twice-differentiated band operator varies continuously in operator norm. -/
theorem continuous_bandSecondOperatorL2 : Continuous bandSecondOperatorL2 := by
  rw [Metric.continuous_iff]
  intro c₀ ε hε
  have hKat : ContinuousAt bandSecondKernelContinuous c₀ :=
    continuous_bandSecondKernelContinuous.continuousAt
  have hK := (Metric.continuousAt_iff.mp hKat) (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hKδ⟩ := hK
  refine ⟨δ, hδ, fun c hc => ?_⟩
  have hdistK := hKδ hc
  rw [dist_eq_norm] at hdistK ⊢
  have hop := GaloisForLFunctions.RHTower.norm_continuousKernelOperator_sub_le
    (a := (-1 : ℝ)) (b := 1) (by norm_num)
    (bandSecondKernelContinuous c) (bandSecondKernelContinuous c₀)
  change ‖bandSecondOperatorL2 c - bandSecondOperatorL2 c₀‖ ≤
    ((1 : ℝ) - (-1)) *
      ‖bandSecondKernelContinuous c - bandSecondKernelContinuous c₀‖ at hop
  calc
    ‖bandSecondOperatorL2 c - bandSecondOperatorL2 c₀‖
        ≤ 2 * ‖bandSecondKernelContinuous c - bandSecondKernelContinuous c₀‖ := by
          norm_num at hop ⊢
          exact hop
    _ < 2 * (ε / 2) := mul_lt_mul_of_pos_left hdistK (by norm_num)
    _ = ε := by ring

/-- Integral sinc model, chosen because joint continuity in the aperture is transparent. -/
def sincIntegralProfile (c u : ℝ) : ℝ :=
  c / (2 * Real.pi) *
    ∫ t : ClosedInterval (-1 : ℝ) 1,
      Real.cos (c * u * (t : ℝ)) ∂volume

theorem sincIntegralProfile_eq_sincSmooth (c u : ℝ) :
    sincIntegralProfile c u = sincSmooth c u := by
  rw [sincIntegralProfile, sincSmooth_eq_cosIntegral]
  congr 1
  exact GaloisForLFunctions.RHTower.integral_subtype_unit
    (fun t => Real.cos (c * u * t))

theorem continuous_sincIntegralProfile_joint :
    Continuous (fun p : ℝ × ℝ => sincIntegralProfile p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × ℝ => p.1 / (2 * Real.pi)) := by fun_prop
  exact hc.mul (by
    simpa only [sincIntegralProfile, pow_zero, one_mul] using
      continuous_closedInterval_cosMoment 0)

/-- Endpoint row as a continuous function before passage to `L²`. -/
def bandEndpointRowContinuous (c : ℝ) : C(ClosedInterval (-1 : ℝ) 1, ℝ) where
  toFun y := sincIntegralProfile c (1 - (y : ℝ))
  continuous_toFun := continuous_sincIntegralProfile_joint.comp
    (continuous_const.prodMk (continuous_const.sub continuous_subtype_val))

theorem continuous_bandEndpointRowContinuous : Continuous bandEndpointRowContinuous := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc : Continuous (fun p : ℝ × ClosedInterval (-1 : ℝ) 1 => p.1) := continuous_fst
  have hy : Continuous (fun p : ℝ × ClosedInterval (-1 : ℝ) 1 => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact continuous_sincIntegralProfile_joint.comp
    (hc.prodMk (continuous_const.sub hy))

/-- `L²` row of the sinc kernel at the regular endpoint `x=1`. -/
def bandEndpointRowL2 (c : ℝ) :
    GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1 :=
  ContinuousMap.toLp 2 volume ℝ (bandEndpointRowContinuous c)

/-- Endpoint kernel row varies continuously in `L²`. -/
theorem continuous_bandEndpointRowL2 : Continuous bandEndpointRowL2 := by
  exact (ContinuousMap.toLp 2 volume ℝ).continuous.comp
    continuous_bandEndpointRowContinuous

/-- Hilbert-space formula for the continuous eigenextension at the endpoint. -/
theorem eigenExtension_one_eq_inv_mul_inner_endpointRow
    (c nu : ℝ)
    (psi : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
    GaloisForLFunctions.RHTower.eigenExtension c nu psi 1 =
      nu⁻¹ * (inner ℝ (bandEndpointRowL2 c) psi : ℝ) := by
  rw [GaloisForLFunctions.RHTower.eigenExtension]
  congr 1
  rw [← GaloisForLFunctions.RHTower.lpPairing_eq_inner,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
    (μ := (volume : Measure (ClosedInterval (-1 : ℝ) 1)))
    (bandEndpointRowContinuous c)] with y hy
  change sincKernelSmooth c 1 (y : ℝ) * (psi y : ℝ) =
    GaloisForLFunctions.RHTower.realMulBilinear
      (((ContinuousMap.toLp 2 volume ℝ)
        (bandEndpointRowContinuous c)) y) (psi y : ℝ)
  rw [hy]
  simp [bandEndpointRowContinuous, sincIntegralProfile_eq_sincSmooth,
    GaloisForLFunctions.RHTower.realMulBilinear, sincKernelSmooth]

/-- The second band transform of a continuous profile is continuous at positive bandwidth. -/
theorem continuous_bandSecondTransform {c : ℝ} (hc : 0 < c)
    {f : ℝ → ℝ} (hf : Continuous f) : Continuous (bandSecondTransform c f) := by
  have hsmooth := GaloisForLFunctions.RHTower.contDiff_bandTransform hc hf
  have hder2 : Continuous (deriv (deriv (bandTransform c f))) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsmooth).2).2.continuous
  have hfun : bandSecondTransform c f = deriv (deriv (bandTransform c f)) := by
    funext x
    exact (deriv2_bandTransform c hf x).symm
  rwa [hfun]

/-- The bounded second-kernel operator realizes the pointwise second band transform. -/
theorem bandSecondOperatorL2_bandClass {c : ℝ} (hc : 0 < c)
    (f : ℝ → ℝ) (hf : Continuous f) :
    bandSecondOperatorL2 c (GaloisForLFunctions.RHTower.bandClass f hf) =
      GaloisForLFunctions.RHTower.bandClass (bandSecondTransform c f)
        (continuous_bandSecondTransform hc hf) := by
  rw [Lp.ext_iff]
  filter_upwards [GaloisForLFunctions.RHTower.continuousKernelOperator_coeFn
      (bandSecondKernelContinuous c) (GaloisForLFunctions.RHTower.bandClass f hf),
    GaloisForLFunctions.RHTower.coeFn_bandClass (bandSecondTransform c f)
      (continuous_bandSecondTransform hc hf)] with x hleft hright
  change ((GaloisForLFunctions.RHTower.continuousKernelOperator
      (bandSecondKernelContinuous c))
        (GaloisForLFunctions.RHTower.bandClass f hf) :
      ClosedInterval (-1 : ℝ) 1 → ℝ) x =
    (GaloisForLFunctions.RHTower.bandClass (bandSecondTransform c f)
      (continuous_bandSecondTransform hc hf) :
        ClosedInterval (-1 : ℝ) 1 → ℝ) x
  rw [hleft, hright]
  have hinner :
      (∫ y : ClosedInterval (-1 : ℝ) 1,
        bandSecondKernelContinuous c (x, y) *
          ((GaloisForLFunctions.RHTower.bandClass f hf :
            GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) y : ℝ) ∂volume) =
      ∫ y : ClosedInterval (-1 : ℝ) 1,
        deriv (deriv (sincSmooth c)) ((x : ℝ) - (y : ℝ)) * f (y : ℝ) ∂volume := by
    apply integral_congr_ae
    filter_upwards [GaloisForLFunctions.RHTower.coeFn_bandClass f hf] with y hy
    rw [hy, bandSecondKernelContinuous_apply]
  rw [hinner, bandSecondTransform]
  exact GaloisForLFunctions.RHTower.integral_subtype_unit
    (fun y => deriv (deriv (sincSmooth c)) ((x : ℝ) - y) * f y)

/-- Hilbert pairing of the second-kernel operator is the classical cross-derivative pairing. -/
theorem inner_bandSecondOperatorL2_bandClass {c : ℝ} (hc : 0 < c)
    {f g : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf2 : Differentiable ℝ (deriv f)) (hg : Continuous g)
    {lam : ℝ} (hband : ∀ x, bandTransform c f x = lam * f x) :
    (inner ℝ
      (bandSecondOperatorL2 c (GaloisForLFunctions.RHTower.bandClass f hf.continuous))
      (GaloisForLFunctions.RHTower.bandClass g hg) : ℝ) =
      lam * ∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x := by
  rw [bandSecondOperatorL2_bandClass hc f hf.continuous,
    GaloisForLFunctions.RHTower.inner_bandClass_eq]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  change bandSecondTransform c f x * g x =
    lam * (deriv (deriv f) x * g x)
  rw [bandSecondTransform_eq_eigen_secondDeriv hf hf2 hband]
  ring

/-- Endpoint value of the smooth extension, expressed entirely in Hilbert-space data. -/
def bandEigenExtensionEndpointL2 (c nu : ℝ)
    (psi : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) : ℝ :=
  nu⁻¹ * (inner ℝ (bandEndpointRowL2 c) psi : ℝ)

theorem bandEigenExtensionEndpointL2_eq (c nu : ℝ)
    (psi : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :
    bandEigenExtensionEndpointL2 c nu psi =
      GaloisForLFunctions.RHTower.eigenExtension c nu psi 1 := by
  exact (eigenExtension_one_eq_inv_mul_inner_endpointRow c nu psi).symm

/-- Oriented second-derivative pairing of two endpoint-normalized live eigenbranches. -/
def normalizedSecondPairingL2 (c nuF nuG : ℝ)
    (f g : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) : ℝ :=
  (nuF⁻¹ * (inner ℝ (bandSecondOperatorL2 c f) g : ℝ)) /
    (bandEigenExtensionEndpointL2 c nuF f *
      bandEigenExtensionEndpointL2 c nuG g)

/-- Bounded-kernel realization makes the endpoint-normalized cross pairing continuous along any
two continuous live branches. -/
theorem continuousAt_normalizedSecondPairingL2
    {c₀ : ℝ}
    {nuF nuG : ℝ → ℝ}
    {f g : ℝ → GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1}
    (hnuF : ContinuousAt nuF c₀) (hnuG : ContinuousAt nuG c₀)
    (hf : ContinuousAt f c₀) (hg : ContinuousAt g c₀)
    (hnuF0 : nuF c₀ ≠ 0) (hnuG0 : nuG c₀ ≠ 0)
    (hendF : bandEigenExtensionEndpointL2 c₀ (nuF c₀) (f c₀) ≠ 0)
    (hendG : bandEigenExtensionEndpointL2 c₀ (nuG c₀) (g c₀) ≠ 0) :
    ContinuousAt
      (fun c => normalizedSecondPairingL2 c (nuF c) (nuG c) (f c) (g c)) c₀ := by
  have hBf : ContinuousAt (fun c => bandSecondOperatorL2 c (f c)) c₀ :=
    continuous_bandSecondOperatorL2.continuousAt.clm_apply hf
  have hpair : ContinuousAt
      (fun c => (inner ℝ (bandSecondOperatorL2 c (f c)) (g c) : ℝ)) c₀ :=
    hBf.inner hg
  have hrowF : ContinuousAt
      (fun c => (inner ℝ (bandEndpointRowL2 c) (f c) : ℝ)) c₀ :=
    continuous_bandEndpointRowL2.continuousAt.inner hf
  have hrowG : ContinuousAt
      (fun c => (inner ℝ (bandEndpointRowL2 c) (g c) : ℝ)) c₀ :=
    continuous_bandEndpointRowL2.continuousAt.inner hg
  have heF : ContinuousAt
      (fun c => bandEigenExtensionEndpointL2 c (nuF c) (f c)) c₀ := by
    exact (hnuF.inv₀ hnuF0).mul hrowF
  have heG : ContinuousAt
      (fun c => bandEigenExtensionEndpointL2 c (nuG c) (g c)) c₀ := by
    exact (hnuG.inv₀ hnuG0).mul hrowG
  exact ((hnuF.inv₀ hnuF0).mul hpair).div (heF.mul heG)
    (mul_ne_zero hendF hendG)

/-- At an actual indexed pair, the bounded Hilbert-space branch pairing is exactly the classical
endpoint-normalized second-derivative integral. -/
theorem normalizedSecondPairingL2_signedMode_eq
    {a : ℝ} (ha : 0 < a) (m n : ℕ) :
    let Dm := signedModeRadialData a m
    let Dn := signedModeRadialData a n
    let fm := GaloisForLFunctions.RHTower.bandClass Dm.R
      (signedModeRadialData_isExact_of_pos ha m).2.2.2.2.2.1.continuous
    let fn := GaloisForLFunctions.RHTower.bandClass Dn.R
      (signedModeRadialData_isExact_of_pos ha n).2.2.2.2.2.1.continuous
    normalizedSecondPairingL2 (signedModeRadialBandwidth a)
      (evenProlateSignedValue a m ^ 2) (evenProlateSignedValue a n ^ 2)
      ((‖fm‖ : ℝ)⁻¹ • fm) ((‖fn‖ : ℝ)⁻¹ • fn) =
        ∫ x in (-1 : ℝ)..1, deriv (deriv Dm.R) x * Dn.R x := by
  dsimp only
  let Dm := signedModeRadialData a m
  let Dn := signedModeRadialData a n
  have hm := signedModeRadialData_isExact_of_pos ha m
  have hn := signedModeRadialData_isExact_of_pos ha n
  rcases hm with ⟨_, _, _, _, hmRdef, hmRSmooth, _, hmROne, hmBand,
    _, _, _, _, _⟩
  rcases hn with ⟨_, _, _, _, hnRdef, hnRSmooth, _, hnROne, hnBand,
    _, _, _, _, _⟩
  let fm := GaloisForLFunctions.RHTower.bandClass Dm.R hmRSmooth.continuous
  let fn := GaloisForLFunctions.RHTower.bandClass Dn.R hnRSmooth.continuous
  have hmRBand : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) Dm.R x =
        evenProlateSignedValue a m ^ 2 * Dm.R x := by
    change ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a m).R x =
        evenProlateSignedValue a m ^ 2 * (signedModeRadialData a m).R x
    rw [hmRdef]
    exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hmBand
  have hnRBand : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) Dn.R x =
        evenProlateSignedValue a n ^ 2 * Dn.R x := by
    change ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a n).R x =
        evenProlateSignedValue a n ^ 2 * (signedModeRadialData a n).R x
    rw [hnRdef]
    exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hnBand
  have hmSigned : evenProlateSignedValue a m ≠ 0 :=
    evenProlateSignedValue_ne_zero ha m
  have hnSigned : evenProlateSignedValue a n ≠ 0 :=
    evenProlateSignedValue_ne_zero ha n
  have hmVal : evenProlateSignedValue a m ^ 2 ≠ 0 :=
    pow_ne_zero 2 hmSigned
  have hnVal : evenProlateSignedValue a n ^ 2 ≠ 0 :=
    pow_ne_zero 2 hnSigned
  have hfm : fm ≠ 0 := by
    exact GaloisForLFunctions.RHTower.bandClass_ne_zero_of_global_band_eigen
      hmRSmooth.continuous hmVal (by
        intro hzero
        have h := congrFun hzero 1
        rw [hmROne] at h
        exact one_ne_zero h) hmRBand
  have hfn : fn ≠ 0 := by
    exact GaloisForLFunctions.RHTower.bandClass_ne_zero_of_global_band_eigen
      hnRSmooth.continuous hnVal (by
        intro hzero
        have h := congrFun hzero 1
        rw [hnROne] at h
        exact one_ne_zero h) hnRBand
  have hfmNorm : ‖fm‖ ≠ 0 := norm_ne_zero_iff.mpr hfm
  have hfnNorm : ‖fn‖ ≠ 0 := norm_ne_zero_iff.mpr hfn
  have hmEnd : bandEigenExtensionEndpointL2 (signedModeRadialBandwidth a)
      (evenProlateSignedValue a m ^ 2) ((‖fm‖ : ℝ)⁻¹ • fm) = ‖fm‖⁻¹ := by
    rw [bandEigenExtensionEndpointL2_eq]
    rw [GaloisForLFunctions.RHTower.eigenExtension_smul,
      show GaloisForLFunctions.RHTower.eigenExtension (signedModeRadialBandwidth a)
          (evenProlateSignedValue a m ^ 2) fm = Dm.R by
        exact eigenExtension_bandClass_eq_self_of_bandEigen hmVal
          hmRSmooth.continuous hmRBand,
      hmROne]
    ring
  have hnEnd : bandEigenExtensionEndpointL2 (signedModeRadialBandwidth a)
      (evenProlateSignedValue a n ^ 2) ((‖fn‖ : ℝ)⁻¹ • fn) = ‖fn‖⁻¹ := by
    rw [bandEigenExtensionEndpointL2_eq]
    rw [GaloisForLFunctions.RHTower.eigenExtension_smul,
      show GaloisForLFunctions.RHTower.eigenExtension (signedModeRadialBandwidth a)
          (evenProlateSignedValue a n ^ 2) fn = Dn.R by
        exact eigenExtension_bandClass_eq_self_of_bandEigen hnVal
          hnRSmooth.continuous hnRBand,
      hnROne]
    ring
  have hpair := inner_bandSecondOperatorL2_bandClass
    (by dsimp [signedModeRadialBandwidth]; positivity)
    (contDiff_infty_iff_deriv.mp hmRSmooth).1
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hmRSmooth).2).1
    hnRSmooth.continuous hmRBand
  change normalizedSecondPairingL2 (signedModeRadialBandwidth a)
      (evenProlateSignedValue a m ^ 2) (evenProlateSignedValue a n ^ 2)
      ((‖fm‖ : ℝ)⁻¹ • fm) ((‖fn‖ : ℝ)⁻¹ • fn) = _
  rw [normalizedSecondPairingL2, hmEnd, hnEnd, map_smul,
    real_inner_smul_left, real_inner_smul_right, hpair]
  field_simp [hmSigned, hnSigned, hmVal, hfmNorm, hfnNorm]

/-- Every actual indexed pair admits two differentiable normalized local eigenbranches on which
the oriented endpoint-normalized cross pairing is continuous and has the exact radial value at the
base aperture. -/
theorem exists_local_continuous_signedMode_crossPairing
    {a : ℝ} (ha : 0 < a) (m n : ℕ) :
    let c₀ := signedModeRadialBandwidth a
    let Dm := signedModeRadialData a m
    let Dn := signedModeRadialData a n
    let fm := GaloisForLFunctions.RHTower.bandClass Dm.R
      (signedModeRadialData_isExact_of_pos ha m).2.2.2.2.2.1.continuous
    let fn := GaloisForLFunctions.RHTower.bandClass Dn.R
      (signedModeRadialData_isExact_of_pos ha n).2.2.2.2.2.1.continuous
    let psiM₀ := (‖fm‖ : ℝ)⁻¹ • fm
    let psiN₀ := (‖fn‖ : ℝ)⁻¹ • fn
    ∃ (psiM psiN : ℝ → GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
        (nuM nuN : ℝ → ℝ),
      psiM c₀ = psiM₀ ∧ nuM c₀ = evenProlateSignedValue a m ^ 2 ∧
      DifferentiableAt ℝ psiM c₀ ∧ DifferentiableAt ℝ nuM c₀ ∧
      (∀ᶠ c in nhds c₀,
        GaloisForLFunctions.RHTower.bandOperatorL2 c (psiM c) = nuM c • psiM c ∧
          (inner ℝ (psiM c) (psiM c) : ℝ) = 1) ∧
      psiN c₀ = psiN₀ ∧ nuN c₀ = evenProlateSignedValue a n ^ 2 ∧
      DifferentiableAt ℝ psiN c₀ ∧ DifferentiableAt ℝ nuN c₀ ∧
      (∀ᶠ c in nhds c₀,
        GaloisForLFunctions.RHTower.bandOperatorL2 c (psiN c) = nuN c • psiN c ∧
          (inner ℝ (psiN c) (psiN c) : ℝ) = 1) ∧
      ContinuousAt (fun c =>
        normalizedSecondPairingL2 c (nuM c) (nuN c) (psiM c) (psiN c)) c₀ ∧
      normalizedSecondPairingL2 c₀ (nuM c₀) (nuN c₀) (psiM c₀) (psiN c₀) =
        ∫ x in (-1 : ℝ)..1, deriv (deriv Dm.R) x * Dn.R x := by
  dsimp only
  let Dm := signedModeRadialData a m
  let Dn := signedModeRadialData a n
  have hm := signedModeRadialData_isExact_of_pos ha m
  have hn := signedModeRadialData_isExact_of_pos ha n
  rcases hm with ⟨_, _, _, _, hmRdef, hmRSmooth, _, hmROne, hmBand,
    _, _, _, _, _⟩
  rcases hn with ⟨_, _, _, _, hnRdef, hnRSmooth, _, hnROne, hnBand,
    _, _, _, _, _⟩
  let fm := GaloisForLFunctions.RHTower.bandClass Dm.R hmRSmooth.continuous
  let fn := GaloisForLFunctions.RHTower.bandClass Dn.R hnRSmooth.continuous
  let psiM₀ := (‖fm‖ : ℝ)⁻¹ • fm
  let psiN₀ := (‖fn‖ : ℝ)⁻¹ • fn
  let lamM := evenProlateSignedValue a m ^ 2
  let lamN := evenProlateSignedValue a n ^ 2
  have hmRBand : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) Dm.R x = lamM * Dm.R x := by
    change ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a m).R x =
        evenProlateSignedValue a m ^ 2 * (signedModeRadialData a m).R x
    rw [hmRdef]
    exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hmBand
  have hnRBand : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) Dn.R x = lamN * Dn.R x := by
    change ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a n).R x =
        evenProlateSignedValue a n ^ 2 * (signedModeRadialData a n).R x
    rw [hnRdef]
    exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hnBand
  have hlamM : lamM ≠ 0 := pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha m)
  have hlamN : lamN ≠ 0 := pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha n)
  have hfm : fm ≠ 0 :=
    GaloisForLFunctions.RHTower.bandClass_ne_zero_of_global_band_eigen
      hmRSmooth.continuous hlamM (by
        intro hzero
        have h := congrFun hzero 1
        rw [hmROne] at h
        exact one_ne_zero h) hmRBand
  have hfn : fn ≠ 0 :=
    GaloisForLFunctions.RHTower.bandClass_ne_zero_of_global_band_eigen
      hnRSmooth.continuous hlamN (by
        intro hzero
        have h := congrFun hzero 1
        rw [hnROne] at h
        exact one_ne_zero h) hnRBand
  have hfmNorm : ‖fm‖ ≠ 0 := norm_ne_zero_iff.mpr hfm
  have hfnNorm : ‖fn‖ ≠ 0 := norm_ne_zero_iff.mpr hfn
  have hmEig : GaloisForLFunctions.RHTower.bandOperatorL2
      (signedModeRadialBandwidth a) fm = lamM • fm :=
    GaloisForLFunctions.RHTower.bandOperatorL2_bandClass_eq_smul_of_global_band_eigen
      hmRSmooth.continuous hmRBand
  have hnEig : GaloisForLFunctions.RHTower.bandOperatorL2
      (signedModeRadialBandwidth a) fn = lamN • fn :=
    GaloisForLFunctions.RHTower.bandOperatorL2_bandClass_eq_smul_of_global_band_eigen
      hnRSmooth.continuous hnRBand
  have hmEigNorm : GaloisForLFunctions.RHTower.bandOperatorL2
      (signedModeRadialBandwidth a) psiM₀ = lamM • psiM₀ := by
    dsimp only [psiM₀]
    rw [map_smul, hmEig, smul_comm]
  have hnEigNorm : GaloisForLFunctions.RHTower.bandOperatorL2
      (signedModeRadialBandwidth a) psiN₀ = lamN • psiN₀ := by
    dsimp only [psiN₀]
    rw [map_smul, hnEig, smul_comm]
  have hmUnit : (inner ℝ psiM₀ psiM₀ : ℝ) = 1 := by
    dsimp only [psiM₀]
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hfmNorm]
  have hnUnit : (inner ℝ psiN₀ psiN₀ : ℝ) = 1 := by
    dsimp only [psiN₀]
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [hfnNorm]
  obtain ⟨psiM, nuM, hpsiM, hnuM, hdpsiM, hdnuM, heventM⟩ :=
    exists_differentiable_bandOperatorL2_branch_of_pos
      (by dsimp [signedModeRadialBandwidth]; positivity) hmEigNorm hmUnit hlamM
  obtain ⟨psiN, nuN, hpsiN, hnuN, hdpsiN, hdnuN, heventN⟩ :=
    exists_differentiable_bandOperatorL2_branch_of_pos
      (by dsimp [signedModeRadialBandwidth]; positivity) hnEigNorm hnUnit hlamN
  have hmEnd : bandEigenExtensionEndpointL2 (signedModeRadialBandwidth a)
      lamM psiM₀ = ‖fm‖⁻¹ := by
    rw [bandEigenExtensionEndpointL2_eq]
    rw [GaloisForLFunctions.RHTower.eigenExtension_smul,
      show GaloisForLFunctions.RHTower.eigenExtension (signedModeRadialBandwidth a)
          lamM fm = Dm.R by
        exact eigenExtension_bandClass_eq_self_of_bandEigen hlamM
          hmRSmooth.continuous hmRBand,
      hmROne]
    ring
  have hnEnd : bandEigenExtensionEndpointL2 (signedModeRadialBandwidth a)
      lamN psiN₀ = ‖fn‖⁻¹ := by
    rw [bandEigenExtensionEndpointL2_eq]
    rw [GaloisForLFunctions.RHTower.eigenExtension_smul,
      show GaloisForLFunctions.RHTower.eigenExtension (signedModeRadialBandwidth a)
          lamN fn = Dn.R by
        exact eigenExtension_bandClass_eq_self_of_bandEigen hlamN
          hnRSmooth.continuous hnRBand,
      hnROne]
    ring
  have hmEndNe : bandEigenExtensionEndpointL2 (signedModeRadialBandwidth a)
      (nuM (signedModeRadialBandwidth a)) (psiM (signedModeRadialBandwidth a)) ≠ 0 := by
    rw [hnuM, hpsiM, hmEnd]
    exact inv_ne_zero hfmNorm
  have hnEndNe : bandEigenExtensionEndpointL2 (signedModeRadialBandwidth a)
      (nuN (signedModeRadialBandwidth a)) (psiN (signedModeRadialBandwidth a)) ≠ 0 := by
    rw [hnuN, hpsiN, hnEnd]
    exact inv_ne_zero hfnNorm
  have hcont := continuousAt_normalizedSecondPairingL2
    hdnuM.continuousAt hdnuN.continuousAt hdpsiM.continuousAt hdpsiN.continuousAt
    (by rwa [hnuM]) (by rwa [hnuN]) hmEndNe hnEndNe
  refine ⟨psiM, psiN, nuM, nuN, hpsiM, hnuM, hdpsiM, hdnuM, heventM,
    hpsiN, hnuN, hdpsiN, hdnuN, heventN, hcont, ?_⟩
  rw [hpsiM, hnuM, hpsiN, hnuN]
  simpa only [Dm, Dn, fm, fn, psiM₀, psiN₀, lamM, lamN] using
    normalizedSecondPairingL2_signedMode_eq ha m n

end RHTower
