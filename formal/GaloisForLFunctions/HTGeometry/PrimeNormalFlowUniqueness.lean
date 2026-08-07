import GaloisForLFunctions.HTGeometry.PrimeNormalFlowExpansion

/-!
# Uniqueness of the prime normal flow

The square-root flow `S(L) = (L I - T/2)^{1/2}` inverts the prime normal flow and has derivative
`(1/2) F(L)`.  For any strong solution `G` of `(2L I - T) G' + G = 0`, the product `S G` therefore
has vanishing derivative, hence is constant; the half-log trace pins the constant, so `G` is the
prime normal flow applied to its trace.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- **The slope estimate for the square root.** -/
theorem abs_sqrtSlope_le {a b s : ℝ} (hs : 0 < s) (ha : s ≤ Real.sqrt a) (hb : s ≤ Real.sqrt b)
    (hab : a ≠ b) :
    |(Real.sqrt b - Real.sqrt a) / (b - a) - (1 / 2) * (Real.sqrt a)⁻¹|
      ≤ |b - a| / (8 * s ^ 3) := by
  set p := Real.sqrt a with hpdef
  set q := Real.sqrt b with hqdef
  have hp0 : 0 < p := lt_of_lt_of_le hs ha
  have hq0 : 0 < q := lt_of_lt_of_le hs hb
  have hapos : 0 < a := by
    by_contra hc
    rw [not_lt] at hc
    rw [hpdef, Real.sqrt_eq_zero_of_nonpos hc] at hp0
    exact lt_irrefl 0 hp0
  have hbpos : 0 < b := by
    by_contra hc
    rw [not_lt] at hc
    rw [hqdef, Real.sqrt_eq_zero_of_nonpos hc] at hq0
    exact lt_irrefl 0 hq0
  have hpa : p ^ 2 = a := Real.sq_sqrt hapos.le
  have hqb : q ^ 2 = b := Real.sq_sqrt hbpos.le
  have hd : q ^ 2 - p ^ 2 ≠ 0 := by rw [hpa, hqb]; exact sub_ne_zero.mpr (Ne.symm hab)
  have hpq : 0 < p + q := by linarith
  have hexpr : (q - p) / (b - a) - (1 / 2) * p⁻¹
      = -((q ^ 2 - p ^ 2) / (2 * p * (p + q) ^ 2)) := by
    rw [← hpa, ← hqb]
    field_simp
    ring
  rw [hexpr, abs_neg, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * p * (p + q) ^ 2), hpa, hqb]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 8 * s ^ 3 ≤ 2 * p * (p + q) ^ 2 := by
    have e1 : 2 * s * (2 * s) ^ 2 ≤ 2 * p * (p + q) ^ 2 := by
      have hsq : (2 * s) ^ 2 ≤ (p + q) ^ 2 := by
        have : 2 * s ≤ p + q := by linarith
        nlinarith [hs.le, hpq.le]
      exact mul_le_mul (by linarith) hsq (by positivity) (by positivity)
    calc 8 * s ^ 3 = 2 * s * (2 * s) ^ 2 := by ring
      _ ≤ 2 * p * (p + q) ^ 2 := e1
  calc |b - a| * (8 * s ^ 3) ≤ |b - a| * (2 * p * (p + q) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |b - a| * (2 * p * (p + q) ^ 2) := rfl

section Flow

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- The symbol `(L − t/2)^{1/2}`. -/
noncomputable def sqrtSymbol (L t : ℝ) : ℝ := Real.sqrt (L - t / 2)

/-- **The square-root flow** `S(L) = (L I − T/2)^{1/2}`. -/
noncomputable def sqrtFlow (T : A) (L : ℝ) : A := cfc (sqrtSymbol L) T

omit [Nontrivial A] in
theorem continuousOn_sqrtSymbol {T : A} (L : ℝ) :
    ContinuousOn (sqrtSymbol L) (spectrum ℝ T) :=
  (Real.continuous_sqrt.comp (by fun_prop)).continuousOn

/-- The defect of the difference quotient of the square-root symbol. -/
noncomputable def sqrtSlopeSymbol (L L' t : ℝ) : ℝ :=
  (L' - L)⁻¹ * (sqrtSymbol L' t - sqrtSymbol L t) - (1 / 2) * flowSymbol L t

theorem abs_sqrtSlopeSymbol_le {T : A} {L L' t : ℝ} (hL : ‖T‖ / 2 < L)
    (hne : L' ≠ L) (hclose : |L' - L| < (L - ‖T‖ / 2) / 2) (ht : t ∈ spectrum ℝ T) :
    |sqrtSlopeSymbol L L' t| ≤ |L' - L| / (8 * Real.sqrt ((L - ‖T‖ / 2) / 2) ^ 3) := by
  have hδ : 0 < L - ‖T‖ / 2 := by linarith
  have hs : 0 < Real.sqrt ((L - ‖T‖ / 2) / 2) := Real.sqrt_pos.mpr (by linarith)
  have htn : t ≤ ‖T‖ := le_trans (le_abs_self t) (abs_le_norm_of_mem_spectrum ht)
  have h1 : L - L' ≤ |L' - L| := by rw [abs_sub_comm]; exact le_abs_self _
  have ha : (L - ‖T‖ / 2) / 2 ≤ L - t / 2 := by linarith
  have hb : (L - ‖T‖ / 2) / 2 ≤ L' - t / 2 := by linarith
  have hsa : Real.sqrt ((L - ‖T‖ / 2) / 2) ≤ Real.sqrt (L - t / 2) := Real.sqrt_le_sqrt ha
  have hsb : Real.sqrt ((L - ‖T‖ / 2) / 2) ≤ Real.sqrt (L' - t / 2) := Real.sqrt_le_sqrt hb
  have hab : L - t / 2 ≠ L' - t / 2 := fun h => hne (by linarith)
  have hkey := abs_sqrtSlope_le hs hsa hsb hab
  rw [show (L' - t / 2) - (L - t / 2) = L' - L by ring] at hkey
  rw [show sqrtSlopeSymbol L L' t
      = (Real.sqrt (L' - t / 2) - Real.sqrt (L - t / 2)) / (L' - L)
        - (1 / 2) * (Real.sqrt (L - t / 2))⁻¹ by
    simp only [sqrtSlopeSymbol, sqrtSymbol, flowSymbol]; ring]
  exact hkey

theorem continuousOn_sqrtSlopeSymbol {T : A} {L L' : ℝ} (hL : ‖T‖ / 2 < L) :
    ContinuousOn (sqrtSlopeSymbol L L') (spectrum ℝ T) :=
  (continuousOn_const.mul ((continuousOn_sqrtSymbol L').sub (continuousOn_sqrtSymbol L))).sub
    (continuousOn_const.mul (continuousOn_flowSymbol hL))

/-- **The square-root flow is differentiable in `L`, with derivative `(1/2)(L I − T/2)^{-1/2}`.** -/
theorem hasDerivAt_sqrtFlow {T : A} (hT : IsSelfAdjoint T) {L : ℝ} (hL : ‖T‖ / 2 < L) :
    HasDerivAt (sqrtFlow T) ((1 / 2 : ℝ) • primeNormalFlow T L) L := by
  have hδ : 0 < L - ‖T‖ / 2 := by linarith
  have hs : 0 < Real.sqrt ((L - ‖T‖ / 2) / 2) := Real.sqrt_pos.mpr (by linarith)
  set D : A := (1 / 2 : ℝ) • primeNormalFlow T L with hDdef
  have hwin : ∀ᶠ L' in 𝓝[≠] L, |L' - L| < (L - ‖T‖ / 2) / 2 := by
    have hball := Metric.ball_mem_nhds L (by linarith : (0:ℝ) < (L - ‖T‖ / 2) / 2)
    have hb2 : ∀ᶠ L' in 𝓝 L, |L' - L| < (L - ‖T‖ / 2) / 2 := by
      filter_upwards [hball] with L' hL'
      rwa [Metric.mem_ball, Real.dist_eq] at hL'
    exact hb2.filter_mono nhdsWithin_le_nhds
  have hident : ∀ᶠ L' in 𝓝[≠] L,
      ‖cfc (sqrtSlopeSymbol L L') T‖ = ‖slope (sqrtFlow T) L L' - D‖ := by
    filter_upwards [self_mem_nhdsWithin] with L' hne
    have hcL := continuousOn_flowSymbol (T := T) hL
    have hsL := continuousOn_sqrtSymbol (T := T) L
    have hsL' := continuousOn_sqrtSymbol (T := T) L'
    have hcd : ContinuousOn (fun t => sqrtSymbol L' t - sqrtSymbol L t) (spectrum ℝ T) :=
      hsL'.sub hsL
    have hsub : cfc (fun t => sqrtSymbol L' t - sqrtSymbol L t) T
        = sqrtFlow T L' - sqrtFlow T L := cfc_sub _ _ T hsL' hsL
    have hslope : slope (sqrtFlow T) L L'
        = cfc (fun t => (L' - L)⁻¹ * (sqrtSymbol L' t - sqrtSymbol L t)) T := by
      rw [slope_def_module, ← hsub]
      exact (cfc_const_mul _ _ T hcd).symm
    have hD : D = cfc (fun t => (1 / 2 : ℝ) * flowSymbol L t) T := by
      rw [hDdef, cfc_const_mul _ _ T hcL]
      rfl
    have hsplit := cfc_sub (fun t => (L' - L)⁻¹ * (sqrtSymbol L' t - sqrtSymbol L t))
      (fun t => (1 / 2 : ℝ) * flowSymbol L t) T
      (continuousOn_const.mul hcd) (continuousOn_const.mul hcL)
    have heqfun : (fun t => (L' - L)⁻¹ * (sqrtSymbol L' t - sqrtSymbol L t)
        - (1 / 2 : ℝ) * flowSymbol L t) = sqrtSlopeSymbol L L' := by
      funext t; rw [sqrtSlopeSymbol]
    rw [heqfun] at hsplit
    rw [hsplit, ← hslope, ← hD]
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ L' in 𝓝[≠] L,
      ∀ t ∈ spectrum ℝ T, ‖sqrtSlopeSymbol L L' t‖ ≤ ε := by
    intro ε hε
    have hbound : Tendsto
        (fun L' : ℝ => |L' - L| / (8 * Real.sqrt ((L - ‖T‖ / 2) / 2) ^ 3)) (𝓝[≠] L) (𝓝 0) := by
      have h1 : Tendsto (fun L' : ℝ => |L' - L|) (𝓝[≠] L) (𝓝 0) := by
        have hc : ContinuousAt (fun L' : ℝ => |L' - L|) L := by fun_prop
        have h0 : Tendsto (fun L' : ℝ => |L' - L|) (𝓝 L) (𝓝 0) := by simpa using hc.tendsto
        exact h0.mono_left nhdsWithin_le_nhds
      simpa using h1.div_const (8 * Real.sqrt ((L - ‖T‖ / 2) / 2) ^ 3)
    filter_upwards [hwin, self_mem_nhdsWithin,
      hbound.eventually (eventually_lt_nhds hε)] with L' hw hne hsm t ht
    rw [Real.norm_eq_abs]
    exact le_trans (abs_sqrtSlopeSymbol_le (T := T) hL hne hw ht) hsm.le
  have hcont : ∀ᶠ L' in 𝓝[≠] L, ContinuousOn (sqrtSlopeSymbol L L') (spectrum ℝ T) :=
    Eventually.of_forall fun L' => continuousOn_sqrtSlopeSymbol hL
  have hmain : Tendsto (fun L' => ‖cfc (sqrtSlopeSymbol L L') T‖) (𝓝[≠] L) (𝓝 0) :=
    tendsto_norm_cfc_zero (𝕜 := ℝ) (sqrtSlopeSymbol L) T hT hcont hsmall
  rw [hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff,
    tendsto_zero_iff_norm_tendsto_zero]
  exact hmain.congr' hident

/-- `S(L) F(L) = 1`: the square-root flow inverts the prime normal flow. -/
theorem sqrtFlow_mul_primeNormalFlow {T : A} (hT : IsSelfAdjoint T) {L : ℝ} (hL : ‖T‖ / 2 < L) :
    sqrtFlow T L * primeNormalFlow T L = 1 := by
  show cfc (sqrtSymbol L) T * cfc (flowSymbol L) T = 1
  have h := cfc_mul (sqrtSymbol L) (flowSymbol L) T (continuousOn_sqrtSymbol L)
    (continuousOn_flowSymbol hL)
  have hsym : ∀ t ∈ spectrum ℝ T, sqrtSymbol L t * flowSymbol L t = 1 := by
    intro t ht
    have hp : 0 < Real.sqrt (L - t / 2) := Real.sqrt_pos.mpr (flow_shift_pos hL ht)
    rw [sqrtSymbol, flowSymbol, mul_inv_cancel₀ hp.ne']
  rw [← h, cfc_congr hsym, cfc_const 1 T, map_one]

/-- `F(L) S(L) = 1`. -/
theorem primeNormalFlow_mul_sqrtFlow {T : A} (hT : IsSelfAdjoint T) {L : ℝ} (hL : ‖T‖ / 2 < L) :
    primeNormalFlow T L * sqrtFlow T L = 1 := by
  show cfc (flowSymbol L) T * cfc (sqrtSymbol L) T = 1
  have h := cfc_mul (flowSymbol L) (sqrtSymbol L) T (continuousOn_flowSymbol hL)
    (continuousOn_sqrtSymbol L)
  have hsym : ∀ t ∈ spectrum ℝ T, flowSymbol L t * sqrtSymbol L t = 1 := by
    intro t ht
    have hp : 0 < Real.sqrt (L - t / 2) := Real.sqrt_pos.mpr (flow_shift_pos hL ht)
    rw [sqrtSymbol, flowSymbol, inv_mul_cancel₀ hp.ne']
  rw [← h, cfc_congr hsym, cfc_const 1 T, map_one]

/-- `2 S(L)² = 2L I − T`. -/
theorem two_smul_sqrtFlow_sq {T : A} (hT : IsSelfAdjoint T) {L : ℝ} (hL : ‖T‖ / 2 < L) :
    (2 : ℝ) • (sqrtFlow T L ^ 2) = (2 * L) • (1 : A) - T := by
  show (2 : ℝ) • (cfc (sqrtSymbol L) T ^ 2) = (2 * L) • (1 : A) - T
  have hpow := cfc_pow (sqrtSymbol L) 2 T (continuousOn_sqrtSymbol L)
  have hsym : ∀ t ∈ spectrum ℝ T, sqrtSymbol L t ^ 2 = L - (1 / 2) * t := by
    intro t ht
    rw [sqrtSymbol, Real.sq_sqrt (flow_shift_pos hL ht).le]
    ring
  have hlin : cfc (fun t : ℝ => L - (1 / 2) * t) T = L • (1 : A) - (1 / 2 : ℝ) • T := by
    rw [cfc_sub (fun _ : ℝ => L) (fun t : ℝ => (1 / 2) * t) T continuousOn_const (by fun_prop),
      cfc_const L T, cfc_const_mul _ _ T (by fun_prop), cfc_id' ℝ T hT,
      Algebra.algebraMap_eq_smul_one]
  rw [← hpow, cfc_congr hsym, hlin, smul_sub, smul_smul, smul_smul]
  norm_num

/-- The renormalized square-root flow converges to the identity. -/
theorem tendsto_inv_sqrt_smul_sqrtFlow {T : A} (hT : IsSelfAdjoint T) :
    Tendsto (fun L => (Real.sqrt L)⁻¹ • sqrtFlow T L) atTop (𝓝 1) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  have hzero : Tendsto (fun L : ℝ => ‖T‖ / 2 / L) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  refine squeeze_zero' (Eventually.of_forall fun L => norm_nonneg _) ?_ hzero
  filter_upwards [eventually_gt_atTop (‖T‖ / 2), eventually_gt_atTop (0:ℝ)] with L hL hL0
  have hsL := continuousOn_sqrtSymbol (T := T) L
  have hone : cfc (fun _ : ℝ => (1 : ℝ)) T = 1 := by rw [cfc_const 1 T, map_one]
  have hcs : ContinuousOn (fun t : ℝ => (Real.sqrt L)⁻¹ * sqrtSymbol L t - 1) (spectrum ℝ T) :=
    (continuousOn_const.mul hsL).sub continuousOn_const
  have hrepr : cfc (fun t : ℝ => (Real.sqrt L)⁻¹ * sqrtSymbol L t - 1) T
      = (Real.sqrt L)⁻¹ • sqrtFlow T L - 1 := by
    have h1 := cfc_sub (fun t : ℝ => (Real.sqrt L)⁻¹ * sqrtSymbol L t) (fun _ : ℝ => (1 : ℝ)) T
      (continuousOn_const.mul hsL) continuousOn_const
    rw [h1, cfc_const_mul _ _ T hsL, hone]
    rfl
  rw [← hrepr]
  refine norm_cfc_le_of_forall_le (𝕜 := ℝ) _ T hcs hT ?_
  intro t ht
  have hTn : (0 : ℝ) ≤ ‖T‖ := norm_nonneg T
  have habs := abs_le_norm_of_mem_spectrum ht
  have hu : 0 < L - t / 2 := flow_shift_pos hL ht
  have hp : 0 < Real.sqrt (L - t / 2) := Real.sqrt_pos.mpr hu
  have hr : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hp2 : Real.sqrt (L - t / 2) ^ 2 = L - t / 2 := Real.sq_sqrt hu.le
  have hr2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
  have hid : (Real.sqrt L)⁻¹ * sqrtSymbol L t - 1
      = -(t / 2) / (Real.sqrt L * (Real.sqrt (L - t / 2) + Real.sqrt L)) := by
    have hkey : ∀ p r : ℝ, 0 < p → 0 < r → p ^ 2 - r ^ 2 = -(t / 2) →
        r⁻¹ * p - 1 = -(t / 2) / (r * (p + r)) := by
      intro p r hp' hr' hpr
      rw [eq_div_iff (by positivity)]
      have hfac : (r⁻¹ * p - 1) * (r * (p + r)) = (p - r) * (p + r) := by field_simp
      rw [hfac]
      linear_combination hpr
    rw [sqrtSymbol]
    exact hkey _ _ hp hr (by rw [hp2, hr2]; ring)
  have hdpos : 0 < Real.sqrt L * (Real.sqrt (L - t / 2) + Real.sqrt L) := mul_pos hr (by linarith)
  rw [Real.norm_eq_abs, hid, abs_div, abs_of_pos hdpos]
  have hnum : |-(t / 2)| ≤ ‖T‖ / 2 := by
    rw [abs_neg, abs_div, abs_two]
    linarith
  have hden : L ≤ Real.sqrt L * (Real.sqrt (L - t / 2) + Real.sqrt L) := by
    nlinarith [hp.le, hr2]
  rw [div_le_div_iff₀ hdpos hL0]
  exact mul_le_mul hnum hden hL0.le (by linarith)

/-- **Uniqueness `(3)`:** a strong solution of the normal equation is determined by its half-log
trace.  The proof multiplies by the square-root flow: `S G` has vanishing derivative, so it is
constant, and the trace pins the constant. -/
theorem primeNormalFlow_unique {T : A} (hT : IsSelfAdjoint T) {G G' : ℝ → A} {β : A}
    (hderiv : ∀ M, ‖T‖ / 2 < M → HasDerivAt G (G' M) M)
    (heq : ∀ M, ‖T‖ / 2 < M → ((2 * M) • (1 : A) - T) * G' M + G M = 0)
    (htrace : Tendsto (fun M => Real.sqrt M • G M) atTop (𝓝 β))
    {L : ℝ} (hL : ‖T‖ / 2 < L) :
    G L = primeNormalFlow T L * β := by
  have hHderiv : ∀ M, ‖T‖ / 2 < M → HasDerivAt (fun M => sqrtFlow T M * G M) 0 M := by
    intro M hM
    have hprod := (hasDerivAt_sqrtFlow hT hM).mul (hderiv M hM)
    have hSF := sqrtFlow_mul_primeNormalFlow hT hM
    have hFS := primeNormalFlow_mul_sqrtFlow hT hM
    have hsq := two_smul_sqrtFlow_sq hT hM
    have hzero : ((1 / 2 : ℝ) • primeNormalFlow T M) * G M + sqrtFlow T M * G' M = 0 := by
      set X := ((1 / 2 : ℝ) • primeNormalFlow T M) * G M + sqrtFlow T M * G' M with hXdef
      have e1 : (2 : ℝ) • (sqrtFlow T M * X)
          = (sqrtFlow T M * primeNormalFlow T M) * G M
            + ((2 : ℝ) • (sqrtFlow T M ^ 2)) * G' M := by
        rw [hXdef, mul_add, smul_add]
        congr 1
        · have h1 : ((1 / 2 : ℝ) • primeNormalFlow T M) * G M
              = (1 / 2 : ℝ) • (primeNormalFlow T M * G M) := smul_mul_assoc _ _ _
          rw [h1, mul_smul_comm, ← mul_assoc, smul_smul]
          norm_num
        · rw [smul_mul_assoc, ← mul_assoc, ← sq]
      have e2 : (2 : ℝ) • (sqrtFlow T M * X) = 0 := by
        rw [e1, hSF, one_mul, hsq, add_comm]
        exact heq M hM
      have e3 : sqrtFlow T M * X = 0 := by
        have := smul_eq_zero.mp e2
        rcases this with h | h
        · norm_num at h
        · exact h
      calc X = (primeNormalFlow T M * sqrtFlow T M) * X := by rw [hFS, one_mul]
        _ = primeNormalFlow T M * (sqrtFlow T M * X) := by rw [mul_assoc]
        _ = 0 := by rw [e3, mul_zero]
    rw [hzero] at hprod
    exact hprod
  have hconst : ∀ M, L ≤ M → sqrtFlow T M * G M = sqrtFlow T L * G L := by
    intro M hM
    have hcont : ContinuousOn (fun M => sqrtFlow T M * G M) (Set.Icc L M) := fun x hx =>
      (hHderiv x (lt_of_lt_of_le hL hx.1)).continuousAt.continuousWithinAt
    have hd : ∀ x ∈ Set.Ico L M, HasDerivWithinAt (fun M => sqrtFlow T M * G M) 0 (Set.Ici x) x :=
      fun x hx => (hHderiv x (lt_of_lt_of_le hL hx.1)).hasDerivWithinAt
    exact constant_of_has_deriv_right_zero hcont hd M (Set.right_mem_Icc.mpr hM)
  have hHlim : Tendsto (fun M => sqrtFlow T M * G M) atTop (𝓝 (sqrtFlow T L * G L)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop L] with M hM
    exact (hconst M hM).symm
  have hHbeta : Tendsto (fun M => sqrtFlow T M * G M) atTop (𝓝 (1 * β)) := by
    have hmul := (tendsto_inv_sqrt_smul_sqrtFlow hT).mul htrace
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with M hM
    have hr : Real.sqrt M ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hr, one_smul]
  rw [one_mul] at hHbeta
  have hHL : sqrtFlow T L * G L = β := tendsto_nhds_unique hHlim hHbeta
  calc G L = (primeNormalFlow T L * sqrtFlow T L) * G L := by
        rw [primeNormalFlow_mul_sqrtFlow hT hL, one_mul]
    _ = primeNormalFlow T L * (sqrtFlow T L * G L) := by rw [mul_assoc]
    _ = primeNormalFlow T L * β := by rw [hHL]


end Flow

end GaloisForLFunctions.HTGeometry
