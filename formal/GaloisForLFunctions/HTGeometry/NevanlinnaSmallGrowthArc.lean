import GaloisForLFunctions.HTGeometry.AlgebraicProximityBound
import GaloisForLFunctions.HTGeometry.AlgebraicRootGrowth
import GaloisForLFunctions.HTGeometry.SmallGrowthMeromorphicField

/-!
# Small Nevanlinna growth cannot dominate a right circular arc

If finitely many global meromorphic functions have characteristic `o(r)`, then the sum of their
positive logarithms cannot have a positive linear lower bound at every point of a fixed
positive-length arc.  This is the quantitative value-distribution obstruction used when peeling
finite Dirichlet series with small-growth meromorphic coefficients.
-/

open Filter Set Topology Metric ValueDistribution Asymptotics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem fullCircleIntegral_eq_twoPi_mul_proximity {f : ℂ → ℂ} (R : ℝ) :
    (∫ θ : ℝ in 0..2 * Real.pi, Real.posLog ‖f (circleMap 0 R θ)‖) =
      (2 * Real.pi) * proximity f ⊤ R := by
  rw [proximity_top, Real.circleAverage_def]
  change (∫ θ : ℝ in 0..2 * Real.pi, Real.posLog ‖f (circleMap 0 R θ)‖) =
    (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
      ∫ θ : ℝ in 0..2 * Real.pi, Real.posLog ‖f (circleMap 0 R θ)‖)
  field_simp [ne_of_gt Real.pi_pos]

/-- A nondegenerate circle parametrization is nowhere locally constant. -/
theorem circleMap_not_eventuallyConst {R : ℝ} (hR : 0 < R) (x : ℝ) :
    ¬ Filter.EventuallyConst (circleMap 0 R) (nhds x) := by
  intro hc
  obtain ⟨z, hz⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.mp hc
  have harg : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((x : ℂ) * Complex.I) * Complex.I) x :=
    (Complex.hasDerivAt_exp ((x : ℂ) * Complex.I)).comp x harg
  have hpath : HasDerivAt (circleMap 0 R)
      ((R : ℂ) * (Complex.exp ((x : ℂ) * Complex.I) * Complex.I)) x := by
    rw [show circleMap 0 R = fun t : ℝ =>
      (R : ℂ) * Complex.exp ((t : ℂ) * Complex.I) by
        funext t
        rw [circleMap_zero]]
    exact hexp.const_mul (R : ℂ)
  have hconst : HasDerivAt (circleMap 0 R) 0 x :=
    (hasDerivAt_const x z).congr_of_eventuallyEq hz
  have hzero := hpath.unique hconst
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  exact hRne ((mul_eq_zero.mp hzero).resolve_right
    (mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero))

/-- Circle parametrization is real analytic on every interval. -/
theorem circleMap_analyticOnNhd_real (R : ℝ) (U : Set ℝ) :
    AnalyticOnNhd ℝ (circleMap 0 R) U := by
  intro x _
  have hfun : circleMap 0 R = fun t : ℝ => (R : ℂ) *
      Complex.exp ((t : ℂ) * Complex.I) := by
    funext t
    rw [circleMap_zero]
  rw [hfun]
  let F : ℂ → ℂ := fun z => (R : ℂ) * Complex.exp (z * Complex.I)
  have hFcomplex : AnalyticAt ℂ F (x : ℂ) := by
    dsimp only [F]
    exact analyticAt_const.mul ((analyticAt_id.mul analyticAt_const).cexp)
  have hFreal : AnalyticAt ℝ F (x : ℂ) := hFcomplex.restrictScalars
  have hcomp : AnalyticAt ℝ (F ∘ Complex.ofReal) x :=
    AnalyticAt.comp (f := Complex.ofReal) (x := x) hFreal
      (Complex.ofRealCLM.analyticAt x)
  convert hcomp using 1
  funext t
  rfl

/-- A codiscrete plane property holds almost everywhere after restriction to a nondegenerate
circle arc. -/
theorem ae_restrict_circleMap_mem_of_mem_codiscrete {S : Set ℂ} (hS : S ∈ Filter.codiscrete ℂ)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ theta ∂MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (Real.pi / 3)), circleMap 0 R theta ∈ S := by
  apply ae_restrict_le_codiscreteWithin measurableSet_Icc
  change (circleMap 0 R) ⁻¹' S ∈
    Filter.codiscreteWithin (Set.Icc (0 : ℝ) (Real.pi / 3))
  have hSwithin : S ∈ Filter.codiscreteWithin
      (circleMap 0 R '' Set.Icc (0 : ℝ) (Real.pi / 3)) := by
    have hSuniv : S ∈ Filter.codiscreteWithin (Set.univ : Set ℂ) := by
      simpa only [Filter.codiscrete] using hS
    exact Filter.codiscreteWithin_mono (Set.subset_univ _) hSuniv
  exact (circleMap_analyticOnNhd_real R _).preimage_mem_codiscreteWithin
    (fun x _ => circleMap_not_eventuallyConst hR x) hSwithin

/-- Finitely many meromorphic functions of characteristic `o(r)` cannot collectively have
positive-logarithmic size at least `c r` almost everywhere on the arc `[0, π/3]` for all large
`r`. -/
theorem not_eventually_ae_linear_le_sum_posLog_on_rightArc {n : ℕ}
    (phi : Fin n → ℂ → ℂ) (hphi : ∀ j, Meromorphic (phi j))
    (hsmall : ∀ j, characteristic (phi j) ⊤ =o[atTop] id)
    {c : ℝ} (hc : 0 < c) :
    ¬ ∀ᶠ R in atTop, ∀ᵐ θ ∂MeasureTheory.volume.restrict
        (Set.Icc (0 : ℝ) (Real.pi / 3)),
      c * R ≤ ∑ j, Real.posLog ‖phi j (circleMap 0 R θ)‖ := by
  intro hlower
  have hcharSum :
      (fun R => ∑ j, characteristic (phi j) ⊤ R) =o[atTop] id := by
    simpa only [Finset.sum_apply] using
      (Asymptotics.IsLittleO.sum (s := Finset.univ)
        (fun j _ => hsmall j))
  have hscaled :
      (fun R => (2 * Real.pi) * ∑ j, characteristic (phi j) ⊤ R) =o[atTop] id :=
    hcharSum.const_mul_left (2 * Real.pi)
  have hslope : 0 < (Real.pi / 3) * c := mul_pos (div_pos Real.pi_pos (by norm_num)) hc
  have hupper := hscaled.bound (half_pos hslope)
  obtain ⟨R, ⟨hRlower, hRupper⟩, hR⟩ := Filter.Eventually.exists
    ((hlower.and hupper).and (eventually_ge_atTop (1 : ℝ)))
  let g : Fin n → ℝ → ℝ := fun j θ =>
    Real.posLog ‖phi j (circleMap 0 R θ)‖
  have hfull : ∀ j, IntervalIntegrable (g j) MeasureTheory.volume
      0 (2 * Real.pi) := by
    intro j
    exact MeromorphicOn.circleIntegrable_posLog_norm (fun z _ => hphi j z)
  have harc : ∀ j, IntervalIntegrable (g j) MeasureTheory.volume
      0 (Real.pi / 3) := by
    intro j
    apply (hfull j).mono_set
    rw [Set.uIcc_of_le (le_of_lt (div_pos Real.pi_pos (by norm_num))),
      Set.uIcc_of_le (le_of_lt (mul_pos (by norm_num) Real.pi_pos))]
    intro θ hθ
    constructor
    · exact hθ.1
    · exact hθ.2.trans (by nlinarith [Real.pi_pos])
  have harcSum : IntervalIntegrable (fun θ => ∑ j, g j θ)
      MeasureTheory.volume 0 (Real.pi / 3) := by
    classical
    induction (Finset.univ : Finset (Fin n)) using Finset.induction with
    | empty => simp
    | @insert j s hj ih =>
        simpa only [Finset.sum_insert hj] using (harc j).add ih
  have hconst : IntervalIntegrable (fun _ : ℝ => c * R)
      MeasureTheory.volume 0 (Real.pi / 3) := intervalIntegrable_const
  have hintegrated :
      (∫ _ : ℝ in 0..Real.pi / 3, c * R) ≤
        ∫ θ : ℝ in 0..Real.pi / 3, ∑ j, g j θ := by
    apply intervalIntegral.integral_mono_ae_restrict
      (le_of_lt (div_pos Real.pi_pos (by norm_num))) hconst harcSum
    exact hRlower
  have harc_le_full : ∀ j,
      (∫ θ : ℝ in 0..Real.pi / 3, g j θ) ≤
        ∫ θ : ℝ in 0..2 * Real.pi, g j θ := by
    intro j
    apply intervalIntegral.integral_mono_interval
      (le_refl 0) (le_of_lt (div_pos Real.pi_pos (by norm_num)))
      (by nlinarith [Real.pi_pos])
    · exact Filter.Eventually.of_forall fun θ => Real.posLog_nonneg
    · exact hfull j
  have hproxChar : ∀ j,
      (∫ θ : ℝ in 0..2 * Real.pi, g j θ) ≤
        (2 * Real.pi) * characteristic (phi j) ⊤ R := by
    intro j
    rw [show (∫ θ : ℝ in 0..2 * Real.pi, g j θ) =
        (2 * Real.pi) * proximity (phi j) ⊤ R by
      exact fullCircleIntegral_eq_twoPi_mul_proximity (f := phi j) R]
    exact mul_le_mul_of_nonneg_left (proximity_le_characteristic hR)
      (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hlowerScaled : (Real.pi / 3) * c * R ≤
      (2 * Real.pi) * ∑ j, characteristic (phi j) ⊤ R := by
    calc
      (Real.pi / 3) * c * R = ∫ _ : ℝ in 0..Real.pi / 3, c * R := by
        rw [intervalIntegral.integral_const]
        ring
      _ ≤ ∫ θ : ℝ in 0..Real.pi / 3, ∑ j, g j θ := hintegrated
      _ = ∑ j, ∫ θ : ℝ in 0..Real.pi / 3, g j θ := by
        exact intervalIntegral.integral_finsetSum
          (fun j _ => harc j)
      _ ≤ ∑ j, ∫ θ : ℝ in 0..2 * Real.pi, g j θ :=
        Finset.sum_le_sum fun j _ => harc_le_full j
      _ ≤ ∑ j, (2 * Real.pi) * characteristic (phi j) ⊤ R :=
        Finset.sum_le_sum fun j _ => hproxChar j
      _ = (2 * Real.pi) * ∑ j, characteristic (phi j) ⊤ R := by
        rw [Finset.mul_sum]
  have hscaledNonneg :
      0 ≤ (2 * Real.pi) * ∑ j, characteristic (phi j) ⊤ R := by
    exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Finset.sum_nonneg fun j _ => characteristic_nonneg hR)
  rw [Real.norm_eq_abs, abs_of_nonneg hscaledNonneg] at hRupper
  change (2 * Real.pi) * ∑ j, characteristic (phi j) ⊤ R ≤
    (Real.pi / 3 * c / 2) * |R| at hRupper
  rw [abs_of_nonneg (zero_le_one.trans hR)] at hRupper
  have hslopeRpos : 0 < (Real.pi / 3) * c * R :=
    mul_pos hslope (zero_lt_one.trans_le hR)
  linarith

/-- Pointwise form of the right-arc positive-log obstruction. -/
theorem not_eventually_linear_le_sum_posLog_on_rightArc {n : ℕ}
    (phi : Fin n → ℂ → ℂ) (hphi : ∀ j, Meromorphic (phi j))
    (hsmall : ∀ j, characteristic (phi j) ⊤ =o[atTop] id)
    {c : ℝ} (hc : 0 < c) :
    ¬ ∀ᶠ R in atTop, ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 3),
        c * R ≤ ∑ j, Real.posLog ‖phi j (circleMap 0 R θ)‖ := by
  intro h
  apply not_eventually_ae_linear_le_sum_posLog_on_rightArc phi hphi hsmall hc
  filter_upwards [h] with R hR
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with theta htheta
  exact hR theta htheta

/-- Exponential size almost everywhere on the right arc is impossible for a finite small-growth
meromorphic family.  The finite-sum `log 2` loss is absorbed into half of the positive exponential
slope. -/
theorem not_eventually_ae_exp_le_sum_norm_on_rightArc {n : ℕ}
    (phi : Fin n → ℂ → ℂ) (hphi : ∀ j, Meromorphic (phi j))
    (hsmall : ∀ j, characteristic (phi j) ⊤ =o[atTop] id)
    {c : ℝ} (hc : 0 < c) :
    ¬ ∀ᶠ R in atTop, ∀ᵐ θ ∂MeasureTheory.volume.restrict
        (Set.Icc (0 : ℝ) (Real.pi / 3)),
      Real.exp (c * R) ≤ ∑ j, ‖phi j (circleMap 0 R θ)‖ := by
  intro hexp
  apply not_eventually_ae_linear_le_sum_posLog_on_rightArc phi hphi hsmall (half_pos hc)
  filter_upwards [hexp, eventually_ge_atTop
    (max 0 (2 * (n : ℝ) * Real.log 2 / c))] with R hRexp hR
  filter_upwards [hRexp] with θ hthetaExp
  have hR0 : 0 ≤ R := (le_max_left _ _).trans hR
  have hposLogExp : Real.posLog (Real.exp (c * R)) = c * R := by
    rw [Real.posLog, Real.log_exp, max_eq_right]
    exact mul_nonneg hc.le hR0
  have hsumNonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ ‖phi j (circleMap 0 R θ)‖ := fun j _ => norm_nonneg _
  have hsplit := posLog_sum_le (Finset.univ : Finset (Fin n))
    (fun j => ‖phi j (circleMap 0 R θ)‖) hsumNonneg
  have hmono : Real.posLog (Real.exp (c * R)) ≤
      Real.posLog (∑ j, ‖phi j (circleMap 0 R θ)‖) :=
    Real.posLog_le_posLog (Real.exp_pos _).le hthetaExp
  have hconstant : 2 * (n : ℝ) * Real.log 2 ≤ c * R := by
    have hc0 : 0 ≤ c := hc.le
    have hthreshold : 2 * (n : ℝ) * Real.log 2 / c ≤ R :=
      (le_max_right _ _).trans hR
    rw [div_le_iff₀ hc] at hthreshold
    simpa [mul_comm] using hthreshold
  rw [hposLogExp] at hmono
  have hcard : ((Finset.univ : Finset (Fin n)).card : ℝ) = n := by simp
  rw [hcard] at hsplit
  linarith

/-- Pointwise exponential form of the right-arc obstruction. -/
theorem not_eventually_exp_le_sum_norm_on_rightArc {n : ℕ}
    (phi : Fin n → ℂ → ℂ) (hphi : ∀ j, Meromorphic (phi j))
    (hsmall : ∀ j, characteristic (phi j) ⊤ =o[atTop] id)
    {c : ℝ} (hc : 0 < c) :
    ¬ ∀ᶠ R in atTop, ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 3),
        Real.exp (c * R) ≤ ∑ j, ‖phi j (circleMap 0 R θ)‖ := by
  intro h
  apply not_eventually_ae_exp_le_sum_norm_on_rightArc phi hphi hsmall hc
  filter_upwards [h] with R hR
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with theta htheta
  exact hR theta htheta

end

end GaloisForLFunctions.HTGeometry
