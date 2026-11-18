import GaloisForLFunctions.ExceptionalLayerTheory.TheBoundaryTraceOfTheTwoIntervalPrimeRadius
import GaloisForLFunctions.HTGeometry.AllScaleIntegralConformalTraceRigidity

/-!
# The squared ordinary-prime increment tracks its extremal trace

Subtracting adjacent squared radii isolates a difference over two steps.
Its forward tail converges geometrically at every supercritical extremal exponent.
-/

noncomputable section
open Filter Topology Complex RHTower
open GaloisForLFunctions.ZeroConfigurationGeometry
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Forward integration of a difference whose envelope contracts under translation. -/
private theorem abs_le_of_decaying_step {g w : ℝ → ℝ} {p q K T : ℝ}
    (hp : 0 < p) (hq : q < 1) (hK : 0 ≤ K)
    (hg : Tendsto g atTop (𝓝 0)) (hw : Tendsto w atTop (𝓝 0))
    (hdec : ∀ t, T ≤ t → w (t+p) ≤ q*w t)
    (hd : ∀ t, T ≤ t → |g t-g (t+p)| ≤ K*w t) :
    ∀ t, T ≤ t → |g t| ≤ (K/(1-q))*w t := by
  let B := K/(1-q)
  have hB : 0 ≤ B := div_nonneg hK (sub_pos.mpr hq).le
  have hBK : B*(1-q) = K := div_mul_cancel₀ _ (sub_pos.mpr hq).ne'
  let f := fun t => |g t|-B*w t
  have hstep (t : ℝ) (ht : T ≤ t) : f t ≤ f (t+p) := by
    have h1 := (abs_sub_abs_le_abs_sub (g t) (g (t+p))).trans (hd t ht)
    have h2 := mul_le_mul_of_nonneg_left (hdec t ht) hB
    have h3 := congrArg (fun a : ℝ => a*w t) hBK
    dsimp only [f]
    linarith only [h1,h2,h3]
  have hlim : Tendsto f atTop (𝓝 0) := by
    simpa only [abs_zero,mul_zero,sub_zero] using hg.abs.sub (hw.const_mul B)
  intro t ht
  have hit (n : ℕ) : f t ≤ f (t+n*p) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc]
      exact ih.trans (hstep _ (ht.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hp.le))))
  have hlat : Tendsto (fun n : ℕ => t+n*p) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const hp)
  exact sub_nonpos.mp (le_of_tendsto_of_tendsto' tendsto_const_nhds (hlim.comp hlat) hit)

private def radialWeight (d t : ℝ) := Real.exp (-d*t)*(1+t)^2

private theorem radialWeight_contracts {d h : ℝ} (hd : 0 < d) (hh : 0 < h) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ᶠ t : ℝ in atTop, radialWeight d (t+h) ≤ q*radialWeight d t := by
  let b := Real.exp (d*h/4)
  have hb : 1 < b := Real.one_lt_exp_iff.mpr (by positivity)
  let q := Real.exp (-(d*h)/2)
  have hq : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [mul_pos hd hh])
  refine ⟨q,Real.exp_pos _,hq,?_⟩
  filter_upwards [eventually_ge_atTop (max 0 (h/(b-1)))] with t ht
  have ht0 := (le_max_left _ _).trans ht
  have ht1 := (div_le_iff₀ (sub_pos.mpr hb)).mp ((le_max_right _ _).trans ht)
  have hscale : 1+(t+h) ≤ b*(1+t) := by nlinarith only [ht1,hb]
  have hrs : Real.exp (-d*h)*b^2 = q := by
    rw [show b^2 = Real.exp (d*h/4+d*h/4) by rw [Real.exp_add, sq]]
    rw [← Real.exp_add]
    congr 1
    ring
  unfold radialWeight
  rw [mul_add, Real.exp_add]
  calc _ ≤ (Real.exp (-d*t)*Real.exp (-d*h)) * (b*(1+t))^2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale 2) (by positivity)
    _ = q*(Real.exp (-d*t)*(1+t)^2) := by rw [← hrs]; ring

private theorem tendsto_radialWeight {d : ℝ} (hd : 0 < d) :
    Tendsto (radialWeight d) atTop (𝓝 0) := by
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 d hd).const_mul 4
  rw [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ radialWeight d t by unfold radialWeight; positivity),
    Real.rpow_two]
  have hsq : (1+t)^2 ≤ 4*t^2 := by nlinarith only [ht,sq_nonneg (t-1)]
  dsimp only [radialWeight]
  calc _ ≤ Real.exp (-d*t)*(4*t^2) :=
            mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = _ := by ring

/-- An asymptotically matched signed component inherits the radial discrepancy
in its square. Subtraction of consecutive squared radii gives a difference
over two steps, whose exponentially decaying tail can be integrated forwards. -/
private theorem squared_trace_rate {U D R : ℝ → ℝ} {h d C K : ℝ}
    (hh : 0 < h) (hd : 0 < d) (hK : 0 ≤ K)
    (hU : Tendsto (fun t => U t - D t) atTop (𝓝 0))
    (hcircle : ∀ t, D t ^ 2 + D (t+h)^2 = C^2)
    (hR : ∀ t, U t ^ 2 + U (t+h)^2 = R t ^ 2)
    (hbound : ∀ᶠ t : ℝ in atTop, |R t-C| ≤ K * radialWeight d t) :
    ∃ L : ℝ, ∀ᶠ t : ℝ in atTop, |U t^2-D t^2| ≤ L * radialWeight d t := by
  let w := radialWeight d
  let g := fun t => U t^2-D t^2
  let B := K*(2*|C|+1)
  have hw0 (t : ℝ) : 0 ≤ w t := by dsimp [w, radialWeight]; positivity
  have hw := tendsto_radialWeight hd
  have hRlim : Tendsto (fun t => R t-C) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa only [mul_zero] using hw.const_mul K)
    simpa only [Real.norm_eq_abs] using hbound
  have habsR : ∀ᶠ t : ℝ in atTop, |R t-C| ≤ 1 := by
    exact (hRlim.abs.eventually
      (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))).mono fun _ h => h.le
  have habsU : ∀ᶠ t : ℝ in atTop, |U t-D t| ≤ 1 :=
    (hU.abs.eventually (gt_mem_nhds (by norm_num : |(0:ℝ)| < 1))).mono fun _ h => h.le
  have hDabs (t : ℝ) : |D t| ≤ |C| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs,sq_abs]
    linarith only [hcircle t,sq_nonneg (D (t+h))]
  have hplus (x y : ℝ) : |x+y| ≤ |x-y|+2*|y| := by
    calc _ = |(x-y)+(y+y)| := by congr 1; ring
      _ ≤ |x-y|+(|y|+|y|) := (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ = _ := by ring
  have hg : Tendsto g atTop (𝓝 0) := by
    have hlim := hU.abs.mul_const (1+2*|C|)
    rw [abs_zero,zero_mul] at hlim
    apply squeeze_zero_norm' _ hlim
    filter_upwards [habsU] with t ht
    rw [Real.norm_eq_abs,show g t = (U t-D t)*(U t+D t) by dsimp [g]; ring,abs_mul]
    exact mul_le_mul_of_nonneg_left ((hplus _ _).trans
      (add_le_add ht (mul_le_mul_of_nonneg_left (hDabs t) (by norm_num)))) (abs_nonneg _)
  have hsum : ∀ᶠ t : ℝ in atTop, |g t+g (t+h)| ≤ B*w t := by
    filter_upwards [habsR,hbound] with t ht hr
    have he : g t+g (t+h) = (R t-C)*(R t+C) := by
      dsimp only [g]
      linear_combination hR t - hcircle t
    rw [he, abs_mul]
    calc _ ≤ K*w t*(1+2*|C|) := mul_le_mul hr ((hplus _ _).trans
              (add_le_add_right ht _)) (abs_nonneg _) (mul_nonneg hK (hw0 t))
      _ = B*w t := by dsimp only [B]; ring
  obtain ⟨q,hq,hq1,hcontract⟩ := radialWeight_contracts hd hh
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hsum.and hcontract)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hstep (t : ℝ) (ht : T ≤ t) : |g t-g (t+2*h)| ≤ (2*B)*w t := by
    have hs := (hT t ht).1
    have ht' := (hT (t+h) (ht.trans (le_add_of_nonneg_right hh.le))).1
    have hw' : w (t+h) ≤ w t := ((hT t ht).2).trans (mul_le_of_le_one_left (hw0 t) hq1.le)
    rw [show g t-g (t+2*h) = (g t+g (t+h))-(g (t+h)+g (t+h+h)) by
          rw [show t+2*h=t+h+h by ring]; ring]
    exact (show |(g t+g (t+h))-(g (t+h)+g (t+h+h))| ≤ |g t+g (t+h)|+|g (t+h)+g (t+h+h)| by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (g t+g (t+h)) 0 (g (t+h)+g (t+h+h))).trans (by
      have hb := add_le_add hs (ht'.trans (mul_le_mul_of_nonneg_left hw' hB))
      linarith only [hb])
  have hdec (t : ℝ) (ht : T ≤ t) : w (t+2*h) ≤ q^2*w t := by
    rw [show t+2*h=t+h+h by ring, sq, mul_assoc]
    exact ((hT (t+h) (ht.trans (le_add_of_nonneg_right hh.le))).2).trans
      (mul_le_mul_of_nonneg_left ((hT t ht).2) hq.le)
  refine ⟨_, eventually_atTop.mpr ⟨T,?_⟩⟩
  exact abs_le_of_decaying_step (mul_pos zero_lt_two hh)
    (by nlinarith only [mul_pos (sub_pos.mpr hq1) (add_pos hq zero_lt_one)] : q^2 < 1)
    (mul_nonneg (by norm_num) hB) hg hw hdec hstep

/-- The ordinary-prime increment with its extremal exponential power divided out. -/
def normalizedPrimeIncrement (β h t : ℝ) : ℝ :=
  logStepIncrement thetaLogError t h / Real.exp (β*t)

private theorem normalized_increment_sub_trace (hΘ : 1/2 < zetaZeroAbscissa) (h : ℝ) :
    Tendsto (fun t => normalizedPrimeIncrement zetaZeroAbscissa h t -
      boundaryStep zetaZeroAbscissa h (primeErrorBoundaryTrace zetaZeroAbscissa) t)
      atTop (𝓝 0) := by
  let β := zetaZeroAbscissa
  let E := fun t => thetaLogError t / Real.exp (β*t)
  let F := primeErrorBoundaryTrace β
  have hsmall : Asymptotics.IsLittleO atTop Real.sqrt (fun x : ℝ => x^β) := by
    simpa only [← Real.sqrt_eq_rpow] using rpow_isLittleO_rpow_atTop_of_lt hΘ
  have hθ := (tendsto_normalized_primeError_sub_boundary hΘ).sub
    ((Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsmall).tendsto_div_nhds_zero)
  rw [sub_zero] at hθ
  have hEF : Tendsto (fun t => E t-F t) atTop (𝓝 0) := by
    apply (hθ.comp Real.tendsto_exp_atTop).congr
    intro t
    simp only [Function.comp_def, Pi.sub_apply, Real.rpow_def_of_pos (Real.exp_pos _),
      Real.log_exp, E, F, thetaLogError]
    change _ = (Chebyshev.theta (Real.exp t)-Real.exp t)/Real.exp (β*t)-primeErrorBoundaryTrace β t
    dsimp only [β]
    rw [mul_comm t zetaZeroAbscissa]
    ring
  have hshift : Tendsto (fun t : ℝ => t+h) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have ht := ((hEF.comp hshift).const_mul (Real.exp (β*h))).sub hEF
  rw [mul_zero,sub_zero] at ht
  apply ht.congr
  intro t
  simp only [Function.comp_apply, E, F, boundaryStep, normalizedPrimeIncrement, logStepIncrement,
    mul_add, Real.exp_add]
  field_simp
  <;> ring

/-- Bounded radial discrepancy controls the individual squared increment to the
same normalized square-root accuracy, uniformly at all sufficiently late times. -/
theorem squared_normalizedPrimeIncrement_sub_boundary {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hγ : γ ≠ 0)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)) :
    let β := zetaZeroAbscissa
    let h := quarterPeriodStep γ
    let D := boundaryStep β h (primeErrorBoundaryTrace β)
    ∃ L : ℝ, ∀ᶠ t : ℝ in atTop, |normalizedPrimeIncrement β h t ^ 2 - D t ^ 2| ≤
      L * (Real.exp (-(β-1/2)*t)*(1+t)^2) := by
  intro β h D
  let A := Real.exp (β*h)
  let C := quartetRadialCoeff β γ m
  let U := normalizedPrimeIncrement β h
  let R := fun t => twoIntervalRadius thetaLogError h A t / Real.exp (β*t)
  have hR (t : ℝ) : U t^2+U (t+h)^2 = R t^2 := by
    dsimp only [U,R,normalizedPrimeIncrement]
    rw [twoIntervalRadius_eq_complex_norm (Real.exp_pos _), div_pow, Complex.sq_norm,
      Complex.normSq_mk]
    dsimp only [A]
    rw [mul_add,Real.exp_add]
    field_simp
    <;> ring
  have hbounded := hb
  rw [isLogSqrtSqUnbounded_iff_not_eventually_le, not_not] at hbounded
  obtain ⟨K,T,hK⟩ := hbounded
  have hscale (t : ℝ) : R t-C = thetaRadialDiscrepancy β γ m t / Real.exp (β*t) := by
    dsimp only [R,C,thetaRadialDiscrepancy,radialDiscrepancyOf,quarterPeriodScale,A]
    rw [sub_div,mul_div_cancel_right₀ _ (Real.exp_pos _).ne']
  have hbound : ∀ᶠ t : ℝ in atTop, |R t-C| ≤ |K|*radialWeight (β-1/2) t := by
    filter_upwards [eventually_ge_atTop T] with t ht
    rw [hscale,abs_div,abs_of_pos (Real.exp_pos _)]
    calc _ ≤ (|K|*Real.exp (t/2)*(1+t)^2)/Real.exp (β*t) :=
               div_le_div_of_nonneg_right ((hK t ht).trans
                 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K)
                   (Real.exp_pos _).le) (sq_nonneg _))) (Real.exp_pos _).le
      _ = _ := by
        rw [radialWeight,show -(β-1/2)*t=t/2-β*t by ring,Real.exp_sub]
        ring
  exact squared_trace_rate (quarterPeriodStep_pos hγ) (sub_pos.mpr hΘ) (abs_nonneg K)
    (normalized_increment_sub_trace hΘ h) (boundaryStep_circle_of_bounded_thetaRadial hΘ hb) hR hbound

#print axioms squared_normalizedPrimeIncrement_sub_boundary

end GaloisForLFunctions.ExceptionalLayerTheory
