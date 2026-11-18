import GaloisForLFunctions.ExceptionalLayerTheory.TheWeightedMassOfTheSignedPrimeIncrement
import GaloisForLFunctions.ExceptionalLayerTheory.ABoundedPrimeRadiusSeparatesTheTopPairFromTheOtherZeros

/-!
# Weighted ordinary-prime increments and the zeros below the extremal pair

The one-step difference controls the exponentially weighted mass of the
subtracted error itself. Its Chebyshev tail bounds the subtracted lag, whose
Laplace transform has a pole at every remaining right zero.
-/

noncomputable section
open Filter Topology Set MeasureTheory RHTower
open GaloisForLFunctions.ZeroConfigurationGeometry
open _root_.HTGeometry
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Summing the one-step inequality in weighted integral norm absorbs the
translated mass with coefficient exp(−s h)<1. -/
private theorem integrable_weighted_of_step {E : ℝ → ℝ} {h s T : ℝ}
    (hh : 0 < h) (hs : 0 < s) (hi : ∀ a b, IntervalIntegrable E volume a b)
    (hstep : IntegrableOn (fun t => Real.exp (-s*t)*(E (t+h)-E t)) (Ioi T)) :
    IntegrableOn (fun t => Real.exp (-s*t)*E t) (Ioi T) := by
  let g := fun t => Real.exp (-s*t)*E t
  let v := fun t => Real.exp (-s*t)*(E (t+h)-E t)
  let q := Real.exp (-s*h)
  let F := fun y => ∫ t in T..y, ‖g t‖
  let V := ∫ t in Ioi T, ‖v t‖
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) hh)
  have hgi (a b : ℝ) : IntervalIntegrable g volume a b := (hi a b).continuousOn_mul (by fun_prop)
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded ((F (T+h)+q*V)/(1-q)) T
    (b := fun y : ℝ => y+h) (fun y => (hgi _ _).1)
    (tendsto_atTop_add_const_right _ _ tendsto_id)
  filter_upwards [eventually_ge_atTop T] with y hTy
  have hv : IntervalIntegrable v volume T y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hTy).mpr (hstep.mono_set Ioc_subset_Ioi_self)
  have hi' : IntervalIntegrable (fun t => g (t+h)) volume T y := by
    simpa only [add_sub_cancel_right] using (hgi (T+h) (y+h)).comp_add_right h
  have hlocal := intervalIntegral.integral_mono_on hTy hi'.norm
    (((hgi T y).norm.add hv.norm).const_mul q) (fun t _ => by
      have he : g (t+h) = q*(g t+v t) := by
        dsimp only [g,v,q]
        rw [mul_add,Real.exp_add]
        ring
      rw [he,norm_mul,Real.norm_of_nonneg hq.le]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hq.le)
  rw [intervalIntegral.integral_comp_add_right (fun t => ‖g t‖),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hgi T y).norm hv.norm] at hlocal
  have hvi : (∫ t in T..y, ‖v t‖) ≤ V := by
    rw [intervalIntegral.integral_of_le hTy]
    exact setIntegral_mono_set hstep.norm (.of_forall fun _ => norm_nonneg _) (.of_forall Ioc_subset_Ioi_self)
  have hF : F y ≤ F (y+h) := by
    dsimp only [F]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgi T y).norm (hgi y (y+h)).norm]
    exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg
      (le_add_of_nonneg_right hh.le) fun t _ => norm_nonneg _)
  have hmain : F (y+h) ≤ F (T+h)+q*(F (y+h)+V) := by
    have he : F (y+h) = F (T+h) + ∫ t in T+h..y+h, ‖g t‖ :=
      (intervalIntegral.integral_add_adjacent_intervals (hgi T (T+h)).norm (hgi _ _).norm).symm
    have H := hlocal.trans (mul_le_mul_of_nonneg_left (add_le_add hF hvi) hq.le)
    exact he.trans_le (add_le_add le_rfl H)
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  change F (y+h)*(1-q) ≤ _
  linarith only [hmain]

private theorem intervalIntegrable_subtractedTheta {β : ℝ} (hβ : 1/2 < β) (a b : ℝ) :
    IntervalIntegrable (subtractedTheta β) volume a b := by
  have hF : Continuous (primeErrorBoundaryTrace β) := by
    rw [funext (primeErrorBoundaryTrace_eq_re_expSeries β)]
    exact Complex.continuous_re.comp (continuous_expSeriesCarrier (summable_primeErrorBoundaryAmplitude hβ) _)
  have hθ : Monotone (fun t : ℝ => Chebyshev.theta (Real.exp t)) :=
    Chebyshev.theta_mono.comp Real.exp_monotone
  exact (hθ.intervalIntegrable.sub Real.continuous_exp.intervalIntegrable).sub
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hF).intervalIntegrable)

/-- Absolute weighted integrability of the unsmoothed ordinary-prime error
after its extremal zero contribution is removed. -/
theorem integrableOn_tail_subtractedTheta {γ s : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hs : 1/2 < s) (hγ : γ ≠ 0) (hm : 1 ≤ m)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)) :
    ∃ T : ℝ, 0 ≤ T ∧ IntegrableOn (fun t => Real.exp (-s*t)*subtractedTheta zetaZeroAbscissa t) (Ioi T) := by
  let β := zetaZeroAbscissa
  let h := quarterPeriodStep γ
  obtain ⟨T,hT,hi⟩ := integrableOn_tail_signed_prime_increment hΘ hs hγ hm hb
  refine ⟨T,hT,integrable_weighted_of_step (quarterPeriodStep_pos hγ)
    (by linarith only [hs] : 0 < s) (intervalIntegrable_subtractedTheta hΘ) ?_⟩
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  rw [subtractedTheta_step,← mul_assoc,← Real.exp_add,show -s*t+β*t=(β-s)*t by ring]

private theorem weighted_theta_mass {γ s : ℝ} {m : ℕ} (hΘ : 1/2 < zetaZeroAbscissa)
    (hs : 1/2 < s) (hγ : γ ≠ 0) (hm : 1 ≤ m)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)) :
    let S := (finite_top_of_bounded_thetaRadial hΘ hγ hb).toFinset
    IntegrableOn (fun x : ℝ => |Chebyshev.theta x-x+(offLineWave S x).re| * x^(-s-1)) (Ioi 1) := by
  classical
  intro S
  let β := zetaZeroAbscissa
  let g := fun t => Real.exp (-s*t)*subtractedTheta β t
  obtain ⟨T,hT,hi⟩ := integrableOn_tail_subtractedTheta hΘ hs hγ hm hb
  have hpiece : IntervalIntegrable g volume 0 T :=
    (intervalIntegrable_subtractedTheta hΘ 0 T).continuousOn_mul (by fun_prop)
  have hg : IntegrableOn g (Ioi 0) := (hpiece.1.union hi).mono_set (by
    intro t ht
    rcases le_or_gt t T with h | h
    · exact Or.inl ⟨ht,h⟩
    · exact Or.inr h)
  have hset : Real.exp '' Ioi 0 = Ioi 1 := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact Real.one_lt_exp_iff.mpr ht
    · intro hx
      exact ⟨Real.log x,Real.log_pos hx,Real.exp_log (zero_lt_one.trans hx)⟩
  rw [← hset, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  apply hg.norm.congr_fun _ measurableSet_Ioi
  intro t _
  have hf := finite_top_of_bounded_thetaRadial hΘ hγ hb
  dsimp only [g,subtractedTheta,thetaLogError]
  rw [mul_exp_boundaryTrace_eq_neg_top_wave hf,sub_neg_eq_add,norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    smul_eq_mul,← Real.exp_mul]
  have he : Real.exp (-s*t) = Real.exp t * Real.exp (t*(-s-1)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  ring

/-- Weighted absolute mass of the corrected ordinary-prime count bounds the
subtracted lag. The order θ≤ψ supplies the required one-sided inequality. -/
private theorem re_le_of_weighted_theta_mass (S : Finset XiZeroCopy) {s : ℝ}
    (hs : 1/2 < s) (hs1 : s < 1)
    (hG : IntegrableOn (fun x : ℝ => |Chebyshev.theta x-x+(offLineWave S x).re| * x^(-s-1)) (Ioi 1))
    (q : XiZeroCopy) (hq : lagPole q ∉ offLinePoles S) : (q.1 : ℂ).re ≤ s := by
  let G := fun x : ℝ => |Chebyshev.theta x-x+(offLineWave S x).re| * x^(-s-1)
  let P := fun x => chebyshevError x+(offLineWave S x).re
  let M := ∫ x in Ioi 1, G x
  have htail (x : ℝ) (hx : 1 < x) :
      -(∫ y in Ioi x, P y / y^2) ≤ x^(s-1)*M := by
    have hx0 := zero_lt_one.trans hx
    have hsub : Ioi x ⊆ Ioi (1:ℝ) := Ioi_subset_Ioi hx.le
    have hint : IntegrableOn (fun y => P y / y^2) (Ioi x) := by
      have H := (integrableOn_chebyshevError_div_sq.mono_set hsub).add
        (mul_integral_offLineWave_re_div_sq S hx0).1
      exact H.congr_fun (fun y _ => (add_div _ _ _).symm) measurableSet_Ioi
    have hpos (y : ℝ) (hy : 1 < y) : 0 ≤ G y :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hy).le _)
    have hpow := Real.rpow_nonneg hx0.le (s-1)
    have hle (y : ℝ) (hy : y ∈ Ioi x) : -(P y / y^2) ≤ x^(s-1)*G y := by
      have hy0 := hx0.trans hy
      have htheta : -(P y) ≤ |Chebyshev.theta y-y+(offLineWave S y).re| := by
        have H : Chebyshev.theta y-y+(offLineWave S y).re ≤ P y :=
          add_le_add (sub_le_sub_right (Chebyshev.theta_le_psi _) _) le_rfl
        exact (neg_le_neg H).trans (neg_le_abs _)
      have he : 1/y^2 = y^(s-1)*y^(-s-1) := by
        rw [← Real.rpow_add hy0,show s-1+(-s-1) = -(2:ℝ) by ring,
          Real.rpow_neg hy0.le,Real.rpow_two,one_div]
      calc _ ≤ |Chebyshev.theta y-y+(offLineWave S y).re| * (1/y^2) := by
               simpa only [← neg_div,mul_one_div] using
                 div_le_div_of_nonneg_right htheta (sq_nonneg y)
        _ = y^(s-1)*G y := by rw [he]; dsimp only [G]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hx0 hy.le (sub_nonpos.mpr hs1.le))
          (hpos y (hx.trans hy))
    have H := setIntegral_mono_on hint.neg ((hG.mono_set hsub).const_mul (x^(s-1)))
      measurableSet_Ioi hle
    rw [integral_neg,integral_const_mul] at H
    refine H.trans (mul_le_mul_of_nonneg_left ?_ hpow)
    exact setIntegral_mono_set hG (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy; exact hpos y hy)
      (.of_forall hsub)
  have hlarge (u : ℝ) (hu : 0 < u) : subtractedLag S u ≤ M*Real.exp ((s-1/2)*u) := by
    let x := Real.exp u
    have hx : 1 < x := Real.one_lt_exp_iff.mpr hu
    have hid := subtractedLag_log_mul_sqrt S hx
    have ht := mul_le_mul_of_nonneg_left (htail x hx) (Real.exp_pos u).le
    change subtractedLag S (Real.log x)*Real.sqrt x =
      -(x*∫ y in Ioi x, P y/y^2)-Real.log (2*Real.pi)+trivialZeroSeriesReal x at hid
    rw [show Real.log x = u from Real.log_exp u] at hid
    have hpow : x*(x^(s-1)*M) = (M*Real.exp ((s-1/2)*u))*Real.sqrt x := by
      dsimp only [x]
      rw [← Real.exp_mul,← Real.exp_half]
      calc _ = M*Real.exp (u+u*(s-1)) := by rw [Real.exp_add]; ring
        _ = M*Real.exp ((s-1/2)*u+u/2) := by congr 2; ring
        _ = _ := by rw [Real.exp_add]; ring
    rw [hpow] at ht
    apply (mul_le_mul_iff_of_pos_right (Real.sqrt_pos.mpr (Real.exp_pos u))).mp
    linarith only [hid,ht,trivialZeroSeriesReal_le_one hx.le,one_lt_log_two_pi]
  have hbound (u : ℝ) (hu : 0 ≤ u) : subtractedLag S u ≤
      max M (subtractedLag S 0)*Real.exp ((s-1/2)*u) := by
    rcases hu.eq_or_lt with he | h
    · subst u
      simpa only [mul_zero,Real.exp_zero,mul_one] using le_max_right M (subtractedLag S 0)
    · exact (hlarge u h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have H := re_le_half_add_of_subtractedLag_le_exp S (sub_nonneg.mpr hs.le)
    (by linarith only [hs1]) hbound q hq
  linarith only [H]

/-- A bounded two-interval trial at a supercritical extremal line excludes
every zero strictly between that line and the critical line. -/
theorem re_le_half_of_bounded_radius_of_not_top {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hγ : γ ≠ 0) (hm : 1 ≤ m)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m))
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ zetaZeroAbscissa) : (q.1 : ℂ).re ≤ 1/2 := by
  by_contra! hqhalf
  obtain ⟨s,hs,hsq⟩ := exists_between hqhalf
  let hf := finite_top_of_bounded_thetaRadial hΘ hγ hb
  exact hsq.not_ge (re_le_of_weighted_theta_mass hf.toFinset hs (hsq.trans (xiZeroCopy_re_lt_one q))
    (weighted_theta_mass hΘ hs hγ hm hb) q (lagPole_notMem_linePoles_of_ne_re hf q hq))

/-- Bounded discrepancy forces finiteness of the entire off-line divisor. -/
theorem finite_offLine_copies_of_bounded_radius {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hγ : γ ≠ 0) (hm : 1 ≤ m)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m)) :
    {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1/2}.Finite := by
  classical
  let hf := finite_top_of_bounded_thetaRadial hΘ hγ hb
  apply finite_offLine_of_re_le_half_off_offLinePoles hf.toFinset
  intro q hq
  refine re_le_half_of_bounded_radius_of_not_top hΘ hγ hm hb q (fun he => hq ?_)
  exact Or.inl ⟨q,hf.mem_toFinset.mpr he,rfl⟩

#print axioms integrableOn_tail_subtractedTheta
#print axioms re_le_half_of_bounded_radius_of_not_top
#print axioms finite_offLine_copies_of_bounded_radius

end GaloisForLFunctions.ExceptionalLayerTheory
