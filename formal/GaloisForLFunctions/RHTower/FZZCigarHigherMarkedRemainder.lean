import GaloisForLFunctions.RHTower.FZZCigarCubicFinitePartExtraction
import GaloisForLFunctions.RHTower.FZZCigarCubicMarkedScreeningCutoff

/-!
# Original higher screening remainder derivatives

Both logarithmic insertions are derived from the admitted original fifth
subtraction. Neighboring powers admit the singular-factor logarithmic moment.
For the regular factor, differentiation of the exact pointwise Taylor integral
remainder retains both the descending-factorial derivative and the lifted
logarithmic moment. Joint integrability precedes Fubini and identifies the
original differentiated subtraction before differentiating its plane integral.

The full cubic Taylor-mark polynomial and its six-slot angular average are
retained, including finite radial terms. The original exterior derivative
then assembles with both distinct local derivatives into the complete cubic
regular-source derivative. Public theorems have only real or complex data;
all domain and integrability conditions are proved internally.

Original marked cutoff extraction, fractional screening continuation, complete
physical normalization, phase-frame identification and mixed Ward production
remain separate obligations. No RH conclusion is claimed here.
-/

open MeasureTheory Set Metric Filter ProbabilityTheory
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private def positiveWeightMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun z => ENNReal.ofReal (max (f z) 0))

private theorem positiveWeight_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (hX : Measurable X) (t : ℝ)
    (hi : Integrable (fun z => f z*Real.exp (t*X z)) μ) :
    Integrable (fun z => Real.exp (t*X z)) (positiveWeightMeasure μ f) := by
  rw [positiveWeightMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]
  apply hi.norm.mono' (by fun_prop)
  filter_upwards with z
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (le_max_right _ _),
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact max_le (le_abs_self _) (abs_nonneg _)

private theorem positiveWeight_integralY {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f Y : Ω → ℝ) (hf : Measurable f) :
    (∫ z, Y z ∂positiveWeightMeasure μ f) = ∫ z, max (f z) 0*Y z ∂μ := by
  rw [positiveWeightMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]

private theorem positiveWeight_integrableY {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f Y : Ω → ℝ) (hf : Measurable f)
    (hi : Integrable Y (positiveWeightMeasure μ f)) :
    Integrable (fun z => max (f z) 0*Y z) μ := by
  rw [positiveWeightMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)] at hi
  simpa only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using hi

private theorem positive_sub_negative (r : ℝ) : max r 0-max (-r) 0 = r := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr), sub_zero]
  · rw [max_eq_right (le_of_not_ge hr), max_eq_left (neg_nonneg.mpr (le_of_not_ge hr))]
    ring

private theorem positive_exp_interior {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (hX : Measurable X) (t : ℝ)
    (hi : ∀ᶠ s in 𝓝 t, Integrable (fun z => f z*Real.exp (s*X z)) μ) :
    t ∈ interior (integrableExpSet X (positiveWeightMeasure μ f)) := by
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hi] with s hs
  exact positiveWeight_integrable μ f X hf hX s hs

private theorem signed_exp_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (hX : Measurable X) (t : ℝ)
    (hi : ∀ᶠ s in 𝓝 t, Integrable (fun z => f z*Real.exp (s*X z)) μ) :
    Integrable (fun z => f z*(X z*Real.exp (t*X z))) μ ∧
      HasDerivAt (fun s => ∫ z, f z*Real.exp (s*X z) ∂μ)
        (∫ z, f z*(X z*Real.exp (t*X z)) ∂μ) t := by
  have hn : ∀ᶠ s in 𝓝 t, Integrable (fun z => (-f z)*Real.exp (s*X z)) μ := by
    filter_upwards [hi] with s hs
    convert! hs.neg using 1
    ext z
    dsimp
    ring
  have hp := positive_exp_interior μ f X hf hX t hi
  have hm := positive_exp_interior μ (fun z => -f z) X hf.neg hX t hn
  have hip : Integrable (fun z => max (f z) 0*(X z*Real.exp (t*X z))) μ := by
    apply positiveWeight_integrableY μ f _ hf
    simpa only [pow_one] using integrable_pow_mul_exp_of_mem_interior_integrableExpSet hp 1
  have him : Integrable (fun z => max (-f z) 0*(X z*Real.exp (t*X z))) μ := by
    apply positiveWeight_integrableY μ (fun z => -f z) _ hf.neg
    simpa only [pow_one] using integrable_pow_mul_exp_of_mem_interior_integrableExpSet hm 1
  have hpoint (z : Ω) (y : ℝ) :
      max (f z) 0*y-max (-f z) 0*y = f z*y := by
    rw [← sub_mul, positive_sub_negative]
  have hint : Integrable (fun z => f z*(X z*Real.exp (t*X z))) μ := by
    apply (hip.sub him).congr
    filter_upwards with z
    exact hpoint z _
  refine ⟨hint, ?_⟩
  have he : (fun s => ∫ z, f z*Real.exp (s*X z) ∂μ) =ᶠ[𝓝 t]
      (fun s => mgf X (positiveWeightMeasure μ f) s-
        mgf X (positiveWeightMeasure μ (fun z => -f z)) s) := by
    filter_upwards [hi,hn] with s hs ht
    have hsp := positiveWeight_integrableY μ f _ hf (positiveWeight_integrable μ f X hf hX s hs)
    have hsm := positiveWeight_integrableY μ (fun z => -f z) _ hf.neg
      (positiveWeight_integrable μ (fun z => -f z) X hf.neg hX s ht)
    rw [mgf, mgf, positiveWeight_integralY μ f _ hf,
      positiveWeight_integralY μ (fun z => -f z) _ hf.neg, ← integral_sub hsp hsm]
    apply integral_congr_ae
    filter_upwards with z
    exact (hpoint z _).symm
  have hd := ((hasDerivAt_mgf hp).sub (hasDerivAt_mgf hm)).congr_of_eventuallyEq he
  rw [positiveWeight_integralY μ f _ hf,
    positiveWeight_integralY μ (fun z => -f z) _ hf.neg, ← integral_sub hip him] at hd
  convert! hd using 1
  apply integral_congr_ae
  filter_upwards with z
  exact (hpoint z _).symm

private theorem fifth_admission (α β : ℝ) (ha : -8 < α) :
    IntegrableOn (fzzScreeningFifthSubtracted α β) (ball 0 (1/2)) := by
  have h := fzzScreeningFifthSubtracted_integrable (Real.log (α+8)) β
  rw [Real.exp_log (by linarith : 0 < α+8)] at h
  simpa only [show -8+(α+8)=α by ring] using h

private theorem fifth_subtracted_shift (α β δ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    fzzScreeningFifthSubtracted α β z * Real.exp (δ*Real.log ‖z‖) =
      fzzScreeningFifthSubtracted (α+δ) β z := by
  have hn := norm_pos_iff.mpr hz
  rw [show Real.exp (δ*Real.log ‖z‖) = ‖z‖^δ by rw [Real.rpow_def_of_pos hn, mul_comm]]
  unfold fzzScreeningFifthSubtracted
  rw [Real.rpow_add hn]
  ring

private theorem fifth_singular_marked_source (α β : ℝ) (ha : -8 < α) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningFifthSubtracted α β z)
      (ball 0 (1/2)) ∧
    HasDerivAt (fun δ => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted (α+δ) β z)
      (∫ z : ℂ in ball 0 (1/2), Real.log ‖z‖*fzzScreeningFifthSubtracted α β z) 0 := by
  have hshift : ∀ᶠ δ : ℝ in 𝓝 0, -8 < α+δ :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simpa using ha)
  have hi : ∀ᶠ δ : ℝ in 𝓝 0, Integrable
      (fun z => fzzScreeningFifthSubtracted α β z*Real.exp (δ*Real.log ‖z‖))
        (volume.restrict (ball 0 (1/2))) := by
    filter_upwards [hshift] with δ hδ
    apply (fifth_admission (α+δ) β hδ).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (fifth_subtracted_shift α β δ hz).symm
  have h := signed_exp_hasDerivAt (volume.restrict (ball (0 : ℂ) (1/2)))
    (fzzScreeningFifthSubtracted α β) (fun z => Real.log ‖z‖)
    (by unfold fzzScreeningFifthSubtracted fzzScreeningFifthTaylor; fun_prop) (by fun_prop) 0 hi
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  have he : (fun δ => ∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted (α+δ) β z) =ᶠ[𝓝 0]
      (fun δ => ∫ z : ℂ in ball 0 (1/2),
        fzzScreeningFifthSubtracted α β z*Real.exp (δ*Real.log ‖z‖)) := by
    filter_upwards with δ
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (fifth_subtracted_shift α β δ hz).symm
  constructor
  · simpa only [IntegrableOn, mul_comm] using h.1
  · simpa only [mul_comm] using h.2.congr_of_eventuallyEq he

theorem fzzScreeningFifthSubtracted_singularMark_integrable (u β : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningFifthSubtracted (-8+Real.exp u) β z)
      (ball 0 (1/2)) :=
  (fifth_singular_marked_source _ β (by linarith [Real.exp_pos u])).1

theorem fzzScreeningFifthSubtracted_singularMark_hasDerivAt (u β : ℝ) :
    HasDerivAt (fun δ => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted (-8+Real.exp u+δ) β z)
      (∫ z : ℂ in ball 0 (1/2),
        Real.log ‖z‖*fzzScreeningFifthSubtracted (-8+Real.exp u) β z) 0 :=
  (fifth_singular_marked_source _ β (by linarith [Real.exp_pos u])).2

private theorem affine_rpow_iteratedDeriv (n : ℕ) (s q t : ℝ)
    (ht : 0 < 1+q*t) :
    iteratedDeriv n (fun x : ℝ => (1+q*x)^s) t =
      q^n * (descPochhammer ℝ n).eval s * (1+q*t)^(s-n) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hpos : ∀ᶠ x in 𝓝 t, 0 < 1+q*x :=
      (show ContinuousAt (fun x : ℝ => 1+q*x) t by fun_prop).eventually
        (eventually_gt_nhds ht)
    have heq : iteratedDeriv n (fun x : ℝ => (1+q*x)^s) =ᶠ[𝓝 t]
        (fun x : ℝ => q^n * (descPochhammer ℝ n).eval s * (1+q*x)^(s-n)) := by
      filter_upwards [hpos] with x hx
      exact ih x hx
    rw [heq.deriv_eq]
    have ha : HasDerivAt (fun x : ℝ => 1+q*x) q t := by
      simpa only [mul_one, id_eq] using ((hasDerivAt_id t).const_mul q).const_add 1
    rw [((ha.rpow_const (p := s-n) (Or.inl ht.ne')).const_mul
      (q^n * (descPochhammer ℝ n).eval s)).deriv]
    rw [descPochhammer_succ_right]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_natCast, Nat.cast_add, Nat.cast_one, pow_succ]
    have he : s - (n : ℝ) - 1 = s - ((n : ℝ)+1) := by ring
    rw [he]
    ring

private theorem affine_rpow_contDiffAt (s q t : ℝ) (ht : 0 < 1+q*t)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n (fun x : ℝ => (1+q*x)^s) t :=
  (Real.contDiffAt_rpow_const_of_ne ht.ne').comp t
    (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))

private theorem affine_base_bounds (q t : ℝ) (hq : q ∈ Icc (-3/4 : ℝ) (5/4))
    (ht : t ∈ Icc (0 : ℝ) 1) : 1+q*t ∈ Icc (1/4 : ℝ) (9/4) := by
  constructor
  · have h := mul_le_mul_of_nonneg_right hq.1 ht.1
    nlinarith [ht.2]
  · have h := mul_le_mul_of_nonneg_right hq.2 ht.1
    nlinarith [ht.2]

private theorem affine_rpow_within (n : ℕ) (s q t : ℝ)
    (hq : q ∈ Icc (-3/4 : ℝ) (5/4)) (ht : t ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin n (fun x : ℝ => (1+q*x)^s) (Icc 0 1) t =
      q^n * (descPochhammer ℝ n).eval s * (1+q*t)^(s-n) := by
  have hp : 0 < 1+q*t := lt_of_lt_of_le (by norm_num) (affine_base_bounds q t hq ht).1
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    (affine_rpow_contDiffAt s q t hp n) ht]
  exact affine_rpow_iteratedDeriv n s q t hp

private theorem plane_q_bounds (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (1/2)) :
    (‖z‖^(2 : ℕ)-2*z.re) ∈ Icc (-3/4 : ℝ) (5/4) ∧
      |‖z‖^(2 : ℕ)-2*z.re| ≤ (5/2)*‖z‖ := by
  have hr : ‖z‖ ≤ 1/2 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hr0 := norm_nonneg z
  have hre := abs_le.mp (Complex.abs_re_le_norm z)
  have hsq := mul_nonneg hr0 (show 0 ≤ 1/2-‖z‖ by linarith)
  have hlow := mul_nonneg (show 0 ≤ 1/2-‖z‖ by linarith)
    (show 0 ≤ 3/2-‖z‖ by linarith)
  constructor
  · constructor <;> nlinarith [hre.1,hre.2]
  · rw [abs_le]
    constructor <;> nlinarith [hre.1,hre.2]

private theorem plane_q_identity (z : ℂ) :
    1+(‖z‖^(2 : ℕ)-2*z.re) = ‖z-1‖^(2 : ℕ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero]
  ring

private theorem affine_rpow_taylor (s q : ℝ) (hq : q ∈ Icc (-3/4 : ℝ) (5/4)) :
    taylorWithinEval (fun t : ℝ => (1+q*t)^s) 5 (Icc 0 1) 0 1 =
      ∑ j ∈ Finset.range 6, (descPochhammer ℝ j).eval s / (j.factorial : ℝ) * q^j := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [affine_rpow_within j s q 0 hq (by norm_num)]
  simp only [mul_zero, add_zero, Real.one_rpow, mul_one, sub_zero, one_pow, smul_eq_mul]
  ring

private theorem scalar_fifth_integral_remainder (s q : ℝ)
    (hq : q ∈ Icc (-3/4 : ℝ) (5/4)) :
    (1+q)^s - ∑ j ∈ Finset.range 6,
      (descPochhammer ℝ j).eval s / (j.factorial : ℝ) * q^j =
      ∫ t : ℝ in Ioc 0 1,
        ((1-t)^(5 : ℕ) / ((5:ℕ).factorial : ℝ)) *
          (q^(6 : ℕ) * (descPochhammer ℝ 6).eval s * (1+q*t)^(s-6)) := by
  have hf : ContDiffOn ℝ (5+1 : ℕ) (fun t : ℝ => (1+q*t)^s) (Icc 0 1) := by
    intro t ht
    exact (affine_rpow_contDiffAt s q t
      (lt_of_lt_of_le (by norm_num) (affine_base_bounds q t hq ht).1) _).contDiffWithinAt
  have h := taylor_integral_remainder (n := 5) (x := 1) (x₀ := 0)
    (by simpa only [uIcc_of_le zero_le_one] using hf)
  rw [uIcc_of_le zero_le_one, affine_rpow_taylor s q hq,
    intervalIntegral.integral_of_le zero_le_one] at h
  simp only [mul_one] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [affine_rpow_within 6 s q t hq ⟨ht.1.le,ht.2⟩, smul_eq_mul]
  simp only [Nat.cast_ofNat]

private theorem fifth_subtracted_lift_pointwise (α β : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) (1/2)) :
    fzzScreeningFifthSubtracted α β z =
      (descPochhammer ℝ 6).eval (β/2) *
        ∫ t : ℝ in Ioc 0 1, fzzScreeningFifthLiftWeight α (z,t) *
          Real.exp (β*fzzScreeningFifthLiftLog (z,t)) := by
  have hq := (plane_q_bounds z hz).1
  have h := scalar_fifth_integral_remainder (β/2) (‖z‖^(2 : ℕ)-2*z.re) hq
  rw [plane_q_identity, ← Real.rpow_natCast_mul (norm_nonneg (z-1))] at h
  simp only [Nat.cast_ofNat, show (2:ℝ)*(β/2)=β by ring] at h
  change ‖z-1‖^β - fzzScreeningFifthTaylor β z = _ at h
  rw [fzzScreeningFifthSubtracted, h, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hp : 0 < 1+(‖z‖^(2 : ℕ)-2*z.re)*t :=
    lt_of_lt_of_le (by norm_num) (affine_base_bounds _ t hq ⟨ht.1.le,ht.2⟩).1
  have he : (1+(‖z‖^(2 : ℕ)-2*z.re)*t)^(β/2-6) =
      (1+(‖z‖^(2 : ℕ)-2*z.re)*t)^(-6 : ℝ) *
        Real.exp (β*(Real.log (1+(‖z‖^(2 : ℕ)-2*z.re)*t)/2)) := by
    rw [show β/2-6 = β/2+(-6) by ring, Real.rpow_add hp]
    rw [Real.rpow_def_of_pos hp]
    rw [mul_comm]
    congr 1
    congr 1
    ring
  rw [he]
  dsimp [fzzScreeningFifthLiftWeight, fzzScreeningFifthLiftLog]
  ring


/-- Derivative of every coefficient in the original fifth subtraction. -/
def fzzScreeningFifthTaylorMark (β : ℝ) (z : ℂ) : ℝ :=
  ∑ j ∈ Finset.range 6,
    (descPochhammer ℝ j).derivative.eval (β/2) / (2*(j.factorial : ℝ)) *
      (‖z‖^(2 : ℕ)-2*z.re)^j

/-- The regular-factor logarithmic insertion retains the differentiated subtraction. -/
def fzzScreeningFifthRegularMark (α β : ℝ) (z : ℂ) : ℝ :=
  ‖z‖^α * (Real.log ‖z-1‖*‖z-1‖^β - fzzScreeningFifthTaylorMark β z)

private theorem pochhammer_half_deriv (j : ℕ) (β : ℝ) :
    HasDerivAt (fun s : ℝ => (descPochhammer ℝ j).eval (s/2))
      ((descPochhammer ℝ j).derivative.eval (β/2)/2) β := by
  simpa only [Function.comp_def,mul_one_div,id_eq] using
    ((descPochhammer ℝ j).hasDerivAt (β/2)).comp β ((hasDerivAt_id β).div_const 2)

private theorem fifth_taylor_deriv (β : ℝ) (z : ℂ) :
    HasDerivAt (fun s => fzzScreeningFifthTaylor s z) (fzzScreeningFifthTaylorMark β z) β := by
  have h := HasDerivAt.fun_sum (u := Finset.range 6) (fun j _ =>
    ((pochhammer_half_deriv j β).div_const (j.factorial : ℝ)).mul_const ((‖z‖^(2 : ℕ)-2*z.re)^j))
  apply h.congr_deriv
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem fifth_regular_point_deriv (α β : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) (1/2)) :
    HasDerivAt (fun s => fzzScreeningFifthSubtracted α s z)
      (fzzScreeningFifthRegularMark α β z) β := by
  have hn : 0 < ‖z-1‖ := by
    apply norm_pos_iff.mpr
    intro he
    have hz' : z=1 := sub_eq_zero.mp he
    have hh : ‖z‖ ≤ 1/2 := by simpa only [mem_closedBall,dist_zero_right] using hz
    rw [hz',norm_one] at hh
    norm_num at hh
  have h := HasDerivAt.const_rpow hn (hasDerivAt_id β)
  simpa only [mul_one,id_eq,Pi.sub_apply,fzzScreeningFifthSubtracted,fzzScreeningFifthRegularMark]
    using (h.sub (fifth_taylor_deriv β z)).const_mul (‖z‖^α)

private theorem fifth_lift_admission (α β : ℝ) (ha : -8 < α) :
    Integrable (fun p => fzzScreeningFifthLiftWeight α p *
      Real.exp (β*fzzScreeningFifthLiftLog p)) fzzScreeningFifthLiftMeasure := by
  have h := fzzScreeningFifthLift_exp_integrable (Real.log (α+8)) β
  rw [Real.exp_log (by linarith : 0 < α+8)] at h
  simpa only [show -8+(α+8)=α by ring] using h

private theorem fifth_lift_source (α β : ℝ) (ha : -8 < α) :
    Integrable (fun p => fzzScreeningFifthLiftWeight α p *
      (fzzScreeningFifthLiftLog p*Real.exp (β*fzzScreeningFifthLiftLog p)))
        fzzScreeningFifthLiftMeasure ∧
    HasDerivAt (fun s => ∫ p, fzzScreeningFifthLiftWeight α p *
      Real.exp (s*fzzScreeningFifthLiftLog p) ∂fzzScreeningFifthLiftMeasure)
      (∫ p, fzzScreeningFifthLiftWeight α p *
        (fzzScreeningFifthLiftLog p*Real.exp (β*fzzScreeningFifthLiftLog p))
          ∂fzzScreeningFifthLiftMeasure) β :=
  signed_exp_hasDerivAt _ _ _ (by unfold fzzScreeningFifthLiftWeight; fun_prop)
    (by unfold fzzScreeningFifthLiftLog; fun_prop) β
    (Eventually.of_forall (fun s => fifth_lift_admission α s ha))

private theorem fifth_slice_admission (α β : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) (1/2)) :
    IntegrableOn (fun t => fzzScreeningFifthLiftWeight α (z,t)*
      Real.exp (β*fzzScreeningFifthLiftLog (z,t))) (Ioc 0 1) := by
  have hp : ∀ t ∈ Icc (0:ℝ) 1, 0 < 1+(‖z‖^(2 : ℕ)-2*z.re)*t := by
    intro t ht
    exact lt_of_lt_of_le (by norm_num) (affine_base_bounds _ t (plane_q_bounds z hz).1 ht).1
  have hc : ContinuousOn (fun t : ℝ => 1+(‖z‖^(2 : ℕ)-2*z.re)*t) (Icc 0 1) := by fun_prop
  have hr := hc.rpow_const (fun t ht => Or.inl (hp t ht).ne') (p := (-6:ℝ))
  have hl := hc.log (fun t ht => (hp t ht).ne')
  have hh : ContinuousOn (fun t => fzzScreeningFifthLiftWeight α (z,t)*
      Real.exp (β*fzzScreeningFifthLiftLog (z,t))) (Icc 0 1) := by
    unfold fzzScreeningFifthLiftWeight fzzScreeningFifthLiftLog
    change ContinuousOn (fun t : ℝ =>
      (‖z‖^α*(‖z‖^(2 : ℕ)-2*z.re)^(6 : ℕ))*((1-t)^(5 : ℕ) / ((5:ℕ).factorial:ℝ))*
        (1+(‖z‖^(2 : ℕ)-2*z.re)*t)^(-6:ℝ)*
          Real.exp (β*(Real.log (1+(‖z‖^(2 : ℕ)-2*z.re)*t)/2))) (Icc 0 1)
    have hc0 : ContinuousOn (fun t : ℝ =>
        (‖z‖^α*(‖z‖^(2 : ℕ)-2*z.re)^(6 : ℕ))*((1-t)^(5 : ℕ) / ((5:ℕ).factorial:ℝ))) (Icc 0 1) := by
      fun_prop
    exact (hc0.mul hr).mul
      (Real.continuous_exp.comp_continuousOn ((hl.div_const 2).const_mul β))
  exact (hh.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self

private theorem fifth_regular_mark_lift (α β : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (0 : ℂ) (1/2)) :
    fzzScreeningFifthRegularMark α β z =
      ((descPochhammer ℝ 6).derivative.eval (β/2)/2)*
        (∫ t : ℝ in Ioc 0 1, fzzScreeningFifthLiftWeight α (z,t)*
          Real.exp (β*fzzScreeningFifthLiftLog (z,t))) +
      (descPochhammer ℝ 6).eval (β/2)*
        (∫ t : ℝ in Ioc 0 1, fzzScreeningFifthLiftWeight α (z,t)*
          (fzzScreeningFifthLiftLog (z,t)*Real.exp (β*fzzScreeningFifthLiftLog (z,t)))) := by
  have h := signed_exp_hasDerivAt (volume.restrict (Ioc (0:ℝ) 1))
    (fun t => fzzScreeningFifthLiftWeight α (z,t)) (fun t => fzzScreeningFifthLiftLog (z,t))
    (by unfold fzzScreeningFifthLiftWeight; fun_prop)
    (by unfold fzzScreeningFifthLiftLog; fun_prop) β
    (Eventually.of_forall (fun s => fifth_slice_admission α s z hz))
  have hd := ((pochhammer_half_deriv 6 β).mul h.2).congr_of_eventuallyEq
    (Eventually.of_forall (fun s => fifth_subtracted_lift_pointwise α s z hz))
  exact (fifth_regular_point_deriv α β z hz).unique hd

private theorem fifth_regular_mark_integrable (α β : ℝ) (ha : -8 < α) :
    IntegrableOn (fzzScreeningFifthRegularMark α β) (ball 0 (1/2)) := by
  have hi := (fifth_lift_admission α β ha).integral_prod_left
  have hm := (fifth_lift_source α β ha).1.integral_prod_left
  apply ((hi.const_mul ((descPochhammer ℝ 6).derivative.eval (β/2)/2)).add
    (hm.const_mul ((descPochhammer ℝ 6).eval (β/2)))).congr
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact (fifth_regular_mark_lift α β z (ball_subset_closedBall hz)).symm

private theorem fifth_regular_mark_integral (α β : ℝ) (ha : -8 < α) :
    (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthRegularMark α β z) =
      ((descPochhammer ℝ 6).derivative.eval (β/2)/2)*
        (∫ p, fzzScreeningFifthLiftWeight α p*Real.exp (β*fzzScreeningFifthLiftLog p)
          ∂fzzScreeningFifthLiftMeasure) +
      (descPochhammer ℝ 6).eval (β/2)*
        (∫ p, fzzScreeningFifthLiftWeight α p*
          (fzzScreeningFifthLiftLog p*Real.exp (β*fzzScreeningFifthLiftLog p))
            ∂fzzScreeningFifthLiftMeasure) := by
  have hi := (fifth_lift_admission α β ha).integral_prod_left
  have hm := (fifth_lift_source α β ha).1.integral_prod_left
  rw [fzzScreeningFifthLiftMeasure, integral_prod _ (fifth_lift_admission α β ha),
    integral_prod _ (fifth_lift_source α β ha).1, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi.const_mul _) (hm.const_mul _)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact fifth_regular_mark_lift α β z (ball_subset_closedBall hz)

theorem fzzScreeningFifthRegularMark_integrable (u β : ℝ) :
    IntegrableOn (fzzScreeningFifthRegularMark (-8+Real.exp u) β) (ball 0 (1/2)) :=
  fifth_regular_mark_integrable _ β (by linarith [Real.exp_pos u])

theorem fzzScreeningFifthSubtracted_regularMark_hasDerivAt (u β : ℝ) :
    HasDerivAt (fun s => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningFifthSubtracted (-8+Real.exp u) s z)
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthRegularMark (-8+Real.exp u) β z) β := by
  rw [fifth_regular_mark_integral _ β (by linarith [Real.exp_pos u])]
  exact ((pochhammer_half_deriv 6 β).mul
    (fifth_lift_source _ β (by linarith [Real.exp_pos u])).2).congr_of_eventuallyEq
      (Eventually.of_forall (fun s => fzzScreeningFifthSubtracted_lift_identity u s))

theorem fzzScreeningFifthTaylorMark_cubic (z : ℂ) :
    fzzScreeningFifthTaylorMark (-6) z =
      (‖z‖^(2 : ℕ)-2*z.re)/2-7*(‖z‖^(2 : ℕ)-2*z.re)^(2 : ℕ)/4+47*(‖z‖^(2 : ℕ)-2*z.re)^(3 : ℕ)/12-
        57*(‖z‖^(2 : ℕ)-2*z.re)^(4 : ℕ)/8+459*(‖z‖^(2 : ℕ)-2*z.re)^(5 : ℕ)/40 := by
  simp only [fzzScreeningFifthTaylorMark,Finset.sum_range_succ,Finset.sum_range_zero,
    descPochhammer_succ_right,descPochhammer_zero,Polynomial.derivative_mul,
    Polynomial.derivative_sub,Polynomial.derivative_X,Polynomial.derivative_natCast,
    Polynomial.derivative_one,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_one,Polynomial.eval_zero,Polynomial.eval_X,Polynomial.eval_natCast]
  norm_num
  ring

private theorem cosine_first : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ) = 0 := by
  rw [integral_cos]
  simp

private theorem cosine_second : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^(2 : ℕ)) = Real.pi := by
  rw [integral_cos_sq]
  simp

private theorem cosine_third : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^(3 : ℕ)) = 0 := by
  rw [integral_cos_pow_three]
  simp

private theorem cosine_fourth : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^(4 : ℕ)) = 3*Real.pi/4 := by
  rw [show (4:ℕ)=2+2 by rfl, integral_cos_pow, cosine_second]
  simp
  ring

private theorem cosine_fifth : (∫ θ : ℝ in 0..2*Real.pi, Real.cos θ^(5 : ℕ)) = 0 := by
  rw [show (5:ℕ)=3+2 by rfl, integral_cos_pow, cosine_third]
  simp

private theorem quintic_cosine_integral (a b c d e f : ℝ) :
    (∫ θ : ℝ in 0..2*Real.pi,
      a+b*Real.cos θ+c*Real.cos θ^(2 : ℕ)+d*Real.cos θ^(3 : ℕ)+e*Real.cos θ^(4 : ℕ)+f*Real.cos θ^(5 : ℕ)) =
        2*Real.pi*a+Real.pi*c+(3*Real.pi/4)*e := by
  have hi (n : ℕ) : IntervalIntegrable (fun θ : ℝ => Real.cos θ^n) volume 0 (2*Real.pi) :=
    (show Continuous _ by fun_prop).intervalIntegrable _ _
  have h0 : IntervalIntegrable (fun _ : ℝ => a) volume 0 (2*Real.pi) := intervalIntegrable_const
  have h1 := (hi 1).const_mul b
  have h2 := (hi 2).const_mul c
  have h3 := (hi 3).const_mul d
  have h4 := (hi 4).const_mul e
  have h5 := (hi 5).const_mul f
  simp only [pow_one] at h1
  rw [intervalIntegral.integral_add ((((h0.add h1).add h2).add h3).add h4) h5,
    intervalIntegral.integral_add (((h0.add h1).add h2).add h3) h4,
    intervalIntegral.integral_add ((h0.add h1).add h2) h3,
    intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1]
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    cosine_first, cosine_second, cosine_third, cosine_fourth, cosine_fifth,
    mul_zero, add_zero, sub_zero, smul_eq_mul]
  ring

theorem fzzScreeningFifthTaylorMark_cubic_circleAverage (r : ℝ) :
    Real.circleAverage (fzzScreeningFifthTaylorMark (-6)) 0 r =
      -3*r^(2 : ℕ)-21*r^(4 : ℕ)+(788/3)*r^(6 : ℕ)+(1779/8)*r^(8 : ℕ)+(459/40)*r^(10 : ℕ) := by
  have h := quintic_cosine_integral
    (r^(2 : ℕ)/2-7*r^(4 : ℕ)/4+47*r^(6 : ℕ)/12-57*r^(8 : ℕ)/8+459*r^(10 : ℕ)/40)
    (-r+7*r^(3 : ℕ)-47*r^(5 : ℕ)/2+57*r^(7 : ℕ)-459*r^(9 : ℕ)/4)
    (-7*r^(2 : ℕ)+47*r^(4 : ℕ)-171*r^(6 : ℕ)+459*r^(8 : ℕ))
    (-94*r^(3 : ℕ)/3+228*r^(5 : ℕ)-918*r^(7 : ℕ))
    (-114*r^(4 : ℕ)+918*r^(6 : ℕ)) (-1836*r^(5 : ℕ)/5)
  have he : (fun θ : ℝ => fzzScreeningFifthTaylorMark (-6) (circleMap 0 r θ)) =
      (fun θ : ℝ =>
        (r^(2 : ℕ)/2-7*r^(4 : ℕ)/4+47*r^(6 : ℕ)/12-57*r^(8 : ℕ)/8+459*r^(10 : ℕ)/40)+
        (-r+7*r^(3 : ℕ)-47*r^(5 : ℕ)/2+57*r^(7 : ℕ)-459*r^(9 : ℕ)/4)*Real.cos θ+
        (-7*r^(2 : ℕ)+47*r^(4 : ℕ)-171*r^(6 : ℕ)+459*r^(8 : ℕ))*Real.cos θ^(2 : ℕ)+
        (-94*r^(3 : ℕ)/3+228*r^(5 : ℕ)-918*r^(7 : ℕ))*Real.cos θ^(3 : ℕ)+
        (-114*r^(4 : ℕ)+918*r^(6 : ℕ))*Real.cos θ^(4 : ℕ)+(-1836*r^(5 : ℕ)/5)*Real.cos θ^(5 : ℕ)) := by
    funext θ
    rw [fzzScreeningFifthTaylorMark_cubic]
    simp only [norm_circleMap_zero,sq_abs,circleMap_zero_re]
    ring
  rw [Real.circleAverage_def,smul_eq_mul,he,h]
  field_simp [Real.pi_ne_zero]
  ring

private theorem exterior_admission (α β : ℝ) (hs : α+β < -2) :
    IntegrableOn (fzzScreeningPlaneKernel α β) fzzScreeningPlaneExterior := by
  have h := fzzScreeningPlaneExterior_integrable α (Real.log (-2-α-β))
  rw [Real.exp_log (by linarith : 0 < -2-α-β)] at h
  simpa only [show -2-α-(-2-α-β) = β by ring] using h

private theorem plane_kernel_shift (α β δ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    fzzScreeningPlaneKernel α β z*Real.exp (δ*Real.log ‖z‖) =
      fzzScreeningPlaneKernel (α+δ) β z := by
  have hn := norm_pos_iff.mpr hz
  rw [show Real.exp (δ*Real.log ‖z‖) = ‖z‖^δ by rw [Real.rpow_def_of_pos hn, mul_comm]]
  unfold fzzScreeningPlaneKernel
  rw [Real.rpow_add hn]
  ring


private theorem exterior_marked_source (α β : ℝ) (hs : α+β < -2) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel α β z)
      fzzScreeningPlaneExterior ∧
    HasDerivAt (fun δ => ∫ z : ℂ in fzzScreeningPlaneExterior,
      fzzScreeningPlaneKernel (α+δ) β z)
      (∫ z : ℂ in fzzScreeningPlaneExterior, Real.log ‖z‖*fzzScreeningPlaneKernel α β z) 0 := by
  have hshift : ∀ᶠ δ : ℝ in 𝓝 0, (α+δ)+β < -2 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hs)
  have hi : ∀ᶠ δ : ℝ in 𝓝 0, Integrable
      (fun z => fzzScreeningPlaneKernel α β z*Real.exp (δ*Real.log ‖z‖))
        (volume.restrict fzzScreeningPlaneExterior) := by
    filter_upwards [hshift] with δ hδ
    apply (exterior_admission (α+δ) β hδ).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (plane_kernel_shift α β δ hz).symm
  have h := signed_exp_hasDerivAt (volume.restrict fzzScreeningPlaneExterior)
    (fzzScreeningPlaneKernel α β) (fun z => Real.log ‖z‖)
    (by unfold fzzScreeningPlaneKernel; fun_prop) (by fun_prop) 0 hi
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  have he : (fun δ => ∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel (α+δ) β z) =ᶠ[𝓝 0]
      (fun δ => ∫ z : ℂ in fzzScreeningPlaneExterior,
        fzzScreeningPlaneKernel α β z*Real.exp (δ*Real.log ‖z‖)) := by
    filter_upwards with δ
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (plane_kernel_shift α β δ hz).symm
  constructor
  · simpa only [IntegrableOn, mul_comm] using h.1
  · simpa only [mul_comm] using h.2.congr_of_eventuallyEq he

theorem fzzScreeningCubicExteriorMark_hasDerivAt :
    HasDerivAt (fun α => ∫ z : ℂ in fzzScreeningPlaneExterior,
      fzzScreeningPlaneKernel α (-6) z)
      (∫ z : ℂ in fzzScreeningPlaneExterior,
        Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z) (-6) := by
  have h0 := (exterior_marked_source (-6) (-6) (by norm_num)).2
  have h := HasDerivAt.comp_sub_const (-6 : ℝ) (-6)
    (by simpa only [sub_self] using h0)
  simpa only [zero_add,show ∀ s : ℝ, -6+(s-(-6))=s by intro s; ring] using h

/-- Differentiation of the complete original regular part retains both distinct
local insertions and the original exterior logarithmic insertion. -/
theorem fzzScreeningCubicOriginalRemainders_hasDerivAt :
    HasDerivAt (fun α =>
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted α (-6) z)+
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthSubtracted (-6) α z)+
      (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α (-6) z))
      ((∫ z : ℂ in ball 0 (1/2), Real.log ‖z‖*fzzScreeningFifthSubtracted (-6) (-6) z)+
      (∫ z : ℂ in ball 0 (1/2), fzzScreeningFifthRegularMark (-6) (-6) z)+
      (∫ z : ℂ in fzzScreeningPlaneExterior,
        Real.log ‖z‖*fzzScreeningPlaneKernel (-6) (-6) z)) (-6) := by
  have h0 := (fifth_singular_marked_source (-6) (-6) (by norm_num)).2
  have hs := HasDerivAt.comp_sub_const (-6 : ℝ) (-6)
    (by simpa only [sub_self] using h0)
  simp only [show ∀ s : ℝ, -6+(s-(-6))=s by intro s; ring] at hs
  have hr := fzzScreeningFifthSubtracted_regularMark_hasDerivAt (Real.log 2) (-6)
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)] at hr
  norm_num only at hr
  exact (hs.fun_add hr).fun_add fzzScreeningCubicExteriorMark_hasDerivAt

end GaloisForLFunctions.RHTower
