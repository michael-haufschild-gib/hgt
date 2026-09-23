import GaloisForLFunctions.RHTower.SelbergMaassUnipotentPaths
import GaloisForLFunctions.RHTower.SelbergMaassTraceDirection
import GaloisForLFunctions.RHTower.SelbergMaassRegulatorMass

/-!
# Exact regulator-removal classification of original source period resistance

The complete original Maass source, with every finite quotient coordinate
retained, determines the one-period reciprocal-amplitude resistance. Original
C² regularity gives a linear amplitude bound on a full period after any common
zero, hence an explicit logarithmic lower bound and divergent resistance.
A zero-free original period instead has its own positive compact amplitude
floor, a finite unregularized reciprocal integral, and error at most e/d².

Uniform boundedness over positive regulators and existence of a finite limit
are each equivalent to original period zero-freeness. Divergence to infinity
is equivalent to existence of a common zero in that period. No nodal point is
asserted to exist; no floor is uniformized over heights, levels or sources.
These results classify the actual resistance factor in the current-path
comparison. They do not provide the missing quotient-area quarter inequality
or full-Xi spectral occurrence.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassPeriodResistance
open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceEnergy
open SelbergMaassSourceCurrents SelbergMaassTraceRegularized SelbergMaassRegulatorMass
open SelbergMaassChordEnergy SelbergMaassUnipotentPaths SelbergMaassTraceDirection
noncomputable section
variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- The actual source amplitude on one horizontal line. -/
def sliceAmplitude (y x : ℝ) : ℝ := Real.sqrt (density N f (ofComplex (point x y)))

theorem sliceAmplitude_continuous {y : ℝ} (hy : 0 < y) : Continuous (sliceAmplitude N f y) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hd := (density_contDiffOn N f).continuousOn
  have hp : 0 < (point x y).im := by simpa [point] using hy
  exact ((hd.continuousAt (isOpen_upperHalfPlaneSet.mem_nhds hp)).comp
    (f := fun t : ℝ => point t y) (point_horizontal x y).continuousAt).sqrt

/-- Actual common zeros give a source-derived linear amplitude bound on the following full period. -/
theorem exists_linear_amplitude_bound_at_node (z : ℍ) (hz : density N f z=0) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x ∈ Icc z.re (z.re+1), sliceAmplitude N f z.im x ≤ L*(x-z.re) := by
  have hF (q : Deck N) : ContDiffOn ℝ 2 (field N f q) {w : ℂ | 0 < w.im} :=
    (quotientForm N f q).2.2.1.1
  have hd (q : Deck N) : Continuous (fun x => dir 1 (field N f q) (point x z.im)) :=
    slice_continuous (directional_contDiffOn (hF q) (m:=1) le_rfl 1).continuousOn z.im_pos
  have hc : Continuous (fun x => ∑ q : Deck N, ‖dir 1 (field N f q) (point x z.im)‖) :=
    continuous_finsetSum Finset.univ (fun q _ => (hd q).norm)
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    (s:=Icc z.re (z.re+1))
  let C : ℝ := |B|+1
  have hCp : 0 < C := by dsimp [C]; positivity
  have hb (q : Deck N) (x : ℝ) (hx : x ∈ Icc z.re (z.re+1)) :
      ‖dir 1 (field N f q) (point x z.im)‖ ≤ C := by
    have hs := Finset.single_le_sum (s:=Finset.univ)
      (fun q _ => norm_nonneg (dir 1 (field N f q) (point x z.im))) (Finset.mem_univ q)
    have h := hB x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at h
    dsimp [C]
    linarith [le_abs_self B]
  have hf0 (q : Deck N) : field N f q (point z.re z.im)=0 := by
    have hp : point z.re z.im=(z:ℂ) := by apply Complex.ext <;> simp [point]
    rw [hp,field,Function.comp_apply,ofComplex_apply]
    exact component_zero_of_density_zero N f z hz q
  have hq (q : Deck N) (x : ℝ) (hx : x ∈ Icc z.re (z.re+1)) :
      ‖field N f q (point x z.im)‖ ≤ C*(x-z.re) := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t (_ : t ∈ Icc z.re (z.re+1)) =>
        (slice_horizontal ((hF q).of_le (by norm_num)) z.im_pos t).hasDerivWithinAt)
      (fun t ht => hb q t ⟨ht.1,ht.2.le⟩) x hx
    simpa only [hf0,sub_zero] using h
  let K : ℝ := (Fintype.card (Deck N):ℝ)*C^(2 : ℕ)
  refine ⟨1+Real.sqrt K,by linarith [Real.sqrt_nonneg K],?_⟩
  intro x hx
  have ht : 0 ≤ x-z.re := sub_nonneg.mpr hx.1
  have hD : density N f (ofComplex (point x z.im)) ≤ K*(x-z.re)^(2 : ℕ) := by
    have he (q : Deck N) : normSq (field N f q (point x z.im)) ≤ C^(2 : ℕ)*(x-z.re)^(2 : ℕ) := by
      rw [← Complex.sq_norm]
      nlinarith [hq q x hx,norm_nonneg (field N f q (point x z.im))]
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun q _ => he q)
    simpa only [density,field,Function.comp_apply,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      K,mul_assoc] using h
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : sliceAmplitude N f z.im x ≤ Real.sqrt K*(x-z.re) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg K) ht,?_⟩
    rw [mul_pow,Real.sq_sqrt hK]
    exact hD
  nlinarith

/-- An affine positive upper amplitude profile has an exact logarithmic reciprocal integral. -/
theorem integral_reciprocal_affine (a L e : ℝ) (hL : 0 < L) (he : 0 < e) :
    (∫ x in a..a+1, 1/(L*(x-a)+e))=(Real.log (L+e)-Real.log e)/L := by
  have hp (x : ℝ) (hx : x ∈ Icc a (a+1)) : 0 < L*(x-a)+e := by nlinarith [hx.1]
  have hd (x : ℝ) (hx : x ∈ Icc a (a+1)) :
      HasDerivAt (fun t => Real.log (L*(t-a)+e)/L) (1/(L*(x-a)+e)) x := by
    have h : HasDerivAt (fun t : ℝ => Real.log (L*(t-a)+e)/L)
        (L/(L*(x-a)+e)/L) x :=
      by simpa only [id_eq,mul_one] using
        (((((hasDerivAt_id x).sub_const a).const_mul L).add_const e).log (hp x hx).ne').div_const L
    have heq : L/(L*(x-a)+e)/L = 1/(L*(x-a)+e) := by field_simp
    rwa [heq] at h
  have hi : IntervalIntegrable (fun x => 1/(L*(x-a)+e)) volume a (a+1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact continuousOn_const.div (by fun_prop) (fun x hx => (hp x hx).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (by simpa [uIcc_of_le (by linarith : a ≤ a+1)] using hx)) hi]
  simp
  ring

/-- A source node forces an explicit logarithmic lower bound on its original period resistance. -/
theorem exists_periodResistance_log_lower (z : ℍ) (hz : density N f z=0) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ e : Ioi (0:ℝ),
      (Real.log (L+(e:ℝ))-Real.log (e:ℝ))/L ≤ periodResistance N f e z.im := by
  obtain ⟨L,hL,hbound⟩ := exists_linear_amplitude_bound_at_node N f z hz
  refine ⟨L,hL,?_⟩
  intro e
  have hepos : 0 < (e : ℝ) := e.2
  have hLp : 0 < L := by linarith
  have hr (x : ℝ) (hx : x ∈ Icc z.re (z.re+1)) :
      radius N f e (point x z.im) ≤ L*(x-z.re)+(e:ℝ) := by
    have ht : 0 ≤ x-z.re := sub_nonneg.mpr hx.1
    have hb := hbound x hx
    have hs := Real.sq_sqrt (density_nonneg N f (ofComplex (point x z.im)))
    change (sliceAmplitude N f z.im x)^(2 : ℕ)=_ at hs
    have ha : 0 ≤ sliceAmplitude N f z.im x := Real.sqrt_nonneg _
    have hu : 0 ≤ L*(x-z.re) := mul_nonneg hLp.le ht
    have hA2 : (sliceAmplitude N f z.im x)^(2 : ℕ) ≤ (L*(x-z.re))^(2 : ℕ) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hb) (add_nonneg hu ha)]
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg hu hepos.le,?_⟩
    nlinarith only [hs,hA2,mul_nonneg hu hepos.le]
  have hpos (x : ℝ) (hx : x ∈ Icc z.re (z.re+1)) : 0 < L*(x-z.re)+(e:ℝ) :=
    add_pos_of_nonneg_of_pos (mul_nonneg hLp.le (sub_nonneg.mpr hx.1)) hepos
  have hi : IntervalIntegrable (fun x => 1/(L*(x-z.re)+(e:ℝ))) volume z.re (z.re+1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact continuousOn_const.div (by fun_prop) (fun x hx => (hpos x hx).ne')
  have hj : IntervalIntegrable (fun x => 1/radius N f e (point x z.im)) volume z.re (z.re+1) :=
    (continuous_const.div (SelbergMaassAugmentedDirection.radius_slice_continuous N f e z.im_pos)
      (fun x => (radius_pos N f e (point x z.im)).ne')).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (by linarith : z.re ≤ z.re+1) hi hj
    (fun x hx => one_div_le_one_div_of_le (radius_pos N f e (point x z.im)) (hr x hx))
  rw [integral_reciprocal_affine _ _ _ hLp e.2] at h
  change _ ≤ pathResistance N f e z.im z.re (z.re+1) at h
  rwa [pathResistance_one_period N f e z.im_pos] at h

/-- Every original common-zero height has divergent resistance as the actual regulator vanishes. -/
theorem periodResistance_tendsto_atTop_of_node (z : ℍ) (hz : density N f z=0) :
    Tendsto (fun e : Ioi (0:ℝ) => periodResistance N f e z.im) regulatorAtZero atTop := by
  obtain ⟨L,hL,hbound⟩ := exists_periodResistance_log_lower N f z hz
  have hLp : 0 < L := by linarith
  have he : Tendsto (fun e : Ioi (0:ℝ) => (e:ℝ)) regulatorAtZero (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨regulator_coe_limit,Eventually.of_forall (fun e => e.2)⟩
  have hl : Tendsto (fun e : Ioi (0:ℝ) => -(Real.log (e:ℝ))/L) regulatorAtZero atTop := by
    have h := (Real.tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg
      (by nlinarith [inv_pos.mpr hLp] : -L⁻¹ < 0)).comp he
    simpa only [Function.comp_def,neg_mul,mul_neg,div_eq_mul_inv,mul_comm] using h
  apply tendsto_atTop_mono (fun e => ?_) hl
  have hepos : 0 < (e : ℝ) := e.2
  have hg := Real.log_nonneg (hL.trans (le_add_of_nonneg_right hepos.le))
  have hb := hbound e
  rw [sub_div] at hb
  have hn := div_nonneg hg hLp.le
  rw [neg_div]
  linarith

/-- Literal unregularized reciprocal amplitude, used only with proven zero-freeness. -/
def unregularizedPeriodResistance (y : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..1, 1 / sliceAmplitude N f y x

/-- A zero-free original period has an amplitude floor supplied by its own compactness. -/
theorem exists_period_amplitude_floor {y : ℝ} (hy : 0 < y)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x y))) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ Icc (0:ℝ) 1, d ≤ sliceAmplitude N f y x := by
  obtain ⟨x,hx,hm⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0:ℝ) 1).Nonempty from ⟨0,by constructor <;> norm_num⟩)
    (sliceAmplitude_continuous N f hy).continuousOn
  exact ⟨sliceAmplitude N f y x,Real.sqrt_pos.mpr (hp x hx),fun t ht => hm ht⟩

/-- Regularization changes actual amplitude by at most its regulator. -/
theorem radius_sub_amplitude_bounds (e : Ioi (0:ℝ)) (y x : ℝ) :
    0 ≤ radius N f e (point x y)-sliceAmplitude N f y x ∧
      radius N f e (point x y)-sliceAmplitude N f y x ≤ (e:ℝ) := by
  have he : 0 < (e:ℝ) := e.2
  have ha : 0 ≤ sliceAmplitude N f y x := Real.sqrt_nonneg _
  have hs : (sliceAmplitude N f y x)^(2 : ℕ) = density N f (ofComplex (point x y)) :=
    Real.sq_sqrt (density_nonneg N f _)
  have hr := radius_sq N f e (point x y)
  have hl : sliceAmplitude N f y x ≤ radius N f e (point x y) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (e:ℝ)))
  refine ⟨sub_nonneg.mpr hl,?_⟩
  nlinarith [radius_pos N f e (point x y),mul_nonneg ha he.le]

/-- A proven source floor controls the reciprocal regularization error pointwise. -/
theorem reciprocal_error_bounds (e : Ioi (0:ℝ)) (y x d : ℝ) (hd : 0 < d)
    (hf : d ≤ sliceAmplitude N f y x) :
    0 ≤ 1/sliceAmplitude N f y x - 1/radius N f e (point x y) ∧
      1/sliceAmplitude N f y x - 1/radius N f e (point x y) ≤ (e:ℝ)/d^(2 : ℕ) := by
  have ha : 0 < sliceAmplitude N f y x := hd.trans_le hf
  have hr := radius_pos N f e (point x y)
  obtain ⟨hlo,hhi⟩ := radius_sub_amplitude_bounds N f e y x
  have hab : sliceAmplitude N f y x ≤ radius N f e (point x y) := sub_nonneg.mp hlo
  have hdr := hf.trans hab
  have hp : d^(2 : ℕ) ≤ sliceAmplitude N f y x * radius N f e (point x y) := by
    simpa only [pow_two] using mul_le_mul hf hdr hd.le ha.le
  have heq : 1/sliceAmplitude N f y x - 1/radius N f e (point x y) =
      (radius N f e (point x y)-sliceAmplitude N f y x)/
        (sliceAmplitude N f y x*radius N f e (point x y)) := by
    field_simp
  rw [heq]
  refine ⟨div_nonneg hlo (mul_pos ha hr).le,?_⟩
  exact (div_le_div_of_nonneg_right hhi (mul_pos ha hr).le).trans
    (div_le_div_of_nonneg_left e.2.le (sq_pos_of_pos hd) hp)

/-- Every actual zero-free period has a finite reciprocal integral. -/
theorem reciprocal_amplitude_intervalIntegrable {y : ℝ} (hy : 0 < y)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x y))) :
    IntervalIntegrable (fun x => 1/sliceAmplitude N f y x) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact continuousOn_const.div (sliceAmplitude_continuous N f hy).continuousOn
    (fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne')

/-- The complete original reciprocal error is at most regulator divided by the squared source floor. -/
theorem periodResistance_error_bounds {y : ℝ} (hy : 0 < y) (d : ℝ) (hd : 0 < d)
    (hf : ∀ x ∈ Icc (0:ℝ) 1, d ≤ sliceAmplitude N f y x) (e : Ioi (0:ℝ)) :
    0 ≤ unregularizedPeriodResistance N f y - periodResistance N f e y ∧
      unregularizedPeriodResistance N f y - periodResistance N f e y ≤ (e:ℝ)/d^(2 : ℕ) := by
  have hp (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      0 < density N f (ofComplex (point x y)) := Real.sqrt_pos.mp (hd.trans_le (hf x hx))
  have hi := reciprocal_amplitude_intervalIntegrable N f hy hp
  have hj : IntervalIntegrable (fun x => 1/radius N f e (point x y)) volume 0 1 := (continuous_const.div
    (SelbergMaassAugmentedDirection.radius_slice_continuous N f e hy)
    (fun x => (radius_pos N f e (point x y)).ne')).intervalIntegrable (0:ℝ) 1
  have heq : unregularizedPeriodResistance N f y - periodResistance N f e y =
      ∫ x in (0:ℝ)..1, (1/sliceAmplitude N f y x - 1/radius N f e (point x y)) := by
    exact (intervalIntegral.integral_sub hi hj).symm
  rw [heq]
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x hx => (reciprocal_error_bounds N f e y x d hd (hf x hx)).1)
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      (hi.sub hj) intervalIntegrable_const
      (fun x hx => (reciprocal_error_bounds N f e y x d hd (hf x hx)).2)
    simpa using h

/-- Zero-freeness yields convergence to the literal finite original reciprocal integral. -/
theorem periodResistance_tendsto_of_zero_free {y : ℝ} (hy : 0 < y)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x y))) :
    Tendsto (fun e : Ioi (0:ℝ) => periodResistance N f e y) regulatorAtZero
      (𝓝 (unregularizedPeriodResistance N f y)) := by
  obtain ⟨d,hd,hf⟩ := exists_period_amplitude_floor N f hy hp
  have hl : Tendsto (fun e : Ioi (0:ℝ) => (e:ℝ)/d^(2 : ℕ)) regulatorAtZero (𝓝 0) := by
    simpa using regulator_coe_limit.div_const (d^(2 : ℕ))
  have he := tendsto_const_nhds.squeeze' hl
    (Eventually.of_forall (fun e => (periodResistance_error_bounds N f hy d hd hf e).1))
    (Eventually.of_forall (fun e => (periodResistance_error_bounds N f hy d hd hf e).2))
  simpa using (tendsto_const_nhds (x:=unregularizedPeriodResistance N f y)).sub he

/-- The source floor also bounds the finite original reciprocal integral. -/
theorem unregularizedPeriodResistance_le {y : ℝ} (hy : 0 < y) (d : ℝ) (hd : 0 < d)
    (hf : ∀ x ∈ Icc (0:ℝ) 1, d ≤ sliceAmplitude N f y x) :
    unregularizedPeriodResistance N f y ≤ 1/d := by
  have hp (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      0 < density N f (ofComplex (point x y)) := Real.sqrt_pos.mp (hd.trans_le (hf x hx))
  have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (reciprocal_amplitude_intervalIntegrable N f hy hp) intervalIntegrable_const
    (fun x hx => one_div_le_one_div_of_le hd (hf x hx))
  simpa [unregularizedPeriodResistance] using h

/-- Uniform boundedness over all positive regulators is exactly absence of original period nodes. -/
theorem periodResistance_bddAbove_iff_zero_free {y : ℝ} (hy : 0 < y) :
    BddAbove (range (fun e : Ioi (0:ℝ) => periodResistance N f e y)) ↔
      ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x y)) := by
  constructor
  · intro hb x hx
    by_contra hn
    have hz : density N f (ofComplex (point x y))=0 :=
      le_antisymm (le_of_not_gt hn) (density_nonneg N f _)
    have hp : 0 < (point x y).im := by simpa [point] using hy
    have hl := periodResistance_tendsto_atTop_of_node N f (ofComplex (point x y)) hz
    have him : (ofComplex (point x y)).im = y := by
      rw [UpperHalfPlane.im,ofComplex_apply_of_im_pos hp]
      simp [point]
    rw [him] at hl
    exact not_bddAbove_of_tendsto_atTop hl hb
  · intro hp
    obtain ⟨d,hd,hf⟩ := exists_period_amplitude_floor N f hy hp
    refine ⟨1/d,?_⟩
    rintro _ ⟨e,rfl⟩
    have h := (periodResistance_error_bounds N f hy d hd hf e).1
    have h0 := unregularizedPeriodResistance_le N f hy d hd hf
    linarith


/-- Divergence occurs exactly when the original complete source period contains a common zero. -/
theorem periodResistance_tendsto_atTop_iff_node {y : ℝ} (hy : 0 < y) :
    Tendsto (fun e : Ioi (0:ℝ) => periodResistance N f e y) regulatorAtZero atTop ↔
      ∃ x ∈ Icc (0:ℝ) 1, density N f (ofComplex (point x y))=0 := by
  constructor
  · intro ht
    by_contra hn
    have hp (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
        0 < density N f (ofComplex (point x y)) := by
      have hne : density N f (ofComplex (point x y)) ≠ 0 := fun hz => hn ⟨x,hx,hz⟩
      exact lt_of_le_of_ne (density_nonneg N f _) hne.symm
    exact not_tendsto_nhds_of_tendsto_atTop ht _ (periodResistance_tendsto_of_zero_free N f hy hp)
  · rintro ⟨x,hx,hz⟩
    have hp : 0 < (point x y).im := by simpa [point] using hy
    have ht := periodResistance_tendsto_atTop_of_node N f (ofComplex (point x y)) hz
    have him : (ofComplex (point x y)).im = y := by
      rw [UpperHalfPlane.im,ofComplex_apply_of_im_pos hp]
      simp [point]
    rwa [him] at ht

/-- Existence of any finite regulator limit is exactly original period zero-freeness. -/
theorem periodResistance_finite_limit_iff_zero_free {y : ℝ} (hy : 0 < y) :
    (∃ R : ℝ, Tendsto (fun e : Ioi (0:ℝ) => periodResistance N f e y) regulatorAtZero (𝓝 R)) ↔
      ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x y)) := by
  constructor
  · rintro ⟨R,hR⟩ x hx
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) (density_nonneg N f (ofComplex (point x y)))
    exact not_tendsto_atTop_of_tendsto_nhds hR
      ((periodResistance_tendsto_atTop_iff_node N f hy).mpr ⟨x,hx,hz⟩)
  · intro hp
    exact ⟨unregularizedPeriodResistance N f y,periodResistance_tendsto_of_zero_free N f hy hp⟩

end
end GaloisForLFunctions.RHTower.SelbergMaassPeriodResistance
