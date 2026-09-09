import GaloisForLFunctions.RHTower.SelbergMaassPeriodCurrentLimit

/-!
# Original-source rigidity of a vanishing current-period limit

Fixed-regulator pair/phase weights give positive lower certificates for the
complete period-current limit. A zero limit therefore annihilates every
horizontal pair and phase current, forcing a common real radial derivative
on the positive-density locus.

At an original common zero, a nonzero horizontal derivative retains positive
regulator-gradient mass on an actual shrinking interval. Thus zero limiting
current forces every component derivative to vanish at the node as well;
the radial law extends through all nodes. Nonflat nodes force divergence
of the complete resistance/current product.

For an exceptional Maass source, actual zero means rule out zero limiting
current on a zero-free period: normalized components would be constant and
could not have the proved negative source correlation. Every positive height
therefore has positive limiting current or an original node with zero first
horizontal derivative energy. No such source or node is asserted to exist,
and this necessary-case classification supplies no quotient-area quarter
bound or full-Xi spectral occurrence.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory ModularGroup
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassPeriodCurrentRigidity
open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceEnergy
open SelbergMaassSourceCurrents SelbergMaassTraceRegularized SelbergMaassRegulatorMass
open SelbergMaassChordEnergy SelbergMaassUnipotentPaths SelbergMaassTraceDirection
open SelbergMaassPeriodResistance SelbergMaassTraceRadial SelbergMaassPairPhaseEnergy
open SelbergMaassPeriodCurrentLimit
noncomputable section
variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Complete horizontal pair-plus-phase numerator of the original source. -/
def horizontalNumerator (z : ℂ) : ℝ := pairEnergy N f 1 z+phaseCurrent N f 1 z^2

theorem horizontalNumerator_nonneg (z : ℂ) : 0 ≤ horizontalNumerator N f z :=
  add_nonneg (pairEnergy_nonneg N f 1 z) (sq_nonneg _)

/-- A fixed regulated pair/phase density, with no regulator-gradient term discarded from the full energy. -/
def horizontalWeight (e : Ioi (0:ℝ)) (z : ℂ) : ℝ := horizontalNumerator N f z / radius N f e z^3

theorem horizontalWeight_nonneg (e : Ioi (0:ℝ)) (z : ℂ) : 0 ≤ horizontalWeight N f e z :=
  div_nonneg (horizontalNumerator_nonneg N f z) (pow_pos (radius_pos N f e z) 3).le

theorem horizontalNumerator_continuous {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => horizontalNumerator N f (point x y)) := by
  have hF (q : Deck N) : ContDiffOn ℝ 2 (field N f q) {z : ℂ | 0 < z.im} :=
    (quotientForm N f q).2.2.1.1
  have hv (q : Deck N) := SelbergMaassMean.slice_continuous (hF q).continuousOn hy
  have hd (q : Deck N) := SelbergMaassMean.slice_continuous
    (dir_contDiffOn (hF q) (m:=1) (by norm_num) 1).continuousOn hy
  unfold horizontalNumerator pairEnergy phaseCurrent bracket
  simp only [normSq_eq_norm_sq]
  fun_prop

theorem horizontalWeight_continuous (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => horizontalWeight N f e (point x y)) :=
  (horizontalNumerator_continuous N f hy).div
    ((SelbergMaassAugmentedDirection.radius_slice_continuous N f e hy).pow 3)
    (fun x => pow_ne_zero 3 (radius_pos N f e (point x y)).ne')

/-- Fixed-regulator pair/phase weight lies below every smaller-regulator complete source current. -/
theorem horizontalWeight_le_current {a b : Ioi (0:ℝ)} (hab : a ≤ b) (z : ℂ) :
    horizontalWeight N f b z ≤ horizontalCurrentDensity N f a z := by
  have ha : 0 < (a:ℝ) := a.2
  have hb : 0 < (b:ℝ) := b.2
  have hr : radius N f a z ≤ radius N f b z := by
    apply Real.sqrt_le_sqrt
    have hab' : (a:ℝ) ≤ (b:ℝ) := hab
    nlinarith
  have h := div_le_div_of_nonneg_left (horizontalNumerator_nonneg N f z)
    (pow_pos (radius_pos N f a z) 3) (pow_le_pow_left₀ (radius_pos N f a z).le hr 3)
  apply h.trans
  apply div_le_div_of_nonneg_right _ (pow_pos (radius_pos N f a z) 3).le
  change horizontalNumerator N f z ≤ horizontalNumerator N f z+(a:ℝ)^2*directionalEnergy N f 1 (ofComplex z)
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => normSq_nonneg _)))

/-- Every fixed-regulator complete period supplies an actual lower certificate for limiting current energy. -/
theorem horizontalWeight_integral_le_limit (b : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) (x₀ : ℝ) :
    (∫ x in x₀..x₀+1, horizontalWeight N f b (point x y)) ≤ periodCurrentLimit N f y := by
  apply ge_of_tendsto (periodCurrentEnergy_tendsto N f hy)
  have he : ∀ᶠ a : Ioi (0:ℝ) in regulatorAtZero, (a:ℝ) < (b:ℝ) :=
    (tendsto_order.1 regulator_coe_limit).2 (b:ℝ) b.2
  filter_upwards [he] with a ha
  have hi : IntervalIntegrable (fun x => horizontalWeight N f b (point x y)) volume x₀ (x₀+1) :=
    (horizontalWeight_continuous N f b hy).intervalIntegrable x₀ (x₀+1)
  have hj := path_energy_intervalIntegrable N f a hy x₀ (x₀+1)
  have hh (x : ℝ) : horizontalWeight N f b (point x y) ≤
      directionalRemainder N f a 1 (ofComplex (point x y))/radius N f a (point x y) := by
    have h := horizontalWeight_le_current N f ha.le (point x y)
    have hc := horizontalCurrentDensity_eq N f a (ofComplex (point x y))
    rw [coe_ofComplex_point x hy] at hc
    rwa [← hc]
  have h := intervalIntegral.integral_mono_on (by linarith : x₀ ≤ x₀+1) hi hj (fun x _ => hh x)
  change _ ≤ pathEnergy N f a y x₀ (x₀+1) at h
  rwa [pathEnergy_one_period N f a hy] at h

/-- Any actual nonzero horizontal pair or phase current forces strictly positive limiting period energy. -/
theorem periodCurrentLimit_pos_of_numerator {y : ℝ} (hy : 0 < y) (x₀ : ℝ)
    (hp : 0 < horizontalNumerator N f (point x₀ y)) : 0 < periodCurrentLimit N f y := by
  let b : Ioi (0:ℝ) := ⟨1,by norm_num⟩
  have hc := horizontalWeight_continuous N f b hy
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by linarith : x₀ < x₀+1) continuousOn_const hc.continuousOn
    (fun x _ => horizontalWeight_nonneg N f b (point x y))
    ⟨x₀,⟨le_rfl,by linarith⟩,div_pos hp (pow_pos (radius_pos N f b _) 3)⟩
  have hi : 0 < ∫ x in x₀..x₀+1, horizontalWeight N f b (point x y) := by simpa using h
  exact hi.trans_le (horizontalWeight_integral_le_limit N f b hy x₀)

/-- Zero complete current limit annihilates the original horizontal pair/phase numerator everywhere on that height. -/
theorem horizontalNumerator_eq_zero_of_limit_zero {y : ℝ} (hy : 0 < y)
    (hE : periodCurrentLimit N f y=0) (x : ℝ) : horizontalNumerator N f (point x y)=0 := by
  by_contra hn
  have h := periodCurrentLimit_pos_of_numerator N f hy x
    (lt_of_le_of_ne (horizontalNumerator_nonneg N f _) (Ne.symm hn))
  simp only [hE,lt_self_iff_false] at h

/-- The complete pair energy and total phase current both vanish when the full current limit vanishes. -/
theorem pair_phase_eq_zero_of_limit_zero {y : ℝ} (hy : 0 < y)
    (hE : periodCurrentLimit N f y=0) (x : ℝ) :
    pairEnergy N f 1 (point x y)=0 ∧ phaseCurrent N f 1 (point x y)=0 := by
  have h := horizontalNumerator_eq_zero_of_limit_zero N f hy hE x
  have hn := pairEnergy_nonneg N f 1 (point x y)
  change pairEnergy N f 1 (point x y)+phaseCurrent N f 1 (point x y)^2=0 at h
  constructor
  · nlinarith [sq_nonneg (phaseCurrent N f 1 (point x y))]
  · nlinarith [sq_nonneg (phaseCurrent N f 1 (point x y))]

/-- On the original positive-density locus, zero limiting current forces a common real radial derivative. -/
theorem component_radial_of_limit_zero (z : ℍ) (hz : 0 < density N f z)
    (hE : periodCurrentLimit N f z.im=0) (q : Deck N) :
    dir 1 (field N f q) (z:ℂ)=(radialSlope N f 1 z:ℂ)*field N f q (z:ℂ) := by
  have h := horizontalNumerator_eq_zero_of_limit_zero N f z.im_pos hE z.re
  have hp : point z.re z.im=(z:ℂ) := by apply Complex.ext <;> simp [point]
  rw [hp] at h
  have hr := density_mul_radialResidual N f 1 z
  change density N f z*radialResidual N f 1 (radialSlope N f 1 z) z=horizontalNumerator N f (z:ℂ) at hr
  rw [h] at hr
  have hzero := (mul_eq_zero.mp hr).resolve_left hz.ne'
  have hv := (radialResidual_eq_zero_iff N f 1 (radialSlope N f 1 z) z).mp hzero q
  simpa only [field,Function.comp_apply,ofComplex_apply] using hv

/-- Bounded original nodal path products force all horizontal pair and phase currents to vanish on their entire height. -/
theorem pair_phase_eq_zero_of_node_bddCost (z : ℍ) (hz : density N f z=0)
    (hb : BddAbove (range (fun e : Ioi (0:ℝ) => periodCost N f e z.im))) (x : ℝ) :
    pairEnergy N f 1 (point x z.im)=0 ∧ phaseCurrent N f 1 (point x z.im)=0 :=
  pair_phase_eq_zero_of_limit_zero N f z.im_pos
    (periodCurrentLimit_eq_zero_of_node_bddCost N f z hz hb) x

/-- Original horizontal derivative energy is nonnegative before any division. -/
theorem directionalEnergy_nonneg (z : ℍ) : 0 ≤ directionalEnergy N f 1 z :=
  Finset.sum_nonneg (fun _ _ => normSq_nonneg _)

/-- Original C² regularity controls horizontal derivative energy continuously. -/
theorem directionalEnergy_continuous {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => directionalEnergy N f 1 (ofComplex (point x y))) := by
  apply continuous_finsetSum Finset.univ
  intro q _
  simp_rw [coe_ofComplex_point _ hy]
  exact Complex.continuous_normSq.comp (SelbergMaassMean.slice_continuous
    (dir_contDiffOn (quotientForm N f q).2.2.1.1 (m:=1) (by norm_num) 1).continuousOn hy)

/-- The complete original horizontal current is nonnegative through nodes. -/
theorem horizontalCurrentDensity_nonneg (e : Ioi (0:ℝ)) (z : ℂ) :
    0 ≤ horizontalCurrentDensity N f e z :=
  div_nonneg (add_nonneg (horizontalNumerator_nonneg N f z)
    (mul_nonneg (sq_nonneg _) (directionalEnergy_nonneg N f _))) (pow_pos (radius_pos N f e z) 3).le

/-- Complete current continuity comes from the original source, including the regulator-gradient term. -/
theorem horizontalCurrentDensity_continuous (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x => horizontalCurrentDensity N f e (point x y)) :=
  ((horizontalNumerator_continuous N f hy).add
    ((directionalEnergy_continuous N f hy).const_mul ((e:ℝ)^2))).div
    ((SelbergMaassAugmentedDirection.radius_slice_continuous N f e hy).pow 3)
    (fun x => pow_ne_zero 3 (radius_pos N f e (point x y)).ne')

/-- Any positively oriented subinterval of a full original period is charged to that period's complete energy. -/
theorem interval_current_le_period (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y)
    (a b : ℝ) (hab : a ≤ b) (hb : b ≤ a+1) :
    (∫ x in a..b, horizontalCurrentDensity N f e (point x y)) ≤ periodCurrentEnergy N f e y := by
  have hi : IntervalIntegrable (fun x => horizontalCurrentDensity N f e (point x y)) volume a (a+1) :=
    (horizontalCurrentDensity_continuous N f e hy).intervalIntegrable a (a+1)
  have h := intervalIntegral.integral_mono_interval le_rfl hab hb
    (Eventually.of_forall (fun x => horizontalCurrentDensity_nonneg N f e (point x y))) hi
  rw [← pathEnergy_eq_current_integral N f e hy a (a+1), pathEnergy_one_period N f e hy] at h
  exact h

/-- A nonflat original node supplies a positive derivative-energy floor on its own right neighborhood. -/
theorem exists_node_derivative_floor (z : ℍ) (hG : 0 < directionalEnergy N f 1 z) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ x ∈ Icc z.re (z.re+d),
      directionalEnergy N f 1 z/2 ≤ directionalEnergy N f 1 (ofComplex (point x z.im)) := by
  have he : ∀ᶠ x in 𝓝 z.re, directionalEnergy N f 1 z/2 <
      directionalEnergy N f 1 (ofComplex (point x z.im)) := by
    apply (directionalEnergy_continuous N f z.im_pos).continuousAt.eventually
    apply lt_mem_nhds
    change directionalEnergy N f 1 z/2 < directionalEnergy N f 1 (ofComplex (point z.re z.im))
    rw [ofComplex_point_self]
    linarith
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min (r/2) 1,lt_min (half_pos hr) (by norm_num),min_le_right _ _,?_⟩
  intro x hx
  have hb : x ∈ Metric.ball z.re r := by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hx.1)]
    have ht := min_le_left (r/2) (1:ℝ)
    linarith [hx.2]
  exact (hs hb).le

/-- Actual first-derivative energy at a common zero yields a positive current mass at every small regulator. -/
theorem exists_node_current_floor (z : ℍ) (hz : density N f z=0)
    (hG : 0 < directionalEnergy N f 1 z) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ e : Ioi (0:ℝ), (e:ℝ) ≤ d → c ≤ periodCurrentEnergy N f e z.im := by
  obtain ⟨L,hL,hbound⟩ := exists_linear_amplitude_bound_at_node N f z hz
  obtain ⟨d,hd,hd1,hfloor⟩ := exists_node_derivative_floor N f z hG
  let k : ℝ := directionalEnergy N f 1 z/2
  have hk : 0 < k := half_pos hG
  have hLp : 0 < L+1 := by linarith
  refine ⟨k/(L+1)^3,d,div_pos hk (pow_pos hLp 3),hd,?_⟩
  intro e hed
  have hep : 0 < (e:ℝ) := e.2
  have he1 : (e:ℝ) ≤ 1 := hed.trans hd1
  have hlocal (x : ℝ) (hx : x ∈ Icc z.re (z.re+(e:ℝ))) :
      (k/(L+1)^3)/(e:ℝ) ≤ horizontalCurrentDensity N f e (point x z.im) := by
    have hxu : x ∈ Icc z.re (z.re+1) := ⟨hx.1,by linarith [hx.2]⟩
    have hxd : x ∈ Icc z.re (z.re+d) := ⟨hx.1,by linarith [hx.2]⟩
    have hGx : k ≤ directionalEnergy N f 1 (ofComplex (point x z.im)) := hfloor x hxd
    have hR : radius N f e (point x z.im) ≤ (L+1)*(e:ℝ) := by
      have ha := hbound x hxu
      have hr := (radius_sub_amplitude_bounds N f e z.im x).2
      have ht : x-z.re ≤ (e:ℝ) := by linarith [hx.2]
      have hh := mul_le_mul_of_nonneg_left ht (by linarith : 0 ≤ L)
      linarith
    have hRpos := radius_pos N f e (point x z.im)
    have hcub := pow_le_pow_left₀ hRpos.le hR 3
    have hA := div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg (e:ℝ)) hk.le)
      (pow_pos hRpos 3) hcub
    have hB := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hGx (sq_nonneg (e:ℝ))) (pow_pos hRpos 3).le
    have hC : (e:ℝ)^2*directionalEnergy N f 1 (ofComplex (point x z.im))/radius N f e (point x z.im)^3 ≤
        horizontalCurrentDensity N f e (point x z.im) := by
      apply div_le_div_of_nonneg_right _ (pow_pos hRpos 3).le
      exact le_add_of_nonneg_left (horizontalNumerator_nonneg N f _)
    have heq : (k/(L+1)^3)/(e:ℝ)=(e:ℝ)^2*k/((L+1)*(e:ℝ))^3 := by
      field_simp
    rw [heq]
    exact hA.trans (hB.trans hC)
  have hi : IntervalIntegrable (fun x => horizontalCurrentDensity N f e (point x z.im)) volume z.re (z.re+(e:ℝ)) :=
    (horizontalCurrentDensity_continuous N f e z.im_pos).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (by linarith : z.re ≤ z.re+(e:ℝ))
    intervalIntegrable_const hi hlocal
  have hs : k/(L+1)^3 ≤ ∫ x in z.re..z.re+(e:ℝ), horizontalCurrentDensity N f e (point x z.im) := by
    simpa only [intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,mul_div_cancel₀ _ hep.ne'] using h
  exact hs.trans (interval_current_le_period N f e z.im_pos z.re (z.re+(e:ℝ))
    (by linarith) (by linarith))

/-- Every actual nonflat horizontal common zero forces a strictly positive complete current-period limit. -/
theorem periodCurrentLimit_pos_of_nonflat_node (z : ℍ) (hz : density N f z=0)
    (hG : 0 < directionalEnergy N f 1 z) : 0 < periodCurrentLimit N f z.im := by
  obtain ⟨c,d,hc,hd,hfloor⟩ := exists_node_current_floor N f z hz hG
  apply hc.trans_le
  apply ge_of_tendsto (periodCurrentEnergy_tendsto N f z.im_pos)
  have he : ∀ᶠ e : Ioi (0:ℝ) in regulatorAtZero, (e:ℝ) < d :=
    (tendsto_order.1 regulator_coe_limit).2 d hd
  filter_upwards [he] with e he
  exact hfloor e he.le

/-- Zero complete current limit forces every original node to be flat to first horizontal order. -/
theorem directionalEnergy_eq_zero_at_node_of_limit_zero (z : ℍ) (hz : density N f z=0)
    (hE : periodCurrentLimit N f z.im=0) : directionalEnergy N f 1 z=0 := by
  by_contra hn
  have h := periodCurrentLimit_pos_of_nonflat_node N f z hz
    (lt_of_le_of_ne (directionalEnergy_nonneg N f z) (Ne.symm hn))
  simp only [hE,lt_self_iff_false] at h

/-- Each original component has zero horizontal derivative at nodes when the full current limit vanishes. -/
theorem component_derivative_eq_zero_at_node_of_limit_zero (z : ℍ) (hz : density N f z=0)
    (hE : periodCurrentLimit N f z.im=0) (q : Deck N) : dir 1 (field N f q) (z:ℂ)=0 := by
  have h := directionalEnergy_eq_zero_at_node_of_limit_zero N f z hz hE
  unfold directionalEnergy at h
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => normSq_nonneg _)] at h
  exact Complex.normSq_eq_zero.mp (h q (Finset.mem_univ q))

/-- The common real radial derivative law extends through every original node in the zero-limit case. -/
theorem component_radial_everywhere_of_limit_zero (z : ℍ)
    (hE : periodCurrentLimit N f z.im=0) (q : Deck N) :
    dir 1 (field N f q) (z:ℂ)=(radialSlope N f 1 z:ℂ)*field N f q (z:ℂ) := by
  by_cases hz : density N f z=0
  · rw [component_derivative_eq_zero_at_node_of_limit_zero N f z hz hE q]
    have hv := component_zero_of_density_zero N f z hz q
    simp only [field,Function.comp_apply,ofComplex_apply,hv,mul_zero]
  · exact component_radial_of_limit_zero N f z (lt_of_le_of_ne (density_nonneg N f z) (Ne.symm hz)) hE q

/-- Nonflat original nodes make the complete resistance/current product diverge. -/
theorem periodCost_tendsto_atTop_of_nonflat_node (z : ℍ) (hz : density N f z=0)
    (hG : 0 < directionalEnergy N f 1 z) :
    Tendsto (fun e : Ioi (0:ℝ) => periodCost N f e z.im) regulatorAtZero atTop :=
  periodCost_tendsto_atTop_of_node N f z hz (periodCurrentLimit_pos_of_nonflat_node N f z hz hG)

/-- Bounded nodal products force every component's first horizontal derivative to vanish at that node. -/
theorem component_derivative_eq_zero_of_node_bddCost (z : ℍ) (hz : density N f z=0)
    (hb : BddAbove (range (fun e : Ioi (0:ℝ) => periodCost N f e z.im))) (q : Deck N) :
    dir 1 (field N f q) (z:ℂ)=0 :=
  component_derivative_eq_zero_at_node_of_limit_zero N f z hz
    (periodCurrentLimit_eq_zero_of_node_bddCost N f z hz hb) q

/-- Original unit density periodicity extends a zero-free complete period to its whole height. -/
theorem density_pos_on_height_of_zero_free_period {y : ℝ} (hy : 0 < y)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x y))) (x : ℝ) :
    0 < density N f (ofComplex (point x y)) := by
  obtain ⟨t,ht,he⟩ := (density_slice_periodic N f hy).exists_mem_Ico₀ (by norm_num) x
  rw [he]
  exact hp t ⟨ht.1,ht.2.le⟩

/-- On a zero-free original height, zero limiting current makes every normalized component constant. -/
theorem direction_constant_of_zero_free_limit_zero {y : ℝ} (hy : 0 < y)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N f (ofComplex (point x y)))
    (hE : periodCurrentLimit N f y=0) (q : Deck N) (a b : ℝ) :
    direction N f q (ofComplex (point a y))=direction N f q (ofComplex (point b y)) := by
  have hpos := density_pos_on_height_of_zero_free_period N f hy hp
  have hd (x : ℝ) : HasDerivAt (fun t => direction N f q (ofComplex (point t y))) 0 x := by
    let z : ℍ := ofComplex (point x y)
    have hco : (z:ℂ)=point x y := coe_ofComplex_point x hy
    have him : z.im=y := by change (z:ℂ).im=y; rw [hco]; simp [point]
    have hz : 0 < density N f z := hpos x
    have hEz : periodCurrentLimit N f z.im=0 := by rwa [him]
    have hrad := component_radial_of_limit_zero N f z hz hEz q
    have hdir := amplitude_mul_direction_dir N f q 1 z hz
    have hrad' : dir 1 ((quotientForm N f q).1.1 ∘ ofComplex) (z:ℂ)=
        (radialSlope N f 1 z:ℂ)*(quotientForm N f q).1.1 z := by
      simpa only [field,Function.comp_apply,ofComplex_apply] using hrad
    rw [hrad',sub_self] at hdir
    have ha : (Real.sqrt (density N f z):ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hz).ne'
    have hdz := (mul_eq_zero.mp hdir).resolve_left ha
    have hdiff := direction_differentiableAt N f q z hz
    rw [hco] at hdiff hdz
    have h := hdiff.hasFDerivAt.comp_hasDerivAt x (point_horizontal x y)
    change HasDerivAt (fun t => direction N f q (ofComplex (point t y)))
      (dir 1 (direction N f q ∘ ofComplex) (point x y)) x at h
    rwa [hdz] at h
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) a b

/-- Actual exceptional Maass zero means force positive limiting current on every zero-free complete period. -/
theorem exceptional_periodCurrentLimit_pos_of_zero_free (μ : Ioo (0:ℝ) (1/4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (μ:ℝ))
    {y : ℝ} (hy : 0 < y)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N g (ofComplex (point x y))) :
    0 < periodCurrentLimit N g y := by
  by_contra hn
  have hE : periodCurrentLimit N g y=0 := le_antisymm (le_of_not_gt hn) (periodCurrentLimit_nonneg N g hy)
  let z : ℍ := ofComplex (point 0 y)
  have hz : 0 < density N g z := hp 0 (by constructor <;> norm_num)
  have hco : (z:ℂ)=point 0 y := coe_ofComplex_point 0 hy
  have him : z.im=y := by change (z:ℂ).im=y; rw [hco]; simp [point]
  obtain ⟨x,hx,hw,hs⟩ := exists_separated_direction N μ g z hz
  rw [him] at hs
  have hc (q : Deck N) : direction N g q (ofComplex (point x y))=direction N g q z :=
    direction_constant_of_zero_free_limit_zero N g hy hp hE q x 0
  simp only [directionDistanceSq,hc,sub_self,normSq_zero,Finset.sum_const_zero] at hs
  norm_num at hs

/-- In the exceptional source class, zero limiting current forces an original node with zero first horizontal energy. -/
theorem exceptional_exists_flat_node_of_limit_zero (μ : Ioo (0:ℝ) (1/4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (μ:ℝ))
    {y : ℝ} (hy : 0 < y) (hE : periodCurrentLimit N g y=0) :
    ∃ x ∈ Icc (0:ℝ) 1, density N g (ofComplex (point x y))=0 ∧
      directionalEnergy N g 1 (ofComplex (point x y))=0 := by
  have hn : ∃ x ∈ Icc (0:ℝ) 1, density N g (ofComplex (point x y))=0 := by
    by_contra hn
    have hp (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : 0 < density N g (ofComplex (point x y)) :=
      lt_of_le_of_ne (density_nonneg N g _) (Ne.symm (fun hz => hn ⟨x,hx,hz⟩))
    have h := exceptional_periodCurrentLimit_pos_of_zero_free N μ g hy hp
    simp only [hE,lt_self_iff_false] at h
  obtain ⟨x,hx,hz⟩ := hn
  refine ⟨x,hx,hz,?_⟩
  have him : (ofComplex (point x y)).im=y := by
    change ((ofComplex (point x y):ℍ):ℂ).im=y
    rw [coe_ofComplex_point x hy]
    simp [point]
  exact directionalEnergy_eq_zero_at_node_of_limit_zero N g (ofComplex (point x y)) hz (by rwa [him])

/-- Every exceptional-source height has positive limiting current or an original first-order-flat node. -/
theorem exceptional_positive_limit_or_flat_node (μ : Ioo (0:ℝ) (1/4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (μ:ℝ))
    {y : ℝ} (hy : 0 < y) :
    0 < periodCurrentLimit N g y ∨ ∃ x ∈ Icc (0:ℝ) 1,
      density N g (ofComplex (point x y))=0 ∧ directionalEnergy N g 1 (ofComplex (point x y))=0 := by
  by_cases hE : 0 < periodCurrentLimit N g y
  · exact Or.inl hE
  · exact Or.inr (exceptional_exists_flat_node_of_limit_zero N μ g hy
      (le_antisymm (le_of_not_gt hE) (periodCurrentLimit_nonneg N g hy)))

end
end GaloisForLFunctions.RHTower.SelbergMaassPeriodCurrentRigidity
