import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCompleteDivisorCenterAtTheCubicMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSurplusOfTheLowerPrimeTriples
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Prime counting on multiplicative triple boxes

Each section of a multiplicative sublevel set in a positive cube is an
interval. Replacing the prime-counting measure one coordinate at a time
therefore costs at most the uniform interval discrepancy times the two
remaining masses.
-/

noncomputable section
open Filter MeasureTheory Set
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def boxTest (a b t x y z : ℝ) : ℝ :=
  if x ∈ Ioc a b ∧ y ∈ Ioc a b ∧ z ∈ Ioc a b ∧ x*y*z ≤ t then 1 else 0

private theorem box_test_measurable (a b t : ℝ) :
    Measurable (fun h : (ℝ × ℝ) × ℝ => boxTest a b t h.1.1 h.1.2 h.2) := by
  let X := fun h : (ℝ × ℝ) × ℝ => h.1.1
  let Y := fun h : (ℝ × ℝ) × ℝ => h.1.2
  let Z := fun h : (ℝ × ℝ) × ℝ => h.2
  have hx : Measurable X := measurable_fst.comp measurable_fst
  have hy : Measurable Y := measurable_snd.comp measurable_fst
  have hz : Measurable Z := measurable_snd
  exact Measurable.ite ((measurableSet_Ioc.preimage hx).inter
    ((measurableSet_Ioc.preimage hy).inter ((measurableSet_Ioc.preimage hz).inter
    (measurableSet_le ((hx.mul hy).mul hz) measurable_const)))) measurable_const measurable_const

private theorem box_test_bound (a b t x y z : ℝ) : |boxTest a b t x y z| ≤ 1 := by
  unfold boxTest
  split <;> norm_num

private theorem box_test_swap_left (a b t x y z : ℝ) :
    boxTest a b t x y z=boxTest a b t y x z := by
  simp only [boxTest,mul_comm x y,and_left_comm]

private theorem box_test_swap_right (a b t x y z : ℝ) :
    boxTest a b t x y z=boxTest a b t x z y := by
  simp only [boxTest,mul_right_comm x y z,and_left_comm]

private theorem integrable_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} {C : ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

private theorem abs_integral_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℝ} {C : ℝ} (h : ∀ x, |f x| ≤ C) :
    |∫ x,f x ∂μ| ≤ C*μ.real univ := by
  rw [←Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const (μ:=μ) (f:=f) (C:=C)
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using h x)

private def tripleBoxMass (a b t : ℝ) (μ ν κ : Measure ℝ) : ℝ :=
  ∫ x,∫ y,∫ z,boxTest a b t x y z ∂κ ∂ν ∂μ

private theorem box_slice_measurable (a b t : ℝ) (κ : Measure ℝ) [IsFiniteMeasure κ] :
    Measurable (fun u : ℝ × ℝ => ∫ z,boxTest a b t u.1 u.2 z ∂κ) :=
  ((box_test_measurable a b t).stronglyMeasurable.integral_prod_right
    (ν:=κ)).measurable

private theorem triple_box_swap_left (a b t : ℝ) (μ ν κ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure κ] :
    tripleBoxMass a b t μ ν κ=tripleBoxMass a b t ν μ κ := by
  let F := fun x y : ℝ => ∫ z,boxTest a b t x y z ∂κ
  have hi : Integrable (Function.uncurry F) (μ.prod ν) :=
    integrable_bounded _ (box_slice_measurable a b t κ) fun h =>
      abs_integral_bounded _ (box_test_bound a b t h.1 h.2)
  unfold tripleBoxMass
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with x
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => box_test_swap_left a b t x y z)

private theorem triple_box_swap_right (a b t : ℝ) (μ ν κ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure κ] :
    tripleBoxMass a b t μ ν κ=tripleBoxMass a b t μ κ ν := by
  apply integral_congr_ae
  filter_upwards with x
  have hm : Measurable (fun u : ℝ × ℝ => boxTest a b t x u.1 u.2) :=
    (box_test_measurable a b t).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [integral_integral_swap (f:=fun y z => boxTest a b t x y z) (integrable_bounded (ν.prod κ) hm
    (fun h => box_test_bound a b t x h.1 h.2))]
  apply integral_congr_ae
  filter_upwards with z
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => box_test_swap_right a b t x y z)

private theorem box_slice_at {a b t x y : ℝ} (ha : 0<a) (hx : x ∈ Ioc a b)
    (hy : y ∈ Ioc a b) (μ : Measure ℝ) :
    (∫ z,boxTest a b t x y z ∂μ) = μ.real (Ioc a (max a (min b (t/(x*y))))) := by
  let v := max a (min b (t/(x*y)))
  have hxy := mul_pos (ha.trans hx.1) (ha.trans hy.1)
  have htst (z : ℝ) : boxTest a b t x y z=(Ioc a v).indicator (fun _ => (1:ℝ)) z := by
    have he : z ∈ Ioc a b ∧ x*y*z ≤ t ↔ z ∈ Ioc a v := by
      simp only [mem_Ioc,v,le_max_iff,le_min_iff]
      rw [mul_comm (x*y) z,←le_div_iff₀ hxy]
      exact ⟨fun h => ⟨h.1.1,Or.inr ⟨h.1.2,h.2⟩⟩,fun h =>
        let hs := h.2.resolve_left (not_le.mpr h.1)
        ⟨⟨h.1,hs.1⟩,hs.2⟩⟩
    simp only [boxTest,Set.indicator,hx,hy,true_and,he]
  simp_rw [htst]
  exact integral_indicator_one measurableSet_Ioc

private theorem box_slice_error {a b t E : ℝ} (ha : 0<a) (hab : a ≤ b)
    (μ ν : Measure ℝ) (hE : 0 ≤ E)
    (h : ∀ v ∈ Icc a b, |μ.real (Ioc a v)-ν.real (Ioc a v)| ≤ E) (x y : ℝ) :
    |(∫ z,boxTest a b t x y z ∂μ)-(∫ z,boxTest a b t x y z ∂ν)| ≤ E := by
  by_cases hx : x ∈ Ioc a b
  · by_cases hy : y ∈ Ioc a b
    · rw [box_slice_at ha hx hy,box_slice_at ha hx hy]
      exact h _ ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩
    · simpa only [boxTest,hy,false_and,and_false,if_false,integral_zero,sub_self,abs_zero] using hE
  · simpa only [boxTest,hx,false_and,if_false,integral_zero,sub_self,abs_zero] using hE

private theorem box_slice_integrable (a b t x : ℝ) (ν κ : Measure ℝ)
    [IsFiniteMeasure ν] [IsFiniteMeasure κ] :
    Integrable (fun y => ∫ z,boxTest a b t x y z ∂κ) ν :=
  integrable_bounded _ ((box_slice_measurable a b t κ).comp (measurable_const.prodMk measurable_id))
    fun y => abs_integral_bounded _ (box_test_bound a b t x y)

private theorem box_double_integrable (a b t : ℝ) (μ ν κ : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure κ] :
    Integrable (fun x => ∫ y,∫ z,boxTest a b t x y z ∂κ ∂ν) μ := by
  apply integrable_bounded _
    ((box_slice_measurable a b t κ).stronglyMeasurable.integral_prod_right' (ν:=ν)).measurable
  exact fun x => abs_integral_bounded _ fun y => abs_integral_bounded _ (box_test_bound a b t x y)

private theorem replace_last_measure {a b t E : ℝ} (ha : 0<a) (hab : a ≤ b)
    (μ ν κ κ₂ : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure κ] [IsFiniteMeasure κ₂] (hE : 0 ≤ E)
    (h : ∀ v ∈ Icc a b, |κ.real (Ioc a v)-κ₂.real (Ioc a v)| ≤ E) :
    |tripleBoxMass a b t μ ν κ-tripleBoxMass a b t μ ν κ₂| ≤ E*ν.real univ*μ.real univ := by
  unfold tripleBoxMass
  rw [←integral_sub (box_double_integrable a b t μ ν κ) (box_double_integrable a b t μ ν κ₂)]
  apply abs_integral_bounded
  intro x
  rw [←integral_sub (box_slice_integrable a b t x ν κ) (box_slice_integrable a b t x ν κ₂)]
  exact abs_integral_bounded _ (box_slice_error ha hab κ κ₂ hE h x)

/-- The three substitutions preserve the same sharp product cut. Their
cost is the interval discrepancy times the three possible pairs of masses. -/
private theorem triple_box_measure_error {a b t E : ℝ} (ha : 0<a) (hab : a ≤ b)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hE : 0 ≤ E)
    (h : ∀ v ∈ Icc a b, |μ.real (Ioc a v)-ν.real (Ioc a v)| ≤ E) :
    |tripleBoxMass a b t μ μ μ-tripleBoxMass a b t ν ν ν| ≤ 
      E*((μ.real univ)^2+μ.real univ*ν.real univ+(ν.real univ)^2) := by
  have h1 := replace_last_measure (t:=t) ha hab μ μ μ ν hE h
  have h2 := replace_last_measure (t:=t) ha hab μ ν μ ν hE h
  have h3 := replace_last_measure (t:=t) ha hab ν ν μ ν hE h
  rw [triple_box_swap_right a b t μ ν μ] at h2
  rw [triple_box_swap_right a b t ν ν μ,triple_box_swap_left a b t ν μ ν] at h3
  apply abs_le.mpr
  constructor <;> linarith only [(abs_le.mp h1).1,(abs_le.mp h1).2,
    (abs_le.mp h2).1,(abs_le.mp h2).2,(abs_le.mp h3).1,(abs_le.mp h3).2]

open _root_.RHTower

/-- Rescaled ordinary primes in the fixed interval (a,b], with mass log(y)/y per prime. -/
private def boxPrimeMeasure (a b y : ℝ) : Measure ℝ :=
  (Real.toNNReal (Real.log y/y)) •
    ∑ p ∈ windowPrimes (a*y) (b*y),Measure.dirac ((p:ℝ)/y)

private instance (a b y : ℝ) : IsFiniteMeasure (boxPrimeMeasure a b y) := by
  unfold boxPrimeMeasure
  infer_instance

private theorem box_prime_integral {y : ℝ} (hy : 1 ≤ y) (a b : ℝ) (f : ℝ → ℝ) :
    (∫ x,f x ∂boxPrimeMeasure a b y) =
      (Real.log y/y)*∑ p ∈ windowPrimes (a*y) (b*y),f ((p:ℝ)/y) := by
  rw [boxPrimeMeasure,←Measure.coe_nnreal_smul,integral_smul_measure,
    integral_finsetSum_measure (fun p _ => integrable_dirac (by finiteness))]
  simp only [integral_dirac,ENNReal.coe_toReal,Real.coe_toNNReal _ (div_nonneg (Real.log_nonneg hy)
    (zero_le_one.trans hy)),smul_eq_mul]

private theorem box_prime_interval {a b v y : ℝ} (ha : 0<a) (hv : v ∈ Icc a b) (hy : 1 ≤ y) :
    (boxPrimeMeasure a b y).real (Ioc a v)=
      (Real.log y/y)*(windowPrimes (a*y) (v*y)).card := by
  have hy0 := zero_lt_one.trans_le hy
  have hav := mul_nonneg ha.le hy0.le
  have hvy := mul_nonneg (ha.le.trans hv.1) hy0.le
  have hby := mul_nonneg ((ha.le.trans hv.1).trans hv.2) hy0.le
  have hset : (windowPrimes (a*y) (b*y)).filter (fun p : ℕ => (p:ℝ)/y ∈ Ioc a v)=
      windowPrimes (a*y) (v*y) := by
    ext p
    simp only [Finset.mem_filter,mem_windowPrimes hav hby,mem_windowPrimes hav hvy,
      mem_Ioc,lt_div_iff₀ hy0,div_le_iff₀ hy0]
    exact ⟨fun h => ⟨h.1.1,h.1.2.1,h.2.2⟩,fun h =>
      ⟨⟨h.1,h.2.1,h.2.2.trans (mul_le_mul_of_nonneg_right hv.2 hy0.le)⟩,h.2⟩⟩
  rw [←integral_indicator_one measurableSet_Ioc,box_prime_integral hy]
  simp only [Set.indicator,Pi.one_apply]
  rw [←Finset.sum_filter, hset,Finset.sum_const,nsmul_eq_mul,mul_one]

private theorem box_prime_total {a b y : ℝ} (hy : 1 ≤ y) :
    (boxPrimeMeasure a b y).real univ=(Real.log y/y)*(windowPrimes (a*y) (b*y)).card := by
  have h := box_prime_integral hy a b (fun _ => 1)
  simpa only [Finset.sum_const,nsmul_eq_mul,integral_const,smul_eq_mul,mul_one] using h

private def boxLebesgue (a b : ℝ) : Measure ℝ := volume.restrict (Ioc a b)

private instance (a b : ℝ) : IsFiniteMeasure (boxLebesgue a b) := by
  unfold boxLebesgue
  infer_instance

private theorem box_lebesgue_interval {a b v : ℝ} (hv : v ∈ Icc a b) :
    (boxLebesgue a b).real (Ioc a v)=v-a := by
  rw [boxLebesgue,measureReal_restrict_apply measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Ioc_right hv.2),Real.volume_real_Ioc_of_le hv.1]

private theorem box_lebesgue_total {a b : ℝ} (hab : a ≤ b) :
    (boxLebesgue a b).real univ=b-a := by
  rw [boxLebesgue,measureReal_restrict_apply MeasurableSet.univ,univ_inter,Real.volume_real_Ioc_of_le hab]

/-- Unnormalized count of ordinary ordered prime triples in a fixed positive
cube subject to the sharp product threshold, multiplied by (log y/y)³. -/
def normalizedPrimeTripleCount (a b t y : ℝ) : ℝ :=
  let P := windowPrimes (a*y) (b*y)
  (Real.log y/y)^3*∑ p ∈ P,∑ q ∈ P,∑ r ∈ P, boxTest a b t ((p:ℝ)/y) ((q:ℝ)/y) ((r:ℝ)/y)

private theorem box_prime_count {y : ℝ} (hy : 1 ≤ y) (a b t : ℝ) :
    tripleBoxMass a b t (boxPrimeMeasure a b y) (boxPrimeMeasure a b y) (boxPrimeMeasure a b y)=
      normalizedPrimeTripleCount a b t y := by
  simp only [tripleBoxMass,box_prime_integral hy,normalizedPrimeTripleCount,
    ←Finset.mul_sum]
  ring

/-- Lebesgue volume in (a,b]³ below the specified product threshold. -/
def primeTripleBoxVolume (a b t : ℝ) : ℝ :=
  tripleBoxMass a b t (boxLebesgue a b) (boxLebesgue a b) (boxLebesgue a b)

/-- Uniform PNT on coordinate intervals gives the Lebesgue volume of the entire
three-dimensional product sublevel set, retaining equality on its upper face. -/
theorem normalized_prime_triple_count_tendsto {a b : ℝ} (ha : 1/2 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) (t : ℝ) :
    Tendsto (normalizedPrimeTripleCount a b t) atTop
      (nhds (primeTripleBoxVolume a b t)) := by
  unfold primeTripleBoxVolume
  obtain ⟨K,hK,hwin⟩ := triple_box_prime_window_discrepancy
  have ha0 := (by norm_num : (0:ℝ)<1/2).trans_le ha
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hwin,eventually_ge_atTop 2,Real.tendsto_log_atTop.eventually_gt_atTop
    (max K (27*K/ε))] with y hslice hy hlog
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hy0 := zero_lt_one.trans_le hy1
  have hL := Real.log_pos (by linarith only [hy] : 1<y)
  have hdisc {v : ℝ} (hv : v ∈ Icc a b) :
      |(boxPrimeMeasure a b y).real (Ioc a v)-(boxLebesgue a b).real (Ioc a v)| ≤ K/Real.log y := by
    rw [box_prime_interval ha0 hv hy1,box_lebesgue_interval hv]
    have hh := hslice (a*y) (v*y) (by linarith only [mul_le_mul_of_nonneg_right ha hy0.le])
      (mul_le_mul_of_nonneg_right hv.1 hy0.le) (mul_le_mul_of_nonneg_right (hv.2.trans hb) hy0.le)
    have he : (Real.log y/y)*(windowPrimes (a*y) (v*y)).card-(v-a) =
        (((windowPrimes (a*y) (v*y)).card:ℝ)*Real.log y-(v*y-a*y))/y := by field_simp
    rw [he,abs_div,abs_of_pos hy0]
    exact (div_le_div_of_nonneg_right hh hy0.le).trans_eq (by field_simp)
  have hmass := (abs_le.mp (hdisc (v:=b) ⟨hab,le_rfl⟩)).2
  rw [box_prime_interval ha0 ⟨hab,le_rfl⟩ hy1,box_lebesgue_interval ⟨hab,le_rfl⟩,
    ←box_prime_total hy1] at hmass
  have hE : 0 ≤ K/Real.log y := div_nonneg hK.le hL.le
  have hE1 : K/Real.log y ≤ 1 := (div_le_one hL).mpr ((le_max_left _ _).trans hlog.le)
  have hμ0 := measureReal_nonneg (μ:=boxPrimeMeasure a b y) (s:=univ)
  have hμ : (boxPrimeMeasure a b y).real univ ≤ 3 := by linarith only [hmass,hE1,ha,hb]
  have hν0 := sub_nonneg.mpr hab
  have hν : b-a ≤ 3 := by linarith only [ha,hb]
  have hbound := triple_box_measure_error (t:=t) ha0 hab _ _ hE (fun v hv => hdisc hv)
  rw [box_lebesgue_total hab,box_prime_count hy1] at hbound
  rw [Real.dist_eq]
  apply hbound.trans_lt
  have hsize : ((boxPrimeMeasure a b y).real univ)^2+
      (boxPrimeMeasure a b y).real univ*(b-a)+(b-a)^2 ≤ 27 := by
    nlinarith only [mul_le_mul hμ hμ hμ0 (by norm_num : (0:ℝ) ≤ 3),
      mul_le_mul hμ hν hν0 (by norm_num : (0:ℝ) ≤ 3),
      mul_le_mul hν hν hν0 (by norm_num : (0:ℝ) ≤ 3)]
  apply (mul_le_mul_of_nonneg_left hsize hE).trans_lt
  rw [div_mul_eq_mul_div,div_lt_iff₀ hL]
  have he := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hlog)
  linarith only [he]


private theorem box_volume_by_slices {a b : ℝ} (ha : 0<a) (hab : a ≤ b) (t : ℝ) :
    primeTripleBoxVolume a b t =
      ∫ x in a..b,∫ y in a..b,(max a (min b (t/(x*y)))-a) := by
  unfold primeTripleBoxVolume tripleBoxMass
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [intervalIntegral.integral_of_le hab]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  dsimp only
  rw [box_slice_at ha hx hy,box_lebesgue_interval ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩]

private theorem upper_volume_column {s v : ℝ} (hv : 1 ≤ v) (hvs : v ≤ s) :
    (∫ y in 1..s,(max 1 (v/y)-1)) = 1-v+v*Real.log v := by
  let f := fun y : ℝ => max 1 (v/y)-1
  have hc {l r : ℝ} (hl : 0<l) (hlr : l ≤ r) : ContinuousOn f (uIcc l r) := by
    rw [uIcc_of_le hlr]
    exact (continuousOn_const.sup (continuousOn_const.div continuousOn_id
      (fun _ h => (hl.trans_le h.1).ne'))).sub continuousOn_const
  change (∫ y in 1..s,f y)=_
  rw [←intervalIntegral.integral_add_adjacent_intervals (hc zero_lt_one hv).intervalIntegrable
    (hc (zero_lt_one.trans_le hv) hvs).intervalIntegrable]
  have hu : (∫ y in 1..v,f y)=(∫ y in 1..v,(v/y-1)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hv] at hy
    exact congrArg (· - 1) (max_eq_right ((one_le_div (zero_lt_one.trans_le hy.1)).mpr hy.2))
  have hz : (∫ y in v..s,f y)=0 := by
    calc _ = ∫ _ in v..s,(0:ℝ) := by
           apply intervalIntegral.integral_congr
           intro y hy
           rw [uIcc_of_le hvs] at hy
           change max 1 (v/y)-1=0
           rw [max_eq_left ((div_le_one ((zero_lt_one.trans_le hv).trans_le hy.1)).mpr hy.1),sub_self]
         _ = _ := intervalIntegral.integral_zero
  rw [hu,hz,add_zero,prime_triple_inner_volume (zero_lt_one.trans_le hv)]

/-- Upper ordered triple volume when all three coordinates exceed one. -/
theorem upper_prime_triple_volume {s : ℝ} (hs : 1 ≤ s) :
    primeTripleBoxVolume 1 s s=(1/2:ℝ)*∫ u in 1..s,Real.log u^2 := by
  rw [box_volume_by_slices zero_lt_one hs,←prime_triple_box_volume (zero_lt_one.trans_le hs)]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hs] at hx
  have hx0 := zero_lt_one.trans_le hx.1
  have hv1 := (one_le_div hx0).mpr hx.2
  have hvs := div_le_self (zero_le_one.trans hs) hx.1
  dsimp only
  rw [←upper_volume_column hv1 hvs]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hs] at hy
  have hxy := one_le_mul_of_one_le_of_one_le hx.1 hy.1
  dsimp only
  rw [min_eq_right (div_le_self (zero_le_one.trans hs) hxy),div_div]


private theorem lower_volume_column {s v : ℝ} (hs : 0<s) (hsv : s ≤ v) (hv : v ≤ 1) :
    (∫ y in s..1,(min 1 (v/y)-s)) = (1-s)^2-(1-v+v*Real.log v) := by
  let f := fun y : ℝ => min 1 (v/y)-s
  have hv0 := hs.trans_le hsv
  have hc {l r : ℝ} (hl : 0<l) (hlr : l ≤ r) : ContinuousOn f (uIcc l r) := by
    rw [uIcc_of_le hlr]
    exact (continuousOn_const.inf (continuousOn_const.div continuousOn_id
      (fun _ h => (hl.trans_le h.1).ne'))).sub continuousOn_const
  change (∫ y in s..1,f y)=_
  rw [←intervalIntegral.integral_add_adjacent_intervals (hc hs hsv).intervalIntegrable
    (hc hv0 hv).intervalIntegrable]
  have hleft : (∫ y in s..v,f y)=(v-s)*(1-s) := by
    calc _ = ∫ _ in s..v,(1-s) := by
           apply intervalIntegral.integral_congr
           intro y hy
           rw [uIcc_of_le hsv] at hy
           exact congrArg (· - s) (min_eq_left ((one_le_div (hs.trans_le hy.1)).mpr hy.2))
         _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]
  have hright : (∫ y in v..1,f y)=(1-v)*(1-s)-(1-v+v*Real.log v) := by
    have hf : (∫ y in v..1,f y)=(∫ y in v..1,((1-s)+(v/y-1))) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hv] at hy
      dsimp only [f]
      rw [min_eq_right ((div_le_one (hv0.trans_le hy.1)).mpr hy.1)]
      ring
    have cg : ContinuousOn (fun y : ℝ => v/y-1) (uIcc v 1) := by
      rw [uIcc_of_le hv]
      exact (continuousOn_const.div continuousOn_id (fun _ h => (hv0.trans_le h.1).ne')).sub continuousOn_const
    rw [hf,intervalIntegral.integral_add intervalIntegrable_const cg.intervalIntegrable,
      intervalIntegral.integral_const,smul_eq_mul,
      intervalIntegral.integral_symm (a:=1) (b:=v) (f:=fun y => v/y-1),prime_triple_inner_volume hv0]
    ring
  rw [hleft,hright]
  ring

/-- The lower box retains triples whose product exceeds the lower threshold,
including all endpoints at one. -/
theorem lower_prime_triple_volume {s : ℝ} (hs : 0<s) (hs1 : s ≤ 1) :
    (1-s)^3-primeTripleBoxVolume s 1 s=(1/2:ℝ)*∫ u in s..1,Real.log u^2 := by
  let F := fun x : ℝ => 1-s/x+(s/x)*Real.log (s/x)
  have hc : ContinuousOn F (uIcc s 1) := by
    rw [uIcc_of_le hs1]
    have hq : ContinuousOn (fun x : ℝ => s/x) (Icc s 1) :=
      continuousOn_const.div continuousOn_id fun _ h => (hs.trans_le h.1).ne'
    exact (continuousOn_const.sub hq).add (hq.mul (hq.log fun _ h => (div_pos hs (hs.trans_le h.1)).ne'))
  rw [box_volume_by_slices hs hs1]
  have hinner (x : ℝ) (hx : x ∈ uIcc s 1) :
      (∫ y in s..1,(max s (min 1 (s/(x*y)))-s))=(1-s)^2-F x := by
    rw [uIcc_of_le hs1] at hx
    have hx0 := hs.trans_le hx.1
    have hsv : s ≤ s/x := (le_div_iff₀ hx0).mpr (mul_le_of_le_one_right hs.le hx.2)
    have hv1 := (div_le_one hx0).mpr hx.1
    rw [show F x=1-s/x+(s/x)*Real.log (s/x) from rfl,←lower_volume_column hs hsv hv1]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hs1] at hy
    have hxy := mul_pos hx0 (hs.trans_le hy.1)
    have he := mul_le_one₀ hx.2 (hs.trans_le hy.1).le hy.2
    have hlo := (le_div_iff₀ hxy).mpr (mul_le_of_le_one_right hs.le he)
    dsimp only
    rw [max_eq_right (le_min hs1 hlo),div_div]
  rw [intervalIntegral.integral_congr hinner,
    intervalIntegral.integral_sub intervalIntegrable_const hc.intervalIntegrable,
    intervalIntegral.integral_const,smul_eq_mul]
  have he := prime_triple_box_volume hs
  change (∫ x in 1..s,F x)=_ at he
  rw [intervalIntegral.integral_symm (a:=1) (b:=s) (f:=F),
    intervalIntegral.integral_symm (a:=1) (b:=s) (f:=fun x => Real.log x^2),he]
  ring


private theorem whole_box_volume {a b : ℝ} (ha : 0<a) (hab : a ≤ b) :
    primeTripleBoxVolume a b (b^3)=(b-a)^3 := by
  rw [box_volume_by_slices ha hab]
  have hh {x y : ℝ} (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
      max a (min b (b^3/(x*y)))-a=b-a := by
    rw [uIcc_of_le hab] at hx hy
    have hxy := mul_pos (ha.trans_le hx.1) (ha.trans_le hy.1)
    have hxy' := mul_le_mul hx.2 hy.2 (ha.trans_le hy.1).le (ha.trans_le hab).le
    have hb := mul_le_mul_of_nonneg_left hxy' (ha.trans_le hab).le
    rw [min_eq_left ((le_div_iff₀ hxy).mpr (by linarith only [hb])),max_eq_right hab]
  calc _ = ∫ x in a..b,∫ _ in a..b,(b-a) := by
             apply intervalIntegral.integral_congr
             exact fun x hx => intervalIntegral.integral_congr fun y hy => hh hx hy
       _ = _ := by simp only [intervalIntegral.integral_const,smul_eq_mul]; ring

private theorem volume_difference_constant :
    27*((1-(2/3:ℝ))^3-primeTripleBoxVolume (2/3) 1 (2/3)-primeTripleBoxVolume 1 (4/3) (4/3))=
      lowerTripleSurplusConstant := by
  rw [lower_prime_triple_volume (by norm_num) (by norm_num),upper_prime_triple_volume (by norm_num)]
  let f := fun x : ℝ => Real.log x^2
  have hl := intervalIntegral.integral_comp_sub_left (a:=0) (b:=1/3) f 1
  have hr := intervalIntegral.integral_comp_add_left (a:=0) (b:=1/3) f 1
  norm_num only [sub_zero,add_zero,zero_add,show (1:ℝ)-1/3=2/3 by norm_num,
    show (1:ℝ)+1/3=4/3 by norm_num,show (1/3:ℝ)+1=4/3 by norm_num] at hl hr
  have hleft : ContinuousOn (fun x : ℝ => f (1-x)) (uIcc 0 (1/3)) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/3)]
    apply ContinuousOn.pow
    exact (continuousOn_const.sub continuousOn_id).log fun x hx =>
      ne_of_gt (by linarith only [hx.2] : 0<1-x)
  have hright : ContinuousOn (fun x : ℝ => f (1+x)) (uIcc 0 (1/3)) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/3)]
    apply ContinuousOn.pow
    exact (continuousOn_const.add continuousOn_id).log fun x hx =>
      ne_of_gt (by linarith only [hx.1] : 0<1+x)
  change 27*((1/2)*(∫ u in (2/3:ℝ)..1,f u)-(1/2)*(∫ u in (1:ℝ)..(4/3),f u))=
    (27/2)*(∫ v in (0:ℝ)..(1/3),(f (1-v)-f (1+v)))
  rw [intervalIntegral.integral_sub hleft.intervalIntegrable hright.intervalIntegrable,hl,hr]
  ring

/-- The unpriced lower and upper prime populations have a strictly positive
normalized difference, with the same coefficient as the weighted boxes
after accounting for the average logarithm and the change of scale. -/
theorem prime_triple_count_surplus_tendsto :
    Tendsto (fun y : ℝ => 27*(normalizedPrimeTripleCount (2/3) 1 1 y-
      normalizedPrimeTripleCount (2/3) 1 (2/3) y-normalizedPrimeTripleCount 1 (4/3) (4/3) y))
      atTop (nhds lowerTripleSurplusConstant) := by
  have lo {t : ℝ} := normalized_prime_triple_count_tendsto (a:=2/3) (b:=1)
    (by norm_num) (by norm_num) (by norm_num) t
  have hi := normalized_prime_triple_count_tendsto (a:=1) (b:=4/3) (by norm_num) (by norm_num)
    (by norm_num) (4/3)
  have h := ((lo (t:=1)).sub (lo (t:=2/3)) |>.sub hi).const_mul (27:ℝ)
  have hw := whole_box_volume (a:=(2/3:ℝ)) (b:=1) (by norm_num) (by norm_num)
  rw [one_pow] at hw
  rwa [hw,volume_difference_constant] at h


/-- Ordered prime triples priced by one third of the product logarithm.
The flag deletes pure cubes as required on the smooth side. -/
def primeTripleLogPrice (a b t y : ℝ) (omitCubes : Bool) : ℝ :=
  let P := windowPrimes (a*y) (b*y)
  ∑ p ∈ P,∑ q ∈ P,∑ r ∈ P,
    boxTest a b t ((p:ℝ)/y) ((q:ℝ)/y) ((r:ℝ)/y)*
      (if omitCubes=true ∧ p=q ∧ p=r then 0 else Real.log (p*q*r:ℕ)/3)

private theorem sum_cube_diagonal (P : Finset ℕ) :
    (∑ p ∈ P,∑ q ∈ P,∑ r ∈ P,(if p=q ∧ p=r then (1:ℝ) else 0))=P.card := by
  calc _ = ∑ p ∈ P,(1:ℝ) := by
             apply Finset.sum_congr rfl
             intro p hp
             rw [Finset.sum_eq_single_of_mem p hp]
             · simp [hp]
             · intro q _ hqp
               simp [Ne.symm hqp]
       _ = _ := by simp

private theorem triple_log_error {a b y : ℝ} (ha : 0<a) (hab : a ≤ b) (hy : 1<y)
    (t : ℝ) (omitCubes : Bool) :
    let P := windowPrimes (a*y) (b*y)
    let ρ := Real.log y/y
    |ρ^3/Real.log y*primeTripleLogPrice a b t y omitCubes-normalizedPrimeTripleCount a b t y| ≤ 
      (|Real.log a|+|Real.log b|)/Real.log y*(ρ*P.card)^3+ρ^2*(ρ*P.card) := by
  let P := windowPrimes (a*y) (b*y)
  let L := Real.log y
  let ρ := L/y
  let C := |Real.log a|+|Real.log b|
  let f := fun p q r : ℕ => boxTest a b t ((p:ℝ)/y) ((q:ℝ)/y) ((r:ℝ)/y)
  let W := fun p q r : ℕ => if omitCubes=true ∧ p=q ∧ p=r then 0 else Real.log (p*q*r:ℕ)/3
  have hy0 := zero_lt_one.trans hy
  have hL : 0<L := Real.log_pos hy
  have hρ : 0 ≤ ρ := div_nonneg hL.le hy0.le
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbase {p : ℕ} (hp : p ∈ P) : 0<(p:ℝ) ∧ |Real.log p-L| ≤ C := by
    obtain ⟨hpr,hl,hr⟩ := (mem_windowPrimes (mul_nonneg ha.le hy0.le)
      (mul_nonneg (ha.le.trans hab) hy0.le)).mp hp
    have hp0 := (Nat.cast_pos (α:=ℝ)).mpr hpr.pos
    have h1 := Real.log_le_log (mul_pos ha hy0) hl.le
    have h2 := Real.log_le_log hp0 hr
    rw [Real.log_mul ha.ne' hy0.ne'] at h1
    rw [Real.log_mul (ha.trans_le hab).ne' hy0.ne'] at h2
    refine ⟨hp0,abs_le.mpr ⟨?_,?_⟩⟩ <;> dsimp only [L,C] <;>
      linarith only [h1,h2,neg_abs_le (Real.log a),le_abs_self (Real.log b),
        abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
  have hterm {p q r : ℕ} (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P) :
      |f p q r*W p q r/L-f p q r| ≤ C/L+(if p=q ∧ p=r then 1 else 0) := by
    have hb := box_test_bound a b t ((p:ℝ)/y) ((q:ℝ)/y) ((r:ℝ)/y)
    change |f p q r| ≤ 1 at hb
    have hCL := div_nonneg hC hL.le
    by_cases h : omitCubes=true ∧ p=q ∧ p=r
    · rw [show W p q r=0 from if_pos h,mul_zero,zero_div,zero_sub,abs_neg,if_pos h.2]
      linarith only [hb,hCL]
    · have hlog : Real.log (p*q*r:ℕ)=Real.log p+Real.log q+Real.log r := by
        simp only [Nat.cast_mul,Real.log_mul (mul_ne_zero (hbase hp).1.ne' (hbase hq).1.ne')
          (hbase hr).1.ne',Real.log_mul (hbase hp).1.ne' (hbase hq).1.ne']
      have hw : |W p q r-L| ≤ C := by
        rw [show W p q r=Real.log (p*q*r:ℕ)/3 from if_neg h,hlog,abs_le]
        have pp := abs_le.mp (hbase hp).2
        have qq := abs_le.mp (hbase hq).2
        have rr := abs_le.mp (hbase hr).2
        constructor <;> linarith only [pp.1,pp.2,qq.1,qq.2,rr.1,rr.2]
      rw [show f p q r*W p q r/L-f p q r=f p q r*(W p q r-L)/L by field_simp,
        abs_div,abs_mul,abs_of_pos hL]
      apply (div_le_div_of_nonneg_right ((mul_le_mul hb hw (abs_nonneg _) zero_le_one).trans_eq
        (one_mul C)) hL.le).trans
      exact le_add_of_nonneg_right (by split <;> norm_num)
  have hsum := Finset.sum_le_sum (s:=P) (fun p hp =>
    Finset.sum_le_sum (s:=P) (fun q hq => Finset.sum_le_sum (s:=P) (fun r hr => hterm hp hq hr)))
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,sum_cube_diagonal] at hsum
  have hnorm :
      |∑ p ∈ P,∑ q ∈ P,∑ r ∈ P,(f p q r*W p q r/L-f p q r)| ≤ 
        ∑ p ∈ P,∑ q ∈ P,∑ r ∈ P,|f p q r*W p q r/L-f p q r| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => Finset.abs_sum_le_sum_abs _ _))
  have heq : ρ^3/L*primeTripleLogPrice a b t y omitCubes-normalizedPrimeTripleCount a b t y=
      ρ^3*(∑ p ∈ P,∑ q ∈ P,∑ r ∈ P,(f p q r*W p q r/L-f p q r)) := by
    simp only [primeTripleLogPrice,normalizedPrimeTripleCount,Finset.sum_sub_distrib,
      ←Finset.sum_div, f,W,P,L,ρ]
    ring
  change |ρ^3/L*primeTripleLogPrice a b t y omitCubes-normalizedPrimeTripleCount a b t y| ≤ _
  rw [heq,abs_mul,abs_of_nonneg (pow_nonneg hρ 3)]
  apply (mul_le_mul_of_nonneg_left (hnorm.trans hsum) (pow_nonneg hρ 3)).trans_eq
  change ρ^3*_ = C/L*(ρ*P.card)^3+ρ^2*(ρ*P.card)
  ring

private theorem eventually_box_prime_mass_le {a b : ℝ} (ha : 1/2 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    ∀ᶠ y : ℝ in atTop, (Real.log y/y)*(windowPrimes (a*y) (b*y)).card ≤ 3 := by
  obtain ⟨K,hK,h⟩ := triple_box_prime_window_discrepancy
  filter_upwards [h,eventually_ge_atTop 2,Real.tendsto_log_atTop.eventually_ge_atTop K]
    with y hy hy2 hL
  have hy0 : 0<y := by linarith only [hy2]
  have hlog := Real.log_pos (by linarith only [hy2] : 1<y)
  have hh := (abs_le.mp (hy (a*y) (b*y)
    (by linarith only [mul_le_mul_of_nonneg_right ha hy0.le])
    (mul_le_mul_of_nonneg_right hab hy0.le) (mul_le_mul_of_nonneg_right hb hy0.le))).2
  have hcoef : K*y/Real.log y ≤ y := (div_le_iff₀ hlog).mpr (by
    linarith only [mul_le_mul_of_nonneg_right hL hy0.le])
  have hs := mul_le_mul_of_nonneg_right (by linarith only [ha,hb] : b-a ≤ 2) hy0.le
  rw [div_mul_eq_mul_div,div_le_iff₀ hy0]
  linarith only [hh,hcoef,hs]

/-- The ordinary product logarithm and deletion of pure cubes preserve the
leading volume for every fixed positive cube inside the prime window. -/
theorem priced_prime_triple_box_tendsto {a b : ℝ} (ha : 1/2 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (t : ℝ) (omitCubes : Bool) :
    Tendsto (fun y : ℝ => (Real.log y/y)^3/Real.log y*primeTripleLogPrice a b t y omitCubes)
      atTop (nhds (primeTripleBoxVolume a b t)) := by
  let C := |Real.log a|+|Real.log b|
  have hρ : Tendsto (fun y : ℝ => Real.log y/y) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
  have hL : Tendsto (fun y : ℝ => C/Real.log y) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hbound : Tendsto (fun y : ℝ => (C/Real.log y)*27+(Real.log y/y)^2*3) atTop (nhds 0) := by
    simpa only [zero_mul,zero_pow (by decide : (2:ℕ)≠0),add_zero] using
      ((hL.mul_const 27).add ((hρ.pow 2).mul_const 3))
  have hcount := normalized_prime_triple_count_tendsto ha hab hb t
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_box_prime_mass_le ha hab hb,eventually_gt_atTop 1,
    Metric.tendsto_nhds.mp hcount (ε/2) (half_pos hε),
    Metric.tendsto_nhds.mp hbound (ε/2) (half_pos hε)] with y hmass hy hc he
  let ρ := Real.log y/y
  let M := ρ*(windowPrimes (a*y) (b*y)).card
  have hρ0 : 0 ≤ ρ := div_nonneg (Real.log_nonneg hy.le) (zero_le_one.trans hy.le)
  have hM : 0 ≤ M := mul_nonneg hρ0 (Nat.cast_nonneg _)
  have herr := triple_log_error ((by norm_num : (0:ℝ)<1/2).trans_le ha) hab hy t omitCubes
  have h3 : M^3 ≤ 27 := (pow_le_pow_left₀ hM hmass 3).trans_eq (by norm_num)
  have hbnd := add_le_add (mul_le_mul_of_nonneg_left h3 (div_nonneg (add_nonneg
    (abs_nonneg (Real.log a)) (abs_nonneg (Real.log b))) (Real.log_nonneg hy.le)))
    (mul_le_mul_of_nonneg_left hmass (sq_nonneg ρ))
  have hd := dist_triangle ((Real.log y/y)^3/Real.log y*primeTripleLogPrice a b t y omitCubes)
    (normalizedPrimeTripleCount a b t y) (primeTripleBoxVolume a b t)
  simp only [Real.dist_eq] at hc hd ⊢
  simp only [Real.dist_eq,sub_zero] at he
  have he' := (le_abs_self _).trans_lt he
  change _ ≤ C/Real.log y*M^3+ρ^2*M at herr
  linarith only [hd,hc,herr,hbnd,he']

/-- The lower side excludes pure cubes and the upper side retains them.
Both count ordered ordinary prime triples at their full product price. -/
def sharpPrimeTripleSurplus (y : ℝ) : ℝ :=
  primeTripleLogPrice (2/3) 1 1 y true-primeTripleLogPrice (2/3) 1 (2/3) y true-
    primeTripleLogPrice 1 (4/3) (4/3) y false

/-- The signed excess of actual weighted triples has a positive leading
coefficient at all real cube-root scales. -/
theorem sharp_prime_triple_surplus_tendsto :
    Tendsto (fun y : ℝ => 27*(Real.log y/y)^3/Real.log y*sharpPrimeTripleSurplus y)
      atTop (nhds lowerTripleSurplusConstant) := by
  have hl (t : ℝ) := priced_prime_triple_box_tendsto (a:=2/3) (b:=1)
    (by norm_num) (by norm_num) (by norm_num) t true
  have hr := priced_prime_triple_box_tendsto (a:=1) (b:=4/3) (by norm_num)
    (by norm_num) (by norm_num) (4/3) false
  have h := (((hl 1).sub (hl (2/3))).sub hr).const_mul (27:ℝ)
  have hw := whole_box_volume (a:=2/3) (b:=1) (by norm_num) (by norm_num)
  rw [one_pow] at hw
  rw [hw,volume_difference_constant] at h
  exact h.congr fun y => by dsimp [sharpPrimeTripleSurplus]; ring

/-- At integer midpoints the cube-root scale gives the lower-minus-upper
price asymptotic K n / log²(3n). -/
theorem integer_prime_triple_surplus_tendsto :
    Tendsto (fun n : ℕ => Real.log (3*(n:ℝ))^2/(n:ℝ)*
      sharpPrimeTripleSurplus ((3*(n:ℝ))^(1/3:ℝ))) atTop (nhds lowerTripleSurplusConstant) := by
  have hx : Tendsto (fun n : ℕ => 3*(n:ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hy := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp hx
  apply (sharp_prime_triple_surplus_tendsto.comp hy).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  let x := 3*(n:ℝ)
  let y := x^(1/3:ℝ)
  have hx1 : 1<x := by dsimp only [x]; linarith only [hn1]
  have hx0 := zero_lt_one.trans hx1
  have hy0 : 0<y := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log y=(1/3:ℝ)*Real.log x := Real.log_rpow hx0 _
  have hpow : y^3=x := by
    dsimp only [y]
    rw [←Real.rpow_natCast,←Real.rpow_mul hx0.le]
    norm_num
  change 27*(Real.log y/y)^3/Real.log y*sharpPrimeTripleSurplus y=
    Real.log x^2/(n:ℝ)*sharpPrimeTripleSurplus y
  rw [div_pow,hpow,hlog]
  dsimp only [x]
  have hn0 := (zero_lt_one.trans_le hn1).ne'
  have hlog0 := (Real.log_pos hx1).ne'
  dsimp only [x] at hlog0
  field_simp [hn0,hlog0]
  ring


/-- The excess of lower prime triples eventually exceeds each fixed
multiple of each power strictly below one. -/
theorem prime_triple_surplus_exceeds_power {t : ℝ} (ht : t < 1) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A*(n:ℝ)^t < sharpPrimeTripleSurplus ((3*(n:ℝ))^(1/3:ℝ)) := by
  have hx : Tendsto (fun n : ℕ => 3*(n:ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hlog := ((isLittleO_log_rpow_rpow_atTop 2 (sub_pos.mpr ht)).tendsto_div_nhds_zero.comp hx).const_mul
    (A*(3:ℝ)^(1-t))
  simp only [mul_zero] at hlog
  filter_upwards [hlog.eventually_lt integer_prime_triple_surplus_tendsto lower_triple_surplus_constant_pos,
    eventually_ge_atTop 1] with n h hn
  have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hscale : A*(3:ℝ)^(1-t)*(Real.log (3*(n:ℝ))^(2:ℝ)/(3*(n:ℝ))^(1-t)) =
      Real.log (3*(n:ℝ))^2/(n:ℝ)*(A*(n:ℝ)^t) := by
    rw [Real.rpow_two,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hn0.le,
      Real.rpow_sub hn0,Real.rpow_one]
    field_simp [(Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<3) (1-t)).ne',
      (Real.rpow_pos_of_pos hn0 t).ne']
  change A*(3:ℝ)^(1-t)*(Real.log (3*(n:ℝ))^(2:ℝ)/(3*(n:ℝ))^(1-t)) < _ at h
  rw [hscale] at h
  by_contra! hle
  exact h.not_ge (mul_le_mul_of_nonneg_left hle (div_nonneg (sq_nonneg _) hn0.le))


section ProductFibers
open Finset ArithmeticFunction

private def boxProductFiber (P : Finset ℕ) (k : ℕ) (omitCubes : Bool) : Finset (ℕ × ℕ × ℕ) :=
  (P ×ˢ P ×ˢ P).filter fun x => x.1*x.2.1*x.2.2=k ∧ ¬(omitCubes=true ∧ x.1=x.2.1 ∧ x.1=x.2.2)

private theorem box_fiber_sum (I P : Finset ℕ) (omitCubes : Bool) :
    (∑ k ∈ I,((boxProductFiber P k omitCubes).card:ℝ)*(Real.log k/3)) =
      ∑ p ∈ P,∑ q ∈ P,∑ r ∈ P,if p*q*r ∈ I then
        (if omitCubes=true ∧ p=q ∧ p=r then 0 else Real.log (p*q*r:ℕ)/3) else 0 := by
  classical
  let S := P ×ˢ P ×ˢ P
  let F (x : ℕ × ℕ × ℕ) := x.1*x.2.1*x.2.2
  let C (x : ℕ × ℕ × ℕ) := omitCubes=true ∧ x.1=x.2.1 ∧ x.1=x.2.2
  have h (k : ℕ) : ((boxProductFiber P k omitCubes).card:ℝ)*(Real.log k/3)=
      ∑ x ∈ S,if F x=k then (if C x then 0 else Real.log k/3) else 0 := by
    rw [←nsmul_eq_mul,←sum_const]
    unfold boxProductFiber
    rw [sum_filter]
    apply sum_congr rfl
    intro x _
    change (if F x=k ∧ ¬C x then Real.log k/3 else 0) =
      (if F x=k then (if C x then 0 else Real.log k/3) else 0)
    by_cases he : F x=k <;> by_cases hc : C x <;> simp [he,hc]
  rw [sum_congr rfl (fun k _ => h k),sum_comm]
  have point (x : ℕ × ℕ × ℕ) :
      (∑ k ∈ I,if F x=k then (if C x then 0 else Real.log k/3) else 0)=
        if F x ∈ I then (if C x then 0 else Real.log (F x)/3) else 0 := by
    classical
    rw [sum_ite_eq]
  rw [sum_congr rfl (fun x _ => point x)]
  simp only [S,sum_product,F,C]

private theorem lower_triple_ordering_weight {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) :
    twiceSmoothTripleWeight (p*q*r)/2 =
      if p=q ∧ q=r then 0 else ((primeTripleOrderings p q r).card:ℝ)/3 := by
  rw [prime_triple_ordering_counts]
  rcases eq_or_ne p q with rfl | hpq
  · rcases eq_or_ne p r with rfl | hpr
    · rw [show p*p*p=p^3 by ring,smooth_triple_cube hp]
      norm_num
    · rw [←pow_two,smooth_triple_repeated hp hr hpr]
      simp [hpr]
  rcases eq_or_ne p r with rfl | hpr
  · rw [show p*q*p=p^2*q by ring,smooth_triple_repeated hp hq hpq]
    simp [hpq]
  rcases eq_or_ne q r with rfl | hqr
  · rw [show p*q*q=q^2*p by ring,smooth_triple_repeated hq hp hpq.symm]
    simp [hpq]
  rw [smooth_triple_distinct hp hq hr hpq hpr hqr]
  norm_num [hpq,hpr,hqr]

private def orderedCubeIndex (k : ℕ) :=
  k.divisorsAntidiagonal.sigma (fun x => x.1.divisorsAntidiagonal)

private def orderedCubeTriple (z : Sigma (fun _ : ℕ × ℕ => ℕ × ℕ)) : ℕ × ℕ × ℕ :=
  (z.2.1,z.2.2,z.1.2)

private theorem upper_fiber_count (Y k : ℕ) (hk : 0<k) (P : Finset ℕ)
    (hP : ∀ p q r : ℕ, p*q*r=k →
      (((p.Prime ∧ Y<p) ∧ (q.Prime ∧ Y<q) ∧ (r.Prime ∧ Y<r)) ↔
        p∈P ∧ q∈P ∧ r∈P)) :
    (cubicPrimeIndicator Y^3 : ArithmeticFunction ℝ) k=(boxProductFiber P k false).card := by
  classical
  let A (p : ℕ) := p.Prime ∧ Y<p
  let S := (orderedCubeIndex k).filter (fun z => A z.2.1 ∧ A z.2.2 ∧ A z.1.2)
  have hcard : S.card=(boxProductFiber P k false).card := by
    apply card_bij' (fun z _ => orderedCubeTriple z) (fun x _ => ⟨(x.1*x.2.1,x.2.2),(x.1,x.2.1)⟩)
    · intro z hz
      obtain ⟨hm,ha⟩ := mem_filter.mp hz
      obtain ⟨ho,hi⟩ := mem_sigma.mp hm
      have he := (Nat.mem_divisorsAntidiagonal.mp hi).1
      have hp : z.2.1*z.2.2*z.1.2=k := by rw [he,(Nat.mem_divisorsAntidiagonal.mp ho).1]
      obtain ⟨h1,h2,h3⟩ := (hP _ _ _ hp).mp ha
      exact mem_filter.mpr ⟨mem_product.mpr ⟨h1,mem_product.mpr ⟨h2,h3⟩⟩,hp,by simp⟩
    · rintro ⟨p,q,r⟩ hx
      obtain ⟨hm,hp,_⟩ := mem_filter.mp hx
      obtain ⟨h1,h23⟩ := mem_product.mp hm
      obtain ⟨h2,h3⟩ := mem_product.mp h23
      have ha := (hP p q r hp).mpr ⟨h1,h2,h3⟩
      exact mem_filter.mpr ⟨mem_sigma.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hp,hk.ne'⟩,
        Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,(Nat.mul_pos ha.1.1.pos ha.2.1.1.pos).ne'⟩⟩,ha⟩
    · rintro ⟨⟨u,r⟩,p,q⟩ hz
      have he := (Nat.mem_divisorsAntidiagonal.mp (mem_sigma.mp (mem_filter.mp hz).1).2).1
      change p*q=u at he
      subst u
      rfl
    · intro _ _; rfl
  rw [←hcard,show cubicPrimeIndicator Y^3=cubicPrimeIndicator Y*cubicPrimeIndicator Y*cubicPrimeIndicator Y by ring,
    mul_apply]
  change _=(S.card:ℝ)
  have hsum : (S.card:ℝ)=∑ z ∈ orderedCubeIndex k,if A z.2.1 ∧ A z.2.2 ∧ A z.1.2 then 1 else 0 := by
    calc
      (S.card:ℝ) = ∑ _z ∈ S, (1:ℝ) := by simp
      _ = _ := by dsimp only [S]; rw [Finset.sum_filter]
  rw [hsum,orderedCubeIndex,sum_sigma]
  apply sum_congr rfl
  intro x _
  rw [mul_apply,sum_mul]
  apply sum_congr rfl
  intro z _
  by_cases hp : z.1.Prime ∧ Y<z.1 <;> by_cases hq : z.2.Prime ∧ Y<z.2 <;>
    by_cases hr : x.2.Prime ∧ Y<x.2 <;> simp [cubic_prime_indicator_apply,A,hp,hq,hr]

private theorem prime_box_as_product_sum {a b y : ℝ} (ha : 0≤a) (hb : 0≤b) (hy : 0<y)
    (t : ℝ) (omitCubes : Bool) :
    primeTripleLogPrice a b t y omitCubes =
      let P := windowPrimes (a*y) (b*y)
      ∑ p ∈ P,∑ q ∈ P,∑ r ∈ P,if ((p*q*r:ℕ):ℝ) ≤ t*y^3 then
        (if omitCubes=true ∧ p=q ∧ p=r then 0 else Real.log (p*q*r:ℕ)/3) else 0 := by
  let P := windowPrimes (a*y) (b*y)
  have hmem {p : ℕ} (hp : p∈P) : (p:ℝ)/y ∈ Set.Ioc a b := by
    obtain ⟨_,hl,hu⟩ := (mem_windowPrimes (mul_nonneg ha hy.le) (mul_nonneg hb hy.le)).mp hp
    exact ⟨(lt_div_iff₀ hy).mpr hl,(div_le_iff₀ hy).mpr hu⟩
  unfold primeTripleLogPrice
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro r hr
  have e : (p:ℝ)/y*((q:ℝ)/y)*((r:ℝ)/y)=((p*q*r:ℕ):ℝ)/y^3 := by
    push_cast
    rw [div_mul_div_comm,div_mul_div_comm,pow_three,mul_assoc y y y]
  simp only [boxTest,hmem hp,hmem hq,hmem hr,true_and,e,div_le_iff₀ (pow_pos hy 3)]
  split_ifs <;> simp

private theorem lower_coordinate {p q r y : ℝ} (hy : 0<y) (hp : 0≤p) (hr : 0≤r)
    (hqy : q≤y) (hry : r≤y) (hprod : (2/3)*y^3<p*q*r) : (2/3)*y<p := by
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hqy hp) hry hr (mul_nonneg hp hy.le)
  have bound : ((2/3)*y)*y^2 < p*y^2 := by linarith only [hprod,hm]
  exact lt_of_mul_lt_mul_right bound (sq_nonneg y)

private theorem upper_coordinate {p q r y : ℝ} (hy : 0<y) (hp : 0≤p)
    (hq : y<q) (hr : y<r) (hprod : p*q*r≤(4/3)*y^3) : p≤(4/3)*y := by
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hq.le hp) hr.le hy.le
    (mul_nonneg hp (hy.trans hq).le)
  have bound : p*y^2 ≤ ((4/3)*y)*y^2 := by linarith only [hm,hprod]
  exact le_of_mul_le_mul_right bound (sq_pos_of_pos hy)

private theorem lower_fiber_coefficient {n k : ℕ} (hY : 3 ≤ cubicMidpointCut n)
    (hk : k∈Finset.Ioc (2*n) (3*n)) (y : ℝ) (hy : 0<y)
    (hy3 : y^3=3*(n:ℝ)) (hf : cubicMidpointCut n=⌊y⌋₊) :
    (if k∈Nat.smoothNumbers (cubicMidpointCut n+1) ∧ k.primeFactorsList.length<4 then
      twiceHighDivisorWeight (cubicMidpointCut n) (4*n/(cubicMidpointCut n+1)) k/2 else 0) =
        ((boxProductFiber (windowPrimes ((2/3)*y) (1*y)) k true).card:ℝ)/3 := by
  classical
  let Y := cubicMidpointCut n
  let P := windowPrimes ((2/3)*y) (1*y)
  let F := boxProductFiber P k true
  obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hk
  have hmem {p : ℕ} : p∈P ↔ p.Prime ∧ (2/3)*y<p ∧ (p:ℝ)≤y := by
    simpa only [P,one_mul] using (mem_windowPrimes (p:=p) (x:=(2/3)*y) (y:=1*y) (by positivity) (by positivity))
  have cut {p : ℕ} : p≤Y ↔ (p:ℝ)≤y := by rw [show Y=⌊y⌋₊ from hf,Nat.le_floor_iff hy.le]
  have hgt : (2/3)*y^3<(k:ℝ) := by rw [hy3]; exact_mod_cast (by linarith only [show 2*(n:ℝ)<k by exact_mod_cast hl] : (2/3:ℝ)*(3*n)<k)
  have members {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
      (h1 : p≤Y) (h2 : q≤Y) (h3 : r≤Y) (e : p*q*r=k) : p∈P ∧ q∈P ∧ r∈P := by
    have hg := hgt
    rw [←e,Nat.cast_mul,Nat.cast_mul] at hg
    have h (a b c : ℕ) (ha : a.Prime) (haY : a≤Y) (hbY : b≤Y) (hcY : c≤Y)
        (hs : (2/3)*y^3<(a:ℝ)*b*c) : a∈P :=
      hmem.mpr ⟨ha,lower_coordinate hy (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (cut.mp hbY) (cut.mp hcY) hs,cut.mp haY⟩
    exact ⟨h p q r hp h1 h2 h3 hg,h q p r hq h2 h1 h3 (by linarith only [hg]),
      h r p q hr h3 h1 h2 (by linarith only [hg])⟩
  by_cases hex : ∃ p q r : ℕ,p.Prime ∧ q.Prime ∧ r.Prime ∧ p≤Y ∧ q≤Y ∧ r≤Y ∧ k=p*q*r
  · obtain ⟨p,q,r,hp,hq,hr,h1,h2,h3,rfl⟩ := hex
    have ⟨hpm,hqm,hrm⟩ := members hp hq hr h1 h2 h3 rfl
    have smooth {a : ℕ} (ha : a.Prime) (h : a≤Y) : a∈Nat.smoothNumbers (Y+1) :=
      Nat.mem_smoothNumbers'.mpr fun b hb hd => (Nat.prime_dvd_prime_iff_eq hb ha).mp hd ▸ Nat.lt_succ_of_le h
    have hs := Nat.mul_mem_smoothNumbers (Nat.mul_mem_smoothNumbers (smooth hp h1) (smooth hq h2)) (smooth hr h3)
    have hlen : (p*q*r).primeFactorsList.length<4 := by
      rw [(Nat.perm_primeFactorsList_mul (Nat.mul_ne_zero hp.ne_zero hq.ne_zero) hr.ne_zero).length_eq,
        List.length_append,(Nat.perm_primeFactorsList_mul hp.ne_zero hq.ne_zero).length_eq,
        List.length_append,Nat.primeFactorsList_prime hp,Nat.primeFactorsList_prime hq,Nat.primeFactorsList_prime hr]
      norm_num
    rw [if_pos ⟨hs,hlen⟩,(high_divisor_weight_on_smooth_triple hp hq hr hY h1 h2 h3 hl).2,
      lower_triple_ordering_weight hp hq hr]
    have hperm (a b c : ℕ) (ha : a∈P) (hb : b∈P) (hc : c∈P) (e : a*b*c=p*q*r) :
        (a,b,c)∈primeTripleOrderings p q r :=
      (mem_prime_triple_orderings hp hq hr).mpr ⟨(hmem.mp ha).1,(hmem.mp hb).1,(hmem.mp hc).1,e⟩
    have eqs : boxProductFiber P (p*q*r) true =
        (primeTripleOrderings p q r).filter (fun x => ¬(x.1=x.2.1 ∧ x.1=x.2.2)) := by
      ext ⟨a,b,c⟩
      simp only [boxProductFiber,mem_filter,mem_product,true_and]
      constructor
      · rintro ⟨⟨ha,hb,hc⟩,he,hn⟩
        exact ⟨hperm _ _ _ ha hb hc he,hn⟩
      · rintro ⟨ho,hn⟩
        have he := ((mem_prime_triple_orderings hp hq hr).mp ho).2.2.2
        simp only [primeTripleOrderings,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at ho
        rcases ho with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|
          ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> exact ⟨⟨by assumption,by assumption,by assumption⟩,he,hn⟩
    change _=((boxProductFiber P (p*q*r) true).card:ℝ)/3
    rw [eqs]
    by_cases same : p=q ∧ q=r
    · obtain ⟨rfl,rfl⟩ := same
      have empty : (primeTripleOrderings p p p).filter (fun x => ¬(x.1=x.2.1 ∧ x.1=x.2.2)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨ho,hd⟩ := Finset.mem_filter.mp hx
        have he : x=(p,p,p) := by simpa [primeTripleOrderings] using ho
        subst x
        exact hd ⟨rfl,rfl⟩
      rw [empty]
      simp
    · rw [if_neg same]
      have all : ∀ x ∈ primeTripleOrderings p q r,¬(x.1=x.2.1 ∧ x.1=x.2.2) := by
        rintro ⟨a,b,c⟩ ho hd
        change a=b ∧ a=c at hd
        obtain ⟨rfl,rfl⟩ := hd
        simp only [primeTripleOrderings,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at ho
        rcases ho with h|h|h|h|h|h <;> obtain ⟨h₁,h₂,h₃⟩ := h <;> exact same ⟨by omega,by omega⟩
      rw [filter_eq_self.mpr all]
  · have empty : F=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨p,q,r⟩ h
      obtain ⟨hm,he,_⟩ := mem_filter.mp h
      obtain ⟨hpm,hqr⟩ := mem_product.mp hm
      obtain ⟨hqm,hrm⟩ := mem_product.mp hqr
      obtain ⟨hp,_,h1⟩ := hmem.mp hpm
      obtain ⟨hq,_,h2⟩ := hmem.mp hqm
      obtain ⟨hr,_,h3⟩ := hmem.mp hrm
      exact hex ⟨p,q,r,hp,hq,hr,cut.mpr h1,cut.mpr h2,cut.mpr h3,he.symm⟩
    change _=(F.card:ℝ)/3
    rw [empty,Finset.card_empty,Nat.cast_zero,zero_div]
    split_ifs with h
    · have hw : twiceHighDivisorWeight Y (4*n/(Y+1)) k=0 := by
        by_contra hn
        exact (surviving_long_divisor_products hY hl (hu.trans (by omega)) hn).2.elim hex (not_le.mpr h.2)
      rw [hw,zero_div]
    · rfl

/-- Grouping the sharp prime boxes by their integer product gives exactly
the lower long-divisor triple price and the upper rough convolution cube. -/
theorem cubic_triple_prices_eq_sharp_boxes {n : ℕ} (hY : 3 ≤ cubicMidpointCut n) :
    lowerCubicTriplePrice n-upperCubicTriplePrice n=sharpPrimeTripleSurplus ((3*(n:ℝ))^(1/3:ℝ)) := by
  classical
  let y := (3*(n:ℝ))^(1/3:ℝ)
  let Y := cubicMidpointCut n
  have hn : 0<n := by
    by_contra! hn
    have he : n=0 := by omega
    subst n
    norm_num [cubicMidpointCut,Real.zero_rpow] at hY
  have hy : 0<y := Real.rpow_pos_of_pos (by positivity) _
  have hy3 : y^3=3*(n:ℝ) := by
    dsimp only [y]
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    norm_num
  let P := windowPrimes ((2/3)*y) (1*y)
  let Q := windowPrimes (1*y) ((4/3)*y)
  have h3 : 1*y^3=((3*n:ℕ):ℝ) := by rw [one_mul,hy3,Nat.cast_mul,Nat.cast_ofNat]
  have h2 : (2/3)*y^3=((2*n:ℕ):ℝ) := by rw [hy3,Nat.cast_mul,Nat.cast_ofNat]; ring
  have h4 : (4/3)*y^3=((4*n:ℕ):ℝ) := by rw [hy3,Nat.cast_mul,Nat.cast_ofNat]; ring
  have lower : lowerCubicTriplePrice n=primeTripleLogPrice (2/3) 1 1 y true-
      primeTripleLogPrice (2/3) 1 (2/3) y true := by
    rw [lowerCubicTriplePrice,sum_filter]
    trans ∑ k ∈ Finset.Ioc (2*n) (3*n),((boxProductFiber P k true).card:ℝ)*(Real.log k/3)
    · apply sum_congr rfl
      intro k hk
      have hh := lower_fiber_coefficient hY hk y hy hy3 rfl
      change (if k∈Nat.smoothNumbers (Y+1) ∧ k.primeFactorsList.length<4 then
        twiceHighDivisorWeight Y (4*n/(Y+1)) k/2*Real.log k else 0)=_
      by_cases hs : k∈Nat.smoothNumbers (Y+1) ∧ k.primeFactorsList.length<4
      · rw [if_pos hs] at hh ⊢
        rw [hh]; ring
      · rw [if_neg hs] at hh ⊢
        rw [show ((boxProductFiber P k true).card:ℝ)=0 by linarith only [hh],zero_mul]
    rw [box_fiber_sum,prime_box_as_product_sum (by norm_num) (by norm_num) hy,
      prime_box_as_product_sum (by norm_num) (by norm_num) hy,h3,h2]
    simp only [Nat.cast_le,←sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    apply sum_congr rfl
    intro q _
    apply sum_congr rfl
    intro r _
    simp only [Finset.mem_Ioc]
    split_ifs <;> first | rfl | omega | ring
  have hQ {p : ℕ} : p∈Q ↔ p.Prime ∧ y<p ∧ (p:ℝ)≤(4/3)*y := by
    simpa only [Q,one_mul] using (mem_windowPrimes (p:=p) (x:=1*y) (y:=(4/3)*y) (by positivity) (by positivity))
  have cut {p : ℕ} : Y<p ↔ y<(p:ℝ) := Nat.floor_lt hy.le
  have upmem {k : ℕ} (hk : k≤4*n) (p q r : ℕ) (he : p*q*r=k) :
      ((p.Prime ∧ Y<p) ∧ (q.Prime ∧ Y<q) ∧ (r.Prime ∧ Y<r)) ↔ p∈Q ∧ q∈Q ∧ r∈Q := by
    constructor
    · rintro ⟨⟨hp,hp'⟩,⟨hq,hq'⟩,hr,hr'⟩
      have hbd : (p:ℝ)*q*r≤(4/3)*y^3 := by rw [h4]; exact_mod_cast he.le.trans hk
      have h (a b c : ℕ) (ha : a.Prime) (haY : Y<a) (hbY : Y<b) (hcY : Y<c)
          (hs : (a:ℝ)*b*c≤(4/3)*y^3) : a∈Q :=
        hQ.mpr ⟨ha,cut.mp haY,upper_coordinate hy (Nat.cast_nonneg _) (cut.mp hbY) (cut.mp hcY) hs⟩
      exact ⟨h p q r hp hp' hq' hr' hbd,h q p r hq hq' hp' hr' (by linarith only [hbd]),
        h r p q hr hr' hp' hq' (by linarith only [hbd])⟩
    · rintro ⟨hp,hq,hr⟩
      exact ⟨⟨(hQ.mp hp).1,cut.mpr (hQ.mp hp).2.1⟩,⟨(hQ.mp hq).1,cut.mpr (hQ.mp hq).2.1⟩,
        (hQ.mp hr).1,cut.mpr (hQ.mp hr).2.1⟩
  have upper : upperCubicTriplePrice n=primeTripleLogPrice 1 (4/3) (4/3) y false := by
    unfold upperCubicTriplePrice
    trans ∑ k ∈ Finset.Ioc (3*n) (4*n),((boxProductFiber Q k false).card:ℝ)*(Real.log k/3)
    · apply sum_congr rfl
      intro k hk
      obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp hk
      rw [upper_fiber_count Y k (by omega) Q (upmem hu)]
      ring
    rw [box_fiber_sum,prime_box_as_product_sum (by norm_num) (by norm_num) hy,h4]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro r hr
    have hh := mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_right (hQ.mp hp).2.1 hy) hy
    have hq' := mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_left (hQ.mp hq).2.1 (hy.trans (hQ.mp hp).2.1)) hy
    have hr' := mul_lt_mul_of_pos_left (hQ.mp hr).2.1 (mul_pos (hy.trans (hQ.mp hp).2.1) (hy.trans (hQ.mp hq).2.1))
    have gt : 3*n<p*q*r := by
      have he : ((3*n:ℕ):ℝ)<(p:ℝ)*q*r := by
        rw [←h3,one_mul,pow_three]
        simpa only [mul_assoc] using hh.trans (hq'.trans hr')
      exact_mod_cast he
    simp only [Finset.mem_Ioc,gt,true_and,Nat.cast_le]
  rw [lower,upper,sharpPrimeTripleSurplus]

end ProductFibers

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
