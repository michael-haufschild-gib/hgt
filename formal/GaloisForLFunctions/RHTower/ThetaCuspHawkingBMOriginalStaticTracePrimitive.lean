import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalStaticTraceDensity

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalStaticTracePrimitive
open D4BMJointSource D4BMModularCore D4BMOriginalStaticTraceDensity D4BMOriginalFullMetricCollar
noncomputable section
set_option autoImplicit false

private theorem exponential_admission (f : ℝ→ℂ) (C a : ℝ) (hC : 0≤C)
    (hi : ∀ b : ℝ,a≤b → IntervalIntegrable f volume a b)
    (hb : ∀ p : ℝ,a≤p → ‖f p‖≤C*Real.exp (-p)) : IntegrableOn f (Ioi a) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (C*Real.exp (-a)) a
    (b:=fun b : ℝ => b) (l:=atTop) ?_ tendsto_id ?_
  · intro b
    exact (hi (max a b) (le_max_left _ _)).1.mono_set
      (fun p hp => ⟨hp.1,hp.2.trans (le_max_right _ _)⟩)
  · filter_upwards [eventually_ge_atTop a] with b hab
    have hCint : IntervalIntegrable (fun p : ℝ => C*Real.exp (-p)) volume a b := by
      apply Continuous.intervalIntegrable
      fun_prop
    calc
      _ ≤ ∫ p in a..b,C*Real.exp (-p) :=
        intervalIntegral.integral_mono_on hab (hi b hab).norm hCint (fun p hp => hb p hp.1)
      _ = C*(Real.exp (-a)-Real.exp (-b)) := by
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp]
      _ ≤ _ := by nlinarith [Real.exp_nonneg (-b)]

private theorem exponential_tail_bound (f : ℝ→ℂ) (C a : ℝ)
    (hb : ∀ p : ℝ,a<p → ‖f p‖≤C*Real.exp (-p)) :
    ‖∫ p in Ioi a,f p‖≤C*Real.exp (-a) := by
  have h := norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi a).const_mul C) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact hb p hp)
  rw [integral_const_mul,integral_exp_neg_Ioi] at h
  exact h

/-- Separate half-line admission of the actual complete endpoint and bulk
terms, obtained from their compact admission and their exponential bound. -/
theorem trace_density_halfline_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a k : ℝ,0<a → 0≤k → 4≤Real.exp k →
      IntegrableOn (endpointDensity q br amp w k) (Ioi a) ∧
      IntegrableOn (bulkDensity q br amp w k) (Ioi a) := by
  obtain ⟨G1,hG1,h1⟩ := trace_density_time_integrable q br amp
  obtain ⟨G2,_,h2⟩ := trace_density_decay q br amp 0
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw a k ha hk hk4
  have hi := h1 w hwi (by linarith [le_max_left G1 G2]) a
  obtain ⟨C,hC,hc⟩ := h2 w (by linarith [le_max_right G1 G2])
  have hb (p : ℝ) (hp : a≤p) := hc p k (ha.trans_le hp) hk
  simp only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] at hb
  exact ⟨exponential_admission _ C a hC (fun b hab => (hi b k ha hab hk hk4).1) (fun p hp => (hb p hp).1),
    exponential_admission _ C a hC (fun b hab => (hi b k ha hab hk hk4).2) (fun p hp => (hb p hp).2)⟩

/-- The original infinite-time trace coefficient, retaining its onset endpoint. -/
def traceMass (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k a : ℝ) : ℂ :=
  -endpointDensity q br amp w k a+∫ p in Ioi a,bulkDensity q br amp w k p

/-- The actual terminal transient of the complete horizon trace. -/
def traceTransient (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k p : ℝ) : ℂ :=
  endpointDensity q br amp w k p-∫ t in Ioi p,bulkDensity q br amp w k t

/-- The retained moving temporal corner is the negative tail primitive of
that original transient; no free finite constant enters this definition. -/
def traceCorner (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (k p : ℝ) : ℂ :=
  -(∫ t in Ioi p,traceTransient q br amp w k t)

/-- The exact finite-time horizon trace is its source-derived mass plus its
terminal transient. The same admitted bulk field appears in all three terms. -/
theorem trace_mass_transient_decomposition (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a b k : ℝ,
      0<a → a≤b → 0≤k → 4≤Real.exp k →
      metricTrace q br amp w a b k=traceMass q br amp w k a+traceTransient q br amp w k b := by
  obtain ⟨G1,hG1,h1⟩ := trace_density_decomposition q br amp
  obtain ⟨G2,_,h2⟩ := trace_density_halfline_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw a b k ha hab hk hk4
  rw [h1 w hwi (by linarith [le_max_left G1 G2]) a b k ha hab hk hk4]
  have hi := (h2 w hwi (by linarith [le_max_right G1 G2]) a k ha hk hk4).2
  have he := intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hab))
  unfold traceMass traceTransient
  linear_combination he

/-- Mass and transient both retain arbitrary cusp decay and the original
positive-time exponential envelope. -/
theorem trace_mass_transient_decay (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∃ C : ℝ,0≤C ∧ ∀ p k : ℝ,0<p → 0≤k →
      ‖traceMass q br amp w k p‖≤C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) ∧
      ‖traceTransient q br amp w k p‖≤C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G,hG,hg⟩ := trace_density_decay q br amp N
  refine ⟨G,hG,?_⟩
  intro w hw
  obtain ⟨C,hC,hc⟩ := hg w hw
  refine ⟨2*C,by positivity,?_⟩
  intro p k hp hk
  have hU := (hc p k hp hk).1
  have hV := exponential_tail_bound (bulkDensity q br amp w k) (C*Real.exp (-(N:ℝ)*k)) p
    (fun t ht => (hc t k (hp.trans ht) hk).2)
  constructor
  · exact (norm_add_le _ _).trans ((add_le_add (by simpa only [norm_neg] using hU) hV).trans_eq (by ring))
  · exact (norm_sub_le _ _).trans ((add_le_add hU hV).trans_eq (by ring))

/-- The actual transient is separately integrable on every positive time
half-line; its tail primitive consequently has an admitted physical meaning. -/
theorem trace_transient_halfline_integrable (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a k : ℝ,0<a → 0≤k → 4≤Real.exp k →
      IntegrableOn (traceTransient q br amp w k) (Ioi a) := by
  obtain ⟨G1,hG1,h1⟩ := trace_density_halfline_integrable q br amp
  obtain ⟨G2,_,h2⟩ := trace_mass_transient_decay q br amp 0
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw a k ha hk hk4
  obtain ⟨hU,hV⟩ := h1 w hwi (by linarith [le_max_left G1 G2]) a k ha hk hk4
  obtain ⟨C,hC,hc⟩ := h2 w (by linarith [le_max_right G1 G2])
  apply exponential_admission _ C a hC
  · intro b hab
    have hiU : IntervalIntegrable (endpointDensity q br amp w k) volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hU.mono_set Ioc_subset_Ioi_self)
    have hiV : IntervalIntegrable (fun p => ∫ t in Ioi p,bulkDensity q br amp w k t) volume a b :=
      (hV.continuousOn_Ici_primitive_Ioi.mono (fun p hp => hp.1)).intervalIntegrable_of_Icc hab
    exact hiU.sub hiV
  · intro p hp
    simpa only [Nat.cast_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] using (hc p k (ha.trans_le hp) hk).2

/-- The original moving corner is uniformly cusp-small, including arbitrary
positive positions of the terminal/horizon intersection. -/
theorem trace_corner_decay (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∃ C : ℝ,0≤C ∧ ∀ p k : ℝ,0<p → 0≤k →
      ‖traceCorner q br amp w k p‖≤C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G,hG,hg⟩ := trace_mass_transient_decay q br amp N
  refine ⟨G,hG,?_⟩
  intro w hw
  obtain ⟨C,hC,hc⟩ := hg w hw
  refine ⟨C,hC,?_⟩
  intro p k hp hk
  rw [traceCorner,norm_neg]
  exact exponential_tail_bound _ (C*Real.exp (-(N:ℝ)*k)) p (fun t ht => (hc t k (hp.trans ht) hk).2)

/-- Exact two-endpoint identity for the complete original trace. Its mass and
both moving corners are retained before any cutoff limit is taken. -/
theorem trace_two_endpoint_identity (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ a R S k : ℝ,
      0<a → a≤R → R≤S → 0≤k → 4≤Real.exp k →
      IntervalIntegrable (fun b => metricTrace q br amp w a b k) volume R S ∧
      (∫ b in R..S,metricTrace q br amp w a b k)=
        (S-R)•traceMass q br amp w k a+traceCorner q br amp w k S-traceCorner q br amp w k R := by
  obtain ⟨G1,hG1,h1⟩ := trace_mass_transient_decomposition q br amp
  obtain ⟨G2,_,h2⟩ := trace_transient_halfline_integrable q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw a R S k ha haR hRS hk hk4
  have he (b : ℝ) (hb : a≤b) := h1 w hwi (by linarith [le_max_left G1 G2]) a b k ha hb hk hk4
  have hZ := h2 w hwi (by linarith [le_max_right G1 G2]) R k (ha.trans_le haR) hk hk4
  have hiZ : IntervalIntegrable (traceTransient q br amp w k) volume R S :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hRS).mpr (hZ.mono_set Ioc_subset_Ioi_self)
  have hrep : (∫ b in R..S,metricTrace q br amp w a b k)=
      ∫ b in R..S,traceMass q br amp w k a+traceTransient q br amp w k b := by
    apply intervalIntegral.integral_congr
    intro b hb
    have hb' : b∈Icc R S := by simpa only [uIcc_of_le hRS] using hb
    exact he b (haR.trans hb'.1)
  constructor
  · apply (intervalIntegrable_const.add hiZ).congr
    intro b hb
    have hb' : b∈Ioc R S := by simpa only [uIoc_of_le hRS] using hb
    exact (he b (haR.trans hb'.1.le)).symm
  · rw [hrep,intervalIntegral.integral_add intervalIntegrable_const hiZ,intervalIntegral.integral_const]
    have hc : traceCorner q br amp w k S-traceCorner q br amp w k R=
        ∫ b in R..S,traceTransient q br amp w k b := by
      rw [traceCorner,traceCorner,neg_sub_neg,intervalIntegral.integral_Ioi_sub_Ioi hZ hRS]
    rw [← hc]
    abel

/-- After its derived mass subtraction, every positive time window of the
full original trace is cusp-small uniformly in both endpoints. -/
theorem trace_two_endpoint_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∃ C : ℝ,0≤C ∧ ∀ a R S k : ℝ,
      0<a → a≤R → R≤S → 0≤k → 4≤Real.exp k →
      ‖(∫ b in R..S,metricTrace q br amp w a b k)-(S-R)•traceMass q br amp w k a‖≤C*Real.exp (-(N:ℝ)*k) := by
  obtain ⟨G1,hG1,h1⟩ := trace_two_endpoint_identity q br amp
  obtain ⟨G2,_,h2⟩ := trace_corner_decay q br amp N
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  obtain ⟨C,hC,hc⟩ := h2 w (by linarith [le_max_right G1 G2])
  refine ⟨2*C,by positivity,?_⟩
  intro a R S k ha haR hRS hk hk4
  rw [(h1 w hwi (by linarith [le_max_left G1 G2]) a R S k ha haR hRS hk hk4).2]
  have hcan : (S-R)•traceMass q br amp w k a+traceCorner q br amp w k S-traceCorner q br amp w k R-
      (S-R)•traceMass q br amp w k a=traceCorner q br amp w k S-traceCorner q br amp w k R := by abel
  rw [hcan]
  have hb (p : ℝ) (hp : 0<p) : ‖traceCorner q br amp w k p‖≤C*Real.exp (-(N:ℝ)*k) :=
    (hc p k hp hk).trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (by linarith : -p≤0)) (by positivity)).trans_eq (mul_one _))
  exact (norm_sub_le _ _).trans ((add_le_add (hb S (ha.trans_le (haR.trans hRS))) (hb R (ha.trans_le haR))).trans_eq (by ring))

end
end RHTower.D4BMOriginalStaticTracePrimitive
