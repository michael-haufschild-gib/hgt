import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaReciprocalCutoffSource

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

private theorem pwGammaCutoff_Ioi_translate (f : ℝ → ℂ) (x a : ℝ) :
    (∫ y in Ioi x, f (y+a))=∫ y in Ioi (x+a), f y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun y => (Ioi (x+a)).indicator f y) a]
  congr 1
  funext y
  by_cases h : y∈Ioi x
  · have h' : y+a∈Ioi (x+a) := by simpa only [mem_Ioi, add_lt_add_iff_right] using h
    rw [indicator_of_mem h, indicator_of_mem h']
  · have h' : y+a∉Ioi (x+a) := by simpa only [mem_Ioi, add_lt_add_iff_right] using h
    rw [indicator_of_notMem h, indicator_of_notMem h']

def pwGammaMobiusReciprocalCutoffLoss (z : ℂ) (v h : ℝ) : ℂ :=
  (Real.exp (-h)/h:ℝ)*pwGammaMobiusReciprocalTail z v

private theorem pwGammaCutoff_loss_kernel_bound {v h : ℝ} (hv : 0<v) (hh : v<h) :
    ‖(Real.exp (-h)/h:ℝ)‖≤Real.exp (-h)/v := by
  rw [Real.norm_of_nonneg (div_pos (Real.exp_pos _) (hv.trans hh)).le]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hv hh.le

private theorem pwGammaCutoff_loss_kernel_integrable {v : ℝ} (hv : 0<v) :
    IntegrableOn (fun h : ℝ => Real.exp (-h)/h) (Ioi v) := by
  apply ((integrableOn_exp_neg_Ioi v).div_const v).mono'
    (by exact (show Measurable (fun h : ℝ => Real.exp (-h)/h) by fun_prop).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact pwGammaCutoff_loss_kernel_bound hv hh

theorem pwGammaMobiusReciprocalCutoffLoss_integrable (z : ℂ) {v : ℝ} (hv : 0<v) :
    IntegrableOn (pwGammaMobiusReciprocalCutoffLoss z v) (Ioi v) :=
  (pwGammaCutoff_loss_kernel_integrable hv).ofReal.mul_const _

/-- A reciprocal cutoff bound suffices to absorb the full source loss at every order. -/
theorem pwGammaMobiusReciprocalCutoffLoss_flat_bound (z : ℂ) (m : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ v : ℝ, 0<v → v≤1 →
      ‖∫ h in Ioi v, pwGammaMobiusReciprocalCutoffLoss z v h‖≤C*v^(m+1) := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusReciprocalTail_flat_bound z (m+2)
  refine ⟨C,hC,?_⟩
  intro v hv hv1
  have ht := norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi v).div_const v)
    (show ∀ᵐ h ∂volume.restrict (Ioi v), ‖Real.exp (-h)/h‖≤Real.exp (-h)/v from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      exact pwGammaCutoff_loss_kernel_bound hv hh)
  rw [integral_div, integral_exp_neg_Ioi] at ht
  unfold pwGammaMobiusReciprocalCutoffLoss
  rw [integral_mul_const, integral_complex_ofReal, norm_mul, Complex.norm_real]
  calc
    _ ≤ (Real.exp (-v)/v)*(C*v^(m+2)) :=
      mul_le_mul ht (hb v hv hv1) (norm_nonneg _) (by positivity)
    _ ≤ (1/v)*(C*v^(m+2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith)) hv.le
    _ = C*v^(m+1) := by rw [show m+2=(m+1)+1 by omega, pow_succ]; field_simp

/-- The exact finite resolvent remainder, still restricted away from its moving pole. -/
def pwGammaMobiusReciprocalCutoffRemainder (z : ℂ) (q : ℕ) (v t : ℝ) : ℂ :=
  (Real.exp (-t):ℂ)*pwGammaMobiusReciprocalTail z t*(v:ℂ)^q/
    ((t:ℂ)^q*((t:ℂ)-(v:ℂ)))

theorem pwGammaMobiusReciprocalCutoffRemainder_norm_bound (z : ℂ) (q : ℕ)
    {v t : ℝ} (hv : 0<v) (ht : 2*v<t) :
    ‖pwGammaMobiusReciprocalCutoffRemainder z q v t‖≤
      (2*v^q)*‖pwGammaMobiusReciprocalEndpointIntegrand z q t‖ := by
  have ht0 : 0<t := by linarith
  have htv : 0<t-v := by linarith
  have hr : t/(t-v)≤2 := (div_le_iff₀ htv).mpr (by linarith)
  have he : ‖pwGammaMobiusReciprocalCutoffRemainder z q v t‖ =
      v^q*‖pwGammaMobiusReciprocalEndpointIntegrand z q t‖*(t/(t-v)) := by
    rw [pwGammaMobiusReciprocalEndpointIntegrand_norm z q ht0]
    unfold pwGammaMobiusReciprocalCutoffRemainder
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
      ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg hv.le, Real.norm_of_nonneg ht0.le, Real.norm_of_nonneg htv.le]
    rw [pow_succ]
    field_simp
  rw [he]
  calc
    _ ≤ v^q*‖pwGammaMobiusReciprocalEndpointIntegrand z q t‖*2 :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

theorem pwGammaMobiusReciprocalCutoffRemainder_integrable (z : ℂ) (q : ℕ)
    {v : ℝ} (hv : 0<v) :
    IntegrableOn (pwGammaMobiusReciprocalCutoffRemainder z q v) (Ioi (2*v)) := by
  have hs : Ioi (2*v)⊆Ioi (0:ℝ) := Ioi_subset_Ioi (by positivity)
  apply (((pwGammaMobiusReciprocalEndpointIntegrand_integrable z q).mono_set hs).norm.const_mul
    (2*v^q)).mono'
  · unfold pwGammaMobiusReciprocalCutoffRemainder
    simp only [div_eq_mul_inv]
    exact (((by fun_prop : AEStronglyMeasurable (fun t : ℝ => (Real.exp (-t):ℂ))
      (volume.restrict (Ioi (2*v)))).mul
        ((pwGammaMobiusReciprocalTail_aestronglyMeasurable z).mono_set hs)).mul_const _).mul
          (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact pwGammaMobiusReciprocalCutoffRemainder_norm_bound z q hv ht

/-- Finite expansion, requiring no convergent series or analyticity at the endpoint. -/
theorem pwGammaMobiusReciprocalCutoffRemainder_finite_eq (z : ℂ) (q : ℕ)
    {v t : ℝ} (hv : 0<v) (ht : 2*v<t) :
    pwGammaMobiusReciprocalCutoffRemainder z 0 v t =
      (∑ j∈Finset.range q, (v:ℂ)^j*pwGammaMobiusReciprocalEndpointIntegrand z j t)+
        pwGammaMobiusReciprocalCutoffRemainder z q v t := by
  have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have htv : (t:ℂ)-(v:ℂ)≠0 := by
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih, add_assoc]
    congr 1
    unfold pwGammaMobiusReciprocalCutoffRemainder pwGammaMobiusReciprocalEndpointIntegrand
    simp only [pow_succ]
    field_simp [ht0, htv]
    ring


/-- The finite remainder is dominated by an admitted complete-source norm moment. -/
theorem pwGammaMobiusReciprocalCutoffRemainder_integral_bound (z : ℂ) (q : ℕ)
    {v : ℝ} (hv : 0<v) :
    ‖∫ t in Ioi (2*v), pwGammaMobiusReciprocalCutoffRemainder z q v t‖≤
      (2*v^q)*(∫ t in Ioi (0:ℝ), ‖pwGammaMobiusReciprocalEndpointIntegrand z q t‖) := by
  have hs : Ioi (2*v)⊆Ioi (0:ℝ) := Ioi_subset_Ioi (by positivity)
  have hi : IntegrableOn (fun t => ‖pwGammaMobiusReciprocalEndpointIntegrand z q t‖) (Ioi (0:ℝ)) :=
    (pwGammaMobiusReciprocalEndpointIntegrand_integrable z q).norm
  have ht := norm_integral_le_of_norm_le ((hi.mono_set hs).const_mul (2*v^q))
    (show ∀ᵐ t ∂volume.restrict (Ioi (2*v)),
      ‖pwGammaMobiusReciprocalCutoffRemainder z q v t‖≤
        (2*v^q)*‖pwGammaMobiusReciprocalEndpointIntegrand z q t‖ from by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact pwGammaMobiusReciprocalCutoffRemainder_norm_bound z q hv ht)
  rw [integral_const_mul] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hi (Eventually.of_forall (fun t => norm_nonneg _))
      (Eventually.of_forall hs)) (by positivity))

/-- The original current is split before either gain or loss is taken to the endpoint. -/
theorem pwGammaMobiusReciprocalResponse_cutoff_eq (z : ℂ) {v : ℝ} (hv : 0<v) :
    (Real.exp (-v):ℂ)*(pwGammaMobiusSameSourceCurrent z v/pwGammaRaySource v) =
      (Real.exp (-v):ℂ)*(∫ h in (0:ℝ)..v, pwGammaMobiusReciprocalResponse z v h)+
      (∫ t in Ioi (2*v), pwGammaMobiusReciprocalCutoffRemainder z 0 v t)-
      (Real.exp (-v):ℂ)*(∫ h in Ioi v, pwGammaMobiusReciprocalCutoffLoss z v h) := by
  have hi := pwGammaMobiusReciprocalResponse_integrable z hv
  have hif := hi.mono_set (Ioi_subset_Ioi hv.le)
  have hl := pwGammaMobiusReciprocalCutoffLoss_integrable z hv
  have hg : (∫ h in Ioi v, pwGammaMobiusReciprocalResponse z v h)+
      (∫ h in Ioi v, pwGammaMobiusReciprocalCutoffLoss z v h) =
      (Real.exp v:ℂ)*(∫ t in Ioi (2*v), pwGammaMobiusReciprocalCutoffRemainder z 0 v t) := by
    rw [← integral_add hif hl, ← integral_const_mul]
    have ht := pwGammaCutoff_Ioi_translate
      (fun t => (Real.exp v:ℂ)*pwGammaMobiusReciprocalCutoffRemainder z 0 v t) v v
    rw [show v+v=2*v by ring] at ht
    rw [← ht]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro h hh
    unfold pwGammaMobiusReciprocalResponse pwGammaMobiusReciprocalCutoffLoss
      pwGammaMobiusReciprocalCutoffRemainder
    simp only [pow_zero, one_mul, mul_one]
    have he : Real.exp v*Real.exp (-(h+v))=Real.exp (-h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [Complex.ofReal_div, Complex.ofReal_add, add_sub_cancel_right]
    conv_rhs => rw [← mul_div_assoc, ← mul_assoc, ← Complex.ofReal_mul, he]
    rw [add_comm h v]
    ring
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hif
  rw [pwGammaMobiusReciprocalResponse_integral_eq z hv] at hsplit
  have he : (Real.exp (-v):ℂ)*(Real.exp v:ℂ)=1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  calc
    _ = (Real.exp (-v):ℂ)*((∫ h in (0:ℝ)..v, pwGammaMobiusReciprocalResponse z v h)+
        (∫ h in Ioi v, pwGammaMobiusReciprocalResponse z v h)) := by rw [hsplit]
    _ = _ := by
      have hgg := congrArg (fun w : ℂ => (Real.exp (-v):ℂ)*w) hg
      rw [mul_add, ← mul_assoc, he, one_mul] at hgg
      linear_combination hgg


/-- Every finite resolvent expansion integrates with its actual far cutoff retained. -/
theorem pwGammaMobiusReciprocalCutoffRemainder_integral_finite_eq (z : ℂ) (q : ℕ)
    {v : ℝ} (hv : 0<v) :
    (∫ t in Ioi (2*v), pwGammaMobiusReciprocalCutoffRemainder z 0 v t) =
      (∑ j∈Finset.range q, (v:ℂ)^j*
        (∫ t in Ioi (2*v), pwGammaMobiusReciprocalEndpointIntegrand z j t))+
      (∫ t in Ioi (2*v), pwGammaMobiusReciprocalCutoffRemainder z q v t) := by
  have hs : Ioi (2*v)⊆Ioi (0:ℝ) := Ioi_subset_Ioi (by positivity)
  have hi : ∀ j∈Finset.range q, IntegrableOn
      (fun t => (v:ℂ)^j*pwGammaMobiusReciprocalEndpointIntegrand z j t) (Ioi (2*v)) := by
    intro j _
    exact ((pwGammaMobiusReciprocalEndpointIntegrand_integrable z j).mono_set hs).const_mul _
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => pwGammaMobiusReciprocalCutoffRemainder_finite_eq z q hv ht),
    integral_add (integrable_finsetSum (Finset.range q) hi)
      (pwGammaMobiusReciprocalCutoffRemainder_integrable z q hv),
    integral_finsetSum (Finset.range q) hi]
  simp only [integral_const_mul]

/-- Exact source expansion with all four errors displayed, before any limiting argument. -/
theorem pwGammaMobiusReciprocalResponse_finite_cutoff_eq (z : ℂ) (q : ℕ)
    {v : ℝ} (hv : 0<v) :
    (Real.exp (-v):ℂ)*(pwGammaMobiusSameSourceCurrent z v/pwGammaRaySource v)-
      (∑ j∈Finset.range q, (v:ℂ)^j*pwGammaMobiusReciprocalEndpointMoment z j) =
      (Real.exp (-v):ℂ)*(∫ h in (0:ℝ)..v, pwGammaMobiusReciprocalResponse z v h)-
      (∑ j∈Finset.range q, (v:ℂ)^j*
        (∫ t in (0:ℝ)..(2*v), pwGammaMobiusReciprocalEndpointIntegrand z j t))+
      (∫ t in Ioi (2*v), pwGammaMobiusReciprocalCutoffRemainder z q v t)-
      (Real.exp (-v):ℂ)*(∫ h in Ioi v, pwGammaMobiusReciprocalCutoffLoss z v h) := by
  rw [pwGammaMobiusReciprocalResponse_cutoff_eq z hv,
    pwGammaMobiusReciprocalCutoffRemainder_integral_finite_eq z q hv]
  have hj : ∀ j : ℕ, (∫ t in Ioi (2*v), pwGammaMobiusReciprocalEndpointIntegrand z j t) =
      pwGammaMobiusReciprocalEndpointMoment z j-
        (∫ t in (0:ℝ)..(2*v), pwGammaMobiusReciprocalEndpointIntegrand z j t) := by
    intro j
    have ht := intervalIntegral.integral_Ioi_sub_Ioi
      (pwGammaMobiusReciprocalEndpointIntegrand_integrable z j) (by positivity : (0:ℝ)≤2*v)
    change pwGammaMobiusReciprocalEndpointMoment z j-_=_ at ht
    linear_combination -ht
  simp_rw [hj, mul_sub, Finset.sum_sub_distrib]
  ring


/-- Each requested finite expansion has an original-current remainder of the stated power. -/
theorem pwGammaMobiusReciprocalResponse_finite_asymptotic_bound (z : ℂ) (q : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ v : ℝ, 0<v → v≤1/2 →
      ‖(Real.exp (-v):ℂ)*(pwGammaMobiusSameSourceCurrent z v/pwGammaRaySource v)-
        (∑ j∈Finset.range q, (v:ℂ)^j*pwGammaMobiusReciprocalEndpointMoment z j)‖≤C*v^q := by
  obtain ⟨A,hA,hnear⟩ := pwGammaMobiusReciprocalResponse_near_flat_bound z q
  obtain ⟨D,hD,hloss⟩ := pwGammaMobiusReciprocalCutoffLoss_flat_bound z q
  choose B hB hb using (fun j => pwGammaMobiusReciprocalEndpointMoment_near_flat_bound z j q)
  let I : ℝ := ∫ t in Ioi (0:ℝ), ‖pwGammaMobiusReciprocalEndpointIntegrand z q t‖
  have hI : 0≤I := integral_nonneg (fun _ => norm_nonneg _)
  let K : ℝ := 2^(q+1)*(∑ j∈Finset.range q, B j)
  have hK : 0≤K := mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hB j))
  refine ⟨A+K+2*I+D, by positivity, ?_⟩
  intro v hv hvhalf
  have hv1 : v≤1 := by linarith
  have hv2 : 2*v≤1 := by linarith
  have hvpow : v^(q+1)≤v^q := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_pos hv q).le hv1
  have hscale (w : ℂ) : ‖(Real.exp (-v):ℂ)*w‖≤‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))
  have hn : ‖(Real.exp (-v):ℂ)*(∫ h in (0:ℝ)..v, pwGammaMobiusReciprocalResponse z v h)‖≤A*v^q :=
    (hscale _).trans ((hnear v hv hv1).trans (mul_le_mul_of_nonneg_left hvpow hA))
  have hl : ‖(Real.exp (-v):ℂ)*(∫ h in Ioi v, pwGammaMobiusReciprocalCutoffLoss z v h)‖≤D*v^q :=
    (hscale _).trans ((hloss v hv hv1).trans (mul_le_mul_of_nonneg_left hvpow hD))
  have hpiece (j : ℕ) : ‖(v:ℂ)^j*
      (∫ t in (0:ℝ)..(2*v), pwGammaMobiusReciprocalEndpointIntegrand z j t)‖≤
        (2^(q+1)*B j)*v^q := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv.le]
    calc
      _ ≤ 1*(B j*(2*v)^(q+1)) := mul_le_mul (pow_le_one₀ hv.le hv1)
        (hb j (2*v) (by positivity) hv2) (norm_nonneg _) zero_le_one
      _ = (2^(q+1)*B j)*v^(q+1) := by rw [mul_pow]; ring
      _ ≤ (2^(q+1)*B j)*v^q := mul_le_mul_of_nonneg_left hvpow (mul_nonneg (by positivity) (hB j))
  have hs : ‖∑ j∈Finset.range q, (v:ℂ)^j*
      (∫ t in (0:ℝ)..(2*v), pwGammaMobiusReciprocalEndpointIntegrand z j t)‖≤K*v^q := by
    calc
      _ ≤ ∑ j∈Finset.range q, ‖(v:ℂ)^j*
          (∫ t in (0:ℝ)..(2*v), pwGammaMobiusReciprocalEndpointIntegrand z j t)‖ := norm_sum_le _ _
      _ ≤ ∑ j∈Finset.range q, (2^(q+1)*B j)*v^q := Finset.sum_le_sum (fun j _ => hpiece j)
      _ = K*v^q := by simp only [← Finset.sum_mul, ← Finset.mul_sum]; rfl
  have hr : ‖∫ t in Ioi (2*v), pwGammaMobiusReciprocalCutoffRemainder z q v t‖≤(2*I)*v^q := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      pwGammaMobiusReciprocalCutoffRemainder_integral_bound z q hv
  rw [pwGammaMobiusReciprocalResponse_finite_cutoff_eq z q hv]
  calc
    _ ≤ (‖(Real.exp (-v):ℂ)*(∫ h in (0:ℝ)..v, pwGammaMobiusReciprocalResponse z v h)‖+
        ‖∑ j∈Finset.range q, (v:ℂ)^j*
          (∫ t in (0:ℝ)..(2*v), pwGammaMobiusReciprocalEndpointIntegrand z j t)‖)+
        ‖∫ t in Ioi (2*v), pwGammaMobiusReciprocalCutoffRemainder z q v t‖+
        ‖(Real.exp (-v):ℂ)*(∫ h in Ioi v, pwGammaMobiusReciprocalCutoffLoss z v h)‖ := by
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ (A*v^q+K*v^q)+(2*I)*v^q+D*v^q := add_le_add (add_le_add (add_le_add hn hs) hr) hl
    _ = (A+K+2*I+D)*v^q := by ring

end
end RHTower
