import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionDensityRatio
import GaloisForLFunctions.RHTower.LiClockCriticalAngularKernel

/-! Full four-coordinate mixed partition moments, signed forcing, and complete Borel source. -/

open MeasureTheory ProbabilityTheory Set Filter Topology Complex RiemannGaussian
open scoped BigOperators ENNReal Interval
noncomputable section
namespace RHTower

def liClockPairedEtaPartitionMixedMeasure (N : ℕ) :
    Measure ((ℝ×ℝ)×(ℝ×ℝ)) :=
  (liClockPairedEtaSymmetrizedMeasure N).prod
    (liClockPairedEtaContiguousSymmetrizedMeasure (Real.log (2*(N:ℝ))))

def liClockPairedEtaPartitionMixedEvenMoment (N j : ℕ) : ℝ :=
  ∫p:(ℝ×ℝ)×(ℝ×ℝ),
    ((p.1.1-p.1.2)+(p.2.1-p.2.2))^(2*j)
    ∂liClockPairedEtaPartitionMixedMeasure N

def liClockPairedEtaPartitionMixedSignedMoment (N j : ℕ) : ℝ :=
  ∫p:(ℝ×ℝ)×(ℝ×ℝ),
    ((p.1.1-p.1.2)-(p.2.1-p.2.2))*
      ((p.1.1-p.1.2)+(p.2.1-p.2.2))^(2*j+1)
    ∂liClockPairedEtaPartitionMixedMeasure N

def liClockPairedEtaPartitionMixedBorelKernel (N : ℕ) (t : ℝ) : ℝ :=
  ∑'j, liClockPairedEtaPartitionMixedEvenMoment N j*t^(2*j)/
    ((2*j).factorial:ℝ)^2

def liClockPairedEtaPartitionRelativeForcing (N : ℕ) (t : ℝ) : ℝ :=
  ∑'j, liClockPairedEtaPartitionMixedSignedMoment N j*t^(2*j+2)/
    (((2*j+2).factorial:ℝ)*((2*j+1).factorial:ℝ))

private abbrev msL (N : ℕ) : ℝ := Real.log (2*(N:ℝ))
private abbrev msX (p : (ℝ×ℝ)×(ℝ×ℝ)) : ℝ := p.1.1-p.1.2
private abbrev msY (p : (ℝ×ℝ)×(ℝ×ℝ)) : ℝ := p.2.1-p.2.2
private abbrev msW (p : (ℝ×ℝ)×(ℝ×ℝ)) : ℝ := msX p+msY p

private theorem ms_length_pos {N : ℕ} (hN : 0<N) : 0< msL N := by
  apply Real.log_pos
  have hn : (1:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  linarith

theorem liClockPairedEtaPartitionMixedMeasure_isProbability
    {N : ℕ} (hN : 0<N) :
  IsProbabilityMeasure (liClockPairedEtaPartitionMixedMeasure N) := by
  letI := liClockPairedEtaSymmetrizedMeasure_isProbability hN
  letI := liClockPairedEtaContiguousSymmetrizedMeasure_isProbability (ms_length_pos hN)
  unfold liClockPairedEtaPartitionMixedMeasure
  infer_instance

private theorem ms_actual_log_support (N : ℕ) :
    ∀ᵐu∂pairedEtaFiniteLogMeasure N, 0≤u ∧ u≤ msL N := by
  rw [pairedEtaFiniteLogMeasure_eq_restrict_union]
  filter_upwards [ae_restrict_mem (measurableSet_liClockPairedEtaPartitionLogSupport N)] with u hu
  have hm := liClockPairedEtaPartitionLogSupport_subset_Ioc N hu
  exact ⟨hm.1.le,hm.2⟩

private theorem ms_actual_support {N : ℕ} (_hN : 0<N) :
    ∀ᵐp∂liClockPairedEtaSymmetrizedMeasure N, |p.1-p.2|≤ msL N := by
  apply Measure.AbsolutelyContinuous.ae_le (tilted_absolutelyContinuous _ _)
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ms_actual_log_support N] with u hu
  filter_upwards [ms_actual_log_support N] with v hv
  rw [abs_le]
  constructor <;> linarith

private theorem ms_reference_support {N : ℕ} (_hN : 0<N) :
    ∀ᵐp∂liClockPairedEtaContiguousSymmetrizedMeasure (msL N),
      |p.1-p.2|≤ msL N :=
  liClockPairedEtaContiguousSymmetrizedMeasure_support _

private theorem ms_marginal_power_admissions
    (μ : Measure (ℝ×ℝ)) [IsProbabilityMeasure μ] {R : ℝ}
    (_hR : 0≤R) (hbound : ∀ᵐp∂μ, |p.1-p.2|≤R) (n : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^n) μ ∧
      |∫p:ℝ×ℝ,(p.1-p.2)^n∂μ|≤R^n := by
  have hb : ∀ᵐp∂μ, ‖(p.1-p.2)^n‖≤R^n := by
    filter_upwards [hbound] with p hp
    rw [Real.norm_eq_abs,abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hp _
  refine ⟨(integrable_const (R^n)).mono'
    (by fun_prop : Continuous (fun p:ℝ×ℝ=>(p.1-p.2)^n)).aestronglyMeasurable hb,?_⟩
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

private theorem ms_even_density_neg_map (g : ℝ→ℝ) (hg : Continuous g)
    (he : ∀x, g (-x)=g x) :
    Measure.map (fun x:ℝ=>-x)
      (volume.withDensity (fun x=>ENNReal.ofReal (g x))) =
      volume.withDensity (fun x=>ENNReal.ofReal (g x)) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ (by fun_prop)]
  have hφneg : Measurable (fun x:ℝ=>φ (-x)) := hφ.comp measurable_neg
  rw [lintegral_withDensity_eq_lintegral_mul _ hg.measurable.ennreal_ofReal hφneg,
    lintegral_withDensity_eq_lintegral_mul _ hg.measurable.ennreal_ofReal hφ]
  have hn := (Measure.measurePreserving_neg (volume:Measure ℝ)).lintegral_comp
    (f:=fun x:ℝ=>ENNReal.ofReal (g x)*φ x) (by fun_prop)
  simp only [Pi.mul_apply]
  rw [←hn]
  apply lintegral_congr
  intro x
  exact congrArg (fun a:ℝ=>ENNReal.ofReal a*φ (-x)) (he x).symm

private theorem ms_odd_from_even_density (μ : Measure (ℝ×ℝ)) (g : ℝ→ℝ)
    (hg : Continuous g) (he : ∀x, g (-x)=g x)
    (hmap : Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ=
      volume.withDensity (fun x=>ENNReal.ofReal (g x))) (j : ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j+1)∂μ)=0 := by
  let ν := Measure.map (fun p:ℝ×ℝ=>p.1-p.2) μ
  have hn : Measure.map (fun x:ℝ=>-x) ν=ν := by
    change Measure.map (fun x:ℝ=>-x) (Measure.map _ μ)=Measure.map _ μ
    rw [hmap]
    exact ms_even_density_neg_map g hg he
  have hi : (∫x:ℝ,x^(2*j+1)∂ν)=(∫p:ℝ×ℝ,(p.1-p.2)^(2*j+1)∂μ) :=
    integral_map (by fun_prop) (by fun_prop)
  have hneg : (∫x:ℝ,(-x)^(2*j+1)∂ν)=(∫x:ℝ,x^(2*j+1)∂ν) := by
    have h := integral_map (μ:=ν) (φ:=fun x:ℝ=>-x) (f:=fun x:ℝ=>x^(2*j+1))
      (by fun_prop) (by fun_prop)
    rw [hn] at h
    exact h.symm
  have hp (x : ℝ) : (-x)^(2*j+1)=-(x^(2*j+1)) := by
    rw [neg_pow,pow_add,pow_mul]
    norm_num
  simp_rw [hp] at hneg
  rw [integral_neg] at hneg
  linarith

private theorem ms_actual_odd_moment {N : ℕ} (hN : 0<N) (j : ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j+1)∂liClockPairedEtaSymmetrizedMeasure N)=0 :=
  ms_odd_from_even_density _ _ (continuous_liClockPairedEtaPartitionDifferenceDensity N)
    (liClockPairedEtaPartitionDifferenceDensity_even N)
    (liClockPairedEtaPartitionDifferenceDensity_map hN) j

private theorem ms_reference_odd_moment {N : ℕ} (hN : 0<N) (j : ℕ) :
    (∫p:ℝ×ℝ,(p.1-p.2)^(2*j+1)
      ∂liClockPairedEtaContiguousSymmetrizedMeasure (msL N))=0 :=
  ms_odd_from_even_density _ _ (continuous_liClockPairedEtaContiguousDifferenceDensity _)
    (liClockPairedEtaContiguousDifferenceDensity_even _)
    (liClockPairedEtaContiguousDifferenceDensity_map (ms_length_pos hN)) j

private theorem ms_mixed_support {N : ℕ} (hN : 0<N) :
    ∀ᵐp∂liClockPairedEtaPartitionMixedMeasure N,
      |msX p|≤ msL N ∧ |msY p|≤ msL N ∧
      |msW p|≤2*msL N ∧ |msX p-msY p|≤2*msL N := by
  letI := liClockPairedEtaSymmetrizedMeasure_isProbability hN
  letI := liClockPairedEtaContiguousSymmetrizedMeasure_isProbability (ms_length_pos hN)
  unfold liClockPairedEtaPartitionMixedMeasure
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ms_actual_support hN] with u hu
  filter_upwards [ms_reference_support hN] with v hv
  refine ⟨hu,hv,?_,?_⟩
  · exact (abs_add_le _ _).trans (by linarith)
  · exact (abs_sub _ _).trans (by linarith)

private theorem ms_mixed_continuous_integrable {N : ℕ} (hN : 0<N)
    (φ : ℝ×ℝ→ℝ) (hφ : Continuous φ) :
    Integrable (fun p:(ℝ×ℝ)×(ℝ×ℝ)=>φ (msX p,msY p))
      (liClockPairedEtaPartitionMixedMeasure N) := by
  letI := liClockPairedEtaPartitionMixedMeasure_isProbability hN
  let K : Set (ℝ×ℝ) := Icc (-msL N) (msL N) ×ˢ Icc (-msL N) (msL N)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C,hC⟩ := hK.bddAbove_image hφ.norm.continuousOn
  apply (integrable_const C).mono' (by
    exact (hφ.comp (by fun_prop : Continuous (fun p:(ℝ×ℝ)×(ℝ×ℝ)=>
      (msX p,msY p)))).aestronglyMeasurable)
  filter_upwards [ms_mixed_support hN] with p hp
  exact hC ⟨(msX p,msY p),⟨abs_le.mp hp.1,abs_le.mp hp.2.1⟩,rfl⟩

private theorem ms_mixed_polynomial_integrable {N : ℕ} (hN : 0<N)
    (p q : ℕ) :
    Integrable (fun z:(ℝ×ℝ)×(ℝ×ℝ)=>msX z^p*msY z^q)
      (liClockPairedEtaPartitionMixedMeasure N) ∧
    Integrable (fun z:(ℝ×ℝ)×(ℝ×ℝ)=>msW z^p)
      (liClockPairedEtaPartitionMixedMeasure N) ∧
    Integrable (fun z:(ℝ×ℝ)×(ℝ×ℝ)=>
      (msX z-msY z)*msW z^q) (liClockPairedEtaPartitionMixedMeasure N) := by
  exact ⟨ms_mixed_continuous_integrable hN (fun z=>z.1^p*z.2^q) (by fun_prop),
    ms_mixed_continuous_integrable hN (fun z=>(z.1+z.2)^p) (by fun_prop),
    ms_mixed_continuous_integrable hN (fun z=>(z.1-z.2)*(z.1+z.2)^q) (by fun_prop)⟩

private theorem ms_mixed_monomial_integral {N : ℕ} (hN : 0<N)
    (p q : ℕ) :
    (∫z:(ℝ×ℝ)×(ℝ×ℝ),msX z^p*msY z^q
      ∂liClockPairedEtaPartitionMixedMeasure N) =
    (∫u:ℝ×ℝ,(u.1-u.2)^p∂liClockPairedEtaSymmetrizedMeasure N)*
    (∫v:ℝ×ℝ,(v.1-v.2)^q
      ∂liClockPairedEtaContiguousSymmetrizedMeasure (msL N)) := by
  letI := liClockPairedEtaSymmetrizedMeasure_isProbability hN
  letI := liClockPairedEtaContiguousSymmetrizedMeasure_isProbability (ms_length_pos hN)
  unfold liClockPairedEtaPartitionMixedMeasure
  exact integral_prod_mul (fun u:ℝ×ℝ=>(u.1-u.2)^p)
    (fun v:ℝ×ℝ=>(v.1-v.2)^q)

private theorem ms_weighted_binomial (m : ℕ) (hm : 0 < m) (x y : ℝ) :
    (∑k∈Finset.range (m+1), (2*(k:ℝ)-(m:ℝ))*(m.choose k:ℝ)*x^k*y^(m-k)) =
      (m:ℝ)*(x-y)*(x+y)^(m-1) := by
  cases m with
  | zero => omega
  | succ n =>
    have hc (k : ℕ) : (n+1:ℝ)*(n.choose k:ℝ)=
        (Nat.choose (n+1) (k+1):ℝ)*(k+1:ℝ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    have hs : (∑k∈Finset.range (n+2), (k:ℝ)*(Nat.choose (n+1) k:ℝ)*x^k*y^(n+1-k)) =
        (n+1:ℝ)*x*(x+y)^n := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero,zero_mul,add_zero]
      calc
        _ = ∑k∈Finset.range (n+1),(n+1:ℝ)*x*((n.choose k:ℝ)*x^k*y^(n-k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [show n+1-(k+1)=n-k by omega,pow_succ]
          rw [Nat.cast_add,Nat.cast_one]
          rw [mul_comm (k+1:ℝ),←hc]
          ring
        _ = (n+1:ℝ)*x*(x+y)^n := by
          rw [←Finset.mul_sum,add_pow]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          ring
    have hb : (∑k∈Finset.range (n+2), (Nat.choose (n+1) k:ℝ)*x^k*y^(n+1-k)) =
        (x+y)^(n+1) := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
    change (∑k∈Finset.range (n+2),(2*(k:ℝ)-(n+1:ℝ))*
      (Nat.choose (n+1) k:ℝ)*x^k*y^(n+1-k))=(n+1:ℝ)*(x-y)*(x+y)^n
    calc
      _=2*(∑k∈Finset.range (n+2),(k:ℝ)*(Nat.choose (n+1) k:ℝ)*x^k*y^(n+1-k))-
          (n+1:ℝ)*(∑k∈Finset.range (n+2),(Nat.choose (n+1) k:ℝ)*x^k*y^(n+1-k)) := by
        rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _=_ := by rw [hs,hb,pow_succ]; ring

private theorem ms_even_index_sum (n : ℕ) (f : ℕ→ℝ)
    (hodd : ∀k∈Finset.range (2*n+1), Odd k→f k=0) :
    (∑k∈Finset.range (2*n+1),f k)=∑a∈Finset.range (n+1),f (2*a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 2*(n+1)+1=(2*n+1)+1+1 := by omega
    rw [hp,Finset.sum_range_succ,Finset.sum_range_succ]
    have ho : f (2*n+1)=0 := hodd _ (Finset.mem_range.mpr (by omega)) ⟨n,by omega⟩
    have hi := ih (by
      intro k hk ho
      exact hodd k (Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)) ho)
    rw [hi,ho,add_zero]
    rw [Finset.sum_range_succ (n:=n+1)]
    have he : (2*n+1)+1=2*(n+1) := by omega
    simp only [he]

private theorem ms_mixed_power_integral {N : ℕ} (hN : 0<N) (m : ℕ) :
    (∫z:(ℝ×ℝ)×(ℝ×ℝ),msW z^m∂liClockPairedEtaPartitionMixedMeasure N)=
      ∑k∈Finset.range (m+1),(m.choose k:ℝ)*
        (∫u:ℝ×ℝ,(u.1-u.2)^k∂liClockPairedEtaSymmetrizedMeasure N)*
        (∫v:ℝ×ℝ,(v.1-v.2)^(m-k)
          ∂liClockPairedEtaContiguousSymmetrizedMeasure (msL N)) := by
  have hpoly (z:(ℝ×ℝ)×(ℝ×ℝ)) : msW z^m=
      ∑k∈Finset.range (m+1),(m.choose k:ℝ)*(msX z^k*msY z^(m-k)) := by
    dsimp [msW]
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hpoly]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_const_mul,ms_mixed_monomial_integral hN]
    ring
  · intro k hk
    exact ((ms_mixed_polynomial_integrable hN k (m-k)).1).const_mul _

private theorem ms_marginal_odd_zero {N : ℕ} (hN : 0<N)
    (k : ℕ) (hk : Odd k) :
    (∫u:ℝ×ℝ,(u.1-u.2)^k∂liClockPairedEtaSymmetrizedMeasure N)=0 := by
  obtain ⟨r,hr⟩ := hk
  have he : k=2*r+1 := by omega
  rw [he]
  exact ms_actual_odd_moment hN r

theorem liClockPairedEtaPartitionMixedEvenMoment_eq_sum
    {N : ℕ} (hN : 0<N) (j : ℕ) :
  liClockPairedEtaPartitionMixedEvenMoment N j =
    ∑a∈Finset.range (j+1), (Nat.choose (2*j) (2*a):ℝ)*
      liClockPairedEtaSymmetrizedEvenMoment N a*
      liClockPairedEtaContiguousSymmetrizedEvenMoment
        (Real.log (2*(N:ℝ))) (j-a) := by
  change (∫z:(ℝ×ℝ)×(ℝ×ℝ),msW z^(2*j)
    ∂liClockPairedEtaPartitionMixedMeasure N)=_
  rw [ms_mixed_power_integral hN]
  rw [ms_even_index_sum j _ (by
    intro k hk ho
    rw [ms_marginal_odd_zero hN k ho]
    ring)]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a≤j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  have he : 2*j-2*a=2*(j-a) := by omega
  simp only [he,liClockPairedEtaSymmetrizedEvenMoment,
    liClockPairedEtaContiguousSymmetrizedEvenMoment]

theorem liClockPairedEtaPartitionMixedSignedMoment_mul_eq_sum
    {N : ℕ} (hN : 0<N) (j : ℕ) :
  (2*j+2:ℝ)*liClockPairedEtaPartitionMixedSignedMoment N j =
    ∑a∈Finset.range (j+2), ((2*a:ℝ)-2*((j+1-a:ℕ):ℝ))*
      (Nat.choose (2*j+2) (2*a):ℝ)*
      liClockPairedEtaSymmetrizedEvenMoment N a*
      liClockPairedEtaContiguousSymmetrizedEvenMoment
        (Real.log (2*(N:ℝ))) (j+1-a) := by
  have hp (z:(ℝ×ℝ)×(ℝ×ℝ)) :
      (2*j+2:ℝ)*(msX z-msY z)*msW z^(2*j+1)=
      ∑k∈Finset.range (2*j+2+1),
        (2*(k:ℝ)-(2*j+2:ℝ))*(Nat.choose (2*j+2) k:ℝ)*
        (msX z^k*msY z^(2*j+2-k)) := by
    have h := ms_weighted_binomial (2*j+2) (by omega) (msX z) (msY z)
    simp only [show 2*j+2-1=2*j+1 by omega] at h
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at h
    calc
      _ = ∑k∈Finset.range (2*j+2+1),
          (2*(k:ℝ)-(2*j+2:ℝ))*(Nat.choose (2*j+2) k:ℝ)*msX z^k*msY z^(2*j+2-k) := h.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
  change (2*j+2:ℝ)*(∫z:(ℝ×ℝ)×(ℝ×ℝ),
    (msX z-msY z)*msW z^(2*j+1)∂liClockPairedEtaPartitionMixedMeasure N)=_
  rw [←integral_const_mul]
  simp_rw [←mul_assoc,hp]
  rw [integral_finsetSum]
  · have hm (k : ℕ) :
        (∫z:(ℝ×ℝ)×(ℝ×ℝ),
          (2*(k:ℝ)-(2*j+2:ℝ))*(Nat.choose (2*j+2) k:ℝ)*
          (msX z^k*msY z^(2*j+2-k))∂liClockPairedEtaPartitionMixedMeasure N)=
        (2*(k:ℝ)-(2*j+2:ℝ))*(Nat.choose (2*j+2) k:ℝ)*
          ((∫u:ℝ×ℝ,(u.1-u.2)^k∂liClockPairedEtaSymmetrizedMeasure N)*
          (∫v:ℝ×ℝ,(v.1-v.2)^(2*j+2-k)
            ∂liClockPairedEtaContiguousSymmetrizedMeasure (msL N))) := by
      rw [integral_const_mul,ms_mixed_monomial_integral hN]
    simp_rw [hm]
    rw [show 2*j+2+1=2*(j+1)+1 by omega]
    rw [ms_even_index_sum (j+1) _ (by
      intro k hk ho
      rw [ms_marginal_odd_zero hN k ho]
      ring)]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a≤j+1 := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have he : 2*j+2-2*a=2*(j+1-a) := by omega
    simp only [he,liClockPairedEtaSymmetrizedEvenMoment,
      liClockPairedEtaContiguousSymmetrizedEvenMoment,Nat.cast_sub ha',Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    dsimp [msL]
    ring
  · intro k hk
    exact ((ms_mixed_polynomial_integrable hN k (2*j+2-k)).1).const_mul _

theorem liClockPairedEtaPartitionMixedSignedMoment_eq_signed_density
    {N : ℕ} (hN : 0<N) (j : ℕ) :
  liClockPairedEtaPartitionMixedSignedMoment N j =
    ∫w:ℝ,w^(2*j+1)*liClockPairedEtaPartitionSignedForcingDensity N w := by
  exact (liClockPairedEtaPartitionSignedForcingDensity_integral_eq_source hN
    (fun w=>w^(2*j+1)) (by fun_prop)).symm

theorem liClockPairedEtaPartitionMixedSignedMoment_zero
    {N : ℕ} (hN : 0<N) :
  liClockPairedEtaPartitionMixedSignedMoment N 0 =
    liClockPairedEtaSymmetrizedEvenMoment N 1-
      liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))) 1 := by
  have h := liClockPairedEtaPartitionMixedSignedMoment_mul_eq_sum hN 0
  have ha := liClockPairedEtaSymmetrizedEvenMoment_zero hN
  have hu := liClockPairedEtaContiguousSymmetrizedEvenMoment_zero (ms_length_pos hN)
  norm_num [Finset.sum_range_succ,ha,hu] at h
  linarith

private theorem ms_mixed_moment_bounds {N : ℕ} (hN : 0<N) (j : ℕ) :
    0≤liClockPairedEtaPartitionMixedEvenMoment N j ∧
    |liClockPairedEtaPartitionMixedEvenMoment N j|≤(2*msL N)^(2*j) ∧
    |liClockPairedEtaPartitionMixedSignedMoment N j|≤(2*msL N)^(2*j+2) := by
  letI := liClockPairedEtaPartitionMixedMeasure_isProbability hN
  refine ⟨?_,?_,?_⟩
  · unfold liClockPairedEtaPartitionMixedEvenMoment
    apply integral_nonneg
    intro z
    change 0≤ msW z^(2*j)
    rw [pow_mul]
    positivity
  · have hb : ∀ᵐz∂liClockPairedEtaPartitionMixedMeasure N,
        ‖msW z^(2*j)‖≤(2*msL N)^(2*j) := by
      filter_upwards [ms_mixed_support hN] with z hz
      rw [Real.norm_eq_abs,abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hz.2.2.1 _
    exact (by simpa only [liClockPairedEtaPartitionMixedEvenMoment,liClockPairedEtaPartitionMixedSignedMoment,msW,msX,msY,Real.norm_eq_abs,probReal_univ,mul_one]
      using norm_integral_le_of_norm_le_const hb)
  · have hb : ∀ᵐz∂liClockPairedEtaPartitionMixedMeasure N,
        ‖(msX z-msY z)*msW z^(2*j+1)‖≤(2*msL N)^(2*j+2) := by
      filter_upwards [ms_mixed_support hN] with z hz
      rw [Real.norm_eq_abs,abs_mul,abs_pow]
      calc
        _≤(2*msL N)*(2*msL N)^(2*j+1) :=
          mul_le_mul hz.2.2.2 (pow_le_pow_left₀ (abs_nonneg _) hz.2.2.1 _)
            (pow_nonneg (abs_nonneg _) _) (by linarith [ms_length_pos hN])
        _=_ := by rw [show 2*j+2=(2*j+1)+1 by omega,pow_succ]; ring
    exact (by simpa only [liClockPairedEtaPartitionMixedEvenMoment,liClockPairedEtaPartitionMixedSignedMoment,msW,msX,msY,Real.norm_eq_abs,probReal_univ,mul_one]
      using norm_integral_le_of_norm_le_const hb)

private theorem ms_mixed_even_zero {N : ℕ} (hN : 0<N) :
    liClockPairedEtaPartitionMixedEvenMoment N 0=1 := by
  letI := liClockPairedEtaPartitionMixedMeasure_isProbability hN
  simp [liClockPairedEtaPartitionMixedEvenMoment]

private theorem ms_factorial_sq_le (j : ℕ) :
    (j.factorial:ℝ)≤((2*j).factorial:ℝ)^2 := by
  have h1 : (j.factorial:ℝ)≤((2*j).factorial:ℝ) :=
    by exact_mod_cast Nat.factorial_le (show j≤2*j by omega)
  have h2 : (1:ℝ)≤((2*j).factorial:ℝ) :=
    by exact_mod_cast Nat.factorial_le (Nat.zero_le (2*j))
  nlinarith

private theorem ms_factorial_signed_le (j : ℕ) :
    (j.factorial:ℝ)≤((2*j+2).factorial:ℝ)*((2*j+1).factorial:ℝ) := by
  have h1 : (j.factorial:ℝ)≤((2*j+2).factorial:ℝ) :=
    by exact_mod_cast Nat.factorial_le (show j≤2*j+2 by omega)
  have h2 : (1:ℝ)≤((2*j+1).factorial:ℝ) :=
    by exact_mod_cast Nat.factorial_le (Nat.zero_le (2*j+1))
  nlinarith

private theorem ms_even_norm_bound {N : ℕ} (hN : 0<N) {T : ℝ}
    {z : ℂ} (hz : ‖z‖≤T) (j : ℕ) :
    ‖(liClockPairedEtaPartitionMixedEvenMoment N j:ℂ)*z^(2*j)/
      ((2*j).factorial:ℂ)^2‖≤((2*msL N)^2*T^2)^j/(j.factorial:ℝ) := by
  have hR : 0≤2*msL N := by linarith [ms_length_pos hN]
  have hT : 0≤T := (norm_nonneg z).trans hz
  rw [norm_div,norm_mul,norm_pow,norm_pow,Complex.norm_natCast,
    Complex.norm_real,Real.norm_eq_abs]
  calc
    _≤(2*msL N)^(2*j)*T^(2*j)/((2*j).factorial:ℝ)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul (ms_mixed_moment_bounds hN j).2.1
          (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_nonneg (norm_nonneg _) _)
          (by positivity)) (sq_nonneg _)
    _≤(2*msL N)^(2*j)*T^(2*j)/(j.factorial:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (ms_factorial_sq_le j)
    _=_ := by simp only [mul_pow,pow_mul]

private theorem ms_signed_norm_bound {N : ℕ} (hN : 0<N) {T : ℝ}
    {z : ℂ} (hz : ‖z‖≤T) (j : ℕ) :
    ‖(liClockPairedEtaPartitionMixedSignedMoment N j:ℂ)*z^(2*j+2)/
      (((2*j+2).factorial:ℂ)*((2*j+1).factorial:ℂ))‖≤
      ((2*msL N)^2*T^2)*((2*msL N)^2*T^2)^j/(j.factorial:ℝ) := by
  have hR : 0≤2*msL N := by linarith [ms_length_pos hN]
  have hT : 0≤T := (norm_nonneg z).trans hz
  rw [norm_div,norm_mul,norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_natCast,
    Complex.norm_real,Real.norm_eq_abs]
  calc
    _≤(2*msL N)^(2*j+2)*T^(2*j+2)/
        (((2*j+2).factorial:ℝ)*((2*j+1).factorial:ℝ)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul (ms_mixed_moment_bounds hN j).2.2
          (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_nonneg (norm_nonneg _) _)
          (by positivity)) (by positivity)
    _≤(2*msL N)^(2*j+2)*T^(2*j+2)/(j.factorial:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (ms_factorial_signed_le j)
    _=_ := by rw [show 2*j+2=2*(j+1) by omega,pow_mul,pow_mul,mul_pow,pow_succ]; ring

private theorem ms_compact_norm_bounds {N : ℕ} (hN : 0<N)
    (T : ℝ) (_hT : 0≤T) :
    Summable (fun j:ℕ=>((2*msL N)^2*T^2)^j/(j.factorial:ℝ)) ∧
    Summable (fun j:ℕ=>((2*msL N)^2*T^2)*
      ((2*msL N)^2*T^2)^j/(j.factorial:ℝ)) ∧
    (∀j (z:ℂ), ‖z‖≤T →
      ‖(liClockPairedEtaPartitionMixedEvenMoment N j:ℂ)*z^(2*j)/
        ((2*j).factorial:ℂ)^2‖≤((2*msL N)^2*T^2)^j/(j.factorial:ℝ)) ∧
    (∀j (z:ℂ), ‖z‖≤T →
      ‖(liClockPairedEtaPartitionMixedSignedMoment N j:ℂ)*z^(2*j+2)/
        (((2*j+2).factorial:ℂ)*((2*j+1).factorial:ℂ))‖≤
        ((2*msL N)^2*T^2)*((2*msL N)^2*T^2)^j/(j.factorial:ℝ)) := by
  refine ⟨Real.summable_pow_div_factorial _,?_,
    fun j z hz=>ms_even_norm_bound hN hz j,fun j z hz=>ms_signed_norm_bound hN hz j⟩
  simpa only [mul_div_assoc] using
    (Real.summable_pow_div_factorial ((2*msL N)^2*T^2)).mul_left
      ((2*msL N)^2*T^2)

theorem summable_norm_liClockPairedEtaPartitionMixedBorelTerm
    {N : ℕ} (hN : 0<N) (z : ℂ) :
  Summable (fun j => ‖(liClockPairedEtaPartitionMixedEvenMoment N j:ℂ)*
    z^(2*j)/((2*j).factorial:ℂ)^2‖) :=
  (Real.summable_pow_div_factorial _).of_nonneg_of_le
    (fun _=>norm_nonneg _) (ms_even_norm_bound hN (le_refl ‖z‖))

theorem summable_norm_liClockPairedEtaPartitionRelativeForcingTerm
    {N : ℕ} (hN : 0<N) (z : ℂ) :
  Summable (fun j => ‖(liClockPairedEtaPartitionMixedSignedMoment N j:ℂ)*
    z^(2*j+2)/(((2*j+2).factorial:ℂ)*((2*j+1).factorial:ℂ))‖) :=
  (ms_compact_norm_bounds hN ‖z‖ (norm_nonneg _)).2.1.of_nonneg_of_le
    (fun _=>norm_nonneg _) (ms_signed_norm_bound hN (le_refl ‖z‖))

private theorem ms_real_even_summable {N : ℕ} (hN : 0<N) (t : ℝ) :
    Summable (fun j=>liClockPairedEtaPartitionMixedEvenMoment N j*t^(2*j)/
      ((2*j).factorial:ℝ)^2) := by
  apply Complex.summable_ofReal.mp
  simpa only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]
    using (summable_norm_liClockPairedEtaPartitionMixedBorelTerm hN (t:ℂ)).of_norm

private theorem ms_real_signed_summable {N : ℕ} (hN : 0<N) (t : ℝ) :
    Summable (fun j=>liClockPairedEtaPartitionMixedSignedMoment N j*t^(2*j+2)/
      (((2*j+2).factorial:ℝ)*((2*j+1).factorial:ℝ))) := by
  apply Complex.summable_ofReal.mp
  simpa only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]
    using (summable_norm_liClockPairedEtaPartitionRelativeForcingTerm hN (t:ℂ)).of_norm

private theorem ms_kernel_series_hasSum (t : ℝ)
    (p : (ℝ×ℝ)×(ℝ×ℝ)) :
    HasSum (fun j:ℕ=>msW p^(2*j)*t^(2*j)/((2*j).factorial:ℝ)^2)
      (liClockCriticalEvenKernel (t*msW p)) := by
  have hs : Summable (fun n:ℕ=>(t*msW p)^n/(n.factorial:ℝ)^2) := by
    apply Complex.summable_ofReal.mp
    simpa only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
      using (summable_norm_liClockCriticalScalarTermComplex ((t*msW p:ℝ):ℂ)).of_norm
  have he : HasSum (fun j:ℕ=>(t*msW p)^(2*j)/((2*j).factorial:ℝ)^2)
      (∑'j,(t*msW p)^(2*j)/((2*j).factorial:ℝ)^2) :=
    (hs.comp_injective (fun x y h=>by omega)).hasSum
  change HasSum _ (∑'j,(t*msW p)^(2*j)/((2*j).factorial:ℝ)^2)
  apply he.congr_fun
  intro j
  rw [mul_pow]
  ring

private theorem ms_kernel_integrable {N : ℕ} (hN : 0<N) (t : ℝ) :
    Integrable (fun p:(ℝ×ℝ)×(ℝ×ℝ)=>liClockCriticalEvenKernel (t*msW p))
      (liClockPairedEtaPartitionMixedMeasure N) :=
  ms_mixed_continuous_integrable hN (fun z=>liClockCriticalEvenKernel (t*(z.1+z.2)))
    (continuous_liClockCriticalEvenKernel.comp (by fun_prop))

private theorem ms_source_series_hasSum {N : ℕ} (hN : 0<N) (t : ℝ) :
    HasSum (fun j:ℕ=>liClockPairedEtaPartitionMixedEvenMoment N j*
      t^(2*j)/((2*j).factorial:ℝ)^2)
      (∫p:(ℝ×ℝ)×(ℝ×ℝ),liClockCriticalEvenKernel (t*msW p)
        ∂liClockPairedEtaPartitionMixedMeasure N) := by
  let f : ℕ→((ℝ×ℝ)×(ℝ×ℝ))→ℝ := fun j p=>
    msW p^(2*j)*t^(2*j)/((2*j).factorial:ℝ)^2
  have hf : ∀j p,0≤f j p := by
    intro j p
    dsimp [f]
    rw [pow_mul,pow_mul]
    positivity
  have hs : ∀p,HasSum (fun j=>f j p) (liClockCriticalEvenKernel (t*msW p)) :=
    ms_kernel_series_hasSum t
  have hi : Integrable (fun p=>∑'j,f j p) (liClockPairedEtaPartitionMixedMeasure N) :=
    (ms_kernel_integrable hN t).congr (Eventually.of_forall (fun p=>(hs p).tsum_eq.symm))
  have he : HasSum (fun j=>∫p,f j p∂liClockPairedEtaPartitionMixedMeasure N)
      (∫p,liClockCriticalEvenKernel (t*msW p)∂liClockPairedEtaPartitionMixedMeasure N) := by
    apply MeasureTheory.hasSum_integral_of_dominated_convergence f
    · intro j
      exact (by fun_prop : Continuous (f j)).aestronglyMeasurable
    · intro j
      exact Eventually.of_forall (fun p=>le_of_eq (Real.norm_of_nonneg (hf j p)))
    · exact Eventually.of_forall (fun p=>(hs p).summable)
    · exact hi
    · exact Eventually.of_forall hs
  apply he.congr_fun
  intro j
  dsimp [f]
  rw [integral_div,integral_mul_const]
  rfl

theorem liClockPairedEtaPartitionMixedBorelKernel_eq_source
    {N : ℕ} (hN : 0<N) (t : ℝ) :
  Integrable (fun p:(ℝ×ℝ)×(ℝ×ℝ) =>
    liClockCriticalEvenKernel (t*((p.1.1-p.1.2)+(p.2.1-p.2.2))))
      (liClockPairedEtaPartitionMixedMeasure N) ∧
  liClockPairedEtaPartitionMixedBorelKernel N t =
    ∫p:(ℝ×ℝ)×(ℝ×ℝ),
      liClockCriticalEvenKernel (t*((p.1.1-p.1.2)+(p.2.1-p.2.2)))
      ∂liClockPairedEtaPartitionMixedMeasure N :=
  ⟨ms_kernel_integrable hN t,(ms_source_series_hasSum hN t).tsum_eq⟩

theorem liClockPairedEtaPartitionMixedBorelKernel_zero
    {N : ℕ} (hN : 0<N) :
  liClockPairedEtaPartitionMixedBorelKernel N 0=1 := by
  unfold liClockPairedEtaPartitionMixedBorelKernel
  rw [tsum_eq_single 0]
  · simp only [mul_zero,Nat.factorial_zero,Nat.cast_one,pow_zero,mul_one,one_pow,div_one,
      ms_mixed_even_zero hN]
  · intro j hj
    have he : 2*j≠0 := by omega
    simp only [zero_pow he,mul_zero,zero_div]

theorem one_le_liClockPairedEtaPartitionMixedBorelKernel
    {N : ℕ} (hN : 0<N) (t : ℝ) :
  1≤liClockPairedEtaPartitionMixedBorelKernel N t := by
  have h := (ms_real_even_summable hN t).le_tsum 0 (fun j hj=>by
    have := (ms_mixed_moment_bounds hN j).1
    rw [pow_mul]
    positivity)
  simpa [liClockPairedEtaPartitionMixedBorelKernel,ms_mixed_even_zero hN] using h

theorem liClockPairedEtaPartitionMixedBorelKernel_pos
    {N : ℕ} (hN : 0<N) (t : ℝ) :
  0<liClockPairedEtaPartitionMixedBorelKernel N t :=
  lt_of_lt_of_le zero_lt_one (one_le_liClockPairedEtaPartitionMixedBorelKernel hN t)

private theorem ms_mixed_series_continuous {N : ℕ} (hN : 0<N) :
    Continuous (liClockPairedEtaPartitionMixedBorelKernel N) ∧
    Continuous (liClockPairedEtaPartitionRelativeForcing N) := by
  constructor
  · rw [continuous_iff_continuousAt]
    intro t
    let T : ℝ := |t|+1
    have hT : 0≤T := by dsimp [T]; positivity
    have hc : ContinuousOn (liClockPairedEtaPartitionMixedBorelKernel N)
        (Metric.closedBall 0 T) := by
      unfold liClockPairedEtaPartitionMixedBorelKernel
      apply continuousOn_tsum (fun j=>by fun_prop)
        (Real.summable_pow_div_factorial ((2*msL N)^2*T^2))
      intro j x hx
      have hx' : ‖(x:ℂ)‖≤T := by
        simpa only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,
          Complex.norm_real,Real.norm_eq_abs] using hx
      have h := ms_even_norm_bound hN hx' j
      norm_cast at h
      simpa only [Nat.cast_pow,Nat.cast_mul] using h
    apply hc.continuousAt
    apply Metric.closedBall_mem_nhds_of_mem
    simp [Metric.mem_ball,T]
  · rw [continuous_iff_continuousAt]
    intro t
    let T : ℝ := |t|+1
    have hT : 0≤T := by dsimp [T]; positivity
    have hc : ContinuousOn (liClockPairedEtaPartitionRelativeForcing N)
        (Metric.closedBall 0 T) := by
      unfold liClockPairedEtaPartitionRelativeForcing
      apply continuousOn_tsum (fun j=>by fun_prop)
        (ms_compact_norm_bounds hN T hT).2.1
      intro j x hx
      have hx' : ‖(x:ℂ)‖≤T := by
        simpa only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,
          Complex.norm_real,Real.norm_eq_abs] using hx
      have h := ms_signed_norm_bound hN hx' j
      norm_cast at h
      simpa only [Nat.cast_pow,Nat.cast_mul] using h
    apply hc.continuousAt
    apply Metric.closedBall_mem_nhds_of_mem
    simp [Metric.mem_ball,T]

end RHTower
