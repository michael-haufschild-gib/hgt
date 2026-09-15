import GaloisForLFunctions.RHTower.EulerDeletionCutoffAverage
import GaloisForLFunctions.RHTower.Sieve.GrahamMeanSquare
import GaloisForLFunctions.RHTower.MoebiusResidualTailForm

/-!
# Averaged divisor source and cumulative covariance

The logarithmic cutoff average is exactly a difference of Barban--Vehov
sources. Its compensated cumulative energy retains every temporal cross term.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology ArithmeticFunction
open scoped BigOperators
namespace RHTower.DeletionAveragedDivisor
open DeletionCutoffAverage Sieve

/-- Literal arithmetic coefficient with its finite support. -/
def arithmeticCoeff (X M d : ℕ) : ℝ :=
  if d≤M then taper X M d*((moebius d : ℤ) : ℝ) else 0

/-- Divisor coefficient of the complete tapered source. -/
def divisorSource (X M k : ℕ) : ℝ := ∑ d ∈ k.divisors, arithmeticCoeff X M d

private theorem span_pos {X M : ℕ} (hX : 1≤X) (hXM : X<M) :
    0<Real.log M-Real.log X := by
  exact sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hX) (by exact_mod_cast hXM))

/-- The taper is precisely the difference of two unnormalized logarithmic sieve weights. -/
theorem arithmeticCoeff_eq_weight_difference {X M : ℕ} (hX : 1≤X) (hXM : X<M) (d : ℕ) :
    arithmeticCoeff X M d=(barbanVehovWeight M d-barbanVehovWeight X d)/
      (Real.log M-Real.log X) := by
  by_cases hd0 : d=0
  · subst d
    simp [arithmeticCoeff,barbanVehovWeight]
  have hd : (d : ℝ)≠0 := by exact_mod_cast hd0
  have hX0 : (X : ℝ)≠0 := by exact_mod_cast (show X≠0 by omega)
  have hM0 : (M : ℝ)≠0 := by exact_mod_cast (show M≠0 by omega)
  by_cases hdM : d≤M
  · by_cases hdX : d≤X
    · rw [arithmeticCoeff,if_pos hdM,taper_eq_one hX hXM hdX,
        barbanVehovWeight,if_pos hdM,barbanVehovWeight,if_pos hdX,
        Real.log_div hM0 hd,Real.log_div hX0 hd]
      field_simp [(span_pos hX hXM).ne']
      ring
    · simp only [arithmeticCoeff,hdM,if_true,barbanVehovWeight,hdX,if_false,sub_zero,
        taper,max_eq_right (by omega : X≤d)]
      rw [Real.log_div hM0 hd]
      ring
  · have hdX : ¬d≤X := by omega
    simp [arithmeticCoeff,barbanVehovWeight,hdM,hdX]

/-- All source coordinates, including those beyond support, retain the difference divisor sum. -/
theorem divisorSource_eq_difference {X M : ℕ} (hX : 1≤X) (hXM : X<M) (k : ℕ) :
    divisorSource X M k=(barbanVehovCoeff M k-barbanVehovCoeff X k)/
      (Real.log M-Real.log X) := by
  simp only [divisorSource,arithmeticCoeff_eq_weight_difference hX hXM,
    ← Finset.sum_div,Finset.sum_sub_distrib,barbanVehovCoeff]

/-- The unit source coefficient remains exactly one. -/
theorem divisorSource_one {X M : ℕ} (hX : 1≤X) (hXM : X<M) : divisorSource X M 1=1 := by
  rw [divisorSource_eq_difference hX hXM,barbanVehovCoeff_one (by omega),
    barbanVehovCoeff_one hX,div_self (span_pos hX hXM).ne']

/-- Through the outer cutoff the source exposes von Mangoldt minus the inner sieve correction. -/
theorem divisorSource_eq_vonMangoldt_sub {X M k : ℕ} (hX : 1≤X) (hXM : X<M)
    (hk : 1<k) (hkM : k≤M) :
    divisorSource X M k=(vonMangoldt k-barbanVehovCoeff X k)/(Real.log M-Real.log X) := by
  rw [divisorSource_eq_difference hX hXM,barbanVehovCoeff_eq_vonMangoldt hk hkM]

/-- Every non-unit source coordinate through the preserved inner cutoff vanishes. -/
theorem divisorSource_initial_zero {X M k : ℕ} (hX : 1≤X) (hXM : X<M)
    (hk : 1<k) (hkX : k≤X) : divisorSource X M k=0 := by
  rw [divisorSource_eq_vonMangoldt_sub hX hXM hk (by omega),
    barbanVehovCoeff_eq_vonMangoldt hk hkX,sub_self,zero_div]

private theorem divisorSource_eq_truncated (X M k : ℕ) (hk : 1≤k) :
    divisorSource X M k=∑ d ∈ Finset.Icc 1 M,
      if d∣k then arithmeticCoeff X M d else 0 := by
  unfold divisorSource
  have hsub : k.divisors.filter (fun d => d≤M)⊆k.divisors := Finset.filter_subset _ _
  have hzero : ∀ d ∈ k.divisors, d∉k.divisors.filter (fun d => d≤M) →
      arithmeticCoeff X M d=0 := by
    intro d hd hnot
    have hdM : ¬d≤M := by simpa only [Finset.mem_filter,hd,true_and] using hnot
    simp [arithmeticCoeff,hdM]
  rw [← Finset.sum_subset hsub hzero,← Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdk,hk0⟩,hdM⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdk hk,hdM⟩,hdk⟩
  · rintro ⟨⟨hd1,hdM⟩,hdk⟩
    exact ⟨⟨hdk,by omega⟩,hdM⟩

/-- The full summatory divisor source is the exact finite floor sum. -/
theorem sum_divisorSource_eq_floor (X M n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, divisorSource X M k)=
      ∑ d ∈ Finset.Icc 1 M, arithmeticCoeff X M d*((n/d : ℕ) : ℝ) := by
  have hrewrite := Finset.sum_congr rfl (fun k (hk : k∈Finset.Icc 1 n) =>
    divisorSource_eq_truncated X M k (Finset.mem_Icc.mp hk).1)
  rw [hrewrite,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter,Finset.sum_const,card_filter_dvd_Icc (by have := (Finset.mem_Icc.mp hd).1; omega)]
  simp only [nsmul_eq_mul]
  ring

/-- Global modular formula: the entire cumulative divisor source minus its fixed drift. -/
theorem modular_eq_centered_divisor_sum {X M : ℕ} (hXM : X≤M) (n : ℕ) :
    modular X M n=(∑ k ∈ Finset.Icc 1 n, divisorSource X M k)-(n : ℝ)*harmonic X M := by
  rw [modular_eq_taper hXM,sum_divisorSource_eq_floor,harmonic_eq_taper hXM,
    Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 := (Finset.mem_Icc.mp hd).1
  rw [arithmeticCoeff,if_pos (Finset.mem_Icc.mp hd).2,natMod_div_eq_div_sub_natDiv n d hd1]
  ring

/-- Error increments include both the unit impulse and the complete harmonic drift. -/
def errorIncrement (X M k : ℕ) : ℝ :=
  (if k=1 then 1 else 0)-divisorSource X M k+harmonic X M

/-- The full coordinate error is the cumulative compensated divisor field. -/
theorem error_eq_cumulative {X M : ℕ} (hXM : X≤M) {n : ℕ} (hn : 1≤n) :
    1-modular X M n=∑ k ∈ Finset.Icc 1 n, errorIncrement X M k := by
  rw [modular_eq_centered_divisor_sum hXM]
  simp only [errorIncrement,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hi : (∑ k ∈ Finset.Icc 1 n, if k=1 then (1 : ℝ) else 0)=1 := by simp [hn]
  rw [hi]
  simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
  ring

private theorem raw_error_eq_signed_floorTail (N n : ℕ) (hn : 1≤n) :
    1-bdMobiusModularApproximant N n=
      (∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ))+
        (n : ℝ)*deningerHarmonicPartial N := by
  have hneg :
      (∑ d ∈ Finset.Icc 1 N,
        (-((moebius d : ℤ) : ℝ))*(((n%d : ℕ) : ℝ)/(d : ℝ)))=
        -(∑ d ∈ Finset.Icc 1 N,
          ((moebius d : ℤ) : ℝ)*(((n%d : ℕ) : ℝ)/(d : ℝ))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  calc
    1-bdMobiusModularApproximant N n=
        1-∑ d ∈ Finset.Icc 1 N,
          (-((moebius d : ℤ) : ℝ))*(((n%d : ℕ) : ℝ)/(d : ℝ)) := by
      rw [bdMobiusModularApproximant,hneg]
    _ = (∑ d ∈ Finset.Ioc N n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ))+
          (n : ℝ)*(∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ)/(d : ℝ)) :=
      moebius_residual_tail_form hn
    _ = _ := by rw [deningerHarmonicPartial_eq_sum_Icc]

/-- The averaged error keeps the complete signed omitted Möbius-floor tail at every cutoff.
No absolute-value or endpoint replacement occurs in this representation. -/
theorem error_eq_signed_floorTail_average {X M n : ℕ}
    (hX : 1≤X) (hXM : X<M) (hn : 1≤n) :
    1-modular X M n=
      ∑ j ∈ Finset.Ico X M, logWeight X M j*
        ((∑ d ∈ Finset.Ioc j n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ))+
          (n : ℝ)*deningerHarmonicPartial j) := by
  rw [error_eq_average hX hXM]
  apply Finset.sum_congr rfl
  intro j hj
  rw [raw_error_eq_signed_floorTail j n hn]

/-- Portion of the logarithmic cutoff average that remains after a modulus `d` enters its
omitted-floor tail. -/
def signedFloorTailRamp (X M d : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico X M, if j<d then logWeight X M j else 0

/-- Below the outer endpoint, the omitted-tail ramp is the complementary generator taper. -/
theorem signedFloorTailRamp_eq_one_sub_taper {X M d : ℕ}
    (hX : 1≤X) (hXM : X<M) (hdM : d≤M) :
    signedFloorTailRamp X M d=1-taper X M d := by
  have hsplit :
      (∑ j ∈ Finset.Ico X M, if j<d then logWeight X M j else 0)+
        (∑ j ∈ Finset.Ico X M, if d≤j then logWeight X M j else 0)=
          ∑ j ∈ Finset.Ico X M, logWeight X M j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjd : j<d
    · simp [hjd]
    · have hdj : d≤j := by omega
      simp [hjd,hdj]
  have hsuffix := logWeight_suffix (X := X) (M := M) (d := d) hXM.le hdM
  unfold signedFloorTailRamp
  linarith [hsplit,logWeight_sum hX hXM]

/-- Once a modulus lies beyond the outer endpoint, it has entered every omitted-floor tail. -/
theorem signedFloorTailRamp_eq_one_of_outer_le {X M d : ℕ}
    (hX : 1≤X) (hXM : X<M) (hMd : M≤d) :
    signedFloorTailRamp X M d=1 := by
  unfold signedFloorTailRamp
  calc
    (∑ j ∈ Finset.Ico X M, if j<d then logWeight X M j else 0)=
        ∑ j ∈ Finset.Ico X M, logWeight X M j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjM := (Finset.mem_Ico.mp hj).2
      simp [show j<d by omega]
    _ = 1 := logWeight_sum hX hXM

/-- The retained ramp resolves every omitted modulus before the outer cutoff: advancing the
modulus by one adds exactly that cutoff's positive logarithmic mass. -/
theorem signedFloorTailRamp_succ_sub {X M d : ℕ}
    (hXd : X≤d) (hdM : d<M) :
    signedFloorTailRamp X M (d+1)-signedFloorTailRamp X M d=logWeight X M d := by
  have hrestrict (e : ℕ) (hXe : X≤e) (heM : e≤M) :
      (∑ j ∈ Finset.Ico X M, if j<e then logWeight X M j else 0)=
        ∑ j ∈ Finset.Ico X e, logWeight X M j := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  unfold signedFloorTailRamp
  rw [hrestrict d hXd hdM.le,
    hrestrict (d+1) (by omega) (by omega),
    Finset.sum_Ico_succ_top hXd]
  ring

/-- A quotient-only transform cannot reproduce the EDQ ramp across a quotient collision.
Tatuzawa--Iseki inputs have precisely this quotient-only form, so its identity cannot replace
the retained ramped tail by a Chebyshev sum without a separate boundary term. -/
theorem signedFloorTailRamp_not_factor_through_natDiv
    {X M N d : ℕ} (hX : 1≤X) (hXM : X<M) (hXd : X≤d) (hdM : d<M)
    (hquot : N/d=N/(d+1)) :
    ¬ ∃ Q : ℕ → ℝ,
      Q (N/d)=signedFloorTailRamp X M d ∧
        Q (N/(d+1))=signedFloorTailRamp X M (d+1) := by
  rintro ⟨Q,hQd,hQsucc⟩
  have hramp : signedFloorTailRamp X M d=signedFloorTailRamp X M (d+1) := by
    calc signedFloorTailRamp X M d=Q (N/d) := hQd.symm
      _ = Q (N/(d+1)) := by rw [hquot]
      _ = signedFloorTailRamp X M (d+1) := hQsucc
  have hslope := signedFloorTailRamp_succ_sub hXd hdM
  have hpos := logWeight_pos hX hXM (Finset.mem_Ico.mpr ⟨hXd,hdM⟩)
  linarith

/-- Concrete quotient collision: `10/4 = 10/5`, while the EDQ ramp retains the distinct
fourth cutoff mass. -/
theorem signedFloorTailRamp_not_factor_through_natDiv_example :
    ¬ ∃ Q : ℕ → ℝ,
      Q (10/4)=signedFloorTailRamp 1 5 4 ∧
        Q (10/5)=signedFloorTailRamp 1 5 5 := by
  exact signedFloorTailRamp_not_factor_through_natDiv
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Reassembling all signed omitted-floor tails produces one ramped tail.  This is finite Fubini:
each omitted modulus retains its precise time of entry and no tail is estimated. -/
theorem signed_floorTail_average_eq_ramped {X M n : ℕ} :
    (∑ j ∈ Finset.Ico X M, logWeight X M j*
      (∑ d ∈ Finset.Ioc j n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ)))=
      ∑ d ∈ Finset.Ioc X n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ)*
        signedFloorTailRamp X M d := by
  have htail (j : ℕ) (hj : j∈Finset.Ico X M) :
      (∑ d ∈ Finset.Ioc j n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ))=
        ∑ d ∈ Finset.Ioc X n,
          if j<d then ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter,Finset.mem_Ioc]
    have hXj := (Finset.mem_Ico.mp hj).1
    omega
  calc
    (∑ j ∈ Finset.Ico X M, logWeight X M j*
      (∑ d ∈ Finset.Ioc j n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ)))=
        ∑ j ∈ Finset.Ico X M, logWeight X M j*
          (∑ d ∈ Finset.Ioc X n,
            if j<d then ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [htail j hj]
    _ = ∑ j ∈ Finset.Ico X M, ∑ d ∈ Finset.Ioc X n,
          if j<d then ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ)*logWeight X M j else 0 := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro d hd
      split <;> ring
    _ = ∑ d ∈ Finset.Ioc X n, ∑ j ∈ Finset.Ico X M,
          if j<d then ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ)*logWeight X M j else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Ioc X n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ)*
          signedFloorTailRamp X M d := by
      apply Finset.sum_congr rfl
      intro d hd
      unfold signedFloorTailRamp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split <;> ring

/-- Exact averaged EDQ error in terms of one signed ramped floor tail and the retained harmonic
drift.  A proof route must bound their cancellation without replacing either term by an endpoint
or an absolute-value majorant. -/
theorem error_eq_ramped_signed_floorTail_average {X M n : ℕ}
    (hX : 1≤X) (hXM : X<M) (hn : 1≤n) :
    1-modular X M n=
      (∑ d ∈ Finset.Ioc X n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ)*
        signedFloorTailRamp X M d)+
      ∑ j ∈ Finset.Ico X M, logWeight X M j*
        ((n : ℝ)*deningerHarmonicPartial j) := by
  calc
    1-modular X M n=
        ∑ j ∈ Finset.Ico X M, logWeight X M j*
          ((∑ d ∈ Finset.Ioc j n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ))+
            (n : ℝ)*deningerHarmonicPartial j) :=
      error_eq_signed_floorTail_average hX hXM hn
    _ = (∑ j ∈ Finset.Ico X M, logWeight X M j*
          (∑ d ∈ Finset.Ioc j n, ((moebius d : ℤ) : ℝ)*((n/d : ℕ) : ℝ)))+
        ∑ j ∈ Finset.Ico X M, logWeight X M j*
          ((n : ℝ)*deningerHarmonicPartial j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [signed_floorTail_average_eq_ramped]

/-- Exact finite cumulative energy at the modular carrier weight. -/
def cumulativeEnergy (c : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 T, (∑ j ∈ Finset.Icc 1 n, c j)^2/((n : ℝ)*((n : ℝ)+1))

/-- Covariance kernel induced by accumulation followed by the critical carrier weight. -/
def cumulativeKernel (T j k : ℕ) : ℝ :=
  1/(max j k : ℕ)-1/((T : ℝ)+1)

private theorem reciprocal_weight_sum {L T : ℕ} (hL : 1≤L) (hLT : L≤T) :
    (∑ n ∈ Finset.Icc L T, 1/((n : ℝ)*((n : ℝ)+1)))=1/(L : ℝ)-1/((T : ℝ)+1) := by
  have hterm (n : ℕ) (hn : n∈Finset.Icc L T) :
      1/((n : ℝ)*((n : ℝ)+1))=1/(n : ℝ)-1/((n+1 : ℕ) : ℝ) := by
    have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by have := (Finset.mem_Icc.mp hn).1; omega)
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm,
    show Finset.Icc L T=Finset.Ico L (T+1) by ext n; simp,
    Finset.sum_Ico_eq_sub _ (by omega),Finset.sum_range_sub' (fun n : ℕ => 1/(n : ℝ)) (T+1),
    Finset.sum_range_sub' (fun n : ℕ => 1/(n : ℝ)) L]
  push_cast
  ring

private theorem cumulativeKernel_eq_sum {T j k : ℕ} (hj : j∈Finset.Icc 1 T)
    (hk : k∈Finset.Icc 1 T) :
    cumulativeKernel T j k=∑ n ∈ Finset.Icc 1 T,
      if j≤n ∧ k≤n then 1/((n : ℝ)*((n : ℝ)+1)) else 0 := by
  rw [← Finset.sum_filter]
  have hset : (Finset.Icc 1 T).filter (fun n => j≤n ∧ k≤n)=Finset.Icc (max j k) T := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,max_le_iff]
    have := (Finset.mem_Icc.mp hj).1
    omega
  rw [hset,reciprocal_weight_sum (by have := (Finset.mem_Icc.mp hj).1; omega)
    (max_le (Finset.mem_Icc.mp hj).2 (Finset.mem_Icc.mp hk).2)]
  rfl

/-- Accumulation creates the exact maximum-index covariance, including every unequal pair. -/
theorem cumulativeEnergy_eq_covariance (c : ℕ → ℝ) (T : ℕ) :
    cumulativeEnergy c T=∑ j ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 T,
      c j*c k*cumulativeKernel T j k := by
  have hext (n : ℕ) (hn : n∈Finset.Icc 1 T) :
      (∑ j ∈ Finset.Icc 1 n, c j)=∑ j ∈ Finset.Icc 1 T, if j≤n then c j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter,Finset.mem_Icc]
    have := (Finset.mem_Icc.mp hn).2
    omega
  have hrow (n : ℕ) (hn : n∈Finset.Icc 1 T) :
      (∑ j ∈ Finset.Icc 1 n, c j)^2/((n : ℝ)*((n : ℝ)+1))=
        ∑ j ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 T,
          if j≤n ∧ k≤n then c j*c k/((n : ℝ)*((n : ℝ)+1)) else 0 := by
    rw [hext n hn,pow_two,Finset.sum_mul,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp_all
  rw [cumulativeEnergy,Finset.sum_congr rfl hrow,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [cumulativeKernel_eq_sum hj hk,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> ring

/-- The averaged target-error energy is precisely the compensated temporal covariance. -/
theorem errorEnergy_eq_covariance {X M : ℕ} (hXM : X≤M) (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, (1-modular X M n)^2/((n : ℝ)*((n : ℝ)+1)))=
      ∑ j ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 T,
        errorIncrement X M j*errorIncrement X M k*cumulativeKernel T j k := by
  rw [← cumulativeEnergy_eq_covariance]
  unfold cumulativeEnergy
  apply Finset.sum_congr rfl
  intro n hn
  rw [error_eq_cumulative hXM (Finset.mem_Icc.mp hn).1]


/-- Graham's corpus estimate controls the unsummed divisor coefficient energy. -/
theorem sum_sq_divisorSource_le {X M N : ℕ} (hX : 1≤X) (hXM : X<M) (hMN : M≤N) :
    (∑ k ∈ Finset.Icc 1 N, divisorSource X M k^2)≤
      2*((N : ℝ)*(4*coprimeLogMoebiusConst^2*(1+Real.log M))+((M : ℝ)*Real.log M)^2+
        ((N : ℝ)*(4*coprimeLogMoebiusConst^2*(1+Real.log X))+((X : ℝ)*Real.log X)^2))/
      (Real.log M-Real.log X)^2 := by
  have hM := sum_sq_barbanVehovCoeff_le (by omega : 1≤M) hMN
  have hX' := sum_sq_barbanVehovCoeff_le hX (hXM.le.trans hMN)
  simp_rw [divisorSource_eq_difference hX hXM,div_pow]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hterm : (∑ k ∈ Finset.Icc 1 N, (barbanVehovCoeff M k-barbanVehovCoeff X k)^2)≤
      ∑ k ∈ Finset.Icc 1 N, (2*barbanVehovCoeff M k^2+2*barbanVehovCoeff X k^2) := by
    apply Finset.sum_le_sum
    intro k hk
    nlinarith [sq_nonneg (barbanVehovCoeff M k+barbanVehovCoeff X k)]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum] at hterm
  linarith

/-- A finite averaged source is uniformly bounded over its entire coordinate path. -/
theorem abs_modular_le {X M : ℕ} (hX : 1≤X) (hXM : X<M) (n : ℕ) :
    |modular X M n|≤(M : ℝ) := by
  calc _ ≤ ∑ j ∈ Finset.Ico X M, |logWeight X M j*bdMobiusModularApproximant j n| :=
          Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ j ∈ Finset.Ico X M, logWeight X M j*(M : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul,abs_of_nonneg (logWeight_pos hX hXM hj).le]
          apply mul_le_mul_of_nonneg_left _ (logWeight_pos hX hXM hj).le
          exact (abs_bdMobiusModularApproximant_le j n).trans
            (by exact_mod_cast (Finset.mem_Ico.mp hj).2.le)
       _ = _ := by rw [← Finset.sum_mul,logWeight_sum hX hXM,one_mul]

private theorem abs_error_le {X M : ℕ} (hX : 1≤X) (hXM : X<M) (n : ℕ) :
    |1-modular X M n|≤(M : ℝ)+1 := by
  have h := (abs_sub (1 : ℝ) (modular X M n)).trans
    (add_le_add le_rfl (abs_modular_le hX hXM n))
  norm_num at h
  linarith

/-- Full target-error energy in the existing modular carrier, with no coordinate cutoff. -/
def fullErrorEnergy (X M : ℕ) : ℝ :=
  stepGram (fun n => 1-modular X M n) (fun n => 1-modular X M n)

/-- The full averaged error is genuinely square summable at each finite pair of cutoffs. -/
theorem hasSum_fullErrorEnergy {X M : ℕ} (hX : 1≤X) (hXM : X<M) :
    HasSum (fun j : ℕ => (1-modular X M (j+1))^2/(((j : ℝ)+1)*((j : ℝ)+2)))
      (fullErrorEnergy X M) := by
  simpa only [pow_two,fullErrorEnergy] using
    hasSum_stepGram (abs_error_le hX hXM) (abs_error_le hX hXM)

/-- The exact finite temporal covariance and the entire omitted tail partition full energy. -/
theorem fullErrorEnergy_eq_covariance_add_tail {X M : ℕ} (hX : 1≤X) (hXM : X<M) (T : ℕ) :
    fullErrorEnergy X M=
      (∑ j ∈ Finset.Icc 1 T, ∑ k ∈ Finset.Icc 1 T,
        errorIncrement X M j*errorIncrement X M k*cumulativeKernel T j k)+
      ∑' i : ℕ, (1-modular X M (i+T+1))^2/
        ((((i+T : ℕ) : ℝ)+1)*(((i+T : ℕ) : ℝ)+2)) := by
  let f : ℕ → ℝ := fun j => (1-modular X M (j+1))^2/(((j : ℝ)+1)*((j : ℝ)+2))
  have hsum : HasSum f (fullErrorEnergy X M) := hasSum_fullErrorEnergy hX hXM
  have hpref (L : ℕ) : (∑ i ∈ Finset.range L, f i)=
      ∑ n ∈ Finset.Icc 1 L, (1-modular X M n)^2/((n : ℝ)*((n : ℝ)+1)) := by
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]
      simp [f,Nat.cast_add,Nat.cast_one,add_assoc]
      ring
  rw [← hsum.tsum_eq,← hsum.summable.sum_add_tsum_nat_add T,hpref,
    errorEnergy_eq_covariance hXM.le]

end RHTower.DeletionAveragedDivisor
