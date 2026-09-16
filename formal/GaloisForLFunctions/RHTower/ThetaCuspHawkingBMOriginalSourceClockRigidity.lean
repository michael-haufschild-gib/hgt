import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCausalSourceMatching
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalGreenPoleMatchingNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFinitePhysicalClockStepCovarianceRigidity
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.Hurwitz.ExpIndependence

/-! Exact temporal clock of the original canonical source profile.
The source selects a quartic clock factor and two original moment coordinates.
At surviving critical sources no finite packet with a fixed linear readout
reproduces this profile. A source-derived quartic clock integral recovers the
complete canonical value; no PDE-flow conjugacy or extinction selector is asserted. -/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMJointSource D4BMModularCore
noncomputable section
set_option autoImplicit false

def sourceClockConstant (q : XiZeroCopy) (br side : Bool) (a : ℂ) : ℂ :=
  let mu := physicalAngularParameter q^2-1/4;
  -mu*physicalSelfSourceCoefficient q*
    ((mu-2)*fundamentalSourceTortoiseMoment (physicalFundamentalFrequency q side)
      (physicalRate q br) a+
      fundamentalSourceForcingMoment (physicalFundamentalFrequency q side) (physicalRate q br) a)

def sourceClockSlope (q : XiZeroCopy) (br side : Bool) (a : ℂ) : ℂ :=
  let mu := physicalAngularParameter q^2-1/4
  mu*physicalSelfSourceCoefficient q*(mu-2)*
    fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q br) a

def sourceClockCompanion (q : XiZeroCopy) (br side : Bool) (a : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (2*physicalRate q br*(u:ℂ))*sourceClockSlope q br side a

/-- The complete original finite-part source is a first-order frequency jet,
with its unchanged smooth onset and all three source moments retained. -/
theorem canonicalCausalSourceProfile_normal_form (q : XiZeroCopy) (br side : Bool)
    (a : ℂ) (u : ℝ) :
    canonicalCausalSourceProfile q br side a u =
      (Real.smoothTransition u:ℂ)*Complex.exp (2*physicalRate q br*(u:ℂ))*
        (sourceClockConstant q br side a+(u:ℂ)*sourceClockSlope q br side a) := by
  unfold canonicalCausalSourceProfile sourceClockConstant sourceClockSlope
  ring

theorem canonicalCausalSourceProfile_late (q : XiZeroCopy) (br side : Bool)
    (a : ℂ) (u : ℝ) (hu : 1≤u) :
    canonicalCausalSourceProfile q br side a u =
      Complex.exp (2*physicalRate q br*(u:ℂ))*
        (sourceClockConstant q br side a+(u:ℂ)*sourceClockSlope q br side a) := by
  rw [canonicalCausalSourceProfile_normal_form,Real.smoothTransition.one_of_one_le hu]
  simp only [Complex.ofReal_one,one_mul]

private theorem sourceExp_add (s : ℂ) (u T : ℝ) :
    Complex.exp (2*s*((u+T:ℝ):ℂ))=
      Complex.exp (2*s*(T:ℂ))*Complex.exp (2*s*(u:ℂ)) := by
  rw [Complex.ofReal_add,mul_add,Complex.exp_add,mul_comm]

/-- Exact clock on the original two source coordinates. The second coordinate
is the original radial moment, not a freely supplied correction. -/
theorem sourceClock_translation (q : XiZeroCopy) (br side : Bool) (a : ℂ)
    (u T : ℝ) (hu : 1≤u) (hT : 0≤T) :
    canonicalCausalSourceProfile q br side a (u+T)=
      Complex.exp (2*physicalRate q br*(T:ℂ))*
        (canonicalCausalSourceProfile q br side a u+(T:ℂ)*sourceClockCompanion q br side a u) ∧
    sourceClockCompanion q br side a (u+T)=
      Complex.exp (2*physicalRate q br*(T:ℂ))*sourceClockCompanion q br side a u := by
  rw [canonicalCausalSourceProfile_late q br side a (u+T) (by linarith),
    canonicalCausalSourceProfile_late q br side a u hu]
  simp only [sourceClockCompanion]
  simp only [sourceExp_add]
  simp only [Complex.ofReal_add]
  constructor <;> ring

/-- The exact two-step determinant measures the source information that a
single clock character would discard. -/
theorem sourceClock_two_step_determinant (q : XiZeroCopy) (br side : Bool) (a : ℂ)
    (u T : ℝ) (hu : 1≤u) (hT : 0≤T) :
    canonicalCausalSourceProfile q br side a u*canonicalCausalSourceProfile q br side a (u+2*T)-
      canonicalCausalSourceProfile q br side a (u+T)^2 =
        -(T:ℂ)^2*sourceClockCompanion q br side a (u+T)^2 := by
  obtain ⟨h1,g1⟩ := sourceClock_translation q br side a u T hu hT
  have h2 := (sourceClock_translation q br side a (u+T) T (by linarith) hT).1
  rw [show u+2*T=(u+T)+T by ring,h2,h1,g1]
  ring

theorem sourceClock_two_step_determinant_ne_zero (q : XiZeroCopy) (br side : Bool)
    (a : ℂ) (hB : sourceClockSlope q br side a≠0)
    (u T : ℝ) (hu : 1≤u) (hT : 0<T) :
    canonicalCausalSourceProfile q br side a u*canonicalCausalSourceProfile q br side a (u+2*T)-
      canonicalCausalSourceProfile q br side a (u+T)^2 ≠ 0 := by
  rw [sourceClock_two_step_determinant q br side a u T hu hT.le]
  exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hT.ne')))
    (pow_ne_zero 2 (mul_ne_zero (Complex.exp_ne_zero _) hB))

/-- Two late observations recover the original radial-moment clock coordinate. -/
theorem sourceClockCompanion_recovery (q : XiZeroCopy) (br side : Bool) (a : ℂ)
    (u T : ℝ) (hu : 1≤u) (hT : 0<T) :
    sourceClockCompanion q br side a u =
      (Complex.exp (-(2*physicalRate q br*(T:ℂ)))*
        canonicalCausalSourceProfile q br side a (u+T)-canonicalCausalSourceProfile q br side a u)/(T:ℂ) := by
  rw [(sourceClock_translation q br side a u T hu hT.le).1,
    ← mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,one_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hT.ne']
  ring

/-- A scalar clock, with arbitrary multiplier, represents every late source
step exactly if and only if the original radial-moment coordinate vanishes. -/
theorem sourceClock_scalar_realization_iff (q : XiZeroCopy) (br side : Bool)
    (a : ℂ) (T : ℝ) (hT : 0<T) :
    (∃ c : ℂ, ∀ u : ℝ, 1≤u →
      canonicalCausalSourceProfile q br side a (u+T)=c*canonicalCausalSourceProfile q br side a u) ↔
      sourceClockSlope q br side a=0 := by
  constructor
  · rintro ⟨c,hc⟩
    by_contra hB
    have hn := sourceClock_two_step_determinant_ne_zero q br side a hB 1 T le_rfl hT
    apply hn
    rw [show (1:ℝ)+2*T=(1+T)+T by ring,hc (1+T) (by linarith),hc 1 le_rfl]
    ring
  · intro hB
    refine ⟨Complex.exp (2*physicalRate q br*(T:ℂ)),?_⟩
    intro u hu
    simpa only [sourceClockCompanion,hB,mul_zero,add_zero] using
      (sourceClock_translation q br side a u T hu hT.le).1

/-- Finite-time extinction of this original profile is equivalent to both
original moment coordinates being zero; there is no nonzero transient tail. -/
theorem sourceClock_eventual_zero_iff (q : XiZeroCopy) (br side : Bool) (a : ℂ) :
    (∃ U : ℝ, ∀ u : ℝ, U≤u → canonicalCausalSourceProfile q br side a u=0) ↔
      sourceClockConstant q br side a=0 ∧ sourceClockSlope q br side a=0 := by
  constructor
  · rintro ⟨U,hU⟩
    let u := max U 1
    have hu : 1≤u := le_max_right _ _
    have huU : U≤u := le_max_left _ _
    have h0 := hU u huU
    have h1 := hU (u+1) (by linarith)
    rw [canonicalCausalSourceProfile_late q br side a u hu] at h0
    rw [canonicalCausalSourceProfile_late q br side a (u+1) (by linarith)] at h1
    have h0' := (mul_eq_zero.mp h0).resolve_left (Complex.exp_ne_zero _)
    have h1' := (mul_eq_zero.mp h1).resolve_left (Complex.exp_ne_zero _)
    have hB : sourceClockSlope q br side a=0 := by
      push_cast at h1'
      linear_combination h1'-h0'
    exact ⟨by simpa only [hB,mul_zero,add_zero] using h0',hB⟩
  · rintro ⟨hA,hB⟩
    refine ⟨0,fun u _ => ?_⟩
    rw [canonicalCausalSourceProfile_normal_form,hA,hB,mul_zero,add_zero,mul_zero]

private theorem finite_exponential_affine_slope_zero {ι : Type*}
    (S : Finset ι) (beta c : ι→ℂ) (A B : ℂ)
    (h : ∀ z : ℂ, ∑ i∈S, c i*Complex.exp (beta i*z)=A+z*B) : B=0 := by
  classical
  induction S using Finset.induction_on generalizing c A B with
  | empty =>
    have h0 := h 0
    have h1 := h 1
    simp only [Finset.sum_empty,zero_mul,add_zero,one_mul] at h0 h1
    linear_combination h0-h1
  | @insert j S hj ih =>
    by_cases hj0 : beta j=0
    · apply ih c (A-c j) B
      intro z
      have hz := h z
      rw [Finset.sum_insert hj,hj0,zero_mul,Complex.exp_zero,mul_one] at hz
      linear_combination hz
    · have hd (z : ℂ) : ∑ i∈insert j S, c i*(beta i*Complex.exp (beta i*z))=B := by
        have hf : HasDerivAt (fun z : ℂ => ∑ i∈insert j S, c i*Complex.exp (beta i*z))
            (∑ i∈insert j S, c i*(beta i*Complex.exp (beta i*z))) z := by
          apply HasDerivAt.fun_sum
          intro i _
          exact (HurwitzExp.hasDerivAt_expLin (beta i) z).const_mul (c i)
        have he : (fun z : ℂ => ∑ i∈insert j S, c i*Complex.exp (beta i*z))=
            (fun z : ℂ => A+z*B) := funext h
        rw [he] at hf
        have hr : HasDerivAt (fun z : ℂ => A+z*B) B z := by
          simpa only [one_mul,id_eq] using ((hasDerivAt_id z).mul_const B).const_add A
        exact hf.unique hr
      have hz (z : ℂ) :
          ∑ i∈S, (c i*(beta i-beta j))*Complex.exp (beta i*z)=
            (B-beta j*A)+z*(-beta j*B) := by
        have hs : (∑ i∈S, (c i*(beta i-beta j))*Complex.exp (beta i*z))=
            (∑ i∈S, c i*(beta i*Complex.exp (beta i*z)))-
              beta j*(∑ i∈S, c i*Complex.exp (beta i*z)) := by
          rw [Finset.mul_sum,← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hs]
        have hsub := congrArg₂ (fun x y : ℂ => x-beta j*y) (hd z) (h z)
        simp only [Finset.sum_insert hj] at hsub
        linear_combination hsub
      have hB := ih (fun i => c i*(beta i-beta j)) (B-beta j*A) (-beta j*B) hz
      exact (mul_eq_zero.mp hB).resolve_left (neg_ne_zero.mpr hj0)

/-- Arbitrary finite sums of scalar clock modes cannot carry the nonzero
original frequency-jet coordinate, even when frequencies repeat. -/
theorem sourceClockSlope_eq_zero_of_finite_exponentials (q : XiZeroCopy) (br side : Bool)
    (a : ℂ) {ι : Type*} (S : Finset ι) (beta c : ι→ℂ)
    (h : ∀ u : ℝ, 1≤u → canonicalCausalSourceProfile q br side a u=
      ∑ i∈S, c i*Complex.exp (beta i*(u:ℂ))) : sourceClockSlope q br side a=0 := by
  let r := 2*physicalRate q br
  let A := sourceClockConstant q br side a
  let B := sourceClockSlope q br side a
  let G : ℂ→ℂ := fun z =>
    (∑ i∈S, c i*Complex.exp ((beta i-r)*z))-(A+z*B)
  have hG : Differentiable ℂ G := by
    dsimp only [G]
    fun_prop
  have hreal (u : ℝ) (hu : 1≤u) : G (u:ℂ)=0 := by
    have hu' := h u hu
    rw [canonicalCausalSourceProfile_late q br side a u hu] at hu'
    have he := congrArg (fun v : ℂ => Complex.exp (-r*(u:ℂ))*v) hu'
    have hs : (∑ i∈S, c i*Complex.exp ((beta i-r)*(u:ℂ)))=
        Complex.exp (-r*(u:ℂ))*(∑ i∈S, c i*Complex.exp (beta i*(u:ℂ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [show (beta i-r)*(u:ℂ)=(-r*(u:ℂ))+(beta i*(u:ℂ)) by ring,Complex.exp_add]
      ring
    change (∑ i∈S, c i*Complex.exp ((beta i-r)*(u:ℂ)))-(A+(u:ℂ)*B)=0
    rw [hs,← he]
    change Complex.exp (-r*(u:ℂ))*(Complex.exp (r*(u:ℂ))*(A+(u:ℂ)*B))-(A+(u:ℂ)*B)=0
    rw [← mul_assoc,← Complex.exp_add,show -r*(u:ℂ)+r*(u:ℂ)=0 by ring,
      Complex.exp_zero,one_mul,sub_self]
  have hae : ∀ᵐ u : ℝ ∂(volume.restrict (Ioo ((2:ℝ)-1) (2+1))), G (u:ℂ)=0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact hreal u (by linarith [hu.1])
  have hg (z : ℂ) : G z=0 :=
    GaloisForLFunctions.HTGeometry.entire_eq_zero_of_ae_vanishing_on_real_interval hG
      (by norm_num : (0:ℝ)<1) hae z
  apply finite_exponential_affine_slope_zero S (fun i => beta i-r) c A B
  intro z
  exact sub_eq_zero.mp (hg z)

private theorem physical_source_clock_factors_ne_zero (q : XiZeroCopy) :
    physicalAngularParameter q^2-1/4≠0 ∧ physicalAngularParameter q^2-1/4-2≠0 := by
  have hn (c : ℝ) : (q.1:ℂ)-(c:ℂ)≠0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    exact xi_divisor_support_im_ne_zero q.1 hi
  have h0 : physicalAngularParameter q^2-1/4=((q.1:ℂ)-0)*((q.1:ℂ)-2)/4 := by
    rw [physicalAngularParameter_eq]
    ring
  have h2 : physicalAngularParameter q^2-1/4-2=((q.1:ℂ)-4)*((q.1:ℂ)-(-2))/4 := by
    rw [physicalAngularParameter_eq]
    ring
  constructor
  · rw [h0]
    exact div_ne_zero (mul_ne_zero (hn 0) (hn 2)) (by norm_num)
  · rw [h2]
    exact div_ne_zero (mul_ne_zero (hn 4) (by simpa using hn (-2))) (by norm_num)

/-- A genuine original physical pole forces the second temporal source
coordinate to survive at every nonzero original amplitude. -/
theorem sourceClockSlope_ne_zero_of_physicalPole (q : XiZeroCopy)
    (hR : physicalSelfResidueCoefficient q true true 1 (-1)≠0)
    (a : ℂ) (ha : a≠0) : sourceClockSlope q true true a≠0 := by
  have hu : ¬ ∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q true w 1 (-1))
      (𝓝[≠] physicalFundamentalFrequency q true) (𝓝 c) := by
    rw [continuedPhysicalSelfResponse_finite_limit_iff q true true 1 (-1) (by norm_num)]
    exact hR
  obtain ⟨hC,hM,hO⟩ := (continuedPhysicalSelfResponse_nonremovable_iff_moment q true true 1 (-1)
    (by norm_num)).mp hu
  obtain ⟨hm,hm2⟩ := physical_source_clock_factors_ne_zero q
  unfold sourceClockSlope
  apply mul_ne_zero (mul_ne_zero (mul_ne_zero hm hC) hm2)
  rw [physicalFundamentalSourceMoment_amplitude]
  exact mul_ne_zero (pow_ne_zero 2 ha) hM

private theorem physicalClock_linear_readout (n : ℕ) (x : HBXiPeierlsPacket)
    (L : HBXiPeierlsPacket→ₗ[ℂ] ℂ) (u : ℝ) :
    L (hbXiPeierlsCenteredQNMPhysicalClockStep n u x)=
      ∑ k∈x.support, (x k*L (Finsupp.single k 1))*
        Complex.exp ((-Complex.I*hbXiPeierlsCenteredQNMFrequency n k)*(u:ℂ)) := by
  classical
  conv_lhs => rw [← Finsupp.sum_single x]
  simp only [Finsupp.sum,map_sum,hbXiPeierlsCenteredQNMPhysicalClockStep_single]
  apply Finset.sum_congr rfl
  intro k _
  have hs (b : ℂ) : Finsupp.single k b=b • (Finsupp.single k (1:ℂ)) := by simp
  rw [hs,map_smul]
  simp only [smul_eq_mul]
  rw [show -Complex.I*(u:ℂ)*hbXiPeierlsCenteredQNMFrequency n k=
    (-Complex.I*hbXiPeierlsCenteredQNMFrequency n k)*(u:ℂ) by ring]
  ring

/-- Even arbitrary finite packet encoding and arbitrary time-independent
linear reading of the unchanged physical clock cannot reproduce this source
profile. The obstruction is its surviving frequency jet, not packet erasure. -/
theorem not_exists_sourceClock_finitePacket_realization (q : XiZeroCopy)
    (hR : physicalSelfResidueCoefficient q true true 1 (-1)≠0)
    (a : ℂ) (ha : a≠0) (n : ℕ) :
    ¬ ∃ x : HBXiPeierlsPacket, ∃ L : HBXiPeierlsPacket→ₗ[ℂ] ℂ,
      ∀ u : ℝ, 1≤u → L (hbXiPeierlsCenteredQNMPhysicalClockStep n u x)=
        canonicalCausalSourceProfile q true true a u := by
  rintro ⟨x,L,h⟩
  apply sourceClockSlope_ne_zero_of_physicalPole q hR a ha
  apply sourceClockSlope_eq_zero_of_finite_exponentials q true true a x.support
    (fun k => -Complex.I*hbXiPeierlsCenteredQNMFrequency n k)
    (fun k => x k*L (Finsupp.single k 1))
  intro u hu
  rw [← h u hu,physicalClock_linear_readout]

/-- An actual critical Xi source admits neither a scalar late clock nor
finite-time extinction of the complete original source profile. -/
theorem exists_critical_sourceClock_obstruction :
    ∃ q : XiZeroCopy, (q.1:ℂ).re=1/2 ∧ ∀ a : ℂ, a≠0 →
      (∀ T : ℝ, 0<T → ¬ ∃ c : ℂ, ∀ u : ℝ, 1≤u →
        canonicalCausalSourceProfile q true true a (u+T)=c*canonicalCausalSourceProfile q true true a u) ∧
      ¬ ∃ U : ℝ, ∀ u : ℝ, U≤u → canonicalCausalSourceProfile q true true a u=0 := by
  obtain ⟨q,hq,hR⟩ := exists_critical_physicalPole_ne_zero
  refine ⟨q,hq,fun a ha => ?_⟩
  have hB := sourceClockSlope_ne_zero_of_physicalPole q hR a ha
  exact ⟨fun T hT h => hB ((sourceClock_scalar_realization_iff q true true a T hT).mp h),
    fun h => hB ((sourceClock_eventual_zero_iff q true true a).mp h).2⟩

/-- Unconditional failure of complete temporal matching through any finite
packet and fixed linear readout of the prescribed physical clock. -/
theorem exists_critical_finitePacket_clock_obstruction :
    ∃ q : XiZeroCopy, (q.1:ℂ).re=1/2 ∧ ∀ a : ℂ, a≠0 → ∀ n : ℕ,
      ¬ ∃ x : HBXiPeierlsPacket, ∃ L : HBXiPeierlsPacket→ₗ[ℂ] ℂ,
        ∀ u : ℝ, 1≤u → L (hbXiPeierlsCenteredQNMPhysicalClockStep n u x)=
          canonicalCausalSourceProfile q true true a u := by
  obtain ⟨q,hq,hR⟩ := exists_critical_physicalPole_ne_zero
  exact ⟨q,hq,fun a ha n => not_exists_sourceClock_finitePacket_realization q hR a ha n⟩

/-- The original doubled source rate is a fourth harmonic of the centered
physical clock, with the same fixed redshift on both source branches. -/
theorem physicalRate_fourfold_clock (q : XiZeroCopy) (br : Bool) (n : ℕ) :
    2*physicalRate q br = -3+4*(-Complex.I*hbXiPeierlsCenteredQNMFrequency n
      (if br then xiZeroCopyReflectEquiv q else q)) := by
  cases br with
  | false =>
    change 2*(-(q.1:ℂ)-1) = -3+4*(-Complex.I*hbXiPeierlsCenteredQNMFrequency n q)
    rw [hbXiPeierlsCenteredQNMFrequency_eq]
    dsimp only [xiSpectralPoint]
    ring_nf
    simp only [Complex.I_sq]
    ring
  | true =>
    change 2*((q.1:ℂ)-2) = -3+4*(-Complex.I*hbXiPeierlsCenteredQNMFrequency n (xiZeroCopyReflectEquiv q))
    rw [hbXiPeierlsCenteredQNMFrequency_reflect,hbXiPeierlsCenteredQNMFrequency_eq]
    dsimp only [xiSpectralPoint]
    ring_nf
    simp only [Complex.I_sq]
    ring

theorem physicalSourceExp_fourfold_clock (q : XiZeroCopy) (br : Bool) (n : ℕ) (u : ℝ) :
    Complex.exp (2*physicalRate q br*(u:ℂ)) =
      Complex.exp (-3*(u:ℂ))*
        (hbXiPeierlsCenteredQNMPhysicalClockStep n u
          (Finsupp.single (if br then xiZeroCopyReflectEquiv q else q) 1)
          (if br then xiZeroCopyReflectEquiv q else q))^4 := by
  rw [hbXiPeierlsCenteredQNMPhysicalClockStep_apply,Finsupp.single_eq_same,mul_one,
    ← Complex.exp_nat_mul,← Complex.exp_add]
  congr 1
  rw [physicalRate_fourfold_clock q br n]
  push_cast
  ring

/-- Exact positive temporal matching at the unchanged physical clock time:
the original source selects a quartic clock observation and its first time
moment. No coefficient is fitted to a desired zero locus. -/
theorem canonicalCausalSourceProfile_physicalClock (q : XiZeroCopy) (br side : Bool)
    (a : ℂ) (n : ℕ) (u : ℝ) :
    canonicalCausalSourceProfile q br side a u =
      (Real.smoothTransition u:ℂ)*Complex.exp (-3*(u:ℂ))*
        (hbXiPeierlsCenteredQNMPhysicalClockStep n u
          (Finsupp.single (if br then xiZeroCopyReflectEquiv q else q) 1)
          (if br then xiZeroCopyReflectEquiv q else q))^4*
        (sourceClockConstant q br side a+(u:ℂ)*sourceClockSlope q br side a) := by
  rw [canonicalCausalSourceProfile_normal_form,physicalSourceExp_fourfold_clock q br n u]
  ring

/-- The complete canonical temporal/metric/QNM value is the convergent
integral of this source-selected quartic physical-clock observation. -/
theorem canonicalQNMValue_physicalClock_integral (q : XiZeroCopy) (br side : Bool)
    (a : ℂ) (n : ℕ) :
    let f := fun u : ℝ =>
      Complex.exp (-physicalFundamentalFrequency q side*(u:ℂ))*
        ((Real.smoothTransition u:ℂ)*Complex.exp (-3*(u:ℂ))*
          (hbXiPeierlsCenteredQNMPhysicalClockStep n u
            (Finsupp.single (if br then xiZeroCopyReflectEquiv q else q) 1)
            (if br then xiZeroCopyReflectEquiv q else q))^4*
          (sourceClockConstant q br side a+(u:ℂ)*sourceClockSlope q br side a));
    IntegrableOn f (Ioi 0) ∧
      (∫ u in Ioi (0:ℝ), f u)=D4BMOriginalCanonicalAction.canonicalQNMValue q br side a := by
  have h := canonicalCausalSourceProfile_laplace q br side a
  simp_rw [canonicalCausalSourceProfile_physicalClock q br side a n] at h
  exact h


end
end RHTower.D4BMOriginalSourceResolvent
