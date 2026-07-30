import GaloisForLFunctions.HTGeometry.PrimeLogGibbsJointLimit
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn

/-!
# Joint compact-open and holomorphic-jet limit of prime-log Gibbs responses

[BRIDGE] A spectral gap suppresses thermal reverse transitions uniformly at low temperature.
For the prime-log Hamiltonians the gap is the subsystem-independent value `log 2`.  On a closed
upper strip `η ≤ Im z`, causality gives the uniform resolvent bound `1 / η`.  Consequently the
simultaneous cold and thermodynamic limit is locally uniform, not merely pointwise.

The compact-open upgrade is directly consumed by the existing holomorphic jet machinery: every
response derivative converges in the same simultaneous product-directed limit.
-/

open scoped BigOperators
open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The total prime mass is nonnegative. -/
theorem primeDyadicTotalMass_nonneg (u : Nat.Primes → ℝ) :
    0 ≤ primeDyadicTotalMass u :=
  tsum_nonneg fun _ => norm_nonneg _

/-- Uniform form of the Boltzmann error bound on a closed upper strip. -/
theorem finitePrimeLogHermitianGibbsCarrier_sub_bound_of_im_ge
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (C : ℝ)
    (hu : ∀ p, u p ≤ C) (β : ℝ) (hβ : 0 ≤ β)
    {η : ℝ} (hη : 0 < η) (z : ℂ) (hz : η ≤ z.im) :
    ‖finitePrimeLogHermitianGibbsCarrier P u β z -
        finitePrimeLogHerglotz P u z‖ ≤
      Real.exp (-β * Real.log 2) * η⁻¹ * primeDyadicTotalMass u := by
  have hzim : 0 < z.im := hη.trans_le hz
  have hinv : (z.im)⁻¹ ≤ η⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hη hz
  exact (finitePrimeLogHermitianGibbsCarrier_sub_bound P u C hu β hβ z hzim).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le)
      (primeDyadicTotalMass_nonneg u))

/-- The reverse-transition error tends uniformly to zero on every closed upper strip. -/
theorem finitePrimeLogHermitianGibbsCarrier_sub_tendstoUniformlyOn_upperStrip
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    {η : ℝ} (hη : 0 < η) :
    TendstoUniformlyOn
      (fun x : Finset Nat.Primes × ℝ => fun z =>
        finitePrimeLogHermitianGibbsCarrier x.1 u x.2 z -
          finitePrimeLogHerglotz x.1 u z)
      (fun _ => 0) Filter.atTop {z : ℂ | η ≤ z.im} := by
  let B : ℝ := η⁻¹ * primeDyadicTotalMass u
  have hlim : Filter.Tendsto
      (fun β : ℝ => Real.exp (-β * Real.log 2) * B)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_exp_neg_mul_log_two_atTop.mul_const B
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ β : ℝ in Filter.atTop,
      Real.exp (-β * Real.log 2) * B < ε :=
    hlim.eventually (gt_mem_nhds hε)
  have hβ : ∀ᶠ β : ℝ in Filter.atTop, 0 ≤ β :=
    eventually_ge_atTop 0
  rw [← Filter.prod_atTop_atTop_eq]
  filter_upwards [(hβ.and hsmall).prod_inr
    (Filter.atTop : Filter (Finset Nat.Primes))] with x hx
  intro z hz
  simp only [dist_zero_left]
  exact (finitePrimeLogHermitianGibbsCarrier_sub_bound_of_im_ge
    x.1 u C hu x.2 hx.1 hη z hz).trans_lt
      (by simpa [B, mul_assoc] using hx.2)

/-- Every finite Hermitian Gibbs carrier is holomorphic on the upper half-plane. -/
theorem differentiableOn_finitePrimeLogHermitianGibbsCarrier_upperHalfPlane
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) :
    DifferentiableOn ℂ (finitePrimeLogHermitianGibbsCarrier P u β)
      upperHalfPlane := by
  intro z hz
  change 0 < z.im at hz
  apply DifferentiableAt.differentiableWithinAt
  unfold finitePrimeLogHermitianGibbsCarrier
  apply DifferentiableAt.fun_sum
  intro p hp
  have hminus : (primeLogSupport p : ℂ) - z ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp at him
    linarith
  have hplus : (primeLogSupport p : ℂ) + z ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp at him
    linarith
  exact (differentiableAt_const (c := (primeDyadicWeight u p : ℂ))).mul
    ((((differentiableAt_const (c := (primeLogSupport p : ℂ))).sub
      differentiableAt_id).inv hminus).sub
      ((differentiableAt_const
        (c := (Real.exp (-β * primeLogSupport p) : ℂ))).mul
        (((differentiableAt_const (c := (primeLogSupport p : ℂ))).add
          differentiableAt_id).inv hplus)))

/-- The reverse-transition error tends locally uniformly to zero on the upper half-plane. -/
theorem finitePrimeLogHermitianGibbsCarrier_sub_tendstoLocallyUniformlyOn
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    TendstoLocallyUniformlyOn
      (fun x : Finset Nat.Primes × ℝ => fun z =>
        finitePrimeLogHermitianGibbsCarrier x.1 u x.2 z -
          finitePrimeLogHerglotz x.1 u z)
      (fun _ => 0) Filter.atTop upperHalfPlane := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  change 0 < z.im at hz
  let η : ℝ := z.im / 2
  let t : Set ℂ := {w | η < w.im}
  have hη : 0 < η := half_pos hz
  have htOpen : IsOpen t := isOpen_lt continuous_const Complex.continuous_im
  have hzt : z ∈ t := by
    change z.im / 2 < z.im
    linarith
  refine ⟨t, Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (htOpen.mem_nhds hzt), ?_⟩
  exact (finitePrimeLogHermitianGibbsCarrier_sub_tendstoUniformlyOn_upperStrip
    u C hu hη).mono fun w hw => by
      simpa only [Set.mem_setOf_eq] using hw.le

/-- **Joint compact-open Gibbs limit.**  Cooling and thermodynamic enlargement may occur
simultaneously, and convergence is locally uniform throughout the upper half-plane. -/
theorem finitePrimeLogHermitianGibbsCarrier_tendstoLocallyUniformlyOn_joint
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    TendstoLocallyUniformlyOn
      (fun x : Finset Nat.Primes × ℝ =>
        finitePrimeLogHermitianGibbsCarrier x.1 u x.2)
      (primeLogHerglotz u) Filter.atTop upperHalfPlane := by
  have herror :=
    finitePrimeLogHermitianGibbsCarrier_sub_tendstoLocallyUniformlyOn u C hu
  have hfiniteBase :=
    finitePrimeLogHerglotz_tendstoLocallyUniformlyOn_primeLogHerglotz u C hu
  have hfinite : TendstoLocallyUniformlyOn
      (fun x : Finset Nat.Primes × ℝ => finitePrimeLogHerglotz x.1 u)
      (primeLogHerglotz u) Filter.atTop upperHalfPlane := by
    intro V hV z hz
    obtain ⟨t, ht, hev⟩ := hfiniteBase V hV z hz
    refine ⟨t, ht, ?_⟩
    rw [← Filter.prod_atTop_atTop_eq]
    exact hev.prod_inl (Filter.atTop : Filter ℝ)
  have hadd := herror.add hfinite
  have hshape : TendstoLocallyUniformlyOn
      (fun x : Finset Nat.Primes × ℝ =>
        finitePrimeLogHermitianGibbsCarrier x.1 u x.2)
      ((fun _ => 0) + primeLogHerglotz u)
      Filter.atTop upperHalfPlane := by
    apply hadd.congr
    intro x z hz
    simp only [Pi.add_apply, sub_add_cancel]
  exact hshape.congr_right fun z hz => by
    simp only [Pi.add_apply, zero_add]

/-- The exact finite Hermitian Gibbs responses converge jointly in the compact-open topology. -/
theorem finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    TendstoLocallyUniformlyOn
      (fun x : Finset Nat.Primes × ℝ => fun z =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteGibbsTransitionIntensity x.2
            (primeLogKMSFiniteEnergy x.1)
            (primeLogGibbsFiniteHermitianAmplitude x.1 u x.2))
          (primeLogKMSFiniteEnergy x.1) z)
      (primeLogHerglotz u) Filter.atTop upperHalfPlane := by
  simpa only [neg_finiteGibbsResponse_primeLogGibbsFiniteHermitianAmplitude] using
    finitePrimeLogHermitianGibbsCarrier_tendstoLocallyUniformlyOn_joint u C hu

/-- Every holomorphic derivative of the finite Gibbs carrier converges in the simultaneous
cold/thermodynamic limit. -/
theorem iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_tendsto_joint
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (j : ℕ) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    Filter.Tendsto
      (fun x : Finset Nat.Primes × ℝ =>
        iteratedDeriv j (finitePrimeLogHermitianGibbsCarrier x.1 u x.2) z)
      Filter.atTop (nhds (iteratedDeriv j (primeLogHerglotz u) z)) := by
  exact GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
    isOpen_upperHalfPlane
    (finitePrimeLogHermitianGibbsCarrier_tendstoLocallyUniformlyOn_joint u C hu)
    (Filter.Eventually.of_forall fun x =>
      differentiableOn_finitePrimeLogHermitianGibbsCarrier_upperHalfPlane x.1 u x.2)
    j hz

/-- Every holomorphic susceptibility jet of the exact finite Hermitian Gibbs response converges
in the same simultaneous limit. -/
theorem iteratedDeriv_finiteHermitianGibbsResponse_tendsto_joint
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (j : ℕ) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    Filter.Tendsto
      (fun x : Finset Nat.Primes × ℝ =>
        iteratedDeriv j
          (fun w => -_root_.HTGeometry.finiteTransitionPassiveResponse
            (_root_.HTGeometry.finiteGibbsTransitionIntensity x.2
              (primeLogKMSFiniteEnergy x.1)
              (primeLogGibbsFiniteHermitianAmplitude x.1 u x.2))
            (primeLogKMSFiniteEnergy x.1) w) z)
      Filter.atTop (nhds (iteratedDeriv j (primeLogHerglotz u) z)) := by
  simpa only [neg_finiteGibbsResponse_primeLogGibbsFiniteHermitianAmplitude] using
    iteratedDeriv_finitePrimeLogHermitianGibbsCarrier_tendsto_joint u C hu j hz

/-- Universal-gauge compact-open specialization. -/
theorem universalFacetOrbitGauge_finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint :
    TendstoLocallyUniformlyOn
      (fun x : Finset Nat.Primes × ℝ => fun z =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteGibbsTransitionIntensity x.2
            (primeLogKMSFiniteEnergy x.1)
            (primeLogGibbsFiniteHermitianAmplitude x.1
              (fun q => universalFacetOrbitGauge q) x.2))
          (primeLogKMSFiniteEnergy x.1) z)
      (primeLogHerglotz (fun q => universalFacetOrbitGauge q))
      Filter.atTop upperHalfPlane :=
  finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q))

/-- Compact-open Hermitian Gibbs selection property for the universal prime orientation. -/
def UniversalPrimeOrientationHermitianGibbsJointCompactOpenLimit
    (ε : Nat.Primes → Bool) : Prop :=
  TendstoLocallyUniformlyOn
    (fun x : Finset Nat.Primes × ℝ => fun z =>
      -_root_.HTGeometry.finiteTransitionPassiveResponse
        (_root_.HTGeometry.finiteGibbsTransitionIntensity x.2
          (primeLogKMSFiniteEnergy x.1)
          (primeLogGibbsFiniteHermitianAmplitude x.1
            (fun q => universalFacetOrbitGauge q) x.2))
        (primeLogKMSFiniteEnergy x.1) z)
    (universalPrimeOrientationLimit ε) Filter.atTop upperHalfPlane

/-- The joint compact-open physical limit selects exactly the all-positive prime orientation. -/
theorem universalPrimeOrientationHermitianGibbsJointCompactOpenLimit_iff
    (ε : Nat.Primes → Bool) :
    UniversalPrimeOrientationHermitianGibbsJointCompactOpenLimit ε ↔
      ε = fun _ => false := by
  constructor
  · intro hlimit
    rw [← universalPrimeOrientationLimit_nonneg_iff_allPositive]
    intro z hz
    have heq : universalPrimeOrientationLimit ε z =
        primeLogHerglotz (fun q => universalFacetOrbitGauge q) z :=
      hlimit.unique
        universalFacetOrbitGauge_finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint
        hz
    rw [heq]
    exact universalFacetOrbitGauge_primeLogHerglotz_im_nonneg hz
  · rintro rfl
    unfold UniversalPrimeOrientationHermitianGibbsJointCompactOpenLimit
    exact
      universalFacetOrbitGauge_finiteHermitianGibbsResponse_tendstoLocallyUniformlyOn_joint.congr_right
        (fun z _ => (universalPrimeOrientationLimit_empty z).symm)

/-- Compact-open and pointwise joint selectors impose the same canonical orientation, while the
compact-open form additionally supplies every analytic jet. -/
theorem universalPrimeOrientationHermitianGibbsJointCompactOpenLimit_iff_jointLimit
    (ε : Nat.Primes → Bool) :
    UniversalPrimeOrientationHermitianGibbsJointCompactOpenLimit ε ↔
      UniversalPrimeOrientationHermitianGibbsJointLimit ε := by
  rw [universalPrimeOrientationHermitianGibbsJointCompactOpenLimit_iff,
    universalPrimeOrientationHermitianGibbsJointLimit_iff]

/-- Constraint-orientation specialization of the compact-open Hermitian Gibbs selector. -/
theorem canonicalConstraintOrientationLimit_primeCarrier_is_HermitianGibbsJointCompactOpenLimit_iff
    (X : CanonicalConstraintOrientationLimit ℕ Nat.Primes) :
    UniversalPrimeOrientationHermitianGibbsJointCompactOpenLimit X.2 ↔
      X.2 = fun _ => false :=
  universalPrimeOrientationHermitianGibbsJointCompactOpenLimit_iff X.2

end

end GaloisForLFunctions.HTGeometry
