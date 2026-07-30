import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary
import GaloisForLFunctions.HTGeometry.GammaCommonInverseCollar
import GaloisForLFunctions.HTGeometry.UniversalPrimeKreinHamming
import GaloisForLFunctions.HTGeometry.UniversalPrimeOrientationCompactOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Minimal polarized critical completion architecture

This file closes the two analytic gaps in the minimal-architecture card.

For the tangent Möbius germ, it proves the continuous-real-exponent Gevrey trichotomy:
subcritical boundedness forces the identity chart, the critical exponent has the exact norm-one
boundedness wall and strict norm-one square-summability wall, and every supercritical profile is
bounded and square-summable.

For every nonempty finite family of rates tending to infinity, the square root of their pointwise
minimum is still unbounded but is little relative to every prescribed rate.  The terminal theorem
packages these results with the existing finite-jet, prime-polarization, and product-bornology
witnesses as one unconditional lower-bound certificate.  It asserts necessity only; it does not
assert the open completeness converse.

Two further exact witnesses isolate information forced by source production.  A polynomial
section of the trivial real line realizes every prescribed finite reduced zero set, so the carrier
does not determine its divisor.  Two explicit integral operators become conjugate over the reals,
while only one has four-saturated integral image.  Thus real analytic realization does not recover
integral cokernel exponent data.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Matrix
open scoped BigOperators Topology

noncomputable section

universe uF uE uE' uIota uKappa uX

def mobiusGevreyProfile (sigma : ℝ) (a : ℂ) (k : ℕ) : ℝ :=
  ‖iteratedDeriv (k + 1) (GaloisForLFunctions.mobiusTangentGerm a) 0‖ /
    ((((k + 1).factorial : ℕ) : ℝ) ^ sigma)

theorem mobiusGevreyProfile_apply (sigma : ℝ) (a : ℂ) (k : ℕ) :
    mobiusGevreyProfile sigma a k =
      ((((k + 1).factorial : ℕ) : ℝ) ^ (1 - sigma)) * ‖a‖ ^ k := by
  rw [mobiusGevreyProfile,
    GaloisForLFunctions.iteratedDeriv_mobiusTangentGerm_zero a (by omega),
    Nat.add_sub_cancel]
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  let f : ℝ := (((k + 1).factorial : ℕ) : ℝ)
  have hf : 0 < f := by
    dsimp [f]
    exact_mod_cast Nat.factorial_pos (k + 1)
  calc
    f * ‖a‖ ^ k / f ^ sigma = (f ^ (1 : ℝ) / f ^ sigma) * ‖a‖ ^ k := by
      rw [Real.rpow_one]
      ring_nf
    _ = f ^ (1 - sigma) * ‖a‖ ^ k := by
      rw [Real.rpow_sub hf]

theorem mobiusGevreyProfile_succ (sigma : ℝ) (a : ℂ) (k : ℕ) :
    mobiusGevreyProfile sigma a (k + 1) =
      (((k + 2 : ℕ) : ℝ) ^ (1 - sigma) * ‖a‖) *
        mobiusGevreyProfile sigma a k := by
  rw [mobiusGevreyProfile_apply, mobiusGevreyProfile_apply]
  rw [show k + 1 + 1 = k + 2 by omega, Nat.factorial_succ]
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [pow_succ]
  ring_nf

theorem mobiusGevreyProfile_nonneg (sigma : ℝ) (a : ℂ) (k : ℕ) :
    0 ≤ mobiusGevreyProfile sigma a k := by
  rw [mobiusGevreyProfile_apply]
  positivity

def mobiusGevreyMultiplier (sigma : ℝ) (a : ℂ) (k : ℕ) : ℝ :=
  (((k + 2 : ℕ) : ℝ) ^ (1 - sigma)) * ‖a‖

theorem mobiusGevreyMultiplier_nonneg (sigma : ℝ) (a : ℂ) (k : ℕ) :
    0 ≤ mobiusGevreyMultiplier sigma a k := by
  rw [mobiusGevreyMultiplier]
  positivity

theorem mobiusGevreyProfile_succ_eq_multiplier
    (sigma : ℝ) (a : ℂ) (k : ℕ) :
    mobiusGevreyProfile sigma a (k + 1) =
      mobiusGevreyMultiplier sigma a k * mobiusGevreyProfile sigma a k := by
  exact mobiusGevreyProfile_succ sigma a k

theorem tendsto_mobiusGevreyMultiplier_atTop
    {sigma : ℝ} (hsigma : sigma < 1) {a : ℂ} (ha : a ≠ 0) :
    Tendsto (mobiusGevreyMultiplier sigma a) atTop atTop := by
  have hbase : Tendsto (fun k : ℕ ↦ ((k + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hpow : Tendsto (fun k : ℕ ↦ ((k + 2 : ℕ) : ℝ) ^ (1 - sigma))
      atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hsigma)).comp hbase
  simpa only [mobiusGevreyMultiplier] using!
    hpow.atTop_mul_const (norm_pos_iff.mpr ha)

theorem tendsto_mobiusGevreyMultiplier_zero
    {sigma : ℝ} (hsigma : 1 < sigma) (a : ℂ) :
    Tendsto (mobiusGevreyMultiplier sigma a) atTop (nhds 0) := by
  have hbase : Tendsto (fun k : ℕ ↦ ((k + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hpow : Tendsto (fun k : ℕ ↦ ((k + 2 : ℕ) : ℝ) ^ (-(sigma - 1)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hsigma)).comp hbase
  convert hpow.mul_const ‖a‖ using 1
  · funext k
    simp only [mobiusGevreyMultiplier]
    congr 2
    ring_nf
  · simp

@[simp] theorem mobiusGevreyProfile_critical (a : ℂ) (k : ℕ) :
    mobiusGevreyProfile 1 a k = ‖a‖ ^ k := by
  simp [mobiusGevreyProfile_apply]

theorem tendsto_mobiusGevreyProfile_atTop_of_lt_one
    {sigma : ℝ} (hsigma : sigma < 1) {a : ℂ} (ha : a ≠ 0) :
    Tendsto (mobiusGevreyProfile sigma a) atTop atTop := by
  have hmult := tendsto_mobiusGevreyMultiplier_atTop hsigma ha
  have hevent : ∀ᶠ k : ℕ in atTop, 2 ≤ mobiusGevreyMultiplier sigma a k :=
    hmult.eventually (eventually_ge_atTop 2)
  rw [eventually_atTop] at hevent
  rcases hevent with ⟨N, hN⟩
  have hprofileN : 0 < mobiusGevreyProfile sigma a N := by
    rw [mobiusGevreyProfile_apply]
    exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (pow_pos (norm_pos_iff.mpr ha) _)
  have htail : Tendsto (fun k ↦ mobiusGevreyProfile sigma a (k + N)) atTop atTop := by
    apply tendsto_atTop_of_geom_le (by simpa using hprofileN)
      (by norm_num : (1 : ℝ) < 2)
    intro k
    rw [show k + 1 + N = (k + N) + 1 by omega,
      mobiusGevreyProfile_succ_eq_multiplier]
    exact mul_le_mul_of_nonneg_right (hN (k + N) (by omega))
      (mobiusGevreyProfile_nonneg sigma a (k + N))
  rw [← map_add_atTop_eq_nat N]
  simpa only [tendsto_map'_iff, Function.comp_apply] using! htail

theorem mobiusGevreyProfile_not_uniformlyBounded_of_lt_one
    {sigma : ℝ} (hsigma : sigma < 1) {a : ℂ} (ha : a ≠ 0) :
    ¬ IsUniformlyBoundedProfile (mobiusGevreyProfile sigma a) := by
  intro hbounded
  rcases hbounded with ⟨B, hB⟩
  have ht := tendsto_mobiusGevreyProfile_atTop_of_lt_one hsigma ha
  have hevent : ∀ᶠ k : ℕ in atTop, B < mobiusGevreyProfile sigma a k :=
    ht.eventually (eventually_gt_atTop B)
  rcases hevent.exists with ⟨k, hk⟩
  exact (not_lt_of_ge ((le_abs_self _).trans (hB k))) hk

theorem mobiusGevreyProfile_uniformlyBounded_iff_eq_zero_of_lt_one
    {sigma : ℝ} (hsigma : sigma < 1) (a : ℂ) :
    IsUniformlyBoundedProfile (mobiusGevreyProfile sigma a) ↔ a = 0 := by
  constructor
  · intro hbounded
    by_contra ha
    exact mobiusGevreyProfile_not_uniformlyBounded_of_lt_one hsigma ha hbounded
  · rintro rfl
    refine ⟨1, fun k ↦ ?_⟩
    cases k with
    | zero => simp [mobiusGevreyProfile_apply]
    | succ k => simp [mobiusGevreyProfile_apply]

theorem summable_mobiusGevreyProfile_of_one_lt
    {sigma : ℝ} (hsigma : 1 < sigma) (a : ℂ) :
    Summable (mobiusGevreyProfile sigma a) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  have hmult := tendsto_mobiusGevreyMultiplier_zero hsigma a
  filter_upwards [hmult.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with k hk
  rw [mobiusGevreyProfile_succ_eq_multiplier]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mobiusGevreyMultiplier_nonneg sigma a k)
      (mobiusGevreyProfile_nonneg sigma a k)),
    Real.norm_eq_abs, abs_of_nonneg (mobiusGevreyProfile_nonneg sigma a k)]
  exact mul_le_mul_of_nonneg_right hk (mobiusGevreyProfile_nonneg sigma a k)

theorem summable_sq_mobiusGevreyProfile_of_one_lt
    {sigma : ℝ} (hsigma : 1 < sigma) (a : ℂ) :
    Summable (fun k ↦ (mobiusGevreyProfile sigma a k) ^ 2) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  have hmult : Tendsto (fun k ↦ (mobiusGevreyMultiplier sigma a k) ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_mobiusGevreyMultiplier_zero hsigma a).pow 2
  filter_upwards [hmult.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with k hk
  rw [mobiusGevreyProfile_succ_eq_multiplier]
  simp only [mul_pow]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_right hk (sq_nonneg _)

theorem mobiusGevreyProfile_uniformlyBounded_of_one_lt
    {sigma : ℝ} (hsigma : 1 < sigma) (a : ℂ) :
    IsUniformlyBoundedProfile (mobiusGevreyProfile sigma a) := by
  have hs := summable_mobiusGevreyProfile_of_one_lt hsigma a
  rcases hs.tendsto_atTop_zero.bddAbove_range with ⟨B, hB⟩
  refine ⟨B, fun k ↦ ?_⟩
  rw [abs_of_nonneg (mobiusGevreyProfile_nonneg sigma a k)]
  exact hB (Set.mem_range_self k)

theorem mobiusGevreyProfile_critical_uniformlyBounded_iff (a : ℂ) :
    IsUniformlyBoundedProfile (mobiusGevreyProfile 1 a) ↔ ‖a‖ ≤ 1 := by
  constructor
  · intro hbounded
    by_contra hnot
    have ha : 1 < ‖a‖ := lt_of_not_ge hnot
    rcases hbounded with ⟨B, hB⟩
    have ht : Tendsto (fun k : ℕ ↦ ‖a‖ ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt ha
    have hevent : ∀ᶠ k : ℕ in atTop, B < ‖a‖ ^ k :=
      ht.eventually (eventually_gt_atTop B)
    rcases hevent.exists with ⟨k, hk⟩
    have hle := hB k
    rw [mobiusGevreyProfile_critical, abs_of_nonneg (pow_nonneg (norm_nonneg a) k)] at hle
    exact (not_lt_of_ge hle) hk
  · intro ha
    refine ⟨1, fun k ↦ ?_⟩
    rw [mobiusGevreyProfile_critical, abs_of_nonneg (pow_nonneg (norm_nonneg a) k)]
    exact pow_le_one₀ (norm_nonneg a) ha

theorem mobiusGevreyProfile_critical_sq_summable_iff (a : ℂ) :
    Summable (fun k ↦ (mobiusGevreyProfile 1 a k) ^ 2) ↔ ‖a‖ < 1 := by
  have hseq : (fun k ↦ (mobiusGevreyProfile 1 a k) ^ 2) =
      (fun k : ℕ ↦ (‖a‖ ^ 2) ^ k) := by
    funext k
    rw [mobiusGevreyProfile_critical]
    simp only [← pow_mul, Nat.mul_comm]
  rw [hseq, summable_geometric_iff_norm_lt_one]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖a‖), sq_lt_one_iff₀ (norm_nonneg a)]

def finiteRateMinimum {m : ℕ} (r : Fin (m + 1) → ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i ↦ r i n)

theorem tendsto_finiteRateMinimum_atTop {m : ℕ} {r : Fin (m + 1) → ℕ → ℝ}
    (hr : ∀ i, Tendsto (r i) atTop atTop) :
    Tendsto (finiteRateMinimum r) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  have h : ∀ᶠ n in atTop, ∀ i, b ≤ r i n := by
    rw [Filter.eventually_all]
    intro i
    exact (hr i).eventually (eventually_ge_atTop b)
  rw [eventually_atTop] at h
  rcases h with ⟨N, hN⟩
  exact ⟨N, fun n hn ↦
    Finset.le_inf' Finset.univ_nonempty _ (fun i _ ↦ hN n hn i)⟩

theorem finiteRateMinimum_le {m : ℕ} (r : Fin (m + 1) → ℕ → ℝ)
    (i : Fin (m + 1)) (n : ℕ) : finiteRateMinimum r n ≤ r i n := by
  exact Finset.inf'_le (fun j ↦ r j n) (Finset.mem_univ i)

def finiteRateInvisibleProfile {m : ℕ} (r : Fin (m + 1) → ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (finiteRateMinimum r n)

theorem tendsto_finiteRateInvisibleProfile_atTop {m : ℕ}
    {r : Fin (m + 1) → ℕ → ℝ}
    (hr : ∀ i, Tendsto (r i) atTop atTop) :
    Tendsto (finiteRateInvisibleProfile r) atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp (tendsto_finiteRateMinimum_atTop hr)

theorem tendsto_finiteRateInvisibleProfile_div_zero {m : ℕ}
    {r : Fin (m + 1) → ℕ → ℝ}
    (hr : ∀ i, Tendsto (r i) atTop atTop) (i : Fin (m + 1)) :
    Tendsto (fun n ↦ finiteRateInvisibleProfile r n / r i n) atTop (nhds 0) := by
  have hq := tendsto_finiteRateMinimum_atTop hr
  have hs := tendsto_finiteRateInvisibleProfile_atTop hr
  have hinv : Tendsto (fun n ↦ (finiteRateInvisibleProfile r n)⁻¹) atTop (nhds 0) :=
    hs.inv_tendsto_atTop
  apply squeeze_zero'
  · filter_upwards [hq.eventually (eventually_gt_atTop 0)] with n hn
    exact div_nonneg (Real.sqrt_nonneg _) (le_trans hn.le (finiteRateMinimum_le r i n))
  · filter_upwards [hq.eventually (eventually_gt_atTop 0)] with n hn
    have hri : 0 < r i n := lt_of_lt_of_le hn (finiteRateMinimum_le r i n)
    have hspos : 0 < finiteRateInvisibleProfile r n := Real.sqrt_pos.2 hn
    calc
      finiteRateInvisibleProfile r n / r i n ≤
          finiteRateInvisibleProfile r n / finiteRateMinimum r n :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hn
          (finiteRateMinimum_le r i n)
      _ = (finiteRateInvisibleProfile r n)⁻¹ := by
        change Real.sqrt (finiteRateMinimum r n) / finiteRateMinimum r n =
          (Real.sqrt (finiteRateMinimum r n))⁻¹
        conv_lhs => rhs; rw [← Real.sq_sqrt hn.le]
        field_simp [hspos.ne']
  · exact hinv

theorem finiteRateInvisibleProfile_not_uniformlyBounded {m : ℕ}
    {r : Fin (m + 1) → ℕ → ℝ}
    (hr : ∀ i, Tendsto (r i) atTop atTop) :
    ¬ IsUniformlyBoundedProfile (finiteRateInvisibleProfile r) := by
  intro hbounded
  rcases hbounded with ⟨B, hB⟩
  have ht := tendsto_finiteRateInvisibleProfile_atTop hr
  have hevent : ∀ᶠ n : ℕ in atTop, B < finiteRateInvisibleProfile r n :=
    ht.eventually (eventually_gt_atTop B)
  rcases hevent.exists with ⟨n, hn⟩
  exact (not_lt_of_ge ((le_abs_self _).trans (hB n))) hn

/-! The five concrete information-loss channels, packaged as one lower-bound certificate. -/

def FiniteJetSourceBlindness : Prop :=
  ∀ {F : Type uF} {E : Type uE} {E' : Type uE'} [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E'] [Differential E] [Differential E']
    {x : E} {y : E'}, HypertranscendentalOver F x → HypertranscendentalOver F y →
    ∀ L : ℕ, Nonempty
      (IntermediateField.adjoin F (Set.range (finiteDifferentialJet x L)) ≃ₐ[F]
        IntermediateField.adjoin F (Set.range (finiteDifferentialJet y L)))

theorem finiteJetSourceBlindness : FiniteJetSourceBlindness := by
  intro F E E' _ _ _ _ _ _ _ x y hx hy L
  exact ⟨hypertranscendentalFiniteJetEquiv hx hy L⟩

def PrimeChamberExactNegativeInertia (J L : Finset Nat.Primes) : Prop :=
  ( ∀ W : Submodule ℂ
        (Fin ((L \ J).card + (J \ L).card) → ℂ),
      (∀ y ∈ W, y ≠ 0 →
        (dotProduct (star y)
          ((universalPrimeChamberRelativeKreinProbeForm J L).mulVec y)).re < 0) →
      Module.finrank ℂ W ≤ (J \ L).card) ∧
    (∃ W : Submodule ℂ
        (Fin ((L \ J).card + (J \ L).card) → ℂ),
      Module.finrank ℂ W = (J \ L).card ∧
      ∀ y ∈ W, y ≠ 0 →
        (dotProduct (star y)
          ((universalPrimeChamberRelativeKreinProbeForm J L).mulVec y)).re < 0)

def PrimeChamberExactPositiveInertia (J L : Finset Nat.Primes) : Prop :=
  ( ∀ W : Submodule ℂ
        (Fin ((L \ J).card + (J \ L).card) → ℂ),
      (∀ y ∈ W, y ≠ 0 →
        0 < (dotProduct (star y)
          ((universalPrimeChamberRelativeKreinProbeForm J L).mulVec y)).re) →
      Module.finrank ℂ W ≤ (L \ J).card) ∧
    (∃ W : Submodule ℂ
        (Fin ((L \ J).card + (J \ L).card) → ℂ),
      Module.finrank ℂ W = (L \ J).card ∧
      ∀ y ∈ W, y ≠ 0 →
        0 < (dotProduct (star y)
          ((universalPrimeChamberRelativeKreinProbeForm J L).mulVec y)).re)

def PrimeOrientationBlindnessAndPolarization : Prop :=
  (∀ J : Finset Nat.Primes,
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialAdjoin (RatFunc ℂ)
        (Set.range (universalFacetOrbitPrimeOrientedSource J)) =
      differentialAdjoin (RatFunc ℂ)
        (Set.range (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
          universalFacetOrbitGauge))) ∧
  (∀ epsilon delta : Nat.Primes → Bool,
    primeOrientationCompletedRing epsilon = primeOrientationCompletedRing delta) ∧
  (∀ J L : Finset Nat.Primes,
    PrimeChamberExactNegativeInertia J L ∧
    PrimeChamberExactPositiveInertia J L ∧
    (primeChamberHammingDistance J L = 0 ↔ J = L))

theorem primeOrientationBlindnessAndPolarization :
    PrimeOrientationBlindnessAndPolarization := by
  refine ⟨universalFacetOrbitPrimeOrientedSource_differentialAdjoin_eq,
    primeOrientationCompletedRing_eq, ?_⟩
  intro J L
  exact ⟨by simpa [PrimeChamberExactNegativeInertia] using
      universalPrimeChamberRelativeKreinProbe_exact_neg_inertia J L,
    by simpa [PrimeChamberExactPositiveInertia] using
      universalPrimeChamberRelativeKreinProbe_exact_pos_inertia J L,
    primeChamberHammingDistance_eq_zero_iff J L⟩

def ContinuousMobiusGevreyTrichotomy : Prop :=
  (∀ (sigma : ℝ), sigma < 1 → ∀ a : ℂ,
    IsUniformlyBoundedProfile (mobiusGevreyProfile sigma a) ↔ a = 0) ∧
  (∀ a : ℂ,
    (IsUniformlyBoundedProfile (mobiusGevreyProfile 1 a) ↔ ‖a‖ ≤ 1) ∧
    (Summable (fun k ↦ (mobiusGevreyProfile 1 a k) ^ 2) ↔ ‖a‖ < 1)) ∧
  (∀ (sigma : ℝ), 1 < sigma → ∀ a : ℂ,
    IsUniformlyBoundedProfile (mobiusGevreyProfile sigma a) ∧
    Summable (fun k ↦ (mobiusGevreyProfile sigma a k) ^ 2))

theorem continuousMobiusGevreyTrichotomy : ContinuousMobiusGevreyTrichotomy := by
  refine ⟨fun sigma hsigma a ↦
      mobiusGevreyProfile_uniformlyBounded_iff_eq_zero_of_lt_one hsigma a,
    fun a ↦ ⟨mobiusGevreyProfile_critical_uniformlyBounded_iff a,
      mobiusGevreyProfile_critical_sq_summable_iff a⟩, ?_⟩
  intro sigma hsigma a
  exact ⟨mobiusGevreyProfile_uniformlyBounded_of_one_lt hsigma a,
    summable_sq_mobiusGevreyProfile_of_one_lt hsigma a⟩

def FullProductBornologyLowerBound : Prop :=
  (¬ IsBornologicallyCofinal movingBoundaryProfile (fun n : ℕ ↦ (n, n))) ∧
  (∀ {iota : Type uIota} {kappa : Type uKappa} {X : Type uX} [PseudoMetricSpace X]
    (p : iota → X) (phi : kappa → iota),
    IsMetricBornologicallyCofinal p phi →
      (IsUniformlyBoundedAround (p ∘ phi) ↔ IsUniformlyBoundedAround p))

theorem fullProductBornologyLowerBound : FullProductBornologyLowerBound := by
  exact ⟨diagonal_not_bornologicallyCofinal_for_movingBoundary,
    fun p phi hcofinal ↦
      uniformlyBoundedAround_iff_subsample_of_metricBornologicallyCofinal hcofinal⟩

def FiniteRateSpectrumLowerBound : Prop :=
  ∀ (m : ℕ) (r : Fin (m + 1) → ℕ → ℝ),
    (∀ i, Tendsto (r i) atTop atTop) →
      Tendsto (finiteRateInvisibleProfile r) atTop atTop ∧
      (∀ i, Tendsto (fun n ↦ finiteRateInvisibleProfile r n / r i n)
        atTop (nhds 0)) ∧
      ¬ IsUniformlyBoundedProfile (finiteRateInvisibleProfile r)

theorem finiteRateSpectrumLowerBound : FiniteRateSpectrumLowerBound := by
  intro m r hr
  exact ⟨tendsto_finiteRateInvisibleProfile_atTop hr,
    tendsto_finiteRateInvisibleProfile_div_zero hr,
    finiteRateInvisibleProfile_not_uniformlyBounded hr⟩

def MinimalHTCompletionArchitecture : Prop :=
  FiniteJetSourceBlindness.{uF, uE, uE'} ∧
  PrimeOrientationBlindnessAndPolarization ∧
  ContinuousMobiusGevreyTrichotomy ∧
  FullProductBornologyLowerBound.{uIota, uKappa, uX} ∧
  FiniteRateSpectrumLowerBound

theorem minimalHTCompletionArchitecture :
    MinimalHTCompletionArchitecture.{uF, uE, uE', uIota, uKappa, uX} :=
  ⟨finiteJetSourceBlindness,
    primeOrientationBlindnessAndPolarization,
    continuousMobiusGevreyTrichotomy,
    fullProductBornologyLowerBound,
    finiteRateSpectrumLowerBound⟩

/-! Two additional information-loss channels: section effectivity and integral realization. -/

def prescribedFiniteZeroSection (S : Finset ℝ) (x : ℝ) : ℝ :=
  ∏ a ∈ S, (x - a)

@[simp] theorem prescribedFiniteZeroSection_eq_zero_iff
    (S : Finset ℝ) (x : ℝ) :
    prescribedFiniteZeroSection S x = 0 ↔ x ∈ S := by
  classical
  rw [prescribedFiniteZeroSection, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

def SourceSectionDivisorBlindness : Prop :=
  ∀ S : Finset ℝ, ∃ s : ℝ → ℝ,
    ∀ x, s x = 0 ↔ x ∈ S

theorem sourceSectionDivisorBlindness : SourceSectionDivisorBlindness := by
  intro S
  exact ⟨prescribedFiniteZeroSection S,
    prescribedFiniteZeroSection_eq_zero_iff S⟩

def splitRealLatticeOperator (v : ℝ × ℝ) : ℝ × ℝ :=
  (2 * v.1, 4 * v.2)

def coupledRealLatticeOperator (v : ℝ × ℝ) : ℝ × ℝ :=
  (-8 * v.2, v.1 + 6 * v.2)

def realLatticeComparison (v : ℝ × ℝ) : ℝ × ℝ :=
  (-4 * v.1 - 2 * v.2, v.1 + v.2)

def realLatticeComparisonInv (v : ℝ × ℝ) : ℝ × ℝ :=
  (-v.1 / 2 - v.2, v.1 / 2 + 2 * v.2)

theorem realLatticeComparison_bijective :
    Function.Bijective realLatticeComparison := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨realLatticeComparisonInv, ?_, ?_⟩
  · intro v
    apply Prod.ext <;> simp [realLatticeComparison, realLatticeComparisonInv] <;> ring
  · intro v
    apply Prod.ext <;> simp [realLatticeComparison, realLatticeComparisonInv] <;> ring

theorem realLatticeComparison_intertwines (v : ℝ × ℝ) :
    coupledRealLatticeOperator (realLatticeComparison v) =
      realLatticeComparison (splitRealLatticeOperator v) := by
  apply Prod.ext <;>
    simp [coupledRealLatticeOperator, realLatticeComparison, splitRealLatticeOperator] <;>
    ring

def splitIntegralLatticeOperator (v : ℤ × ℤ) : ℤ × ℤ :=
  (2 * v.1, 4 * v.2)

def coupledIntegralLatticeOperator (v : ℤ × ℤ) : ℤ × ℤ :=
  (-8 * v.2, v.1 + 6 * v.2)

def FourSaturatedImage (T : (ℤ × ℤ) → (ℤ × ℤ)) : Prop :=
  ∀ v : ℤ × ℤ, ∃ w, T w = (4 * v.1, 4 * v.2)

theorem splitIntegralLatticeOperator_fourSaturated :
    FourSaturatedImage splitIntegralLatticeOperator := by
  intro v
  refine ⟨(2 * v.1, v.2), ?_⟩
  simp [splitIntegralLatticeOperator]
  ring

theorem coupledIntegralLatticeOperator_not_fourSaturated :
    ¬ FourSaturatedImage coupledIntegralLatticeOperator := by
  intro h
  obtain ⟨w, hw⟩ := h (1, 0)
  have hfirst := congrArg Prod.fst hw
  simp [coupledIntegralLatticeOperator] at hfirst
  omega

def IntegralRealificationBlindness : Prop :=
  Function.Bijective realLatticeComparison ∧
  (∀ v, coupledRealLatticeOperator (realLatticeComparison v) =
    realLatticeComparison (splitRealLatticeOperator v)) ∧
  FourSaturatedImage splitIntegralLatticeOperator ∧
  ¬ FourSaturatedImage coupledIntegralLatticeOperator

theorem integralRealificationBlindness : IntegralRealificationBlindness :=
  ⟨realLatticeComparison_bijective,
    realLatticeComparison_intertwines,
    splitIntegralLatticeOperator_fourSaturated,
    coupledIntegralLatticeOperator_not_fourSaturated⟩

def SourceProducerIntegralLowerBound : Prop :=
  SourceSectionDivisorBlindness ∧ IntegralRealificationBlindness

theorem sourceProducerIntegralLowerBound : SourceProducerIntegralLowerBound :=
  ⟨sourceSectionDivisorBlindness, integralRealificationBlindness⟩

/-! The integral root criterion for a finite orbit divisor. -/

def IntegralOrbitDivisorCoefficientwiseDivisible
    {G : Type*} (m : ℕ) (D : G →₀ ℤ) : Prop :=
  ∀ g, (m : ℤ) ∣ D g

def integralOrbitDivisorQuotient
    {G : Type*} (m : ℕ) (D : G →₀ ℤ) : G →₀ ℤ :=
  D.mapRange (fun z => z / (m : ℤ)) (by simp)

theorem integralOrbitDivisor_has_nsmul_root_iff
    {G : Type*} (m : ℕ) (D : G →₀ ℤ) :
    (∃ E : G →₀ ℤ, m • E = D) ↔
      IntegralOrbitDivisorCoefficientwiseDivisible m D := by
  constructor
  · rintro ⟨E, rfl⟩ g
    refine ⟨E g, ?_⟩
    simp
  · intro h
    refine ⟨integralOrbitDivisorQuotient m D, ?_⟩
    ext g
    change (m : ℤ) * (D g / (m : ℤ)) = D g
    rw [mul_comm, Int.ediv_mul_cancel (h g)]

/-- The Kummer content of a finite integral orbit divisor: the gcd of the absolute values of all
nonzero coefficients. -/
def integralOrbitDivisorContent {G : Type*} (D : G →₀ ℤ) : ℕ :=
  D.support.gcd fun g => (D g).natAbs

theorem integralOrbitDivisor_coefficientwiseDivisible_iff_content_dvd
    {G : Type*} (m : ℕ) (D : G →₀ ℤ) :
    IntegralOrbitDivisorCoefficientwiseDivisible m D ↔
      m ∣ integralOrbitDivisorContent D := by
  constructor
  · intro h
    apply Finset.dvd_gcd
    intro g hg
    exact Int.natCast_dvd.mp (h g)
  · intro h g
    rw [Int.natCast_dvd]
    by_cases hg : g ∈ D.support
    · exact h.trans (Finset.gcd_dvd hg)
    · rw [Finsupp.notMem_support_iff.mp hg]
      exact dvd_zero m

theorem integralOrbitDivisor_has_nsmul_root_iff_content_dvd
    {G : Type*} (m : ℕ) (D : G →₀ ℤ) :
    (∃ E : G →₀ ℤ, m • E = D) ↔
      m ∣ integralOrbitDivisorContent D := by
  rw [integralOrbitDivisor_has_nsmul_root_iff,
    integralOrbitDivisor_coefficientwiseDivisible_iff_content_dvd]

/-! The exact root criterion and uniqueness statement modulo the kernel of a
surjective integral divisor map.  This is the group-theoretic Kummer core: an
analytic source class can be substituted for `M`, with its DA subgroup as the
kernel of `D`. -/

def HasSourceRootModuloKernel
    {M G : Type*} [AddCommGroup M]
    (D : M →+ G →₀ ℤ) (m : ℕ) (Y : M) : Prop :=
  ∃ Z : M, Y - m • Z ∈ D.ker

theorem hasSourceRootModuloKernel_iff
    {M G : Type*} [AddCommGroup M]
    (D : M →+ G →₀ ℤ) (hD : Function.Surjective D)
    (m : ℕ) (Y : M) :
    HasSourceRootModuloKernel D m Y ↔
      IntegralOrbitDivisorCoefficientwiseDivisible m (D Y) := by
  rw [← integralOrbitDivisor_has_nsmul_root_iff]
  constructor
  · rintro ⟨Z, hZ⟩
    refine ⟨D Z, ?_⟩
    change D (Y - m • Z) = 0 at hZ
    simp only [map_sub, map_nsmul] at hZ
    exact (sub_eq_zero.mp hZ).symm
  · rintro ⟨E, hE⟩
    obtain ⟨Z, rfl⟩ := hD E
    refine ⟨Z, ?_⟩
    change D (Y - m • Z) = 0
    simp only [map_sub, map_nsmul]
    exact sub_eq_zero.mpr hE.symm

theorem hasSourceRootModuloKernel_iff_content_dvd
    {M G : Type*} [AddCommGroup M]
    (D : M →+ G →₀ ℤ) (hD : Function.Surjective D)
    (m : ℕ) (Y : M) :
    HasSourceRootModuloKernel D m Y ↔
      m ∣ integralOrbitDivisorContent (D Y) := by
  rw [hasSourceRootModuloKernel_iff D hD,
    integralOrbitDivisor_coefficientwiseDivisible_iff_content_dvd]

theorem sourceRoot_unique_mod_kernel
    {M G : Type*} [AddCommGroup M]
    (D : M →+ G →₀ ℤ) {m : ℕ} (hm : m ≠ 0) {Y Z₁ Z₂ : M}
    (h₁ : Y - m • Z₁ ∈ D.ker) (h₂ : Y - m • Z₂ ∈ D.ker) :
    Z₁ - Z₂ ∈ D.ker := by
  change D (Y - m • Z₁) = 0 at h₁
  change D (Y - m • Z₂) = 0 at h₂
  change D (Z₁ - Z₂) = 0
  simp only [map_sub, map_nsmul] at h₁ h₂ ⊢
  apply sub_eq_zero.mpr
  apply nsmul_right_injective hm
  exact (sub_eq_zero.mp h₁).symm.trans (sub_eq_zero.mp h₂)

end

end GaloisForLFunctions.HTGeometry
