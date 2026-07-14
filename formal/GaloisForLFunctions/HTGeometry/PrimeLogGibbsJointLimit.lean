import GaloisForLFunctions.HTGeometry.PrimeLogGibbsZeroTemperature
import Mathlib.Order.Filter.AtTopBot.Prod

/-!
# Uniform-gap joint cold and thermodynamic limit

[BRIDGE] In a gapped quantum system, reverse thermal transitions are Boltzmann-suppressed at
least at the lowest excitation energy.  The prime-log Hamiltonians have the uniform gap `log 2`,
independently of the finite prime subsystem.  Together with the finite total dyadic prime mass,
this makes the zero-temperature error uniform in the finite subsystem.

The result is stronger than the existing iterated limit: the prime cutoff and inverse temperature
may tend to infinity simultaneously in the product directed order.  No order of limits remains.
-/

open scoped BigOperators
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Total variation mass of the dyadically weighted prime source. -/
def primeDyadicTotalMass (u : Nat.Primes → ℝ) : ℝ :=
  ∑' p, ‖(primeDyadicWeight u p : ℂ)‖

/-- Every prime-log excitation lies above the subsystem-independent spectral gap `log 2`. -/
theorem log_two_le_primeLogSupport (p : Nat.Primes) :
    Real.log 2 ≤ primeLogSupport p := by
  rw [primeLogSupport]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)

/-- On the upper half-plane, every reverse-transition resolvent is bounded by `1 / Im z`. -/
theorem norm_primeLogSupport_add_inv_le_im_inv
    (p : Nat.Primes) (z : ℂ) (hz : 0 < z.im) :
    ‖((primeLogSupport p : ℂ) + z)⁻¹‖ ≤ (z.im)⁻¹ := by
  have hnorm : z.im ≤ ‖(primeLogSupport p : ℂ) + z‖ := calc
    z.im ≤ |z.im| := le_abs_self _
    _ = |(((primeLogSupport p : ℂ) + z).im)| := by simp
    _ ≤ ‖(primeLogSupport p : ℂ) + z‖ := Complex.abs_im_le_norm _
  simpa only [norm_inv, one_div] using one_div_le_one_div_of_le hz hnorm

/-- The reverse transition at any prime is bounded by the Boltzmann factor of the uniform gap. -/
theorem exp_neg_beta_primeLogSupport_le_gap
    (p : Nat.Primes) {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-β * primeLogSupport p) ≤
      Real.exp (-β * Real.log 2) := by
  apply Real.exp_le_exp.mpr
  nlinarith [log_two_le_primeLogSupport p]

/-- **Uniform Boltzmann error bound.**  The cold-limit error is independent of the finite prime
subsystem.  This is the quantitative input that removes the order of limits. -/
theorem finitePrimeLogHermitianGibbsCarrier_sub_bound
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (C : ℝ)
    (hu : ∀ p, u p ≤ C) (β : ℝ) (hβ : 0 ≤ β)
    (z : ℂ) (hz : 0 < z.im) :
    ‖finitePrimeLogHermitianGibbsCarrier P u β z -
        finitePrimeLogHerglotz P u z‖ ≤
      Real.exp (-β * Real.log 2) * (z.im)⁻¹ * primeDyadicTotalMass u := by
  have hsum : ∑ p ∈ P, ‖(primeDyadicWeight u p : ℂ)‖ ≤
      primeDyadicTotalMass u := by
    exact (summable_norm_primeDyadicWeight u C hu).sum_le_tsum P
      (fun p hp => norm_nonneg _)
  have hid : finitePrimeLogHermitianGibbsCarrier P u β z -
        finitePrimeLogHerglotz P u z =
      -∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
        (Real.exp (-β * primeLogSupport p) : ℂ) *
          ((primeLogSupport p : ℂ) + z)⁻¹ := by
    rw [finitePrimeLogHermitianGibbsCarrier, finitePrimeLogHerglotz,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hid, norm_neg]
  calc
    ‖∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
        (Real.exp (-β * primeLogSupport p) : ℂ) *
          ((primeLogSupport p : ℂ) + z)⁻¹‖ ≤
        ∑ p ∈ P, ‖(primeDyadicWeight u p : ℂ) *
          (Real.exp (-β * primeLogSupport p) : ℂ) *
            ((primeLogSupport p : ℂ) + z)⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ P, Real.exp (-β * Real.log 2) * (z.im)⁻¹ *
          ‖(primeDyadicWeight u p : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul, norm_mul,
        Complex.norm_real (Real.exp (-β * primeLogSupport p)), Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hw : 0 ≤ ‖(primeDyadicWeight u p : ℂ)‖ := norm_nonneg _
      have hres : 0 ≤ ‖((primeLogSupport p : ℂ) + z)⁻¹‖ := norm_nonneg _
      have hgap : 0 ≤ Real.exp (-β * Real.log 2) := (Real.exp_pos _).le
      calc
        ‖(primeDyadicWeight u p : ℂ)‖ *
            Real.exp (-β * primeLogSupport p) *
              ‖((primeLogSupport p : ℂ) + z)⁻¹‖ ≤
            ‖(primeDyadicWeight u p : ℂ)‖ *
              Real.exp (-β * Real.log 2) *
                ‖((primeLogSupport p : ℂ) + z)⁻¹‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (exp_neg_beta_primeLogSupport_le_gap p hβ) hw) hres
        _ ≤
            ‖(primeDyadicWeight u p : ℂ)‖ *
              Real.exp (-β * Real.log 2) * (z.im)⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (norm_primeLogSupport_add_inv_le_im_inv p z hz)
            (mul_nonneg hw hgap)
        _ = Real.exp (-β * Real.log 2) * (z.im)⁻¹ *
            ‖(primeDyadicWeight u p : ℂ)‖ := by ring
    _ = Real.exp (-β * Real.log 2) * (z.im)⁻¹ *
          (∑ p ∈ P, ‖(primeDyadicWeight u p : ℂ)‖) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-β * Real.log 2) * (z.im)⁻¹ *
          primeDyadicTotalMass u := by
      exact mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr hz.le))

private theorem tendsto_exp_neg_mul_log_two_atTop :
    Filter.Tendsto (fun β : ℝ => Real.exp (-β * Real.log 2))
      Filter.atTop (nhds 0) := by
  have hpos : Filter.Tendsto (fun β : ℝ => Real.log 2 * β)
      Filter.atTop Filter.atTop :=
    tendsto_id.const_mul_atTop (Real.log_pos (by norm_num))
  have hlin : Filter.Tendsto (fun β : ℝ => β * (-Real.log 2))
      Filter.atTop Filter.atBot := by
    convert tendsto_neg_atTop_atBot.comp hpos using 1
    funext β
    simp [mul_comm]
  convert Real.tendsto_exp_atBot.comp hlin using 1
  funext β
  congr 1
  ring

/-- **Simultaneous cold/thermodynamic prime-log limit.**  Both the finite prime subsystem and
inverse temperature tend to infinity in the product directed order.  In particular, the theorem
does not assume either iterated limit, a relative rate, or a chosen diagonal schedule. -/
theorem finitePrimeLogHermitianGibbsCarrier_tendsto_joint
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (z : ℂ) (hz : 0 < z.im) :
    Filter.Tendsto
      (fun x : Finset Nat.Primes × ℝ =>
        finitePrimeLogHermitianGibbsCarrier x.1 u x.2 z)
      Filter.atTop (nhds (primeLogHerglotz u z)) := by
  let B : ℝ := (z.im)⁻¹ * primeDyadicTotalMass u
  have hrhsβ : Filter.Tendsto
      (fun β : ℝ => Real.exp (-β * Real.log 2) * B)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_exp_neg_mul_log_two_atTop.mul_const B
  have hrhs : Filter.Tendsto
      (fun x : Finset Nat.Primes × ℝ =>
        Real.exp (-x.2 * Real.log 2) * B)
      Filter.atTop (nhds 0) := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact hrhsβ.comp Filter.tendsto_snd
  have hβ : ∀ᶠ x : Finset Nat.Primes × ℝ in Filter.atTop, 0 ≤ x.2 := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact (eventually_ge_atTop (0 : ℝ)).prod_inr Filter.atTop
  have hbound : ∀ᶠ x : Finset Nat.Primes × ℝ in Filter.atTop,
      ‖finitePrimeLogHermitianGibbsCarrier x.1 u x.2 z -
        finitePrimeLogHerglotz x.1 u z‖ ≤
          Real.exp (-x.2 * Real.log 2) * B := by
    filter_upwards [hβ] with x hx
    simpa [B, mul_assoc] using
      finitePrimeLogHermitianGibbsCarrier_sub_bound x.1 u C hu x.2 hx z hz
  have herr : Filter.Tendsto
      (fun x : Finset Nat.Primes × ℝ =>
        finitePrimeLogHermitianGibbsCarrier x.1 u x.2 z -
          finitePrimeLogHerglotz x.1 u z)
      Filter.atTop (nhds 0) :=
    squeeze_zero_norm' hbound hrhs
  have hfinite : Filter.Tendsto
      (fun x : Finset Nat.Primes × ℝ => finitePrimeLogHerglotz x.1 u z)
      Filter.atTop (nhds (primeLogHerglotz u z)) := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact (finitePrimeLogHerglotz_tendsto_primeLogHerglotz u C hu z hz).comp
      Filter.tendsto_fst
  simpa only [sub_add_cancel, zero_add] using herr.add hfinite

/-- The exact finite Hermitian Gibbs responses converge in the simultaneous product limit. -/
theorem finiteHermitianGibbsResponse_tendsto_primeLogHerglotz_joint
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (z : ℂ) (hz : 0 < z.im) :
    Filter.Tendsto
      (fun x : Finset Nat.Primes × ℝ =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteGibbsTransitionIntensity x.2
            (primeLogKMSFiniteEnergy x.1)
            (primeLogGibbsFiniteHermitianAmplitude x.1 u x.2))
          (primeLogKMSFiniteEnergy x.1) z)
      Filter.atTop (nhds (primeLogHerglotz u z)) := by
  simpa only [neg_finiteGibbsResponse_primeLogGibbsFiniteHermitianAmplitude] using
    finitePrimeLogHermitianGibbsCarrier_tendsto_joint u C hu z hz

/-- Universal-gauge specialization of the simultaneous Hermitian Gibbs limit. -/
theorem universalFacetOrbitGauge_finiteHermitianGibbsResponse_tendsto_joint
    (z : ℂ) (hz : 0 < z.im) :
    Filter.Tendsto
      (fun x : Finset Nat.Primes × ℝ =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteGibbsTransitionIntensity x.2
            (primeLogKMSFiniteEnergy x.1)
            (primeLogGibbsFiniteHermitianAmplitude x.1
              (fun q => universalFacetOrbitGauge q) x.2))
          (primeLogKMSFiniteEnergy x.1) z)
      Filter.atTop
      (nhds (primeLogHerglotz (fun q => universalFacetOrbitGauge q) z)) :=
  finiteHermitianGibbsResponse_tendsto_primeLogHerglotz_joint
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q)) z hz

/-- The universal orientation is selected by one simultaneous cold and finite-prime
thermodynamic limit of explicit Hermitian Gibbs systems. -/
def UniversalPrimeOrientationHermitianGibbsJointLimit
    (ε : Nat.Primes → Bool) : Prop :=
  ∀ z : ℂ, 0 < z.im →
    Filter.Tendsto
      (fun x : Finset Nat.Primes × ℝ =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteGibbsTransitionIntensity x.2
            (primeLogKMSFiniteEnergy x.1)
            (primeLogGibbsFiniteHermitianAmplitude x.1
              (fun q => universalFacetOrbitGauge q) x.2))
          (primeLogKMSFiniteEnergy x.1) z)
      Filter.atTop (nhds (universalPrimeOrientationLimit ε z))

/-- **Joint Hermitian Gibbs selection of the canonical prime orientation.**  The stronger
simultaneous limit still selects exactly the all-positive orientation. -/
theorem universalPrimeOrientationHermitianGibbsJointLimit_iff
    (ε : Nat.Primes → Bool) :
    UniversalPrimeOrientationHermitianGibbsJointLimit ε ↔
      ε = fun _ => false := by
  constructor
  · intro hlimit
    rw [← universalPrimeOrientationLimit_nonneg_iff_allPositive]
    intro z hz
    have heq : universalPrimeOrientationLimit ε z =
        primeLogHerglotz (fun q => universalFacetOrbitGauge q) z :=
      tendsto_nhds_unique (hlimit z hz)
        (universalFacetOrbitGauge_finiteHermitianGibbsResponse_tendsto_joint z hz)
    rw [heq]
    exact universalFacetOrbitGauge_primeLogHerglotz_im_nonneg hz
  · rintro rfl z hz
    simpa only [universalPrimeOrientationLimit_empty] using
      universalFacetOrbitGauge_finiteHermitianGibbsResponse_tendsto_joint z hz

/-- The new joint-limit hypothesis is interchangeable with the older iterated-limit hypothesis,
while exposing the strictly stronger physical realization at its theorem surface. -/
theorem universalPrimeOrientationHermitianGibbsJointLimit_iff_coldLimit
    (ε : Nat.Primes → Bool) :
    UniversalPrimeOrientationHermitianGibbsJointLimit ε ↔
      UniversalPrimeOrientationHermitianGibbsColdLimit ε := by
  rw [universalPrimeOrientationHermitianGibbsJointLimit_iff,
    universalPrimeOrientationHermitianGibbsColdLimit_iff]

/-- Constraint-orientation specialization of the simultaneous Hermitian Gibbs selector. -/
theorem canonicalConstraintOrientationLimit_primeCarrier_is_HermitianGibbsJointLimit_iff
    (X : CanonicalConstraintOrientationLimit ℕ Nat.Primes) :
    UniversalPrimeOrientationHermitianGibbsJointLimit X.2 ↔
      X.2 = fun _ => false :=
  universalPrimeOrientationHermitianGibbsJointLimit_iff X.2

end

end GaloisForLFunctions.HTGeometry
