import GaloisForLFunctions.HTGeometry.PrimeLogKMSHermitianCompletion
import Mathlib.Order.Filter.AtTopBot.Field

open scoped BigOperators
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Hermitian prime-log observable normalized by the vacuum Gibbs occupation rather than by the
symmetric Wightman half-density. -/
def primeLogGibbsFiniteHermitianAmplitude (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (β : ℝ) : Option P → Option P → ℂ
  | some p, none =>
      (Real.sqrt (primeDyadicWeight u p.1 /
        _root_.HTGeometry.finiteGibbsStateWeight β
          (primeLogKMSFiniteEnergy P) none) : ℂ)
  | none, some p =>
      (Real.sqrt (primeDyadicWeight u p.1 /
        _root_.HTGeometry.finiteGibbsStateWeight β
          (primeLogKMSFiniteEnergy P) none) : ℂ)
  | _, _ => 0

theorem primeLogGibbsFiniteHermitianAmplitude_hermitian
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) :
    ∀ a b, primeLogGibbsFiniteHermitianAmplitude P u β b a =
      star (primeLogGibbsFiniteHermitianAmplitude P u β a b) := by
  intro a b
  cases a <;> cases b <;>
    simp [primeLogGibbsFiniteHermitianAmplitude]

/-- Detailed-balance Gibbs intensities: the vacuum-to-prime weight is fixed, while the reverse
transition carries the Boltzmann factor. -/
def primeLogGibbsFiniteIntensity (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (β : ℝ) : Option P → Option P → ℝ
  | some p, none => primeDyadicWeight u p.1
  | none, some p =>
      Real.exp (-β * primeLogSupport p.1) * primeDyadicWeight u p.1
  | _, _ => 0

theorem primeLogGibbsFiniteIntensity_nonneg
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) (a b : Option P) :
    0 ≤ primeLogGibbsFiniteIntensity P u β a b := by
  cases a with
  | none =>
      cases b with
      | none => simp [primeLogGibbsFiniteIntensity]
      | some p =>
          exact mul_nonneg (Real.exp_pos _).le (primeDyadicWeight_pos u p.1).le
  | some p =>
      cases b <;>
        simp [primeLogGibbsFiniteIntensity, (primeDyadicWeight_pos u p.1).le]

/-- At zero inverse temperature, every reverse prime transition loses its Boltzmann bias and the
finite Gibbs intensity is exactly the symmetric KMS intensity. -/
theorem primeLogGibbsFiniteIntensity_zero_eq_primeLogKMSFiniteHermitianIntensity
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (a b : Option P) :
    primeLogGibbsFiniteIntensity P u 0 a b =
      primeLogKMSFiniteHermitianIntensity P u a b := by
  cases a <;> cases b <;>
    simp [primeLogGibbsFiniteIntensity, primeLogKMSFiniteHermitianIntensity]

theorem finiteGibbsStateWeight_primeLog_some_eq_boltzmann_mul_none
    (P : Finset Nat.Primes) (β : ℝ) (p : P) :
    _root_.HTGeometry.finiteGibbsStateWeight β (primeLogKMSFiniteEnergy P) (some p) =
      Real.exp (-β * primeLogSupport p.1) *
        _root_.HTGeometry.finiteGibbsStateWeight β
          (primeLogKMSFiniteEnergy P) none := by
  simp [_root_.HTGeometry.finiteGibbsStateWeight, primeLogKMSFiniteEnergy]
  rw [div_eq_mul_inv]

/-- The unsymmetrized Gibbs/Lehmann spectrum of the normalized Hermitian observable has exactly
the prescribed forward prime weight and its detailed-balance reverse. -/
theorem finiteGibbsTransitionIntensity_primeLogGibbsFiniteHermitianAmplitude
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ)
    (a b : Option P) :
    _root_.HTGeometry.finiteGibbsTransitionIntensity β
        (primeLogKMSFiniteEnergy P) (primeLogGibbsFiniteHermitianAmplitude P u β) a b =
      primeLogGibbsFiniteIntensity P u β a b := by
  cases a with
  | none =>
      cases b with
      | none =>
          simp [_root_.HTGeometry.finiteGibbsTransitionIntensity,
            primeLogGibbsFiniteHermitianAmplitude, primeLogGibbsFiniteIntensity]
      | some p =>
          let r := _root_.HTGeometry.finiteGibbsStateWeight β
            (primeLogKMSFiniteEnergy P) none
          have hr : 0 < r := _root_.HTGeometry.finiteGibbsStateWeight_pos _ _ _
          have hw : 0 ≤ primeDyadicWeight u p.1 := (primeDyadicWeight_pos u p.1).le
          rw [_root_.HTGeometry.finiteGibbsTransitionIntensity,
            finiteGibbsStateWeight_primeLog_some_eq_boltzmann_mul_none]
          simp only [primeLogGibbsFiniteHermitianAmplitude, primeLogGibbsFiniteIntensity]
          change Real.exp (-β * primeLogSupport p.1) * r *
              Complex.normSq (↑(Real.sqrt (primeDyadicWeight u p.1 / r))) =
            Real.exp (-β * primeLogSupport p.1) * primeDyadicWeight u p.1
          rw [Complex.normSq_ofReal, Real.mul_self_sqrt (div_nonneg hw hr.le)]
          rw [mul_assoc, mul_div_cancel₀ _ hr.ne']
  | some p =>
      cases b with
      | some q =>
          simp [_root_.HTGeometry.finiteGibbsTransitionIntensity,
            primeLogGibbsFiniteHermitianAmplitude, primeLogGibbsFiniteIntensity]
      | none =>
          let r := _root_.HTGeometry.finiteGibbsStateWeight β
            (primeLogKMSFiniteEnergy P) none
          have hr : 0 < r := _root_.HTGeometry.finiteGibbsStateWeight_pos _ _ _
          have hw : 0 ≤ primeDyadicWeight u p.1 := (primeDyadicWeight_pos u p.1).le
          simp only [_root_.HTGeometry.finiteGibbsTransitionIntensity,
            primeLogGibbsFiniteHermitianAmplitude, primeLogGibbsFiniteIntensity]
          change r * Complex.normSq
              (↑(Real.sqrt (primeDyadicWeight u p.1 / r))) = primeDyadicWeight u p.1
          rw [Complex.normSq_ofReal, Real.mul_self_sqrt (div_nonneg hw hr.le)]
          exact mul_div_cancel₀ _ hr.ne'

/-- The normalized finite prime-log Gibbs response is the symmetric KMS response at zero inverse
temperature. -/
theorem finiteGibbsTransitionIntensity_primeLog_zero_eq_kms
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ)
    (a b : Option P) :
    _root_.HTGeometry.finiteGibbsTransitionIntensity 0
        (primeLogKMSFiniteEnergy P) (primeLogGibbsFiniteHermitianAmplitude P u 0) a b =
      primeLogKMSFiniteHermitianIntensity P u a b := by
  rw [finiteGibbsTransitionIntensity_primeLogGibbsFiniteHermitianAmplitude,
    primeLogGibbsFiniteIntensity_zero_eq_primeLogKMSFiniteHermitianIntensity]

/-- Finite thermal Hermitian prime-log carrier. -/
def finitePrimeLogHermitianGibbsCarrier (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (β : ℝ) (z : ℂ) : ℂ :=
  ∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
    (((primeLogSupport p : ℂ) - z)⁻¹ -
      (Real.exp (-β * primeLogSupport p) : ℂ) *
        ((primeLogSupport p : ℂ) + z)⁻¹)

theorem neg_finiteTransitionPassiveResponse_primeLogGibbsFiniteIntensity
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) (z : ℂ) :
    -_root_.HTGeometry.finiteTransitionPassiveResponse
        (primeLogGibbsFiniteIntensity P u β) (primeLogKMSFiniteEnergy P) z =
      finitePrimeLogHermitianGibbsCarrier P u β z := by
  rw [_root_.HTGeometry.finiteTransitionPassiveResponse, Fintype.sum_option]
  simp only [primeLogGibbsFiniteIntensity]
  simp_rw [Fintype.sum_option]
  simp only [primeLogKMSFiniteEnergy, sub_zero, zero_sub, Complex.ofReal_zero,
    zero_div, Finset.sum_const_zero, add_zero, zero_add]
  rw [finitePrimeLogHermitianGibbsCarrier]
  calc
    -(∑ p : P, (↑(Real.exp (-β * primeLogSupport p.1) *
            primeDyadicWeight u p.1) : ℂ) /
          (z - (↑(-primeLogSupport p.1) : ℂ)) +
        ∑ p : P, (primeDyadicWeight u p.1 : ℂ) /
          (z - (primeLogSupport p.1 : ℂ))) =
        ∑ p : P, (primeDyadicWeight u p.1 : ℂ) *
          (((primeLogSupport p.1 : ℂ) - z)⁻¹ -
            (Real.exp (-β * primeLogSupport p.1) : ℂ) *
              ((primeLogSupport p.1 : ℂ) + z)⁻¹) := by
      rw [neg_add_rev, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      push_cast
      rw [show z - (-(primeLogSupport p.1 : ℂ)) =
          z + (primeLogSupport p.1 : ℂ) by ring,
        show z - (primeLogSupport p.1 : ℂ) =
          -((primeLogSupport p.1 : ℂ) - z) by ring,
        div_eq_mul_inv, div_eq_mul_inv, inv_neg]
      ring
    _ = ∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
        (((primeLogSupport p : ℂ) - z)⁻¹ -
          (Real.exp (-β * primeLogSupport p) : ℂ) *
            ((primeLogSupport p : ℂ) + z)⁻¹) := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach P (fun p => (primeDyadicWeight u p : ℂ) *
          (((primeLogSupport p : ℂ) - z)⁻¹ -
            (Real.exp (-β * primeLogSupport p) : ℂ) *
              ((primeLogSupport p : ℂ) + z)⁻¹)))

theorem neg_finiteGibbsResponse_primeLogGibbsFiniteHermitianAmplitude
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) (z : ℂ) :
    -_root_.HTGeometry.finiteTransitionPassiveResponse
        (_root_.HTGeometry.finiteGibbsTransitionIntensity β
          (primeLogKMSFiniteEnergy P) (primeLogGibbsFiniteHermitianAmplitude P u β))
        (primeLogKMSFiniteEnergy P) z =
      finitePrimeLogHermitianGibbsCarrier P u β z := by
  rw [show _root_.HTGeometry.finiteGibbsTransitionIntensity β
      (primeLogKMSFiniteEnergy P) (primeLogGibbsFiniteHermitianAmplitude P u β) =
      primeLogGibbsFiniteIntensity P u β by
    funext a b
    exact finiteGibbsTransitionIntensity_primeLogGibbsFiniteHermitianAmplitude
      P u β a b]
  exact neg_finiteTransitionPassiveResponse_primeLogGibbsFiniteIntensity P u β z

theorem finitePrimeLogHermitianGibbsCarrier_zero
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (z : ℂ) :
    finitePrimeLogHermitianGibbsCarrier P u 0 z =
      finitePrimeLogHermitianKMSCarrier P u z := by
  simp [finitePrimeLogHermitianGibbsCarrier, finitePrimeLogHermitianKMSCarrier]

private theorem tendsto_exp_neg_mul_atTop_primeLog (p : Nat.Primes) :
    Filter.Tendsto (fun β : ℝ => Real.exp (-β * primeLogSupport p))
      Filter.atTop (nhds 0) := by
  have hpos : Filter.Tendsto (fun β : ℝ => primeLogSupport p * β)
      Filter.atTop Filter.atTop :=
    tendsto_id.const_mul_atTop (primeLogSupport_pos p)
  have hlin : Filter.Tendsto (fun β : ℝ => β * (-primeLogSupport p))
      Filter.atTop Filter.atBot := by
    convert tendsto_neg_atTop_atBot.comp hpos using 1
    funext β
    simp [mul_comm]
  convert Real.tendsto_exp_atBot.comp hlin using 1
  funext β
  congr 1
  ring

/-- The zero-temperature limit suppresses every reverse Boltzmann transition and recovers the
existing directed finite prime-log carrier. -/
theorem finitePrimeLogHermitianGibbsCarrier_tendsto_finitePrimeLogHerglotz
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (z : ℂ) :
    Filter.Tendsto (fun β : ℝ => finitePrimeLogHermitianGibbsCarrier P u β z)
      Filter.atTop (nhds (finitePrimeLogHerglotz P u z)) := by
  rw [finitePrimeLogHerglotz]
  unfold finitePrimeLogHermitianGibbsCarrier
  apply tendsto_finsetSum
  intro p hp
  have hexp : Filter.Tendsto
      (fun β : ℝ => (Real.exp (-β * primeLogSupport p) : ℂ))
      Filter.atTop (nhds 0) :=
    (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_exp_neg_mul_atTop_primeLog p)
  have hmirror := hexp.mul
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℝ => ((primeLogSupport p : ℂ) + z)⁻¹)
      Filter.atTop (nhds (((primeLogSupport p : ℂ) + z)⁻¹)))
  have hmirror0 : Filter.Tendsto
      (fun β : ℝ => (Real.exp (-β * primeLogSupport p) : ℂ) *
        ((primeLogSupport p : ℂ) + z)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa using hmirror
  have hbracket :=
    (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℝ => ((primeLogSupport p : ℂ) - z)⁻¹)
      Filter.atTop (nhds (((primeLogSupport p : ℂ) - z)⁻¹))).sub hmirror0
  have hbracket' : Filter.Tendsto
      (fun β : ℝ => ((primeLogSupport p : ℂ) - z)⁻¹ -
        (Real.exp (-β * primeLogSupport p) : ℂ) *
          ((primeLogSupport p : ℂ) + z)⁻¹)
      Filter.atTop (nhds (((primeLogSupport p : ℂ) - z)⁻¹)) := by
    simpa using hbracket
  simpa using
    (tendsto_const_nhds.mul hbracket' : Filter.Tendsto
      (fun β : ℝ => (primeDyadicWeight u p : ℂ) *
        (((primeLogSupport p : ℂ) - z)⁻¹ -
          (Real.exp (-β * primeLogSupport p) : ℂ) *
            ((primeLogSupport p : ℂ) + z)⁻¹))
      Filter.atTop
      (nhds ((primeDyadicWeight u p : ℂ) *
        ((primeLogSupport p : ℂ) - z)⁻¹)))

/-- The existing directed finite carrier is a zero-temperature limit of explicit Hermitian Gibbs
responses. -/
theorem finiteHermitianGibbsResponse_tendsto_finitePrimeLogHerglotz
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (z : ℂ) :
    Filter.Tendsto
      (fun β : ℝ =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteGibbsTransitionIntensity β
            (primeLogKMSFiniteEnergy P) (primeLogGibbsFiniteHermitianAmplitude P u β))
          (primeLogKMSFiniteEnergy P) z)
      Filter.atTop (nhds (finitePrimeLogHerglotz P u z)) := by
  simpa only [neg_finiteGibbsResponse_primeLogGibbsFiniteHermitianAmplitude] using
    finitePrimeLogHermitianGibbsCarrier_tendsto_finitePrimeLogHerglotz P u z

/-- Universal-gauge specialization: each finite subsystem of the existing HT carrier is the cold
limit of an explicit Hermitian Gibbs response. -/
theorem universalFacetOrbitGauge_finiteHermitianGibbsResponse_tendsto
    (P : Finset Nat.Primes) (z : ℂ) :
    Filter.Tendsto
      (fun β : ℝ =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteGibbsTransitionIntensity β
            (primeLogKMSFiniteEnergy P)
            (primeLogGibbsFiniteHermitianAmplitude P
              (fun q => universalFacetOrbitGauge q) β))
          (primeLogKMSFiniteEnergy P) z)
      Filter.atTop
      (nhds (finitePrimeLogHerglotz P
        (fun q => universalFacetOrbitGauge q) z)) :=
  finiteHermitianGibbsResponse_tendsto_finitePrimeLogHerglotz P
    (fun q => universalFacetOrbitGauge q) z

/-- The universal orientation is selected by first cooling each explicit Hermitian Gibbs system
and then taking its finite-prime thermodynamic limit. -/
def UniversalPrimeOrientationHermitianGibbsColdLimit
    (ε : Nat.Primes → Bool) : Prop :=
  ∀ z : ℂ, 0 < z.im →
    ∃ cold : Finset Nat.Primes → ℂ,
      (∀ P,
        Filter.Tendsto
          (fun β : ℝ =>
            -_root_.HTGeometry.finiteTransitionPassiveResponse
              (_root_.HTGeometry.finiteGibbsTransitionIntensity β
                (primeLogKMSFiniteEnergy P)
                (primeLogGibbsFiniteHermitianAmplitude P
                  (fun q => universalFacetOrbitGauge q) β))
              (primeLogKMSFiniteEnergy P) z)
          Filter.atTop (nhds (cold P))) ∧
      Filter.Tendsto cold Filter.atTop
        (nhds (universalPrimeOrientationLimit ε z))

/-- **Hermitian Gibbs selection of the canonical prime orientation.**  The iterated cold and
thermodynamic limit of the explicit self-adjoint finite systems selects exactly the all-positive
prime orientation. -/
theorem universalPrimeOrientationHermitianGibbsColdLimit_iff
    (ε : Nat.Primes → Bool) :
    UniversalPrimeOrientationHermitianGibbsColdLimit ε ↔
      ε = fun _ => false := by
  constructor
  · intro hlimit
    rw [← universalPrimeOrientationLimit_nonneg_iff_allPositive]
    intro z hz
    obtain ⟨cold, hcold, htherm⟩ := hlimit z hz
    have hcoldEq : cold = fun P =>
        finitePrimeLogHerglotz P (fun q => universalFacetOrbitGauge q) z := by
      funext P
      exact tendsto_nhds_unique (hcold P)
        (universalFacetOrbitGauge_finiteHermitianGibbsResponse_tendsto P z)
    have hcoldFull : Filter.Tendsto cold Filter.atTop
        (nhds (primeLogHerglotz (fun q => universalFacetOrbitGauge q) z)) := by
      rw [hcoldEq]
      exact finitePrimeLogHerglotz_tendsto_primeLogHerglotz
        (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
        (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
          (universalFacetOrbitGauge.norm_coe_le_norm q)) z hz
    have heq : universalPrimeOrientationLimit ε z =
        primeLogHerglotz (fun q => universalFacetOrbitGauge q) z :=
      tendsto_nhds_unique htherm hcoldFull
    rw [heq]
    exact universalFacetOrbitGauge_primeLogHerglotz_im_nonneg hz
  · rintro rfl z hz
    refine ⟨fun P =>
      finitePrimeLogHerglotz P (fun q => universalFacetOrbitGauge q) z, ?_, ?_⟩
    · intro P
      exact universalFacetOrbitGauge_finiteHermitianGibbsResponse_tendsto P z
    · simpa only [universalPrimeOrientationLimit_empty] using
        finitePrimeLogHerglotz_tendsto_primeLogHerglotz
          (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
          (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
            (universalFacetOrbitGauge.norm_coe_le_norm q)) z hz

/-- Constraint-orientation specialization of the Hermitian Gibbs cold-limit selector. -/
theorem canonicalConstraintOrientationLimit_primeCarrier_is_HermitianGibbsColdLimit_iff
    (X : CanonicalConstraintOrientationLimit ℕ Nat.Primes) :
    UniversalPrimeOrientationHermitianGibbsColdLimit X.2 ↔
      X.2 = fun _ => false :=
  universalPrimeOrientationHermitianGibbsColdLimit_iff X.2

end

end GaloisForLFunctions.HTGeometry
