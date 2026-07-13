import GaloisForLFunctions.HTGeometry.FinitePassiveResponse
import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz
import GaloisForLFunctions.HTGeometry.UniversalFiniteConstraintCarrier

/-!
# Prime-log carriers as finite KMS response values

The multiplicative Hamiltonian has energy `log n` on `|n⟩`, so the directed dilation transition
`|1⟩ → |p⟩` has the exact Liouvillian frequency `log p`.  This is precisely the support of the
prime-log Herglotz carrier already used throughout HT geometry.

For a finite set of primes, this file constructs a vacuum plus one excited level per prime.  At
every inverse temperature, the observable amplitude is normalized by the strictly positive KMS
half-density so that its transition intensity is exactly the prescribed dyadic prime weight.  The
negative finite passive response is then exactly the finite prime-log Herglotz sum, not merely an
analogy or a sign consequence.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The finite multiplicative Hamiltonian restricted to the vacuum and a finite set of prime
levels. -/
def primeLogKMSFiniteEnergy (P : Finset Nat.Primes) : Option P → ℝ
  | none => 0
  | some p => primeLogSupport p.1

/-- The vacuum-to-prime Liouvillian gap is exactly the prime logarithm. -/
@[simp] theorem primeLogKMSFiniteEnergy_gap (P : Finset Nat.Primes) (p : P) :
    primeLogKMSFiniteEnergy P (some p) - primeLogKMSFiniteEnergy P none =
      primeLogSupport p.1 := by
  simp [primeLogKMSFiniteEnergy]

/-- Directed vacuum-to-prime transition intensities equal the carrier's dyadic weights. -/
def primeLogKMSFiniteIntensity (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) : Option P → Option P → ℝ
  | some p, none => primeDyadicWeight u p.1
  | _, _ => 0

/-- The carrier transition intensities are nonnegative. -/
theorem primeLogKMSFiniteIntensity_nonneg (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (a b : Option P) :
    0 ≤ primeLogKMSFiniteIntensity P u a b := by
  cases a <;> cases b <;>
    simp [primeLogKMSFiniteIntensity, (primeDyadicWeight_pos u _).le]

/-- KMS-normalized directed observable whose transition intensities reproduce the carrier
weights exactly. -/
def primeLogKMSFiniteAmplitude (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (β : ℝ) : Option P → Option P → ℂ
  | some p, none =>
      (Real.sqrt (primeDyadicWeight u p.1 /
        _root_.HTGeometry.finiteKMSWightmanWeight β
          (primeLogKMSFiniteEnergy P) (some p) none) : ℂ)
  | _, _ => 0

/-- The canonical KMS/Wightman intensity of the normalized observable is exactly the requested
prime-log carrier intensity. -/
theorem finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteAmplitude
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ)
    (a b : Option P) :
    _root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
        (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteAmplitude P u β) a b =
      primeLogKMSFiniteIntensity P u a b := by
  cases a with
  | none =>
      cases b <;> simp [primeLogKMSFiniteAmplitude, primeLogKMSFiniteIntensity,
        _root_.HTGeometry.finiteKMSWightmanTransitionIntensity,
        _root_.HTGeometry.wightmanTransitionIntensity]
  | some p =>
      cases b with
      | some q =>
          simp [primeLogKMSFiniteAmplitude, primeLogKMSFiniteIntensity,
            _root_.HTGeometry.finiteKMSWightmanTransitionIntensity,
            _root_.HTGeometry.wightmanTransitionIntensity]
      | none =>
          let w := _root_.HTGeometry.finiteKMSWightmanWeight β
            (primeLogKMSFiniteEnergy P) (some p) none
          have hw : 0 < w := _root_.HTGeometry.finiteKMSWightmanWeight_pos _ _ _ _
          have hweight : 0 ≤ primeDyadicWeight u p.1 :=
            (primeDyadicWeight_pos u p.1).le
          simp only [_root_.HTGeometry.finiteKMSWightmanTransitionIntensity,
            _root_.HTGeometry.wightmanTransitionIntensity,
            primeLogKMSFiniteAmplitude, primeLogKMSFiniteIntensity]
          change w * Complex.normSq
              (↑(Real.sqrt (primeDyadicWeight u p.1 / w))) = primeDyadicWeight u p.1
          rw [Complex.normSq_ofReal,
            Real.mul_self_sqrt (div_nonneg hweight hw.le)]
          exact mul_div_cancel₀ _ hw.ne'

/-- Finite truncation of the positive prime-log Herglotz carrier. -/
def finitePrimeLogHerglotz (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (z : ℂ) : ℂ :=
  ∑ p ∈ P, (primeDyadicWeight u p : ℂ) * ((primeLogSupport p : ℂ) - z)⁻¹

/-- Exact response identity before inserting the canonical KMS amplitude. -/
theorem neg_finiteTransitionPassiveResponse_primeLogKMSFiniteIntensity
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (z : ℂ) :
    -_root_.HTGeometry.finiteTransitionPassiveResponse
        (primeLogKMSFiniteIntensity P u) (primeLogKMSFiniteEnergy P) z =
      finitePrimeLogHerglotz P u z := by
  rw [_root_.HTGeometry.finiteTransitionPassiveResponse, Fintype.sum_option]
  simp only [primeLogKMSFiniteIntensity]
  simp_rw [Fintype.sum_option]
  simp only [primeLogKMSFiniteEnergy, sub_zero, Complex.ofReal_zero, zero_div,
    Finset.sum_const_zero, add_zero, zero_add]
  rw [finitePrimeLogHerglotz]
  calc
    -(∑ p : P, (primeDyadicWeight u p.1 : ℂ) /
        (z - (primeLogSupport p.1 : ℂ))) =
        ∑ p : P, (primeDyadicWeight u p.1 : ℂ) *
          ((primeLogSupport p.1 : ℂ) - z)⁻¹ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [show z - (primeLogSupport p.1 : ℂ) =
          -((primeLogSupport p.1 : ℂ) - z) by ring,
        div_eq_mul_inv, inv_neg]
      ring
    _ = ∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
        ((primeLogSupport p : ℂ) - z)⁻¹ := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach P (fun p => (primeDyadicWeight u p : ℂ) *
          ((primeLogSupport p : ℂ) - z)⁻¹))

/-- **Finite prime-log KMS realization.**  At every inverse temperature, the finite prime-log
Herglotz carrier is exactly the negative passive response of the explicitly normalized finite
multiplicative Hamiltonian. -/
theorem neg_finiteKMSWightmanResponse_primeLogKMSFiniteAmplitude
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) (z : ℂ) :
    -_root_.HTGeometry.finiteTransitionPassiveResponse
        (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
          (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteAmplitude P u β))
        (primeLogKMSFiniteEnergy P) z = finitePrimeLogHerglotz P u z := by
  rw [show _root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
      (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteAmplitude P u β) =
      primeLogKMSFiniteIntensity P u by
    funext a b
    exact finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteAmplitude P u β a b]
  exact neg_finiteTransitionPassiveResponse_primeLogKMSFiniteIntensity P u z

/-- Finite prime subsystems converge pointwise to the full prime-log Herglotz carrier along the
directed set of finite prime sets. -/
theorem finitePrimeLogHerglotz_tendsto_primeLogHerglotz
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (z : ℂ) (hz : 0 < z.im) :
    Filter.Tendsto (fun P : Finset Nat.Primes => finitePrimeLogHerglotz P u z)
      Filter.atTop (nhds (primeLogHerglotz u z)) := by
  simpa only [finitePrimeLogHerglotz, primeLogHerglotz, discreteHerglotz] using
    (summable_discreteHerglotz_term primeLogSupport (primeDyadicWeight u) z hz
      (summable_norm_primeDyadicWeight u C hu)).hasSum

/-- The finite prime carriers converge locally uniformly on the upper half-plane, not merely
pointwise.  This is the normal-family strength needed by analytic-continuation consumers. -/
theorem finitePrimeLogHerglotz_tendstoLocallyUniformlyOn_primeLogHerglotz
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    TendstoLocallyUniformlyOn
      (fun P : Finset Nat.Primes => finitePrimeLogHerglotz P u)
      (primeLogHerglotz u) Filter.atTop upperHalfPlane := by
  simpa only [HasSumLocallyUniformlyOn, finitePrimeLogHerglotz,
    primeLogHerglotz, discreteHerglotz] using
    (summableLocallyUniformlyOn_discreteHerglotz primeLogSupport
      (primeDyadicWeight u)
      (summable_norm_primeDyadicWeight u C hu)).hasSumLocallyUniformlyOn

/-- **Prime-log KMS thermodynamic limit.**  The full bounded-gauge prime-log Herglotz carrier is
the pointwise finite-subsystem limit of explicit canonical KMS/Wightman responses at every inverse
temperature. -/
theorem finiteKMSWightmanResponse_tendsto_primeLogHerglotz
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (β : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Filter.Tendsto
      (fun P : Finset Nat.Primes =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
            (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteAmplitude P u β))
          (primeLogKMSFiniteEnergy P) z)
      Filter.atTop (nhds (primeLogHerglotz u z)) := by
  simpa only [neg_finiteKMSWightmanResponse_primeLogKMSFiniteAmplitude] using
    finitePrimeLogHerglotz_tendsto_primeLogHerglotz u C hu z hz

/-- The explicit finite KMS responses converge locally uniformly to the full carrier. -/
theorem finiteKMSWightmanResponse_tendstoLocallyUniformlyOn_primeLogHerglotz
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (β : ℝ) :
    TendstoLocallyUniformlyOn
      (fun P : Finset Nat.Primes => fun z =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
            (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteAmplitude P u β))
          (primeLogKMSFiniteEnergy P) z)
      (primeLogHerglotz u) Filter.atTop upperHalfPlane := by
  apply
    (finitePrimeLogHerglotz_tendstoLocallyUniformlyOn_primeLogHerglotz u C hu).congr'
  exact Filter.Eventually.of_forall fun P z _ =>
    neg_finiteKMSWightmanResponse_primeLogKMSFiniteAmplitude P u β z

/-- The particular universal carrier used to realize all finite HT constraint complexes inherits
the finite KMS/Wightman thermodynamic realization directly. -/
theorem universalFacetOrbitGauge_finiteKMSWightmanResponse_tendsto
    (β : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Filter.Tendsto
      (fun P : Finset Nat.Primes =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
            (primeLogKMSFiniteEnergy P)
            (primeLogKMSFiniteAmplitude P (fun q => universalFacetOrbitGauge q) β))
          (primeLogKMSFiniteEnergy P) z)
      Filter.atTop
      (nhds (primeLogHerglotz (fun q => universalFacetOrbitGauge q) z)) := by
  exact finiteKMSWightmanResponse_tendsto_primeLogHerglotz
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q)) β z hz

end

end GaloisForLFunctions.HTGeometry
