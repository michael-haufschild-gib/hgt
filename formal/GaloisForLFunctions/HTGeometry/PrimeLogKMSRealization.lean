import GaloisForLFunctions.HTGeometry.FiniteKMSFluctuationDissipation
import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz
import GaloisForLFunctions.HTGeometry.UniversalPrimeOrientationLimit
import Mathlib.Analysis.Complex.LocallyUniformLimit

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

/-- Positive coefficient multiplying the squared amplitude in the energy-weighted finite KMS
fluctuation--dissipation transform on a vacuum-to-prime transition. -/
def primeLogKMSFiniteDissipativeNormalizer (P : Finset Nat.Primes)
    (β : ℝ) (p : P) : ℝ :=
  primeLogSupport p.1 *
    (2 * Real.sinh (β * primeLogSupport p.1 / 2) *
      _root_.HTGeometry.finiteKMSWightmanWeight β
        (primeLogKMSFiniteEnergy P) (some p) none)

/-- At positive inverse temperature, every vacuum-to-prime dissipative normalizer is strictly
positive. -/
theorem primeLogKMSFiniteDissipativeNormalizer_pos
    (P : Finset Nat.Primes) (β : ℝ) (hβ : 0 < β) (p : P) :
    0 < primeLogKMSFiniteDissipativeNormalizer P β p := by
  rw [primeLogKMSFiniteDissipativeNormalizer]
  exact mul_pos (primeLogSupport_pos p.1)
    (mul_pos
      (mul_pos (by norm_num)
        (Real.sinh_pos_iff.mpr
          (div_pos (mul_pos hβ (primeLogSupport_pos p.1)) (by norm_num))))
      (_root_.HTGeometry.finiteKMSWightmanWeight_pos _ _ _ _))

/-- Directed jump amplitude normalized against the positive KMS dissipative oscillator strength.
Its energy-weighted FDT intensity is the prescribed dyadic prime weight. -/
def primeLogKMSFiniteDissipativeAmplitude (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (β : ℝ) : Option P → Option P → ℂ
  | some p, none =>
      (Real.sqrt (primeDyadicWeight u p.1 /
        primeLogKMSFiniteDissipativeNormalizer P β p) : ℂ)
  | _, _ => 0

/-- **Finite prime-log fluctuation--dissipation realization.**  At positive inverse temperature,
the energy-weighted FDT intensity of the normalized finite multiplicative Hamiltonian jump is
exactly the prescribed prime-log carrier intensity. -/
theorem finiteKMSDissipativeTransitionIntensity_primeLogKMSFiniteAmplitude
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) (hβ : 0 < β)
    (a b : Option P) :
    _root_.HTGeometry.finiteKMSDissipativeTransitionIntensity β
        (primeLogKMSFiniteEnergy P)
        (primeLogKMSFiniteDissipativeAmplitude P u β) a b =
      primeLogKMSFiniteIntensity P u a b := by
  cases a with
  | none =>
      cases b <;> simp [primeLogKMSFiniteDissipativeAmplitude,
        primeLogKMSFiniteIntensity,
        _root_.HTGeometry.finiteKMSDissipativeTransitionIntensity,
        _root_.HTGeometry.finiteKMSWightmanTransitionIntensity,
        _root_.HTGeometry.wightmanTransitionIntensity]
  | some p =>
      cases b with
      | some q =>
          simp [primeLogKMSFiniteDissipativeAmplitude, primeLogKMSFiniteIntensity,
            _root_.HTGeometry.finiteKMSDissipativeTransitionIntensity,
            _root_.HTGeometry.finiteKMSWightmanTransitionIntensity,
            _root_.HTGeometry.wightmanTransitionIntensity]
      | none =>
          let d := primeLogKMSFiniteDissipativeNormalizer P β p
          have hd : 0 < d := primeLogKMSFiniteDissipativeNormalizer_pos P β hβ p
          have hweight : 0 ≤ primeDyadicWeight u p.1 :=
            (primeDyadicWeight_pos u p.1).le
          simp only [_root_.HTGeometry.finiteKMSDissipativeTransitionIntensity,
            _root_.HTGeometry.finiteKMSWightmanTransitionIntensity,
            _root_.HTGeometry.wightmanTransitionIntensity,
            primeLogKMSFiniteDissipativeAmplitude, primeLogKMSFiniteIntensity]
          simp only [primeLogKMSFiniteEnergy_gap]
          change primeLogSupport p.1 *
              (2 * Real.sinh (β * primeLogSupport p.1 / 2) *
                (_root_.HTGeometry.finiteKMSWightmanWeight β
                    (primeLogKMSFiniteEnergy P) (some p) none *
                  Complex.normSq
                    (↑(Real.sqrt (primeDyadicWeight u p.1 / d))))) =
            primeDyadicWeight u p.1
          calc
            _ = d * Complex.normSq
                (↑(Real.sqrt (primeDyadicWeight u p.1 / d))) := by
              simp only [d, primeLogKMSFiniteDissipativeNormalizer]
              ring
            _ = d * (primeDyadicWeight u p.1 / d) := by
              rw [Complex.normSq_ofReal,
                Real.mul_self_sqrt (div_nonneg hweight hd.le)]
            _ = primeDyadicWeight u p.1 := mul_div_cancel₀ _ hd.ne'

/-- Finite truncation of the positive prime-log Herglotz carrier. -/
def finitePrimeLogHerglotz (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (z : ℂ) : ℂ :=
  ∑ p ∈ P, (primeDyadicWeight u p : ℂ) * ((primeLogSupport p : ℂ) - z)⁻¹

/-- Every finite prime-log carrier is holomorphic on the upper half-plane. -/
theorem differentiableOn_finitePrimeLogHerglotz_upperHalfPlane
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) :
    DifferentiableOn ℂ (finitePrimeLogHerglotz P u) upperHalfPlane := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  change DifferentiableAt ℂ
    (fun z => ∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
      ((primeLogSupport p : ℂ) - z)⁻¹) z
  apply DifferentiableAt.fun_sum
  intro p hp
  apply (differentiableAt_const (c := (primeDyadicWeight u p : ℂ))).mul
  apply ((differentiableAt_const (c := (primeLogSupport p : ℂ))).sub
    differentiableAt_id).inv
  intro hzero
  have heq : (primeLogSupport p : ℂ) = z := sub_eq_zero.mp hzero
  have him : z.im = 0 := by rw [← heq]; simp
  change 0 < z.im at hz
  linarith

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

/-- The positive finite KMS dissipative response is exactly the same finite prime-log Herglotz
carrier.  This is the direct fluctuation--dissipation consumer of the generic identity. -/
theorem neg_finiteKMSDissipativeResponse_primeLogKMSFiniteAmplitude
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) (hβ : 0 < β) (z : ℂ) :
    -_root_.HTGeometry.finiteTransitionPassiveResponse
        (_root_.HTGeometry.finiteKMSDissipativeTransitionIntensity β
          (primeLogKMSFiniteEnergy P)
          (primeLogKMSFiniteDissipativeAmplitude P u β))
        (primeLogKMSFiniteEnergy P) z = finitePrimeLogHerglotz P u z := by
  rw [show _root_.HTGeometry.finiteKMSDissipativeTransitionIntensity β
      (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteDissipativeAmplitude P u β) =
      primeLogKMSFiniteIntensity P u by
    funext a b
    exact finiteKMSDissipativeTransitionIntensity_primeLogKMSFiniteAmplitude
      P u β hβ a b]
  exact neg_finiteTransitionPassiveResponse_primeLogKMSFiniteIntensity P u z

/-- The explicitly normalized finite KMS response is holomorphic on the upper half-plane. -/
theorem differentiableOn_neg_finiteKMSWightmanResponse_upperHalfPlane
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) :
    DifferentiableOn ℂ
      (fun z => -_root_.HTGeometry.finiteTransitionPassiveResponse
        (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
          (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteAmplitude P u β))
        (primeLogKMSFiniteEnergy P) z) upperHalfPlane := by
  rw [show (fun z => -_root_.HTGeometry.finiteTransitionPassiveResponse
      (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
        (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteAmplitude P u β))
      (primeLogKMSFiniteEnergy P) z) = finitePrimeLogHerglotz P u by
    funext z
    exact neg_finiteKMSWightmanResponse_primeLogKMSFiniteAmplitude P u β z]
  exact differentiableOn_finitePrimeLogHerglotz_upperHalfPlane P u

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
    (finitePrimeLogHerglotz_tendstoLocallyUniformlyOn_primeLogHerglotz u C hu).congr
  intro P z _
  exact (neg_finiteKMSWightmanResponse_primeLogKMSFiniteAmplitude P u β z).symm

/-- Linear-response susceptibilities of the finite KMS systems converge locally uniformly to the
derivative of the full prime-log carrier.  This is the first jet-level interface needed by the
existing upper-end differential and Cauchy-jet consumers. -/
theorem finiteKMSWightmanResponse_deriv_tendstoLocallyUniformlyOn_primeLogHerglotz
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) (β : ℝ) :
    TendstoLocallyUniformlyOn
      (deriv ∘ fun P : Finset Nat.Primes => fun z =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
            (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteAmplitude P u β))
          (primeLogKMSFiniteEnergy P) z)
      (deriv (primeLogHerglotz u)) Filter.atTop upperHalfPlane := by
  apply
    (finiteKMSWightmanResponse_tendstoLocallyUniformlyOn_primeLogHerglotz u C hu β).deriv
  · exact Filter.Eventually.of_forall fun P =>
      differentiableOn_neg_finiteKMSWightmanResponse_upperHalfPlane P u β
  · exact isOpen_upperHalfPlane

/-- At every upper-half-plane point, the finite KMS response susceptibilities converge to the
prime-log carrier susceptibility. -/
theorem finiteKMSWightmanResponse_deriv_tendsto_primeLogHerglotz
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (β : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Filter.Tendsto
      (fun P : Finset Nat.Primes =>
        deriv (fun w => -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
            (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteAmplitude P u β))
          (primeLogKMSFiniteEnergy P) w) z)
      Filter.atTop (nhds (deriv (primeLogHerglotz u) z)) := by
  simpa only [Function.comp_apply] using
    (finiteKMSWightmanResponse_deriv_tendstoLocallyUniformlyOn_primeLogHerglotz
      u C hu β).tendsto_at hz

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

/-- The universal HT carrier is the locally uniform thermodynamic limit of the canonical finite
KMS response net on the whole upper half-plane. -/
theorem universalFacetOrbitGauge_finiteKMSWightmanResponse_tendstoLocallyUniformlyOn
    (β : ℝ) :
    TendstoLocallyUniformlyOn
      (fun P : Finset Nat.Primes => fun z =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
            (primeLogKMSFiniteEnergy P)
            (primeLogKMSFiniteAmplitude P (fun q => universalFacetOrbitGauge q) β))
          (primeLogKMSFiniteEnergy P) z)
      (primeLogHerglotz (fun q => universalFacetOrbitGauge q))
      Filter.atTop upperHalfPlane := by
  exact finiteKMSWightmanResponse_tendstoLocallyUniformlyOn_primeLogHerglotz
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q)) β

/-- The first response jets of the finite KMS models converge locally uniformly to the first jet
of the fixed universal HT carrier. -/
theorem universalFacetOrbitGauge_finiteKMSWightmanResponse_deriv_tendstoLocallyUniformlyOn
    (β : ℝ) :
    TendstoLocallyUniformlyOn
      (deriv ∘ fun P : Finset Nat.Primes => fun z =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
            (primeLogKMSFiniteEnergy P)
            (primeLogKMSFiniteAmplitude P (fun q => universalFacetOrbitGauge q) β))
          (primeLogKMSFiniteEnergy P) z)
      (deriv (primeLogHerglotz (fun q => universalFacetOrbitGauge q)))
      Filter.atTop upperHalfPlane := by
  exact finiteKMSWightmanResponse_deriv_tendstoLocallyUniformlyOn_primeLogHerglotz
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q)) β

/-- **KMS selection of the canonical prime orientation.**  An infinite Boolean prime orientation
is the pointwise thermodynamic limit of the canonical finite multiplicative KMS responses exactly
when every residue has the positive orientation.  Thus the existing analytic orientation selector
is also an exact quantum-statistical response selector. -/
theorem universalPrimeOrientationLimit_is_canonicalKMSLimit_iff
    (ε : Nat.Primes → Bool) (β : ℝ) :
    (∀ z : ℂ, 0 < z.im →
      Filter.Tendsto
        (fun P : Finset Nat.Primes =>
          -_root_.HTGeometry.finiteTransitionPassiveResponse
            (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
              (primeLogKMSFiniteEnergy P)
              (primeLogKMSFiniteAmplitude P (fun q => universalFacetOrbitGauge q) β))
            (primeLogKMSFiniteEnergy P) z)
        Filter.atTop (nhds (universalPrimeOrientationLimit ε z))) ↔
      ε = fun _ => false := by
  constructor
  · intro hlimit
    rw [← universalPrimeOrientationLimit_nonneg_iff_allPositive]
    intro z hz
    have heq : universalPrimeOrientationLimit ε z =
        primeLogHerglotz (fun q => universalFacetOrbitGauge q) z :=
      tendsto_nhds_unique (hlimit z hz)
        (universalFacetOrbitGauge_finiteKMSWightmanResponse_tendsto β z hz)
    rw [heq]
    exact universalFacetOrbitGauge_primeLogHerglotz_im_nonneg hz
  · rintro rfl z hz
    simpa only [universalPrimeOrientationLimit_empty] using
      universalFacetOrbitGauge_finiteKMSWightmanResponse_tendsto β z hz

/-- The KMS selector applies directly to the prime coordinate of the existing canonical
constraint-orientation limit. -/
theorem canonicalConstraintOrientationLimit_primeCarrier_is_canonicalKMSLimit_iff
    (X : CanonicalConstraintOrientationLimit ℕ Nat.Primes) (β : ℝ) :
    (∀ z : ℂ, 0 < z.im →
      Filter.Tendsto
        (fun P : Finset Nat.Primes =>
          -_root_.HTGeometry.finiteTransitionPassiveResponse
            (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
              (primeLogKMSFiniteEnergy P)
              (primeLogKMSFiniteAmplitude P (fun q => universalFacetOrbitGauge q) β))
            (primeLogKMSFiniteEnergy P) z)
        Filter.atTop (nhds (universalPrimeOrientationLimit X.2 z))) ↔
      X.2 = fun _ => false :=
  universalPrimeOrientationLimit_is_canonicalKMSLimit_iff X.2 β

end

end GaloisForLFunctions.HTGeometry
