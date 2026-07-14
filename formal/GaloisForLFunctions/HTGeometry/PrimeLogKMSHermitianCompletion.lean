import GaloisForLFunctions.HTGeometry.FiniteKMSDetailedBalance
import GaloisForLFunctions.HTGeometry.PrimeLogKMSRealization

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Hermitian completion of the directed vacuum-to-prime observable. -/
def primeLogKMSFiniteHermitianAmplitude (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (β : ℝ) : Option P → Option P → ℂ
  | some p, none =>
      (Real.sqrt (primeDyadicWeight u p.1 /
        _root_.HTGeometry.finiteKMSWightmanWeight β
          (primeLogKMSFiniteEnergy P) (some p) none) : ℂ)
  | none, some p =>
      (Real.sqrt (primeDyadicWeight u p.1 /
        _root_.HTGeometry.finiteKMSWightmanWeight β
          (primeLogKMSFiniteEnergy P) (some p) none) : ℂ)
  | _, _ => 0

theorem primeLogKMSFiniteHermitianAmplitude_hermitian
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) :
    ∀ a b, primeLogKMSFiniteHermitianAmplitude P u β b a =
      star (primeLogKMSFiniteHermitianAmplitude P u β a b) := by
  intro a b
  cases a <;> cases b <;>
    simp [primeLogKMSFiniteHermitianAmplitude]

/-- Symmetric transition intensities of the Hermitian prime-log observable. -/
def primeLogKMSFiniteHermitianIntensity (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) : Option P → Option P → ℝ
  | some p, none => primeDyadicWeight u p.1
  | none, some p => primeDyadicWeight u p.1
  | _, _ => 0

theorem primeLogKMSFiniteHermitianIntensity_symm
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (a b : Option P) :
    primeLogKMSFiniteHermitianIntensity P u a b =
      primeLogKMSFiniteHermitianIntensity P u b a := by
  cases a <;> cases b <;> simp [primeLogKMSFiniteHermitianIntensity]

theorem primeLogKMSFiniteHermitianIntensity_nonneg
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (a b : Option P) :
    0 ≤ primeLogKMSFiniteHermitianIntensity P u a b := by
  cases a <;> cases b <;>
    simp [primeLogKMSFiniteHermitianIntensity, (primeDyadicWeight_pos u _).le]

theorem finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteHermitianAmplitude
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ)
    (a b : Option P) :
    _root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
        (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β) a b =
      primeLogKMSFiniteHermitianIntensity P u a b := by
  cases a with
  | none =>
      cases b with
      | none =>
          simp [primeLogKMSFiniteHermitianAmplitude,
            primeLogKMSFiniteHermitianIntensity,
            _root_.HTGeometry.finiteKMSWightmanTransitionIntensity,
            _root_.HTGeometry.wightmanTransitionIntensity]
      | some p =>
          rw [_root_.HTGeometry.finiteKMSWightmanTransitionIntensity_symm β
            (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β)
            (primeLogKMSFiniteHermitianAmplitude_hermitian P u β)]
          let w := _root_.HTGeometry.finiteKMSWightmanWeight β
            (primeLogKMSFiniteEnergy P) (some p) none
          have hw : 0 < w := _root_.HTGeometry.finiteKMSWightmanWeight_pos _ _ _ _
          have hweight : 0 ≤ primeDyadicWeight u p.1 :=
            (primeDyadicWeight_pos u p.1).le
          simp only [_root_.HTGeometry.finiteKMSWightmanTransitionIntensity,
            _root_.HTGeometry.wightmanTransitionIntensity,
            primeLogKMSFiniteHermitianAmplitude, primeLogKMSFiniteHermitianIntensity]
          change w * Complex.normSq
              (↑(Real.sqrt (primeDyadicWeight u p.1 / w))) = primeDyadicWeight u p.1
          rw [Complex.normSq_ofReal,
            Real.mul_self_sqrt (div_nonneg hweight hw.le)]
          exact mul_div_cancel₀ _ hw.ne'
  | some p =>
      cases b with
      | some q =>
          simp [primeLogKMSFiniteHermitianAmplitude,
            primeLogKMSFiniteHermitianIntensity,
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
            primeLogKMSFiniteHermitianAmplitude, primeLogKMSFiniteHermitianIntensity]
          change w * Complex.normSq
              (↑(Real.sqrt (primeDyadicWeight u p.1 / w))) = primeDyadicWeight u p.1
          rw [Complex.normSq_ofReal,
            Real.mul_self_sqrt (div_nonneg hweight hw.le)]
          exact mul_div_cancel₀ _ hw.ne'

/-- Exact Gibbs intensity of the Hermitian prime-log observable in Wightman half-density
coordinates. -/
theorem finiteGibbsTransitionIntensity_primeLogKMSFiniteHermitianAmplitude
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ)
    (a b : Option P) :
    _root_.HTGeometry.finiteGibbsTransitionIntensity β
        (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β) a b =
      Real.exp (β * (primeLogKMSFiniteEnergy P a - primeLogKMSFiniteEnergy P b) / 2) *
        primeLogKMSFiniteHermitianIntensity P u a b := by
  rw [_root_.HTGeometry.finiteGibbsTransitionIntensity_eq_exp_half_mul_wightman,
    finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteHermitianAmplitude]

/-- Forward Gibbs spectral value at a prime logarithm. -/
theorem finiteGibbsTransitionIntensity_primeLog_forward
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ) (β : ℝ) :
    _root_.HTGeometry.finiteGibbsTransitionIntensity β
        (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β)
        (some p) none =
      Real.exp (β * primeLogSupport p.1 / 2) * primeDyadicWeight u p.1 := by
  rw [finiteGibbsTransitionIntensity_primeLogKMSFiniteHermitianAmplitude]
  simp [primeLogKMSFiniteEnergy, primeLogKMSFiniteHermitianIntensity]

/-- Reverse Gibbs spectral value, with the exact detailed-balance Boltzmann factor. -/
theorem finiteGibbsTransitionIntensity_primeLog_reverse
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ) (β : ℝ) :
    _root_.HTGeometry.finiteGibbsTransitionIntensity β
        (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β)
        none (some p) =
      Real.exp (-β * primeLogSupport p.1 / 2) * primeDyadicWeight u p.1 := by
  rw [finiteGibbsTransitionIntensity_primeLogKMSFiniteHermitianAmplitude]
  simp [primeLogKMSFiniteEnergy, primeLogKMSFiniteHermitianIntensity]

/-- Prime-log commutator spectral value: the universal thermal `sinh` factor times the carrier
weight. -/
theorem finiteKMSCommutatorTransitionIntensity_primeLog
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ) (β : ℝ) :
    _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity β
        (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β)
        (some p) none =
      2 * Real.sinh (β * primeLogSupport p.1 / 2) * primeDyadicWeight u p.1 := by
  rw [_root_.HTGeometry.finiteKMSCommutatorTransitionIntensity_eq_sinh β
    (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β)
    (primeLogKMSFiniteHermitianAmplitude_hermitian P u β),
    finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteHermitianAmplitude]
  simp [primeLogKMSFiniteEnergy, primeLogKMSFiniteHermitianIntensity]

/-- Prime-log symmetrized fluctuation spectral value: the universal thermal `cosh` factor times
the carrier weight. -/
theorem finiteKMSSymmetricTransitionIntensity_primeLog
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ) (β : ℝ) :
    _root_.HTGeometry.finiteKMSSymmetricTransitionIntensity β
        (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β)
        (some p) none =
      2 * Real.cosh (β * primeLogSupport p.1 / 2) * primeDyadicWeight u p.1 := by
  rw [_root_.HTGeometry.finiteKMSSymmetricTransitionIntensity_eq_cosh β
    (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β)
    (primeLogKMSFiniteHermitianAmplitude_hermitian P u β),
    finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteHermitianAmplitude]
  simp [primeLogKMSFiniteEnergy, primeLogKMSFiniteHermitianIntensity]

/-- Prime-log fluctuation--dissipation relation specialized to the exact carrier frequency. -/
theorem finiteKMSCommutatorTransitionIntensity_primeLog_eq_tanh_mul_symmetric
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ) (β : ℝ) :
    _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity β
        (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β)
        (some p) none =
      Real.tanh (β * primeLogSupport p.1 / 2) *
        _root_.HTGeometry.finiteKMSSymmetricTransitionIntensity β
          (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β)
          (some p) none := by
  simpa [primeLogKMSFiniteEnergy] using
    (_root_.HTGeometry.finiteKMSCommutatorTransitionIntensity_eq_tanh_mul_symmetric β
      (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β)
      (primeLogKMSFiniteHermitianAmplitude_hermitian P u β) (some p) none)

/-- Finite mirror-odd prime-log carrier selected by a Hermitian observable. -/
def finitePrimeLogHermitianKMSCarrier (P : Finset Nat.Primes)
    (u : Nat.Primes → ℝ) (z : ℂ) : ℂ :=
  ∑ p ∈ P, (primeDyadicWeight u p : ℂ) *
    (((primeLogSupport p : ℂ) - z)⁻¹ - ((primeLogSupport p : ℂ) + z)⁻¹)

theorem neg_finiteTransitionPassiveResponse_primeLogKMSFiniteHermitianIntensity
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (z : ℂ) :
    -_root_.HTGeometry.finiteTransitionPassiveResponse
        (primeLogKMSFiniteHermitianIntensity P u) (primeLogKMSFiniteEnergy P) z =
      finitePrimeLogHermitianKMSCarrier P u z := by
  rw [_root_.HTGeometry.finiteTransitionPassiveResponse, Fintype.sum_option]
  simp only [primeLogKMSFiniteHermitianIntensity]
  simp_rw [Fintype.sum_option]
  simp only [primeLogKMSFiniteEnergy, sub_zero, zero_sub, Complex.ofReal_zero,
    zero_div, Finset.sum_const_zero, add_zero, zero_add]
  rw [finitePrimeLogHermitianKMSCarrier]
  calc
    -( ∑ p : P, (primeDyadicWeight u p.1 : ℂ) /
          (z - (-(primeLogSupport p.1) : ℝ)) +
        ∑ p : P, (primeDyadicWeight u p.1 : ℂ) /
          (z - (primeLogSupport p.1 : ℝ))) =
        ∑ p : P, (primeDyadicWeight u p.1 : ℂ) *
          (((primeLogSupport p.1 : ℂ) - z)⁻¹ -
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
          ((primeLogSupport p : ℂ) + z)⁻¹) := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach P (fun p => (primeDyadicWeight u p : ℂ) *
          (((primeLogSupport p : ℂ) - z)⁻¹ -
            ((primeLogSupport p : ℂ) + z)⁻¹)))

theorem neg_finiteKMSWightmanResponse_primeLogKMSFiniteHermitianAmplitude
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (β : ℝ) (z : ℂ) :
    -_root_.HTGeometry.finiteTransitionPassiveResponse
        (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
          (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β))
        (primeLogKMSFiniteEnergy P) z = finitePrimeLogHermitianKMSCarrier P u z := by
  rw [show _root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
      (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β) =
      primeLogKMSFiniteHermitianIntensity P u by
    funext a b
    exact finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteHermitianAmplitude
      P u β a b]
  exact neg_finiteTransitionPassiveResponse_primeLogKMSFiniteHermitianIntensity P u z

/-- Exact mirror projection: Hermitian completion retains the odd part of the directed carrier. -/
theorem finitePrimeLogHermitianKMSCarrier_eq_mirrorOdd
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (z : ℂ) :
    finitePrimeLogHermitianKMSCarrier P u z =
      finitePrimeLogHerglotz P u z - finitePrimeLogHerglotz P u (-z) := by
  rw [finitePrimeLogHermitianKMSCarrier, finitePrimeLogHerglotz,
    finitePrimeLogHerglotz, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring_nf

/-- The one-sided directed carrier splits into the physical Hermitian response and its exact
mirror-completion defect. -/
theorem finitePrimeLogHerglotz_eq_hermitian_add_mirrorDefect
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (z : ℂ) :
    finitePrimeLogHerglotz P u z = finitePrimeLogHermitianKMSCarrier P u z +
      finitePrimeLogHerglotz P u (-z) := by
  rw [finitePrimeLogHermitianKMSCarrier_eq_mirrorOdd]
  ring

/-- Hermitian KMS completion is exactly odd in the centered spectral coordinate. -/
theorem finitePrimeLogHermitianKMSCarrier_neg
    (P : Finset Nat.Primes) (u : Nat.Primes → ℝ) (z : ℂ) :
    finitePrimeLogHermitianKMSCarrier P u (-z) =
      -finitePrimeLogHermitianKMSCarrier P u z := by
  rw [← neg_finiteKMSWightmanResponse_primeLogKMSFiniteHermitianAmplitude P u 0,
    ← neg_finiteKMSWightmanResponse_primeLogKMSFiniteHermitianAmplitude P u 0]
  rw [_root_.HTGeometry.finiteKMSWightmanTransitionPassiveResponse_neg 0
    (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u 0)
    (primeLogKMSFiniteHermitianAmplitude_hermitian P u 0)]

/-- A nonempty directed prime-log transition model cannot be the Wightman spectrum of any
Hermitian observable. -/
theorem noHermitianAmplitude_realizes_primeLogKMSFiniteIntensity
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ) (β : ℝ) :
    ¬ ∃ amplitude : Option P → Option P → ℂ,
        (∀ a b, amplitude b a = star (amplitude a b)) ∧
        _root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
            (primeLogKMSFiniteEnergy P) amplitude = primeLogKMSFiniteIntensity P u := by
  rintro ⟨amplitude, hHermitian, hrealizes⟩
  have hsymm := _root_.HTGeometry.finiteKMSWightmanTransitionIntensity_symm β
    (primeLogKMSFiniteEnergy P) amplitude hHermitian (some p) none
  rw [hrealizes] at hsymm
  simp only [primeLogKMSFiniteIntensity] at hsymm
  exact (primeDyadicWeight_pos u p.1).ne' hsymm

/-- Infinite Hermitian KMS carrier with poles at both orientations of every prime logarithm. -/
def primeLogHermitianKMSCarrier (u : Nat.Primes → ℝ) (z : ℂ) : ℂ :=
  discreteHerglotz primeLogSupport (primeDyadicWeight u) z +
    discreteHerglotz (fun p => -primeLogSupport p) (primeDyadicWeight u) z

theorem primeLogHermitianKMSCarrier_im_nonneg
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (primeLogHermitianKMSCarrier u z).im := by
  rw [primeLogHermitianKMSCarrier, Complex.add_im]
  exact add_nonneg
    (discreteHerglotz_im_nonneg primeLogSupport (primeDyadicWeight u) z hz
      (fun p => (primeDyadicWeight_pos u p).le)
      (summable_norm_primeDyadicWeight u C hu))
    (discreteHerglotz_im_nonneg (fun p => -primeLogSupport p) (primeDyadicWeight u) z hz
      (fun p => (primeDyadicWeight_pos u p).le)
      (summable_norm_primeDyadicWeight u C hu))

theorem differentiableOn_primeLogHermitianKMSCarrier_upperHalfPlane
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C) :
    DifferentiableOn ℂ (primeLogHermitianKMSCarrier u) upperHalfPlane := by
  apply DifferentiableOn.add
  · exact differentiableOn_discreteHerglotz_upperHalfPlane primeLogSupport
      (primeDyadicWeight u) (summable_norm_primeDyadicWeight u C hu)
  · exact differentiableOn_discreteHerglotz_upperHalfPlane
      (fun p => -primeLogSupport p) (primeDyadicWeight u)
      (summable_norm_primeDyadicWeight u C hu)

/-- Finite Hermitian prime systems converge to the two-sided physical KMS carrier. -/
theorem finitePrimeLogHermitianKMSCarrier_tendsto_primeLogHermitianKMSCarrier
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (z : ℂ) (hz : 0 < z.im) :
    Filter.Tendsto
      (fun P : Finset Nat.Primes => finitePrimeLogHermitianKMSCarrier P u z)
      Filter.atTop (nhds (primeLogHermitianKMSCarrier u z)) := by
  have hw := summable_norm_primeDyadicWeight u C hu
  have hpos :=
    (summable_discreteHerglotz_term primeLogSupport (primeDyadicWeight u) z hz hw).hasSum
  have hneg :=
    (summable_discreteHerglotz_term (fun p => -primeLogSupport p)
      (primeDyadicWeight u) z hz hw).hasSum
  have hsum : HasSum
      (fun p : Nat.Primes => (primeDyadicWeight u p : ℂ) *
        (((primeLogSupport p : ℂ) - z)⁻¹ -
          ((primeLogSupport p : ℂ) + z)⁻¹))
      (discreteHerglotz primeLogSupport (primeDyadicWeight u) z +
        discreteHerglotz (fun p => -primeLogSupport p) (primeDyadicWeight u) z) := by
    apply HasSum.congr_fun (hpos.add hneg)
    intro p
    push_cast
    rw [show -(primeLogSupport p : ℂ) - z =
        -((primeLogSupport p : ℂ) + z) by ring, inv_neg]
    ring
  simpa only [finitePrimeLogHermitianKMSCarrier, primeLogHermitianKMSCarrier,
    discreteHerglotz] using hsum

/-- Thermodynamic limit of the explicit Hermitian finite KMS responses. -/
theorem finiteHermitianKMSWightmanResponse_tendsto_primeLogHermitianKMSCarrier
    (u : Nat.Primes → ℝ) (C : ℝ) (hu : ∀ p, u p ≤ C)
    (β : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Filter.Tendsto
      (fun P : Finset Nat.Primes =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
            (primeLogKMSFiniteEnergy P) (primeLogKMSFiniteHermitianAmplitude P u β))
          (primeLogKMSFiniteEnergy P) z)
      Filter.atTop (nhds (primeLogHermitianKMSCarrier u z)) := by
  simpa only [neg_finiteKMSWightmanResponse_primeLogKMSFiniteHermitianAmplitude] using
    finitePrimeLogHermitianKMSCarrier_tendsto_primeLogHermitianKMSCarrier u C hu z hz

/-- Reversing every prime-log support gives the negative reflected directed carrier. -/
theorem discreteHerglotz_neg_primeLogSupport_eq_neg_mirror
    (u : Nat.Primes → ℝ) (z : ℂ) :
    discreteHerglotz (fun p => -primeLogSupport p) (primeDyadicWeight u) z =
      -primeLogHerglotz u (-z) := by
  rw [discreteHerglotz, primeLogHerglotz, discreteHerglotz]
  calc
    ∑' p : Nat.Primes, (primeDyadicWeight u p : ℂ) *
        ((-(primeLogSupport p) : ℝ) - z)⁻¹ =
        ∑' p : Nat.Primes, -((primeDyadicWeight u p : ℂ) *
          ((primeLogSupport p : ℂ) - (-z))⁻¹) := by
      apply tsum_congr
      intro p
      push_cast
      rw [show -(primeLogSupport p : ℂ) - z =
          -((primeLogSupport p : ℂ) - -z) by ring, inv_neg]
      ring
    _ = -∑' p : Nat.Primes, (primeDyadicWeight u p : ℂ) *
        ((primeLogSupport p : ℂ) - (-z))⁻¹ := by
      exact tsum_neg

/-- Infinite mirror identity.  The Hermitian response is exactly the directed carrier minus its
reflected value. -/
theorem primeLogHermitianKMSCarrier_eq_mirrorOdd
    (u : Nat.Primes → ℝ) (z : ℂ) :
    primeLogHermitianKMSCarrier u z =
      primeLogHerglotz u z - primeLogHerglotz u (-z) := by
  rw [primeLogHermitianKMSCarrier,
    discreteHerglotz_neg_primeLogSupport_eq_neg_mirror]
  change primeLogHerglotz u z + -primeLogHerglotz u (-z) = _
  ring

/-- Infinite one-sided carrier decomposition; the reflected term is the exact orientation defect
discarded by Hermitian completion. -/
theorem primeLogHerglotz_eq_hermitian_add_mirrorDefect
    (u : Nat.Primes → ℝ) (z : ℂ) :
    primeLogHerglotz u z = primeLogHermitianKMSCarrier u z +
      primeLogHerglotz u (-z) := by
  rw [primeLogHermitianKMSCarrier_eq_mirrorOdd]
  ring

/-- Universal HT gauge specialization of the physical Hermitian KMS thermodynamic limit. -/
theorem universalFacetOrbitGauge_finiteHermitianKMSWightmanResponse_tendsto
    (β : ℝ) (z : ℂ) (hz : 0 < z.im) :
    Filter.Tendsto
      (fun P : Finset Nat.Primes =>
        -_root_.HTGeometry.finiteTransitionPassiveResponse
          (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
            (primeLogKMSFiniteEnergy P)
            (primeLogKMSFiniteHermitianAmplitude P
              (fun q => universalFacetOrbitGauge q) β))
          (primeLogKMSFiniteEnergy P) z)
      Filter.atTop
      (nhds (primeLogHermitianKMSCarrier
        (fun q => universalFacetOrbitGauge q) z)) := by
  exact finiteHermitianKMSWightmanResponse_tendsto_primeLogHermitianKMSCarrier
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q)) β z hz

end

end GaloisForLFunctions.HTGeometry
