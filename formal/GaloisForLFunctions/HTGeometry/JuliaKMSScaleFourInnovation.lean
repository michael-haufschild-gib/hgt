import GaloisForLFunctions.HTGeometry.JuliaDefectSpectralEquilibrium
import GaloisForLFunctions.HTGeometry.PrimeLogKMSHermitianCompletion

/-!
# Julia scale-four innovations as exact finite KMS fluctuation layers

The critical Dirichlet radial density `D(x) = 1 / (2 sinh x)` is exactly the inverse
fluctuation--dissipation factor at a positive finite KMS gap.  Combining this inverse law with
the Dirichlet--Julia scale-four telescope decomposes every positive-gap Wightman transition
weight into Julia innovation layers and one unresolved tail.

For the Hermitian prime-log KMS realization, every dyadic prime carrier weight therefore has an
exact finite decomposition into strictly positive Julia layers plus a strictly positive tail.
This is a source-level coupling between the Julia equilibrium law and the existing arithmetic
prime-log carrier, rather than a comparison between unrelated positive functions.

The construction does not remove an external oscillatory observable: multiplying these positive
carrier layers by counter-phased sine values can still reverse their signs.  Thus the theorem
isolates the remaining RH obstruction as phase control, not thermal or Julia-layer positivity.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Inverse finite fluctuation--dissipation law.**  At a positive thermal energy gap, the
critical Dirichlet radial density converts commutator intensity exactly back to its Wightman
transition weight. -/
theorem criticalDirichletLevyRadialDensity_mul_finiteKMSCommutator_eq_wightman
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    (a b : α)
    (hx : 0 < β * (energy a - energy b) / 2) :
    _root_.HTGeometry.criticalDirichletLevyRadialDensity
          (β * (energy a - energy b) / 2) *
        _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity
          β energy amplitude a b =
      _root_.HTGeometry.finiteKMSWightmanTransitionIntensity
        β energy amplitude a b := by
  rw [_root_.HTGeometry.finiteKMSCommutatorTransitionIntensity_eq_sinh
    β energy amplitude hHermitian a b,
    _root_.HTGeometry.criticalDirichletLevyRadialDensity]
  have hsinh : Real.sinh (β * (energy a - energy b) / 2) ≠ 0 :=
    (Real.sinh_pos_iff.mpr hx).ne'
  field_simp [hsinh]

/-- **Finite Julia innovation resolution of a KMS transition.**  Every positive-gap Wightman
weight is the sum of its first `n` scale-four Julia innovation responses and one exact residual
Dirichlet response. -/
theorem finiteKMSWightmanTransitionIntensity_eq_juliaScaleFourInnovationTelescope
    {α : Type*} [Fintype α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    (a b : α)
    (hx : 0 < β * (energy a - energy b) / 2) (n : ℕ) :
    _root_.HTGeometry.finiteKMSWightmanTransitionIntensity
          β energy amplitude a b =
      (∑ j ∈ Finset.range n,
          (4 : ℝ) ^ j *
            _root_.HTGeometry.juliaScaleFourInnovationDensity
              ((4 : ℝ) ^ j * (β * (energy a - energy b) / 2)) *
            _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity
              β energy amplitude a b) +
        (4 : ℝ) ^ n *
          _root_.HTGeometry.criticalDirichletLevyRadialDensity
            ((4 : ℝ) ^ n * (β * (energy a - energy b) / 2)) *
          _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity
            β energy amplitude a b := by
  rw [← criticalDirichletLevyRadialDensity_mul_finiteKMSCommutator_eq_wightman
      β energy amplitude hHermitian a b hx,
    _root_.HTGeometry.criticalDirichletLevyRadialDensity_scaleFour_telescope]
  simp only [add_mul, Finset.sum_mul]
  ring

/-- Every generic Julia innovation response is nonnegative at a positive KMS gap.  It is strict
whenever the underlying Wightman transition is nonzero. -/
theorem juliaScaleFourKMSInnovationLayer_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hHermitian : ∀ a b, amplitude b a = star (amplitude a b))
    (a b : α)
    (hx : 0 < β * (energy a - energy b) / 2) (j : ℕ) :
    0 ≤ (4 : ℝ) ^ j *
          _root_.HTGeometry.juliaScaleFourInnovationDensity
            ((4 : ℝ) ^ j * (β * (energy a - energy b) / 2)) *
          _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity
            β energy amplitude a b := by
  have harg : 0 < (4 : ℝ) ^ j * (β * (energy a - energy b) / 2) := by
    positivity
  have hinnovation :=
    _root_.HTGeometry.juliaScaleFourInnovationDensity_pos harg
  have hcommutator :
      0 ≤ _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity
        β energy amplitude a b := by
    rw [_root_.HTGeometry.finiteKMSCommutatorTransitionIntensity_eq_sinh
      β energy amplitude hHermitian a b]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sinh_pos_iff.mpr hx).le)
      (_root_.HTGeometry.finiteKMSWightmanTransitionIntensity_nonneg
        β energy amplitude a b)
  positivity

/-- A dyadic prime carrier weight is exactly the inverse-FDT image of its Hermitian prime-log
commutator intensity. -/
theorem primeDyadicWeight_eq_criticalDirichletFDT
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ)
    (β : ℝ) (hβ : 0 < β) :
    primeDyadicWeight u p.1 =
      _root_.HTGeometry.criticalDirichletLevyRadialDensity
          (β * primeLogSupport p.1 / 2) *
        _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity β
          (primeLogKMSFiniteEnergy P)
          (primeLogKMSFiniteHermitianAmplitude P u β) (some p) none := by
  have hx : 0 < β *
      (primeLogKMSFiniteEnergy P (some p) - primeLogKMSFiniteEnergy P none) / 2 := by
    simpa [primeLogKMSFiniteEnergy] using
      (div_pos (mul_pos hβ (primeLogSupport_pos p.1)) (by norm_num : (0 : ℝ) < 2))
  have hinv :=
    criticalDirichletLevyRadialDensity_mul_finiteKMSCommutator_eq_wightman
      β (primeLogKMSFiniteEnergy P)
      (primeLogKMSFiniteHermitianAmplitude P u β)
      (primeLogKMSFiniteHermitianAmplitude_hermitian P u β)
      (some p) none hx
  symm
  calc
    _ = _root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
          (primeLogKMSFiniteEnergy P)
          (primeLogKMSFiniteHermitianAmplitude P u β) (some p) none := by
      simpa [primeLogKMSFiniteEnergy] using hinv
    _ = primeDyadicWeight u p.1 := by
      rw [finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteHermitianAmplitude]
      simp [primeLogKMSFiniteHermitianIntensity]

/-- **Prime-log Julia innovation tower.**  Every dyadic prime carrier weight admits an exact
finite scale-four decomposition into Julia innovation responses and one residual response. -/
theorem primeDyadicWeight_eq_juliaScaleFourInnovationTelescope
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ)
    (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    primeDyadicWeight u p.1 =
      (∑ j ∈ Finset.range n,
          (4 : ℝ) ^ j *
            _root_.HTGeometry.juliaScaleFourInnovationDensity
              ((4 : ℝ) ^ j * (β * primeLogSupport p.1 / 2)) *
            _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity β
              (primeLogKMSFiniteEnergy P)
              (primeLogKMSFiniteHermitianAmplitude P u β) (some p) none) +
        (4 : ℝ) ^ n *
          _root_.HTGeometry.criticalDirichletLevyRadialDensity
            ((4 : ℝ) ^ n * (β * primeLogSupport p.1 / 2)) *
          _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity β
            (primeLogKMSFiniteEnergy P)
            (primeLogKMSFiniteHermitianAmplitude P u β) (some p) none := by
  have hx : 0 < β *
      (primeLogKMSFiniteEnergy P (some p) - primeLogKMSFiniteEnergy P none) / 2 := by
    simpa [primeLogKMSFiniteEnergy] using
      (div_pos (mul_pos hβ (primeLogSupport_pos p.1)) (by norm_num : (0 : ℝ) < 2))
  have htelescope :=
    finiteKMSWightmanTransitionIntensity_eq_juliaScaleFourInnovationTelescope
      β (primeLogKMSFiniteEnergy P)
      (primeLogKMSFiniteHermitianAmplitude P u β)
      (primeLogKMSFiniteHermitianAmplitude_hermitian P u β)
      (some p) none hx n
  calc
    _ = _root_.HTGeometry.finiteKMSWightmanTransitionIntensity β
          (primeLogKMSFiniteEnergy P)
          (primeLogKMSFiniteHermitianAmplitude P u β) (some p) none := by
      rw [finiteKMSWightmanTransitionIntensity_primeLogKMSFiniteHermitianAmplitude]
      simp [primeLogKMSFiniteHermitianIntensity]
    _ = _ := by
      simpa [primeLogKMSFiniteEnergy] using htelescope

/-- Every Julia layer in the prime-log decomposition is strictly positive. -/
theorem primeJuliaScaleFourInnovationLayer_pos
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ)
    (β : ℝ) (hβ : 0 < β) (j : ℕ) :
    0 < (4 : ℝ) ^ j *
          _root_.HTGeometry.juliaScaleFourInnovationDensity
            ((4 : ℝ) ^ j * (β * primeLogSupport p.1 / 2)) *
          _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity β
            (primeLogKMSFiniteEnergy P)
            (primeLogKMSFiniteHermitianAmplitude P u β) (some p) none := by
  have hx : 0 < β * primeLogSupport p.1 / 2 := by
    exact div_pos (mul_pos hβ (primeLogSupport_pos p.1)) (by norm_num)
  have harg : 0 < (4 : ℝ) ^ j * (β * primeLogSupport p.1 / 2) := by
    positivity
  have hinnovation :=
    _root_.HTGeometry.juliaScaleFourInnovationDensity_pos harg
  rw [finiteKMSCommutatorTransitionIntensity_primeLog]
  have hsinh : 0 < Real.sinh (β * primeLogSupport p.1 / 2) :=
    Real.sinh_pos_iff.mpr hx
  have hweight := primeDyadicWeight_pos u p.1
  positivity

/-- The unresolved Dirichlet tail in every finite prime-log decomposition is strictly positive. -/
theorem primeJuliaScaleFourInnovationTail_pos
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ)
    (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    0 < (4 : ℝ) ^ n *
          _root_.HTGeometry.criticalDirichletLevyRadialDensity
            ((4 : ℝ) ^ n * (β * primeLogSupport p.1 / 2)) *
          _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity β
            (primeLogKMSFiniteEnergy P)
            (primeLogKMSFiniteHermitianAmplitude P u β) (some p) none := by
  have hx : 0 < β * primeLogSupport p.1 / 2 := by
    exact div_pos (mul_pos hβ (primeLogSupport_pos p.1)) (by norm_num)
  have harg : 0 < (4 : ℝ) ^ n * (β * primeLogSupport p.1 / 2) := by
    positivity
  have hsinharg : 0 < Real.sinh
      ((4 : ℝ) ^ n * (β * primeLogSupport p.1 / 2)) :=
    Real.sinh_pos_iff.mpr harg
  rw [_root_.HTGeometry.criticalDirichletLevyRadialDensity,
    finiteKMSCommutatorTransitionIntensity_primeLog]
  have hsinh : 0 < Real.sinh (β * primeLogSupport p.1 / 2) :=
    Real.sinh_pos_iff.mpr hx
  have hweight := primeDyadicWeight_pos u p.1
  positivity

/-- **Sharp phase obstruction.**  A counter-phased observable remains strictly negative on every
positive Julia prime layer.  The innovation tower resolves carrier mass but cannot repair an
external sign reversal. -/
theorem primeJuliaScaleFourInnovationLayer_mul_neg
    (P : Finset Nat.Primes) (p : P) (u : Nat.Primes → ℝ)
    (β : ℝ) (hβ : 0 < β) (j : ℕ) (phase : ℝ) (hphase : phase < 0) :
    (4 : ℝ) ^ j *
          _root_.HTGeometry.juliaScaleFourInnovationDensity
            ((4 : ℝ) ^ j * (β * primeLogSupport p.1 / 2)) *
          _root_.HTGeometry.finiteKMSCommutatorTransitionIntensity β
            (primeLogKMSFiniteEnergy P)
            (primeLogKMSFiniteHermitianAmplitude P u β) (some p) none * phase < 0 := by
  exact mul_neg_of_pos_of_neg
    (primeJuliaScaleFourInnovationLayer_pos P p u β hβ j) hphase

end

end GaloisForLFunctions.HTGeometry
