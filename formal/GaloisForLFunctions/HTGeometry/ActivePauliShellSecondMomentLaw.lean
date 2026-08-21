import GaloisForLFunctions.HTGeometry.ActivePauliShellSpectralLaw
import GaloisForLFunctions.HTGeometry.CliffordEnsembleCollisionMean

/-!
# Collision second moment on the corrected active Pauli shell

First a family-level theorem shows that product-Clifford covariance plus invariant coefficient law
forces the product-input mean collision bound `(2/3)^n`.  The active-shell rate, covariance, and
simple-spectrum laws then discharge every premise for the corrected fixed-rate two-local ensemble.
-/

open Matrix MeasureTheory
open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- Mean collision is unchanged under any measure-preserving coefficient transformation whose
Hamiltonian family is conjugated by the corresponding product Clifford. -/
theorem integral_spectralCollision_family_clifford_eq
    {X : Type*} [MeasurableSpace X] {n : ℕ} {μ : Measure X} [IsProbabilityMeasure μ]
    (H : X → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hmeas : ∀ x y, Measurable fun a => H a x y)
    (g : Fin n → QubitTwoDesign.BinaryOctahedral)
    (T : X → X) (hinv : MeasurePreserving T μ μ)
    (hcov : ∀ᵐ a ∂μ, finiteProductCliffordGate g * H a *
      (finiteProductCliffordGate g)ᴴ = H (T a))
    (ψ : FiniteQubitConfiguration (Fin n) → ℂ)
    {e : X → FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ}
    {lam : X → FiniteQubitConfiguration (Fin n) → ℝ}
    (hae : ∀ᵐ a ∂μ, IsOrthoEigenBasis (H a) (e a) (lam a) ∧
      Function.Injective (lam a)) :
    (∫ a, spectralCollision (e a) ((finiteProductCliffordGate g)ᴴ *ᵥ ψ) ∂μ) =
      ∫ a, spectralCollision (e a) ψ ∂μ := by
  refine integral_spectralCollision_conj_eq (Hf := H) hmeas ψ hae
    (U := (finiteProductCliffordGate g)ᴴ) ?_ ?_ (T := T) hinv ?_
  · rw [Matrix.conjTranspose_conjTranspose]
    exact finiteProductCliffordGate_mul_conjTranspose g
  · rw [Matrix.conjTranspose_conjTranspose]
    exact finiteProductCliffordGate_unitary g
  · filter_upwards [hcov] with a ha
    simpa only [Matrix.conjTranspose_conjTranspose] using ha.symm

/-- Universal product-Clifford orbit bound for a covariant Hamiltonian ensemble. -/
theorem integral_spectralCollision_zeroProductState_le_of_covariant
    {X : Type*} [MeasurableSpace X] {n : ℕ} {μ : Measure X} [IsProbabilityMeasure μ]
    (H : X → Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
    (hmeas : ∀ x y, Measurable fun a => H a x y)
    (T : (Fin n → QubitTwoDesign.BinaryOctahedral) → X → X)
    (hinv : ∀ g, MeasurePreserving (T g) μ μ)
    (hcov : ∀ g a, finiteProductCliffordGate g * H a *
      (finiteProductCliffordGate g)ᴴ = H (T g a))
    {e : X → FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ}
    {lam : X → FiniteQubitConfiguration (Fin n) → ℝ}
    (hae : ∀ᵐ a ∂μ, IsOrthoEigenBasis (H a) (e a) (lam a) ∧
      Function.Injective (lam a)) :
    (∫ a, spectralCollision (e a) (zeroProductState (Fin n)) ∂μ) ≤ (2 / 3 : ℝ) ^ n := by
  classical
  set Ω := zeroProductState (Fin n) with hΩ
  set orb : (Fin n → Fin 6) → FiniteQubitConfiguration (Fin n) → ℂ :=
    fun τ => finiteProductCliffordGate (fun s => stabClifford (τ s)) *ᵥ Ω with horb
  have hconj : ∀ τ : Fin n → Fin 6,
      (finiteProductCliffordGate fun s => (stabClifford (τ s))⁻¹)ᴴ =
        finiteProductCliffordGate fun s => stabClifford (τ s) := by
    intro τ
    rw [finiteProductCliffordGate_conjTranspose_eq_inv]
    simp
  have horbitInv : ∀ τ : Fin n → Fin 6,
      (∫ a, spectralCollision (e a) (orb τ) ∂μ) =
        ∫ a, spectralCollision (e a) Ω ∂μ := by
    intro τ
    have h := integral_spectralCollision_family_clifford_eq H hmeas
      (fun s => (stabClifford (τ s))⁻¹) (T _) (hinv _) (Filter.Eventually.of_forall
        fun a => hcov _ a) Ω hae
    rw [hconj τ] at h
    exact h
  have hint : ∀ τ : Fin n → Fin 6,
      Integrable (fun a => spectralCollision (e a) (orb τ)) μ := by
    intro τ
    exact integrable_spectralCollision hmeas (sum_normSq_cliffordOrbitState τ) hae
  have hptwise : ∀ᵐ a ∂μ,
      (∑ τ : Fin n → Fin 6, spectralCollision (e a) (orb τ)) ≤
        (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) * 2 ^ n := by
    filter_upwards [hae] with a ha
    exact sum_spectralCollision_cliffordOrbit_le (e a)
      fun j => sum_normSq_eigenvector ha.1 j
  have hsum : (Fintype.card (Fin n → Fin 6) : ℝ) *
      ∫ a, spectralCollision (e a) Ω ∂μ ≤
        (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) * 2 ^ n := by
    have hswap : (∑ τ : Fin n → Fin 6,
        ∫ a, spectralCollision (e a) (orb τ) ∂μ) =
        ∫ a, ∑ τ : Fin n → Fin 6, spectralCollision (e a) (orb τ) ∂μ :=
      (integral_finsetSum _ fun τ _ => hint τ).symm
    have hconst : (∑ τ : Fin n → Fin 6,
        ∫ a, spectralCollision (e a) (orb τ) ∂μ) =
        (Fintype.card (Fin n → Fin 6) : ℝ) *
          ∫ a, spectralCollision (e a) Ω ∂μ := by
      rw [Finset.sum_congr rfl fun τ (_ : τ ∈ Finset.univ) => horbitInv τ,
        Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [← hconst, hswap]
    refine le_trans (integral_mono_ae
      (g := fun _ => (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) * 2 ^ n)
      (integrable_finsetSum _ fun τ _ => hint τ) (integrable_const _) hptwise) ?_
    rw [integral_const]
    simp
  have hcard6 : (Fintype.card (Fin n → Fin 6) : ℝ) = 6 ^ n := by simp
  have hcardD : (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) = 2 ^ n := by simp
  rw [hcard6, hcardD] at hsum
  have h63 : (6 : ℝ) ^ n = 2 ^ n * 3 ^ n := by
    rw [← mul_pow]
    norm_num
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [h63] at hsum
  have hkey : (2 : ℝ) ^ n *
      (3 ^ n * ∫ a, spectralCollision (e a) Ω ∂μ) ≤ 2 ^ n * 2 ^ n := by
    linarith [hsum]
  have h3 := le_of_mul_le_mul_left hkey h2
  rw [div_pow, le_div_iff₀ (by positivity : (0 : ℝ) < 3 ^ n)]
  rw [mul_comm] at h3
  exact h3

/-- Corrected active-shell mean collision bound, with simple spectrum discharged. -/
theorem integral_spectralCollision_activePauliFin_shell_le
    (n : ℕ) {q : ℕ} (hq : 2 ≤ q) [Nonempty (ActivePauliCoordinate n q)] :
    (∫ p, spectralCollision
        (hermitianEigenBasis (activePauliFinHamiltonian p)
          (isHermitian_activePauliFinHamiltonian p))
        (zeroProductState (Fin n))
      ∂(shellProbability (ActivePauliCoordinate n q))) ≤ (2 / 3 : ℝ) ^ n := by
  apply integral_spectralCollision_zeroProductState_le_of_covariant
    (H := activePauliFinHamiltonian)
    (T := fun g => activeFinCliffordCoefficientMap g)
  · exact measurable_activePauliFinHamiltonian_entry
  · exact measurePreserving_activeFinCliffordCoefficientMap_shell
  · exact activePauliFinHamiltonian_conj
  · exact isOrthoEigenBasis_injective_activePauliFin_shell_ae n hq

/-- Markov tail for collision on the corrected active shell. -/
theorem measureReal_spectralCollision_activePauliFin_shell_ge_le
    (n : ℕ) {q : ℕ} (hq : 2 ≤ q) [Nonempty (ActivePauliCoordinate n q)]
    {L : ℝ} (hL : 0 < L) :
    (shellProbability (ActivePauliCoordinate n q)).real
        {p | L * (2 / 3 : ℝ) ^ n ≤ spectralCollision
          (hermitianEigenBasis (activePauliFinHamiltonian p)
            (isHermitian_activePauliFinHamiltonian p))
          (zeroProductState (Fin n))} ≤ 1 / L := by
  exact measureReal_spectralCollision_ge_le
    measurable_activePauliFinHamiltonian_entry
    (sum_normSq_zeroProductState (Fin n))
    (isOrthoEigenBasis_injective_activePauliFin_shell_ae n hq)
    (by positivity)
    (integral_spectralCollision_activePauliFin_shell_le n hq) hL

instance instNonemptyActivePauliCoordinateSuccTwo (n : ℕ) :
    Nonempty (ActivePauliCoordinate (n + 1) 2) := by
  let i : Fin (n + 1) := ⟨0, by omega⟩
  have hactive : Nonempty (PauliTracelessLabel (n + 1) 2) :=
    ⟨⟨pauliZLabel i, by
      constructor
      · rw [pauliWeight_pauliZLabel]
        omega
      · exact pauliZLabel_ne_identity i⟩⟩
  exact Fin.pos_iff_nonempty.mp (Fintype.card_pos_iff.mpr hactive)

/-- **Unconditional corrected two-local fixed-shell collision law.** -/
theorem integral_spectralCollision_activePauliFin_twoLocal_shell_le (n : ℕ) :
    (∫ p, spectralCollision
        (hermitianEigenBasis (activePauliFinHamiltonian p)
          (isHermitian_activePauliFinHamiltonian p))
        (zeroProductState (Fin (n + 1)))
      ∂(shellProbability (ActivePauliCoordinate (n + 1) 2))) ≤
        (2 / 3 : ℝ) ^ (n + 1) := by
  exact integral_spectralCollision_activePauliFin_shell_le (n + 1) (q := 2) (by omega)

end GaloisForLFunctions.HTGeometry
