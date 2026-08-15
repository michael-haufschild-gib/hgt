import GaloisForLFunctions.HTGeometry.CliffordOrbitCollisionBound
import GaloisForLFunctions.HTGeometry.PauliEnsembleCliffordCovariance

/-!
# Mean spectral collision of a fixed product input under a Pauli Gaussian ensemble

Product-Clifford conjugation leaves the ensemble law invariant, so the mean collision at the
all-zero product state equals the mean collision at every product-Clifford image of it.  Averaging
over the `6ⁿ` product Cliffords that reach the product stabilizer states and using the orbit
collision bound gives mean collision at most `(2/3)ⁿ`, and Markov's inequality then bounds the
probability of exceeding any multiple of it.
-/

open Matrix MeasureTheory

open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem sum_normSq_zeroProductState (σ : Type*) [Fintype σ] [DecidableEq σ] :
    (∑ x : FiniteQubitConfiguration σ, ‖zeroProductState σ x‖ ^ 2) = 1 := by
  rw [zeroProductState, sum_normSq_localProductState]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [Fintype.sum_bool]
  simp [boolZeroState]

theorem sum_normSq_cliffordOrbitState {σ : Type*} [Fintype σ] [DecidableEq σ]
    (τ : σ → Fin 6) :
    (∑ x : FiniteQubitConfiguration σ,
      ‖(finiteProductCliffordGate (fun s => stabClifford (τ s)) *ᵥ zeroProductState σ) x‖ ^ 2)
      = 1 := by
  obtain ⟨c, hc, hact⟩ := finiteProductCliffordGate_stabClifford_mulVec τ
  rw [hact]
  have hterm : ∀ x : FiniteQubitConfiguration σ, ‖(c • prodBoolStabAmp τ) x‖ ^ 2 =
      ‖prodBoolStabAmp τ x‖ ^ 2 := by
    intro x
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hterm x]
  exact sum_normSq_prodBoolStabAmp τ

/-- The weighted Pauli ensemble is Hermitian at every real coefficient vector. -/
theorem isHermitian_pauliEnsemble {σ : Type*} [Fintype σ] [DecidableEq σ]
    (w J : (σ → Option (Fin 3)) → ℝ) : (pauliEnsemble w J).IsHermitian := by
  classical
  rw [pauliEnsemble, Matrix.IsHermitian, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Matrix.conjTranspose_smul, finitePauliMatrix_isHermitian P, RCLike.star_def,
    Complex.conj_ofReal]

/-- Every member of the weighted Pauli ensemble carries an orthonormal eigenbasis. -/
theorem exists_isOrthoEigenBasis_pauliEnsemble {σ : Type*} [Fintype σ] [DecidableEq σ]
    (w J : (σ → Option (Fin 3)) → ℝ) :
    ∃ (e : FiniteQubitConfiguration σ → FiniteQubitConfiguration σ → ℂ)
      (lam : FiniteQubitConfiguration σ → ℝ),
      IsOrthoEigenBasis (pauliEnsemble w J) e lam :=
  exists_isOrthoEigenBasis _ (isHermitian_pauliEnsemble w J)

section Ensemble

variable {n : ℕ}

/-- **The mean spectral collision of the all-zero product input is at most `(2/3)ⁿ`.** -/
theorem integral_spectralCollision_zeroProductState_le
    (w : (Fin n → Option (Fin 3)) → ℝ) (hw : SupportInvariantWeight w) (v : NNReal)
    {e : ((Fin n → Option (Fin 3)) → ℝ) →
      FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ}
    {lam : ((Fin n → Option (Fin 3)) → ℝ) → FiniteQubitConfiguration (Fin n) → ℝ}
    (hae : ∀ᵐ J ∂(centredProductGaussian (Fin n → Option (Fin 3)) v),
      IsOrthoEigenBasis (pauliEnsemble w J) (e J) (lam J) ∧ Function.Injective (lam J)) :
    (∫ J, spectralCollision (e J) (zeroProductState (Fin n))
        ∂(centredProductGaussian (Fin n → Option (Fin 3)) v)) ≤ (2 / 3 : ℝ) ^ n := by
  classical
  set μ := centredProductGaussian (Fin n → Option (Fin 3)) v with hμ
  set Ω := zeroProductState (Fin n) with hΩ
  set orb : (Fin n → Fin 6) → FiniteQubitConfiguration (Fin n) → ℂ :=
    fun τ => finiteProductCliffordGate (fun s => stabClifford (τ s)) *ᵥ Ω with horb
  have hconj : ∀ τ : Fin n → Fin 6,
      (finiteProductCliffordGate fun s => (stabClifford (τ s))⁻¹)ᴴ =
        finiteProductCliffordGate fun s => stabClifford (τ s) := by
    intro τ
    rw [finiteProductCliffordGate_conjTranspose_eq_inv]
    simp
  have hinv : ∀ τ : Fin n → Fin 6,
      (∫ J, spectralCollision (e J) (orb τ) ∂μ) = ∫ J, spectralCollision (e J) Ω ∂μ := by
    intro τ
    have h := integral_spectralCollision_pauliEnsemble_clifford_eq w hw v
      (fun s => (stabClifford (τ s))⁻¹) Ω (e := e) (lam := lam) hae
    rw [hconj τ] at h
    exact h
  have hint : ∀ τ : Fin n → Fin 6,
      Integrable (fun J => spectralCollision (e J) (orb τ)) μ := by
    intro τ
    exact integrable_spectralCollision (fun x y => measurable_pauliEnsemble_entry w x y)
      (sum_normSq_cliffordOrbitState τ) hae
  have hptwise : ∀ᵐ J ∂μ,
      (∑ τ : Fin n → Fin 6, spectralCollision (e J) (orb τ)) ≤
        (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) * 2 ^ n := by
    filter_upwards [hae] with J hJ
    exact sum_spectralCollision_cliffordOrbit_le (e J)
      fun j => sum_normSq_eigenvector hJ.1 j
  have hsum : (Fintype.card (Fin n → Fin 6) : ℝ) * ∫ J, spectralCollision (e J) Ω ∂μ ≤
      (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) * 2 ^ n := by
    have hswap : (∑ τ : Fin n → Fin 6, ∫ J, spectralCollision (e J) (orb τ) ∂μ) =
        ∫ J, ∑ τ : Fin n → Fin 6, spectralCollision (e J) (orb τ) ∂μ :=
      (integral_finsetSum _ fun τ _ => hint τ).symm
    have hconst : (∑ τ : Fin n → Fin 6, ∫ J, spectralCollision (e J) (orb τ) ∂μ) =
        (Fintype.card (Fin n → Fin 6) : ℝ) * ∫ J, spectralCollision (e J) Ω ∂μ := by
      rw [Finset.sum_congr rfl fun τ (_ : τ ∈ Finset.univ) => hinv τ, Finset.sum_const,
        nsmul_eq_mul, Finset.card_univ]
    rw [← hconst, hswap]
    refine le_trans (integral_mono_ae
      (g := fun _ => (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) * 2 ^ n)
      (integrable_finsetSum _ fun τ _ => hint τ) (integrable_const _) ?_) ?_
    · filter_upwards [hptwise] with J hJ
      exact hJ
    · rw [integral_const]
      simp
  have hcard6 : (Fintype.card (Fin n → Fin 6) : ℝ) = 6 ^ n := by
    simp
  have hcardD : (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) = 2 ^ n := by
    simp
  rw [hcard6, hcardD] at hsum
  have h63 : (6 : ℝ) ^ n = 2 ^ n * 3 ^ n := by
    rw [← mul_pow]
    norm_num
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [h63] at hsum
  have hkey : (2 : ℝ) ^ n * (3 ^ n * ∫ J, spectralCollision (e J) Ω ∂μ) ≤ 2 ^ n * 2 ^ n := by
    linarith [hsum]
  have h3 := le_of_mul_le_mul_left hkey h2
  rw [div_pow, le_div_iff₀ (by positivity : (0 : ℝ) < 3 ^ n)]
  rw [mul_comm] at h3
  exact h3

/-- **Markov bound for the fixed product input.**  The quenched collision exceeds `L (2/3)ⁿ` with
probability at most `1 / L`. -/
theorem measureReal_spectralCollision_zeroProductState_ge_le
    (w : (Fin n → Option (Fin 3)) → ℝ) (hw : SupportInvariantWeight w) (v : NNReal)
    {e : ((Fin n → Option (Fin 3)) → ℝ) →
      FiniteQubitConfiguration (Fin n) → FiniteQubitConfiguration (Fin n) → ℂ}
    {lam : ((Fin n → Option (Fin 3)) → ℝ) → FiniteQubitConfiguration (Fin n) → ℝ}
    (hae : ∀ᵐ J ∂(centredProductGaussian (Fin n → Option (Fin 3)) v),
      IsOrthoEigenBasis (pauliEnsemble w J) (e J) (lam J) ∧ Function.Injective (lam J))
    {L : ℝ} (hL : 0 < L) :
    (centredProductGaussian (Fin n → Option (Fin 3)) v).real
        {J | L * (2 / 3 : ℝ) ^ n ≤ spectralCollision (e J) (zeroProductState (Fin n))} ≤ 1 / L :=
  measureReal_spectralCollision_ge_le (fun x y => measurable_pauliEnsemble_entry w x y)
    (sum_normSq_zeroProductState (Fin n)) hae (by positivity)
    (integral_spectralCollision_zeroProductState_le w hw v hae) hL

end Ensemble

end GaloisForLFunctions.HTGeometry
