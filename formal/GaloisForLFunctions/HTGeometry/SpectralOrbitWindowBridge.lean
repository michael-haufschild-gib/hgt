import GaloisForLFunctions.HTGeometry.ArithmeticWindowHardCell
import GaloisForLFunctions.HTGeometry.ClockPhaseEvolutionBridge
import GaloisForLFunctions.HTGeometry.SpectralCollisionCovariance

/-!
# The Schrödinger orbit is the radian phase orbit of its spectral weights

Theorem B of the arithmetic hardness–recurrence card is stated for the abstract phase orbit
`radianOrbit p φ`.  For a Hermitian Hamiltonian and a unit state the two agree on the nose: the
eigencoordinates of `e^{-itH}Ω` are `√(p_j)·e^{i(ψ_j − t E_j)}` with `p_j = |⟨e_j,Ω⟩|²` and
`ψ_j = arg⟨e_j,Ω⟩`, and Parseval turns the orbit fidelity into the physical one.

## Main results

* `spectralWeights`, `spectralPhases` — the modulus-squared and argument of the overlaps.
* `radianOrbit_spectral_eq_eigenCoords` — **the orbit identity.**
* `finitePureStateFidelity_radianOrbit_spectral` — **the fidelity identity.**
* `finitePureStateFidelity_reindex`, `radianOrbit_reindex` — transport along an index equivalence.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The spectral weights of a state in an orthonormal eigenbasis. -/
def spectralWeights (e : α → α → ℂ) (Ω : α → ℂ) : α → ℝ :=
  fun j => ‖finiteComplexInner (e j) Ω‖ ^ (2 : ℕ)

/-- The spectral phases of a state in an orthonormal eigenbasis. -/
def spectralPhases (e : α → α → ℂ) (Ω : α → ℂ) : α → ℝ :=
  fun j => Complex.arg (finiteComplexInner (e j) Ω)

theorem spectralWeights_nonneg (e : α → α → ℂ) (Ω : α → ℂ) (j : α) :
    0 ≤ spectralWeights e Ω j := by
  rw [spectralWeights]
  positivity

theorem sum_spectralWeights {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) {Ω : α → ℂ} (hΩ : finiteComplexInner Ω Ω = 1) :
    ∑ j, spectralWeights e Ω j = 1 := sum_normSq_eigenCoords heb Ω hΩ

theorem occupationCollision_spectralWeights (e : α → α → ℂ) (Ω : α → ℂ) :
    occupationCollision (spectralWeights e Ω) = spectralCollision e Ω := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [spectralWeights, finitePureStateFidelity]

/-- **The orbit identity.**  The radian phase orbit of the spectral weights is the eigencoordinate
vector of the evolved state. -/
theorem radianOrbit_spectral_eq_eigenCoords {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (Ω : α → ℂ) (t : ℝ) :
    radianOrbit (spectralWeights e Ω) (fun j => spectralPhases e Ω j - t * lam j)
      = eigenCoords e (unitaryEvolution H t *ᵥ Ω) := by
  funext j
  rw [eigenCoords_unitaryEvolution heb Ω t]
  show ((Real.sqrt (spectralWeights e Ω j) : ℝ) : ℂ)
      * Complex.exp (((spectralPhases e Ω j - t * lam j : ℝ)) * Complex.I)
    = eigenCoords e Ω j * Complex.exp (-(Complex.I * ((t : ℂ) * (lam j : ℂ))))
  set z : ℂ := finiteComplexInner (e j) Ω with hz
  have hsqrt : Real.sqrt (spectralWeights e Ω j) = ‖z‖ := by
    rw [spectralWeights, Real.sqrt_sq (norm_nonneg _)]
  have hsplit : Complex.exp (((spectralPhases e Ω j - t * lam j : ℝ)) * Complex.I)
      = Complex.exp ((Complex.arg z : ℂ) * Complex.I)
        * Complex.exp (-(Complex.I * ((t : ℂ) * (lam j : ℂ)))) := by
    rw [← Complex.exp_add]
    congr 1
    rw [spectralPhases]
    push_cast
    ring
  rw [hsqrt, hsplit, ← mul_assoc]
  congr 1
  exact Complex.norm_mul_exp_arg_mul_I z

/-- **The fidelity identity.**  The orbit fidelity against the eigencoordinates of a target is the
physical fidelity of the evolved state against that target. -/
theorem finitePureStateFidelity_radianOrbit_spectral {H : Matrix α α ℂ} {e : α → α → ℂ}
    {lam : α → ℝ} (heb : IsOrthoEigenBasis H e lam) (Ω Z : α → ℂ) (t : ℝ) :
    finitePureStateFidelity
        (radianOrbit (spectralWeights e Ω) (fun j => spectralPhases e Ω j - t * lam j))
        (eigenCoords e Z)
      = finitePureStateFidelity (unitaryEvolution H t *ᵥ Ω) Z := by
  rw [radianOrbit_spectral_eq_eigenCoords heb Ω t, finitePureStateFidelity,
    finitePureStateFidelity, finiteComplexInner_eigenCoords heb]

/-! ### Transport along an index equivalence -/

variable {β : Type*} [Fintype β] [DecidableEq β]

theorem finiteComplexInner_reindex (ρ : α ≃ β) (v w : α → ℂ) :
    finiteComplexInner (fun j => v (ρ.symm j)) (fun j => w (ρ.symm j))
      = finiteComplexInner v w := by
  rw [finiteComplexInner, finiteComplexInner]
  exact Fintype.sum_equiv ρ.symm _ _ (fun _ => rfl)

theorem finitePureStateFidelity_reindex (ρ : α ≃ β) (v w : α → ℂ) :
    finitePureStateFidelity (fun j => v (ρ.symm j)) (fun j => w (ρ.symm j))
      = finitePureStateFidelity v w := by
  rw [finitePureStateFidelity, finitePureStateFidelity, finiteComplexInner_reindex]

theorem radianOrbit_reindex (ρ : α ≃ β) (p φ : α → ℝ) (j : β) :
    radianOrbit (fun k => p (ρ.symm k)) (fun k => φ (ρ.symm k)) j
      = radianOrbit p φ (ρ.symm j) := rfl

theorem occupationCollision_reindex (ρ : α ≃ β) (p : α → ℝ) :
    occupationCollision (fun k => p (ρ.symm k)) = occupationCollision p :=
  Fintype.sum_equiv ρ.symm _ _ (fun _ => rfl)

/-- At time zero the radian orbit is the eigencoordinate vector. -/
theorem radianOrbit_spectral_zero (e : α → α → ℂ) (Ω : α → ℂ) :
    radianOrbit (spectralWeights e Ω) (spectralPhases e Ω) = eigenCoords e Ω := by
  funext j
  show ((Real.sqrt (spectralWeights e Ω j) : ℝ) : ℂ)
      * Complex.exp (((spectralPhases e Ω j : ℝ)) * Complex.I) = eigenCoords e Ω j
  have hsqrt : Real.sqrt (spectralWeights e Ω j) = ‖finiteComplexInner (e j) Ω‖ := by
    rw [spectralWeights, Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrt, spectralPhases]
  exact Complex.norm_mul_exp_arg_mul_I _

/-! ### The eigencoordinate map is an isometry -/

theorem eigenCoords_sub_smul (e : α → α → ℂ) (v w : α → ℂ) (c : ℂ) :
    (fun j => eigenCoords e v j - c * eigenCoords e w j)
      = eigenCoords e (fun x => v x - c * w x) := by
  funext j
  rw [eigenCoords, eigenCoords, eigenCoords, finiteComplexInner, finiteComplexInner,
    finiteComplexInner, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem sum_normSq_eigenCoords_eq {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (v : α → ℂ) :
    ∑ j, ‖eigenCoords e v j‖ ^ (2 : ℕ) = ∑ x, ‖v x‖ ^ (2 : ℕ) := by
  have hpar := finiteComplexInner_eigenCoords heb v v
  have hL : finiteComplexInner (eigenCoords e v) (eigenCoords e v)
      = ((∑ j, ‖eigenCoords e v j‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [finiteComplexInner, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Complex.sq_norm]
      exact (Complex.normSq_eq_conj_mul_self).symm
  have hR : finiteComplexInner v v = ((∑ x, ‖v x‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [finiteComplexInner, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Complex.sq_norm]
      exact (Complex.normSq_eq_conj_mul_self).symm
  rw [hL, hR] at hpar
  exact_mod_cast hpar

/-- **The eigencoordinate map is an isometry.** -/
theorem norm_toLp_eigenCoords {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (v : α → ℂ) :
    ‖(WithLp.toLp 2 (eigenCoords e v) : EuclideanSpace ℂ α)‖
      = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ α)‖ := by
  have h1 := sq_norm_toLp (eigenCoords e v)
  have h2 := sq_norm_toLp v
  have h3 := sum_normSq_eigenCoords_eq heb v
  nlinarith [norm_nonneg (WithLp.toLp 2 (eigenCoords e v) : EuclideanSpace ℂ α),
    norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ α)]

theorem norm_toLp_reindex (ρ : α ≃ β) (v : α → ℂ) :
    ‖(WithLp.toLp 2 (fun j => v (ρ.symm j)) : EuclideanSpace ℂ β)‖
      = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ α)‖ := by
  have h1 := sq_norm_toLp (fun j => v (ρ.symm j))
  have h2 := sq_norm_toLp v
  have h3 : ∑ j, ‖v (ρ.symm j)‖ ^ (2 : ℕ) = ∑ x, ‖v x‖ ^ (2 : ℕ) :=
    Fintype.sum_equiv ρ.symm (fun j => ‖v (ρ.symm j)‖ ^ (2 : ℕ)) (fun x => ‖v x‖ ^ (2 : ℕ)) (fun _ => rfl)
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun j => v (ρ.symm j)) : EuclideanSpace ℂ β),
    norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ α)]

end

end GaloisForLFunctions.HTGeometry
