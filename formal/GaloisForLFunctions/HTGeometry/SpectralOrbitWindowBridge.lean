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
  fun j => ‖finiteComplexInner (e j) Ω‖ ^ 2

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

end

end GaloisForLFunctions.HTGeometry
