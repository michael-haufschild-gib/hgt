import GaloisForLFunctions.HTGeometry.StabilizerCliffordOrbit
import GaloisForLFunctions.HTGeometry.LocalProductStateAction
import GaloisForLFunctions.HTGeometry.SpectralCollisionFunctional
import GaloisForLFunctions.HTGeometry.SpectralCollisionCovariance

/-!
# Product stabilizer states as the product-Clifford orbit of the computational zero

A product Clifford acts sitewise on a product state, so the product-Clifford images of the
all-zero state are exactly the product stabilizer states, each up to one unit phase.  The spectral
collision is invariant under a unit phase and under a bijection of the configuration index, so the
collision bound for product stabilizer amplitudes transports to that orbit.
-/

open Matrix

open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Orbit

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The all-zero product state. -/
def zeroProductState (σ : Type*) [Fintype σ] [DecidableEq σ] :
    FiniteQubitConfiguration σ → ℂ :=
  localProductState fun _ => boolZeroState

/-- A product stabilizer state. -/
def prodBoolStabAmp (τ : σ → Fin 6) : FiniteQubitConfiguration σ → ℂ :=
  localProductState fun s => boolStabAmp (τ s)

theorem localProductState_smul (c : σ → ℂ) (w : σ → Bool → ℂ) :
    localProductState (fun s => c s • w s) = (∏ s, c s) • localProductState w := by
  funext x
  simp only [localProductState, Pi.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib]

/-- **Product stabilizer states are product-Clifford images of the computational zero.** -/
theorem finiteProductCliffordGate_stabClifford_mulVec (τ : σ → Fin 6) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      finiteProductCliffordGate (fun s => stabClifford (τ s)) *ᵥ zeroProductState σ =
        c • prodBoolStabAmp τ := by
  classical
  choose cs hcs hact using fun s : σ => booleanQubitClifford_stabClifford_mulVec (τ s)
  refine ⟨∏ s, cs s, ?_, ?_⟩
  · rw [norm_prod]
    exact Finset.prod_eq_one fun s _ => hcs s
  · rw [finiteProductCliffordGate, zeroProductState, finiteLocalMatrix_mulVec_localProductState,
      show (fun s => booleanQubitClifford (stabClifford (τ s)) *ᵥ boolZeroState) =
        fun s => cs s • boolStabAmp (τ s) from funext fun s => hact s,
      localProductState_smul, prodBoolStabAmp]

end Orbit

section Invariance

variable {D α β : Type*} [Fintype D] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The spectral collision is invariant under a unit phase. -/
theorem spectralCollision_smul (e : D → α → ℂ) (ψ : α → ℂ) {c : ℂ} (hc : ‖c‖ = 1) :
    spectralCollision e (c • ψ) = spectralCollision e ψ := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finitePureStateFidelity, finitePureStateFidelity, finiteComplexInner_smul_right,
    norm_mul, hc, one_mul]

/-- The spectral collision is invariant under a bijection of the configuration index. -/
theorem spectralCollision_comp_equiv (φ : α ≃ β) (e : D → β → ℂ) (ψ : β → ℂ) :
    spectralCollision (fun j => (e j) ∘ φ) (ψ ∘ φ) = spectralCollision e ψ := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have hinner : finiteComplexInner ((e j) ∘ φ) (ψ ∘ φ) = finiteComplexInner (e j) ψ := by
    rw [finiteComplexInner, finiteComplexInner]
    exact Fintype.sum_equiv φ
      (fun a => (starRingEnd ℂ) (((e j) ∘ φ) a) * ((ψ ∘ φ) a))
      (fun b => (starRingEnd ℂ) (e j b) * ψ b) fun _ => rfl
  rw [finitePureStateFidelity, finitePureStateFidelity, hinner]

theorem sum_normSq_comp_equiv (φ : α ≃ β) (z : β → ℂ) :
    (∑ a, ‖(z ∘ φ) a‖ ^ 2) = ∑ b, ‖z b‖ ^ 2 :=
  Fintype.sum_equiv φ (fun a => ‖(z ∘ φ) a‖ ^ 2) (fun b => ‖z b‖ ^ 2) fun _ => rfl

end Invariance

section IndexBridge

/-- The bit/index bijection used by the stabilizer amplitudes. -/
def boolFin2Equiv : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := if i = 0 then false else true
  left_inv b := by cases b <;> simp
  right_inv i := by fin_cases i <;> simp

theorem boolStabAmp_eq (t : Fin 6) (b : Bool) :
    boolStabAmp t b = stabAmp rt2inv t (boolFin2Equiv b) := rfl

/-- Configurations over `Bool` and over `Fin 2` correspond. -/
def configEquiv (σ : Type*) : (σ → Bool) ≃ (σ → Fin 2) :=
  Equiv.piCongrRight fun _ => boolFin2Equiv

theorem prodBoolStabAmp_eq {n : ℕ} (τ : Fin n → Fin 6) :
    prodBoolStabAmp τ = (prodStabAmp rt2inv τ) ∘ (configEquiv (Fin n)) := by
  funext x
  rw [prodBoolStabAmp, localProductState, Function.comp_apply, prodStabAmp]
  exact Finset.prod_congr rfl fun s _ => boolStabAmp_eq (τ s) (x s)

end IndexBridge

end GaloisForLFunctions.HTGeometry
