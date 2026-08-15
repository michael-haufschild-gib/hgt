import GaloisForLFunctions.HTGeometry.ProductStabilizerCliffordOrbit

/-!
# The collision bound on the product-Clifford orbit of the computational zero

The product-Clifford images of the all-zero state are the product stabilizer states up to a unit
phase, and the spectral collision is invariant under both a unit phase and the configuration
bijection, so the product stabilizer collision bound transports verbatim to that orbit: summed over
the `6ⁿ` product Cliffords it is at most the Hilbert dimension times `2ⁿ`.
-/

open Matrix

open QuantumAlg

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

theorem ofReal_normSq_rt2inv : ((‖rt2inv‖ ^ 2 : ℝ) : ℂ) = 1 / 2 := by
  rw [Complex.sq_norm, ← Complex.mul_conj]
  rw [show (starRingEnd ℂ) rt2inv = rt2inv from rt2inv_conj]
  exact rt2inv_mul_self

theorem normSq_rt2inv : ‖rt2inv‖ ^ 2 = 1 / 2 := by
  have h : ((‖rt2inv‖ ^ 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    rw [ofReal_normSq_rt2inv]
    norm_num
  exact_mod_cast h

/-- Every single-qubit stabilizer amplitude is a unit vector. -/
theorem sum_normSq_boolStabAmp (t : Fin 6) : (∑ b : Bool, ‖boolStabAmp t b‖ ^ 2) = 1 := by
  have hr := normSq_rt2inv
  rw [Fintype.sum_bool]
  fin_cases t <;>
    · simp [boolStabAmp, stabAmp]
      try rw [hr]
      try linarith [hr]

/-- Every product stabilizer state is a unit vector. -/
theorem sum_normSq_prodBoolStabAmp {σ : Type*} [Fintype σ] [DecidableEq σ] (τ : σ → Fin 6) :
    (∑ x : FiniteQubitConfiguration σ, ‖prodBoolStabAmp τ x‖ ^ 2) = 1 := by
  rw [prodBoolStabAmp, sum_normSq_localProductState]
  exact Finset.prod_eq_one fun s _ => sum_normSq_boolStabAmp (τ s)

/-- **Collision bound on the product-Clifford orbit of the computational zero.** -/
theorem sum_spectralCollision_cliffordOrbit_le {n : ℕ}
    {D : Type*} [Fintype D] (e : D → FiniteQubitConfiguration (Fin n) → ℂ)
    (he : ∀ j, (∑ b, ‖e j b‖ ^ 2) = 1) :
    (∑ τ : Fin n → Fin 6,
        spectralCollision e (finiteProductCliffordGate (fun s => stabClifford (τ s)) *ᵥ
          zeroProductState (Fin n))) ≤ (Fintype.card D : ℝ) * 2 ^ n := by
  classical
  set φ := configEquiv (Fin n) with hφ
  have hterm : ∀ τ : Fin n → Fin 6,
      spectralCollision e (finiteProductCliffordGate (fun s => stabClifford (τ s)) *ᵥ
          zeroProductState (Fin n)) =
        spectralCollision (fun j => (e j) ∘ φ.symm) (prodStabAmp rt2inv τ) := by
    intro τ
    obtain ⟨c, hc, hact⟩ := finiteProductCliffordGate_stabClifford_mulVec τ
    rw [hact, spectralCollision_smul e _ hc, prodBoolStabAmp_eq τ]
    have hcomp : (fun j => ((e j) ∘ φ.symm) ∘ φ) = e := by
      funext j x
      simp [hφ]
    rw [← spectralCollision_comp_equiv φ (fun j => (e j) ∘ φ.symm) (prodStabAmp rt2inv τ), hcomp]
  rw [Finset.sum_congr rfl fun τ (_ : τ ∈ Finset.univ) => hterm τ]
  refine sum_spectralCollision_prodStab_le rt2inv rt2inv_mul_self ?_ _ ?_
  · exact rt2inv_conj
  · intro j
    rw [show (∑ b, ‖((e j) ∘ φ.symm) b‖ ^ 2) = ∑ x, ‖e j x‖ ^ 2 from
      sum_normSq_comp_equiv φ.symm (e j)]
    exact he j

end GaloisForLFunctions.HTGeometry
