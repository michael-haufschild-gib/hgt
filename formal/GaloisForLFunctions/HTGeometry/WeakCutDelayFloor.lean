import GaloisForLFunctions.HTGeometry.WeakCutOnsetDelay
import GaloisForLFunctions.HTGeometry.CutConductanceUnionSandwich

/-!
# A small edge block delays the complexity onset

Deleting one interaction block decouples the chain, and the block's operator norm is at most three
times the Euclidean length of its Pauli coefficients.  A block whose coefficient length is below
the remaining resolution divided by three times a prescribed delay therefore leaves the interacting
orbit inside the split-system synthesis cap for the whole delay.
-/

open Matrix

open scoped Matrix Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {Θ : Type*} {E : Type*} [Fintype E] [Nonempty E]

theorem blockRadius_nonneg (J : E → Θ → (σ → Option (Fin 3)) → ℂ) (e : E) (θ : Θ) :
    0 ≤ blockRadius J e θ := Real.sqrt_nonneg _

variable {Γ : Type*}

/-- **A small edge block keeps the orbit easy for the whole delay.**  This is the exact mechanism
behind the delay floor: the failure event of the split-system synthesis cap is contained in the
event that the edge coefficient length exceeds the reduced threshold. -/
theorem approxComplexity_le_of_blockRadius_le
    {act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration σ) →
      EuclideanSpace ℂ (FiniteQubitConfiguration σ)}
    {H K : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ}
    (hH : IsSelfAdjoint H) (hK : IsSelfAdjoint K)
    {J : E → Θ → (σ → Option (Fin 3)) → ℂ} {e₀ : E} {θ : Θ}
    (hHK : H - K = blockMatrix J e₀ θ)
    (S : Finset (σ → Option (Fin 3))) (hcard : S.card = 9)
    (hJ : ∀ e θ, ∀ P ∉ S, J e θ P = 0)
    {ψ : EuclideanSpace ℂ (FiniteQubitConfiguration σ)} (hψ : ‖ψ‖ = 1)
    {t : ℝ} {cap : ℕ} {η ε L : ℝ} (hL : 0 < L) (ht : |t| ≤ L)
    (hsyn : ∃ w : List Γ, w.length ≤ cap ∧
      dist (evolvedState K t ψ) (wordAct act w ψ) ≤ η)
    (hsmall : blockRadius J e₀ θ ≤ (ε - η) / (3 * L)) :
    approxComplexity act ψ ε (evolvedState H t ψ) ≤ cap := by
  have hnorm : ‖H - K‖ ≤ 3 * blockRadius J e₀ θ := by
    rw [hHK]
    exact norm_blockMatrix_le J S hcard hJ e₀ θ
  have hrad : 0 ≤ blockRadius J e₀ θ := blockRadius_nonneg J e₀ θ
  have h3L : (0 : ℝ) < 3 * L := by linarith
  have hbound : 3 * blockRadius J e₀ θ * L ≤ ε - η := by
    have := mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 3)
    have hkey : 3 * blockRadius J e₀ θ ≤ 3 * ((ε - η) / (3 * L)) := this
    calc 3 * blockRadius J e₀ θ * L ≤ 3 * ((ε - η) / (3 * L)) * L :=
          mul_le_mul_of_nonneg_right hkey (le_of_lt hL)
      _ = ε - η := by field_simp
  have habs : 0 ≤ |t| := abs_nonneg t
  have hstep : |t| * ‖H - K‖ ≤ ε - η := by
    calc |t| * ‖H - K‖ ≤ L * (3 * blockRadius J e₀ θ) :=
          mul_le_mul ht hnorm (norm_nonneg _) (le_of_lt hL)
      _ = 3 * blockRadius J e₀ θ * L := by ring
      _ ≤ ε - η := hbound
  exact approxComplexity_evolvedState_le_synthesis hH hK hψ hsyn hstep

end

end GaloisForLFunctions.HTGeometry
