import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Clustered exponential packets with exact moment cancellation

For any `n + 1` complex offsets, the first `n` monomial moments admit a nonzero
annihilating coefficient vector.  This is the rectangular Vandermonde mechanism behind
clustered exponential packets: after factoring a common carrier frequency, every term of
the exponential Taylor polynomial of degree below `n` cancels exactly.

No separation, distinctness, or clustering assumption is needed for the algebraic theorem.
Those conditions enter only when this exact cancellation is combined with an analytic
Taylor-remainder estimate.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators

/-- Rectangular Vandermonde moment matrix for `n + 1` offsets and moments `0, …, n - 1`. -/
def clusteredMomentMatrix (n : ℕ) (δ : Fin (n + 1) → ℂ) :
    Matrix (Fin n) (Fin (n + 1)) ℂ :=
  fun q k => δ k ^ (q : ℕ)

/-- Truncated exponential packet after a common carrier has been factored out. -/
def clusteredExpTaylorPacket (n : ℕ) (δ d : Fin (n + 1) → ℂ) (z : ℂ) : ℂ :=
  ∑ k, d k * ∑ q : Fin n, (z * δ k) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)

/-- **Rectangular Vandermonde annihilator.**  Any `n + 1` complex offsets have a nonzero
coefficient vector annihilating all monomial moments of degree below `n`. -/
theorem exists_nonzero_clusteredMoment_annihilator (n : ℕ) (δ : Fin (n + 1) → ℂ) :
    ∃ d : Fin (n + 1) → ℂ, d ≠ 0 ∧
      ∀ q : Fin n, ∑ k, d k * δ k ^ (q : ℕ) = 0 := by
  let A : Matrix (Fin n) (Fin (n + 1)) ℂ := clusteredMomentMatrix n δ
  have hdim : Module.finrank ℂ (Fin n → ℂ) < Module.finrank ℂ (Fin (n + 1) → ℂ) := by
    simp
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨d, hdker, hdne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨d, hdne, ?_⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hdker
  intro q
  have hq := congrFun hdker q
  simpa [A, clusteredMomentMatrix, Matrix.mulVec, dotProduct, mul_comm] using hq

/-- **Exact clustered Taylor cancellation.**  The same nonzero coefficients annihilate
every term of the exponential Taylor polynomial of degree below `n`, simultaneously for
every complex evaluation point. -/
theorem exists_nonzero_clusteredExpTaylorPacket_eq_zero
    (n : ℕ) (δ : Fin (n + 1) → ℂ) :
    ∃ d : Fin (n + 1) → ℂ, d ≠ 0 ∧
      (∀ q : Fin n, ∑ k, d k * δ k ^ (q : ℕ) = 0) ∧
      ∀ z : ℂ, clusteredExpTaylorPacket n δ d z = 0 := by
  obtain ⟨d, hdne, hmoment⟩ := exists_nonzero_clusteredMoment_annihilator n δ
  refine ⟨d, hdne, hmoment, ?_⟩
  intro z
  rw [clusteredExpTaylorPacket]
  calc
    ∑ k, d k * ∑ q : Fin n, (z * δ k) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ) =
        ∑ k, ∑ q : Fin n,
          d k * ((z * δ k) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
    _ = ∑ q : Fin n, ∑ k,
          d k * ((z * δ k) ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) :=
      Finset.sum_comm
    _ = ∑ q : Fin n,
          (z ^ (q : ℕ) / ((q : ℕ).factorial : ℂ)) *
            ∑ k, d k * δ k ^ (q : ℕ) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_pow]
      ring
    _ = 0 := by simp [hmoment]

end

end GaloisForLFunctions.HTGeometry
