import Mathlib

/-!
# The normalized projective moving frame is a fundamental matrix

For a lift `v` whose top derivative satisfies `δ^N v = ∑_j q_j δ^j v`, the moving frame
`[v, δv, …, δ^{N−1}v]` differentiates into itself times the companion matrix of that relation, so it
is a fundamental matrix of the associated first-order system.  When the normalized Wronskian is `1`
the frame lies in `SL_N`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

variable {F : Type*} [Field F] [Differential F]

/-- Componentwise derivation of a vector. -/
def vecDeriv {N : ℕ} (v : Fin N → F) : Fin N → F := fun i => (v i)′

/-- The moving frame `[v, δv, …, δ^{N−1}v]`. -/
def frameMatrix {N : ℕ} (v : Fin N → F) : Matrix (Fin N) (Fin N) F :=
  Matrix.of fun i j => (vecDeriv^[(j : ℕ)] v) i

/-- The companion matrix of the normalized relation `δ^N v = ∑ q_j δ^j v`. -/
def companionMatrix {N : ℕ} (q : Fin N → F) : Matrix (Fin N) (Fin N) F :=
  Matrix.of fun j k => if (k : ℕ) + 1 < N then (if (j : ℕ) = (k : ℕ) + 1 then 1 else 0) else q j

/-- **The moving frame is a fundamental matrix of the companion system.** -/
theorem deriv_frameMatrix {N : ℕ} (v q : Fin N → F)
    (hrel : ∀ i, (vecDeriv^[N] v) i = ∑ j, q j * (vecDeriv^[(j : ℕ)] v) i) :
    (Matrix.of fun i j => ((frameMatrix v) i j)′) = frameMatrix v * companionMatrix q := by
  classical
  ext i k
  simp only [Matrix.of_apply, frameMatrix, Matrix.mul_apply, companionMatrix]
  have hstep : ((vecDeriv^[(k : ℕ)] v) i)′ = (vecDeriv^[(k : ℕ) + 1] v) i := by
    rw [Function.iterate_succ_apply']
    rfl
  rw [hstep]
  by_cases hk : (k : ℕ) + 1 < N
  · rw [Finset.sum_eq_single (⟨(k : ℕ) + 1, hk⟩ : Fin N)]
    · rw [if_pos hk, if_pos rfl, mul_one]
    · intro b _ hb
      rw [if_pos hk, if_neg (fun h => hb (Fin.ext h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hkN : (k : ℕ) + 1 = N := by omega
    have hcoef : ∀ j : Fin N,
        (if (k : ℕ) + 1 < N then (if (j : ℕ) = (k : ℕ) + 1 then (1 : F) else 0) else q j) = q j :=
      fun j => if_neg hk
    simp only [hcoef]
    rw [hkN, hrel i]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The frame as an element of `SL_N`, given the normalized Wronskian. -/
def frameSL {N : ℕ} (v : Fin N → F) (h : (frameMatrix v).det = 1) :
    Matrix.SpecialLinearGroup (Fin N) F := ⟨frameMatrix v, h⟩

@[simp] theorem coe_frameSL {N : ℕ} (v : Fin N → F) (h : (frameMatrix v).det = 1) :
    ((frameSL v h : Matrix.SpecialLinearGroup (Fin N) F) : Matrix (Fin N) (Fin N) F)
      = frameMatrix v := rfl

end GaloisForLFunctions.HTGeometry
