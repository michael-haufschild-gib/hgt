import GaloisForLFunctions.RHTower.ConnesShellWindowMass

/-!
# §VIII: the trace of the cut-off window against the regular representation

§VIII of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  "One has `Trace(S_Λ V(f)) = 2 f(1) log' Λ`."

`S_Λ` is the orthogonal projection onto the functions supported in the module window
`|g| ∈ [Λ^{-1}, Λ]`, and `V` is the left regular representation of the idele class group.  The
compression of `V(f)` to the window is the matrix `(i,j) ↦ f(i − j)`, whose diagonal is constant
equal to `f(1)`, so the trace is `(mass of the window) · f(1)`.  At a non-archimedean place the
window is the symmetric shell interval `−N ≤ n ≤ N`, of cardinality `2N + 1`, and with
`Λ = q^N` the normalization `2 log' Λ = (2N+1) log q` of §VIII (9) turns this into exactly
`2 f(1) log' Λ`.

The computation is finite and unconditional.
-/

open Finset

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The compression of the convolution operator `V(f)` to a window `W`: its matrix in the basis
indexed by `W` is `(i, j) ↦ f(i − j)`. -/
def connesWindowMatrix (W : Finset G) (f : G → ℂ) : Matrix W W ℂ :=
  fun i j => f ((i : G) - (j : G))

@[simp] theorem connesWindowMatrix_apply (W : Finset G) (f : G → ℂ) (i j : W) :
    connesWindowMatrix W f i j = f ((i : G) - (j : G)) := rfl

/-- **§VIII, the window trace.**  `Trace(S_Λ V(f)) = |W| · f(1)`. -/
theorem connesWindowMatrix_trace (W : Finset G) (f : G → ℂ) :
    (connesWindowMatrix W f).trace = (W.card : ℂ) * f 0 := by
  have hdiag : ∀ i : W, connesWindowMatrix W f i i = f 0 := by
    intro i
    rw [connesWindowMatrix_apply, sub_self]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, hdiag]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

/-- **§VIII (9), the shell window.**  At a non-archimedean place the symmetric window
`−N ≤ n ≤ N` has `2N + 1` shells, so the window trace is `(2N+1) f(1)`. -/
theorem connes_shellWindow_trace (N : ℕ) (f : ℤ → ℂ) :
    (connesWindowMatrix (Finset.Icc (-(N : ℤ)) (N : ℤ)) f).trace
      = ((2 * N + 1 : ℕ) : ℂ) * f 0 := by
  rw [connesWindowMatrix_trace]
  congr 2
  rw [Int.card_Icc]
  simp only [sub_neg_eq_add]
  omega

/-- **§VIII, `Trace(S_Λ V(f)) = 2 f(1) log' Λ`.**  With `Λ = q^N` the shell window has
`2 log' Λ = (2N+1) log q`, so the trace of the compressed regular representation is exactly
`2 f(1) log' Λ` in the normalized measure. -/
theorem connes_shellWindow_trace_logPrime (N : ℕ) (q : ℝ) (f : ℤ → ℂ) :
    ((Real.log q : ℝ) : ℂ) * (connesWindowMatrix (Finset.Icc (-(N : ℤ)) (N : ℤ)) f).trace
      = ((((2 * N + 1 : ℕ) : ℝ) * Real.log q : ℝ) : ℂ) * f 0 := by
  rw [connes_shellWindow_trace]
  push_cast
  ring

end

end GaloisForLFunctions.RHTower
