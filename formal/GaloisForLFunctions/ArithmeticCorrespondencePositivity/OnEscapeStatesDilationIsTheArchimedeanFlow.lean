import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheEscapeRankCountsTheDominantZeros

/-!
# On escape states, dilation is the archimedean flow

Positive-definite functions on `ℚ_{>0}` split into an archimedean and a Kronecker-null part (APD),
and arithmetic successors see only the null part: positivity on the multiplicative group alone does
not couple the places. Escape states are not functions on `ℚ_{>0}`: an escape state `K_θ` of a
dominant configuration (`TheEscapeRankCountsTheDominantZeros`) carries the weight `(jk)^{−x}` and
the phase `θ`. On them the places are coupled exactly.

* **Translated characters are characters** (`transChar_add`): `ψ(a + t) = ψ(t) ψ(a)`.
* **The dilation law** (`escapeKernel_shift`). Translating both arguments by `t` multiplies the kernel
  by `e^{−2xt}` and turns the phases by `e^{−i y_k t}`:
  `K_θ(a + t, b + t) = e^{−2xt} K_{θ e^{−i y t}}(a, b)`.
* **Dilation is the archimedean flow** (`escapeKernel_phase_shift`, `escapeKernel_phase_dilate`).
  Along the horizons, `K_{θ(L)}(a + t, b + t) = e^{−2xt} K_{θ(L − t)}(a, b)`; at `t = log p`,
  dilating both arguments by the prime `p` is the archimedean flow back by `log p`, scaled by
  `p^{−2x}`.

So the finite places act on escape states through the archimedean frequencies `y_k` of the
dominant zeros: the dilation by `p` and the horizon flow by `log p` are one operation. This is the
coupling that positivity on `ℚ_{>0}` cannot carry: it lives in the weight `(jk)^{−x}` and the phase,
which a dilation-invariant kernel does not have.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

variable {r : ℕ}

/-- **Translated characters are characters**: `ψ(a + t) = ψ(t) ψ(a)`. -/
theorem transChar_add (x y a t : ℝ) : transChar x y (a + t) = transChar x y t * transChar x y a := by
  simp only [transChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `ψ_k(t) conj ψ_l(t) = e^{−2xt} e^{−i y_k t} conj(e^{−i y_l t})`. -/
theorem transChar_mul_conj (x p q t : ℝ) :
    transChar x p t * conj (transChar x q t) =
      (Real.exp (-(2 * x * t)) : ℂ) * (Complex.exp (-((p * t : ℝ) * I)) *
        conj (Complex.exp (-((q * t : ℝ) * I)))) := by
  simp only [transChar, Complex.ofReal_exp, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **The dilation law**: `K_θ(a + t, b + t) = e^{−2xt} K_{θ e^{−i y t}}(a, b)`. -/
theorem escapeKernel_shift (x : ℝ) (y : Fin r → ℝ) (c θ : Fin r → ℂ) (a b t : ℝ) :
    escapeKernel x y c θ (a + t) (b + t) =
      (Real.exp (-(2 * x * t)) : ℂ) *
        escapeKernel x y c (fun k => θ k * Complex.exp (-((y k * t : ℝ) * I))) a b := by
  unfold escapeKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [transChar_add, transChar_add]
  have h := transChar_mul_conj x (y k) (y l) t
  simp only [map_mul]
  linear_combination (c k * θ k * transChar x (y k) a * (conj (c l) * conj (θ l) *
    conj (transChar x (y l) b)) / (2 * (x : ℂ) + ((y k : ℂ) - y l) * I)) * h

/-- The horizon flow turns the phases: `θ_k(L) e^{−i y_k t} = θ_k(L − t)`. -/
theorem phase_mul_exp (y : Fin r → ℝ) (L t : ℝ) (k : Fin r) :
    phase y L k * Complex.exp (-((y k * t : ℝ) * I)) = phase y (L - t) k := by
  simp only [phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Dilation is the archimedean flow**: `K_{θ(L)}(a + t, b + t) = e^{−2xt} K_{θ(L − t)}(a, b)`. -/
theorem escapeKernel_phase_shift (x : ℝ) (y : Fin r → ℝ) (c : Fin r → ℂ) (L a b t : ℝ) :
    escapeKernel x y c (phase y L) (a + t) (b + t) =
      (Real.exp (-(2 * x * t)) : ℂ) * escapeKernel x y c (phase y (L - t)) a b := by
  rw [escapeKernel_shift]
  congr 2
  funext k
  exact phase_mul_exp y L t k

/-- At a prime: dilating both arguments by `p` is the archimedean flow back by `log p`, scaled by
`p^{−2x}`. -/
theorem escapeKernel_phase_dilate (x : ℝ) (y : Fin r → ℝ) (c : Fin r → ℂ) (L a b : ℝ) {p : ℕ}
    (hp : 0 < p) :
    escapeKernel x y c (phase y L) (a + Real.log p) (b + Real.log p) =
      ((p : ℝ) ^ (-(2 * x)) : ℝ) * escapeKernel x y c (phase y (L - Real.log p)) a b := by
  rw [escapeKernel_phase_shift, Real.rpow_def_of_pos (by exact_mod_cast hp)]
  congr 3
  ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
