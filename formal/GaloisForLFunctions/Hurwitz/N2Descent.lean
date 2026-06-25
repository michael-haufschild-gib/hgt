/-
# Hurwitz N=2 — block-descent applications (quadratic + linear)

Wires the committed descent engine `HurwitzSpine.block_descent` to the collected blocks: the quadratic
block (base `2s`) is a direct application; the linear block (base `s`) reuses `block_descent` at `s/2`
(since `2·(s/2) = s`).
-/
import GaloisForLFunctions.Hurwitz.Encoding

open Complex HurwitzSpine

namespace HurwitzN2Descent

/-- The weight-`w` coefficient of the quadratic block: `A_w = ∑_{i+j=w} q_{ij}`. -/
noncomputable def Aq (q : Fin 3 → Fin 3 → Polynomial ℂ) (w : ℕ) : Polynomial ℂ :=
  ∑ ij ∈ Finset.univ.filter (fun ij : Fin 3 × Fin 3 => (ij.1 : ℕ) + (ij.2 : ℕ) = w), q ij.1 ij.2

/-- **Quadratic-block descent.** Vanishing of the quadratic block forces every `A_w = 0`. -/
theorem quad_descent {s : ℂ} (q : Fin 3 → Fin 3 → Polynomial ℂ) {N : ℕ} {Bregion : ℕ → ℝ}
    (hΦ : ∀ n, N ≤ n → ∀ z : ℂ, z.re < Bregion n →
      ∑ w ∈ Finset.range 5, (Aq q w).eval (-(n : ℂ) + Complex.exp z)
        * Complex.exp (-(2 * s + (w : ℂ)) * z) = 0) :
    ∀ w, w ≤ 4 → Aq q w = 0 :=
  block_descent (s := s) (A := Aq q) (W := 4) (N := N) (Bregion := Bregion) hΦ

/-- **Linear-block descent.** Vanishing of the linear block (base `s`) forces every `l_k = 0`;
instantiate `block_descent` at `s/2` since `2·(s/2)=s`. -/
theorem lin_descent {s : ℂ} (l : ℕ → Polynomial ℂ) {N : ℕ} {Bregion : ℕ → ℝ}
    (hΨ : ∀ n, N ≤ n → ∀ z : ℂ, z.re < Bregion n →
      ∑ k ∈ Finset.range 3, (l k).eval (-(n : ℂ) + Complex.exp z)
        * Complex.exp (-(s + (k : ℂ)) * z) = 0) :
    ∀ k, k ≤ 2 → l k = 0 := by
  apply block_descent (s := s / 2) (A := l) (W := 2) (N := N) (Bregion := Bregion)
  intro n hn z hz
  simp only [show (2 : ℂ) * (s / 2) = s from by ring]
  exact hΨ n hn z hz

end HurwitzN2Descent
