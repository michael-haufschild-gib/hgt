/-
# Hurwitz N=2 — the linear+cross block regrouped by singular exponent

The linear+cross block `Ψb = ∑_{i,j} q_{ij}(E_iR_j + E_jR_i) + ∑_k l_k E_k` regroups by the singular
exponential `E_k = e^{−(s+k)z}` into `∑_k c_k·E_k` with coefficient `c_k = ∑_j (q_{kj}+q_{jk})·R_j + l_k`.
This is the form `linear_laurent_top` consumes (peel the `E_2 = x^{−s−2}` coefficient `c_2`). Linear-case
analogue of `quadratic_weight_regroup`.
-/
import Mathlib

namespace HurwitzN2PsiRegroup

/-- **Linear+cross block regrouped by `E_k`.** `∑_{i,j} q_{ij}(E_iR_j+E_jR_i) + ∑_k l_k E_k
= ∑_k (∑_j (q_{kj}+q_{jk})·R_j + l_k)·E_k`. -/
theorem psi_regroup (q : Fin 3 → Fin 3 → ℂ) (l : Fin 3 → ℂ) (R : Fin 3 → ℂ) (E : Fin 3 → ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3, q i j * (E i * R j + E j * R i)) + ∑ k : Fin 3, l k * E k
      = ∑ k : Fin 3, ((∑ j : Fin 3, (q k j + q j k) * R j) + l k) * E k := by
  simp only [Fin.sum_univ_three]
  ring

end HurwitzN2PsiRegroup
