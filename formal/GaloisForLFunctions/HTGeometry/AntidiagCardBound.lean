import Mathlib

/-!
# The convolution index set is polynomially bounded

The number of ordered ways to split `N` across `r` slots — the cardinality of `finsuppAntidiag N`
over `Fin r`, i.e. the number of convolution atoms of a degree-`r` differential monomial at
coefficient index `N` — is at most `(N+1)^r` (`card_finsuppAntidiag_le`): each slot value is at
most `N`, so the coordinate map injects the antidiagonal into `Fin r → Fin (N+1)`.

This is the atom-count half of the polynomial weight bound `#A_N ≤ (N+2)^{C_P}` of the
Taylor-magnitude hypertranscendence cards: the number of grouped convolution atoms is polynomial
in the coefficient index.
-/

open Finset

namespace GaloisForLFunctions

/-- **Atom-count bound.**  The convolution index set `finsuppAntidiag N` over `Fin r` has at most
`(N+1)^r` elements. -/
theorem card_finsuppAntidiag_le {r N : ℕ} :
    ((Finset.univ : Finset (Fin r)).finsuppAntidiag N).card ≤ (N + 1) ^ r := by
  classical
  have hmap : ∀ l ∈ (Finset.univ : Finset (Fin r)).finsuppAntidiag N,
      (⇑l : Fin r → ℕ) ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1)) := by
    intro l hl
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    rw [Finset.mem_finsuppAntidiag] at hl
    have hli : l i ≤ N := by
      rw [← hl.1]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hinj : Set.InjOn (fun l : Fin r →₀ ℕ => (⇑l : Fin r → ℕ))
      ((Finset.univ : Finset (Fin r)).finsuppAntidiag N) :=
    fun a _ b _ h => DFunLike.coe_injective h
  calc ((Finset.univ : Finset (Fin r)).finsuppAntidiag N).card
      ≤ (Fintype.piFinset (fun _ : Fin r => Finset.range (N + 1))).card :=
        Finset.card_le_card_of_injOn _ hmap hinj
    _ = (N + 1) ^ r := by
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ,
          Fintype.card_fin]

end GaloisForLFunctions
