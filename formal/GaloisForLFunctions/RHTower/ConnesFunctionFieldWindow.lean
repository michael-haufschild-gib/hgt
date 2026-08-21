import Mathlib

/-!
# Connes' function-field window count

Formalization of the counting steps (9)-(13) inside the proof of Lemma 1 of §VIII of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

In positive characteristic the module of the idele class group is `q^ℤ`, the normalized Haar
measure is `log q` times counting measure (Appendix II b (7)(8), formalized in
`ConnesModulatedHaar`), and with the cut-off `Λ = q^N` Connes computes

  `2 h_χ(1) log' Λ = (2N+1) l`,                                     (9)
  `Trace (P̂_Λ P_Λ U(h_χ)) = (2N+1) l - f l + (2-2g) l`,             (12)

and then exhibits exactly that many linearly independent vectors `U(g) η_χ` in `B_Λ^χ`, namely the
`g ∈ D_S` with `|g| ≤ Λ` and `|g^{-1}| ≤ q^{2-2g-f} Λ`.  Since `|g| = q^n` on `D_S`, that window is
the integer interval `[-N, N + (2-2g-f)]`, whose cardinality is `(2N+1) + (2-2g-f)`: the equality of
the trace with the dimension is exactly this lattice-point count, which is proved here.
-/

namespace GaloisForLFunctions.RHTower

open Finset

/-- **§VIII (9)/(13).**  The number of degrees in the cut-off window `[-N, N+m]`. -/
theorem connes_windowCard (N : ℕ) (m : ℤ) (hm : -(2 * (N:ℤ) + 1) ≤ m) :
    ((Finset.Icc (-(N:ℤ)) ((N:ℤ) + m)).card : ℤ) = 2 * (N:ℤ) + 1 + m := by
  rw [Int.card_Icc]
  have hnn : (0:ℤ) ≤ (N:ℤ) + m + 1 - -(N:ℤ) := by linarith
  rw [Int.toNat_of_nonneg hnn]
  ring

/-- **§VIII (9).**  With no ramification and no genus correction the window has `2N+1` elements,
which is the normalization `2 log' Λ = (2N+1) log q` of the cut-off. -/
theorem connes_windowCard_symmetric (N : ℕ) :
    ((Finset.Icc (-(N:ℤ)) (N:ℤ)).card : ℤ) = 2 * (N:ℤ) + 1 := by
  have h := connes_windowCard N 0 (by
    have : (0:ℤ) ≤ 2 * (N:ℤ) + 1 := by positivity
    linarith)
  simpa using h

/-- **§VIII (12).**  Multiplying by the index `l` of the open subgroup gives Connes' displayed
trace `(2N+1) l - f l + (2-2g) l`, with `m = (2 - 2g) - f`. -/
theorem connes_windowCard_index (N : ℕ) (l : ℤ) (g f : ℤ)
    (hm : -(2 * (N:ℤ) + 1) ≤ (2 - 2 * g) - f) :
    ((Finset.Icc (-(N:ℤ)) ((N:ℤ) + ((2 - 2 * g) - f))).card : ℤ) * l
      = (2 * (N:ℤ) + 1) * l - f * l + (2 - 2 * g) * l := by
  rw [connes_windowCard N _ hm]
  ring

end GaloisForLFunctions.RHTower
