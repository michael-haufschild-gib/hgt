import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! A finite coefficient pairing equals its adjacent-prefix pairing plus one boundary term. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeil_prefix_pairing {n : ℕ} (c f : Fin (n + 1) → ℝ) :
    (∑ j, c j * f j) = (∑ j, c j) * f (Fin.last n) +
      ∑ i : Fin n, (∑ j ∈ Finset.Iic i.castSucc, c j) *
        (f i.castSucc - f i.succ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun i => c i.castSucc) (fun i => f i.castSucc)
    rw [Fin.sum_univ_castSucc (fun j => c j * f j), hi,
      Fin.sum_univ_castSucc c,
      Fin.sum_univ_castSucc (fun i : Fin (n + 1) =>
        (∑ j ∈ Finset.Iic i.castSucc, c j) * (f i.castSucc - f i.succ))]
    simp_rw [Fin.sum_Iic_castSucc]
    simp only [Fin.succ_castSucc, Fin.succ_last]
    have ht : (Finset.Iic (Fin.last n) : Finset (Fin (n + 1))) = Finset.univ := by
      ext j
      simp
      exact Fin.le_last j
    rw [ht]
    ring

theorem finiteWeil_prefix_pairing_zero {n : ℕ} (c f : Fin (n + 1) → ℝ)
    (hc : ∑ j, c j = 0) :
    (∑ j, c j * f j) = ∑ i : Fin n,
      (∑ j ∈ Finset.Iic i.castSucc, c j) * (f i.castSucc - f i.succ) := by
  rw [finiteWeil_prefix_pairing, hc, zero_mul, zero_add]

end RHTower
