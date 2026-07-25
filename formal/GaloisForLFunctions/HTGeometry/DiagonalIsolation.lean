import Mathlib

/-!
# Diagonal isolation by a frequency gap

A double sum `∑_{d,e} A d · B e · Φ(λ d − λ e)` collapses to its diagonal as soon as the weight `Φ`
vanishes at every non-zero frequency difference occurring in the sum.  For a finite index set with
injective frequencies such a `Φ` always exists, because the finitely many non-zero differences are
bounded away from `0`.

This is the finite form of the diagonal-extraction mechanism for Dirichlet series: with
`λ n = log n` and `A`, `B` supported on prime powers, the non-zero differences are the linear forms
`k log q − j log p` with `p^j ≠ q^k`, and Baker's theorem on linear forms in two logarithms supplies
an **effective** gap `≫ (log X)^{−C}` for indices up to `X` — so the required `Φ` can be taken with
support shrinking only logarithmically.  The two statements below isolate the purely combinatorial
content, which is unconditional and needs no transcendence input.
-/

open Finset

namespace HTGeometry

open Finset

theorem exists_gap_of_injOn {S : Finset ℕ} {lam : ℕ → ℝ} (h : Set.InjOn lam S) :
    ∃ δ > 0, ∀ d ∈ S, ∀ e ∈ S, d ≠ e → δ ≤ |lam d - lam e| := by
  classical
  set T := (S ×ˢ S).filter (fun x => x.1 ≠ x.2) with hT
  by_cases hS : T = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro d hd e he hde
    have : (d, e) ∈ T := by
      rw [hT, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hd, he⟩, hde⟩
    rw [hS] at this; simp at this
  · have hne : T.Nonempty := Finset.nonempty_of_ne_empty hS
    set δ := T.inf' hne (fun x => |lam x.1 - lam x.2|) with hδ
    refine ⟨δ, ?_, ?_⟩
    · show (0:ℝ) < δ
      rw [hδ, Finset.lt_inf'_iff]
      intro x hx
      rw [hT, Finset.mem_filter, Finset.mem_product] at hx
      have := h hx.1.1 hx.1.2
      have hne' : lam x.1 ≠ lam x.2 := fun hh => hx.2 (this hh)
      exact abs_pos.2 (sub_ne_zero.2 hne')
    · intro d hd e he hde
      have hmem : (d, e) ∈ T := by
        rw [hT, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hd, he⟩, hde⟩
      exact Finset.inf'_le (fun x => |lam x.1 - lam x.2|) hmem

theorem diagonal_isolation {S : Finset ℕ} (A B : ℕ → ℂ) (lam : ℕ → ℝ) (Φ : ℝ → ℂ)
    (hvan : ∀ d ∈ S, ∀ e ∈ S, d ≠ e → Φ (lam d - lam e) = 0) :
    ∑ d ∈ S, ∑ e ∈ S, A d * B e * Φ (lam d - lam e)
      = Φ 0 * ∑ d ∈ S, A d * B d := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_eq_single d]
  · simp; ring
  · intro e he hed
    rw [hvan d hd e he (Ne.symm hed)]; ring
  · intro h; exact absurd hd h

end HTGeometry
