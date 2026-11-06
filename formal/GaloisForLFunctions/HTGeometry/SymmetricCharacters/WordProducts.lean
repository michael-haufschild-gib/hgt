import GaloisForLFunctions.Core
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Absolute mass of independent words over a summable alphabet -/

noncomputable section
open scoped BigOperators

namespace GaloisForLFunctions.SymmetricCharacters

/-- The total mass of words of length `r` is the `r`th power of the letter mass. -/
theorem wordProducts_summable_and_tsum {A : Type*} {g : A → ℝ}
    (hg : Summable g) (hnn : ∀ m, 0 ≤ g m) (r : ℕ) :
    (Summable fun f : Fin r → A => ∏ j, g (f j)) ∧
      (∑' f : Fin r → A, ∏ j, g (f j)) = (∑' m, g m) ^ r := by
  induction r with
  | zero =>
      haveI : Unique (Fin 0 → A) := Pi.uniqueOfIsEmpty _
      have hfun : (fun f : Fin 0 → A => ∏ j, g (f j)) = fun _ => (1 : ℝ) := by
        funext f
        simp
      refine ⟨?_, ?_⟩
      · rw [hfun]
        exact summable_of_hasFiniteSupport (Set.toFinite _)
      · rw [hfun, pow_zero, tsum_eq_single default]
        intro b hb
        exact absurd (Subsingleton.elim b default) hb
  | succ r ih =>
      obtain ⟨ihsum, ihtsum⟩ := ih
      have hprodSummable : Summable fun q : A × (Fin r → A) => g q.1 * ∏ j, g (q.2 j) :=
        Summable.mul_of_nonneg (f := g) (g := fun f : Fin r → A => ∏ j, g (f j)) hg ihsum hnn
          (fun f => Finset.prod_nonneg fun j _ => hnn (f j))
      have hcons : ∀ q : A × (Fin r → A),
          (∏ j, g (Fin.consEquiv (fun _ => A) q j)) = g q.1 * ∏ j, g (q.2 j) := by
        intro q
        rw [Fin.prod_univ_succ]
        simp [Fin.consEquiv_apply]
      refine ⟨?_, ?_⟩
      · refine ((Fin.consEquiv (fun _ : Fin (r + 1) => A)).summable_iff
          (f := fun f : Fin (r + 1) → A => ∏ j, g (f j))).mp ?_
        exact hprodSummable.congr fun q => (hcons q).symm
      · rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => A)).tsum_eq
          (fun f : Fin (r + 1) → A => ∏ j, g (f j))]
        rw [tsum_congr hcons]
        have hnormg : Summable fun m => ‖g m‖ := by
          refine hg.congr fun m => ?_
          rw [Real.norm_of_nonneg (hnn m)]
        have hnormp : Summable fun f : Fin r → A => ‖∏ j, g (f j)‖ := by
          refine ihsum.congr fun f => ?_
          rw [Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => hnn (f j))]
        rw [← tsum_mul_tsum_of_summable_norm hnormg hnormp, ihtsum, pow_succ]
        ring

end GaloisForLFunctions.SymmetricCharacters
