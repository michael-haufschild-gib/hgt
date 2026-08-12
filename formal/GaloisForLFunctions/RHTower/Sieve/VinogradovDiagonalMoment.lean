import GaloisForLFunctions.RHTower.Sieve.VinogradovPowerSumRigidity
import Mathlib.Data.List.Permutation
import Mathlib.Data.Fintype.Card

/-!
# Diagonal Vinogradov moment bound

For `b ≤ k`, the first `k` power-sum equations force the right tuple to be
a permutation of the left tuple.  Consequently the solution count is at most
`b! N^b`.  This is Lemma 24.3(a) and the base case of the classical
Vinogradov mean-value induction.
-/

namespace RHTower.Sieve

open scoped BigOperators

/-- A pair of length-`b` tuples in `[0,N)` satisfying the first `k`
Vinogradov power-sum equations. -/
def VinogradovDiagonalSolution (N b k : ℕ) :=
  {p : (Fin b → Fin N) × (Fin b → Fin N) //
    ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin b, (p.1 i).val ^ j = ∑ i : Fin b, (p.2 i).val ^ j}

noncomputable instance vinogradovDiagonalSolutionFinite (N b k : ℕ) :
    Finite (VinogradovDiagonalSolution N b k) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance vinogradovDiagonalSolutionFintype (N b k : ℕ) :
    Fintype (VinogradovDiagonalSolution N b k) := Fintype.ofFinite _

noncomputable section

/-- In the diagonal range `b ≤ k`, every solution has equal value multisets. -/
theorem vinogradovDiagonalSolution_multiset_eq
    {N b k : ℕ} (hbk : b ≤ k) (p : VinogradovDiagonalSolution N b k) :
    Finset.univ.val.map p.1.1 = Finset.univ.val.map p.1.2 := by
  have hnat : Finset.univ.val.map (fun i => (p.1.1 i).val) =
      Finset.univ.val.map (fun i => (p.1.2 i).val) := by
    apply nat_multiset_eq_of_powerSums_eq
    intro j hj1 hjb
    exact p.2 j hj1 (hjb.trans hbk)
  apply Multiset.map_injective Fin.val_injective
  simpa [Multiset.map_map, Function.comp_def] using hnat

/-- List-valued permutation certificate attached to a diagonal solution. -/
def vinogradovDiagonalSolutionPermutation
    {N b k : ℕ} (hbk : b ≤ k) (p : VinogradovDiagonalSolution N b k) :
    {l : List (Fin N) // l ∈ (List.ofFn p.1.1).permutations} :=
  ⟨List.ofFn p.1.2, List.mem_permutations.mpr <|
    Multiset.coe_eq_coe.mp <| by
      simpa using (vinogradovDiagonalSolution_multiset_eq hbk p).symm⟩

/-- A diagonal solution is determined by its left tuple and its right
permutation list. -/
def vinogradovDiagonalSolutionEmbedding
    {N b k : ℕ} (hbk : b ≤ k) :
    VinogradovDiagonalSolution N b k ↪
      Σ x : Fin b → Fin N,
        {l : List (Fin N) // l ∈ (List.ofFn x).permutations} where
  toFun p := ⟨p.1.1, vinogradovDiagonalSolutionPermutation hbk p⟩
  inj' := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Sigma.fst hpq
    · apply List.ofFn_injective
      exact congrArg (fun z => z.2.1) hpq

/-- At most `b!` distinct lists occur among the permutations of a length-`b`
list, with repetitions only decreasing the count. -/
theorem card_permutation_list_subtype_le_factorial
    {α : Type*} [Fintype α] [DecidableEq α] {b : ℕ} (x : Fin b → α) :
    Fintype.card {l : List α // l ∈ (List.ofFn x).permutations} ≤ b.factorial := by
  rw [Fintype.card_of_subtype ((List.ofFn x).permutations.toFinset) (by simp)]
  calc
    (List.ofFn x).permutations.toFinset.card ≤
        (List.ofFn x).permutations.length :=
      (List.ofFn x).permutations.toFinset_card_le
    _ = b.factorial := by rw [List.length_permutations, List.length_ofFn]

/-- **Diagonal Vinogradov moment bound.**  If `b ≤ k`, the number of
solutions of the first `k` power-sum equations in `[0,N)` is at most
`b! N^b`. -/
theorem card_vinogradovDiagonalSolution_le
    {N b k : ℕ} (hbk : b ≤ k) :
    Fintype.card (VinogradovDiagonalSolution N b k) ≤ b.factorial * N ^ b := by
  have hembed := Fintype.card_le_of_embedding
    (vinogradovDiagonalSolutionEmbedding (N := N) hbk)
  rw [Fintype.card_sigma] at hembed
  refine hembed.trans ?_
  calc
    (∑ x : Fin b → Fin N,
        Fintype.card {l : List (Fin N) // l ∈ (List.ofFn x).permutations}) ≤
        ∑ _x : Fin b → Fin N, b.factorial := by
      exact Finset.sum_le_sum fun x _ => card_permutation_list_subtype_le_factorial x
    _ = Fintype.card (Fin b → Fin N) * b.factorial := by simp
    _ = N ^ b * b.factorial := by simp
    _ = b.factorial * N ^ b := Nat.mul_comm _ _

end

end RHTower.Sieve
