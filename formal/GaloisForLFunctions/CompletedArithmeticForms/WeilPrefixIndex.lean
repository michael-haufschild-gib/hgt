import GaloisForLFunctions.TransMetzlerWeilPositivity.APositivePrefixGivesTheExactSchurReduction

/-!
# A macroscopic upper index bound for the complete Weil source

The uniformly paid prefix gives a quantitative dimension ceiling without discarding
mixed entries: tail restriction is injective on every strictly negative subspace. At
overlap three halves and length `3K`, the ceiling is `K`. This bound grows with the
horizon; it does not assert positivity of the remaining complete Schur complement.
-/

noncomputable section

open Finset Matrix Filter Topology

namespace GaloisForLFunctions.CompletedArithmeticForms

open TransMetzlerWeilPositivity SpacingScaleHarmonicAnalysis
  CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory

private def horizonTailEquivFin (M N : ℕ) : HorizonTail M N ≃ Fin (N - M) where
  toFun n := ⟨n.val.val - (M + 1), by
    have hn := (mem_Icc.mp n.val.property).2
    have ht := n.property
    omega⟩
  invFun i := ⟨⟨M + i.val + 1, mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩⟩,
    by omega⟩
  left_inv n := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have := n.property
    omega
  right_inv i := by
    apply Fin.ext
    dsimp
    omega

private theorem card_horizonTail (M N : ℕ) : Fintype.card (HorizonTail M N) = N - M := by
  rw [Fintype.card_congr (horizonTailEquivFin M N), Fintype.card_fin]

private theorem sum_horizon_split {M N : ℕ} (hMN : M ≤ N)
    (f : PrimeHorizonIndex N → ℝ) :
    (∑ n : PrimeHorizonIndex N, f n) =
      (∑ n : PrimeHorizonIndex M, f (horizonPrefixMap hMN n)) +
        ∑ n : HorizonTail M N, f n.val := by
  rw [← Equiv.sum_comp (horizonPrefixSplit hMN) f, Fintype.sum_sum_type]
  rfl

private theorem completeWeil_quad_eq_prefix {M N : ℕ} (hMN : M ≤ N)
    (c : ℝ) (x : PrimeHorizonIndex N → ℝ) (hx : ∀ n : HorizonTail M N, x n.val = 0) :
    x ⬝ᵥ (completeWeilMatrix transMetzlerProfile c N).mulVec x =
      (fun n => x (horizonPrefixMap hMN n)) ⬝ᵥ
        (plateauPrefixBlock hMN c).mulVec (fun n => x (horizonPrefixMap hMN n)) := by
  simp only [dotProduct, Matrix.mulVec, mul_sum]
  rw [sum_horizon_split hMN]
  have htail : (∑ n : HorizonTail M N, ∑ j : PrimeHorizonIndex N,
      x n.val * (completeWeilMatrix transMetzlerProfile c N n.val j * x j)) = 0 := by
    simp only [hx, zero_mul, sum_const_zero]
  rw [htail, add_zero]
  refine sum_congr rfl fun n _ => ?_
  rw [sum_horizon_split hMN]
  simp only [hx, mul_zero, zero_mul, sum_const_zero, add_zero,
    plateauPrefixBlock, Matrix.submatrix_apply]

/-- Tail coordinates distinguish every vector in a negative subspace of the actual source. -/
theorem eventually_completeWeil_negative_subspace_dim_le_tail :
    ∀ᶠ M : ℕ in atTop, ∀ N : ℕ, ∀ hMN : M ≤ N, ∀ c : ℝ,
      0 < c → c * M ≤ N →
      ∀ W : Submodule ℝ (PrimeHorizonIndex N → ℝ),
        (∀ x ∈ W, x ≠ 0 → x ⬝ᵥ (completeWeilMatrix transMetzlerProfile c N).mulVec x < 0) →
          Module.finrank ℝ W ≤ N - M := by
  classical
  filter_upwards [eventually_plateauPrefixBlock_posDef] with M hM
  intro N hMN c hc hcM W hW
  have hprefix := hM N hMN c hc hcM
  let F : W →ₗ[ℝ] (HorizonTail M N → ℝ) :=
    { toFun := fun x n => x.val n.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have hx0 : (x : PrimeHorizonIndex N → ℝ) ≠ 0 := fun h => hne (Subtype.ext h)
    have hzero : ∀ n : HorizonTail M N, x.val n.val = 0 := fun n => congrFun hx n
    have hneg := hW x x.property hx0
    rw [completeWeil_quad_eq_prefix hMN c x hzero] at hneg
    have hnonneg := hprefix.posSemidef.2 (fun n => x.val (horizonPrefixMap hMN n))
    simp only [star_trivial] at hnonneg
    exact not_lt_of_ge hnonneg hneg
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fintype_fun_eq_card, card_horizonTail] using hdim

/-- At fixed overlap three halves, negative directions occupy at most one third of the horizon. -/
theorem eventually_three_halves_negative_subspace_dim_le :
    ∀ᶠ K : ℕ in atTop,
      ∀ W : Submodule ℝ (PrimeHorizonIndex (3 * K) → ℝ),
        (∀ x ∈ W, x ≠ 0 →
          x ⬝ᵥ (completeWeilMatrix transMetzlerProfile (3 / 2) (3 * K)).mulVec x < 0) →
            Module.finrank ℝ W ≤ K := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp eventually_completeWeil_negative_subspace_dim_le_tail
  filter_upwards [eventually_ge_atTop B] with K hK
  intro W hW
  have h := hB (2 * K) (by omega) (3 * K) (by omega) (3 / 2)
    (by positivity) (by push_cast; linarith) W hW
  simpa only [show 3 * K - 2 * K = K by omega] using h

#print axioms eventually_completeWeil_negative_subspace_dim_le_tail
#print axioms eventually_three_halves_negative_subspace_dim_le

end GaloisForLFunctions.CompletedArithmeticForms
