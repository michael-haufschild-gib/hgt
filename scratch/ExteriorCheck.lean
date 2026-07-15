import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

open Module

example {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {n : ℕ} (v : Fin n → M) (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K n v ≠ 0 := by
  let s : Set.powersetCard (Fin n) n :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.id (Fin n))
  have hLI := exteriorPower.ιMulti_family_linearIndependent_field (n := n) hv
  have hne := hLI.ne_zero s
  simpa [exteriorPower.ιMulti_family, s] using hne

example {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {n : ℕ} (v : Fin n → M) (hv : ¬ LinearIndependent K v) :
    exteriorPower.ιMulti K n v = 0 := by
  let W : Submodule K M := Submodule.span K (Set.range v)
  let w : Fin n → W := fun i => ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  letI : Module.Finite K W := by
    dsimp [W]
    exact FiniteDimensional.span_of_finite K (Set.finite_range v)
  have hdim_le : Module.finrank K W ≤ n := by
    simpa [W] using (finrank_range_le_card (R := K) v)
  have hdim_ne : Module.finrank K W ≠ n := by
    intro h
    apply hv
    apply (linearIndependent_iff_card_eq_finrank_span (R := K)).2
    simpa [W] using h.symm
  have hdim_lt : Module.finrank K W < n := lt_of_le_of_ne hdim_le hdim_ne
  have hfin : Module.finrank K (⋀[K]^n W) = 0 := by
    rw [exteriorPower.finrank_eq, Nat.choose_eq_zero_of_lt hdim_lt]
  letI : Subsingleton (⋀[K]^n W) := Module.finrank_zero_iff.mp hfin
  have hwedge : exteriorPower.ιMulti K n w = 0 := Subsingleton.elim _ _
  have hmap := congrArg (exteriorPower.map n W.subtype) hwedge
  simpa [w, Function.comp_def] using hmap
