import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit

/-!
# The finite-stratum law on the heat family is the Riemann hypothesis

The heat deformations `H_t` of Riemann's `Ξ` (`riemannHeat t`, `t > 0`) keep the functional
equation, reality on the real axis and the positivity of the Pólya kernel, and each has only
finitely many non-real zeros (Ki–Kim–Lee, `riemannHeat_nonreal_zeros_finite`): every `H_t` lies in
the finite stratum.

**Theorem** (`riemannHypothesis_of_finiteStratumLaw_on_heat`). Let `P` be any property of entire
functions that holds for every `H_t`, `t > 0`, and that implies the finite-stratum law "finitely many
non-real zeros forces none". Then RH holds.

So a mechanism for B13 that applies to the heat family is already RH (de Bruijn–Newman). An input for
B13 must separate `Ξ` from its heat deformations, which share the functional equation and Pólya
positivity but carry no Euler product.
-/

open Complex Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

open _root_.RHTower _root_.RHTower.DeBruijn

/-- **The finite-stratum law on the heat family is RH.** -/
theorem riemannHypothesis_of_finiteStratumLaw_on_heat {P : (ℂ → ℂ) → Prop}
    (hP : ∀ t : ℝ, 0 < t → P (riemannHeat t))
    (hlaw : ∀ F : ℂ → ℂ, P F → {z : ℂ | F z = 0 ∧ z.im ≠ 0}.Finite →
      ∀ z : ℂ, F z = 0 → z.im = 0) :
    RiemannHypothesis := by
  refine riemannHypothesis_iff_eventually_nonrealZeroCount_eq_zero.mpr ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [nonrealZeroCount_eq ht]
  refine Finset.sum_eq_zero fun z hz => ?_
  have hz' := (Set.Finite.mem_toFinset _).mp hz
  exact absurd (hlaw _ (hP t ht) (riemannHeat_nonreal_zeros_finite ht) z hz'.1) hz'.2

end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
