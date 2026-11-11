import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit
import GaloisForLFunctions.RHTower.DeBruijnLocalPairLawMonotonicity

/-!
# The heat flow has the count of its limit

The de Bruijn–Newman flow `H_t` is a regulator of `Ξ = H_0` that approaches it from the good
side. For `t ≥ 1/8` all zeros of `H_t` are real (`RHTower.DeBruijn.riemannHeat_zeros_real`); the
number `N(t)` of nonreal zeros is finite for `t > 0`, does not increase with `t`
(`nonrealZeroCount_antitoneOn`), and `H_t → Ξ` locally uniformly as `t → 0⁺`.

The nonreal zeros of `Ξ` come in conjugate pairs, so a unit gap of the regulator on times
tending to zero gives the Riemann hypothesis:

* `eventually_two_le_nonrealZeroCount`: if the Riemann hypothesis fails, `N(t) ≥ 2` for all
  small `t > 0`;
* `riemannHypothesis_of_frequently_nonrealZeroCount_le_one`: `N(t) ≤ 1` on times accumulating
  at `0` gives the Riemann hypothesis.

The gap is not available before the limit: when `Ξ` has finitely many nonreal zeros, `N(t)` is
their number for all small `t > 0` (`eventually_nonrealZeroCount_eq_of_finite`). Like the
scattering tower, the heat flow has the count of its limit at every small cutoff.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open _root_.RHTower _root_.RHTower.DeBruijn

/-- **Without the Riemann hypothesis the heat flow has at least two nonreal zeros** at every
small time: a nonreal zero of `Ξ` and its conjugate survive. -/
theorem eventually_two_le_nonrealZeroCount (h : ¬ RiemannHypothesis) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), 2 ≤ nonrealZeroCount s := by
  rw [riemannHypothesis_iff_riemannHeat_zero_real] at h
  push Not at h
  obtain ⟨z, hz, him⟩ := h
  have hc : riemannHeat 0 (conj z) = 0 := by
    rw [riemannHeat_conj le_rfl, hz, map_zero]
  have hne : z ≠ conj z := fun heq => him (by
    have hi := congrArg Complex.im heq
    rw [Complex.conj_im] at hi
    linarith only [hi])
  have hlow := eventually_sum_zeroMult_le_nonrealZeroCount (E := {z, conj z}) (fun e he => by
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨hz, him⟩
    · rw [Finset.mem_singleton.mp he]
      exact ⟨hc, by rw [Complex.conj_im]; exact neg_ne_zero.mpr him⟩)
  filter_upwards [hlow] with s hs
  rw [Finset.sum_pair hne] at hs
  have h1 := one_le_zeroMult_riemannHeat le_rfl hz
  have h2 := one_le_zeroMult_riemannHeat le_rfl hc
  omega

/-- **A unit gap of the heat flow gives the Riemann hypothesis.** If `H_t` has at most one
nonreal zero on times `t > 0` accumulating at `0`, all zeros of `Ξ` are real. -/
theorem riemannHypothesis_of_frequently_nonrealZeroCount_le_one
    (h : ∃ᶠ s in 𝓝[>] (0 : ℝ), nonrealZeroCount s ≤ 1) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨s, hs1, hs2⟩ := (h.and_eventually (eventually_two_le_nonrealZeroCount hRH)).exists
  omega

end GaloisForLFunctions.FloorFreeArithmetic
