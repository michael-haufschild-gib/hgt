import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerCombTailConvergenceCriterion

/-!
# Convergent power combs give an asymptotic for weighted prime contacts

The archimedean row and reference mesh already have unconditional limits.
The exact finite decomposition therefore transfers convergence of the
literal comb to its normalized arithmetic convolution, including endpoints.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The summatory prime-deviation convolution at the normalization of the comb. -/
def normalizedPowerContacts (a : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (2 * a - 1) *
    ∑ n ∈ Icc 1 N, (powerTailZeta (2 * a) * powerTailPrimeDeviation a) n

/-- Convergence of the power comb is equivalent to an actual leading
asymptotic for its weighted prime-contact sum, without a strict width gap. -/
theorem powerCombTailConverges_iff_normalizedPowerContacts_converges
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    PowerCombTailConverges a ↔
      ∃ L : ℝ, Tendsto (normalizedPowerContacts a) atTop (𝓝 L) := by
  let E : ℕ → ℝ := fun N =>
    (N : ℝ) ^ (2 * a - 1) * powerTailArchimedean a N -
      2 * tailRiemannSum (powerTailReferenceProfile a) N + powerTailCombRemainder a N
  have hE := ((tendsto_normalized_powerTailArchimedean ha ha2).sub
    ((riemannOn_powerTailReferenceProfile ha ha2).2.const_mul 2)).add
      (tendsto_powerTailCombRemainder ha ha2)
  change Tendsto E atTop (𝓝 _) at hE
  have he (N : ℕ) (hN : 1 ≤ N) :
      powerCombTail a N = E N - 2 * normalizedPowerContacts a N := by
    rw [powerCombTail_eq_mellin_meshes a hN]
    unfold E normalizedPowerContacts
    ring
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨_, ((hE.sub hL).div_const 2).congr' ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [he N hN]
    ring
  · rintro ⟨L, hL⟩
    refine ⟨_, (hE.sub (hL.const_mul 2)).congr' ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (he N hN).symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
