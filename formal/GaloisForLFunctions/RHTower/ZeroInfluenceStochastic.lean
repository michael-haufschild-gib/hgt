import GaloisForLFunctions.RHTower.ZeroNetworkConductance

/-!
# The divisor-side influence matrix is exactly stochastic

Lane A of the uniform-certificate program asks whether a bounded-local-dependency argument of
Dobrushin type can force the free-orbit count to vanish. Dobrushin's mechanism needs the influence
matrix to be a strict contraction: `sup_j Σ_k P(j,k) < 1`, with the constant absolute and
independent of system size. This module computes that row sum for the zero network and finds it is
**exactly one**.

The influence of one zero on another is the conductance `1/|ρ_j − ρ_k|²`, whose rows are summable
because the divisor is locally finite. Normalising by the row total gives the influence matrix, and
the row sums are then `1` by construction — identically, with no dependence on the height and no
margin either way.

That is the verdict for this lane, and its shape matters more than its sign. Dobrushin does not fail
by a large factor, nor by a factor that grows with the height as every analytic estimate in this
field does. It fails by **exactly zero**. The mechanism is not weak here; it is marginal, in the same
way that every other inequality in this field is marginal.

The normalisation is not an artefact. The transverse marginality identity states
`Σ_k (δ_j − δ_k)·c(j,k) = 0`, which rearranges to `δ_j = Σ_k P(j,k)·δ_k`: the displacement is a
**harmonic function for this very chain**. So the influence matrix is stochastic because the
equilibrium condition is an averaging identity, and contraction would contradict the equilibrium.
The surviving question is the one this identifies — whether a bounded harmonic function on this chain
is constant — which is a recurrence question, not a contraction question.
-/

namespace RHTower

noncomputable section

/-- The total conductance at a zero: the row sum of the influence weights. -/
def zeroTotalConductance (j : XiDivisorSupport) : ℝ := ∑' k, zeroConductance j k

theorem zeroTotalConductance_nonneg (j : XiDivisorSupport) : 0 ≤ zeroTotalConductance j :=
  tsum_nonneg fun _ => div_nonneg zero_le_one (Complex.normSq_nonneg _)

/-- The normalised influence of one zero on another. -/
def zeroInfluence (j k : XiDivisorSupport) : ℝ :=
  zeroConductance j k * (zeroTotalConductance j)⁻¹

theorem zeroInfluence_nonneg (j k : XiDivisorSupport) : 0 ≤ zeroInfluence j k :=
  mul_nonneg (div_nonneg zero_le_one (Complex.normSq_nonneg _))
    (inv_nonneg.mpr (zeroTotalConductance_nonneg j))

theorem summable_zeroInfluence (j : XiDivisorSupport) :
    Summable (fun k => zeroInfluence j k) :=
  (summable_zeroConductance j).mul_right _

/-- **The row sums are exactly one.** -/
theorem tsum_zeroInfluence_eq_one {j : XiDivisorSupport} (h : zeroTotalConductance j ≠ 0) :
    ∑' k, zeroInfluence j k = 1 := by
  simp only [zeroInfluence]
  rw [tsum_mul_right]
  exact mul_inv_cancel₀ h

/-- **Dobrushin's contraction condition fails with exactly zero margin.** The row sum is not below
one, and the failure carries no dependence on the height. -/
theorem not_tsum_zeroInfluence_lt_one {j : XiDivisorSupport} (h : zeroTotalConductance j ≠ 0) :
    ¬ (∑' k, zeroInfluence j k < 1) := by
  rw [tsum_zeroInfluence_eq_one h]
  exact lt_irrefl 1

/-- The complementary statement: the row sum is not above one either. The matrix is stochastic on
the nose. -/
theorem not_one_lt_tsum_zeroInfluence {j : XiDivisorSupport} (h : zeroTotalConductance j ≠ 0) :
    ¬ (1 < ∑' k, zeroInfluence j k) := by
  rw [tsum_zeroInfluence_eq_one h]
  exact lt_irrefl 1

end

end RHTower
