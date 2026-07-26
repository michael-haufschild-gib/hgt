/-
A covering by unrestricted exponent pairs is worth exactly the best single pair.

The demand of an exponent pair at the critical length is its pointwise exponent `μ`, whatever its
displacement.  Consequently, in a covering argument for `x ∈ [0, 1/2]`:

* whichever source covers the right endpoint `x = 1/2` must already demand at least its own `μ`, so
  a covering assembled from sources that are valid at every length can never beat `min μ`;
* conversely a single pair on or above the line of symmetry covers the whole interval at exactly its
  own `μ`.

**So the covering architecture is worth nothing over the best available pair, and its entire value
comes from sources whose validity is restricted to a sub-range.**  A restricted source available only
on `[x₁, 1/2]` is worth what it improves on the pairs' demand at `x₁`, and the pairs' demand at `x₁`
is discounted below their `μ` by exactly the displacement times the length deficit `1/2 - x₁`.

This gives the exact value of a range restriction: the improvement obtainable from a source valid
only above `T^(x₁)` is bounded by the displacement discount available at `x₁`, unless further
restricted sources are supplied to fill the remaining range.
-/
import GaloisForLFunctions.HTGeometry.CriticalLengthEigenspace

namespace HTGeometry

/-! ### A covering by unrestricted pairs cannot beat the best pair -/

/-- **Whatever source covers the critical length already pays its own `μ`.** -/
theorem covering_pays_mu_at_critical {ι : Type*} (S : Finset ι) (κ lam : ι → ℚ) (θ : ℚ)
    (hcov : ∃ i ∈ S, covDemandOfPair (1 / 2) (κ i) (lam i) ≤ θ) :
    ∃ i ∈ S, epMu (κ i) (lam i) ≤ θ := by
  obtain ⟨i, hi, h⟩ := hcov
  exact ⟨i, hi, by rwa [displacement_free_at_critical_length] at h⟩

/-- **A covering of the whole range by pairs valid at every length is worth exactly the best pair.**
The hypothesis is the covering condition; the conclusion is that some pair already has `μ ≤ θ`. -/
theorem unrestricted_covering_floor {ι : Type*} (S : Finset ι) (κ lam : ι → ℚ) (θ : ℚ)
    (hcov : ∀ x : ℚ, 0 ≤ x → x ≤ 1 / 2 → ∃ i ∈ S, covDemandOfPair x (κ i) (lam i) ≤ θ) :
    ∃ i ∈ S, epMu (κ i) (lam i) ≤ θ :=
  covering_pays_mu_at_critical S κ lam θ (hcov (1 / 2) (by norm_num) le_rfl)

/-- **Conversely, one pair on or above the line of symmetry covers the whole range at its own `μ`.**
So the bound `min μ` is attained, not merely approached. -/
theorem single_pair_covers_at_mu {κ lam : ℚ} (hd : 0 ≤ epDisplacement κ lam) {x : ℚ}
    (hx : x ≤ 1 / 2) :
    covDemandOfPair x κ lam ≤ epMu κ lam := by
  rw [covDemand_factorisation]
  have : epDisplacement κ lam * (x - 1 / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hd (by linarith)
  linarith

/-- The two halves together: for unrestricted pairs the covering value is exactly the best `μ`. -/
theorem unrestricted_covering_value {κ lam : ℚ} (hd : 0 ≤ epDisplacement κ lam) :
    (∀ x : ℚ, 0 ≤ x → x ≤ 1 / 2 → covDemandOfPair x κ lam ≤ epMu κ lam) ∧
      covDemandOfPair (1 / 2) κ lam = epMu κ lam :=
  ⟨fun _ _ hx => single_pair_covers_at_mu hd hx, displacement_free_at_critical_length κ lam⟩

/-! ### The value of a range restriction -/

/-- The discount a pair's demand enjoys at length `x₁` relative to its own `μ`. -/
def displacementDiscount (κ lam x₁ : ℚ) : ℚ := epDisplacement κ lam * (1 / 2 - x₁)

/-- **The demand at `x₁` is the pointwise exponent less the displacement discount.** -/
theorem demand_eq_mu_sub_discount (κ lam x₁ : ℚ) :
    covDemandOfPair x₁ κ lam = epMu κ lam - displacementDiscount κ lam x₁ := by
  rw [covDemand_factorisation]; unfold displacementDiscount; ring

/-- The discount is nonnegative for pairs above the line and lengths below the critical one. -/
theorem displacementDiscount_nonneg {κ lam x₁ : ℚ} (hd : 0 ≤ epDisplacement κ lam)
    (hx : x₁ ≤ 1 / 2) : 0 ≤ displacementDiscount κ lam x₁ :=
  mul_nonneg hd (by linarith)

/-- The discount vanishes exactly at the critical length, for any pair off the line. -/
theorem displacementDiscount_eq_zero_iff {κ lam x₁ : ℚ} (hd : epDisplacement κ lam ≠ 0) :
    displacementDiscount κ lam x₁ = 0 ↔ x₁ = 1 / 2 := by
  unfold displacementDiscount
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hd
    · linarith
  · intro h; rw [h]; ring

/-- **The exact value of a range-restricted source.**  If a source valid only on `[x₁, 1/2]` demands
`β` there, and a pair covers `[0, x₁]`, the resulting exponent is the larger of `β` and the pair's
discounted demand.  So the restricted source improves on the pair's own `μ` precisely when it beats
`μ` and the pair still reaches `x₁`. -/
theorem restricted_source_value {κ lam x₁ β : ℚ} (hβ : β < epMu κ lam)
    (hreach : covDemandOfPair x₁ κ lam ≤ β) :
    max β (covDemandOfPair x₁ κ lam) = β ∧ β < epMu κ lam :=
  ⟨max_eq_left hreach, hβ⟩

/-- **The cap on what a range restriction can buy.**  The pair reaches `x₁` at demand
`μ - discount`, so any restricted source that the pair can hand off to must have
`β ≥ μ - discount`: the total improvement over the pair's own exponent is at most the displacement
discount at the restriction's threshold. -/
theorem restriction_improvement_capped {κ lam x₁ β : ℚ}
    (hreach : covDemandOfPair x₁ κ lam ≤ β) :
    epMu κ lam - β ≤ displacementDiscount κ lam x₁ := by
  rw [demand_eq_mu_sub_discount] at hreach
  linarith

/-! ### The published architecture in these terms -/

/-- The discount available to the `A`-image of Huxley's pair at the decoupling threshold. -/
theorem procA_huxleyPair_discount :
    displacementDiscount (procA_fst huxleyPairKappa) (procA_snd huxleyPairKappa huxleyPairLambda)
        decouplingStart = 205 / 9954 := by
  unfold displacementDiscount
  rw [procA_huxleyPair_data.2]
  unfold decouplingStart; norm_num

/-- **The best pre-existing pointwise exponent is Huxley's `32/205`, and the best discounted demand at
the decoupling threshold is `6173/39816`.**  Their difference is the entire window in which a
range-restricted source can improve on the exponent-pair record using a single handoff. -/
theorem improvement_window :
    epMu huxleyPairKappa huxleyPairLambda = 32 / 205 ∧
      covDemandOfPair decouplingStart (procA_fst huxleyPairKappa)
          (procA_snd huxleyPairKappa huxleyPairLambda) = 6173 / 39816 ∧
      (32 : ℚ) / 205 - 6173 / 39816 = 8647 / 8162280 := by
  refine ⟨huxleyPair_mu, procA_huxleyPair_demand_at_decoupling, by norm_num⟩

/-- **Bourgain's exponent lies below the window.**  His restricted source is better than any single
handoff from an exponent pair can absorb, which is exactly why a second restricted source — Huxley's
bound — is required to fill the range. -/
theorem record_below_improvement_window :
    bourgainTheta < covDemandOfPair decouplingStart (procA_fst huxleyPairKappa)
        (procA_snd huxleyPairKappa huxleyPairLambda) ∧
      bourgainTheta < epMu huxleyPairKappa huxleyPairLambda := by
  rw [procA_huxleyPair_demand_at_decoupling, huxleyPair_mu]
  constructor <;> (unfold bourgainTheta; norm_num)

/-- **Summary of the architecture.**  Sources valid at every length contribute only their `μ`; the
record is strictly below every such `μ`; hence the record is carried entirely by range-restricted
sources, and the exponent pairs serve only to complete the range. -/
theorem architecture_summary :
    bourgainTheta < epMu huxleyPairKappa huxleyPairLambda ∧
      bourgainTheta < epMu weylKappa weylLambda ∧
      bourgainTheta < epMu biKappa biLambda ∧
      covDemandOfPair (1 / 2) bourgainKappa bourgainLambda = bourgainTheta := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [huxleyPair_mu]; unfold bourgainTheta; norm_num
  · unfold epMu weylKappa weylLambda bourgainTheta; norm_num
  · unfold epMu biKappa biLambda bourgainTheta; norm_num
  · rw [displacement_free_at_critical_length, bourgain_pair_mu]

end HTGeometry
