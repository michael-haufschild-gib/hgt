/-
The low-range input of a three-source subconvexity chain is slack, and the middle source is not.

The covering demand of an exponent pair `(κ, λ)` at length `T^(x₀)` is `G_(x₀)(κ,λ) - x₀/2` with
`G_(x₀)(κ,λ) = (1-x₀)κ + x₀λ`.  Minimising it at a prescribed length is minimising a linear
functional over the exponent-pair region, so the relevant pair changes with the length.

Two lengths matter in the published chain: `x₀ = 12/31`, where the middle source becomes available,
and `x₀ = 17/42`, where the final source becomes available.

* At `12/31` the demand of the published low-range pair `(1/9, 13/18)` is `43/279`, but the pure
  van der Corput word `(1/11, 3/4)` already gives `52/341`, and `A(32/205, 269/410) = (16/237, 743/948)`
  gives `1111/7347`.  All are far below the middle source's own demand `277/1792`, so **the low-range
  input is not the binding constraint** and cannot be made one.

* At `17/42` the same pairs demand `41/264` and `6173/39816`, both strictly **above** `13/84`.  The
  best of them misses by exactly `11/39816`.  So the low-range input cannot reach the final source's
  threshold, and **the middle source is necessary**.

A caution, recorded as a theorem below: the `A`-image of the *final* source's own exponent pair
`(13/84, 55/84)` would reach `17/42` with demand `15/97 < 13/84`, but that pair is the output of the
covering and so cannot be one of its inputs.  Its demand is recorded only to exhibit the exact margin
`13/84 - 15/97 = 1/8148`.
-/
import GaloisForLFunctions.HTGeometry.CoveringFunctionalNonstationarity

namespace HTGeometry

/-! ### Two pre-existing exponent pairs -/

/-- First coordinate of the van der Corput word `ABAB…` reached at `(1/11, 3/4)`. -/
def vdcWordKappa : ℚ := 1 / 11

/-- Its second coordinate. -/
def vdcWordLambda : ℚ := 3 / 4

/-- Huxley's exponent pair, first coordinate. -/
def huxleyPairKappa : ℚ := 32 / 205

/-- Huxley's exponent pair, second coordinate. -/
def huxleyPairLambda : ℚ := 269 / 410

/-- **The `A`-image of Huxley's pair.** -/
theorem procA_huxleyPair :
    procA_fst huxleyPairKappa = 16 / 237 ∧
      procA_snd huxleyPairKappa huxleyPairLambda = 743 / 948 := by
  constructor
  · unfold procA_fst huxleyPairKappa; norm_num
  · unfold procA_snd huxleyPairKappa huxleyPairLambda; norm_num

/-- Huxley's pair lies on the line of symmetry. -/
theorem huxleyPair_on_line : huxleyPairLambda = huxleyPairKappa + 1 / 2 := by
  unfold huxleyPairKappa huxleyPairLambda; norm_num

/-- Its subconvexity exponent is Huxley's `32/205`. -/
theorem huxleyPair_mu : epMu huxleyPairKappa huxleyPairLambda = 32 / 205 := by
  unfold epMu huxleyPairKappa huxleyPairLambda; norm_num

/-! ### At the middle source's threshold the low-range input is slack -/

/-- The van der Corput word's demand at `12/31`. -/
theorem vdcWord_demand_at_huxleyStart :
    covDemandOfPair huxleyStart vdcWordKappa vdcWordLambda = 52 / 341 := by
  unfold covDemandOfPair covFunctional huxleyStart vdcWordKappa vdcWordLambda; norm_num

/-- The `A`-image of Huxley's pair, demand at `12/31`. -/
theorem procA_huxleyPair_demand_at_huxleyStart :
    covDemandOfPair huxleyStart (procA_fst huxleyPairKappa)
        (procA_snd huxleyPairKappa huxleyPairLambda) = 1111 / 7347 := by
  rw [procA_huxleyPair.1, procA_huxleyPair.2]
  unfold covDemandOfPair covFunctional huxleyStart; norm_num

/-- **Both beat the published low-range pair.** -/
theorem low_range_inputs_beat_published :
    covDemandOfPair huxleyStart vdcWordKappa vdcWordLambda < expPairDemand ∧
      covDemandOfPair huxleyStart (procA_fst huxleyPairKappa)
          (procA_snd huxleyPairKappa huxleyPairLambda)
        < covDemandOfPair huxleyStart vdcWordKappa vdcWordLambda := by
  rw [vdcWord_demand_at_huxleyStart, procA_huxleyPair_demand_at_huxleyStart, expPairDemand_eq]
  constructor <;> norm_num

/-- **And all of them are strictly below the middle source's own demand**, so the low-range input is
slack: no improvement of it can lower the architecture's floor. -/
theorem low_range_strictly_slack :
    covDemandOfPair huxleyStart (procA_fst huxleyPairKappa)
        (procA_snd huxleyPairKappa huxleyPairLambda) < huxleyDemand ∧
      covDemandOfPair huxleyStart vdcWordKappa vdcWordLambda < huxleyDemand := by
  rw [procA_huxleyPair_demand_at_huxleyStart, vdcWord_demand_at_huxleyStart, huxleyDemand_eq]
  constructor <;> norm_num

/-- The slack of the pure van der Corput word against the middle source's demand. -/
theorem vdcWord_slack :
    huxleyDemand - covDemandOfPair huxleyStart vdcWordKappa vdcWordLambda = 1273 / 611072 := by
  rw [vdcWord_demand_at_huxleyStart, huxleyDemand_eq]; norm_num

/-- **Consequently the published cap `43/279` is not a barrier.**  It is an artefact of the choice of
low-range pair; already a pure van der Corput word does better, and the true floor of the architecture
is the middle source's demand `277/1792`. -/
theorem published_cap_is_not_a_barrier :
    covDemandOfPair huxleyStart vdcWordKappa vdcWordLambda < expPairDemand ∧
      expPairDemand < huxleyDemand ∧ huxleyDemand = sectionFourFloor := by
  refine ⟨low_range_inputs_beat_published.1, huxley_demand_dominates, ?_⟩
  rw [sectionFourFloor_eq, huxleyDemand_eq]

/-! ### At the final source's threshold the middle source is necessary -/

/-- The van der Corput word's demand at `17/42`. -/
theorem vdcWord_demand_at_decoupling :
    covDemandOfPair decouplingStart vdcWordKappa vdcWordLambda = 41 / 264 := by
  unfold covDemandOfPair covFunctional decouplingStart vdcWordKappa vdcWordLambda; norm_num

/-- The `A`-image of Huxley's pair, demand at `17/42`. -/
theorem procA_huxleyPair_demand_at_decoupling :
    covDemandOfPair decouplingStart (procA_fst huxleyPairKappa)
        (procA_snd huxleyPairKappa huxleyPairLambda) = 6173 / 39816 := by
  rw [procA_huxleyPair.1, procA_huxleyPair.2]
  unfold covDemandOfPair covFunctional decouplingStart; norm_num

/-- **The best pre-existing pair falls short of the final source's threshold by exactly
`11/39816`.** -/
theorem procA_huxleyPair_shortfall :
    covDemandOfPair decouplingStart (procA_fst huxleyPairKappa)
        (procA_snd huxleyPairKappa huxleyPairLambda) - bourgainTheta = 11 / 39816 := by
  rw [procA_huxleyPair_demand_at_decoupling]; unfold bourgainTheta; norm_num

/-- **The middle source cannot be removed.**  Every pre-existing exponent pair considered demands
strictly more than the record in order to cover as far as the final source's threshold. -/
theorem middle_source_necessary :
    bourgainTheta < covDemandOfPair decouplingStart (procA_fst huxleyPairKappa)
        (procA_snd huxleyPairKappa huxleyPairLambda) ∧
      bourgainTheta < covDemandOfPair decouplingStart vdcWordKappa vdcWordLambda ∧
      bourgainTheta < covDemandOfPair decouplingStart (1 / 9) (13 / 18) := by
  rw [procA_huxleyPair_demand_at_decoupling, vdcWord_demand_at_decoupling]
  refine ⟨?_, ?_, ?_⟩
  · unfold bourgainTheta; norm_num
  · unfold bourgainTheta; norm_num
  · unfold covDemandOfPair covFunctional decouplingStart bourgainTheta; norm_num

/-! ### The circular shortcut, recorded and excluded

The `A`-image of the final source's own exponent pair does reach the threshold, with margin
`1/8148`.  It is not an admissible input: that pair is the conclusion the covering establishes. -/

/-- The margin by which the `A`-image of the record pair would cover the threshold. -/
theorem record_pair_image_margin :
    bourgainTheta - covDemandOfPair decouplingStart (procA_fst bourgainKappa)
        (procA_snd bourgainKappa bourgainLambda) = 1 / 8148 := by
  rw [procA_bourgain_demand_at_decoupling]; unfold bourgainTheta; norm_num

/-- **The exact contrast.**  The image of the record pair covers the threshold; the image of the best
pair available beforehand does not; and the two demands differ by `1541/3862152`. -/
theorem covering_margin_contrast :
    covDemandOfPair decouplingStart (procA_fst bourgainKappa)
        (procA_snd bourgainKappa bourgainLambda) < bourgainTheta ∧
      bourgainTheta < covDemandOfPair decouplingStart (procA_fst huxleyPairKappa)
        (procA_snd huxleyPairKappa huxleyPairLambda) ∧
      covDemandOfPair decouplingStart (procA_fst huxleyPairKappa)
          (procA_snd huxleyPairKappa huxleyPairLambda)
        - covDemandOfPair decouplingStart (procA_fst bourgainKappa)
            (procA_snd bourgainKappa bourgainLambda) = 1541 / 3862152 := by
  rw [procA_bourgain_demand_at_decoupling, procA_huxleyPair_demand_at_decoupling]
  refine ⟨?_, ?_, ?_⟩
  · unfold bourgainTheta; norm_num
  · unfold bourgainTheta; norm_num
  · norm_num

end HTGeometry
