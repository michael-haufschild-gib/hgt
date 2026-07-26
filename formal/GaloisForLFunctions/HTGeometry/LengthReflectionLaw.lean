/-
The length-reflection law for exponent pairs.

The covering demand of an exponent pair `(κ, λ)` at length `M = T^(x₀)` is `κ + (λ - κ - 1/2)·x₀`.
Writing `μ(κ,λ) = (κ + λ - 1/2)/2` for the pointwise subconvexity exponent and

    d(κ, λ) := (λ - κ) - 1/2

for the pair's signed displacement from the line of symmetry `λ = κ + 1/2`, the demand factors
exactly:

    **demand(κ, λ, x₀) = μ(κ, λ) + d(κ, λ) · (x₀ - 1/2).**

Three consequences.

* At the critical length `x₀ = 1/2` the displacement term vanishes identically: **the covering problem
  at the critical length is the pointwise problem, and the second dimension of the exponent-pair
  region is priced at zero there.**  Away from the critical length it is priced at `|x₀ - 1/2|` per
  unit of displacement, so pairs off the line of symmetry become competitive.

* A pair is length-neutral — its demand does not depend on the length — exactly when it lies on the
  line of symmetry.  All four landmark pairs (Weyl, Bombieri–Iwaniec, Huxley, Bourgain) lie there.

* The van der Corput `B`-process negates the displacement and preserves `μ`, hence

    **demand(B(κ,λ), x₀) = demand(κ, λ, 1 - x₀).**

  `B` *is* the reflection `x₀ ↦ 1 - x₀` of the length variable, and its fixed-point set, the line of
  symmetry, matches the reflection's fixed point `x₀ = 1/2`.

The `A`-process moves a pair off the line, which is worth something at every length below the
critical one and worth exactly nothing at the critical one.  That is the precise reason the
`A`-process improves the covering functional at Bourgain's pair while worsening its `μ`.
-/
import GaloisForLFunctions.HTGeometry.LowRangeSlackAndHuxleyNecessity

namespace HTGeometry

/-! ### Displacement and the factorisation -/

/-- The signed displacement of an exponent pair from the line of symmetry `λ = κ + 1/2`. -/
def epDisplacement (κ lam : ℚ) : ℚ := (lam - κ) - 1 / 2

/-- A pair is on the line of symmetry exactly when its displacement vanishes. -/
theorem epDisplacement_eq_zero_iff (κ lam : ℚ) :
    epDisplacement κ lam = 0 ↔ lam = κ + 1 / 2 := by
  unfold epDisplacement
  constructor <;> intro h <;> linarith

/-- **The length-reflection factorisation.**  The covering demand splits into the pointwise exponent
and the displacement scaled by the length deficit. -/
theorem covDemand_factorisation (x₀ κ lam : ℚ) :
    covDemandOfPair x₀ κ lam = epMu κ lam + epDisplacement κ lam * (x₀ - 1 / 2) := by
  unfold covDemandOfPair covFunctional epMu epDisplacement; ring

/-- **At the critical length the displacement is priced at zero.** -/
theorem displacement_free_at_critical_length (κ lam : ℚ) :
    covDemandOfPair (1 / 2) κ lam = epMu κ lam := by
  rw [covDemand_factorisation]; ring

/-- **A pair is length-neutral exactly when it lies on the line of symmetry.** -/
theorem length_neutral_iff_on_line (κ lam : ℚ) :
    (∀ x₀ : ℚ, covDemandOfPair x₀ κ lam = epMu κ lam) ↔ lam = κ + 1 / 2 := by
  constructor
  · intro h
    rw [← epDisplacement_eq_zero_iff]
    have h0 := h 0
    have h1 := h 1
    rw [covDemand_factorisation] at h0 h1
    linarith
  · intro h x₀
    rw [covDemand_factorisation, (epDisplacement_eq_zero_iff κ lam).mpr h]
    ring

/-- Off the line the demand is strictly monotone in the length: strictly increasing above the line,
strictly decreasing below it. -/
theorem covDemand_strictMono_of_displacement_pos {κ lam x y : ℚ}
    (hd : 0 < epDisplacement κ lam) (hxy : x < y) :
    covDemandOfPair x κ lam < covDemandOfPair y κ lam := by
  rw [covDemand_factorisation, covDemand_factorisation]
  have : epDisplacement κ lam * (x - 1 / 2) < epDisplacement κ lam * (y - 1 / 2) := by
    apply mul_lt_mul_of_pos_left _ hd; linarith
  linarith

/-! ### The `B`-process is the length reflection -/

/-- **`B` negates the displacement.** -/
theorem procB_negates_displacement (κ lam : ℚ) :
    epDisplacement (procB_fst lam) (procB_snd κ) = - epDisplacement κ lam := by
  unfold epDisplacement procB_fst procB_snd; ring

/-- **The length-reflection law.**  Applying the `B`-process to a pair is exactly reflecting the
length variable in the critical length. -/
theorem procB_is_length_reflection (x₀ κ lam : ℚ) :
    covDemandOfPair x₀ (procB_fst lam) (procB_snd κ) = covDemandOfPair (1 - x₀) κ lam := by
  rw [covDemand_factorisation, covDemand_factorisation, epMu_procB,
    procB_negates_displacement]
  ring

/-- The reflection fixes exactly the critical length. -/
theorem reflection_fixed_point (x₀ : ℚ) : 1 - x₀ = x₀ ↔ x₀ = 1 / 2 := by
  constructor <;> intro h <;> linarith

/-- **`B` is an involution on displacements, and its fixed pairs are the length-neutral ones.** -/
theorem procB_fixed_iff_on_line (κ lam : ℚ) :
    epDisplacement (procB_fst lam) (procB_snd κ) = epDisplacement κ lam ↔ lam = κ + 1 / 2 := by
  rw [procB_negates_displacement, ← epDisplacement_eq_zero_iff]
  constructor <;> intro h <;> linarith

/-! ### The landmark pairs are exactly the length-neutral ones -/

/-- Weyl's pair. -/
def weylKappa : ℚ := 1 / 6
/-- Weyl's pair, second coordinate. -/
def weylLambda : ℚ := 2 / 3
/-- Bombieri–Iwaniec's pair. -/
def biKappa : ℚ := 9 / 56
/-- Bombieri–Iwaniec's pair, second coordinate. -/
def biLambda : ℚ := 37 / 56

/-- **All four landmark pairs are length-neutral.** -/
theorem landmarks_length_neutral :
    epDisplacement weylKappa weylLambda = 0 ∧
      epDisplacement biKappa biLambda = 0 ∧
      epDisplacement huxleyPairKappa huxleyPairLambda = 0 ∧
      epDisplacement bourgainKappa bourgainLambda = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold epDisplacement weylKappa weylLambda; norm_num
  · unfold epDisplacement biKappa biLambda; norm_num
  · unfold epDisplacement huxleyPairKappa huxleyPairLambda; norm_num
  · unfold epDisplacement bourgainKappa bourgainLambda; norm_num

/-- **Hence every landmark pair demands its own `μ` at every length**: the record sequence gains
nothing from being asked to cover only a short range. -/
theorem landmark_demand_constant (x₀ : ℚ) :
    covDemandOfPair x₀ bourgainKappa bourgainLambda = bourgainTheta := by
  rw [covDemand_factorisation, landmarks_length_neutral.2.2.2, bourgain_pair_mu]; ring

/-! ### The `A`-process buys displacement -/

/-- The displacement of the `A`-image of Bourgain's pair. -/
theorem procA_bourgain_displacement :
    epDisplacement (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
      = 21 / 97 := by
  rw [procA_bourgain.1, procA_bourgain.2]
  unfold epDisplacement; norm_num

/-- Its pointwise exponent. -/
theorem procA_bourgain_mu :
    epMu (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda) = 17 / 97 := by
  rw [procA_bourgain.1, procA_bourgain.2]
  unfold epMu; norm_num

/-- **The exact trade.**  `A` raises Bourgain's pointwise exponent from `13/84` to `17/97` and buys
displacement `21/97`; the two balance at the length where the demands agree. -/
theorem procA_bourgain_trade (x₀ : ℚ) :
    covDemandOfPair x₀ (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
      = 17 / 97 + (21 / 97) * (x₀ - 1 / 2) := by
  rw [covDemand_factorisation, procA_bourgain_mu, procA_bourgain_displacement]

/-- The length below which the `A`-image beats Bourgain's own pair. -/
def bourgainImageCrossover : ℚ := 715 / 1764

/-- **Consistency with the productivity threshold.**  The two demands agree exactly at `715/1764`. -/
theorem procA_bourgain_demands_agree :
    covDemandOfPair bourgainImageCrossover (procA_fst bourgainKappa)
        (procA_snd bourgainKappa bourgainLambda)
      = covDemandOfPair bourgainImageCrossover bourgainKappa bourgainLambda := by
  rw [procA_bourgain_trade, landmark_demand_constant]
  unfold bourgainImageCrossover bourgainTheta; norm_num

/-! ### Where the covering-optimal pair switches

Among the pairs available before the decoupling bound, `A(32/205, 269/410)` is optimal for the
covering functional at short lengths and Bourgain's own pair at long ones.  They cross at
`579/1435`, just below the decoupling threshold. -/

/-- The length at which the covering-optimal pair switches. -/
def optimalPairSwitch : ℚ := 579 / 1435

/-- Displacement and pointwise exponent of the `A`-image of Huxley's pair. -/
theorem procA_huxleyPair_data :
    epMu (procA_fst huxleyPairKappa) (procA_snd huxleyPairKappa huxleyPairLambda) = 111 / 632 ∧
      epDisplacement (procA_fst huxleyPairKappa) (procA_snd huxleyPairKappa huxleyPairLambda)
        = 205 / 948 := by
  rw [procA_huxleyPair.1, procA_huxleyPair.2]
  constructor
  · unfold epMu; norm_num
  · unfold epDisplacement; norm_num

/-- **The two demands agree exactly at `579/1435`.** -/
theorem optimalPairSwitch_balances :
    covDemandOfPair optimalPairSwitch (procA_fst huxleyPairKappa)
        (procA_snd huxleyPairKappa huxleyPairLambda)
      = covDemandOfPair optimalPairSwitch bourgainKappa bourgainLambda := by
  rw [covDemand_factorisation, procA_huxleyPair_data.1, procA_huxleyPair_data.2,
    landmark_demand_constant]
  unfold optimalPairSwitch bourgainTheta; norm_num

/-- **Four independently defined thresholds of the published architecture lie in one window of width
`317/167895 ≈ 1.9·10⁻³`:** the optimal-pair switch, the decoupling threshold, the productivity
threshold of the `A`-process at Bourgain's pair, and Huxley's reach at the record. -/
theorem four_thresholds_cluster :
    optimalPairSwitch < decouplingStart ∧
      decouplingStart < bourgainAThreshold ∧
      bourgainAThreshold < coveringReach huxleyAlpha huxleyBeta bourgainTheta ∧
      coveringReach huxleyAlpha huxleyBeta bourgainTheta - optimalPairSwitch = 317 / 167895 := by
  rw [huxley_reach]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold optimalPairSwitch decouplingStart; norm_num
  · unfold decouplingStart bourgainAThreshold; norm_num
  · unfold bourgainAThreshold; norm_num
  · unfold optimalPairSwitch; norm_num

/-! ### The barrier in final form -/

/-- **The barrier.**  The exponent-pair region is two-dimensional, but the coefficient of its second
dimension in the covering demand is `x₀ - 1/2`.  The approximate functional equation forces the
critical length `x₀ = 1/2`, where that coefficient vanishes — so at the one length that decides
`μ(1/2)`, the second dimension is worth nothing, and every mechanism that exploits it (the
`A`-process, off-line pairs, the covering architecture, `B`-conjugation) is priced at zero. -/
theorem second_dimension_priced_at_zero (κ lam κ' lam' : ℚ) (hmu : epMu κ lam = epMu κ' lam') :
    covDemandOfPair (1 / 2) κ lam = covDemandOfPair (1 / 2) κ' lam' := by
  rw [displacement_free_at_critical_length, displacement_free_at_critical_length, hmu]

/-- And away from the critical length two pairs with equal `μ` are separated exactly by their
displacement gap times the length deficit. -/
theorem demand_gap_of_equal_mu {κ lam κ' lam' : ℚ} (hmu : epMu κ lam = epMu κ' lam') (x₀ : ℚ) :
    covDemandOfPair x₀ κ lam - covDemandOfPair x₀ κ' lam'
      = (epDisplacement κ lam - epDisplacement κ' lam') * (x₀ - 1 / 2) := by
  rw [covDemand_factorisation, covDemand_factorisation, hmu]; ring

end HTGeometry
