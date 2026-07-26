/-
What an exponent pair gives off the critical line, and why the transfer needs something else.

Split the approximate functional equation into dyadic blocks `M`.  The block at `M` contributes
`M^(-σ)` times an exponential sum of length `M` with `F ≍ t`, so an exponent pair `(κ, λ)` bounds it
by `t^κ M^(λ-κ-σ)`, while the trivial bound gives `M^(1-σ)`.  The two agree at the crossover
`M₀ = t^(κ/(1+κ-λ))`, and the profile's maximum is attained either there or at the critical block
`M = t^(1/2)`.

On the line of symmetry `λ = κ + 1/2` — where every record pair lies — the two branch values are

    crossover block :  **2κ(1 - σ)** ,        critical block :  **κ - (σ - 1/2)/2** ,

and the crossover dominates exactly for `σ ≥ 1/2`, since `κ < 1/4`.  So a record pair gives the
**linear** profile

    **μ(σ) ≤ 2κ(1 - σ)   for σ ≥ 1/2,**

correct at both ends: `2κ·(1/2) = κ` at `σ = 1/2`, and `0` at `σ = 1`.

Feeding that profile into the off-line transfer `μ(1/2) ≤ μ(σ) + (σ - 1/2)/2` gives
`2κ(1-σ) + (σ - 1/2)/2`, whose derivative in `σ` is `1/2 - 2κ > 0`.  **The minimum is at `σ = 1/2`
and equals `κ`: the transfer returns exactly the pair's own critical-line value.**  So the transfer is
useful only with an off-line bound that does not come from an exponent pair.

For the record pair at `σ = 7/10`, in eight-hundred-fortieths:

    exponent-pair prediction   13/140 = **78/840**
    published bound             3/40  = **63/840**
    record-matching threshold  23/420 = **46/840**

The published bound has captured `15/840` of the `32/840` available; `17/840` remains.
-/
import GaloisForLFunctions.HTGeometry.OffLineTransfer

namespace HTGeometry

/-! ### The two branches -/

/-- The crossover block's contribution to the growth exponent, for a pair on the line. -/
def crossoverBranch (κ σ : ℚ) : ℚ := 2 * κ * (1 - σ)

/-- The critical block's contribution, for a pair on the line. -/
def criticalBranch (κ σ : ℚ) : ℚ := κ - (σ - 1 / 2) / 2

/-- **The two branches agree exactly on the critical line.** -/
@[simp] theorem branches_agree_at_half (κ : ℚ) :
    crossoverBranch κ (1 / 2) = criticalBranch κ (1 / 2) := by
  unfold crossoverBranch criticalBranch; ring

/-- Their difference factorises. -/
theorem branch_difference (κ σ : ℚ) :
    crossoverBranch κ σ - criticalBranch κ σ = (σ - 1 / 2) * (1 / 2 - 2 * κ) := by
  unfold crossoverBranch criticalBranch; ring

/-- **The crossover branch dominates exactly to the right of the critical line**, for every pair with
`κ < 1/4`. -/
theorem crossover_dominates_iff {κ σ : ℚ} (hκ : κ < 1 / 4) :
    criticalBranch κ σ ≤ crossoverBranch κ σ ↔ 1 / 2 ≤ σ := by
  rw [← sub_nonneg, branch_difference]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- The record pair satisfies the hypothesis. -/
theorem bourgainKappa_lt_quarter : bourgainKappa < 1 / 4 := by
  unfold bourgainKappa; norm_num

/-! ### The linear off-line profile of a record pair -/

/-- The growth profile a pair on the line of symmetry delivers for `σ ≥ 1/2`. -/
def linePairProfile (κ σ : ℚ) : ℚ := 2 * κ * (1 - σ)

/-- **At the critical line it returns the pair's own exponent.** -/
@[simp] theorem linePairProfile_at_half (κ : ℚ) : linePairProfile κ (1 / 2) = κ := by
  unfold linePairProfile; ring

/-- **At `σ = 1` it vanishes**, as the true growth exponent does. -/
@[simp] theorem linePairProfile_at_one (κ : ℚ) : linePairProfile κ 1 = 0 := by
  unfold linePairProfile; ring

/-- The profile is linear and decreasing. -/
theorem linePairProfile_antitone {κ σ σ' : ℚ} (hκ : 0 < κ) (h : σ < σ') :
    linePairProfile κ σ' < linePairProfile κ σ := by
  unfold linePairProfile; nlinarith

/-- **The record pair's prediction at `σ = 7/10` is `13/140`.** -/
@[simp] theorem linePairProfile_bourgain_seven_tenths :
    linePairProfile bourgainKappa (7 / 10) = 13 / 140 := by
  unfold linePairProfile bourgainKappa; norm_num

/-! ### The transfer returns nothing new from a pair's own profile -/

/-- The value the transfer produces from a pair's off-line profile at abscissa `σ`. -/
def transferOfProfile (κ σ : ℚ) : ℚ := linePairProfile κ σ + (σ - 1 / 2) / 2

/-- **It equals the pair's own critical exponent plus a nonnegative term.** -/
theorem transferOfProfile_eq (κ σ : ℚ) :
    transferOfProfile κ σ = κ + (σ - 1 / 2) * (1 / 2 - 2 * κ) := by
  unfold transferOfProfile linePairProfile; ring

/-- **The transfer of a pair's own profile is minimised at the critical line, where it returns the
pair's exponent.**  So no exponent pair's off-line bound improves on its own critical-line value. -/
theorem transfer_of_own_profile_useless {κ σ : ℚ} (hκ : κ < 1 / 4) (hσ : 1 / 2 ≤ σ) :
    κ ≤ transferOfProfile κ σ := by
  rw [transferOfProfile_eq]
  nlinarith

/-- At the critical line the transfer is exact. -/
@[simp] theorem transferOfProfile_at_half (κ : ℚ) : transferOfProfile κ (1 / 2) = κ := by
  rw [transferOfProfile_eq]; ring

/-- **For the record pair at `σ = 7/10` the transfer returns `13/140 + 1/10 = 27/140`**, worse than
`13/84` — the pair loses by going off the line and coming back. -/
theorem transfer_of_bourgain_profile :
    transferOfProfile bourgainKappa (7 / 10) = 27 / 140 ∧ bourgainTheta < 27 / 140 := by
  constructor
  · unfold transferOfProfile linePairProfile bourgainKappa; norm_num
  · unfold bourgainTheta; norm_num

/-! ### The ledger at `σ = 7/10` -/

/-- The exponent-pair prediction, published bound and record threshold at `σ = 7/10`, in
eight-hundred-fortieths. -/
theorem seven_tenths_ledger :
    linePairProfile bourgainKappa (7 / 10) = 78 / 840 ∧
      muSevenTenths = 63 / 840 ∧
      recordThresholdAtSevenTenths = 46 / 840 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [linePairProfile_bourgain_seven_tenths]; norm_num
  · unfold muSevenTenths; norm_num
  · unfold recordThresholdAtSevenTenths; norm_num

/-- **The published bound genuinely beats the exponent-pair prediction, by `1/56 = 15/840`.** -/
theorem published_beats_pair_prediction :
    linePairProfile bourgainKappa (7 / 10) - muSevenTenths = 1 / 56 := by
  rw [linePairProfile_bourgain_seven_tenths]
  unfold muSevenTenths; norm_num

/-- **But the remaining gap to the record threshold is `17/840`, larger than the gain already made.**
Closing it means roughly doubling the existing off-line advantage over the exponent pair. -/
theorem remaining_exceeds_gain :
    muSevenTenths - recordThresholdAtSevenTenths = 17 / 840 ∧
      linePairProfile bourgainKappa (7 / 10) - muSevenTenths = 15 / 840 ∧
      (15 : ℚ) / 840 < 17 / 840 := by
  refine ⟨seven_tenths_shortfall.2, ?_, by norm_num⟩
  rw [published_beats_pair_prediction]; norm_num

/-- The total available at `σ = 7/10`, from the exponent-pair prediction down to the record
threshold, is `32/840 = 4/105`. -/
theorem total_available_at_seven_tenths :
    linePairProfile bourgainKappa (7 / 10) - recordThresholdAtSevenTenths = 4 / 105 := by
  rw [linePairProfile_bourgain_seven_tenths]
  unfold recordThresholdAtSevenTenths; norm_num

end HTGeometry
