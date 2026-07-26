/-
The covering geometry of a three-source subconvexity endgame, and its floor.

A subconvexity endgame supplies several bounds `A ≤ M^α · T^β`, each valid on its own range of
lengths `M`, and asks for the single target `A ≤ M^(1/2) · T^θ`.  Writing `M = T^x`, a source of
shape `(α, β)` with `α > 1/2` implies the target exactly on

    x ≤ (θ - β) / (α - 1/2) =: reach(α, β, θ),

a half-line whose right endpoint grows with `θ`.  Equivalently, the source reaches a prescribed
length `x₀` precisely when

    θ ≥ β + (α - 1/2)·x₀ =: demand(α, β, x₀).

A chain of sources therefore covers the whole conductor range iff each source's reach passes the
next source's starting point, and the target exponent must satisfy the *maximum* of the resulting
demands.  That maximum is the floor of the architecture: no improvement of the final source can push
the record below it.

The three inputs of Bourgain's global endgame are

    exponent pair `(1/9, 13/18)` :  A ≤ M^(11/18) T^(1/9)          all M
    Huxley                       :  A ≤ M^(103/128) T^(1/32)       M > T^(12/31)
    decoupling                   :  A ≤ M^(1/2) T^(13/84)          M ≥ T^(17/42)

The third has slope exactly `1/2`, so it is the target itself and covers its entire range of
validity; the first two must cover everything below `T^(17/42)`.  Their reaches at `θ = 13/84` are
`11/28` and `332/819`, and the two junction overlaps are

    11/28 - 12/31 = 5/868 ,      332/819 - 17/42 = 1/1638 .

The binding demand is Huxley's, `demand(103/128, 1/32, 17/42) = 277/1792`, and the published record
exceeds it by exactly `1/5376`.  Since `277/1792` also exceeds the internal spacing floor `11/72`, it
is the floor of the whole architecture.
-/
import GaloisForLFunctions.HTGeometry.SpacingWindowGeometry

namespace HTGeometry

/-! ### Reach and demand -/

/-- The largest length exponent at which a source of shape `(α, β)` implies the target
`M^(1/2) T^θ`. -/
def coveringReach (α β θ : ℚ) : ℚ := (θ - β) / (α - 1 / 2)

/-- The smallest target exponent for which a source of shape `(α, β)` still reaches `x₀`. -/
def coveringDemand (α β x₀ : ℚ) : ℚ := β + (α - 1 / 2) * x₀

/-- **Reach and demand are inverse to each other.**  A source reaches `x₀` exactly when the target
exponent meets its demand. -/
theorem reach_ge_iff_demand_le {α β θ x₀ : ℚ} (hα : 1 / 2 < α) :
    x₀ ≤ coveringReach α β θ ↔ coveringDemand α β x₀ ≤ θ := by
  have hpos : 0 < α - 1 / 2 := by linarith
  unfold coveringReach coveringDemand
  rw [le_div_iff₀ hpos]
  constructor <;> intro h <;> linarith

/-- The reach is monotone in the target exponent. -/
theorem coveringReach_mono {α β θ θ' : ℚ} (hα : 1 / 2 < α) (h : θ ≤ θ') :
    coveringReach α β θ ≤ coveringReach α β θ' := by
  have hpos : 0 < α - 1 / 2 := by linarith
  unfold coveringReach
  gcongr

/-! ### The three published inputs -/

/-- The `M`-exponent of the exponent-pair bound `A ≤ M^(11/18) T^(1/9)`. -/
def expPairAlpha : ℚ := 11 / 18

/-- Its `T`-exponent. -/
def expPairBeta : ℚ := 1 / 9

/-- The `M`-exponent of Huxley's bound `A ≤ M^(103/128) T^(1/32)`. -/
def huxleyAlpha : ℚ := 103 / 128

/-- Its `T`-exponent. -/
def huxleyBeta : ℚ := 1 / 32

/-- The length above which Huxley's bound is available. -/
def huxleyStart : ℚ := 12 / 31

/-- The length above which the decoupling bound is available. -/
def decouplingStart : ℚ := 17 / 42

theorem expPairAlpha_gt_half : (1 / 2 : ℚ) < expPairAlpha := by
  unfold expPairAlpha; norm_num

theorem huxleyAlpha_gt_half : (1 / 2 : ℚ) < huxleyAlpha := by
  unfold huxleyAlpha; norm_num

/-! ### The reaches at the record, and the two junction overlaps -/

/-- **The exponent-pair bound reaches `T^(11/28)`.** -/
@[simp] theorem expPair_reach :
    coveringReach expPairAlpha expPairBeta bourgainTheta = 11 / 28 := by
  unfold coveringReach expPairAlpha expPairBeta bourgainTheta; norm_num

/-- **Huxley's bound reaches `T^(332/819)`.** -/
@[simp] theorem huxley_reach :
    coveringReach huxleyAlpha huxleyBeta bourgainTheta = 332 / 819 := by
  unfold coveringReach huxleyAlpha huxleyBeta bourgainTheta; norm_num

/-- The first junction overlaps by `5/868`. -/
theorem first_junction_overlap :
    coveringReach expPairAlpha expPairBeta bourgainTheta - huxleyStart = 5 / 868 := by
  rw [expPair_reach]; unfold huxleyStart; norm_num

/-- **The second junction overlaps by only `1/1638`.** -/
theorem second_junction_overlap :
    coveringReach huxleyAlpha huxleyBeta bourgainTheta - decouplingStart = 1 / 1638 := by
  rw [huxley_reach]; unfold decouplingStart; norm_num

/-- The second junction is the tighter of the two. -/
theorem second_junction_is_tighter :
    coveringReach huxleyAlpha huxleyBeta bourgainTheta - decouplingStart
      < coveringReach expPairAlpha expPairBeta bourgainTheta - huxleyStart := by
  rw [first_junction_overlap, second_junction_overlap]; norm_num

/-! ### The two demands, and the floor -/

/-- The exponent the exponent-pair bound demands in order to reach Huxley's starting point. -/
def expPairDemand : ℚ := coveringDemand expPairAlpha expPairBeta huxleyStart

/-- The exponent Huxley's bound demands in order to reach the decoupling starting point. -/
def huxleyDemand : ℚ := coveringDemand huxleyAlpha huxleyBeta decouplingStart

@[simp] theorem expPairDemand_eq : expPairDemand = 43 / 279 := by
  unfold expPairDemand coveringDemand expPairAlpha expPairBeta huxleyStart; norm_num

/-- **Huxley's demand is `277/1792`.** -/
@[simp] theorem huxleyDemand_eq : huxleyDemand = 277 / 1792 := by
  unfold huxleyDemand coveringDemand huxleyAlpha huxleyBeta decouplingStart; norm_num

/-- **Huxley's demand dominates.** -/
theorem huxley_demand_dominates : expPairDemand < huxleyDemand := by
  rw [expPairDemand_eq, huxleyDemand_eq]; norm_num

/-- The floor of the three-source covering architecture. -/
def sectionFourFloor : ℚ := max expPairDemand huxleyDemand

@[simp] theorem sectionFourFloor_eq : sectionFourFloor = 277 / 1792 := by
  unfold sectionFourFloor
  rw [max_eq_right huxley_demand_dominates.le, huxleyDemand_eq]

/-- **The covering succeeds at a target exponent exactly when both demands are met.** -/
theorem covering_succeeds_iff (θ : ℚ) :
    (huxleyStart ≤ coveringReach expPairAlpha expPairBeta θ ∧
      decouplingStart ≤ coveringReach huxleyAlpha huxleyBeta θ)
      ↔ sectionFourFloor ≤ θ := by
  rw [reach_ge_iff_demand_le expPairAlpha_gt_half,
    reach_ge_iff_demand_le huxleyAlpha_gt_half]
  constructor
  · rintro ⟨h1, h2⟩
    unfold sectionFourFloor expPairDemand huxleyDemand
    exact max_le h1 h2
  · intro h
    unfold sectionFourFloor expPairDemand huxleyDemand at h
    exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

/-- **The record is exactly `1/5376` above the floor of its own architecture.** -/
theorem record_room_above_sectionFourFloor :
    bourgainTheta - sectionFourFloor = 1 / 5376 := by
  rw [sectionFourFloor_eq]; unfold bourgainTheta; norm_num

theorem sectionFourFloor_lt_record : sectionFourFloor < bourgainTheta := by
  rw [sectionFourFloor_eq]; unfold bourgainTheta; norm_num

/-- **The global covering floor dominates the internal spacing floor.**  The binding constraint on
the whole proof is not how well the decoupling estimate performs, but how far Huxley's bound reaches
into the range below the decoupling estimate's threshold. -/
theorem covering_floor_dominates_spacing_floor :
    spacingCoverageFloor bourgainB bourgainC < sectionFourFloor := by
  rw [sectionFourFloor_eq, bourgain_coverage_floor]; norm_num

/-- Consequently the architectural floor of the whole endgame is `277/1792`. -/
theorem architectural_floor_eq :
    max (spacingCoverageFloor bourgainB bourgainC) sectionFourFloor = 277 / 1792 := by
  rw [max_eq_right covering_floor_dominates_spacing_floor.le, sectionFourFloor_eq]

/-! ### What lowering the decoupling threshold would buy

The floor depends on the decoupling estimate only through the length `x₀` above which it is
available.  Lowering that threshold lowers the floor at the exact linear rate `39/128`. -/

/-- The floor as a function of the decoupling estimate's threshold. -/
def floorOfThreshold (x₀ : ℚ) : ℚ := max expPairDemand (coveringDemand huxleyAlpha huxleyBeta x₀)

/-- **Every unit lowered from the decoupling threshold lowers Huxley's demand by `39/128`.** -/
theorem demand_rate (x₀ x₁ : ℚ) :
    coveringDemand huxleyAlpha huxleyBeta x₀ - coveringDemand huxleyAlpha huxleyBeta x₁
      = (39 / 128) * (x₀ - x₁) := by
  unfold coveringDemand huxleyAlpha; ring

/-- The decoupling threshold at which Huxley's demand would drop to the exponent-pair demand: below
this, lowering the threshold further buys nothing. -/
def thresholdOfEqualDemands : ℚ := 4388 / 10881

/-- At that threshold the two demands coincide. -/
theorem demands_equal_at_threshold :
    coveringDemand huxleyAlpha huxleyBeta thresholdOfEqualDemands = expPairDemand := by
  unfold coveringDemand huxleyAlpha huxleyBeta thresholdOfEqualDemands
  rw [expPairDemand_eq]; norm_num

/-- **Below that threshold the exponent-pair bound alone caps the architecture at `43/279`.**  Even a
decoupling estimate available for arbitrarily short polynomials cannot push the covering floor below
the exponent pair's own demand. -/
theorem floor_bounded_below_by_expPair (x₀ : ℚ) : expPairDemand ≤ floorOfThreshold x₀ :=
  le_max_left _ _

/-- **The hardest limit of the published architecture.**  No improvement of the decoupling estimate —
neither in its exponent nor in its threshold — can bring the record below `43/279`, and with the
published threshold `17/42` the limit is `277/1792`. -/
theorem architecture_hard_floor :
    expPairDemand = 43 / 279 ∧
      floorOfThreshold decouplingStart = 277 / 1792 ∧
      (43 : ℚ) / 279 < 277 / 1792 ∧ (277 : ℚ) / 1792 < bourgainTheta := by
  refine ⟨expPairDemand_eq, ?_, by norm_num, ?_⟩
  · unfold floorOfThreshold
    rw [show coveringDemand huxleyAlpha huxleyBeta decouplingStart = huxleyDemand from rfl,
      huxleyDemand_eq, expPairDemand_eq]
    rw [max_eq_right (by norm_num : (43 : ℚ) / 279 ≤ 277 / 1792)]
  · unfold bourgainTheta; norm_num

end HTGeometry
