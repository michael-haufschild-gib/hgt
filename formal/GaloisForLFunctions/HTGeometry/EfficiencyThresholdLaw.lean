/-
The efficiency law: which lengths a given exponent pair beats the record at.

By the length-reflection factorisation, a pair's demand is `μ(κ,λ) + d(κ,λ)·(x - 1/2)`.  Comparing it
with a fixed target `θ` — in practice the current record — gives, for a pair strictly above the line
of symmetry,

    demand(κ, λ, x) < θ   ⟺   x  <  1/2 - (μ(κ,λ) - θ) / d(κ,λ).

The subtracted quantity is the reciprocal of the pair's **efficiency**

    η(κ, λ) := d(κ, λ) / (μ(κ, λ) - θ),

the displacement it buys per unit of pointwise excess over the target.  So each pair beats the record
on an initial segment of lengths whose right endpoint is `1/2 - 1/η`, and a pair is useful at longer
lengths exactly in proportion to how cheaply it buys displacement.

Applied to the `A`-images of the last two record pairs, with `θ = 13/84`:

    A(13/84, 55/84) = (13/194, 76/97)   :  μ = 17/97,   d = 21/97,    η = 1764/167,  threshold 715/1764
    A(32/205, 269/410) = (16/237, 743/948) : μ = 111/632, d = 205/948, η = 2870/277,  threshold 579/1435

These are exactly the two thresholds found separately: the length at which the `A`-process stops
improving Bourgain's pair, and the length at which the covering-optimal pre-Bourgain pair switches.
Their proximity is the statement that the `A`-process has nearly the same efficiency at the last two
record pairs — `10.5629` against `10.3610`, a difference under two percent.
-/
import GaloisForLFunctions.HTGeometry.SupportFunctionMaximalAtCritical

namespace HTGeometry

/-! ### The law -/

/-- The efficiency of a pair against a target: displacement bought per unit of pointwise excess. -/
def epEfficiency (κ lam θ : ℚ) : ℚ := epDisplacement κ lam / (epMu κ lam - θ)

/-- The largest length at which a pair still beats the target. -/
def efficiencyThreshold (κ lam θ : ℚ) : ℚ := 1 / 2 - (epMu κ lam - θ) / epDisplacement κ lam

/-- **The efficiency law.**  A pair above the line of symmetry beats a target exactly on the lengths
below its efficiency threshold. -/
theorem beats_target_iff_below_threshold {κ lam θ x : ℚ} (hd : 0 < epDisplacement κ lam) :
    covDemandOfPair x κ lam < θ ↔ x < efficiencyThreshold κ lam θ := by
  have hiff : x < efficiencyThreshold κ lam θ ↔
      epMu κ lam - θ < (1 / 2 - x) * epDisplacement κ lam := by
    unfold efficiencyThreshold
    rw [lt_sub_comm, div_lt_iff₀ hd]
  rw [hiff, covDemand_factorisation]
  constructor <;> intro h <;> nlinarith

/-- The threshold and the efficiency are reciprocal: `threshold = 1/2 - 1/η`. -/
theorem threshold_eq_half_sub_inv_efficiency (κ lam θ : ℚ) :
    efficiencyThreshold κ lam θ = 1 / 2 - (epEfficiency κ lam θ)⁻¹ := by
  unfold efficiencyThreshold epEfficiency
  rw [inv_div]

/-- A pair with no excess over the target and positive displacement beats it at every length below
the critical one; its threshold is exactly the critical length. -/
theorem threshold_at_critical_of_no_excess {κ lam θ : ℚ} (hexc : epMu κ lam = θ) :
    efficiencyThreshold κ lam θ = 1 / 2 := by
  unfold efficiencyThreshold; rw [hexc]; simp

/-- The threshold is below the critical length exactly when the pair has positive excess. -/
theorem threshold_lt_critical_iff {κ lam θ : ℚ} (hd : 0 < epDisplacement κ lam) :
    efficiencyThreshold κ lam θ < 1 / 2 ↔ θ < epMu κ lam := by
  unfold efficiencyThreshold
  rw [sub_lt_self_iff, div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · linarith
  · intro h; exact Or.inl ⟨by linarith, hd⟩

/-! ### The two published thresholds are instances -/

/-- Excess and displacement of the `A`-image of Bourgain's pair against the record. -/
theorem procA_bourgain_excess :
    epMu (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda) - bourgainTheta
      = 167 / 8148 := by
  rw [procA_bourgain_mu]; unfold bourgainTheta; norm_num

/-- Its efficiency is `1764/167`. -/
theorem procA_bourgain_efficiency :
    epEfficiency (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda) bourgainTheta
      = 1764 / 167 := by
  unfold epEfficiency
  rw [procA_bourgain_displacement, procA_bourgain_excess]
  norm_num

/-- **And its efficiency threshold is exactly the productivity threshold `715/1764`.** -/
theorem procA_bourgain_threshold :
    efficiencyThreshold (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        bourgainTheta = bourgainAThreshold := by
  unfold efficiencyThreshold bourgainAThreshold
  rw [procA_bourgain_displacement, procA_bourgain_excess]
  norm_num

/-- Excess of the `A`-image of Huxley's pair against the record. -/
theorem procA_huxleyPair_excess :
    epMu (procA_fst huxleyPairKappa) (procA_snd huxleyPairKappa huxleyPairLambda) - bourgainTheta
      = 277 / 13272 := by
  rw [procA_huxleyPair_data.1]; unfold bourgainTheta; norm_num

/-- Its efficiency is `2870/277`. -/
theorem procA_huxleyPair_efficiency :
    epEfficiency (procA_fst huxleyPairKappa) (procA_snd huxleyPairKappa huxleyPairLambda)
        bourgainTheta = 2870 / 277 := by
  unfold epEfficiency
  rw [procA_huxleyPair_data.2, procA_huxleyPair_excess]
  norm_num

/-- **And its efficiency threshold is exactly the optimal-pair switch `579/1435`.** -/
theorem procA_huxleyPair_threshold :
    efficiencyThreshold (procA_fst huxleyPairKappa) (procA_snd huxleyPairKappa huxleyPairLambda)
        bourgainTheta = optimalPairSwitch := by
  unfold efficiencyThreshold optimalPairSwitch
  rw [procA_huxleyPair_data.2, procA_huxleyPair_excess]
  norm_num

/-- **The cluster of Theorem 111 explained.**  The two thresholds are reciprocal efficiencies, and the
two efficiencies differ by less than two percent. -/
theorem efficiency_cluster :
    epEfficiency (procA_fst huxleyPairKappa) (procA_snd huxleyPairKappa huxleyPairLambda)
        bourgainTheta
      < epEfficiency (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        bourgainTheta ∧
    epEfficiency (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda) bourgainTheta
      - epEfficiency (procA_fst huxleyPairKappa) (procA_snd huxleyPairKappa huxleyPairLambda)
        bourgainTheta < 21 / 100 := by
  rw [procA_bourgain_efficiency, procA_huxleyPair_efficiency]
  constructor <;> norm_num

/-- Both efficiencies lie between `10.3` and `10.6`. -/
theorem efficiencies_bracketed :
    (103 : ℚ) / 10 < epEfficiency (procA_fst huxleyPairKappa)
        (procA_snd huxleyPairKappa huxleyPairLambda) bourgainTheta ∧
      epEfficiency (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        bourgainTheta < 106 / 10 := by
  rw [procA_bourgain_efficiency, procA_huxleyPair_efficiency]
  constructor <;> norm_num

/-! ### What infinite efficiency would and would not give -/

/-- **A pair with zero excess and positive displacement pushes its threshold to the critical length
but does not lower the record.**  Infinite efficiency shapes the profile below `1/2`; it does not
change `h(1/2)`. -/
theorem infinite_efficiency_does_not_lower_record {κ lam θ : ℚ}
    (hexc : epMu κ lam = θ) :
    efficiencyThreshold κ lam θ = 1 / 2 ∧ covDemandOfPair (1 / 2) κ lam = θ := by
  refine ⟨threshold_at_critical_of_no_excess hexc, ?_⟩
  rw [displacement_free_at_critical_length, hexc]

/-- **The record is unreachable from below by any efficiency argument.**  No matter how efficient a
pair is, at the critical length its demand is its own `μ`, which is at least the record. -/
theorem efficiency_cannot_beat_record_at_critical {κ lam θ : ℚ} (hmu : θ ≤ epMu κ lam) :
    θ ≤ covDemandOfPair (1 / 2) κ lam := by
  rw [displacement_free_at_critical_length]; exact hmu

end HTGeometry
