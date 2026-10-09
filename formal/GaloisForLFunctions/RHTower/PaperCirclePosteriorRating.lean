import GaloisForLFunctions.RHTower.PaperCircleAdaptiveHistory
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Procedure.Rare

/-! # Exponential rating and rare freezing for actual observation posteriors

Ten extra grid levels pay the source's separation between the stopping depth and
the ambient grid. Every native observation history then admits an adaptive road
with a paid exponential rating budget and a vanishing frozen-input probability.
The selected roads below are certified for all sufficiently large scales.
-/

open Filter
open scoped Topology BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- All source conditions are conclusions of this certificate for the native input. -/
structure PaperCircleHistoryRatingCertificate (a : ι → CCMCircleBoundedSymbol)
    (J k : ℕ) (s : List (ℝ≥0 × Grid (J+10))) (j : ℕ)
    (road : Road j (J+10) (paperCircleHistoryBegin a (J+10) k s)) : Prop where
  trusted : road.Trusted J (paperCircleHistoryLikelihood a (J+10) k s)
  terminal_mass : ∀ x : Grid (J+10), 0 < (road.hike x).done.mass
  exponential_rating : (paperCircleHistoryPosterior a (J+10) k s).Ex
    (fun x => Real.exp (Road.rating (paperCircleHistoryBegin a (J+10) k s)
      (road.hike x))) ≤ Thermal.H j * Real.exp (Compress.Params.height j)
  frozen : (paperCircleHistoryPosterior a (J+10) k s).prob
    (fun x => (road.hike x).froze = true) ≤ 1 / Thermal.H j^10

/-- Actual native data pay positivity, height, mass and grid-margin requirements. -/
theorem paperCircleHistory_rated_road_exists (a : ι → CCMCircleBoundedSymbol)
    (J k : ℕ) (s : List (ℝ≥0 × Grid (J+10))) :
    ∀ᶠ j : ℕ in atTop,
      ∃ road : Road j (J+10) (paperCircleHistoryBegin a (J+10) k s),
        PaperCircleHistoryRatingCertificate a J k s j road := by
  filter_upwards [plant, paperCircleHistoryBegin_mass_ready a (J+10) k s,
    Road.rating_bound, Road.rare] with j hp hm hscore hrare
  have hheight (x : Grid (J+10)) :
      paperCircleHistoryLikelihood a (J+10) k s x ≤
        Real.exp (Compress.Params.height j) :=
    (paperCircleHistoryLikelihood_le_one a (J+10) k s x).trans
      (Real.one_le_exp (Thermal.d_pos j).le)
  obtain ⟨play, hplay⟩ := hp (J+10) J (by omega)
    (paperCircleHistoryLikelihood a (J+10) k s)
    (fun x => (paperCircleHistoryLikelihood_pos a (J+10) k s x).le)
    ((paperCircleHistoryEvidence_le_one a (J+10) k s).trans (by norm_num)) hheight true
  let road := Road.trace false play
  have hr : road.Trusted J (paperCircleHistoryLikelihood a (J+10) k s) :=
    Road.traced play false hplay
  have hgrid : 1000 * (2:ℝ)^J ≤ 2^(J+10) := by
    rw [pow_add]
    have hpow : 0 ≤ (2:ℝ)^J := by positivity
    norm_num
    nlinarith
  have hs := hscore (J+10) J hgrid
    (paperCircleHistoryLikelihood a (J+10) k s) hheight road hr hm
  have hf := hrare (J+10) J hgrid
    (paperCircleHistoryLikelihood a (J+10) k s) hheight road hr hm
  have hactor := paperCircleHistoryBegin_actor a (J+10) k s
  refine ⟨road, {
    trusted := hr
    terminal_mass := ?_
    exponential_rating := ?_
    frozen := ?_ }⟩
  · intro x
    exact (Road.final_sound hr (paperCircleHistoryBegin_mass_pos a (J+10) k s)
      (show 0 < (paperCircleHistoryBegin a (J+10) k s).actor x by
        rw [hactor]
        exact paperCircleHistoryPosterior_pos a (J+10) k s x)).2.2.1
  · change (paperCircleHistoryBegin a (J+10) k s).actor.Ex
      (fun x => Real.exp (Road.rating (paperCircleHistoryBegin a (J+10) k s)
        (road.hike x))) ≤ _ at hs
    rw [hactor] at hs
    simpa only [paperCircleHistoryBegin] using hs
  · change (paperCircleHistoryBegin a (J+10) k s).actor.prob _ ≤ _ at hf
    rw [hactor] at hf
    simpa only [paperCircleHistoryBegin] using hf

/-- Choose a certified road whenever available; early scales have an inert fallback. -/
def paperCircleHistoryRatedRoad (a : ι → CCMCircleBoundedSymbol)
    (J k : ℕ) (s : List (ℝ≥0 × Grid (J+10))) (j : ℕ) :
    Road j (J+10) (paperCircleHistoryBegin a (J+10) k s) := by
  classical
  exact if h : ∃ road, PaperCircleHistoryRatingCertificate a J k s j road then
    Classical.choose h else Road.finish _ false

theorem paperCircleHistoryRatedRoad_certified (a : ι → CCMCircleBoundedSymbol)
    (J k : ℕ) (s : List (ℝ≥0 × Grid (J+10))) :
    ∀ᶠ j : ℕ in atTop, PaperCircleHistoryRatingCertificate a J k s j
      (paperCircleHistoryRatedRoad a J k s j) := by
  classical
  filter_upwards [paperCircleHistory_rated_road_exists a J k s] with j hj
  unfold paperCircleHistoryRatedRoad
  rw [dif_pos hj]
  exact Classical.choose_spec hj

/-- The native rating has an exponential upper tail after its explicit source offset. -/
theorem paperCircleHistoryRatedRoad_rating_tail (a : ι → CCMCircleBoundedSymbol)
    (J k : ℕ) (s : List (ℝ≥0 × Grid (J+10))) :
    ∀ᶠ j : ℕ in atTop, ∀ u : ℝ,
      (paperCircleHistoryPosterior a (J+10) k s).prob (fun x =>
        Compress.Params.height j + Real.log (Thermal.H j) + u ≤
          Road.rating (paperCircleHistoryBegin a (J+10) k s)
            ((paperCircleHistoryRatedRoad a J k s j).hike x)) ≤ Real.exp (-u) := by
  filter_upwards [paperCircleHistoryRatedRoad_certified a J k s] with j hj u
  let P := paperCircleHistoryPosterior a (J+10) k s
  let Y := fun x => Road.rating (paperCircleHistoryBegin a (J+10) k s)
    ((paperCircleHistoryRatedRoad a J k s j).hike x)
  let v := Compress.Params.height j + Real.log (Thermal.H j) + u
  have htail := P.upperTail (fun x => v ≤ Y x) (fun x => Real.exp (Y x))
    (fun x => (Real.exp_pos (Y x)).le) (Real.exp v)
    (fun x hx => Real.exp_le_exp.mpr hx)
  have h := htail.trans hj.exponential_rating
  have hid : Real.exp v * Real.exp (-u) =
      Thermal.H j * Real.exp (Compress.Params.height j) := by
    rw [← Real.exp_add]
    dsimp [v]
    rw [show Compress.Params.height j + Real.log (Thermal.H j) + u + -u =
      Compress.Params.height j + Real.log (Thermal.H j) by ring,
      Real.exp_add, Real.exp_log (Thermal.H_pos j), mul_comm]
  rw [← hid] at h
  exact le_of_mul_le_mul_left h (Real.exp_pos v)

theorem paperCircleHistoryRatedRoad_frozen_bound (a : ι → CCMCircleBoundedSymbol)
    (J k : ℕ) (s : List (ℝ≥0 × Grid (J+10))) :
    ∀ᶠ j : ℕ in atTop, (paperCircleHistoryPosterior a (J+10) k s).prob
      (fun x => ((paperCircleHistoryRatedRoad a J k s j).hike x).froze = true) ≤
        1 / Thermal.H j^10 := by
  filter_upwards [paperCircleHistoryRatedRoad_certified a J k s] with j hj
  exact hj.frozen

/-- At fixed native data, the frozen-input probability actually tends to zero. -/
theorem paperCircleHistoryRatedRoad_frozen_tendsto_zero (a : ι → CCMCircleBoundedSymbol)
    (J k : ℕ) (s : List (ℝ≥0 × Grid (J+10))) :
    Tendsto (fun j => (paperCircleHistoryPosterior a (J+10) k s).prob
      (fun x => ((paperCircleHistoryRatedRoad a J k s j).hike x).froze = true))
      atTop (𝓝 0) := by
  have hH : Tendsto Thermal.H atTop atTop := tendsto_atTop.mpr Thermal.h_large
  have hlim : Tendsto (fun j => 1 / Thermal.H j^10) atTop (𝓝 0) := by
    simpa only [div_pow, one_pow, zero_pow (by norm_num : 10 ≠ 0)] using
      ((hH.const_div_atTop 1).pow 10)
  exact squeeze_zero' (Eventually.of_forall fun j => Law.prob_nonneg _ _)
    (paperCircleHistoryRatedRoad_frozen_bound a J k s) hlim

/-- The probability of avoiding the static-transfer stop tends to one. -/
theorem paperCircleHistoryRatedRoad_unfrozen_tendsto_one (a : ι → CCMCircleBoundedSymbol)
    (J k : ℕ) (s : List (ℝ≥0 × Grid (J+10))) :
    Tendsto (fun j => (paperCircleHistoryPosterior a (J+10) k s).prob
      (fun x => ((paperCircleHistoryRatedRoad a J k s j).hike x).froze ≠ true))
      atTop (𝓝 1) := by
  simp only [Law.prob_compl]
  simpa only [sub_zero] using
    (tendsto_const_nhds.sub (paperCircleHistoryRatedRoad_frozen_tendsto_zero a J k s))

/-- Finiteness and positive native posterior mass strengthen rarity to no frozen inputs.
The threshold depends on the fixed grid and observation history. -/
theorem paperCircleHistoryRatedRoad_eventually_unfrozen (a : ι → CCMCircleBoundedSymbol)
    (J k : ℕ) (s : List (ℝ≥0 × Grid (J+10))) :
    ∀ᶠ j : ℕ in atTop, ∀ x : Grid (J+10),
      ((paperCircleHistoryRatedRoad a J k s j).hike x).froze = false := by
  apply eventually_all.mpr
  intro x
  have ht := Filter.Tendsto.eventually_lt_const
    (paperCircleHistoryPosterior_pos a (J+10) k s x)
    (paperCircleHistoryRatedRoad_frozen_tendsto_zero a J k s)
  filter_upwards [ht] with j hj
  cases hb : ((paperCircleHistoryRatedRoad a J k s j).hike x).froze with
  | false => rfl
  | true =>
    exact ((not_le.mpr hj)
      ((paperCircleHistoryPosterior a (J+10) k s).mem_le_prob hb)).elim

theorem paperCircleHistoryRatedRoad_frozen_eventually_zero (a : ι → CCMCircleBoundedSymbol)
    (J k : ℕ) (s : List (ℝ≥0 × Grid (J+10))) :
    ∀ᶠ j : ℕ in atTop, (paperCircleHistoryPosterior a (J+10) k s).prob
      (fun x => ((paperCircleHistoryRatedRoad a J k s j).hike x).froze = true) = 0 := by
  filter_upwards [paperCircleHistoryRatedRoad_eventually_unfrozen a J k s] with j hj
  simp [Law.prob_eq, hj]

end
end RHTower
