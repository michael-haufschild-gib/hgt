import GaloisForLFunctions.RHTower.BaezDuarteDetectorGram

/-!
# The Báez-Duarte distances, and the criterion in the form `d_N → 0 ⟹ RH`

`NymanBeurlingCriterion` states the criterion through membership in a topological closure.  The
literature states it through the *distances*

`d_N = dist( 1_{(0,1]} , span of the first N generators )`,

and asks whether `d_N → 0`.  This file supplies that form.  Everything is the metric bookkeeping around
`Metric.infDist`; the analytic content is entirely in the detector floor of `BaezDuarteL2Carrier`.

* `bdDist` — the distance from the target to the span of an arbitrary family of generators, and
  `bdDistFinset` for a finite section;
* `bdDist_le_one` — the distances live in `[0,1]`, since the target is a unit vector (`norm_bdTarget`) and
  `0` is in every span;
* `bdDistFinset_antitone` — a larger section is at least as good;
* `riemannHypothesis_of_bdDist_eq_zero` — **if the distance is zero the Riemann hypothesis holds**;
* `riemannHypothesis_of_tendsto_bdDistFinset` — **if the finite-section distances tend to `0`, the Riemann
  hypothesis holds.**  This is the criterion in the shape the literature uses, for an arbitrary family of
  dilations and an arbitrary exhausting sequence of finite sections;
* `bdDist_floor_of_zero` — the converse quantitative statement: at a zero of `ζ` with `½ < Re ρ < 1`, every
  such distance is at least `√(2Re ρ − 1)/|ρ|`, so the distances are bounded away from `0` and no
  approximation scheme can succeed.
-/

open MeasureTheory Set Complex Metric Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The span of a family of Báez-Duarte generators, as a set of the carrier. -/
def bdSpanSet {I : Type*} (θ : I → ℝ) : Set BDCarrier :=
  (Submodule.span ℂ (Set.range (fun i : I => bdGen (θ i))) : Submodule ℂ BDCarrier)

theorem zero_mem_bdSpanSet {I : Type*} (θ : I → ℝ) : (0 : BDCarrier) ∈ bdSpanSet θ :=
  Submodule.zero_mem _

theorem bdSpanSet_nonempty {I : Type*} (θ : I → ℝ) : (bdSpanSet θ).Nonempty :=
  ⟨0, zero_mem_bdSpanSet θ⟩

/-- **The Báez-Duarte distance** of a family of dilations. -/
def bdDist {I : Type*} (θ : I → ℝ) : ℝ := Metric.infDist bdTarget (bdSpanSet θ)

/-- The distance of a finite section. -/
def bdDistFinset {I : Type*} [DecidableEq I] (θ : I → ℝ) (s : Finset I) : ℝ :=
  bdDist (fun i : {x // x ∈ s} => θ i)

theorem bdDist_nonneg {I : Type*} (θ : I → ℝ) : 0 ≤ bdDist θ :=
  Metric.infDist_nonneg

/-- The distances live in `[0,1]`: the target is a unit vector and `0` is in every span. -/
theorem bdDist_le_one {I : Type*} (θ : I → ℝ) : bdDist θ ≤ 1 := by
  have h := Metric.infDist_le_dist_of_mem (x := bdTarget) (zero_mem_bdSpanSet θ)
  rw [dist_zero_right, norm_bdTarget] at h
  exact h

/-- Enlarging the family cannot increase the distance. -/
theorem bdDist_mono {I J : Type*} (θ : I → ℝ) (η : J → ℝ)
    (h : Set.range (fun i : I => bdGen (θ i)) ⊆ Set.range (fun j : J => bdGen (η j))) :
    bdDist η ≤ bdDist θ := by
  refine Metric.infDist_le_infDist_of_subset ?_ (bdSpanSet_nonempty θ)
  exact Submodule.span_mono h

/-- A larger finite section is at least as good. -/
theorem bdDistFinset_antitone {I : Type*} [DecidableEq I] (θ : I → ℝ) {s t : Finset I}
    (hst : s ⊆ t) : bdDistFinset θ t ≤ bdDistFinset θ s := by
  refine bdDist_mono _ _ ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i.1, hst i.2⟩, rfl⟩

/-! ## The criterion in distance form -/

/-- **If a Báez-Duarte distance vanishes, the Riemann hypothesis holds.** -/
theorem riemannHypothesis_of_bdDist_eq_zero {I : Type*} (θ : I → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (h : bdDist θ = 0) : RiemannHypothesis := by
  refine riemannHypothesis_of_bdTarget_mem_closedSpan_family θ hθ ?_
  have hmem : bdTarget ∈ closure (bdSpanSet θ) :=
    (Metric.mem_closure_iff_infDist_zero (bdSpanSet_nonempty θ)).mpr h
  rwa [bdSpanSet, ← Submodule.topologicalClosure_coe] at hmem

/-- **If the finite-section distances tend to zero, the Riemann hypothesis holds.**  This is the criterion
in the shape the literature uses.  The sections are an arbitrary sequence of finite subsets. -/
theorem riemannHypothesis_of_tendsto_bdDistFinset {I : Type*} [DecidableEq I] (θ : I → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (s : ℕ → Finset I)
    (hd : Tendsto (fun N => bdDistFinset θ (s N)) atTop (𝓝 0)) : RiemannHypothesis := by
  refine riemannHypothesis_of_bdDist_eq_zero θ hθ ?_
  have hle : ∀ N, bdDist θ ≤ bdDistFinset θ (s N) := by
    intro N
    refine bdDist_mono _ _ ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩
  have hub : bdDist θ ≤ 0 := by
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds hd ?_
    exact hle
  exact le_antisymm hub (bdDist_nonneg θ)

/-- The classical Báez-Duarte distances: the target against the span of the first `N` generators of the
discrete system `θ = 1/(n+1)`. -/
def bdDistDiscrete (N : ℕ) : ℝ := bdDistFinset bdDiscrete (Finset.range N)

theorem bdDistDiscrete_antitone {M N : ℕ} (h : M ≤ N) : bdDistDiscrete N ≤ bdDistDiscrete M :=
  bdDistFinset_antitone bdDiscrete (Finset.range_mono h)

theorem bdDistDiscrete_mem_Icc (N : ℕ) : 0 ≤ bdDistDiscrete N ∧ bdDistDiscrete N ≤ 1 :=
  ⟨bdDist_nonneg _, bdDist_le_one _⟩

/-- **`d_N → 0 ⟹ RH`.**  The Nyman--Beurling/Báez-Duarte criterion in its classical form: if the distances
from `1_{(0,1]}` to the spans of the first `N` functions `({u/n} − {u}/n)/u` tend to zero, the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_tendsto_bdDistDiscrete
    (hd : Tendsto bdDistDiscrete atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_tendsto_bdDistFinset bdDiscrete bdDiscrete_mem
    (fun N => Finset.range N) hd

/-! ## The floor in distance form -/

/-- **The quantitative obstruction.**  At a zero of `ζ` with `½ < Re ρ < 1` every Báez-Duarte distance is
at least `√(2Re ρ − 1)/|ρ|`. -/
theorem bdDist_floor_of_zero {I : Type*} (θ : I → ℝ) (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) (hzero : riemannZeta ρ = 0) :
    Real.sqrt (2 * ρ.re - 1) / ‖ρ‖ ≤ bdDist θ := by
  rw [bdDist, Metric.le_infDist (bdSpanSet_nonempty θ)]
  intro G hG
  rw [dist_eq_norm]
  refine bdTarget_dist_floor_of_mem_closedSpan_family θ hθ hρ hρ1 hzero ?_
  exact Submodule.le_topologicalClosure _ hG

/-- The floor for the classical discrete distances: if RH fails they are bounded away from `0`, uniformly
in `N`, so `d_N → 0` cannot hold. -/
theorem bdDistDiscrete_floor_of_zero {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) (N : ℕ) :
    Real.sqrt (2 * ρ.re - 1) / ‖ρ‖ ≤ bdDistDiscrete N :=
  bdDist_floor_of_zero _ (fun i => bdDiscrete_mem i.1) hρ hρ1 hzero

/-- The two halves together: vanishing distance forces the Riemann hypothesis, and its failure forces a
uniform positive floor on every distance. -/
theorem bdDist_dichotomy {I : Type*} (θ : I → ℝ) (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) :
    (bdDist θ = 0 → RiemannHypothesis) ∧
      (¬ RiemannHypothesis → ∃ c : ℝ, 0 < c ∧ c ≤ bdDist θ) := by
  refine ⟨riemannHypothesis_of_bdDist_eq_zero θ hθ, fun hRH => ?_⟩
  obtain ⟨ρ, hzero, hρ, hρ1⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ
    linarith
  refine ⟨Real.sqrt (2 * ρ.re - 1) / ‖ρ‖, ?_, bdDist_floor_of_zero θ hθ hρ hρ1 hzero⟩
  have h1 : (0 : ℝ) < 2 * ρ.re - 1 := by linarith
  exact div_pos (Real.sqrt_pos.mpr h1) (norm_pos_iff.mpr hρ0)

end RHTower

end
