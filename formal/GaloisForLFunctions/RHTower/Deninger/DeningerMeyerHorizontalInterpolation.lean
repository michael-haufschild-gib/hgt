import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStripSeries

/-! # Arbitrary full germs on a horizontally escaping divisor

The denominator, rather than the Xi divisor, supplies the interpolation
geometry. No node separation, bound on multiplicities, bound on target jets,
or unproved infinite-source admission is required.
-/

open Complex Filter Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

theorem exists_deningerMeyerHorizontalInterpolation {ι : Type*} [Countable ι]
    {D : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hB : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖D z‖ ≤ C)
    {w : ι → ℂ} (hw : Function.Injective w) (m : ι → ℕ)
    (hm : ∀ i, analyticOrderAt D (w i) = (m i : ℕ∞))
    (hesc : Tendsto (fun i => |(w i).re|) cofinite atTop)
    (f : ι → ℂ → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) (w i)) :
    ∃ H : ℂ → ℂ, DeningerEntireMellinRegular H ∧
      ∀ i, (m i : ℕ∞) ≤ analyticOrderAt (fun z => H z-f i z) (w i) := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat ι
  let u : ι → ℝ := fun i => (1/2 : ℝ)^e i
  have hu : Summable u :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective he
  have hu₀ : ∀ i, 0 < u i := fun i => by positivity
  choose F hF hFgerm hFother using fun i =>
    exists_deningerMeyerStripCardinal hD hB (hm i) (hf i)
  choose T hT hTgerm hTorder hTsmall using fun i =>
    exists_deningerMeyerStripSmallCarrier (hF i) (w i) (m i) ⌊|(w i).re|⌋₊
      (r := |(w i).re|-1) (by linarith) (hu₀ i)
  have hb : ∀ (r : ℝ) (K : ℕ), ∀ᶠ i in cofinite, ∀ z : ℂ, |z.re| ≤ r →
      ‖T i z‖*(1+z.im^2)^K ≤ u i := by
    intro r K
    filter_upwards [hesc.eventually_ge_atTop (max (r+1) (K : ℝ))] with i hi z hz
    have hr : r ≤ |(w i).re|-1 := by linarith [le_max_left (r+1) (K : ℝ)]
    have hK : K ≤ ⌊|(w i).re|⌋₊ :=
      Nat.le_floor ((le_max_right (r+1) (K : ℝ)).trans hi)
    calc ‖T i z‖*(1+z.im^2)^K
        ≤ ‖T i z‖*(1+z.im^2)^⌊|(w i).re|⌋₊ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by nlinarith [sq_nonneg z.im]) hK)
            (norm_nonneg _)
      _ ≤ u i := hTsmall i z (hz.trans hr)
  have hreg := deningerMeyerStripSeries_regular hT hu hb
  have hloc := deningerMeyerStripSeries_locallyUniform hu (fun r => by simpa using hb r 0)
  refine ⟨fun z => ∑' i, T i z, hreg, fun j => ?_⟩
  apply deningerMeyerStripSeries_germ (fun i => (hT i).differentiable)
    hreg.differentiable hloc j (hf j)
  · have heq : (fun z => T j z-f j z) =
        (fun z => T j z-F j z)+(fun z => F j z-f j z) := by funext z; simp
    rw [heq]
    exact (le_min (hTgerm j) (hFgerm j)).trans le_analyticOrderAt_add
  · intro i hij
    have hne : w j ≠ w i := fun h => hij (hw h).symm
    rw [← hm j]
    exact (hFother i (w j) hne).trans (hTorder i (w j))

end
end RHTower
