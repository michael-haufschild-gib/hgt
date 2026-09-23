/-
# The quantitative transversality dephasing bound

Assembling the two halves of the transversality estimate: on the discarded region the unit total
coefficient mass makes the cost one copy of its measure, and on the good region each term obeys a
nonstationary-phase bound whose constants sum against an *aggregate* derivative budget rather than
being multiplied by the number of terms.  The remainder decays like `1/|t|`, so the deviation from
the diagonal terms is asymptotically at most the transversality tail.

Main results:
* `sum_good_bound_le` — per-term bounds sum against an aggregate budget.
* `norm_integral_sub_diagonal_le_transversalityTail` — **the dephasing bound**: the deviation is at
  most the tail plus `B|t|⁻¹(g⁻¹ + g⁻²)`.
* `tendsto_transversality_remainder` — the remainder vanishes as `|t| → ∞`.
-/
import GaloisForLFunctions.HTGeometry.AggregatedOscillatoryMass

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Per-term nonstationary-phase bounds sum against an aggregate derivative budget. -/
theorem sum_good_bound_le {s : Finset ι} {A : ι → ℝ} {b : ι → ℝ} {B t g : ℝ} (hg : 0 < g)
    (hb : ∀ j ∈ s, b j ≤ (A j / |t|) * (1 / g + 1 / g ^ (2 : ℕ)))
    (hA : ∑ j ∈ s, A j ≤ B) :
    ∑ j ∈ s, b j ≤ (B / |t|) * (1 / g + 1 / g ^ (2 : ℕ)) := by
  have h1 : 0 < 1 / g := one_div_pos.mpr hg
  have h2 : 0 < 1 / g ^ (2 : ℕ) := one_div_pos.mpr (pow_pos hg 2)
  have hc : 0 ≤ (1 / g + 1 / g ^ (2 : ℕ)) / |t| := div_nonneg (by linarith) (abs_nonneg t)
  calc ∑ j ∈ s, b j ≤ ∑ j ∈ s, (A j / |t|) * (1 / g + 1 / g ^ (2 : ℕ)) := Finset.sum_le_sum hb
    _ = (∑ j ∈ s, A j) * ((1 / g + 1 / g ^ (2 : ℕ)) / |t|) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ B * ((1 / g + 1 / g ^ (2 : ℕ)) / |t|) := mul_le_mul_of_nonneg_right hA hc
    _ = (B / |t|) * (1 / g + 1 / g ^ (2 : ℕ)) := by ring

/-- **The quantitative transversality dephasing bound.**  A finite oscillatory family whose total
absolute coefficient mass on the discarded region is at most one, and whose good-region terms obey
nonstationary-phase bounds with an aggregate derivative budget `B`, deviates from its
zero-phase terms by at most the transversality tail plus `B|t|⁻¹(g⁻¹ + g⁻²)`. -/
theorem norm_integral_sub_diagonal_le_transversalityTail [DecidableEq ι]
    (a : ι → X → ℂ) (φ : ι → X → ℝ) (t : ℝ) (Dset : Finset ι) {E : Set X}
    (hmeas : MeasurableSet E)
    (hzero : ∀ j ∈ Dset, ∀ x, φ j x = 0)
    (hint : ∀ j, Integrable (fun x => a j x * oscFactor t (φ j) x) μ)
    (hmass : ∀ x ∈ E, ∑ j, ‖a j x‖ ≤ 1) (hfin : μ E ≠ ⊤)
    {A : ι → ℝ} {B g Q : ℝ} (hg : 0 < g)
    (hgood : ∀ j, ‖∫ x in Eᶜ, a j x * oscFactor t (φ j) x ∂μ‖
      ≤ (A j / |t|) * (1 / g + 1 / g ^ (2 : ℕ)))
    (hA : ∑ j ∈ Finset.univ \ Dset, A j ≤ B)
    (hQ : μ.real E ≤ Q) :
    ‖(∫ x, ∑ j, a j x * oscFactor t (φ j) x ∂μ) - ∑ j ∈ Dset, ∫ x, a j x ∂μ‖
      ≤ Q + (B / |t|) * (1 / g + 1 / g ^ (2 : ℕ)) := by
  classical
  have hmain := norm_integral_sub_diagonal_le_measureReal_add a φ t Dset hmeas hzero hint hmass
    hfin (fun j => (A j / |t|) * (1 / g + 1 / g ^ (2 : ℕ))) hgood
  have hsum : ∑ j ∈ Finset.univ \ Dset, (A j / |t|) * (1 / g + 1 / g ^ (2 : ℕ))
      ≤ (B / |t|) * (1 / g + 1 / g ^ (2 : ℕ)) :=
    sum_good_bound_le hg (fun j _ => le_refl _) hA
  linarith [hmain, hsum, hQ]

/-- The nonstationary-phase remainder vanishes at large frequency. -/
theorem tendsto_transversality_remainder (B g : ℝ) :
    Tendsto (fun t : ℝ => (B / |t|) * (1 / g + 1 / g ^ (2 : ℕ))) (cocompact ℝ) (nhds 0) := by
  have habs : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
    exact ⟨tendsto_abs_atBot_atTop, tendsto_abs_atTop_atTop⟩
  have hdiv : Tendsto (fun t : ℝ => B / |t|) (cocompact ℝ) (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds habs
  have hres : Tendsto (fun t : ℝ => (B / |t|) * (1 / g + 1 / g ^ (2 : ℕ))) (cocompact ℝ)
      (nhds (0 * (1 / g + 1 / g ^ (2 : ℕ)))) := hdiv.mul_const _
  rwa [zero_mul] at hres

end

end GaloisForLFunctions.HTGeometry
