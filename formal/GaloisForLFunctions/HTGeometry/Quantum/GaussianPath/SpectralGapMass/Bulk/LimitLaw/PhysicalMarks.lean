import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.LimitLaw.WeightedTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.LimitLaw.MarkedEntries

/-! # Limiting distribution of the closing speed at actual scalar entries -/
open MeasureTheory Filter Finset Set Real
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- Face labels whose angular endpoints approach faster than the prescribed
scaled energy gap. The Schrödinger phase velocities have the opposite sign
from the energies. -/
def fastPairs {n : ℕ} (u : PathShell n) (a : ℝ) :=
  univ.filter fun p : (Fin (n+2)→Bool)×(Fin (n+2)→Bool) => a < scaledGap u p.swap

private theorem swap_integral {n : ℕ} (u : PathShell n) (f : ℝ→ℝ) :
    (∫ x, f x ∂(listLaw (scaledGap u) : Measure ℝ)) =
      (Fintype.card ((Fin (n+2)→Bool)×(Fin (n+2)→Bool)):ℝ)⁻¹ *
        ∑ p, f (scaledGap u p.swap) := by
  rw [integral_listLaw]
  congr 1
  simp only [Fintype.sum_prod_type]
  rw [sum_comm]

private theorem fast_pair_ratio {n : ℕ} (u : PathShell n) {a : ℝ} (ha : 0 ≤ a) :
    let E := fun i => -(isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues i
    let μ := (listLaw (scaledGap u) : Measure ℝ)
    selectedRate E (fastPairs u a)/pairTurnRate E =
      (∫ x in Ioi a, x ∂μ)/(∫ x : ℝ, max 0 x ∂μ) := by
  classical
  intro E μ
  let I := Fin (n+2)→Bool
  let v := sqrt (n+2:ℕ)
  let w (p : I×I) := scaledGap u p.swap
  have hv : 0 < v := by dsimp only [v]; positivity
  have hK : v/(2*π) ≠ 0 := (div_pos hv (by positivity)).ne'
  have hD : (Fintype.card (I×I):ℝ)⁻¹ ≠ 0 := by positivity
  have hpair (p : I×I) : max 0 (E p.1-E p.2)/(2*π) = v/(2*π)*max 0 (w p) := by
    have he : E p.1-E p.2=v*w p := by
      dsimp only [E,v,w,scaledGap,scaledEnergy,Prod.swap]
      field_simp [hv.ne']
      ring
    rw [he]
    rcases le_total 0 (w p) with h|h
    · rw [max_eq_right (mul_nonneg hv.le h),max_eq_right h]; ring
    · rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hv.le h),max_eq_left h,mul_zero,zero_div]
  have hsel (p : I×I) : (if a < w p then max 0 (w p) else 0) =
      (Ioi a).indicator (fun x : ℝ => x) (w p) := by
    by_cases h : a < w p
    · rw [if_pos h,indicator_of_mem (show w p∈Ioi a from h),max_eq_right (ha.trans h.le)]
    · rw [if_neg h,indicator_of_notMem (show w p∉Ioi a from h)]
  rw [←integral_indicator measurableSet_Ioi]
  change _=(∫ x, (Ioi a).indicator (fun y : ℝ => y) x ∂(listLaw (scaledGap u) : Measure ℝ)) / _
  rw [swap_integral,show μ=(listLaw (scaledGap u) : Measure ℝ) from rfl,swap_integral,
    selectedRate,pairTurnRate]
  simp only [hpair,←mul_sum]
  change ((v/(2*π))*(∑ p ∈ univ.filter (fun p => a<w p), max 0 (w p))) / _ = _
  rw [sum_filter]
  simp only [hsel,mul_div_mul_left _ _ hK,mul_div_mul_left _ _ hD,w]

/-- Count distinct entries after the genuine first near-Hilbert crossing.
For every physical tolerance below √2 the fraction with closing speed
greater than a√N tends, in the long-record then large-chain limits, to
exp(−a²/48). -/
theorem gaussian_first_crossing_closing_gaps :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a ≥ (0:ℝ), ∃ F : ℕ→ℝ,
      Tendsto F atTop (𝓝 (exp (-(a^2/48)))) ∧ ∀ᶠ k : ℕ in atTop,
        let u := pathPauliDisorderShell ω (k+1)
        let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
        let P := nearHilbertContinuousCircuitBudget (k+3)
        let E := fun j => -H.2.isHermitian.eigenvalues j
        ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
          (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
          ∀ ε ∈ Ioo (0:ℝ) (sqrt 2), let r := physicalArc ε
            Tendsto (fun T : ℝ => (((selectedDates E (fastPairs u a) r T) \ (entryDates E r σ)).card:ℝ)/
              (entriesAfter E r σ T).card) atTop (𝓝 (F k)) := by
  filter_upwards [gaussian_size_biased_gap,gaussian_first_crossing_flux,
    gaussian_path_all_prefixes_maximally_projective] with ω hg hc hi
  intro a ha
  let F (k : ℕ) :=
    let μ := (listLaw (scaledGap (pathPauliDisorderShell ω (k+1))) : Measure ℝ)
    (∫ x in Ioi a, x ∂μ)/(∫ x : ℝ, max 0 x ∂μ)
  refine ⟨F,(hg a ha).comp (tendsto_add_atTop_nat 1),?_⟩
  filter_upwards [hc] with k hk
  intro u H P E
  obtain ⟨σ,hσ,he,hb,_⟩ := hk
  refine ⟨σ,hσ,he,hb,?_⟩
  intro ε hε r
  have hx := (physicalArc_spec hε.1 hε.2).1
  have hE : MaximallyProjectiveEnergy E := maximallyProjectiveEnergy_neg (hi k)
  have hh := selected_entry_fraction E hE (fastPairs u a) hx.1 hx.2 σ (pair_rate_pos E hE)
  exact (fast_pair_ratio u ha) ▸ hh

#print axioms gaussian_first_crossing_closing_gaps
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
