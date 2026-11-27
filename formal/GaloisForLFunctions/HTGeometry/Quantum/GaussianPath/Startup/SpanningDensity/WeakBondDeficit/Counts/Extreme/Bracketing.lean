import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.Extreme.FirstMoment
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.Relative.MovingGrid
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.PhysicalBonds

/-! # Almost-sure bracketing of the weakest surviving and removable bond -/
open Set Finset Filter MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BlockDilations.AdaptiveCuts
open private physical_counts from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.Counts.PhysicalBonds
noncomputable section

/-- A summable upper estimate on the expected number at one threshold
keeps all smaller prefixes empty. Logarithmic mean at another threshold
supplies a removable odd bond to every larger prefix. -/
theorem gaussian_extreme_brackets (M m : ℕ→ℕ) (h g : ℕ→ℝ)
    (hs : Summable fun j => (M j:ℝ)*bondLaw.real (weakBond (h j)))
    (hm : ∀ᶠ j : ℕ in atTop, 16*log j≤bondLaw.real (weakBond (g j))*(m j:ℝ)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      n+1≤M j → m j≤n/2 → let u := pathPauliDisorderShell ω n
        (weakEdges u (h j)).card=0 ∧ 0<(removable u (g j)).card := by
  let A (j : ℕ) := {ω | 0<boxCount ω 0 1 (M j) (h j)}
  let μ := pathPauliDisorderLaw
  letI : IsProbabilityMeasure μ := by dsimp only [μ,pathPauliDisorderLaw]; infer_instance
  have hsum : Summable fun j => μ.real (A j) := hs.of_norm_bounded fun j => by
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact any_weak_row_bound 0 1 (M j) one_pos (h j)
  have hrare : ∀ᵐ ω ∂μ, ∀ᶠ j : ℕ in atTop, ω∉A j := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top _ _)] using hsum.tsum_ofReal_ne_top
  have hgood := gaussian_relative_box_grid 1 2 (by decide) m (fun j _ => g j)
  filter_upwards [hrare,hgood] with ω hw hx
  filter_upwards [hw,hx,hm,eventually_gt_atTop (1:ℕ)] with j hr hg hM hj
  intro n hn hn' u
  have hz : boxCount ω 0 1 (M j) (h j)=0 := Nat.eq_zero_of_not_pos hr
  have hpos := (hg ⟨0,by omega⟩ hM).1
  have hm₀ : 0≤bondLaw.real (weakBond (g j))*(m j:ℝ)/4 := by positivity
  have hlarge : 0<boxCount ω 1 2 (m j) (g j) := by exact_mod_cast hm₀.trans_lt hpos
  have hlow := boxCount_mono_length ω 0 1 hn (h j)
  have hhigh := boxCount_mono_length ω 1 2 hn' (g j)
  rw [hz] at hlow
  exact ⟨(physical_counts ω n (h j)).1.trans (Nat.eq_zero_of_le_zero hlow),
    hlarge.trans_le (hhigh.trans_eq (physical_counts ω n (g j)).2.symm)⟩

#print axioms gaussian_extreme_brackets
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
