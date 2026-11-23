import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.ThreeGateWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.FirstThreeDate

/-! # Sharp scale of the first three-gate date after extensive spectral cost -/
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

/-- The first three-gate date after inverse-size onset has order
N⁻¹ᐟ² on one frozen chain. The spectator floor gives the lower bound.
If the upper bound fails, even half that date admits three gates. -/
theorem gaussian_first_three_scale :
    ∃ A c C : ℝ, 0<A ∧ 0<c ∧ 0<C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      (n+2:ℕ)*(firstThreeDate A ω n)^2 ∈ Icc c C := by
  obtain ⟨A,B,hA,hB,h⟩ := gaussian_first_three_date
  obtain ⟨M,hM,hw⟩ := gaussian_inverse_root_three_window
  refine ⟨A,1/B,4*M,hA,by positivity,by positivity,?_⟩
  filter_upwards [h,hw] with ω hω hv
  filter_upwards [hω.1.eventually_lt_const zero_lt_one,hω.2.1,
    hω.2.2.eventually (eventually_ge_atTop (2*A)),hv 1] with n hu hl hlate hn
  let u := firstThreeDate A ω n
  have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
  have hs : A/(n+1:ℕ) ≤ u/2 := (div_le_iff₀ hN).mpr (by
    change 2*A ≤ u*(n+1:ℕ) at hlate
    linarith only [hlate])
  have hpos := (div_pos hA hN).trans_le hs
  constructor
  · apply (div_le_iff₀ hB).mpr
    nlinarith only [hl]
  · by_contra! hhigh
    have hh : M ≤ (n+2:ℕ)*(u/2)^2 := by
      change 4*M < (n+2:ℕ)*u^2 at hhigh
      linarith only [hhigh]
    have hfit := hn (u/2) ⟨hpos.le,by change u<1 at hu; linarith only [hu]⟩ hh
    have hmin := SpectralApproximation.firstVisit_isLeast
      ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      (A/(n+1:ℕ)) 3 (by norm_num : (0:ℝ)<1/10)
    have hbad : u ≤ u/2 := hmin.2 ⟨hs,hfit⟩
    linarith only [hbad,hpos]

#print axioms gaussian_first_three_scale
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
