import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.FirstPeriods
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.Density
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.PhysicalRates

/-! # Spectral periods and physical time for a frozen Gaussian prefix -/

open Set MeasureTheory Filter Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
open SharpOccupation FirstAscent.ThermodynamicEdges
noncomputable section

abbrev register (k : ℕ) (ω : PathPauliDisorder) : selfAdjoint (SharpOccupation.Register (k+3)) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))⟩

/-- Actual physical time of the selected extremal antipode. -/
def origin (k n : ℕ) (ω : PathPauliDisorder) : ℝ :=
  let x := fun l => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) l)
  date (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x) (topLevel k) 0 n 0

def elapsed (k n : ℕ) (ε : ℝ) (ω : PathPauliDisorder) : ℝ :=
  PrecisionReturns.firstVisit (register k ω) (origin k n ω) 0 ε-origin k n ω

/-- Finite spectral-width density bounds the number of full-width periods
per unit of physical time by a constant times the register size. -/
theorem gaussian_periods_per_time :
    ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ∀ n : ℕ, ∀ ε>0,
      firstPeriods k n ε ω ≤ elapsed k n ε ω*(C*(k+3:ℕ)) := by
  obtain ⟨w,hw,_,hd⟩ := gaussian_energy_density
  refine ⟨w+1,by linarith only [hw],?_⟩
  filter_upwards [hd,gaussian_path_all_prefixes_maximally_projective] with ω hω hsimple
  have hlim := hω.comp (tendsto_add_atTop_nat 1)
  filter_upwards [hlim.eventually_lt_const (lt_add_one w)] with k hk n ε hε
  let H := register k ω
  let x := fun l => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) l)
  let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
  let i := topLevel k
  let j : Level k := 0
  obtain ⟨e,he⟩ := physical_sorted_order k ω (hsimple k).injective
  have hbound : E i-E j ≤ physicalWidth ω (k+1) := by
    change E i-E j ≤ _ - _
    have ha := Finset.le_sup' H.2.isHermitian.eigenvalues (Finset.mem_univ (e.symm i))
    have hb := Finset.inf'_le H.2.isHermitian.eigenvalues (Finset.mem_univ (e.symm j))
    have hlabel (l : Level k) : H.2.isHermitian.eigenvalues (e.symm l)=E l := by
      simpa only [e.apply_symm_apply] using he (e.symm l)
    rw [←hlabel i,←hlabel j]
    exact sub_le_sub ha hb
  have hwidth : physicalWidth ω (k+1) < (w+1)*(k+3:ℕ) := by
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < (k+3:ℕ))).mp
    exact hk
  have hrate : (E i-E j)/(2*π) ≤ (w+1)*(k+3:ℕ) := by
    apply (div_le_iff₀ two_pi_pos).mpr
    refine (hbound.trans hwidth.le).trans ?_
    exact le_mul_of_one_le_right (by positivity) (by linarith only [pi_gt_three])
  change elapsed k n ε ω*((E i-E j)/(2*π)) ≤ _
  exact mul_le_mul_of_nonneg_left hrate (sub_nonneg.mpr
    (PrecisionReturns.firstVisit_isLeast H (origin k n ω) 0 hε).1.1)

/-- Every origin on a sufficiently long frozen prefix has a zero-gate
return within the same doubly exponential physical time horizon. -/
theorem gaussian_elapsed_upper :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ ε ∈ Ioo (0:ℝ) (sqrt 2), ∀ᶠ k : ℕ in atTop,
      ∀ a : ℝ, PrecisionReturns.firstVisit (register k ω) a 0 ε-a ≤ 2*(2:ℝ)^((2^(k+3):ℕ)^c) := by
  obtain ⟨c,hc⟩ := FiniteRecords.gaussian_finite_physical_rates_full
  refine ⟨c,?_⟩
  filter_upwards [hc] with ω hω ε hε
  have hx := (physicalArc_spec hε.1 hε.2).1
  have hs : sqrt 2 ≤ 2 := by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
  have h := hω (fun n => n^1) (polynomial_subcritical 1) ε ⟨hε.1,hε.2.trans_le hs⟩
    (physicalArc ε/2) 1 (half_pos hx.1) (half_lt_self hx.1) (hx.2.trans (by norm_num))
  filter_upwards [h] with k hk a
  let G := 2*(2:ℝ)^((2^(k+3):ℕ)^c)
  let H := register k ω
  have hp := (((hk 0 (Nat.zero_le _) a).1 G le_rfl).1)
  have hpos : 0 < visitFraction H 0 ε a (a+G) := (pow_pos (half_pos hx.1) _).trans hp
  have hne : (visitSet H 0 ε ∩ Icc a (a+G)).Nonempty := by
    by_contra hempty
    rw [visitFraction,not_nonempty_iff_eq_empty.mp hempty] at hpos
    simp only [measureReal_empty,zero_div,lt_self_iff_false] at hpos
  obtain ⟨t,ht,hta,htb⟩ := hne
  have hle := (PrecisionReturns.firstVisit_isLeast H a 0 hε.1).2 ⟨hta,ht⟩
  linarith only [hle,htb]

#print axioms gaussian_periods_per_time
#print axioms gaussian_elapsed_upper
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
