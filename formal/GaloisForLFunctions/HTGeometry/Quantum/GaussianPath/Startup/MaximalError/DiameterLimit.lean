import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.MaximalError.PhysicalWindow
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralEnclosingArc

/-! # Sharp limiting error for sublinear physical budgets -/
open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.MaximalError
noncomputable section

private abbrev prefixHamiltonian (ω : PathPauliDisorder) (n : ℕ) :
    selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
  ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩

/-- On one frozen chain even the best circuit of sublinear size has
projective operator error tending to two at bounded signed dates with
N|t| tending to infinity. Both schedules can be chosen after the draw. -/
theorem gaussian_sublinear_error_tends_to_two :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (t : ℕ → ℝ) (s : ℕ → ℕ) (T : ℕ),
      (∀ᶠ n : ℕ in atTop, |t n|≤T) → Tendsto (fun n => (n+2:ℕ)*|t n|) atTop atTop →
      Tendsto (fun n => (s n:ℝ)/(n+2:ℕ)) atTop (𝓝 0) →
      Tendsto (fun n => orbitCircuitDistance (prefixHamiltonian ω n) (s n) (t n)) atTop (𝓝 2) := by
  let J := {q : ℚ // (q:ℝ)<2}
  have hw (q : J) (T : ℕ) := gaussian_positive_density_below_diameter q.property (Nat.cast_nonneg T)
  choose A c hA hc hpath using hw
  filter_upwards [ae_all_iff.mpr (fun q => ae_all_iff.mpr (hpath q))] with ω hω
  intro t s T hT ht hs
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r,har,hr⟩ := exists_rat_btwn ha
    let q : J := ⟨r,hr⟩
    filter_upwards [hω q T,hT,ht.eventually (eventually_ge_atTop (A q T)),
      hs.eventually_lt_const (hc q T)] with n hn hb hl hsmall
    apply har.trans
    apply lt_of_not_ge
    intro hfit
    have h := hn (t n) hl hb (s n) ((hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr hfit)
    exact ((div_lt_iff₀ (by positivity : 0<((n+2:ℕ):ℝ))).mp hsmall).not_ge h.le
  · intro a ha
    filter_upwards with n
    let H := prefixHamiltonian ω n
    obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr
      (orbitCircuitDistance_zeroGate_lt_two H (t n)).le
    exact lt_of_le_of_lt ((hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
      ⟨z,hz,C,hC.trans (Nat.zero_le _),he⟩) ha

#print axioms gaussian_sublinear_error_tends_to_two
end
end GaloisForLFunctions.HTGeometry.MaximalError
