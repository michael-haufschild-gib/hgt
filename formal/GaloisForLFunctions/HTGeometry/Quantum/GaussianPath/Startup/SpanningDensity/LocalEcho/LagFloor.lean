import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.PhysicalWindow
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Unit lower gate density for both ends of every vanishing physical lag -/
open Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section

/-- The two physical gate counts across an arbitrary absolute date sum to
nearly one gate per bond. The lag range has a prefix-independent upper limit. -/
theorem gaussian_lag_floor : ∀ η : ℝ, 0<η → ∃ A b : ℝ, 0<A ∧ 0<b ∧
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ v t : ℝ, A ≤ |t| * (n+1:ℕ) → |t|≤b → ∀ j s : ℕ, ∀ ε δ : ℝ, ε+δ ≤ 1/4 →
        HasProjectiveCircuitApproximation (n+2) ε j (unitaryEvolution H v) →
        HasProjectiveCircuitApproximation (n+2) δ s (unitaryEvolution H (v+t)) →
          (1-η)*(n+1:ℕ) < (j+s:ℕ) := by
  intro η hη
  obtain ⟨A,b,hA,hb,h⟩ := gaussian_physical_window η hη
  refine ⟨A,b,hA,hb,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro H v t ht hb j s ε δ hε hv hs
  let K : selfAdjoint (Register (n+2)) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  have hh := affordable_add_time K (hv.neg_time K) hs
  have he : -v+(v+t)=t := by ring
  rw [he] at hh
  obtain ⟨z,hz,C,hC,herr⟩ := hh
  exact hn t ht hb _ ⟨z,hz,C,hC,herr.trans hε⟩

/-- One Gaussian event works for every draw-dependent sequence of lags,
origins and affordable budgets, with no bound on N times the squared lag. -/
theorem gaussian_vanishing_lags : ∀ᵐ ω ∂pathPauliDisorderLaw,
    ∀ v t : ℕ→ℝ, ∀ j s : ℕ→ℕ, Tendsto t atTop (𝓝 0) → Tendsto (fun n => |t n| * (n+1:ℕ)) atTop atTop →
    (∀ᶠ n : ℕ in atTop, let H := pathHamiltonian (pathPauliDisorderShell ω n)
      HasProjectiveCircuitApproximation (n+2) (1/10) (j n) (unitaryEvolution H (v n)) ∧
      HasProjectiveCircuitApproximation (n+2) (1/10) (s n) (unitaryEvolution H (v n+t n))) →
    ∀ z : ℝ, z<1 → ∀ᶠ n : ℕ in atTop, z < ((j n+s n:ℕ):ℝ)/(n+1:ℕ) := by
  let δ (k : ℕ) : ℝ := 1/(k+1:ℕ)
  have he (k : ℕ) := gaussian_lag_floor (δ k) (by dsimp only [δ]; positivity)
  choose A b hA hb ht using he
  filter_upwards [ae_all_iff.mpr ht] with ω hw
  intro v t j s hzero hlate hfit z hz
  obtain ⟨k,hk⟩ := exists_nat_gt (1/(1-z))
  have hd : z<1-δ k := by
    have h := (div_lt_iff₀ (sub_pos.mpr hz)).mp hk
    have hk' : 0<((k+1:ℕ):ℝ) := by positivity
    have hδ : δ k<1-z := (div_lt_iff₀ hk').mpr (by push_cast; linarith only [h,hz])
    linarith only [hδ]
  have hab : Tendsto (fun n => |t n|) atTop (𝓝 0) := by simpa only [abs_zero] using hzero.abs
  filter_upwards [hw k,hfit,hlate.eventually_ge_atTop (A k),hab.eventually_lt_const (hb k)] with n hn hfit ht hb'
  have hl := hn (v n) (t n) ht hb'.le (j n) (s n) (1/10) (1/10) (by norm_num) hfit.1 hfit.2
  exact hd.trans ((lt_div_iff₀ (show 0<((n+1:ℕ):ℝ) by positivity)).mpr hl)

#print axioms gaussian_vanishing_lags
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
