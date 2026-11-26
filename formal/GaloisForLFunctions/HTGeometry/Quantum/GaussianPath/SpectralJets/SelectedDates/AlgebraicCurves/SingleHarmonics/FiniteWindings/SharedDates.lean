import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings.InitialAntipodes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianClock

/-! # A common physical first visit over almost quadratically many windings -/

open Real Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings
open FirstAscent FirstAscent.ThermodynamicEdges PrecisionReturns
noncomputable section

/-- The empty circuit fits precisely one initial interval up through the
polynomial horizon. Its endpoint uses the actual width of the prefix. -/
theorem gaussian_exact_initial_scalar_interval :
    ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let W := physicalWidth ω n
      let H := shellOperator (pathPauliDisorderShell ω n)
      ∀ t∈Icc (0:ℝ) (δ*K/(log K)^2), ∀ e∈Icc (0:ℝ) (1/4),
        HasProjectiveCircuitApproximation (n+2) e 0 (unitaryEvolution H.val t) ↔
          t≤4*arcsin (e/2)/W := by
  obtain ⟨_,_,δ,hδ,h⟩ := gaussian_initial_antipodal_exclusion
  obtain ⟨a,_,ha,_,hc⟩ := gaussian_initial_clock
  refine ⟨δ,hδ,?_⟩
  filter_upwards [h,hc] with ω hω hc
  have hz : Tendsto (fun n : ℕ => (((0:ℕ):ℝ))/((n+2:ℕ):ℝ)) atTop (𝓝 0) := by simp
  filter_upwards [hω.2 (fun _ => 0) hz,hc] with n hn hclock
  intro K W H t ht e he
  have hW : 0<W := (mul_pos ha (by dsimp [K]; positivity : 0<K)).trans_le hclock.1
  have he' : e∈Icc (0:ℝ) 2 := ⟨he.1,he.2.trans (by norm_num)⟩
  by_cases hs : t≤π/W
  · exact hclock.2.2 t ⟨ht.1,hs⟩ e he'
  · have hstart := (le_of_not_ge hs)
    have h₁ := hn t ⟨hstart,ht.2⟩
    have h₂ := hn (π/W) ⟨le_rfl,hstart.trans ht.2⟩
    constructor
    · intro hf
      exact (h₁.not_ge (((hasProjectiveCircuitApproximation_iff_infDist ..).mp hf).trans he.2)).elim
    · intro hl
      have hf := (hclock.2.2 (π/W) ⟨(div_pos pi_pos hW).le,le_rfl⟩ e he').mpr (hstart.trans hl)
      exact (h₂.not_ge (((hasProjectiveCircuitApproximation_iff_infDist ..).mp hf).trans he.2)).elim

/-- Every one of the first c(K/log K)² antipodes has the same next
s-gate visit. Its elapsed wait exceeds δK/(log K)² for all these origins,
including the first one, on the original frozen sample. -/
theorem gaussian_shared_initial_windings :
    ∃ c>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ→ℕ,
      Tendsto (fun n => (s n:ℝ)/((n+2:ℕ):ℝ)) atTop (𝓝 0) → ∀ᶠ n in atTop,
      let K : ℝ := (n+2:ℕ)
      let W := physicalWidth ω n
      let H := shellOperator (pathPauliDisorderShell ω n)
      ∀ j : ℕ, (j:ℝ)+1≤c*(K/log K)^2 → ∀ e∈Ioc (0:ℝ) (1/4),
        let a := (2*(j:ℝ)+1)*π/W
        firstVisit H a (s n) e=firstVisit H (π/W) (s n) e ∧
          δ*K/(log K)^2<firstVisit H a (s n) e-a := by
  obtain ⟨δ,hδ,h⟩ := gaussian_initial_common_first_visit
  obtain ⟨w,hw,_,hd⟩ := gaussian_energy_density
  let c := δ*w/(8*π)
  have hc : 0<c := by dsimp only [c]; positivity
  refine ⟨c,hc,δ/2,half_pos hδ,?_⟩
  filter_upwards [h,hd] with ω hω hd
  intro s hs
  filter_upwards [hω s hs,hd.eventually_const_lt (half_lt_self hw)] with n hn hW
  intro K W H j hj e he a
  have hK : 1<K := by dsimp only [K]; exact_mod_cast (show 1<n+2 by omega)
  have hK' := zero_lt_one.trans hK
  have hlog := log_pos hK
  have hlow : w/2*K<W := (lt_div_iff₀ hK').mp hW
  have hWp := (mul_pos (half_pos hw) hK').trans hlow
  have hbase : π/W≤a := div_le_div_of_nonneg_right
    (by nlinarith only [mul_nonneg (Nat.cast_nonneg j : 0≤(j:ℝ)) pi_pos.le]) hWp.le
  let T := δ*K/(log K)^2
  have ht : 0≤T := div_nonneg (mul_nonneg hδ.le hK'.le) (sq_nonneg _)
  have htop : a≤T/2 := by
    apply (div_le_iff₀ hWp).mpr
    calc
      (2*(j:ℝ)+1)*π ≤ (j+1:ℝ)*(2*π) := by linarith only [pi_pos]
      _ ≤ c*(K/log K)^2*(2*π) := mul_le_mul_of_nonneg_right hj two_pi_pos.le
      _ = T/2*(w/2*K) := by dsimp only [c,T]; field_simp; ring
      _ ≤ T/2*W := mul_le_mul_of_nonneg_left hlow.le (div_nonneg ht zero_le_two)
  obtain ⟨hdate,hfirst⟩ := hn a ⟨hbase,htop.trans (half_le_self ht)⟩ e he
  refine ⟨hfirst,?_⟩
  change δ/2*K/(log K)^2<_
  rw [show δ/2*K/(log K)^2=T/2 by dsimp only [T]; ring]
  linarith only [hdate,htop]

#print axioms gaussian_exact_initial_scalar_interval
#print axioms gaussian_shared_initial_windings
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings
