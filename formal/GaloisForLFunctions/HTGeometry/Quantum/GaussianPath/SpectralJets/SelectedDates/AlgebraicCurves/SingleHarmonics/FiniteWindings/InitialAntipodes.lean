import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.PhysicalWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ShortCircuitReplay.BoundedHorizon
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # The first affordable date shared by the initial extremal antipodes -/

open Real Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings
open FirstAscent FirstAscent.ThermodynamicEdges FirstAscent.EnergyMesh PrecisionReturns
noncomputable section

private theorem chord_floor {x : ℝ} (hx : 2*π/3≤x) : 1≤clippedChord x := by
  let y := min x (2*π)/4
  have h₁ : π/6≤y := by
    have h := le_min hx (by linarith only [pi_pos] : 2*π/3≤2*π)
    dsimp only [y]; linarith only [h]
  have h₂ : y≤π/2 := by dsimp only [y]; linarith only [min_le_right x (2*π)]
  have hh := monotoneOn_sin (show π/6∈Icc (-(π/2)) (π/2) by constructor <;> linarith only [pi_pos])
    (show y∈Icc (-(π/2)) (π/2) from ⟨by linarith only [pi_pos,h₁],h₂⟩) h₁
  rw [sin_pi_div_six] at hh
  change 1≤2*sin y
  linarith only [hh]

/-- Every sublinear gate budget fails throughout the interval from
the very first extremal antipode through a polynomial physical time. -/
theorem gaussian_initial_antipodal_exclusion :
    ∃ w>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw,
      let K := fun n : ℕ => ((n+2:ℕ):ℝ)
      let W := physicalWidth ω
      let H := fun n => shellOperator (pathPauliDisorderShell ω n)
      Tendsto (fun n => W n/K n) atTop (𝓝 w) ∧ ∀ s : ℕ→ℕ,
        Tendsto (fun n => (s n:ℝ)/K n) atTop (𝓝 0) → ∀ᶠ n in atTop,
        ∀ t∈Icc (π/W n) (δ*K n/(log (K n))^2), 1/4<orbitCircuitDistance (H n) (s n) t := by
  obtain ⟨w,hw,hr⟩ := ShortCircuitReplay.gaussian_bounded_gate_replay
  obtain ⟨κ,hκ,A,_,δ,hδ,hp⟩ := BlockDilations.gaussian_polynomial_from_startup
  refine ⟨w,hw,δ,hδ,?_⟩
  filter_upwards [hr,hp] with ω hr hp
  intro K W H
  have hWlim : Tendsto (fun n => W n/K n) atTop (𝓝 w) := hr.1
  refine ⟨hWlim,?_⟩
  intro s hs
  have hprofile := hr.2 (fun _ => 0) s (Eventually.of_forall fun _ => Nat.zero_le _) hs
    1 (1/4) (by norm_num)
  have htop : Tendsto K atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [hp,hprofile,hs.eventually_lt_const hκ,hWlim.eventually_const_lt hw,
    hWlim.eventually_lt_const (show w<3*w/2 by linarith only [hw]),htop.eventually (eventually_ge_atTop A)]
    with n hn hshort hcost hpos hwidth hsize
  intro t ht
  have hK : 0<K n := by dsimp only [K]; positivity
  have hW : 0<W n := by simpa only [zero_mul] using (lt_div_iff₀ hK).mp hpos
  have ht₀ := (div_pos pi_pos hW).le.trans ht.1
  by_cases h : t≤1
  · have hh := hshort 0 t ⟨ht₀,h⟩
    have hz := orbitCircuitDistance_zeroGate_eq_spectralArc (H n)
      ⟨0,by simpa only [abs_zero,zero_mul] using pi_pos.le⟩
    have hzero : orbitCircuitDistance (H n) 0 0=0 := by
      simpa only [abs_zero,zero_mul,sin_zero,mul_zero] using hz
    change |orbitCircuitDistance (H n) (s n) (0+t)-clippedChord (K n*t*w)|≤orbitCircuitDistance (H n) 0 0+1/4 at hh
    rw [zero_add,hzero,zero_add] at hh
    have hf : 2*π/3≤K n*t*w := by
      have hh := mul_le_mul_of_nonneg_left ((div_lt_iff₀ hK).mp hwidth).le ht₀
      nlinarith only [hh,(div_le_iff₀ hW).mp ht.1]
    linarith only [(abs_le.mp hh).1,chord_floor hf]
  · apply lt_of_not_ge
    intro hfit
    have hf := hn t (hsize.trans (by
      rw [abs_of_nonneg ht₀]
      exact le_mul_of_one_le_right hK.le (le_of_not_ge h))) (by rw [abs_of_nonneg ht₀]; exact ht.2)
      (s n) ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr hfit)
    exact hf.not_ge ((div_lt_iff₀ hK).mp hcost).le

/-- An exclusion interval identifies the same first actual visit from
every origin inside it, simultaneously at all smaller tolerances. -/
theorem firstVisit_on_gap {N : ℕ} (H : selfAdjoint (PrecisionReturns.Register N)) {a T : ℝ}
    (s : ℕ) (e d : ℝ) (he : 0<e) (hd : e≤d)
    (hgap : ∀ t∈Icc a T, d<orbitCircuitDistance H s t) {u : ℝ} (hu : u∈Icc a T) :
    T<firstVisit H u s e ∧ firstVisit H u s e=firstVisit H a s e := by
  have hset : visitSet H u s e=visitSet H a s e := by
    ext t
    constructor
    · exact fun ht => ⟨hu.1.trans ht.1,ht.2⟩
    · intro ht
      have hh := (hasProjectiveCircuitApproximation_iff_infDist ..).mp ht.2
      exact ⟨le_of_not_gt fun h => (hgap t ⟨ht.1,h.le.trans hu.2⟩).not_ge (hh.trans hd),ht.2⟩
  have hm := (firstVisit_isLeast H u s he).1
  refine ⟨lt_of_not_ge (fun h => ?_),congrArg sInf hset⟩
  exact (hgap _ ⟨hu.1.trans hm.1,h⟩).not_ge (((hasProjectiveCircuitApproximation_iff_infDist ..).mp hm.2).trans hd)

/-- Every origin after the first antipode and before the polynomial
horizon sees one common first affordable date beyond the horizon. -/
theorem gaussian_initial_common_first_visit :
    ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ→ℕ,
      Tendsto (fun n => (s n:ℝ)/((n+2:ℕ):ℝ)) atTop (𝓝 0) → ∀ᶠ n in atTop,
        let K : ℝ := (n+2:ℕ)
        let a := π/physicalWidth ω n
        let T := δ*K/(log K)^2
        let H := shellOperator (pathPauliDisorderShell ω n)
        ∀ u∈Icc a T, ∀ e∈Ioc (0:ℝ) (1/4),
          T<firstVisit H u (s n) e ∧ firstVisit H u (s n) e=firstVisit H a (s n) e := by
  obtain ⟨_,_,δ,hδ,h⟩ := gaussian_initial_antipodal_exclusion
  refine ⟨δ,hδ,?_⟩
  filter_upwards [h] with ω hω
  intro s hs
  filter_upwards [hω.2 s hs] with n hn
  intro K a T H u hu e he
  exact firstVisit_on_gap H _ e (1/4) he.1 he.2 hn hu

#print axioms gaussian_initial_antipodal_exclusion
#print axioms gaussian_initial_common_first_visit
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings
