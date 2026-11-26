import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.PhysicalWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ShortCircuitReplay.PairedSpan
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.WindowMeasure

/-! # Sharp low-budget visit spans and rebound at the first physical dip -/

open Real Filter MeasureTheory Set
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
open FirstAscent.ThermodynamicEdges
noncomputable section

/-- For sublinear combined budgets and tolerance at most one eighth,
the maximum scaled visit span through time δK/(log K)² converges to
8 arcsin(e/2)/w. Near-maximal spans occur after every origin. -/
theorem gaussian_polynomial_sharp_span :
    ∃ w>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw,
      let K := fun n : ℕ => ((n+2:ℕ):ℝ)
      let H := fun n => shellOperator (pathPauliDisorderShell ω n)
      Tendsto (fun n => physicalWidth ω n/K n) atTop (𝓝 w) ∧
      ∀ i j : ℕ→ℕ, Tendsto (fun n => ((i n+j n:ℕ):ℝ)/K n) atTop (𝓝 0) →
        ∀ e ∈ Ioc (0:ℝ) (1/8), ∀ η>0, ∀ᶠ n in atTop,
          let x := 8*arcsin (e/2)/w
          let T := max 1 (δ*K n/(log (K n))^2)
          (∀ v : ℝ, ∀ t∈Icc (0:ℝ) T, orbitCircuitDistance (H n) (i n) v≤e →
            orbitCircuitDistance (H n) (j n) (v+t)≤e → K n*t<x+η) ∧
          ∀ a : ℝ, ∃ v≥a, ∃ t∈Icc (0:ℝ) T, x-η<K n*t ∧
            orbitCircuitDistance (H n) (i n) v<e ∧ orbitCircuitDistance (H n) (j n) (v+t)<e := by
  obtain ⟨w,hw,hspan⟩ := FirstAscent.ShortCircuitReplay.gaussian_sharp_pair_span
  obtain ⟨κ,hκ,A,_,δ,hδ,hgap⟩ := gaussian_polynomial_visit_spacing
  refine ⟨w,hw,δ,hδ,?_⟩
  filter_upwards [hspan,hgap] with ω hs hg
  intro K H
  refine ⟨hs.1,?_⟩
  intro i j hij e he η hη
  have he' : e∈Ioo (0:ℝ) (sqrt 2) := ⟨he.1,he.2.trans_lt ((by norm_num : (1/8:ℝ)<1).trans Real.one_lt_sqrt_two)⟩
  have hcost := hij.eventually_lt_const hκ
  have htop : Tendsto K atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [hs.2 i j hij e he' 1 zero_lt_one η hη,hg,hcost,htop.eventually (eventually_ge_atTop A)]
    with n hs hg hc hK
  intro x T
  have hp : 0<K n := by dsimp only [K]; positivity
  constructor
  · intro v t ht hv hw
    apply hs.1 v t ⟨ht.1,?_⟩ hv hw
    have hfit := hg v (v+t) (i n) (j n) e e (by linarith only [he.2])
      ((div_lt_iff₀ hp).mp hc).le ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr hv)
      ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr hw)
    rw [add_sub_cancel_left,abs_of_nonneg ht.1] at hfit
    rcases hfit with h|h
    · exact h.le.trans ((div_le_one hp).mpr hK)
    · exact (le_max_iff.mp ht.2).resolve_right (not_le_of_gt h)
  · intro a
    obtain ⟨v,hv,t,ht,hl,h₁,h₂⟩ := hs.2 a
    exact ⟨v,hv,t,⟨ht.1,ht.2.trans (le_max_left ..)⟩,hl,h₁,h₂⟩

#print axioms gaussian_polynomial_sharp_span


/-- In every time record the total duration of low-cost visits at one
tenth is bounded by the inverse-size cluster width times a count of
polynomial-length windows. The bound is uniform in the record origin. -/
theorem gaussian_polynomial_occupation :
    ∃ κ>0, ∃ A>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H := shellOperator (pathPauliDisorderShell ω n)
      let T := δ*K/(log K)^2
      ∀ s : ℕ, (s:ℝ)≤κ*K →
        let E := {v : ℝ | HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H.val v)}
        ∀ a W : ℝ, 0≤W → volume.real (E∩Icc a (a+W))≤(1+W/T)*(A/K) := by
  obtain ⟨κ,hκ,A,hA,δ,hδ,hg⟩ := gaussian_polynomial_visit_spacing
  refine ⟨κ/2,half_pos hκ,A,hA,δ,hδ,?_⟩
  filter_upwards [hg] with ω hw
  filter_upwards [hw] with n hn
  intro K H T s hs E a W hW
  have hK : 1<K := by dsimp only [K]; exact_mod_cast (by omega : 1<n+2)
  have hp := zero_lt_one.trans hK
  have hT : 0<T := div_pos (mul_pos hδ hp) (sq_pos_of_pos (log_pos hK))
  apply SpanningDensity.LocalEcho.occupation_of_forbidden_lags E _ _ (div_nonneg hA.le hp.le) hT _ a W hW
  intro v hv w hw
  have hsum : ((s+s:ℕ):ℝ)≤κ*K := by rw [Nat.cast_add]; linarith only [hs]
  exact hn v w s s (1/10) (1/10) (by norm_num) hsum hv hw

#print axioms gaussian_polynomial_occupation

/-- After the first low-budget visit following the original near-Hilbert
crossing, the entire interval of intermediate lags requires an extensive
combined gate budget. The incoming visit itself may cost positive gates. -/
theorem gaussian_polynomial_first_rebound :
    ∃ κ>0, ∃ A>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H := shellOperator (pathPauliDisorderShell ω n)
      ∀ (s r : ℕ) (h : ℝ), A/K≤h → h≤δ*K/(log K)^2 →
        let v := RepeatedGates.PhysicalBlocks.firstLowAfterCrossing ω n s
        HasProjectiveCircuitApproximation (n+2) (3/20) r (unitaryEvolution H.val (v+h)) →
        κ*K<((s+r:ℕ):ℝ) := by
  obtain ⟨κ,hκ,A,hA,δ,hδ,hg⟩ := gaussian_polynomial_visit_spacing
  refine ⟨κ,hκ,A,hA,δ,hδ,?_⟩
  filter_upwards [hg] with ω hω
  filter_upwards [hω] with n hn
  intro K H s r h hstart hend v hf
  have hv : HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H.val v) :=
    (PrecisionReturns.firstVisit_isLeast H _ s (by norm_num : (0:ℝ)<1/10)).1.2
  have hK : 0<K := by dsimp only [K]; positivity
  have hp := (div_pos hA hK).le.trans hstart
  by_contra! hk
  have hl := hn v (v+h) s r (1/10) (3/20) (by norm_num) hk hv hf
  rw [add_sub_cancel_left,abs_of_nonneg hp] at hl
  exact hl.elim hstart.not_gt hend.not_gt

#print axioms gaussian_polynomial_first_rebound

end
end GaloisForLFunctions.HTGeometry.BlockDilations
