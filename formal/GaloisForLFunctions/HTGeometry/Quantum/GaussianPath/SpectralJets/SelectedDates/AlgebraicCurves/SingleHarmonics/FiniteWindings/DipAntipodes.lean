import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings.InitialAntipodes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess

/-! # The rebound after an actual dip, beginning at the first spectral antipode -/

open Real Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings
open FirstAscent FirstAscent.ThermodynamicEdges PrecisionReturns
noncomputable section

/-- At any tolerance strictly below one quarter, even a fixed positive
fraction of the wires is too small from the first antipode onward.
On microscopic dates the advantage over the scalar fit costs at most
a constant times the square root of the fraction of wires. -/
theorem gaussian_extensive_from_first_antipode {e : ℝ} (he : e<1/4) :
    ∃ κ>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H := shellOperator (pathPauliDisorderShell ω n)
      ∀ t∈Icc (π/physicalWidth ω n) (δ*K/(log K)^2), ∀ s : ℕ, (s:ℝ)≤κ*K →
        e<orbitCircuitDistance H s t := by
  obtain ⟨w,hw,d,hd,hscalar⟩ := gaussian_initial_antipodal_exclusion
  obtain ⟨k,hk,A,hA,c,hc,hlarge⟩ := BlockDilations.gaussian_polynomial_from_startup
  obtain ⟨_,b,_,hb,hdis⟩ := gaussian_path_eventual_coefficient_mass
  let u := (1/4-e)/(2*A)
  have hu : 0<u := div_pos (sub_pos.mpr he) (mul_pos two_pos hA)
  let κ := min k (u^2/(42*b))
  have hκ : 0<κ := lt_min hk (div_pos (sq_pos_of_pos hu) (by positivity))
  refine ⟨κ,hκ,min d c,lt_min hd hc,?_⟩
  filter_upwards [hscalar,hlarge,hdis] with ω hz hl hd'
  have hs₀ : Tendsto (fun n : ℕ => (((0:ℕ):ℝ))/((n+2:ℕ):ℝ)) atTop (𝓝 0) := by simp
  filter_upwards [hz.2 (fun _ => 0) hs₀,hl,hd',hz.1.eventually_const_lt hw] with n hs hl hd' hp
  intro K H t ht s hsize
  have hK : 0<K := by dsimp only [K]; positivity
  have hW : 0<physicalWidth ω n := by simpa only [zero_mul] using (lt_div_iff₀ hK).mp hp
  have ht₀ := (div_pos pi_pos hW).le.trans ht.1
  have hbound {y : ℝ} (hy : min d c≤y) : t≤y*K/(log K)^2 :=
    ht.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hy hK.le) (sq_nonneg _))
  by_cases ha : A≤K*t
  · apply lt_of_not_ge
    intro hf
    have h := hl t (by rwa [abs_of_nonneg ht₀]) (by rw [abs_of_nonneg ht₀]; exact hbound (min_le_right ..))
      s ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr (hf.trans he.le))
    exact h.not_ge (hsize.trans (mul_le_mul_of_nonneg_right (min_le_left ..) hK.le))
  · have h₀ := hs t ⟨ht.1,hbound (min_le_left ..)⟩
    have hfrac := (div_le_iff₀ hK).mpr hsize
    have hrad : sqrt ((42*b)*((s:ℝ)/K))≤u := by
      rw [←sqrt_sq hu.le]
      apply sqrt_le_sqrt
      exact (mul_le_mul_of_nonneg_left (hfrac.trans (min_le_right ..)) (by positivity)).trans_eq
        (by field_simp : (42*b)*(u^2/(42*b))=u^2)
    have h := ShortCircuitReplay.scaled_advantage (pathPauliDisorderShell ω n) s (K*t) hb.le hd'.2
    change orbitCircuitDistance H 0 (K*t/K)≤orbitCircuitDistance H s (K*t/K)+
      2*|K*t| *sqrt ((42*b)*((s:ℝ)/K)) at h
    rw [show K*t/K=t by field_simp,abs_of_nonneg (mul_nonneg hK.le ht₀)] at h
    have hcost := mul_le_mul (mul_le_mul_of_nonneg_left (le_of_not_ge ha) zero_le_two)
      hrad (sqrt_nonneg _) (mul_nonneg zero_le_two hA.le)
    have heq : 2*A*u=1/4-e := by dsimp only [u]; field_simp
    linarith only [h,hcost,h₀,heq]

/-- After the true first low visit following the near-Hilbert crossing,
the combined budgets of the incoming and outgoing circuits are extensive
at every lag from the first spectral antipode through the growing horizon. -/
theorem gaussian_first_dip_antipodal_rebound :
    ∃ κ>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H := shellOperator (pathPauliDisorderShell ω n)
      ∀ s r : ℕ, ((s+r:ℕ):ℝ)≤κ*K → ∀ t∈Icc (π/physicalWidth ω n) (δ*K/(log K)^2),
        let v := RepeatedGates.PhysicalBlocks.firstLowAfterCrossing ω n s
        1/10<orbitCircuitDistance H r (v+t) := by
  obtain ⟨κ,hκ,δ,hδ,h⟩ := gaussian_extensive_from_first_antipode (e:=1/5) (by norm_num)
  refine ⟨κ,hκ,δ,hδ,?_⟩
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  intro K H s r hsize t ht v
  apply lt_of_not_ge
  intro hh
  have hv : HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H.val v) :=
    (firstVisit_isLeast H _ s (by norm_num : (0:ℝ)<1/10)).1.2
  have hf := affordable_add_time H (x:= -v) (y:=v+t) (hv.neg_time H)
    ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr hh)
  rw [show -v+(v+t)=t by ring,show (1/10:ℝ)+1/10=1/5 by norm_num] at hf
  exact (hn t ht (s+r) hsize).not_ge ((hasProjectiveCircuitApproximation_iff_infDist ..).mp hf)

#print axioms gaussian_extensive_from_first_antipode
#print axioms gaussian_first_dip_antipodal_rebound
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.FiniteWindings
