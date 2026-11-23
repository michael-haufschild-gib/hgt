import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.PhysicalWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.WindowMeasure

/-! # Physical occupation and rebound on a diverging time scale -/
open MeasureTheory Filter Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- Every pair of visits at a lag from inverse size through the growing
horizon costs almost one gate per bond in total. -/
theorem gaussian_expanding_lag_floor :
    ∃ L : ℕ → ℕ, Monotone L ∧ Tendsto L atTop atTop ∧ ∀ η : ℝ, 0 < η →
      ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let H := pathHamiltonian (pathPauliDisorderShell ω n)
        ∀ v w : ℝ, A ≤ |w-v| *(n+1:ℕ) → |w-v| ≤ (L n:ℝ) → ∀ j s : ℕ, ∀ ε δ : ℝ, ε+δ ≤ 1/4 →
          HasProjectiveCircuitApproximation (n+2) ε j (unitaryEvolution H v) →
          HasProjectiveCircuitApproximation (n+2) δ s (unitaryEvolution H w) →
          (1-η)*(n+1:ℕ)<((j+s:ℕ):ℝ) := by
  obtain ⟨L,hm,ht,h⟩ := gaussian_expanding_from_startup
  refine ⟨L,hm,ht,?_⟩
  intro η hη
  obtain ⟨A,hA,hw⟩ := h η hη
  refine ⟨A,hA,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  intro _ v w hlate hend j s ε δ herr hv hw
  let H : selfAdjoint (Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ) :=
    ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  apply hn (w-v) hlate hend (j+s)
  have he := affordable_add_time H (x := -v) (y := w) (i := j) (j := s) (hv.neg_time H) hw
  rw [show -v+w=w-v by ring] at he
  obtain ⟨z,hz,C,hC,hfit⟩ := he
  exact ⟨z,hz,C,hC,hfit.trans herr⟩

/-- Uniformly over all origins a window of length T contains at most
(1+T/L)A/(N−1) affordable time below any fixed sub-half density. -/
theorem gaussian_expanding_occupation :
    ∃ L : ℕ → ℕ, Monotone L ∧ Tendsto L atTop atTop ∧ ∀ κ : ℝ, κ < 1/2 →
      ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, (s:ℝ) ≤ κ*(n+1:ℕ) →
        let H := pathHamiltonian (pathPauliDisorderShell ω n)
        let E := {t : ℝ | HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H t)}
        (∀ v∈E, ∀ w∈E, |w-v|<A/(n+1:ℕ) ∨ (L n:ℝ) < |w-v|) ∧
        ∀ a T : ℝ, 0 ≤ T → volume.real (E∩Icc a (a+T)) ≤ (1+T/(L n:ℝ))*(A/(n+1:ℕ)) := by
  obtain ⟨L,hm,ht,h⟩ := gaussian_expanding_lag_floor
  refine ⟨L,hm,ht,?_⟩
  intro κ hκ
  obtain ⟨A,hA,hw⟩ := h (1-2*κ) (by linarith only [hκ])
  refine ⟨A,hA,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω,ht.eventually (eventually_ge_atTop 1)] with n hn hL
  intro s hs H E
  have hpos : 0 < ((n+1:ℕ):ℝ) := by positivity
  have gap (v : ℝ) (hv : v∈E) (w : ℝ) (hw : w∈E) : |w-v|<A/(n+1:ℕ) ∨ (L n:ℝ) < |w-v| := by
    by_contra! hbad
    have hh := hn v w ((div_le_iff₀ hpos).mp hbad.1) hbad.2 s s (1/10) (1/10) (by norm_num) hv hw
    rw [Nat.cast_add s s] at hh
    linarith only [hh,hs]
  exact ⟨gap,LocalEcho.occupation_of_forbidden_lags E _ (L n:ℝ) (div_nonneg hA.le hpos.le)
    (Nat.cast_pos.mpr hL) gap⟩

#print axioms gaussian_expanding_lag_floor
#print axioms gaussian_expanding_occupation
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
