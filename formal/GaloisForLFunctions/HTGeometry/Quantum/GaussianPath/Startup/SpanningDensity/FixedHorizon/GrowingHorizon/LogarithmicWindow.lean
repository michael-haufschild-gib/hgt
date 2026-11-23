import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.LogarithmicMesh
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.PhysicalWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.WindowMeasure

/-! # Physical gate counts and return spacing through logarithmic time -/
open MeasureTheory Filter Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- For each fixed density deficit, an inverse-size onset and a
logarithmic signed horizon bound a whole interval of extensive cost. -/
theorem gaussian_logarithmic_from_startup {η : ℝ} (hη : 0 < η) :
    ∃ A > 0, ∃ b : ℕ, 2 ≤ b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      A ≤ |t| *(n+1:ℕ) → |t| ≤ (Nat.log b n:ℝ) → ∀ s : ℕ,
      HasProjectiveCircuitApproximation (n+2) (1/4) s
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
      (1-η)*(n+1:ℕ) < (s:ℝ) := by
  obtain ⟨A,hA,hs⟩ := gaussian_all_bounded_horizons hη
  obtain ⟨b,hb,hl⟩ := logarithmic_cut_window (a:=1) zero_lt_one (half_pos hη)
    (by norm_num : (0:ℝ) < 1-(1/4)^2/2)
  refine ⟨A,hA,b,hb,?_⟩
  filter_upwards [hs,hl] with ω hω hw
  filter_upwards [hω 1,hw] with n hn hl
  intro t ht htime s hfit
  by_cases h : |t| ≤ 1
  · exact hn t ht h s hfit
  apply gate_floor_of_cut (hl |t| ⟨le_of_not_ge h,htime⟩)
  rcases le_total 0 t with ht|ht
  · rwa [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht]
    let H : selfAdjoint (Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ) :=
      ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
    exact hfit.neg_time H

/-- Low-cost dates in any window cluster on intervals of inverse-size
width separated by more than the logarithmic horizon. -/
theorem gaussian_logarithmic_occupation {κ : ℝ} (hκ : κ < 1/2) :
    ∃ A > 0, ∃ b : ℕ, 2 ≤ b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ s : ℕ, (s:ℝ) ≤ κ*(n+1:ℕ) →
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      let E := {t : ℝ | HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H t)}
      (∀ v∈E, ∀ w∈E, |w-v| < A/(n+1:ℕ) ∨ (Nat.log b n:ℝ) < |w-v|) ∧
      ∀ a T : ℝ, 0 ≤ T → volume.real (E∩Icc a (a+T)) ≤ (1+T/(Nat.log b n:ℝ))*(A/(n+1:ℕ)) := by
  obtain ⟨A,hA,b,hb,h⟩ := gaussian_logarithmic_from_startup (η:=1-2*κ) (by linarith only [hκ])
  refine ⟨A,hA,b,hb,?_⟩
  filter_upwards [h] with ω hω
  filter_upwards [hω,eventually_ge_atTop b] with n hn hbn
  intro s hs H E
  let G : selfAdjoint (Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
  have hlog : 0 < Nat.log b n := (Nat.le_log_iff_pow_le hb (by omega)).mpr (by simpa using hbn)
  have gap (v : ℝ) (hv : v∈E) (w : ℝ) (hw : w∈E) : |w-v| < A/(n+1:ℕ) ∨ (Nat.log b n:ℝ) < |w-v| := by
    by_contra! hh
    have hfit := affordable_add_time G (x := -v) (y := w) (i:=s) (j:=s) (hv.neg_time G) hw
    rw [show -v+w=w-v by ring] at hfit
    obtain ⟨z,hz,C,hC,he⟩ := hfit
    have hbad := hn (w-v) ((div_le_iff₀ hN).mp hh.1) hh.2 (s+s)
      ⟨z,hz,C,hC,he.trans (by norm_num)⟩
    simp only [Nat.cast_add,Nat.cast_one] at hbad hs
    linarith only [hbad,hs]
  exact ⟨gap,LocalEcho.occupation_of_forbidden_lags E _ _ (div_nonneg hA.le hN.le)
    (Nat.cast_pos.mpr hlog) gap⟩

#print axioms gaussian_logarithmic_from_startup
#print axioms gaussian_logarithmic_occupation
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
