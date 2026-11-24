import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.IntervalMinima.RecordHeights
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.IntervalMinima.WindowScale
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.QuadraticBits

/-! # Same-error complexity variation throughout a superexponential interval -/

open Set Filter MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
open MaximumIntervals
noncomputable section

/-- On a window of 2^(N(floor(sqrt N)+2))/2 physical time units,
every affordable date centers a D^γ/2 interval with at most D^α extra
gates at the very same tolerance. The error can avoid one zero-dimensional
set after the observation origins are chosen. -/
theorem gaussian_local_windows (γ α : ℝ) (hγ : 0 ≤ γ) (hγα : γ < α) (hα : α ≤ 1) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a : ℕ → ℝ, ∃ E : Set ℝ, dimH E=0 ∧
      ∀ e > (0:ℝ), e ∉ E → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        ∀ v ∈ Ico (a k) (a k+(2:ℝ)^(windowBits k)/2), ∀ s : ℕ,
          HasProjectiveCircuitApproximation N e s (unitaryEvolution H.val v) →
          ∀ t : ℝ, |t-v| ≤ (2:ℝ)^(γ*(N:ℝ))/2 →
            HasProjectiveCircuitApproximation N e (s+⌊(2:ℝ)^(α*(N:ℝ))⌋₊) (unitaryEvolution H.val t) := by
  obtain ⟨m,hm,hcompile⟩ := LocalPatches.gaussian_quadratic_precision_compiler γ α hγ hγα hα
  filter_upwards [hcompile] with ω hω a
  let u (k i : ℕ) := a k+(i:ℝ)/2
  let E := intervalExceptional ω u (fun _ _ => 1/2) windowBits
  obtain ⟨hE,hreg⟩ := interval_clearance ω u (fun _ _ => 1/2) windowBits
    windowBits_strictMono prefix_le_windowBits
  refine ⟨E,hE,?_⟩
  intro e he hr
  obtain ⟨q,hq⟩ := hreg e he hr
  filter_upwards [hω,hq,windowBits_le_precision q m hm] with k hsim hcell hbits
  intro N H v hv s hfit t hlag
  let δ := 1/(2:ℝ)^(q*windowBits k)
  let h := 1/(2:ℝ)^((N/m)^2)
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hbudget : h ≤ δ := one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hbits)
  let i := ⌊2*(v-a k)⌋₊
  have hnon : 0 ≤ 2*(v-a k) := mul_nonneg zero_le_two (sub_nonneg.mpr hv.1)
  have hi : i < 2^(windowBits k) := (Nat.floor_lt hnon).mpr (by
    push_cast; linarith only [hv.2])
  have hvI : v ∈ Icc (u k i) (u k i+max (1/2:ℝ) 0) := by
    have h₁ := Nat.floor_le hnon
    have h₂ := Nat.lt_floor_add_one (2*(v-a k))
    change (i:ℝ) ≤ 2*(v-a k) at h₁
    change 2*(v-a k) < (i:ℝ)+1 at h₂
    rw [max_eq_left (by norm_num : (0:ℝ) ≤ 1/2)]
    dsimp only [u]
    exact ⟨by linarith only [h₁],by linarith only [h₂]⟩
  obtain ⟨z,hz,F,hF,herr⟩ := hfit
  obtain ⟨w,hw,hfit'⟩ := hcell i hi s v hvI ⟨z,hz,F,hF,herr.trans (le_add_of_nonneg_right hδ)⟩
  have hnear : |v-w| ≤ 1/2 := by
    rw [max_eq_left (by norm_num : (0:ℝ) ≤ 1/2)] at hvI hw
    exact abs_le.mpr ⟨by linarith only [hvI.1,hw.2],by linarith only [hvI.2,hw.1]⟩
  have hradius : 1 ≤ (2:ℝ)^(γ*(N:ℝ)) := one_le_rpow (by norm_num) (mul_nonneg hγ (Nat.cast_nonneg N))
  have hdist : |t-w| ≤ (2:ℝ)^(γ*(N:ℝ)) := by
    have ht := abs_add_le (t-v) (v-w)
    rw [sub_add_sub_cancel] at ht
    linarith only [ht,hlag,hnear,hradius]
  obtain ⟨z',hz',F',hF',herr'⟩ := affordable_add_time H hfit' (hsim _ hdist)
  rw [show w+(t-w)=t by ring] at herr'
  exact ⟨z',hz',F',hF',herr'.trans (by change e-δ+h ≤ e; linarith only [hbudget])⟩

#print axioms gaussian_local_windows
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
