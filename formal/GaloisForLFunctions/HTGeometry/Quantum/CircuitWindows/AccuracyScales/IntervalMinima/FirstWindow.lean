import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.IntervalMinima.FirstWait
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.ExponentialCompiler

/-! # Affordable intervals near the chronological first return at regular tolerances -/

open Filter Set Real MeasureTheory
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
open MaximumIntervals PrecisionReturns
noncomputable section

/-- At the same fixed error, every first visit has a subsequent center
within logarithmic waiting-time excess D⁻ᵇ around which a whole interval
of radius D^γ needs at most D^α extra gates. The origin can be the
first robust crossing of the frozen path. -/
theorem gaussian_first_return_window (b : ℕ) :
    ∃ C : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a : ℕ → ℝ,
      let E := waitExceptional ω a C b
      dimH E=0 ∧ ∀ e > (0:ℝ), e ∉ E → ∀ γ α : ℝ, 0 ≤ γ → γ < α → α ≤ 1 → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        ∀ s : ℕ, let v := firstVisit H (a k) s e
          ∃ w ≥ v, 1+(w-a k) ≤ (1+(v-a k))*exp (1/(2:ℝ)^(b*N)) ∧
            ∀ t : ℝ, |t-w| ≤ (2:ℝ)^(γ*(N:ℝ)) →
              HasProjectiveCircuitApproximation N e (s+⌊(2:ℝ)^(α*(N:ℝ))⌋₊)
                (unitaryEvolution H.val t) := by
  obtain ⟨C,hC⟩ := gaussian_first_wait_tolerance b
  refine ⟨C,?_⟩
  filter_upwards [hC,LocalPatches.gaussian_exponential_precision_compiler]
    with ω hw hsim a
  intro E
  obtain ⟨hE,hreg⟩ := hw a
  refine ⟨hE,?_⟩
  intro e he hr γ α hγ hγα hα
  obtain ⟨c,hc⟩ := hreg e he hr
  obtain ⟨K,hK⟩ := exists_nat_gt (2/e)
  filter_upwards [hc,hsim (c+1) γ α hγ hγα hα,eventually_ge_atTop K] with k hw hsim hk
  intro N H s v
  let h := min (e/2) (1/(2:ℝ)^(c*N))
  let δ := 1/(2:ℝ)^((c+1)*N)
  have hp : 0 < h := lt_min (half_pos he) (by positivity)
  have heh : 0 < e-h := sub_pos.mpr ((min_le_left ..).trans_lt (half_lt_self he))
  have hδ : δ ≤ h := by
    have hN : k ≤ (c+1)*N := (show k ≤ N by dsimp only [N]; omega).trans
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    have hn : K ≤ 2^((c+1)*N) := hk.trans (hN.trans (Nat.lt_two_pow_self (n:=(c+1)*N)).le)
    have hh : 2/e ≤ (2:ℝ)^((c+1)*N) := hK.le.trans (by exact_mod_cast hn)
    rw [div_le_iff₀ he] at hh
    apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^((c+1)*N))).mpr
      linarith only [hh]
    · apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right N (Nat.le_succ _))
  let w := firstVisit H (a k) s (e-h)
  obtain ⟨hw',z,hz,F,hF,herr⟩ := (firstVisit_isLeast H (a k) s heh).1
  have hv := firstVisit_isLeast H (a k) s he
  have hvw : v ≤ w := hv.2 ⟨hw',z,hz,F,hF,herr.trans (sub_le_self _ hp.le)⟩
  have hcoarse := firstVisit_isLeast H (a k) s (add_pos he hp)
  obtain ⟨ht,z',hz',F',hF',herr'⟩ := hv.1
  have hsv := hcoarse.2 ⟨ht,z',hz',F',hF',herr'.trans (le_add_of_nonneg_right hp.le)⟩
  have hh := (hw s).2
  refine ⟨w,hvw,hh.trans (mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (sub_le_sub_right hsv _)) (exp_pos _).le),?_⟩
  intro t hlag
  have h1 : HasProjectiveCircuitApproximation N (e-h) s (unitaryEvolution H.val w) :=
    ⟨z,hz,F,hF,herr⟩
  obtain ⟨z',hz',C,hC,he'⟩ := affordable_add_time H h1 (hsim (t-w) hlag)
  rw [show w+(t-w)=t by ring] at he'
  exact ⟨z',hz',C,hC,he'.trans (by change e-h+δ ≤ e; linarith only [hδ])⟩

#print axioms gaussian_first_return_window
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
