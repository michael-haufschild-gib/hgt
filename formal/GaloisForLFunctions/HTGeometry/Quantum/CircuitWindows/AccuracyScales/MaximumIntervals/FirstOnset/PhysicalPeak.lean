import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.FirstOnset.MeshPeaks
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.DatedIntervals

/-! # A near-maximum interval localized at the first physical threshold contact -/

open Filter Set MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals.FirstOnset
noncomputable section

/-- From each chosen origin, let v be the first date at which the
distance to the (m−1)-gate set reaches the tolerance. Here m is the
actual maximum. Within D⁻ᵇ of v in log waiting time there is an exact
maximizer supporting a full exponential interval near that maximum. -/
theorem gaussian_first_peak_interval (b : ℕ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a : ℕ → ℝ, ∃ E : Set ℝ, dimH E=0 ∧
      ∀ e ∈ Ioc (0:ℝ) (11/25), e ∉ E →
      ∀ γ α : ℝ, 0 ≤ γ → γ < α → α ≤ 1 → ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        ∃ m > nearHilbertContinuousCircuitBudget N, IsRecurrentOrbitCircuitMaximumAt H e m ∧
          ∃ v w : ℝ, IsLeast {t | a k ≤ t ∧ e ≤ orbitCircuitDistance H (m-1) t} v ∧
            v ≤ w ∧ 1+(w-a k) ≤ (1+(v-a k))*exp (1/(2:ℝ)^(b*N)) ∧
            (∀ j, HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val w) → m ≤ j) ∧
            ∀ t : ℝ, |t-w| ≤ (2:ℝ)^(γ*(N:ℝ)) → ∀ j,
              HasProjectiveCircuitApproximation N e j (unitaryEvolution H.val t) →
                m ≤ j+⌊(2:ℝ)^(α*(N:ℝ))⌋₊ := by
  obtain ⟨C,hC⟩ := gaussian_dated_same_error_maximum_intervals
  filter_upwards [hC,LocalPatches.gaussian_exponential_precision_compiler] with ω hdate hcompile a
  let E := chainExceptional ω ∪ peakExceptional ω a C b
  obtain ⟨hE,hmesh⟩ := mesh_peak_clearance ω a C b
  refine ⟨E,?_,?_⟩
  · change dimH (chainExceptional ω ∪ peakExceptional ω a C b)=0
    rw [dimH_union,hE,show dimH (chainExceptional ω)=0 from dimH_exceptionalTolerances _,sup_idem]
  intro e he hr γ α hγ hγα hα
  obtain ⟨c,hc⟩ := hmesh e (fun h => hr (Or.inr h))
  have hd := hdate e he (fun h => hr (Or.inl h)) 0 (1/2) le_rfl (by norm_num) (by norm_num)
  filter_upwards [hd,hc,hcompile c γ α hγ hγα hα] with k hmax hrec hsim
  intro N H
  obtain ⟨m,hmp,hm,hcenter⟩ := hmax
  obtain ⟨z,hz,hzmax,_⟩ := hcenter (a k)
  have hmpos : 0 < m := (Nat.zero_le _).trans_lt hmp
  let s := m-1
  have hsm : s<m := by dsimp only [s]; omega
  have hsB := hsm.trans_le (max_cap (by dsimp only [N]; omega : 2 ≤ N) H he.1.le hm)
  have hz' : e < orbitCircuitDistance H s z := by
    by_contra! hle
    exact (not_le_of_gt hsm) (hzmax s ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr hle))
  let A := Ici (a k) ∩ {t | e ≤ orbitCircuitDistance H s t}
  let v := sInf A
  have hA : IsClosed A := isClosed_Ici.inter
    (isClosed_le continuous_const (orbitCircuitDistance_lipschitz H s).continuous)
  have hAz : z ∈ A := ⟨hz.1,hz'.le⟩
  have hb : BddBelow A := ⟨a k,fun _ ht => ht.1⟩
  have hv : IsLeast A v := ⟨hA.csInf_mem ⟨z,hAz⟩ hb,fun _ hx => csInf_le hb hx⟩
  have hvz := hv.2 hAz
  obtain ⟨w,hw,hbound,hpeak⟩ := hrec s hsB v ⟨hv.1.1,hvz.trans hz.2⟩ hv.1.2
  let δ := 1/(2:ℝ)^(c*N)
  have hδ : 0≤δ := by dsimp only [δ]; positivity
  have hhard (j : ℕ) (hfit : HasProjectiveCircuitApproximation N (e+δ) j
      (unitaryEvolution H.val w)) : m ≤ j := by
    by_contra! hlt
    obtain ⟨y,hy,F,hF,herr⟩ := hfit
    have hfit' : HasProjectiveCircuitApproximation N (e+δ) s (unitaryEvolution H.val w) :=
      ⟨y,hy,F,hF.trans (by dsimp only [s]; omega),herr⟩
    exact (not_le_of_gt hpeak) ((hasProjectiveCircuitApproximation_iff_infDist ..).mp hfit')
  refine ⟨m,hmp,hm,v,w,hv,hv.2 ⟨hw,(le_add_of_nonneg_right hδ).trans hpeak.le⟩,hbound,?_,?_⟩
  · rintro j ⟨y,hy,F,hF,herr⟩
    exact hhard j ⟨y,hy,F,hF,herr.trans (le_add_of_nonneg_right hδ)⟩
  · intro t ht j hf
    have hh := affordable_add_time H hf (hsim (w-t) (by rwa [abs_sub_comm]))
    rw [show t+(w-t)=w by ring] at hh
    exact hhard _ hh

#print axioms gaussian_first_peak_interval
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals.FirstOnset
