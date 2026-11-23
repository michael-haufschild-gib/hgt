import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.AnchoredSublevel
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.GaussianSlices

/-! # Releasing a calibrated Gaussian field -/
open MeasureTheory ProbabilityTheory Set Function
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- Each real one-field restriction extends to an entire function obeying
the same envelope, regardless of the real values of the other fields. -/
def EntireFieldSlice {n : ℕ} (F : (Fin n → ℝ) → ℝ) (M : ℝ → ℝ) (i : Fin n) : Prop :=
  ∀ x : Fin n → ℝ, ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
    (∀ t : ℝ, f (t:ℂ) = (F (update x i t):ℂ)) ∧ ∀ z : ℂ, ‖f z‖≤M ‖z‖

/-- A uniform bound on real one-dimensional sublevel sets transfers to
a Gaussian coordinate with all other coordinates integrated out. -/
theorem gaussian_release_field_at {b h δ ε : ℝ} (M : ℝ → ℝ)
    (hs : ∀ (f : ℂ → ℂ), Differentiable ℂ f → (∀ x : ℝ, (f x).im=0) →
      (∀ z : ℂ, ‖f z‖≤M ‖z‖) → ∀ u : ℝ, |u|≤b → h≤|(f u).re| →
      volume.real {x ∈ Ioo (-b) b | |(f (x:ℂ)).re|≤ε} ≤ δ) :
    ∀ {n : ℕ} (F : (Fin n → ℝ) → ℝ), Continuous F →
      ∀ i : Fin n, EntireFieldSlice F M i → ∀ u : ℝ, |u|≤b →
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        {x | x i ∈ Ioo (-b) b ∧ h≤|F (update x i u)| ∧ |F x|≤ε} ≤ ENNReal.ofReal δ := by
  intro n F hc i ha u hu
  have hc' : Continuous (fun x : Fin n → ℝ => F (update x i u)) := by
    apply hc.comp
    apply continuous_pi
    intro j
    by_cases hj : j=i
    · subst j
      simpa only [update_self] using (continuous_const (y := u) : Continuous (fun _ : Fin n → ℝ => u))
    · simpa only [update_of_ne hj] using (continuous_apply j : Continuous (fun x : Fin n → ℝ => x j))
  apply SpectralJets.gaussian_update_slices i _ ((measurableSet_Ioo.preimage (measurable_pi_apply i)).inter
    ((isClosed_le continuous_const hc'.abs).measurableSet.inter (isClosed_le hc.abs continuous_const).measurableSet))
  intro x
  obtain ⟨f,hf,he,hg⟩ := ha x
  change volume {t : ℝ | update x i t i∈Ioo (-b) b ∧ h≤|F (update (update x i t) i u)| ∧
    |F (update x i t)|≤ε} ≤ ENNReal.ofReal δ
  simp only [update_self,update_idem]
  by_cases hx : h≤|F (update x i u)|
  · simp only [hx,true_and]
    have hv := hs f hf (fun t => by rw [he]; rfl) hg u hu (by simpa only [he,Complex.ofReal_re] using hx)
    simp only [he,Complex.ofReal_re] at hv
    let S := {t ∈ Ioo (-b) b | |F (update x i t)|≤ε}
    have hfin : volume S ≠ ⊤ := measure_ne_top_of_subset (fun t ht => ht.1 : S ⊆ Ioo (-b) b)
      (by simp)
    exact (ENNReal.ofReal_toReal hfin).ge.trans (ENNReal.ofReal_le_ofReal hv)
  · simp [hx]

/-- Replacing one calibrated coordinate costs at most `δ` probability on a
bounded interval. Other coordinates can already be random. -/
theorem gaussian_release_field {b h δ : ℝ} (hb : 0<b) (hh : 0<h) (hδ : 0<δ)
    (M : ℝ → ℝ) (hM : ∀ R, 0≤M R) :
    ∃ ε : ℝ, 0<ε ∧ ∀ {n : ℕ} (F : (Fin n → ℝ) → ℝ), Continuous F →
      ∀ i : Fin n, EntireFieldSlice F M i → ∀ u : ℝ, |u|≤b →
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        {x | x i ∈ Ioo (-b) b ∧ h≤|F (update x i u)| ∧ |F x|≤ε} ≤ ENNReal.ofReal δ := by
  obtain ⟨ε,hε,hs⟩ := anchored_sublevel hb hh hδ M hM
  exact ⟨ε,hε,gaussian_release_field_at M hs⟩

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
