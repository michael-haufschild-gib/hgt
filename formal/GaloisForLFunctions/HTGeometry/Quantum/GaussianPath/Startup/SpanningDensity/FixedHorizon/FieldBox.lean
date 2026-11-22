import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.FieldSlices

/-! # Uniform calibrated signals under finitely many Gaussian fields -/
open MeasureTheory ProbabilityTheory Set Function
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- Release the first `k` fields while retaining the calibration elsewhere. -/
private def release {n : ℕ} (k : ℕ) (u x : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i.val<k then x i else u i

private theorem continuous_release {n : ℕ} (k : ℕ) (u : Fin n → ℝ) : Continuous (release k u) := by
  apply continuous_pi
  intro i
  by_cases h : i.val<k
  · simpa only [release,if_pos h] using (continuous_apply i : Continuous (fun x : Fin n → ℝ => x i))
  · simpa only [release,if_neg h] using (continuous_const (y := u i) : Continuous (fun _ : Fin n → ℝ => u i))

private theorem release_update {n : ℕ} (i : Fin n) (u x : Fin n → ℝ) (t : ℝ) :
    release (i.val+1) u (update x i t) = update (release i.val u x) i t := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [release]
  · have hv : j.val ≠ i.val := fun h => hj (Fin.ext h)
    have he : j.val < i.val+1 ↔ j.val < i.val := by omega
    simp only [release,he,update_of_ne hj]

private theorem release_calibration {n : ℕ} (i : Fin n) (u x : Fin n → ℝ) :
    release (i.val+1) u (update x i (u i)) = release i.val u x := by
  rw [release_update]
  funext j
  by_cases hj : j=i
  · subst j; simp [release]
  · exact update_of_ne hj ..

/-- From a signal at one calibration, releasing `n` coordinates loses at
most `n*δ` probability within the box. Thresholds depend only on the common
one-variable envelope, the box, and the calibration strength. -/
theorem gaussian_field_box (n : ℕ) {b h δ : ℝ} (hb : 0<b) (hh : 0<h) (hδ : 0<δ)
    (M : ℝ → ℝ) (hM : ∀ R, 0≤M R) :
    ∃ ε : ℝ, 0<ε ∧ ∀ (F : (Fin n → ℝ) → ℝ), Continuous F → (∀ i, EntireFieldSlice F M i) →
      ∀ (u : Fin n → ℝ), (∀ i, |u i|≤b) → h≤|F u| →
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        {x | (∀ i, x i ∈ Ioo (-b) b) ∧ |F x|≤ε} ≤ n * ENNReal.ofReal δ := by
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let B := {x : Fin n → ℝ | ∀ i, x i ∈ Ioo (-b) b}
  have steps (k : ℕ) (hk : k≤n) : ∃ r : ℝ, 0<r ∧ ∀ (F : (Fin n → ℝ) → ℝ),
      Continuous F → (∀ i, EntireFieldSlice F M i) → ∀ u, (∀ i, |u i|≤b) → h≤|F u| →
      μ {x ∈ B | |F (release k u x)| ≤ r} ≤ k*ENNReal.ofReal δ := by
    induction k with
    | zero =>
      refine ⟨h/2,by positivity,?_⟩
      intro F _ _ u _ hu
      have he (x : Fin n → ℝ) : release 0 u x = u := by ext; simp [release]
      have hlo : ¬|F u|≤h/2 := by linarith only [hu,hh]
      simp [he,hlo]
    | succ k ih =>
      let i : Fin n := ⟨k,by omega⟩
      obtain ⟨r,hr,hold⟩ := ih (by omega)
      obtain ⟨s,hs,hnew⟩ := gaussian_release_field hb hr hδ M hM
      refine ⟨s,hs,?_⟩
      intro F hc hf u hu hcal
      let G := F ∘ release (k+1) u
      have hslice : EntireFieldSlice G M i := by
        intro x
        obtain ⟨f,hf',he,hg⟩ := hf i (release k u x)
        refine ⟨f,hf',fun t => ?_,hg⟩
        rw [he]
        change _ = (F (release (i.val+1) u (update x i t)):ℂ)
        rw [release_update]
      have h1 := hold F hc hf u hu hcal
      have h2 := hnew G (hc.comp (continuous_release _ _)) i hslice (u i) (hu i)
      refine (measure_mono (t :=
        {x ∈ B | |F (release k u x)|≤r} ∪
        {x | x i ∈ Ioo (-b) b ∧ r ≤ |G (update x i (u i))| ∧ |G x| ≤ s}) ?_).trans
        ((measure_union_le _ _).trans ((add_le_add h1 h2).trans_eq ?_))
      · rintro x ⟨hx,hsig⟩
        rcases le_total |F (release k u x)| r with hr'|hr'
        · exact Or.inl ⟨hx,hr'⟩
        · exact Or.inr ⟨hx i,by simpa only [G,Function.comp_apply,release_calibration i u x] using hr',hsig⟩
      · rw [Nat.cast_succ,add_mul,one_mul]
  obtain ⟨ε,hε,ht⟩ := steps n le_rfl
  refine ⟨ε,hε,?_⟩
  intro F hc hf u hu hcal
  have he (x : Fin n → ℝ) : release n u x=x := by funext j; simp only [release,if_pos j.isLt]
  simpa only [he] using ht F hc hf u hu hcal

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
