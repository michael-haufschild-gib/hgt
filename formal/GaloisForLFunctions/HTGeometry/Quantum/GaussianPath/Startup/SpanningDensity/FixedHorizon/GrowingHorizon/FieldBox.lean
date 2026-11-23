import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.FieldDegree
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.FieldBox

/-! # Detection through finitely many Gaussian coordinates on growing horizons -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- Releasing any fixed number of fields preserves a threshold geometric
in the time horizon, with an additive loss of δ per coordinate. -/
theorem geometric_field_box (n : ℕ) {b h δ : ℝ} (hb : 0<b) (hh : 0<h) (hδ : 0<δ) :
    ∃ s>0, ∀ L : ℕ, 0<L → ∀ F : (Fin n→ℝ)→ℝ, Continuous F →
      (∀ i, EntireFieldSlice F (fun R => Real.exp (2*L*R)) i) →
      ∀ u : Fin n→ℝ, (∀ i, |u i|≤b) → h^L≤|F u| →
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        {x | (∀ i, x i∈Ioo (-b) b) ∧ |F x|≤ s^L}≤n*ENNReal.ofReal δ := by
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let B := {x : Fin n→ℝ | ∀ i, x i∈Ioo (-b) b}
  have steps (k : ℕ) (hk : k≤n) : ∃ r>0, ∀ L : ℕ, 0<L → ∀ F : (Fin n→ℝ)→ℝ,
      Continuous F → (∀ i, EntireFieldSlice F (fun R => Real.exp (2*L*R)) i) →
      ∀ u : Fin n→ℝ, (∀ i, |u i|≤b) → h^L≤|F u| →
      μ {x ∈ B | |F (release k u x)|≤r^L}≤k*ENNReal.ofReal δ := by
    induction k with
    | zero =>
      refine ⟨h/2,by positivity,?_⟩
      intro L hL F _ _ u _ hcal
      have he (x : Fin n→ℝ) : release 0 u x=u := by ext; simp [release]
      have hlo : ¬|F u|≤(h/2)^L := ((pow_lt_pow_left₀ (half_lt_self hh) (half_pos hh).le hL.ne').trans_le hcal).not_ge
      simp [he,hlo]
    | succ k ih =>
      obtain ⟨r,hr,hold⟩ := ih (by omega)
      obtain ⟨s,hs,hnew⟩ := geometric_anchored_sublevel hb hr hδ
      refine ⟨s,hs,?_⟩
      intro L hL F hc hf u hu hcal
      have ho := hold L hL F hc hf u hu hcal
      have hn := field_box_step (k:=k) (by omega : k<n) (fun R => Real.exp (2*L*R))
        (fun G hG j hG' => gaussian_release_field_at _ (hnew L hL) G hG j hG') F hc hf u hu
      apply hn.trans ((add_le_add ho le_rfl).trans_eq ?_)
      rw [Nat.cast_succ,add_mul,one_mul]
  obtain ⟨s,hs,hw⟩ := steps n le_rfl
  refine ⟨s,hs,?_⟩
  intro L hL F hc hf u hu hcal
  have he (x : Fin n→ℝ) : release n u x=x := by funext j; simp only [release,if_pos j.isLt]
  simpa only [he,μ,B,Set.mem_setOf_eq] using hw L hL F hc hf u hu hcal

#print axioms geometric_field_box
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
