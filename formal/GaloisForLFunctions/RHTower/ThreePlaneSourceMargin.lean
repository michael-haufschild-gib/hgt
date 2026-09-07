import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
/-!
# Uniform margins for three planar source directions

Strict directional coverage has a positive uniform margin on the unit sphere.
Independent perturbations within one quarter of that margin retain half of it.
This supplies the tolerance needed when exact child profiles are copied at
clipped prime-quotient endpoints.
-/

noncomputable section
open Set Metric
namespace RHTower

/-- A finite strict spanning family of planar directions has a uniform directional margin. -/
theorem exists_threePlaneSource_margin (v₀ v₁ v₂ : ℝ × ℝ)
    (hv : ∀ z : ℝ × ℝ,z≠0 →
      0<max (z.1*v₀.1+z.2*v₀.2) (max (z.1*v₁.1+z.2*v₁.2) (z.1*v₂.1+z.2*v₂.2))) :
    ∃ c : ℝ,0<c ∧ ∀ z : ℝ × ℝ,
      c*‖z‖≤max (z.1*v₀.1+z.2*v₀.2)
        (max (z.1*v₁.1+z.2*v₁.2) (z.1*v₂.1+z.2*v₂.2)) := by
  let F : ℝ × ℝ → ℝ := fun z => max (z.1*v₀.1+z.2*v₀.2)
    (max (z.1*v₁.1+z.2*v₁.2) (z.1*v₂.1+z.2*v₂.2))
  have hcont : Continuous F := by dsimp [F]; fun_prop
  have hne : (sphere (0:ℝ × ℝ) 1).Nonempty := by
    refine ⟨(1,0),?_⟩
    simp [Prod.norm_def]
  obtain ⟨z₀,hz₀,hmin⟩ := (isCompact_sphere (0:ℝ × ℝ) 1).exists_isMinOn hne hcont.continuousOn
  have hz₀norm : ‖z₀‖=1 := by simpa only [mem_sphere,dist_zero_right] using hz₀
  have hz₀ne : z₀≠0 := by intro h; simp [h] at hz₀norm
  refine ⟨F z₀,hv z₀ hz₀ne,?_⟩
  intro z
  by_cases hz : z=0
  · subst z; simp [F]
  have hn : 0<‖z‖ := norm_pos_iff.mpr hz
  have hunit : ‖z‖⁻¹ • z∈sphere (0:ℝ × ℝ) 1 := by
    simp [norm_smul,hn.ne']
  have hh : F z₀≤F (‖z‖⁻¹ • z) := hmin hunit
  have hscale : F (‖z‖⁻¹ • z)=‖z‖⁻¹*F z := by
    dsimp [F]
    simp only [mul_assoc,← mul_add]
    simp only [mul_max_of_nonneg _ _ (inv_nonneg.mpr hn.le)]
  rw [hscale] at hh
  have hm := mul_le_mul_of_nonneg_left hh hn.le
  have he : ‖z‖*(‖z‖⁻¹*F z)=F z := by field_simp
  rw [he] at hm
  change F z₀*‖z‖≤F z
  simpa only [mul_comm] using hm

/-- Planar pairing bound in the product norm, retaining both coordinates. -/
theorem abs_planePairing_le (z d : ℝ × ℝ) :
    |z.1*d.1+z.2*d.2|≤2*‖z‖*‖d‖ := by
  have h1 : |z.1| * |d.1|≤‖z‖*‖d‖ :=
    mul_le_mul (by simpa using norm_fst_le z) (by simpa using norm_fst_le d)
      (abs_nonneg _) (norm_nonneg _)
  have h2 : |z.2| * |d.2|≤‖z‖*‖d‖ :=
    mul_le_mul (by simpa using norm_snd_le z) (by simpa using norm_snd_le d)
      (abs_nonneg _) (norm_nonneg _)
  have h := abs_add_le (z.1*d.1) (z.2*d.2)
  rw [abs_mul,abs_mul] at h
  linarith

/-- Independent small perturbations preserve half of a finite planar source margin. -/
theorem threePlaneSource_margin_perturb (v₀ v₁ v₂ w₀ w₁ w₂ : ℝ × ℝ) (c : ℝ)
    (_hc : 0<c)
    (hv : ∀ z : ℝ × ℝ,c*‖z‖≤max (z.1*v₀.1+z.2*v₀.2)
      (max (z.1*v₁.1+z.2*v₁.2) (z.1*v₂.1+z.2*v₂.2)))
    (h₀ : ‖w₀-v₀‖≤c/4) (h₁ : ‖w₁-v₁‖≤c/4) (h₂ : ‖w₂-v₂‖≤c/4)
    (z : ℝ × ℝ) :
    (c/2)*‖z‖≤max (z.1*w₀.1+z.2*w₀.2)
      (max (z.1*w₁.1+z.2*w₁.2) (z.1*w₂.1+z.2*w₂.2)) := by
  have step (v w : ℝ × ℝ) (hw : ‖w-v‖≤c/4) :
      z.1*v.1+z.2*v.2≤z.1*w.1+z.2*w.2+(c/2)*‖z‖ := by
    have h := abs_planePairing_le z (w-v)
    have hh := mul_le_mul_of_nonneg_left hw (show 0≤2*‖z‖ by positivity)
    have hl := neg_abs_le (z.1*(w-v).1+z.2*(w-v).2)
    dsimp only [Prod.fst_sub,Prod.snd_sub] at h hl
    nlinarith only [h,hh,hl]
  have a := step v₀ w₀ h₀
  have b := step v₁ w₁ h₁
  have d := step v₂ w₂ h₂
  have hh := hv z
  have m₀ := le_max_left (z.1*w₀.1+z.2*w₀.2) (max (z.1*w₁.1+z.2*w₁.2) (z.1*w₂.1+z.2*w₂.2))
  have m₁ := (le_max_left (z.1*w₁.1+z.2*w₁.2) (z.1*w₂.1+z.2*w₂.2)).trans
    (le_max_right (z.1*w₀.1+z.2*w₀.2) _)
  have m₂ := (le_max_right (z.1*w₁.1+z.2*w₁.2) (z.1*w₂.1+z.2*w₂.2)).trans
    (le_max_right (z.1*w₀.1+z.2*w₀.2) _)
  rcases le_max_iff.mp hh with h|h
  · linarith only [a,m₀,h]
  · rcases le_max_iff.mp h with h|h
    · linarith only [b,m₁,h]
    · linarith only [d,m₂,h]

end RHTower
