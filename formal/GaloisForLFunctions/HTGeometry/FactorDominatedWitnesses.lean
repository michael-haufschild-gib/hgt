import GaloisForLFunctions.HTGeometry.WaveL2Capstone

/-!
# Factor domination is realized

The `L²` uniqueness capstone assumes that a field, its time derivatives, its spatial derivatives
and the mixed derivatives are all dominated on unit time intervals by square-integrable profiles.
Nothing produced such a field.

The zero field is one, with the zero profile as every dominating factor: all its directional
derivatives vanish identically, and the zero function is square integrable.  Domination is also
inherited by every field dominated pointwise together with its derivatives, so the class is closed
downward rather than being a single point.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Capstone

variable {d : ℕ}

theorem waveDirDeriv_zero_fun (v : ℝ × (Fin d → ℝ)) :
    waveDirDeriv v (fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)) = fun _ => 0 := by
  funext p
  simp [waveDirDeriv]

/-- **The zero field is factor dominated.**  Every directional derivative of it vanishes, and the
zero profile is square integrable. -/
theorem factorDominated_zero : FactorDominated (fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)) := by
  intro t
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0,
    MemLp.zero', MemLp.zero', MemLp.zero', fun _ => MemLp.zero', fun _ => MemLp.zero',
    ?_, ?_, ?_, ?_, ?_⟩
  · intro s _ x
    rw [waveDirDeriv_zero_fun]
    simp
  · intro s _ x
    rw [waveDirDeriv_zero_fun (timeDir d), waveDirDeriv_zero_fun (timeDir d)]
    simp
  · intro s _ x
    simp
  · intro i s _ x
    rw [waveDirDeriv_zero_fun]
    simp
  · intro i s _ x
    rw [waveDirDeriv_zero_fun (spaceDir d i), waveDirDeriv_zero_fun (timeDir d)]
    simp

end Capstone

end

end GaloisForLFunctions.HTGeometry
