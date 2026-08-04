import GaloisForLFunctions.HTGeometry.WaveDecayingCompactSupport

/-!
# The decay hypothesis is a genuine restriction

The estimate for decaying solutions is only as strong as its hypothesis class is wide, and the
previous file shows the class contains every compactly supported solution. It does **not** contain
every bounded one: the constant field solves the free clock equation, and its energy density is the
constant `1`, which is not integrable over a space of positive dimension. So finiteness of the
energy is an assumption about the solution, not a consequence of solving the equation — and a
construction that produces merely *bounded* solutions, as a Fourier synthesis does, has to prove
decay separately before the estimate applies to it.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Sharp

variable {d : ℕ}

theorem contDiff_one_field : ContDiff ℝ ∞ fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ) := contDiff_const

theorem waveDirDeriv_one_field (v p : ℝ × (Fin d → ℝ)) :
    waveDirDeriv v (fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ)) p = 0 := by
  rw [waveDirDeriv, fderiv_fun_const]
  rfl

/-- **The constant field solves the free clock equation.** -/
theorem solvesWaveEq_one_field :
    SolvesWaveEq (fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ))
      (fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)) := by
  intro p
  have hz : ∀ v : ℝ × (Fin d → ℝ),
      waveDirDeriv v (fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ)) = fun _ => (0 : ℝ) := by
    intro v
    funext q
    exact waveDirDeriv_one_field v q
  show waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d)
      fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ)) p
    = (∑ i : Fin d, waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i)
        fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ)) p) + 0 * 1
  rw [hz (timeDir d), Finset.sum_congr rfl fun i _ => by rw [hz (spaceDir d i)]]
  simp [waveDirDeriv, fderiv_fun_const]

theorem energyDensity_one_field (p : ℝ × (Fin d → ℝ)) :
    energyDensity (fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ)) p = 1 := by
  rw [energyDensity, waveDirDeriv_one_field,
    Finset.sum_congr rfl fun i _ => by rw [waveDirDeriv_one_field]]
  simp

/-- **The constant field has non-integrable energy density in positive dimension.** -/
theorem not_integrable_energyDensity_one_field (hd : 0 < d) (t : ℝ) :
    ¬ Integrable (fun x : Fin d → ℝ =>
        energyDensity (fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ)) (t, x))
      (volume : Measure (Fin d → ℝ)) := by
  intro hint
  have hone : Integrable (fun _ : Fin d → ℝ => (1 : ℝ)) (volume : Measure (Fin d → ℝ)) := by
    refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    exact energyDensity_one_field (t, x)
  have hvol : (volume : Measure (Fin d → ℝ)) Set.univ = ⊤ := by
    have hne : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    simp
  rcases (integrable_const_iff (μ := (volume : Measure (Fin d → ℝ))) (c := (1 : ℝ))).mp hone with
    h | h
  · exact one_ne_zero h
  · have hfin := h.measure_univ_lt_top
    rw [hvol] at hfin
    exact absurd hfin (lt_irrefl ⊤)

/-- **So the decay hypothesis is not implied by solving the equation.** -/
theorem not_decayingSolution_one_field (hd : 0 < d) :
    ¬ DecayingSolution (fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ))
        (fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)) := by
  intro h
  exact not_integrable_energyDensity_one_field hd 0 (h.energyInt 0)

end Sharp

end GaloisForLFunctions.HTGeometry
