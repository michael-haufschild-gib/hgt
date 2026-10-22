import GaloisForLFunctions.RHTower.Deninger.DeningerDlogPeriod

/-!
# Independence of the logarithmic differentials

No nonzero combination of the logarithmic differentials of the coordinates of a character stage is
exact: restricting a primitive to the loop in one coordinate produces a primitive of a multiple of
`z⁻¹` on the punctured plane, and the period `2πi` forces that multiple to vanish.  So the classes
`d log P(a)` are linearly independent in the first cohomology of a stage, which is the injectivity
half of the identification of the cohomology with the exterior algebra on the lattice.

* `deningerCoordLoop` : the loop through one coordinate of the stage.
* `deningerDlogForm_independent` : a combination of logarithmic differentials is exact only if all
  its coefficients vanish.
-/

namespace RHTower

section Independence

variable {r : ℕ}

/-- **The loop through one coordinate** of the stage, with the other coordinates equal to one. -/
def deningerCoordLoop (r : ℕ) (i : Fin r) (w : ℂ) : Fin r → ℂ :=
  Function.update (fun _ => (1 : ℂ)) i w

theorem deningerCoordLoop_apply_self (i : Fin r) (w : ℂ) : deningerCoordLoop r i w i = w := by
  simp [deningerCoordLoop]

theorem deningerCoordLoop_mem (i : Fin r) {w : ℂ} (hw : w ≠ 0) :
    deningerCoordLoop r i w ∈ deningerStageTorus r := by
  intro l
  rcases eq_or_ne l i with rfl | h
  · simpa [deningerCoordLoop] using hw
  · simp [deningerCoordLoop, h]

theorem deningerCoordLoop_eq (i : Fin r) :
    deningerCoordLoop r i =
      fun w : ℂ => (fun _ => (1 : ℂ)) + (w - 1) • (Pi.single i (1 : ℂ) : Fin r → ℂ) := by
  funext w l
  rcases eq_or_ne l i with rfl | hl
  · simp [deningerCoordLoop]
  · simp [deningerCoordLoop, hl]

/-- **The loop is a holomorphic curve** with constant derivative the corresponding basis vector. -/
theorem deningerCoordLoop_hasDerivAt (i : Fin r) (w : ℂ) :
    HasDerivAt (deningerCoordLoop r i) (Pi.single i (1 : ℂ) : Fin r → ℂ) w := by
  rw [deningerCoordLoop_eq]
  have h := ((hasDerivAt_id w).sub_const 1).smul_const (Pi.single i (1 : ℂ) : Fin r → ℂ)
  rw [one_smul] at h
  exact h.const_add _

/-- **A combination of the logarithmic differentials is exact only if it vanishes**: the classes
`d log P(a)` are independent in the first cohomology of a character stage. -/
theorem deningerDlogForm_independent (c : Fin r → ℂ) (i : Fin r) (H : DeningerStageForm r 0)
    (hH : DeningerIsHolomorphicForm H)
    (hd : ∀ z ∈ deningerStageTorus r, extDeriv H z = ∑ j, c j • deningerDlogForm r j z) :
    c i = 0 := by
  refine deningerDlogScalar_not_exact
    (f := fun w => H (deningerCoordLoop r i w) (fun l : Fin 0 => l.elim0)) ?_
  intro w hw
  set z : Fin r → ℂ := deningerCoordLoop r i w with hz
  have hzΩ : z ∈ deningerStageTorus r := deningerCoordLoop_mem i hw
  have hdiff : DifferentiableAt ℂ H z := (hH z hzΩ).differentiableAt
  have hH'diff : DifferentiableAt ℂ (fun y => H y (fun l : Fin 0 => l.elim0)) z :=
    hdiff.continuousAlternatingMap_apply fun l : Fin 0 => l.elim0
  have hempty : ∀ w₀ w₁ : Fin 0 → (Fin r → ℂ), w₀ = w₁ := fun _ _ => funext fun l => l.elim0
  have hval : extDeriv H z (fun _ : Fin 1 => (Pi.single i (1 : ℂ) : Fin r → ℂ)) =
      fderiv ℂ (fun y => H y (fun l : Fin 0 => l.elim0)) z
        (Pi.single i (1 : ℂ) : Fin r → ℂ) := by
    rw [extDeriv_apply hdiff]
    rw [Finset.sum_eq_single (0 : Fin 1)]
    · rw [hempty (Fin.removeNth 0 fun _ : Fin 1 => (Pi.single i (1 : ℂ) : Fin r → ℂ))
        (fun l : Fin 0 => l.elim0)]
      simp
    · intro b _ hb
      exact absurd (Subsingleton.elim b 0) hb
    · intro hb
      exact absurd (Finset.mem_univ (0 : Fin 1)) hb
  have hrhs : (∑ j, c j • deningerDlogForm r j z)
      (fun _ : Fin 1 => (Pi.single i (1 : ℂ) : Fin r → ℂ)) = c i * w⁻¹ := by
    rw [ContinuousAlternatingMap.sum_apply]
    rw [Finset.sum_eq_single i]
    · show c i * ((z i)⁻¹ * (Pi.single i (1 : ℂ) : Fin r → ℂ) i) = c i * w⁻¹
      rw [hz, deningerCoordLoop_apply_self]
      simp
    · intro b _ hb
      show c b * ((z b)⁻¹ * (Pi.single i (1 : ℂ) : Fin r → ℂ) b) = 0
      rw [Pi.single_apply, if_neg hb]
      ring
    · intro hb
      exact absurd (Finset.mem_univ i) hb
  have hkey : fderiv ℂ (fun y => H y (fun l : Fin 0 => l.elim0)) z
      (Pi.single i (1 : ℂ) : Fin r → ℂ) = c i * w⁻¹ := by
    rw [← hval, hd z hzΩ, hrhs]
  have hcomp := hH'diff.hasFDerivAt.comp_hasDerivAt w (deningerCoordLoop_hasDerivAt i w)
  rw [hkey] at hcomp
  exact hcomp

end Independence

end RHTower
