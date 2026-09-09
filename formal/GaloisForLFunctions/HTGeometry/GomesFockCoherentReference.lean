import GaloisForLFunctions.HTGeometry.GomesFockScalarObservation

/-!
Coherent reference observations repair the scalar phase ambiguity of Fock moments.
This is the positive reconstruction survivor of the invariant-menu obstruction
in Gomes, arXiv:2607.24901v1, applied to the actual free-Fock moment functional.
Two reference directions recover a complex scalar exactly when they are real-linearly
independent and the observing state is nonzero. No state or reference assumptions
are supplied to the classifications.
-/
open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Difference between opposite coherent-reference mass observations. -/
def gomesFockReferenceContrast {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (c a : ℂ) : ℝ :=
  freeFockVectorMoment A ((c+a) • x) 0 - freeFockVectorMoment A ((c-a) • x) 0

/-- Coherent contrast is exactly the real scalar pairing with the reference, weighted by state mass. -/
theorem gomesFockReferenceContrast_formula {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (c a : ℂ) :
    gomesFockReferenceContrast A x c a =
      4*(c.re*a.re+c.im*a.im)*freeFockVectorMoment A x 0 := by
  simp only [gomesFockReferenceContrast,freeFockVectorMoment_smul]
  simp [Complex.normSq_apply]
  ring

/-- The real reference isolates the real scalar coordinate. -/
theorem gomesFockReferenceContrast_one {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (c : ℂ) :
    gomesFockReferenceContrast A x c 1 = 4*c.re*freeFockVectorMoment A x 0 := by
  simp [gomesFockReferenceContrast_formula]

/-- The imaginary reference isolates the imaginary scalar coordinate. -/
theorem gomesFockReferenceContrast_I {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (c : ℂ) :
    gomesFockReferenceContrast A x c Complex.I = 4*c.im*freeFockVectorMoment A x 0 := by
  simp [gomesFockReferenceContrast_formula]

/-- Two coherent references provide a real observation pair. -/
def gomesFockCoherentMenu {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (a b c : ℂ) : ℝ × ℝ :=
  (gomesFockReferenceContrast A x c a,gomesFockReferenceContrast A x c b)

/-- The two standard coherent references recover the scalar exactly away from the zero observing state. -/
theorem gomesFockCoherentMenu_standard_reconstruction {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (c e : ℂ) :
    gomesFockCoherentMenu A x 1 Complex.I c = gomesFockCoherentMenu A x 1 Complex.I e ↔
      c = e ∨ x = 0 := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inr hx
    · left
      have hm : freeFockVectorMoment A x 0 ≠ 0 :=
        fun hz => hx ((gomesFockVector_mass_zero_iff A x).mp hz)
      have hr := congrArg Prod.fst h
      have hi := congrArg Prod.snd h
      simp only [gomesFockCoherentMenu,gomesFockReferenceContrast_one,gomesFockReferenceContrast_I] at hr hi
      have hr' := mul_right_cancel₀ hm hr
      have hi' := mul_right_cancel₀ hm hi
      apply Complex.ext <;> linarith
  · rintro (rfl|rfl)
    · rfl
    · simp [gomesFockCoherentMenu,gomesFockReferenceContrast_formula,gomesFock_zeroVector_moment]

/-- The coherent references are sufficient exactly when their real-plane determinant and observing state are nonzero. -/
theorem gomesFockCoherentMenu_injective_iff {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (a b : ℂ) :
    Function.Injective (gomesFockCoherentMenu A x a b) ↔
      x ≠ 0 ∧ a.re*b.im-a.im*b.re ≠ 0 := by
  constructor
  · intro h
    have hx : x ≠ 0 := by
      intro hz
      subst x
      have he : (1 : ℂ) = 0 := h (by
        simp [gomesFockCoherentMenu,gomesFockReferenceContrast_formula,gomesFock_zeroVector_moment])
      exact one_ne_zero he
    refine ⟨hx,?_⟩
    intro hd
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        intro hb
        subst a b
        have he : (1 : ℂ) = 0 := h (by simp [gomesFockCoherentMenu,gomesFockReferenceContrast_formula])
        exact one_ne_zero he
      have he : b*Complex.I = 0 := h (by
        subst a
        apply Prod.ext <;>
          simp only [gomesFockCoherentMenu,gomesFockReferenceContrast_formula,
            Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.zero_re,Complex.zero_im] <;> ring)
      exact (mul_ne_zero hb Complex.I_ne_zero) he
    · have he : a*Complex.I = 0 := h (by
        apply Prod.ext
        · simp only [gomesFockCoherentMenu,gomesFockReferenceContrast_formula,
            Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.zero_re,Complex.zero_im]
          ring
        · simp only [gomesFockCoherentMenu,gomesFockReferenceContrast_formula,
            Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.zero_re,Complex.zero_im]
          linear_combination 4*(freeFockVectorMoment A x 0)*hd)
      exact (mul_ne_zero ha Complex.I_ne_zero) he
  · rintro ⟨hx,hd⟩ c e h
    have hm : freeFockVectorMoment A x 0 ≠ 0 :=
      fun hz => hx ((gomesFockVector_mass_zero_iff A x).mp hz)
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    simp only [gomesFockCoherentMenu,gomesFockReferenceContrast_formula] at ha hb
    have ha' := mul_right_cancel₀ hm ha
    have hb' := mul_right_cancel₀ hm hb
    have hreal : (a.re*b.im-a.im*b.re)*(c.re-e.re) = 0 := by
      linear_combination b.im/4*ha' - a.im/4*hb'
    have himag : (a.re*b.im-a.im*b.re)*(c.im-e.im) = 0 := by
      linear_combination a.re/4*hb' - b.re/4*ha'
    apply Complex.ext
    · exact sub_eq_zero.mp ((mul_eq_zero.mp hreal).resolve_left hd)
    · exact sub_eq_zero.mp ((mul_eq_zero.mp himag).resolve_left hd)

/-- Actual completed-Fock affine states admit unconditional phase-and-amplitude reconstruction by the two fixed references. -/
theorem gomesFockObservation_coherent_reconstruction {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (c e : ℂ) :
    gomesFockCoherentMenu (gomesCompletedFockGenerators B) (gomesFockObservationVector y) 1 Complex.I c =
      gomesFockCoherentMenu (gomesCompletedFockGenerators B) (gomesFockObservationVector y) 1 Complex.I e ↔ c = e := by
  rw [gomesFockCoherentMenu_standard_reconstruction]
  simp only [gomesFockObservationVector_ne_zero,or_false]

end GaloisForLFunctions.HTGeometry
