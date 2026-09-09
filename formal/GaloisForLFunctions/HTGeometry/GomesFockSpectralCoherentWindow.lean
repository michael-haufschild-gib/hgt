import GaloisForLFunctions.HTGeometry.GomesFockSpectralWindowSupport

/-!
Sharp coherent intensity reconstruction inside an actual spectral window.
Applying the invariant-menu obstruction and its positive reconstruction survivor
from Gomes, arXiv:2607.24901v1, three reference intensities recover a complex scalar
exactly whenever the observing state is outside the window kernel. Every pair of
reference intensities has a reflection ambiguity, so this three-record recovery
threshold is sharp for this observation class.
-/
open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Three actual spectral-window intensities, referenced at zero, one, and the imaginary unit. -/
def gomesFockWindowIntensityMenu {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) (c : ℂ) : ℝ × ℝ × ℝ :=
  (gomesFockWindowMass B S (c • x),gomesFockWindowMass B S ((c+1) • x),
    gomesFockWindowMass B S ((c+Complex.I) • x))

/-- Three reference intensities reconstruct phase and amplitude exactly unless this state has zero window mass. -/
theorem gomesFockWindowIntensityMenu_reconstruction {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) (c e : ℂ) :
    gomesFockWindowIntensityMenu B S x c = gomesFockWindowIntensityMenu B S x e ↔
      c = e ∨ gomesFockWindowMass B S x = 0 := by
  constructor
  · intro h
    by_cases hx : gomesFockWindowMass B S x = 0
    · exact Or.inr hx
    · left
      have h0 := congrArg (fun v : ℝ × ℝ × ℝ => v.1) h
      have h1 := congrArg (fun v : ℝ × ℝ × ℝ => v.2.1) h
      have hI := congrArg (fun v : ℝ × ℝ × ℝ => v.2.2) h
      simp only [gomesFockWindowIntensityMenu,gomesFockWindowMass_smul] at h0 h1 hI
      have h0' := mul_right_cancel₀ hx h0
      have h1' := mul_right_cancel₀ hx h1
      have hI' := mul_right_cancel₀ hx hI
      simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,
        Complex.I_re,Complex.I_im] at h0' h1' hI'
      apply Complex.ext <;> nlinarith
  · rintro (rfl|hx)
    · rfl
    · simp [gomesFockWindowIntensityMenu,gomesFockWindowMass_smul,hx]

/-- Three reference intensities are an injective scalar observation exactly at states with nonzero window mass. -/
theorem gomesFockWindowIntensityMenu_injective_iff {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    Function.Injective (gomesFockWindowIntensityMenu B S x) ↔ gomesFockWindowMass B S x ≠ 0 := by
  constructor
  · intro h hx
    have he : (0 : ℂ) = 1 := h ((gomesFockWindowIntensityMenu_reconstruction B S x 0 1).mpr (Or.inr hx))
    exact zero_ne_one he
  · intro hx c e h
    exact ((gomesFockWindowIntensityMenu_reconstruction B S x c e).mp h).resolve_right hx

/-- Any two coherently shifted spectral-window intensities. -/
def gomesFockWindowTwoReferenceMenu {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) (a b c : ℂ) : ℝ × ℝ :=
  (gomesFockWindowMass B S ((c+a) • x),gomesFockWindowMass B S ((c+b) • x))

/-- Every two-reference intensity menu loses a reflection: three records are necessary for unrestricted complex scalar recovery. -/
theorem gomesFockWindowTwoReferenceMenu_not_injective {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) (a b : ℂ) :
    ¬ Function.Injective (gomesFockWindowTwoReferenceMenu B S x a b) := by
  intro h
  by_cases hab : a = b
  · subst b
    have hm : gomesFockWindowTwoReferenceMenu B S x a a (-a+Complex.I) =
        gomesFockWindowTwoReferenceMenu B S x a a (-a-Complex.I) := by
      apply Prod.ext <;>
        simp only [gomesFockWindowTwoReferenceMenu,gomesFockWindowMass_smul,Complex.normSq_apply,
          Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
          Complex.I_re,Complex.I_im] <;> ring
    have hi := congrArg Complex.im (h hm)
    simp only [Complex.add_im,Complex.sub_im,Complex.neg_im,Complex.I_im] at hi
    linarith
  · have hm : gomesFockWindowTwoReferenceMenu B S x a b (-a+(b-a)*Complex.I) =
        gomesFockWindowTwoReferenceMenu B S x a b (-a-(b-a)*Complex.I) := by
      apply Prod.ext <;>
        simp only [gomesFockWindowTwoReferenceMenu,gomesFockWindowMass_smul,Complex.normSq_apply,
          Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
          Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im] <;> ring
    have he := h hm
    have hv : (b-a)*Complex.I = 0 := by linear_combination (1/2 : ℂ)*he
    exact (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hab)) Complex.I_ne_zero) hv

/-- The exact failure locus of phase reconstruction is the kernel of the spectral-window tensor. -/
theorem gomesFockWindowIntensityMenu_kernel_reconstruction {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) (c e : ℂ) :
    gomesFockWindowIntensityMenu B S x c = gomesFockWindowIntensityMenu B S x e ↔
      c = e ∨ gomesFockWindowMatrix B S*ᵥx = 0 := by
  rw [gomesFockWindowIntensityMenu_reconstruction,gomesFockWindowMass_zero_iff_kernel]

/-- Three intensities recover the scalar exactly at states detected by the spectral-window tensor. -/
theorem gomesFockWindowIntensityMenu_injective_iff_detected {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    Function.Injective (gomesFockWindowIntensityMenu B S x) ↔ gomesFockWindowMatrix B S*ᵥx ≠ 0 := by
  rw [gomesFockWindowIntensityMenu_injective_iff]
  exact not_congr (gomesFockWindowMass_zero_iff_kernel B S x)

end GaloisForLFunctions.HTGeometry
