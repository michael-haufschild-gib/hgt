import GaloisForLFunctions.RHTower.Sieve.GuthMaynardCubicTermIntegral
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45TripleFubini

/-!
# `I_m` is the Chen–Gupta–Li Lemma 4.5 frequency term at modulus one

The Chen–Gupta–Li tower writes the cubic trace of the character packet matrix through the
three-frequency terms `cglLemma45TripleFrequencyTerm`, each a product of three factors
`χ(a) conj ψ(a) e(am/q) (N/q) ĥ_t((N/q) m)`. At modulus `q = 1` there is one residue `a = 0`, every
character is trivial and `e(0) = 1`, so a factor is `N ĥ_t(Nm)`, and

`I_m = Σ_{t₁,t₂,t₃ ∈ W} cglLemma45TripleFrequencyTerm (t₁−t₂) (t₂−t₃) (t₃−t₁) 0 0 0 ((m₁, m₂), m₃)`,

i.e. the Guth–Maynard `I_m` (Lemma 4.5) is the `ζ` (principal, `q = 1`) case of the CGL object.
-/

set_option autoImplicit false

open scoped FourierTransform

namespace RHTower.GuthMaynard

noncomputable section

/-- The modulus `q = 1` of the `ζ` case. -/
def modulusOne : CGLPositiveModulus := ⟨1, one_pos⟩

/-- `ZMod 1` has a single residue. -/
instance : Subsingleton (ZMod modulusOne.value) := by
  change Subsingleton (Fin 1); infer_instance

/-- At modulus one a CGL character-pair frequency term is `N ĥ_t(Nm)`. -/
theorem cglLemma45CharacterPairFourierTerm_modulusOne (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (χ ψ : DirichletCharacter ℂ modulusOne.value) (t : ℝ)
    (a : ZMod modulusOne.value) (m : ℤ) :
    cglLemma45CharacterPairFourierTerm w N modulusOne χ ψ t a m =
      (N.value : ℂ) * bumpFourier w.toCGLSmoothBump t (m * N.value) := by
  have ha : a = 1 := Subsingleton.elim a 1
  have hscale : cglAffineFourierScale N modulusOne = N.value := by
    simp [cglAffineFourierScale, modulusOne]
  have hchar : ZMod.stdAddChar (a * (m : ZMod modulusOne.value)) = 1 := by
    rw [Subsingleton.elim (a * (m : ZMod modulusOne.value)) 0, AddChar.map_zero_eq_one]
  rw [cglLemma45CharacterPairFourierTerm, hchar, hscale, ha, MulChar.map_one, MulChar.map_one,
    map_one, bumpFourier, mul_comm (m : ℝ)]
  push_cast; ring

/-- **`I_m` as CGL Lemma 4.5 frequency terms.** For the `ζ` case `q = 1` (any characters mod 1,
residues `0`), `I_m` is the sum over `t₁, t₂, t₃ ∈ W` of the CGL three-frequency term at the time
differences `(t₁ − t₂, t₂ − t₃, t₃ − t₁)` and the frequency `((m₁, m₂), m₃)`. -/
theorem cubicTerm_eq_sum_cglLemma45TripleFrequencyTerm (w : CGLRealSmoothBump)
    (N : CGLPositiveLength) (χ : DirichletCharacter ℂ modulusOne.value) (W : Finset ℝ)
    (m₁ m₂ m₃ : ℤ) :
    cubicTerm w.toCGLSmoothBump W N.value m₁ m₂ m₃ =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        cglLemma45TripleFrequencyTerm w N modulusOne χ χ χ χ χ χ
          (t₁ - t₂) (t₂ - t₃) (t₃ - t₁) 0 0 0 ((m₁, m₂), m₃) := by
  unfold cubicTerm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t₂ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t₃ _ => ?_
  simp only [cglLemma45TripleFrequencyTerm, cglLemma45CharacterPairFourierTerm_modulusOne]
  push_cast; ring

end

end RHTower.GuthMaynard
