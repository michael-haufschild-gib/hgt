import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms
import GaloisForLFunctions.RHTower.WeilDeletionTwoBump

/-!
# The zeros are the weights of the contacts under scaling

A weight line of the shifts is a sequence `χ_z = (n^z)_n`, `F_k χ_z = k^z χ_z`. Tested against a
packet `g` at the scale `e^a`, a weight line gives `e^{za}` times a number: the scale flow acts on
it by the character `a ↦ e^{za}`. The contact weights `Λ(n)/√n` of the arithmetic square, tested
in the same way, are

  `Σ_n (Λ(n)/√n)·(g(log n − a) + g(−log n − a))`
    `= e^{−a/2} ĝ(i/2) + e^{a/2} ĝ(−i/2) + (1/2π) ∫ e^{ira} ĝ(r) G(r) dr − Σ_ρ m_ρ ĝ(γ_ρ) e^{(ρ−½)a}`

(`contactScale_eq`): the two characters `e^{∓a/2}` of the pole plane, the characters of the jets
integrated against the symbol `G` of the Gamma factor, and one character `e^{(ρ−½)a}` for every
nontrivial zero `ρ`, with coefficient `−m_ρ ĝ(γ_ρ)`. In the unitary normalization the weights of
the contact sequence under scaling are the weights `±½` of the pole plane, the weights of the jets
and the numbers `ρ − ½`.

This is the explicit formula for the translated test. It is a statement on packets: the sequence
`Λ` is not a sum of weight lines term by term.
-/

open Complex MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The contact weights `Λ(n)/√n` of the square tested against the packet `g` at the scale
`e^a`. -/
def contactScale (g : ℝ → ℝ) (a : ℝ) : ℂ :=
  ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) *
    (((g (Real.log n - a) : ℝ) : ℂ) + ((g (-Real.log n - a) : ℝ) : ℂ))

/-- **The zeros are the weights of the contacts under scaling.** The contact weights tested
against a packet at the scale `e^a` are the two characters of the pole plane, the jets against
the symbol of the Gamma factor, and minus one character `e^{(ρ−½)a}` for every zero. -/
theorem contactScale_eq {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (a : ℝ) :
    contactScale g a =
      cexp (-((a : ℂ) / 2)) * paperFT (fun x => (g x : ℂ)) (I / 2) +
        cexp ((a : ℂ) / 2) * paperFT (fun x => (g x : ℂ)) (-I / 2) +
        (1 / (2 * Real.pi) : ℂ) * (∫ r : ℝ,
          cexp (I * r * a) * paperFT (fun x => (g x : ℂ)) r * (EF.gammaBracket r : ℂ)) -
        ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
          cexp (((ρ : ℂ) - 1 / 2) * a) * paperFT (fun x => (g x : ℂ)) (gammaOf ρ) := by
  have hk : ContDiff ℝ 2 fun y => ((g (y - a) : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hg.comp (contDiff_id.sub contDiff_const))
  have hkc : HasCompactSupport fun y => ((g (y - a) : ℝ) : ℂ) :=
    (hgc.comp_homeomorph (Homeomorph.subRight a)).comp_left Complex.ofReal_zero
  obtain ⟨-, heq⟩ := WeilEF.EF_lit_zetaZeroConfig _ hk hkc
  have hT : ∀ z : ℂ, paperFT (fun y => ((g (y - a) : ℝ) : ℂ)) z =
      cexp (I * z * a) * paperFT (fun x => (g x : ℂ)) z :=
    _root_.RHTower.WeilDeletion.paperFT_translate g a
  have hz : (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
        paperFT (fun y => ((g (y - a) : ℝ) : ℂ)) (gammaOf ρ)) =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
        cexp (((ρ : ℂ) - 1 / 2) * a) * paperFT (fun x => (g x : ℂ)) (gammaOf ρ) := by
    refine tsum_congr fun ρ => ?_
    have hw : I * gammaOf (ρ : ℂ) * (a : ℂ) = ((ρ : ℂ) - 1 / 2) * a := by
      rw [gammaOf, mul_div_cancel₀ _ I_ne_zero]
    rw [hT, hw]
    ring
  have hint : (∫ r : ℝ, paperFT (fun y => ((g (y - a) : ℝ) : ℂ)) r * (EF.gammaBracket r : ℂ)) =
      ∫ r : ℝ, cexp (I * r * a) * paperFT (fun x => (g x : ℂ)) r * (EF.gammaBracket r : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun r => by
      show paperFT (fun y => ((g (y - a) : ℝ) : ℂ)) r * (EF.gammaBracket r : ℂ) =
        cexp (I * r * a) * paperFT (fun x => (g x : ℂ)) r * (EF.gammaBracket r : ℂ)
      rw [hT])
  have e1 : cexp (I * (I / 2) * (a : ℂ)) = cexp (-((a : ℂ) / 2)) := by
    congr 1
    rw [show I * (I / 2) * (a : ℂ) = I * I * ((a : ℂ) / 2) by ring, I_mul_I]
    ring
  have e2 : cexp (I * (-I / 2) * (a : ℂ)) = cexp ((a : ℂ) / 2) := by
    congr 1
    rw [show I * (-I / 2) * (a : ℂ) = -(I * I) * ((a : ℂ) / 2) by ring, I_mul_I]
    ring
  rw [hz, EF.literatureRHS, hint, hT, hT, e1, e2] at heq
  unfold contactScale
  linear_combination heq

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
