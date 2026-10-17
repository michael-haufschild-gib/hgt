import GaloisForLFunctions.BiScaleUncertainty.FactorialWeilCoercivity

/-! The literal full Weil form on the entire factorial ramp–tent span. -/

open MeasureTheory Set
open scoped CompactlySupported
open Zeta23
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly
noncomputable section
set_option autoImplicit false

/-- Actual spectral Weil energy of the concrete two-parameter source. -/
def factorialSpanWeil (n : ℕ) (c d : ℝ) : ℝ :=
  (weilFullFunctional (fun j => (ArithmeticFunction.vonMangoldt j : ℝ))
    (EF.weilTest
      (fun u => ((c • factorialSourceLeft n+d • factorialSourceRight n) u : ℂ))
      (fun u => ((c • factorialSourceLeft n+d • factorialSourceRight n) u : ℂ)))).re

/-- The complete signed mixed coefficient, including the arithmetic and polar terms. -/
def factorialWeilMixed (n : ℕ) : ℝ :=
  -(∫ x in Ioi (0 : ℝ), sourceFactorialCausal (n+1) x*archLevySinhWeight x) -
    2*fullPairing (sourceFactorialCausal (n+1))

private theorem mixed_integrable (f g : C_c(ℝ, ℝ)) (x : ℝ) :
    Integrable (fun u => f u*g (u+x)) :=
  (f.continuous.mul (g.continuous.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
    (f.hasCompactSupport.mul_right)

theorem factorialSource_combination_autocorr (n : ℕ) (c d x : ℝ) :
    autocorr (c • factorialSourceLeft n+d • factorialSourceRight n) x =
      c^2*autocorr (factorialSourceLeft n) x+d^2*autocorr (factorialSourceRight n) x+
        c*d*factorialSourceContrast n x := by
  have hLL := mixed_integrable (factorialSourceLeft n) (factorialSourceLeft n) x
  have hRR := mixed_integrable (factorialSourceRight n) (factorialSourceRight n) x
  have hLR := mixed_integrable (factorialSourceLeft n) (factorialSourceRight n) x
  have hRL := mixed_integrable (factorialSourceRight n) (factorialSourceLeft n) x
  calc
    _ = ∫ u : ℝ, c^2*(factorialSourceLeft n u*factorialSourceLeft n (u+x))+
        d^2*(factorialSourceRight n u*factorialSourceRight n (u+x))+
        (c*d)*(factorialSourceLeft n u*factorialSourceRight n (u+x)+
          factorialSourceRight n u*factorialSourceLeft n (u+x)) := by
      unfold autocorr
      apply integral_congr_ae
      filter_upwards [] with u
      change (c*factorialSourceLeft n u+d*factorialSourceRight n u)*
        (c*factorialSourceLeft n (u+x)+d*factorialSourceRight n (u+x)) = _
      ring
    _ = _ := by
      rw [integral_add ((hLL.const_mul _).add (hRR.const_mul _)) ((hLR.add hRL).const_mul _),
        integral_add (hLL.const_mul _) (hRR.const_mul _)]
      simp only [integral_const_mul]
      rw [integral_add hLR hRL, factorialSource_mixed_forward, factorialSource_mixed_reverse,
        ← factorialSourceContrast_eq]
      rfl

private theorem contrast_zero (n : ℕ) : factorialSourceContrast n 0 = 0 := by
  rw [factorialSourceContrast_eq, neg_zero,
    sourceFactorialCausal_zero_of_nonpos (by omega : 1 ≤ n+1) le_rfl]
  ring

private theorem combination_pairing (n : ℕ) (c d : ℝ) :
    fullPairing (autocorr (c • factorialSourceLeft n+d • factorialSourceRight n)) =
      c^2*fullPairing (autocorr (factorialSourceLeft n))+
      d^2*fullPairing (autocorr (factorialSourceRight n))+
      c*d*fullPairing (factorialSourceContrast n) := by
  obtain ⟨_, hLs, hLi⟩ := autocorr_fullPairing_admissible (factorialSourceLeft n)
  obtain ⟨_, hRs, hRi⟩ := autocorr_fullPairing_admissible (factorialSourceRight n)
  obtain ⟨_, hCs, hCi⟩ := factorialSourceContrast_admissible n
  have hp : primeTerm (autocorr (c • factorialSourceLeft n+d • factorialSourceRight n)) =
      fun j => c^2*primeTerm (autocorr (factorialSourceLeft n)) j+
        d^2*primeTerm (autocorr (factorialSourceRight n)) j+
        c*d*primeTerm (factorialSourceContrast n) j := by
    funext j
    unfold primeTerm
    split_ifs <;> simp only [factorialSource_combination_autocorr] <;> ring
  have hs : (∑' j, primeTerm (autocorr (c • factorialSourceLeft n+d • factorialSourceRight n)) j) =
      c^2*(∑' j, primeTerm (autocorr (factorialSourceLeft n)) j)+
      d^2*(∑' j, primeTerm (autocorr (factorialSourceRight n)) j)+
      c*d*(∑' j, primeTerm (factorialSourceContrast n) j) := by
    rw [hp, Summable.tsum_add ((hLs.of_abs.mul_left _).add (hRs.of_abs.mul_left _))
        (hCs.of_abs.mul_left _),
      Summable.tsum_add (hLs.of_abs.mul_left _) (hRs.of_abs.mul_left _)]
    simp only [tsum_mul_left]
  have hi : (∫ x in Ici (0 : ℝ), polarDensity x*
        autocorr (c • factorialSourceLeft n+d • factorialSourceRight n) x) =
      c^2*(∫ x in Ici (0 : ℝ), polarDensity x*autocorr (factorialSourceLeft n) x)+
      d^2*(∫ x in Ici (0 : ℝ), polarDensity x*autocorr (factorialSourceRight n) x)+
      c*d*(∫ x in Ici (0 : ℝ), polarDensity x*factorialSourceContrast n x) := by
    have he : (fun x => polarDensity x*autocorr
        (c • factorialSourceLeft n+d • factorialSourceRight n) x) =
        fun x => c^2*(polarDensity x*autocorr (factorialSourceLeft n) x)+
          d^2*(polarDensity x*autocorr (factorialSourceRight n) x)+
          c*d*(polarDensity x*factorialSourceContrast n x) := by
      funext x
      rw [factorialSource_combination_autocorr]
      ring
    rw [he, integral_add ((hLi.const_mul _).add (hRi.const_mul _)) (hCi.const_mul _),
      integral_add (hLi.const_mul _) (hRi.const_mul _)]
    simp only [integral_const_mul]
  unfold fullPairing
  rw [hs, hi]
  ring

private theorem combination_jump (n : ℕ) (c d : ℝ) :
    biScaleLevyEnergy (c • factorialSourceLeft n+d • factorialSourceRight n) =
      c^2*biScaleLevyEnergy (factorialSourceLeft n)+d^2*biScaleLevyEnergy (factorialSourceRight n)-
      c*d*(∫ x in Ioi (0 : ℝ), sourceFactorialCausal (n+1) x*archLevySinhWeight x) := by
  have he : (fun x => (autocorr (c • factorialSourceLeft n+d • factorialSourceRight n) 0-
      autocorr (c • factorialSourceLeft n+d • factorialSourceRight n) x)*archLevySinhWeight x) =ᵐ[volume.restrict (Ioi 0)]
      fun x => c^2*((autocorr (factorialSourceLeft n) 0-autocorr (factorialSourceLeft n) x)*archLevySinhWeight x)+
        d^2*((autocorr (factorialSourceRight n) 0-autocorr (factorialSourceRight n) x)*archLevySinhWeight x)-
        c*d*(sourceFactorialCausal (n+1) x*archLevySinhWeight x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [factorialSource_combination_autocorr, factorialSource_combination_autocorr,
      contrast_zero, factorialSourceContrast_eq_of_nonneg n hx.le]
    ring
  unfold biScaleLevyEnergy
  rw [integral_congr_ae he,
    integral_sub (((factorialSourceLeft_jump_integrable n).const_mul _).add
      ((factorialSourceRight_jump_integrable n).const_mul _))
      ((integrableOn_sourceFactorialCausal_archWeight n).const_mul _),
    integral_add ((factorialSourceLeft_jump_integrable n).const_mul _)
      ((factorialSourceRight_jump_integrable n).const_mul _)]
  simp only [integral_const_mul]

theorem factorialSpanWeil_eq_complete (n : ℕ) (c d : ℝ) :
    factorialSpanWeil n c d =
      EF.gammaBracket 0*autocorr (c • factorialSourceLeft n+d • factorialSourceRight n) 0+
      biScaleLevyEnergy (c • factorialSourceLeft n+d • factorialSourceRight n)-
      2*fullPairing (autocorr (c • factorialSourceLeft n+d • factorialSourceRight n)) :=
  re_weilFullFunctional_eq_of_compact_finite_jump _ (factorialSource_combination_jump_integrable n c d)

/-- Exact quadratic formula with no sign, arithmetic, or domain premise. -/
theorem factorialSpanWeil_gram (n : ℕ) (c d : ℝ) :
    factorialSpanWeil n c d = c^2*factorialSpanWeil n 1 0+
      d^2*factorialSpanWeil n 0 1+c*d*factorialWeilMixed n := by
  rw [factorialSpanWeil_eq_complete, factorialSpanWeil_eq_complete n 1 0,
    factorialSpanWeil_eq_complete n 0 1]
  simp only [one_smul, zero_smul, add_zero, zero_add]
  rw [factorialSource_combination_autocorr, contrast_zero, combination_jump, combination_pairing,
    fullPairing_factorialSourceContrast]
  unfold factorialWeilMixed
  ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
