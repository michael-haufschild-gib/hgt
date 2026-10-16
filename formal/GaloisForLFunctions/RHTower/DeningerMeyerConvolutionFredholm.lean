import GaloisForLFunctions.RHTower.DeningerMeyerConvolutionResonance
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-! # Unconditional Fredholm repair for every original convolution symbol

Replacing each complete resonant block by identity removes the entire
kernel. Compactness then supplies a bounded inverse for every original
source, without a smallness, positivity or multiplicity assumption.
-/

noncomputable section
open Complex ContinuousLinearMap

namespace RHTower

theorem deningerMeyerConvolutionFredholmRepair_ker (g : DeningerMeyerStrongLogTarget)
    (x : DeningerArithmeticJetHilbert) (hx : deningerMeyerConvolutionFredholmRepair g x = 0) :
    x = 0 := by
  classical
  have hz (rho : XiDivisorSupport) (j : ℕ) :
      ∀ hj : j < xiSupportMultiplicity rho, x ⟨rho, ⟨j, hj⟩⟩ = 0 := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      let q : DeningerArithmeticJetCoordinate := ⟨rho, ⟨j, hj⟩⟩
      have hp := congrArg (fun y : DeningerArithmeticJetHilbert => y q) hx
      rw [deningerMeyerConvolutionFredholmRepair_apply] at hp
      by_cases hrho : rho ∈ deningerMeyerConvolutionResonance g
      · simpa only [q, hrho, ↓reduceIte, lp.coeFn_zero, Pi.zero_apply] using hp
      · have hc : deningerMeyerHilbertConvolution g x q =
            deningerMeyerStrongLogMellin g (rho : ℂ) * x q := by
          rw [deningerMeyerHilbertConvolution_jets, Finset.sum_eq_single 0]
          · simp only [deningerHasseLower, Nat.sub_zero]
            simp only [deningerMeyerHasseMoment, Nat.factorial_zero, Nat.cast_one, div_one]
            rfl
          · intro k hk hk0
            have hk' := Finset.mem_range.mp hk
            have hlt : j-k < j := by change k < j+1 at hk'; omega
            have he := ih (j-k) hlt (lt_of_le_of_lt (Nat.sub_le _ _) hj)
            change _ * x ⟨rho, ⟨j-k, _⟩⟩ = 0
            rw [he, mul_zero]
          · simp
        change (if rho ∈ deningerMeyerConvolutionResonance g then x q
          else x q + deningerMeyerHilbertConvolution g x q) = 0 at hp
        rw [if_neg hrho, hc] at hp
        have he : (1+deningerMeyerStrongLogMellin g (rho : ℂ))*x q = 0 := by
          linear_combination hp
        exact (mul_eq_zero.mp he).resolve_left hrho
  apply lp.ext
  funext q
  exact hz q.1 q.2.val q.2.isLt

private theorem unit_one_add_compact {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H] (K : H →L[ℂ] H)
    (hK : IsCompactOperator K) (hker : ∀ x, (1+K) x = 0 → x = 0) :
    IsUnit (1+K) := by
  rcases hK.hasEigenvalue_or_mem_resolventSet (μ := (-1 : ℂ)) (by simp) with he | hu
  · obtain ⟨x, hx, hne⟩ := he.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hx
    apply False.elim
    apply hne
    apply hker
    change x + K x = 0
    change K x = (-1 : ℂ) • x at hx
    rw [hx, neg_one_smul, add_neg_cancel]
  · rw [resolventSet, Set.mem_setOf_eq] at hu
    have he : (algebraMap ℂ (H →L[ℂ] H)) (-1) - K = -(1+K) := by simp; abel
    rw [he] at hu
    exact (IsUnit.neg_iff _).mp hu

/-- The repair is an actual invertible operator for every original source. -/
theorem deningerMeyerConvolutionFredholmRepair_isUnit (g : DeningerMeyerStrongLogTarget) :
    IsUnit (deningerMeyerConvolutionFredholmRepair g) := by
  let Q : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
    1-deningerMeyerConvolutionResonantProjection g
  have hc : IsCompactOperator (fun x : DeningerArithmeticJetHilbert =>
      deningerMeyerHilbertConvolution g (Q x)) :=
    (deningerMeyerHilbertConvolution_isCompact g).comp_clm Q
  exact unit_one_add_compact ((deningerMeyerHilbertConvolution g).comp Q) hc
    (fun x hx => deningerMeyerConvolutionFredholmRepair_ker g x hx)

def deningerMeyerConvolutionFredholmInverse (g : DeningerMeyerStrongLogTarget) :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  Ring.inverse (deningerMeyerConvolutionFredholmRepair g)

theorem deningerMeyerConvolutionFredholmInverse_right (g : DeningerMeyerStrongLogTarget)
    (f : DeningerArithmeticJetHilbert) :
    deningerMeyerConvolutionFredholmRepair g (deningerMeyerConvolutionFredholmInverse g f) = f := by
  exact congrArg (fun T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert => T f)
    (Ring.mul_inverse_cancel _ (deningerMeyerConvolutionFredholmRepair_isUnit g))

theorem deningerMeyerConvolutionFredholmInverse_left (g : DeningerMeyerStrongLogTarget)
    (f : DeningerArithmeticJetHilbert) :
    deningerMeyerConvolutionFredholmInverse g (deningerMeyerConvolutionFredholmRepair g f) = f := by
  exact congrArg (fun T : DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert => T f)
    (Ring.inverse_mul_cancel _ (deningerMeyerConvolutionFredholmRepair_isUnit g))

/-- Arbitrary completed source forcing has a unique bounded, fully confluent solution. -/
theorem deningerMeyerConvolutionFredholm_existsUnique (g : DeningerMeyerStrongLogTarget)
    (f : DeningerArithmeticJetHilbert) :
    ∃! x : DeningerArithmeticJetHilbert, deningerMeyerConvolutionFredholmRepair g x = f := by
  refine ⟨deningerMeyerConvolutionFredholmInverse g f,
    deningerMeyerConvolutionFredholmInverse_right g f, ?_⟩
  intro x hx
  rw [← deningerMeyerConvolutionFredholmInverse_left g x, hx]

end RHTower
