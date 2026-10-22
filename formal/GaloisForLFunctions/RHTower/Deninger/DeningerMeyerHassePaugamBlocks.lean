import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHasseHilbertDensity
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPaugamGeneralizedJetPairing

/-! # Full Paugam blocks in native Hasse normalization -/

noncomputable section
open Complex Set

namespace RHTower

def deningerMeyerXiFullJetDatum (rho : XiDivisorSupport) : DeningerMeyerZetaZeroJetDatum where
  point := rho
  re_pos := (xi_divisor_support_re_mem_open_unit rho).1
  ne_one := xiDivisorSupport_ne_one rho
  jetOrder := xiSupportMultiplicity rho - 1
  zeta_vanishing j hj := iteratedDeriv_riemannZeta_eq_zero_of_lt_xiSupportMultiplicity rho (by
    have := xiSupportMultiplicity_pos rho
    omega)

def deningerMeyerHassePaugamBlock (rho : XiDivisorSupport)
    (u v : DeningerMeyerStrongLogCohomology) : ℂ :=
  ∑ j : DeningerArithmeticJetIndex rho,
    (deningerMeyerHasseJet u ⟨rho, j⟩ *
        deningerMeyerHasseJet (deningerMeyerStrongLogCohomologyJ v) ⟨rho, j.rev⟩ -
      deningerMeyerHasseJet v ⟨rho, j⟩ *
        deningerMeyerHasseJet (deningerMeyerStrongLogCohomologyJ u) ⟨rho, j.rev⟩)

private theorem hasse_complementary_coeff (n k : ℕ) (hk : k ≤ n) (a b c d : ℂ) :
    (n.choose k : ℂ) * (a*b-c*d) / (n.factorial : ℂ) =
      a / (k.factorial : ℂ) * (b / ((n-k).factorial : ℂ)) -
        c / (k.factorial : ℂ) * (d / ((n-k).factorial : ℂ)) := by
  have h : (n.choose k : ℂ) * (k.factorial : ℂ) * ((n-k).factorial : ℂ) =
      (n.factorial : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hl : ((n-k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n-k)
  field_simp
  linear_combination (a*b-c*d)*h

/-- Factorial normalization preserves the entire existing complementary-jet block. -/
theorem deningerMeyerHassePaugamBlock_eq (rho : XiDivisorSupport)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHassePaugamBlock rho u v =
      deningerMeyerPaugamGeneralizedJetPairing (deningerMeyerXiFullJetDatum rho) u v /
        ((xiSupportMultiplicity rho - 1).factorial : ℂ) := by
  have hm : xiSupportMultiplicity rho - 1 + 1 = xiSupportMultiplicity rho := by
    have := xiSupportMultiplicity_pos rho
    omega
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h =>
      rw [deningerMeyerPaugamGeneralizedJetPairing_apply, Finset.sum_div]
      unfold deningerMeyerHassePaugamBlock
      symm
      apply Fintype.sum_equiv (finCongr hm)
      intro j
      have hj : j.val ≤ xiSupportMultiplicity rho - 1 := Nat.le_of_lt_succ j.isLt
      have hr : ((finCongr hm j).rev).val = xiSupportMultiplicity rho - 1 - j.val := by
        simp only [Fin.val_rev, finCongr_apply_coe]
        omega
      simp only [DeningerMeyerZetaZeroJetDatum.evaluationLE_mk,
        deningerMeyerStrongLogCohomologyJ_mk, deningerMeyerHasseJet,
        deningerMeyerXiSupportJetEvaluationLM_mk, deningerMeyerXiFullJetDatum,
        finCongr_apply_coe, hr]
      exact hasse_complementary_coeff (xiSupportMultiplicity rho - 1) j.val hj _ _ _ _

theorem deningerMeyerHassePaugamBlock_flow (rho : XiDivisorSupport) (c : ℝ)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHassePaugamBlock rho
        (deningerMeyerStrongLogCohomologyFlow c u) (deningerMeyerStrongLogCohomologyFlow c v) =
      (Real.exp c : ℂ) * deningerMeyerHassePaugamBlock rho u v := by
  simp only [deningerMeyerHassePaugamBlock_eq, deningerMeyerPaugamGeneralizedJetPairing_flow,
    mul_div_assoc]

theorem deningerMeyerHassePaugamBlock_J (rho : XiDivisorSupport)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHassePaugamBlock rho
        (deningerMeyerStrongLogCohomologyJ u) (deningerMeyerStrongLogCohomologyJ v) =
      -deningerMeyerHassePaugamBlock rho u v := by
  simp only [deningerMeyerHassePaugamBlock_eq, deningerMeyerPaugamGeneralizedJetPairing_J,
    neg_div]

end RHTower
