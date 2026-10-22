import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerCohomologyExponential
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGlobalHassePaugamPairing

/-! # Actual convolution adjunction and global symplectic source gauges

The full Paugam pairing is balanced over actual source convolution, with
weighted inversion as adjoint. Exponentiating any anti-invariant source
therefore gives an original-source automorphism preserving this global
nondegenerate pairing, including every repeated-zero slot.
-/

open Complex
namespace RHTower
noncomputable section
local notation "V" => DeningerMeyerStrongLogTarget
local notation "Q" => DeningerMeyerStrongLogCohomology
local notation "C" => deningerMeyerCohomologyConvolution
local notation "J" => deningerMeyerStrongLogCohomologyJ
local notation "B" => deningerMeyerGlobalHassePaugamPairing

theorem deningerMeyerSourceConvolution_J (g h : V) :
    deningerMeyerStrongLogJ (deningerMeyerSourceConvolution g h) =
      deningerMeyerSourceConvolution (deningerMeyerStrongLogJ g) (deningerMeyerStrongLogJ h) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  simp only [deningerMeyerStrongLogMellin_J, deningerMeyerSourceConvolution_mellin]

theorem deningerMeyerCohomologyConvolution_J (u v : Q) : J (C u v) = C (J u) (J v) := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h =>
      simp only [deningerMeyerCohomologyConvolution_mk, deningerMeyerStrongLogCohomologyJ_mk,
        deningerMeyerSourceConvolution_J]

private theorem top_convolution (d : DeningerMeyerZetaZeroJetDatum) (u v : Q) :
    d.evaluationLE d.jetOrder (le_refl _) (C u v) =
      ∑ i : Fin (d.jetOrder+1), (d.jetOrder.choose i.val : ℂ) *
        d.evaluationLE i.val (Nat.le_of_lt_succ i.isLt) u *
        d.evaluationLE (d.jetOrder-i.val) (Nat.sub_le _ _) v := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h =>
      simp only [deningerMeyerCohomologyConvolution_mk,
        DeningerMeyerZetaZeroJetDatum.evaluationLE_mk,
        deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
      have he : deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g h) =
          deningerMeyerStrongLogMellin g * deningerMeyerStrongLogMellin h :=
        funext (deningerMeyerSourceConvolution_mellin g h)
      rw [he, iteratedDeriv_mul
        ((deningerMeyerStrongLogMellin_entireRegular g).differentiable.contDiff.of_le le_top).contDiffAt
        ((deningerMeyerStrongLogMellin_entireRegular h).differentiable.contDiff.of_le le_top).contDiffAt]
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (d.jetOrder.choose i : ℂ) *
        iteratedDeriv i (deningerMeyerStrongLogMellin g) d.point *
        iteratedDeriv (d.jetOrder-i) (deningerMeyerStrongLogMellin h) d.point)]

/-- An actual alternating convolution class; no geometric cup identification is assumed. -/
def deningerMeyerConvolutionSkewProduct (u v : Q) : Q := C u (J v) - C v (J u)

theorem deningerMeyerPaugamGeneralizedJetPairing_convolution
    (d : DeningerMeyerZetaZeroJetDatum) (u v : Q) :
    deningerMeyerPaugamGeneralizedJetPairing d u v =
      d.evaluationLE d.jetOrder (le_refl _) (deningerMeyerConvolutionSkewProduct u v) := by
  rw [deningerMeyerPaugamGeneralizedJetPairing_apply,
    deningerMeyerConvolutionSkewProduct, map_sub, top_convolution, top_convolution,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem conv_left_comm (a u v : Q) : C a (C u v) = C u (C a v) := by
  rw [← deningerMeyerCohomologyConvolution_assoc,
    deningerMeyerCohomologyConvolution_comm a u, deningerMeyerCohomologyConvolution_assoc]

theorem deningerMeyerConvolutionSkewProduct_adjoint (a u v : Q) :
    deningerMeyerConvolutionSkewProduct (C a u) v =
      deningerMeyerConvolutionSkewProduct u (C (J a) v) := by
  simp only [deningerMeyerConvolutionSkewProduct, deningerMeyerCohomologyConvolution_J,
    deningerMeyerStrongLogCohomologyJ_sq, deningerMeyerCohomologyConvolution_assoc]
  rw [conv_left_comm a u (J v), conv_left_comm v (J a) (J u)]

/-- Global source-native adjunction for the existing full nondegenerate Paugam pairing. -/
theorem deningerMeyerGlobalHassePaugamPairing_convolution_adjoint (a u v : Q) :
    B (C a u) v = B u (C (J a) v) := by
  rw [deningerMeyerGlobalHassePaugamPairing_blocks, deningerMeyerGlobalHassePaugamPairing_blocks]
  apply tsum_congr
  intro rho
  simp only [deningerMeyerHassePaugamBlock_eq,
    deningerMeyerPaugamGeneralizedJetPairing_convolution, deningerMeyerConvolutionSkewProduct_adjoint]

theorem deningerMeyerSourceExp_J (g : V) :
    deningerMeyerSourceExp (deningerMeyerStrongLogJ g) =
      deningerMeyerStrongLogJ (deningerMeyerSourceExp g) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  simp only [deningerMeyerSourceExp_mellin, deningerMeyerStrongLogMellin_J]

private theorem sourceGauge_eq (g : V) (u : Q) :
    deningerMeyerCohomologySourceGauge g u = u + C (Submodule.Quotient.mk (deningerMeyerSourceExp g)) u := by
  rw [← deningerMeyerCohomologyGauge_mk]
  rfl

theorem deningerMeyerGlobalHassePaugamPairing_gauge_adjoint (g : V) (u v : Q) :
    B (deningerMeyerCohomologySourceGauge g u) v =
      B u (deningerMeyerCohomologySourceGauge (deningerMeyerStrongLogJ g) v) := by
  rw [sourceGauge_eq, sourceGauge_eq, map_add, LinearMap.add_apply, map_add,
    deningerMeyerGlobalHassePaugamPairing_convolution_adjoint,
    deningerMeyerStrongLogCohomologyJ_mk, ← deningerMeyerSourceExp_J]

/-- Arbitrary original sources produce global pairing-preserving automorphisms. -/
theorem deningerMeyerAntiInvariantGauge_preserves_Paugam (g : V) (u v : Q) :
    B (deningerMeyerCohomologySourceGauge (g-deningerMeyerStrongLogJ g) u)
      (deningerMeyerCohomologySourceGauge (g-deningerMeyerStrongLogJ g) v) = B u v := by
  rw [deningerMeyerGlobalHassePaugamPairing_gauge_adjoint]
  have he : deningerMeyerStrongLogJ (g-deningerMeyerStrongLogJ g) +
      (g-deningerMeyerStrongLogJ g) = 0 := by
    rw [map_sub, deningerMeyerStrongLogJ_sq]
    abel
  change B u (((deningerMeyerCohomologySourceGauge
    (deningerMeyerStrongLogJ (g-deningerMeyerStrongLogJ g))).comp
      (deningerMeyerCohomologySourceGauge (g-deningerMeyerStrongLogJ g))) v) = B u v
  rw [← deningerMeyerCohomologySourceGauge_add, he, deningerMeyerCohomologySourceGauge_zero]
  rfl

end
end RHTower
