import GaloisForLFunctions.RHTower.DeningerArithmeticJetFrobenius
import GaloisForLFunctions.RHTower.DeningerArithmeticSemisimpleHodge
import GaloisForLFunctions.RHTower.XiDivisorHilbertCarrier

/-!
# Source jet filtration and Deninger's associated-graded Frobenius

Compact-open arithmetic middle cohomology is the full product of multiplicity-bounded Xi jets.
The source Frobenius on a local jet block is

`(Theta a)_(rho,k) = lambda_rho a_(rho,k) + k I a_(rho,k-1)`.

The decreasing depth filtration consists of classes whose jets below depth `n` vanish.  The
nilpotent predecessor term raises depth, so source Frobenius preserves this filtration and agrees
modulo the next step with the diagonal semisimple Frobenius.  This proves, from the source
quotient rather than by declaration, that the multiplicity-exact divisor operator is the
associated-graded operator.

No RH, Hodge compatibility, positivity, simplicity, or zero-location premise is used.
-/

open Complex

namespace RHTower

noncomputable section

/-- Diagonal part of source Frobenius on the full product of local jets. -/
def deningerArithmeticJetProductGradedTheta :
    Module.End ℂ DeningerArithmeticJetProduct where
  toFun a rho k :=
    (1 / 2 + Complex.I * xiSpectralPointSupport rho) * a rho k
  map_add' a b := by
    funext rho k
    simp only [Pi.add_apply]
    ring
  map_smul' c a := by
    funext rho k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem deningerArithmeticJetProductGradedTheta_apply
    (a : DeningerArithmeticJetProduct)
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    deningerArithmeticJetProductGradedTheta a rho k =
      (1 / 2 + Complex.I * xiSpectralPointSupport rho) * a rho k :=
  rfl

/--
Semisimple source Frobenius on compact-open middle cohomology, transported through the
source-derived all-jets homeomorphism.
-/
def deningerCompactOpenGradedTheta :
    Module.End ℂ DeningerArithmeticCompactOpenH1 where
  toFun x :=
    deningerCompactOpenJetProductToH1
      (deningerArithmeticJetProductGradedTheta
        (deningerCompactOpenH1AllJets x))
  map_add' x y := by
    simp
  map_smul' c x := by
    simp

@[simp]
theorem deningerCompactOpenH1AllJets_gradedTheta
    (x : DeningerArithmeticCompactOpenH1)
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    deningerCompactOpenH1AllJets
        (deningerCompactOpenGradedTheta x) rho k =
      (1 / 2 + Complex.I * xiSpectralPointSupport rho) *
        deningerCompactOpenH1AllJets x rho k := by
  simp [deningerCompactOpenGradedTheta]

/--
Decreasing source jet-depth filtration.  `F n` consists of compact-open cohomology classes whose
local jets of order strictly below `n` vanish.
-/
def deningerArithmeticJetDepthFiltration (n : ℕ) :
    Submodule ℂ DeningerArithmeticCompactOpenH1 where
  carrier :=
    {x | ∀ rho k, k.val < n →
      deningerCompactOpenH1AllJets x rho k = 0}
  zero_mem' := by
    intro rho k hk
    simp
  add_mem' := by
    intro x y hx hy rho k hk
    simp only [map_add, Pi.add_apply]
    rw [hx rho k hk, hy rho k hk, add_zero]
  smul_mem' := by
    intro c x hx rho k hk
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hx rho k hk, mul_zero]

theorem mem_deningerArithmeticJetDepthFiltration_iff
    (n : ℕ) (x : DeningerArithmeticCompactOpenH1) :
    x ∈ deningerArithmeticJetDepthFiltration n ↔
      ∀ rho k, k.val < n →
        deningerCompactOpenH1AllJets x rho k = 0 :=
  Iff.rfl

/-- Jet-depth filtration is decreasing. -/
theorem deningerArithmeticJetDepthFiltration_antitone :
    Antitone deningerArithmeticJetDepthFiltration := by
  intro m n hmn x hx rho k hkn
  exact hx rho k (lt_of_lt_of_le hkn hmn)

/-- Source Frobenius preserves every step of the decreasing jet-depth filtration. -/
theorem deningerCompactOpenTheta_mem_jetDepthFiltration
    {n : ℕ} {x : DeningerArithmeticCompactOpenH1}
    (hx : x ∈ deningerArithmeticJetDepthFiltration n) :
    deningerCompactOpenTheta x ∈
      deningerArithmeticJetDepthFiltration n := by
  intro rho k hk
  rw [deningerCompactOpenH1AllJets_theta, hx rho k hk]
  have hpred :
      (deningerArithmeticJetIndexPred rho k).val < n := by
    rw [deningerArithmeticJetIndexPred_val]
    omega
  rw [hx rho (deningerArithmeticJetIndexPred rho k) hpred]
  ring

/-- The diagonal source Frobenius preserves every jet-depth step. -/
theorem deningerCompactOpenGradedTheta_mem_jetDepthFiltration
    {n : ℕ} {x : DeningerArithmeticCompactOpenH1}
    (hx : x ∈ deningerArithmeticJetDepthFiltration n) :
    deningerCompactOpenGradedTheta x ∈
      deningerArithmeticJetDepthFiltration n := by
  intro rho k hk
  rw [deningerCompactOpenH1AllJets_gradedTheta, hx rho k hk, mul_zero]

/--
The full source Frobenius and its diagonal part agree modulo the next jet-depth step.

This is the exact associated-graded comparison: on `F n / F (n+1)` the nilpotent predecessor
term vanishes, leaving multiplication by the Xi support eigenvalue.
-/
theorem deningerCompactOpenTheta_eq_gradedTheta_mod_next
    {n : ℕ} {x : DeningerArithmeticCompactOpenH1}
    (hx : x ∈ deningerArithmeticJetDepthFiltration n) :
    deningerCompactOpenTheta x -
        deningerCompactOpenGradedTheta x ∈
      deningerArithmeticJetDepthFiltration (n + 1) := by
  intro rho k hk
  simp only [map_sub, Pi.sub_apply]
  rw [deningerCompactOpenH1AllJets_theta,
    deningerCompactOpenH1AllJets_gradedTheta]
  by_cases hk0 : k.val = 0
  · simp [hk0]
  · have hpred :
        (deningerArithmeticJetIndexPred rho k).val < n := by
      rw [deningerArithmeticJetIndexPred_val]
      omega
    rw [hx rho (deningerArithmeticJetIndexPred rho k) hpred]
    ring

/--
On finite source jets, compact-open graded Frobenius is exactly the previously constructed
multiplicity-copy divisor Frobenius after the canonical Gelfand distribution embedding.
-/
theorem deningerCompactOpenGradedTheta_test
    (a : DeningerArithmeticJetTest) :
    deningerCompactOpenGradedTheta
        (deningerArithmeticJetHilbertToH1
          (deningerArithmeticJetTestToHilbert a)) =
      deningerArithmeticJetHilbertToH1
        (deningerArithmeticJetTestToHilbert
          (deningerArithmeticGradedTheta a)) := by
  apply deningerCompactOpenH1AllJets_injective
  funext rho k
  rw [deningerCompactOpenH1AllJets_gradedTheta]
  rw [deningerCompactOpenH1AllJets_apply,
    deningerCompactOpenH1AllJets_apply]
  rw [deningerCompactOpenH1Jet_jetHilbertToH1
      (⟨rho, k⟩ : DeningerArithmeticJetCoordinate)
      (deningerArithmeticJetTestToHilbert a),
    deningerCompactOpenH1Jet_jetHilbertToH1
      (⟨rho, k⟩ : DeningerArithmeticJetCoordinate)
      (deningerArithmeticJetTestToHilbert
        (deningerArithmeticGradedTheta a)),
    deningerArithmeticJetTestToHilbert_apply,
    deningerArithmeticJetTestToHilbert_apply]
  change
    (1 / 2 + Complex.I * xiSpectralPointSupport rho) *
        a ⟨rho, k⟩ =
      deningerArithmeticGradedTheta a ⟨rho, k⟩
  rw [show deningerArithmeticGradedTheta a ⟨rho, k⟩ =
      deningerDivisorThetaEigen ⟨rho, k⟩ * a ⟨rho, k⟩ by
    exact finsuppDiagonal_apply deningerDivisorThetaEigen a ⟨rho, k⟩]
  rw [deningerDivisorThetaEigen_eq, xiSpectralPoint_eq_support]
  ring

/--
The completed associated-graded source carrier is definitionally the canonical square-summable
jet carrier.  This equivalence records its source origin explicitly.
-/
def deningerArithmeticGradedHilbertEquivSourceJets :
    XiDivisorL2 ≃ₗ[ℂ] DeningerArithmeticJetHilbert :=
  LinearEquiv.refl ℂ DeningerArithmeticJetHilbert

end

end RHTower
