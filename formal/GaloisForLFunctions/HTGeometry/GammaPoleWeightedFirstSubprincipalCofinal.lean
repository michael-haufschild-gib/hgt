import GaloisForLFunctions.HTGeometry.SimplePoleWeightedFirstSubprincipal

/-!
# Cofinal discharge of the Gamma first-subprincipal reflection

The branchwise weighted first-subprincipal order theorem requires a nonzero principal partial
reflection and a nonzero Gamma finite part on the same pole branch.  Separate cofinal statements do
not provide such a branch.  This module packages the principal frame in the existing symbolic
factorial-scale Laurent algebra and multiplies its partial reflection by the finite-part generator.

Joint scale/unit-derivative Laurent injectivity makes that product a nonzero pole-index germ whenever
the symbolic partial reflection is nonzero.  A symbolic principal cancellation is eventually exact
on the branch sequence, so one tail detection supplies a common branch carrying cancellation and
both nonzero factors.  The existing analytic theorem then gives the same exact order for covariant
and native affine Gamma packets.
-/

open Complex Filter Topology Finset MvPolynomial Polynomial LaurentPolynomial

namespace GaloisForLFunctions

noncomputable section

local instance gammaPoleWeightedFirstSubprincipalCofinalLocalInst1 : Algebra ℂ NatGerm := complexNatGerm.toAlgebra

/-- Symbolic principal frame obtained as the highest pole coefficient of each Gamma jet. -/
def gammaPolePrincipalReflectionSymbol (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* GammaPoleScaleDerivativeSymbolic :=
  MvPolynomial.eval₂Hom gammaPoleComplexScaleDerivativeInclude
    (fun j : Fin (n + 1) =>
      (gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ)).coeff
        (((j : ℕ) + 1 : ℕ) : ℤ))

/-- Actual pole-index germ of the symbolic principal reflection. -/
def gammaPolePrincipalReflectionGerm (n : ℕ) :
    MvPolynomial (Fin (n + 1)) ℂ →+* NatGerm :=
  gammaPoleScaleAndUnitDerivativeLaurentEval.comp
    (gammaPolePrincipalReflectionSymbol n)

/-- Each symbolic principal coordinate evaluates to the corresponding Gamma principal-coefficient
sequence. -/
theorem gammaPolePrincipalCoefficientSymbol_eq_sequence (j : ℕ) :
    gammaPoleScaleAndUnitDerivativeLaurentEval
        ((gammaPoleSymbolicDerivativeLaurentProfile j).coeff
          ((j + 1 : ℕ) : ℤ)) =
      (fun N : ℕ => gammaPoleJetPrincipalCoefficient (N - 1) j : NatGerm) := by
  rw [gammaPoleSymbolicDerivativeLaurentProfile_coeff_top, map_mul,
    gammaPoleScaleAndUnitDerivativeLaurentEval_derivativeScale]
  simp only [gammaPoleComplexScaleDerivativeInclude,
    RingHom.comp_apply,
    gammaPoleScaleAndUnitDerivativeLaurentEval_rationalInclude]
  rw [gammaPolePhysicalScaleGerm_eq_actual]
  change -(↑(fun N : ℕ => reciprocalGammaFactorialScale (N - 1)) : NatGerm)⁻¹ ^ j *
      complexNatGerm (((-1 : ℂ) ^ j) * (j.factorial : ℂ)) = _
  rw [complexNatGerm_eq_constGerm]
  rw [← Filter.Germ.coe_inv, ← Filter.Germ.coe_pow,
    ← Filter.Germ.coe_neg, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun N => by
    simp only [Pi.inv_apply, Pi.pow_apply, Pi.neg_apply, Pi.mul_apply]
    simp [gammaPoleJetPrincipalCoefficient]

/-- The full symbolic principal reflection is exactly evaluation on the branchwise principal
coefficient frame. -/
theorem gammaPolePrincipalReflectionGerm_eq_sequence
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    gammaPolePrincipalReflectionGerm n P =
      (fun N : ℕ => MvPolynomial.eval
        (fun j : Fin (n + 1) => gammaPoleJetPrincipalCoefficient (N - 1) (j : ℕ)) P :
        NatGerm) := by
  have hhom : gammaPolePrincipalReflectionGerm n =
      MvPolynomial.eval₂Hom complexNatGerm
        (fun j : Fin (n + 1) =>
          (fun N : ℕ => gammaPoleJetPrincipalCoefficient (N - 1) (j : ℕ) : NatGerm)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [gammaPolePrincipalReflectionGerm,
        gammaPolePrincipalReflectionSymbol, RingHom.comp_apply,
        MvPolynomial.eval₂Hom_C]
      change gammaPoleScaleAndUnitDerivativeLaurentEval
          (gammaPoleComplexScaleDerivativeInclude c) = complexNatGerm c
      simp [gammaPoleComplexScaleDerivativeInclude, complexNatGerm]
    · intro j
      simp only [gammaPolePrincipalReflectionGerm,
        gammaPolePrincipalReflectionSymbol, RingHom.comp_apply,
        MvPolynomial.eval₂Hom_X']
      change gammaPoleScaleAndUnitDerivativeLaurentEval
          ((gammaPoleSymbolicDerivativeLaurentProfile (j : ℕ)).coeff
            (((j : ℕ) + 1 : ℕ) : ℤ)) =
        (fun N : ℕ => gammaPoleJetPrincipalCoefficient (N - 1) (j : ℕ) : NatGerm)
      exact gammaPolePrincipalCoefficientSymbol_eq_sequence (j : ℕ)
  rw [RingHom.congr_fun hhom P,
    show MvPolynomial.eval₂Hom complexNatGerm
        (fun j : Fin (n + 1) =>
          (fun N : ℕ => gammaPoleJetPrincipalCoefficient (N - 1) (j : ℕ) : NatGerm)) P =
      MvPolynomial.aeval
        (fun j : Fin (n + 1) =>
          (fun N : ℕ => gammaPoleJetPrincipalCoefficient (N - 1) (j : ℕ) : NatGerm)) P by rfl,
    aeval_sequenceGerm_eq, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun N =>
    mvPolynomialSequenceEval_apply
      (fun j : Fin (n + 1) =>
        fun N : ℕ => gammaPoleJetPrincipalCoefficient (N - 1) (j : ℕ)) P N

/-- The base finite part is the negative first positive derivative of the regular Gamma unit. -/
theorem gammaPoleFinitePartJetGerm_zero_eq_neg_unitDerivative :
    gammaPoleFinitePartJetGerm 0 =
      -gammaPoleUnitPositiveDerivativeRationalGerm 0 := by
  rw [gammaPoleFinitePartJetGerm_eq_unitCoefficient]
  have hactual :=
    gammaPoleScaleAndUnitDerivativeRationalFamily_some_eq_actual 0
  simp only [gammaPoleScaleAndUnitDerivativeRationalFamily] at hactual
  rw [← hactual]
  simp

/-- Symbol whose actual value is the joint first-subprincipal product. -/
def gammaPoleFirstSubprincipalJointSymbol
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    GammaPoleScaleDerivativeSymbolic :=
  gammaPolePrincipalReflectionSymbol n
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
    (-LaurentPolynomial.C
      (MvPolynomial.X 0 : MvPolynomial ℕ GammaPoleRationalBase))

/-- Pole-index germ of the joint first-subprincipal symbol. -/
def gammaPoleFirstSubprincipalJointGerm
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) : NatGerm :=
  gammaPoleScaleAndUnitDerivativeLaurentEval
    (gammaPoleFirstSubprincipalJointSymbol n P)

/-- The symbolic first unit-derivative generator evaluates to the base Gamma finite part. -/
theorem gammaPoleScaleAndUnitDerivativeLaurentEval_finitePartSymbol :
    gammaPoleScaleAndUnitDerivativeLaurentEval
        (-LaurentPolynomial.C
          (MvPolynomial.X 0 : MvPolynomial ℕ GammaPoleRationalBase)) =
      gammaPoleFinitePartJetGerm 0 := by
  rw [map_neg]
  rw [gammaPoleScaleAndUnitDerivativeLaurentEval,
    LaurentPolynomial.eval₂_C]
  change -gammaPoleUnitDerivativeRationalEval
      (MvPolynomial.X 0 : MvPolynomial ℕ GammaPoleRationalBase) = _
  rw [gammaPoleFinitePartJetGerm_zero_eq_neg_unitDerivative]
  simp [gammaPoleUnitDerivativeRationalEval]

/-- The joint symbol evaluates to partial principal reflection times base finite part on every
branch, modulo the pole-index germ relation. -/
theorem gammaPoleFirstSubprincipalJointGerm_eq_sequence
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) :
    gammaPoleFirstSubprincipalJointGerm n P =
      (fun N : ℕ =>
        MvPolynomial.eval
            (fun j : Fin (n + 1) =>
              gammaPoleJetPrincipalCoefficient (N - 1) (j : ℕ))
            (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
          gammaPoleJetRegularRemainder (N - 1) 0 0 : NatGerm) := by
  rw [gammaPoleFirstSubprincipalJointGerm,
    gammaPoleFirstSubprincipalJointSymbol, map_mul,
    gammaPoleScaleAndUnitDerivativeLaurentEval_finitePartSymbol]
  change gammaPolePrincipalReflectionGerm n
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
        gammaPoleFinitePartJetGerm 0 = _
  rw [gammaPolePrincipalReflectionGerm_eq_sequence]
  change (↑(fun N : ℕ => MvPolynomial.eval
      (fun j : Fin (n + 1) =>
        gammaPoleJetPrincipalCoefficient (N - 1) (j : ℕ))
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P)) : NatGerm) *
      (↑(fun N : ℕ => gammaPoleJetRegularRemainder (N - 1) 0 0) : NatGerm) = _
  rw [← Filter.Germ.coe_mul]
  rw [Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun _ => rfl

/-- A nonzero symbolic partial reflection remains nonzero after adjoining the finite-part
generator. -/
theorem gammaPoleFirstSubprincipalJointSymbol_ne_zero
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ)
    (hpartial : gammaPolePrincipalReflectionSymbol n
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) ≠ 0) :
    gammaPoleFirstSubprincipalJointSymbol n P ≠ 0 := by
  have hfinite :
      -LaurentPolynomial.C
          (MvPolynomial.X 0 : MvPolynomial ℕ GammaPoleRationalBase) ≠ 0 := by
    have hX : (MvPolynomial.X 0 : MvPolynomial ℕ GammaPoleRationalBase) ≠ 0 :=
      MvPolynomial.X_ne_zero 0
    have hfiniteGerm : gammaPoleFinitePartJetGerm 0 ≠ 0 := by
      have heval := gammaPoleFinitePartJetRationalEval_injective.ne hX
      simpa [gammaPoleFinitePartJetRationalEval] using heval
    intro hzero
    apply hfiniteGerm
    rw [← gammaPoleScaleAndUnitDerivativeLaurentEval_finitePartSymbol,
      hzero, map_zero]
  exact mul_ne_zero hpartial hfinite

/-- Injective joint Laurent evaluation carries symbolic nonvanishing to the actual pole-index
germ. -/
theorem gammaPoleFirstSubprincipalJointGerm_ne_zero
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ)
    (hpartial : gammaPolePrincipalReflectionSymbol n
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) ≠ 0) :
    gammaPoleFirstSubprincipalJointGerm n P ≠ 0 := by
  simpa [gammaPoleFirstSubprincipalJointGerm] using
    gammaPoleScaleAndUnitDerivativeLaurentEval_injective.ne
      (gammaPoleFirstSubprincipalJointSymbol_ne_zero n P hpartial)

/-- A symbolic principal cancellation and nonzero symbolic first partial are realized together
with a nonzero Gamma finite part on arbitrarily remote branches. -/
theorem exists_cofinal_gammaPoleFirstSubprincipalFactors
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ)
    (hcancel : gammaPolePrincipalReflectionSymbol n P = 0)
    (hpartial : gammaPolePrincipalReflectionSymbol n
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) ≠ 0)
    (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      MvPolynomial.eval
        (fun j : Fin (n + 1) =>
          gammaPoleJetPrincipalCoefficient branch (j : ℕ)) P = 0 ∧
      MvPolynomial.eval
        (fun j : Fin (n + 1) =>
          gammaPoleJetPrincipalCoefficient branch (j : ℕ))
        (MvPolynomial.pderiv (0 : Fin (n + 1)) P) ≠ 0 ∧
      gammaPoleJetRegularRemainder branch 0 0 ≠ 0 := by
  have hcancelGerm : gammaPolePrincipalReflectionGerm n P = 0 := by
    change gammaPoleScaleAndUnitDerivativeLaurentEval
      (gammaPolePrincipalReflectionSymbol n P) = 0
    rw [hcancel, map_zero]
  rw [gammaPolePrincipalReflectionGerm_eq_sequence] at hcancelGerm
  have hcancelEventually : ∀ᶠ N : ℕ in Filter.atTop,
      MvPolynomial.eval
        (fun j : Fin (n + 1) =>
          gammaPoleJetPrincipalCoefficient (N - 1) (j : ℕ)) P = 0 := by
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at hcancelGerm
    exact hcancelGerm
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.1 hcancelEventually
  have hjoint := gammaPoleFirstSubprincipalJointGerm_ne_zero n P hpartial
  have hdetect : ∃ N : ℕ, max (B + 1) C ≤ N ∧
      MvPolynomial.eval
          (fun j : Fin (n + 1) =>
            gammaPoleJetPrincipalCoefficient (N - 1) (j : ℕ))
          (MvPolynomial.pderiv (0 : Fin (n + 1)) P) *
        gammaPoleJetRegularRemainder (N - 1) 0 0 ≠ 0 := by
    by_contra hdetect
    simp only [not_exists, not_and, not_not] at hdetect
    apply hjoint
    rw [gammaPoleFirstSubprincipalJointGerm_eq_sequence,
      ← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
    exact Filter.eventually_atTop.2
      ⟨max (B + 1) C, fun N hN => hdetect N hN⟩
  obtain ⟨N, hN, hproduct⟩ := hdetect
  have hBN : B ≤ N - 1 := by omega
  have hCN : C ≤ N := le_trans (le_max_right _ _) hN
  have hcancelN := hC N hCN
  have hparts := mul_ne_zero_iff.mp hproduct
  exact ⟨N - 1, hBN, hcancelN, hparts.1, hparts.2⟩

/-- Cofinal exact first-subprincipal order, simultaneously for covariant and native Gamma
packets. -/
theorem exists_cofinal_meromorphicOrderAt_gammaWeightedJetEval_of_firstSubprincipal
    (n : ℕ) (P : MvPolynomial (Fin (n + 1)) ℂ) {W : ℕ}
    (hP : P.IsWeightedHomogeneous (bellJetWeight (n + 1)) W)
    (hW : 0 < W)
    (hcancel : gammaPolePrincipalReflectionSymbol n P = 0)
    (hpartial : gammaPolePrincipalReflectionSymbol n
      (MvPolynomial.pderiv (0 : Fin (n + 1)) P) ≠ 0)
    (B : ℕ) :
    ∃ branch : ℕ, B ≤ branch ∧
      meromorphicOrderAt (gammaPoleWeightedJetEval branch n P) 0 =
        ((-((W - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ∧
      meromorphicOrderAt (gammaAffineWeightedJetEval branch n P) 0 =
        ((-((W - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  obtain ⟨branch, hbranch, hcancelBranch, hpartialBranch, hfiniteBranch⟩ :=
    exists_cofinal_gammaPoleFirstSubprincipalFactors n P hcancel hpartial B
  exact ⟨branch, hbranch,
    meromorphicOrderAt_gammaPoleWeightedJetEval_of_firstSubprincipal
      branch n P hP hW hcancelBranch hpartialBranch hfiniteBranch,
    meromorphicOrderAt_gammaAffineWeightedJetEval_of_firstSubprincipal
      branch n P hP hW hcancelBranch hpartialBranch hfiniteBranch⟩

end

end GaloisForLFunctions
