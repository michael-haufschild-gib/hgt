import GaloisForLFunctions.RHTower.DeningerArithmeticGelfandTriple

/-!
# Continuous compact-support jet classes

Every multiplicity-bounded Xi jet annihilates the compact-open differential and therefore
descends to a member of the strong continuous dual of source middle cohomology.  Finite Hermite
interpolation proves each descended jet is nonzero.  Exact global division proves that the whole
family separates compact-open cohomology.

These functionals are the unconditional local test vectors on the compact-support boundary of
the Deninger Gelfand triple.
-/

namespace RHTower

noncomputable section

/-- Descended continuous compact-support jet at one Xi divisor point. -/
def deningerCompactOpenH1Jet
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    DeningerArithmeticTopologicalH1Compact :=
  DeningerCompactOpenQuotient.liftL
    deningerCompactOpenXiRange
    (deningerCompactOpenJet
      (xiSpectralPointSupport rho) k)
    (fun {F} hF => by
      obtain ⟨G, rfl⟩ := hF
      exact
        deningerCompactOpenJet_XiMul_eq_zero
          rho k.isLt G)

@[simp]
theorem deningerCompactOpenH1Jet_class
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho)
    (F : DeningerCompactOpenEntire) :
    deningerCompactOpenH1Jet rho k
        (deningerArithmeticCompactOpenH1Class F) =
      deningerCompactOpenJet
        (xiSpectralPointSupport rho) k F :=
  rfl

/-- The descended local jet is the corresponding coordinate of the descended all-jets map. -/
theorem deningerCompactOpenH1AllJets_apply
    (x : DeningerArithmeticCompactOpenH1)
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    deningerCompactOpenH1AllJets x rho k =
      deningerCompactOpenH1Jet rho k x := by
  obtain ⟨F, rfl⟩ := Quotient.exists_rep x
  rfl

/-- Every local compact-support Xi jet is a nonzero continuous functional. -/
theorem deningerCompactOpenH1Jet_ne_zero
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    deningerCompactOpenH1Jet rho k ≠ 0 := by
  let S : Finset XiDivisorSupport := {rho}
  obtain ⟨F, hF⟩ :=
    exists_deningerCompactOpenPolynomial_finiteXiScalarJets
      S (fun _ _ => 1)
  intro hzero
  have heval :=
    congrArg
      (fun L : DeningerArithmeticTopologicalH1Compact =>
        L (deningerArithmeticCompactOpenH1Class F))
      hzero
  have hvalue :
      deningerCompactOpenH1Jet rho k
          (deningerArithmeticCompactOpenH1Class F) = 1 := by
    rw [deningerCompactOpenH1Jet_class]
    exact hF ⟨rho, Finset.mem_singleton_self rho⟩ k
  change
    deningerCompactOpenH1Jet rho k
        (deningerArithmeticCompactOpenH1Class F) =
      (0 : DeningerArithmeticTopologicalH1Compact)
        (deningerArithmeticCompactOpenH1Class F) at heval
  rw [hvalue] at heval
  simp at heval

/-- Zeroth local jet index at a Xi divisor point. -/
def deningerArithmeticJetIndexZero
    (rho : XiDivisorSupport) :
    DeningerArithmeticJetIndex rho :=
  ⟨0, xiSupportMultiplicity_pos rho⟩

/--
Compact-support Frobenius reflects the zeroth source jet from weight `lambda` to weight
`1 - lambda`.
-/
theorem deningerCompactOpenThetaCompact_H1Jet_zero
    (rho : XiDivisorSupport) :
    deningerCompactOpenThetaCompact
        (deningerCompactOpenH1Jet rho
          (deningerArithmeticJetIndexZero rho)) =
      (1 -
        (1 / 2 + Complex.I * xiSpectralPointSupport rho)) •
        deningerCompactOpenH1Jet rho
          (deningerArithmeticJetIndexZero rho) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨F, rfl⟩ := Quotient.exists_rep x
  change
    deningerCompactOpenThetaCompact
        (deningerCompactOpenH1Jet rho
          (deningerArithmeticJetIndexZero rho))
        (deningerArithmeticCompactOpenH1Class F) =
      ((1 -
        (1 / 2 + Complex.I * xiSpectralPointSupport rho)) •
        deningerCompactOpenH1Jet rho
          (deningerArithmeticJetIndexZero rho))
        (deningerArithmeticCompactOpenH1Class F)
  rw [deningerCompactOpenThetaCompact_apply,
    _root_.smul_apply,
    deningerCompactOpenH1Jet_class,
    deningerCompactOpenTheta_class,
    deningerCompactOpenH1Jet_class]
  simp only [deningerArithmeticJetIndexZero,
    deningerCompactOpenJet_apply, iteratedDeriv_zero,
    deningerCompactOpenThetaMul_apply, smul_eq_mul]
  ring

/-- The complete family of continuous compact-support jets separates ordinary source classes. -/
theorem deningerCompactOpenH1Jets_separating
    {x : DeningerArithmeticCompactOpenH1}
    (hx :
      ∀ (rho : XiDivisorSupport)
        (k : DeningerArithmeticJetIndex rho),
        deningerCompactOpenH1Jet rho k x = 0) :
    x = 0 := by
  apply deningerCompactOpenH1AllJets_injective
  rw [map_zero]
  funext rho k
  rw [deningerCompactOpenH1AllJets_apply]
  exact hx rho k

end

end RHTower
