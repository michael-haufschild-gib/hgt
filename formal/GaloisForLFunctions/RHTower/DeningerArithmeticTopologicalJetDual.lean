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
  rw [hvalue] at heval
  simpa using heval

/-- The complete family of continuous compact-support jets separates ordinary source classes. -/
theorem deningerCompactOpenH1Jets_separating
    {x : DeningerArithmeticCompactOpenH1}
    (hx :
      ∀ (rho : XiDivisorSupport)
        (k : DeningerArithmeticJetIndex rho),
        deningerCompactOpenH1Jet rho k x = 0) :
    x = 0 := by
  apply deningerCompactOpenH1AllJets_injective
  change deningerCompactOpenH1AllJets x =
    deningerCompactOpenH1AllJets 0
  rw [map_zero]
  funext rho k
  exact hx rho k

end

end RHTower
