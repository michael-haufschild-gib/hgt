import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationPhysicalJets

/-! All positive real algebraic zeta dilations are jointly differentially
independent over the actual theta–Gamma coefficient field. Every finite packet
uses its own physical convergence line; Gamma remains in the original variable. -/

open Complex Filter Set Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Classical Differential UpperEndDifferentialInstances UpperEndComplexTowerInstances
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaAlgebraic
open DilationGerms AlgebraicDilationPhysicalJets
noncomputable section

local instance : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
local instance : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
local instance : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra
local instance : DifferentialAlgebra ↥gammaCoefficientField upperEndMeroField where
  deriv_algebraMap _ := rfl

/-- Positive real algebraic dilation parameters. -/
abbrev Dilation := {r : ℝ // 0 < r ∧ IsAlgebraic ℤ r}

/-- The actual dilate in the physical meromorphic field containing Gamma and theta. -/
def zetaDilationMero (r : Dilation) : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField (physicalZetaAnalytic r.val r.property.1)

/-- Every finite distinct positive algebraic dilation packet is free over physical Gamma. -/
theorem finite_dilations_differentialIndependent_gamma {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (ha : ∀ i, IsAlgebraic ℤ (r i))
    (hinj : Function.Injective r) :
    DifferentialIndependent ↥gammaCoefficientField (fun i =>
      algebraMap upperEndAnalyticSubring upperEndMeroField (physicalZetaAnalytic (r i) (hr i))) := by
  obtain ⟨a,_,ha0,hra⟩ := exists_common_line r hr 0
  have has : a < 2*a := by linarith only [ha0]
  have hs : 0 < 2*a := mul_pos (by norm_num) ha0
  have hrs : ∀ i, 2 ≤ r i*(2*a) := by
    intro i
    nlinarith only [hra i]
  have h := GammaJoint.algebraicIndependent_gamma_of_line hs
    (fun ik : ι × ℕ => upperEndAnalyticDeriv^[ik.2]
      (physicalZetaAnalytic (r ik.1) (hr ik.1)))
    (fun ik : ι × ℕ => iteratedDeriv ik.2 (dilate (r ik.1)))
    (fun ik => upperEndAnalyticDeriv_iterate_repr ik.2
      (physicalZetaAnalytic (r ik.1) (hr ik.1)) (dilate (r ik.1)) rfl)
    (fun ik => (dilate_jet_line (r ik.1) (hr ik.1) (2*a) (hrs ik.1) ik.2).1)
    (fun ik => (dilate_jet_line (r ik.1) (hr ik.1) (2*a) (hrs ik.1) ik.2).2)
    (dilate_jets_line_algebraicIndependent r hr ha hinj has hra)
  simpa only [DifferentialIndependent,
    GaloisForLFunctions.HTGeometry.differentialJet_algebraMap] using h

/-- All positive real algebraic dilates are jointly free over the actual Gamma differential field. -/
theorem zetaDilation_differentialIndependent_gamma :
    DifferentialIndependent ↥gammaCoefficientField zetaDilationMero := by
  apply (differentialIndependent_iff_forall_finite_subfamily _).mpr
  intro S hS
  letI : Fintype S := hS.fintype
  exact finite_dilations_differentialIndependent_gamma (fun r : S => r.val.val)
    (fun r => r.val.property.1) (fun r => r.val.property.2)
    (Subtype.val_injective.comp Subtype.val_injective)

/-- Adjoining the actual theta constants and Eisenstein `E₂` preserves full algebraic-dilation freeness. -/
theorem zetaDilation_differentialIndependent_thetaGamma :
    DifferentialIndependent ↥ModularThetaCoefficients.thetaGammaCoefficientField zetaDilationMero :=
  (ModularThetaCoefficients.thetaGamma_differentialIndependent_iff _).mpr
    zetaDilation_differentialIndependent_gamma

/-- Every positive algebraic power remains a positive algebraic dilation. -/
def orbitDilation (q : Dilation) (j : ℕ) : Dilation :=
  ⟨q.val^j,pow_pos q.property.1 _,q.property.2.pow j⟩

/-- The literal multiplicative orbit, including contracting positive algebraic multipliers. -/
def mahlerZetaMero (q : Dilation) (j : ℕ) : upperEndMeroField :=
  zetaDilationMero (orbitDilation q j)

theorem mahlerZetaMero_differentialIndependent (q : Dilation) (hq : q.val ≠ 1) :
    DifferentialIndependent ↥ModularThetaCoefficients.thetaGammaCoefficientField
      (mahlerZetaMero q) := by
  have hinj : Function.Injective (orbitDilation q) := by
    intro j k he
    exact pow_right_injective₀ q.property.1 hq (congrArg Subtype.val he)
  exact zetaDilation_differentialIndependent_thetaGamma.comp (orbitDilation q) hinj

/-- The unique degenerate positive algebraic multiplier is one. -/
theorem mahlerZetaMero_differentialIndependent_iff (q : Dilation) :
    DifferentialIndependent ↥ModularThetaCoefficients.thetaGammaCoefficientField
      (mahlerZetaMero q) ↔ q.val ≠ 1 := by
  constructor
  · intro h hq
    have ha : AlgebraicIndependent ↥ModularThetaCoefficients.thetaGammaCoefficientField
        (fun p : ℕ × ℕ => differentialJet p.2 (mahlerZetaMero q p.1)) := h
    have he : differentialJet 0 (mahlerZetaMero q 0) = differentialJet 0 (mahlerZetaMero q 1) := by
      change zetaDilationMero (orbitDilation q 0) = zetaDilationMero (orbitDilation q 1)
      congr 1
      apply Subtype.ext
      simp only [orbitDilation,pow_zero,pow_one,hq]
    have hn : ((0,0) : ℕ × ℕ) = (1,0) := ha.injective he
    exact Nat.zero_ne_one (congrArg Prod.fst hn)
  · exact mahlerZetaMero_differentialIndependent q

/-- No nonzero differential–Mahler polynomial over the concrete theta–Gamma field
vanishes at a positive algebraic orbit with multiplier different from one. -/
theorem mahlerZeta_no_polynomial_relation (q : Dilation) (hq : q.val ≠ 1)
    (P : MvPolynomial (ℕ × ℕ) ↥ModularThetaCoefficients.thetaGammaCoefficientField)
    (hP : P ≠ 0) :
    MvPolynomial.aeval (fun p : ℕ × ℕ => differentialJet p.2 (mahlerZetaMero q p.1)) P ≠ 0 :=
  fun he => hP ((mahlerZetaMero_differentialIndependent q hq).eq_zero_of_aeval_eq_zero P he)

/-- The orbit representative is exactly `s ↦ ζ(q^j s)`. -/
theorem mahlerZeta_representative (q : Dilation) (j : ℕ) :
    upperEndAnalyticSubring.subtype
      (physicalZetaAnalytic (orbitDilation q j).val (orbitDilation q j).property.1) =
      Germ.coeRingHom upperEndFilter (fun s : ℂ => riemannZeta (((q.val : ℂ)^j)*s)) := by
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall fun s => by
    simp only [dilate,orbitDilation,Complex.ofReal_pow]

#print axioms finite_dilations_differentialIndependent_gamma
#print axioms zetaDilation_differentialIndependent_gamma
#print axioms zetaDilation_differentialIndependent_thetaGamma
#print axioms mahlerZetaMero_differentialIndependent_iff
#print axioms mahlerZeta_no_polynomial_relation
#print axioms mahlerZeta_representative
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.GammaAlgebraic
