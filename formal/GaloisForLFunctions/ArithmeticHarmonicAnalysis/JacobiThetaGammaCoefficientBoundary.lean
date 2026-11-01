import GaloisForLFunctions.Bottcher.Ramanujan
import GaloisForLFunctions.HTGeometry.FiniteGeneratorDifferentialEscape
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicBaseChange
import GaloisForLFunctions.HTGeometry.ZetaHypertranscendence

/-!
# Jacobi theta–Gamma coefficient boundary

The actual variable-modulus theta constants and `E₂` satisfy a closed polynomial
system in the same upper-end meromorphic field as zeta and Gamma. Their ordinary
four-generator field is consequently a differential field of finite transcendence
degree, and every element is differentially algebraic over `ℂ(τ)`.

Adjoining these concrete coefficients and all their jets to `ℂ(τ)⟨Γ⟩` preserves
and reflects every joint differential independence. Zeta and every Dirichlet
`L`-function remain hypertranscendental over the resulting theta–Gamma field.
The result concerns finite algebraic differential equations; it asserts no
obstruction to special-value period relations or to q-difference realizations.
-/

open Complex Filter Set Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Bottcher
open scoped Differential

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.ModularThetaCoefficients

/-- Common coefficient in the theta–Eisenstein differential system. -/
def kappa : ℂ := (Real.pi : ℂ) * I / 12

/-- The actual theta constants `θ₂, θ₃, θ₄` and Eisenstein `E₂`, in that order. -/
def source (i : Fin 4) : ℂ → ℂ :=
  match i.val with
  | 0 => thetaTwo
  | 1 => thetaThree
  | 2 => thetaFour
  | _ => EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex

/-- Polynomial vector field for the four theta–Eisenstein coordinates. -/
def rhs {R : Type*} [CommRing R] (k : R) (x : Fin 4 → R) (i : Fin 4) : R :=
  match i.val with
  | 0 => k * x 0 * (x 3 + x 0 ^ 4 + 2 * x 2 ^ 4)
  | 1 => k * x 1 * (x 3 + x 0 ^ 4 - x 2 ^ 4)
  | 2 => k * x 2 * (x 3 - 2 * x 0 ^ 4 - x 2 ^ 4)
  | _ => k * (2 * x 3 ^ 2 - x 0 ^ 8 - x 1 ^ 8 - x 2 ^ 8)

private theorem theta_log_derivatives {z : ℂ} (hz : 0 < z.im) :
    deriv thetaTwo z / thetaTwo z =
        kappa * (EisensteinSeries.E2 ⟨z, hz⟩ + thetaTwo z ^ 4 + 2 * thetaFour z ^ 4) ∧
    deriv thetaFour z / thetaFour z =
        kappa * (EisensteinSeries.E2 ⟨z, hz⟩ - 2 * thetaTwo z ^ 4 - thetaFour z ^ 4) := by
  have h2 := thetaTwo_ne_zero_of_im_pos hz
  have h3 := thetaThree_ne_zero_of_im_pos hz
  have hW := thetaWronskian23 hz
  have hWlog : deriv thetaTwo z / thetaTwo z - deriv thetaThree z / thetaThree z =
      (Real.pi : ℂ) * I / 4 * thetaFour z ^ 4 := by
    field_simp [h2, h3]
    linear_combination 4 * hW
  have ht := thetaThree_logDeriv_eq_E2 hz
  have hp := thetaProduct_logDeriv_eq_E2 hz
  unfold kappa
  constructor
  · linear_combination hWlog + ht
  · linear_combination hp - hWlog - 2 * ht

/-- The four actual modular functions satisfy a closed polynomial system. -/
theorem source_deriv {z : ℂ} (hz : 0 < z.im) (i : Fin 4) :
    deriv (source i) z = rhs kappa (fun j => source j z) i := by
  have h2 := (div_eq_iff (thetaTwo_ne_zero_of_im_pos hz)).mp (theta_log_derivatives hz).1
  have h3 := (div_eq_iff (thetaThree_ne_zero_of_im_pos hz)).mp (thetaThree_logDeriv_eq_E2 hz)
  have h4 := (div_eq_iff (thetaFour_ne_zero_of_im_pos hz)).mp (theta_log_derivatives hz).2
  have hE := deriv_eisensteinSeries_E2_comp_ofComplex (⟨z, hz⟩ : UpperHalfPlane)
  have hE4 := eisensteinSeries_E4_eq_theta_nullwerte (⟨z, hz⟩ : UpperHalfPlane)
  have hz' : UpperHalfPlane.ofComplex z = ⟨z, hz⟩ :=
    UpperHalfPlane.ofComplex_apply_of_im_pos hz
  fin_cases i
  · change deriv thetaTwo z = kappa * thetaTwo z *
      (EisensteinSeries.E2 (UpperHalfPlane.ofComplex z) + thetaTwo z ^ 4 + 2 * thetaFour z ^ 4)
    rw [hz']
    unfold kappa at h2 ⊢
    linear_combination h2
  · change deriv thetaThree z = kappa * thetaThree z *
      (EisensteinSeries.E2 (UpperHalfPlane.ofComplex z) + thetaTwo z ^ 4 - thetaFour z ^ 4)
    rw [hz']
    unfold kappa
    linear_combination h3
  · change deriv thetaFour z = kappa * thetaFour z *
      (EisensteinSeries.E2 (UpperHalfPlane.ofComplex z) - 2 * thetaTwo z ^ 4 - thetaFour z ^ 4)
    rw [hz']
    unfold kappa at h4 ⊢
    linear_combination h4
  · change deriv (EisensteinSeries.E2 ∘ UpperHalfPlane.ofComplex) z = kappa *
      (2 * EisensteinSeries.E2 (UpperHalfPlane.ofComplex z) ^ 2 -
        thetaTwo z ^ 8 - thetaThree z ^ 8 - thetaFour z ^ 8)
    rw [hz']
    unfold kappa
    rw [hE, hE4]
    ring

section AnalyticRealization

local instance : IsDomain upperEndAnalyticSubring := isDomain_upperEndAnalyticSubring
local instance : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
local instance : Differential upperEndMeroField := upperEndMeroFieldDifferential
local instance : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
local instance : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective
local instance : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
local instance : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
local instance : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncDifferentialAlgebra

private theorem source_analytic (i : Fin 4) : AnalyticOnNhd ℂ (source i) (upperTail 0) := by
  apply DifferentiableOn.analyticOnNhd _ (upperTail_isOpen 0)
  fin_cases i
  · exact fun z hz => (differentiableAt_thetaTwo hz).differentiableWithinAt
  · exact fun z hz => (differentiableAt_thetaThree hz).differentiableWithinAt
  · exact fun z hz => (differentiableAt_thetaFour hz).differentiableWithinAt
  · exact UpperHalfPlane.mdifferentiable_iff.mp E2_mdifferentiable

/-- The source functions as their actual upper-end analytic germs. -/
def sourceAnalytic (i : Fin 4) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (source i), source i, 0, source_analytic i, rfl⟩

/-- The same source functions in the meromorphic carrier containing zeta and Gamma. -/
def sourceMero (i : Fin 4) : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField (sourceAnalytic i)

private theorem rhs_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : R) (x : Fin 4 → R) (i : Fin 4) :
    f (rhs k x i) = rhs (f k) (fun j => f (x j)) i := by
  fin_cases i <;> dsimp only [rhs] <;>
    simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]

private theorem sourceAnalytic_deriv (i : Fin 4) :
    upperEndAnalyticDeriv (sourceAnalytic i) =
      rhs (upperEndPolyToAnalytic (Polynomial.C kappa)) sourceAnalytic i := by
  apply Subtype.ext
  change (deriv (source i) : Germ upperEndFilter ℂ) = _
  have hcoerce : ((rhs (upperEndPolyToAnalytic (Polynomial.C kappa)) sourceAnalytic i :
      upperEndAnalyticSubring) : Germ upperEndFilter ℂ) =
      ((fun z => rhs kappa (fun j => source j z) i) : Germ upperEndFilter ℂ) := by
    have hc : ((upperEndPolyToAnalytic (Polynomial.C kappa) : upperEndAnalyticSubring) :
        Germ upperEndFilter ℂ) = ((fun _ : ℂ => kappa) : Germ upperEndFilter ℂ) := by
      change ((fun z => (Polynomial.C kappa).eval z) : Germ upperEndFilter ℂ) = _
      simp only [Polynomial.eval_C]
    change upperEndAnalyticSubring.subtype
      (rhs (upperEndPolyToAnalytic (Polynomial.C kappa)) sourceAnalytic i) = _
    rw [rhs_map]
    change rhs ((upperEndPolyToAnalytic (Polynomial.C kappa) : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) (fun j => ((sourceAnalytic j : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ)) i = _
    rw [hc]
    fin_cases i <;> rfl
  rw [hcoerce, Germ.coe_eq]
  exact upperEndFilter_basis.eventually_iff.mpr ⟨0, trivial, fun z hz => source_deriv hz i⟩

/-- Ordinary complex differentiation descends to the polynomial source system. -/
theorem sourceMero_deriv (i : Fin 4) :
    (sourceMero i)′ = rhs (upperEndPolyToMero (Polynomial.C kappa)) sourceMero i := by
  rw [sourceMero, upperEndMeroFieldDifferential_algebraMap, sourceAnalytic_deriv]
  exact rhs_map (algebraMap upperEndAnalyticSubring upperEndMeroField)
    (upperEndPolyToAnalytic (Polynomial.C kappa)) sourceAnalytic i

/-- The ordinary rational function field generated by the four modular sources. -/
def modularField : IntermediateField (RatFunc ℂ) upperEndMeroField :=
  IntermediateField.adjoin (RatFunc ℂ) (range sourceMero)

private theorem sourceMero_mem (i : Fin 4) : sourceMero i ∈ modularField :=
  IntermediateField.subset_adjoin _ _ (mem_range_self i)

private theorem rhs_mem {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (k : E) (x : Fin 4 → E)
    (hk : k ∈ K) (hx : ∀ j, x j ∈ K) (i : Fin 4) : rhs k x i ∈ K := by
  have hp (j : Fin 4) (n : ℕ) : x j ^ n ∈ K := pow_mem (hx j) n
  have h2 : (2 : E) ∈ K := K.natCast_mem 2
  fin_cases i <;> dsimp only [rhs]
  · exact K.mul_mem (K.mul_mem hk (hx 0))
      (K.add_mem (K.add_mem (hx 3) (hp 0 4)) (K.mul_mem h2 (hp 2 4)))
  · exact K.mul_mem (K.mul_mem hk (hx 1))
      (K.sub_mem (K.add_mem (hx 3) (hp 0 4)) (hp 2 4))
  · exact K.mul_mem (K.mul_mem hk (hx 2))
      (K.sub_mem (K.sub_mem (hx 3) (K.mul_mem h2 (hp 0 4))) (hp 2 4))
  · exact K.mul_mem hk (K.sub_mem (K.sub_mem (K.sub_mem
      (K.mul_mem h2 (hp 3 2)) (hp 0 8)) (hp 1 8)) (hp 2 8))

private theorem sourceMero_deriv_mem (i : Fin 4) : (sourceMero i)′ ∈ modularField := by
  rw [sourceMero_deriv]
  apply rhs_mem modularField _ sourceMero _ sourceMero_mem i
  rw [← upperEndRatfuncToMero_algebraMap_polynomial]
  exact modularField.algebraMap_mem _

/-- Actual theta and Eisenstein generators are differentially algebraic in zeta's carrier. -/
theorem sourceMero_differentialAlgebraic (i : Fin 4) :
    DifferentialAlgebraicOver (RatFunc ℂ) (sourceMero i) :=
  differentialAlgebraicOver_of_mem_finiteGeneratorState sourceMero
    sourceMero_deriv_mem (sourceMero_mem i)

end AnalyticRealization

section CoefficientBoundary

local instance : IsDomain upperEndAnalyticSubring := isDomain_upperEndAnalyticSubring
local instance : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
local instance : Differential upperEndMeroField := upperEndMeroFieldDifferential
local instance : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
local instance : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective
local instance : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
local instance : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
local instance : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncDifferentialAlgebra
local instance : DifferentialAlgebra ↥gammaCoefficientField upperEndMeroField where
  deriv_algebraMap _ := rfl

/-- The actual finite modular field is closed under differentiation. -/
theorem modularField_derivationClosed : DerivationClosed modularField :=
  derivationClosed_adjoin_range_of_deriv_mem sourceMero sourceMero_deriv_mem

/-- The ordinary four-generator field already contains every theta/Eisenstein jet. -/
theorem differentialAdjoin_source_eq :
    differentialAdjoin (RatFunc ℂ) (range sourceMero) = modularField := by
  apply le_antisymm
  · exact differentialAdjoin_le _
      (by rintro y ⟨i, rfl⟩; exact sourceMero_mem i) modularField_derivationClosed
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro y ⟨i, rfl⟩
    exact differentialJet_mem_differentialAdjoin (RatFunc ℂ) (mem_range_self i) 0

/-- Every rational observable of the modular state is differentially algebraic over `ℂ(τ)`. -/
theorem modularField_differentialAlgebraic {x : upperEndMeroField}
    (hx : x ∈ modularField) : DifferentialAlgebraicOver (RatFunc ℂ) x :=
  differentialAlgebraicOver_of_mem_finiteGeneratorState sourceMero sourceMero_deriv_mem hx

private theorem sourceMero_gamma_differentialAlgebraic (i : Fin 4) :
    DifferentialAlgebraicOver ↥gammaCoefficientField (sourceMero i) :=
  differentialAlgebraicOver_mono (sourceMero_differentialAlgebraic i)

/-- Gamma together with the actual modular theta constants, Eisenstein `E₂`, and all their jets. -/
def thetaGammaCoefficientField :=
  differentialAdjoin ↥gammaCoefficientField (range sourceMero)

private theorem source_range_gamma_differentialAlgebraic :
    ∀ x ∈ range sourceMero, DifferentialAlgebraicOver ↥gammaCoefficientField x := by
  rintro x ⟨i, rfl⟩
  exact sourceMero_gamma_differentialAlgebraic i

/-- Adding these concrete theta coefficients preserves every joint differential independence. -/
theorem thetaGamma_differentialIndependent_iff {ι : Type*}
    (x : ι → upperEndMeroField) :
    DifferentialIndependent ↥thetaGammaCoefficientField x ↔
      DifferentialIndependent ↥gammaCoefficientField x :=
  differentialIndependent_differentialAdjoin_iff source_range_gamma_differentialAlgebraic

/-- The exact DA/HT boundary is unchanged for every upper-end meromorphic observable. -/
theorem thetaGamma_hypertranscendental_iff (x : upperEndMeroField) :
    HypertranscendentalOver ↥thetaGammaCoefficientField x ↔
      HypertranscendentalOver ↥gammaCoefficientField x :=
  hypertranscendentalOver_differentialAdjoin_iff source_range_gamma_differentialAlgebraic

/-- No finite algebraic differential equation for zeta is unlocked by theta–Gamma coefficients. -/
theorem zeta_hypertranscendentalOver_thetaGamma :
    HypertranscendentalOver ↥thetaGammaCoefficientField
      (algebraMap upperEndAnalyticSubring upperEndMeroField zetaUpperAnalytic) :=
  (thetaGamma_hypertranscendental_iff _).mpr
    (zeta_hypertranscendentalOver_gammaCoefficientField (σ := 2) (by norm_num))

/-- The same concrete coefficient obstruction holds for every Dirichlet `L`-function. -/
theorem lfunction_hypertranscendentalOver_thetaGamma {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    HypertranscendentalOver ↥thetaGammaCoefficientField
      (algebraMap upperEndAnalyticSubring upperEndMeroField (lfunctionUpperAnalytic χ)) :=
  (thetaGamma_hypertranscendental_iff _).mpr
    (lfunction_hypertranscendentalOver_gammaCoefficientField χ (σ := 2) (by norm_num))

end CoefficientBoundary

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.ModularThetaCoefficients

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.ModularThetaCoefficients.source_deriv
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.ModularThetaCoefficients.sourceMero_differentialAlgebraic
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.ModularThetaCoefficients.differentialAdjoin_source_eq
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.ModularThetaCoefficients.thetaGamma_differentialIndependent_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.ModularThetaCoefficients.zeta_hypertranscendentalOver_thetaGamma
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.ModularThetaCoefficients.lfunction_hypertranscendentalOver_thetaGamma
