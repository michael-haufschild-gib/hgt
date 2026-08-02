import GaloisForLFunctions.HTGeometry.VerticalFlatGermElimination
import GaloisForLFunctions.HTGeometry.UpperEndJetTransport
import GaloisForLFunctions.HTGeometry.JetHypertranscendenceBridge
import GaloisForLFunctions.HTGeometry.UpperEndRatfuncDifferentialAlgebra
import GaloisForLFunctions.HTGeometry.DigammaFieldJetPresentation
import GaloisForLFunctions.HTGeometry.GammaFieldRatDatum
import GaloisForLFunctions.HTGeometry.GammaFieldGeneratedByDigamma
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# Hölder's theorem in the carrier: the digamma element is hypertranscendental over `ℂ(s)`

A relation among the digamma jets with coefficients in `ℂ(s)` would make a nonzero jet polynomial
vanish identically at the upper end.  A function vanishing there vanishes on every vertical line
beyond a height, hence decays faster than every power — it is *flat* — and the corpus's flat
elimination forbids that for a nonzero jet polynomial.  So no relation exists: `ψ` is
hypertranscendental over `ℂ(s)`, the analytic form of eq. (16).
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance digHTDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance digHTIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance digHTDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance digHTComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance digHTRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance digHTRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance digHTRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- The jet polynomial attached to a family of polynomial coefficients and exponent vectors. -/
def jetMvPoly {n N : ℕ} (e : Fin N → Fin (n + 1) → ℕ) (p : Fin N → Polynomial ℂ) :
    MvPolynomial (Fin (n + 1)) (RatFunc ℂ) :=
  ∑ α : Fin N, MvPolynomial.monomial
    (Finsupp.indicator (Finset.univ : Finset (Fin (n + 1))) (fun i _ => e α i))
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) (p α))

/-- With distinct exponent vectors and nonzero coefficients the jet polynomial is nonzero. -/
theorem jetMvPoly_ne_zero {n N : ℕ} (hN : 0 < N) {e : Fin N → Fin (n + 1) → ℕ}
    (he : Function.Injective e) {p : Fin N → Polynomial ℂ} (hp : ∀ α, p α ≠ 0) :
    jetMvPoly e p ≠ 0 := by
  classical
  set d : Fin N → (Fin (n + 1) →₀ ℕ) :=
    fun α => Finsupp.indicator (Finset.univ : Finset (Fin (n + 1))) (fun i _ => e α i) with hd
  have hdinj : Function.Injective d := by
    intro α β hab
    refine he ?_
    funext i
    have := congrArg (fun f : Fin (n + 1) →₀ ℕ => f i) hab
    simpa [hd, Finsupp.indicator_apply] using this
  intro h0
  have hcoeff : MvPolynomial.coeff (d ⟨0, hN⟩) (jetMvPoly e p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p ⟨0, hN⟩) := by
    rw [jetMvPoly, MvPolynomial.coeff_sum, Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro β _ hβ
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro hdd
      exact hβ (hdinj hdd)
    · intro hmem
      exact absurd (Finset.mem_univ (⟨0, hN⟩ : Fin N)) hmem
  rw [h0, MvPolynomial.coeff_zero] at hcoeff
  exact hp ⟨0, hN⟩ (RatFunc.algebraMap_injective ℂ (by rw [← hcoeff, map_zero]))

/-- **The jet polynomial evaluates to the germ of the corresponding function.** -/
theorem digammaJetEval_jetMvPoly (σ₀ : ℝ) {n N : ℕ} (e : Fin N → Fin (n + 1) → ℕ)
    (p : Fin N → Polynomial ℂ) :
    digammaJetEval σ₀ (n + 1) (jetMvPoly e p)
      = ((fun z : ℂ => ∑ α : Fin N, (p α).eval z
          * ∏ i : Fin (n + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ e α i : ℂ → ℂ) :
        HalfPlaneGerm σ₀) := by
  classical
  set Φ : (ℂ → ℂ) →+* HalfPlaneGerm σ₀ := Filter.Germ.coeRingHom (halfPlaneUpper σ₀) with hΦ
  have hmono : ∀ α : Fin N,
      digammaJetEval σ₀ (n + 1) (MvPolynomial.monomial
        (Finsupp.indicator (Finset.univ : Finset (Fin (n + 1))) (fun i _ => e α i))
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (p α)))
        = Φ (fun z : ℂ => (p α).eval z)
          * ∏ i : Fin (n + 1), Φ (fun z : ℂ => iteratedDeriv (i : ℕ) Complex.digamma z) ^ e α i := by
    intro α
    have hsplit : (MvPolynomial.monomial
        (Finsupp.indicator (Finset.univ : Finset (Fin (n + 1))) (fun i _ => e α i))
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (p α)) : MvPolynomial (Fin (n + 1)) (RatFunc ℂ))
        = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) (p α))
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) (RatFunc ℂ))
            ^ (e α i) := by
      rw [MvPolynomial.prod_X_pow (fun i => e α i) Finset.univ, MvPolynomial.C_mul_monomial,
        mul_one]
    have hfac : ∀ i : Fin (n + 1), digammaJetEval σ₀ (n + 1) (MvPolynomial.X i ^ e α i)
        = Φ (fun z : ℂ => iteratedDeriv (i : ℕ) Complex.digamma z) ^ e α i := by
      intro i
      rw [map_pow, digammaJetEval_X, digammaJetGerm]
      rfl
    rw [hsplit, map_mul, map_prod, Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => hfac i),
      digammaJetEval_C, ratGerm_algebraMap]
    rfl
  have hgoal : ((fun z : ℂ => ∑ α : Fin N, (p α).eval z
      * ∏ i : Fin (n + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ e α i : ℂ → ℂ) :
      HalfPlaneGerm σ₀)
      = ∑ α : Fin N, Φ (fun z : ℂ => (p α).eval z)
        * ∏ i : Fin (n + 1), Φ (fun z : ℂ => iteratedDeriv (i : ℕ) Complex.digamma z) ^ e α i := by
    have hpush : ∑ α : Fin N, Φ (fun z : ℂ => (p α).eval z)
        * ∏ i : Fin (n + 1), Φ (fun z : ℂ => iteratedDeriv (i : ℕ) Complex.digamma z) ^ e α i
        = Φ (∑ α : Fin N, (fun z : ℂ => (p α).eval z)
            * ∏ i : Fin (n + 1), (fun z : ℂ => iteratedDeriv (i : ℕ) Complex.digamma z) ^ e α i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_mul, map_prod]
      simp only [map_pow]
    rw [hpush]
    congr 1
    funext z
    simp [Finset.sum_apply, Finset.prod_apply]
  rw [jetMvPoly, map_sum, Finset.sum_congr rfl fun α _ => hmono α, hgoal]

/-- A function vanishing at the upper end is flat on every vertical line. -/
theorem isVertFlat_of_eventually_zero {f : ℂ → ℂ} (hf : ∀ᶠ z : ℂ in upperEndFilter, f z = 0)
    (σ₀ : ℝ) : IsVertFlat σ₀ f := by
  intro M σ _
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_line_of_upperEnd hf σ] with t ht
  rw [ht]
  simp

/-- The relation, transported to the analytic subring. -/
theorem algebraMap_digammaJetSum {n N : ℕ} (e : Fin N → Fin (n + 1) → ℕ)
    (p : Fin N → Polynomial ℂ) :
    algebraMap upperEndAnalyticSubring upperEndMeroField
      (∑ α : Fin N, upperEndPolyToAnalytic (p α)
        * ∏ i : Fin (n + 1), (upperEndAnalyticDeriv^[(i : ℕ)] digammaAnalytic) ^ (e α i))
      = ∑ α : Fin N, upperEndPolyToMero (p α)
        * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) digammaMero) ^ (e α i) := by
  have hjet : ∀ i : ℕ, algebraMap upperEndAnalyticSubring upperEndMeroField
      (upperEndAnalyticDeriv^[i] digammaAnalytic) = differentialJet i digammaMero :=
    fun i => (digammaJetMero_eq_algebraMap i).symm
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, map_prod,
    Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => by
      rw [map_pow, hjet (i : ℕ)])]
  rfl

/-- The analytic element of the relation is the germ of the jet-polynomial function. -/
theorem subtype_digammaJetSum {n N : ℕ} (e : Fin N → Fin (n + 1) → ℕ)
    (p : Fin N → Polynomial ℂ) :
    upperEndAnalyticSubring.subtype (∑ α : Fin N, upperEndPolyToAnalytic (p α)
        * ∏ i : Fin (n + 1), (upperEndAnalyticDeriv^[(i : ℕ)] digammaAnalytic) ^ (e α i))
      = Germ.coeRingHom upperEndFilter (fun z : ℂ => ∑ α : Fin N, (p α).eval z
        * ∏ i : Fin (n + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ e α i) := by
  rw [map_sum]
  have hterm : ∀ α : Fin N, upperEndAnalyticSubring.subtype (upperEndPolyToAnalytic (p α)
      * ∏ i : Fin (n + 1), (upperEndAnalyticDeriv^[(i : ℕ)] digammaAnalytic) ^ (e α i))
      = Germ.coeRingHom upperEndFilter (fun z : ℂ => (p α).eval z
        * ∏ i : Fin (n + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ e α i) := by
    intro α
    rw [map_mul, polyToAnalytic_subtype, map_prod]
    have hfac : ∀ i : Fin (n + 1),
        upperEndAnalyticSubring.subtype ((upperEndAnalyticDeriv^[(i : ℕ)] digammaAnalytic)
          ^ (e α i))
        = Germ.coeRingHom upperEndFilter
          (fun z : ℂ => iteratedDeriv (i : ℕ) Complex.digamma z ^ e α i) := by
      intro i
      rw [map_pow, show upperEndAnalyticSubring.subtype
        (upperEndAnalyticDeriv^[(i : ℕ)] digammaAnalytic)
          = Germ.coeRingHom upperEndFilter (iteratedDeriv (i : ℕ) Complex.digamma) from
        digammaJet_analytic_coe (i : ℕ), ← map_pow]
      rfl
    rw [Finset.prod_congr rfl fun i _ => hfac i, ← map_prod, ← map_mul]
    refine congrArg _ ?_
    funext z
    simp
  rw [Finset.sum_congr rfl fun α _ => hterm α, ← map_sum]
  refine congrArg _ ?_
  funext z
  simp

/-- **No relation among the digamma jets with polynomial coefficients.** -/
theorem no_digamma_jet_relation_poly {n N : ℕ} (hN : 0 < N) {e : Fin N → Fin (n + 1) → ℕ}
    (he : Function.Injective e) {p : Fin N → Polynomial ℂ} (hp : ∀ α, p α ≠ 0) :
    ∑ α : Fin N, upperEndPolyToMero (p α)
      * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) digammaMero) ^ (e α i) ≠ 0 := by
  intro hrel
  have hW0 : (∑ α : Fin N, upperEndPolyToAnalytic (p α)
      * ∏ i : Fin (n + 1), (upperEndAnalyticDeriv^[(i : ℕ)] digammaAnalytic) ^ (e α i)) = 0 := by
    refine IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField ?_
    rw [algebraMap_digammaJetSum, hrel, map_zero]
  have hzero : Germ.coeRingHom upperEndFilter (fun z : ℂ => ∑ α : Fin N, (p α).eval z
      * ∏ i : Fin (n + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ e α i) = 0 := by
    rw [← subtype_digammaJetSum e p, hW0, map_zero]
  rw [← Germ.coe_zero] at hzero
  have hev : ∀ᶠ z : ℂ in upperEndFilter, (fun z : ℂ => ∑ α : Fin N, (p α).eval z
      * ∏ i : Fin (n + 1), iteratedDeriv (i : ℕ) Complex.digamma z ^ e α i) z = 0 := by
    have h := Filter.Germ.coe_eq.mp hzero
    filter_upwards [h] with z hz
    exact hz
  refine not_isVertFlatGerm_digammaJetEval (σ₀ := 0) le_rfl (jetMvPoly_ne_zero hN he hp) ?_
  rw [digammaJetEval_jetMvPoly]
  exact isVertFlat_of_eventually_zero hev 0

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance digHT2Domain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance digHT2IntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance digHT2Differential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance digHT2ComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance digHT2RatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance digHT2RatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance digHT2RatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- Clearing the denominators of a finite family of rational functions. -/
theorem exists_polynomial_clearing {N : ℕ} (c : Fin N → RatFunc ℂ) (hc : ∀ α, c α ≠ 0) :
    ∃ (D : Polynomial ℂ) (p : Fin N → Polynomial ℂ), D ≠ 0 ∧ (∀ α, p α ≠ 0) ∧
      ∀ α, algebraMap (Polynomial ℂ) (RatFunc ℂ) (p α)
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) D * c α := by
  classical
  refine ⟨∏ β : Fin N, (c β).denom,
    fun α => (c α).num * ∏ β ∈ Finset.univ.erase α, (c β).denom, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun β _ => RatFunc.denom_ne_zero (c β)
  · intro α
    exact mul_ne_zero (RatFunc.num_ne_zero (hc α))
      (Finset.prod_ne_zero_iff.mpr fun β _ => RatFunc.denom_ne_zero (c β))
  · intro α
    have hsplit : (∏ β : Fin N, (c β).denom)
        = (c α).denom * ∏ β ∈ Finset.univ.erase α, (c β).denom :=
      (Finset.mul_prod_erase Finset.univ (fun β => (c β).denom) (Finset.mem_univ α)).symm
    have hden : algebraMap (Polynomial ℂ) (RatFunc ℂ) ((c α).denom) ≠ 0 := by
      intro h0
      exact RatFunc.denom_ne_zero (c α) (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
    have hnum : algebraMap (Polynomial ℂ) (RatFunc ℂ) ((c α).denom) * c α
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) ((c α).num) := by
      rw [mul_comm]
      exact ((div_eq_iff hden).mp (RatFunc.num_div_denom (c α))).symm
    rw [hsplit, map_mul, map_mul, ← hnum]
    ring

/-- **No relation among the digamma jets with coefficients in `ℂ(s)`.** -/
theorem no_digamma_jet_relation {n N : ℕ} (hN : 0 < N) {e : Fin N → Fin (n + 1) → ℕ}
    (he : Function.Injective e) {c : Fin N → RatFunc ℂ} (hc : ∀ α, c α ≠ 0) :
    ∑ α : Fin N, algebraMap (RatFunc ℂ) upperEndMeroField (c α)
      * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) digammaMero) ^ (e α i) ≠ 0 := by
  classical
  intro hrel
  obtain ⟨D, p, hD, hp, hpc⟩ := exists_polynomial_clearing c hc
  refine no_digamma_jet_relation_poly hN he hp ?_
  have hterm : ∀ α : Fin N, upperEndPolyToMero (p α)
      = upperEndPolyToMero D * algebraMap (RatFunc ℂ) upperEndMeroField (c α) := by
    intro α
    have h1 : upperEndPolyToMero (p α)
        = upperEndRatfuncToMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) (p α)) :=
      (upperEndRatfuncToMero_algebraMap_polynomial (p α)).symm
    have h2 : upperEndPolyToMero D
        = upperEndRatfuncToMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) D) :=
      (upperEndRatfuncToMero_algebraMap_polynomial D).symm
    rw [h1, h2, hpc α, map_mul]
    rfl
  calc ∑ α : Fin N, upperEndPolyToMero (p α)
      * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) digammaMero) ^ (e α i)
      = upperEndPolyToMero D * ∑ α : Fin N, algebraMap (RatFunc ℂ) upperEndMeroField (c α)
        * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) digammaMero) ^ (e α i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hterm α, mul_assoc]
    _ = 0 := by rw [hrel, mul_zero]

/-- **Hölder's theorem for the digamma element.**  `ψ` is hypertranscendental over `ℂ(s)`: no
nontrivial algebraic differential equation with rational-function coefficients holds for it. -/
theorem hypertranscendentalOver_ratFunc_digammaMero :
    HypertranscendentalOver (RatFunc ℂ) digammaMero :=
  hypertranscendentalOver_of_no_jet_relation
    (fun _ _ hN _ he _ hc => no_digamma_jet_relation hN he hc)

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance digHT3Domain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance digHT3IntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance digHT3Differential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance digHT3ComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance digHT3RatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance digHT3RatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance digHT3RatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

local instance digHT3CharZero : CharZero upperEndMeroField :=
  charZero_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective ℂ upperEndMeroField)

/-- **Hölder's theorem.**  The Euler Gamma function is hypertranscendental over `ℂ(s)`: it satisfies
no algebraic differential equation with rational-function coefficients.  If it did, its logarithmic
derivative `ψ = Γ′/Γ` would be differentially algebraic too, and it is not. -/
theorem hypertranscendentalOver_ratFunc_gammaUpperMero :
    HypertranscendentalOver (RatFunc ℂ) gammaUpperMero := by
  intro hDA
  refine hypertranscendentalOver_ratFunc_digammaMero ?_
  have hderiv : DifferentialAlgebraicOver (RatFunc ℂ) (gammaUpperMero)′ :=
    differentialAlgebraicOver_deriv hDA
  have hinv : DifferentialAlgebraicOver (RatFunc ℂ) gammaUpperMero⁻¹ :=
    differentialAlgebraicOver_inv hDA
  have hpsi : digammaMero = (gammaUpperMero)′ * gammaUpperMero⁻¹ := by
    rw [deriv_gammaUpperMero, mul_comm, ← mul_assoc, inv_mul_cancel₀ gammaUpperMero_ne_zero,
      one_mul]
  rw [hpsi]
  exact differentialAlgebraicOver_mul hderiv hinv

end

end GaloisForLFunctions.HTGeometry
