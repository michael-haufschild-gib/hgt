import GaloisForLFunctions.HTGeometry.PrimeClockCompletionCorrespondence
import GaloisForLFunctions.HTGeometry.FiniteAbscissaRationalCoordinateIndependence
import GaloisForLFunctions.RHTower.CanonicalEulerLog

/-!
# Analytic Euler completion from the prime-clock module

This module transfers the scalar prime-clock completion boundary to actual finite-abscissa
Dirichlet germs over the genuine rational coordinate field.  The analytic base contains every
prime-zeta valuation layer at once.  The Euler logarithm profile remains differentially
independent over that single countably generated field.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Filter Set
open scoped Differential LSeries.notation

noncomputable section

local instance primeClockAnalyticUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance primeClockAnalyticUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance primeClockAnalyticUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- A uniformly bounded scalar valuation profile, replicated on every prime ray, has finite
abscissa of absolute convergence. -/
def boundedScalarReplicatedFiniteAbscissa
    (u : Nat → ℂ) (M : ℝ) (hu : ∀ e, ‖u e‖ ≤ M) :
    finiteAbscissaArithmeticSubalgebra := by
  refine ⟨scalarReplicatedPrimeProfile u, 1, ?_⟩
  intro y hy
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := M)
  · intro n hn
    by_cases hpow : IsPrimePow n
    · simpa [scalarReplicatedPrimeProfile, hpow] using
        hu (Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩).2
    · simpa [scalarReplicatedPrimeProfile, hpow] using
        (norm_nonneg (u 0)).trans (hu 0)
  · simpa using hy

@[simp]
theorem boundedScalarReplicatedFiniteAbscissa_val
    (u : Nat → ℂ) (M : ℝ) (hu : ∀ e, ‖u e‖ ≤ M) :
    (boundedScalarReplicatedFiniteAbscissa u M hu).1 =
      scalarReplicatedPrimeProfile u :=
  rfl

/-- The replicated Euler valuation profile is exactly the classical coefficient stream
`Lambda(n) / log n` of the canonical Euler logarithm. -/
theorem scalarReplicatedPrimeProfile_eulerLogValuationProfile :
    scalarReplicatedPrimeProfile eulerLogValuationProfile =
      RHTower.eulerLogDirichletCoeff := by
  classical
  ext n
  by_cases hpow : IsPrimePow n
  · let x : PrimePowerClockIndex :=
      Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
    have hx := congrArg Subtype.val
      (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
    have hn : (x.1 : Nat) ^ (x.2 + 1) = n := by
      simpa only [x, Nat.Primes.coe_prodNatEquiv_apply] using hx
    rw [← hn]
    have hcoord :=
      primePowerCoordinateProfile_scalarReplicatedPrimeProfile
        eulerLogValuationProfile x
    change scalarReplicatedPrimeProfile eulerLogValuationProfile
        ((x.1 : Nat) ^ (x.2 + 1)) = eulerLogValuationProfile x.2 at hcoord
    rw [hcoord, eulerLogValuationProfile,
      RHTower.eulerLogDirichletCoeff_prime_pow_succ
        (x.1 : Nat) x.2 x.1.2]
    norm_num [Nat.cast_add, Nat.cast_one]
  · rw [RHTower.eulerLogDirichletCoeff_eq_zero_of_not_primePower hpow]
    simp [scalarReplicatedPrimeProfile, hpow]

/-- Actual upper-end meromorphic carrier of one bounded replicated valuation profile. -/
def analyticScalarReplicatedCarrier
    (u : Nat → ℂ) (M : ℝ) (hu : ∀ e, ‖u e‖ ≤ M) :
    upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero
    (boundedScalarReplicatedFiniteAbscissa u M hu)

/-- Formal differential independence over `C` is the exact algebraic input needed to transfer a
finite-abscissa source family to the actual upper-end meromorphic field over `C(z)`. -/
theorem differentialIndependent_finiteAbscissaPrimeProfiles_of_formal
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (f : I → finiteAbscissaArithmeticSubalgebra)
    (hformal : GaloisForLFunctions.DifferentialIndependent ℂ
      (fun i ↦ algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (f i).1)) :
    GaloisForLFunctions.DifferentialIndependent upperEndRationalCoordinateField
      (fun i ↦ finiteAbscissaLSeriesToUpperEndMero (f i)) := by
  let sourceJets : I × Nat → finiteAbscissaArithmeticSubalgebra := fun q ↦
    (finiteAbscissaRotatedDeriv^[q.2]) (f q.1)
  have hformalC : AlgebraicIndependent ℂ
      (fun q : I × Nat ↦ algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
          (primeProfileRotatedLogJet q.2 (f q.1).1)) := by
    unfold GaloisForLFunctions.DifferentialIndependent at hformal
    have hjets : (fun q : I × Nat ↦
        GaloisForLFunctions.differentialJet q.2
          (algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (f q.1).1)) =
        (fun q : I × Nat ↦ algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField
            (primeProfileRotatedLogJet q.2 (f q.1).1)) := by
      funext q
      exact differentialJet_algebraMap_primeProfileRotatedLogJet q.2 (f q.1).1
    rw [hjets] at hformal
    exact hformal
  let arithmeticIncl : ArithmeticFunction ℂ →ₐ[ℂ]
      arithmeticFunctionFractionField :=
    IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
      arithmeticFunctionFractionField
  have harithmetic : AlgebraicIndependent ℂ
      (fun q : I × Nat ↦ primeProfileRotatedLogJet q.2 (f q.1).1) := by
    apply (AlgHom.algebraicIndependent_iff arithmeticIncl
      (FaithfulSMul.algebraMap_injective (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField)).mp
    simpa only [arithmeticIncl] using hformalC
  let finiteIncl : finiteAbscissaArithmeticSubalgebra →ₐ[ℂ]
      ArithmeticFunction ℂ := finiteAbscissaArithmeticSubalgebra.val
  have hfiniteIncl : Function.Injective finiteIncl := by
    intro x y hxy
    exact Subtype.ext hxy
  have hsourceJets : AlgebraicIndependent ℂ sourceJets := by
    apply (AlgHom.algebraicIndependent_iff finiteIncl hfiniteIncl).mp
    convert harithmetic using 1
    funext q
    apply ArithmeticFunction.ext
    intro n
    exact finiteAbscissaRotatedDeriv_iterate_apply (f q.1) q.2 n
  have hanalytic :=
    algebraicIndependent_finiteAbscissaLSeries_over_upperEndRationalCoordinate
      sourceJets hsourceJets
  unfold GaloisForLFunctions.DifferentialIndependent
  convert hanalytic using 1
  funext q
  exact differentialJet_finiteAbscissaLSeriesToUpperEndMero (f q.1) q.2

/-- Finite-abscissa prime-power source families inherit their complete differential spectrum in
the actual upper-end meromorphic field over the genuine rational coordinate. -/
theorem differentialIndependent_finiteAbscissaPrimeProfiles_of_clockIndependent
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (f : I → finiteAbscissaArithmeticSubalgebra)
    (hsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (f i).1)
    (hclock : PrimeProfileClockIndependent (fun i ↦ (f i).1)) :
    GaloisForLFunctions.DifferentialIndependent upperEndRationalCoordinateField
      (fun i ↦ finiteAbscissaLSeriesToUpperEndMero (f i)) := by
  apply differentialIndependent_finiteAbscissaPrimeProfiles_of_formal f
  have hformal : GaloisForLFunctions.DifferentialIndependent
      finitePrimeCoefficientField
      (fun i ↦ algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (f i).1) :=
    (differentialIndependent_fractionPrimeProfiles_iff_clockIndependent
      (fun i ↦ (f i).1) hsupport).mpr hclock
  unfold GaloisForLFunctions.DifferentialIndependent at hformal ⊢
  exact AlgebraicIndependent.restrictScalars
    (FaithfulSMul.algebraMap_injective ℂ finitePrimeCoefficientField) hformal

/-- Actual analytic differential independence of finite bounded replicated profiles is exactly
ordinary profile independence in the direction needed for completion. -/
theorem differentialIndependent_analyticScalarReplicatedCarriers_of_linearIndependent
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (u : I → Nat → ℂ) (M : I → ℝ)
    (hu : ∀ i e, ‖u i e‖ ≤ M i)
    (hlinear : LinearIndependent ℂ u) :
    GaloisForLFunctions.DifferentialIndependent upperEndRationalCoordinateField
      (fun i ↦ analyticScalarReplicatedCarrier (u i) (M i) (hu i)) := by
  let f : I → finiteAbscissaArithmeticSubalgebra := fun i ↦
    boundedScalarReplicatedFiniteAbscissa (u i) (M i) (hu i)
  apply differentialIndependent_finiteAbscissaPrimeProfiles_of_clockIndependent
    f (fun i ↦ scalarReplicatedPrimeProfile_supportedOnPositivePrimePowers (u i))
  apply (scalarReplicatedPrimeProfile_clockIndependent_iff u).mpr hlinear

theorem scalarValuationBasisProfile_norm_le_one (n e : Nat) :
    ‖scalarValuationBasisProfile n e‖ ≤ 1 := by
  by_cases h : e = n <;> simp [scalarValuationBasisProfile, h]

/-- The standard prime-zeta coefficient stream, as a finite-abscissa arithmetic source. -/
def primeZetaFiniteAbscissaSource : finiteAbscissaArithmeticSubalgebra :=
  boundedPrimeFiniteAbscissa (fun _ : Nat.Primes ↦ (1 : ℂ)) (by simp)

/-- The prime zeta function in its absolutely convergent half-plane, written as the ordinary
L-series of the prime indicator. -/
def canonicalPrimeZeta (s : ℂ) : ℂ :=
  LSeries (fun n ↦ (primeZetaFiniteAbscissaSource.1 n)) s

/-- The upper-end germ represented by the prime zeta function after the fixed rotation
`s = -I z`. -/
def analyticPrimeZetaUpperEndGerm : Germ upperEndFilter ℂ :=
  finiteAbscissaLSeriesToUpperEndGerm primeZetaFiniteAbscissaSource

@[simp]
theorem analyticPrimeZetaUpperEndGerm_eq :
    analyticPrimeZetaUpperEndGerm =
      ((fun z : ℂ ↦ canonicalPrimeZeta (-Complex.I * z)) :
        Germ upperEndFilter ℂ) := by
  rfl

/-- Replicating the valuation basis vector at depth `e + 1` is exactly the
`(e + 1)`-st prime-power dilation of the prime indicator. -/
theorem scalarReplicatedPrimeProfile_scalarValuationBasisProfile
    (e : Nat) :
    scalarReplicatedPrimeProfile (scalarValuationBasisProfile e) =
      arithmeticOfPrimePowerColumn e (fun _ : Nat.Primes ↦ (1 : ℂ)) := by
  classical
  ext n
  by_cases hpow : IsPrimePow n
  · let x : PrimePowerClockIndex :=
      Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
    have hx := congrArg Subtype.val
      (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
    have hn : (x.1 : Nat) ^ (x.2 + 1) = n := by
      simpa only [x, Nat.Primes.coe_prodNatEquiv_apply] using hx
    rw [← hn]
    have hcoord :=
      primePowerCoordinateProfile_scalarReplicatedPrimeProfile
        (scalarValuationBasisProfile e) x
    change scalarReplicatedPrimeProfile (scalarValuationBasisProfile e)
        ((x.1 : Nat) ^ (x.2 + 1)) = scalarValuationBasisProfile e x.2 at hcoord
    rw [hcoord]
    by_cases hxe : x.2 = e
    · subst e
      simp [scalarValuationBasisProfile, arithmeticOfPrimePowerColumn_apply]
    · have hnone : ¬ ∃ q : Nat.Primes,
          (x.1 : Nat) ^ (x.2 + 1) = (q : Nat) ^ (e + 1) := by
        rintro ⟨q, hq⟩
        have heq : Nat.Primes.prodNatEquiv x =
            Nat.Primes.prodNatEquiv (q, e) := by
          apply Subtype.ext
          simpa only [Nat.Primes.coe_prodNatEquiv_apply] using hq
        exact hxe (congrArg Prod.snd (Nat.Primes.prodNatEquiv.injective heq))
      change scalarValuationBasisProfile e x.2 =
        (if h : ∃ q : Nat.Primes,
            (x.1 : Nat) ^ (x.2 + 1) = (q : Nat) ^ (e + 1) then
          (1 : ℂ) else 0)
      rw [dif_neg hnone]
      simp [scalarValuationBasisProfile, hxe]
  · have hnone : ¬ ∃ p : Nat.Primes, n = (p : Nat) ^ (e + 1) := by
      rintro ⟨p, rfl⟩
      exact hpow (Nat.Primes.prodNatEquiv (p, e)).property
    simp [scalarReplicatedPrimeProfile, hpow,
      arithmeticOfPrimePowerColumn, hnone]

/-- The finite-abscissa valuation layer is literally the corresponding dilation of the
prime-zeta source. -/
theorem boundedScalarReplicatedFiniteAbscissa_basis_eq_primeZetaDilation
    (e : Nat) :
    boundedScalarReplicatedFiniteAbscissa
        (scalarValuationBasisProfile e) 1
        (scalarValuationBasisProfile_norm_le_one e) =
      finiteAbscissaPrimePowerDilation e primeZetaFiniteAbscissaSource := by
  apply Subtype.ext
  rw [boundedScalarReplicatedFiniteAbscissa_val,
    scalarReplicatedPrimeProfile_scalarValuationBasisProfile]
  exact (finiteAbscissaPrimePowerDilation_eq_arithmeticOfPrimePowerColumn
    e primeZetaFiniteAbscissaSource (fun _ : Nat.Primes ↦ (1 : ℂ)) rfl).symm

/-- The analytic valuation layer is the actual prime-zeta germ at the dilated argument
`(e + 1)s`. -/
theorem analyticScalarValuationLayer_germ_eq_primeZetaDilation (e : Nat) :
    (finiteAbscissaLSeriesToUpperEndAnalytic
        (boundedScalarReplicatedFiniteAbscissa
          (scalarValuationBasisProfile e) 1
          (scalarValuationBasisProfile_norm_le_one e)) :
      Germ upperEndFilter ℂ) =
      upperEndPrimePowerScaleGerm e analyticPrimeZetaUpperEndGerm := by
  rw [finiteAbscissaLSeriesToUpperEndAnalytic_coe,
    boundedScalarReplicatedFiniteAbscissa_basis_eq_primeZetaDilation,
    finiteAbscissaLSeriesToUpperEndGerm_primePowerDilation]
  rfl

/-- Actual meromorphic carrier of the valuation layer concentrated at exponent `n + 1`. -/
def analyticScalarValuationLayerCarrier (n : Nat) : upperEndMeroField :=
  analyticScalarReplicatedCarrier (scalarValuationBasisProfile n) 1
    (scalarValuationBasisProfile_norm_le_one n)

/-- In the meromorphic field, the named valuation-layer generator is exactly the faithful
realization of the corresponding prime-zeta dilation. -/
theorem analyticScalarValuationLayerCarrier_eq_primeZetaDilation (e : Nat) :
    analyticScalarValuationLayerCarrier e =
      finiteAbscissaLSeriesToUpperEndMero
        (finiteAbscissaPrimePowerDilation e primeZetaFiniteAbscissaSource) := by
  unfold analyticScalarValuationLayerCarrier analyticScalarReplicatedCarrier
  rw [boundedScalarReplicatedFiniteAbscissa_basis_eq_primeZetaDilation]

/-- The actual coordinate-field differential field generated by every prime-zeta valuation
layer simultaneously. -/
def analyticScalarValuationLayerDifferentialField :
    IntermediateField upperEndRationalCoordinateField upperEndMeroField :=
  GaloisForLFunctions.differentialAdjoin upperEndRationalCoordinateField
    (Set.range analyticScalarValuationLayerCarrier)

theorem eulerLogValuationProfile_norm_le_one (e : Nat) :
    ‖eulerLogValuationProfile e‖ ≤ 1 := by
  rw [eulerLogValuationProfile, norm_div, norm_one, Complex.norm_natCast]
  apply (div_le_one (by positivity)).2
  norm_num

/-- Actual upper-end Dirichlet carrier of the Euler logarithm valuation profile. -/
def analyticEulerLogReplicatedCarrier : upperEndMeroField :=
  analyticScalarReplicatedCarrier eulerLogValuationProfile 1
    eulerLogValuationProfile_norm_le_one

/-- The analytic representative of the named Euler carrier is exactly the canonical Euler
logarithm of zeta after the fixed upper-end rotation `s = -I z`. -/
theorem analyticEulerLogReplicated_germ_eq_canonicalEulerLogZeta :
    (finiteAbscissaLSeriesToUpperEndAnalytic
        (boundedScalarReplicatedFiniteAbscissa
          eulerLogValuationProfile 1 eulerLogValuationProfile_norm_le_one) :
      Germ upperEndFilter ℂ) =
      ((fun z : ℂ ↦ RHTower.canonicalEulerLogZeta (-Complex.I * z)) :
        Germ upperEndFilter ℂ) := by
  rw [finiteAbscissaLSeriesToUpperEndAnalytic_coe]
  change ((fun z : ℂ ↦
      LSeries (fun n ↦
        scalarReplicatedPrimeProfile eulerLogValuationProfile n)
          (-Complex.I * z)) : Germ upperEndFilter ℂ) = _
  rw [scalarReplicatedPrimeProfile_eulerLogValuationProfile]
  rfl

/-- **Analytic Euler completion barrier.**  The actual finite-abscissa Euler-profile Dirichlet
germ is differentially independent over the one field generated by the genuine coordinate and
all individual prime-zeta valuation layers. -/
theorem analyticEulerLogReplicatedCarrier_differentialIndependent_over_all_valuationLayers :
    GaloisForLFunctions.DifferentialIndependent
      analyticScalarValuationLayerDifferentialField
      (fun _ : Unit ↦ analyticEulerLogReplicatedCarrier) := by
  classical
  let y : upperEndMeroField := analyticEulerLogReplicatedCarrier
  let G : Set upperEndMeroField := Set.range analyticScalarValuationLayerCarrier
  have hstages : ∀ G₀ : Set upperEndMeroField,
      G₀ ⊆ G → G₀.Finite →
        GaloisForLFunctions.DiffIndepOn
          (GaloisForLFunctions.differentialAdjoin
            upperEndRationalCoordinateField G₀)
          ({y} : Set upperEndMeroField) := by
    intro G₀ hG₀ hfinite
    letI : Fintype G₀ := hfinite.fintype
    letI : DecidableEq G₀ := Classical.decEq G₀
    choose idx hidxCarrier using fun z : G₀ ↦ hG₀ z.2
    have hidx : Function.Injective idx := by
      intro z w hzw
      apply Subtype.ext
      rw [← hidxCarrier z, ← hidxCarrier w, hzw]
    let oldProfile : G₀ → Nat → ℂ := fun z ↦
      scalarValuationBasisProfile (idx z)
    let profiles : Unit ⊕ G₀ → Nat → ℂ :=
      Sum.elim (fun _ : Unit ↦ eulerLogValuationProfile) oldProfile
    have hprofiles : LinearIndependent ℂ profiles := by
      rw [Fintype.linearIndependent_iff]
      intro c hsum z
      let used : Finset Nat := Finset.univ.image idx
      have hnsubset : ¬ {e : Nat | eulerLogValuationProfile e ≠ 0} ⊆
          (↑used : Set Nat) := by
        intro hsub
        exact eulerLogValuationProfile_support_infinite
          (used.finite_toSet.subset hsub)
      obtain ⟨e, heu, heused⟩ := Set.not_subset.mp hnsubset
      have hbzero : ∀ w : G₀,
          scalarValuationBasisProfile (idx w) e = 0 := by
        intro w
        have hene : e ≠ idx w := by
          intro heq
          apply heused
          exact Finset.mem_coe.mpr
            (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, heq.symm⟩)
        simp [scalarValuationBasisProfile, hene]
      have hnewzero : c (Sum.inl ()) = 0 := by
        have heval := congrFun hsum e
        have hmul : c (Sum.inl ()) * eulerLogValuationProfile e = 0 := by
          simpa [profiles, oldProfile, Fintype.sum_sum_type, hbzero,
            Pi.smul_apply, smul_eq_mul] using heval
        exact (mul_eq_zero.mp hmul).resolve_right heu
      have holdzero : ∀ w : G₀, c (Sum.inr w) = 0 := by
        intro w
        have heval := congrFun hsum (idx w)
        simpa [profiles, oldProfile, Fintype.sum_sum_type, hnewzero,
          scalarValuationBasisProfile, hidx.eq_iff,
          Pi.smul_apply, smul_eq_mul] using heval
      rcases z with z | z
      · simpa using hnewzero
      · exact holdzero z
    have hprofilesBound : ∀ z e, ‖profiles z e‖ ≤ 1 := by
      intro z e
      rcases z with u | z
      · exact eulerLogValuationProfile_norm_le_one e
      · exact scalarValuationBasisProfile_norm_le_one (idx z) e
    have hcombined : GaloisForLFunctions.DifferentialIndependent
        upperEndRationalCoordinateField
        (fun z ↦ analyticScalarReplicatedCarrier (profiles z) 1
          (hprofilesBound z)) :=
      differentialIndependent_analyticScalarReplicatedCarriers_of_linearIndependent
        profiles (fun _ ↦ 1) hprofilesBound hprofiles
    have hfamily :
        (fun z ↦ analyticScalarReplicatedCarrier (profiles z) 1
          (hprofilesBound z)) =
          Sum.elim (fun _ : Unit ↦ y) (fun z : G₀ ↦ z.1) := by
      funext z
      rcases z with v | z
      · apply congrArg finiteAbscissaLSeriesToUpperEndMero
        apply Subtype.ext
        rfl
      · simpa only [profiles, oldProfile, analyticScalarValuationLayerCarrier] using
          hidxCarrier z
    rw [hfamily] at hcombined
    have hrelative :=
      (GaloisForLFunctions.differentialIndependent_sumElim_right_iff
        (fun _ : Unit ↦ y) (fun z : G₀ ↦ z.1)).mp hcombined |>.2
    rw [Subtype.range_val] at hrelative
    unfold GaloisForLFunctions.DiffIndepOn
    have hsingleton := hrelative.comp
      (fun _ : ({y} : Set upperEndMeroField) ↦ ())
      (fun a b _ ↦ Subsingleton.elim a b)
    have htarget :
        ((fun _ : Unit ↦ y) ∘
            (fun _ : ({y} : Set upperEndMeroField) ↦ ())) =
          (fun z : ({y} : Set upperEndMeroField) ↦ z.1) := by
      funext z
      exact (Set.mem_singleton_iff.mp z.2).symm
    rw [htarget] at hsingleton
    exact hsingleton
  have hset : GaloisForLFunctions.DiffIndepOn
      (GaloisForLFunctions.differentialAdjoin upperEndRationalCoordinateField G)
      ({y} : Set upperEndMeroField) :=
    diffIndepOn_differentialAdjoin_of_forall_finite_subset hstages
  unfold GaloisForLFunctions.DiffIndepOn at hset
  have hunit := hset.comp (fun _ : Unit ↦
      (⟨y, Set.mem_singleton y⟩ : ({y} : Set upperEndMeroField)))
    (fun a b _ ↦ Subsingleton.elim a b)
  simpa [analyticScalarValuationLayerDifferentialField, G, y,
    analyticEulerLogReplicatedCarrier, Function.comp_def] using hunit

end

end GaloisForLFunctions.HTGeometry
