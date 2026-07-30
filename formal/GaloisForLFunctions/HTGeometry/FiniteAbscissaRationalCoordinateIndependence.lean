import GaloisForLFunctions.HTGeometry.PrimeResidueValuationAnalyticSuperselection
import GaloisForLFunctions.RHTower.LSeriesPolynomialWeightUniqueness
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Rational-coordinate independence for finite-abscissa Dirichlet germs

The upper-end coordinate is transcendental over the field of convergent Dirichlet-series germs.
Consequently algebraic independence of finite-abscissa coefficient sources over `C` survives their
analytic realization over the genuine coordinate field `C(s)`.

The analytic input is polynomial-weighted L-series uniqueness: after clearing denominators, a
polynomial relation in the coordinate has finite-abscissa L-series coefficients, and restriction
to the far-right real ray kills every coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Filter Set Polynomial LSeries
open scoped Differential LSeries.notation

noncomputable section

local instance finiteAbscissaBridgeUpperEndAnalyticDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance finiteAbscissaBridgeUpperEndMeroComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

/-- Finite-abscissa L-series as actual eventual-analytic upper-end elements. -/
noncomputable def finiteAbscissaLSeriesToUpperEndAnalytic :
    finiteAbscissaArithmeticSubalgebra →+* upperEndAnalyticSubring where
  toFun := finiteAbscissaLSeriesUpperEndAnalyticElement
  map_zero' := by
    apply Subtype.ext
    exact finiteAbscissaLSeriesToUpperEndGerm.map_zero
  map_one' := by
    apply Subtype.ext
    exact finiteAbscissaLSeriesToUpperEndGerm.map_one
  map_add' f g := by
    apply Subtype.ext
    exact finiteAbscissaLSeriesToUpperEndGerm.map_add f g
  map_mul' f g := by
    apply Subtype.ext
    exact finiteAbscissaLSeriesToUpperEndGerm.map_mul f g

@[simp]
theorem finiteAbscissaLSeriesToUpperEndAnalytic_coe
    (f : finiteAbscissaArithmeticSubalgebra) :
    (finiteAbscissaLSeriesToUpperEndAnalytic f : Germ upperEndFilter ℂ) =
      finiteAbscissaLSeriesToUpperEndGerm f :=
  rfl

/-- Dirichlet translation is carried faithfully to analytic upper-end translation. -/
theorem finiteAbscissaLSeriesToUpperEndAnalytic_dirichletShift
    (a : ℂ) (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaLSeriesToUpperEndAnalytic
        (finiteAbscissaDirichletShift a f) =
      upperEndTranslationAnalyticEquiv (Complex.I * a)
        (finiteAbscissaLSeriesToUpperEndAnalytic f) := by
  apply Subtype.ext
  exact finiteAbscissaLSeriesToUpperEndGerm_dirichletShift a f

/-- The analytic upper-end coordinate. -/
noncomputable def upperEndCoordinateAnalytic : upperEndAnalyticSubring :=
  upperEndPolyToAnalytic Polynomial.X

/-- The same coordinate in the upper-end meromorphic field. -/
noncomputable def upperEndCoordinateMero : upperEndMeroField :=
  upperEndPolyToMero Polynomial.X

@[simp]
theorem upperEndCoordinateAnalytic_coe :
    ((upperEndCoordinateAnalytic : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      ((fun z : ℂ => z) : Germ upperEndFilter ℂ) := by
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    simp

@[simp]
theorem upperEndCoordinateMero_eq_algebraMap :
    upperEndCoordinateMero =
      algebraMap upperEndAnalyticSubring upperEndMeroField upperEndCoordinateAnalytic :=
  rfl

@[simp]
theorem finiteAbscissaLSeriesToUpperEndMero_eq_algebraMap
    (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaLSeriesToUpperEndMero f =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (finiteAbscissaLSeriesToUpperEndAnalytic f) :=
  rfl

/-- **Meromorphic Dirichlet-translation intertwiner.** Faithful finite-abscissa realization
conjugates coefficient-side Dirichlet translation to the upper-end meromorphic translation
automorphism. -/
theorem finiteAbscissaLSeriesToUpperEndMero_dirichletShift
    (a : ℂ) (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaLSeriesToUpperEndMero
        (finiteAbscissaDirichletShift a f) =
      upperEndTranslationMeroEquiv (Complex.I * a)
        (finiteAbscissaLSeriesToUpperEndMero f) := by
  rw [finiteAbscissaLSeriesToUpperEndMero_eq_algebraMap,
    finiteAbscissaLSeriesToUpperEndMero_eq_algebraMap,
    upperEndTranslationMeroEquiv_algebraMap,
    finiteAbscissaLSeriesToUpperEndAnalytic_dirichletShift]

/-- A coefficient stream rotated so that evaluation on `z = I*x` has the ordinary polynomial
weight `x^k`. -/
def finiteAbscissaCoordinateCoefficient
    (P : Polynomial finiteAbscissaArithmeticSubalgebra) (k n : ℕ) : ℂ :=
  Complex.I ^ k * (P.coeff k).1 n

/-- The pointwise function represented by an analytic polynomial relation. -/
def finiteAbscissaAnalyticPolynomialRelationFunction
    (P : Polynomial finiteAbscissaArithmeticSubalgebra) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    LSeries (fun n => (P.coeff k).1 n) (-Complex.I * z) * z ^ k

theorem finiteAbscissaAnalyticPolynomialRelation_coe
    (P : Polynomial finiteAbscissaArithmeticSubalgebra) :
    ((Polynomial.eval₂ finiteAbscissaLSeriesToUpperEndAnalytic
        upperEndCoordinateAnalytic P : upperEndAnalyticSubring) :
          Germ upperEndFilter ℂ) =
      (finiteAbscissaAnalyticPolynomialRelationFunction P :
        Germ upperEndFilter ℂ) := by
  rw [Polynomial.eval₂_eq_sum_range]
  change (SubringClass.subtype upperEndAnalyticSubring)
      (∑ k ∈ Finset.range (P.natDegree + 1),
        finiteAbscissaLSeriesToUpperEndAnalytic (P.coeff k) *
          upperEndCoordinateAnalytic ^ k) = _
  rw [map_sum]
  change
    (∑ k ∈ Finset.range (P.natDegree + 1),
      (finiteAbscissaLSeriesToUpperEndGerm (P.coeff k)) *
        (((upperEndCoordinateAnalytic : upperEndAnalyticSubring) :
          Germ upperEndFilter ℂ) ^ k)) = _
  simp_rw [upperEndCoordinateAnalytic_coe]
  change
    ∑ k ∈ Finset.range (P.natDegree + 1),
        (Germ.coeRingHom upperEndFilter)
            (fun z : ℂ => LSeries (fun n => (P.coeff k).1 n) (-Complex.I * z)) *
          ((Germ.coeRingHom upperEndFilter) (fun z : ℂ => z)) ^ k =
      (Germ.coeRingHom upperEndFilter)
        (finiteAbscissaAnalyticPolynomialRelationFunction P)
  simp_rw [← map_pow, ← map_mul]
  rw [← map_sum]
  apply congrArg (Germ.coeRingHom upperEndFilter)
  funext z
  simp [finiteAbscissaAnalyticPolynomialRelationFunction]

theorem finiteAbscissaCoordinateCoefficient_summable
    (P : Polynomial finiteAbscissaArithmeticSubalgebra) :
    ∃ x₀ : ℝ, ∀ k, k ≤ P.natDegree →
      LSeriesSummable (finiteAbscissaCoordinateCoefficient P k) (x₀ : ℂ) := by
  choose H hH using fun k => (P.coeff k).2
  let x₀ : ℝ := ∑ k ∈ Finset.range (P.natDegree + 1), (|H k| + 1)
  refine ⟨x₀, fun k hk => ?_⟩
  have hkmem : k ∈ Finset.range (P.natDegree + 1) := Finset.mem_range.mpr (by omega)
  have hterm : |H k| + 1 ≤ x₀ := by
    dsimp only [x₀]
    exact Finset.single_le_sum (f := fun i => |H i| + 1)
      (fun i _ => by positivity) hkmem
  have hHlt : H k < x₀ := lt_of_lt_of_le (by linarith [le_abs_self (H k)]) hterm
  have hs := hH k x₀ hHlt
  refine (LSeriesSummable_congr (x₀ : ℂ)
    (f := (Complex.I ^ k) • fun n => (P.coeff k).1 n)
    (g := finiteAbscissaCoordinateCoefficient P k) ?_).mp
      (hs.smul (Complex.I ^ k))
  intro n _
  simp [finiteAbscissaCoordinateCoefficient, Pi.smul_apply, smul_eq_mul]

theorem upperEndAnalyticPolynomialRelation_coeff_eq_zero
    (P : Polynomial finiteAbscissaArithmeticSubalgebra)
    (hzero : Polynomial.eval₂ finiteAbscissaLSeriesToUpperEndAnalytic
      upperEndCoordinateAnalytic P = 0) :
    ∀ k, P.coeff k = 0 := by
  obtain ⟨H₀, hsumm₀⟩ := finiteAbscissaCoordinateCoefficient_summable P
  have hgerm :
      (finiteAbscissaAnalyticPolynomialRelationFunction P :
        Germ upperEndFilter ℂ) = 0 := by
    rw [← finiteAbscissaAnalyticPolynomialRelation_coe]
    exact congrArg Subtype.val hzero
  rw [← Germ.coe_zero, Germ.coe_eq] at hgerm
  change ∀ᶠ z in upperEndFilter,
    finiteAbscissaAnalyticPolynomialRelationFunction P z = 0 at hgerm
  rw [upperEndFilter_basis.eventually_iff] at hgerm
  obtain ⟨B, -, hB⟩ := hgerm
  let x₀ : ℝ := max H₀ B + 1
  have hsumm : ∀ k, k ≤ P.natDegree →
      LSeriesSummable (finiteAbscissaCoordinateCoefficient P k) (x₀ : ℂ) := by
    intro k hk
    exact (hsumm₀ k hk).of_re_le_re (by simp [x₀]; linarith [le_max_left H₀ B])
  have hrelation : ∀ x : ℝ, x₀ ≤ x →
      ∑ k ∈ Finset.range (P.natDegree + 1),
        (x : ℂ) ^ k *
          LSeries (finiteAbscissaCoordinateCoefficient P k) (x : ℂ) = 0 := by
    intro x hx
    have hBx : B < x := by
      dsimp only [x₀] at hx
      linarith [le_max_right H₀ B]
    have hpoint := hB (show Complex.I * (x : ℂ) ∈ upperTail B by
      simpa [upperTail, Complex.mul_im] using hBx)
    change finiteAbscissaAnalyticPolynomialRelationFunction P
      (Complex.I * (x : ℂ)) = 0 at hpoint
    have hrot : -Complex.I * (Complex.I * (x : ℂ)) = (x : ℂ) := by
      calc
        -Complex.I * (Complex.I * (x : ℂ)) =
            (-Complex.I * Complex.I) * (x : ℂ) := (mul_assoc _ _ _).symm
        _ = (x : ℂ) := by rw [neg_mul, Complex.I_mul_I]; ring
    rw [finiteAbscissaAnalyticPolynomialRelationFunction, hrot] at hpoint
    calc
      ∑ k ∈ Finset.range (P.natDegree + 1),
          (x : ℂ) ^ k * LSeries (finiteAbscissaCoordinateCoefficient P k) (x : ℂ) =
          ∑ k ∈ Finset.range (P.natDegree + 1),
            LSeries (fun n => (P.coeff k).1 n) (x : ℂ) *
              (Complex.I * (x : ℂ)) ^ k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show finiteAbscissaCoordinateCoefficient P k =
            (Complex.I ^ k) • (fun n => (P.coeff k).1 n) by
          funext n
          simp [finiteAbscissaCoordinateCoefficient]]
        rw [LSeries_smul]
        ring
      _ = 0 := by
        exact hpoint
  have hcoeff := lseries_polyWeightFamily_coeff_eq_zero
    (A := P.natDegree) (finiteAbscissaCoordinateCoefficient P) hsumm hrelation
  intro k
  apply Subtype.ext
  apply ArithmeticFunction.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  by_cases hk : k ≤ P.natDegree
  · have hz := hcoeff n (Nat.one_le_iff_ne_zero.mpr hn) k hk
    have hI : Complex.I ^ k ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    exact mul_left_cancel₀ hI (by simpa [finiteAbscissaCoordinateCoefficient] using hz)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- No nonzero polynomial with finite-abscissa Dirichlet coefficients can annihilate the genuine
upper-end coordinate. -/
theorem upperEndCoordinate_polynomial_relation_eq_zero
    (P : Polynomial finiteAbscissaArithmeticSubalgebra)
    (hzero : Polynomial.eval₂ finiteAbscissaLSeriesToUpperEndMero
      upperEndCoordinateMero P = 0) :
    P = 0 := by
  let Q : upperEndAnalyticSubring :=
    Polynomial.eval₂ finiteAbscissaLSeriesToUpperEndAnalytic upperEndCoordinateAnalytic P
  have hmap : algebraMap upperEndAnalyticSubring upperEndMeroField Q = 0 := by
    dsimp only [Q]
    calc
      algebraMap upperEndAnalyticSubring upperEndMeroField
          (Polynomial.eval₂ finiteAbscissaLSeriesToUpperEndAnalytic
            upperEndCoordinateAnalytic P) =
          Polynomial.eval₂ finiteAbscissaLSeriesToUpperEndMero
            upperEndCoordinateMero P := by
        rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval₂_eq_sum_range, map_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [map_mul, map_pow]
        rfl
      _ = 0 := hzero
  have hQ : Q = 0 :=
    (IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField) (by simpa using hmap)
  apply Polynomial.ext
  intro k
  exact upperEndAnalyticPolynomialRelation_coeff_eq_zero P hQ k

/-! ## Denominator clearing and the genuine rational coordinate -/

/-- The fraction field of all finite-abscissa Dirichlet coefficient streams. -/
abbrev finiteAbscissaDirichletFractionField :=
  FractionRing finiteAbscissaArithmeticSubalgebra

/-- The underlying ring map of the analytic finite-abscissa realization. Naming it prevents the
fraction-field lift from repeatedly unfolding the much larger algebra-hom structure. -/
noncomputable def finiteAbscissaCoefficientToUpperEndMeroRingHom :
    finiteAbscissaArithmeticSubalgebra →+* upperEndMeroField :=
  finiteAbscissaLSeriesToUpperEndMero.toRingHom

@[simp]
theorem finiteAbscissaCoefficientToUpperEndMeroRingHom_apply
    (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaCoefficientToUpperEndMeroRingHom f =
      finiteAbscissaLSeriesToUpperEndMero f :=
  rfl

theorem finiteAbscissaCoefficientToUpperEndMeroRingHom_injective :
    Function.Injective finiteAbscissaCoefficientToUpperEndMeroRingHom :=
  finiteAbscissaLSeriesToUpperEndMero_injective

/-- Faithful realization of finite-abscissa Dirichlet fractions in the upper-end meromorphic
field. -/
noncomputable def finiteAbscissaFractionToUpperEndMero :
    finiteAbscissaDirichletFractionField →+* upperEndMeroField :=
  IsFractionRing.lift
    (A := finiteAbscissaArithmeticSubalgebra)
    (K := finiteAbscissaDirichletFractionField)
    (g := finiteAbscissaCoefficientToUpperEndMeroRingHom)
    finiteAbscissaCoefficientToUpperEndMeroRingHom_injective

theorem finiteAbscissaFractionToUpperEndMero_injective :
    Function.Injective finiteAbscissaFractionToUpperEndMero :=
  finiteAbscissaFractionToUpperEndMero.injective

noncomputable instance finiteAbscissaFractionUpperEndAlgebra :
    Algebra finiteAbscissaDirichletFractionField upperEndMeroField :=
  finiteAbscissaFractionToUpperEndMero.toAlgebra

@[simp]
theorem finiteAbscissaFractionToUpperEndMero_algebraMap
    (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaFractionToUpperEndMero
        (algebraMap finiteAbscissaArithmeticSubalgebra
          finiteAbscissaDirichletFractionField f) =
      finiteAbscissaLSeriesToUpperEndMero f :=
  by
    change (IsFractionRing.lift
      (A := finiteAbscissaArithmeticSubalgebra)
      (K := finiteAbscissaDirichletFractionField)
      (g := finiteAbscissaCoefficientToUpperEndMeroRingHom)
      finiteAbscissaCoefficientToUpperEndMeroRingHom_injective)
        (algebraMap finiteAbscissaArithmeticSubalgebra
          finiteAbscissaDirichletFractionField f) =
            finiteAbscissaCoefficientToUpperEndMeroRingHom f
    apply IsFractionRing.lift_algebraMap

/-- Clearing a finite family of fraction coefficients produces one nonzero denominator and a
finite-abscissa numerator for every coefficient. -/
theorem finiteAbscissaFractionPolynomial_exists_commonDenominator
    (P : Polynomial finiteAbscissaDirichletFractionField) :
    ∃ b : nonZeroDivisors finiteAbscissaArithmeticSubalgebra,
      ∃ a : Fin (P.natDegree + 1) → finiteAbscissaArithmeticSubalgebra,
        ∀ k,
          algebraMap finiteAbscissaArithmeticSubalgebra
              finiteAbscissaDirichletFractionField (a k) =
            algebraMap finiteAbscissaArithmeticSubalgebra
                finiteAbscissaDirichletFractionField (b :
                  finiteAbscissaArithmeticSubalgebra) * P.coeff k := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors finiteAbscissaArithmeticSubalgebra)
    (fun k : Fin (P.natDegree + 1) => P.coeff k)
  choose a ha using hb
  refine ⟨b, a, fun k => ?_⟩
  simpa only [Algebra.smul_def] using ha k

/-- **Dirichlet-coordinate disjointness.** The genuine upper-end coordinate is transcendental
over the whole fraction field of finite-abscissa Dirichlet-series germs. -/
theorem upperEndCoordinateMero_transcendental_over_finiteAbscissaFraction :
    Transcendental finiteAbscissaDirichletFractionField upperEndCoordinateMero := by
  rw [transcendental_iff]
  intro P hP
  obtain ⟨b, a, ha⟩ :=
    finiteAbscissaFractionPolynomial_exists_commonDenominator P
  let Q : Polynomial finiteAbscissaArithmeticSubalgebra :=
    ∑ k : Fin (P.natDegree + 1), Polynomial.monomial (k : ℕ) (a k)
  have hPeval : Polynomial.eval₂
      finiteAbscissaFractionToUpperEndMero upperEndCoordinateMero P = 0 := by
    simpa [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hP
  have hQeval : Polynomial.eval₂ finiteAbscissaLSeriesToUpperEndMero
      upperEndCoordinateMero Q = 0 := by
    let B : upperEndMeroField :=
      finiteAbscissaFractionToUpperEndMero
        (algebraMap finiteAbscissaArithmeticSubalgebra
          finiteAbscissaDirichletFractionField
            (b : finiteAbscissaArithmeticSubalgebra))
    calc
      Polynomial.eval₂ finiteAbscissaLSeriesToUpperEndMero
          upperEndCoordinateMero Q =
          ∑ k : Fin (P.natDegree + 1),
            finiteAbscissaLSeriesToUpperEndMero (a k) *
              upperEndCoordinateMero ^ (k : ℕ) := by
        change (Polynomial.eval₂RingHom finiteAbscissaLSeriesToUpperEndMero
          upperEndCoordinateMero) Q = _
        dsimp only [Q]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k hk
        change Polynomial.eval₂ finiteAbscissaLSeriesToUpperEndMero
            upperEndCoordinateMero (Polynomial.monomial (k : ℕ) (a k)) = _
        rw [Polynomial.eval₂_monomial]
        rfl
      _ = ∑ k : Fin (P.natDegree + 1),
          B * finiteAbscissaFractionToUpperEndMero (P.coeff k) *
            upperEndCoordinateMero ^ (k : ℕ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← finiteAbscissaFractionToUpperEndMero_algebraMap, ha k, map_mul]
      _ = B * Polynomial.eval₂ finiteAbscissaFractionToUpperEndMero
          upperEndCoordinateMero P := by
        rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [dif_pos (Finset.mem_range.mp hk)]
        ring
      _ = 0 := by rw [hPeval, mul_zero]
  have hQzero := upperEndCoordinate_polynomial_relation_eq_zero Q hQeval
  apply Polynomial.ext
  intro k
  by_cases hk : k ≤ P.natDegree
  · let j : Fin (P.natDegree + 1) := ⟨k, by omega⟩
    have haj : a j = 0 := by
      have hcoeff := congrArg (fun R : Polynomial finiteAbscissaArithmeticSubalgebra =>
        R.coeff k) hQzero
      have hQcoeff : Q.coeff k = a j := by
        dsimp only [Q]
        rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
        · rw [Polynomial.coeff_monomial, if_pos rfl]
        · intro i _ hij
          rw [Polynomial.coeff_monomial, if_neg]
          intro hik
          apply hij
          apply Fin.ext
          simpa [j] using hik
        · simp
      change Q.coeff k = 0 at hcoeff
      rw [hQcoeff] at hcoeff
      exact hcoeff
    have hmul : algebraMap finiteAbscissaArithmeticSubalgebra
          finiteAbscissaDirichletFractionField
          (b : finiteAbscissaArithmeticSubalgebra) * P.coeff k = 0 := by
      rw [← ha j]
      simp [haj]
    have hbA : (b : finiteAbscissaArithmeticSubalgebra) ≠ 0 := by
      exact nonZeroDivisors.ne_zero b.2
    have hbF : algebraMap finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField
        (b : finiteAbscissaArithmeticSubalgebra) ≠ 0 :=
      fun hb0 => hbA ((IsFractionRing.injective finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField)
          (hb0.trans (map_zero _).symm))
    exact (mul_eq_zero.mp hmul).resolve_left hbF
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-! ## Algebraic independence over the actual rational-coordinate field -/

/-- The actual embedded rational-coordinate field `ℂ(s)` at the upper end. -/
abbrev upperEndRationalCoordinateField : IntermediateField ℂ upperEndMeroField :=
  IntermediateField.adjoin ℂ {upperEndCoordinateMero}

set_option synthInstance.maxHeartbeats 100000 in
local instance finiteAbscissaFractionUpperEndComplexScalarTower :
    IsScalarTower ℂ finiteAbscissaDirichletFractionField upperEndMeroField :=
  .of_algebraMap_eq fun z => by
    change algebraMap ℂ upperEndMeroField z =
      finiteAbscissaFractionToUpperEndMero
        (algebraMap finiteAbscissaArithmeticSubalgebra
          finiteAbscissaDirichletFractionField
            (algebraMap ℂ finiteAbscissaArithmeticSubalgebra z))
    rw [finiteAbscissaFractionToUpperEndMero_algebraMap]
    exact (finiteAbscissaLSeriesToUpperEndMero.commutes z).symm

/-- **Actual-coordinate base-extension law.** Any finite-abscissa coefficient family that is
algebraically independent over `ℂ` remains algebraically independent after analytic realization
over the genuine embedded rational-coordinate field `ℂ(s)`. -/
theorem algebraicIndependent_finiteAbscissaLSeries_over_upperEndRationalCoordinate
    {I : Type*} (f : I → finiteAbscissaArithmeticSubalgebra)
    (hf : AlgebraicIndependent ℂ f) :
    AlgebraicIndependent upperEndRationalCoordinateField
      (fun i => finiteAbscissaLSeriesToUpperEndMero (f i)) := by
  let xF : I → finiteAbscissaDirichletFractionField := fun i =>
    algebraMap finiteAbscissaArithmeticSubalgebra
      finiteAbscissaDirichletFractionField (f i)
  let xM : I → upperEndMeroField := fun i =>
    algebraMap finiteAbscissaDirichletFractionField upperEndMeroField (xF i)
  let t : Unit → upperEndMeroField := fun _ => upperEndCoordinateMero
  have hxF : AlgebraicIndependent ℂ xF := by
    exact hf.map'
      (f := IsScalarTower.toAlgHom ℂ finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField)
      (IsFractionRing.injective finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField)
  have ht : AlgebraicIndependent finiteAbscissaDirichletFractionField t := by
    rw [algebraicIndependent_unique_type_iff]
    exact upperEndCoordinateMero_transcendental_over_finiteAbscissaFraction
  have hjoint₀ : AlgebraicIndependent ℂ
      (Sum.elim t (algebraMap finiteAbscissaDirichletFractionField
        upperEndMeroField ∘ xF)) :=
    AlgebraicIndependent.sumElim_comp hxF ht
  have hjoint : AlgebraicIndependent ℂ (Sum.elim xM t) := by
    let e : I ⊕ Unit ≃ Unit ⊕ I := Equiv.sumComm I Unit
    have hcomp := hjoint₀.comp e e.injective
    have heq : (Sum.elim t
        (algebraMap finiteAbscissaDirichletFractionField upperEndMeroField ∘ xF)) ∘ e =
          Sum.elim xM t := by
      funext z
      rcases z with i | u <;> rfl
    rwa [heq] at hcomp
  have hAlg : AlgebraicIndependent (Algebra.adjoin ℂ (Set.range t)) xM :=
    (AlgebraicIndependent.sumElim_iff.mp hjoint).2
  have hrange : Set.range t = ({upperEndCoordinateMero} : Set upperEndMeroField) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      rfl
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      exact ⟨(), hz.symm⟩
  rw [hrange] at hAlg
  have hField : AlgebraicIndependent upperEndRationalCoordinateField xM :=
    IntermediateField.algebraicIndependent_adjoin_iff.mpr hAlg
  have hxM : xM = fun i => finiteAbscissaLSeriesToUpperEndMero (f i) := by
    funext i
    exact finiteAbscissaFractionToUpperEndMero_algebraMap (f i)
  rwa [hxM] at hField


end

end GaloisForLFunctions.HTGeometry
