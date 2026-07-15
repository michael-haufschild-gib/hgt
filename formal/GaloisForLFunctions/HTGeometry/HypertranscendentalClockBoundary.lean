import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.HypertranscendentalHorizonFunctionField
import GaloisForLFunctions.HTGeometry.KaehlerKernel
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.MapCoeffs

/-!
# The clock-observable boundary of a hypertranscendental source

The derivation is used here as an algebraic clock: it tests which observables remain visible at a
fixed finite jet resolution.  It is not interpreted as time and does not propagate the source by
a flow.

The first exact ingredient is rational coordinate rigidity.  On the one-variable function field
`K(t)` in characteristic zero, the kernel of the coordinate derivation is exactly `K`.  Thus a
rational observable cannot depend on a boundary coordinate while hiding that dependence from the
coordinate derivative.  This excludes the only possible rational cancellation in the proposed
one-layer clock-boundary law.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

/-- The coordinate derivation `d/dt` on the rational function field `K(t)`. -/
def ratFuncCoordinateDerivation (K : Type*) [Field K] :
    Derivation K (RatFunc K) (RatFunc K) :=
  GaloisForLFunctions.fractionRingDerivation
    (Polynomial.mkDerivation K (1 : RatFunc K))

/-- The rational coordinate derivation extends the formal derivative on `K[t]`. -/
@[simp]
theorem ratFuncCoordinateDerivation_algebraMap
    {K : Type*} [Field K] (p : K[X]) :
    ratFuncCoordinateDerivation K (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) p.derivative := by
  rw [ratFuncCoordinateDerivation,
    GaloisForLFunctions.fractionRingDerivation_algebraMap,
    Polynomial.mkDerivation_apply]
  rw [Algebra.smul_def, mul_one]

/-- Quotient-rule formula exposing the unique coordinate-boundary coefficient of a rational
observable. -/
theorem ratFuncCoordinateDerivation_apply
    {K : Type*} [Field K] (z : RatFunc K) :
    ratFuncCoordinateDerivation K z =
      (algebraMap K[X] (RatFunc K) z.denom)⁻¹ ^ 2 *
        (algebraMap K[X] (RatFunc K) z.denom *
            algebraMap K[X] (RatFunc K) z.num.derivative -
          algebraMap K[X] (RatFunc K) z.num *
            algebraMap K[X] (RatFunc K) z.denom.derivative) := by
  conv_lhs => rw [← RatFunc.num_div_denom z]
  rw [Derivation.leibniz_div,
    ratFuncCoordinateDerivation_algebraMap,
    ratFuncCoordinateDerivation_algebraMap]
  simp only [smul_eq_mul]

/-- Vanishing of the coordinate derivative gives the reduced numerator-denominator Wronskian
identity. -/
theorem ratFuncCoordinateDerivation_eq_zero_cross
    {K : Type*} [Field K] (z : RatFunc K)
    (hz : ratFuncCoordinateDerivation K z = 0) :
    z.denom * z.num.derivative - z.num * z.denom.derivative = 0 := by
  have hden : algebraMap K[X] (RatFunc K) z.denom ≠ 0 :=
    fun hzero => RatFunc.denom_ne_zero z
      (IsFractionRing.injective K[X] (RatFunc K) (by simpa using hzero))
  rw [← RatFunc.num_div_denom z] at hz
  rw [Derivation.leibniz_div,
    ratFuncCoordinateDerivation_algebraMap,
    ratFuncCoordinateDerivation_algebraMap] at hz
  simp only [smul_eq_mul] at hz
  have hcrossF :
      algebraMap K[X] (RatFunc K) z.denom *
          algebraMap K[X] (RatFunc K) z.num.derivative -
        algebraMap K[X] (RatFunc K) z.num *
          algebraMap K[X] (RatFunc K) z.denom.derivative = 0 :=
    (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (inv_ne_zero hden))
  exact IsFractionRing.injective K[X] (RatFunc K)
    (by simpa only [map_sub, map_mul, map_zero] using hcrossF)

/-- Over a field, a polynomial which divides its own derivative has zero derivative. -/
theorem polynomial_derivative_eq_zero_of_dvd_self
    {K : Type*} [Field K] {p : K[X]} (h : p ∣ p.derivative) :
    p.derivative = 0 := by
  by_contra hp'
  have hdeg : p.natDegree ≠ 0 := by
    intro hpdeg
    exact hp' (Polynomial.derivative_of_natDegree_zero hpdeg)
  exact (not_lt_of_ge (Polynomial.natDegree_le_of_dvd h hp'))
    (Polynomial.natDegree_derivative_lt hdeg)

/-- If a rational coordinate derivative vanishes, its reduced numerator is constant. -/
theorem ratFuncCoordinateDerivation_num_derivative_eq_zero
    {K : Type*} [Field K] (z : RatFunc K)
    (hz : ratFuncCoordinateDerivation K z = 0) :
    z.num.derivative = 0 := by
  have hcross := ratFuncCoordinateDerivation_eq_zero_cross z hz
  have heq : z.denom * z.num.derivative = z.num * z.denom.derivative :=
    sub_eq_zero.mp hcross
  have hdiv : z.num ∣ z.num.derivative * z.denom := by
    refine ⟨z.denom.derivative, ?_⟩
    calc
      z.num.derivative * z.denom = z.denom * z.num.derivative := mul_comm _ _
      _ = z.num * z.denom.derivative := heq
  exact polynomial_derivative_eq_zero_of_dvd_self
    ((RatFunc.isCoprime_num_denom z).dvd_of_dvd_mul_right hdiv)

/-- If a rational coordinate derivative vanishes, its normalized denominator is constant. -/
theorem ratFuncCoordinateDerivation_denom_derivative_eq_zero
    {K : Type*} [Field K] (z : RatFunc K)
    (hz : ratFuncCoordinateDerivation K z = 0) :
    z.denom.derivative = 0 := by
  have hcross := ratFuncCoordinateDerivation_eq_zero_cross z hz
  have heq : z.denom * z.num.derivative = z.num * z.denom.derivative :=
    sub_eq_zero.mp hcross
  have hdiv : z.denom ∣ z.denom.derivative * z.num := by
    refine ⟨z.num.derivative, ?_⟩
    calc
      z.denom.derivative * z.num = z.num * z.denom.derivative := mul_comm _ _
      _ = z.denom * z.num.derivative := heq.symm
  exact polynomial_derivative_eq_zero_of_dvd_self
    ((RatFunc.isCoprime_num_denom z).symm.dvd_of_dvd_mul_right hdiv)

/-- **Rational coordinate rigidity.**  In characteristic zero the constants of the coordinate
derivation on `K(t)` are exactly the coefficient field `K`. -/
theorem ratFuncCoordinateDerivation_eq_zero_iff
    {K : Type*} [Field K] [CharZero K] (z : RatFunc K) :
    ratFuncCoordinateDerivation K z = 0 ↔
      ∃ c : K, z = algebraMap K (RatFunc K) c := by
  constructor
  · intro hz
    have hp : z.num = Polynomial.C (z.num.coeff 0) :=
      Polynomial.eq_C_of_derivative_eq_zero
        (ratFuncCoordinateDerivation_num_derivative_eq_zero z hz)
    have hq : z.denom = Polynomial.C (z.denom.coeff 0) :=
      Polynomial.eq_C_of_derivative_eq_zero
        (ratFuncCoordinateDerivation_denom_derivative_eq_zero z hz)
    let a := z.num.coeff 0
    let b := z.denom.coeff 0
    refine ⟨a / b, ?_⟩
    calc
      z = algebraMap K[X] (RatFunc K) z.num /
          algebraMap K[X] (RatFunc K) z.denom :=
        (RatFunc.num_div_denom z).symm
      _ = algebraMap K[X] (RatFunc K) (Polynomial.C a) /
          algebraMap K[X] (RatFunc K) (Polynomial.C b) := by
        rw [hp, hq]
      _ = algebraMap K (RatFunc K) a / algebraMap K (RatFunc K) b := by
        congr 1
      _ = algebraMap K (RatFunc K) (a / b) :=
        (map_div₀ (algebraMap K (RatFunc K)) a b).symm
  · rintro ⟨c, rfl⟩
    exact Derivation.map_algebraMap _ _

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial
open scoped Differential

/-- Evaluating a polynomial in `t` stays in the simple transcendental field generated by `t`. -/
theorem polynomial_aeval_mem_adjoin_simple
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (P : IntermediateField F E) (t : E) (p : P[X]) :
    Polynomial.aeval t p ∈ IntermediateField.adjoin P {t} := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      exact IntermediateField.add_mem _ hp hq
  | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact IntermediateField.mul_mem _
        (IntermediateField.algebraMap_mem _ a)
        ((IntermediateField.adjoin P {t}).toSubfield.pow_mem
          (IntermediateField.subset_adjoin P {t} (Set.mem_singleton t)) n)

/-- If coefficient derivatives lie in `P(t)`, then the coefficient part of differentiating a
polynomial evaluation also lies in `P(t)`. -/
theorem coefficientDerivativeEval_mem_adjoin_simple
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (P : IntermediateField F E) (t : E)
    (hP : ∀ a : P, (a.1)′ ∈ IntermediateField.adjoin P {t})
    (p : P[X]) :
    PolynomialModule.eval t
        (((Differential.deriv : Derivation ℤ E E).compAlgebraMap P).mapCoeffs p) ∈
      IntermediateField.adjoin P {t} := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      change PolynomialModule.eval t
        ((show PolynomialModule E E from
            ((Differential.deriv : Derivation ℤ E E).compAlgebraMap P).mapCoeffs p) +
          (show PolynomialModule E E from
            ((Differential.deriv : Derivation ℤ E E).compAlgebraMap P).mapCoeffs q)) ∈
        IntermediateField.adjoin P {t}
      rw [LinearMap.map_add]
      exact IntermediateField.add_mem _ hp hq
  | monomial n a =>
      rw [Derivation.mapCoeffs_monomial]
      change PolynomialModule.eval t
        (PolynomialModule.single E n ((a.1)′)) ∈ IntermediateField.adjoin P {t}
      rw [PolynomialModule.eval_single, smul_eq_mul]
      exact IntermediateField.mul_mem _
        ((IntermediateField.adjoin P {t}).toSubfield.pow_mem
          (IntermediateField.subset_adjoin P {t} (Set.mem_singleton t)) n)
        (hP a)

/-- A transcendental extension has no total algebraic backward map to its base.  Indeed, an
algebra homomorphism back to the base would send `x` to some base scalar; injectivity would then
identify `x` with that scalar, contradicting transcendence. -/
theorem noAlgHomToBase_of_transcendental
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) (hx : Transcendental K x) :
    IsEmpty (L →ₐ[K] K) := by
  constructor
  intro r
  have hback : x = algebraMap K L (r x) := by
    apply r.injective
    simp
  apply hx
  rw [hback]
  exact isAlgebraic_algebraMap (R := K) (A := L) (r x)

/-- In particular, the simple transcendental clock step `P(t)/P` has no total `P`-algebra
evaluation or retraction.  Any backward clock semantics must therefore leave the category of
fields (for example, by using a place, residue, linear expectation, or boundary projection). -/
theorem noAlgHom_adjoin_to_base_of_transcendental
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (P : IntermediateField F E) (t : E) (ht : Transcendental P t) :
    IsEmpty ((IntermediateField.adjoin P {t}) →ₐ[P] P) := by
  constructor
  intro r
  let Q : IntermediateField P E := IntermediateField.adjoin P {t}
  let tq : Q := ⟨t, IntermediateField.subset_adjoin P {t} (Set.mem_singleton t)⟩
  have hback : tq = algebraMap P Q (r tq) := by
    apply r.injective
    change r tq = r (algebraMap P Q (r tq))
    rw [r.commutes]
    exact (Algebra.algebraMap_self_apply (r tq)).symm
  apply ht
  have ht_eq : t = algebraMap P E (r tq) := by
    exact congrArg Subtype.val hback
  rw [ht_eq]
  exact isAlgebraic_algebraMap (R := P) (A := E) (r tq)

/-- A fresh transcendental coordinate cannot carry a nonzero coefficient back into its base
field. -/
theorem transcendental_mul_mem_base_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (P : IntermediateField F E) (u : E) (hu : Transcendental P u) (b : P) :
    b.1 * u ∈ P ↔ b = 0 := by
  constructor
  · intro hbu
    by_contra hb
    have hbval : b.1 ≠ 0 := by
      intro hb0
      exact hb (Subtype.ext hb0)
    have hu_mem : u ∈ P := by
      have hinv : (b.1)⁻¹ ∈ P := IntermediateField.inv_mem P b.2
      have hprod := IntermediateField.mul_mem P hinv hbu
      simpa [hbval] using hprod
    apply hu
    rw [show u = algebraMap P E (⟨u, hu_mem⟩ : P) from rfl]
    exact isAlgebraic_algebraMap (R := P) (A := E) ⟨u, hu_mem⟩
  · rintro rfl
    simp

/-- **Rank-one clock-boundary theorem.**  Let `P(t)` be a simple transcendental observable
extension.  Suppose differentiating coefficients of `P` stays in `P(t)`, while `t'` is
transcendental over `P(t)`.  Then an observable in `P(t)` has derivative in `P(t)` exactly when it
already belongs to `P`.

This is the abstract one-layer erosion law.  It permits an arbitrary coefficient derivation, so
all closure failure is localized in the single fresh coordinate `t'`; there is no bulk leakage. -/
theorem simpleTranscendental_clock_internal_iff
    {F E : Type*} [Field F] [Field E] [CharZero E] [Algebra F E] [Differential E]
    (P : IntermediateField F E) (t z : E)
    (ht : Transcendental P t)
    (hP : ∀ a : P, (a.1)′ ∈ IntermediateField.adjoin P {t})
    (htop : Transcendental (IntermediateField.adjoin P {t}) t′)
    (hz : z ∈ IntermediateField.adjoin P {t}) :
    z′ ∈ IntermediateField.adjoin P {t} ↔ z ∈ P := by
  let Q : IntermediateField P E := IntermediateField.adjoin P {t}
  let e : RatFunc P ≃ₐ[P] Q := RatFunc.algEquivOfTranscendental t ht
  let w : RatFunc P := e.symm ⟨z, hz⟩
  have hew : e w = (⟨z, hz⟩ : Q) := e.apply_symm_apply _
  have hzrepr : z = Polynomial.aeval t w.num / Polynomial.aeval t w.denom := by
    have happ := RatFunc.algEquivOfTranscendental_apply t ht w
    have hval := happ
    have hewval := congrArg Subtype.val hew
    rw [hewval] at hval
    exact hval
  constructor
  · intro hz'
    let A : E := Polynomial.aeval t w.num
    let B : E := Polynomial.aeval t w.denom
    let Ac : E := PolynomialModule.eval t
      (((Differential.deriv : Derivation ℤ E E).compAlgebraMap P).mapCoeffs w.num)
    let Bc : E := PolynomialModule.eval t
      (((Differential.deriv : Derivation ℤ E E).compAlgebraMap P).mapCoeffs w.denom)
    let boundary : E := B⁻¹ ^ 2 *
      (B * Polynomial.aeval t w.num.derivative -
        A * Polynomial.aeval t w.denom.derivative)
    let internal : E := B⁻¹ ^ 2 * (B * Ac - A * Bc)
    have hnum := Derivation.apply_aeval_eq
      (Differential.deriv : Derivation ℤ E E) t w.num
    have hden := Derivation.apply_aeval_eq
      (Differential.deriv : Derivation ℤ E E) t w.denom
    have hclock : z′ = internal + boundary * t′ := by
      rw [hzrepr, Derivation.leibniz_div, hnum, hden]
      simp only [smul_eq_mul]
      dsimp only [A, B, Ac, Bc, boundary, internal]
      ring
    have hA : A ∈ Q := polynomial_aeval_mem_adjoin_simple P t w.num
    have hBmem : B ∈ Q := polynomial_aeval_mem_adjoin_simple P t w.denom
    have hA' : Polynomial.aeval t w.num.derivative ∈ Q :=
      polynomial_aeval_mem_adjoin_simple P t w.num.derivative
    have hB' : Polynomial.aeval t w.denom.derivative ∈ Q :=
      polynomial_aeval_mem_adjoin_simple P t w.denom.derivative
    have hAc : Ac ∈ Q := coefficientDerivativeEval_mem_adjoin_simple P t hP w.num
    have hBc : Bc ∈ Q := coefficientDerivativeEval_mem_adjoin_simple P t hP w.denom
    have hBinv2 : B⁻¹ ^ (2 : ℕ) ∈ Q :=
      Q.toSubfield.pow_mem (IntermediateField.inv_mem Q hBmem) 2
    have hboundary : boundary ∈ Q := by
      exact IntermediateField.mul_mem Q hBinv2
        (IntermediateField.sub_mem Q
          (IntermediateField.mul_mem Q hBmem hA')
          (IntermediateField.mul_mem Q hA hB'))
    have hinternal : internal ∈ Q := by
      exact IntermediateField.mul_mem Q hBinv2
        (IntermediateField.sub_mem Q
          (IntermediateField.mul_mem Q hBmem hAc)
          (IntermediateField.mul_mem Q hA hBc))
    let boundaryQ : Q := ⟨boundary, hboundary⟩
    have hboundary_top : boundary * t′ ∈ Q := by
      have hsub : z′ - internal ∈ Q := IntermediateField.sub_mem Q hz' hinternal
      rw [hclock] at hsub
      simpa only [add_sub_cancel_left] using hsub
    have hboundary_zero : boundary = 0 := by
      have hqzero : boundaryQ = 0 :=
        (transcendental_mul_mem_base_iff Q t′ htop boundaryQ).mp hboundary_top
      exact congrArg Subtype.val hqzero
    have hB : B ≠ 0 := by
      intro hzero
      apply RatFunc.denom_ne_zero w
      apply (transcendental_iff_injective.mp ht)
      simpa only [map_zero] using hzero
    have hcrossEval :
        B * Polynomial.aeval t w.num.derivative -
          A * Polynomial.aeval t w.denom.derivative = 0 := by
      exact (mul_eq_zero.mp hboundary_zero).resolve_left
        (pow_ne_zero 2 (inv_ne_zero hB))
    have hcross :
        w.denom * w.num.derivative - w.num * w.denom.derivative = 0 := by
      apply (transcendental_iff_injective.mp ht)
      simpa only [map_sub, map_mul, map_zero, A, B] using hcrossEval
    have hwzero : ratFuncCoordinateDerivation P w = 0 := by
      rw [ratFuncCoordinateDerivation_apply]
      have hmapcross :
          algebraMap P[X] (RatFunc P) w.denom *
              algebraMap P[X] (RatFunc P) w.num.derivative -
            algebraMap P[X] (RatFunc P) w.num *
              algebraMap P[X] (RatFunc P) w.denom.derivative = 0 := by
        simpa only [map_sub, map_mul, map_zero] using
          congrArg (algebraMap P[X] (RatFunc P)) hcross
      rw [hmapcross, mul_zero]
    obtain ⟨c, hc⟩ := (ratFuncCoordinateDerivation_eq_zero_iff w).mp hwzero
    have hewc : e (algebraMap P (RatFunc P) c) = (⟨z, hz⟩ : Q) := by
      rw [← hc]
      exact hew
    have hval := congrArg Subtype.val hewc
    have hcomm := congrArg Subtype.val (e.commutes c)
    have hcz : c.1 = z := by
      calc
        c.1 = (algebraMap P Q c).1 := rfl
        _ = (e (algebraMap P (RatFunc P) c)).1 := hcomm.symm
        _ = z := hval
    rw [← hcz]
    exact c.2
  · intro hzP
    exact hP ⟨z, hzP⟩

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

/-- The field of rational observables visible below jet order `N`. -/
def jetObservableField
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (x : E) (N : ℕ) : IntermediateField F E :=
  IntermediateField.adjoin F ((fun n : ℕ => differentialJet n x) '' Set.Iio N)

/-- Adding one unit of observational resolution adjoins exactly the next jet coordinate. -/
theorem jetObservableField_succ
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (x : E) (N : ℕ) :
    jetObservableField F x (N + 1) =
      (IntermediateField.adjoin (jetObservableField F x N) {differentialJet N x}).restrictScalars F := by
  have hIio : Set.Iio (N + 1) = insert N (Set.Iio N) := by
    ext m
    change m < N + 1 ↔ m = N ∨ m < N
    omega
  have himage :
      (fun n : ℕ => differentialJet n x) '' insert N (Set.Iio N) =
        insert (differentialJet N x)
          ((fun n : ℕ => differentialJet n x) '' Set.Iio N) :=
    Set.image_insert_eq
  rw [jetObservableField, jetObservableField, hIio, himage,
    ← Set.union_singleton, IntermediateField.adjoin_adjoin_left]

/-- Hypertranscendence makes the next jet transcendental over every finite observable prefix. -/
theorem hypertranscendental_jet_transcendental_observableField
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    Transcendental (jetObservableField F x N) (differentialJet N x) := by
  have hj : AlgebraicIndependent F (fun n : ℕ => differentialJet n x) :=
    algebraicIndependent_differentialJet_of_hypertranscendentalOver hx
  apply (IntermediateField.transcendental_adjoin_iff).2
  exact hj.transcendental_adjoin (by simp)

/-- **No algebraic backward clock.**  Every hypertranscendental jet step is a proper
transcendental field extension and admits no total algebra homomorphism back to the preceding
observable field.  Thus the forward jet filtration is not an inverse system in the field
category; every backward realization necessarily adds external boundary structure. -/
theorem hypertranscendental_no_backwardClock_algHom
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    IsEmpty
      ((IntermediateField.adjoin (jetObservableField F x N)
          {differentialJet N x}) →ₐ[jetObservableField F x N]
        jetObservableField F x N) :=
  noAlgHom_adjoin_to_base_of_transcendental
    (jetObservableField F x N) (differentialJet N x)
    (hypertranscendental_jet_transcendental_observableField hx N)

/-- Differentiating an observable visible below order `N` introduces no jet beyond order `N`. -/
theorem jetObservableField_deriv_mem_succ
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E]
    (x : E) (N : ℕ) {z : E} (hz : z ∈ jetObservableField F x N) :
    z′ ∈ jetObservableField F x (N + 1) := by
  have hmono : jetObservableField F x N ≤ jetObservableField F x (N + 1) := by
    apply IntermediateField.adjoin.mono F
    exact Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ N))
  apply IntermediateField.adjoin_induction F
    (s := (fun n : ℕ => differentialJet n x) '' Set.Iio N)
    (p := fun y _ => y′ ∈ jetObservableField F x (N + 1))
  · rintro y ⟨n, hn, rfl⟩
    change n < N at hn
    rw [← differentialJet_succ]
    apply IntermediateField.subset_adjoin F _
    exact ⟨n + 1, Nat.add_lt_add_right hn 1, rfl⟩
  · intro c
    rw [deriv_algebraMap]
    exact IntermediateField.algebraMap_mem _ _
  · intro a b ha hb hda hdb
    rw [map_add]
    exact IntermediateField.add_mem _ hda hdb
  · intro a ha hda
    rw [Derivation.leibniz_inv]
    have hainv : a⁻¹ ∈ jetObservableField F x (N + 1) :=
      IntermediateField.inv_mem _ (hmono ha)
    have hasq : a⁻¹ ^ (2 : ℕ) ∈ jetObservableField F x (N + 1) :=
      (jetObservableField F x (N + 1)).toSubfield.pow_mem hainv 2
    exact IntermediateField.mul_mem _ (IntermediateField.neg_mem _ hasq) hda
  · intro a b ha hb hda hdb
    rw [Derivation.leibniz]
    exact IntermediateField.add_mem _
      (IntermediateField.mul_mem _ (hmono ha) hdb)
      (IntermediateField.mul_mem _ (hmono hb) hda)
  exact hz

/-- At every cutoff, the derivative of the boundary coordinate is fresh over the entire current
observable field. -/
theorem hypertranscendental_boundaryDeriv_transcendental_stepField
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) :
    Transcendental
      (IntermediateField.adjoin (jetObservableField F x N) {differentialJet N x})
      (differentialJet N x)′ := by
  have h := hypertranscendental_jet_transcendental_observableField hx (N + 1)
  rw [jetObservableField_succ] at h
  rw [← differentialJet_succ]
  exact h

/-- **Hypertranscendental one-tick erosion.**  Among rational observables visible through jet order
`N`, the ones whose derivative is still visible at that resolution are exactly the observables
visible through order `N - 1` (with the indexing convention that `P_(N+1)` contains jets
`0,...,N`). -/
theorem hypertranscendental_clock_internal_iff
    {F E : Type*} [Field F] [Field E] [CharZero E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    {x : E} (hx : HypertranscendentalOver F x) (N : ℕ) {z : E}
    (hz : z ∈ jetObservableField F x (N + 1)) :
    z′ ∈ jetObservableField F x (N + 1) ↔ z ∈ jetObservableField F x N := by
  let P : IntermediateField F E := jetObservableField F x N
  let Q : IntermediateField P E :=
    IntermediateField.adjoin P {differentialJet N x}
  have hstep : jetObservableField F x (N + 1) = Q.restrictScalars F :=
    jetObservableField_succ F x N
  have hzQ : z ∈ Q := by
    have hzR : z ∈ Q.restrictScalars F := by
      rw [← hstep]
      exact hz
    exact hzR
  have ht : Transcendental P (differentialJet N x) :=
    hypertranscendental_jet_transcendental_observableField hx N
  have hP : ∀ a : P, (a.1)′ ∈ Q := by
    intro a
    have ha := jetObservableField_deriv_mem_succ x N a.2
    rw [hstep] at ha
    exact ha
  have htop : Transcendental Q (differentialJet N x)′ :=
    hypertranscendental_boundaryDeriv_transcendental_stepField hx N
  have hcore := simpleTranscendental_clock_internal_iff
    P (differentialJet N x) z ht hP htop hzQ
  constructor
  · intro hzder
    apply hcore.mp
    have hzderR : z′ ∈ Q.restrictScalars F := by
      rw [← hstep]
      exact hzder
    exact hzderR
  · intro hzP
    have hzderQ := hcore.mpr hzP
    have hzderR : z′ ∈ Q.restrictScalars F := hzderQ
    rw [← hstep] at hzderR
    exact hzderR

/-- Increasing observational resolution only enlarges the observable field. -/
theorem jetObservableField_mono
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (x : E) {M N : ℕ} (hMN : M ≤ N) :
    jetObservableField F x M ≤ jetObservableField F x N := by
  apply IntermediateField.adjoin.mono F
  exact Set.image_mono (Set.Iio_subset_Iio hMN)

/-- `r` clock ticks applied to an order-`N` observable are visible at order `N+r`. -/
theorem differentialJet_mem_jetObservableField_add
    {F E : Type*} [Field F] [Field E] [Differential F] [Differential E]
    [Algebra F E] [DifferentialAlgebra F E]
    (x : E) {N : ℕ} {z : E} (hz : z ∈ jetObservableField F x N) (r : ℕ) :
    differentialJet r z ∈ jetObservableField F x (N + r) := by
  induction r with
  | zero => simpa using hz
  | succ r ih =>
      rw [differentialJet_succ]
      simpa only [Nat.add_assoc] using jetObservableField_deriv_mem_succ x (N + r) ih

/-- **Exact finite clock erosion.**  At resolution `N+r`, surviving every clock test through tick
`r` is equivalent to having started in the order-`N` observable field.  Thus every tick removes
exactly one outer rational jet layer, independently of the bulk size. -/
theorem hypertranscendental_clock_erosion_iff
    {F E : Type*} [Field F] [Field E] [CharZero E]
    [Differential F] [Differential E] [Algebra F E] [DifferentialAlgebra F E]
    {x : E} (hx : HypertranscendentalOver F x) (N r : ℕ) {z : E} :
    (∀ q : ℕ, q ≤ r →
      differentialJet q z ∈ jetObservableField F x (N + r)) ↔
      z ∈ jetObservableField F x N := by
  induction r with
  | zero =>
      constructor
      · intro h
        simpa using h 0 (Nat.le_refl 0)
      · intro hz q hq
        have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
        subst q
        simpa using hz
  | succ r ih =>
      constructor
      · intro h
        apply ih.mp
        intro q hqr
        let y := differentialJet q z
        have hy : y ∈ jetObservableField F x ((N + r) + 1) := by
          simpa only [y, Nat.add_assoc] using h q (Nat.le_trans hqr (Nat.le_succ r))
        have hy' : y′ ∈ jetObservableField F x ((N + r) + 1) := by
          have hnext := h (q + 1) (Nat.add_le_add_right hqr 1)
          simpa only [y, ← differentialJet_succ, Nat.add_assoc] using hnext
        exact (hypertranscendental_clock_internal_iff hx (N + r) hy).mp hy'
      · intro hz q hqr
        have hq := differentialJet_mem_jetObservableField_add x hz q
        exact jetObservableField_mono x (Nat.add_le_add_left hqr N) hq

/-! ### The linearized one-layer clock boundary -/

/-- The additive copy of an inner observable field `C` inside a finite observable field `B`.
Quotienting by this subgroup linearizes the interval `C ≤ B` without pretending that a quotient of
fields exists. -/
def clockBoundarySubgroup
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (C B : IntermediateField F E) : AddSubgroup B :=
  C.toSubfield.toAddSubgroup.comap B.toSubfield.subtype.toAddMonoidHom

/-- The derivative of an observable, reduced modulo the current observable field. -/
def clockBoundaryRawSymbol
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (B : IntermediateField F E) :
    B →+ E ⧸ B.toSubfield.toAddSubgroup :=
  (QuotientAddGroup.mk' B.toSubfield.toAddSubgroup).comp
    ((Differential.deriv : Derivation ℤ E E).toLinearMap.toAddMonoidHom.comp
      B.toSubfield.subtype.toAddMonoidHom)

/-- The one-layer clock symbol descends modulo any inner field whose derivatives remain visible in
the outer field. -/
def clockBoundarySymbol
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (C B : IntermediateField F E)
    (hder : ∀ z : E, z ∈ C → z′ ∈ B) :
    (B ⧸ clockBoundarySubgroup C B) →+
      (E ⧸ B.toSubfield.toAddSubgroup) :=
  QuotientAddGroup.lift (clockBoundarySubgroup C B)
    (clockBoundaryRawSymbol B) (by
      intro z hz
      rw [AddMonoidHom.mem_ker]
      change (↑z.1′ : E ⧸ B.toSubfield.toAddSubgroup) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      exact hder z.1 hz)

@[simp] theorem clockBoundarySymbol_mk
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (C B : IntermediateField F E)
    (hder : ∀ z : E, z ∈ C → z′ ∈ B) (z : B) :
    clockBoundarySymbol C B hder (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk z.1′ := rfl

/-- Exact identification of the one-tick internal core is equivalent to injectivity of the
linearized boundary symbol.  This is the exact sequence underlying the proposed decorated boundary
theory; it has no degeneracy until an external constraint is added. -/
theorem clockBoundarySymbol_injective
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (C B : IntermediateField F E) (hCB : C ≤ B)
    (hcore : ∀ z : E, z ∈ B → (z′ ∈ B ↔ z ∈ C)) :
    Function.Injective
      (clockBoundarySymbol C B (fun z hz => (hcore z (hCB hz)).2 hz)) := by
  intro q₁ q₂ heq
  have hqmap :
      clockBoundarySymbol C B (fun z hz => (hcore z (hCB hz)).2 hz) (q₁ - q₂) = 0 := by
    rw [map_sub, heq, sub_self]
  have hzero_of_map_zero :
      ∀ q,
        clockBoundarySymbol C B (fun z hz => (hcore z (hCB hz)).2 hz) q = 0 → q = 0 := by
    intro q
    refine QuotientAddGroup.induction_on q ?_
    intro z hz
    rw [clockBoundarySymbol_mk, QuotientAddGroup.eq_zero_iff] at hz
    rw [QuotientAddGroup.eq_zero_iff]
    exact (hcore z.1 z.2).mp hz
  exact sub_eq_zero.mp (hzero_of_map_zero (q₁ - q₂) hqmap)

/-! ### Intrinsic Kähler boundary covectors -/

/-- Coordinate derivation on the rational field generated by an algebraically independent
family.  These derivations form the dual coordinate system used to certify independence of the
intrinsic Kähler clock boundaries. -/
def adjoinCoordinateDerivation
    {ι K L : Type*} [DecidableEq ι] [Field K] [Field L] [Algebra K L]
    {x : ι → L} (hx : AlgebraicIndependent K x) (i : ι) :
    Derivation K (IntermediateField.adjoin K (Set.range x))
      (IntermediateField.adjoin K (Set.range x)) := by
  let Q := FractionRing (MvPolynomial ι K)
  let dpoly : Derivation K (MvPolynomial ι K) Q :=
    MvPolynomial.mkDerivation K (fun j ↦ if j = i then 1 else 0)
  let dfrac : Derivation K Q Q :=
    GaloisForLFunctions.fractionRingDerivation dpoly
  let e : Q ≃ₐ[K] IntermediateField.adjoin K (Set.range x) :=
    hx.aevalEquivField
  exact GaloisForLFunctions.transportDerivation e dfrac

@[simp] theorem adjoinCoordinateDerivation_apply_coordinate
    {ι K L : Type*} [DecidableEq ι] [Field K] [Field L] [Algebra K L]
    {x : ι → L} (hx : AlgebraicIndependent K x) (i j : ι) :
    adjoinCoordinateDerivation hx i
      (⟨x j, IntermediateField.subset_adjoin K (Set.range x) ⟨j, rfl⟩⟩) =
        if j = i then 1 else 0 := by
  classical
  let F := IntermediateField.adjoin K (Set.range x)
  let Q := FractionRing (MvPolynomial ι K)
  let dpoly : Derivation K (MvPolynomial ι K) Q :=
    MvPolynomial.mkDerivation K (fun k ↦ if k = i then 1 else 0)
  let dfrac : Derivation K Q Q :=
    GaloisForLFunctions.fractionRingDerivation dpoly
  let e : Q ≃ₐ[K] F := hx.aevalEquivField
  let xj : F :=
    ⟨x j, IntermediateField.subset_adjoin K (Set.range x) ⟨j, rfl⟩⟩
  have heX : e.symm xj = algebraMap (MvPolynomial ι K) Q (MvPolynomial.X j) := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change x j = (hx.aevalEquivField
      (algebraMap (MvPolynomial ι K) Q (MvPolynomial.X j)) : F)
    rw [hx.aevalEquivField_algebraMap_apply_coe]
    simp
  change GaloisForLFunctions.transportDerivation e dfrac xj = _
  rw [GaloisForLFunctions.transportDerivation_apply, heX]
  rw [GaloisForLFunctions.fractionRingDerivation_algebraMap]
  simp [dpoly]

/-- Universal differentials of an algebraically independent family remain linearly independent
over its generated rational function field.  This is the coordinate-free direct-sum half of the
Kähler--Tate clock construction. -/
theorem kaehlerD_adjoin_coordinates_linearIndependent
    {ι K L : Type*} [DecidableEq ι] [Field K] [Field L] [Algebra K L]
    {x : ι → L} (hx : AlgebraicIndependent K x) :
    let F := IntermediateField.adjoin K (Set.range x)
    LinearIndependent F (fun i : ι ↦
      KaehlerDifferential.D K F
        (⟨x i, IntermediateField.subset_adjoin K (Set.range x) ⟨i, rfl⟩⟩ : F)) := by
  classical
  dsimp only
  apply linearIndependent_iff'.mpr
  intro s g hrel i hi
  have hmap := congrArg
    (adjoinCoordinateDerivation hx i).liftKaehlerDifferential hrel
  simp only [map_sum, map_smul, map_zero,
    Derivation.liftKaehlerDifferential_comp_D,
    adjoinCoordinateDerivation_apply_coordinate] at hmap
  simpa [hi] using hmap

/-- The full rational field generated by all finite clock observables. -/
def jetObservableFieldInfinity
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (x : E) : IntermediateField F E :=
  IntermediateField.adjoin F (Set.range fun n : ℕ ↦ differentialJet n x)

/-- **Infinite intrinsic Kähler clock capacity.**  The universal differentials of all jet
coordinates of a hypertranscendental element are linearly independent over the full rational jet
field.  Hence each finite clock cut adds a genuinely new cotangent boundary line, before any
analytic completion or Hermitian structure is chosen. -/
theorem hypertranscendental_kaehlerD_jet_linearIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {x : E} (hx : HypertranscendentalOver F x) :
    LinearIndependent (jetObservableFieldInfinity F x) (fun n : ℕ ↦
      KaehlerDifferential.D F (jetObservableFieldInfinity F x)
        (⟨differentialJet n x,
          IntermediateField.subset_adjoin F
            (Set.range fun q : ℕ ↦ differentialJet q x) ⟨n, rfl⟩⟩ :
          jetObservableFieldInfinity F x)) := by
  exact kaehlerD_adjoin_coordinates_linearIndependent
    (algebraicIndependent_differentialJet_of_hypertranscendentalOver hx)

/-- **Affine-origin no-go.**  Relative Kähler clock covectors forget every base-valued
translation, at every jet order.  Thus the Kähler--Tate linearization records infinitesimal clock
capacity but cannot by itself recover the source's affine origin. -/
theorem kaehlerD_differentialJet_addBase_eq
    {F E : Type*} [Field F] [Field E]
    [Algebra F E] [Differential F] [Differential E] [DifferentialAlgebra F E]
    (n : ℕ) (x : E) (c : F) :
    KaehlerDifferential.D F E
        (differentialJet n (x + algebraMap F E c)) =
      KaehlerDifferential.D F E (differentialJet n x) := by
  rw [differentialJet_add_algebraMap]
  simp

/-- A derivation-constant base scalar acts diagonally on every jet order. -/
theorem differentialJet_algebraMap_mul_of_deriv_eq_zero
    {F E : Type*} [Field F] [Field E]
    [Algebra F E] [Differential F] [Differential E] [DifferentialAlgebra F E]
    (n : ℕ) (a : F) (ha : a′ = 0) (x : E) :
    differentialJet n (algebraMap F E a * x) =
      algebraMap F E a * differentialJet n x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, ih,
        Derivation.leibniz, deriv_algebraMap, ha]
      simp

/-- **Affine-calibration law.**  Relative Kähler clock covectors remember a common constant unit
but forget the affine origin.  The full jet cotangent flag therefore determines only an affine
calibration class, so a source normalization must be supplied as torsor data beyond the vector
Tate clock. -/
theorem kaehlerD_differentialJet_affineConstant_eq
    {F E : Type*} [Field F] [Field E]
    [Algebra F E] [Differential F] [Differential E] [DifferentialAlgebra F E]
    (n : ℕ) (x : E) (a b : F) (ha : a′ = 0) :
    KaehlerDifferential.D F E
        (differentialJet n (algebraMap F E a * x + algebraMap F E b)) =
      algebraMap F E a •
        KaehlerDifferential.D F E (differentialJet n x) := by
  rw [differentialJet_add_algebraMap,
    differentialJet_algebraMap_mul_of_deriv_eq_zero n a ha x]
  simp

/-! ### The self-dual algebraic Tate-clock skeleton -/

/-- Successor as the forward clock embedding. -/
def tateClockSucc : ℕ ↪ ℕ :=
  ⟨Nat.succ, Nat.succ_injective⟩

/-- Forward shift on the discrete/Ind half of the algebraic Tate clock. -/
def tateClockIndForward {K : Type*} [Zero K]
    (a : ℕ →₀ K) : ℕ →₀ K :=
  Finsupp.embDomain tateClockSucc a

@[simp] theorem tateClockIndForward_apply_zero
    {K : Type*} [Zero K] (a : ℕ →₀ K) :
    tateClockIndForward a 0 = 0 := by
  simp [tateClockIndForward, tateClockSucc, Finsupp.embDomain_apply]

@[simp] theorem tateClockIndForward_apply_succ
    {K : Type*} [Zero K] (a : ℕ →₀ K) (n : ℕ) :
    tateClockIndForward a (n + 1) = a n := by
  exact Finsupp.embDomain_apply_self tateClockSucc a n

theorem tateClockIndForward_injective
    {K : Type*} [Zero K] :
    Function.Injective (tateClockIndForward : (ℕ →₀ K) → ℕ →₀ K) :=
  Finsupp.embDomain_injective tateClockSucc

/-- The range of the forward clock consists exactly of finite sequences with zero boundary
coordinate.  Together with surjectivity of evaluation at zero, this is the exact Ind sequence
`0 → K^(ℕ) → K^(ℕ) → K → 0`. -/
theorem exists_tateClockIndForward_iff_apply_zero_eq_zero
    {K : Type*} [Zero K] (a : ℕ →₀ K) :
    (∃ b, tateClockIndForward b = a) ↔ a 0 = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact tateClockIndForward_apply_zero b
  · intro hzero
    have hsupp : (↑a.support : Set ℕ) ⊆ Set.range tateClockSucc := by
      intro n hn
      cases n with
      | zero =>
          have hn0 : a 0 ≠ 0 := Finsupp.mem_support_iff.mp hn
          exact (hn0 hzero).elim
      | succ n => exact ⟨n, rfl⟩
    let b : ℕ →₀ K :=
      Finsupp.comapDomain tateClockSucc a tateClockSucc.injective.injOn
    exact ⟨b, Finsupp.embDomain_comapDomain hsupp⟩

theorem tateClockInd_evalZero_surjective
    {K : Type*} [Zero K] :
    Function.Surjective (fun a : ℕ →₀ K ↦ a 0) := by
  intro c
  exact ⟨Finsupp.single 0 c, by simp⟩

/-- Backward shift on the linearly compact/Pro half of the algebraic Tate clock. -/
def tateClockProBackward {K : Type*} (p : ℕ → K) : ℕ → K :=
  fun n ↦ p (n + 1)

theorem tateClockProBackward_surjective
    {K : Type*} [Zero K] :
    Function.Surjective (tateClockProBackward : (ℕ → K) → ℕ → K) := by
  intro p
  let q : ℕ → K := fun n ↦ match n with
    | 0 => 0
    | m + 1 => p m
  refine ⟨q, ?_⟩
  funext n
  rfl

/-- The one-dimensional boundary embedded in the Pro clock. -/
def tateClockProBoundary {K : Type*} [Zero K] (c : K) : ℕ → K :=
  fun n ↦ if n = 0 then c else 0

/-- The backward clock loses exactly the boundary line and nothing else.  This is the exact Pro
sequence `0 → K → K^ℕ → K^ℕ → 0`, dual to the Ind sequence above. -/
theorem tateClockProBackward_eq_zero_iff_exists_boundary
    {K : Type*} [Zero K] (p : ℕ → K) :
    tateClockProBackward p = 0 ↔ ∃ c, p = tateClockProBoundary c := by
  constructor
  · intro hback
    refine ⟨p 0, ?_⟩
    funext n
    cases n with
    | zero => simp [tateClockProBoundary]
    | succ n =>
        have hn := congrFun hback n
        simpa [tateClockProBackward, tateClockProBoundary] using hn
  · rintro ⟨c, rfl⟩
    funext n
    simp [tateClockProBackward, tateClockProBoundary]

/-- Restricted evaluation pairing between the Ind and Pro clock halves. -/
def tateClockPairing {K : Type*} [Semiring K]
    (a : ℕ →₀ K) (p : ℕ → K) : K :=
  a.sum fun n c ↦ c * p n

/-- Forward shift on the Ind half is adjoint to backward shift on the Pro half.  Therefore the
rank-one cokernel of the forward clock and rank-one kernel of the backward clock are the two dual
faces of one thin boundary. -/
theorem tateClockPairing_indForward
    {K : Type*} [Semiring K] (a : ℕ →₀ K) (p : ℕ → K) :
    tateClockPairing (tateClockIndForward a) p =
      tateClockPairing a (tateClockProBackward p) := by
  rw [tateClockPairing, tateClockIndForward, Finsupp.sum_embDomain]
  rfl

/-- Every finite set of formal clock observables can be varied independently inside `W`.  This
is the linear tangent form of having no finite observable constraint. -/
def TateClockFiniteObservableSurjective
    {K : Type*} [Semiring K] (W : Submodule K (ℕ → K)) : Prop :=
  ∀ s : Finset ℕ,
    Function.Surjective (fun w : W ↦ fun i : s ↦ w.1 i.1)

/-- **Finite-observable conormal no-go.**  If admissible source variations realize arbitrary
values on every finite set of clock coordinates, then no nonzero finitely supported clock
covector annihilates them.  Consequently a nontrivial constraint conormal must live beyond the
ordinary finite-support Kähler cotangent, in a source-selected enlarged dual or corona. -/
theorem tateClock_finiteObservable_conormal_eq_zero
    {K : Type*} [Field K]
    (W : Submodule K (ℕ → K)) (hW : TateClockFiniteObservableSurjective W)
    (a : ℕ →₀ K) (ha : ∀ w : W, tateClockPairing a w.1 = 0) :
    a = 0 := by
  classical
  ext i
  by_cases hi : a i = 0
  · exact hi
  · have hisupp : i ∈ a.support := Finsupp.mem_support_iff.mpr hi
    let target : a.support → K := fun j ↦ if j.1 = i then 1 else 0
    obtain ⟨w, hw⟩ := hW a.support target
    have hw' : ∀ n ∈ a.support, w.1 n = if n = i then 1 else 0 := by
      intro n hn
      exact congrFun hw ⟨n, hn⟩
    have hz := ha w
    have heval : tateClockPairing a w.1 = a i := by
      rw [tateClockPairing]
      calc
        a.sum (fun n c ↦ c * w.1 n) =
            a.sum (fun n c ↦ c * if n = i then 1 else 0) := by
              apply Finsupp.sum_congr
              intro n hn
              rw [hw' n hn]
        _ = a i := by simp [hisupp]
    rw [heval] at hz
    exact hz

end

end GaloisForLFunctions.HTGeometry
