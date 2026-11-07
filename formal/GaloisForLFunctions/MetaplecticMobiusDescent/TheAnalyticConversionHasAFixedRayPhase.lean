/-
The finite square-phase factorization is adapted from OpenAI’s formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheQuadraticGaussPhaseLivesModuloFour
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicPhaseLivesModuloTwo

/-!
# The analytic conversion has a fixed ray phase

Square-root counting and CRT identify the quadratic-character Gauss sum with
the actual trace square sum. Its exact evaluation separates the Möbius-to-cubic
conversion into a phase depending only on the modulus modulo four and the
explicit angular factor `‖c‖/c`.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.MetaplecticMobiusDescent

namespace ProductGauss

/-- Counting square roots identifies the quadratic-character Gauss sum with its square phase. -/
theorem quadratic_eq_square_sum {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hchar : ringChar F ≠ 2) (hψ : ψ ≠ 1) :
    gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ =
      ∑ x : F, ψ (x ^ 2) := by
  classical
  have hfiber : (∑ x : F, ψ (x ^ 2)) =
      ∑ y : F, (({x : F | x ^ 2 = y}.toFinset.card : ℕ) : ℂ) * ψ y := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun x : F => x ^ 2) (f := fun x : F => ψ (x ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_congr rfl (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hx])]
    simp
  have hcount (y : F) : (({x : F | x ^ 2 = y}.toFinset.card : ℕ) : ℂ) =
      (quadraticChar F y : ℂ) + 1 := by
    exact_mod_cast quadraticChar_card_sqrts hchar y
  rw [hfiber]
  simp_rw [hcount, add_mul, one_mul]
  rw [Finset.sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, add_zero]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]

/-- The square phase factors over the actual coordinate decomposition. -/
theorem square_sum_factorization (ψ : AddChar (∀ i, F i) ℂ) :
    (∑ x : ∀ i, F i, ψ (x ^ 2)) =
      ∏ i, ∑ y : F i, localChar F ψ i (y ^ 2) := by
  simp_rw [character_eq_prod F ψ, Pi.pow_apply]
  exact (Fintype.prod_sum (fun i y => localChar F ψ i (y ^ 2))).symm

/-- A primitive character on a product of odd finite fields has the same quadratic Gauss sum and square sum. -/
theorem quadratic_factorization_equiv {R : Type*} [CommRing R] [Fintype R]
    (e : R ≃+* ∀ i, F i) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (hchar : ∀ i, ringChar (F i) ≠ 2) :
    (∑ x : R, (∏ i, ((quadraticChar (F i)).ringHomComp (Int.castRingHom ℂ)) (e x i)) * ψ x) =
      ∑ x : R, ψ (x ^ 2) := by
  rw [factorization_equiv F e]
  have hψ' := primitive_comp_ringEquiv e.symm ψ hψ
  calc
    _ = ∏ i, ∑ y : F i,
        localChar F (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i (y ^ 2) := by
      apply Finset.prod_congr rfl
      intro i _
      apply quadratic_eq_square_sum _ (hchar i)
      have hp := localChar_primitive F _ hψ' i
      simpa only [AddChar.mulShift_one] using hp (a := 1) one_ne_zero
    _ = ∑ x : ∀ i, F i, (ψ.compAddMonoidHom e.symm.toAddMonoidHom) (x ^ 2) :=
      (square_sum_factorization F _).symm
    _ = ∑ x : R, ψ (x ^ 2) := by
      apply Fintype.sum_equiv e.symm.toEquiv
      intro x
      change ψ (e.symm (x ^ 2)) = ψ ((e.symm x) ^ 2)
      rw [map_pow]

end ProductGauss
namespace Eisenstein

/-- The fixed cubic residue factor of the conversion. -/
def cubicRayPhase (c : O) : ℂ :=
  ringComplex (cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal c))

/-- The finite ray factor after separating the complex argument of the modulus. -/
def rayConversionPhase (c : O) : ℂ := cubicRayPhase c / fixedDualAverage c

theorem cubicRayPhase_eq_of_mod_four (c d : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) :
    cubicRayPhase c = cubicRayPhase d := by
  obtain ⟨w,hw⟩ := Ideal.mem_span_singleton.mp
    ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h)
  apply congrArg ringComplex
  apply congrArg (cubicChar cubicTwoIdeal cubicTwoIdeal_good)
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [cubicTwoIdeal, Ideal.span_singleton_neg]
  exact Ideal.mem_span_singleton.mpr ⟨2*w, by linear_combination hw⟩

/-- All finite arithmetic phases factor through the modulus modulo four. -/
theorem rayConversionPhase_eq_of_mod_four (c d : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) :
    rayConversionPhase c = rayConversionPhase d := by
  rw [rayConversionPhase, rayConversionPhase,
    cubicRayPhase_eq_of_mod_four c d h, fixedDualAverage_eq_of_mod_four c d h]

theorem rayConversionPhase_one : rayConversionPhase 1 = 1 := by
  simp only [rayConversionPhase, cubicRayPhase, fixedDualAverage_one, map_one, div_one]

theorem rayConversionPhase_eq_one (c : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c = 1) :
    rayConversionPhase c = 1 := by
  rw [rayConversionPhase_eq_of_mod_four c 1 (by simpa only [map_one] using h),
    rayConversionPhase_one]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (P : ι → Ideal O) [∀ i, (P i).IsMaximal]

/-- The third sextic Gauss sum for the analytic character is the actual quadratic trace sum. -/
theorem analytic_sextic_third_eq_quadratic (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) :
    sexticResidueGauss P hinj hgood 3 (analyticCompositeAddChar P hgood) =
      quadraticTraceGauss (∏ i, primaryGenerator (P i) (hgood i))
        (Finset.prod_ne_zero_iff.mpr (fun i _ => primaryGenerator_ne_zero (P i) (hgood i))) := by
  classical
  let p := ∏ i, primaryGenerator (P i) (hgood i)
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => primaryGenerator_ne_zero (P i) (hgood i))
  let e := primeCRT P hinj
  letI : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (∀ i, O ⧸ P i) e.symm.toEquiv
  letI : Finite (O ⧸ Ideal.span {p}) :=
    (Ideal.span {p}).finiteQuotientOfFreeOfNeBot
      (fun h => hp (Ideal.span_singleton_eq_bot.mp h))
  letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  change (∑ x : O ⧸ ∏ i, P i,
    (∏ i, (complexSexticChar (P i) (hgood i) ^ 3) (e x i)) *
      analyticCompositeAddChar P hgood x) = _
  have hpowers (i : ι) : complexSexticChar (P i) (hgood i) ^ 3 =
      complexQuadraticChar (P i) := (complexSexticChar_powers (P i) (hgood i)).2.1
  simp_rw [hpowers]
  rw [show (∑ x : O ⧸ ∏ i, P i,
      (∏ i, complexQuadraticChar (P i) (e x i)) * analyticCompositeAddChar P hgood x) =
      ∑ x : O ⧸ ∏ i, P i, analyticCompositeAddChar P hgood (x ^ 2) from
    ProductGauss.quadratic_factorization_equiv (fun i => O ⧸ P i) e
      (analyticCompositeAddChar P hgood) (analyticCompositeAddChar_primitive P hgood) hchar]
  change _ = ∑ y : O ⧸ Ideal.span {p}, principalTraceChar p hp (y ^ 2)
  let eqv := Ideal.quotEquivOfEq (primeProduct_eq_span_primaryProduct P hgood)
  apply Fintype.sum_equiv eqv.toEquiv
  intro x
  change principalTraceChar p hp (eqv (x ^ 2)) =
    principalTraceChar p hp ((eqv x) ^ 2)
  rw [map_pow]

omit [DecidableEq ι] in
/-- The product of residue-field orders is the squared complex modulus of the primary product. -/
theorem primaryProduct_norm_sq (hgood : ∀ i, lambda ∉ P i) :
    (∏ i, (Fintype.card (O ⧸ P i) : ℂ)) =
      (‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ : ℂ) ^ 2 := by
  have hr : (∏ i, (Fintype.card (O ⧸ P i) : ℝ)) =
      ‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ ^ 2 := by
    rw [map_prod, norm_prod, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [norm_primaryGenerator, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact_mod_cast hr

/-- The analytic conversion splits into a fixed finite ray factor and the argument of the modulus. -/
theorem analyticConversionFactor_eq_rayPhase (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) :
    compositeConversionFactor P hinj hgood (analyticCompositeAddChar P hgood) =
      rayConversionPhase (∏ i, primaryGenerator (P i) (hgood i)) *
        ((‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ : ℂ) /
          ringComplex (∏ i, primaryGenerator (P i) (hgood i))) := by
  let p := ∏ i, primaryGenerator (P i) (hgood i)
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => primaryGenerator_ne_zero (P i) (hgood i))
  have hpC : ringComplex p ≠ 0 :=
    fun h => hp (ringComplex_injective (by simpa using h))
  have hn : (‖ringComplex p‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hpC
  have hG : quadraticTraceGauss p hp =
      (‖ringComplex p‖ : ℂ) * fixedDualAverage p := by
    have h := normalizedQuadraticTraceGauss_eq_fixedDualAverage p hp
    exact ((div_eq_iff hn).mp h).trans (mul_comm _ _)
  rw [compositeConversionFactor_eq_rayFactor P hinj hgood hchar,
    analytic_sextic_third_eq_quadratic P hinj hgood hchar,
    hG, primaryProduct_norm_sq P hgood]
  change cubicRayPhase p * (‖ringComplex p‖ : ℂ) ^ 2 /
      (ringComplex p * ((‖ringComplex p‖ : ℂ) * fixedDualAverage p)) =
      (cubicRayPhase p / fixedDualAverage p) * ((‖ringComplex p‖ : ℂ) / ringComplex p)
  by_cases hA : fixedDualAverage p = 0
  · simp only [hA, mul_zero, div_zero, zero_mul]
  · field_simp [hn, hpC, hA]

/-- The finite ray factor has unit modulus on squarefree primary products away from six. -/
theorem rayConversionPhase_norm_primaryProduct (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) :
    ‖rayConversionPhase (∏ i, primaryGenerator (P i) (hgood i))‖ = 1 := by
  let p := ∏ i, primaryGenerator (P i) (hgood i)
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => primaryGenerator_ne_zero (P i) (hgood i))
  have hn : ‖ringComplex p‖ ≠ 0 := norm_ne_zero_iff.mpr
    (fun h => hp (ringComplex_injective (by simpa using h)))
  have h := norm_compositeConversionFactor P hinj hgood hchar _
    (analyticCompositeAddChar_primitive P hgood)
  rw [analyticConversionFactor_eq_rayPhase P hinj hgood hchar] at h
  change ‖rayConversionPhase p * ((‖ringComplex p‖ : ℂ) / ringComplex p)‖ = 1 at h
  simpa only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self hn, mul_one] using h

/-- On the principal class modulo four, only the explicit angular factor remains. -/
theorem analyticConversionFactor_principal_ray (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (hfour : Ideal.Quotient.mk (Ideal.span {(4 : O)})
      (∏ i, primaryGenerator (P i) (hgood i)) = 1) :
    compositeConversionFactor P hinj hgood (analyticCompositeAddChar P hgood) =
      (‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ : ℂ) /
        ringComplex (∏ i, primaryGenerator (P i) (hgood i)) := by
  rw [analyticConversionFactor_eq_rayPhase P hinj hgood hchar,
    rayConversionPhase_eq_one _ hfour, one_mul]

/-- The actual analytic Möbius conversion has a unit phase fixed on each class modulo four. -/
theorem analytic_moebius_conversion_fixed_ray (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) :
    (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) *
        star (sexticResidueGauss P hinj hgood 1 (analyticCompositeAddChar P hgood)) =
      (rayConversionPhase (∏ i, primaryGenerator (P i) (hgood i)) *
        ((‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ : ℂ) /
          ringComplex (∏ i, primaryGenerator (P i) (hgood i)))) *
        sexticResidueGauss P hinj hgood 2 (analyticCompositeAddChar P hgood) := by
  rw [moebius_star_sexticGauss_eq_cubic P hinj hgood hchar _
    (analyticCompositeAddChar_primitive P hgood),
    analyticConversionFactor_eq_rayPhase P hinj hgood hchar]

/-- The analytic Möbius-to-cubic conversion has a completely determined phase on a fixed ray class. -/
theorem analytic_moebius_conversion_principal_ray (hinj : Function.Injective P)
    (hgood : ∀ i, lambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (hfour : Ideal.Quotient.mk (Ideal.span {(4 : O)})
      (∏ i, primaryGenerator (P i) (hgood i)) = 1) :
    (UniqueFactorizationMonoid.moebius (∏ i, P i) : ℂ) *
        star (sexticResidueGauss P hinj hgood 1 (analyticCompositeAddChar P hgood)) =
      ((‖ringComplex (∏ i, primaryGenerator (P i) (hgood i))‖ : ℂ) /
        ringComplex (∏ i, primaryGenerator (P i) (hgood i))) *
        sexticResidueGauss P hinj hgood 2 (analyticCompositeAddChar P hgood) := by
  rw [moebius_star_sexticGauss_eq_cubic P hinj hgood hchar _
    (analyticCompositeAddChar_primitive P hgood),
    analyticConversionFactor_principal_ray P hinj hgood hchar hfour]

end Eisenstein
end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.analytic_sextic_third_eq_quadratic
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.rayConversionPhase_eq_of_mod_four
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.analyticConversionFactor_eq_rayPhase
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.rayConversionPhase_norm_primaryProduct
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.analytic_moebius_conversion_fixed_ray
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.analytic_moebius_conversion_principal_ray
