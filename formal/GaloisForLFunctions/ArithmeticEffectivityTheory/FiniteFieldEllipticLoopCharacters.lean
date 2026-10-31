import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLoopCarrier
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticIdeleCharacters
import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveLoopFieldMap

/-!
# Spectral sections on the actual elliptic adelic loop group

The two intrinsic Borel coordinates are actual ideles. Their spectral
character is trivial on the integral–Borel intersection, so evaluating it
on Iwasawa factors gives a well-defined nonzero section on the restricted
adelic central loop group.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein Filter
open scoped WithZero WithZeroMulInt
noncomputable section

private def borelUnitCoordinate {F : Type*} [Field F] (i : Bool) :
    LoopSL2.positiveBorel F →* Fˣ where
  toFun b := if i then (LoopSL2.borelTorusHom F b).2 else (LoopSL2.borelTorusHom F b).1
  map_one' := by cases i <;> simp only [Bool.false_eq_true, if_false, if_true, map_one,
    Prod.fst_one, Prod.snd_one]
  map_mul' a b := by cases i <;> simp only [Bool.false_eq_true, if_false, if_true, map_mul,
    Prod.fst_mul, Prod.snd_mul]

private theorem borelUnitCoordinate_fieldMap {F E : Type*} [Field F] [Field E]
    (ι : F →+* E) (i : Bool) (b : LoopSL2.positiveBorel F) :
    borelUnitCoordinate i (LoopSL2.borelFieldMap ι b) =
      Units.map ι.toMonoidHom (borelUnitCoordinate i b) := by
  cases i
  · exact congrArg Prod.fst (LoopSL2.borelTorusHom_fieldMap ι b)
  · exact congrArg Prod.snd (LoopSL2.borelTorusHom_fieldMap ι b)

/-- Assemble local units and their inverses into a unit of the actual adele ring. -/
def ideleOfLocalUnits (x : ∀ v : FinitePlace, (v.adicCompletion K)ˣ) (y : InfinityCompletionˣ)
    (hx : ∀ᶠ v : FinitePlace in cofinite,
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (x v : v.adicCompletion K) = 1) : Ideles where
  val := (⟨fun v => (x v : v.adicCompletion K), hx.mono fun _ hv => hv.le⟩, y)
  inv := (⟨fun v => ((x v)⁻¹ : (v.adicCompletion K)ˣ), by
    filter_upwards [hx] with v hv
    change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (((x v)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]⟩, (y⁻¹ : InfinityCompletionˣ))
  val_inv := by
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      exact (x v).val_inv
    · exact y.val_inv
  inv_val := by
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      exact (x v).inv_val
    · exact y.inv_val

private theorem borelUnitCoordinate_eventually (i : Bool) (b : adelicPositiveBorel) :
    ∀ᶠ v : FinitePlace in cofinite,
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
        ((borelUnitCoordinate i (finiteBorelEvaluation v b) : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) = 1 := by
  cases i
  · exact (adelicBorel_torus_eventually_integral b).mono fun _ hv => hv.1
  · exact (adelicBorel_torus_eventually_integral b).mono fun _ hv => hv.2

/-- Either intrinsic Borel torus coordinate, as a genuine idele-valued homomorphism. -/
def adelicBorelCoordinate (i : Bool) : adelicPositiveBorel →* Ideles where
  toFun b := ideleOfLocalUnits (fun v => borelUnitCoordinate i (finiteBorelEvaluation v b))
    (borelUnitCoordinate i (infinityBorelEvaluation b)) (borelUnitCoordinate_eventually i b)
  map_one' := by
    apply Units.ext
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      change ((borelUnitCoordinate i (finiteBorelEvaluation v 1) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1
      rw [map_one, map_one, Units.val_one]
    · change ((borelUnitCoordinate i (infinityBorelEvaluation 1) : InfinityCompletionˣ) :
        InfinityCompletion) = 1
      rw [map_one, map_one, Units.val_one]
  map_mul' a b := by
    apply Units.ext
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      change ((borelUnitCoordinate i (finiteBorelEvaluation v (a * b)) :
          (v.adicCompletion K)ˣ) : v.adicCompletion K) = _
      rw [map_mul, map_mul, Units.val_mul]
      rfl
    · change ((borelUnitCoordinate i (infinityBorelEvaluation (a * b)) :
          InfinityCompletionˣ) : InfinityCompletion) = _
      rw [map_mul, map_mul, Units.val_mul]
      rfl

/-- The two intrinsic adelic Borel coordinates. -/
def adelicBorelTorus : adelicPositiveBorel →* (Ideles × Ideles) where
  toFun b := (adelicBorelCoordinate false b, adelicBorelCoordinate true b)
  map_one' := Prod.ext (map_one _) (map_one _)
  map_mul' a b := Prod.ext (map_mul _ a b) (map_mul _ a b)

private theorem adelicBorelCoordinate_magnitude_integral (i : Bool) (b : adelicPositiveBorel)
    (hb : (b : AdelicLoop) ∈ adelicIntegralLoop) : ideleMagnitude (adelicBorelCoordinate i b) = 1 := by
  have hv (v : FinitePlace) :
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
        ((borelUnitCoordinate i (finiteBorelEvaluation v b) : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) = 1 := by
    have h := LoopSL2.borelValuationHom_integralLoop
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (finiteBorelEvaluation v b) (hb.1 v)
    cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hi : (Valued.v : Valuation InfinityCompletion ℤᵐ⁰)
      ((borelUnitCoordinate i (infinityBorelEvaluation b) : InfinityCompletionˣ) : InfinityCompletion) = 1 := by
    have h := LoopSL2.borelValuationHom_integralLoop
      (Valued.v : Valuation InfinityCompletion ℤᵐ⁰) (infinityBorelEvaluation b) hb.2
    cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hm (v : FinitePlace) :
      finiteCompletionMagnitude v (((adelicBorelCoordinate i b : Ideles) : Adeles).1 v) = 1 := by
    change finiteCompletionMagnitude v
      ((borelUnitCoordinate i (finiteBorelEvaluation v b) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = 1
    simp only [finiteCompletionMagnitude, MonoidWithZeroHom.comp_apply, hv, map_one]
  have hmi : infinityCompletionMagnitude (((adelicBorelCoordinate i b : Ideles) : Adeles).2) = 1 := by
    change infinityCompletionMagnitude
      ((borelUnitCoordinate i (infinityBorelEvaluation b) : InfinityCompletionˣ) : InfinityCompletion) = 1
    simp only [infinityCompletionMagnitude, MonoidWithZeroHom.comp_apply, hi, map_one]
  change infinityCompletionMagnitude (((adelicBorelCoordinate i b : Ideles) : Adeles).2) *
    (∏ᶠ v : FinitePlace,
      finiteCompletionMagnitude v (((adelicBorelCoordinate i b : Ideles) : Adeles).1 v)) = 1
  simp only [hmi, hm, finprod_one, one_mul]

/-- The spectral character on the actual restricted adelic positive Borel. -/
def adelicBorelCharacter (s t : ℂ) : adelicPositiveBorel →* ℂ :=
  (ideleTorusCharacter s t).comp adelicBorelTorus

theorem adelicBorelCharacter_ne_zero (s t : ℂ) (b : adelicPositiveBorel) :
    adelicBorelCharacter s t b ≠ 0 :=
  isUnit_iff_ne_zero.mp ((Group.isUnit b).map (adelicBorelCharacter s t))

/-- The spectral character is trivial on the actual integral–Borel intersection. -/
theorem adelicBorelCharacter_integral (s t : ℂ) (b : adelicPositiveBorel)
    (hb : (b : AdelicLoop) ∈ adelicIntegralLoop) : adelicBorelCharacter s t b = 1 := by
  change ideleCharacter s (adelicBorelCoordinate false b) *
    ideleCharacter t (adelicBorelCoordinate true b) = 1
  simp only [ideleCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    adelicBorelCoordinate_magnitude_integral _ b hb, NNReal.coe_one, Real.log_one,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]

/-- The actual arithmetic Borel has trivial spectral character by the curve product formula. -/
theorem adelicBorelCharacter_arithmetic (s t : ℂ) (b : adelicPositiveBorel)
    (hb : (b : AdelicLoop) ∈ arithmeticLoopGroup) : adelicBorelCharacter s t b = 1 := by
  obtain ⟨r, hr⟩ := hb
  have hrInf : LoopSL2.fieldMap infinityEmbedding (r : LoopSL2 K) ∈
      LoopSL2.positiveBorel InfinityCompletion := by
    have he := congrArg Prod.snd hr
    change LoopSL2.fieldMap infinityEmbedding (r : LoopSL2 K) = (b : AdelicLoop).2 at he
    rw [he]
    exact b.property.2
  let br : LoopSL2.positiveBorel K := ⟨r,
    (LoopSL2.fieldMap_mem_positiveBorel_iff infinityEmbedding (r : LoopSL2 K)).mp hrInf⟩
  have hfinite (v : FinitePlace) : finiteBorelEvaluation v b =
      LoopSL2.borelFieldMap (algebraMap K (v.adicCompletion K)) br := by
    apply Subtype.ext
    exact (congrArg (fun g : AdelicLoop => g.1 v) hr).symm
  have hinfinity : infinityBorelEvaluation b = LoopSL2.borelFieldMap infinityEmbedding br := by
    apply Subtype.ext
    exact (congrArg Prod.snd hr).symm
  have hcoord (i : Bool) : adelicBorelCoordinate i b = diagonalIdeles (borelUnitCoordinate i br) := by
    apply Units.ext
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      change ((borelUnitCoordinate i (finiteBorelEvaluation v b) : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) = algebraMap K (v.adicCompletion K) ((borelUnitCoordinate i br : Kˣ) : K)
      rw [hfinite, borelUnitCoordinate_fieldMap]
      rfl
    · change ((borelUnitCoordinate i (infinityBorelEvaluation b) : InfinityCompletionˣ) :
        InfinityCompletion) = infinityEmbedding ((borelUnitCoordinate i br : Kˣ) : K)
      rw [hinfinity, borelUnitCoordinate_fieldMap]
      rfl
  change ideleCharacter s (adelicBorelCoordinate false b) *
    ideleCharacter t (adelicBorelCoordinate true b) = 1
  rw [hcoord false, hcoord true, ideleCharacter_diagonal, ideleCharacter_diagonal, one_mul]

/-- Spectral values do not depend on the chosen actual Iwasawa factors. -/
theorem adelicBorelCharacter_iwasawa_unique (s t : ℂ)
    (k₁ k₂ : adelicIntegralLoop) (b₁ b₂ : adelicPositiveBorel)
    (he : (k₁ : AdelicLoop) * b₁ = (k₂ : AdelicLoop) * b₂) :
    adelicBorelCharacter s t b₁ = adelicBorelCharacter s t b₂ := by
  have hd : ((b₁ * b₂⁻¹ : adelicPositiveBorel) : AdelicLoop) = (k₁ : AdelicLoop)⁻¹ * k₂ := by
    change (b₁ : AdelicLoop) * (b₂ : AdelicLoop)⁻¹ = _
    calc
      _ = (k₁ : AdelicLoop)⁻¹ * ((k₁ : AdelicLoop) * b₁) * (b₂ : AdelicLoop)⁻¹ := by group
      _ = (k₁ : AdelicLoop)⁻¹ * ((k₂ : AdelicLoop) * b₂) * (b₂ : AdelicLoop)⁻¹ := by rw [he]
      _ = _ := by group
  have hk : ((b₁ * b₂⁻¹ : adelicPositiveBorel) : AdelicLoop) ∈ adelicIntegralLoop := by
    rw [hd]
    exact adelicIntegralLoop.mul_mem (adelicIntegralLoop.inv_mem k₁.property) k₂.property
  have hv := adelicBorelCharacter_integral s t (b₁ * b₂⁻¹) hk
  calc
    adelicBorelCharacter s t b₁ = adelicBorelCharacter s t ((b₁ * b₂⁻¹) * b₂) := by congr 1; group
    _ = adelicBorelCharacter s t (b₁ * b₂⁻¹) * adelicBorelCharacter s t b₂ := map_mul _ _ _
    _ = adelicBorelCharacter s t b₂ := by rw [hv, one_mul]

private def adelicIwasawaFactors (g : AdelicLoop) : adelicIntegralLoop × adelicPositiveBorel :=
  (Classical.choose (exists_adelic_integral_borel g),
    Classical.choose (Classical.choose_spec (exists_adelic_integral_borel g)))

private theorem adelicIwasawaFactors_spec (g : AdelicLoop) :
    ((adelicIwasawaFactors g).1 : AdelicLoop) * (adelicIwasawaFactors g).2 = g :=
  Classical.choose_spec (Classical.choose_spec (exists_adelic_integral_borel g))

/-- The spectral section defined independently from actual adelic Iwasawa factors. -/
def adelicIwasawaSection (s t : ℂ) (g : AdelicLoop) : ℂ :=
  adelicBorelCharacter s t (adelicIwasawaFactors g).2

theorem adelicIwasawaSection_evaluate (s t : ℂ) (k : adelicIntegralLoop) (b : adelicPositiveBorel) :
    adelicIwasawaSection s t ((k : AdelicLoop) * b) = adelicBorelCharacter s t b :=
  adelicBorelCharacter_iwasawa_unique s t _ k _ b (adelicIwasawaFactors_spec _)

theorem adelicIwasawaSection_ne_zero (s t : ℂ) (g : AdelicLoop) :
    adelicIwasawaSection s t g ≠ 0 := adelicBorelCharacter_ne_zero s t _

/-- Left integral multiplication preserves the actual spectral section. -/
theorem adelicIwasawaSection_left_integral (s t : ℂ) (k : adelicIntegralLoop) (g : AdelicLoop) :
    adelicIwasawaSection s t ((k : AdelicLoop) * g) = adelicIwasawaSection s t g := by
  obtain ⟨l, b, rfl⟩ := exists_adelic_integral_borel g
  rw [← mul_assoc]
  change adelicIwasawaSection s t (((k * l : adelicIntegralLoop) : AdelicLoop) * b) = _
  rw [adelicIwasawaSection_evaluate, adelicIwasawaSection_evaluate]

/-- Right Borel multiplication transforms the section by its intrinsic spectral character. -/
theorem adelicIwasawaSection_right_borel (s t : ℂ) (g : AdelicLoop) (b : adelicPositiveBorel) :
    adelicIwasawaSection s t (g * b) = adelicIwasawaSection s t g * adelicBorelCharacter s t b := by
  obtain ⟨k, a, rfl⟩ := exists_adelic_integral_borel g
  rw [mul_assoc]
  change adelicIwasawaSection s t ((k : AdelicLoop) * (a * b : adelicPositiveBorel)) = _
  rw [adelicIwasawaSection_evaluate, adelicIwasawaSection_evaluate, map_mul]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicBorelCharacter_integral
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicIwasawaSection_left_integral
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicIwasawaSection_right_borel

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicBorelCharacter_arithmetic
