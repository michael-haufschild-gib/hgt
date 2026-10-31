import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticSimpleRoots
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLoopCharacters
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticGlobalSpectralIntegral


/-!
# Actual elliptic simple-root intertwining integrals

The logarithm of an idele magnitude is the finite sum of local valuation
logarithms. The two simple-root Iwasawa pairs therefore read the actual
adelic radial height, including the affine central shift. Their independently
defined spectral sections inherit the exact global zeta-ratio integral.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open Function Filter MeasureTheory HTGeometry.LoopEisenstein HTGeometry.DiscreteValuationHaar
open scoped NNReal WithZero WithZeroMulInt
noncomputable section

private theorem log_ideleMagnitude_eq_finsum (a : Ideles) :
    Real.log (ideleMagnitude a : ℝ) =
      (∑ᶠ v : FinitePlace, Real.log (finiteCompletionMagnitude v ((a : Adeles).1 v) : ℝ)) +
        Real.log (infinityCompletionMagnitude (a : Adeles).2 : ℝ) := by
  classical
  let f : FinitePlace → ℝ≥0 := fun v => finiteCompletionMagnitude v ((a : Adeles).1 v)
  have hunit : IsUnit (a : Adeles).1 := a.isUnit.map (RingHom.fst FiniteAdeles InfinityCompletion)
  have hv := (IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp hunit).2
  have hf : HasFiniteMulSupport f := by
    apply Filter.eventually_cofinite.mp
    filter_upwards [hv] with v hv
    change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).toMonoidWithZeroHom
      ((a : Adeles).1 v) = 1 at hv
    simp only [f, finiteCompletionMagnitude, MonoidWithZeroHom.comp_apply, hv, map_one]
  have hfi (v : FinitePlace) : f v ≠ 0 := by
    have he : ((a : Adeles).1 v) * (((a⁻¹ : Ideles) : Adeles).1 v) = 1 :=
      congrArg (fun z : Adeles => z.1 v) a.val_inv
    have hm : f v * finiteCompletionMagnitude v (((a⁻¹ : Ideles) : Adeles).1 v) = 1 := by
      change finiteCompletionMagnitude v ((a : Adeles).1 v) *
        finiteCompletionMagnitude v (((a⁻¹ : Ideles) : Adeles).1 v) = 1
      rw [← map_mul, he, map_one]
    intro hz
    rw [hz, zero_mul] at hm
    exact zero_ne_one hm
  have hi : infinityCompletionMagnitude (a : Adeles).2 ≠ 0 := by
    have he : (a : Adeles).2 * ((a⁻¹ : Ideles) : Adeles).2 = 1 := congrArg Prod.snd a.val_inv
    have hm : infinityCompletionMagnitude (a : Adeles).2 *
        infinityCompletionMagnitude ((a⁻¹ : Ideles) : Adeles).2 = 1 := by
      rw [← map_mul, he, map_one]
    intro hz
    rw [hz, zero_mul] at hm
    exact zero_ne_one hm
  have hfir (v : FinitePlace) : (f v : ℝ) ≠ 0 := by exact_mod_cast hfi v
  have hir : (infinityCompletionMagnitude (a : Adeles).2 : ℝ) ≠ 0 := by exact_mod_cast hi
  let S : Finset FinitePlace := hf.toFinset
  have hs : mulSupport f ⊆ S := fun v hv => hf.mem_toFinset.mpr hv
  have hlogs : support (fun v => Real.log (f v : ℝ)) ⊆ S := by
    intro v hv
    apply hs
    intro he
    apply hv
    change Real.log (f v : ℝ) = 0
    rw [he, NNReal.coe_one, Real.log_one]
  change Real.log ((infinityCompletionMagnitude (a : Adeles).2 * ∏ᶠ v, f v : ℝ≥0) : ℝ) =
    (∑ᶠ v, Real.log (f v : ℝ)) + _
  rw [finprod_eq_prod_of_mulSupport_subset f hs, finsum_eq_sum_of_support_subset _ hlogs,
    NNReal.coe_mul, NNReal.coe_prod,
    Real.log_mul hir (Finset.prod_ne_zero_iff.mpr (fun v _ => hfir v)),
    Real.log_prod (fun v _ => hfir v)]
  exact add_comm _ _


private def normalizedValueLog (q : ℝ≥0) (hq : q ≠ 0) (m : ℤᵐ⁰) : ℝ :=
  Real.log (WithZeroMulInt.toNNReal hq m : ℝ)

private theorem normalizedValueLog_one (q : ℝ≥0) (hq : q ≠ 0) :
    normalizedValueLog q hq 1 = 0 := by
  simp only [normalizedValueLog, map_one, NNReal.coe_one, Real.log_one]

private theorem normalizedValueLog_inv (q : ℝ≥0) (hq : q ≠ 0) (m : ℤᵐ⁰) :
    normalizedValueLog q hq m⁻¹ = -normalizedValueLog q hq m := by
  simp only [normalizedValueLog, map_inv₀, NNReal.coe_inv, Real.log_inv]

private theorem normalizedValueLog_max (q : ℝ≥0) (hq : q ≠ 0) (h₁ : 1 < q) (m : ℤᵐ⁰) :
    normalizedValueLog q hq (max 1 m) =
      Real.log (max 1 (WithZeroMulInt.toNNReal hq m : ℝ)) := by
  have hm : Monotone (WithZeroMulInt.toNNReal hq) :=
    (WithZeroMulInt.toNNReal_strictMono h₁).monotone
  have he : WithZeroMulInt.toNNReal hq (max 1 m) = max 1 (WithZeroMulInt.toNNReal hq m) := by
    rw [hm.map_max, map_one]
  have hr : (WithZeroMulInt.toNNReal hq (max 1 m) : ℝ) =
      max 1 (WithZeroMulInt.toNNReal hq m : ℝ) := by exact_mod_cast he
  exact congrArg Real.log hr

local instance rootSectionFiniteCompact (v : FinitePlace) :
    CompactSpace (Integer (v.adicCompletion K)) := finiteCompletionInteger_compact v

private theorem finiteResidue_gt_one (v : FinitePlace) :
    (1 : ℝ≥0) < Nat.card (RingOfIntegers ⧸ v.asIdeal) := by
  have hcard : Nat.card (Residue (v.adicCompletion K)) =
      Nat.card (RingOfIntegers ⧸ v.asIdeal) := Nat.card_congr (finiteCompletionResidueEquiv v).toEquiv
  rw [← hcard]
  exact_mod_cast residue_card_gt_one (v.adicCompletion K)

private def finiteLogValue (v : FinitePlace) : ℤᵐ⁰ → ℝ :=
  normalizedValueLog (Nat.card (RingOfIntegers ⧸ v.asIdeal)) (finiteResidue_gt_one v).ne_zero

private def infinityLogValue : ℤᵐ⁰ → ℝ := normalizedValueLog 3 (by norm_num)

private theorem finiteLogValue_one (v : FinitePlace) : finiteLogValue v 1 = 0 :=
  normalizedValueLog_one _ _
private theorem infinityLogValue_one : infinityLogValue 1 = 0 := normalizedValueLog_one _ _

private theorem finiteLogValue_inv (v : FinitePlace) (m : ℤᵐ⁰) :
    finiteLogValue v m⁻¹ = -finiteLogValue v m := normalizedValueLog_inv _ _ _
private theorem infinityLogValue_inv (m : ℤᵐ⁰) :
    infinityLogValue m⁻¹ = -infinityLogValue m := normalizedValueLog_inv _ _ _

private theorem finiteLogValue_max (v : FinitePlace) (x : v.adicCompletion K) :
    finiteLogValue v (max 1 (Valued.v x)) = finiteCompletionLogHeight v x :=
  normalizedValueLog_max _ _ (finiteResidue_gt_one v) _
private theorem infinityLogValue_max (x : InfinityCompletion) :
    infinityLogValue (max 1 (Valued.v x)) = infinityCompletionLogHeight x :=
  normalizedValueLog_max _ _ (by norm_num) _

private theorem log_borelCoordinate (i : Bool) (b : adelicPositiveBorel) :
    Real.log (ideleMagnitude (adelicBorelCoordinate i b) : ℝ) =
      (∑ᶠ v : FinitePlace, finiteLogValue v
        (if i then (LoopSL2.borelValuationHom Valued.v (finiteBorelEvaluation v b)).2
          else (LoopSL2.borelValuationHom Valued.v (finiteBorelEvaluation v b)).1)) +
      infinityLogValue
        (if i then (LoopSL2.borelValuationHom Valued.v (infinityBorelEvaluation b)).2
          else (LoopSL2.borelValuationHom Valued.v (infinityBorelEvaluation b)).1) := by
  rw [log_ideleMagnitude_eq_finsum]
  cases i <;> rfl

private theorem section_eq_of_borelCharacter (s t : ℂ) (g : AdelicLoop) (z : ℂ)
    (h : ∀ k : adelicIntegralLoop, ∀ b : adelicPositiveBorel,
      (k : AdelicLoop) * b = g → adelicBorelCharacter s t b = z) :
    adelicIwasawaSection s t g = z :=
  (exists_adelic_integral_borel g).elim fun k hk =>
    hk.elim fun b he =>
      (congrArg (adelicIwasawaSection s t) he.symm).trans
        ((adelicIwasawaSection_evaluate s t k b).trans (h k b he))

/-- The finite negative root reads the full actual adelic radial height. -/
theorem adelicIwasawaSection_finiteNegativeRoot (s t : ℂ) (a : Adeles) :
    adelicIwasawaSection s t (adelicFiniteNegativeRoot a) =
      Complex.exp (t * (adelicLogHeight a : ℂ)) := by
  refine section_eq_of_borelCharacter s t (adelicFiniteNegativeRoot a) _ ?_
  intro k b he
  have hf := adelicFiniteNegativeRoot_finite_values a k b he
  have hi := adelicFiniteNegativeRoot_infinity_values a k b he
  have hc : Real.log (ideleMagnitude (adelicBorelCoordinate false b) : ℝ) = 0 := by
    rw [log_borelCoordinate]
    simp only [Bool.false_eq_true, if_false, hf, hi, finiteLogValue_one,
      infinityLogValue_one, finsum_zero, zero_add]
  have ht : Real.log (ideleMagnitude (adelicBorelCoordinate true b) : ℝ) = adelicLogHeight a := by
    rw [log_borelCoordinate]
    simp only [if_true, hf, hi, finiteLogValue_max, infinityLogValue_max]
    rfl
  change Complex.exp (s * (Real.log (ideleMagnitude (adelicBorelCoordinate false b) : ℝ) : ℂ)) *
    Complex.exp (t * (Real.log (ideleMagnitude (adelicBorelCoordinate true b) : ℝ) : ℂ)) = _
  rw [hc, ht]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]

/-- The affine negative root has central height and opposite finite height. -/
theorem adelicIwasawaSection_affineNegativeRoot (s t : ℂ) (a : Adeles) :
    adelicIwasawaSection s t (adelicAffineNegativeRoot a) =
      Complex.exp ((s-t) * (adelicLogHeight a : ℂ)) := by
  refine section_eq_of_borelCharacter s t (adelicAffineNegativeRoot a) _ ?_
  intro k b he
  have hf := adelicAffineNegativeRoot_finite_values a k b he
  have hi := adelicAffineNegativeRoot_infinity_values a k b he
  have hc : Real.log (ideleMagnitude (adelicBorelCoordinate false b) : ℝ) = adelicLogHeight a := by
    rw [log_borelCoordinate]
    simp only [Bool.false_eq_true, if_false, hf, hi, finiteLogValue_max, infinityLogValue_max]
    rfl
  have ht : Real.log (ideleMagnitude (adelicBorelCoordinate true b) : ℝ) = -adelicLogHeight a := by
    rw [log_borelCoordinate]
    simp only [if_true, hf, hi, finiteLogValue_inv, infinityLogValue_inv,
      finiteLogValue_max, infinityLogValue_max, finsum_neg_distrib]
    unfold adelicLogHeight
    ring
  change Complex.exp (s * (Real.log (ideleMagnitude (adelicBorelCoordinate false b) : ℝ) : ℂ)) *
    Complex.exp (t * (Real.log (ideleMagnitude (adelicBorelCoordinate true b) : ℝ) : ℂ)) = _
  rw [hc, ht, Complex.ofReal_neg, ← Complex.exp_add]
  congr 1
  ring

/-- Normalizing the finite-root parameter gives the actual adelic spectral kernel. -/
theorem adelicIwasawaSection_finiteNegativeRoot_eq_kernel (s z : ℂ) (a : Adeles) :
    adelicIwasawaSection s (-(z+1)) (adelicFiniteNegativeRoot a) =
      ellipticAdeleSpectralKernel z a :=
  adelicIwasawaSection_finiteNegativeRoot s (-(z+1)) a

/-- The affine normalization gives the same kernel, with its intrinsic central character retained. -/
theorem adelicIwasawaSection_affineNegativeRoot_eq_kernel (t z : ℂ) (a : Adeles) :
    adelicIwasawaSection (t-(z+1)) t (adelicAffineNegativeRoot a) =
      ellipticAdeleSpectralKernel z a := by
  rw [adelicIwasawaSection_affineNegativeRoot]
  have he : t-(z+1)-t = -(z+1) := by ring
  rw [he]
  rfl


/-- The independently defined finite-root section is absolutely integrable in its convergence chamber. -/
theorem adelicIwasawaSection_finiteNegativeRoot_integrable (s z : ℂ) (hz : 1 < z.re) :
    Integrable (fun a => adelicIwasawaSection s (-(z+1)) (adelicFiniteNegativeRoot a)) adeleHaar := by
  simpa only [adelicIwasawaSection_finiteNegativeRoot_eq_kernel] using
    ellipticAdeleSpectralKernel_integrable z hz

/-- The finite simple-root intertwiner is the actual elliptic zeta ratio. -/
theorem integral_adelicIwasawaSection_finiteNegativeRoot (s z : ℂ) (hz : 1 < z.re) :
    (∫ a, adelicIwasawaSection s (-(z+1)) (adelicFiniteNegativeRoot a) ∂adeleHaar) =
      ellipticSpectralZetaRatio z := by
  simp only [adelicIwasawaSection_finiteNegativeRoot_eq_kernel]
  exact integral_ellipticAdeleSpectralKernel z hz

/-- The affine-root section has the same convergence chamber after its central shift. -/
theorem adelicIwasawaSection_affineNegativeRoot_integrable (t z : ℂ) (hz : 1 < z.re) :
    Integrable (fun a => adelicIwasawaSection (t-(z+1)) t (adelicAffineNegativeRoot a)) adeleHaar := by
  simpa only [adelicIwasawaSection_affineNegativeRoot_eq_kernel] using
    ellipticAdeleSpectralKernel_integrable z hz

/-- The affine simple-root intertwiner retains the central parameter and has the exact zeta ratio. -/
theorem integral_adelicIwasawaSection_affineNegativeRoot (t z : ℂ) (hz : 1 < z.re) :
    (∫ a, adelicIwasawaSection (t-(z+1)) t (adelicAffineNegativeRoot a) ∂adeleHaar) =
      ellipticSpectralZetaRatio z := by
  simp only [adelicIwasawaSection_affineNegativeRoot_eq_kernel]
  exact integral_ellipticAdeleSpectralKernel z hz

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.integral_adelicIwasawaSection_finiteNegativeRoot
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.integral_adelicIwasawaSection_affineNegativeRoot
