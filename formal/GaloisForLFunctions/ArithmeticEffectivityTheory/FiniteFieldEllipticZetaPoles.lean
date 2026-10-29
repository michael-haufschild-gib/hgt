import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticZeta
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticDifferentials
import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact poles of the arithmetic zeta quotient

The point-count zeta function of the genus-one curve over `𝔽₃` has two numerator
zeros counted with multiplicity. All survive in the reciprocal and in `Z(T)/Z(T/3)`.
Weil's root circle proves noncancellation and gives the complete finite pole locus.
The additive coordinate `T=3⁻ˢ` preserves orders and places the arithmetic poles on
`Re s=-1/2`. Explicit pole parameters use the actual Frobenius roots.
-/

open Polynomial Filter Topology

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

/-- Divide the actual zeta series by its one-step rescaling. -/
def shiftedZetaQuotientSeries : PowerSeries ℂ :=
  zeta * (PowerSeries.rescale (1 / 3 : ℂ) zeta)⁻¹

private lemma rescaled_zeta_constantCoeff :
    PowerSeries.constantCoeff (PowerSeries.rescale (1 / 3 : ℂ) zeta) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
    pow_zero, one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, zeta_constantCoeff]

theorem shiftedZetaQuotientSeries_constantCoeff :
    PowerSeries.constantCoeff shiftedZetaQuotientSeries = 1 := by
  rw [shiftedZetaQuotientSeries, map_mul, PowerSeries.constantCoeff_inv,
    rescaled_zeta_constantCoeff, zeta_constantCoeff, inv_one, one_mul]

/-- Multiplication recovers the original curve's zeta series, coefficient by coefficient. -/
theorem shiftedZetaQuotientSeries_mul :
    shiftedZetaQuotientSeries * PowerSeries.rescale (1 / 3 : ℂ) zeta = zeta := by
  rw [shiftedZetaQuotientSeries, mul_assoc,
    PowerSeries.inv_mul_cancel _ (by rw [rescaled_zeta_constantCoeff]; exact one_ne_zero),
    mul_one]

/-- Rationality of the quotient series follows from the actual point-count rationality identity. -/
theorem shiftedZetaQuotientSeries_rational :
    (((1 - PowerSeries.X) * (1 - PowerSeries.C 3 * PowerSeries.X)) *
        PowerSeries.rescale (1 / 3 : ℂ) (numerator : PowerSeries ℂ)) *
      shiftedZetaQuotientSeries =
    PowerSeries.rescale (1 / 3 : ℂ)
        ((1 - PowerSeries.X) * (1 - PowerSeries.C 3 * PowerSeries.X)) *
      (numerator : PowerSeries ℂ) := by
  have hs := congrArg (PowerSeries.rescale (1 / 3 : ℂ)) zeta_rational
  rw [map_mul] at hs
  rw [← hs]
  calc
    _ = PowerSeries.rescale (1 / 3 : ℂ)
          ((1 - PowerSeries.X) * (1 - PowerSeries.C 3 * PowerSeries.X)) *
        (((1 - PowerSeries.X) * (1 - PowerSeries.C 3 * PowerSeries.X)) *
          (shiftedZetaQuotientSeries * PowerSeries.rescale (1 / 3 : ℂ) zeta)) := by ring
    _ = _ := by rw [shiftedZetaQuotientSeries_mul, zeta_rational]

private lemma numerator_analytic (z : ℂ) :
    AnalyticAt ℂ (fun T => numerator.eval T) z := by
  simpa using (analyticAt_id : AnalyticAt ℂ (fun T : ℂ => T) z).aeval_polynomial numerator

private lemma denominator_analytic (z : ℂ) :
    AnalyticAt ℂ (fun T : ℂ => (1 - T) * (1 - 3 * T)) z := by fun_prop

lemma zetaFunction_meromorphic (z : ℂ) : MeromorphicAt zetaFunction z :=
  (numerator_analytic z).meromorphicAt.div (denominator_analytic z).meromorphicAt

lemma zetaFunction_analytic (z : ℂ) (hz : (1 - z) * (1 - 3 * z) ≠ 0) :
    AnalyticAt ℂ zetaFunction z :=
  (numerator_analytic z).div (denominator_analytic z) hz

lemma numerator_meromorphicOrder (z : ℂ) :
    meromorphicOrderAt (fun T => numerator.eval T) z =
      ((numerator.rootMultiplicity z : ℤ) : WithTop ℤ) := by
  rw [(numerator_analytic z).meromorphicOrderAt_eq,
    HTGeometry.analyticOrderAt_eval_eq_rootMultiplicity numerator_ne_zero]
  rfl

private lemma analytic_unit_order {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hne : f z ≠ 0) : meromorphicOrderAt f z = 0 := by
  rw [hf.meromorphicOrderAt_eq, hf.analyticOrderAt_eq_zero.mpr hne]
  rfl

private lemma zetaFunction_order_eq (z : ℂ) :
    meromorphicOrderAt zetaFunction z =
      meromorphicOrderAt (fun T => numerator.eval T) z -
        meromorphicOrderAt (fun T : ℂ => (1 - T) * (1 - 3 * T)) z := by
  convert! meromorphicOrderAt_div (numerator_analytic z).meromorphicAt
    (denominator_analytic z).meromorphicAt using 1

/-- Every arithmetic zeta zero has its original polynomial multiplicity. -/
theorem zetaFunction_order_at_root (z : ℂ) (hz : numerator.eval z = 0) :
    meromorphicOrderAt zetaFunction z =
      ((numerator.rootMultiplicity z : ℤ) : WithTop ℤ) := by
  rw [zetaFunction_order_eq,
    numerator_meromorphicOrder,
    analytic_unit_order (denominator_analytic z) (reciprocal_numerator_nonzero z hz),
    sub_zero]

/-- The reciprocal of the actual point-count zeta function. -/
def reciprocalZeta (T : ℂ) : ℂ := (zetaFunction T)⁻¹

/-- Zeta zeros become poles of the reciprocal, with exactly the same multiplicity. -/
theorem reciprocalZeta_order_at_root (z : ℂ) (hz : numerator.eval z = 0) :
    meromorphicOrderAt reciprocalZeta z =
      -((numerator.rootMultiplicity z : ℤ) : WithTop ℤ) := by
  change meromorphicOrderAt zetaFunction⁻¹ z = _
  rw [meromorphicOrderAt_inv, zetaFunction_order_at_root z hz]

private lemma root_multiplicity_pos (z : ℂ) (hz : numerator.eval z = 0) :
    0 < numerator.rootMultiplicity z :=
  (Polynomial.rootMultiplicity_pos numerator_ne_zero).mpr hz

theorem reciprocalZeta_pole_at_root (z : ℂ) (hz : numerator.eval z = 0) :
    meromorphicOrderAt reciprocalZeta z < 0 := by
  rw [reciprocalZeta_order_at_root z hz]
  have hm := root_multiplicity_pos z hz
  change ((-(numerator.rootMultiplicity z : ℤ) : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
  exact_mod_cast (neg_neg_of_pos (by exact_mod_cast hm : (0 : ℤ) < numerator.rootMultiplicity z))

/-- The reciprocal has no finite poles beyond the actual zeta zeros. -/
theorem reciprocalZeta_pole_iff (z : ℂ) :
    meromorphicOrderAt reciprocalZeta z < 0 ↔ numerator.eval z = 0 := by
  constructor
  · intro hpole
    by_contra hp
    have ha : AnalyticAt ℂ reciprocalZeta z := by
      have he : reciprocalZeta = fun T => (1 - T) * (1 - 3 * T) / numerator.eval T := by
        funext T
        simp only [reciprocalZeta, zetaFunction, inv_div]
      rw [he]
      exact (denominator_analytic z).div (numerator_analytic z) hp
    exact not_le_of_gt hpole ha.meromorphicOrderAt_nonneg
  · exact reciprocalZeta_pole_at_root z

/-- The one-step zeta quotient in multiplicative coordinate `T=3⁻ˢ`. -/
def shiftedZetaQuotient (T : ℂ) : ℂ := zetaFunction T / zetaFunction (T / 3)

private lemma divide_three_analytic (z : ℂ) :
    AnalyticAt ℂ (fun T : ℂ => T / 3) z := by fun_prop

private lemma divide_three_deriv (z : ℂ) :
    deriv (fun T : ℂ => T / 3) z = 1 / 3 :=
  ((hasDerivAt_id z).div_const 3).deriv

lemma zetaFunction_divide_three_order (z : ℂ) :
    meromorphicOrderAt (fun T => zetaFunction (T / 3)) z =
      meromorphicOrderAt zetaFunction (z / 3) := by
  exact meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := zetaFunction) (g := fun T : ℂ => T / 3) (divide_three_analytic z)
    (by rw [divide_three_deriv]; norm_num)

lemma shiftedZetaQuotient_meromorphic (z : ℂ) :
    MeromorphicAt shiftedZetaQuotient z := by
  exact (zetaFunction_meromorphic z).div
    ((zetaFunction_meromorphic (z / 3)).comp_analyticAt (g := fun T : ℂ => T / 3) (divide_three_analytic z))

lemma shiftedZetaQuotient_order (z : ℂ) :
    meromorphicOrderAt shiftedZetaQuotient z =
      meromorphicOrderAt zetaFunction z - meromorphicOrderAt zetaFunction (z / 3) := by
  calc
    _ = meromorphicOrderAt zetaFunction z -
        meromorphicOrderAt (fun T => zetaFunction (T / 3)) z := by
      convert! meromorphicOrderAt_div (zetaFunction_meromorphic z)
        ((zetaFunction_meromorphic (z / 3)).comp_analyticAt
          (g := fun T : ℂ => T / 3) (divide_three_analytic z)) using 1
    _ = _ := by rw [zetaFunction_divide_three_order]

lemma scaled_root_norm_sq (z : ℂ) (hz : numerator.eval z = 0) :
    ‖(3 : ℂ) * z‖ ^ 2 = (3 : ℝ) := by
  rw [norm_mul, mul_pow, numerator_zero_norm_sq z hz]
  norm_num

lemma numerator_at_scaled_root_ne_zero (z : ℂ) (hz : numerator.eval z = 0) :
    numerator.eval (3 * z) ≠ 0 := by
  intro h
  have h₁ := scaled_root_norm_sq z hz
  have h₂ := numerator_zero_norm_sq (3 * z) h
  linarith only [h₁, h₂]

lemma denominator_at_scaled_root_ne_zero (z : ℂ) (hz : numerator.eval z = 0) :
    (1 - 3 * z) * (1 - 3 * (3 * z)) ≠ 0 := by
  have hn := scaled_root_norm_sq z hz
  apply mul_ne_zero
  · intro h
    have he : 3 * z = 1 := (sub_eq_zero.mp h).symm
    rw [he] at hn
    norm_num at hn
  · intro h
    have he : 3 * z = 1 / 3 := by linear_combination -(1 / 3 : ℂ) * h
    rw [he] at hn
    norm_num [norm_div] at hn

/-- Weil's circle makes the numerator zeta function a unit at every shifted zero. -/
lemma zetaFunction_order_at_scaled_root (z : ℂ) (hz : numerator.eval z = 0) :
    meromorphicOrderAt zetaFunction (3 * z) = 0 := by
  apply analytic_unit_order
    (zetaFunction_analytic _ (denominator_at_scaled_root_ne_zero z hz))
  exact div_ne_zero (numerator_at_scaled_root_ne_zero z hz)
    (denominator_at_scaled_root_ne_zero z hz)

/-- All zeta zeros survive as poles of `Z(T)/Z(T/3)`, with exact multiplicity. -/
theorem shiftedZetaQuotient_order_at_root (z : ℂ) (hz : numerator.eval z = 0) :
    meromorphicOrderAt shiftedZetaQuotient (3 * z) =
      -((numerator.rootMultiplicity z : ℤ) : WithTop ℤ) := by
  rw [shiftedZetaQuotient_order, zetaFunction_order_at_scaled_root z hz]
  have he : (3 : ℂ) * z / 3 = z := by ring
  rw [he, zetaFunction_order_at_root z hz, zero_sub]

theorem shiftedZetaQuotient_pole_at_root (z : ℂ) (hz : numerator.eval z = 0) :
    meromorphicOrderAt shiftedZetaQuotient (3 * z) < 0 := by
  rw [shiftedZetaQuotient_order_at_root z hz]
  have hm := root_multiplicity_pos z hz
  change ((-(numerator.rootMultiplicity z : ℤ) : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
  exact_mod_cast (neg_neg_of_pos (by exact_mod_cast hm : (0 : ℤ) < numerator.rootMultiplicity z))

private lemma denominator_deriv (z : ℂ) :
    HasDerivAt (fun T : ℂ => (1 - T) * (1 - 3 * T)) (6 * z - 4) z := by
  have h₁ : HasDerivAt (fun T : ℂ => 1 - T) (-1) z := by
    convert! (hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z) using 1
    simp
  have h₂ : HasDerivAt (fun T : ℂ => 1 - 3 * T) (-3) z := by
    convert! (hasDerivAt_const z (1 : ℂ)).sub
      (HasDerivAt.const_mul 3 (hasDerivAt_id z)) using 1
    simp
  convert! h₁.mul h₂ using 1
  ring

private lemma denominator_order_one :
    meromorphicOrderAt (fun T : ℂ => (1 - T) * (1 - 3 * T)) 1 = 1 := by
  have ha := denominator_analytic 1
  rw [ha.meromorphicOrderAt_eq,
    ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by norm_num)
      (by rw [(denominator_deriv 1).deriv]; norm_num)]
  rfl

private lemma denominator_order_third :
    meromorphicOrderAt (fun T : ℂ => (1 - T) * (1 - 3 * T)) (1 / 3) = 1 := by
  have ha := denominator_analytic (1 / 3)
  rw [ha.meromorphicOrderAt_eq,
    ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by norm_num)
      (by rw [(denominator_deriv (1 / 3)).deriv]; norm_num)]
  rfl

theorem zetaFunction_order_one : meromorphicOrderAt zetaFunction 1 = -1 := by
  rw [zetaFunction_order_eq,
    analytic_unit_order (numerator_analytic 1) numerator_at_one_ne_zero,
    denominator_order_one, zero_sub]

theorem zetaFunction_order_third : meromorphicOrderAt zetaFunction (1 / 3) = -1 := by
  rw [zetaFunction_order_eq,
    analytic_unit_order (numerator_analytic (1 / 3)) numerator_at_third_ne_zero,
    denominator_order_third, zero_sub]

private lemma denominator_ne_zero (z : ℂ) (h₁ : z ≠ 1) (h₃ : z ≠ 1 / 3) :
    (1 - z) * (1 - 3 * z) ≠ 0 := by
  apply mul_ne_zero
  · exact sub_ne_zero.mpr h₁.symm
  · intro h
    apply h₃
    linear_combination -(1 / 3 : ℂ) * h

lemma zetaFunction_order_of_unit (z : ℂ) (hp : numerator.eval z ≠ 0)
    (h₁ : z ≠ 1) (h₃ : z ≠ 1 / 3) : meromorphicOrderAt zetaFunction z = 0 :=
  analytic_unit_order (zetaFunction_analytic z (denominator_ne_zero z h₁ h₃))
    (div_ne_zero hp (denominator_ne_zero z h₁ h₃))

private lemma numerator_at_ninth_ne_zero : numerator.eval (1 / 9) ≠ 0 := by
  intro h
  have hn := numerator_zero_norm_sq (1 / 9) h
  norm_num [norm_div] at hn

theorem shiftedZetaQuotient_order_third :
    meromorphicOrderAt shiftedZetaQuotient (1 / 3) = -1 := by
  rw [shiftedZetaQuotient_order, zetaFunction_order_third]
  rw [show (1 / 3 : ℂ) / 3 = 1 / 9 by norm_num]
  rw [zetaFunction_order_of_unit (1 / 9) numerator_at_ninth_ne_zero (by norm_num)
    (by norm_num), sub_zero]

/-- The common pole at `T=1` cancels in the shifted quotient as a meromorphic germ. -/
theorem shiftedZetaQuotient_order_one :
    meromorphicOrderAt shiftedZetaQuotient 1 = 0 := by
  rw [shiftedZetaQuotient_order, zetaFunction_order_one, zetaFunction_order_third]
  norm_num

/-- Exact pole locus: one simple rational pole and all shifted arithmetic zeros. -/
theorem shiftedZetaQuotient_pole_iff (z : ℂ) :
    meromorphicOrderAt shiftedZetaQuotient z < 0 ↔
      z = 1 / 3 ∨ numerator.eval (z / 3) = 0 := by
  constructor
  · intro hpole
    by_cases hz : z = 1 / 3
    · exact Or.inl hz
    by_cases hp : numerator.eval (z / 3) = 0
    · exact Or.inr hp
    exfalso
    apply not_le_of_gt hpole
    by_cases h₁ : z = 1
    · subst z
      rw [shiftedZetaQuotient_order_one]
    by_cases h₃ : z = 3
    · subst z
      rw [shiftedZetaQuotient_order]
      rw [show (3 : ℂ) / 3 = 1 by norm_num]
      rw [zetaFunction_order_one]
      have hn := (zetaFunction_analytic 3 (by norm_num)).meromorphicOrderAt_nonneg
      simpa only [sub_neg_eq_add] using add_nonneg hn (by norm_num : (0 : WithTop ℤ) ≤ 1)
    rw [shiftedZetaQuotient_order,
      zetaFunction_order_of_unit (z / 3) hp
        (by intro h; apply h₃; linear_combination 3 * h)
        (by intro h; apply h₁; linear_combination 3 * h), sub_zero]
    exact (zetaFunction_analytic z (denominator_ne_zero z h₁ hz)).meromorphicOrderAt_nonneg
  · rintro (rfl | hz)
    · rw [shiftedZetaQuotient_order_third]
      change ((-1 : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
      exact_mod_cast (by norm_num : (-1 : ℤ) < 0)
    · have h := shiftedZetaQuotient_pole_at_root (z / 3) hz
      have he : (3 : ℂ) * (z / 3) = z := by ring
      rwa [he] at h

/-- The arithmetic pole multiset transports the actual numerator roots by `T↦3T`. -/
def arithmeticPoleMultiset : Multiset ℂ := numerator.roots.map (fun z => 3 * z)

theorem arithmeticPoleMultiset_card : arithmeticPoleMultiset.card = 2 * geometricGenus := by
  rw [arithmeticPoleMultiset, Multiset.card_map, numerator_root_count, geometricGenus_eq_one]


theorem mem_arithmeticPoleMultiset_iff (z : ℂ) :
    z ∈ arithmeticPoleMultiset ↔ numerator.eval (z / 3) = 0 := by
  simp only [arithmeticPoleMultiset, Multiset.mem_map, Polynomial.mem_roots numerator_ne_zero,
    Polynomial.IsRoot.def]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have he : (3 : ℂ) * r / 3 = r := by ring
    rwa [he]
  · intro hz
    exact ⟨z / 3, hz, by ring⟩

theorem arithmeticPoleMultiset_poles (z : ℂ) (hz : z ∈ arithmeticPoleMultiset) :
    meromorphicOrderAt shiftedZetaQuotient z < 0 :=
  (shiftedZetaQuotient_pole_iff z).mpr (Or.inr ((mem_arithmeticPoleMultiset_iff z).mp hz))

/-- Multiset multiplicities equal the pole orders, not merely a list of candidate locations. -/
theorem arithmeticPoleMultiset_order (z : ℂ) (hz : z ∈ arithmeticPoleMultiset) :
    meromorphicOrderAt shiftedZetaQuotient z =
      -((arithmeticPoleMultiset.count z : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
  rw [shiftedZetaQuotient_order_at_root r ((Polynomial.mem_roots numerator_ne_zero).mp hr),
    arithmeticPoleMultiset, Multiset.count_map_eq_count'
      (fun r : ℂ => 3 * r) numerator.roots
      (fun a b h => mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) h),
    Polynomial.count_roots]

/-- The multiplicative coordinate for the zeta function over `𝔽₃`. -/
def zetaCoordinate (s : ℂ) : ℂ := Complex.exp (-(Real.log 3 : ℂ) * s)

lemma log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

lemma log_three_ne_zero : (Real.log 3 : ℂ) ≠ 0 := by
  exact_mod_cast log_three_pos.ne'

lemma zetaCoordinate_ne_zero (s : ℂ) : zetaCoordinate s ≠ 0 := Complex.exp_ne_zero _

lemma zetaCoordinate_analytic (s : ℂ) : AnalyticAt ℂ zetaCoordinate s := by
  unfold zetaCoordinate
  fun_prop

lemma zetaCoordinate_deriv (s : ℂ) :
    deriv zetaCoordinate s = zetaCoordinate s * -(Real.log 3 : ℂ) := by
  convert! ((HasDerivAt.const_mul (-(Real.log 3 : ℂ)) (hasDerivAt_id s)).cexp).deriv using 1
  simp only [zetaCoordinate, mul_one, id_eq]

lemma zetaCoordinate_deriv_ne_zero (s : ℂ) : deriv zetaCoordinate s ≠ 0 := by
  rw [zetaCoordinate_deriv]
  exact mul_ne_zero (zetaCoordinate_ne_zero s) (neg_ne_zero.mpr log_three_ne_zero)

lemma zetaCoordinate_add_one (s : ℂ) : zetaCoordinate (s + 1) = zetaCoordinate s / 3 := by
  have he : Complex.exp (-(Real.log 3 : ℂ)) = (1 / 3 : ℂ) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  simp only [zetaCoordinate, mul_add, mul_one, Complex.exp_add, he, div_eq_mul_inv, one_mul]

lemma zetaCoordinate_norm_sq (s : ℂ) :
    ‖zetaCoordinate s‖ ^ 2 = Real.exp (-2 * Real.log 3 * s.re) := by
  rw [zetaCoordinate, Complex.norm_exp, pow_two, ← Real.exp_add]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  ring

lemma zetaCoordinate_re_of_norm_sq (s : ℂ) (hs : ‖zetaCoordinate s‖ ^ 2 = 3) :
    s.re = -(1 / 2 : ℝ) := by
  rw [zetaCoordinate_norm_sq] at hs
  have he : Real.exp (-2 * Real.log 3 * s.re) = Real.exp (Real.log 3) := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    exact hs
  have hl := Real.exp_injective he
  have hh : Real.log 3 * (2 * s.re + 1) = 0 := by nlinarith only [hl]
  have hx := (mul_eq_zero.mp hh).resolve_left log_three_pos.ne'
  linarith only [hx]

/-- An explicit additive coordinate over any nonzero multiplicative parameter. -/
def zetaParameter (T : ℂ) : ℂ := -Complex.log T / (Real.log 3 : ℂ)

lemma zetaCoordinate_parameter (T : ℂ) (hT : T ≠ 0) :
    zetaCoordinate (zetaParameter T) = T := by
  unfold zetaCoordinate zetaParameter
  have he : -(Real.log 3 : ℂ) * (-Complex.log T / (Real.log 3 : ℂ)) = Complex.log T := by
    calc
      _ = (Real.log 3 : ℂ) * Complex.log T / (Real.log 3 : ℂ) := by ring
      _ = _ := mul_div_cancel_left₀ _ log_three_ne_zero
  rw [he, Complex.exp_log hT]

/-- The arithmetic zeta function in its additive parameter. -/
def arithmeticZeta (s : ℂ) : ℂ := zetaFunction (zetaCoordinate s)

/-- The literal zeta ratio occurring in rank-one intertwining coefficients. -/
def arithmeticZetaRatio (s : ℂ) : ℂ := arithmeticZeta s / arithmeticZeta (s + 1)

theorem arithmeticZetaRatio_eq (s : ℂ) :
    arithmeticZetaRatio s = shiftedZetaQuotient (zetaCoordinate s) := by
  simp only [arithmeticZetaRatio, arithmeticZeta, zetaCoordinate_add_one, shiftedZetaQuotient]

theorem arithmeticZetaRatio_meromorphic (s : ℂ) : MeromorphicAt arithmeticZetaRatio s := by
  have he : arithmeticZetaRatio = shiftedZetaQuotient ∘ zetaCoordinate :=
    funext arithmeticZetaRatio_eq
  rw [he]
  exact (shiftedZetaQuotient_meromorphic (zetaCoordinate s)).comp_analyticAt
    (g := zetaCoordinate) (zetaCoordinate_analytic s)

theorem arithmeticZetaRatio_order (s : ℂ) :
    meromorphicOrderAt arithmeticZetaRatio s =
      meromorphicOrderAt shiftedZetaQuotient (zetaCoordinate s) := by
  have he : arithmeticZetaRatio = shiftedZetaQuotient ∘ zetaCoordinate :=
    funext arithmeticZetaRatio_eq
  rw [he]
  exact meromorphicOrderAt_comp_of_deriv_ne_zero
    (zetaCoordinate_analytic s) (zetaCoordinate_deriv_ne_zero s)

/-- A denominator zeta zero gives an actual pole with its full multiplicity. -/
theorem arithmeticZetaRatio_order_at_zero (s : ℂ)
    (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) :
    meromorphicOrderAt arithmeticZetaRatio s =
      -((numerator.rootMultiplicity (zetaCoordinate (s + 1)) : ℤ) : WithTop ℤ) := by
  rw [arithmeticZetaRatio_order]
  have he : zetaCoordinate s = 3 * zetaCoordinate (s + 1) := by
    rw [zetaCoordinate_add_one]
    ring
  rw [he, shiftedZetaQuotient_order_at_root _ hs]

theorem arithmeticZetaRatio_pole_iff (s : ℂ) :
    meromorphicOrderAt arithmeticZetaRatio s < 0 ↔
      zetaCoordinate s = 1 / 3 ∨ numerator.eval (zetaCoordinate (s + 1)) = 0 := by
  rw [arithmeticZetaRatio_order, shiftedZetaQuotient_pole_iff, zetaCoordinate_add_one]

/-- Arithmetic denominator zeros lie on the shifted Weil line. -/
theorem arithmeticZetaRatio_zero_re (s : ℂ)
    (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) : s.re = -(1 / 2 : ℝ) := by
  apply zetaCoordinate_re_of_norm_sq
  have he : zetaCoordinate s = 3 * zetaCoordinate (s + 1) := by
    rw [zetaCoordinate_add_one]
    ring
  rw [he]
  exact scaled_root_norm_sq _ hs

/-- Explicit additive pole parameters, indexed by the actual Frobenius roots. -/
def arithmeticPoleParameter (i : FrobeniusIndex) : ℂ :=
  zetaParameter (3 * (datum.alpha i)⁻¹)

theorem arithmeticPoleParameter_zero (i : FrobeniusIndex) :
    numerator.eval (zetaCoordinate (arithmeticPoleParameter i + 1)) = 0 := by
  rw [zetaCoordinate_add_one, arithmeticPoleParameter,
    zetaCoordinate_parameter _ (mul_ne_zero (by norm_num) (inv_ne_zero (alpha_ne_zero i)))]
  have he : (3 : ℂ) * (datum.alpha i)⁻¹ / 3 = (datum.alpha i)⁻¹ := by ring
  rw [he, numerator_eval_eq_zero_iff]
  exact ⟨i, rfl⟩

/-- Both arithmetic root copies supply genuine poles on `Re s = -1/2`. -/
theorem arithmeticPoleParameter_spec (i : FrobeniusIndex) :
    (arithmeticPoleParameter i).re = -(1 / 2 : ℝ) ∧
      meromorphicOrderAt arithmeticZetaRatio (arithmeticPoleParameter i) < 0 :=
  ⟨arithmeticZetaRatio_zero_re _ (arithmeticPoleParameter_zero i),
    (arithmeticZetaRatio_pole_iff _).mpr (Or.inr (arithmeticPoleParameter_zero i))⟩

/-- An unconditional zero-to-pole certificate for the actual genus-one arithmetic source. -/
theorem finiteFieldZetaPoleTransfer_spec :
    geometricGenus = 1 ∧
      PowerSeries.constantCoeff shiftedZetaQuotientSeries = 1 ∧
      arithmeticPoleMultiset.card = 2 * geometricGenus ∧
      (∀ z ∈ arithmeticPoleMultiset,
        meromorphicOrderAt shiftedZetaQuotient z =
            -((arithmeticPoleMultiset.count z : ℤ) : WithTop ℤ) ∧
          meromorphicOrderAt shiftedZetaQuotient z < 0) ∧
      (∀ i : FrobeniusIndex,
        (arithmeticPoleParameter i).re = -(1 / 2 : ℝ) ∧
          meromorphicOrderAt arithmeticZetaRatio (arithmeticPoleParameter i) < 0) :=
  ⟨geometricGenus_eq_one, shiftedZetaQuotientSeries_constantCoeff, arithmeticPoleMultiset_card,
    fun z hz => ⟨arithmeticPoleMultiset_order z hz, arithmeticPoleMultiset_poles z hz⟩,
    arithmeticPoleParameter_spec⟩

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
