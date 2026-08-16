import GaloisForLFunctions.HTGeometry.FormalParameterRelationNormalization
import Mathlib.RingTheory.LaurentSeries

/-!
# The coefficientwise derivation on formal Laurent series

The coefficientwise extension of a derivation to formal power series extends further to formal
Laurent series.  The Leibniz rule survives because both product terms can be summed over one and
the same Hahn antidiagonal — the support of a coefficientwise derivative is contained in the
support of the original series.

Every integral power of the formal parameter is a differential constant, so the coefficientwise
jets of a Laurent series are the monomial shift of the coefficientwise jets of its power-series
part.

## Main results

* `laurentCoeffwise` — the coefficientwise derivative of a Laurent series;
* `laurentCoeffwise_mul` — the Leibniz rule;
* `laurentCoeffwise_single_one` — every monomial `E^m` is a differential constant;
* `laurentCoeffwise_coe` — it restricts to the power-series derivation;
* `laurentCoeffwiseJet_eq_single_mul` — the jets of `F` are `E^m` times the jets of the
  power-series part of `F`.
-/

noncomputable section

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace LaurentDeriv

open HahnSeries PowerSeriesDeriv

variable {K : Type*} [CommRing K] [Differential K]

/-- The coefficientwise derivative of a formal Laurent series. -/
def laurentCoeffwise (f : LaurentSeries K) : LaurentSeries K where
  coeff := fun n => (Differential.deriv (f.coeff n) : K)
  isPWO_support' := by
    refine f.isPWO_support.mono ?_
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    simp only [HahnSeries.support, Function.mem_support, ne_eq]
    intro h
    exact hn (by rw [h]; simp)

@[simp]
theorem coeff_laurentCoeffwise (f : LaurentSeries K) (n : ℤ) :
    (laurentCoeffwise f).coeff n = (f.coeff n)′ := rfl

theorem support_laurentCoeffwise_subset (f : LaurentSeries K) :
    (laurentCoeffwise f).support ⊆ f.support := by
  intro n hn
  simp only [HahnSeries.support, Function.mem_support, ne_eq, coeff_laurentCoeffwise] at hn ⊢
  intro h
  exact hn (by rw [h]; simp)

/-- The coefficientwise derivative of a Laurent series, as an additive map. -/
def laurentCoeffwiseAdd : LaurentSeries K →+ LaurentSeries K where
  toFun := laurentCoeffwise
  map_zero' := by
    refine HahnSeries.ext ?_
    funext n
    simp
  map_add' f g := by
    refine HahnSeries.ext ?_
    funext n
    simp

@[simp]
theorem laurentCoeffwiseAdd_apply (f : LaurentSeries K) :
    laurentCoeffwiseAdd f = laurentCoeffwise f := rfl

/-- **The Leibniz rule for the Laurent coefficientwise derivative.** -/
theorem laurentCoeffwise_mul (f g : LaurentSeries K) :
    laurentCoeffwise (f * g) = f * laurentCoeffwise g + laurentCoeffwise f * g := by
  refine HahnSeries.ext ?_
  funext n
  rw [coeff_laurentCoeffwise, HahnSeries.coeff_mul, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_right' g.isPWO_support (support_laurentCoeffwise_subset g),
    HahnSeries.coeff_mul_left' f.isPWO_support (support_laurentCoeffwise_subset f),
    ← Finset.sum_add_distrib, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Derivation.leibniz, coeff_laurentCoeffwise, coeff_laurentCoeffwise]
  simp only [smul_eq_mul]
  ring

/-- **Every monomial in the formal parameter is a differential constant.** -/
@[simp]
theorem laurentCoeffwise_single_one (m : ℤ) :
    laurentCoeffwise (HahnSeries.single m (1 : K)) = 0 := by
  refine HahnSeries.ext ?_
  funext n
  rw [coeff_laurentCoeffwise, HahnSeries.coeff_single]
  rcases eq_or_ne n m with rfl | hn
  · simp
  · rw [if_neg hn]
    simp

/-- **The Laurent derivative restricts to the power-series derivation.** -/
theorem laurentCoeffwise_coe (g : PowerSeries K) :
    laurentCoeffwise ((g : LaurentSeries K)) = ((coeffwiseAdd g : PowerSeries K) : LaurentSeries K) := by
  refine HahnSeries.ext ?_
  funext n
  rw [coeff_laurentCoeffwise, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  rcases lt_or_ge n 0 with hn | hn
  · rw [if_pos hn, if_pos hn]
    simp
  · rw [if_neg (not_lt.mpr hn), if_neg (not_lt.mpr hn), coeff_coeffwiseAdd]

/-- The `n`-th coefficientwise jet of a formal Laurent series. -/
def laurentCoeffwiseJet (n : ℕ) (f : LaurentSeries K) : LaurentSeries K :=
  (laurentCoeffwise)^[n] f

@[simp]
theorem laurentCoeffwiseJet_zero (f : LaurentSeries K) : laurentCoeffwiseJet 0 f = f := rfl

theorem laurentCoeffwiseJet_succ (n : ℕ) (f : LaurentSeries K) :
    laurentCoeffwiseJet (n + 1) f = laurentCoeffwise (laurentCoeffwiseJet n f) :=
  Function.iterate_succ_apply' _ n f

/-- **The jets of a monomial shift are the monomial shift of the jets.** -/
theorem laurentCoeffwiseJet_single_mul (m : ℤ) (g : PowerSeries K) (n : ℕ) :
    laurentCoeffwiseJet n (HahnSeries.single m (1 : K) * (g : LaurentSeries K))
      = HahnSeries.single m (1 : K) * ((coeffwiseJet n g : PowerSeries K) : LaurentSeries K) := by
  induction n with
  | zero => rw [laurentCoeffwiseJet_zero, coeffwiseJet_zero]
  | succ k ih =>
      rw [laurentCoeffwiseJet_succ, ih, laurentCoeffwise_mul, laurentCoeffwise_single_one,
        zero_mul, add_zero, laurentCoeffwise_coe, coeffwiseJet_succ]

/-- **The jets of a Laurent series are the monomial shift of the jets of its power-series
part.** -/
theorem laurentCoeffwiseJet_eq_single_mul (f : LaurentSeries K) (n : ℕ) :
    laurentCoeffwiseJet n f
      = HahnSeries.single f.order (1 : K)
        * ((coeffwiseJet n f.powerSeriesPart : PowerSeries K) : LaurentSeries K) := by
  conv_lhs => rw [← LaurentSeries.single_order_mul_powerSeriesPart f]
  exact laurentCoeffwiseJet_single_mul f.order f.powerSeriesPart n

omit [Differential K] in
/-- The leading coefficient of a Laurent series is the constant coefficient of its power-series
part. -/
theorem constantCoeff_powerSeriesPart (f : LaurentSeries K) :
    PowerSeries.constantCoeff f.powerSeriesPart = f.leadingCoeff := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, LaurentSeries.powerSeriesPart_coeff,
    HahnSeries.leadingCoeff_eq, Nat.cast_zero, add_zero]

end LaurentDeriv

end GaloisForLFunctions.HTGeometry
