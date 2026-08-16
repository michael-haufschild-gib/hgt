import GaloisForLFunctions.HTGeometry.FormalLeadingCoefficientSpecialization

/-!
# The coefficientwise derivation on formal power series

A derivation of a coefficient ring extends coefficientwise to formal power series, with the formal
parameter as a differential constant.  Constant-term extraction then commutes with the extended
derivation, so every jet of a series has the corresponding jet of its constant coefficient as its
own constant coefficient.

This is the differential structure in which a germ in a differential-constant parameter is compared
with its leading coefficient.

## Main results

* `coeffwiseAdd` — the coefficientwise derivative, as an additive map;
* `coeffwiseAdd_mul` — it satisfies the Leibniz rule, so it is a derivation;
* `coeffwiseAdd_X` — the formal parameter is a differential constant;
* `constantCoeff_coeffwiseAdd` — constant-term extraction commutes with it;
* `constantCoeff_coeffwiseJet` — hence with every jet.
-/

noncomputable section

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace PowerSeriesDeriv

variable {K : Type*} [CommRing K] [Differential K]

/-- The coefficientwise derivative of a formal power series, as an additive map. -/
def coeffwiseAdd : PowerSeries K →+ PowerSeries K where
  toFun f := PowerSeries.mk fun n => (Differential.deriv (PowerSeries.coeff n f) : K)
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

@[simp]
theorem coeff_coeffwiseAdd (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (coeffwiseAdd f) = (PowerSeries.coeff n f)′ := by
  simp [coeffwiseAdd]

/-- **The Leibniz rule.**  The coefficientwise derivative is a derivation of the power-series
ring. -/
theorem coeffwiseAdd_mul (f g : PowerSeries K) :
    coeffwiseAdd (f * g) = f * coeffwiseAdd g + g * coeffwiseAdd f := by
  ext n
  rw [coeff_coeffwiseAdd, PowerSeries.coeff_mul, map_sum, map_add,
    PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  have hswap : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 (coeffwiseAdd f))
      = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        PowerSeries.coeff p.2 g * PowerSeries.coeff p.1 (coeffwiseAdd f) :=
    Finset.Nat.sum_antidiagonal_swap
      (f := fun p => PowerSeries.coeff p.2 g * PowerSeries.coeff p.1 (coeffwiseAdd f))
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Derivation.leibniz, coeff_coeffwiseAdd, coeff_coeffwiseAdd]
  simp only [smul_eq_mul]

/-- **The formal parameter is a differential constant.** -/
@[simp]
theorem coeffwiseAdd_X : coeffwiseAdd (PowerSeries.X : PowerSeries K) = 0 := by
  ext n
  rw [coeff_coeffwiseAdd, PowerSeries.coeff_X]
  rcases eq_or_ne n 1 with rfl | hn
  · simp
  · rw [if_neg hn]
    simp

@[simp]
theorem coeffwiseAdd_one : coeffwiseAdd (1 : PowerSeries K) = 0 := by
  ext n
  rw [coeff_coeffwiseAdd, PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg (by omega)]
    simp

/-- **Constant-term extraction commutes with the coefficientwise derivative.** -/
@[simp]
theorem constantCoeff_coeffwiseAdd (f : PowerSeries K) :
    PowerSeries.constantCoeff (coeffwiseAdd f) = (PowerSeries.constantCoeff f)′ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coeffwiseAdd,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The `n`-th coefficientwise jet of a formal power series. -/
def coeffwiseJet (n : ℕ) (f : PowerSeries K) : PowerSeries K :=
  (coeffwiseAdd)^[n] f

@[simp]
theorem coeffwiseJet_zero (f : PowerSeries K) : coeffwiseJet 0 f = f := rfl

theorem coeffwiseJet_succ (n : ℕ) (f : PowerSeries K) :
    coeffwiseJet (n + 1) f = coeffwiseAdd (coeffwiseJet n f) :=
  Function.iterate_succ_apply' _ n f

/-- **Constant-term extraction commutes with every jet.** -/
theorem constantCoeff_coeffwiseJet (f : PowerSeries K) (n : ℕ) :
    PowerSeries.constantCoeff (coeffwiseJet n f)
      = GaloisForLFunctions.differentialJet n (PowerSeries.constantCoeff f) := by
  induction n with
  | zero => rw [coeffwiseJet_zero, GaloisForLFunctions.differentialJet_zero]
  | succ k ih =>
      rw [coeffwiseJet_succ, GaloisForLFunctions.differentialJet_succ,
        constantCoeff_coeffwiseAdd, ih]

end PowerSeriesDeriv

end GaloisForLFunctions.HTGeometry
