import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Data.Finsupp.Basic

/-!
# Finite support of principal valuation divisors

The nonzero valuation logs of a function lie among its poles and the
poles of its inverse. Both sets are finite in a Dedekind fraction field.
This gives an actual finitely supported divisor for every nonzero
function; zero is assigned the zero divisor.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain
variable (B K : Type*) [CommRing B] [IsDedekindDomain B]
    [Field K] [Algebra B K] [IsFractionRing B K]

/-- A function has nonzero normalized valuation log at only finitely many finite places. -/
theorem finite_valuation_log_support (f : K) :
    (Function.support (fun v : HeightOneSpectrum B => WithZero.log (v.valuation K f))).Finite := by
  by_cases hf : f = 0
  · subst f
    simp only [map_zero, WithZero.log_zero]
    change (Function.support (0 : HeightOneSpectrum B → ℤ)).Finite
    rw [Function.support_zero]
    exact Set.finite_empty
  · apply ((HeightOneSpectrum.Support.finite B f).union
      (HeightOneSpectrum.Support.finite B f⁻¹)).subset
    intro v hv
    change WithZero.log (v.valuation K f) ≠ 0 at hv
    have hv1 : v.valuation K f ≠ 1 := by
      intro h
      exact hv (by rw [h, WithZero.log_one])
    rcases lt_or_gt_of_ne hv1 with hlt | hgt
    · right
      change 1 < v.valuation K f⁻¹
      rw [map_inv₀]
      exact (one_lt_inv₀ (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hf))).mpr hlt
    · exact Or.inl hgt

/-- The normalized finite-place valuation logs, regarded as an actual finite divisor. -/
def finiteValuationDivisor (f : K) : HeightOneSpectrum B →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => WithZero.log (v.valuation K f))
    (finite_valuation_log_support B K f)

/-- Each coefficient of the principal valuation divisor is its literal valuation log. -/
theorem finiteValuationDivisor_apply (f : K) (v : HeightOneSpectrum B) :
    finiteValuationDivisor B K f v = WithZero.log (v.valuation K f) := rfl

/-- Multiplication of nonzero functions adds their finite principal valuation divisors. -/
theorem finiteValuationDivisor_mul (f g : K) (hf : f ≠ 0) (hg : g ≠ 0) :
    finiteValuationDivisor B K (f * g) = finiteValuationDivisor B K f + finiteValuationDivisor B K g := by
  ext v
  change WithZero.log (v.valuation K (f * g)) =
    WithZero.log (v.valuation K f) + WithZero.log (v.valuation K g)
  rw [map_mul, WithZero.log_mul ((map_ne_zero _).mpr hf) ((map_ne_zero _).mpr hg)]

/-- Taking the inverse negates the finite principal valuation divisor. -/
theorem finiteValuationDivisor_inv (f : K) :
    finiteValuationDivisor B K f⁻¹ = -finiteValuationDivisor B K f := by
  ext v
  change WithZero.log (v.valuation K f⁻¹) = -WithZero.log (v.valuation K f)
  rw [map_inv₀, WithZero.log_inv]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
