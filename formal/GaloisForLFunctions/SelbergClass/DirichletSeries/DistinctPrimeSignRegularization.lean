import GaloisForLFunctions.SelbergClass.DirichletSeries.DistinctPrimeSignCorrection
import GaloisForLFunctions.BezoutValuationIncidence.SingularSeries.TwinPrimeConstant

/-!
# The distinct-prime correction and the twin-prime constant

At one, the normally convergent odd-prime correction is exactly half the
gap-two Hardy–Littlewood singular series.
-/

noncomputable section
namespace GaloisForLFunctions.SelbergClass

/-- The analytic local correction specializes to the prime-pair factor. -/
theorem oddPrimeCorrectionFactor_one (p : Nat.Primes) :
    oddPrimeCorrectionFactor p 1 =
      (BezoutValuationIncidence.twinPrimeFactor p : ℂ) := by
  unfold oddPrimeCorrectionFactor BezoutValuationIncidence.twinPrimeFactor
  split_ifs with hp
  · simp only [Complex.ofReal_one]
  · rw [distinctPrimeDecay_one]
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
    have hp1 : (p : ℂ) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast p.prop.ne_one)
    push_cast
    field_simp

/-- The holomorphic correction takes the positive twin-prime value at one. -/
theorem oddPrimeCorrection_one :
    oddPrimeCorrection 1 = (BezoutValuationIncidence.twinPrimeConstant : ℂ) := by
  have h : HasProd BezoutValuationIncidence.twinPrimeFactor
      BezoutValuationIncidence.twinPrimeConstant := by
    rw [BezoutValuationIncidence.twinPrimeConstant_eq_singularSeries]
    exact BezoutValuationIncidence.hasProd_twinPrimeFactor
  exact ((h.map Complex.ofRealHom Complex.continuous_ofReal).congr_fun
    oddPrimeCorrectionFactor_one).tprod_eq

#print axioms oddPrimeCorrection_one
end GaloisForLFunctions.SelbergClass
