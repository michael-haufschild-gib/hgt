import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe

/-!
# The prescribed cubic-spline Weil coefficient

At `ρ = 1/2 + z`, the cubic-spline Fourier transform is `(sinh z / z)^4`.
Its diagonal Weil summand is therefore the integer zero multiplicity times
`(sinh z / z)^8`. This fixes the coefficient convention for spline cone moments.
-/

open Complex
open scoped ComplexConjugate
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open RHTower.WeilDeletion
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma paperFT_cubicSpline_div_I {z : ℂ} (hz : z ≠ 0) :
    Zeta23.paperFT (fun x => (cubicSpline x : ℂ)) (z/Complex.I)=
      (Complex.sinh z/z)^4 := by
  rw [cubicSpline, paperFT_upow, paperFT_unif (by norm_num : (0 : ℝ) < 1)
    (div_ne_zero hz Complex.I_ne_zero)]
  have hIz : Complex.I*(z/Complex.I)=z := by field_simp
  simp only [Nat.reduceAdd, Complex.ofReal_one, mul_one, hIz]
  congr 1
  rw [Complex.sinh]
  field_simp

/-- The cubic-spline diagonal Weil coefficient is the exact eighth-power factor. -/
theorem cubicSpline_Wsummand {z : ℂ} (hz : z ≠ 0) :
    Zeta23.zetaZeroConfig.Wsummand (fun x => (cubicSpline x : ℂ))
      (fun x => (cubicSpline x : ℂ)) (1/2+z)=
      (Zeta23.zetaZeroConfig.mult (1/2+z) : ℂ)*(Complex.sinh z/z)^8 := by
  have hγ : Zeta23.gammaOf (1/2+z)=z/Complex.I := by
    rw [Zeta23.gammaOf]
    congr 1
    ring
  have hc : conj (z/Complex.I)=(-conj z)/Complex.I := by
    simp only [map_div₀, Complex.conj_I]
    ring
  have hzc : -conj z ≠ 0 := by
    apply neg_ne_zero.mpr
    intro h
    apply hz
    simpa only [Complex.conj_conj, map_zero] using congrArg (starRingEnd ℂ) h
  rw [Zeta23.ZeroConfig.Wsummand, hγ, paperFT_cubicSpline_div_I hz, hc,
    paperFT_cubicSpline_div_I hzc]
  simp only [Complex.sinh_neg, neg_div_neg_eq, Complex.sinh_conj, map_pow, map_div₀,
    Complex.conj_conj]
  ring

#print axioms cubicSpline_Wsummand
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
