import GaloisForLFunctions.RHTower.FZZCigarOneSidedRadialRealCompactWardNoGo

/-! # Reflection law for physical one-sided FZZ radial response -/

open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

private theorem deriv_digamma_conj_pair (z : ℂ) :
    deriv Complex.digamma (conj z) = conj (deriv Complex.digamma z) := by
  have hfun : (conj ∘ Complex.digamma ∘ conj) = Complex.digamma := by
    funext w
    simp [Function.comp_def, ReflectedDigammaAnomaly.digamma_conj]
  have hderiv := deriv_conj_conj (f := Complex.digamma)
  rw [hfun] at hderiv
  have h := congrFun hderiv (conj z)
  simpa [Function.comp_def] using h

/-- Momentum reflection negates conjugate of physical one-sided mixed receiver. -/
theorem fzzMarkedRadialReplicaResponse_momentum_deriv_neg_eq_neg_conj
    (radialCoupling radialScale momentum : ℝ) :
    deriv (fzzMarkedRadialReplicaResponse
      radialCoupling radialScale) (-momentum) =
      -conj (deriv (fzzMarkedRadialReplicaResponse
        radialCoupling radialScale) momentum) := by
  have harg :
      1 + (((-momentum) / Real.exp radialScale : ℝ) : ℂ) * I =
        conj (1 + ((momentum / Real.exp radialScale : ℝ) : ℂ) * I) := by
    simp only [neg_div, Complex.ofReal_neg, map_add, map_one, map_mul,
      Complex.conj_ofReal, Complex.conj_I, neg_mul, mul_neg]
  rw [(hasDerivAt_fzzMarkedRadialReplicaResponse_momentum
      radialCoupling radialScale (-momentum)).deriv,
    (hasDerivAt_fzzMarkedRadialReplicaResponse_momentum
      radialCoupling radialScale momentum).deriv,
    harg, deriv_digamma_conj_pair]
  let a : ℂ :=
    ((fzzMarkedRadialReplicaRate radialScale / Real.exp radialScale : ℝ) : ℂ)
  let T : ℂ := deriv Complex.digamma
    (1 + ((momentum / Real.exp radialScale : ℝ) : ℂ) * I)
  change -a * I * conj T = -conj (-a * I * T)
  have ha : conj a = a := by
    dsimp only [a]
    exact Complex.conj_ofReal _
  rw [map_mul, map_mul, map_neg, ha, Complex.conj_I]
  ring

/-- Momentum reflection reverses real part and preserves imaginary orientation. -/
theorem fzzMarkedRadialReplicaResponse_momentum_deriv_neg_re
    (radialCoupling radialScale momentum : ℝ) :
    (deriv (fzzMarkedRadialReplicaResponse
      radialCoupling radialScale) (-momentum)).re =
      -(deriv (fzzMarkedRadialReplicaResponse
        radialCoupling radialScale) momentum).re := by
  have h := congrArg Complex.re
    (fzzMarkedRadialReplicaResponse_momentum_deriv_neg_eq_neg_conj
      radialCoupling radialScale momentum)
  simpa using h

end

end GaloisForLFunctions.RHTower
