import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactSourceScalars

/-!
# Scalar reflected modular jets through order ten

Each finite Leibniz sum is normalized before taking determinants. Separate
ring identities keep the proof terms bounded and retain exact source incidence.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Evaluation of the finite reflection sum without unfolding source-jet recurrences. -/
theorem eval_oddCompactReflectedJetPolynomial
    (v : ModularThetaLyapunovState → ℂ) (n : ℕ) :
    MvPolynomial.eval v (oddCompactReflectedJetPolynomial n) =
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℂ)*(-1 : ℂ)^(n-i) *
        MvPolynomial.eval v (modularThetaLyapunovNormalizedSourceJet i) *
        MvPolynomial.eval v (modularThetaLyapunovNormalizedSourceJet (n-i)) := by
  unfold oddCompactReflectedJetPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, map_mul, MvPolynomial.eval_C]

/-- Determinant evaluation with the five reflected observables kept abstract. -/
theorem eval_oddCompactDetPolynomial (v : ModularThetaLyapunovState → ℂ) :
    MvPolynomial.eval v oddCompactDetPolynomial =
      let a := -MvPolynomial.eval v (oddCompactReflectedJetPolynomial 2)
      let b := MvPolynomial.eval v (oddCompactReflectedJetPolynomial 4)
      let c := -MvPolynomial.eval v (oddCompactReflectedJetPolynomial 6)
      let d := MvPolynomial.eval v (oddCompactReflectedJetPolynomial 8)
      let e := -MvPolynomial.eval v (oddCompactReflectedJetPolynomial 10)
      a*c*e-a*d^(2 : ℕ)-b^(2 : ℕ)*e+2*b*c*d-c^(3 : ℕ) := by
  have hmap (p q r s t : ModularThetaLyapunovPolynomial) :
      MvPolynomial.eval v ((-p)*(-r)*(-t)-(-p)*s^(2 : ℕ)-q^(2 : ℕ)*(-t)+
        MvPolynomial.C 2*q*(-r)*s-(-r)^(3 : ℕ)) =
      (-MvPolynomial.eval v p)*(-MvPolynomial.eval v r)*(-MvPolynomial.eval v t)-
      (-MvPolynomial.eval v p)*(MvPolynomial.eval v s)^(2 : ℕ)-
      (MvPolynomial.eval v q)^(2 : ℕ)*(-MvPolynomial.eval v t)+
      2*MvPolynomial.eval v q*(-MvPolynomial.eval v r)*MvPolynomial.eval v s-
      (-MvPolynomial.eval v r)^(3 : ℕ) := by
    simp only [map_sub, map_add, map_mul, map_pow, map_neg, MvPolynomial.eval_C]
  exact hmap _ _ _ _ _

/-- Leading-minor evaluation with its reflected observables kept abstract. -/
theorem eval_oddCompactHeadPolynomial (v : ModularThetaLyapunovState → ℂ) :
    MvPolynomial.eval v oddCompactHeadPolynomial =
      (-MvPolynomial.eval v (oddCompactReflectedJetPolynomial 2)) *
        (-MvPolynomial.eval v (oddCompactReflectedJetPolynomial 6)) -
          MvPolynomial.eval v (oddCompactReflectedJetPolynomial 4)^(2 : ℕ) := by
  have hmap (p q r : ModularThetaLyapunovPolynomial) :
      MvPolynomial.eval v ((-p)*(-r)-q^(2 : ℕ)) =
        (-MvPolynomial.eval v p)*(-MvPolynomial.eval v r)-(MvPolynomial.eval v q)^(2 : ℕ) := by
    simp only [map_sub, map_mul, map_pow, map_neg]
  exact hmap _ _ _


end
end HTGeometry
