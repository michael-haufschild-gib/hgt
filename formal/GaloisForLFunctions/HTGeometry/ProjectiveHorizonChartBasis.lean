import GaloisForLFunctions.HTGeometry.ProjectiveHorizonMinorRatio

/-!
# The chart transcendence basis

The chart change of variables `X_(k,l) ↦ x_k^(l)` is inverted by the polynomial substitution
`X_(k,l) ↦ D^l (X_(k,0) X_(i,0))`, which fixes the denominator tower.  On numerators it reads

`chartBack N_(k,l) = X_(k,l) X_(i,0)^(l+1)`,

so after inverting `X_(i,0)` it sends each affine chart jet back to its homogeneous coordinate while
leaving the tower of the chart denominator alone.

This is the substitution behind the statement that the denominator tower together with the chart
jets is a transcendence basis of the homogeneous jet field.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The inverse chart substitution -/

/-- Generators of the substitution inverting the chart change of variables. -/
def chartBackGen (i : n) : n × ℕ → MvPolynomial (n × ℕ) K := fun p =>
  if p.1 = i then MvPolynomial.X p
  else ((differentialPolynomialDerivation n K :
      MvPolynomial (n × ℕ) K → MvPolynomial (n × ℕ) K)^[p.2])
    (MvPolynomial.X (p.1, 0) * MvPolynomial.X (i, 0))

/-- The substitution inverting the chart change of variables. -/
def chartBack (i : n) : MvPolynomial (n × ℕ) K →ₐ[K] MvPolynomial (n × ℕ) K :=
  MvPolynomial.aeval (chartBackGen i)

omit [Fintype n] in
@[simp]
theorem chartBack_X_self (i : n) (l : ℕ) :
    chartBack (K := K) i (MvPolynomial.X (i, l)) = MvPolynomial.X (i, l) := by
  simp [chartBack, chartBackGen]

omit [Fintype n] in
theorem chartBack_X_of_ne {i k : n} (hk : k ≠ i) (l : ℕ) :
    chartBack (K := K) i (MvPolynomial.X (k, l)) =
      ((differentialPolynomialDerivation n K :
        MvPolynomial (n × ℕ) K → MvPolynomial (n × ℕ) K)^[l])
        (MvPolynomial.X (k, 0) * MvPolynomial.X (i, 0)) := by
  simp [chartBack, chartBackGen, hk]

omit [Fintype n] in
/-- The inverse chart substitution commutes with the jet shift. -/
theorem chartBack_deriv (i : n) (p : MvPolynomial (n × ℕ) K) :
    chartBack i (differentialPolynomialDerivation n K p) =
      differentialPolynomialDerivation n K (chartBack i p) := by
  have hX : ∀ (k : n) (l : ℕ),
      chartBack (K := K) i (differentialPolynomialDerivation n K (MvPolynomial.X (k, l))) =
        differentialPolynomialDerivation n K (chartBack i (MvPolynomial.X (k, l))) := by
    intro k l
    rw [differentialPolynomialDerivation_X]
    rcases eq_or_ne k i with rfl | hk
    · rw [chartBack_X_self, chartBack_X_self, differentialPolynomialDerivation_X]
    · rw [chartBack_X_of_ne hk, chartBack_X_of_ne hk, Function.iterate_succ_apply']
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hCa : differentialPolynomialDerivation n K (MvPolynomial.C a) = 0 := by
        rw [← MvPolynomial.algebraMap_eq]
        exact Derivation.map_algebraMap _ a
      have hspec : chartBack (K := K) i (MvPolynomial.C a) = MvPolynomial.C a := by
        rw [← MvPolynomial.algebraMap_eq]
        exact (chartBack i).commutes a
      rw [hCa, map_zero, hspec, hCa]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      obtain ⟨k, l⟩ := j
      have hL : chartBack (K := K) i (differentialPolynomialDerivation n K
            (p * MvPolynomial.X (k, l))) =
          chartBack i p *
              chartBack i (differentialPolynomialDerivation n K (MvPolynomial.X (k, l))) +
            chartBack i (MvPolynomial.X (k, l)) *
              chartBack i (differentialPolynomialDerivation n K p) := by
        rw [Derivation.leibniz]
        simp [smul_eq_mul]
      have hR : differentialPolynomialDerivation n K
            (chartBack (K := K) i (p * MvPolynomial.X (k, l))) =
          chartBack i p *
              differentialPolynomialDerivation n K (chartBack i (MvPolynomial.X (k, l))) +
            chartBack i (MvPolynomial.X (k, l)) *
              differentialPolynomialDerivation n K (chartBack i p) := by
        rw [map_mul, Derivation.leibniz]
        simp [smul_eq_mul]
      rw [hL, hR, hp, hX]

omit [Fintype n] in
/-- **Inversion on numerators.**  The inverse chart substitution turns the affine numerator back
into its homogeneous coordinate, scaled by the chart denominator. -/
theorem chartBack_affineNumer {i k : n} (hk : k ≠ i) (l : ℕ) :
    chartBack (K := K) i (affineNumer i k l) =
      MvPolynomial.X (k, l) * MvPolynomial.X (i, 0) ^ (l + 1) := by
  induction l with
  | zero =>
      rw [affineNumer_zero, chartBack_X_of_ne hk]
      simp
  | succ l ih =>
      rw [affineNumer_succ, map_sub, map_mul, map_nsmul, map_mul, chartBack_deriv, ih,
        chartBack_X_self, chartBack_X_self]
      have hD : differentialPolynomialDerivation n K
          (MvPolynomial.X ((k, l) : n × ℕ) * MvPolynomial.X ((i, 0) : n × ℕ) ^ (l + 1)) =
          MvPolynomial.X ((k, l + 1) : n × ℕ) * MvPolynomial.X ((i, 0) : n × ℕ) ^ (l + 1) +
            (l + 1) • (MvPolynomial.X ((k, l) : n × ℕ) *
              (MvPolynomial.X ((i, 0) : n × ℕ) ^ l * MvPolynomial.X ((i, 1) : n × ℕ))) := by
        rw [Derivation.leibniz, Derivation.leibniz_pow, differentialPolynomialDerivation_X,
          differentialPolynomialDerivation_X]
        simp [smul_eq_mul]
        ring
      rw [hD]
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

end

end GaloisForLFunctions.HTGeometry
