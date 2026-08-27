import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicExactAdSOuterBasis

/-!
# Exact BM second-harmonic horizon-to-AdS connection matrix

Conserved cross-Wronskians and Cramer's rule express both exact horizon solutions in the exact AdS
source/normalizable basis. Coefficients are fixed at `z=1/2`, independent of radius, and their
connection determinant is exactly `-2(4n+3+2i chi)`. Gamma/Jost identification remains separate.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Generic interval constancy of a normalized cross-Wronskian between two exact BM solution
jets. -/
theorem d4BMPlusPlusNormalizedWronskian_eq_of_solutionJets
    (n : ℕ) (chi : ℂ) (y dy ddy v dv ddv : ℝ → ℂ)
    (hy : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt y (dy z) z)
    (hdy : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt dy (ddy z) z)
    (hv : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt v (dv z) z)
    (hdv : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt dv (ddv z) z)
    (hyjet : ∀ z ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusHypergeometricJet n chi z (y z) (dy z) (ddy z) = 0)
    (hvjet : ∀ z ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusHypergeometricJet n chi z (v z) (dv z) (ddv z) = 0)
    {x t : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    d4BMPlusPlusNormalizedWronskian n chi y dy v dv x =
      d4BMPlusPlusNormalizedWronskian n chi y dy v dv t := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
  · intro z hz
    exact (hasDerivAt_d4BMPlusPlusNormalizedWronskian_of_solutionJets
      n chi y dy ddy v dv ddv hz.1 hz.2
      (hy z hz) (hdy z hz) (hv z hz) (hdv z hz)
      (hyjet z hz) (hvjet z hz)).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (hasDerivAt_d4BMPlusPlusNormalizedWronskian_of_solutionJets
      n chi y dy ddy v dv ddv hz.1 hz.2
      (hy z hz) (hdy z hz) (hv z hz) (hdv z hz)
      (hyjet z hz) (hvjet z hz)).deriv
  · exact hx
  · exact ht

/-- Pointwise Cramer's rule for a phase vector in a nondegenerate normalized basis. -/
theorem d4BMPlusPlusNormalizedWronskian_cramer_phase
    (n : ℕ) (chi : ℂ) (y dy S Sd V Vd : ℝ → ℂ) (z : ℝ)
    (hW : d4BMPlusPlusNormalizedWronskian n chi S Sd V Vd z ≠ 0) :
    y z =
          (d4BMPlusPlusNormalizedWronskian n chi y dy V Vd z /
              d4BMPlusPlusNormalizedWronskian n chi S Sd V Vd z) * S z +
            (d4BMPlusPlusNormalizedWronskian n chi S Sd y dy z /
              d4BMPlusPlusNormalizedWronskian n chi S Sd V Vd z) * V z ∧
      dy z =
          (d4BMPlusPlusNormalizedWronskian n chi y dy V Vd z /
              d4BMPlusPlusNormalizedWronskian n chi S Sd V Vd z) * Sd z +
            (d4BMPlusPlusNormalizedWronskian n chi S Sd y dy z /
              d4BMPlusPlusNormalizedWronskian n chi S Sd V Vd z) * Vd z := by
  rw [d4BMPlusPlusNormalizedWronskian] at hW
  have hp : d4BMPlusPlusIntegratingFactor n chi z ≠ 0 := by
    intro hp0
    apply hW
    rw [hp0, zero_mul]
  have hdet : S z * Vd z - Sd z * V z ≠ 0 := by
    intro hdet0
    apply hW
    rw [hdet0, mul_zero]
  have hdet' : Vd z * S z - V z * Sd z ≠ 0 := by
    simpa [mul_comm] using hdet
  constructor
  · simp only [d4BMPlusPlusNormalizedWronskian]
    rw [mul_div_mul_left _ _ hp, mul_div_mul_left _ _ hp]
    field_simp [hdet']
    ring
  · simp only [d4BMPlusPlusNormalizedWronskian]
    rw [mul_div_mul_left _ _ hp, mul_div_mul_left _ _ hp]
    field_simp [hdet']
    ring

private def d4BMPlusPlusConnectionBase : ℝ := 1 / 2

/-- Forbidden/source coefficient of horizon-regular solution in exact AdS basis. -/
def d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMPlusPlusNormalizedWronskian n chi
      (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ))
      (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ))
      (d4BMPlusPlusAdSNormalizableSolution n chi)
      (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi)
      d4BMPlusPlusConnectionBase /
    d4BMPlusPlusAdSOuterWronskian n chi d4BMPlusPlusConnectionBase

/-- Normalizable coefficient of horizon-regular solution in exact AdS basis. -/
def d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMPlusPlusNormalizedWronskian n chi
      (d4BMPlusPlusAdSForbiddenSolution n chi)
      (d4BMPlusPlusAdSForbiddenSolutionDerivative n chi)
      (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ))
      (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ))
      d4BMPlusPlusConnectionBase /
    d4BMPlusPlusAdSOuterWronskian n chi d4BMPlusPlusConnectionBase

/-- Forbidden/source coefficient of horizon-complementary solution in exact AdS basis. -/
def d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMPlusPlusNormalizedWronskian n chi
      (d4BMPlusPlusComplementaryHypergeometricSolution n chi)
      (d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi)
      (d4BMPlusPlusAdSNormalizableSolution n chi)
      (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi)
      d4BMPlusPlusConnectionBase /
    d4BMPlusPlusAdSOuterWronskian n chi d4BMPlusPlusConnectionBase

/-- Normalizable coefficient of horizon-complementary solution in exact AdS basis. -/
def d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient
    (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMPlusPlusNormalizedWronskian n chi
      (d4BMPlusPlusAdSForbiddenSolution n chi)
      (d4BMPlusPlusAdSForbiddenSolutionDerivative n chi)
      (d4BMPlusPlusComplementaryHypergeometricSolution n chi)
      (d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi)
      d4BMPlusPlusConnectionBase /
    d4BMPlusPlusAdSOuterWronskian n chi d4BMPlusPlusConnectionBase

/-- Exact phase-vector connection of horizon-regular solution into AdS basis. -/
theorem d4BMPlusPlusRegularAdSConnection_phase
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) =
          d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
              d4BMPlusPlusAdSForbiddenSolution n chi z +
            d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi *
              d4BMPlusPlusAdSNormalizableSolution n chi z ∧
      d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) =
          d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
              d4BMPlusPlusAdSForbiddenSolutionDerivative n chi z +
            d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi *
              d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z := by
  let R := fun x : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ)
  let Rd := fun x : ℝ =>
    d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (x : ℂ)
  let Rdd := fun x : ℝ =>
    d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (x : ℂ)
  let S := d4BMPlusPlusAdSForbiddenSolution n chi
  let Sd := d4BMPlusPlusAdSForbiddenSolutionDerivative n chi
  let Sdd := d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi
  let V := d4BMPlusPlusAdSNormalizableSolution n chi
  let Vd := d4BMPlusPlusAdSNormalizableSolutionDerivative n chi
  let Vdd := d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi
  have hR : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt R (Rd x) x := by
    intro x hx
    simpa [R, Rd] using!
      (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolution n chi (x : ℂ)
        hchi (enorm_ofReal_lt_one hx.1 hx.2)).comp_ofReal
  have hRd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Rd (Rdd x) x := by
    intro x hx
    simpa [Rd, Rdd] using!
      (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (x : ℂ)
        hchi (enorm_ofReal_lt_one hx.1 hx.2)).comp_ofReal
  have hRjet : ∀ x ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusHypergeometricJet n chi x (R x) (Rd x) (Rdd x) = 0 := by
    intro x hx
    simpa [R, Rd, Rdd] using
      d4BMPlusPlusRegularHypergeometricSolution_real_jet_eq_zero
        n chi hchi hx.1 hx.2
  have hS : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt S (Sd x) x := by
    intro x hx
    exact hasDerivAt_d4BMPlusPlusAdSForbiddenSolution n chi hchi hx.1 hx.2
  have hSd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Sd (Sdd x) x := by
    intro x hx
    exact hasDerivAt_d4BMPlusPlusAdSForbiddenSolutionDerivative n chi hchi hx.1 hx.2
  have hSjet : ∀ x ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusHypergeometricJet n chi x (S x) (Sd x) (Sdd x) = 0 := by
    intro x hx
    exact d4BMPlusPlusAdSForbiddenSolution_jet_eq_zero n chi hchi hx.1 hx.2
  have hV : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt V (Vd x) x := by
    intro x hx
    exact hasDerivAt_d4BMPlusPlusAdSNormalizableSolution n chi hchi hx.1 hx.2
  have hVd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Vd (Vdd x) x := by
    intro x hx
    exact hasDerivAt_d4BMPlusPlusAdSNormalizableSolutionDerivative n chi hchi hx.1 hx.2
  have hVjet : ∀ x ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusHypergeometricJet n chi x (V x) (Vd x) (Vdd x) = 0 := by
    intro x hx
    exact d4BMPlusPlusAdSNormalizableSolution_jet_eq_zero n chi hchi hx.1 hx.2
  have hb : d4BMPlusPlusConnectionBase ∈ Ioo (0 : ℝ) 1 := by
    norm_num [d4BMPlusPlusConnectionBase]
  have hRV := d4BMPlusPlusNormalizedWronskian_eq_of_solutionJets
    n chi R Rd Rdd V Vd Vdd hR hRd hV hVd hRjet hVjet ⟨hz0, hz1⟩ hb
  have hSR := d4BMPlusPlusNormalizedWronskian_eq_of_solutionJets
    n chi S Sd Sdd R Rd Rdd hS hSd hR hRd hSjet hRjet ⟨hz0, hz1⟩ hb
  have hO : d4BMPlusPlusAdSOuterWronskian n chi z =
      d4BMPlusPlusAdSOuterWronskian n chi d4BMPlusPlusConnectionBase := by
    rw [d4BMPlusPlusAdSOuterWronskian_eq_neg_half n chi hchi hz0 hz1,
      d4BMPlusPlusAdSOuterWronskian_eq_neg_half n chi hchi hb.1 hb.2]
  have hcr := d4BMPlusPlusNormalizedWronskian_cramer_phase
    n chi R Rd S Sd V Vd z
    (by simpa [d4BMPlusPlusAdSOuterWronskian, S, Sd, V, Vd] using
      d4BMPlusPlusAdSOuterWronskian_ne_zero n chi hchi hz0 hz1)
  rw [d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient,
    d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient,
    ← hRV, ← hSR, ← hO]
  simpa [R, Rd, S, Sd, V, Vd, d4BMPlusPlusAdSOuterWronskian] using hcr

/-- Exact phase-vector connection of horizon-complementary solution into AdS basis. -/
theorem d4BMPlusPlusComplementaryAdSConnection_phase
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4BMPlusPlusComplementaryHypergeometricSolution n chi z =
          d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi *
              d4BMPlusPlusAdSForbiddenSolution n chi z +
            d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi *
              d4BMPlusPlusAdSNormalizableSolution n chi z ∧
      d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi z =
          d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi *
              d4BMPlusPlusAdSForbiddenSolutionDerivative n chi z +
            d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi *
              d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z := by
  let C := d4BMPlusPlusComplementaryHypergeometricSolution n chi
  let Cd := d4BMPlusPlusComplementaryHypergeometricSolutionDerivative n chi
  let Cdd := d4BMPlusPlusComplementaryHypergeometricSolutionSecondDerivative n chi
  let S := d4BMPlusPlusAdSForbiddenSolution n chi
  let Sd := d4BMPlusPlusAdSForbiddenSolutionDerivative n chi
  let Sdd := d4BMPlusPlusAdSForbiddenSolutionSecondDerivative n chi
  let V := d4BMPlusPlusAdSNormalizableSolution n chi
  let Vd := d4BMPlusPlusAdSNormalizableSolutionDerivative n chi
  let Vdd := d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi
  have hC : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt C (Cd x) x := by
    intro x hx
    exact hasDerivAt_d4BMPlusPlusComplementaryHypergeometricSolution
      n chi hchi hx.1 hx.2
  have hCd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Cd (Cdd x) x := by
    intro x hx
    exact hasDerivAt_d4BMPlusPlusComplementaryHypergeometricSolutionDerivative
      n chi hchi hx.1 hx.2
  have hCjet : ∀ x ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusHypergeometricJet n chi x (C x) (Cd x) (Cdd x) = 0 := by
    intro x hx
    exact d4BMPlusPlusComplementaryHypergeometricSolution_jet_eq_zero
      n chi hchi hx.1 hx.2
  have hS : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt S (Sd x) x := by
    intro x hx
    exact hasDerivAt_d4BMPlusPlusAdSForbiddenSolution n chi hchi hx.1 hx.2
  have hSd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Sd (Sdd x) x := by
    intro x hx
    exact hasDerivAt_d4BMPlusPlusAdSForbiddenSolutionDerivative n chi hchi hx.1 hx.2
  have hSjet : ∀ x ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusHypergeometricJet n chi x (S x) (Sd x) (Sdd x) = 0 := by
    intro x hx
    exact d4BMPlusPlusAdSForbiddenSolution_jet_eq_zero n chi hchi hx.1 hx.2
  have hV : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt V (Vd x) x := by
    intro x hx
    exact hasDerivAt_d4BMPlusPlusAdSNormalizableSolution n chi hchi hx.1 hx.2
  have hVd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Vd (Vdd x) x := by
    intro x hx
    exact hasDerivAt_d4BMPlusPlusAdSNormalizableSolutionDerivative n chi hchi hx.1 hx.2
  have hVjet : ∀ x ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusHypergeometricJet n chi x (V x) (Vd x) (Vdd x) = 0 := by
    intro x hx
    exact d4BMPlusPlusAdSNormalizableSolution_jet_eq_zero n chi hchi hx.1 hx.2
  have hb : d4BMPlusPlusConnectionBase ∈ Ioo (0 : ℝ) 1 := by
    norm_num [d4BMPlusPlusConnectionBase]
  have hCV := d4BMPlusPlusNormalizedWronskian_eq_of_solutionJets
    n chi C Cd Cdd V Vd Vdd hC hCd hV hVd hCjet hVjet ⟨hz0, hz1⟩ hb
  have hSC := d4BMPlusPlusNormalizedWronskian_eq_of_solutionJets
    n chi S Sd Sdd C Cd Cdd hS hSd hC hCd hSjet hCjet ⟨hz0, hz1⟩ hb
  have hO : d4BMPlusPlusAdSOuterWronskian n chi z =
      d4BMPlusPlusAdSOuterWronskian n chi d4BMPlusPlusConnectionBase := by
    rw [d4BMPlusPlusAdSOuterWronskian_eq_neg_half n chi hchi hz0 hz1,
      d4BMPlusPlusAdSOuterWronskian_eq_neg_half n chi hchi hb.1 hb.2]
  have hcr := d4BMPlusPlusNormalizedWronskian_cramer_phase
    n chi C Cd S Sd V Vd z
    (by simpa [d4BMPlusPlusAdSOuterWronskian, S, Sd, V, Vd] using
      d4BMPlusPlusAdSOuterWronskian_ne_zero n chi hchi hz0 hz1)
  rw [d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient,
    d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient,
    ← hCV, ← hSC, ← hO]
  simpa [C, Cd, S, Sd, V, Vd, d4BMPlusPlusAdSOuterWronskian] using hcr

/-- Determinant of exact horizon-to-AdS connection matrix. -/
theorem d4BMPlusPlusAdSConnectionDet_eq
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
          d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi -
        d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi *
          d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi =
      -2 * d4BMPlusPlusComplementaryFrobeniusExponent n chi := by
  let z : ℝ := 1 / 2
  have hz0 : 0 < z := by norm_num [z]
  have hz1 : z < 1 := by norm_num [z]
  rcases d4BMPlusPlusRegularAdSConnection_phase n chi hchi hz0 hz1 with
    ⟨hR, hRd⟩
  rcases d4BMPlusPlusComplementaryAdSConnection_phase n chi hchi hz0 hz1 with
    ⟨hC, hCd⟩
  have hW := d4BMPlusPlusRegularComplementaryWronskian_eq_exponent
    n chi hchi hz0 hz1
  have hO := d4BMPlusPlusAdSOuterWronskian_eq_neg_half
    n chi hchi hz0 hz1
  have hexpand :
      d4BMPlusPlusRegularComplementaryWronskian n chi z =
        (d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n chi *
              d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n chi -
            d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n chi *
              d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n chi) *
          d4BMPlusPlusAdSOuterWronskian n chi z := by
    rw [d4BMPlusPlusRegularComplementaryWronskian,
      d4BMPlusPlusAdSOuterWronskian,
      d4BMPlusPlusNormalizedWronskian,
      hR, hRd, hC, hCd]
    ring
  rw [hW, hO] at hexpand
  linear_combination 2 * hexpand

/-- Every Xi-fibre horizon-to-AdS connection matrix is invertible. -/
theorem d4BMXiPlusPlusAdSConnectionDet_ne_zero
    (n : ℕ) (q : XiZeroCopy) :
    d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) -
        d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
            (d4BMXiMixedHorizonAngularMomentum q) ≠ 0 := by
  rw [d4BMPlusPlusAdSConnectionDet_eq n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)]
  exact mul_ne_zero (by norm_num)
    (d4BMXiPlusPlusRegularComplementaryWronskian_limit_ne_zero n q)

end

end RHTower
