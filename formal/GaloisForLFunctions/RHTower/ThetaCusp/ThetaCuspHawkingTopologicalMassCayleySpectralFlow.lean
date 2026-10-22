import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTopologicalDarbouxStarobinskySpectralFlow

/-!
The exact Birmingham--Mokhtari Starobinsky defect and absorbed-mass-induced
Teukolsky chiral defect form a complex return pair. Their quotient is the unique
mass-Cayley scattering matrix, with conjugate simple zero/pole incidence and a
strictly oriented two-mass spectral-flow determinant on every tilted Xi fibre.
-/
open Complex Real

namespace RHTower

noncomputable section

def d4BMXiThetaMirrorMassSpectralCoordinate (M : ℝ) (q : XiZeroCopy) : ℝ :=
  d4BMXiThetaMirrorAIMEDenominator q *
    (M - d4BMXiThetaMirrorCriticalMass q)

def d4BMXiThetaMirrorMixingAmplitude
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) : ℂ :=
  (d4BMXiThetaMirrorTopologicalStarobinskyDefect n M q : ℂ) +
    Complex.I * (d4BMXiThetaMirrorAIMEChiralKernelDefect q : ℂ)

def d4BMXiThetaMirrorMixingAdjointAmplitude
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) : ℂ :=
  (d4BMXiThetaMirrorTopologicalStarobinskyDefect n M q : ℂ) -
    Complex.I * (d4BMXiThetaMirrorAIMEChiralKernelDefect q : ℂ)

theorem d4BMXiThetaMirrorMixingAdjointAmplitude_eq_conj
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorMixingAdjointAmplitude n M q =
      (starRingEnd ℂ) (d4BMXiThetaMirrorMixingAmplitude n M q) := by
  unfold d4BMXiThetaMirrorMixingAdjointAmplitude
    d4BMXiThetaMirrorMixingAmplitude
  simp [sub_eq_add_neg]

theorem d4BMXiThetaMirrorMixingAmplitude_factorization
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorMixingAmplitude n M q =
      -((24 * ((q.1 : ℂ).re - 1 / 2) /
          d4BMXiThetaMirrorAIMEDenominator q : ℝ) : ℂ) *
        ((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) - Complex.I) := by
  rw [d4BMXiThetaMirrorMixingAmplitude,
    d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq,
    d4BMXiThetaMirrorAIMEChiralKernelDefect_eq]
  unfold d4BMXiThetaMirrorMassSpectralCoordinate
  have hD := ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)
  push_cast
  field_simp [hD]
  ring

theorem d4BMXiThetaMirrorMixingAdjointAmplitude_factorization
    (n : ℕ) (M : ℝ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorMixingAdjointAmplitude n M q =
      -((24 * ((q.1 : ℂ).re - 1 / 2) /
          d4BMXiThetaMirrorAIMEDenominator q : ℝ) : ℂ) *
        ((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) + Complex.I) := by
  rw [d4BMXiThetaMirrorMixingAdjointAmplitude,
    d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq,
    d4BMXiThetaMirrorAIMEChiralKernelDefect_eq]
  unfold d4BMXiThetaMirrorMassSpectralCoordinate
  have hD := ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)
  push_cast
  field_simp [hD]
  ring

def d4BMXiThetaMirrorMassCayleySMatrix (M : ℝ) (q : XiZeroCopy) : ℂ :=
  ((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) - Complex.I) /
    ((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) + Complex.I)

lemma d4BMXiThetaMirrorMassCayleyDenominator_ne_zero
    (M : ℝ) (q : XiZeroCopy) :
    (d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) + Complex.I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp at him

theorem d4BMXiThetaMirrorMassCayleySMatrix_eq_return_ratio_of_tilted
    (n : ℕ) (M : ℝ) (q : XiZeroCopy)
    (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiThetaMirrorMassCayleySMatrix M q =
      d4BMXiThetaMirrorMixingAmplitude n M q /
        d4BMXiThetaMirrorMixingAdjointAmplitude n M q := by
  rw [d4BMXiThetaMirrorMixingAmplitude_factorization,
    d4BMXiThetaMirrorMixingAdjointAmplitude_factorization]
  unfold d4BMXiThetaMirrorMassCayleySMatrix
  have hD := ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)
  have hdelta : (q.1 : ℂ).re - 1 / 2 ≠ 0 := sub_ne_zero.mpr htilt
  let c : ℂ := -((24 * ((q.1 : ℂ).re - 1 / 2) /
    d4BMXiThetaMirrorAIMEDenominator q : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    unfold c
    exact neg_ne_zero.mpr (by
      exact_mod_cast div_ne_zero (mul_ne_zero (by norm_num) hdelta) hD)
  change
    ((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) - Complex.I) /
        ((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) + Complex.I) =
      (c * ((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) - Complex.I)) /
        (c * ((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) + Complex.I))
  exact (mul_div_mul_left _ _ hc).symm

theorem normSq_d4BMXiThetaMirrorMassCayleySMatrix
    (M : ℝ) (q : XiZeroCopy) :
    Complex.normSq (d4BMXiThetaMirrorMassCayleySMatrix M q) = 1 := by
  let u := d4BMXiThetaMirrorMassSpectralCoordinate M q
  have hu : u * u + 1 ≠ 0 := by
    have : 0 < u * u + 1 := by nlinarith [sq_nonneg u]
    exact ne_of_gt this
  unfold d4BMXiThetaMirrorMassCayleySMatrix
  rw [Complex.normSq_div]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
    Complex.I_re, sub_zero, Complex.sub_im, Complex.ofReal_im, Complex.I_im,
    zero_sub, Complex.add_re, add_zero, Complex.add_im, zero_add]
  norm_num
  simpa [u] using div_self hu

theorem norm_d4BMXiThetaMirrorMassCayleySMatrix
    (M : ℝ) (q : XiZeroCopy) :
    ‖d4BMXiThetaMirrorMassCayleySMatrix M q‖ = 1 := by
  rw [Complex.norm_def, normSq_d4BMXiThetaMirrorMassCayleySMatrix]
  norm_num

theorem d4BMXiThetaMirrorMassCayleySMatrix_criticalMass
    (q : XiZeroCopy) :
    d4BMXiThetaMirrorMassCayleySMatrix
      (d4BMXiThetaMirrorCriticalMass q) q = -1 := by
  unfold d4BMXiThetaMirrorMassCayleySMatrix
    d4BMXiThetaMirrorMassSpectralCoordinate
  simp

theorem d4BMXiThetaMirrorMassCayleySMatrix_reflectMass
    (M : ℝ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorMassCayleySMatrix
        (2 * d4BMXiThetaMirrorCriticalMass q - M) q =
      (d4BMXiThetaMirrorMassCayleySMatrix M q)⁻¹ := by
  have hreflect :
      d4BMXiThetaMirrorMassSpectralCoordinate
          (2 * d4BMXiThetaMirrorCriticalMass q - M) q =
        -d4BMXiThetaMirrorMassSpectralCoordinate M q := by
    unfold d4BMXiThetaMirrorMassSpectralCoordinate
    ring
  unfold d4BMXiThetaMirrorMassCayleySMatrix
  rw [hreflect]
  have hnum :
      (d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) - Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
  rw [show ((-d4BMXiThetaMirrorMassSpectralCoordinate M q : ℝ) : ℂ) -
        Complex.I = -((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) +
          Complex.I) by push_cast; ring]
  rw [show ((-d4BMXiThetaMirrorMassSpectralCoordinate M q : ℝ) : ℂ) +
        Complex.I = -((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) -
          Complex.I) by push_cast; ring]
  rw [inv_div]
  field_simp [hnum, d4BMXiThetaMirrorMassCayleyDenominator_ne_zero M q]

def d4BMXiThetaMirrorMassSpectralFlowArea
    (n : ℕ) (M₁ M₂ : ℝ) (q : XiZeroCopy) : ℝ :=
  d4BMXiThetaMirrorTopologicalStarobinskyDefect n M₁ q *
      d4BMXiThetaMirrorAIMEChiralKernelDefect q -
    d4BMXiThetaMirrorAIMEChiralKernelDefect q *
      d4BMXiThetaMirrorTopologicalStarobinskyDefect n M₂ q

theorem d4BMXiThetaMirrorMassSpectralFlowArea_eq
    (n : ℕ) (M₁ M₂ : ℝ) (q : XiZeroCopy) :
    d4BMXiThetaMirrorMassSpectralFlowArea n M₁ M₂ q =
      576 * ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) * (M₂ - M₁) /
        d4BMXiThetaMirrorAIMEDenominator q := by
  unfold d4BMXiThetaMirrorMassSpectralFlowArea
  rw [d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq,
    d4BMXiThetaMirrorTopologicalStarobinskyDefect_eq,
    d4BMXiThetaMirrorAIMEChiralKernelDefect_eq]
  have hD := ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)
  field_simp [hD]
  ring

theorem d4BMXiThetaMirrorMassSpectralFlowArea_pos
    (n : ℕ) (M₁ M₂ : ℝ) (q : XiZeroCopy)
    (hM : M₁ < M₂) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < d4BMXiThetaMirrorMassSpectralFlowArea n M₁ M₂ q := by
  rw [d4BMXiThetaMirrorMassSpectralFlowArea_eq]
  exact div_pos
    (mul_pos
      (mul_pos (by norm_num) (sq_pos_of_ne_zero (sub_ne_zero.mpr htilt)))
      (sub_pos.mpr hM))
    (d4BMXiThetaMirrorAIMEDenominator_pos q)

def d4BMXiThetaMirrorComplexMassCayleyNumerator (mu : ℂ) (q : XiZeroCopy) : ℂ :=
  (d4BMXiThetaMirrorAIMEDenominator q : ℂ) *
      (mu - (d4BMXiThetaMirrorCriticalMass q : ℂ)) - Complex.I

def d4BMXiThetaMirrorComplexMassCayleyDenominator (mu : ℂ) (q : XiZeroCopy) : ℂ :=
  (d4BMXiThetaMirrorAIMEDenominator q : ℂ) *
      (mu - (d4BMXiThetaMirrorCriticalMass q : ℂ)) + Complex.I

def d4BMXiThetaMirrorComplexMassScatteringZero (q : XiZeroCopy) : ℂ :=
  (d4BMXiThetaMirrorCriticalMass q : ℂ) +
    Complex.I / (d4BMXiThetaMirrorAIMEDenominator q : ℂ)

def d4BMXiThetaMirrorComplexMassScatteringPole (q : XiZeroCopy) : ℂ :=
  (d4BMXiThetaMirrorCriticalMass q : ℂ) -
    Complex.I / (d4BMXiThetaMirrorAIMEDenominator q : ℂ)

theorem d4BMXiThetaMirrorComplexMassCayleyNumerator_zero (q : XiZeroCopy) :
    d4BMXiThetaMirrorComplexMassCayleyNumerator
      (d4BMXiThetaMirrorComplexMassScatteringZero q) q = 0 := by
  unfold d4BMXiThetaMirrorComplexMassCayleyNumerator
    d4BMXiThetaMirrorComplexMassScatteringZero
  have hD := ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)
  field_simp [hD]
  ring

theorem d4BMXiThetaMirrorComplexMassCayleyDenominator_zero (q : XiZeroCopy) :
    d4BMXiThetaMirrorComplexMassCayleyDenominator
      (d4BMXiThetaMirrorComplexMassScatteringPole q) q = 0 := by
  unfold d4BMXiThetaMirrorComplexMassCayleyDenominator
    d4BMXiThetaMirrorComplexMassScatteringPole
  have hD := ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)
  field_simp [hD]
  ring

theorem d4BMXiThetaMirrorComplexMassScatteringPole_eq_conj_zero (q : XiZeroCopy) :
    d4BMXiThetaMirrorComplexMassScatteringPole q =
      (starRingEnd ℂ) (d4BMXiThetaMirrorComplexMassScatteringZero q) := by
  unfold d4BMXiThetaMirrorComplexMassScatteringPole
    d4BMXiThetaMirrorComplexMassScatteringZero
  simp
  ring

theorem d4BMXiThetaMirrorComplexMassScatteringZero_ne_pole (q : XiZeroCopy) :
    d4BMXiThetaMirrorComplexMassScatteringZero q ≠
      d4BMXiThetaMirrorComplexMassScatteringPole q := by
  intro h
  have him := congrArg Complex.im h
  unfold d4BMXiThetaMirrorComplexMassScatteringZero
    d4BMXiThetaMirrorComplexMassScatteringPole at him
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
    Complex.normSq_ofReal, Complex.sub_im, zero_sub] at him
  have hD := ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)
  field_simp [hD] at him
  norm_num at him

theorem d4BMXiThetaMirrorComplexMassCayleyDenominator_at_zero (q : XiZeroCopy) :
    d4BMXiThetaMirrorComplexMassCayleyDenominator
      (d4BMXiThetaMirrorComplexMassScatteringZero q) q = 2 * Complex.I := by
  unfold d4BMXiThetaMirrorComplexMassCayleyDenominator
    d4BMXiThetaMirrorComplexMassScatteringZero
  have hD := ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)
  field_simp [hD]
  ring

theorem d4BMXiThetaMirrorComplexMassCayleyNumerator_at_pole (q : XiZeroCopy) :
    d4BMXiThetaMirrorComplexMassCayleyNumerator
      (d4BMXiThetaMirrorComplexMassScatteringPole q) q = -2 * Complex.I := by
  unfold d4BMXiThetaMirrorComplexMassCayleyNumerator
    d4BMXiThetaMirrorComplexMassScatteringPole
  have hD := ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)
  field_simp [hD]
  ring

theorem hasDerivAt_d4BMXiThetaMirrorComplexMassCayleyNumerator
    (mu : ℂ) (q : XiZeroCopy) :
    HasDerivAt (fun z => d4BMXiThetaMirrorComplexMassCayleyNumerator z q)
      (d4BMXiThetaMirrorAIMEDenominator q : ℂ) mu := by
  unfold d4BMXiThetaMirrorComplexMassCayleyNumerator
  have hsub : HasDerivAt
      (fun z : ℂ => z - (d4BMXiThetaMirrorCriticalMass q : ℂ)) 1 mu :=
    (hasDerivAt_id mu).sub_const
      (d4BMXiThetaMirrorCriticalMass q : ℂ)
  simpa only [mul_one] using
    (hsub.const_mul
      (d4BMXiThetaMirrorAIMEDenominator q : ℂ)).sub_const Complex.I

theorem hasDerivAt_d4BMXiThetaMirrorComplexMassCayleyDenominator
    (mu : ℂ) (q : XiZeroCopy) :
    HasDerivAt (fun z => d4BMXiThetaMirrorComplexMassCayleyDenominator z q)
      (d4BMXiThetaMirrorAIMEDenominator q : ℂ) mu := by
  unfold d4BMXiThetaMirrorComplexMassCayleyDenominator
  have hsub : HasDerivAt
      (fun z : ℂ => z - (d4BMXiThetaMirrorCriticalMass q : ℂ)) 1 mu :=
    (hasDerivAt_id mu).sub_const
      (d4BMXiThetaMirrorCriticalMass q : ℂ)
  simpa only [mul_one] using
    (hsub.const_mul
      (d4BMXiThetaMirrorAIMEDenominator q : ℂ)).add_const Complex.I

theorem d4BMXiThetaMirrorComplexMassCayleyDerivative_ne_zero (q : XiZeroCopy) :
    (d4BMXiThetaMirrorAIMEDenominator q : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (d4BMXiThetaMirrorAIMEDenominator_pos q)

theorem d4BMXiThetaMirrorMassCayleySMatrix_unique
    (M : ℝ) (q : XiZeroCopy) (S : ℂ)
    (hreturn :
      ((d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) + Complex.I) * S =
        (d4BMXiThetaMirrorMassSpectralCoordinate M q : ℂ) - Complex.I) :
    S = d4BMXiThetaMirrorMassCayleySMatrix M q := by
  unfold d4BMXiThetaMirrorMassCayleySMatrix
  apply (eq_div_iff (d4BMXiThetaMirrorMassCayleyDenominator_ne_zero M q)).2
  rw [mul_comm]
  exact hreturn

end

end RHTower

