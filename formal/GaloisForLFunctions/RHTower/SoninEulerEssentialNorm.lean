/-
Exact essential norms of the even Sonin dilation and Euler corners.

At equal scales the mixed shell translation degenerates to the two-polarization shell, so the
adjoint square of the one-scale even Sonin dilation corner agrees modulo compact operators
with the shell between the cutoff and its dilate. The corner is therefore a Calkin partial
isometry with that shell as initial projection, and the compact-congruence upper bound meets
the shell-sequence lower bound: every one-scale corner and every ordered two-scale Gram entry
has essential norm exactly one. Scalar transport gives the exact essential norms `(√p)⁻¹` and
`(√p √q)⁻¹` of the positive Euler corners, and unitary transport carries all four identities
to the literal archimedean Hardy--Titchmarsh operators.
-/
import GaloisForLFunctions.RHTower.SoninCalkinNormBound

noncomputable section

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct

/-! ### The diagonal shell reduction -/

theorem evenDilationCLM_eq_one_of_eq_one {r : ℝ} (hr : 0 < r) (h : r = 1) :
    evenDilationCLM r hr = 1 := by
  subst h
  exact evenDilationCLM_one

/-- At equal scales the mixed shell translation is the two-polarization shell itself: the
translating dilation degenerates to the identity and the shell factors absorb the outer
complement. -/
theorem evenSoninMixedShellTranslation_self
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    evenSoninMixedShellTranslation a p p hp hp = evenTwoPolarizationShell a (p * a) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hap : a ≤ p * a := by nlinarith
  have hU₁ : evenDilationCLM (p⁻¹ * p) (mul_pos (inv_pos.mpr hp0) hp0) = 1 :=
    evenDilationCLM_eq_one_of_eq_one _ (inv_mul_cancel₀ hp0.ne')
  have hU₂ : evenDilationCLM (p * p⁻¹) (mul_pos hp0 (inv_pos.mpr hp0)) = 1 :=
    evenDilationCLM_eq_one_of_eq_one _ (mul_inv_cancel₀ hp0.ne')
  have hphys : (evenIndicatorCutoff (p * a) - evenIndicatorCutoff a) *
      (1 - evenIndicatorCutoff a) =
      evenIndicatorCutoff (p * a) - evenIndicatorCutoff a := by
    have h1 : evenIndicatorCutoff (p * a) * evenIndicatorCutoff a = evenIndicatorCutoff a :=
      evenIndicatorCutoff_mul_of_le_rev a (p * a) hap
    have h2 : evenIndicatorCutoff a * evenIndicatorCutoff a = evenIndicatorCutoff a :=
      evenIndicatorCutoff_mul_of_le a a le_rfl
    rw [mul_sub, mul_one, sub_mul, h1, h2]
    abel
  have hfour : (evenFourierCutoff (p * a) - evenFourierCutoff a) *
      (1 - evenFourierCutoff a) =
      evenFourierCutoff (p * a) - evenFourierCutoff a := by
    have h1 : evenFourierCutoff (p * a) * evenFourierCutoff a = evenFourierCutoff a :=
      evenFourierCutoff_mul_of_le_rev a (p * a) hap
    have h2 : evenFourierCutoff a * evenFourierCutoff a = evenFourierCutoff a :=
      evenFourierCutoff_mul_of_le a a le_rfl
    rw [mul_sub, mul_one, sub_mul, h1, h2]
    abel
  dsimp [evenSoninMixedShellTranslation, evenPhysicalMixedShellTranslation,
    evenFourierMixedShellTranslation, evenTwoPolarizationShell]
  rw [hU₁, hU₂, mul_one, mul_one, hphys, hfour]

/-- **Initial Calkin projection of the one-scale corner.** The adjoint square of the even
Sonin dilation corner agrees modulo compact operators with the sum of the physical and
Fourier shell projections between the cutoff and its dilate. -/
theorem evenCentralSoninDilationCorner_adjoint_mul_compactEq_shell
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    (evenCentralSoninDilationCorner a p hp)† * evenCentralSoninDilationCorner a p hp =ₖ
      evenTwoPolarizationShell a (p * a) := by
  have h := evenCentralSoninQuadraticCorner_compactEq_shellTranslation a p p ha hp hp
  rw [evenSoninMixedShellTranslation_self a p ha hp] at h
  have hdef : (evenCentralSoninDilationCorner a p hp)† *
      evenCentralSoninDilationCorner a p hp =
      evenCentralSoninQuadraticCorner a p p hp hp := rfl
  exact (CompactOperatorEq.of_eq hdef).trans h

/-- **One-scale Calkin partial isometry.** The even Sonin dilation corner is a partial
isometry modulo compact operators; its initial projection is the two-polarization shell
between the cutoff and its dilate. -/
theorem evenCentralSoninDilationCorner_isCalkinPartialIsometry
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    IsCalkinPartialIsometry (evenCentralSoninDilationCorner a p hp) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hap : a ≤ p * a := by nlinarith
  have hSadj := adjoint_evenTwoPolarizationShell a (p * a)
  have hSS := evenTwoPolarizationShell_mul_compactEq_self a (p * a) ha hap
  have hLS := evenCentralSoninDilationCorner_adjoint_mul_compactEq_shell a p ha hp
  exact ⟨compactEq_idempotent_of_compactEq hLS hSS,
    mul_adjoint_sq_compactEq_of_adjoint_mul_compactEq _ _ hSadj hLS hSS⟩

/-! ### Upper bounds against the compact ideal -/

/-- The one-scale even Sonin dilation corner is within `1 + ε` of a compact operator. -/
theorem exists_isCompactOperator_norm_evenCentralSoninDilationCorner_sub_le
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : evenSubspace →L[ℂ] evenSubspace,
      IsCompactOperator K ∧ ‖evenCentralSoninDilationCorner a p hp - K‖ ≤ 1 + ε := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hap : a ≤ p * a := by nlinarith
  exact exists_isCompactOperator_norm_sub_le_one_add _ _
    (adjoint_evenTwoPolarizationShell a (p * a))
    (evenCentralSoninDilationCorner_adjoint_mul_compactEq_shell a p ha hp)
    (evenTwoPolarizationShell_mul_compactEq_self a (p * a) ha hap) hε

/-- Every ordered two-scale even Sonin Gram entry is within `1 + ε` of a compact operator. -/
theorem exists_isCompactOperator_norm_evenCentralSoninQuadraticCorner_sub_le
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : evenSubspace →L[ℂ] evenSubspace,
      IsCompactOperator K ∧ ‖evenCentralSoninQuadraticCorner a p q hp hq - K‖ ≤ 1 + ε := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hm : 1 < min p q := lt_min hp hq
  have hm0 : 0 < min p q := zero_lt_one.trans hm
  have hs : 0 < (q * (min p q)⁻¹) * a := by positivity
  have hst : (q * (min p q)⁻¹) * a ≤ q * a := by
    have hminv : (min p q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm.le
    have hscale : q * (min p q)⁻¹ ≤ q := by nlinarith
    nlinarith
  exact exists_isCompactOperator_norm_sub_le_one_add _ _
    (adjoint_evenTwoPolarizationShell ((q * (min p q)⁻¹) * a) (q * a))
    (evenCentralSoninQuadraticCorner_adjoint_mul_compactEq_shell a p q ha hp hq)
    (evenTwoPolarizationShell_mul_compactEq_self ((q * (min p q)⁻¹) * a) (q * a) hs hst) hε

/-! ### Exact essential norms on the even Sonin carrier -/

/-- **Exact essential norm of the one-scale corner.** -/
theorem essentialNorm_evenCentralSoninDilationCorner
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    essentialNorm (evenCentralSoninDilationCorner a p hp) = 1 :=
  essentialNorm_eq_of_bounds _ 1
    (one_le_norm_evenCentralSoninDilationCorner_sub_compact a p ha hp)
    (fun _ hε =>
      exists_isCompactOperator_norm_evenCentralSoninDilationCorner_sub_le a p ha hp hε)

/-- **Exact essential norm of every ordered two-scale Gram entry.** -/
theorem essentialNorm_evenCentralSoninQuadraticCorner
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    essentialNorm (evenCentralSoninQuadraticCorner a p q hp hq) = 1 :=
  essentialNorm_eq_of_bounds _ 1
    (one_le_norm_evenCentralSoninQuadraticCorner_sub_compact a p q ha hp hq)
    (fun _ hε =>
      exists_isCompactOperator_norm_evenCentralSoninQuadraticCorner_sub_le a p q ha hp hq hε)

/-- **Exact essential norm of the positive Euler corner:** `(√p)⁻¹`. -/
theorem essentialNorm_evenCentralPositiveEulerCorner
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    essentialNorm (evenCentralPositiveEulerCorner a p hp) = (Real.sqrt p)⁻¹ := by
  rw [evenCentralPositiveEulerCorner_eq_smul, essentialNorm_smul,
    essentialNorm_evenCentralSoninDilationCorner a p ha hp, mul_one,
    norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg p)]

/-- **Exact essential norm of the ordered positive Euler Gram entry:** `(√p √q)⁻¹`. -/
theorem essentialNorm_evenCentralPositiveEulerQuadraticCorner
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    essentialNorm (evenCentralPositiveEulerQuadraticCorner a p q hp hq) =
      (Real.sqrt p * Real.sqrt q)⁻¹ := by
  rw [evenCentralPositiveEulerQuadraticCorner_eq_smul, essentialNorm_smul,
    essentialNorm_evenCentralSoninQuadraticCorner a p q ha hp hq, mul_one,
    norm_mul, norm_star, norm_neg, norm_neg, norm_inv, norm_inv,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg p), abs_of_nonneg (Real.sqrt_nonneg q),
    mul_inv]

/-! ### Exact essential norms on the concrete archimedean Hardy--Titchmarsh line -/

/-- **Exact essential norm of the literal archimedean one-prime Euler metric corner:**
`(√p)⁻¹`, uniformly in the cutoff. -/
theorem essentialNorm_archimedeanPrimeEulerCorner
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    essentialNorm (archimedeanPrimeEulerCorner a p) = (Real.sqrt p)⁻¹ := by
  rw [archimedeanPrimeEulerCorner_eq_sourceCorner a p hp,
    hardyTitchmarshEulerCorner_eq_unitaryPush archimedeanDualHardyTitchmarshUnitary a p hp,
    essentialNorm_unitaryPush]
  exact essentialNorm_evenCentralPositiveEulerCorner a p ha hp

/-- **Exact essential norm of the literal archimedean two-scale Euler Gram entry:**
`(√p √q)⁻¹`, uniformly in the cutoff. -/
theorem essentialNorm_archimedeanPrimeEulerQuadraticCorner
    (a p q : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) :
    essentialNorm (archimedeanPrimeEulerQuadraticCorner a p q) =
      (Real.sqrt p * Real.sqrt q)⁻¹ := by
  rw [archimedeanPrimeEulerQuadraticCorner_eq_unitaryPush a p q hp hq,
    essentialNorm_unitaryPush]
  exact essentialNorm_evenCentralPositiveEulerQuadraticCorner a p q ha hp hq

/-- The exact archimedean essential norm at a rational prime. -/
theorem essentialNorm_archimedeanPrimeEulerCorner_natPrime
    (a : ℝ) (p : ℕ) (ha : 0 < a) (hp : p.Prime) :
    essentialNorm (archimedeanPrimeEulerCorner a (p : ℝ)) = (Real.sqrt (p : ℝ))⁻¹ :=
  essentialNorm_archimedeanPrimeEulerCorner a (p : ℝ) ha (by exact_mod_cast hp.one_lt)

/-- The exact archimedean quadratic essential norm at an ordered pair of rational primes. -/
theorem essentialNorm_archimedeanPrimeEulerQuadraticCorner_natPrime
    (a : ℝ) (p q : ℕ) (ha : 0 < a) (hp : p.Prime) (hq : q.Prime) :
    essentialNorm (archimedeanPrimeEulerQuadraticCorner a (p : ℝ) (q : ℝ)) =
      (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ))⁻¹ :=
  essentialNorm_archimedeanPrimeEulerQuadraticCorner a (p : ℝ) (q : ℝ) ha
    (by exact_mod_cast hp.one_lt) (by exact_mod_cast hq.one_lt)

end RHTower
