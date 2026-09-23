import GaloisForLFunctions.RHTower.FiniteHermiteCRT
import GaloisForLFunctions.RHTower.XiCTaylorSignedThreeAtomReflectionEscape

/-!
# Four atoms are the sharp literal-profile reflection escape

Three atoms carry an off-center reflection-coherent projective ray, but the reflected
representatives differ by a nontrivial scalar.  A literal source multiplier has one coefficient
vector at both fibres.  This module proves that at most three full-turn atoms cannot carry equal
nonzero reflected derivative charge with one vector, while four atoms can.

The four-atom ray is explicit.  A real finite Hermite interpolation theorem then supplies one
bounded correction vector that normalizes both reflected values and both derivative corrections
simultaneously.  Hence the same four weights give exact unit source-connection charge at both
off-center fibres.
-/

open Complex Real Polynomial Function

namespace RHTower

noncomputable section

/-! ## Real finite Hermite interpolation -/

/-- Product modulus for a finite real Hermite packet. -/
def realFiniteHermiteModulus {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (m : ι → ℕ) : Polynomial ℝ :=
  ∏ i, (X - C (w i)) ^ m i

theorem realFiniteHermiteModulus_monic {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (m : ι → ℕ) : (realFiniteHermiteModulus w m).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (monic_X_sub_C (w i)).pow _

theorem real_power_linear_dvd_realFiniteHermiteModulus
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (m : ι → ℕ) (i : ι) :
    (X - C (w i)) ^ m i ∣ realFiniteHermiteModulus w m := by
  exact Finset.dvd_prod_of_mem
    (fun j => (X - C (w j)) ^ m j) (Finset.mem_univ i)

theorem exists_real_polynomial_power_linear_dvd_sub
    {ι : Type*} [Finite ι] (w : ι → ℝ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℝ) :
    ∃ B : Polynomial ℝ, ∀ i,
      (X - C (w i)) ^ m i ∣ B - target i := by
  let I : ι → Ideal (Polynomial ℝ) := fun i =>
    Ideal.span ({(X - C (w i)) ^ m i} : Set (Polynomial ℝ))
  have hI : Pairwise (IsCoprime on I) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (pairwise_coprime_X_sub_C hw hij).pow
  obtain ⟨B, hB⟩ := Ideal.exists_forall_sub_mem_ideal hI target
  refine ⟨B, fun i => ?_⟩
  simpa only [I, Ideal.mem_span_singleton] using hB i

theorem exists_real_polynomial_power_linear_dvd_sub_degree_lt_modulus
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℝ) :
    ∃ B : Polynomial ℝ,
      B.degree < (realFiniteHermiteModulus w m).degree ∧
      ∀ i, (X - C (w i)) ^ m i ∣ B - target i := by
  obtain ⟨P, hP⟩ := exists_real_polynomial_power_linear_dvd_sub w hw m target
  let M := realFiniteHermiteModulus w m
  refine ⟨P %ₘ M,
    Polynomial.degree_modByMonic_lt P (realFiniteHermiteModulus_monic w m), ?_⟩
  intro i
  have hfactor : (X - C (w i)) ^ m i ∣ M :=
    real_power_linear_dvd_realFiniteHermiteModulus w m i
  have hmod : M ∣ P - P %ₘ M := by
    refine ⟨P /ₘ M, ?_⟩
    have hdiv := Polynomial.modByMonic_add_div P M
    rw [eq_comm]
    linear_combination hdiv
  have hlocal : (X - C (w i)) ^ m i ∣ P - P %ₘ M := hfactor.trans hmod
  rw [show P %ₘ M - target i =
    (P - target i) - (P - P %ₘ M) by ring]
  exact dvd_sub (hP i) hlocal

theorem real_eval_iterate_derivative_eq_of_power_linear_dvd_sub
    {B T : Polynomial ℝ} {w : ℝ} {m n : ℕ}
    (hdvd : (X - C w) ^ m ∣ B - T) (hn : n < m) :
    (derivative^[n] B).eval w = (derivative^[n] T).eval w := by
  have hpow : (X - C w) ^ (m - n) ∣ derivative^[n] (B - T) :=
    pow_sub_dvd_iterate_derivative_of_pow_dvd n hdvd
  have hmn : m - n ≠ 0 := Nat.sub_ne_zero_of_lt hn
  have hlin : X - C w ∣ derivative^[n] (B - T) :=
    (dvd_pow_self (X - C w) hmn).trans hpow
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot,
    iterate_derivative_sub, eval_sub, sub_eq_zero] at hlin
  exact hlin

/-- Degree-bounded simultaneous Hermite interpolation over the real field. -/
theorem exists_real_polynomial_iterateDerivative_eval_eq_degree_lt_modulus
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → Polynomial ℝ) :
    ∃ B : Polynomial ℝ,
      B.degree < (realFiniteHermiteModulus w m).degree ∧
      ∀ i n, n < m i →
        (derivative^[n] B).eval (w i) =
          (derivative^[n] (target i)).eval (w i) := by
  obtain ⟨B, hdegree, hB⟩ :=
    exists_real_polynomial_power_linear_dvd_sub_degree_lt_modulus w hw m target
  exact ⟨B, hdegree, fun i n hn =>
    real_eval_iterate_derivative_eq_of_power_linear_dvd_sub (hB i) hn⟩

/-! ## Full-turn coefficient rows -/

/-- Real value coefficient of a four-atom full-turn multiplier. -/
def signedFourAtomFullTurnValueCoefficient
    (r a₁ a₂ a₃ a₄ : ℝ) : ℝ :=
  a₁ * (1 - r) + a₂ * (1 - r ^ (2 : ℕ)) +
    a₃ * (1 - r ^ (3 : ℕ)) + a₄ * (1 - r ^ (4 : ℕ))

/-- Real derivative charge of a four-atom full-turn multiplier. -/
def signedFourAtomFullTurnDerivativeCoefficient
    (T r a₁ a₂ a₃ a₄ : ℝ) : ℝ :=
  -T * (r * a₁ + 2 * r ^ (2 : ℕ) * a₂ +
    3 * r ^ (3 : ℕ) * a₃ + 4 * r ^ (4 : ℕ) * a₄)

/-- Three-atom literal profiles cannot carry equal nonzero reflected charge off center. -/
theorem signedThreeAtom_literalReflection_equalCharge_zero
    {T r a₁ a₂ a₃ m : ℝ}
    (hT : T ≠ 0) (hrpos : 0 < r) (hr1 : r ≠ 1)
    (hvaluePlus :
      signedThreeAtomFullTurnValue r a₁ a₂ a₃ = 0)
    (hvalueMinus :
      signedThreeAtomFullTurnValue r⁻¹ a₁ a₂ a₃ = 0)
    (hchargePlus :
      signedThreeAtomFullTurnDerivative T r a₁ a₂ a₃ = I * (m : ℂ))
    (hchargeMinus :
      signedThreeAtomFullTurnDerivative T r⁻¹ a₁ a₂ a₃ = I * (m : ℂ)) :
    m = 0 := by
  have hr0 : r ≠ 0 := hrpos.ne'
  have hrInv1 : r⁻¹ ≠ 1 := inv_ne_one.mpr hr1
  have hrInv : r ≠ r⁻¹ := by
    intro h
    have hmul := congrArg (fun x : ℝ => x * r) h
    simp only [inv_mul_cancel₀ hr0] at hmul
    have hfac : (r - 1) * (r + 1) = 0 := by
      calc
        _ = r * r - 1 := by ring
        _ = 0 := by rw [hmul]; ring
    rcases mul_eq_zero.mp hfac with hminus | hplus
    · exact hr1 (sub_eq_zero.mp hminus)
    · nlinarith
  have hplus :
      a₁ + (1 + r) * a₂ + (1 + r + r ^ (2 : ℕ)) * a₃ = 0 := by
    have hfac :
        (1 - r) *
          (a₁ + (1 + r) * a₂ + (1 + r + r ^ (2 : ℕ)) * a₃) = 0 := by
      have hre := congrArg Complex.re hvaluePlus
      simp only [signedThreeAtomFullTurnValue, signedThreeAtomFullTurnCoefficient,
        zero_re] at hre
      calc
        _ = a₁ * (1 - r) + a₂ * (1 - r ^ (2 : ℕ)) +
            a₃ * (1 - r ^ (3 : ℕ)) := by ring
        _ = 0 := by simpa only [pow_one] using hre
    exact (mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr hr1.symm)
  have hminus :
      a₁ + (1 + r⁻¹) * a₂ + (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ)) * a₃ = 0 := by
    have hfac :
        (1 - r⁻¹) *
          (a₁ + (1 + r⁻¹) * a₂ +
            (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ)) * a₃) = 0 := by
      have hre := congrArg Complex.re hvalueMinus
      simp only [signedThreeAtomFullTurnValue, signedThreeAtomFullTurnCoefficient,
        zero_re] at hre
      calc
        _ = a₁ * (1 - r⁻¹) + a₂ * (1 - (r⁻¹) ^ (2 : ℕ)) +
            a₃ * (1 - (r⁻¹) ^ (3 : ℕ)) := by ring
        _ = 0 := by simpa only [pow_one] using hre
    exact (mul_eq_zero.mp hfac).resolve_left
      (sub_ne_zero.mpr hrInv1.symm)
  have hb₂ : a₂ = -(1 + r + r⁻¹) * a₃ := by
    have hfac :
        (r - r⁻¹) * (a₂ + (1 + r + r⁻¹) * a₃) = 0 := by
      calc
        _ = (a₁ + (1 + r) * a₂ + (1 + r + r ^ (2 : ℕ)) * a₃) -
            (a₁ + (1 + r⁻¹) * a₂ +
              (1 + r⁻¹ + (r⁻¹) ^ (2 : ℕ)) * a₃) := by
              field_simp [hr0]
              all_goals ring
        _ = 0 := by rw [hplus, hminus, sub_zero]
    have hsum := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hrInv)
    linarith
  have hb₁ : a₁ = (1 + r + r⁻¹) * a₃ := by
    rw [hb₂] at hplus
    field_simp [hr0] at hplus
    field_simp [hr0]
    nlinarith
  have hdplus :
      signedThreeAtomFullTurnDerivative T r a₁ a₂ a₃ =
        ⟨0, -T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃⟩ := by
    rw [hb₁, hb₂]
    apply Complex.ext
    · simp [signedThreeAtomFullTurnDerivative]
    · simp [signedThreeAtomFullTurnDerivative]
      field_simp [hr0]
      all_goals ring
  have hdminus :
      signedThreeAtomFullTurnDerivative T r⁻¹ a₁ a₂ a₃ =
        ⟨0, (-T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃) / r ^ (3 : ℕ)⟩ := by
    rw [hb₁, hb₂]
    apply Complex.ext
    · simp [signedThreeAtomFullTurnDerivative]
    · simp [signedThreeAtomFullTurnDerivative]
      field_simp [hr0]
      all_goals ring
  have heq :
      -T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃ =
        (-T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃) / r ^ (3 : ℕ) := by
    have hp := congrArg Complex.im hchargePlus
    have hm := congrArg Complex.im hchargeMinus
    rw [hdplus] at hp
    rw [hdminus] at hm
    norm_num [Complex.mul_im] at hp hm
    convert hp.trans hm.symm using 1 <;> ring
  have hr3 : r ^ (3 : ℕ) ≠ 1 := by
    intro h
    have hfac : (r - 1) * (r ^ (2 : ℕ) + r + 1) = 0 := by
      calc
        _ = r ^ (3 : ℕ) - 1 := by ring
        _ = 0 := by rw [h]; ring
    have hpos : 0 < r ^ (2 : ℕ) + r + 1 := by positivity
    exact hr1 (sub_eq_zero.mp
      ((mul_eq_zero.mp hfac).resolve_right hpos.ne'))
  have hzero : -T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃ = 0 := by
    have heq' :
        (-T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃) * r ^ (3 : ℕ) =
          -T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃ := by
      calc
        _ = ((-T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃) / r ^ (3 : ℕ)) *
            r ^ (3 : ℕ) := congrArg (fun x : ℝ => x * r ^ (3 : ℕ)) heq
        _ = _ := div_mul_cancel₀ _ (pow_ne_zero 3 hr0)
    have hfac :
        (-T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃) * (r ^ (3 : ℕ) - 1) = 0 := by
      calc
        _ = (-T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃) * r ^ (3 : ℕ) -
            (-T * (1 - r) * (1 - r ^ (2 : ℕ)) * a₃) := by ring
        _ = 0 := sub_eq_zero.mpr heq'
    exact (mul_eq_zero.mp hfac).resolve_right (sub_ne_zero.mpr hr3)
  have hr2 : r ^ (2 : ℕ) ≠ 1 := by
    intro h
    have hfac : (r - 1) * (r + 1) = 0 := by
      calc
        _ = r ^ (2 : ℕ) - 1 := by ring
        _ = 0 := by rw [h]; ring
    have hpos : 0 < r + 1 := by positivity
    exact hr1 (sub_eq_zero.mp
      ((mul_eq_zero.mp hfac).resolve_right hpos.ne'))
  have ha₃ : a₃ = 0 := by
    have hcoeff :
        -T * (1 - r) * (1 - r ^ (2 : ℕ)) ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero (neg_ne_zero.mpr hT)
          (sub_ne_zero.mpr hr1.symm))
        (sub_ne_zero.mpr hr2.symm)
    exact (mul_eq_zero.mp hzero).resolve_left hcoeff
  have hp := congrArg Complex.im hchargePlus
  rw [hdplus, ha₃] at hp
  norm_num [Complex.mul_im] at hp
  exact hp.symm

/-! ## Explicit common four-atom ray -/

/-- Fourth root selected by equality of the two reciprocal derivative charges. -/
def signedFourAtomLiteralAuxRoot (r : ℝ) : ℝ :=
  (1 + r + r ^ (2 : ℕ) + r ^ (3 : ℕ) + r ^ (4 : ℕ)) /
    (r * (1 + r + r ^ (2 : ℕ)))

def signedFourAtomLiteralRootSum (r : ℝ) : ℝ :=
  1 + r + r⁻¹

def signedFourAtomLiteralRayOne (r : ℝ) : ℝ :=
  1 + signedFourAtomLiteralAuxRoot r *
    signedFourAtomLiteralRootSum r

def signedFourAtomLiteralRayTwo (r : ℝ) : ℝ :=
  -signedFourAtomLiteralRootSum r *
    (1 + signedFourAtomLiteralAuxRoot r)

def signedFourAtomLiteralRayThree (r : ℝ) : ℝ :=
  signedFourAtomLiteralRootSum r + signedFourAtomLiteralAuxRoot r

def signedFourAtomLiteralRayFour (_r : ℝ) : ℝ :=
  -1

/-- Common nonzero derivative charge of the literal four-atom ray. -/
def signedFourAtomLiteralRayCharge (T r : ℝ) : ℝ :=
  -T * (r - 1) ^ (2 : ℕ) * (r + 1) ^ (2 : ℕ) /
    (r * (1 + r + r ^ (2 : ℕ)))

private theorem signedFourAtomLiteral_denominator_pos
    {r : ℝ} (hr : 0 < r) :
    0 < r * (1 + r + r ^ (2 : ℕ)) := by positivity

theorem signedFourAtomLiteralRay_value_plus
    {r : ℝ} (hr : 0 < r) :
    signedFourAtomFullTurnValueCoefficient r
      (signedFourAtomLiteralRayOne r)
      (signedFourAtomLiteralRayTwo r)
      (signedFourAtomLiteralRayThree r)
      (signedFourAtomLiteralRayFour r) = 0 := by
  have hr0 := hr.ne'
  have hden := (signedFourAtomLiteral_denominator_pos hr).ne'
  unfold signedFourAtomFullTurnValueCoefficient
    signedFourAtomLiteralRayOne signedFourAtomLiteralRayTwo
    signedFourAtomLiteralRayThree signedFourAtomLiteralRayFour
    signedFourAtomLiteralRootSum signedFourAtomLiteralAuxRoot
  field_simp [hr0, hden]
  all_goals ring

theorem signedFourAtomLiteralRay_value_minus
    {r : ℝ} (hr : 0 < r) :
    signedFourAtomFullTurnValueCoefficient r⁻¹
      (signedFourAtomLiteralRayOne r)
      (signedFourAtomLiteralRayTwo r)
      (signedFourAtomLiteralRayThree r)
      (signedFourAtomLiteralRayFour r) = 0 := by
  have hr0 := hr.ne'
  have hden := (signedFourAtomLiteral_denominator_pos hr).ne'
  unfold signedFourAtomFullTurnValueCoefficient
    signedFourAtomLiteralRayOne signedFourAtomLiteralRayTwo
    signedFourAtomLiteralRayThree signedFourAtomLiteralRayFour
    signedFourAtomLiteralRootSum signedFourAtomLiteralAuxRoot
  field_simp [hr0, hden]
  all_goals ring

theorem signedFourAtomLiteralRay_derivative_plus
    {T r : ℝ} (hr : 0 < r) :
    signedFourAtomFullTurnDerivativeCoefficient T r
      (signedFourAtomLiteralRayOne r)
      (signedFourAtomLiteralRayTwo r)
      (signedFourAtomLiteralRayThree r)
      (signedFourAtomLiteralRayFour r) =
        signedFourAtomLiteralRayCharge T r := by
  have hr0 := hr.ne'
  have hden := (signedFourAtomLiteral_denominator_pos hr).ne'
  unfold signedFourAtomFullTurnDerivativeCoefficient
    signedFourAtomLiteralRayOne signedFourAtomLiteralRayTwo
    signedFourAtomLiteralRayThree signedFourAtomLiteralRayFour
    signedFourAtomLiteralRootSum signedFourAtomLiteralAuxRoot
    signedFourAtomLiteralRayCharge
  field_simp [hr0, hden]
  all_goals ring

theorem signedFourAtomLiteralRay_derivative_minus
    {T r : ℝ} (hr : 0 < r) :
    signedFourAtomFullTurnDerivativeCoefficient T r⁻¹
      (signedFourAtomLiteralRayOne r)
      (signedFourAtomLiteralRayTwo r)
      (signedFourAtomLiteralRayThree r)
      (signedFourAtomLiteralRayFour r) =
        signedFourAtomLiteralRayCharge T r := by
  have hr0 := hr.ne'
  have hden := (signedFourAtomLiteral_denominator_pos hr).ne'
  unfold signedFourAtomFullTurnDerivativeCoefficient
    signedFourAtomLiteralRayOne signedFourAtomLiteralRayTwo
    signedFourAtomLiteralRayThree signedFourAtomLiteralRayFour
    signedFourAtomLiteralRootSum signedFourAtomLiteralAuxRoot
    signedFourAtomLiteralRayCharge
  field_simp [hr0, hden]
  all_goals ring

theorem signedFourAtomLiteralRayCharge_ne_zero
    {T r : ℝ} (hT : T ≠ 0) (hr : 0 < r) (hr1 : r ≠ 1) :
    signedFourAtomLiteralRayCharge T r ≠ 0 := by
  have hr0 := hr.ne'
  have hrp1 : r + 1 ≠ 0 := by positivity
  have hden := (signedFourAtomLiteral_denominator_pos hr).ne'
  unfold signedFourAtomLiteralRayCharge
  exact div_ne_zero
    (mul_ne_zero
      (mul_ne_zero (neg_ne_zero.mpr hT)
        (pow_ne_zero 2 (sub_ne_zero.mpr hr1)))
      (pow_ne_zero 2 hrp1))
    hden

/-! ## One bounded Hermite correction at both fibres -/

def signedFourAtomLiteralHermiteNode (r : ℝ) : Fin 3 → ℝ :=
  ![1, r, r⁻¹]

def signedFourAtomLiteralHermiteMultiplicity : Fin 3 → ℕ :=
  ![1, 2, 2]

def signedFourAtomLiteralHermiteTarget
    (T r ηp ηm : ℝ) : Fin 3 → Polynomial ℝ :=
  ![0,
    C 1 + C (ηp / (T * r)) * (X - C r),
    C 1 + C (ηm / (T * r⁻¹)) * (X - C r⁻¹)]

private theorem signedFourAtomLiteralHermiteNode_injective
    {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    Function.Injective (signedFourAtomLiteralHermiteNode r) := by
  have hr0 := hr.ne'
  have hi1 : r⁻¹ ≠ 1 := inv_ne_one.mpr hr1
  have hri : r ≠ r⁻¹ := by
    intro h
    have hmul := congrArg (fun x : ℝ => x * r) h
    simp only [inv_mul_cancel₀ hr0] at hmul
    have hfac : (r - 1) * (r + 1) = 0 := by
      calc
        _ = r * r - 1 := by ring
        _ = 0 := by rw [hmul]; ring
    rcases mul_eq_zero.mp hfac with hm | hp
    · exact hr1 (sub_eq_zero.mp hm)
    · nlinarith
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [signedFourAtomLiteralHermiteNode]

theorem signedFourAtomLiteralHermiteModulus_natDegree (r : ℝ) :
    (realFiniteHermiteModulus
      (signedFourAtomLiteralHermiteNode r)
      signedFourAtomLiteralHermiteMultiplicity).natDegree = 5 := by
  unfold realFiniteHermiteModulus
  rw [Polynomial.natDegree_prod]
  · norm_num [signedFourAtomLiteralHermiteMultiplicity,
      Polynomial.natDegree_pow, Fin.sum_univ_succ]
  · intro i hi
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)

theorem signedFourAtomLiteralHermiteModulus_degree (r : ℝ) :
    (realFiniteHermiteModulus
      (signedFourAtomLiteralHermiteNode r)
      signedFourAtomLiteralHermiteMultiplicity).degree = 5 := by
  rw [Polynomial.degree_eq_natDegree
    (realFiniteHermiteModulus_monic
      (signedFourAtomLiteralHermiteNode r)
      signedFourAtomLiteralHermiteMultiplicity).ne_zero]
  norm_cast
  exact signedFourAtomLiteralHermiteModulus_natDegree r

/-- Real degree-four Hermite correction imposing both reflected values and derivatives. -/
theorem exists_signedFourAtomLiteralCorrectionPolynomial
    {T r ηp ηm : ℝ} (hT : T ≠ 0) (hr : 0 < r) (hr1 : r ≠ 1) :
    ∃ Q : Polynomial ℝ,
      Q.natDegree < 5 ∧
      Q.eval 1 = 0 ∧
      Q.eval r = 1 ∧
      Q.derivative.eval r = ηp / (T * r) ∧
      Q.eval r⁻¹ = 1 ∧
      Q.derivative.eval r⁻¹ = ηm / (T * r⁻¹) := by
  have _hT := hT
  obtain ⟨Q, hdegree, hQ⟩ :=
    exists_real_polynomial_iterateDerivative_eval_eq_degree_lt_modulus
      (signedFourAtomLiteralHermiteNode r)
      (signedFourAtomLiteralHermiteNode_injective hr hr1)
      signedFourAtomLiteralHermiteMultiplicity
      (signedFourAtomLiteralHermiteTarget T r ηp ηm)
  have hnat : Q.natDegree < 5 := by
    by_cases hzero : Q = 0
    · simp [hzero]
    · apply (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr
      simpa [signedFourAtomLiteralHermiteModulus_degree] using hdegree
  have h0 := hQ (0 : Fin 3) 0 (by
    simp [signedFourAtomLiteralHermiteMultiplicity])
  have hr0 := hQ (1 : Fin 3) 0 (by
    simp [signedFourAtomLiteralHermiteMultiplicity])
  have hr1d := hQ (1 : Fin 3) 1 (by
    simp [signedFourAtomLiteralHermiteMultiplicity])
  have hi0 := hQ (2 : Fin 3) 0 (by
    simp [signedFourAtomLiteralHermiteMultiplicity])
  have hi1d := hQ (2 : Fin 3) 1 (by
    simp [signedFourAtomLiteralHermiteMultiplicity])
  refine ⟨Q, hnat, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [signedFourAtomLiteralHermiteNode,
      signedFourAtomLiteralHermiteTarget] using h0
  · simpa [signedFourAtomLiteralHermiteNode,
      signedFourAtomLiteralHermiteTarget] using hr0
  · simpa [signedFourAtomLiteralHermiteNode,
      signedFourAtomLiteralHermiteTarget] using hr1d
  · simpa [signedFourAtomLiteralHermiteNode,
      signedFourAtomLiteralHermiteTarget] using hi0
  · simpa [signedFourAtomLiteralHermiteNode,
      signedFourAtomLiteralHermiteTarget] using hi1d

private theorem polynomial_eq_coeffs_zero_to_four
    {Q : Polynomial ℝ} (hdegree : Q.natDegree < 5) :
    Q =
      C (Q.coeff 0) +
      C (Q.coeff 1) * X +
      C (Q.coeff 2) * X ^ (2 : ℕ) +
      C (Q.coeff 3) * X ^ (3 : ℕ) +
      C (Q.coeff 4) * X ^ (4 : ℕ) := by
  simpa [Finset.sum_range_succ, add_assoc] using
    Q.as_sum_range_C_mul_X_pow' hdegree

private theorem polynomial_constant_eq_neg_sum_coeff_one_to_four
    {Q : Polynomial ℝ} (hdegree : Q.natDegree < 5)
    (hone : Q.eval 1 = 0) :
    Q.coeff 0 =
      -(Q.coeff 1 + Q.coeff 2 + Q.coeff 3 + Q.coeff 4) := by
  rw [polynomial_eq_coeffs_zero_to_four hdegree] at hone
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, one_pow, mul_one] at hone
  linarith

theorem signedFourAtomFullTurnValueCoefficient_of_polynomial
    {Q : Polynomial ℝ} (hdegree : Q.natDegree < 5)
    (hone : Q.eval 1 = 0) (x : ℝ) :
    signedFourAtomFullTurnValueCoefficient x
      (-Q.coeff 1) (-Q.coeff 2) (-Q.coeff 3) (-Q.coeff 4) =
        Q.eval x := by
  have hconstant :=
    polynomial_constant_eq_neg_sum_coeff_one_to_four hdegree hone
  have hQ := polynomial_eq_coeffs_zero_to_four hdegree
  conv_rhs => rw [hQ]
  simp only [signedFourAtomFullTurnValueCoefficient,
    eval_add, eval_mul, eval_C, eval_X, eval_pow]
  rw [hconstant]
  ring

theorem signedFourAtomFullTurnDerivativeCoefficient_of_polynomial
    {Q : Polynomial ℝ} (hdegree : Q.natDegree < 5)
    (T x : ℝ) :
    signedFourAtomFullTurnDerivativeCoefficient T x
      (-Q.coeff 1) (-Q.coeff 2) (-Q.coeff 3) (-Q.coeff 4) =
        T * x * Q.derivative.eval x := by
  have hQ := polynomial_eq_coeffs_zero_to_four hdegree
  conv_rhs => rw [hQ]
  simp only [signedFourAtomFullTurnDerivativeCoefficient,
    derivative_add, derivative_mul, derivative_C, derivative_X,
    derivative_pow, eval_add, eval_mul, eval_C, eval_X, eval_pow,
    eval_one, zero_mul, zero_add, Nat.cast_ofNat]
  ring

/-- One real four-vector supplies arbitrary bounded value/derivative corrections at both fibres. -/
theorem exists_signedFourAtomLiteralCorrection
    {T r ηp ηm : ℝ} (hT : T ≠ 0) (hr : 0 < r) (hr1 : r ≠ 1) :
    ∃ v₁ v₂ v₃ v₄ : ℝ,
      signedFourAtomFullTurnValueCoefficient r v₁ v₂ v₃ v₄ = 1 ∧
      signedFourAtomFullTurnValueCoefficient r⁻¹ v₁ v₂ v₃ v₄ = 1 ∧
      signedFourAtomFullTurnDerivativeCoefficient T r v₁ v₂ v₃ v₄ = ηp ∧
      signedFourAtomFullTurnDerivativeCoefficient T r⁻¹ v₁ v₂ v₃ v₄ = ηm := by
  obtain ⟨Q, hdegree, hone, hvr, hdr, hvi, hdi⟩ :=
    exists_signedFourAtomLiteralCorrectionPolynomial
      (ηp := ηp) (ηm := ηm) hT hr hr1
  refine ⟨-Q.coeff 1, -Q.coeff 2, -Q.coeff 3, -Q.coeff 4,
    ?_, ?_, ?_, ?_⟩
  · rw [signedFourAtomFullTurnValueCoefficient_of_polynomial hdegree hone, hvr]
  · rw [signedFourAtomFullTurnValueCoefficient_of_polynomial hdegree hone, hvi]
  · rw [signedFourAtomFullTurnDerivativeCoefficient_of_polynomial hdegree, hdr]
    field_simp [hT, hr.ne']
  · rw [signedFourAtomFullTurnDerivativeCoefficient_of_polynomial hdegree, hdi]
    field_simp [hT, hr.ne']

/-- The singular four-atom ray plus one common bounded correction gives exact equal reflected
value and derivative data. -/
theorem exists_signedFourAtomLiteralExactCoefficientPair
    {T r δ ηp ηm : ℝ}
    (hT : T ≠ 0) (hr : 0 < r) (hr1 : r ≠ 1) (_hδ : δ ≠ 0) :
    ∃ a₁ a₂ a₃ a₄ : ℝ,
      signedFourAtomFullTurnValueCoefficient r a₁ a₂ a₃ a₄ = 1 ∧
      signedFourAtomFullTurnValueCoefficient r⁻¹ a₁ a₂ a₃ a₄ = 1 ∧
      signedFourAtomFullTurnDerivativeCoefficient T r a₁ a₂ a₃ a₄ =
        1 / δ + ηp ∧
      signedFourAtomFullTurnDerivativeCoefficient T r⁻¹ a₁ a₂ a₃ a₄ =
        1 / δ + ηm := by
  obtain ⟨v₁, v₂, v₃, v₄, hvp, hvm, hdp, hdm⟩ :=
    exists_signedFourAtomLiteralCorrection
      (ηp := ηp) (ηm := ηm) hT hr hr1
  let M := signedFourAtomLiteralRayCharge T r
  have hM : M ≠ 0 :=
    signedFourAtomLiteralRayCharge_ne_zero hT hr hr1
  refine ⟨
    signedFourAtomLiteralRayOne r / M / δ + v₁,
    signedFourAtomLiteralRayTwo r / M / δ + v₂,
    signedFourAtomLiteralRayThree r / M / δ + v₃,
    signedFourAtomLiteralRayFour r / M / δ + v₄,
    ?_, ?_, ?_, ?_⟩
  · rw [show signedFourAtomFullTurnValueCoefficient r
        (signedFourAtomLiteralRayOne r / M / δ + v₁)
        (signedFourAtomLiteralRayTwo r / M / δ + v₂)
        (signedFourAtomLiteralRayThree r / M / δ + v₃)
        (signedFourAtomLiteralRayFour r / M / δ + v₄) =
      signedFourAtomFullTurnValueCoefficient r
          (signedFourAtomLiteralRayOne r)
          (signedFourAtomLiteralRayTwo r)
          (signedFourAtomLiteralRayThree r)
          (signedFourAtomLiteralRayFour r) / M / δ +
        signedFourAtomFullTurnValueCoefficient r v₁ v₂ v₃ v₄ by
      unfold signedFourAtomFullTurnValueCoefficient
      ring]
    rw [signedFourAtomLiteralRay_value_plus hr, hvp]
    ring
  · rw [show signedFourAtomFullTurnValueCoefficient r⁻¹
        (signedFourAtomLiteralRayOne r / M / δ + v₁)
        (signedFourAtomLiteralRayTwo r / M / δ + v₂)
        (signedFourAtomLiteralRayThree r / M / δ + v₃)
        (signedFourAtomLiteralRayFour r / M / δ + v₄) =
      signedFourAtomFullTurnValueCoefficient r⁻¹
          (signedFourAtomLiteralRayOne r)
          (signedFourAtomLiteralRayTwo r)
          (signedFourAtomLiteralRayThree r)
          (signedFourAtomLiteralRayFour r) / M / δ +
        signedFourAtomFullTurnValueCoefficient r⁻¹ v₁ v₂ v₃ v₄ by
      unfold signedFourAtomFullTurnValueCoefficient
      ring]
    rw [signedFourAtomLiteralRay_value_minus hr, hvm]
    ring
  · rw [show signedFourAtomFullTurnDerivativeCoefficient T r
        (signedFourAtomLiteralRayOne r / M / δ + v₁)
        (signedFourAtomLiteralRayTwo r / M / δ + v₂)
        (signedFourAtomLiteralRayThree r / M / δ + v₃)
        (signedFourAtomLiteralRayFour r / M / δ + v₄) =
      signedFourAtomFullTurnDerivativeCoefficient T r
          (signedFourAtomLiteralRayOne r)
          (signedFourAtomLiteralRayTwo r)
          (signedFourAtomLiteralRayThree r)
          (signedFourAtomLiteralRayFour r) / M / δ +
        signedFourAtomFullTurnDerivativeCoefficient T r v₁ v₂ v₃ v₄ by
      unfold signedFourAtomFullTurnDerivativeCoefficient
      ring]
    rw [signedFourAtomLiteralRay_derivative_plus hr, hdp]
    change M / M / δ + ηp = 1 / δ + ηp
    rw [div_self hM]
  · rw [show signedFourAtomFullTurnDerivativeCoefficient T r⁻¹
        (signedFourAtomLiteralRayOne r / M / δ + v₁)
        (signedFourAtomLiteralRayTwo r / M / δ + v₂)
        (signedFourAtomLiteralRayThree r / M / δ + v₃)
        (signedFourAtomLiteralRayFour r / M / δ + v₄) =
      signedFourAtomFullTurnDerivativeCoefficient T r⁻¹
          (signedFourAtomLiteralRayOne r)
          (signedFourAtomLiteralRayTwo r)
          (signedFourAtomLiteralRayThree r)
          (signedFourAtomLiteralRayFour r) / M / δ +
        signedFourAtomFullTurnDerivativeCoefficient T r⁻¹ v₁ v₂ v₃ v₄ by
      unfold signedFourAtomFullTurnDerivativeCoefficient
      ring]
    rw [signedFourAtomLiteralRay_derivative_minus hr, hdm]
    change M / M / δ + ηm = 1 / δ + ηm
    rw [div_self hM]

/-- Coordinatewise singular-plus-bounded normalization for the common four-atom profile. -/
theorem tendsto_signedFourAtomLiteralScaledWeight
    {δ : ℕ → ℝ} (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hδne : ∀ n, δ n ≠ 0) (T r b v : ℝ) :
    Filter.Tendsto
      (fun n => δ n *
        (b / signedFourAtomLiteralRayCharge T r / δ n + v))
      Filter.atTop
      (nhds (b / signedFourAtomLiteralRayCharge T r)) := by
  simpa only [div_div] using
    tendsto_scaledSingular_plus_bounded hδ hδne
      (b / signedFourAtomLiteralRayCharge T r) v

/-- All four coordinates of one literal profile converge to the normalized common ray. -/
theorem tendsto_signedFourAtomLiteralNormalizedWeights
    {δ : ℕ → ℝ} (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hδne : ∀ n, δ n ≠ 0) (T r v₁ v₂ v₃ v₄ : ℝ) :
    Filter.Tendsto
        (fun n => δ n *
          (signedFourAtomLiteralRayOne r /
            signedFourAtomLiteralRayCharge T r / δ n + v₁))
        Filter.atTop
        (nhds (signedFourAtomLiteralRayOne r /
          signedFourAtomLiteralRayCharge T r)) ∧
      Filter.Tendsto
        (fun n => δ n *
          (signedFourAtomLiteralRayTwo r /
            signedFourAtomLiteralRayCharge T r / δ n + v₂))
        Filter.atTop
        (nhds (signedFourAtomLiteralRayTwo r /
          signedFourAtomLiteralRayCharge T r)) ∧
      Filter.Tendsto
        (fun n => δ n *
          (signedFourAtomLiteralRayThree r /
            signedFourAtomLiteralRayCharge T r / δ n + v₃))
        Filter.atTop
        (nhds (signedFourAtomLiteralRayThree r /
          signedFourAtomLiteralRayCharge T r)) ∧
      Filter.Tendsto
        (fun n => δ n *
          (signedFourAtomLiteralRayFour r /
            signedFourAtomLiteralRayCharge T r / δ n + v₄))
        Filter.atTop
        (nhds (signedFourAtomLiteralRayFour r /
          signedFourAtomLiteralRayCharge T r)) := by
  exact ⟨
    tendsto_signedFourAtomLiteralScaledWeight hδ hδne T r
      (signedFourAtomLiteralRayOne r) v₁,
    tendsto_signedFourAtomLiteralScaledWeight hδ hδne T r
      (signedFourAtomLiteralRayTwo r) v₂,
    tendsto_signedFourAtomLiteralScaledWeight hδ hδne T r
      (signedFourAtomLiteralRayThree r) v₃,
    tendsto_signedFourAtomLiteralScaledWeight hδ hδne T r
      (signedFourAtomLiteralRayFour r) v₄⟩

/-! ## Exact full-turn analytic source pair -/

theorem signedFourAtomCompletion_of_fullTurnPhases
    {T r a₁ a₂ a₃ a₄ : ℝ} {z : ℂ}
    (h₁ : spectralTranslationPhase T z = (r : ℂ))
    (h₂ : spectralTranslationPhase (2 * T) z = (r : ℂ) ^ (2 : ℕ))
    (h₃ : spectralTranslationPhase (3 * T) z = (r : ℂ) ^ (3 : ℕ))
    (h₄ : spectralTranslationPhase (4 * T) z = (r : ℂ) ^ (4 : ℕ)) :
    signedFourAtomCompletion T a₁ a₂ a₃ a₄ z =
      (signedFourAtomFullTurnValueCoefficient r a₁ a₂ a₃ a₄ : ℂ) := by
  rw [signedFourAtomCompletion, h₁, h₂, h₃, h₄]
  apply Complex.ext
  · norm_num [signedFourAtomFullTurnValueCoefficient,
      Complex.mul_re, pow_succ]
  · norm_num [signedFourAtomFullTurnValueCoefficient,
      Complex.mul_im, pow_succ]

theorem signedFourAtomCompletionDerivative_of_fullTurnPhases
    {T r a₁ a₂ a₃ a₄ : ℝ} {z : ℂ}
    (h₁ : spectralTranslationPhase T z = (r : ℂ))
    (h₂ : spectralTranslationPhase (2 * T) z = (r : ℂ) ^ (2 : ℕ))
    (h₃ : spectralTranslationPhase (3 * T) z = (r : ℂ) ^ (3 : ℕ))
    (h₄ : spectralTranslationPhase (4 * T) z = (r : ℂ) ^ (4 : ℕ)) :
    signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄ z =
      I * (signedFourAtomFullTurnDerivativeCoefficient
        T r a₁ a₂ a₃ a₄ : ℂ) := by
  rw [signedFourAtomCompletionDerivative, h₁, h₂, h₃, h₄]
  apply Complex.ext
  · norm_num [signedFourAtomFullTurnDerivativeCoefficient,
      Complex.mul_re, pow_succ]
  · norm_num [signedFourAtomFullTurnDerivativeCoefficient,
      Complex.mul_im, pow_succ]
    ring

theorem signedFourAtomCompletion_fullTurn_eq
    {T : ℝ} (hT : T ≠ 0) (y a₁ a₂ a₃ a₄ : ℝ) :
    signedFourAtomCompletion T a₁ a₂ a₃ a₄
        (signedThreeAtomFullTurnPoint T y) =
      (signedFourAtomFullTurnValueCoefficient
        (Real.exp (-T * y)) a₁ a₂ a₃ a₄ : ℂ) := by
  have hbase := spectralTranslationPhase_fullTurn hT y
  have htwo :
      spectralTranslationPhase (2 * T)
          (signedThreeAtomFullTurnPoint T y) =
        (Real.exp (-T * y) : ℂ) ^ (2 : ℕ) := by
    calc
      _ = spectralTranslationPhase T
          (signedThreeAtomFullTurnPoint T y) ^ (2 : ℕ) := by
        simpa using spectralTranslationPhase_nat_mul 2 T
          (signedThreeAtomFullTurnPoint T y)
      _ = _ := by rw [hbase]
  have hthree :
      spectralTranslationPhase (3 * T)
          (signedThreeAtomFullTurnPoint T y) =
        (Real.exp (-T * y) : ℂ) ^ (3 : ℕ) := by
    calc
      _ = spectralTranslationPhase T
          (signedThreeAtomFullTurnPoint T y) ^ (3 : ℕ) := by
        simpa using spectralTranslationPhase_nat_mul 3 T
          (signedThreeAtomFullTurnPoint T y)
      _ = _ := by rw [hbase]
  have hfour :
      spectralTranslationPhase (4 * T)
          (signedThreeAtomFullTurnPoint T y) =
        (Real.exp (-T * y) : ℂ) ^ (4 : ℕ) := by
    calc
      _ = spectralTranslationPhase T
          (signedThreeAtomFullTurnPoint T y) ^ (4 : ℕ) := by
        simpa using spectralTranslationPhase_nat_mul 4 T
          (signedThreeAtomFullTurnPoint T y)
      _ = _ := by rw [hbase]
  exact signedFourAtomCompletion_of_fullTurnPhases
    hbase htwo hthree hfour

theorem signedFourAtomCompletionDerivative_fullTurn_eq
    {T : ℝ} (hT : T ≠ 0) (y a₁ a₂ a₃ a₄ : ℝ) :
    signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄
        (signedThreeAtomFullTurnPoint T y) =
      I * (signedFourAtomFullTurnDerivativeCoefficient
        T (Real.exp (-T * y)) a₁ a₂ a₃ a₄ : ℂ) := by
  have hbase := spectralTranslationPhase_fullTurn hT y
  have htwo :
      spectralTranslationPhase (2 * T)
          (signedThreeAtomFullTurnPoint T y) =
        (Real.exp (-T * y) : ℂ) ^ (2 : ℕ) := by
    calc
      _ = spectralTranslationPhase T
          (signedThreeAtomFullTurnPoint T y) ^ (2 : ℕ) := by
        simpa using spectralTranslationPhase_nat_mul 2 T
          (signedThreeAtomFullTurnPoint T y)
      _ = _ := by rw [hbase]
  have hthree :
      spectralTranslationPhase (3 * T)
          (signedThreeAtomFullTurnPoint T y) =
        (Real.exp (-T * y) : ℂ) ^ (3 : ℕ) := by
    calc
      _ = spectralTranslationPhase T
          (signedThreeAtomFullTurnPoint T y) ^ (3 : ℕ) := by
        simpa using spectralTranslationPhase_nat_mul 3 T
          (signedThreeAtomFullTurnPoint T y)
      _ = _ := by rw [hbase]
  have hfour :
      spectralTranslationPhase (4 * T)
          (signedThreeAtomFullTurnPoint T y) =
        (Real.exp (-T * y) : ℂ) ^ (4 : ℕ) := by
    calc
      _ = spectralTranslationPhase T
          (signedThreeAtomFullTurnPoint T y) ^ (4 : ℕ) := by
        simpa using spectralTranslationPhase_nat_mul 4 T
          (signedThreeAtomFullTurnPoint T y)
      _ = _ := by rw [hbase]
  exact signedFourAtomCompletionDerivative_of_fullTurnPhases
    hbase htwo hthree hfour

/-- Four atoms give one literal coefficient vector with exact unit source-connection charge at
both off-center reflected full-turn fibres. -/
theorem exists_signedFourAtomFullTurn_literalReflectionExactPair
    {T δ y : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hy : y ≠ 0) :
    let zp := signedThreeAtomFullTurnPoint T y
    let zm := signedThreeAtomFullTurnPoint T (-y)
    ∃ a₁ a₂ a₃ a₄ : ℝ,
      signedFourAtomCompletion T a₁ a₂ a₃ a₄ zp = 1 ∧
      signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄ zp =
        I * ((1 / δ + (1 / zp).im : ℝ) : ℂ) ∧
      δ * (atomicSourceConnectionDerivative 1
        (I * ((1 / δ + (1 / zp).im : ℝ) : ℂ)) zp /
          atomicSourceConnectionValue 1 zp).im = 1 ∧
      signedFourAtomCompletion T a₁ a₂ a₃ a₄ zm = 1 ∧
      signedFourAtomCompletionDerivative T a₁ a₂ a₃ a₄ zm =
        I * ((1 / δ + (1 / zm).im : ℝ) : ℂ) ∧
      δ * (atomicSourceConnectionDerivative 1
        (I * ((1 / δ + (1 / zm).im : ℝ) : ℂ)) zm /
          atomicSourceConnectionValue 1 zm).im = 1 := by
  dsimp only
  have hT0 := hT.ne'
  let r := Real.exp (-T * y)
  have hrpos : 0 < r := Real.exp_pos _
  have hr1 : r ≠ 1 := by
    intro hr
    dsimp only [r] at hr
    have hr' : Real.exp (-(T * y)) = 1 := by
      simpa only [neg_mul] using hr
    have harg : -(T * y) = 0 :=
      (Real.exp_eq_one_iff (-(T * y))).mp hr'
    exact hy (by nlinarith)
  let zp := signedThreeAtomFullTurnPoint T y
  let zm := signedThreeAtomFullTurnPoint T (-y)
  have hzp : zp ≠ 0 := by
    intro hz
    have hre : zp.re = 0 := by rw [hz]; rfl
    have hrePos : 0 < zp.re := by
      dsimp only [zp, signedThreeAtomFullTurnPoint]
      positivity
    linarith
  have hzm : zm ≠ 0 := by
    intro hz
    have hre : zm.re = 0 := by rw [hz]; rfl
    have hrePos : 0 < zm.re := by
      dsimp only [zm, signedThreeAtomFullTurnPoint]
      positivity
    linarith
  obtain ⟨a₁, a₂, a₃, a₄, hvp, hvm, hdp, hdm⟩ :=
    exists_signedFourAtomLiteralExactCoefficientPair
      (ηp := (1 / zp).im) (ηm := (1 / zm).im)
      hT0 hrpos hr1 hδ.ne'
  have hrminus :
      Real.exp (-T * (-y)) = r⁻¹ := by
    dsimp only [r]
    rw [show -T * -y = T * y by ring, ← Real.exp_neg]
    congr 1
    ring
  refine ⟨a₁, a₂, a₃, a₄, ?_, ?_,
    atomicSourceConnection_exactUnitScaledCharge hδ.ne' hzp,
    ?_, ?_, atomicSourceConnection_exactUnitScaledCharge hδ.ne' hzm⟩
  · rw [signedFourAtomCompletion_fullTurn_eq hT0]
    change (signedFourAtomFullTurnValueCoefficient r a₁ a₂ a₃ a₄ : ℂ) = 1
    norm_cast
  · rw [signedFourAtomCompletionDerivative_fullTurn_eq hT0]
    change I * (signedFourAtomFullTurnDerivativeCoefficient
      T r a₁ a₂ a₃ a₄ : ℂ) =
        I * ((1 / δ + (1 / zp).im : ℝ) : ℂ)
    rw [hdp]
  · rw [signedFourAtomCompletion_fullTurn_eq hT0, hrminus]
    norm_cast
  · rw [signedFourAtomCompletionDerivative_fullTurn_eq hT0, hrminus]
    change I * (signedFourAtomFullTurnDerivativeCoefficient
      T r⁻¹ a₁ a₂ a₃ a₄ : ℂ) =
        I * ((1 / δ + (1 / zm).im : ℝ) : ℂ)
    rw [hdm]

end

end RHTower
