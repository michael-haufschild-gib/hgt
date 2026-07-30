import GaloisForLFunctions.RHTower.XiPrimeSeamEulerZeroTangent
import GaloisForLFunctions.RHTower.SummableEulerCalkinInjectivity

/-!
# Higher Euler grades are Calkin-faithful to Xi orientation

The exact functional-equation-paired Lambert tail begins at prime-power grade two.  Its
coefficients are absolutely summable in the open critical strip, while the associated scales are
strictly increasing.  Summable Euler Calkin injectivity therefore shows that the additive
positive-Euler principal lift of this tail is compact exactly on the critical line.

This is a positive rigidity statement: passing from the empty Euler chart to the actual Euler
tangent does not make the higher grades invisible in the Sonin Calkin quotient.  Consequently a
future completed-product cancellation must couple grades or places; it cannot discard this
additive higher-grade tail as a compact remainder.
-/

namespace RHTower

noncomputable section

/-- Prime-power scales beginning at grade two. -/
def primeHigherPowerScale (p : Nat.Primes) (j : ℕ) : ℝ :=
  ((p : ℕ) : ℝ) ^ (j + 2)

theorem primeHigherPowerScale_one_lt (p : Nat.Primes) (j : ℕ) :
    1 < primeHigherPowerScale p j := by
  rw [primeHigherPowerScale, ← pow_zero (((p : ℕ) : ℝ))]
  exact pow_lt_pow_right₀ (by exact_mod_cast p.prop.one_lt) (by omega)

theorem primeHigherPowerScale_strictMono (p : Nat.Primes) :
    StrictMono (primeHigherPowerScale p) := by
  intro i j hij
  exact pow_lt_pow_right₀ (by exact_mod_cast p.prop.one_lt) (by omega)

/-- The exact FE-paired Lambert coefficient at prime-power grade `j + 2`. -/
def primeEulerFEHigherGradeCoefficient (p : Nat.Primes) (s : ℂ) (j : ℕ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * ((j + 2 : ℕ) : ℂ) *
    ((((p : ℕ) : ℂ) ^ (-s)) ^ (j + 2) -
      (((p : ℕ) : ℂ) ^ (-(1 - s))) ^ (j + 2))

/-- The higher-grade coefficient sequence sums to the exact FE-paired Lambert tail. -/
theorem primeEulerFEHigherGradeCoefficient_hasSum (p : Nat.Primes) {s : ℂ}
    (hstrip : 0 < s.re ∧ s.re < 1) :
    HasSum (primeEulerFEHigherGradeCoefficient p s)
      (primeEulerUnitFEHigherTail (p : ℕ) s) := by
  have hleft := primeEulerUnitTangentHigherTail_hasSum p.prop.two_le hstrip.1
  have hright := primeEulerUnitTangentHigherTail_hasSum p.prop.two_le (s := 1 - s) (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith)
  have hcoeff :
      primeEulerFEHigherGradeCoefficient p s =
        fun j =>
          (Real.log (p : ℝ) : ℂ) * ((j + 2 : ℕ) : ℂ) *
              ((((p : ℕ) : ℂ) ^ (-s)) ^ (j + 2)) -
            (Real.log (p : ℝ) : ℂ) * ((j + 2 : ℕ) : ℂ) *
              ((((p : ℕ) : ℂ) ^ (-(1 - s))) ^ (j + 2)) := by
    funext j
    simp only [primeEulerFEHigherGradeCoefficient]
    ring
  rw [hcoeff, primeEulerUnitFEHigherTail]
  exact hleft.sub hright

/-- Absolute summability of the exact FE-paired higher-grade coefficients. -/
theorem summable_norm_primeEulerFEHigherGradeCoefficient (p : Nat.Primes) {s : ℂ}
    (hstrip : 0 < s.re ∧ s.re < 1) :
    Summable fun j => ‖primeEulerFEHigherGradeCoefficient p s j‖ :=
  (primeEulerFEHigherGradeCoefficient_hasSum p hstrip).summable.norm

theorem primeEulerFEHigherGradeCoefficient_zero_of_re_eq_half
    (p : Nat.Primes) {sigma : ℝ} (hhalf : sigma = 1 / 2) (j : ℕ) :
    primeEulerFEHigherGradeCoefficient p (sigma : ℂ) j = 0 := by
  subst sigma
  have hexp :
      -(((1 / 2 : ℝ) : ℂ)) = -(1 - (((1 / 2 : ℝ) : ℂ))) := by norm_num
  rw [primeEulerFEHigherGradeCoefficient, hexp, sub_self, mul_zero]

/-- Off the critical line, already the grade-two coefficient is nonzero. -/
theorem primeEulerFEHigherGradeCoefficient_ne_zero_of_re_ne_half
    (p : Nat.Primes) {sigma : ℝ} (hne : sigma ≠ 1 / 2) :
    primeEulerFEHigherGradeCoefficient p (sigma : ℂ) 0 ≠ 0 := by
  intro hzero
  have hlog : (Real.log (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  have hdiff :
      (((p : ℕ) : ℂ) ^ (-(sigma : ℂ))) ^ 2 =
        (((p : ℕ) : ℂ) ^ (-(1 - (sigma : ℂ)))) ^ 2 := by
    have hz :
        (((p : ℕ) : ℂ) ^ (-(sigma : ℂ))) ^ 2 -
          (((p : ℕ) : ℂ) ^ (-(1 - (sigma : ℂ)))) ^ 2 = 0 := by
      have hm := mul_eq_zero.mp hzero
      exact hm.resolve_left (mul_ne_zero hlog (by norm_num))
    exact sub_eq_zero.mp hz
  have hnorm := congrArg norm hdiff
  rw [norm_pow, norm_pow] at hnorm
  change
    ‖((((p : ℕ) : ℝ) : ℂ) ^ (-((sigma : ℝ) : ℂ)))‖ ^ 2 =
      ‖((((p : ℕ) : ℝ) : ℂ) ^ (-(1 - ((sigma : ℝ) : ℂ))))‖ ^ 2 at hnorm
  rw [
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast p.prop.pos),
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast p.prop.pos)] at hnorm
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.sub_re, Complex.one_re] at hnorm
  have hposLeft : 0 < (p : ℝ) ^ (-sigma) :=
    Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have hposRight : 0 < (p : ℝ) ^ (-(1 - sigma)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have heq : (p : ℝ) ^ (-sigma) = (p : ℝ) ^ (-(1 - sigma)) := by
    nlinarith
  have hexp := (Real.strictMono_rpow_of_base_gt_one
    (by exact_mod_cast p.prop.one_lt)).injective heq
  apply hne
  linarith

/-- The additive positive-Euler principal lift of the exact higher-grade Lambert tail. -/
def primeEulerFEHigherGradeEvenCorner
    (a : ℝ) (p : Nat.Primes) (sigma : ℝ) :
    evenSubspace →L[ℂ] evenSubspace :=
  summableEvenPositiveEulerCorner a (primeHigherPowerScale p)
    (primeHigherPowerScale_one_lt p)
    (primeEulerFEHigherGradeCoefficient p (sigma : ℂ))

/-- The exact higher-grade principal tail is compact on the even Sonin carrier precisely on the
critical line. -/
theorem primeEulerFEHigherGradeEvenCorner_isCompactOperator_iff
    {a sigma : ℝ} (ha : 0 < a) (p : Nat.Primes)
    (hstrip : 0 < sigma ∧ sigma < 1) :
    IsCompactOperator (primeEulerFEHigherGradeEvenCorner a p sigma) ↔
      sigma = 1 / 2 := by
  constructor
  · intro hcompact
    by_contra hne
    exact (summableEvenPositiveEulerCorner_not_isCompactOperator
      (primeHigherPowerScale p) (primeHigherPowerScale_one_lt p)
      (primeHigherPowerScale_strictMono p)
      (primeEulerFEHigherGradeCoefficient p (sigma : ℂ))
      (summable_norm_primeEulerFEHigherGradeCoefficient p (by simpa using hstrip)) ha
      ⟨0, primeEulerFEHigherGradeCoefficient_ne_zero_of_re_ne_half p hne⟩) hcompact
  · intro hhalf
    have hsum :
        (∑' j : ℕ,
          (primeEulerFEHigherGradeCoefficient p (sigma : ℂ) j *
            (-((Real.sqrt (primeHigherPowerScale p j) : ℂ)⁻¹))) •
              evenDilationSum (primeHigherPowerScale p j)
                (primeHigherPowerScale_one_lt p j)) = 0 := by
      calc
        _ = ∑' _ : ℕ, (0 : evenSubspace →L[ℂ] evenSubspace) := by
          apply tsum_congr
          intro j
          rw [primeEulerFEHigherGradeCoefficient_zero_of_re_eq_half p hhalf j,
            zero_mul]
          exact zero_smul ℂ
            (evenDilationSum (primeHigherPowerScale p j)
              (primeHigherPowerScale_one_lt p j))
        _ = 0 := tsum_zero
    have hcorner : primeEulerFEHigherGradeEvenCorner a p sigma = 0 := by
      unfold primeEulerFEHigherGradeEvenCorner summableEvenPositiveEulerCorner
        summableEvenDilationCorner summableEvenDilationCombination
      rw [hsum]
      simp [crossBoundary]
    rw [hcorner]
    exact isCompactOperator_zero

/-- The same higher-grade principal lift on the concrete Hardy--Titchmarsh source line. -/
def primeEulerFEHigherGradeArchimedeanCorner
    (a : ℝ) (p : Nat.Primes) (sigma : ℝ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  summableArchimedeanPositiveEulerCorner a (primeHigherPowerScale p)
    (primeHigherPowerScale_one_lt p)
    (primeEulerFEHigherGradeCoefficient p (sigma : ℂ))

/-- The exact higher-grade principal tail remains Calkin-faithful on the concrete
Hardy--Titchmarsh source line. -/
theorem primeEulerFEHigherGradeArchimedeanCorner_isCompactOperator_iff
    {a sigma : ℝ} (ha : 0 < a) (p : Nat.Primes)
    (hstrip : 0 < sigma ∧ sigma < 1) :
    IsCompactOperator (primeEulerFEHigherGradeArchimedeanCorner a p sigma) ↔
      sigma = 1 / 2 := by
  constructor
  · intro hcompact
    by_contra hne
    exact (summableArchimedeanPositiveEulerCorner_not_isCompactOperator
      (primeHigherPowerScale p) (primeHigherPowerScale_one_lt p)
      (primeHigherPowerScale_strictMono p)
      (primeEulerFEHigherGradeCoefficient p (sigma : ℂ))
      (summable_norm_primeEulerFEHigherGradeCoefficient p (by simpa using hstrip)) ha
      ⟨0, primeEulerFEHigherGradeCoefficient_ne_zero_of_re_ne_half p hne⟩) hcompact
  · intro hhalf
    have hsum :
        (∑' j : ℕ,
          (primeEulerFEHigherGradeCoefficient p (sigma : ℂ) j *
            (-((Real.sqrt (primeHigherPowerScale p j) : ℂ)⁻¹))) •
              evenDilationSum (primeHigherPowerScale p j)
                (primeHigherPowerScale_one_lt p j)) = 0 := by
      calc
        _ = ∑' _ : ℕ, (0 : evenSubspace →L[ℂ] evenSubspace) := by
          apply tsum_congr
          intro j
          rw [primeEulerFEHigherGradeCoefficient_zero_of_re_eq_half p hhalf j,
            zero_mul]
          exact zero_smul ℂ
            (evenDilationSum (primeHigherPowerScale p j)
              (primeHigherPowerScale_one_lt p j))
        _ = 0 := tsum_zero
    have hcorner : primeEulerFEHigherGradeArchimedeanCorner a p sigma = 0 := by
      unfold primeEulerFEHigherGradeArchimedeanCorner
        summableArchimedeanPositiveEulerCorner unitaryPush
        summableEvenPositiveEulerCorner summableEvenDilationCorner
        summableEvenDilationCombination
      rw [hsum]
      simp [crossBoundary]
    rw [hcorner]
    exact isCompactOperator_zero

/-- Compactness of one fixed-prime higher-grade principal tail on every actual Xi divisor point. -/
def XiPrimeEulerFEHigherGradeCompact (a : ℝ) (p : Nat.Primes) : Prop :=
  ∀ rho : XiDivisorSupport,
    IsCompactOperator (primeEulerFEHigherGradeArchimedeanCorner a p (rho : ℂ).re)

/-- One fixed prime's higher-grade Calkin compactness across the actual Xi divisor is equivalent to
RH.  The substantive input is the pointwise Calkin-faithfulness theorem above. -/
theorem xiPrimeEulerFEHigherGradeCompact_iff_riemannHypothesis
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    XiPrimeEulerFEHigherGradeCompact a p ↔ RiemannHypothesis := by
  constructor
  · intro hcompact
    apply riemannHypothesis_iff_xiZero_reflection_fixed.mpr
    intro rho hzero
    let q : XiDivisorSupport := ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hstrip := xi_divisor_support_re_mem_open_unit q
    have hre := (primeEulerFEHigherGradeArchimedeanCorner_isCompactOperator_iff
      ha p hstrip).mp (hcompact q)
    exact (fe_reflection_fixed_iff rho).mpr hre
  · intro hRH rho
    apply (primeEulerFEHigherGradeArchimedeanCorner_isCompactOperator_iff
      ha p (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH rho

end

end RHTower
