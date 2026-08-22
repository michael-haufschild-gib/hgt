import GaloisForLFunctions.HTGeometry.ShiftedEulerTangentFiltration
import GaloisForLFunctions.HTGeometry.DirichletMaurerCartanMellinOrbitLaw

/-!
# Exact third tangent of Suzuki's shifted Euler coefficients

This module realizes the literal shifted Euler coefficient as a reflected
Möbius--zeta Mellin convolution and differentiates that convolution three times.
The exact third tangent contains both the cubic von Mangoldt convolution and a
prime-power curvature term.  Thus the third Suzuki layer cannot lawfully be
replaced by a pure triple convolution.
-/

open scoped ArithmeticFunction

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev D := arithmeticLogDerivation
private abbrev M : ComplexArithmeticFunction :=
  (ArithmeticFunction.moebius : ComplexArithmeticFunction)
private abbrev Z : ComplexArithmeticFunction :=
  (ArithmeticFunction.zeta : ComplexArithmeticFunction)
private abbrev A : ComplexArithmeticFunction := complexVonMangoldt

/-- Entire complex Mellin character acting coefficientwise on an arithmetic function. -/
def complexArithmeticMellinTwist (ω : ℂ) (f : ComplexArithmeticFunction) :
    ComplexArithmeticFunction :=
  ⟨fun n => Complex.exp (-(ω * (Real.log n : ℂ))) * f n, by simp⟩

@[simp] theorem complexArithmeticMellinTwist_apply
    (ω : ℂ) (f : ComplexArithmeticFunction) (n : ℕ) :
    complexArithmeticMellinTwist ω f n =
      Complex.exp (-(ω * (Real.log n : ℂ))) * f n := rfl

theorem contDiff_complexArithmeticMellinTwist_apply
    (k : ℕ∞) (f : ComplexArithmeticFunction) (n : ℕ) :
    ContDiff ℂ k (fun z : ℂ => complexArithmeticMellinTwist z f n) := by
  change ContDiff ℂ k
    (fun z : ℂ => Complex.exp (-(z * (Real.log n : ℂ))) * f n)
  fun_prop

theorem contDiff_complexArithmeticMellinTwist_neg_apply
    (k : ℕ∞) (f : ComplexArithmeticFunction) (n : ℕ) :
    ContDiff ℂ k (fun z : ℂ => complexArithmeticMellinTwist (-z) f n) := by
  exact (contDiff_complexArithmeticMellinTwist_apply k f n).comp contDiff_id.neg

theorem iteratedDeriv_complexArithmeticMellinTwist_apply
    (k : ℕ) (f : ComplexArithmeticFunction) (n : ℕ) (ω : ℂ) :
    iteratedDeriv k (fun z : ℂ => complexArithmeticMellinTwist z f n) ω =
      (-(Real.log n : ℂ)) ^ k * complexArithmeticMellinTwist ω f n := by
  have hfun : (fun z : ℂ => complexArithmeticMellinTwist z f n) =
      fun z : ℂ => Complex.exp ((-(Real.log n : ℂ)) * z) * f n := by
    funext z
    rw [complexArithmeticMellinTwist_apply]
    congr 1
    ring
  rw [hfun]
  rw [iteratedDeriv_mul_const_field]
  rw [iteratedDeriv_cexp_const_mul]
  rw [complexArithmeticMellinTwist_apply]
  ring

theorem iteratedDeriv_complexArithmeticMellinTwist_neg_apply_zero
    (k : ℕ) (f : ComplexArithmeticFunction) (n : ℕ) :
    iteratedDeriv k (fun z : ℂ => complexArithmeticMellinTwist (-z) f n) 0 =
      (Real.log n : ℂ) ^ k * f n := by
  have hfun : (fun z : ℂ => complexArithmeticMellinTwist (-z) f n) =
      fun z : ℂ => Complex.exp ((Real.log n : ℂ) * z) * f n := by
    funext z
    rw [complexArithmeticMellinTwist_apply]
    congr 1
    ring
  rw [hfun, iteratedDeriv_mul_const_field,
    iteratedDeriv_cexp_const_mul]
  simp

theorem complexArithmeticMellinTwist_isMultiplicative
    (ω : ℂ) {f : ComplexArithmeticFunction} (hf : f.IsMultiplicative) :
    (complexArithmeticMellinTwist ω f).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [complexArithmeticMellinTwist, hf.map_one]
  · intro m n hm hn hmn
    have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [complexArithmeticMellinTwist_apply,
      complexArithmeticMellinTwist_apply,
      complexArithmeticMellinTwist_apply, hf.map_mul_of_coprime hmn]
    have hlog : (Real.log (m * n : ℕ) : ℂ) =
        (Real.log m : ℂ) + (Real.log n : ℂ) := by
      rw [Nat.cast_mul, Real.log_mul hmpos.ne' hnpos.ne']
      norm_cast
    rw [hlog, show -(ω * ((Real.log m : ℂ) + (Real.log n : ℂ))) =
      -(ω * (Real.log m : ℂ)) + -(ω * (Real.log n : ℂ)) by ring,
      Complex.exp_add]
    ring

/-- Arithmetic-function packaging of the entire shifted Euler coefficient. -/
def shiftedEulerCoeffArithmetic (ω : ℂ) : ComplexArithmeticFunction :=
  ⟨fun n => if n = 0 then 0 else shiftedEulerCoeff n ω, by simp⟩

@[simp] theorem shiftedEulerCoeffArithmetic_apply_of_ne
    (ω : ℂ) {n : ℕ} (hn : n ≠ 0) :
    shiftedEulerCoeffArithmetic ω n = shiftedEulerCoeff n ω := by
  simp [shiftedEulerCoeffArithmetic, hn]

theorem shiftedEulerCoeffArithmetic_isMultiplicative (ω : ℂ) :
    (shiftedEulerCoeffArithmetic ω).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [shiftedEulerCoeffArithmetic, shiftedEulerCoeff]
  · intro m n hm hn hmn
    have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [shiftedEulerCoeffArithmetic_apply_of_ne ω hm,
      shiftedEulerCoeffArithmetic_apply_of_ne ω hn,
      shiftedEulerCoeffArithmetic_apply_of_ne ω (mul_ne_zero hm hn)]
    rw [shiftedEulerCoeff, shiftedEulerCoeff, shiftedEulerCoeff,
      hmn.primeFactors_mul, Finset.prod_union hmn.disjoint_primeFactors]
    have hlog : (Real.log (m * n : ℕ) : ℂ) =
        (Real.log m : ℂ) + (Real.log n : ℂ) := by
      rw [Nat.cast_mul, Real.log_mul hmpos.ne' hnpos.ne']
      norm_cast
    rw [hlog, show ω * ((Real.log m : ℂ) + (Real.log n : ℂ)) =
      ω * (Real.log m : ℂ) + ω * (Real.log n : ℂ) by ring,
      Complex.exp_add]
    ring

/-- Coefficient of the reflected Möbius--zeta Mellin convolution. -/
def reflectedMellinConvolutionCoefficient (n : ℕ) (ω : ℂ) : ℂ :=
  (complexArithmeticMellinTwist ω
      (ArithmeticFunction.moebius : ComplexArithmeticFunction) *
    complexArithmeticMellinTwist (-ω)
      (ArithmeticFunction.zeta : ComplexArithmeticFunction)) n

theorem reflectedMellinConvolutionCoefficient_prime_pow
    (ω : ℂ) {p a : ℕ} (hp : p.Prime) :
    reflectedMellinConvolutionCoefficient (p ^ a) ω =
      shiftedEulerCoeff (p ^ a) ω := by
  rcases a with _ | k
  · simp [reflectedMellinConvolutionCoefficient,
      complexArithmeticMellinTwist, shiftedEulerCoeff]
  · unfold reflectedMellinConvolutionCoefficient
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun d e =>
        complexArithmeticMellinTwist ω M d *
          complexArithmeticMellinTwist (-ω) Z e),
      Nat.sum_divisors_prime_pow hp]
    have hstep : ∀ x ∈ Finset.range (k + 2),
        complexArithmeticMellinTwist ω M (p ^ x) *
            complexArithmeticMellinTwist (-ω) Z (p ^ (k + 1) / p ^ x) =
          if x = 0 then Complex.exp (ω * (Real.log (p ^ (k + 1) : ℕ) : ℂ))
          else if x = 1 then
            -Complex.exp (((k : ℂ) - 1) * ω * (Real.log p : ℂ))
          else 0 := by
      intro x hx
      have hxle : x ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      rw [Nat.pow_div hxle hp.pos]
      by_cases hx0 : x = 0
      · subst x
        simp [complexArithmeticMellinTwist, hp.ne_zero,
          Real.log_pow, Complex.ofReal_mul]
        have hlog : Complex.log ((p ^ (k + 1) : ℕ) : ℂ) =
            (k + 1 : ℂ) * (Real.log p : ℂ) := by
          calc
            Complex.log ((p ^ (k + 1) : ℕ) : ℂ) =
                (Real.log ((p ^ (k + 1) : ℕ) : ℝ) : ℂ) :=
              Complex.natCast_log.symm
            _ = (k + 1 : ℂ) * (Real.log p : ℂ) := by
              rw [Nat.cast_pow, Real.log_pow]
              push_cast
              ring
        rw [← Nat.cast_pow]
        rw [hlog]
        rw [← Complex.natCast_log]
      by_cases hx1 : x = 1
      · subst x
        simp [complexArithmeticMellinTwist, hp.ne_zero,
          ArithmeticFunction.moebius_apply_prime hp]
        have hlog : Complex.log ((p ^ k : ℕ) : ℂ) =
            (k : ℂ) * (Real.log p : ℂ) := by
          calc
            Complex.log ((p ^ k : ℕ) : ℂ) =
                (Real.log ((p ^ k : ℕ) : ℝ) : ℂ) :=
              Complex.natCast_log.symm
            _ = (k : ℂ) * (Real.log p : ℂ) := by
              rw [Nat.cast_pow, Real.log_pow]
              push_cast
              rfl
        rw [← Nat.cast_pow]
        rw [hlog, ← Complex.exp_add]
        rw [← Complex.natCast_log]
        congr 1
        ring
      · have hx2 : 2 ≤ x := by omega
        rw [if_neg hx0, if_neg hx1]
        have hmu : M (p ^ x) = 0 := by
          change ((ArithmeticFunction.moebius (p ^ x) : ℤ) : ℂ) = 0
          rw [ArithmeticFunction.moebius_apply_prime_pow hp hx0, if_neg hx1]
          norm_num
        rw [complexArithmeticMellinTwist_apply, hmu, mul_zero, zero_mul]
    rw [Finset.sum_congr rfl hstep]
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (k + 2) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp
    have hzero : ∀ x ∈ Finset.range (k + 2),
        x ∉ ({0, 1} : Finset ℕ) →
          (if x = 0 then Complex.exp (ω * (Real.log (p ^ (k + 1) : ℕ) : ℂ))
          else if x = 1 then
            -Complex.exp (((k : ℂ) - 1) * ω * (Real.log p : ℂ))
          else 0) = 0 := by
      intro x hx hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      rw [if_neg hnot.1, if_neg hnot.2]
    rw [← Finset.sum_subset hsub hzero,
      Finset.sum_insert (by norm_num), Finset.sum_singleton]
    simp only [if_pos, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    rw [shiftedEulerCoeff]
    have hfac : (p ^ (k + 1)).primeFactors = {p} := by
      rw [Nat.primeFactors_pow _ (by omega), hp.primeFactors]
    rw [hfac, Finset.prod_singleton]
    have hlogpow : (Real.log (p ^ (k + 1) : ℕ) : ℂ) =
        (k + 1 : ℂ) * (Real.log p : ℂ) := by
      push_cast
      rw [Real.log_pow]
      push_cast
      ring
    rw [hlogpow]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    ring

private theorem reflectedMellinConvolution_eq_shiftedEulerCoeffArithmetic (ω : ℂ) :
    complexArithmeticMellinTwist ω M * complexArithmeticMellinTwist (-ω) Z =
      shiftedEulerCoeffArithmetic ω := by
  have hM : M.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_moebius.intCast
  have hZ : Z.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  have href : (complexArithmeticMellinTwist ω M *
      complexArithmeticMellinTwist (-ω) Z).IsMultiplicative :=
    (complexArithmeticMellinTwist_isMultiplicative ω hM).mul
      (complexArithmeticMellinTwist_isMultiplicative (-ω) hZ)
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    _ href _ (shiftedEulerCoeffArithmetic_isMultiplicative ω)).2
  intro p i hp
  change reflectedMellinConvolutionCoefficient (p ^ i) ω =
    shiftedEulerCoeffArithmetic ω (p ^ i)
  rw [shiftedEulerCoeffArithmetic_apply_of_ne ω
    (pow_ne_zero i hp.ne_zero),
    reflectedMellinConvolutionCoefficient_prime_pow ω hp]

theorem reflectedMellinConvolutionCoefficient_eq_shiftedEulerCoeff
    {n : ℕ} (hn : n ≠ 0) (ω : ℂ) :
    reflectedMellinConvolutionCoefficient n ω = shiftedEulerCoeff n ω := by
  have h := congrArg (fun f : ComplexArithmeticFunction => f n)
    (reflectedMellinConvolution_eq_shiftedEulerCoeffArithmetic ω)
  simpa [reflectedMellinConvolutionCoefficient,
    shiftedEulerCoeffArithmetic_apply_of_ne ω hn] using h

private theorem iteratedDeriv_three_reflectedMellinConvolutionCoefficient (n : ℕ) :
    iteratedDeriv 3 (reflectedMellinConvolutionCoefficient n) 0 =
      (-(D (D (D M)) * Z) +
          (3 : ℂ) • (D (D M) * D Z) -
          (3 : ℂ) • (D M * D (D Z)) +
          M * D (D (D Z))) n := by
  unfold reflectedMellinConvolutionCoefficient
  simp only [ArithmeticFunction.mul_apply]
  rw [iteratedDeriv_fun_sum]
  · change (∑ i ∈ n.divisorsAntidiagonal,
        iteratedDeriv 3
          (fun ω => (complexArithmeticMellinTwist ω M) i.1 *
            (complexArithmeticMellinTwist (-ω) Z) i.2) 0) =
      -(∑ x ∈ n.divisorsAntidiagonal, (D (D (D M))) x.1 * Z x.2) +
        3 * (∑ x ∈ n.divisorsAntidiagonal, (D (D M)) x.1 * (D Z) x.2) -
        3 * (∑ x ∈ n.divisorsAntidiagonal, (D M) x.1 * (D (D Z)) x.2) +
        ∑ x ∈ n.divisorsAntidiagonal, M x.1 * (D (D (D Z))) x.2
    calc
      _ = ∑ x ∈ n.divisorsAntidiagonal,
          (-(D (D (D M)) x.1 * Z x.2) +
            3 * (D (D M) x.1 * D Z x.2) -
            3 * (D M x.1 * D (D Z) x.2) +
            M x.1 * D (D (D Z)) x.2) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hf : ContDiffAt ℂ 3
            (fun z : ℂ => complexArithmeticMellinTwist z M x.1) 0 :=
          (contDiff_complexArithmeticMellinTwist_apply 3 M x.1).contDiffAt
        have hg : ContDiffAt ℂ 3
            (fun z : ℂ => complexArithmeticMellinTwist (-z) Z x.2) 0 :=
          (contDiff_complexArithmeticMellinTwist_neg_apply 3 Z x.2).contDiffAt
        change iteratedDeriv 3
          ((fun z : ℂ => complexArithmeticMellinTwist z M x.1) *
            (fun z : ℂ => complexArithmeticMellinTwist (-z) Z x.2)) 0 = _
        have hleft : ∀ k : ℕ, iteratedDeriv k
            (fun z : ℂ => complexArithmeticMellinTwist z M x.1) 0 =
              (-(Real.log x.1 : ℂ)) ^ k * M x.1 := by
          intro k
          simpa using iteratedDeriv_complexArithmeticMellinTwist_apply
            k M x.1 0
        have hright : ∀ k : ℕ, iteratedDeriv k
            (fun z : ℂ => complexArithmeticMellinTwist (-z) Z x.2) 0 =
              (Real.log x.2 : ℂ) ^ k * Z x.2 :=
          fun k => iteratedDeriv_complexArithmeticMellinTwist_neg_apply_zero
            k Z x.2
        rw [iteratedDeriv_mul hf hg]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        rw [hleft 0, hright 3, hleft 1, hright 2,
          hleft 2, hright 1, hleft 3, hright 0]
        norm_num [arithmeticLogDerivation_apply]
        have hx20 : x.2 ≠ 0 := by
          intro hx2
          have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
          have hn0 := (Nat.mem_divisorsAntidiagonal.mp hx).2
          rw [hx2, mul_zero] at hprod
          exact hn0 hprod.symm
        simp only [complexArithmeticLog, hx20, if_false,
          ArithmeticFunction.coe_mk]
        rw [← Complex.natCast_log]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_neg_distrib, Finset.mul_sum]
  · intro x hx
    exact ((contDiff_complexArithmeticMellinTwist_apply 3 M x.1).mul
      (contDiff_complexArithmeticMellinTwist_neg_apply 3 Z x.2)).contDiffAt

private theorem reflectedMellinThirdJet_algebra :
    -(D (D (D M)) * Z) +
        (3 : ℂ) • (D (D M) * D Z) -
        (3 : ℂ) • (D M * D (D Z)) +
        M * D (D (D Z)) =
      (8 : ℂ) • A ^ 3 + (2 : ℂ) • D (D A) := by
  have hprod : M * Z = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hA : M * D Z = A := by
    rw [arithmeticLogDerivation_zeta,
      complex_moebius_mul_log_eq_vonMangoldt]
  have hDM : D M = -(M * A) := by
    have hd := D.leibniz_of_mul_eq_one hprod
    rw [smul_eq_mul] at hd
    calc
      D M = -M ^ 2 * D Z := hd
      _ = -(M * (M * D Z)) := by ring
      _ = -(M * A) := by rw [hA]
  have hDZ : D Z = Z * A := by
    calc
      D Z = 1 * D Z := by rw [one_mul]
      _ = (Z * M) * D Z := by rw [mul_comm Z M, hprod]
      _ = Z * A := by rw [← hA]; ring
  have hD2M : D (D M) = M * (A ^ 2 - D A) := by
    rw [hDM, map_neg, D.leibniz, hDM]
    ring
  have hD2Z : D (D Z) = Z * (A ^ 2 + D A) := by
    rw [hDZ, D.leibniz, hDZ]
    ring
  have hD3M : D (D (D M)) = M * (-A ^ 3 + 3 * A * D A - D (D A)) := by
    rw [hD2M, D.leibniz, hDM, map_sub]
    simp only [pow_two]
    rw [D.leibniz]
    ring
  have hD3Z : D (D (D Z)) = Z * (A ^ 3 + 3 * A * D A + D (D A)) := by
    rw [hD2Z, D.leibniz, hDZ, map_add]
    simp only [pow_two]
    rw [D.leibniz]
    ring
  rw [hD3M, hD3Z, hD2M, hD2Z, hDM, hDZ]
  simp only [Algebra.smul_def, map_ofNat]
  calc
    -(M * (-A ^ 3 + 3 * A * D A - D (D A)) * Z) +
          3 * (M * (A ^ 2 - D A) * (Z * A)) -
          3 * (-(M * A) * (Z * (A ^ 2 + D A))) +
          M * (Z * (A ^ 3 + 3 * A * D A + D (D A))) =
        (M * Z) *
          (8 * A ^ 3 + 2 * D (D A)) := by ring
    _ = 8 * A ^ 3 + 2 * D (D A) := by rw [hprod, one_mul]

private theorem iteratedDeriv_three_reflectedMellinConvolutionCoefficient_eq_source
    (n : ℕ) :
    iteratedDeriv 3 (reflectedMellinConvolutionCoefficient n) 0 =
      ((8 : ℂ) • A ^ 3 + (2 : ℂ) • D (D A)) n := by
  rw [iteratedDeriv_three_reflectedMellinConvolutionCoefficient,
    reflectedMellinThirdJet_algebra]

private theorem iteratedDeriv_three_shiftedEulerCoeff_source
    {n : ℕ} (hn : n ≠ 0) :
    iteratedDeriv 3 (shiftedEulerCoeff n) 0 =
      ((8 : ℂ) • A ^ 3 + (2 : ℂ) • D (D A)) n := by
  have hfun : shiftedEulerCoeff n = reflectedMellinConvolutionCoefficient n := by
    funext ω
    exact (reflectedMellinConvolutionCoefficient_eq_shiftedEulerCoeff hn ω).symm
  rw [hfun,
    iteratedDeriv_three_reflectedMellinConvolutionCoefficient_eq_source]

private theorem iteratedDeriv_three_shiftedEulerCoeff_of_ne
    {n : ℕ} (hn : n ≠ 0) :
    iteratedDeriv 3 (shiftedEulerCoeff n) 0 =
      8 * (((((ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt) *
            ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ)) +
        2 * (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (Real.log n : ℂ) ^ 2) := by
  rw [iteratedDeriv_three_shiftedEulerCoeff_source hn]
  simp only [ArithmeticFunction.add_apply]
  change 8 * (A ^ 3) n + 2 * D (D A) n = _
  rw [show (A ^ 3) n =
      ((((ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt) *
          ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ) by
    rw [show A ^ 3 = A * A * A by ring]
    simp only [ArithmeticFunction.mul_apply, A,
      complexVonMangoldt, ArithmeticFunction.coe_mk]
    push_cast
    rfl]
  rw [show D (D A) n =
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (Real.log n : ℂ) ^ 2 by
    simp [arithmeticLogDerivation_apply, A, complexVonMangoldt]
    ring]

/-- Exact third transverse derivative of Suzuki's shifted Euler coefficient.

The third jet is not the pure cubic von Mangoldt convolution: it contains the
forced prime-power curvature term `2 * Λ(n) * log(n)^2`. -/
theorem iteratedDeriv_three_shiftedEulerCoeff (n : ℕ) :
    iteratedDeriv 3 (shiftedEulerCoeff n) 0 =
      8 * (((((ArithmeticFunction.vonMangoldt *
          ArithmeticFunction.vonMangoldt) *
            ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ)) +
        2 * (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (Real.log n : ℂ) ^ 2) := by
  by_cases hn : n = 0
  · subst n
    have hzero : shiftedEulerCoeff 0 = fun _ : ℂ => 1 := by
      funext ω
      simp [shiftedEulerCoeff]
    rw [hzero]
    simp [iteratedDeriv_succ]
  · exact iteratedDeriv_three_shiftedEulerCoeff_of_ne hn

/-- First arithmetic tangent of the literal shifted Euler family. -/
def shiftedEulerFirstTangentArithmetic : ComplexArithmeticFunction :=
  ⟨fun n => iteratedDeriv 1 (shiftedEulerCoeff n) 0, by
    rw [iteratedDeriv_one_shiftedEulerCoeff]
    simp⟩

/-- Second arithmetic tangent of the literal shifted Euler family. -/
def shiftedEulerSecondTangentArithmetic : ComplexArithmeticFunction :=
  ⟨fun n => iteratedDeriv 2 (shiftedEulerCoeff n) 0, by
    rw [iteratedDeriv_two_shiftedEulerCoeff]
    simp⟩

/-- Third arithmetic tangent of the literal shifted Euler family. -/
def shiftedEulerThirdTangentArithmetic : ComplexArithmeticFunction :=
  ⟨fun n => iteratedDeriv 3 (shiftedEulerCoeff n) 0, by
    rw [iteratedDeriv_three_shiftedEulerCoeff]
    simp⟩

@[simp] theorem shiftedEulerFirstTangentArithmetic_apply (n : ℕ) :
    shiftedEulerFirstTangentArithmetic n =
      iteratedDeriv 1 (shiftedEulerCoeff n) 0 := rfl

@[simp] theorem shiftedEulerSecondTangentArithmetic_apply (n : ℕ) :
    shiftedEulerSecondTangentArithmetic n =
      iteratedDeriv 2 (shiftedEulerCoeff n) 0 := rfl

@[simp] theorem shiftedEulerThirdTangentArithmetic_apply (n : ℕ) :
    shiftedEulerThirdTangentArithmetic n =
      iteratedDeriv 3 (shiftedEulerCoeff n) 0 := rfl

theorem shiftedEulerFirstTangentArithmetic_eq :
    shiftedEulerFirstTangentArithmetic =
      (2 : ℂ) • complexVonMangoldt := by
  ext n
  rw [shiftedEulerFirstTangentArithmetic_apply,
    iteratedDeriv_one_shiftedEulerCoeff]
  simp [complexVonMangoldt]

theorem shiftedEulerSecondTangentArithmetic_eq :
    shiftedEulerSecondTangentArithmetic =
      (4 : ℂ) • complexVonMangoldt ^ 2 := by
  ext n
  rw [shiftedEulerSecondTangentArithmetic_apply,
    iteratedDeriv_two_shiftedEulerCoeff]
  change 4 * (((ArithmeticFunction.vonMangoldt *
    ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ) =
      4 * (complexVonMangoldt ^ 2) n
  rw [show complexVonMangoldt ^ 2 =
    complexVonMangoldt * complexVonMangoldt by ring]
  simp only [ArithmeticFunction.mul_apply, complexVonMangoldt,
    ArithmeticFunction.coe_mk]
  push_cast
  rfl

theorem shiftedEulerThirdTangentArithmetic_eq :
    shiftedEulerThirdTangentArithmetic =
      (8 : ℂ) • complexVonMangoldt ^ 3 +
        (2 : ℂ) • arithmeticLogDerivation
          (arithmeticLogDerivation complexVonMangoldt) := by
  ext n
  rw [shiftedEulerThirdTangentArithmetic_apply,
    iteratedDeriv_three_shiftedEulerCoeff]
  change 8 * (((((ArithmeticFunction.vonMangoldt *
      ArithmeticFunction.vonMangoldt) *
        ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ)) +
      2 * (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (Real.log n : ℂ) ^ 2) =
    8 * (complexVonMangoldt ^ 3) n +
      2 * arithmeticLogDerivation
        (arithmeticLogDerivation complexVonMangoldt) n
  rw [show (complexVonMangoldt ^ 3) n =
      ((((ArithmeticFunction.vonMangoldt *
        ArithmeticFunction.vonMangoldt) *
          ArithmeticFunction.vonMangoldt) n : ℝ) : ℂ) by
    rw [show complexVonMangoldt ^ 3 =
      complexVonMangoldt * complexVonMangoldt * complexVonMangoldt by ring]
    simp only [ArithmeticFunction.mul_apply, complexVonMangoldt,
      ArithmeticFunction.coe_mk]
    push_cast
    rfl]
  rw [show arithmeticLogDerivation
      (arithmeticLogDerivation complexVonMangoldt) n =
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (Real.log n : ℂ) ^ 2 by
    simp [arithmeticLogDerivation_apply, complexVonMangoldt]
    ring]

/-- Dirichlet connected third cumulant, formed before any coefficient readout. -/
def shiftedEulerConnectedThirdTangentArithmetic : ComplexArithmeticFunction :=
  shiftedEulerThirdTangentArithmetic -
    (3 : ℂ) •
      (shiftedEulerSecondTangentArithmetic * shiftedEulerFirstTangentArithmetic) +
    (2 : ℂ) •
      (shiftedEulerFirstTangentArithmetic ^ 3)

/-- Disconnected three-prime mass cancels identically in the pre-scalar cumulant. -/
theorem shiftedEulerConnectedThirdTangentArithmetic_eq :
    shiftedEulerConnectedThirdTangentArithmetic =
      (2 : ℂ) • arithmeticLogDerivation
        (arithmeticLogDerivation complexVonMangoldt) := by
  rw [shiftedEulerConnectedThirdTangentArithmetic,
    shiftedEulerFirstTangentArithmetic_eq,
    shiftedEulerSecondTangentArithmetic_eq,
    shiftedEulerThirdTangentArithmetic_eq]
  simp only [Algebra.smul_def, map_ofNat]
  ring

/-- Coefficient law for the connected producer: only prime-power curvature survives. -/
theorem shiftedEulerConnectedThirdTangentArithmetic_apply (n : ℕ) :
    shiftedEulerConnectedThirdTangentArithmetic n =
      2 * (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (Real.log n : ℂ) ^ 2) := by
  rw [shiftedEulerConnectedThirdTangentArithmetic_eq]
  simp [arithmeticLogDerivation_apply, complexVonMangoldt]
  ring

end

end GaloisForLFunctions.HTGeometry
