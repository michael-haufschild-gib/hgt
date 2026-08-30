import GaloisForLFunctions.HTGeometry.PrimeOccupationCompletionLimit
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GasAlgebra
import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter
import GaloisForLFunctions.HTGeometry.CirclePoissonProductEquivalence
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGroupDelay
import GaloisForLFunctions.HTGeometry.SummableCircleFourierDensity

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Filter
open scoped ENNReal ComplexConjugate

noncomputable section

local instance circlePoissonOuterFactorLocalInst1 : MeasurableSpace Circle :=
  instMeasurableSpaceCircle_galoisForLFunctions

/-- Positive prime-exponent characters, as vectors in Haar `L²` of the prime torus. -/
def primeBohrCharacterLp (nu : Nat.Primes →₀ ℕ) :
    Lp ℂ 2 (torusHaar Nat.Primes) :=
  ContinuousMap.toLp 2 (torusHaar Nat.Primes) ℂ
    (torusCharacter (GasWord.natToInt nu))

theorem GasWord.natToInt_injective :
    Function.Injective (GasWord.natToInt (M := Nat.Primes)) := by
  intro nu mu h
  apply Finsupp.ext
  intro p
  have hp := DFunLike.congr_fun h p
  simp only [GasWord.natToInt_apply] at hp
  exact_mod_cast hp

/-- Positive prime-exponent characters form an orthonormal family in Haar `L²`. -/
theorem orthonormal_primeBohrCharacterLp :
    Orthonormal ℂ primeBohrCharacterLp := by
  classical
  rw [orthonormal_iff_ite]
  intro nu mu
  rw [primeBohrCharacterLp, primeBohrCharacterLp, MeasureTheory.L2.inner_def]
  have hnu := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (torusHaar Nat.Primes)
    (torusCharacter (GasWord.natToInt nu))
  have hmu := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (torusHaar Nat.Primes)
    (torusCharacter (GasWord.natToInt mu))
  have hzero : -GasWord.natToInt nu + GasWord.natToInt mu = 0 ↔ nu = mu := by
    constructor
    · intro h
      apply GasWord.natToInt_injective
      exact neg_add_eq_zero.mp h
    · rintro rfl
      simp
  calc
    (∫ x, inner ℂ
        (((ContinuousMap.toLp 2 (torusHaar Nat.Primes) ℂ)
          (torusCharacter (GasWord.natToInt nu))) x)
        (((ContinuousMap.toLp 2 (torusHaar Nat.Primes) ℂ)
          (torusCharacter (GasWord.natToInt mu))) x) ∂torusHaar Nat.Primes) =
        ∫ x, torusCharacter
          (-GasWord.natToInt nu + GasWord.natToInt mu) x
          ∂torusHaar Nat.Primes := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hnu, hmu] with x hxnu hxmu
      rw [RCLike.inner_apply, hxnu, hxmu, ← torusCharacter_neg_index,
        ← torusCharacter_add_index]
      rw [add_comm]
    _ = if -GasWord.natToInt nu + GasWord.natToInt mu = 0 then 1 else 0 :=
      integral_torusCharacter _
    _ = if nu = mu then 1 else 0 := by simp only [hzero]

/-- Canonical Bohr isometry from square-summable occupation coefficients to Haar `L²`. -/
def primeBohrTransform :
    lp (fun _ : Nat.Primes →₀ ℕ => ℂ) 2 →ₗᵢ[ℂ]
      Lp ℂ 2 (torusHaar Nat.Primes) :=
  orthonormal_primeBohrCharacterLp.orthogonalFamily.linearIsometry

@[simp]
theorem primeBohrTransform_single (nu : Nat.Primes →₀ ℕ) (c : ℂ) :
    primeBohrTransform (lp.single 2 nu c) = c • primeBohrCharacterLp nu := by
  rw [primeBohrTransform, OrthogonalFamily.linearIsometry_apply_single]
  rfl

/-- The normalized analytic outer factor whose boundary modulus squares to the Poisson kernel. -/
def circlePoissonOuterFactor (a : CirclePoissonParameter) (z : Circle) : ℂ :=
  (Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) : ℂ) /
    (1 - conj (a : ℂ) * (z : ℂ))

theorem circlePoissonOuterFactor_den_ne_zero
    (a : CirclePoissonParameter) (z : Circle) :
    1 - conj (a : ℂ) * (z : ℂ) ≠ 0 := by
  have ha' : dist (a : ℂ) 0 < 1 := Metric.mem_ball.mp a.2
  have ha : ‖(a : ℂ)‖ < 1 := by simpa only [dist_zero_right] using ha'
  exact blaschkeFactor_den_ne_zero ha (Circle.norm_coe z).le

theorem continuous_circlePoissonOuterFactor (a : CirclePoissonParameter) :
    Continuous (circlePoissonOuterFactor a) := by
  unfold circlePoissonOuterFactor
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact fun z => circlePoissonOuterFactor_den_ne_zero a z

/-- Exact local outer-factor identity on the unit circle. -/
theorem norm_sq_circlePoissonOuterFactor
    (a : CirclePoissonParameter) (z : Circle) :
    ‖circlePoissonOuterFactor a z‖ ^ 2 =
      poissonKernel 0 (a : ℂ) (z : ℂ) := by
  have ha' : dist (a : ℂ) 0 < 1 := Metric.mem_ball.mp a.2
  have ha : ‖(a : ℂ)‖ < 1 := by simpa only [dist_zero_right] using ha'
  have ha0 : 0 ≤ 1 - ‖(a : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg (a : ℂ)]
  have hz : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
  have hden : ‖1 - conj (a : ℂ) * (z : ℂ)‖ = ‖(z : ℂ) - (a : ℂ)‖ := by
    have hunit : (z : ℂ) * conj (z : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
      norm_num
    have heq : 1 - conj (a : ℂ) * (z : ℂ) =
        (z : ℂ) * conj ((z : ℂ) - (a : ℂ)) := by
      rw [map_sub]
      calc
        1 - conj (a : ℂ) * (z : ℂ) =
            (z : ℂ) * conj (z : ℂ) - conj (a : ℂ) * (z : ℂ) := by rw [hunit]
        _ = (z : ℂ) * (conj (z : ℂ) - conj (a : ℂ)) := by ring
    rw [heq, norm_mul, hz, one_mul]
    exact norm_star ((z : ℂ) - (a : ℂ))
  have hnum : ‖((Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) : ℝ) : ℂ)‖ ^ 2 =
      1 - ‖(a : ℂ)‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt ha0]
  rw [circlePoissonOuterFactor, norm_div, div_pow, hnum, hden,
    poissonKernel_zero_eq_normSq_ratio hz,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]

/-- Haar is the circle-Poisson law at the disk origin. -/
def zeroCirclePoissonParameter : CirclePoissonParameter :=
  ⟨0, Metric.mem_ball.mpr (by norm_num)⟩

@[simp]
theorem circlePoissonHalfDensity_zero (z : Circle) :
    circlePoissonHalfDensity zeroCirclePoissonParameter z = 1 := by
  rw [circlePoissonHalfDensity]
  simp [zeroCirclePoissonParameter, poissonKernel_def]

/-- Outer factor and positive half-likelihood have exactly the same pointwise modulus. -/
theorem norm_circlePoissonOuterFactor_eq_halfLikelihood
    (a : CirclePoissonParameter) (z : Circle) :
    ‖circlePoissonOuterFactor a z‖ =
      circlePoissonHalfLikelihood a zeroCirclePoissonParameter z := by
  have hout0 : 0 ≤ ‖circlePoissonOuterFactor a z‖ := norm_nonneg _
  have hhalf0 : 0 ≤ circlePoissonHalfLikelihood a zeroCirclePoissonParameter z :=
    (circlePoissonHalfLikelihood_pos a zeroCirclePoissonParameter z).le
  have hsquare : ‖circlePoissonOuterFactor a z‖ ^ 2 =
      circlePoissonHalfLikelihood a zeroCirclePoissonParameter z ^ 2 := by
    rw [norm_sq_circlePoissonOuterFactor, circlePoissonHalfLikelihood,
      circlePoissonHalfDensity_zero, div_one, circlePoissonHalfDensity_sq]
  nlinarith

/-- Haar mean of one normalized outer factor is its positive local Euler normalizer. -/
theorem integral_circlePoissonOuterFactor (a : CirclePoissonParameter) :
    (∫ z : Circle, circlePoissonOuterFactor a z ∂circleLebesgue) =
      (Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) : ℂ) := by
  let c : ℂ := conj (a : ℂ)
  have ha' : dist (a : ℂ) 0 < 1 := Metric.mem_ball.mp a.2
  have ha : ‖(a : ℂ)‖ < 1 := by simpa only [dist_zero_right] using ha'
  have hc : ‖c‖ < 1 := by simpa [c] using ha
  let term : ℕ → Circle → ℂ := fun n z => c ^ n * (z : ℂ) ^ n
  have htermInt : ∀ n, Integrable (term n) circleLebesgue := by
    intro n
    have hcont : Continuous (term n) :=
      Continuous.const_mul (continuous_subtype_val.pow n) (c ^ n)
    have hsupp : HasCompactSupport (term n) :=
      HasCompactSupport.of_compactSpace (term n)
    exact hcont.integrable_of_hasCompactSupport (μ := circleLebesgue) hsupp
  have htermNorm (n : ℕ) :
      ∫ z : Circle, ‖term n z‖ ∂circleLebesgue = ‖c‖ ^ n := by
    simp [term]
  have hsumNorm : Summable (fun n => ∫ z : Circle, ‖term n z‖ ∂circleLebesgue) := by
    have hgeom := (summable_geometric_of_norm_lt_one hc).norm
    simpa only [htermNorm, norm_pow] using hgeom
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm htermInt hsumNorm
  have hpoint (z : Circle) :
      ∑' n : ℕ, term n z = (1 - c * (z : ℂ))⁻¹ := by
    have hcz : ‖c * (z : ℂ)‖ < 1 := by
      rw [norm_mul, Circle.norm_coe, mul_one]
      exact hc
    simpa [term, mul_pow] using (hasSum_geometric_of_norm_lt_one hcz).tsum_eq
  have hinterms : (∑' n : ℕ, ∫ z : Circle, term n z ∂circleLebesgue) = 1 := by
    calc
      (∑' n : ℕ, ∫ z : Circle, term n z ∂circleLebesgue) =
          ∫ z : Circle, term 0 z ∂circleLebesgue := by
        apply tsum_eq_single 0
        intro n hn
        change (∫ z : Circle, c ^ n * (z : ℂ) ^ n ∂circleLebesgue) = 0
        rw [MeasureTheory.integral_const_mul,
          integral_circleLebesgue_coe_pow_eq_zero n hn, mul_zero]
      _ = 1 := by simp [term]
  unfold circlePoissonOuterFactor
  rw [show (fun z : Circle =>
      (Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) : ℂ) /
        (1 - conj (a : ℂ) * (z : ℂ))) =
      fun z => (Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) : ℂ) *
        ∑' n : ℕ, term n z by
      funext z
      rw [hpoint]
      simp [c, div_eq_mul_inv]]
  rw [MeasureTheory.integral_const_mul, ← hswap, hinterms, mul_one]

/-- Finite Euler outer product on the natural enumeration of prime coordinates. -/
def circlePoissonPrefixOuterFactor
    (a : ℕ → CirclePoissonParameter) (N : ℕ) (x : ℕ → Circle) : ℂ :=
  ∏ n : ↑(Finset.range N), circlePoissonOuterFactor (a n) (x n)

theorem continuous_circlePoissonPrefixOuterFactor
    (a : ℕ → CirclePoissonParameter) (N : ℕ) :
    Continuous (circlePoissonPrefixOuterFactor a N) := by
  unfold circlePoissonPrefixOuterFactor
  exact continuous_finsetProd Finset.univ fun n _ =>
    (continuous_circlePoissonOuterFactor (a n)).comp (continuous_apply (n : ℕ))

/-- Every finite analytic Euler prefix has the existing positive half-likelihood as modulus. -/
theorem norm_circlePoissonPrefixOuterFactor
    (a : ℕ → CirclePoissonParameter) (N : ℕ) (x : ℕ → Circle) :
    ‖circlePoissonPrefixOuterFactor a N x‖ =
      circlePoissonPrefixHalfLikelihood a (fun _ => zeroCirclePoissonParameter) N x := by
  rw [circlePoissonPrefixOuterFactor, circlePoissonPrefixHalfLikelihood, norm_prod]
  apply Finset.prod_congr rfl
  intro n _
  exact norm_circlePoissonOuterFactor_eq_halfLikelihood (a n) (x n)

theorem memLp_two_circlePoissonPrefixOuterFactor
    (a : ℕ → CirclePoissonParameter) (N : ℕ) :
    MemLp (circlePoissonPrefixOuterFactor a N) 2
      (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) := by
  have hcont := continuous_circlePoissonPrefixOuterFactor a N
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  exact (hcont.norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Haar `L²` class of a finite normalized analytic Euler product. -/
def circlePoissonPrefixOuterFactorLp
    (a : ℕ → CirclePoissonParameter) (N : ℕ) :
    Lp ℂ 2 (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) :=
  (memLp_two_circlePoissonPrefixOuterFactor a N).toLp
    (circlePoissonPrefixOuterFactor a N)

theorem norm_circlePoissonPrefixOuterFactorLp
    (a : ℕ → CirclePoissonParameter) (N : ℕ) :
    ‖circlePoissonPrefixOuterFactorLp a N‖ = 1 := by
  have hsq : ‖circlePoissonPrefixOuterFactorLp a N‖ ^ 2 = 1 := by
    unfold circlePoissonPrefixOuterFactorLp
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    have hmem := memLp_two_circlePoissonPrefixOuterFactor a N
    calc
      (∫ x, ‖(hmem.toLp (circlePoissonPrefixOuterFactor a N)) x‖ ^ 2
          ∂natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) =
          ∫ x, ‖circlePoissonPrefixOuterFactor a N x‖ ^ 2
            ∂natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter) := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hmem] with x hx
        rw [hx]
      _ = ∫ x, circlePoissonPrefixHalfLikelihood a
          (fun _ => zeroCirclePoissonParameter) N x ^ 2
            ∂natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [norm_circlePoissonPrefixOuterFactor]
      _ = 1 := integral_sq_circlePoissonPrefixHalfLikelihood a
        (fun _ => zeroCirclePoissonParameter) N
  nlinarith [norm_nonneg (circlePoissonPrefixOuterFactorLp a N)]

theorem integral_circlePoissonMeasure_zero_complex (f : Circle → ℂ) :
    (∫ z, f z ∂circlePoissonMeasure zeroCirclePoissonParameter) =
      ∫ z, f z ∂circleLebesgue := by
  rw [integral_circlePoissonMeasure_complex_eq]
  apply integral_congr_ae
  filter_upwards with z
  simp [zeroCirclePoissonParameter, poissonKernel_def]

theorem integral_ofReal_complex
    {A : Type*} [MeasurableSpace A] {mu : Measure A} {f : A → ℝ}
    (hf : Integrable f mu) :
    ∫ x, ((f x : ℝ) : ℂ) ∂mu = ((∫ x, f x ∂mu : ℝ) : ℂ) := by
  rw [← Complex.ofRealCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hf]
  rfl

theorem integral_conj_outer_mul_outer (a : CirclePoissonParameter) :
    (∫ z : Circle, conj (circlePoissonOuterFactor a z) *
        circlePoissonOuterFactor a z
        ∂circlePoissonMeasure zeroCirclePoissonParameter) = 1 := by
  rw [integral_circlePoissonMeasure_zero_complex]
  have hreal := integral_sq_circlePoissonHalfDensity a
  have hpoint : (fun z : Circle => conj (circlePoissonOuterFactor a z) *
      circlePoissonOuterFactor a z) =
      fun z => ((circlePoissonHalfDensity a z ^ 2 : ℝ) : ℂ) := by
    funext z
    rw [mul_comm, Complex.mul_conj']
    exact_mod_cast (show ‖circlePoissonOuterFactor a z‖ ^ 2 =
      circlePoissonHalfDensity a z ^ 2 by
        rw [norm_sq_circlePoissonOuterFactor, circlePoissonHalfDensity_sq])
  rw [hpoint, integral_ofReal_complex]
  · norm_cast
  · exact ((continuous_circlePoissonHalfDensity a).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem integral_outer_zeroCirclePoissonMeasure (a : CirclePoissonParameter) :
    (∫ z : Circle, circlePoissonOuterFactor a z
      ∂circlePoissonMeasure zeroCirclePoissonParameter) =
      (Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) : ℂ) := by
  rw [integral_circlePoissonMeasure_zero_complex]
  exact integral_circlePoissonOuterFactor a

private theorem circlePoissonPrefixOuterFactor_eq_prod_range
    (a : ℕ → CirclePoissonParameter) (N : ℕ) (x : ℕ → Circle) :
    circlePoissonPrefixOuterFactor a N x =
      ∏ n ∈ Finset.range N, circlePoissonOuterFactor (a n) (x n) :=
  Finset.prod_attach (Finset.range N)
    (fun n => circlePoissonOuterFactor (a n) (x n))

private def circlePoissonOuterCrossLocal
    (a : ℕ → CirclePoissonParameter) (M n : ℕ) (z : Circle) : ℂ :=
  if n < M then conj (circlePoissonOuterFactor (a n) z) *
    circlePoissonOuterFactor (a n) z
  else circlePoissonOuterFactor (a n) z

private theorem continuous_circlePoissonOuterCrossLocal
    (a : ℕ → CirclePoissonParameter) (M n : ℕ) :
    Continuous (circlePoissonOuterCrossLocal a M n) := by
  by_cases h : n < M
  · have heq : circlePoissonOuterCrossLocal a M n =
        fun z => conj (circlePoissonOuterFactor (a n) z) *
          circlePoissonOuterFactor (a n) z := by
      funext z
      simp [circlePoissonOuterCrossLocal, h]
    rw [heq]
    exact (continuous_circlePoissonOuterFactor (a n)).star.mul
      (continuous_circlePoissonOuterFactor (a n))
  · have heq : circlePoissonOuterCrossLocal a M n =
        circlePoissonOuterFactor (a n) := by
      funext z
      simp [circlePoissonOuterCrossLocal, h]
    rw [heq]
    exact continuous_circlePoissonOuterFactor (a n)

private theorem conj_prefixOuter_mul_prefixOuter_eq_crossLocal_prod
    (a : ℕ → CirclePoissonParameter) {M N : ℕ} (hMN : M ≤ N) (x : ℕ → Circle) :
    conj (circlePoissonPrefixOuterFactor a M x) *
        circlePoissonPrefixOuterFactor a N x =
      ∏ n : ↑(Finset.range N), circlePoissonOuterCrossLocal a M n (x n) := by
  rw [circlePoissonPrefixOuterFactor_eq_prod_range,
    circlePoissonPrefixOuterFactor_eq_prod_range, map_prod]
  rw [show (∏ n : ↑(Finset.range N), circlePoissonOuterCrossLocal a M n (x n)) =
      ∏ n ∈ Finset.range N, circlePoissonOuterCrossLocal a M n (x n) from
    Finset.prod_attach (Finset.range N)
      (fun n => circlePoissonOuterCrossLocal a M n (x n))]
  let L : ℕ → ℂ := fun n => circlePoissonOuterFactor (a n) (x n)
  have hsub : Finset.range M ⊆ Finset.range N := Finset.range_mono hMN
  have hdiff : Finset.range N \ Finset.range M = Finset.Ico M N := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
    omega
  have hsplit := Finset.prod_sdiff (f := L) hsub
  rw [hdiff] at hsplit
  change (∏ n ∈ Finset.range M, conj (L n)) * (∏ n ∈ Finset.range N, L n) = _
  rw [← hsplit]
  have hcross :
      (∏ n ∈ Finset.range N, circlePoissonOuterCrossLocal a M n (x n)) =
        (∏ n ∈ Finset.range M, conj (L n) * L n) *
          ∏ n ∈ Finset.Ico M N, L n := by
    have hunion : Finset.range M ∪ Finset.Ico M N = Finset.range N := by
      ext n
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range M) (Finset.Ico M N) :=
      Finset.disjoint_left.2 fun n hn hIco => by
        simp only [Finset.mem_range] at hn
        simp only [Finset.mem_Ico] at hIco
        omega
    rw [← hunion, Finset.prod_union hdisj]
    congr 1
    · apply Finset.prod_congr rfl
      intro n hn
      simp [circlePoissonOuterCrossLocal, Finset.mem_range.mp hn, L]
    · apply Finset.prod_congr rfl
      intro n hn
      have hnIco := Finset.mem_Ico.mp hn
      simp [circlePoissonOuterCrossLocal, show ¬ n < M by omega, L]
  rw [hcross, Finset.prod_mul_distrib]
  ring

/-- Tail overlap of two finite analytic Euler products. -/
def circlePoissonOuterIntervalOverlap
    (a : ℕ → CirclePoissonParameter) (M N : ℕ) : ℝ :=
  ∏ n ∈ Finset.Ico M N, Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2)

theorem integral_conj_prefixOuter_mul_prefixOuter
    (a : ℕ → CirclePoissonParameter) {M N : ℕ} (hMN : M ≤ N) :
    (∫ x, conj (circlePoissonPrefixOuterFactor a M x) *
        circlePoissonPrefixOuterFactor a N x
        ∂natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) =
      (circlePoissonOuterIntervalOverlap a M N : ℂ) := by
  rw [integral_congr_ae (Eventually.of_forall fun x =>
    conj_prefixOuter_mul_prefixOuter_eq_crossLocal_prod a hMN x)]
  have h := integral_finset_coordProd_natCirclePoissonProduct_complex
    (fun _ => zeroCirclePoissonParameter) (Finset.range N)
    (fun n z => circlePoissonOuterCrossLocal a M n z)
    (fun n => continuous_circlePoissonOuterCrossLocal a M n)
  rw [h]
  rw [show (∏ n : ↑(Finset.range N),
      ∫ z, circlePoissonOuterCrossLocal a M n z
        ∂circlePoissonMeasure zeroCirclePoissonParameter) =
      ∏ n ∈ Finset.range N,
        ∫ z, circlePoissonOuterCrossLocal a M n z
          ∂circlePoissonMeasure zeroCirclePoissonParameter from
    Finset.prod_attach (Finset.range N)
      (fun n => ∫ z, circlePoissonOuterCrossLocal a M n z
        ∂circlePoissonMeasure zeroCirclePoissonParameter)]
  have hlocal (n : ℕ) :
      (∫ z, circlePoissonOuterCrossLocal a M n z
          ∂circlePoissonMeasure zeroCirclePoissonParameter) =
        if n < M then 1 else (Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℂ) := by
    by_cases hn : n < M
    · simp only [circlePoissonOuterCrossLocal, hn, if_true,
        integral_conj_outer_mul_outer]
    · simp only [circlePoissonOuterCrossLocal, hn, if_false,
        integral_outer_zeroCirclePoissonMeasure]
  simp_rw [hlocal]
  have hunion : Finset.range M ∪ Finset.Ico M N = Finset.range N := by
    ext n
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range M) (Finset.Ico M N) :=
    Finset.disjoint_left.2 fun n hn hIco => by
      simp only [Finset.mem_range] at hn
      simp only [Finset.mem_Ico] at hIco
      omega
  rw [← hunion, Finset.prod_union hdisj]
  have hhead : (∏ n ∈ Finset.range M,
      if n < M then (1 : ℂ)
      else (Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℂ)) = 1 := by
    apply Finset.prod_eq_one
    intro n hn
    simp [Finset.mem_range.mp hn]
  have htail : (∏ n ∈ Finset.Ico M N,
      if n < M then (1 : ℂ)
      else (Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℂ)) =
      (circlePoissonOuterIntervalOverlap a M N : ℂ) := by
    unfold circlePoissonOuterIntervalOverlap
    push_cast
    apply Finset.prod_congr rfl
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    simp [show ¬ n < M by omega]
  rw [hhead, htail, one_mul]

theorem inner_circlePoissonPrefixOuterFactorLp
    (a : ℕ → CirclePoissonParameter) {M N : ℕ} (hMN : M ≤ N) :
    inner ℂ (circlePoissonPrefixOuterFactorLp a M)
        (circlePoissonPrefixOuterFactorLp a N) =
      (circlePoissonOuterIntervalOverlap a M N : ℂ) := by
  unfold circlePoissonPrefixOuterFactorLp
  rw [MeasureTheory.L2.inner_def]
  have hM := MemLp.coeFn_toLp (memLp_two_circlePoissonPrefixOuterFactor a M)
  have hN := MemLp.coeFn_toLp (memLp_two_circlePoissonPrefixOuterFactor a N)
  calc
    (∫ x, inner ℂ ((circlePoissonPrefixOuterFactorLp a M) x)
        ((circlePoissonPrefixOuterFactorLp a N) x)
        ∂natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) =
        ∫ x, conj (circlePoissonPrefixOuterFactor a M x) *
          circlePoissonPrefixOuterFactor a N x
          ∂natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter) := by
      apply integral_congr_ae
      filter_upwards [hM, hN] with x hxM hxN
      rw [RCLike.inner_apply]
      change
        ((memLp_two_circlePoissonPrefixOuterFactor a N).toLp
            (circlePoissonPrefixOuterFactor a N) x) *
          conj ((memLp_two_circlePoissonPrefixOuterFactor a M).toLp
            (circlePoissonPrefixOuterFactor a M) x) = _
      rw [hxM, hxN]
      ring
    _ = _ := integral_conj_prefixOuter_mul_prefixOuter a hMN

theorem norm_sq_circlePoissonPrefixOuterFactorLp_sub
    (a : ℕ → CirclePoissonParameter) {M N : ℕ} (hMN : M ≤ N) :
    ‖circlePoissonPrefixOuterFactorLp a M -
        circlePoissonPrefixOuterFactorLp a N‖ ^ 2 =
      2 * (1 - circlePoissonOuterIntervalOverlap a M N) := by
  have hpolar := norm_sub_sq (𝕜 := ℂ)
    (circlePoissonPrefixOuterFactorLp a M)
    (circlePoissonPrefixOuterFactorLp a N)
  rw [norm_circlePoissonPrefixOuterFactorLp,
    norm_circlePoissonPrefixOuterFactorLp,
    inner_circlePoissonPrefixOuterFactorLp a hMN] at hpolar
  norm_num at hpolar
  nlinarith

theorem circlePoissonOuterNormalizer_nonneg (a : CirclePoissonParameter) :
    0 ≤ Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) := Real.sqrt_nonneg _

theorem circlePoissonOuterNormalizer_le_one (a : CirclePoissonParameter) :
    Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) ≤ 1 := by
  have ha' : dist (a : ℂ) 0 < 1 := Metric.mem_ball.mp a.2
  have ha : ‖(a : ℂ)‖ < 1 := by simpa only [dist_zero_right] using ha'
  have hx0 : 0 ≤ 1 - ‖(a : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg (a : ℂ)]
  have hsquare := Real.sq_sqrt hx0
  nlinarith [Real.sqrt_nonneg (1 - ‖(a : ℂ)‖ ^ 2),
    sq_nonneg (Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) - 1)]

theorem one_sub_circlePoissonOuterNormalizer_le_norm_sq
    (a : CirclePoissonParameter) :
    1 - Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) ≤ ‖(a : ℂ)‖ ^ 2 := by
  have ha' : dist (a : ℂ) 0 < 1 := Metric.mem_ball.mp a.2
  have ha : ‖(a : ℂ)‖ < 1 := by simpa only [dist_zero_right] using ha'
  have hx0 : 0 ≤ 1 - ‖(a : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg (a : ℂ)]
  have hsquare := Real.sq_sqrt hx0
  have hsqrt1 := circlePoissonOuterNormalizer_le_one a
  nlinarith [Real.sqrt_nonneg (1 - ‖(a : ℂ)‖ ^ 2)]

/-- Square-summable disk parameters make normalized analytic Euler prefixes Cauchy in Haar `L²`. -/
theorem cauchySeq_circlePoissonPrefixOuterFactorLp
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2)) :
    CauchySeq (circlePoissonPrefixOuterFactorLp a) := by
  rw [Metric.cauchySeq_iff]
  intro epsilon hepsilon
  let d : ℕ → ℝ := fun n => 1 - Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2)
  have hd0 : ∀ n, 0 ≤ d n := fun n =>
    sub_nonneg.mpr (circlePoissonOuterNormalizer_le_one (a n))
  have hdle : ∀ n, d n ≤ ‖(a n : ℂ)‖ ^ 2 := fun n =>
    one_sub_circlePoissonOuterNormalizer_le_norm_sq (a n)
  have hdsum : Summable d := by
    apply Summable.of_nonneg_of_le hd0 hdle
    exact hsum
  have hfactor0 : ∀ n, 0 ≤ Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) := fun n =>
    circlePoissonOuterNormalizer_nonneg (a n)
  have hfactor1 : ∀ n, Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) ≤ 1 := fun n =>
    circlePoissonOuterNormalizer_le_one (a n)
  have hdelta : 0 < epsilon ^ 2 / 8 := by positivity
  obtain ⟨K, hK⟩ := HTGeometry.exists_forall_Ico_sum_le
    (c := d) hdsum hd0 hdelta
  refine ⟨K, ?_⟩
  have hord : ∀ m ≥ K, ∀ n ≥ K, m ≤ n →
      dist (circlePoissonPrefixOuterFactorLp a m)
        (circlePoissonPrefixOuterFactorLp a n) < epsilon := by
    intro m hm n hn hmn
    have hsub : Finset.Ico m n ⊆ Finset.Ico K n := by
      intro j hj
      simp only [Finset.mem_Ico] at hj ⊢
      omega
    have hsumTail : (∑ j ∈ Finset.Ico m n, d j) ≤ epsilon ^ 2 / 8 :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun j _ _ => hd0 j)).trans (hK n)
    have hprod : 1 - circlePoissonOuterIntervalOverlap a m n ≤
        ∑ j ∈ Finset.Ico m n, d j := by
      unfold circlePoissonOuterIntervalOverlap
      simpa [d] using one_sub_prod_le_sum_one_sub (Finset.Ico m n)
        (fun j => Real.sqrt (1 - ‖(a j : ℂ)‖ ^ 2)) hfactor0 hfactor1
    have hnormsq := norm_sq_circlePoissonPrefixOuterFactorLp_sub a hmn
    rw [dist_eq_norm]
    have hnorm0 : 0 ≤ ‖circlePoissonPrefixOuterFactorLp a m -
        circlePoissonPrefixOuterFactorLp a n‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖circlePoissonPrefixOuterFactorLp a m -
      circlePoissonPrefixOuterFactorLp a n‖ - epsilon)]
  intro m hm n hn
  rcases le_total m n with hmn | hnm
  · exact hord m hm n hn hmn
  · rw [dist_comm]
    exact hord n hn m hm hnm

theorem exists_tendsto_circlePoissonPrefixOuterFactorLp
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2)) :
    ∃ F : Lp ℂ 2
        (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)),
      Tendsto (circlePoissonPrefixOuterFactorLp a) atTop (nhds F) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_circlePoissonPrefixOuterFactorLp a hsum)

/-- Strong `L²` limit of normalized analytic Euler prefixes. -/
def circlePoissonOuterFactorLimitLp
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2)) :
    Lp ℂ 2 (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) :=
  Classical.choose (exists_tendsto_circlePoissonPrefixOuterFactorLp a hsum)

theorem tendsto_circlePoissonPrefixOuterFactorLp
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2)) :
    Tendsto (circlePoissonPrefixOuterFactorLp a) atTop
      (nhds (circlePoissonOuterFactorLimitLp a hsum)) :=
  Classical.choose_spec (exists_tendsto_circlePoissonPrefixOuterFactorLp a hsum)

/-! ## Pointwise modulus as a contraction on `L²` -/

/-- Pointwise norm of a Bochner `L²` class, as a real `L²` class. -/
def lpPointwiseNorm
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {mu : Measure A} (F : Lp E 2 mu) : Lp ℝ 2 mu :=
  (Lp.memLp F).norm.toLp (fun x => ‖F x‖)

theorem coeFn_lpPointwiseNorm
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {mu : Measure A} (F : Lp E 2 mu) :
    (lpPointwiseNorm F : A → ℝ) =ᵐ[mu] fun x => ‖F x‖ :=
  MemLp.coeFn_toLp (Lp.memLp F).norm

/-- Reverse triangle inequality makes pointwise modulus a contraction on every `L²`. -/
theorem norm_lpPointwiseNorm_sub_le
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {mu : Measure A} (F G : Lp E 2 mu) :
    ‖lpPointwiseNorm F - lpPointwiseNorm G‖ ≤ ‖F - G‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.memLp (F - G)).eLpNorm_ne_top
  apply eLpNorm_mono_ae
  filter_upwards [Lp.coeFn_sub (lpPointwiseNorm F) (lpPointwiseNorm G),
    coeFn_lpPointwiseNorm F, coeFn_lpPointwiseNorm G,
    Lp.coeFn_sub F G] with x hnormSub hF hG hsub
  rw [hnormSub, hsub]
  change ‖(lpPointwiseNorm F : A → ℝ) x -
      (lpPointwiseNorm G : A → ℝ) x‖ ≤ ‖(F : A → E) x - (G : A → E) x‖
  rw [hF, hG, Real.norm_eq_abs]
  exact abs_norm_sub_norm_le (F x) (G x)

theorem tendsto_lpPointwiseNorm
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    {mu : Measure A} {l : Filter ℕ} {F : ℕ → Lp E 2 mu} {G : Lp E 2 mu}
    (hF : Tendsto F l (nhds G)) :
    Tendsto (fun n => lpPointwiseNorm (F n)) l (nhds (lpPointwiseNorm G)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hF ⊢
  exact squeeze_zero'
    (Eventually.of_forall fun n => norm_nonneg _)
    (Eventually.of_forall fun n => norm_lpPointwiseNorm_sub_le (F n) G)
    hF

/-- At every finite stage, taking modulus of the analytic Euler prefix gives the positive
half-likelihood prefix exactly as an `L²` class. -/
theorem lpPointwiseNorm_circlePoissonPrefixOuterFactorLp
    (a : ℕ → CirclePoissonParameter) (N : ℕ) :
    lpPointwiseNorm (circlePoissonPrefixOuterFactorLp a N) =
      circlePoissonPrefixHalfLikelihoodLp a
        (fun _ => zeroCirclePoissonParameter) N := by
  unfold lpPointwiseNorm circlePoissonPrefixOuterFactorLp
  unfold circlePoissonPrefixHalfLikelihoodLp
  rw [MemLp.toLp_eq_toLp_iff]
  filter_upwards [MemLp.coeFn_toLp
    (memLp_two_circlePoissonPrefixOuterFactor a N)] with x hx
  rw [hx, norm_circlePoissonPrefixOuterFactor]

theorem lpPointwiseNorm_circlePoissonOuterFactorLimitLp_eq
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2))
    {G : Lp ℝ 2
      (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter))}
    (hG : Tendsto (circlePoissonPrefixHalfLikelihoodLp a
        (fun _ => zeroCirclePoissonParameter)) atTop (nhds G)) :
    lpPointwiseNorm (circlePoissonOuterFactorLimitLp a hsum) = G := by
  have hmod := tendsto_lpPointwiseNorm
    (tendsto_circlePoissonPrefixOuterFactorLp a hsum)
  have heq : (fun N => lpPointwiseNorm (circlePoissonPrefixOuterFactorLp a N)) =
      circlePoissonPrefixHalfLikelihoodLp a
        (fun _ => zeroCirclePoissonParameter) := by
    funext N
    exact lpPointwiseNorm_circlePoissonPrefixOuterFactorLp a N
  rw [heq] at hmod
  exact tendsto_nhds_unique hmod hG

/-- Squared modulus of an analytic Haar `L²` vector, as a density measure. -/
def circlePoissonOuterDensityMeasure
    (F : Lp ℂ 2
      (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter))) :
    Measure (ℕ → Circle) :=
  (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)).withDensity
    fun x => ENNReal.ofReal ((lpPointwiseNorm F x) ^ 2)

/-- Exact spectral factorization: the product-Poisson law is Haar weighted by the squared modulus
of the strong `L²` Euler-product limit. -/
theorem natCirclePoissonProductMeasure_eq_outerDensityMeasure
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2))
    (hhell : Summable (fun n => 1 - circlePoissonHellingerAffinity
      (a n) zeroCirclePoissonParameter)) :
    natCirclePoissonProductMeasure a =
      circlePoissonOuterDensityMeasure (circlePoissonOuterFactorLimitLp a hsum) := by
  obtain ⟨G, hG⟩ := exists_tendsto_circlePoissonPrefixHalfLikelihoodLp a
    (fun _ => zeroCirclePoissonParameter) hhell
  have hmod := lpPointwiseNorm_circlePoissonOuterFactorLimitLp_eq a hsum hG
  rw [natCirclePoissonProductMeasure_eq_circlePoissonLimitDensityMeasure a
    (fun _ => zeroCirclePoissonParameter) hG]
  unfold circlePoissonLimitDensityMeasure circlePoissonOuterDensityMeasure
  rw [hmod]

/-- Fourier coefficient of one normalized analytic outer factor. -/
theorem integral_conj_zpow_mul_circlePoissonOuterFactor
    (a : CirclePoissonParameter) (k : ℤ) :
    (∫ z : Circle, conj ((z : ℂ) ^ k) * circlePoissonOuterFactor a z
      ∂circleLebesgue) =
      if 0 ≤ k then
        (Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) : ℂ) * conj (a : ℂ) ^ k.toNat
      else 0 := by
  let c : ℂ := conj (a : ℂ)
  have ha' : dist (a : ℂ) 0 < 1 := Metric.mem_ball.mp a.2
  have ha : ‖(a : ℂ)‖ < 1 := by simpa only [dist_zero_right] using ha'
  have hc : ‖c‖ < 1 := by simpa [c] using ha
  let term : ℕ → Circle → ℂ := fun n z => conj ((z : ℂ) ^ k) * (c ^ n * (z : ℂ) ^ n)
  have hconj_zpow (z : Circle) :
      conj ((z : ℂ) ^ k) = (z : ℂ) ^ (-k) := by
    rw [show conj ((z : ℂ) ^ k) = conj (z : ℂ) ^ k from
      map_zpow₀ (starRingEnd ℂ) (z : ℂ) k]
    have hconj : conj (z : ℂ) = (z : ℂ)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, Circle.norm_coe]
      norm_num
    rw [hconj, inv_zpow']
  have hterm (n : ℕ) (z : Circle) :
      term n z = c ^ n * (z : ℂ) ^ ((n : ℤ) - k) := by
    change conj ((z : ℂ) ^ k) * (c ^ n * (z : ℂ) ^ n) = _
    rw [hconj_zpow, ← zpow_natCast]
    calc
      (z : ℂ) ^ (-k) * (c ^ n * (z : ℂ) ^ (n : ℤ)) =
          c ^ n * ((z : ℂ) ^ (-k) * (z : ℂ) ^ (n : ℤ)) := by ring
      _ = c ^ n * (z : ℂ) ^ ((-k) + n) := by
        rw [zpow_add₀ (Circle.coe_ne_zero z)]
      _ = _ := by congr 2; omega
  have htermInt : ∀ n, Integrable (term n) circleLebesgue := by
    intro n
    have hcont : Continuous (term n) := by
      rw [funext (hterm n)]
      exact Continuous.const_mul (Continuous.zpow₀ continuous_subtype_val _
        (fun z => Or.inl (Circle.coe_ne_zero z))) _
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have htermNorm (n : ℕ) :
      ∫ z : Circle, ‖term n z‖ ∂circleLebesgue = ‖c‖ ^ n := by
    simp [term]
  have hsumNorm : Summable (fun n => ∫ z : Circle, ‖term n z‖ ∂circleLebesgue) := by
    have hgeom := (summable_geometric_of_norm_lt_one hc).norm
    simpa only [htermNorm, norm_pow] using hgeom
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm htermInt hsumNorm
  have hpoint (z : Circle) :
      ∑' n : ℕ, term n z =
        conj ((z : ℂ) ^ k) * (1 - c * (z : ℂ))⁻¹ := by
    have hcz : ‖c * (z : ℂ)‖ < 1 := by
      rw [norm_mul, Circle.norm_coe, mul_one]
      exact hc
    rw [tsum_mul_left]
    congr 1
    simpa [term, mul_pow] using (hasSum_geometric_of_norm_lt_one hcz).tsum_eq
  have htermIntegral (n : ℕ) :
      (∫ z : Circle, term n z ∂circleLebesgue) =
        c ^ n * if (n : ℤ) - k = 0 then 1 else 0 := by
    rw [integral_congr_ae (Eventually.of_forall (hterm n)),
      MeasureTheory.integral_const_mul, integral_circleLebesgue_coe_zpow]
  have hinterms :
      (∑' n : ℕ, ∫ z : Circle, term n z ∂circleLebesgue) =
        if 0 ≤ k then c ^ k.toNat else 0 := by
    by_cases hk : 0 ≤ k
    · rw [if_pos hk, tsum_eq_single k.toNat]
      · rw [htermIntegral, Int.toNat_of_nonneg hk, sub_self, if_pos rfl, mul_one]
      · intro n hn
        rw [htermIntegral]
        have hne : (n : ℤ) - k ≠ 0 := by
          intro hzero
          have : n = k.toNat := by
            exact_mod_cast (sub_eq_zero.mp hzero).trans (Int.toNat_of_nonneg hk).symm
          exact hn this
        simp [hne]
    · rw [if_neg hk]
      have hzero : (fun n : ℕ => ∫ z : Circle, term n z ∂circleLebesgue) =
          fun _ => 0 := by
        funext n
        rw [htermIntegral]
        have hne : (n : ℤ) - k ≠ 0 := by omega
        simp [hne]
      rw [hzero, tsum_zero]
  unfold circlePoissonOuterFactor
  rw [show (fun z : Circle =>
      conj ((z : ℂ) ^ k) *
        ((Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) : ℂ) /
          (1 - conj (a : ℂ) * (z : ℂ)))) =
      fun z => (Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) : ℂ) *
        ∑' n : ℕ, term n z by
    funext z
    rw [hpoint]
    simp [c, div_eq_mul_inv]
    ring]
  rw [MeasureTheory.integral_const_mul, ← hswap, hinterms]
  by_cases hk : 0 ≤ k
  · rw [if_pos hk, if_pos hk]
  · rw [if_neg hk, if_neg hk, mul_zero]

theorem integral_conj_zpow_mul_circlePoissonOuterFactor_zeroMeasure
    (a : CirclePoissonParameter) (k : ℤ) :
    (∫ z : Circle, conj ((z : ℂ) ^ k) * circlePoissonOuterFactor a z
      ∂circlePoissonMeasure zeroCirclePoissonParameter) =
      if 0 ≤ k then
        (Real.sqrt (1 - ‖(a : ℂ)‖ ^ 2) : ℂ) * conj (a : ℂ) ^ k.toNat
      else 0 := by
  rw [integral_circlePoissonMeasure_zero_complex]
  exact integral_conj_zpow_mul_circlePoissonOuterFactor a k

/-- Exact full Laurent coefficient of a finite normalized analytic prefix once the prefix contains
the character support. -/
theorem integral_conj_infiniteCircleFourier_mul_prefixOuter
    (a : ℕ → CirclePoissonParameter) (q : ℕ →₀ ℤ) (N : ℕ)
    (hq : q.support ⊆ Finset.range N) :
    (∫ x, conj (infiniteCircleFourier q x) *
        circlePoissonPrefixOuterFactor a N x
        ∂natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) =
      ∏ n : ↑(Finset.range N),
        if 0 ≤ q n then
          (Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℂ) *
            conj (a n : ℂ) ^ (q n).toNat
        else 0 := by
  classical
  have hchar (x : ℕ → Circle) :
      infiniteCircleFourier q x =
        ∏ n ∈ Finset.range N, (x n : ℂ) ^ q n := by
    rw [infiniteCircleFourier]
    exact Finset.prod_subset hq fun n hnRange hnSupport => by
      simp only [Finsupp.mem_support_iff] at hnSupport
      simp [not_not.mp hnSupport]
  have hfun : (fun x : ℕ → Circle =>
      conj (infiniteCircleFourier q x) *
        circlePoissonPrefixOuterFactor a N x) =
      fun x => ∏ n : ↑(Finset.range N),
        conj ((x n : ℂ) ^ q n) * circlePoissonOuterFactor (a n) (x n) := by
    funext x
    rw [hchar, map_prod, circlePoissonPrefixOuterFactor]
    rw [show (∏ n ∈ Finset.range N, conj ((x n : ℂ) ^ q n)) =
        ∏ n : ↑(Finset.range N), conj ((x n : ℂ) ^ q n) from
      (Finset.prod_attach (Finset.range N)
        (fun n => conj ((x n : ℂ) ^ q n))).symm]
    exact Finset.prod_mul_distrib.symm
  rw [hfun, integral_finset_coordProd_natCirclePoissonProduct_complex
    (fun _ => zeroCirclePoissonParameter) (Finset.range N)
    (fun n z => conj ((z : ℂ) ^ q n) * circlePoissonOuterFactor (a n) z)]
  · apply Finset.prod_congr rfl
    intro n _
    exact integral_conj_zpow_mul_circlePoissonOuterFactor_zeroMeasure (a n) (q n)
  · intro n
    exact (Continuous.zpow₀ continuous_subtype_val _
      (fun z => Or.inl (Circle.coe_ne_zero z))).star.mul
        (continuous_circlePoissonOuterFactor (a n))

/-- Haar `L²` class of a finite Laurent character on the natural circle product. -/
def infiniteCircleFourierLp (q : ℕ →₀ ℤ) :
    Lp ℂ 2 (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) :=
  ContinuousMap.toLp 2
    (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) ℂ
    (infiniteCircleFourier q)

theorem inner_infiniteCircleFourierLp_prefixOuter
    (a : ℕ → CirclePoissonParameter) (q : ℕ →₀ ℤ) (N : ℕ)
    (hq : q.support ⊆ Finset.range N) :
    inner ℂ (infiniteCircleFourierLp q)
        (circlePoissonPrefixOuterFactorLp a N) =
      ∏ n : ↑(Finset.range N),
        if 0 ≤ q n then
          (Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℂ) *
            conj (a n : ℂ) ^ (q n).toNat
        else 0 := by
  rw [infiniteCircleFourierLp, circlePoissonPrefixOuterFactorLp,
    MeasureTheory.L2.inner_def]
  have hqLp := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter))
    (infiniteCircleFourier q)
  have hprefix := MemLp.coeFn_toLp (memLp_two_circlePoissonPrefixOuterFactor a N)
  rw [integral_congr_ae (by
    filter_upwards [hqLp, hprefix] with x hxq hxprefix
    change inner ℂ
      ((ContinuousMap.toLp 2
        (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) ℂ)
          (infiniteCircleFourier q) x)
      ((memLp_two_circlePoissonPrefixOuterFactor a N).toLp
        (circlePoissonPrefixOuterFactor a N) x) =
      conj (infiniteCircleFourier q x) * circlePoissonPrefixOuterFactor a N x
    rw [RCLike.inner_apply, hxq, hxprefix]
    ring)]
  exact integral_conj_infiniteCircleFourier_mul_prefixOuter a q N hq

/-- Infinite product of positive local outer normalizers. -/
def circlePoissonOuterNormalizerProduct (a : ℕ → CirclePoissonParameter) : ℝ :=
  ∏' n : ℕ, Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2)

theorem multipliable_circlePoissonOuterNormalizer
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2)) :
    Multipliable (fun n => Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2)) := by
  let d : ℕ → ℝ := fun n => 1 - Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2)
  have hd0 : ∀ n, 0 ≤ d n := fun n =>
    sub_nonneg.mpr (circlePoissonOuterNormalizer_le_one (a n))
  have hdle : ∀ n, d n ≤ ‖(a n : ℂ)‖ ^ 2 := fun n =>
    one_sub_circlePoissonOuterNormalizer_le_norm_sq (a n)
  have hdsum : Summable d := Summable.of_nonneg_of_le hd0 hdle hsum
  have hnorm : Summable (fun n => ‖-d n‖) := by
    simpa only [norm_neg, Real.norm_of_nonneg (hd0 _)] using hdsum
  have hmul := multipliable_one_add_of_summable hnorm
  have hfun : (fun n => 1 + -d n) =
      fun n => Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) := by
    funext n
    simp [d]
  rw [← hfun]
  exact hmul

theorem hasProd_circlePoissonOuterNormalizer
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2)) :
    HasProd (fun n => Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2))
      (circlePoissonOuterNormalizerProduct a) :=
  (multipliable_circlePoissonOuterNormalizer a hsum).hasProd

theorem tendsto_circlePoissonOuterNormalizer_prefix
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2)) :
    Tendsto (fun N => ∏ n ∈ Finset.range N,
      Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2)) atTop
      (nhds (circlePoissonOuterNormalizerProduct a)) :=
  (hasProd_circlePoissonOuterNormalizer a hsum).tendsto_prod_nat

theorem inner_infiniteCircleFourierLp_outerLimit_natToInt
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2)) (ν : ℕ →₀ ℕ) :
    inner ℂ (infiniteCircleFourierLp (GasWord.natToInt ν))
        (circlePoissonOuterFactorLimitLp a hsum) =
      (circlePoissonOuterNormalizerProduct a : ℂ) *
        ν.prod fun n k => conj (a n : ℂ) ^ k := by
  classical
  let K := ν.support.sup id + 1
  have hsupport : ∀ N ≥ K, (GasWord.natToInt ν).support ⊆ Finset.range N := by
    intro N hN n hn
    have hnν : n ∈ ν.support := by
      rw [Finsupp.mem_support_iff] at hn ⊢
      rw [GasWord.natToInt_apply] at hn
      exact_mod_cast hn
    rw [Finset.mem_range]
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hnν)) hN
  have hinner' : Tendsto (fun N => inner ℂ
      (infiniteCircleFourierLp (GasWord.natToInt ν))
      (circlePoissonPrefixOuterFactorLp a N)) atTop
      (nhds (inner ℂ (infiniteCircleFourierLp (GasWord.natToInt ν))
        (circlePoissonOuterFactorLimitLp a hsum))) := by
    exact tendsto_const_nhds.inner
      (tendsto_circlePoissonPrefixOuterFactorLp a hsum)
  have hevent : ∀ᶠ N in atTop,
      inner ℂ (infiniteCircleFourierLp (GasWord.natToInt ν))
        (circlePoissonPrefixOuterFactorLp a N) =
      ((∏ n ∈ Finset.range N,
          Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℝ) : ℂ) *
        ν.prod fun n k => conj (a n : ℂ) ^ k := by
    filter_upwards [eventually_ge_atTop K] with N hN
    rw [inner_infiniteCircleFourierLp_prefixOuter a _ N (hsupport N hN)]
    simp only [GasWord.natToInt_apply, Int.natCast_nonneg, if_pos, Int.toNat_natCast]
    rw [Finset.prod_mul_distrib]
    have hnormalAttach : (∏ n : ↑(Finset.range N),
        (Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℂ)) =
        ((∏ n ∈ Finset.range N,
          Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℝ) : ℂ) := by
      push_cast
      change (∏ n ∈ (Finset.range N).attach,
        (Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℂ)) =
        ∏ n ∈ Finset.range N,
          (Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℂ)
      exact Finset.prod_attach (Finset.range N)
        (fun n => (Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℂ))
    have hattach : (∏ n : ↑(Finset.range N),
        conj (a n : ℂ) ^ ν n) =
        ∏ n ∈ Finset.range N, conj (a n : ℂ) ^ ν n := by
      change (∏ n ∈ (Finset.range N).attach,
        conj (a n : ℂ) ^ ν n) = _
      exact Finset.prod_attach (Finset.range N)
        (fun n => conj (a n : ℂ) ^ ν n)
    have hmonomial : (∏ n : ↑(Finset.range N),
        conj (a n : ℂ) ^ ν n) =
        ν.prod fun n k => conj (a n : ℂ) ^ k := by
      rw [hattach, Finsupp.prod]
      exact (Finset.prod_subset (fun n hn => by
        have hn' : n < K := Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
        exact Finset.mem_range.mpr (lt_of_lt_of_le hn' hN))
        (fun n _ hn => by
          simp only [Finsupp.mem_support_iff] at hn
          simp [not_not.mp hn])).symm
    rw [hnormalAttach, hmonomial]
  have hnormalizer := (tendsto_circlePoissonOuterNormalizer_prefix a hsum).ofReal
  have htarget : Tendsto (fun N =>
      (((∏ n ∈ Finset.range N,
          Real.sqrt (1 - ‖(a n : ℂ)‖ ^ 2) : ℝ) : ℂ) *
        ν.prod fun n k => conj (a n : ℂ) ^ k)) atTop
      (nhds ((circlePoissonOuterNormalizerProduct a : ℂ) *
        ν.prod fun n k => conj (a n : ℂ) ^ k)) :=
    hnormalizer.mul tendsto_const_nhds
  have hevent' := hevent.mono fun _ h => h.symm
  exact tendsto_nhds_unique hinner' (htarget.congr' hevent')

theorem inner_infiniteCircleFourierLp_outerLimit_eq_zero_of_neg
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2))
    (q : ℕ →₀ ℤ) {j : ℕ} (hj : q j < 0) :
    inner ℂ (infiniteCircleFourierLp q)
        (circlePoissonOuterFactorLimitLp a hsum) = 0 := by
  classical
  let K := q.support.sup id + 1
  have hjSupport : j ∈ q.support := Finsupp.mem_support_iff.mpr (by omega)
  have hsupport : ∀ N ≥ K, q.support ⊆ Finset.range N := by
    intro N hN n hn
    rw [Finset.mem_range]
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)) hN
  have hinner' : Tendsto (fun N => inner ℂ
      (infiniteCircleFourierLp q) (circlePoissonPrefixOuterFactorLp a N)) atTop
      (nhds (inner ℂ (infiniteCircleFourierLp q)
        (circlePoissonOuterFactorLimitLp a hsum))) := by
    exact tendsto_const_nhds.inner
      (tendsto_circlePoissonPrefixOuterFactorLp a hsum)
  have hevent : ∀ᶠ N in atTop,
      inner ℂ (infiniteCircleFourierLp q)
        (circlePoissonPrefixOuterFactorLp a N) = 0 := by
    filter_upwards [eventually_ge_atTop K] with N hN
    rw [inner_infiniteCircleFourierLp_prefixOuter a q N (hsupport N hN)]
    refine Finset.prod_eq_zero (i := ⟨j, hsupport N hN hjSupport⟩) (by simp) ?_
    rw [if_neg (not_le.mpr hj)]
  have hevent' := hevent.mono fun _ h => h.symm
  exact tendsto_nhds_unique hinner' (tendsto_const_nhds.congr' hevent')

/-- Positive natural-exponent character in Haar `L²` of the enumerated circle product. -/
def naturalBohrCharacterLp (ν : ℕ →₀ ℕ) :
    Lp ℂ 2 (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) :=
  infiniteCircleFourierLp (GasWord.natToInt ν)

theorem inner_infiniteCircleFourierLp
    (q r : ℕ →₀ ℤ) :
    inner ℂ (infiniteCircleFourierLp q) (infiniteCircleFourierLp r) =
      if q = r then 1 else 0 := by
  rw [infiniteCircleFourierLp, infiniteCircleFourierLp, MeasureTheory.L2.inner_def]
  have hq := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter))
    (infiniteCircleFourier q)
  have hr := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter))
    (infiniteCircleFourier r)
  calc
    (∫ x, inner ℂ
        (((ContinuousMap.toLp 2
          (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) ℂ)
            (infiniteCircleFourier q)) x)
        (((ContinuousMap.toLp 2
          (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) ℂ)
            (infiniteCircleFourier r)) x)
        ∂natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) =
        ∫ x, infiniteCircleFourier (-q + r) x
          ∂natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter) := by
      apply integral_congr_ae
      filter_upwards [hq, hr] with x hxq hxr
      rw [RCLike.inner_apply, hxq, hxr]
      change infiniteCircleFourier r x * conj (infiniteCircleFourier q x) =
        infiniteCircleFourier (-q + r) x
      rw [← infiniteTorusFourier_circleProductHomeomorphUnitTorus,
        ← infiniteTorusFourier_circleProductHomeomorphUnitTorus,
        ← infiniteTorusFourier_circleProductHomeomorphUnitTorus]
      rw [← infiniteTorusFourier_neg q, ← infiniteTorusFourier_add]
      congr 1
      abel_nf
    _ = if q = r then 1 else 0 := by
      rw [integral_infiniteCircleFourier_natCirclePoissonProductMeasure]
      have hmoment (k : ℤ) :
          circlePoissonFourierMoment zeroCirclePoissonParameter k =
            if k = 0 then 1 else 0 := by
        rcases k with k | k
        · by_cases hk : k = 0 <;>
            simp [circlePoissonFourierMoment, zeroCirclePoissonParameter, hk]
        · simp [circlePoissonFourierMoment, zeroCirclePoissonParameter]
      simp_rw [hmoment]
      by_cases hqr : q = r
      · subst r
        simp
      · rw [if_neg hqr]
        have hne : -q + r ≠ 0 := by
          intro h
          exact hqr (neg_add_eq_zero.mp h)
        have hi : ∃ i ∈ (-q + r).support, (-q + r) i ≠ 0 := by
          have hsne : (-q + r).support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
            intro hempty
            apply hne
            exact Finsupp.support_eq_empty.mp hempty)
          obtain ⟨i, hi⟩ := hsne
          exact ⟨i, hi, Finsupp.mem_support_iff.mp hi⟩
        obtain ⟨i, hiSupport, hiNe⟩ := hi
        rw [Finsupp.prod]
        exact Finset.prod_eq_zero hiSupport (if_neg hiNe)

theorem GasWord.natToInt_injective_any {M : Type*} :
    Function.Injective (GasWord.natToInt (M := M)) := by
  intro ν μ h
  apply Finsupp.ext
  intro i
  have hi := DFunLike.congr_fun h i
  simp only [GasWord.natToInt_apply] at hi
  exact_mod_cast hi

theorem orthonormal_naturalBohrCharacterLp :
    Orthonormal ℂ naturalBohrCharacterLp := by
  rw [orthonormal_iff_ite]
  intro ν μ
  rw [naturalBohrCharacterLp, naturalBohrCharacterLp,
    inner_infiniteCircleFourierLp]
  by_cases h : ν = μ
  · subst μ
    simp
  · have hnat : GasWord.natToInt ν ≠ GasWord.natToInt μ :=
      fun h' => h (GasWord.natToInt_injective_any h')
    simp [h, hnat]

/-- Bohr isometry from square-summable positive natural multi-indices to Haar `L²`. -/
def naturalBohrTransform :
    lp (fun _ : ℕ →₀ ℕ => ℂ) 2 →ₗᵢ[ℂ]
      Lp ℂ 2 (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) :=
  orthonormal_naturalBohrCharacterLp.orthogonalFamily.linearIsometry

@[simp]
theorem naturalBohrTransform_single (ν : ℕ →₀ ℕ) (c : ℂ) :
    naturalBohrTransform (lp.single 2 ν c) = c • naturalBohrCharacterLp ν := by
  rw [naturalBohrTransform, OrthogonalFamily.linearIsometry_apply_single]
  rfl

theorem inner_naturalBohrCharacterLp_naturalBohrTransform
    (ν : ℕ →₀ ℕ) (c : lp (fun _ : ℕ →₀ ℕ => ℂ) 2) :
    inner ℂ (naturalBohrCharacterLp ν) (naturalBohrTransform c) = c ν := by
  calc
    inner ℂ (naturalBohrCharacterLp ν) (naturalBohrTransform c) =
        inner ℂ (naturalBohrTransform (lp.single 2 ν 1))
          (naturalBohrTransform c) := by
      rw [naturalBohrTransform_single, one_smul]
    _ = inner ℂ (lp.single 2 ν 1) c :=
      naturalBohrTransform.inner_map_map _ _
    _ = c ν := by rw [lp.inner_single_left]; simp

theorem inner_infiniteCircleFourierLp_naturalBohrTransform_eq_zero
    (q : ℕ →₀ ℤ) (c : lp (fun _ : ℕ →₀ ℕ => ℂ) 2)
    (hq : ∀ ν : ℕ →₀ ℕ, q ≠ GasWord.natToInt ν) :
    inner ℂ (infiniteCircleFourierLp q) (naturalBohrTransform c) = 0 := by
  classical
  let Φ : lp (fun _ : ℕ →₀ ℕ => ℂ) 2 →L[ℂ] ℂ :=
    (innerSL ℂ (infiniteCircleFourierLp q)).comp naturalBohrTransform.toContinuousLinearMap
  have hsum := lp.hasSum_single (p := 2) (by norm_num) c
  change Φ c = 0
  rw [← hsum.tsum_eq, Φ.map_tsum hsum.summable]
  have hzero : (fun ν : ℕ →₀ ℕ => Φ (lp.single 2 ν (c ν))) = fun _ => 0 := by
    funext ν
    change inner ℂ (infiniteCircleFourierLp q)
      (naturalBohrTransform (lp.single 2 ν (c ν))) = 0
    rw [naturalBohrTransform_single, inner_smul_right,
      naturalBohrCharacterLp, inner_infiniteCircleFourierLp, if_neg (hq ν)]
    simp
  rw [hzero, tsum_zero]

theorem exists_natToInt_eq_iff_nonneg (q : ℕ →₀ ℤ) :
    (∃ ν : ℕ →₀ ℕ, GasWord.natToInt ν = q) ↔ ∀ n, 0 ≤ q n := by
  constructor
  · rintro ⟨ν, rfl⟩ n
    simp [GasWord.natToInt_apply]
  · intro hq
    let ν : ℕ →₀ ℕ := q.mapRange Int.toNat (by simp)
    refine ⟨ν, Finsupp.ext fun n => ?_⟩
    change ((q n).toNat : ℤ) = q n
    exact Int.toNat_of_nonneg (hq n)

theorem infiniteCircleFourier_zero :
    infiniteCircleFourier (0 : ℕ →₀ ℤ) = 1 := by
  ext x
  simp [infiniteCircleFourier]

theorem infiniteCircleFourier_add (q r : ℕ →₀ ℤ) (x : ℕ → Circle) :
    infiniteCircleFourier (q + r) x =
      infiniteCircleFourier q x * infiniteCircleFourier r x := by
  rw [← infiniteTorusFourier_circleProductHomeomorphUnitTorus,
    ← infiniteTorusFourier_circleProductHomeomorphUnitTorus,
    ← infiniteTorusFourier_circleProductHomeomorphUnitTorus,
    infiniteTorusFourier_add]

theorem infiniteCircleFourier_neg (q : ℕ →₀ ℤ) (x : ℕ → Circle) :
    infiniteCircleFourier (-q) x = conj (infiniteCircleFourier q x) := by
  rw [← infiniteTorusFourier_circleProductHomeomorphUnitTorus,
    ← infiniteTorusFourier_circleProductHomeomorphUnitTorus,
    infiniteTorusFourier_neg]

/-- Star algebra generated by finite Laurent characters of the natural circle product. -/
def infiniteCircleFourierSubalgebra : StarSubalgebra ℂ C((ℕ → Circle), ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range infiniteCircleFourier)
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range infiniteCircleFourier) ≤
      star (Algebra.adjoin ℂ (Set.range infiniteCircleFourier))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨q, rfl⟩
    refine Algebra.subset_adjoin ⟨-q, ?_⟩
    ext x
    simp only [infiniteCircleFourier_neg, starRingEnd_apply,
      ContinuousMap.star_apply]

theorem infiniteCircleFourierSubalgebra_coe :
    infiniteCircleFourierSubalgebra.toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range infiniteCircleFourier) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ⟨0, ?_⟩ ?_ hx
  · exact infiniteCircleFourier_zero
  · rintro _ _ _ _ ⟨q, rfl⟩ ⟨r, rfl⟩
    exact ⟨q + r, ContinuousMap.ext fun x => infiniteCircleFourier_add q r x⟩

theorem infiniteCircleFourierSubalgebra_separatesPoints :
    infiniteCircleFourierSubalgebra.SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
  refine ⟨_, ⟨infiniteCircleFourier (Finsupp.single i 1),
    Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩, ?_⟩
  simp only [infiniteCircleFourier, ContinuousMap.coe_mk]
  simpa [Finsupp.prod_single_index] using (Subtype.coe_injective.ne hi)

/-- Finite Laurent characters are uniformly dense on the natural circle product. -/
theorem span_infiniteCircleFourier_closure_eq_top :
    (Submodule.span ℂ (Set.range infiniteCircleFourier)).topologicalClosure = ⊤ := by
  rw [← infiniteCircleFourierSubalgebra_coe]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      infiniteCircleFourierSubalgebra
      infiniteCircleFourierSubalgebra_separatesPoints)

/-- Full Laurent characters detect every vector in Haar `L²` of the natural circle product. -/
theorem eq_zero_of_inner_infiniteCircleFourierLp_eq_zero
    {v : Lp ℂ 2
      (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter))}
    (h : ∀ q : ℕ →₀ ℤ, inner ℂ (infiniteCircleFourierLp q) v = 0) :
    v = 0 := by
  let T : C((ℕ → Circle), ℂ) →L[ℂ]
      Lp ℂ 2 (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) :=
    ContinuousMap.toLp 2
      (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) ℂ
  let Φ : C((ℕ → Circle), ℂ) →L[ℂ] ℂ := (innerSL ℂ v).comp T
  have hchar : ∀ q : ℕ →₀ ℤ, Φ (infiniteCircleFourier q) = 0 := by
    intro q
    change inner ℂ v (infiniteCircleFourierLp q) = 0
    exact inner_eq_zero_symm.mpr (h q)
  have hspan : ∀ f ∈ Submodule.span ℂ (Set.range infiniteCircleFourier), Φ f = 0 := by
    intro f hf
    refine Submodule.span_induction (p := fun f _ => Φ f = 0) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨q, rfl⟩
      exact hchar q
    · exact Φ.map_zero
    · intro f g _ _ hf hg
      rw [Φ.map_add, hf, hg, add_zero]
    · intro c f _ hf
      rw [Φ.map_smul, hf, smul_zero]
  have hdenseSpan : Dense (Submodule.span ℂ (Set.range infiniteCircleFourier) :
      Set C((ℕ → Circle), ℂ)) := by
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
      span_infiniteCircleFourier_closure_eq_top
  have hΦ : (fun f => Φ f) = fun _ => 0 := by
    apply Continuous.ext_on hdenseSpan Φ.continuous continuous_const
    intro f hf
    exact hspan f hf
  have hcontinuous (f : C((ℕ → Circle), ℂ)) : inner ℂ v (T f) = 0 := by
    exact congrFun hΦ f
  have hdenseLp : DenseRange T :=
    ContinuousMap.toLp_denseRange ℂ
      (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) ℂ
      (by norm_num)
  have hLp : (fun u : Lp ℂ 2
      (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) =>
      inner ℂ v u) = fun _ => 0 := by
    apply Continuous.ext_on hdenseLp (innerSL ℂ v).continuous continuous_const
    rintro u ⟨f, rfl⟩
    exact hcontinuous f
  exact inner_self_eq_zero.mp (congrFun hLp v)

/-- Abstract exact Bohr-series identification of the analytic outer limit. -/
theorem circlePoissonOuterFactorLimitLp_eq_naturalBohrTransform
    (a : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n => ‖(a n : ℂ)‖ ^ 2))
    (c : lp (fun _ : ℕ →₀ ℕ => ℂ) 2)
    (hc : ∀ ν : ℕ →₀ ℕ, c ν =
      (circlePoissonOuterNormalizerProduct a : ℂ) *
        ν.prod fun n k => conj (a n : ℂ) ^ k) :
    circlePoissonOuterFactorLimitLp a hsum = naturalBohrTransform c := by
  apply sub_eq_zero.mp
  apply eq_zero_of_inner_infiniteCircleFourierLp_eq_zero
  intro q
  by_cases hnonneg : ∀ n, 0 ≤ q n
  · obtain ⟨ν, hν⟩ := (exists_natToInt_eq_iff_nonneg q).mpr hnonneg
    subst q
    rw [inner_sub_right, inner_infiniteCircleFourierLp_outerLimit_natToInt]
    rw [show infiniteCircleFourierLp (GasWord.natToInt ν) =
      naturalBohrCharacterLp ν from rfl,
      inner_naturalBohrCharacterLp_naturalBohrTransform, hc, sub_self]
  · simp only [not_forall] at hnonneg
    obtain ⟨j, hjnot⟩ := hnonneg
    have hj : q j < 0 := lt_of_not_ge hjnot
    rw [inner_sub_right,
      inner_infiniteCircleFourierLp_outerLimit_eq_zero_of_neg a hsum q hj]
    have hq : ∀ ν : ℕ →₀ ℕ, q ≠ GasWord.natToInt ν := by
      intro ν h
      have := DFunLike.congr_fun h j
      simp only [GasWord.natToInt_apply] at this
      omega
    rw [inner_infiniteCircleFourierLp_naturalBohrTransform_eq_zero q c hq,
      sub_zero]


end
end GaloisForLFunctions.HTGeometry
