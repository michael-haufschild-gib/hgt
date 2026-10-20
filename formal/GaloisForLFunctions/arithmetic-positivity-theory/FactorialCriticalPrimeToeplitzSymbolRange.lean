import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeScaleCoupling

/-!
# Toeplitz symbol and sharp spectral range of the critical prime form

The limiting translated prime form is the Toeplitz form
`P∞(b) = (4/π⁴) Σ_{i,j} b_i b_j κ(|i-j|)` of the scale couplings `κ(k) = ∫₀¹ R(t) cos(2πkt) dt`.
The critical kernel `R` is continuous on the cell and symmetric about its midpoint, so its
sine moments vanish and its Fourier coefficients are exactly `κ(|n|)`; the couplings are
`O(1/k²)`, and Fourier inversion on the circle gives the **symbol law**
`R(t) = Σ_{n ∈ ℤ} κ(|n|) cos(2πnt)`.

For the cosine and sine patterns of frequency `t` on `[0,L)`, the Toeplitz counting identity
(lag `n` occurs `L - n` times, twice for `n ≠ 0`) and dominated convergence show that the sum of
their two prime energies divided by their total energy `L` tends to `(4/π⁴) R(t)`. A mediant
argument selects one of the two patterns, so the Rayleigh quotients of `P∞` come arbitrarily
close to `(4/π⁴) R(t)` from both sides. Hence the exact spectral range of the limiting critical
prime form over all finite patterns is `[(4/π⁴) min R, (4/π⁴) max R]`, and the optimal
negativity constant is `-(4/π⁴) max R`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The critical kernel is symmetric about the midpoint of the cell. -/
theorem factorialCriticalPrimeContinuousRealKernel_reflect (t : ℝ) :
    factorialCriticalPrimeContinuousRealKernel (1 - t) = factorialCriticalPrimeContinuousRealKernel t := by
  unfold factorialCriticalPrimeContinuousRealKernel
  rw [sub_sub_cancel]; ring

private theorem natAbs_cast_eq_abs (n : ℤ) : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

private theorem cos_natAbs (n : ℤ) (x : ℝ) :
    Real.cos (2 * Real.pi * (n.natAbs : ℕ) * x) = Real.cos (2 * Real.pi * n * x) := by
  rw [natAbs_cast_eq_abs]
  rcases abs_choice (n : ℝ) with h | h <;> rw [h]
  rw [show 2 * Real.pi * -(n : ℝ) * x = -(2 * Real.pi * n * x) by ring, Real.cos_neg]

/-- The sine moments of the critical kernel vanish by its reflection symmetry. -/
theorem integral_factorialCriticalPrimeContinuousRealKernel_mul_sin (n : ℤ) :
    ∫ t in (0 : ℝ)..1, factorialCriticalPrimeContinuousRealKernel t * Real.sin (2 * Real.pi * n * t) = 0 := by
  set R := factorialCriticalPrimeContinuousRealKernel
  have h := intervalIntegral.integral_comp_sub_left
    (fun t => R t * Real.sin (2 * Real.pi * n * t)) (a := 0) (b := 1) 1
  simp only [sub_zero, sub_self] at h
  have hpt (t : ℝ) : R (1 - t) * Real.sin (2 * Real.pi * n * (1 - t)) =
      -(R t * Real.sin (2 * Real.pi * n * t)) := by
    rw [show R (1 - t) = R t from factorialCriticalPrimeContinuousRealKernel_reflect t,
      show 2 * Real.pi * n * (1 - t) = ((2 * n : ℤ) : ℝ) * Real.pi - 2 * Real.pi * n * t by push_cast; ring,
      Real.sin_sub, Real.sin_int_mul_pi,
      show ((2 * n : ℤ) : ℝ) * Real.pi = (n : ℝ) * (2 * Real.pi) by push_cast; ring, Real.cos_int_mul_two_pi]
    ring
  simp only [hpt, intervalIntegral.integral_neg] at h
  linarith

private theorem intervalIntegrable_kernel_mul {g : ℝ → ℝ} (hg : Continuous g) :
    IntervalIntegrable (fun t => ((factorialCriticalPrimeContinuousRealKernel t * g t : ℝ) : ℂ)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  exact Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_factorialCriticalPrimeContinuousRealKernel.mul hg.continuousOn)

/-- The `n`-th Fourier coefficient of the critical kernel on the unit cell is the scale
coupling `κ(|n|)`. -/
theorem fourierCoeffOn_factorialCriticalPrimeContinuousRealKernel (n : ℤ) :
    fourierCoeffOn zero_lt_one (fun t => (factorialCriticalPrimeContinuousRealKernel t : ℂ)) n =
      (factorialCriticalPrimeCoupling n.natAbs : ℂ) := by
  set R := factorialCriticalPrimeContinuousRealKernel
  rw [fourierCoeffOn_eq_integral]
  have hpt (x : ℝ) : (fourier (T := (1 : ℝ) - 0) (-n)) ((x : ℝ) : AddCircle ((1 : ℝ) - 0)) • (R x : ℂ) =
      ((R x * Real.cos (2 * Real.pi * n * x) : ℝ) : ℂ) -
        Complex.I * ((R x * Real.sin (2 * Real.pi * n * x) : ℝ) : ℂ) := by
    rw [fourier_coe_apply, smul_eq_mul]
    have : 2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ) / (((1 : ℝ) - 0 : ℝ) : ℂ) =
        ((-(2 * Real.pi * n * x) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  simp_rw [hpt]
  have hc := intervalIntegrable_kernel_mul (g := fun x => Real.cos (2 * Real.pi * n * x)) (by fun_prop)
  have hs := intervalIntegrable_kernel_mul (g := fun x => Real.sin (2 * Real.pi * n * x)) (by fun_prop)
  rw [intervalIntegral.integral_sub hc (hs.const_mul Complex.I),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    integral_factorialCriticalPrimeContinuousRealKernel_mul_sin]
  unfold factorialCriticalPrimeCoupling
  simp_rw [cos_natAbs]
  simp only [mul_zero, sub_zero, div_one, one_smul, Complex.ofReal_zero]

/-- The scale couplings are absolutely summable: `|κ(k)| = O(1/k²)`. -/
theorem summable_abs_factorialCriticalPrimeCoupling :
    Summable fun k : ℕ => |factorialCriticalPrimeCoupling k| := by
  set A := ∑' m : ℕ, |factorialCriticalPrimeHarmonicCharge m| / (m : ℝ) ^ 3
  have hA : 0 ≤ A := tsum_nonneg fun m => by positivity
  refine (summable_nat_add_iff 1).mp ?_
  have hs : Summable fun k : ℕ => A * ((Real.pi / 6) ^ 3 / 6 / Real.pi ^ 2) * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)).mul_left _
  refine hs.of_nonneg_of_le (fun _ => abs_nonneg _) fun k => ?_
  have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have hkR : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk
  have hpi := Real.pi_pos
  have hk2 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := one_le_pow₀ hkR
  have hD : Real.pi ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 4 * Real.pi ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 - (Real.pi / 6) ^ 2 := by
    nlinarith [sq_nonneg Real.pi]
  have hD0 : 0 < Real.pi ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have h2 : (Real.pi / 6) ^ 3 / 6 / (4 * Real.pi ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 - (Real.pi / 6) ^ 2) ≤
      (Real.pi / 6) ^ 3 / 6 / Real.pi ^ 2 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    calc _ ≤ (Real.pi / 6) ^ 3 / 6 / (Real.pi ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hD0 hD
      _ = _ := by field_simp
  calc _ ≤ A * ((Real.pi / 6) ^ 3 / 6 / (4 * Real.pi ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2 - (Real.pi / 6) ^ 2)) :=
        abs_factorialCriticalPrimeCoupling_le hk
    _ ≤ A * ((Real.pi / 6) ^ 3 / 6 / Real.pi ^ 2 * (1 / ((k + 1 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 hA
    _ = _ := by ring

private theorem fourierCoeffOn_kernel_of_eq {b : ℝ} (hb : b = 1) (hab : 0 < b) (n : ℤ) :
    fourierCoeffOn hab (fun t => (factorialCriticalPrimeContinuousRealKernel t : ℂ)) n =
      (factorialCriticalPrimeCoupling n.natAbs : ℂ) := by
  subst hb; exact fourierCoeffOn_factorialCriticalPrimeContinuousRealKernel n

/-- **Toeplitz symbol law.** The critical kernel is the absolutely convergent cosine series of the
scale couplings: `R(t) = Σ_{n ∈ ℤ} κ(|n|) cos(2πnt)` on the closed cell. -/
theorem hasSum_factorialCriticalPrimeCoupling_cos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℤ => factorialCriticalPrimeCoupling n.natAbs * Real.cos (2 * Real.pi * n * t))
      (factorialCriticalPrimeContinuousRealKernel t) := by
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  set R := factorialCriticalPrimeContinuousRealKernel
  set F : ℝ → ℂ := fun t => (R t : ℂ)
  have hR01 : R 0 = R 1 := by
    have := factorialCriticalPrimeContinuousRealKernel_reflect 0
    rw [sub_zero] at this; exact this.symm
  have hcont : Continuous (AddCircle.liftIco 1 0 F) := by
    refine AddCircle.liftIco_continuous (by simp only [F, zero_add, hR01]) ?_
    rw [zero_add]
    exact Complex.continuous_ofReal.comp_continuousOn continuousOn_factorialCriticalPrimeContinuousRealKernel
  set f : C(AddCircle (1 : ℝ), ℂ) := ⟨AddCircle.liftIco 1 0 F, hcont⟩
  have hcoef (n : ℤ) : fourierCoeff f n = (factorialCriticalPrimeCoupling n.natAbs : ℂ) := by
    change fourierCoeff (AddCircle.liftIco 1 0 F) n = _
    rw [fourierCoeff_liftIco_eq]
    exact fourierCoeffOn_kernel_of_eq (zero_add 1) _ n
  have hsum : Summable (fourierCoeff f) := by
    rw [show fourierCoeff f = fun n => (factorialCriticalPrimeCoupling n.natAbs : ℂ) from funext hcoef]
    refine Summable.of_norm ?_
    simp only [Complex.norm_real, Real.norm_eq_abs]
    refine Summable.of_nat_of_neg ?_ ?_
    · simpa using summable_abs_factorialCriticalPrimeCoupling
    · simpa using summable_abs_factorialCriticalPrimeCoupling
  have key (s : ℝ) (hs : s ∈ Ico (0 : ℝ) 1) :
      HasSum (fun n : ℤ => factorialCriticalPrimeCoupling n.natAbs * Real.cos (2 * Real.pi * n * s)) (R s) := by
    have h := Complex.hasSum_re (has_pointwise_sum_fourier_series_of_summable hsum (s : AddCircle (1 : ℝ)))
    have hval : (f (s : AddCircle (1 : ℝ))).re = R s := by
      change (AddCircle.liftIco 1 0 F (s : AddCircle (1 : ℝ))).re = R s
      rw [AddCircle.liftIco_coe_apply (by rwa [zero_add])]
      simp [F]
    rw [hval] at h
    refine h.congr_fun fun n => ?_
    rw [hcoef, fourier_coe_apply, smul_eq_mul, Complex.re_ofReal_mul]
    congr 1
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (s : ℂ) / ((1 : ℝ) : ℂ) =
      ((2 * Real.pi * n * s : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    have h0 := key 0 ⟨le_rfl, one_pos⟩
    rw [← hR01]
    refine h0.congr_fun fun n => ?_
    rw [mul_zero, mul_one, show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring,
      Real.cos_int_mul_two_pi, Real.cos_zero]
  · exact key t ⟨ht.1, h1⟩

/-- **Toeplitz counting identity.** A Toeplitz sum over the square `[0,L)²` counts each lag `n`
with multiplicity `L - n`, twice for `n ≠ 0`. -/
theorem sum_range_sum_range_natAbs (γ : ℕ → ℝ) (L : ℕ) :
    ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, γ ((i : ℤ) - j).natAbs =
      ∑ n ∈ Finset.range L, ((L : ℝ) - n) * (if n = 0 then 1 else 2) * γ n := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hrow : ∑ i ∈ Finset.range L, γ ((i : ℤ) - L).natAbs = ∑ i ∈ Finset.range L, γ (i + 1) := by
      rw [← Finset.sum_range_reflect (fun i => γ (i + 1)) L]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi := Finset.mem_range.mp hi
      congr 1; omega
    have hcol : ∑ j ∈ Finset.range (L + 1), γ ((L : ℤ) - j).natAbs =
        ∑ j ∈ Finset.range L, γ (j + 1) + γ 0 := by
      rw [← Finset.sum_range_succ' γ L, ← Finset.sum_range_reflect γ (L + 1)]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj := Finset.mem_range.mp hj
      congr 1; omega
    have hdiag : ∑ n ∈ Finset.range (L + 1), (if n = 0 then (1 : ℝ) else 2) * γ n =
        2 * ∑ j ∈ Finset.range L, γ (j + 1) + γ 0 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp
    calc ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (L + 1), γ ((i : ℤ) - j).natAbs
        = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, γ ((i : ℤ) - j).natAbs +
            ∑ i ∈ Finset.range L, γ ((i : ℤ) - L).natAbs +
            ∑ j ∈ Finset.range (L + 1), γ ((L : ℤ) - j).natAbs := by
          rw [Finset.sum_range_succ]
          simp only [Finset.sum_range_succ (fun j => γ ((_ : ℤ) - j).natAbs), Finset.sum_add_distrib]
      _ = ∑ n ∈ Finset.range L, ((L : ℝ) - n) * (if n = 0 then 1 else 2) * γ n +
            ∑ n ∈ Finset.range (L + 1), (if n = 0 then (1 : ℝ) else 2) * γ n := by
          rw [ih, hrow, hcol, hdiag]; ring
      _ = ∑ n ∈ Finset.range (L + 1), (((L + 1 : ℕ) : ℝ) - n) * (if n = 0 then 1 else 2) * γ n := by
          rw [Finset.sum_range_succ _ L, Finset.sum_range_succ _ L, ← add_assoc, ← Finset.sum_add_distrib]
          push_cast
          have : ∑ x ∈ Finset.range L, (((L : ℝ) - x) * (if x = 0 then 1 else 2) * γ x +
              (if x = 0 then 1 else 2) * γ x) =
              ∑ x ∈ Finset.range L, (((L : ℝ) + 1 - x) * (if x = 0 then 1 else 2) * γ x) :=
            Finset.sum_congr rfl fun x _ => by ring
          rw [this]; ring

private theorem kernel_integral_bounds (S : Finset ℕ) (b : ℕ → ℝ) {m M : ℝ}
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ factorialCriticalPrimeContinuousRealKernel t)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, factorialCriticalPrimeContinuousRealKernel t ≤ M) :
    m * ∑ j ∈ S, b j ^ 2 ≤ ∫ t in (0 : ℝ)..1, factorialCriticalPrimeContinuousRealKernel t *
        factorialCriticalPatternDensity S b t ∧
      ∫ t in (0 : ℝ)..1, factorialCriticalPrimeContinuousRealKernel t *
        factorialCriticalPatternDensity S b t ≤ M * ∑ j ∈ S, b j ^ 2 := by
  have hQ := continuous_factorialCriticalPatternDensity S b
  have hR := continuousOn_factorialCriticalPrimeContinuousRealKernel
  have hRQ : IntervalIntegrable (fun t => factorialCriticalPrimeContinuousRealKernel t *
      factorialCriticalPatternDensity S b t) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact hR.mul hQ.continuousOn
  have hE : ∫ t in (0 : ℝ)..1, factorialCriticalPatternDensity S b t = ∑ j ∈ S, b j ^ 2 := by
    simpa using factorialCriticalPatternDensity_cell S b one_pos 0
  constructor
  · have h := intervalIntegral.integral_mono_on zero_le_one
      ((by fun_prop : Continuous fun t => m * factorialCriticalPatternDensity S b t).intervalIntegrable _ _) hRQ
      fun t ht => mul_le_mul_of_nonneg_right (hm t ht) (factorialCriticalPatternDensity_nonneg S b t)
    rwa [intervalIntegral.integral_const_mul, hE] at h
  · have h := intervalIntegral.integral_mono_on zero_le_one hRQ
      ((by fun_prop : Continuous fun t => M * factorialCriticalPatternDensity S b t).intervalIntegrable _ _)
      fun t ht => mul_le_mul_of_nonneg_right (hM t ht) (factorialCriticalPatternDensity_nonneg S b t)
    rwa [intervalIntegral.integral_const_mul, hE] at h

/-- **Kernel range bounds.** Pointwise bounds `m ≤ R ≤ M` on the cell bound the limiting prime
form between `(4/π⁴) m Σ b_j²` and `(4/π⁴) M Σ b_j²`. -/
theorem factorialCriticalTranslatedPrimeLimit_mem_kernel_range (S : Finset ℕ) (b : ℕ → ℝ) {m M : ℝ}
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, m ≤ factorialCriticalPrimeContinuousRealKernel t)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, factorialCriticalPrimeContinuousRealKernel t ≤ M) :
    4 / Real.pi ^ 4 * m * ∑ j ∈ S, b j ^ 2 ≤ factorialCriticalTranslatedPrimeLimit S b ∧
      factorialCriticalTranslatedPrimeLimit S b ≤ 4 / Real.pi ^ 4 * M * ∑ j ∈ S, b j ^ 2 := by
  rw [factorialCriticalTranslatedPrimeLimit_eq_continuous_kernel_integral]
  obtain ⟨h1, h2⟩ := kernel_integral_bounds S b hm hM
  have hc : 0 ≤ 4 / Real.pi ^ 4 := by positivity
  exact ⟨by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hc,
    by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hc⟩

private theorem primeLimit_eq_zero_of_energy_eq_zero {S : Finset ℕ} {b : ℕ → ℝ}
    (h : ∑ j ∈ S, b j ^ 2 = 0) : factorialCriticalTranslatedPrimeLimit S b = 0 := by
  have := abs_factorialCriticalTranslatedPrimeLimit_sub_isotropic_le S b
  rw [h, mul_zero, mul_zero, sub_zero] at this
  exact abs_nonpos_iff.mp this

/-- **Cesàro limit of the Toeplitz form.** For the cosine and sine patterns of frequency `t` on
`[0,L)`, the sum of the two limiting prime energies, divided by their total energy `L`,
converges to `(4/π⁴) R(t)`. -/
theorem tendsto_factorialCriticalTranslatedPrimeLimit_cos_add_sin {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun L : ℕ => (factorialCriticalTranslatedPrimeLimit (Finset.range L)
        (fun j => Real.cos (2 * Real.pi * j * t)) +
      factorialCriticalTranslatedPrimeLimit (Finset.range L) (fun j => Real.sin (2 * Real.pi * j * t))) / L)
      atTop (𝓝 (4 / Real.pi ^ 4 * factorialCriticalPrimeContinuousRealKernel t)) := by
  set κ := factorialCriticalPrimeCoupling
  set γ : ℕ → ℝ := fun n => κ n * Real.cos (2 * Real.pi * n * t)
  set ε : ℕ → ℝ := fun n => if n = 0 then 1 else 2
  have hform (L : ℕ) : factorialCriticalTranslatedPrimeLimit (Finset.range L)
      (fun j => Real.cos (2 * Real.pi * j * t)) +
      factorialCriticalTranslatedPrimeLimit (Finset.range L) (fun j => Real.sin (2 * Real.pi * j * t)) =
      4 / Real.pi ^ 4 * ∑ n ∈ Finset.range L, ((L : ℝ) - n) * ε n * γ n := by
    rw [factorialCriticalTranslatedPrimeLimit_eq_coupling, factorialCriticalTranslatedPrimeLimit_eq_coupling,
      ← mul_add, ← sum_range_sum_range_natAbs]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [γ]
    rw [cos_natAbs]
    push_cast
    rw [show 2 * Real.pi * ((i : ℝ) - j) * t = 2 * Real.pi * i * t - 2 * Real.pi * j * t by ring, Real.cos_sub]
    ring
  have hγ (n : ℕ) : |ε n * γ n| ≤ 2 * |κ n| := by
    simp only [ε, γ, abs_mul]
    have hc := Real.abs_cos_le_one (2 * Real.pi * n * t)
    split_ifs <;> norm_num <;> nlinarith [abs_nonneg (κ n)]
  have hdom : Tendsto (fun L : ℕ => ∑' n : ℕ, if n < L then (1 - (n : ℝ) / L) * (ε n * γ n) else 0) atTop
      (𝓝 (∑' n : ℕ, ε n * γ n)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => 2 * |κ n|)
      (summable_abs_factorialCriticalPrimeCoupling.mul_left 2) (fun n => ?_) ?_
    · have h1 : Tendsto (fun L : ℕ => 1 - (n : ℝ) / L) atTop (𝓝 1) := by
        simpa using (tendsto_const_div_atTop_nhds_zero_nat (n : ℝ)).const_sub 1
      refine ((h1.mul_const (ε n * γ n)).congr' ?_).trans (by rw [one_mul])
      filter_upwards [eventually_gt_atTop n] with L hL
      rw [if_pos hL]
    · refine Eventually.of_forall fun L n => ?_
      split_ifs with hL
      · rw [Real.norm_eq_abs, abs_mul]
        have h0 : 0 ≤ 1 - (n : ℝ) / L := by
          rw [sub_nonneg, div_le_one (by exact_mod_cast (Nat.zero_lt_of_lt hL))]
          exact_mod_cast hL.le
        have h1 : 1 - (n : ℝ) / L ≤ 1 := by
          have : 0 ≤ (n : ℝ) / L := by positivity
          linarith
        rw [abs_of_nonneg h0]
        nlinarith [hγ n, abs_nonneg (ε n * γ n)]
      · simp only [norm_zero]; positivity
  have hval : ∑' n : ℕ, ε n * γ n = factorialCriticalPrimeContinuousRealKernel t := by
    have h := (hasSum_factorialCriticalPrimeCoupling_cos ht).nat_add_neg
    have h2 : HasSum (fun n : ℕ => 2 * γ n) (factorialCriticalPrimeContinuousRealKernel t + γ 0) := by
      refine (h.congr_fun fun n => ?_).trans (by simp [γ, κ])
      simp only [γ, Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast]
      rw [show 2 * Real.pi * -(n : ℝ) * t = -(2 * Real.pi * n * t) by ring, Real.cos_neg]
      ring
    have h3 := h2.sub (hasSum_ite_eq 0 (γ 0))
    rw [add_sub_cancel_right] at h3
    refine (h3.congr_fun fun n => ?_).tsum_eq
    simp only [ε]
    split_ifs with hn
    · subst hn; ring
    · ring
  rw [← hval]
  refine ((hdom.const_mul (4 / Real.pi ^ 4)).congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with L hL
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [hform, tsum_eq_sum (s := Finset.range L) (fun n hn => by
    rw [if_neg (by simpa using hn)]), mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos (Finset.mem_range.mp hn)]
  field_simp

private theorem energy_cos_add_sin (t : ℝ) (L : ℕ) :
    ∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * j * t) ^ 2 +
      ∑ j ∈ Finset.range L, Real.sin (2 * Real.pi * j * t) ^ 2 = L := by
  rw [← Finset.sum_add_distrib]
  simp [Real.cos_sq_add_sin_sq]

private theorem energy_nonneg (S : Finset ℕ) (b : ℕ → ℝ) : 0 ≤ ∑ j ∈ S, b j ^ 2 :=
  Finset.sum_nonneg fun j _ => sq_nonneg (b j)

/-- **Upper sharpness.** Every value below `(4/π⁴) R(t)` is exceeded by the Rayleigh quotient of
the limiting prime form on some finite pattern (a cosine or sine pattern of frequency `t`). -/
theorem exists_lt_factorialCriticalTranslatedPrimeLimit {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {c : ℝ}
    (hc : c < 4 / Real.pi ^ 4 * factorialCriticalPrimeContinuousRealKernel t) :
    ∃ (S : Finset ℕ) (b : ℕ → ℝ), 0 < ∑ j ∈ S, b j ^ 2 ∧
      c * ∑ j ∈ S, b j ^ 2 < factorialCriticalTranslatedPrimeLimit S b := by
  obtain ⟨L, hgt, hL⟩ := (((tendsto_factorialCriticalTranslatedPrimeLimit_cos_add_sin ht).eventually
    (eventually_gt_nhds hc)).and (eventually_gt_atTop 0)).exists
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  have hbound (b : ℕ → ℝ) : factorialCriticalTranslatedPrimeLimit (Finset.range L) b ≤
      c * ∑ j ∈ Finset.range L, b j ^ 2 := by
    rcases (energy_nonneg (Finset.range L) b).lt_or_eq with hE | hE
    · exact hno _ _ hE
    · rw [primeLimit_eq_zero_of_energy_eq_zero hE.symm, ← hE, mul_zero]
  have h1 := hbound fun j => Real.cos (2 * Real.pi * j * t)
  have h2 := hbound fun j => Real.sin (2 * Real.pi * j * t)
  rw [lt_div_iff₀ hL'] at hgt
  have e : c * (L : ℝ) = c * ∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * j * t) ^ 2 +
      c * ∑ j ∈ Finset.range L, Real.sin (2 * Real.pi * j * t) ^ 2 := by
    rw [← energy_cos_add_sin t L]; ring
  linarith

/-- **Lower sharpness.** Every value above `(4/π⁴) R(t)` exceeds the Rayleigh quotient of the
limiting prime form on some finite pattern. -/
theorem exists_factorialCriticalTranslatedPrimeLimit_lt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {c : ℝ}
    (hc : 4 / Real.pi ^ 4 * factorialCriticalPrimeContinuousRealKernel t < c) :
    ∃ (S : Finset ℕ) (b : ℕ → ℝ), 0 < ∑ j ∈ S, b j ^ 2 ∧
      factorialCriticalTranslatedPrimeLimit S b < c * ∑ j ∈ S, b j ^ 2 := by
  obtain ⟨L, hlt, hL⟩ := (((tendsto_factorialCriticalTranslatedPrimeLimit_cos_add_sin ht).eventually
    (eventually_lt_nhds hc)).and (eventually_gt_atTop 0)).exists
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  by_contra hno
  simp only [not_exists, not_and, not_lt] at hno
  have hbound (b : ℕ → ℝ) : c * ∑ j ∈ Finset.range L, b j ^ 2 ≤
      factorialCriticalTranslatedPrimeLimit (Finset.range L) b := by
    rcases (energy_nonneg (Finset.range L) b).lt_or_eq with hE | hE
    · exact hno _ _ hE
    · rw [primeLimit_eq_zero_of_energy_eq_zero hE.symm, ← hE, mul_zero]
  have h1 := hbound fun j => Real.cos (2 * Real.pi * j * t)
  have h2 := hbound fun j => Real.sin (2 * Real.pi * j * t)
  rw [div_lt_iff₀ hL'] at hlt
  have e : c * (L : ℝ) = c * ∑ j ∈ Finset.range L, Real.cos (2 * Real.pi * j * t) ^ 2 +
      c * ∑ j ∈ Finset.range L, Real.sin (2 * Real.pi * j * t) ^ 2 := by
    rw [← energy_cos_add_sin t L]; ring
  linarith

/-- Rayleigh quotients of the limiting critical prime form over all nonzero finite patterns. -/
def factorialCriticalPrimeRayleighSet : Set ℝ :=
  {r | ∃ (S : Finset ℕ) (b : ℕ → ℝ), 0 < ∑ j ∈ S, b j ^ 2 ∧
    r = factorialCriticalTranslatedPrimeLimit S b / ∑ j ∈ S, b j ^ 2}

private theorem kernel_image_bdd :
    BddAbove (factorialCriticalPrimeContinuousRealKernel '' Icc (0 : ℝ) 1) ∧
      BddBelow (factorialCriticalPrimeContinuousRealKernel '' Icc (0 : ℝ) 1) :=
  let hK := isCompact_Icc.image_of_continuousOn continuousOn_factorialCriticalPrimeContinuousRealKernel
  ⟨hK.bddAbove, hK.bddBelow⟩

private theorem kernel_image_nonempty :
    (factorialCriticalPrimeContinuousRealKernel '' Icc (0 : ℝ) 1).Nonempty :=
  (nonempty_Icc.mpr zero_le_one).image _

/-- **Sharp spectral range, top.** The supremum of the Rayleigh quotients of the limiting critical
prime form is exactly `(4/π⁴) max R`. -/
theorem isLUB_factorialCriticalPrimeRayleighSet :
    IsLUB factorialCriticalPrimeRayleighSet
      (4 / Real.pi ^ 4 * sSup (factorialCriticalPrimeContinuousRealKernel '' Icc (0 : ℝ) 1)) := by
  set K := factorialCriticalPrimeContinuousRealKernel '' Icc (0 : ℝ) 1
  have hπ : 0 < 4 / Real.pi ^ 4 := by positivity
  constructor
  · rintro r ⟨S, b, hE, rfl⟩
    have h := (factorialCriticalTranslatedPrimeLimit_mem_kernel_range S b (m := sInf K) (M := sSup K)
      (fun t ht => csInf_le kernel_image_bdd.2 (mem_image_of_mem _ ht))
      (fun t ht => le_csSup kernel_image_bdd.1 (mem_image_of_mem _ ht))).2
    rwa [div_le_iff₀ hE]
  · intro u hu
    by_contra hlt
    have hlt := not_le.mp hlt
    have hp : 0 < Real.pi ^ 4 / 4 := by positivity
    have : u * (Real.pi ^ 4 / 4) < sSup K := by
      have h := mul_lt_mul_of_pos_right hlt hp
      rwa [show 4 / Real.pi ^ 4 * sSup K * (Real.pi ^ 4 / 4) = sSup K by field_simp] at h
    obtain ⟨_, ⟨t, ht, rfl⟩, hty⟩ := exists_lt_of_lt_csSup kernel_image_nonempty this
    have hc : u < 4 / Real.pi ^ 4 * factorialCriticalPrimeContinuousRealKernel t := by
      have h := mul_lt_mul_of_pos_left hty hπ
      rwa [show 4 / Real.pi ^ 4 * (u * (Real.pi ^ 4 / 4)) = u by field_simp] at h
    obtain ⟨S, b, hE, hgt⟩ := exists_lt_factorialCriticalTranslatedPrimeLimit ht hc
    have := hu ⟨S, b, hE, rfl⟩
    rw [div_le_iff₀ hE] at this
    linarith

/-- **Sharp spectral range, bottom.** The infimum of the Rayleigh quotients of the limiting critical
prime form is exactly `(4/π⁴) min R`. -/
theorem isGLB_factorialCriticalPrimeRayleighSet :
    IsGLB factorialCriticalPrimeRayleighSet
      (4 / Real.pi ^ 4 * sInf (factorialCriticalPrimeContinuousRealKernel '' Icc (0 : ℝ) 1)) := by
  set K := factorialCriticalPrimeContinuousRealKernel '' Icc (0 : ℝ) 1
  have hπ : 0 < 4 / Real.pi ^ 4 := by positivity
  constructor
  · rintro r ⟨S, b, hE, rfl⟩
    have h := (factorialCriticalTranslatedPrimeLimit_mem_kernel_range S b (m := sInf K) (M := sSup K)
      (fun t ht => csInf_le kernel_image_bdd.2 (mem_image_of_mem _ ht))
      (fun t ht => le_csSup kernel_image_bdd.1 (mem_image_of_mem _ ht))).1
    rwa [le_div_iff₀ hE]
  · intro u hu
    by_contra hlt
    have hlt := not_le.mp hlt
    have hp : 0 < Real.pi ^ 4 / 4 := by positivity
    have : sInf K < u * (Real.pi ^ 4 / 4) := by
      have h := mul_lt_mul_of_pos_right hlt hp
      rwa [show 4 / Real.pi ^ 4 * sInf K * (Real.pi ^ 4 / 4) = sInf K by field_simp] at h
    obtain ⟨_, ⟨t, ht, rfl⟩, hty⟩ := exists_lt_of_csInf_lt kernel_image_nonempty this
    have hc : 4 / Real.pi ^ 4 * factorialCriticalPrimeContinuousRealKernel t < u := by
      have h := mul_lt_mul_of_pos_left hty hπ
      rwa [show 4 / Real.pi ^ 4 * (u * (Real.pi ^ 4 / 4)) = u by field_simp] at h
    obtain ⟨S, b, hE, hlt'⟩ := exists_factorialCriticalTranslatedPrimeLimit_lt ht hc
    have := hu ⟨S, b, hE, rfl⟩
    rw [le_div_iff₀ hE] at this
    linarith

/-- The top of the spectral range is strictly negative: the optimal negativity constant of the
limiting critical prime form is `-(4/π⁴) max R ≥ 4/(7000π⁴)`. -/
theorem sSup_factorialCriticalPrimeContinuousRealKernel_le :
    sSup (factorialCriticalPrimeContinuousRealKernel '' Icc (0 : ℝ) 1) ≤ -1 / 7000 :=
  csSup_le kernel_image_nonempty (by
    rintro _ ⟨t, ht, rfl⟩
    exact factorialCriticalPrimeContinuousRealKernel_le ht)

end GaloisForLFunctions.ArithmeticPositivityTheory
