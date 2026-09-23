import GaloisForLFunctions.RHTower.SoninSemilocalJacobiTransform
import GaloisForLFunctions.RHTower.SoninSemilocalPoissonFrequencyCollapse
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual finite-prime Euler-weighted Gamma integral

This file identifies the analytic Euler density with its absolutely convergent finite-lattice
Poisson expansion, justifies termwise polynomial integration against the Gamma measure, and proves
that the normalized integral of every positive even Jacobi polynomial is the previously constructed
Poisson-series moment.  This is equation (1) on the literal normalized integral, not only on an
abstract series surrogate.
-/

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace RHTower

def semilocalFinitePrimeEulerDensity {n : ℕ}
    (p : Fin n → ℕ) (s : ℝ) : ℝ :=
  ∏ i, (Complex.normSq
    (1 - (semilocalPrimePoissonRatio (p i) : ℂ) *
      semilocalPrimePhase (p i) s))⁻¹

def semilocalFinitePrimePoissonPrefactor {n : ℕ}
    (p : Fin n → ℕ) : ℝ :=
  ∏ i, (1 - semilocalPrimePoissonRatio (p i) ^ (2 : ℕ))⁻¹

theorem semilocalFinitePrimeEulerDensity_eq_poissonSeries_complex
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    (semilocalFinitePrimeEulerDensity p s : ℂ) =
      (semilocalFinitePrimePoissonPrefactor p : ℂ) *
        ∑' m : Fin n → ℤ,
          (semilocalFinitePrimePoissonWeight p m : ℂ) *
            Complex.exp
              (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) * Complex.I) := by
  unfold semilocalFinitePrimeEulerDensity semilocalFinitePrimePoissonPrefactor
  push_cast
  simpa using semilocalFinitePrimePoissonExpansion_frequency p hprime s

def semilocalFinitePrimePoissonPolynomialTerm {n : ℕ}
    (p : Fin n → ℕ) (q : ℝ[X]) (m : Fin n → ℤ) (s : ℝ) : ℂ :=
  (semilocalFinitePrimePoissonWeight p m : ℂ) * ((q.eval s : ℝ) : ℂ) *
    Complex.exp
      (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) * Complex.I)

theorem integrable_semilocalFinitePrimePoissonPolynomialTerm
    {n : ℕ} (p : Fin n → ℕ) (q : ℝ[X]) (m : Fin n → ℤ) :
    Integrable (semilocalFinitePrimePoissonPolynomialTerm p q m)
      semilocalArchimedeanGammaMeasure := by
  apply (integrable_semilocalArchimedeanPolynomialFourier_integrand q
    (semilocalFinitePrimeLogFrequency p m)).const_mul
      (semilocalFinitePrimePoissonWeight p m : ℂ) |>.congr
  filter_upwards with s
  unfold semilocalFinitePrimePoissonPolynomialTerm
  ring

theorem summable_integral_norm_semilocalFinitePrimePoissonPolynomialTerm
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (q : ℝ[X]) :
    Summable fun m : Fin n → ℤ =>
      ∫ s : ℝ, ‖semilocalFinitePrimePoissonPolynomialTerm p q m s‖
        ∂semilocalArchimedeanGammaMeasure := by
  have hweight := summable_semilocalFinitePrimePoissonWeight p hprime
  have hmajor := hweight.mul_right
    (∫ s : ℝ, ‖((q.eval s : ℝ) : ℂ)‖ ∂semilocalArchimedeanGammaMeasure)
  apply hmajor.congr
  intro m
  rw [show (fun s : ℝ =>
      ‖semilocalFinitePrimePoissonPolynomialTerm p q m s‖) =
      fun s : ℝ => semilocalFinitePrimePoissonWeight p m *
        ‖((q.eval s : ℝ) : ℂ)‖ by
    funext s
    unfold semilocalFinitePrimePoissonPolynomialTerm
    rw [norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (semilocalFinitePrimePoissonWeight_pos p hprime m).le,
      Complex.norm_exp]
    simp]
  rw [integral_const_mul]

theorem integral_semilocalFinitePrimeEulerDensity_mul_polynomial_eq_poissonSeries
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (q : ℝ[X]) :
    (∫ s : ℝ, ((q.eval s : ℝ) : ℂ) *
        (semilocalFinitePrimeEulerDensity p s : ℂ)
          ∂semilocalArchimedeanGammaMeasure) =
      (semilocalFinitePrimePoissonPrefactor p : ℂ) *
        ∑' m : Fin n → ℤ,
          (semilocalFinitePrimePoissonWeight p m : ℂ) *
            semilocalArchimedeanPolynomialFourier q
              (semilocalFinitePrimeLogFrequency p m) := by
  let F : (Fin n → ℤ) → ℝ → ℂ :=
    semilocalFinitePrimePoissonPolynomialTerm p q
  have hFint (m : Fin n → ℤ) :
      Integrable (F m) semilocalArchimedeanGammaMeasure :=
    integrable_semilocalFinitePrimePoissonPolynomialTerm p q m
  have hswap := integral_tsum_of_summable_integral_norm hFint
    (summable_integral_norm_semilocalFinitePrimePoissonPolynomialTerm p hprime q)
  calc
    (∫ s : ℝ, ((q.eval s : ℝ) : ℂ) *
        (semilocalFinitePrimeEulerDensity p s : ℂ)
          ∂semilocalArchimedeanGammaMeasure) =
        ∫ s : ℝ, (semilocalFinitePrimePoissonPrefactor p : ℂ) *
          (∑' m : Fin n → ℤ, F m s)
            ∂semilocalArchimedeanGammaMeasure := by
      apply integral_congr_ae
      filter_upwards with s
      rw [semilocalFinitePrimeEulerDensity_eq_poissonSeries_complex p hprime s]
      calc
        ((q.eval s : ℝ) : ℂ) *
            ((semilocalFinitePrimePoissonPrefactor p : ℂ) *
              ∑' m : Fin n → ℤ,
                (semilocalFinitePrimePoissonWeight p m : ℂ) *
                  Complex.exp (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) *
                    Complex.I)) =
            (semilocalFinitePrimePoissonPrefactor p : ℂ) *
              (((q.eval s : ℝ) : ℂ) *
                ∑' m : Fin n → ℤ,
                  (semilocalFinitePrimePoissonWeight p m : ℂ) *
                    Complex.exp (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) *
                      Complex.I)) := by ring
        _ = (semilocalFinitePrimePoissonPrefactor p : ℂ) *
              ∑' m : Fin n → ℤ,
                ((q.eval s : ℝ) : ℂ) *
                  ((semilocalFinitePrimePoissonWeight p m : ℂ) *
                    Complex.exp (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) *
                      Complex.I)) := by
            rw [tsum_mul_left]
        _ = (semilocalFinitePrimePoissonPrefactor p : ℂ) *
              ∑' m : Fin n → ℤ, F m s := by
            congr 1
            apply tsum_congr
            intro m
            unfold F semilocalFinitePrimePoissonPolynomialTerm
            ring
    _ = (semilocalFinitePrimePoissonPrefactor p : ℂ) *
        ∫ s : ℝ, ∑' m : Fin n → ℤ, F m s
          ∂semilocalArchimedeanGammaMeasure := by
      rw [integral_const_mul]
    _ = (semilocalFinitePrimePoissonPrefactor p : ℂ) *
        ∑' m : Fin n → ℤ,
          ∫ s : ℝ, F m s ∂semilocalArchimedeanGammaMeasure := by
      rw [← hswap]
    _ = (semilocalFinitePrimePoissonPrefactor p : ℂ) *
        ∑' m : Fin n → ℤ,
          (semilocalFinitePrimePoissonWeight p m : ℂ) *
            semilocalArchimedeanPolynomialFourier q
              (semilocalFinitePrimeLogFrequency p m) := by
      congr 1
      apply tsum_congr
      intro m
      unfold F semilocalFinitePrimePoissonPolynomialTerm
      unfold semilocalArchimedeanPolynomialFourier
      rw [show (fun s : ℝ =>
          (semilocalFinitePrimePoissonWeight p m : ℂ) * ((q.eval s : ℝ) : ℂ) *
            Complex.exp
              (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) * Complex.I)) =
          fun s : ℝ => (semilocalFinitePrimePoissonWeight p m : ℂ) *
            (((q.eval s : ℝ) : ℂ) *
              Complex.exp
                (((semilocalFinitePrimeLogFrequency p m * s : ℝ) : ℂ) * Complex.I)) by
        funext s
        ring]
      rw [integral_const_mul]

/-- **Real Poisson-series value interface.** If the polynomial Fourier transform is represented
pointwise by a real kernel, then the actual Euler-density integral is the corresponding real
Poisson series. -/
theorem integral_semilocalFinitePrimeEulerDensity_mul_polynomial_eq_realPoissonSeries
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (q : ℝ[X]) (K : ℝ → ℝ)
    (hK : ∀ t, semilocalArchimedeanPolynomialFourier q t = (K t : ℂ)) :
    (∫ s : ℝ, q.eval s * semilocalFinitePrimeEulerDensity p s
        ∂semilocalArchimedeanGammaMeasure) =
      semilocalFinitePrimePoissonPrefactor p *
        ∑' m : Fin n → ℤ,
          semilocalFinitePrimePoissonWeight p m *
            K (semilocalFinitePrimeLogFrequency p m) := by
  have hseries :=
    integral_semilocalFinitePrimeEulerDensity_mul_polynomial_eq_poissonSeries p hprime q
  apply Complex.ofReal_injective
  calc
    (((∫ s : ℝ, q.eval s * semilocalFinitePrimeEulerDensity p s
        ∂semilocalArchimedeanGammaMeasure) : ℝ) : ℂ) =
        ∫ s : ℝ, ((q.eval s * semilocalFinitePrimeEulerDensity p s : ℝ) : ℂ)
          ∂semilocalArchimedeanGammaMeasure := by
      rw [integral_complex_ofReal]
    _ =
        ∫ s : ℝ, ((q.eval s : ℝ) : ℂ) *
          (semilocalFinitePrimeEulerDensity p s : ℂ)
            ∂semilocalArchimedeanGammaMeasure := by
      apply integral_congr_ae
      filter_upwards with s
      push_cast
      rfl
    _ = (semilocalFinitePrimePoissonPrefactor p : ℂ) *
        ∑' m : Fin n → ℤ,
          (semilocalFinitePrimePoissonWeight p m : ℂ) *
            semilocalArchimedeanPolynomialFourier q
              (semilocalFinitePrimeLogFrequency p m) := hseries
    _ = (semilocalFinitePrimePoissonPrefactor p : ℂ) *
        ∑' m : Fin n → ℤ,
          ((semilocalFinitePrimePoissonWeight p m *
            K (semilocalFinitePrimeLogFrequency p m) : ℝ) : ℂ) := by
      congr 1
      apply tsum_congr
      intro m
      rw [hK]
      push_cast
      rfl
    _ = ((semilocalFinitePrimePoissonPrefactor p *
        ∑' m : Fin n → ℤ,
          semilocalFinitePrimePoissonWeight p m *
            K (semilocalFinitePrimeLogFrequency p m) : ℝ) : ℂ) := by
      push_cast
      rfl

theorem semilocalArchimedeanPolynomialFourier_one (t : ℝ) :
    semilocalArchimedeanPolynomialFourier (1 : ℝ[X]) t =
      (semilocalArchimedeanCharacteristic t : ℂ) := by
  simpa [semilocalArchimedeanPolynomialFourier] using
    integral_cexp_semilocalArchimedeanGammaMeasure t

theorem semilocalFinitePrimePoissonPrefactor_pos
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) :
    0 < semilocalFinitePrimePoissonPrefactor p := by
  unfold semilocalFinitePrimePoissonPrefactor
  apply Finset.prod_pos
  intro i _hi
  apply inv_pos.mpr
  have h0 := semilocalPrimePoissonRatio_pos (hprime i)
  have h1 := semilocalPrimePoissonRatio_lt_one (hprime i)
  nlinarith [sq_nonneg (semilocalPrimePoissonRatio (p i))]

theorem integral_semilocalFinitePrimeEulerDensity_eq_prefactor_mul_mass
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    (∫ s : ℝ, semilocalFinitePrimeEulerDensity p s
        ∂semilocalArchimedeanGammaMeasure) =
      semilocalFinitePrimePoissonPrefactor p *
        semilocalFinitePrimePoissonMass p := by
  simpa only [eval_one, one_mul, semilocalFinitePrimePoissonMass] using
    integral_semilocalFinitePrimeEulerDensity_mul_polynomial_eq_realPoissonSeries
      p hprime (1 : ℝ[X]) semilocalArchimedeanCharacteristic
        semilocalArchimedeanPolynomialFourier_one

theorem integral_semilocalFinitePrimeEulerDensity_pos
    {n : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    0 < ∫ s : ℝ, semilocalFinitePrimeEulerDensity p s
      ∂semilocalArchimedeanGammaMeasure := by
  rw [integral_semilocalFinitePrimeEulerDensity_eq_prefactor_mul_mass p hprime]
  exact mul_pos (semilocalFinitePrimePoissonPrefactor_pos p hprime)
    (semilocalFinitePrimePoissonMass_pos p hprime)

theorem semilocalArchimedeanPolynomialFourier_evenJacobi (k : ℕ) (t : ℝ) :
    semilocalArchimedeanPolynomialFourier
        (semilocalArchimedeanJacobiPolynomial (2 * k)) t =
      (semilocalArchimedeanEvenJacobiKernel k t : ℂ) := by
  change semilocalArchimedeanJacobiFourier (2 * k) t = _
  rw [semilocalArchimedeanJacobiFourier_eq_closedForm,
    semilocalArchimedeanJacobiFourierClosedForm_even]
  rfl

theorem summable_semilocalFinitePrimeEvenJacobiFullTerm
    {n k : ℕ} (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    Summable fun m : Fin (n + 1) → ℤ =>
      semilocalFinitePrimePoissonWeight p m *
        semilocalArchimedeanEvenJacobiKernel k
          (semilocalFinitePrimeLogFrequency p m) := by
  have hweight := summable_semilocalFinitePrimePoissonWeight p hprime
  have hmajor := hweight.mul_left
    (semilocalArchimedeanJacobiNormalization (2 * k))
  refine hmajor.of_norm_bounded ?_
  intro m
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (semilocalFinitePrimePoissonWeight_pos p hprime m)]
  calc
    semilocalFinitePrimePoissonWeight p m *
        |semilocalArchimedeanEvenJacobiKernel k
          (semilocalFinitePrimeLogFrequency p m)| ≤
      semilocalFinitePrimePoissonWeight p m *
        semilocalArchimedeanJacobiNormalization (2 * k) :=
      mul_le_mul_of_nonneg_left
        (abs_semilocalArchimedeanEvenJacobiKernel_le k _)
        (semilocalFinitePrimePoissonWeight_pos p hprime m).le
    _ = semilocalArchimedeanJacobiNormalization (2 * k) *
        semilocalFinitePrimePoissonWeight p m := by ring

theorem semilocalArchimedeanEvenJacobiKernel_zero
    {k : ℕ} (hk : 0 < k) :
    semilocalArchimedeanEvenJacobiKernel k 0 = 0 := by
  unfold semilocalArchimedeanEvenJacobiKernel
  rw [Real.tanh_zero,
    zero_pow (Nat.mul_ne_zero (by norm_num) hk.ne')]
  ring

theorem tsum_semilocalFinitePrimeEvenJacobiFullTerm_eq_numerator
    {n k : ℕ} (hk : 0 < k)
    (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    (∑' m : Fin (n + 1) → ℤ,
      semilocalFinitePrimePoissonWeight p m *
        semilocalArchimedeanEvenJacobiKernel k
          (semilocalFinitePrimeLogFrequency p m)) =
      semilocalFinitePrimeEvenJacobiNumerator k p := by
  let f : (Fin (n + 1) → ℤ) → ℝ := fun m =>
    semilocalFinitePrimePoissonWeight p m *
      semilocalArchimedeanEvenJacobiKernel k
        (semilocalFinitePrimeLogFrequency p m)
  have hf0 : f 0 = 0 := by
    unfold f
    have hfreq0 : semilocalFinitePrimeLogFrequency p 0 = 0 := by
      simp [semilocalFinitePrimeLogFrequency]
    rw [hfreq0, semilocalArchimedeanEvenJacobiKernel_zero hk]
    ring
  let s : Set (Fin (n + 1) → ℤ) := {m | m ≠ 0}
  have hsum : Summable f := by
    simpa [f] using
      (summable_semilocalFinitePrimeEvenJacobiFullTerm (k := k) p hprime)
  have hcomp : (∑' m : {m // m ∈ sᶜ}, f m.1) = 0 := by
    calc
      (∑' m : {m // m ∈ sᶜ}, f m.1) =
          ∑' _m : {m // m ∈ sᶜ}, (0 : ℝ) := by
        apply tsum_congr
        intro m
        have hm : m.1 = 0 := by
          simpa [s] using m.2
        rw [hm, hf0]
      _ = 0 := tsum_zero
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl s
  rw [hcomp, add_zero] at hsplit
  simpa [s, f, semilocalFinitePrimeEvenJacobiNumerator] using! hsplit.symm

theorem integral_semilocalFinitePrimeEulerDensity_mul_evenJacobi_eq_numerator
    {n k : ℕ} (hk : 0 < k)
    (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    (∫ s : ℝ,
        (semilocalArchimedeanJacobiPolynomial (2 * k)).eval s *
          semilocalFinitePrimeEulerDensity p s
            ∂semilocalArchimedeanGammaMeasure) =
      semilocalFinitePrimePoissonPrefactor p *
        semilocalFinitePrimeEvenJacobiNumerator k p := by
  rw [integral_semilocalFinitePrimeEulerDensity_mul_polynomial_eq_realPoissonSeries
    p hprime (semilocalArchimedeanJacobiPolynomial (2 * k))
      (semilocalArchimedeanEvenJacobiKernel k)
      (semilocalArchimedeanPolynomialFourier_evenJacobi k)]
  rw [tsum_semilocalFinitePrimeEvenJacobiFullTerm_eq_numerator hk p hprime]

def semilocalFinitePrimeActualEvenJacobiMoment
    {n : ℕ} (k : ℕ) (p : Fin (n + 1) → ℕ) : ℝ :=
  (∫ s : ℝ,
      (semilocalArchimedeanJacobiPolynomial (2 * k)).eval s *
        semilocalFinitePrimeEulerDensity p s
          ∂semilocalArchimedeanGammaMeasure) /
    (∫ s : ℝ, semilocalFinitePrimeEulerDensity p s
      ∂semilocalArchimedeanGammaMeasure)

theorem semilocalFinitePrimeActualEvenJacobiMoment_eq_seriesMoment
    {n k : ℕ} (hk : 0 < k)
    (p : Fin (n + 1) → ℕ) (hprime : ∀ i, (p i).Prime) :
    semilocalFinitePrimeActualEvenJacobiMoment k p =
      semilocalFinitePrimeEvenJacobiMoment k p := by
  unfold semilocalFinitePrimeActualEvenJacobiMoment
  rw [integral_semilocalFinitePrimeEulerDensity_mul_evenJacobi_eq_numerator hk p hprime,
    integral_semilocalFinitePrimeEulerDensity_eq_prefactor_mul_mass p hprime,
    semilocalFinitePrimeEvenJacobiMoment]
  field_simp [ne_of_gt (semilocalFinitePrimePoissonPrefactor_pos p hprime)]

/-- Equation (1) for the actual normalized Euler-weighted Gamma integral. -/
theorem semilocalFinitePrimeActualEvenJacobiMoment_signed_pos
    {n k : ℕ} (hk : 0 < k)
    (p : Fin (n + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    0 < (-1 : ℝ) ^ k * semilocalFinitePrimeActualEvenJacobiMoment k p := by
  rw [semilocalFinitePrimeActualEvenJacobiMoment_eq_seriesMoment hk p hprime]
  exact semilocalFinitePrimeEvenJacobiMoment_signed_pos p hp hprime

end RHTower
