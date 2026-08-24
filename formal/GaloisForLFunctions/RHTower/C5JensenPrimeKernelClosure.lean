import GaloisForLFunctions.RHTower.C5JensenRootPerturbation
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.XiShiftEulerProductBridge
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.Core

open Complex Filter Topology Polynomial

namespace GaloisForLFunctions.RHTower

noncomputable section

/-!
# C5 Jensen prime kernel: exact finite survivor and critical-line no-go

The finite single-frequency Jensen kernel is exact after specializing its
archimedean data to the actual polynomial--Gamma factor. Its prime amplitude
is neither absolutely nor square summable at half density.

The proposed global pointwise bridge from the critical-line prime expansion
cannot exist: the exponential of a complex-valued function never vanishes,
whereas Hardy's theorem supplies zeros of the actual centered completed zeta
function and its archimedean factor is nowhere zero on the critical line.
Thus the infinite critical-line expression must remain distributional and
cannot be inserted into pointwise derivative jets. The finite-prime analytic
simple-root response below is the strongest exact pointwise survivor.
-/

/-- Critical prime coefficient in the C5 logarithmic-zeta expansion. -/
def c5CriticalPrimeAmplitude (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-(1 / 2 : ℝ))

/-- Actual polynomial--Gamma factor in the C5 centered coordinate. -/
def c5XiArchimedeanFactor (z : ℂ) : ℂ :=
  _root_.RHTower.eulerXiArchimedeanFactor (1 / 2 + z * Complex.I)

/-- Actual all-order archimedean jet used by the finite C5 Jensen section. -/
def c5XiArchimedeanJet (t : ℝ) (j : ℕ) : ℂ :=
  iteratedDeriv j c5XiArchimedeanFactor (t : ℂ)

/-- The actual C5 archimedean factor never vanishes on the real centered line. -/
theorem c5XiArchimedeanFactor_ne_zero (t : ℝ) :
    c5XiArchimedeanFactor (t : ℂ) ≠ 0 := by
  let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  have hsre : s.re = 1 / 2 := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hsre] at hre
    norm_num at hre
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have heq : s = 1 := sub_eq_zero.mp h
    have hre := congrArg Complex.re heq
    rw [hsre] at hre
    norm_num at hre
  unfold c5XiArchimedeanFactor _root_.RHTower.eulerXiArchimedeanFactor
  change s * (s - 1) / 2 * Complex.Gammaℝ s ≠ 0
  exact mul_ne_zero
    (div_ne_zero (mul_ne_zero hs0 hs1) (by norm_num))
    (Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num))

/-- Exact completed-zeta factorization on the centered critical line. -/
theorem XiC_eq_c5XiArchimedeanFactor_mul_riemannZeta (t : ℝ) :
    _root_.RHTower.XiC (t : ℂ) =
      c5XiArchimedeanFactor (t : ℂ) *
        riemannZeta (1 / 2 + (t : ℂ) * Complex.I) := by
  let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  have hsre : s.re = 1 / 2 := by simp [s]
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hsre] at hre
    norm_num at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hsre] at hre
    norm_num at hre
  rw [_root_.RHTower.XiC,
    _root_.RHTower.xi_eq_mul_completedRiemannZeta hs0 hs1,
    _root_.RHTower.completedRiemannZeta_eq_Gammaℝ_mul (by rw [hsre]; norm_num)]
  unfold c5XiArchimedeanFactor _root_.RHTower.eulerXiArchimedeanFactor
  simp only [s]
  ring

/-- The card's literal global pointwise identity `exp P = zeta` on the critical
line is impossible. Any boundary prime expansion must remain distributional
and cannot be substituted into pointwise Jensen jets. -/
theorem not_exists_c5GlobalCriticalLineLogZeta :
    ¬ ∃ primeLog : ℝ → ℂ, ∀ t,
      Complex.exp (primeLog t) =
        riemannZeta (1 / 2 + (t : ℂ) * Complex.I) := by
  rintro ⟨primeLog, hprimeLog⟩
  obtain ⟨a, _, _, _, _, hza, _⟩ :=
    _root_.RHTower.exists_two_distinct_positive_real_XiC_zeros
  have hprod : c5XiArchimedeanFactor (a : ℂ) *
      riemannZeta (1 / 2 + (a : ℂ) * Complex.I) = 0 := by
    rw [← XiC_eq_c5XiArchimedeanFactor_mul_riemannZeta, hza]
  have hzeta : riemannZeta (1 / 2 + (a : ℂ) * Complex.I) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (c5XiArchimedeanFactor_ne_zero a)
  have hexp := hprimeLog a
  rw [hzeta] at hexp
  exact (Complex.exp_ne_zero _) hexp

/-- No global pointwise exponential prime part can multiply a nowhere-zero
archimedean factor to the centered completed zeta function on the real line. -/
theorem not_exists_c5GlobalPointwiseExponentialFactorization :
    ¬ ∃ arch primeLog : ℝ → ℂ,
      (∀ t, arch t ≠ 0) ∧
      ∀ t, arch t * Complex.exp (primeLog t) = _root_.RHTower.XiC (t : ℂ) := by
  rintro ⟨arch, primeLog, harch, hfactor⟩
  obtain ⟨a, _, _, _, _, hza, _⟩ :=
    _root_.RHTower.exists_two_distinct_positive_real_XiC_zeros
  have hzero : arch a * Complex.exp (primeLog a) = 0 := by
    rw [hfactor a, hza]
  exact (mul_ne_zero (harch a) (Complex.exp_ne_zero _)) hzero

/-- Critical C5 prime coefficients are not absolutely summable. -/
theorem not_summable_c5CriticalPrimeAmplitude :
    ¬ Summable c5CriticalPrimeAmplitude := by
  exact HTGeometry.not_summable_prime_rpow_of_exponent_le_one
    (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)

/-- Squaring the critical C5 prime coefficient gives the harmonic prime mass. -/
theorem c5CriticalPrimeAmplitude_sq (p : Nat.Primes) :
    c5CriticalPrimeAmplitude p ^ 2 = (p : ℝ) ^ (-1 : ℝ) := by
  unfold c5CriticalPrimeAmplitude
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  norm_num

/-- Critical C5 prime coefficients are not square summable. -/
theorem not_summable_sq_c5CriticalPrimeAmplitude :
    ¬ Summable (fun p : Nat.Primes => c5CriticalPrimeAmplitude p ^ 2) := by
  intro hs
  apply HTGeometry.not_summable_prime_rpow_of_exponent_le_one
    (a := (1 : ℝ)) (by norm_num) (by norm_num)
  exact hs.congr c5CriticalPrimeAmplitude_sq

/-- Exact finite single-prime C5 kernel built from the actual archimedean jet. -/
def c5ActualPrimeFirstOrderKernel
    (d : ℕ) (t : ℝ) (p : Nat.Primes) (X : ℂ) : ℂ :=
  (c5CriticalPrimeAmplitude p : ℂ) *
    ∑ i ∈ Finset.range (d + 1),
      if i = 0 then 0 else
        (-Complex.I * (Real.log (p : ℕ) : ℂ)) ^ i *
          c5JensenLeibnizCoefficient d (c5XiArchimedeanJet t) i X

/-- The literal first-order single-prime jet equals the finite actual-archimedean
kernel, with no zero-order term. -/
theorem c5JensenFirstOrderSection_actualPrime
    (d : ℕ) (t : ℝ) (p : Nat.Primes) (X : ℂ) :
    c5JensenFirstOrderSection d (c5XiArchimedeanJet t)
        (fun i => if i = 0 then 0 else
          (c5CriticalPrimeAmplitude p : ℂ) *
            (-Complex.I * (Real.log (p : ℕ) : ℂ)) ^ i) X =
      c5ActualPrimeFirstOrderKernel d t p X := by
  simpa [c5ActualPrimeFirstOrderKernel] using
    c5JensenFirstOrderSection_singleFrequency_noConstant d
      (c5XiArchimedeanJet t) (c5CriticalPrimeAmplitude p : ℂ)
      (Real.log (p : ℕ) : ℂ) X

/-- Strongest pointwise survivor: every simple root of the actual
archimedean Jensen section has an analytic branch under one finite prime
mode, with velocity given by the exact finite C5 kernel. -/
theorem exists_c5ActualPrimeJensenRootBranch
    (d : ℕ) (t : ℝ) (p : Nat.Primes) {r0 : ℂ}
    (hroot : (c5JensenSectionPolynomial d (c5XiArchimedeanJet t)).eval r0 = 0)
    (hsimple :
      (c5JensenSectionPolynomial d (c5XiArchimedeanJet t)).derivative.eval r0 ≠ 0) :
    ∃ r : ℂ → ℂ,
      AnalyticAt ℂ r 0 ∧ r 0 = r0 ∧
      (∀ᶠ epsilon in 𝓝 0,
        (c5JensenSectionPolynomial d (c5XiArchimedeanJet t)).eval (r epsilon) +
          epsilon * c5ActualPrimeFirstOrderKernel d t p (r epsilon) = 0) ∧
      HasDerivAt r
        (-c5ActualPrimeFirstOrderKernel d t p r0 /
          (c5JensenSectionPolynomial d
            (c5XiArchimedeanJet t)).derivative.eval r0) 0 := by
  simpa [c5ActualPrimeFirstOrderKernel] using
    exists_c5JensenLogFrequencyRootBranch d (c5XiArchimedeanJet t)
      (c5CriticalPrimeAmplitude p : ℂ) (Real.log (p : ℕ) : ℂ)
      hroot hsimple

/-- Closed proposition asserting the exact analytic simple-root response for
every degree, base point, prime, and admissible simple root. -/
def C5ActualPrimeSimpleRootLaw : Prop :=
  ∀ (d : ℕ) (t : ℝ) (p : Nat.Primes) (r0 : ℂ),
    (c5JensenSectionPolynomial d (c5XiArchimedeanJet t)).eval r0 = 0 →
    (c5JensenSectionPolynomial d
      (c5XiArchimedeanJet t)).derivative.eval r0 ≠ 0 →
    ∃ r : ℂ → ℂ,
      AnalyticAt ℂ r 0 ∧ r 0 = r0 ∧
      (∀ᶠ epsilon in 𝓝 0,
        (c5JensenSectionPolynomial d (c5XiArchimedeanJet t)).eval (r epsilon) +
          epsilon * c5ActualPrimeFirstOrderKernel d t p (r epsilon) = 0) ∧
      HasDerivAt r
        (-c5ActualPrimeFirstOrderKernel d t p r0 /
          (c5JensenSectionPolynomial d
            (c5XiArchimedeanJet t)).derivative.eval r0) 0

/-- The actual finite-prime simple-root law is unconditional as a universally
quantified implication; simplicity is its exact natural domain condition. -/
theorem c5ActualPrimeSimpleRootLaw : C5ActualPrimeSimpleRootLaw := by
  intro d t p r0 hroot hsimple
  exact exists_c5ActualPrimeJensenRootBranch d t p hroot hsimple

/-- Premise-free closure of the C5 card. It packages exact arithmetic
coefficients, actual critical-line factorization, both summability
obstructions, the finite actual-archimedean kernel, and its simple-root
response. It also records that the proposed global pointwise logarithmic
prime bridge is mathematically impossible. -/
theorem c5JensenPrimeKernelClosure_capstone :
    (∀ p : Nat.Primes,
      _root_.GaloisForLFunctions.logZetaPrimeCoeff (p : ℕ) =
        c5CriticalPrimeAmplitude p) ∧
    (∀ (p : Nat.Primes) (k : ℕ), k ≠ 0 →
      _root_.GaloisForLFunctions.logZetaPrimeCoeff ((p : ℕ) ^ k) =
        (p : ℝ) ^ (-(k : ℝ) / 2) / (k : ℝ)) ∧
    (∀ t : ℝ, _root_.RHTower.XiC (t : ℂ) =
      c5XiArchimedeanFactor (t : ℂ) *
        riemannZeta (1 / 2 + (t : ℂ) * Complex.I)) ∧
    (∀ t : ℝ, c5XiArchimedeanFactor (t : ℂ) ≠ 0) ∧
    (¬ ∃ primeLog : ℝ → ℂ, ∀ t,
      Complex.exp (primeLog t) =
        riemannZeta (1 / 2 + (t : ℂ) * Complex.I)) ∧
    (¬ Summable c5CriticalPrimeAmplitude) ∧
    (¬ Summable (fun p : Nat.Primes => c5CriticalPrimeAmplitude p ^ 2)) ∧
    (∀ (d : ℕ) (t : ℝ) (p : Nat.Primes) (X : ℂ),
      c5JensenFirstOrderSection d (c5XiArchimedeanJet t)
          (fun i => if i = 0 then 0 else
            (c5CriticalPrimeAmplitude p : ℂ) *
              (-Complex.I * (Real.log (p : ℕ) : ℂ)) ^ i) X =
        c5ActualPrimeFirstOrderKernel d t p X) ∧
    C5ActualPrimeSimpleRootLaw := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact _root_.GaloisForLFunctions.logZetaPrimeCoeff_prime p
  · intro p k hk
    exact _root_.GaloisForLFunctions.logZetaPrimeCoeff_primePower p hk
  · exact XiC_eq_c5XiArchimedeanFactor_mul_riemannZeta
  · exact c5XiArchimedeanFactor_ne_zero
  · exact not_exists_c5GlobalCriticalLineLogZeta
  · exact not_summable_c5CriticalPrimeAmplitude
  · exact not_summable_sq_c5CriticalPrimeAmplitude
  · exact c5JensenFirstOrderSection_actualPrime
  · exact c5ActualPrimeSimpleRootLaw

end

end GaloisForLFunctions.RHTower
