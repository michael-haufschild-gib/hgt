import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialAffineClockResonance
import GaloisForLFunctions.RHTower.BakerGeneralConsequences
import GaloisForLFunctions.RHTower.BakerProof.BakerIteration

/-!
# Baker Prime-Logarithm Transcendence, Collar Width Transcendence, and Spectral Disjointness

This module connects the unconditional qualitative Baker theorem on linear forms in logarithms
(`RHTower/BakerGeneralConsequences.lean`, `RHTower/BakerProof/BakerIteration.lean`) to the
factorial arithmetic collar and Bohr resonance analysis of `ArithmeticPositivityTheory`
(`FactorialCollarIrrationalityAndSpacing.lean`, `FactorialAffineClockResonance.lean`):

1. **Transcendence of Every Non-Trivial $\overline{\mathbb{Q}}$-Linear Form in Prime Logarithms
   (`primeLog_linearForm_transcendental`, `real_primeLog_linearForm_transcendental`):**
   Combines `bakerLinearIndependence_holds` (`BakerIteration.lean:995`) with
   `baker_linearForm_transcendental` (`BakerGeneralConsequences.lean:19`) to prove that for any
   injective family of primes $p_1, \dots, p_n$ and any algebraic coefficients $c_1, \dots, c_n$
   not all zero, the linear form $\sum_{i=1}^n c_i \log p_i$ is transcendental over $\mathbb{Q}$.

2. **Cubic Algebraicity of Collar Frequencies vs. Transcendence of the Logarithmic Collar Width
   (`isAlgebraic_factorialShiftedFreq`, `isAlgebraic_collar_linearForm`,
   `transcendental_sourceFactorialWidth`):**
   - For every $N \ge 1$, the shifted collar frequency $\lambda_N = N(1 + \varepsilon_N)$ satisfies
     $4 \lambda_N^3 = N^2 (4N + 1)$ (`four_mul_factorialShiftedFreq_cube`), so $\lambda_N$ is
     algebraic over $\mathbb{Q}$ (of degree $3$, since it is irrational by
     `irrational_factorialShiftedFreq`), and every $\overline{\mathbb{Q}}$-linear combination
     $\sum_{j=1}^m \alpha_j \lambda_{N_j}$ is algebraic over $\mathbb{Q}$.
   - By contrast, the logarithmic collar width
     $\operatorname{sourceFactorialWidth}(N) = \frac{1}{3} \log(1 + \frac{1}{4N})$ satisfies
     $\exp(3 \operatorname{sourceFactorialWidth}(N)) = 1 + \frac{1}{4N} \in \mathbb{Q}_{>1}$, so
     Baker's theorem implies that $\operatorname{sourceFactorialWidth}(N)$ is transcendental over
     $\mathbb{Q}$ for every $N \ge 1$.

3. **Absolute Spectral Disjointness and Zero Bohr Cross-Correlation Between Prime Logarithms and
   Factorial Collar Harmonics
   (`primeLog_linearForm_ne_collar_linearForm`, `tendsto_primeLog_sub_collar_bohr_zero`):**
   Upgrades the rational non-resonance theorem `mul_factorialShiftedFreq_ne_mul_nat`
   (`FactorialCollarIrrationalityAndSpacing.lean:147`): because every non-trivial
   $\overline{\mathbb{Q}}$-linear combination of prime logarithms is transcendental while every
   $\overline{\mathbb{Q}}$-linear combination of factorial collar frequencies is algebraic, the two
   spectra are strictly disjoint and their relative phase has vanishing Bohr mean as $L \to \infty$.
-/

open scoped Classical BigOperators Topology
open Filter MeasureTheory Set
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-! ## §1. Transcendence of Non-Trivial $\overline{\mathbb{Q}}$-Linear Forms in Prime Logarithms -/

/-- A real number algebraic over `ℚ` remains algebraic over `ℚ` under `ℝ ↪ ℂ`. -/
theorem isAlgebraic_rat_ofReal {x : ℝ} (hx : IsAlgebraic ℚ x) :
    IsAlgebraic ℚ (x : ℂ) := by
  have h := hx.algHom (IsScalarTower.toAlgHom ℚ ℝ ℂ)
  have heq : (IsScalarTower.toAlgHom ℚ ℝ ℂ) x = (x : ℂ) := by
    simp [Complex.coe_algebraMap]
  rwa [heq] at h

/-- If the complex embedding of a real number is transcendental over `ℚ`, so is the real number. -/
theorem transcendental_rat_ofReal {x : ℝ} (hx : Transcendental ℚ (x : ℂ)) :
    Transcendental ℚ x :=
  fun halg => hx (isAlgebraic_rat_ofReal halg)

/-- For every prime $p$, the complex prime logarithm $(\log p : \mathbb{C})$ is a logarithm of an
algebraic number (`IsLogarithmOfAlgebraic`). -/
theorem isLogarithmOfAlgebraic_primeLog {p : ℕ} (hp : p.Prime) :
    IsLogarithmOfAlgebraic ((Real.log (p : ℝ) : ℝ) : ℂ) := by
  unfold IsLogarithmOfAlgebraic
  rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hp.pos)]
  have hnat : ((p : ℝ) : ℂ) = algebraMap ℚ ℂ (p : ℚ) := by simp
  rw [hnat]
  exact isAlgebraic_algebraMap (p : ℚ)

/-- Any finite injective family of primes has $\mathbb{Q}$-linearly independent complex logarithms. -/
theorem linearIndependent_rat_primeLog {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime) :
    LinearIndependent ℚ (fun i => ((Real.log (p i) : ℝ) : ℂ)) := by
  rw [Fintype.linearIndependent_iff]
  intro q hsum i
  have hβalg : ∀ j, IsAlgebraic ℤ ((q j : ℚ) : ℂ) := fun j => by
    apply (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr
    have hrat : ((q j : ℚ) : ℂ) = algebraMap ℚ ℂ (q j) := by simp
    rw [hrat]
    exact isAlgebraic_algebraMap (q j)
  have hrel : ∑ j, ((q j : ℚ) : ℂ) * ((Real.log (p j) : ℝ) : ℂ) = 0 := by
    simpa [Algebra.smul_def] using hsum
  have hz := bakerLinearIndependence_holds n p (fun j => ((q j : ℚ) : ℂ))
    hp hprime hβalg hrel i
  exact_mod_cast hz

/-- **Complex Baker Transcendence for Prime Logarithms (`primeLog_linearForm_transcendental`):**
Every non-trivial $\overline{\mathbb{Q}}$-linear combination of logarithms of distinct primes is
transcendental over $\mathbb{Q}$. -/
theorem primeLog_linearForm_transcendental {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (β : Fin n → ℂ) (hβ : ∀ i, IsAlgebraic ℚ (β i)) (hne : ∃ i, β i ≠ 0) :
    Transcendental ℚ (∑ i, β i * ((Real.log (p i) : ℝ) : ℂ)) :=
  baker_linearForm_transcendental
    (fun i => ((Real.log (p i) : ℝ) : ℂ)) β
    (fun i => isLogarithmOfAlgebraic_primeLog (hprime i))
    (linearIndependent_rat_primeLog p hp hprime)
    hβ hne

/-- **Real Baker Transcendence for Prime Logarithms (`real_primeLog_linearForm_transcendental`):**
For any injective family of primes $p : \operatorname{Fin} n \to \mathbb{N}$ and any real algebraic
coefficients $c : \operatorname{Fin} n \to \mathbb{R}$ not all zero, the real linear form
$\sum_{i=1}^n c_i \log p_i$ is transcendental over $\mathbb{Q}$. -/
theorem real_primeLog_linearForm_transcendental {n : ℕ} (p : Fin n → ℕ)
    (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (c : Fin n → ℝ) (hc : ∀ i, IsAlgebraic ℚ (c i)) (hne : ∃ i, c i ≠ 0) :
    Transcendental ℚ (∑ i, c i * Real.log (p i)) := by
  apply transcendental_rat_ofReal
  have hcast : (((∑ i, c i * Real.log (p i) : ℝ) : ℂ)) =
      ∑ i, (c i : ℂ) * ((Real.log (p i) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  refine primeLog_linearForm_transcendental p hp hprime
    (fun i => (c i : ℂ)) (fun i => isAlgebraic_rat_ofReal (hc i)) ?_
  obtain ⟨i, hi⟩ := hne
  exact ⟨i, Complex.ofReal_ne_zero.mpr hi⟩

/-! ## §2. Cubic Algebraicity of Collar Frequencies vs. Transcendence of Collar Width -/

/-- **Cubic Algebraicity of `factorialShiftedFreq N` (`isAlgebraic_factorialShiftedFreq`):**
For every $N \ge 1$, the shifted collar frequency $\lambda_N = N(1 + \varepsilon_N)$ satisfies
$4 \lambda_N^3 - N^2(4N + 1) = 0$ and is therefore algebraic over $\mathbb{Q}$. -/
theorem isAlgebraic_factorialShiftedFreq {N : ℕ} (hN : 1 ≤ N) :
    IsAlgebraic ℚ (factorialShiftedFreq N) := by
  let c0 : ℚ := (N : ℚ) ^ (2 : ℕ) * (4 * (N : ℚ) + 1)
  let P : Polynomial ℚ :=
    Polynomial.C (4 : ℚ) * Polynomial.X ^ (3 : ℕ) - Polynomial.C c0
  refine ⟨P, ?_, ?_⟩
  · intro hP0
    have hcoeff : P.coeff 3 = 4 := by
      dsimp only [P]
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl, Polynomial.coeff_C, if_neg (by norm_num : (3 : ℕ) ≠ 0)]
      ring
    rw [hP0, Polynomial.coeff_zero] at hcoeff
    norm_num at hcoeff
  · dsimp only [P, c0]
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow,
      eq_ratCast, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_add,
      Rat.cast_natCast, Rat.cast_one]
    linarith [four_mul_factorialShiftedFreq_cube hN]

/-- **Algebraicity of Every $\overline{\mathbb{Q}}$-Linear Combination of Collar Frequencies
(`isAlgebraic_collar_linearForm`):**
For any finite family of scales $N : \operatorname{Fin} m \to \mathbb{N}$ with $N_j \ge 1$ and any
real algebraic coefficients $\alpha : \operatorname{Fin} m \to \mathbb{R}$, the linear combination
$\sum_{j=1}^m \alpha_j \lambda_{N_j}$ is algebraic over $\mathbb{Q}$. -/
theorem isAlgebraic_collar_linearForm {m : ℕ} (N : Fin m → ℕ) (hN : ∀ j, 1 ≤ N j)
    (α : Fin m → ℝ) (hα : ∀ j, IsAlgebraic ℚ (α j)) :
    IsAlgebraic ℚ (∑ j, α j * factorialShiftedFreq (N j)) := by
  classical
  have hsum : ∀ s : Finset (Fin m),
      IsAlgebraic ℚ (∑ j ∈ s, α j * factorialShiftedFreq (N j)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact isAlgebraic_zero
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact ((hα j).mul (isAlgebraic_factorialShiftedFreq (hN j))).add ih
  exact hsum Finset.univ

/-- **Transcendence of the Logarithmic Collar Width (`transcendental_sourceFactorialWidth`):**
Whereas the multiplicative collar frequency $\lambda_N = N \exp(\operatorname{sourceFactorialWidth}(N))$
is algebraic of degree $3$, the logarithmic collar width
$\operatorname{sourceFactorialWidth}(N) = \frac{1}{3}\log(1 + \frac{1}{4N})$ itself is
transcendental over $\mathbb{Q}$ for every $N \ge 1$. -/
theorem transcendental_sourceFactorialWidth {N : ℕ} (hN : 1 ≤ N) :
    Transcendental ℚ (sourceFactorialWidth N) := by
  apply transcendental_rat_ofReal
  let lam0 : Fin 1 → ℂ := fun _ => ((3 * sourceFactorialWidth N : ℝ) : ℂ)
  let beta0 : Fin 1 → ℂ := fun _ => ((1 / 3 : ℝ) : ℂ)
  have hpos : 0 < sourceFactorialWidth N :=
    lt_of_lt_of_le (by positivity) (sourceFactorialWidth_bounds hN).1
  have hlamne : lam0 0 ≠ 0 := by
    dsimp [lam0]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have halg : ∀ i : Fin 1, IsLogarithmOfAlgebraic (lam0 i) := by
    intro _
    unfold IsLogarithmOfAlgebraic
    dsimp [lam0]
    rw [← Complex.ofReal_exp, exp_three_sourceFactorialWidth N]
    have hrat : (((1 + 1 / (4 * (N : ℝ)) : ℝ) : ℂ)) =
        algebraMap ℚ ℂ (1 + 1 / (4 * (N : ℚ))) := by simp
    rw [hrat]
    exact isAlgebraic_algebraMap _
  have hind : LinearIndependent ℚ lam0 :=
    Fintype.linearIndependent_iff.mpr fun g hg i => by
      fin_cases i
      rw [Fin.sum_univ_one, smul_eq_zero] at hg
      rcases hg with hg0 | hlam0
      · exact hg0
      · exact (hlamne hlam0).elim
  have hβalg : ∀ i : Fin 1, IsAlgebraic ℚ (beta0 i) := by
    intro _
    dsimp [beta0]
    have hrat : (((1 / 3 : ℝ) : ℂ)) = algebraMap ℚ ℂ (1 / 3 : ℚ) := by simp
    rw [hrat]
    exact isAlgebraic_algebraMap _
  have hβne : ∃ i : Fin 1, beta0 i ≠ 0 := ⟨0, by dsimp [beta0]; norm_num⟩
  have htrans := baker_linearForm_transcendental lam0 beta0 halg hind hβalg hβne
  have hform : (∑ i : Fin 1, beta0 i * lam0 i) = (sourceFactorialWidth N : ℂ) := by
    rw [Fin.sum_univ_one]
    dsimp [beta0, lam0]
    push_cast
    ring
  rwa [hform] at htrans

/-! ## §3. Spectral Disjointness and Zero Bohr Cross-Correlation -/

/-- **Absolute Disjointness Between the Prime-Logarithm Spectrum and the Factorial Collar Spectrum
(`primeLog_linearForm_ne_collar_linearForm`):**
For any injective family of primes $p : \operatorname{Fin} n \to \mathbb{N}$, any real algebraic
coefficients $c : \operatorname{Fin} n \to \mathbb{R}$ not all zero, any collar scales
$N : \operatorname{Fin} m \to \mathbb{N}$ with $N_j \ge 1$, and any real algebraic collar
coefficients $\alpha : \operatorname{Fin} m \to \mathbb{R}$,
$$\sum_{i=1}^n c_i \log p_i \neq \sum_{j=1}^m \alpha_j \operatorname{factorialShiftedFreq}(N_j).$$ -/
theorem primeLog_linearForm_ne_collar_linearForm
    {n m : ℕ} (p : Fin n → ℕ) (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (c : Fin n → ℝ) (hc : ∀ i, IsAlgebraic ℚ (c i)) (hne : ∃ i, c i ≠ 0)
    (N : Fin m → ℕ) (hN : ∀ j, 1 ≤ N j)
    (α : Fin m → ℝ) (hα : ∀ j, IsAlgebraic ℚ (α j)) :
    (∑ i, c i * Real.log (p i)) ≠ ∑ j, α j * factorialShiftedFreq (N j) := by
  intro heq
  apply real_primeLog_linearForm_transcendental p hp hprime c hc hne
  rw [heq]
  exact isAlgebraic_collar_linearForm N hN α hα

/-- **Vanishing Bohr Cross-Correlation Between Prime-Logarithm Modes and Collar Modes
(`tendsto_primeLog_sub_collar_bohr_zero`):**
Because $\sum_i c_i \log p_i \neq \sum_j \alpha_j \lambda_{N_j}$, their frequency difference is
strictly non-zero and the continuous Bohr mean of the relative phase tends to $0$ as $L \to \infty$. -/
theorem tendsto_primeLog_sub_collar_bohr_zero
    {n m : ℕ} (p : Fin n → ℕ) (hp : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (c : Fin n → ℝ) (hc : ∀ i, IsAlgebraic ℚ (c i)) (hne : ∃ i, c i ≠ 0)
    (N : Fin m → ℕ) (hN : ∀ j, 1 ≤ N j)
    (α : Fin m → ℝ) (hα : ∀ j, IsAlgebraic ℚ (α j)) :
    Tendsto (fun L : ℝ => ((1 / L : ℝ) : ℂ) *
      ∫ v in (0 : ℝ)..L,
        Complex.exp ((Complex.I *
          ((2 * Real.pi *
            ((∑ i, c i * Real.log (p i)) -
              ∑ j, α j * factorialShiftedFreq (N j)) : ℝ) : ℂ)) *
          (v : ℂ))) atTop (𝓝 0) := by
  apply tendsto_bohr_mean_cexp_zero_of_ne_zero
  have hdiff : (∑ i, c i * Real.log (p i)) - ∑ j, α j * factorialShiftedFreq (N j) ≠ 0 :=
    sub_ne_zero.mpr (primeLog_linearForm_ne_collar_linearForm p hp hprime c hc hne N hN α hα)
  exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hdiff

end

end GaloisForLFunctions.ArithmeticPositivityTheory
