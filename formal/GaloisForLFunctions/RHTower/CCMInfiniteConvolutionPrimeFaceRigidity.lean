import GaloisForLFunctions.RHTower.CCMFirstClockHalfWaveReflection

/-!
# Infinite Dirichlet-convolution functionals are scalar on the CCM prime face

For Dirichlet convolution, evaluation at a prime obeys an exact Leibniz rule: only the factor
pairs `(1,p)` and `(p,1)` occur.  Consequently every convolution power obeys a chain rule on the
prime face.  Passing to an arbitrary coefficientwise infinite convolution series gives

`(sum_n c_n f^{*n})(p) = (sum_n c_n n f(1)^{n-1}) f(p)`.

Thus adjoining an arbitrary scalar Gamma/unit coordinate and applying any infinite
Dirichlet-convolution functional cannot mix distinct prime atoms.  On the literal CCM first
clock, its complete prime layer is multiplied by one aperture-independent scalar.  Nonlinear
convolution may alter composite and higher prime-power layers, but it cannot implement the
required non-diagonal transport of irreducible outer primes into inner primes plus Gamma mass.

No RH, zero-location, finiteness, or numerical hypothesis is used.  At a prime every convolution
power is exactly its first differential in the prime direction, so the coefficientwise `tsum`
identity reduces to the displayed prime derivative.  Ordinary convergent analytic series are an
immediate specialization.
-/

open ArithmeticFunction Finset

namespace RHTower

noncomputable section

/-- Dirichlet convolution has an exact two-term Leibniz rule at every prime. -/
theorem arithmeticFunction_mul_apply_prime
    {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R)
    {p : ℕ} (hp : p.Prime) :
    (f * g) p = f 1 * g p + f p * g 1 := by
  have hanti :
      p.divisorsAntidiagonal = {(1, p), (p, 1)} := by
    ext xy
    rw [Nat.mem_divisorsAntidiagonal]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hprod, _hp0⟩
      rcases hp.eq_one_or_self_of_dvd xy.1 ⟨xy.2, hprod.symm⟩ with hx | hx
      · left
        apply Prod.ext
        · exact hx
        · simpa [hx] using hprod
      · right
        apply Prod.ext
        · exact hx
        · exact Nat.mul_left_cancel hp.pos (by simpa [hx] using hprod)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hp.ne_zero]
  rw [ArithmeticFunction.mul_apply, hanti]
  simp [hp.ne_one]

/-- Dirichlet convolution evaluated at the unit is ordinary multiplication. -/
theorem arithmeticFunction_mul_apply_one
    {R : Type*} [Semiring R]
    (f g : ArithmeticFunction R) :
    (f * g) 1 = f 1 * g 1 := by
  rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one]
  simp

/-- Every convolution power has the expected unit coefficient. -/
theorem arithmeticFunction_pow_apply_one
    {R : Type*} [Semiring R]
    (f : ArithmeticFunction R) (n : ℕ) :
    (f ^ n) 1 = f 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, arithmeticFunction_mul_apply_one, ih, pow_succ]

/-- **Prime-face convolution chain rule.**  The prime coefficient of the `n`th Dirichlet
convolution power is the formal derivative of `X^n` at the unit coefficient, multiplied by the
original prime coefficient. -/
theorem arithmeticFunction_pow_apply_prime_chainRule
    (f : ArithmeticFunction ℝ)
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (f ^ n) p = (n : ℝ) * f 1 ^ (n - 1) * f p := by
  induction n with
  | zero =>
      simp [ArithmeticFunction.one_apply_ne hp.ne_one]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [pow_succ, arithmeticFunction_mul_apply_prime _ _ hp, ih,
        arithmeticFunction_pow_apply_one]
      simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one, pow_succ]
      ring

/-- Noncommutative derivative of the `n`th power at `a` in direction `b`. -/
def dirichletConvolutionPowerPrimeDifferential
    {R : Type*} [Semiring R] (a b : R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range n, a ^ i * b * a ^ (n - 1 - i)

/-- **Noncommutative prime-face chain rule.**  For arithmetic functions valued in any semiring,
the prime coefficient of a convolution power is the full noncommutative derivative of the power
map.  This covers operator-valued and infinite-dimensional coefficient algebras. -/
theorem arithmeticFunction_pow_apply_prime_noncommutative
    {R : Type*} [Semiring R]
    (f : ArithmeticFunction R)
    {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (f ^ n) p =
      dirichletConvolutionPowerPrimeDifferential (f 1) (f p) n := by
  induction n with
  | zero =>
      simp [dirichletConvolutionPowerPrimeDifferential,
        ArithmeticFunction.one_apply_ne hp.ne_one]
  | succ n ih =>
      rw [pow_succ, arithmeticFunction_mul_apply_prime _ _ hp, ih,
        arithmeticFunction_pow_apply_one]
      simp only [dirichletConvolutionPowerPrimeDifferential]
      rw [Finset.sum_range_succ, Finset.sum_mul]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      rw [mul_assoc, ← pow_succ]
      congr 2
      omega

/-- Coefficientwise infinite convolution series with values in an arbitrary real Banach algebra.
The algebra may be noncommutative and infinite-dimensional. -/
def operatorDirichletConvolutionSeries
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (c : ℕ → ℝ) (f : ArithmeticFunction A) :
    ArithmeticFunction A :=
  ⟨fun k => ∑' n, c n • (f ^ n) k, by simp⟩

/-- Universal operator-valued prime derivative selected by an infinite convolution series. -/
def operatorConvolutionSeriesPrimeDifferential
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (c : ℕ → ℝ) (a b : A) : A :=
  ∑' n, c n • dirichletConvolutionPowerPrimeDifferential a b n

/-- **Infinite operator-valued prime-face rigidity.**  Every coefficientwise infinite
Dirichlet-convolution functional acts at each prime through the same derivative map, evaluated on
that prime coefficient.  It cannot mix coefficients belonging to distinct primes. -/
theorem operatorDirichletConvolutionSeries_apply_prime
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (c : ℕ → ℝ) (f : ArithmeticFunction A)
    {p : ℕ} (hp : p.Prime) :
    operatorDirichletConvolutionSeries c f p =
      operatorConvolutionSeriesPrimeDifferential c (f 1) (f p) := by
  rw [operatorDirichletConvolutionSeries,
    operatorConvolutionSeriesPrimeDifferential]
  change (∑' n, c n • (f ^ n) p) =
    ∑' n, c n •
      dirichletConvolutionPowerPrimeDifferential (f 1) (f p) n
  apply tsum_congr
  intro n
  rw [arithmeticFunction_pow_apply_prime_noncommutative f hp n]

/-- Coefficientwise infinite Dirichlet-convolution functional.  Its prime coefficient is always
a one-term derivative law, independently of convergence behavior on composite coefficients. -/
def dirichletConvolutionSeries
    (c : ℕ → ℝ) (f : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ :=
  ⟨fun k => ∑' n, c n * (f ^ n) k, by simp⟩

/-- Scalar derivative selected by the irreducible prime face. -/
def dirichletConvolutionSeriesPrimeDerivative
    (c : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∑' n, c n * (n : ℝ) * a ^ (n - 1)

/-- **Infinite prime-face rigidity law.**  Every coefficientwise infinite convolution
functional is scalar on all primes, with the same scalar at every prime. -/
theorem dirichletConvolutionSeries_apply_prime
    (c : ℕ → ℝ) (f : ArithmeticFunction ℝ)
    {p : ℕ} (hp : p.Prime) :
    dirichletConvolutionSeries c f p =
      dirichletConvolutionSeriesPrimeDerivative c (f 1) * f p := by
  rw [dirichletConvolutionSeries]
  change (∑' n, c n * (f ^ n) p) =
    dirichletConvolutionSeriesPrimeDerivative c (f 1) * f p
  calc
    (∑' n, c n * (f ^ n) p) =
        ∑' n, (c n * (n : ℝ) * f 1 ^ (n - 1)) * f p := by
          apply tsum_congr
          intro n
          rw [arithmeticFunction_pow_apply_prime_chainRule f hp n]
          ring
    _ = dirichletConvolutionSeriesPrimeDerivative c (f 1) * f p := by
          rw [dirichletConvolutionSeriesPrimeDerivative, tsum_mul_right]

/-- Arithmetic prime source with an arbitrary scalar unit/Gamma coordinate. -/
def ccmGammaSewnVonMangoldtSource (a : ℝ) : ArithmeticFunction ℝ :=
  a • (1 : ArithmeticFunction ℝ) + ArithmeticFunction.vonMangoldt

@[simp] theorem ccmGammaSewnVonMangoldtSource_apply_one (a : ℝ) :
    ccmGammaSewnVonMangoldtSource a 1 = a := by
  simp [ccmGammaSewnVonMangoldtSource]

theorem ccmGammaSewnVonMangoldtSource_apply_prime
    (a : ℝ) {p : ℕ} (hp : p.Prime) :
    ccmGammaSewnVonMangoldtSource a p = Real.log p := by
  simp [ccmGammaSewnVonMangoldtSource, hp.ne_one,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- Physical first-clock atom after arbitrary scalar Gamma sewing and an infinite nonlinear
Dirichlet-convolution functional. -/
def ccmGammaSewnConvolutionPrimeClockAtom
    (c : ℕ → ℝ) (a L : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-1 / 2 : ℝ) *
    dirichletConvolutionSeries c (ccmGammaSewnVonMangoldtSource a) p *
      Real.sin ((2 * Real.pi / L) * Real.log p)

/-- Every transformed literal prime atom is the original CCM first-clock atom multiplied by the
same prime-independent derivative scalar. -/
theorem ccmGammaSewnConvolutionPrimeClockAtom_eq_derivative_mul
    (c : ℕ → ℝ) (a L : ℝ) {p : ℕ} (hp : p.Prime) :
    ccmGammaSewnConvolutionPrimeClockAtom c a L p =
      dirichletConvolutionSeriesPrimeDerivative c a *
        (criticalMellinAtomWeight p *
          Real.sin ((2 * Real.pi / L) * Real.log p)) := by
  rw [ccmGammaSewnConvolutionPrimeClockAtom,
    dirichletConvolutionSeries_apply_prime c
      (ccmGammaSewnVonMangoldtSource a) hp,
    ccmGammaSewnVonMangoldtSource_apply_one,
    ccmGammaSewnVonMangoldtSource_apply_prime a hp,
    criticalMellinAtomWeight,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  ring

/-- Original irreducible-prime layer of the literal physical CCM first clock. -/
def ccmFirstClockIrreduciblePrimeSineMass (L : ℝ) : ℝ :=
  ∑ k ∈ (Finset.Icc 2 ⌊Real.exp L⌋₊).filter Nat.Prime,
    criticalMellinAtomWeight k *
      Real.sin ((2 * Real.pi / L) * Real.log k)

/-- Prime layer after arbitrary scalar Gamma sewing and an infinite convolution functional. -/
def ccmGammaSewnConvolutionPrimeSineMass
    (c : ℕ → ℝ) (a L : ℝ) : ℝ :=
  ∑ k ∈ (Finset.Icc 2 ⌊Real.exp L⌋₊).filter Nat.Prime,
    ccmGammaSewnConvolutionPrimeClockAtom c a L k

/-- **CCM irreducible-prime rigidity.**  At every aperture, the whole transformed prime layer is
one scalar multiple of the original literal prime layer.  Hence infinite convolution nonlinearities
and scalar Gamma sewing cannot implement any non-diagonal outer-to-inner transport on primes. -/
theorem ccmGammaSewnConvolutionPrimeSineMass_eq_derivative_mul
    (c : ℕ → ℝ) (a L : ℝ) :
    ccmGammaSewnConvolutionPrimeSineMass c a L =
      dirichletConvolutionSeriesPrimeDerivative c a *
        ccmFirstClockIrreduciblePrimeSineMass L := by
  rw [ccmGammaSewnConvolutionPrimeSineMass,
    ccmFirstClockIrreduciblePrimeSineMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  exact ccmGammaSewnConvolutionPrimeClockAtom_eq_derivative_mul
    c a L hp.2

end

end RHTower
