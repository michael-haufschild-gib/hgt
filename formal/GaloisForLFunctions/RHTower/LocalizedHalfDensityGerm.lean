import GaloisForLFunctions.RHTower.LocalizedHalfDensityCurvature
import GaloisForLFunctions.RHTower.ShiftedEulerQuotientCocycleFlatness

/-!
# The half-density germ, its exact inverse law, and the localized boundary curvature

The half-density coefficient `e_σ(n) = n^{σ/2} ∏_{p ∣ n} (1 - p^{-σ})` is the unique exponential
normalization of the Möbius boundary germ whose two boundary directions are exact Dirichlet
convolution inverses, `e_σ ⍟ e_{-σ} = ε`, and whose boundary jets are `e_0 = ε`, `e'_0 = Λ`,
`e''_0 = Λ ⍟ Λ`.

Localizing it by an even kernel `W` gives the exact boundary-curvature law

```text
½ H''_{R,W}(0) = L_W(R) − (Λ ⍟ Λ)(R) W(log R) ,
```

whose right-hand endpoint term is the contribution of the two trivial factorizations.  Deleting
those endpoints and centring the kernel forces the counterterm back explicitly:

```text
J_{R,A,c}(τ) = H_{R,T_c}(τ) + (c²/A) (e_{iτ}(R) + e_{-iτ}(R)) ,
½ J''_{R,A,c}(0) = L_{T_c}(R) − (c²/A)(Λ ⍟ Λ)(R) .
```

The counterterm carries no one-sided sign: already on an ordinary semiprime it is
`-8 sin(τ log p / 2) sin(τ log q / 2)`.

All second jets are genuine second derivatives: each fibre is a finite exponential mode sum in the
boundary parameter, so its second derivative at zero is the second moment of its modes.
-/

open ArithmeticFunction Finset GaloisForLFunctions.HTGeometry

open scoped ArithmeticFunction

namespace RHTower

noncomputable section

/-! ## Equations (5)--(7) and (16): the half-density germ and its exact inverse law -/

/-- **Equation (5).**  The half-density coefficient `e_σ(n) = n^{σ/2} ∏_{p ∣ n} (1 - p^{-σ})`,
presented as the Dirichlet convolution `(μ(d) d^{-σ/2}) ⍟ (e ↦ e^{σ/2})` that produces it. -/
def halfDensityCoeff (σ : ℂ) : ArithmeticFunction ℂ :=
  dirichletShift (σ / 2) ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) *
    dirichletShift (-(σ / 2)) ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)

/-- The half-density germ is the shifted Euler quotient stream at `σ = 2α`. -/
theorem halfDensityCoeff_two_mul_ofReal (α : ℝ) :
    halfDensityCoeff (2 * ((α : ℝ) : ℂ)) = suzukiCoeffAF α := by
  rw [halfDensityCoeff, suzukiCoeffAF_eq_convolution,
    show (2 * ((α : ℝ) : ℂ)) / 2 = ((α : ℝ) : ℂ) by ring]
  exact mul_comm _ _

/-- **Equation (6).**  The two boundary directions are exact Dirichlet-convolution inverses:
`e_σ ⍟ e_{-σ} = ε`. -/
theorem halfDensityCoeff_mul_neg (σ : ℂ) :
    halfDensityCoeff σ * halfDensityCoeff (-σ) = 1 := by
  set M : ArithmeticFunction ℂ := ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) with hM
  set Z : ArithmeticFunction ℂ := ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) with hZ
  have hMZ : M * Z = 1 := by
    rw [hM, hZ]
    exact coe_moebius_mul_coe_zeta
  rw [halfDensityCoeff, halfDensityCoeff, show (-σ) / 2 = -(σ / 2) by ring, neg_neg,
    show dirichletShift (σ / 2) M * dirichletShift (-(σ / 2)) Z
        * (dirichletShift (-(σ / 2)) M * dirichletShift (σ / 2) Z)
      = dirichletShift (σ / 2) M * dirichletShift (σ / 2) Z
        * (dirichletShift (-(σ / 2)) M * dirichletShift (-(σ / 2)) Z) from by ring,
    ← dirichletShift_mul, ← dirichletShift_mul, hMZ, dirichletShift_one, dirichletShift_one,
    one_mul]

/-- A positive integer power with complex exponent is an exponential of its logarithm. -/
theorem natCast_cpow_eq_cexp {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    (n : ℂ) ^ z = Complex.exp ((Real.log n : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log]

/-- The half-density germ is a finite exponential sum in the shift parameter. -/
theorem halfDensityCoeff_apply (σ : ℂ) {n : ℕ} (hn : n ≠ 0) :
    halfDensityCoeff σ n
      = ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℂ)
          * Complex.exp (σ * ((Real.log n / 2 - Real.log d : ℝ) : ℂ)) := by
  classical
  rw [halfDensityCoeff, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e =>
      dirichletShift (σ / 2) ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) d
        * dirichletShift (-(σ / 2)) ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) e)]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hn (Nat.eq_zero_of_zero_dvd hdvd)
  have hdiv0 : n / d ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨hd0, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd⟩
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hcastdiv : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
    rw [Nat.cast_div hdvd (ne_of_gt hdR)]
  have hlogdiv : Real.log ((n / d : ℕ) : ℝ) = Real.log n - Real.log d := by
    rw [hcastdiv, Real.log_div (by exact_mod_cast hn) (ne_of_gt hdR)]
  have hsplit : Complex.exp (σ * ((Real.log n / 2 - Real.log d : ℝ) : ℂ))
      = Complex.exp ((Real.log d : ℂ) * (-(σ / 2)))
        * Complex.exp (((Real.log n - Real.log d : ℝ) : ℂ) * (-(-(σ / 2)))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [dirichletShift_apply, dirichletShift_apply, cpowWeight, cpowWeight,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hdiv0,
    natCast_cpow_eq_cexp hd0, natCast_cpow_eq_cexp hdiv0, hlogdiv, hsplit]
  push_cast
  ring

/-- The value of the half-density germ at a prime. -/
theorem halfDensityCoeff_prime (σ : ℂ) {p : ℕ} (hp : p.Prime) :
    halfDensityCoeff σ p
      = Complex.exp (σ * ((Real.log p / 2 : ℝ) : ℂ))
        - Complex.exp (-(σ * ((Real.log p / 2 : ℝ) : ℂ))) := by
  classical
  have h2 : Complex.exp (σ * (((-(Real.log p / 2)) : ℝ) : ℂ))
      = Complex.exp (-(σ * ((Real.log p / 2 : ℝ) : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [halfDensityCoeff_apply σ hp.ne_zero, hp.divisors, Finset.sum_pair hp.one_lt.ne,
    ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hp,
    show Real.log ((1 : ℕ) : ℝ) = 0 by norm_num,
    show (Real.log ((p : ℕ) : ℝ) / 2 - 0 : ℝ) = Real.log p / 2 by ring,
    show (Real.log ((p : ℕ) : ℝ) / 2 - Real.log p : ℝ) = -(Real.log p / 2) by ring, h2]
  push_cast
  ring

/-- The half-density germ is multiplicative. -/
theorem isMultiplicative_halfDensityCoeff (σ : ℂ) :
    (halfDensityCoeff σ).IsMultiplicative :=
  (isMultiplicative_dirichletShift isMultiplicative_moebius.intCast).mul
    (isMultiplicative_dirichletShift isMultiplicative_zeta.natCast)

theorem halfDensityCoeff_semiprime (σ : ℂ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    halfDensityCoeff σ (p * q) = halfDensityCoeff σ p * halfDensityCoeff σ q :=
  (isMultiplicative_halfDensityCoeff σ).map_mul_of_coprime ((Nat.coprime_primes hp hq).mpr hpq)

/-- On the imaginary axis the prime value of the half-density germ is a pure sine. -/
theorem halfDensityCoeff_prime_imaginary (τ : ℝ) {p : ℕ} (hp : p.Prime) :
    halfDensityCoeff (Complex.I * (τ : ℂ)) p
      = 2 * Complex.I * (Real.sin (τ * Real.log p / 2) : ℂ) := by
  have key : ∀ x : ℝ, Complex.exp ((x : ℂ) * Complex.I) - Complex.exp (-(x : ℂ) * Complex.I)
      = 2 * Complex.I * (Real.sin x : ℂ) := by
    intro x
    rw [Complex.ofReal_sin]
    have h := Complex.two_sin ((x : ℝ) : ℂ)
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-Complex.I) * h
      + (Complex.exp ((x : ℂ) * Complex.I) - Complex.exp (-(x : ℂ) * Complex.I)) * hI
  rw [halfDensityCoeff_prime _ hp, ← key (τ * Real.log p / 2)]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring

/-- **Equation (16).**  The endpoint counterterm of an ordinary semiprime layer is the product of
two half-angle sines; in particular it changes sign. -/
theorem halfDensityCoeff_add_neg_semiprime (τ : ℝ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    halfDensityCoeff (Complex.I * (τ : ℂ)) (p * q)
        + halfDensityCoeff (-(Complex.I * (τ : ℂ))) (p * q)
      = -8 * (Real.sin (τ * Real.log p / 2) : ℂ) * (Real.sin (τ * Real.log q / 2) : ℂ) := by
  have hneg : -(Complex.I * (τ : ℂ)) = Complex.I * ((-τ : ℝ) : ℂ) := by
    push_cast
    ring
  have hsinp : Real.sin (-τ * Real.log p / 2) = -Real.sin (τ * Real.log p / 2) := by
    rw [show (-τ * Real.log p / 2 : ℝ) = -(τ * Real.log p / 2) by ring, Real.sin_neg]
  have hsinq : Real.sin (-τ * Real.log q / 2) = -Real.sin (τ * Real.log q / 2) := by
    rw [show (-τ * Real.log q / 2 : ℝ) = -(τ * Real.log q / 2) by ring, Real.sin_neg]
  rw [hneg, halfDensityCoeff_semiprime _ hp hq hpq, halfDensityCoeff_semiprime _ hp hq hpq,
    halfDensityCoeff_prime_imaginary τ hp, halfDensityCoeff_prime_imaginary τ hq,
    halfDensityCoeff_prime_imaginary (-τ) hp, halfDensityCoeff_prime_imaginary (-τ) hq,
    hsinp, hsinq]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [Complex.ofReal_neg, Complex.ofReal_neg]
  linear_combination (8 * (Real.sin (τ * Real.log p / 2) : ℂ)
    * (Real.sin (τ * Real.log q / 2) : ℂ)) * hI

/-! ## Equation (24): the unordered-pair relabeling is injective -/

theorem primeFactors_two_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p * q).primeFactors = {p, q} := by
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors,
    Finset.singleton_union]

/-- **Equation (24).**  Grouping the distinct-prime pair matrix by the product `R = pq` is only a
relabeling: the map from an unordered pair of distinct primes to its product is injective. -/
theorem two_prime_pair_injective {p q p' q' : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp' : p'.Prime) (hq' : q'.Prime) (h : p * q = p' * q') :
    ({p, q} : Finset ℕ) = {p', q'} := by
  rw [← primeFactors_two_prime hp hq, ← primeFactors_two_prime hp' hq', h]

/-! ## The finite exponential mode jet -/

/-- A finite complex-weighted exponential mode sum in a real parameter. -/
def expModeSum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (c : ι → ℝ) (τ : ℝ) : ℂ :=
  ∑ j ∈ s, a j * Complex.exp (Complex.I * (τ : ℂ) * (c j : ℂ))

theorem hasDerivAt_expModeSum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (c : ι → ℝ) (τ : ℝ) :
    HasDerivAt (expModeSum s a c)
      (expModeSum s (fun j => a j * (Complex.I * (c j : ℂ))) c τ) τ := by
  have hofReal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 τ := by
    simpa using (hasDerivAt_id τ).ofReal_comp
  have hterm : ∀ j ∈ s,
      HasDerivAt (fun t : ℝ => a j * Complex.exp (Complex.I * (t : ℂ) * (c j : ℂ)))
        (a j * (Complex.I * (c j : ℂ)) * Complex.exp (Complex.I * (τ : ℂ) * (c j : ℂ))) τ := by
    intro j _
    have hinner : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ) * (c j : ℂ))
        (Complex.I * 1 * (c j : ℂ)) τ :=
      (hofReal.const_mul Complex.I).mul_const (c j : ℂ)
    exact ((hinner.cexp).const_mul (a j)).congr_deriv (by ring)
  have hsum := HasDerivAt.sum hterm
  have hfun : (∑ j ∈ s, fun t : ℝ => a j * Complex.exp (Complex.I * (t : ℂ) * (c j : ℂ)))
      = expModeSum s a c := by
    funext t
    rw [Finset.sum_apply]
    rfl
  rw [← hfun]
  exact hsum

theorem deriv_expModeSum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (c : ι → ℝ) :
    deriv (expModeSum s a c) = expModeSum s (fun j => a j * (Complex.I * (c j : ℂ))) c := by
  funext τ
  exact (hasDerivAt_expModeSum s a c τ).deriv

/-- The second jet of a finite exponential mode sum is the second moment of its modes. -/
theorem iteratedDeriv_two_expModeSum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (c : ι → ℝ) :
    iteratedDeriv 2 (expModeSum s a c) 0 = -∑ j ∈ s, a j * (c j : ℂ) ^ 2 := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hterm : ∀ j ∈ s,
      (a j * (Complex.I * (c j : ℂ)) * (Complex.I * (c j : ℂ)))
          * Complex.exp (Complex.I * ((0 : ℝ) : ℂ) * (c j : ℂ))
        = -(a j * (c j : ℂ) ^ 2) := by
    intro j _
    rw [show Complex.I * ((0 : ℝ) : ℂ) * (c j : ℂ) = 0 by push_cast; ring, Complex.exp_zero,
      mul_one]
    linear_combination (a j * (c j : ℂ) ^ 2) * hI
  have hfin : ∑ j ∈ s, (a j * (Complex.I * (c j : ℂ)) * (Complex.I * (c j : ℂ)))
        * Complex.exp (Complex.I * ((0 : ℝ) : ℂ) * (c j : ℂ))
      = -∑ j ∈ s, a j * (c j : ℂ) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hterm
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_expModeSum,
    deriv_expModeSum]
  exact hfin

/-- A constant multiple of a second mode sum joins the first as one mode sum on the disjoint union
of the index sets. -/
theorem expModeSum_add_const_mul {ι κ : Type*} (s : Finset ι) (a : ι → ℂ) (c : ι → ℝ)
    (t : Finset κ) (b : κ → ℂ) (e : κ → ℝ) (z : ℂ) (τ : ℝ) :
    expModeSum s a c τ + z * expModeSum t b e τ
      = expModeSum (s.disjSum t) (Sum.elim a fun k => z * b k) (Sum.elim c e) τ := by
  rw [expModeSum, expModeSum, expModeSum, Finset.sum_disjSum, Finset.mul_sum]
  refine congrArg₂ (· + ·) rfl ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Sum.elim_inr, Sum.elim_inr]
  ring

/-! ## Equation (8): the localized half-density product fibre -/

/-- **Equation (8).**  The localized half-density product fibre of a layer against an even ratio
kernel. -/
def halfDensityFibre (W : ℝ → ℝ) (R : ℕ) (τ : ℝ) : ℂ :=
  ∑ x ∈ R.divisorsAntidiagonal,
    halfDensityCoeff (Complex.I * (τ : ℂ)) x.1 * halfDensityCoeff (-(Complex.I * (τ : ℂ))) x.2
      * (W (Real.log x.1 - Real.log x.2) : ℂ)

/-- The index set of the mode expansion of a product fibre. -/
def fibreModeIndex (R : ℕ) : Finset (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
  (R.divisorsAntidiagonal).sigma fun x => x.1.divisors ×ˢ x.2.divisors

/-- The mode weight of the fibre expansion. -/
def fibreModeWeight (W : ℝ → ℝ) (j : Σ _ : ℕ × ℕ, ℕ × ℕ) : ℂ :=
  ((moebius j.2.1 : ℤ) : ℂ) * ((moebius j.2.2 : ℤ) : ℂ)
    * (W (Real.log j.1.1 - Real.log j.1.2) : ℂ)

/-- The mode frequency of the fibre expansion. -/
def fibreModeFrequency (j : Σ _ : ℕ × ℕ, ℕ × ℕ) : ℝ :=
  (Real.log j.1.1 / 2 - Real.log j.2.1) - (Real.log j.1.2 / 2 - Real.log j.2.2)

/-- The half-density product fibre is a finite exponential mode sum. -/
theorem halfDensityFibre_eq_expModeSum (W : ℝ → ℝ) (R : ℕ) :
    halfDensityFibre W R
      = expModeSum (fibreModeIndex R) (fibreModeWeight W) fibreModeFrequency := by
  funext τ
  rw [halfDensityFibre, expModeSum, fibreModeIndex, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hxR, hR0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have hx1 : x.1 ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hxR
    exact hR0 hxR.symm
  have hx2 : x.2 ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hxR
    exact hR0 hxR.symm
  rw [Finset.sum_product, halfDensityCoeff_apply _ hx1, halfDensityCoeff_apply _ hx2,
    Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hmul : Complex.exp (Complex.I * (τ : ℂ) * ((Real.log x.1 / 2 - Real.log d : ℝ) : ℂ))
      * Complex.exp (-(Complex.I * (τ : ℂ)) * ((Real.log x.2 / 2 - Real.log e : ℝ) : ℂ))
      = Complex.exp (Complex.I * (τ : ℂ)
          * ((((Real.log x.1 / 2 - Real.log d) - (Real.log x.2 / 2 - Real.log e)) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [fibreModeWeight, fibreModeFrequency]
  linear_combination (((moebius d : ℤ) : ℂ) * ((moebius e : ℤ) : ℂ)
    * (W (Real.log x.1 - Real.log x.2) : ℂ)) * hmul

/-- The second jet of the half-density product fibre. -/
theorem iteratedDeriv_two_halfDensityFibre (W : ℝ → ℝ) (R : ℕ) :
    iteratedDeriv 2 (halfDensityFibre W R) 0
      = -∑ x ∈ R.divisorsAntidiagonal, ∑ d ∈ x.1.divisors, ∑ e ∈ x.2.divisors,
          (((moebius d : ℤ) : ℂ) * ((moebius e : ℤ) : ℂ)
            * (W (Real.log x.1 - Real.log x.2) : ℂ))
          * ((((Real.log x.1 / 2 - Real.log d)
              - (Real.log x.2 / 2 - Real.log e)) : ℝ) : ℂ) ^ 2 := by
  rw [halfDensityFibre_eq_expModeSum W R, iteratedDeriv_two_expModeSum, fibreModeIndex,
    Finset.sum_sigma]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [fibreModeWeight, fibreModeFrequency]

/-- **Equation (10).**  The exact localized boundary curvature: the second jet of the half-density
product fibre is the localized von Mangoldt pair sum minus the two trivial endpoint
factorizations. -/
theorem halfDensityFibre_second_derivative (W : ℝ → ℝ) (hW : ∀ x : ℝ, W (-x) = W x)
    {R : ℕ} (hR : R ≠ 0) :
    (1 / 2 : ℂ) * iteratedDeriv 2 (halfDensityFibre W R) 0
      = ((localizedVonMangoldtPair W R : ℝ) : ℂ)
        - (((Λ * Λ) R * W (Real.log R) : ℝ) : ℂ) := by
  have hreal : ∀ x : ℕ × ℕ,
      (∑ d ∈ x.1.divisors, ∑ e ∈ x.2.divisors,
          (((moebius d : ℤ) : ℂ) * ((moebius e : ℤ) : ℂ)
            * (W (Real.log x.1 - Real.log x.2) : ℂ))
          * ((((Real.log x.1 / 2 - Real.log d)
              - (Real.log x.2 / 2 - Real.log e)) : ℝ) : ℂ) ^ 2)
        = (((∑ d ∈ x.1.divisors, ∑ e ∈ x.2.divisors,
            ((moebius d : ℤ) : ℝ) * ((moebius e : ℤ) : ℝ)
              * ((Real.log x.1 / 2 - Real.log d) - (Real.log x.2 / 2 - Real.log e)) ^ 2)
            * W (Real.log x.1 - Real.log x.2) : ℝ) : ℂ) := by
    intro x
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have hjet := fibre_second_jet hR W hW
  rw [iteratedDeriv_two_halfDensityFibre W R, Finset.sum_congr rfl (fun x _ => hreal x),
    ← Complex.ofReal_sum,
    show ((1 : ℂ) / 2) * (-(((∑ x ∈ R.divisorsAntidiagonal,
        (∑ d ∈ x.1.divisors, ∑ e ∈ x.2.divisors,
          ((moebius d : ℤ) : ℝ) * ((moebius e : ℤ) : ℝ)
            * ((Real.log x.1 / 2 - Real.log d) - (Real.log x.2 / 2 - Real.log e)) ^ 2)
          * W (Real.log x.1 - Real.log x.2) : ℝ) : ℝ) : ℂ))
      = (((-(1 / 2 : ℝ)) * ∑ x ∈ R.divisorsAntidiagonal,
        (∑ d ∈ x.1.divisors, ∑ e ∈ x.2.divisors,
          ((moebius d : ℤ) : ℝ) * ((moebius e : ℤ) : ℝ)
            * ((Real.log x.1 / 2 - Real.log d) - (Real.log x.2 / 2 - Real.log e)) ^ 2)
          * W (Real.log x.1 - Real.log x.2) : ℝ) : ℂ) from by push_cast; ring,
    hjet, localizedVonMangoldtPair]
  push_cast
  ring

/-! ## Equations (13)--(15): endpoint deletion and the interior curvature -/

/-- Only the two trivial factorizations of a nontrivial layer have a unit factor. -/
theorem antidiagonal_filter_not_interior {R : ℕ} (hR : 1 < R) :
    (R.divisorsAntidiagonal).filter (fun x => ¬ (1 < x.1 ∧ 1 < x.2)) = {(1, R), (R, 1)} := by
  classical
  have hR0 : R ≠ 0 := by omega
  ext x
  simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hx, -⟩, hnot⟩
    have hx1 : x.1 ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hx
      exact hR0 hx.symm
    have hx2 : x.2 ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hx
      exact hR0 hx.symm
    rcases not_and_or.mp hnot with h | h
    · have h1 : x.1 = 1 := by omega
      refine Or.inl (Prod.ext_iff.mpr ⟨h1, ?_⟩)
      rw [h1, one_mul] at hx
      exact hx
    · have h2 : x.2 = 1 := by omega
      refine Or.inr (Prod.ext_iff.mpr ⟨?_, h2⟩)
      rw [h2, mul_one] at hx
      exact hx
  · rintro (rfl | rfl)
    · exact ⟨⟨one_mul R, hR0⟩, by simp⟩
    · exact ⟨⟨mul_one R, hR0⟩, by simp⟩

/-- **Equation (13).**  The interior fibre: the two trivial factorization endpoints deleted and the
ratio kernel centred. -/
def halfDensityInteriorFibre (A c : ℝ) (R : ℕ) (τ : ℝ) : ℂ :=
  ∑ x ∈ (R.divisorsAntidiagonal).filter (fun x => 1 < x.1 ∧ 1 < x.2),
    halfDensityCoeff (Complex.I * (τ : ℂ)) x.1 * halfDensityCoeff (-(Complex.I * (τ : ℂ))) x.2
      * (centredTriangularKernel A c (Real.log x.1 - Real.log x.2) : ℂ)

/-- **Equation (14).**  Exact endpoint deletion before differentiation: matching the active
fixed-ratio block forces the constant centring back as an explicit endpoint counterterm. -/
theorem halfDensityInteriorFibre_eq (A c : ℝ) {R : ℕ} (hR : 1 < R) (hc : c ≤ Real.log R) (τ : ℝ) :
    halfDensityInteriorFibre A c R τ
      = halfDensityFibre (triangularKernel c) R τ
        + ((c ^ 2 / A : ℝ) : ℂ) * (halfDensityCoeff (Complex.I * (τ : ℂ)) R
            + halfDensityCoeff (-(Complex.I * (τ : ℂ))) R) := by
  classical
  have hR0 : R ≠ 0 := by omega
  have hRne1 : R ≠ 1 := by omega
  set σ : ℂ := Complex.I * (τ : ℂ) with hσ
  set F : ℕ × ℕ → ℂ := fun x => halfDensityCoeff σ x.1 * halfDensityCoeff (-σ) x.2 with hF
  have hone : halfDensityCoeff σ 1 = 1 := (isMultiplicative_halfDensityCoeff σ).map_one
  have honeneg : halfDensityCoeff (-σ) 1 = 1 := (isMultiplicative_halfDensityCoeff (-σ)).map_one
  have htotal : ∑ x ∈ R.divisorsAntidiagonal, F x = 0 := by
    have happ : (halfDensityCoeff σ * halfDensityCoeff (-σ)) R = (1 : ArithmeticFunction ℂ) R := by
      rw [halfDensityCoeff_mul_neg σ]
    rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply_ne hRne1] at happ
    exact happ
  have hendpoints : ((R.divisorsAntidiagonal).filter (fun x => ¬ (1 < x.1 ∧ 1 < x.2)))
      = {(1, R), (R, 1)} := antidiagonal_filter_not_interior hR
  have hpairne : ((1, R) : ℕ × ℕ) ≠ (R, 1) := by
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro h
    omega
  have hlog1 : Real.log ((1 : ℕ) : ℝ) = 0 := by norm_num
  have hlogRpos : 0 ≤ Real.log ((R : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hR.le)
  have hT1 : triangularKernel c (Real.log ((1 : ℕ) : ℝ) - Real.log ((R : ℕ) : ℝ)) = 0 := by
    refine triangularKernel_eq_zero_of_le ?_
    rw [hlog1, zero_sub, abs_neg, abs_of_nonneg hlogRpos]
    exact hc
  have hT2 : triangularKernel c (Real.log ((R : ℕ) : ℝ) - Real.log ((1 : ℕ) : ℝ)) = 0 := by
    refine triangularKernel_eq_zero_of_le ?_
    rw [hlog1, sub_zero, abs_of_nonneg hlogRpos]
    exact hc
  have hnotT : ∑ x ∈ (R.divisorsAntidiagonal).filter (fun x => ¬ (1 < x.1 ∧ 1 < x.2)),
      F x * (triangularKernel c (Real.log x.1 - Real.log x.2) : ℂ) = 0 := by
    rw [hendpoints, Finset.sum_pair hpairne, hT1, hT2]
    simp
  have hnotF : ∑ x ∈ (R.divisorsAntidiagonal).filter (fun x => ¬ (1 < x.1 ∧ 1 < x.2)), F x
      = halfDensityCoeff (-σ) R + halfDensityCoeff σ R := by
    rw [hendpoints, Finset.sum_pair hpairne]
    simp only [hF, hone, honeneg, one_mul, mul_one]
  have hsplitT := Finset.sum_filter_add_sum_filter_not (R.divisorsAntidiagonal)
    (fun x => 1 < x.1 ∧ 1 < x.2)
    (fun x => F x * (triangularKernel c (Real.log x.1 - Real.log x.2) : ℂ))
  have hsplitF := Finset.sum_filter_add_sum_filter_not (R.divisorsAntidiagonal)
    (fun x => 1 < x.1 ∧ 1 < x.2) F
  rw [hnotT, add_zero] at hsplitT
  rw [hnotF, htotal] at hsplitF
  have hinterior : ∑ x ∈ (R.divisorsAntidiagonal).filter (fun x => 1 < x.1 ∧ 1 < x.2), F x
      = -(halfDensityCoeff (-σ) R + halfDensityCoeff σ R) := by linear_combination hsplitF
  have hsplitKernel : halfDensityInteriorFibre A c R τ
      = (∑ x ∈ (R.divisorsAntidiagonal).filter (fun x => 1 < x.1 ∧ 1 < x.2),
          F x * (triangularKernel c (Real.log x.1 - Real.log x.2) : ℂ))
        - ((c ^ 2 / A : ℝ) : ℂ)
          * ∑ x ∈ (R.divisorsAntidiagonal).filter (fun x => 1 < x.1 ∧ 1 < x.2), F x := by
    rw [halfDensityInteriorFibre, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [centredTriangularKernel, hF]
    push_cast
    ring
  rw [hsplitKernel, hsplitT, hinterior, halfDensityFibre, hF]
  push_cast
  ring

/-- The index set of the endpoint counterterm modes. -/
def endpointModeIndex (R : ℕ) : Finset (ℕ ⊕ ℕ) := R.divisors.disjSum R.divisors

/-- The weight of the endpoint counterterm modes. -/
def endpointModeWeight : ℕ ⊕ ℕ → ℂ :=
  Sum.elim (fun d => ((moebius d : ℤ) : ℂ)) fun d => ((moebius d : ℤ) : ℂ)

/-- The frequency of the endpoint counterterm modes. -/
def endpointModeFrequency (R : ℕ) : ℕ ⊕ ℕ → ℝ :=
  Sum.elim (fun d => Real.log R / 2 - Real.log d) fun d => -(Real.log R / 2 - Real.log d)

theorem halfDensityCoeff_pair_eq_expModeSum {R : ℕ} (hR : R ≠ 0) :
    (fun τ : ℝ => halfDensityCoeff (Complex.I * (τ : ℂ)) R
        + halfDensityCoeff (-(Complex.I * (τ : ℂ))) R)
      = expModeSum (endpointModeIndex R) endpointModeWeight (endpointModeFrequency R) := by
  funext τ
  rw [expModeSum, endpointModeIndex, Finset.sum_disjSum, halfDensityCoeff_apply _ hR,
    halfDensityCoeff_apply _ hR]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun d _ => ?_
    simp only [endpointModeWeight, endpointModeFrequency, Sum.elim_inl]
  · refine Finset.sum_congr rfl fun d _ => ?_
    simp only [endpointModeWeight, endpointModeFrequency, Sum.elim_inr]
    congr 1
    push_cast
    ring_nf

/-- The second jet of the endpoint counterterm is twice the pure convolution square. -/
theorem iteratedDeriv_two_halfDensityCoeff_pair {R : ℕ} (hR : R ≠ 0) :
    iteratedDeriv 2 (fun τ : ℝ => halfDensityCoeff (Complex.I * (τ : ℂ)) R
        + halfDensityCoeff (-(Complex.I * (τ : ℂ))) R) 0
      = -2 * (((Λ * Λ) R : ℝ) : ℂ) := by
  rw [halfDensityCoeff_pair_eq_expModeSum hR, iteratedDeriv_two_expModeSum, endpointModeIndex,
    Finset.sum_disjSum]
  have h1 : ∀ d ∈ R.divisors, endpointModeWeight (Sum.inl d)
      * ((endpointModeFrequency R (Sum.inl d) : ℝ) : ℂ) ^ 2
      = (((moebius d : ℤ) : ℝ) * (Real.log R / 2 - Real.log d) ^ 2 : ℝ) := by
    intro d _
    simp only [endpointModeWeight, endpointModeFrequency, Sum.elim_inl]
    push_cast
    ring
  have h2 : ∀ d ∈ R.divisors, endpointModeWeight (Sum.inr d)
      * ((endpointModeFrequency R (Sum.inr d) : ℝ) : ℂ) ^ 2
      = (((moebius d : ℤ) : ℝ) * (Real.log R / 2 - Real.log d) ^ 2 : ℝ) := by
    intro d _
    simp only [endpointModeWeight, endpointModeFrequency, Sum.elim_inr]
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Complex.ofReal_sum,
    sum_divisors_moebius_half_sq hR]
  ring

/-- The second jet of a mode sum plus a constant multiple of a second mode sum. -/
theorem iteratedDeriv_two_expModeSum_add_const_mul {ι κ : Type*} (s : Finset ι) (a : ι → ℂ)
    (c : ι → ℝ) (t : Finset κ) (b : κ → ℂ) (e : κ → ℝ) (z : ℂ) :
    iteratedDeriv 2 (fun τ : ℝ => expModeSum s a c τ + z * expModeSum t b e τ) 0
      = (-∑ j ∈ s, a j * (c j : ℂ) ^ 2) + z * (-∑ j ∈ t, b j * (e j : ℂ) ^ 2) := by
  have hfun : (fun τ : ℝ => expModeSum s a c τ + z * expModeSum t b e τ)
      = expModeSum (s.disjSum t) (Sum.elim a fun k => z * b k) (Sum.elim c e) := by
    funext τ
    exact expModeSum_add_const_mul s a c t b e z τ
  rw [hfun, iteratedDeriv_two_expModeSum, Finset.sum_disjSum]
  have h1 : ∀ j ∈ s, (Sum.elim a fun k => z * b k) (Sum.inl j)
      * (((Sum.elim c e) (Sum.inl j) : ℝ) : ℂ) ^ 2 = a j * (c j : ℂ) ^ 2 := by
    intro j _
    simp only [Sum.elim_inl]
  have h2 : ∀ j ∈ t, (Sum.elim a fun k => z * b k) (Sum.inr j)
      * (((Sum.elim c e) (Sum.inr j) : ℝ) : ℂ) ^ 2 = z * (b j * (e j : ℂ) ^ 2) := by
    intro j _
    simp only [Sum.elim_inr]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum]
  ring

/-- **Equation (15).**  The exact all-grade survivor: the second jet of the interior fibre is the
localized von Mangoldt pair sum of the centred fixed-ratio kernel. -/
theorem halfDensityInteriorFibre_second_derivative (A c : ℝ) {R : ℕ} (hR : 1 < R)
    (hc : c ≤ Real.log R) :
    (1 / 2 : ℂ) * iteratedDeriv 2 (halfDensityInteriorFibre A c R) 0
      = ((localizedVonMangoldtPair (triangularKernel c) R : ℝ) : ℂ)
        - ((c ^ 2 / A : ℝ) : ℂ) * (((Λ * Λ) R : ℝ) : ℂ) := by
  have hR0 : R ≠ 0 := by omega
  have hfun : halfDensityInteriorFibre A c R
      = fun τ : ℝ => expModeSum (fibreModeIndex R) (fibreModeWeight (triangularKernel c))
            fibreModeFrequency τ
          + ((c ^ 2 / A : ℝ) : ℂ)
            * expModeSum (endpointModeIndex R) endpointModeWeight (endpointModeFrequency R) τ := by
    funext τ
    rw [halfDensityInteriorFibre_eq A c hR hc τ,
      ← congrFun (halfDensityFibre_eq_expModeSum (triangularKernel c) R) τ,
      ← congrFun (halfDensityCoeff_pair_eq_expModeSum hR0) τ]
  have hT : triangularKernel c (Real.log R) = 0 := by
    refine triangularKernel_eq_zero_of_le ?_
    rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hR.le))]
    exact hc
  have hjet := halfDensityFibre_second_derivative (triangularKernel c) (triangularKernel_even c)
    hR0
  have hpair := iteratedDeriv_two_halfDensityCoeff_pair hR0
  rw [halfDensityCoeff_pair_eq_expModeSum hR0] at hpair
  rw [halfDensityFibre_eq_expModeSum (triangularKernel c) R] at hjet
  rw [hfun, iteratedDeriv_two_expModeSum_add_const_mul]
  rw [iteratedDeriv_two_expModeSum] at hjet hpair
  rw [hT] at hjet
  linear_combination (norm := (push_cast; ring)) hjet + ((c ^ 2 / A : ℝ) : ℂ) / 2 * hpair

/-! ## Equation (21): the spectral reading of an even kernel -/

/-- **Equation (21).**  If the ratio kernel has a Fourier representation with matching
normalization, the localized von Mangoldt pair sum of a layer is the spectral average of its
twisted product fibre. -/
theorem localizedVonMangoldtPair_eq_integral (W : ℝ → ℝ) (Wh : ℝ → ℂ) (R : ℕ)
    (hrep : ∀ y : ℝ, ((W y : ℝ) : ℂ)
      = ∫ t : ℝ, Wh t * Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)))
    (hint : ∀ y : ℝ, MeasureTheory.Integrable
      (fun t : ℝ => Wh t * Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)))) :
    ((localizedVonMangoldtPair W R : ℝ) : ℂ) = ∫ t : ℝ, Wh t * twistedFibre t R := by
  classical
  have hfibre : ∀ t : ℝ, Wh t * twistedFibre t R
      = ∑ x ∈ R.divisorsAntidiagonal, ((Λ x.1 * Λ x.2 : ℝ) : ℂ)
          * (Wh t * Complex.exp (Complex.I * (t : ℂ)
              * ((Real.log x.1 - Real.log x.2 : ℝ) : ℂ))) := by
    intro t
    rw [twistedFibre, ArithmeticFunction.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hxR, hR0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hx1 : x.1 ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hxR
      exact hR0 hxR.symm
    have hx2 : x.2 ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hxR
      exact hR0 hxR.symm
    have hmul : Complex.exp ((Real.log x.1 : ℂ) * (Complex.I * (t : ℂ)))
        * Complex.exp ((Real.log x.2 : ℂ) * (Complex.I * ((-t : ℝ) : ℂ)))
        = Complex.exp (Complex.I * (t : ℂ)
            * ((Real.log x.1 - Real.log x.2 : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [twistedVonMangoldt_apply, twistedVonMangoldt_apply, natCast_cpow_eq_cexp hx1,
      natCast_cpow_eq_cexp hx2, Complex.ofReal_mul]
    linear_combination (Wh t * (Λ x.1 : ℂ) * (Λ x.2 : ℂ)) * hmul
  have hswap : ∫ t : ℝ, Wh t * twistedFibre t R
      = ∑ x ∈ R.divisorsAntidiagonal, ((Λ x.1 * Λ x.2 : ℝ) : ℂ)
          * ∫ t : ℝ, Wh t * Complex.exp (Complex.I * (t : ℂ)
              * ((Real.log x.1 - Real.log x.2 : ℝ) : ℂ)) := by
    rw [funext hfibre, MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun x _ => ?_
      exact MeasureTheory.integral_const_mul _ _
    · intro x _
      exact (hint _).const_mul _
  rw [hswap, localizedVonMangoldtPair, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hrep, Complex.ofReal_mul]

/-! ## Equation (5): the Euler product form of the half-density germ -/

theorem dirichletShift_zero (f : ArithmeticFunction ℂ) : dirichletShift 0 f = f := by
  ext n
  rw [dirichletShift_apply, cpowWeight, neg_zero, Complex.cpow_zero, one_mul]

/-- **Equation (7), zeroth jet.**  `e_0 = ε`. -/
theorem halfDensityCoeff_zero : halfDensityCoeff 0 = 1 := by
  rw [halfDensityCoeff, zero_div, neg_zero, dirichletShift_zero, dirichletShift_zero]
  exact coe_moebius_mul_coe_zeta

theorem sum_divisors_prime_pow_moebius_cpow (σ : ℂ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ∑ d ∈ (p ^ k).divisors,
        dirichletShift σ ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) d
      = 1 - (p : ℂ) ^ (-σ) := by
  rw [Nat.sum_divisors_prime_pow hp]
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (k + 1) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> (simp only [Finset.mem_range]; omega)
  have hzero : ∀ i ∈ Finset.range (k + 1), i ∉ ({0, 1} : Finset ℕ) →
      dirichletShift σ ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) (p ^ i) = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [dirichletShift_apply, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [← Finset.sum_subset hsub hzero, Finset.sum_insert (by norm_num), Finset.sum_singleton,
    pow_zero, pow_one, dirichletShift_apply, dirichletShift_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.isMultiplicative_moebius.1,
    cpowWeight, cpowWeight, Nat.cast_one, Complex.one_cpow]
  push_cast
  ring

/-- The complex Euler product of the Möbius power sum over the divisors of a layer. -/
theorem sum_divisors_moebius_cpow (σ : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℂ) * (d : ℂ) ^ (-σ)
      = ∏ p ∈ n.primeFactors, (1 - (p : ℂ) ^ (-σ)) := by
  have hzeta : ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ).IsMultiplicative :=
    isMultiplicative_zeta.natCast
  have hM := isMultiplicative_dirichletShift (a := σ)
    (f := ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ))
    isMultiplicative_moebius.intCast
  have hfact := (hzeta.mul hM).multiplicative_factorization _ hn
  rw [ArithmeticFunction.coe_zeta_mul_apply] at hfact
  have hsum : ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℂ) * (d : ℂ) ^ (-σ)
      = ∑ d ∈ n.divisors,
        dirichletShift σ ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) d := by
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [dirichletShift_apply, cpowWeight, ArithmeticFunction.intCoe_apply]
    ring
  rw [hsum, hfact, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hk : n.factorization p ≠ 0 := by
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpos : 0 < n.factorization p := Nat.Prime.factorization_pos_of_dvd hprime hn hdvd
    omega
  rw [ArithmeticFunction.coe_zeta_mul_apply, sum_divisors_prime_pow_moebius_cpow σ hprime hk]

/-- **Equation (5), Euler product form.**  `e_σ(n) = n^{σ/2} ∏_{p ∣ n} (1 - p^{-σ})`. -/
theorem halfDensityCoeff_eq_prod (σ : ℂ) {n : ℕ} (hn : n ≠ 0) :
    halfDensityCoeff σ n
      = (n : ℂ) ^ (σ / 2) * ∏ p ∈ n.primeFactors, (1 - (p : ℂ) ^ (-σ)) := by
  rw [← sum_divisors_moebius_cpow σ hn, halfDensityCoeff_apply σ hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hn (Nat.eq_zero_of_zero_dvd hdvd)
  have hsplit : (n : ℂ) ^ (σ / 2) * ((d : ℂ) ^ (-σ))
      = Complex.exp (σ * ((Real.log n / 2 - Real.log d : ℝ) : ℂ)) := by
    rw [natCast_cpow_eq_cexp hn, natCast_cpow_eq_cexp hd0, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (-((moebius d : ℤ) : ℂ)) * hsplit

/-! ## Equations (7) and (12): the boundary jets of the germ -/

theorem halfDensityCoeff_eq_expModeSum {n : ℕ} (hn : n ≠ 0) :
    (fun τ : ℝ => halfDensityCoeff (Complex.I * (τ : ℂ)) n)
      = expModeSum n.divisors (fun d => ((moebius d : ℤ) : ℂ))
          fun d => Real.log n / 2 - Real.log d := by
  funext τ
  rw [expModeSum, halfDensityCoeff_apply _ hn]

/-- **Equation (7), first jet.**  `e'_0 = Λ`. -/
theorem deriv_halfDensityCoeff {n : ℕ} (hn : n ≠ 0) :
    deriv (fun τ : ℝ => halfDensityCoeff (Complex.I * (τ : ℂ)) n) 0
      = Complex.I * ((Λ n : ℝ) : ℂ) := by
  rw [halfDensityCoeff_eq_expModeSum hn, deriv_expModeSum, expModeSum]
  have h : ∀ d ∈ n.divisors,
      ((moebius d : ℤ) : ℂ) * (Complex.I * ((Real.log n / 2 - Real.log d : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((0 : ℝ) : ℂ) * ((Real.log n / 2 - Real.log d : ℝ) : ℂ))
      = Complex.I * (((moebius d : ℤ) : ℝ) * (Real.log n / 2 - Real.log d) : ℝ) := by
    intro d _
    rw [show Complex.I * ((0 : ℝ) : ℂ) * ((Real.log n / 2 - Real.log d : ℝ) : ℂ) = 0 by
      push_cast; ring, Complex.exp_zero, mul_one]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ← Complex.ofReal_sum,
    sum_divisors_moebius_half hn]

/-- **Equation (7), second jet.**  `e''_0 = Λ ⍟ Λ`, read as an actual second derivative along the
imaginary boundary direction. -/
theorem iteratedDeriv_two_halfDensityCoeff {n : ℕ} (hn : n ≠ 0) :
    iteratedDeriv 2 (fun τ : ℝ => halfDensityCoeff (Complex.I * (τ : ℂ)) n) 0
      = -(((Λ * Λ) n : ℝ) : ℂ) := by
  rw [halfDensityCoeff_eq_expModeSum hn, iteratedDeriv_two_expModeSum]
  have h : ∀ d ∈ n.divisors,
      ((moebius d : ℤ) : ℂ) * ((Real.log n / 2 - Real.log d : ℝ) : ℂ) ^ 2
        = (((moebius d : ℤ) : ℝ) * (Real.log n / 2 - Real.log d) ^ 2 : ℝ) := by
    intro d _
    push_cast
    ring
  rw [Finset.sum_congr rfl h, ← Complex.ofReal_sum, sum_divisors_moebius_half_sq hn]

/-- **Equation (12).**  Beyond the kernel aperture the endpoint term drops out and the curvature is
the pure localized pair sum. -/
theorem halfDensityFibre_second_derivative_triangular (c : ℝ) {R : ℕ} (hR : 1 < R)
    (hc : c ≤ Real.log R) :
    (1 / 2 : ℂ) * iteratedDeriv 2 (halfDensityFibre (triangularKernel c) R) 0
      = ((localizedVonMangoldtPair (triangularKernel c) R : ℝ) : ℂ) := by
  have hT : triangularKernel c (Real.log ((R : ℕ) : ℝ)) = 0 := by
    refine triangularKernel_eq_zero_of_le ?_
    rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hR.le))]
    exact hc
  rw [halfDensityFibre_second_derivative (triangularKernel c) (triangularKernel_even c)
    (by omega : R ≠ 0), hT]
  push_cast
  ring

end

end RHTower
