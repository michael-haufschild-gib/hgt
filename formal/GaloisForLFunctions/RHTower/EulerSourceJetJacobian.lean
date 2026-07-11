import GaloisForLFunctions.RHTower.PinnedAffinePrimeJetRigidity
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# The finite Euler-source jet Jacobian

For distinct prime labels `p i`, vary the degree-one local Euler factors

`(1 - a i * (p i)^(-s))^(-1)`

near the trivial parameter `a = 0`.  The differential at zero of the first `k`
derivatives of the negative logarithmic derivative is the weighted Vandermonde map below.
The weights are nonzero and the nodes `-log (p i)` are distinct, so this Jacobian is
bijective.  This is the algebraic certificate used by the holomorphic inverse-function
argument proving local finite-jet openness of degree-one Euler sources.
-/

noncomputable section

namespace RHTower

open Complex
open scoped BigOperators

/-- The differential at the trivial Euler product of the first `k` logarithmic-flux
jet coordinates. -/
def eulerSourceJetJacobian {k : ℕ} (p : Fin k → ℕ) (s₀ : ℂ)
    (a : Fin k → ℂ) : Fin k → ℂ :=
  fun j ↦ ∑ i : Fin k,
    a i * ((Real.log (p i) : ℂ) * (p i : ℂ) ^ (-s₀)) *
      (-(Real.log (p i) : ℂ)) ^ (j : ℕ)

/-- **Nonsingular Euler-source jet Jacobian.**  Every finite target jet has a unique
preimage under the differential at the trivial degree-one Euler product. -/
theorem existsUnique_eulerSourceJetJacobian_preimage {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p)
    (s₀ : ℂ) (c : Fin k → ℂ) :
    ∃! a : Fin k → ℂ, eulerSourceJetJacobian p s₀ a = c := by
  have hpos : ∀ i, 0 < p i := fun i ↦ (Nat.zero_lt_one.trans (hp i))
  have hweight : ∀ i : Fin k,
      (Real.log (p i) : ℂ) * (p i : ℂ) ^ (-s₀) ≠ 0 := by
    intro i
    apply mul_ne_zero
    · exact_mod_cast (Real.log_pos (by exact_mod_cast hp i)).ne'
    · exact Complex.cpow_ne_zero_iff.mpr
        (Or.inl (by exact_mod_cast (hpos i).ne'))
  simpa only [eulerSourceJetJacobian, funext_iff] using
    existsUnique_weightedFiniteMoments
      (fun i ↦ -(Real.log (p i) : ℂ))
      (fun i ↦ (Real.log (p i) : ℂ) * (p i : ℂ) ^ (-s₀))
      (neg_log_nat_injective p hpos hpinj) hweight c

/-- Function-level form of the nonsingular Jacobian certificate. -/
theorem eulerSourceJetJacobian_bijective {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p)
    (s₀ : ℂ) :
    Function.Bijective (eulerSourceJetJacobian p s₀) := by
  constructor
  · intro a b hab
    obtain ⟨x, hx, huniq⟩ :=
      existsUnique_eulerSourceJetJacobian_preimage p hp hpinj s₀
        (eulerSourceJetJacobian p s₀ a)
    exact (huniq a rfl).trans (huniq b hab.symm).symm
  · intro c
    obtain ⟨a, ha, _⟩ :=
      existsUnique_eulerSourceJetJacobian_preimage p hp hpinj s₀ c
    exact ⟨a, ha⟩

/-! ## All-prime coefficient faithfulness -/

/-- The ordinary Dirichlet coefficient stream of a degree-one Euler logarithmic flux.
At a prime power `p^m` it is `(log p) * (a p)^m`, and it vanishes off prime powers. -/
def degreeOneEulerFluxCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if IsPrimePow n then
    (Real.log (Nat.minFac n) : ℂ) *
      a (Nat.minFac n) ^ n.factorization (Nat.minFac n)
  else 0

@[simp]
theorem degreeOneEulerFluxCoeff_prime (a : ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    degreeOneEulerFluxCoeff a p = (Real.log p : ℂ) * a p := by
  rw [degreeOneEulerFluxCoeff, if_pos hp.isPrimePow, hp.minFac_eq,
    hp.factorization_self]
  simp

@[simp]
theorem degreeOneEulerFluxCoeff_eq_zero_of_not_isPrimePow
    (a : ℕ → ℂ) {n : ℕ} (hn : ¬IsPrimePow n) :
    degreeOneEulerFluxCoeff a n = 0 := by
  simp [degreeOneEulerFluxCoeff, hn]

@[simp]
theorem degreeOneEulerFluxCoeff_prime_pow (a : ℕ → ℂ)
    {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    degreeOneEulerFluxCoeff a (p ^ m) =
      (Real.log p : ℂ) * (a p) ^ m := by
  rw [degreeOneEulerFluxCoeff,
    if_pos ((isPrimePow_pow_iff hm).2 hp.isPrimePow), hp.pow_minFac hm,
    Nat.factorization_pow]
  simp [hp.factorization_self]

/-- Degree-one local factors are exactly geometric along every prime-power ray. -/
theorem degreeOneEulerFluxCoeff_prime_ray_mul (a : ℕ → ℂ)
    {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    degreeOneEulerFluxCoeff a (p ^ m) * degreeOneEulerFluxCoeff a (p ^ n) =
      (Real.log p : ℂ) * degreeOneEulerFluxCoeff a (p ^ (m + n)) := by
  rw [degreeOneEulerFluxCoeff_prime_pow a hp hm,
    degreeOneEulerFluxCoeff_prime_pow a hp hn,
    degreeOneEulerFluxCoeff_prime_pow a hp (add_ne_zero.mpr (Or.inl hm)), pow_add]
  ring

/-- The zeta parameter field `a_p = 1` recovers the complexified von Mangoldt stream. -/
theorem degreeOneEulerFluxCoeff_one_eq_vonMangoldt (n : ℕ) :
    degreeOneEulerFluxCoeff (fun _ ↦ 1) n =
      (ArithmeticFunction.vonMangoldt n : ℂ) := by
  rw [degreeOneEulerFluxCoeff, ArithmeticFunction.vonMangoldt_apply]
  split_ifs <;> simp

/-- **All-prime parameter recovery from the Euler flux Dirichlet series.**  Whenever the two
coefficient streams converge somewhere, equality of their L-series recovers every prime-local
degree-one parameter.  This is the coefficient-uniqueness step in full-jet faithfulness. -/
theorem degreeOneEulerParameter_eq_of_LSeries_eq
    (a b : ℕ → ℂ)
    (ha : LSeries.abscissaOfAbsConv (degreeOneEulerFluxCoeff a) < ⊤)
    (hb : LSeries.abscissaOfAbsConv (degreeOneEulerFluxCoeff b) < ⊤)
    (hseries : LSeries (degreeOneEulerFluxCoeff a) =
      LSeries (degreeOneEulerFluxCoeff b)) :
    ∀ p : ℕ, p.Prime → a p = b p := by
  intro p hp
  have hcoeff :=
    (LSeries_eq_iff_of_abscissaOfAbsConv_lt_top ha hb).mp hseries p hp.ne_zero
  rw [degreeOneEulerFluxCoeff_prime a hp,
    degreeOneEulerFluxCoeff_prime b hp] at hcoeff
  exact (mul_left_cancel₀ (by exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'))
    hcoeff

/-! ## Exact coefficient-image classification -/

/-- A coefficient stream has degree-one Euler shape when it is supported on prime powers and,
after normalization by `log p`, every prime-power ray is the geometric sequence generated by its
prime coefficient.  This is an all-order condition: it constrains every exponent on every prime
ray, not any finite jet projection. -/
def DegreeOneEulerRayCompatible (c : ℕ → ℂ) : Prop :=
  (∀ n : ℕ, ¬ IsPrimePow n → c n = 0) ∧
    ∀ (p m : ℕ), p.Prime → m ≠ 0 →
      c (p ^ m) =
        (Real.log p : ℂ) * (c p / (Real.log p : ℂ)) ^ m

/-- Recover the local Euler parameter at an integer label directly from its prime coefficient. -/
def degreeOneEulerParameterOfCoeff (c : ℕ → ℂ) (p : ℕ) : ℂ :=
  c p / (Real.log p : ℂ)

/-- Every degree-one Euler coefficient stream satisfies the support and geometric-ray classifier. -/
theorem degreeOneEulerRayCompatible_degreeOneEulerFluxCoeff (a : ℕ → ℂ) :
    DegreeOneEulerRayCompatible (degreeOneEulerFluxCoeff a) := by
  constructor
  · intro n hn
    exact degreeOneEulerFluxCoeff_eq_zero_of_not_isPrimePow a hn
  · intro p m hp hm
    rw [degreeOneEulerFluxCoeff_prime_pow a hp hm,
      degreeOneEulerFluxCoeff_prime a hp]
    have hlog : (Real.log p : ℂ) ≠ 0 := by
      exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    rw [mul_div_cancel_left₀ _ hlog]

/-- The support and geometric-ray conditions reconstruct the complete coefficient stream. -/
theorem degreeOneEulerFluxCoeff_parameterOfCoeff_eq {c : ℕ → ℂ}
    (hc : DegreeOneEulerRayCompatible c) :
    degreeOneEulerFluxCoeff (degreeOneEulerParameterOfCoeff c) = c := by
  funext n
  by_cases hn : IsPrimePow n
  · rcases hn with ⟨p, m, hp, hm, rfl⟩
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    rw [degreeOneEulerFluxCoeff_prime_pow _ hp' (Nat.ne_of_gt hm)]
    exact (hc.2 p m hp' (Nat.ne_of_gt hm)).symm
  · rw [degreeOneEulerFluxCoeff_eq_zero_of_not_isPrimePow _ hn, hc.1 n hn]

/-- Coefficient-level source-image theorem, before quotienting out irrelevant nonprime parameter
labels. -/
theorem degreeOneEulerRayCompatible_iff_exists_parameter (c : ℕ → ℂ) :
    DegreeOneEulerRayCompatible c ↔
      ∃ a : ℕ → ℂ, degreeOneEulerFluxCoeff a = c := by
  constructor
  · intro hc
    exact ⟨degreeOneEulerParameterOfCoeff c,
      degreeOneEulerFluxCoeff_parameterOfCoeff_eq hc⟩
  · rintro ⟨a, rfl⟩
    exact degreeOneEulerRayCompatible_degreeOneEulerFluxCoeff a

/-- Two integer-indexed Euler parameter fields give the same coefficient stream whenever they
agree at every prime; values at nonprime labels are irrelevant. -/
theorem degreeOneEulerFluxCoeff_eq_of_eq_on_primes
    {a b : ℕ → ℂ} (h : ∀ p : ℕ, p.Prime → a p = b p) :
    degreeOneEulerFluxCoeff a = degreeOneEulerFluxCoeff b := by
  funext n
  by_cases hn : IsPrimePow n
  · rcases hn with ⟨p, m, hp, hm, rfl⟩
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    rw [degreeOneEulerFluxCoeff_prime_pow a hp' (Nat.ne_of_gt hm),
      degreeOneEulerFluxCoeff_prime_pow b hp' (Nat.ne_of_gt hm), h p hp']
  · rw [degreeOneEulerFluxCoeff_eq_zero_of_not_isPrimePow a hn,
      degreeOneEulerFluxCoeff_eq_zero_of_not_isPrimePow b hn]

/-- The exact coefficient map on genuinely prime-indexed parameter fields. -/
def degreeOneEulerPrimeFluxCoeff (a : Nat.Primes → ℂ) : ℕ → ℂ :=
  degreeOneEulerFluxCoeff (fun n ↦ if hn : n.Prime then a ⟨n, hn⟩ else 0)

/-- The unique prime-indexed parameter recovered from a compatible coefficient stream. -/
def degreeOneEulerPrimeParameterOfCoeff (c : ℕ → ℂ) (p : Nat.Primes) : ℂ :=
  c p / (Real.log (p : ℕ) : ℂ)

@[simp]
theorem degreeOneEulerPrimeFluxCoeff_prime
    (a : Nat.Primes → ℂ) (p : Nat.Primes) :
    degreeOneEulerPrimeFluxCoeff a p =
      (Real.log (p : ℕ) : ℂ) * a p := by
  rw [degreeOneEulerPrimeFluxCoeff,
    degreeOneEulerFluxCoeff_prime _ p.property]
  simp only [dif_pos p.property]
  congr 1

/-- Prime-indexing removes the irrelevant nonprime kernel of the coefficient map. -/
theorem degreeOneEulerPrimeFluxCoeff_injective :
    Function.Injective degreeOneEulerPrimeFluxCoeff := by
  intro a b hab
  funext p
  have hp := congrFun hab (p : ℕ)
  rw [degreeOneEulerPrimeFluxCoeff_prime,
    degreeOneEulerPrimeFluxCoeff_prime] at hp
  exact mul_left_cancel₀
    (by exact_mod_cast (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne') hp

/-- Every prime-indexed parameter field lands in the ray-compatible coefficient locus. -/
theorem degreeOneEulerRayCompatible_primeFluxCoeff (a : Nat.Primes → ℂ) :
    DegreeOneEulerRayCompatible (degreeOneEulerPrimeFluxCoeff a) :=
  degreeOneEulerRayCompatible_degreeOneEulerFluxCoeff _

/-- The recovered prime-indexed parameter reconstructs every compatible coefficient stream. -/
theorem degreeOneEulerPrimeFluxCoeff_parameterOfCoeff_eq {c : ℕ → ℂ}
    (hc : DegreeOneEulerRayCompatible c) :
    degreeOneEulerPrimeFluxCoeff (degreeOneEulerPrimeParameterOfCoeff c) = c := by
  funext n
  by_cases hn : IsPrimePow n
  · rcases hn with ⟨p, m, hp, hm, rfl⟩
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    rw [degreeOneEulerPrimeFluxCoeff,
      degreeOneEulerFluxCoeff_prime_pow _ hp' (Nat.ne_of_gt hm)]
    simp only [dif_pos hp', degreeOneEulerPrimeParameterOfCoeff]
    exact (hc.2 p m hp' (Nat.ne_of_gt hm)).symm
  · rw [degreeOneEulerPrimeFluxCoeff,
      degreeOneEulerFluxCoeff_eq_zero_of_not_isPrimePow _ hn, hc.1 n hn]

/-- **Exact degree-one Euler coefficient-image classification.**  A stream is supported on prime
powers with geometric normalized rays if and only if it has a unique prime-indexed Euler parameter
field. -/
theorem degreeOneEulerRayCompatible_iff_existsUnique_primeParameter (c : ℕ → ℂ) :
    DegreeOneEulerRayCompatible c ↔
      ∃! a : Nat.Primes → ℂ, degreeOneEulerPrimeFluxCoeff a = c := by
  constructor
  · intro hc
    refine ⟨degreeOneEulerPrimeParameterOfCoeff c,
      degreeOneEulerPrimeFluxCoeff_parameterOfCoeff_eq hc, ?_⟩
    intro b hb
    exact degreeOneEulerPrimeFluxCoeff_injective
      (hb.trans (degreeOneEulerPrimeFluxCoeff_parameterOfCoeff_eq hc).symm)
  · rintro ⟨a, ha, _⟩
    rw [← ha]
    exact degreeOneEulerRayCompatible_primeFluxCoeff a

/-- The polynomial form of the all-order Euler image: support is restricted to prime powers and,
after adjoining normalized exponent zero with value `1`, every prime ray has vanishing `2 x 2`
Hankel minors. -/
def DegreeOneEulerQuadraticCompatible (c : ℕ → ℂ) : Prop :=
  (∀ n : ℕ, ¬ IsPrimePow n → c n = 0) ∧
    ∀ (p m n : ℕ), p.Prime → m ≠ 0 → n ≠ 0 →
      c (p ^ m) * c (p ^ n) =
        (Real.log p : ℂ) * c (p ^ (m + n))

/-- Geometric Euler rays satisfy every quadratic rank-one identity. -/
theorem degreeOneEulerQuadraticCompatible_of_rayCompatible {c : ℕ → ℂ}
    (hc : DegreeOneEulerRayCompatible c) :
    DegreeOneEulerQuadraticCompatible c := by
  rw [degreeOneEulerRayCompatible_iff_exists_parameter] at hc
  obtain ⟨a, rfl⟩ := hc
  exact ⟨degreeOneEulerRayCompatible_degreeOneEulerFluxCoeff a |>.1,
    fun p m n hp hm hn ↦ degreeOneEulerFluxCoeff_prime_ray_mul a hp hm hn⟩

/-- The quadratic identities recursively reconstruct the whole normalized ray from exponent one. -/
theorem degreeOneEulerQuadraticCompatible_prime_ray {c : ℕ → ℂ}
    (hc : DegreeOneEulerQuadraticCompatible c)
    (p : ℕ) (hp : p.Prime) :
    ∀ m : ℕ, m ≠ 0 →
      c (p ^ m) = (Real.log p : ℂ) *
        (c p / (Real.log p : ℂ)) ^ m := by
  have hlog : (Real.log p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  intro m
  induction m with
  | zero =>
      intro hm
      exact (hm rfl).elim
  | succ m ih =>
      intro _
      by_cases hm : m = 0
      · subst m
        simp only [zero_add, pow_one]
        field_simp
      · have hrec := hc.2 p 1 m hp one_ne_zero hm
        rw [pow_one, ih hm] at hrec
        have hpow : (c p / (Real.log p : ℂ)) ^ (m + 1) =
            (c p / (Real.log p : ℂ)) ^ m *
              (c p / (Real.log p : ℂ)) := by rw [pow_succ]
        rw [hpow]
        apply mul_left_cancel₀ hlog
        calc
          (Real.log p : ℂ) * c (p ^ (m + 1)) =
              (Real.log p : ℂ) * c (p ^ (1 + m)) := by rw [Nat.add_comm]
          _ = c p * ((Real.log p : ℂ) *
                (c p / (Real.log p : ℂ)) ^ m) := hrec.symm
          _ = (Real.log p : ℂ) *
              ((Real.log p : ℂ) *
                ((c p / (Real.log p : ℂ)) ^ m *
                  (c p / (Real.log p : ℂ)))) := by field_simp

/-- Quadratic rank-one identities and the explicit geometric-ray classifier are equivalent. -/
theorem degreeOneEulerQuadraticCompatible_iff_rayCompatible (c : ℕ → ℂ) :
    DegreeOneEulerQuadraticCompatible c ↔ DegreeOneEulerRayCompatible c := by
  constructor
  · intro hc
    exact ⟨hc.1, fun p m hp hm ↦
      degreeOneEulerQuadraticCompatible_prime_ray hc p hp m hm⟩
  · exact degreeOneEulerQuadraticCompatible_of_rayCompatible

/-- **Quadratic source-image classification.**  The all-order prime-power Hankel-minor equations
cut out exactly the coefficient image of a unique prime-indexed degree-one Euler parameter field. -/
theorem degreeOneEulerQuadraticCompatible_iff_existsUnique_primeParameter (c : ℕ → ℂ) :
    DegreeOneEulerQuadraticCompatible c ↔
      ∃! a : Nat.Primes → ℂ, degreeOneEulerPrimeFluxCoeff a = c := by
  rw [degreeOneEulerQuadraticCompatible_iff_rayCompatible,
    degreeOneEulerRayCompatible_iff_existsUnique_primeParameter]

/-- The actual von Mangoldt source lies in the all-order quadratic coefficient image. -/
theorem vonMangoldt_degreeOneEulerQuadraticCompatible :
    DegreeOneEulerQuadraticCompatible
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) := by
  apply degreeOneEulerQuadraticCompatible_of_rayCompatible
  rw [← funext degreeOneEulerFluxCoeff_one_eq_vonMangoldt]
  exact degreeOneEulerRayCompatible_degreeOneEulerFluxCoeff (fun _ ↦ 1)

/-- **The zeta source is the unit point of the classified prime parameter space.**  The
complexified von Mangoldt stream has one and only one genuinely prime-indexed degree-one Euler
parameter field. -/
theorem vonMangoldt_existsUnique_degreeOneEulerPrimeParameter :
    ∃! a : Nat.Primes → ℂ,
      degreeOneEulerPrimeFluxCoeff a =
        fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) :=
  (degreeOneEulerQuadraticCompatible_iff_existsUnique_primeParameter _).mp
    vonMangoldt_degreeOneEulerQuadraticCompatible

/-- The uniquely recovered zeta parameter equals `1` at every prime. -/
theorem vonMangoldt_primeParameter_eq_one (p : Nat.Primes) :
    degreeOneEulerPrimeParameterOfCoeff
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) p = 1 := by
  rw [degreeOneEulerPrimeParameterOfCoeff,
    ArithmeticFunction.vonMangoldt_apply_prime p.property]
  have hlog : (Real.log (p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  exact div_self hlog

end RHTower
