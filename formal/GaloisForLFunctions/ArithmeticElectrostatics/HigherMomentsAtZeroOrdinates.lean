import GaloisForLFunctions.ArithmeticElectrostatics.LargeValuesAtZeroOrdinates

/-!
# Higher moments of prime polynomials at zero ordinates

The large-values law at zero ordinates (`LargeValuesAtZeroOrdinates`) bounds how often a Dirichlet
polynomial is large at the zeros by its coefficient mass. Applied to a power `F^k` of a prime
polynomial `F(t) = Σ_{p ∈ P} c_p p^{it}` — itself a Dirichlet polynomial, of length `X^k` — it bounds
the `2k`-th moment, and the number of aligned zero ordinates falls by the factor `V^{−2k}`.

* **Powers are Dirichlet polynomials** (`expSum_pow`): `F(t)^k = Σ_{n ≤ X^k} a^{⋆k}(n) n^{it}` for the
  Dirichlet convolution power of the prime-supported coefficient function `a`.
* **The mass of a convolution power** (`sum_normSq_pow_le`): `Σ_n |a^{⋆k}(n)|² ≤ k! (Σ_p |c_p|²)^k`. A
  number `n` with `a^{⋆(k+1)}(n) ≠ 0` has exactly `k + 1` prime factors with multiplicity, so at most
  `k + 1` prime divisors: Cauchy–Schwarz over them costs `k + 1` at each step.
* **Higher-moment large values** (`exists_card_largeValues_pow_le`): the zero copies with ordinates
  in `(A, A + R]` at which `|F(γ)| ≥ V` number at most
  `K log(A + R + 1)(R + 8X^k(1 + log X^k))(2 + log² X^k) k! (Σ|c_p|²)^k / V^{2k}`.

For the detector `c_p = w_p log p/√p` with `X = (log T)^C`, the mass is `O(log² X)`, and the choice
`k ≍ log T/(C log log T)` (so that `X^k ≤ T`) makes the ratio `k!(Σ|c_p|²)^k/V^{2k}` at `V ≍ log T` a
negative power of `T`: aligned zero ordinates are power-sparse, the input the report's Q1 asks to
compare with zero density.
-/

noncomputable section

open Finset ArithmeticFunction RHTower.Sieve

namespace GaloisForLFunctions.ArithmeticElectrostatics

/-- The **prime-supported coefficient function**: `c_p` on the primes of `P`, `0` elsewhere. -/
def primeSupported (P : Finset ℕ) (c : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Prime ∧ n ∈ P then c n else 0, by simp [Nat.not_prime_zero]⟩

theorem primeSupported_apply (P : Finset ℕ) (c : ℕ → ℂ) (n : ℕ) :
    primeSupported P c n = if n.Prime ∧ n ∈ P then c n else 0 := rfl

/-- The phase `n ↦ n^{it}` as an arithmetic function (`0` at `0`). -/
def phase (t : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I), by simp⟩

theorem phase_mul (t : ℝ) (m n : ℕ) : phase t (m * n) = phase t m * phase t n := by
  simp only [phase, ArithmeticFunction.coe_mk]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [if_neg (Nat.mul_pos hm hn).ne', if_neg hm.ne', if_neg hn.ne', ← Complex.exp_add,
    Nat.cast_mul, Real.log_mul (by exact_mod_cast hm.ne') (by exact_mod_cast hn.ne')]
  congr 1
  push_cast
  ring

/-- Twisting by a completely multiplicative function commutes with Dirichlet convolution. -/
theorem pmul_mul_pmul_complex {ω f g : ArithmeticFunction ℂ} (hω : ∀ a b, ω (a * b) = ω a * ω b) :
    (f.pmul ω) * (g.pmul ω) = (f * g).pmul ω := by
  ext n
  simp only [mul_apply, pmul_apply, sum_mul]
  refine sum_congr rfl fun x hx => ?_
  rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, hω]
  ring

/-- The exponential sum `Σ_{1 ≤ n ≤ M} f(n) n^{it}`. -/
def expSum (f : ArithmeticFunction ℂ) (M : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 M, f n * phase t n

/-- The exponential sum is the Dirichlet polynomial with coefficients `f(m + 1)`. -/
theorem expSum_eq_dirPoly (f : ArithmeticFunction ℂ) (M : ℕ) (t : ℝ) :
    expSum f M t = dirPoly M (fun m => f ((m : ℕ) + 1)) t := by
  rw [expSum, dirPoly, Fin.sum_univ_eq_sum_range (fun m => f (m + 1) *
    Complex.exp (((t * Real.log ((m : ℕ) + 1) : ℝ) : ℂ) * Complex.I)) M, Finset.range_eq_Ico]
  have hterm : ∀ i ∈ Ico 0 M, f (i + 1) * Complex.exp (((t * Real.log ((i : ℕ) + 1) : ℝ) : ℂ) *
      Complex.I) = (fun n => f n * phase t n) (i + 1) := by
    intro i _
    simp only [phase, ArithmeticFunction.coe_mk, if_neg (Nat.succ_ne_zero i)]
    push_cast
    rfl
  rw [sum_congr rfl hterm, Finset.sum_Ico_add' (fun n => f n * phase t n) 0 M 1]
  rfl

theorem Icc_one_eq_Ioc (M : ℕ) : Icc 1 M = Ioc 0 M := rfl

/-- `n` in the support of `a^{⋆k}` has exactly `k` prime factors with multiplicity and is at most
`X^k`. -/
theorem support_pow_primeSupported {P : Finset ℕ} {c : ℕ → ℂ} {X : ℕ}
    (hP : ∀ p ∈ P, p ≤ X) (k : ℕ) {n : ℕ} (hn : (primeSupported P c ^ k) n ≠ 0) :
    n ≠ 0 ∧ cardFactors n = k ∧ n ≤ X ^ k := by
  induction k generalizing n with
  | zero =>
    rw [pow_zero] at hn
    have h1 : n = 1 := by
      by_contra h; exact hn (by rw [one_apply_ne h])
    subst h1
    simp
  | succ k ih =>
    rw [pow_succ', mul_apply] at hn
    obtain ⟨x, hx, hne⟩ := exists_ne_zero_of_sum_ne_zero hn
    have ha : primeSupported P c x.1 ≠ 0 := left_ne_zero_of_mul hne
    have hb : (primeSupported P c ^ k) x.2 ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    rw [primeSupported_apply] at ha
    have hp : x.1.Prime ∧ x.1 ∈ P := by
      by_contra h; exact ha (if_neg h)
    obtain ⟨hx20, hx2Ω, hx2X⟩ := ih hb
    refine ⟨hn0, ?_, ?_⟩
    · rw [← hprod, cardFactors_mul hp.1.ne_zero hx20, cardFactors_apply_prime hp.1, hx2Ω]
      ring
    · rw [← hprod, pow_succ']
      exact Nat.mul_le_mul (hP _ hp.2) hx2X

/-- Prime divisors are at most the prime factors with multiplicity. -/
theorem card_primeFactors_le_cardFactors (n : ℕ) : n.primeFactors.card ≤ cardFactors n := by
  rw [cardFactors_apply, Nat.primeFactors]
  exact List.toFinset_card_le _

/-- One convolution step: `|(a ⋆ b)(n)|² ≤ (k + 1) Σ_{d ∣ n} |a(d)|² |b(n/d)|²`. -/
theorem normSq_mul_apply_le {P : Finset ℕ} {c : ℕ → ℂ} {X : ℕ} (hP : ∀ p ∈ P, p ≤ X) (k n : ℕ) :
    ‖(primeSupported P c * primeSupported P c ^ k) n‖ ^ 2 ≤
      (k + 1) * ∑ d ∈ n.divisors,
        ‖primeSupported P c d‖ ^ 2 * ‖(primeSupported P c ^ k) (n / d)‖ ^ 2 := by
  set a := primeSupported P c
  set b := primeSupported P c ^ k
  by_cases hz : (a * b) n = 0
  · rw [hz, norm_zero]
    have : 0 ≤ ∑ d ∈ n.divisors, ‖a d‖ ^ 2 * ‖b (n / d)‖ ^ 2 :=
      sum_nonneg fun d _ => by positivity
    nlinarith
  -- the support of `a ⋆ b` has `k + 1` prime factors
  have hsupp := support_pow_primeSupported hP (k + 1) (n := n) (by rwa [pow_succ'])
  -- only prime divisors contribute
  have hsum : (a * b) n = ∑ d ∈ n.primeFactors, a d * b (n / d) := by
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => a x * b y)]
    refine (sum_subset (fun d hd => Nat.mem_divisors.mpr
      ⟨Nat.dvd_of_mem_primeFactors hd, hsupp.1⟩) fun d _ hd => ?_).symm
    have : a d = 0 := by
      rw [primeSupported_apply, if_neg]
      rintro ⟨hdp, -⟩
      exact hd (Nat.mem_primeFactors.mpr ⟨hdp, Nat.dvd_of_mem_divisors ‹_›, hsupp.1⟩)
    rw [this, zero_mul]
  have hcard : (n.primeFactors.card : ℝ) ≤ k + 1 := by
    have := card_primeFactors_le_cardFactors n
    rw [hsupp.2.1] at this
    exact_mod_cast this
  calc ‖(a * b) n‖ ^ 2 ≤ (∑ d ∈ n.primeFactors, ‖a d‖ * ‖b (n / d)‖) ^ 2 := by
        rw [hsum]
        refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans ?_) 2
        exact le_of_eq (sum_congr rfl fun d _ => norm_mul _ _)
    _ ≤ (n.primeFactors.card : ℝ) * ∑ d ∈ n.primeFactors, (‖a d‖ * ‖b (n / d)‖) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ (k + 1) * ∑ d ∈ n.divisors, ‖a d‖ ^ 2 * ‖b (n / d)‖ ^ 2 := by
        refine mul_le_mul hcard ?_ (sum_nonneg fun d _ => by positivity) (by positivity)
        refine (sum_le_sum fun d _ => le_of_eq (mul_pow _ _ 2)).trans ?_
        exact sum_le_sum_of_subset_of_nonneg (fun d hd => Nat.mem_divisors.mpr
          ⟨Nat.dvd_of_mem_primeFactors hd, hsupp.1⟩) fun d _ _ => by positivity

/-- **The mass of a convolution power**: `Σ_{n ≤ N} |a^{⋆k}(n)|² ≤ k! (Σ_{n ≤ N} |a(n)|²)^k`. -/
theorem sum_normSq_pow_le {P : Finset ℕ} {c : ℕ → ℂ} {X : ℕ} (hP : ∀ p ∈ P, p ≤ X) (k N : ℕ) :
    ∑ n ∈ Ioc 0 N, ‖(primeSupported P c ^ k) n‖ ^ 2 ≤
      k.factorial * (∑ n ∈ Ioc 0 N, ‖primeSupported P c n‖ ^ 2) ^ k := by
  set a := primeSupported P c
  set S := ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2
  have hS : 0 ≤ S := sum_nonneg fun _ _ => by positivity
  induction k with
  | zero =>
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
    have hone : ∀ n, ‖(1 : ArithmeticFunction ℂ) n‖ ^ 2 = if n = 1 then 1 else 0 := by
      intro n
      by_cases h : n = 1
      · subst h; simp
      · rw [one_apply_ne h, if_neg h]; simp
    rw [sum_congr rfl fun n _ => hone n, sum_ite_eq']
    split_ifs <;> norm_num
  | succ k ih =>
    -- the convolution of the squared moduli
    set A : ArithmeticFunction ℝ := ⟨fun n => ‖a n‖ ^ 2, by simp⟩
    set B : ArithmeticFunction ℝ := ⟨fun n => ‖(a ^ k) n‖ ^ 2, by simp⟩
    have hA0 : ∀ n, 0 ≤ A n := fun n => show (0 : ℝ) ≤ ‖a n‖ ^ 2 from sq_nonneg _
    have hB0 : ∀ n, 0 ≤ B n := fun n => show (0 : ℝ) ≤ ‖(a ^ k) n‖ ^ 2 from sq_nonneg _
    have hAB : ∀ n, (A * B) n =
        ∑ d ∈ n.divisors, ‖a d‖ ^ 2 * ‖(a ^ k) (n / d)‖ ^ 2 := by
      intro n
      rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => A x * B y)]
      rfl
    have hstep : ∀ n, ‖(a ^ (k + 1)) n‖ ^ 2 ≤ (k + 1) * (A * B) n := by
      intro n
      rw [pow_succ' a k, hAB]
      exact normSq_mul_apply_le hP k n
    have hconv : ∑ n ∈ Ioc 0 N, (A * B) n ≤ S * ∑ n ∈ Ioc 0 N, B n := by
      rw [sum_Ioc_mul_eq_sum_sum, sum_mul]
      refine sum_le_sum fun n hn => ?_
      refine (mul_le_mul_of_nonneg_left ?_ (hA0 n)).trans (le_of_eq rfl)
      exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right (Nat.div_le_self N n))
        fun m _ _ => hB0 m
    have hB : ∑ n ∈ Ioc 0 N, B n ≤ k.factorial * S ^ k := ih
    calc ∑ n ∈ Ioc 0 N, ‖(a ^ (k + 1)) n‖ ^ 2
        ≤ ∑ n ∈ Ioc 0 N, (k + 1) * (A * B) n := sum_le_sum fun n _ => hstep n
      _ = (k + 1) * ∑ n ∈ Ioc 0 N, (A * B) n := by rw [mul_sum]
      _ ≤ (k + 1) * (S * (k.factorial * S ^ k)) := by
          gcongr
          exact hconv.trans (mul_le_mul_of_nonneg_left hB hS)
      _ = (k + 1).factorial * S ^ (k + 1) := by
          rw [Nat.factorial_succ]; push_cast; ring

/-- **Powers are Dirichlet polynomials**: `F(t)^k = Σ_{n ≤ X^k} a^{⋆k}(n) n^{it}`. -/
theorem expSum_pow {P : Finset ℕ} {c : ℕ → ℂ} {X : ℕ} (hX : 1 ≤ X) (hP : ∀ p ∈ P, p ≤ X)
    (k : ℕ) (t : ℝ) :
    expSum (primeSupported P c) X t ^ k = expSum (primeSupported P c ^ k) (X ^ k) t := by
  set a := primeSupported P c
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero, expSum, Icc_self, sum_singleton]
    simp [phase]
  | succ k ih =>
    rw [pow_succ', ih]
    set E := expSum (a ^ k) (X ^ k) t
    have hmul := pmul_mul_pmul_complex (ω := phase t) (f := a) (g := a ^ k) (phase_mul t)
    have hXX : X ≤ X ^ (k + 1) :=
      calc X = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    -- for `n ≤ X` the inner range covers the support of `a^{⋆k}`
    have hinner : ∀ n ∈ Ioc 0 X,
        ∑ m ∈ Ioc 0 (X ^ (k + 1) / n), ((a ^ k).pmul (phase t)) m = E := by
      intro n hn
      have hn0 : 0 < n := (mem_Ioc.mp hn).1
      have hcov : X ^ k ≤ X ^ (k + 1) / n := by
        rw [Nat.le_div_iff_mul_le hn0, pow_succ]
        exact Nat.mul_le_mul_left _ (mem_Ioc.mp hn).2
      rw [show E = ∑ m ∈ Ioc 0 (X ^ k), ((a ^ k).pmul (phase t)) m by
        rw [expSum, Icc_one_eq_Ioc]; exact sum_congr rfl fun m _ => (pmul_apply _ _ _).symm]
      symm
      refine sum_subset (Ioc_subset_Ioc_right hcov) fun m hm hmk => ?_
      rw [pmul_apply]
      by_contra hne
      have hb : (a ^ k) m ≠ 0 := left_ne_zero_of_mul hne
      exact hmk (mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1, (support_pow_primeSupported hP k hb).2.2⟩)
    -- outside `n ≤ X` the outer coefficient vanishes
    have hout : ∀ n ∈ Ioc 0 (X ^ (k + 1)), n ∉ Ioc 0 X →
        (a.pmul (phase t)) n * ∑ m ∈ Ioc 0 (X ^ (k + 1) / n), ((a ^ k).pmul (phase t)) m = 0 := by
      intro n hn hnX
      have : a n = 0 := by
        rw [primeSupported_apply, if_neg]
        rintro ⟨-, hnP⟩
        exact hnX (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, hP n hnP⟩)
      rw [pmul_apply, this, zero_mul, zero_mul]
    symm
    calc expSum (a ^ (k + 1)) (X ^ (k + 1)) t
        = ∑ n ∈ Ioc 0 (X ^ (k + 1)), ((a.pmul (phase t)) * ((a ^ k).pmul (phase t))) n := by
          rw [expSum, Icc_one_eq_Ioc, hmul, pow_succ' a k]
          exact sum_congr rfl fun n _ => (pmul_apply _ _ _).symm
      _ = ∑ n ∈ Ioc 0 (X ^ (k + 1)), (a.pmul (phase t)) n *
            ∑ m ∈ Ioc 0 (X ^ (k + 1) / n), ((a ^ k).pmul (phase t)) m :=
          sum_Ioc_mul_eq_sum_sum _ _ _
      _ = ∑ n ∈ Ioc 0 X, (a.pmul (phase t)) n *
            ∑ m ∈ Ioc 0 (X ^ (k + 1) / n), ((a ^ k).pmul (phase t)) m :=
          (sum_subset (Ioc_subset_Ioc_right hXX) hout).symm
      _ = ∑ n ∈ Ioc 0 X, (a.pmul (phase t)) n * E :=
          sum_congr rfl fun n hn => by rw [hinner n hn]
      _ = expSum a X t * E := by
          rw [← sum_mul, expSum, Icc_one_eq_Ioc]
          exact congrArg (· * E) (sum_congr rfl fun n _ => pmul_apply _ _ _)

/-- **Higher-moment large values at zero ordinates.** -/
theorem exists_card_largeValues_pow_le :
    ∃ K T₀ : ℝ, 0 < K ∧ 4 ≤ T₀ ∧ ∀ A : ℝ, T₀ ≤ A → ∀ R : ℕ, ∀ G : Finset RHTower.XiZeroCopy,
      (∀ q ∈ G, A < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ A + R) →
      ∀ (X : ℕ), 1 ≤ X → ∀ (P : Finset ℕ), (∀ p ∈ P, p ≤ X) → ∀ (c : ℕ → ℂ) (k : ℕ) (V : ℝ),
      0 ≤ V →
      ((G.filter fun q => V ≤ ‖expSum (primeSupported P c) X (q.1 : ℂ).im‖).card : ℝ) *
          (V ^ k) ^ 2 ≤
        K * Real.log (A + R + 1) * ((R + 8 * (X ^ k : ℕ) * (1 + Real.log (X ^ k : ℕ))) *
          ((2 + Real.log (X ^ k : ℕ) ^ 2) *
            (k.factorial * (∑ n ∈ Ioc 0 X, ‖primeSupported P c n‖ ^ 2) ^ k))) := by
  obtain ⟨K, T₀, hK, hT₀, h⟩ := exists_card_largeValues_le
  refine ⟨K, T₀, hK, hT₀, fun A hA R G hG X hX P hP c k V hV => ?_⟩
  set a := primeSupported P c
  set b : Fin (X ^ k) → ℂ := fun m => (a ^ k) ((m : ℕ) + 1)
  have hpow : ∀ t : ℝ, expSum a X t ^ k = dirPoly (X ^ k) b t := fun t => by
    rw [expSum_pow hX hP k t, expSum_eq_dirPoly]
  -- the coefficient mass of the power
  have hmass : coeffMass b ≤ k.factorial * (∑ n ∈ Ioc 0 X, ‖a n‖ ^ 2) ^ k := by
    have hreindex : coeffMass b = ∑ n ∈ Ioc 0 (X ^ k), ‖(a ^ k) n‖ ^ 2 := by
      rw [coeffMass, Fin.sum_univ_eq_sum_range (fun m => ‖(a ^ k) (m + 1)‖ ^ 2) (X ^ k),
        Finset.range_eq_Ico, ← Icc_one_eq_Ioc,
        Finset.sum_Ico_add' (fun n => ‖(a ^ k) n‖ ^ 2) 0 (X ^ k) 1]
      rfl
    have hXk : 1 ≤ X ^ k := Nat.one_le_pow _ _ (by omega)
    have hkN : X ^ k ≤ X ^ k * X := Nat.le_mul_of_pos_right _ (by omega)
    have hXN : X ≤ X ^ k * X := Nat.le_mul_of_pos_left _ hXk
    have h1 : ∑ n ∈ Ioc 0 (X ^ k), ‖(a ^ k) n‖ ^ 2 ≤ ∑ n ∈ Ioc 0 (X ^ k * X), ‖(a ^ k) n‖ ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hkN) fun _ _ _ => by positivity
    have h2 := sum_normSq_pow_le (c := c) hP k (X ^ k * X)
    have h3 : ∑ n ∈ Ioc 0 (X ^ k * X), ‖a n‖ ^ 2 = ∑ n ∈ Ioc 0 X, ‖a n‖ ^ 2 := by
      symm
      refine sum_subset (Ioc_subset_Ioc_right hXN) fun n hn hn' => ?_
      have : a n = 0 := by
        rw [primeSupported_apply, if_neg]
        rintro ⟨-, hnP⟩
        exact hn' (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, hP n hnP⟩)
      rw [this, norm_zero]; ring
    rw [hreindex]
    rw [h3] at h2
    exact h1.trans h2
  -- a large value of `F` is a large value of `F^k`
  have hsub : G.filter (fun q => V ≤ ‖expSum a X (q.1 : ℂ).im‖) ⊆
      G.filter (fun q => V ^ k ≤ ‖dirPoly (X ^ k) b (q.1 : ℂ).im‖) := by
    intro q hq
    rw [mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    rw [← hpow, norm_pow]
    exact pow_le_pow_left₀ hV hq.2 k
  have hcard := card_le_card hsub
  have hmain := h A hA R G hG (X ^ k) b (V ^ k) (pow_nonneg hV k)
  have hlog : 0 ≤ Real.log (A + R + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith)
  have hR : 0 ≤ (R : ℝ) + 8 * ((X ^ k : ℕ) : ℝ) * (1 + Real.log ((X ^ k : ℕ) : ℝ)) := by
    have := Real.log_natCast_nonneg (X ^ k)
    positivity
  have h2 : 0 ≤ 2 + Real.log ((X ^ k : ℕ) : ℝ) ^ 2 := by positivity
  calc ((G.filter fun q => V ≤ ‖expSum a X (q.1 : ℂ).im‖).card : ℝ) * (V ^ k) ^ 2
      ≤ ((G.filter fun q => V ^ k ≤ ‖dirPoly (X ^ k) b (q.1 : ℂ).im‖).card : ℝ) * (V ^ k) ^ 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
    _ ≤ _ := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass h2) hR) (mul_nonneg hK.le hlog)

end GaloisForLFunctions.ArithmeticElectrostatics
