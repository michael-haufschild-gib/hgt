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
* **The saving of order `k`** (`exists_card_largeValues_le_theta_pow`): if `X^k ≤ R` and
  `k Σ|c_p|² ≤ θ V²`, the count is `O(log(A + R) R log³ R · θ^k)`, since `k! ≤ k^k`.
* **Power saving for the prime detector** (`sum_normSq_detector_le`,
  `exists_card_aligned_power_saving`): for `c_p = w_p log p/√p`, `|w_p| ≤ 1`, the mass is at most
  `log X (log X + log 4 + 4)`; with `k = ⌊log R/log X⌋` and `log R (log X + 7) ≤ θ V²` the count is
  `O(log(A + R) R log³ R · θ^{−1} R^{log θ/log X})`.

At `V = η log T`, `X = (log T)^C`, `R ≍ T` one may take `θ ≍ log log T/(η² log T)`: the aligned zero
ordinates number `T^{1 − 1/C + o(1)}`, a power saving against the `≍ T log T` zeros of the window.
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
    set E := expSum (a ^ k) (X ^ k) t with hEdef
    have hE : E = ∑ m ∈ Ioc 0 (X ^ k), ((a ^ k).pmul (phase t)) m := by
      rw [hEdef, expSum, Icc_one_eq_Ioc]
      exact sum_congr rfl fun m _ => pmul_apply.symm
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
      rw [hE]
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
          exact sum_congr rfl fun n _ => pmul_apply.symm
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
          exact congrArg (· * E) (sum_congr rfl fun n _ => pmul_apply)

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

/-- Reindexing `Σ_{0 < n ≤ X} f(n) = Σ_{m < X} f(m + 1)`. -/
theorem sum_Ioc_eq_sum_fin (f : ℕ → ℝ) (X : ℕ) :
    ∑ n ∈ Ioc 0 X, f n = ∑ m : Fin X, f ((m : ℕ) + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun m => f (m + 1)) X, Finset.range_eq_Ico, ← Icc_one_eq_Ioc,
    Finset.sum_Ico_add' f 0 X 1]
  rfl

/-- The **prime detector** `c_p = w_p log p/√p`. -/
def detector (w : ℕ → ℂ) : ℕ → ℂ := fun n => w n * ((Real.log n / Real.sqrt n : ℝ) : ℂ)

/-- **The detector's mass**: `Σ_{p ∈ P, p ≤ X} |w_p|² log² p/p ≤ log X (log X + log 4 + 4)`. -/
theorem sum_normSq_detector_le (P : Finset ℕ) {X : ℕ} (hX : 1 ≤ X) {w : ℕ → ℂ}
    (hw : ∀ n, ‖w n‖ ≤ 1) :
    ∑ n ∈ Ioc 0 X, ‖primeSupported P (detector w) n‖ ^ 2 ≤
      Real.log X * (Real.log X + (Real.log 4 + 4)) := by
  -- the detector is the prime polynomial with the weights `w` cut to the primes of `P`
  set w' : Fin X → ℂ := fun m =>
    if ((m : ℕ) + 1).Prime ∧ (m : ℕ) + 1 ∈ P then w ((m : ℕ) + 1) else 0
  have hw' : ∀ m, ‖w' m‖ ≤ 1 := fun m => by
    simp only [w']
    split_ifs
    · exact hw _
    · simp
  refine le_of_eq_of_le ?_ (coeffMass_primeCoeff_le hX w' hw')
  rw [sum_Ioc_eq_sum_fin (fun n => ‖primeSupported P (detector w) n‖ ^ 2), coeffMass]
  refine sum_congr rfl fun m _ => ?_
  simp only [primeSupported_apply, primeCoeff, w', detector]
  split_ifs with h
  · rw [ArithmeticFunction.vonMangoldt_apply_prime h.1]
    push_cast
    rfl
  · simp

/-- **Aligned zero ordinates are power-sparse.** If `X^k ≤ R` and `k S ≤ θ V²` for the coefficient
mass `S`, the zero copies in `(A, A + R]` with `|F(γ)| ≥ V` number at most
`K log(A + R + 1) R (1 + log R)(2 + log² R) θ^k`: the moment of order `2k` saves `θ^k`. -/
theorem exists_card_largeValues_le_theta_pow :
    ∃ K T₀ : ℝ, 0 < K ∧ 4 ≤ T₀ ∧ ∀ A : ℝ, T₀ ≤ A → ∀ R : ℕ, ∀ G : Finset RHTower.XiZeroCopy,
      (∀ q ∈ G, A < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ A + R) →
      ∀ (X : ℕ), 1 ≤ X → ∀ (P : Finset ℕ), (∀ p ∈ P, p ≤ X) → ∀ (c : ℕ → ℂ) (k : ℕ),
      X ^ k ≤ R → ∀ (V θ : ℝ), 0 < V → 0 ≤ θ →
      k * (∑ n ∈ Ioc 0 X, ‖primeSupported P c n‖ ^ 2) ≤ θ * V ^ 2 →
      ((G.filter fun q => V ≤ ‖expSum (primeSupported P c) X (q.1 : ℂ).im‖).card : ℝ) ≤
        K * Real.log (A + R + 1) * (R * (1 + Real.log R) * (2 + Real.log R ^ 2)) * θ ^ k := by
  obtain ⟨K, T₀, hK, hT₀, h⟩ := exists_card_largeValues_pow_le
  refine ⟨9 * K, T₀, by positivity, hT₀, fun A hA R G hG X hX P hP c k hXR V θ hV hθ hkS => ?_⟩
  set S := ∑ n ∈ Ioc 0 X, ‖primeSupported P c n‖ ^ 2
  set C := ((G.filter fun q => V ≤ ‖expSum (primeSupported P c) X (q.1 : ℂ).im‖).card : ℝ)
  have hmain := h A hA R G hG X hX P hP c k V hV.le
  have hS : 0 ≤ S := sum_nonneg fun _ _ => by positivity
  have hXk1 : 1 ≤ X ^ k := Nat.one_le_pow _ _ (by omega)
  have hY1 : (1 : ℝ) ≤ (X ^ k : ℕ) := by exact_mod_cast hXk1
  have hYR : ((X ^ k : ℕ) : ℝ) ≤ R := by exact_mod_cast hXR
  have hR1 : (1 : ℝ) ≤ R := hY1.trans hYR
  have hlY : 0 ≤ Real.log (X ^ k : ℕ) := Real.log_nonneg hY1
  have hlYR : Real.log (X ^ k : ℕ) ≤ Real.log R := Real.log_le_log (by linarith) hYR
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hlog : 0 ≤ Real.log (A + R + 1) := Real.log_nonneg (by linarith)
  -- the window factors at length `X^k ≤ R`
  have hwin : (R : ℝ) + 8 * (X ^ k : ℕ) * (1 + Real.log (X ^ k : ℕ)) ≤ 9 * (R * (1 + Real.log R)) := by
    have : ((X ^ k : ℕ) : ℝ) * (1 + Real.log (X ^ k : ℕ)) ≤ R * (1 + Real.log R) :=
      mul_le_mul hYR (by linarith) (by linarith) (by linarith)
    nlinarith
  have hsob : 2 + Real.log (X ^ k : ℕ) ^ 2 ≤ 2 + Real.log R ^ 2 := by
    have := pow_le_pow_left₀ hlY hlYR 2
    linarith
  -- `k! S^k ≤ (k S)^k ≤ θ^k (V^k)²`
  have hfac : (k.factorial : ℝ) * S ^ k ≤ θ ^ k * (V ^ k) ^ 2 := by
    calc (k.factorial : ℝ) * S ^ k ≤ (k : ℝ) ^ k * S ^ k := by
          gcongr; exact_mod_cast Nat.factorial_le_pow k
      _ = ((k : ℝ) * S) ^ k := (mul_pow _ _ _).symm
      _ ≤ (θ * V ^ 2) ^ k := pow_le_pow_left₀ (by positivity) hkS k
      _ = θ ^ k * (V ^ k) ^ 2 := by ring
  have hVk : 0 < (V ^ k) ^ 2 := by positivity
  have hbound : C * (V ^ k) ^ 2 ≤
      (9 * K * Real.log (A + R + 1) * (R * (1 + Real.log R) * (2 + Real.log R ^ 2)) * θ ^ k) *
        (V ^ k) ^ 2 := by
    calc C * (V ^ k) ^ 2 ≤ _ := hmain
      _ ≤ K * Real.log (A + R + 1) * ((9 * (R * (1 + Real.log R))) *
            ((2 + Real.log R ^ 2) * (θ ^ k * (V ^ k) ^ 2))) := by
          gcongr
      _ = _ := by ring
  exact le_of_mul_le_mul_right hbound hVk

/-- **The power saving for the prime detector.** For `X ≥ 2`, `0 < θ ≤ 1` and
`log R (log X + 7) ≤ θ V²`, the zero copies in `(A, A + R]` at which the prime detector
`Σ_{p ∈ P} w_p log p · p^{−1/2 + iγ}` (with `|w_p| ≤ 1`, primes `p ≤ X`) reaches `V` number at most
`K log(A + R + 1) R (1 + log R)(2 + log² R) θ^{−1} R^{log θ/log X}`.

The exponent `log θ/log X` is negative: against the `≍ R log A` zeros of the window this is a
saving of `R^{−log(1/θ)/log X}`. For `V = η log T`, `X = (log T)^C`, `R ≍ T` one may take
`θ ≍ log log T/(η² log T)`, and the saving is `T^{−1/C + o(1)}`. -/
theorem exists_card_aligned_power_saving :
    ∃ K T₀ : ℝ, 0 < K ∧ 4 ≤ T₀ ∧ ∀ A : ℝ, T₀ ≤ A → ∀ R : ℕ, 1 ≤ R →
      ∀ G : Finset RHTower.XiZeroCopy,
      (∀ q ∈ G, A < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ A + R) →
      ∀ (X : ℕ), 2 ≤ X → ∀ (P : Finset ℕ), (∀ p ∈ P, p ≤ X) → ∀ (w : ℕ → ℂ),
      (∀ n, ‖w n‖ ≤ 1) → ∀ (V θ : ℝ), 0 < V → 0 < θ → θ ≤ 1 →
      Real.log R * (Real.log X + 7) ≤ θ * V ^ 2 →
      ((G.filter fun q =>
          V ≤ ‖expSum (primeSupported P (detector w)) X (q.1 : ℂ).im‖).card : ℝ) ≤
        K * Real.log (A + R + 1) * (R * (1 + Real.log R) * (2 + Real.log R ^ 2)) *
          (θ⁻¹ * (R : ℝ) ^ (Real.log θ / Real.log X)) := by
  obtain ⟨K, T₀, hK, hT₀, h⟩ := exists_card_largeValues_le_theta_pow
  refine ⟨K, T₀, hK, hT₀, fun A hA R hR G hG X hX P hP w hw V θ hV hθ hθ1 hcond => ?_⟩
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hlX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hlR : 0 ≤ Real.log R := Real.log_nonneg (by exact_mod_cast hR)
  -- the order `k = ⌊log R/log X⌋` of the moment
  set q := Real.log R / Real.log X
  have hq : 0 ≤ q := div_nonneg hlR hlX.le
  set k := ⌊q⌋₊
  have hkq : (k : ℝ) ≤ q := Nat.floor_le hq
  have hqk : q < k + 1 := Nat.lt_floor_add_one q
  have hXR : X ^ k ≤ R := by
    have hk : (k : ℝ) * Real.log X ≤ Real.log R := by
      rw [← le_div_iff₀ hlX]; exact hkq
    have : ((X : ℝ) ^ k) ≤ R := by
      rw [← Real.log_le_log_iff (by positivity) hR0, Real.log_pow]; exact hk
    exact_mod_cast this
  -- `k S ≤ q · log X (log X + 7) = log R (log X + 7) ≤ θ V²`
  have hmass := sum_normSq_detector_le P (by omega : 1 ≤ X) hw
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hkS : (k : ℝ) * (∑ n ∈ Ioc 0 X, ‖primeSupported P (detector w) n‖ ^ 2) ≤ θ * V ^ 2 := by
    have hS0 : 0 ≤ ∑ n ∈ Ioc 0 X, ‖primeSupported P (detector w) n‖ ^ 2 :=
      sum_nonneg fun _ _ => by positivity
    calc (k : ℝ) * (∑ n ∈ Ioc 0 X, ‖primeSupported P (detector w) n‖ ^ 2)
        ≤ q * (Real.log X * (Real.log X + 7)) := by
          refine mul_le_mul hkq (hmass.trans ?_) hS0 hq
          exact mul_le_mul_of_nonneg_left (by linarith) hlX.le
      _ = Real.log R * (Real.log X + 7) := by
          simp only [q]; field_simp
      _ ≤ θ * V ^ 2 := hcond
  have hmain := h A hA R G hG X (by omega) P hP (detector w) k hXR V θ hV hθ.le hkS
  -- `θ^k ≤ θ^{q − 1} = θ^{−1} R^{log θ/log X}`
  have hpow : θ ^ k ≤ θ⁻¹ * (R : ℝ) ^ (Real.log θ / Real.log X) := by
    rw [← Real.rpow_natCast]
    calc θ ^ (k : ℝ) ≤ θ ^ (q - 1) := Real.rpow_le_rpow_of_exponent_ge hθ hθ1 (by linarith)
      _ = θ⁻¹ * (R : ℝ) ^ (Real.log θ / Real.log X) := by
          rw [Real.rpow_sub hθ, Real.rpow_one, Real.rpow_def_of_pos hθ,
            Real.rpow_def_of_pos hR0, div_eq_inv_mul]
          congr 2
          simp only [q]; ring
  have hfront : 0 ≤ K * Real.log (A + R + 1) * (R * (1 + Real.log R) * (2 + Real.log R ^ 2)) := by
    have : 0 ≤ Real.log (A + R + 1) := Real.log_nonneg (by linarith)
    positivity
  exact hmain.trans (mul_le_mul_of_nonneg_left hpow hfront)

end GaloisForLFunctions.ArithmeticElectrostatics
