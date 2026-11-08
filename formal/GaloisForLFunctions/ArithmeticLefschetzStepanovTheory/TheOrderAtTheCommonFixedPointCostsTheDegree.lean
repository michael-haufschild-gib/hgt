import GaloisForLFunctions.RHTower.GelfondSchneider
import GaloisForLFunctions.HTGeometry.ArchimedeanCorank
import Mathlib.Algebra.Group.ForwardDiff

/-!
# The order at the common fixed point costs the degree

All prime progressions `2πiℤ/log p` meet at `s = 0`, the one exact fixed point that the Frobenius
of every prime shares. Vanishing there is cheap in conditions: an auxiliary
`A(s) = Σ_e c_e (p^{e₁} q^{e₂})^{−s}` vanishes to order `J` at `s = 0` iff its **orbit moments**
`μ_k = Σ_e c_e (e₁ log p + e₂ log q)^k` vanish for `k < J` (`(−1)^k μ_k = A^{(k)}(0)`): `J` linear
conditions. With real coefficients these can be met on any `J + 1` exponents, so the order grows
like the number of terms, `≍ (log N)²/(2 log p log q)` for length `N`.

With **integer** coefficients the same conditions cost the degree. For two primes the orbit moment
`μ_k` is a binary form in `(log p, log q)` whose coefficients are the integer **power moments**
`M_{a,b} = Σ_e c_e e₁^a e₂^b`, `a + b = k` (`orbitMoment_eq`); since `log q/log p` is transcendental
(Gelfond–Schneider, `RHTower.log_ratio_transcendental`) each `M_{a,b}` vanishes
(`powerMoment_eq_zero_of_orbitMoment_eq_zero`). Power moments of total order `≤ D` determine a
coefficient vector on the simplex `e₁ + e₂ ≤ D` (Lagrange polynomials on the simplex,
`eq_zero_of_powerMoment_eq_zero`). Hence:

* **Bézout at the common fixed point** (`exists_le_of_orbitMoment_eq_zero`): a nonzero integer
  `{p, q}`-smooth auxiliary vanishing to order `J` at `s = 0` has an exponent with `e₁ + e₂ ≥ J`, so
  its length is at least `2^J`: `J ≤ log N / log 2`.
* **Sharpness** (`orbitMoment_binomial_eq_zero`): `(p^{−s} − 1)^J` vanishes to order `J` and has
  length `p^J`.

For any finite set of primes, integrality alone decides the first two orders: `A(0) = Σ c_e` is an
integer, and `A'(0) = −log(U/V)` for integers `U, V ≤ H`, so `|A'(0)| < 1/H` forces `A'(0) = 0`
(`firstMoment_eq_zero_of_lt`), and then every first power moment vanishes
(`firstPowerMoment_eq_zero`). Beyond order two, three primes need quadratic relations among the
`log p`, a question of algebraic independence.

So at the common fixed point vanishing is either cheap and approximate (real coefficients; copies to
returns are capped by `InfiniteRankWeilTheory.order_le_of_rouche`) or exact and paid in degree
(integer coefficients). Stepanov's Frobenius makes it cheap **and** exact; over `ℤ` neither place
does.
-/

open Finset Polynomial

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

/-! ### Orbit moments and power moments for two primes -/

/-- The orbit moment `μ_k = Σ_e c_e (e₁ log p + e₂ log q)^k`; `(−1)^k μ_k` is the `k`-th derivative
at `s = 0` of `A(s) = Σ_e c_e (p^{e₁} q^{e₂})^{−s}`. -/
def orbitMoment (p q : ℕ) (E : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℤ) (k : ℕ) : ℝ :=
  ∑ e ∈ E, (c e : ℝ) * ((e.1 : ℝ) * Real.log p + (e.2 : ℝ) * Real.log q) ^ k

/-- The power moment `M_{a,b} = Σ_e c_e e₁^a e₂^b`, an integer. -/
def powerMoment (E : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℤ) (a b : ℕ) : ℤ :=
  ∑ e ∈ E, c e * (e.1 : ℤ) ^ a * (e.2 : ℤ) ^ b

/-- The orbit moment is a binary form in `(log p, log q)` with the power moments as coefficients. -/
theorem orbitMoment_eq (p q : ℕ) (E : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℤ) (k : ℕ) :
    orbitMoment p q E c k = ∑ a ∈ range (k + 1),
      (k.choose a : ℝ) * Real.log p ^ a * Real.log q ^ (k - a) * (powerMoment E c a (k - a) : ℝ) := by
  simp only [orbitMoment, powerMoment, add_pow, mul_sum, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun e _ => ?_
  ring

/-- **Gelfond–Schneider separates the power moments.** If an orbit moment of order `k` vanishes, so
does every power moment `M_{a,k−a}`. -/
theorem powerMoment_eq_zero_of_orbitMoment_eq_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (E : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℤ) {k : ℕ}
    (h : orbitMoment p q E c k = 0) : ∀ a ≤ k, powerMoment E c a (k - a) = 0 := by
  set ξ : ℝ := Real.log q / Real.log p
  have hLp : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hLq : Real.log q = ξ * Real.log p := by simp only [ξ]; field_simp
  set M : ℕ → ℚ := fun a => (k.choose a : ℚ) * powerMoment E c a (k - a)
  let g : ℚ[X] := ∑ a ∈ range (k + 1), C (M a) * X ^ (k - a)
  have hgeval : aeval ξ g = ∑ a ∈ range (k + 1), ((M a : ℚ) : ℝ) * ξ ^ (k - a) := by
    simp only [g, map_sum, map_mul, aeval_C, aeval_X_pow, eq_ratCast]
  have hg : aeval ξ g = 0 := by
    have h' := h
    rw [orbitMoment_eq, hLq] at h'
    have hsum : Real.log p ^ k * aeval ξ g = 0 := by
      rw [← h', hgeval, mul_sum]
      refine sum_congr rfl fun a ha => ?_
      have hak : a ≤ k := Nat.lt_succ_iff.mp (mem_range.mp ha)
      have hpow : Real.log p ^ k = Real.log p ^ a * Real.log p ^ (k - a) := by
        rw [← pow_add, Nat.add_sub_cancel' hak]
      rw [hpow, mul_pow]
      simp only [M]
      push_cast
      ring
    exact (mul_eq_zero.mp hsum).resolve_left (pow_ne_zero _ hLp)
  have hg0 : g = 0 := by
    by_contra hne
    exact RHTower.log_ratio_transcendental hp hq hpq ⟨g, hne, hg⟩
  intro a ha
  have hcoeff : g.coeff (k - a) = M a := by
    simp only [g, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [sum_eq_single a]
    · simp
    · intro b hb hba
      have hbk : b ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hb)
      rw [if_neg]
      omega
    · intro hna
      exact absurd (mem_range.mpr (Nat.lt_succ_of_le ha)) hna
  rw [hg0, coeff_zero] at hcoeff
  have hch : (k.choose a : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos ha).ne'
  have := hcoeff.symm
  simp only [M, mul_eq_zero, hch, false_or] at this
  exact_mod_cast this

/-! ### Power moments determine coefficients on the simplex -/

/-- The moment functional `Q ↦ Σ_e c_e Q(e)` on integer polynomials in two variables. -/
def momentFun (E : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℤ) (Q : MvPolynomial (Fin 2) ℤ) : ℤ :=
  ∑ e ∈ E, c e * MvPolynomial.eval ![(e.1 : ℤ), (e.2 : ℤ)] Q

theorem momentFun_eq_zero_of_totalDegree_le {E : Finset (ℕ × ℕ)} {c : ℕ × ℕ → ℤ} {D : ℕ}
    (hM : ∀ a b, a + b ≤ D → powerMoment E c a b = 0) {Q : MvPolynomial (Fin 2) ℤ}
    (hQ : Q.totalDegree ≤ D) : momentFun E c Q = 0 := by
  classical
  have hmono : ∀ s ∈ Q.support, momentFun E c (MvPolynomial.monomial s (Q.coeff s)) = 0 := by
    intro s hs
    have hdeg : s 0 + s 1 ≤ D := by
      have := MvPolynomial.le_totalDegree hs
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
      omega
    have h := hM (s 0) (s 1) hdeg
    simp only [momentFun, MvPolynomial.eval_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp only [powerMoment] at h
    rw [← mul_zero (Q.coeff s), ← h, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    ring
  rw [MvPolynomial.as_sum Q]
  simp only [momentFun, map_sum, mul_sum] at hmono ⊢
  rw [sum_comm]
  exact sum_eq_zero hmono

/-- A linear polynomial has total degree at most one. -/
theorem totalDegree_X_sub_C_le (i : Fin 2) (r : ℤ) :
    (MvPolynomial.X i - MvPolynomial.C r : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le (by rw [MvPolynomial.totalDegree_X])
    (by rw [MvPolynomial.totalDegree_C]; exact zero_le_one))

theorem totalDegree_C_sub_X_sub_X_le (r : ℤ) :
    (MvPolynomial.C r - MvPolynomial.X 0 - MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ).totalDegree
      ≤ 1 :=
  (MvPolynomial.totalDegree_sub _ _).trans
    (max_le ((MvPolynomial.totalDegree_sub _ _).trans
      (max_le (by rw [MvPolynomial.totalDegree_C]; exact zero_le_one)
        (by rw [MvPolynomial.totalDegree_X])))
      (by rw [MvPolynomial.totalDegree_X]))

/-- The Lagrange polynomial of the simplex point `(i₀, j₀)`, `i₀ + j₀ ≤ D`. -/
def simplexLagrange (D i₀ j₀ : ℕ) : MvPolynomial (Fin 2) ℤ :=
  (∏ k ∈ range i₀, (MvPolynomial.X 0 - MvPolynomial.C (k : ℤ))) *
    (∏ k ∈ range j₀, (MvPolynomial.X 1 - MvPolynomial.C (k : ℤ))) *
      ∏ k ∈ range (D - (i₀ + j₀)),
        (MvPolynomial.C ((D : ℤ) - k) - MvPolynomial.X 0 - MvPolynomial.X 1)

theorem totalDegree_simplexLagrange_le {D i₀ j₀ : ℕ} (h : i₀ + j₀ ≤ D) :
    (simplexLagrange D i₀ j₀).totalDegree ≤ D := by
  have h1 := MvPolynomial.totalDegree_finsetProd (range i₀)
    (fun k : ℕ => (MvPolynomial.X 0 - MvPolynomial.C (k : ℤ) : MvPolynomial (Fin 2) ℤ))
  have h2 := MvPolynomial.totalDegree_finsetProd (range j₀)
    (fun k : ℕ => (MvPolynomial.X 1 - MvPolynomial.C (k : ℤ) : MvPolynomial (Fin 2) ℤ))
  have h3 := MvPolynomial.totalDegree_finsetProd (range (D - (i₀ + j₀)))
    (fun k : ℕ => (MvPolynomial.C ((D : ℤ) - k) - MvPolynomial.X 0 - MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℤ))
  have b1 : ∑ k ∈ range i₀, (MvPolynomial.X 0 - MvPolynomial.C (k : ℤ) :
      MvPolynomial (Fin 2) ℤ).totalDegree ≤ i₀ := by
    simpa using sum_le_sum fun k (_ : k ∈ range i₀) => totalDegree_X_sub_C_le 0 k
  have b2 : ∑ k ∈ range j₀, (MvPolynomial.X 1 - MvPolynomial.C (k : ℤ) :
      MvPolynomial (Fin 2) ℤ).totalDegree ≤ j₀ := by
    simpa using sum_le_sum fun k (_ : k ∈ range j₀) => totalDegree_X_sub_C_le 1 k
  have b3 : ∑ k ∈ range (D - (i₀ + j₀)), (MvPolynomial.C ((D : ℤ) - k) - MvPolynomial.X 0 -
      MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ).totalDegree ≤ D - (i₀ + j₀) := by
    simpa using sum_le_sum fun k (_ : k ∈ range (D - (i₀ + j₀))) =>
      totalDegree_C_sub_X_sub_X_le ((D : ℤ) - k)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hm := MvPolynomial.totalDegree_mul
    (∏ k ∈ range i₀, (MvPolynomial.X 0 - MvPolynomial.C (k : ℤ) : MvPolynomial (Fin 2) ℤ))
    (∏ k ∈ range j₀, (MvPolynomial.X 1 - MvPolynomial.C (k : ℤ)))
  omega

theorem eval_simplexLagrange (D i₀ j₀ : ℕ) (e : ℕ × ℕ) :
    MvPolynomial.eval ![(e.1 : ℤ), (e.2 : ℤ)] (simplexLagrange D i₀ j₀) =
      (∏ k ∈ range i₀, ((e.1 : ℤ) - k)) * (∏ k ∈ range j₀, ((e.2 : ℤ) - k)) *
        ∏ k ∈ range (D - (i₀ + j₀)), ((D : ℤ) - k - e.1 - e.2) := by
  simp [simplexLagrange, map_prod]

/-- The Lagrange polynomial vanishes at every other point of the simplex. -/
theorem eval_simplexLagrange_eq_zero {D i₀ j₀ : ℕ} {e : ℕ × ℕ} (he : e.1 + e.2 ≤ D)
    (hne : e ≠ (i₀, j₀)) :
    MvPolynomial.eval ![(e.1 : ℤ), (e.2 : ℤ)] (simplexLagrange D i₀ j₀) = 0 := by
  rw [eval_simplexLagrange]
  by_cases h1 : e.1 < i₀
  · rw [prod_eq_zero (mem_range.mpr h1) (by ring), zero_mul, zero_mul]
  by_cases h2 : e.2 < j₀
  · rw [prod_eq_zero (mem_range.mpr h2) (by ring), mul_zero, zero_mul]
  have hgt : i₀ + j₀ < e.1 + e.2 := by
    rcases e with ⟨a, b⟩
    simp only [ne_eq, Prod.mk.injEq] at hne
    simp only at h1 h2 he ⊢
    omega
  have hk : D - (e.1 + e.2) ∈ range (D - (i₀ + j₀)) := mem_range.mpr (by omega)
  rw [prod_eq_zero hk (by push_cast [Nat.cast_sub he]; ring), mul_zero]

theorem eval_simplexLagrange_self_ne_zero (D i₀ j₀ : ℕ) :
    MvPolynomial.eval ![(i₀ : ℤ), (j₀ : ℤ)] (simplexLagrange D i₀ j₀) ≠ 0 := by
  have h := eval_simplexLagrange D i₀ j₀ (i₀, j₀)
  simp only at h
  rw [h]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> rw [prod_ne_zero_iff] <;> intro k hk <;>
    have := mem_range.mp hk <;> omega

/-- **Unisolvence of the simplex.** A coefficient vector supported on `e₁ + e₂ ≤ D` whose power
moments of total order `≤ D` vanish is zero. -/
theorem eq_zero_of_powerMoment_eq_zero {E : Finset (ℕ × ℕ)} {c : ℕ × ℕ → ℤ} {D : ℕ}
    (hsupp : ∀ e ∈ E, e.1 + e.2 ≤ D) (hM : ∀ a b, a + b ≤ D → powerMoment E c a b = 0) :
    ∀ e ∈ E, c e = 0 := by
  intro t ht
  have hD := hsupp t ht
  have h0 := momentFun_eq_zero_of_totalDegree_le hM (totalDegree_simplexLagrange_le (j₀ := t.2) hD)
  rw [momentFun, sum_eq_single t] at h0
  · exact (mul_eq_zero.mp h0).resolve_right (eval_simplexLagrange_self_ne_zero D t.1 t.2)
  · intro e he hne
    rw [eval_simplexLagrange_eq_zero (hsupp e he) hne, mul_zero]
  · exact fun h => absurd ht h

/-! ### Bézout at the common fixed point -/

/-- **Bézout at the common fixed point.** A nonzero integer `{p, q}`-smooth auxiliary whose first
`J` orbit moments vanish (order `J` at `s = 0`) has an exponent of total degree at least `J`. -/
theorem exists_le_of_orbitMoment_eq_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {E : Finset (ℕ × ℕ)} {c : ℕ × ℕ → ℤ} {J : ℕ} (hmom : ∀ k < J, orbitMoment p q E c k = 0)
    (hc : ∃ e ∈ E, c e ≠ 0) : ∃ e ∈ E, c e ≠ 0 ∧ J ≤ e.1 + e.2 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht, hct⟩ := hc
  set E' := E.filter (fun e => c e ≠ 0)
  have hJ : 0 < J := by have := hcon t ht hct; omega
  have hsupp : ∀ e ∈ E', e.1 + e.2 ≤ J - 1 := by
    intro e he
    rw [mem_filter] at he
    have := hcon e he.1 he.2
    omega
  have hmom' : ∀ k < J, orbitMoment p q E' c k = 0 := by
    intro k hk
    rw [← hmom k hk, orbitMoment, orbitMoment, sum_filter]
    refine sum_congr rfl fun e _ => ?_
    split_ifs with h
    · rfl
    · push Not at h; simp [h]
  have hM : ∀ a b, a + b ≤ J - 1 → powerMoment E' c a b = 0 := by
    intro a b hab
    have h := powerMoment_eq_zero_of_orbitMoment_eq_zero hp hq hpq E' c (hmom' (a + b) (by omega))
      a (Nat.le_add_right a b)
    rwa [Nat.add_sub_cancel_left] at h
  have := eq_zero_of_powerMoment_eq_zero hsupp hM t (mem_filter.mpr ⟨ht, hct⟩)
  exact hct this

/-- The length bound: the auxiliary has a term `n = p^{e₁}q^{e₂} ≥ 2^J`. -/
theorem exists_two_pow_le_of_orbitMoment_eq_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {E : Finset (ℕ × ℕ)} {c : ℕ × ℕ → ℤ} {J : ℕ}
    (hmom : ∀ k < J, orbitMoment p q E c k = 0) (hc : ∃ e ∈ E, c e ≠ 0) :
    ∃ e ∈ E, c e ≠ 0 ∧ 2 ^ J ≤ p ^ e.1 * q ^ e.2 := by
  obtain ⟨e, he, hce, hJ⟩ := exists_le_of_orbitMoment_eq_zero hp hq hpq hmom hc
  refine ⟨e, he, hce, ?_⟩
  calc 2 ^ J ≤ 2 ^ (e.1 + e.2) := Nat.pow_le_pow_right (by norm_num) hJ
    _ = 2 ^ e.1 * 2 ^ e.2 := pow_add _ _ _
    _ ≤ p ^ e.1 * q ^ e.2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hp.two_le _) (Nat.pow_le_pow_left hq.two_le _)

/-- **Sharpness.** The coefficients of `(p^{−s} − 1)^J`, `c(i, 0) = (−1)^{J−i} C(J, i)`, have
vanishing orbit moments of every order `k < J`, and their top exponent is `J`. -/
theorem orbitMoment_binomial_eq_zero (p q J : ℕ) {k : ℕ} (hk : k < J) :
    orbitMoment p q ((range (J + 1)).map ⟨fun i => (i, 0), fun _ _ h => (Prod.mk.inj h).1⟩)
      (fun e => (-1 : ℤ) ^ (J - e.1) * J.choose e.1) k = 0 := by
  have hdiff := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hk) 0
  rw [fwdDiff_iter_eq_sum_shift] at hdiff
  simp only [orbitMoment, sum_map, Function.Embedding.coeFn_mk, Nat.cast_zero, zero_mul,
    add_zero]
  simp only [zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul, Pi.zero_apply] at hdiff
  have : ∑ i ∈ range (J + 1), (((-1 : ℤ) ^ (J - i) * (J.choose i : ℤ) : ℤ) : ℝ) *
      ((i : ℝ) * Real.log p) ^ k = Real.log p ^ k *
      ∑ i ∈ range (J + 1), (((-1 : ℤ) ^ (J - i) * (J.choose i : ℤ) : ℤ) : ℝ) * (i : ℝ) ^ k := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] at hdiff ⊢
  rw [hdiff, mul_zero]

/-! ### The first two orders for any finite set of primes -/

variable {P : Finset Nat.Primes}

/-- The first power moments `M_p = Σ_α c_α α_p`. -/
def firstPowerMoment (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ) (p : P) : ℤ :=
  ∑ α ∈ S, c α * α p

/-- The first orbit moment `μ₁ = Σ_α c_α Σ_p α_p log p = −A'(0)`. -/
def firstMoment (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ) : ℝ :=
  ∑ α ∈ S, (c α : ℝ) * ∑ p : P, (α p : ℝ) * Real.log ((p : Nat.Primes) : ℕ)

theorem firstMoment_eq (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ) :
    firstMoment S c = ∑ p : P, (firstPowerMoment S c p : ℝ) * Real.log ((p : Nat.Primes) : ℕ) := by
  simp only [firstMoment, firstPowerMoment, mul_sum, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => sum_congr rfl fun α _ => ?_
  ring

/-- **Order two is exact.** A vanishing first orbit moment forces every first power moment to
vanish (unique factorization: the `log p` are `ℚ`-linearly independent). -/
theorem firstPowerMoment_eq_zero (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ)
    (h : firstMoment S c = 0) (p : P) : firstPowerMoment S c p = 0 := by
  have hli := primeLogFiniteSlice_linearIndependent P
  rw [firstMoment_eq] at h
  have hz := linearIndependent_iff'.mp hli univ (fun p => (firstPowerMoment S c p : ℚ))
    (by
      rw [← h]
      refine sum_congr rfl fun p _ => ?_
      rw [Rat.smul_def]
      push_cast
      ring) p (mem_univ p)
  exact_mod_cast hz

/-- `|log U − log V| ≥ 1/max(U, V)` for distinct positive integers. -/
theorem inv_max_le_abs_log_sub {U V : ℕ} (hU : 0 < U) (hV : 0 < V) (hUV : U ≠ V) :
    1 / (max U V : ℝ) ≤ |Real.log U - Real.log V| := by
  wlog h : V < U generalizing U V
  · have h' : U < V := lt_of_le_of_ne (not_lt.mp h) hUV
    have := this hV hU hUV.symm h'
    rwa [max_comm, abs_sub_comm] at this
  have hUr : (0 : ℝ) < U := by exact_mod_cast hU
  have hVr : (0 : ℝ) < V := by exact_mod_cast hV
  have hle : (V : ℝ) + 1 ≤ U := by exact_mod_cast h
  rw [max_eq_left (by exact_mod_cast h.le), abs_of_nonneg (by
    rw [sub_nonneg]; exact Real.log_le_log hVr (by linarith))]
  rw [← Real.log_div hUr.ne' hVr.ne']
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hUr hVr)
  rw [inv_div] at hlog
  have : 1 / (U : ℝ) ≤ 1 - V / U := by
    rw [div_le_iff₀ hUr, sub_mul, one_mul, div_mul_cancel₀ _ hUr.ne']
    linarith
  linarith

/-- The height `H = Π_p p^{|M_p|}` that controls the first-order amplifier. -/
def firstHeight (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ) : ℕ :=
  ∏ p : P, ((p : Nat.Primes) : ℕ) ^ (firstPowerMoment S c p).natAbs

/-- **The first-order integrality amplifier.** `A'(0) = −log(U/V)` with integers `U, V ≤ H`, so
`|A'(0)| < 1/H` forces `A'(0) = 0`. -/
theorem firstMoment_eq_zero_of_lt (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ)
    (h : |firstMoment S c| < 1 / (firstHeight S c : ℝ)) : firstMoment S c = 0 := by
  set M := firstPowerMoment S c with hMdef
  set U : ℕ := ∏ p : P, ((p : Nat.Primes) : ℕ) ^ (M p).toNat
  set V : ℕ := ∏ p : P, ((p : Nat.Primes) : ℕ) ^ (-M p).toNat
  have hpos : ∀ p : P, 0 < ((p : Nat.Primes) : ℕ) := fun p => (p : Nat.Primes).2.pos
  have hU : 0 < U := prod_pos fun p _ => pow_pos (hpos p) _
  have hV : 0 < V := prod_pos fun p _ => pow_pos (hpos p) _
  have hlog : firstMoment S c = Real.log U - Real.log V := by
    rw [firstMoment_eq]
    simp only [U, V, Nat.cast_prod, Nat.cast_pow]
    rw [Real.log_prod (fun p _ => pow_ne_zero _ (by exact_mod_cast (hpos p).ne')),
      Real.log_prod (fun p _ => pow_ne_zero _ (by exact_mod_cast (hpos p).ne')), ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [Real.log_pow, Real.log_pow, ← sub_mul]
    congr 1
    have := Int.toNat_sub_toNat_neg (M p)
    exact_mod_cast this.symm
  have hmax : (max U V : ℝ) ≤ firstHeight S c := by
    have hU' : U ≤ firstHeight S c := prod_le_prod' fun p _ =>
      Nat.pow_le_pow_right (hpos p) (by rw [hMdef]; omega)
    have hV' : V ≤ firstHeight S c := prod_le_prod' fun p _ =>
      Nat.pow_le_pow_right (hpos p) (by rw [hMdef]; omega)
    exact_mod_cast max_le hU' hV'
  by_contra hne
  have hUV : U ≠ V := by
    intro hUV
    exact hne (by rw [hlog, hUV, sub_self])
  have h1 := inv_max_le_abs_log_sub hU hV hUV
  have hmaxpos : (0 : ℝ) < (max U V : ℝ) := by exact_mod_cast lt_max_of_lt_left hU
  have h2 : 1 / (firstHeight S c : ℝ) ≤ 1 / (max U V : ℝ) :=
    one_div_le_one_div_of_le hmaxpos hmax
  rw [← hlog] at h1
  linarith

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
