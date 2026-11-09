import GaloisForLFunctions.HTGeometry.ArchimedeanCorank
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The excess order is a relation among the logarithms

At the common fixed point `s = 0` of all prime progressions, an integer `P`-smooth auxiliary
`A(s) = Σ_α c_α n_α^{-s}` vanishes to orbit order `J` iff its orbit moments
`μ_j = Σ_α c_α λ_α^j`, `λ_α = Σ_p α_p log p`, vanish for `j < J`. For any finite set of primes:

* **The orbit moment is the moment form at the logarithms** (`orbitMomentF_eq`): by the multinomial
  theorem `μ_d = Σ_{|β| = d} multinomial(β) M_β Π_p (log p)^{β_p}`, with integer power moments
  `M_β = Σ_α c_α α^β`.
* **Each vanishing orbit moment is a relation or a block of vanishing power moments**
  (`powerMomentF_eq_zero_or_relation`): either all `M_β` of total order `d` vanish, or the `log p`
  satisfy the nonzero integer homogeneous relation `Σ_{|β|=d} multinomial(β) M_β (log p)^β = 0`.
* **Power moments determine the coefficients on a simplex** (`eq_zero_of_powerMomentF_eq_zero`):
  Lagrange polynomials on `|α| ≤ D` in `|P|` variables.
* **The dichotomy** (`exists_large_or_relation`): a nonzero integer auxiliary vanishing to orbit
  order `J` at `s = 0` either has a term `n_α ≥ 2^J` (`J ≤ log N/log 2`), or the logarithms of the
  primes of `P` satisfy a nonzero integer homogeneous polynomial relation of degree `< J`.

For two primes the second alternative is excluded by Gelfond–Schneider
(`exists_two_pow_le_of_orbitMoment_eq_zero`); for three or more it is the algebraic independence of
logarithms (a consequence of Schanuel's conjecture). Integrality alone makes the order at the common
fixed point cost the degree, up to exactly this transcendence question.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {P : Finset Nat.Primes}

/-- The vector `(log p)_{p ∈ P}`. -/
def logVec (P : Finset Nat.Primes) : P → ℝ := fun p => Real.log ((p : Nat.Primes) : ℕ)

/-- The frequency `λ_α = Σ_p α_p log p` of an exponent vector. -/
def freqF (α : P → ℕ) : ℝ := ∑ p, (α p : ℝ) * logVec P p

/-- The orbit moment `μ_j = Σ_α c_α λ_α^j`. -/
def orbitMomentF (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ) (j : ℕ) : ℝ :=
  ∑ α ∈ S, (c α : ℝ) * freqF α ^ j

/-- The power moment `M_β = Σ_α c_α Π_p α_p^{β_p}`, an integer. -/
def powerMomentF (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ) (β : P → ℕ) : ℤ :=
  ∑ α ∈ S, c α * ∏ p, (α p : ℤ) ^ β p

/-- **The orbit moment is the moment form at the logarithms.** -/
theorem orbitMomentF_eq (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ) (d : ℕ) :
    orbitMomentF S c d = ∑ β ∈ piAntidiag univ d,
      (Nat.multinomial univ β : ℝ) * (powerMomentF S c β : ℝ) * ∏ p, logVec P p ^ β p := by
  simp only [orbitMomentF, freqF, sum_pow_eq_sum_piAntidiag, mul_sum, powerMomentF, Int.cast_sum,
    Int.cast_mul, Int.cast_prod, Int.cast_pow, Int.cast_natCast, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun β _ => sum_congr rfl fun α _ => ?_
  simp only [mul_pow, prod_mul_distrib]
  ring

/-- **A vanishing orbit moment is a block of vanishing power moments or a relation.** -/
theorem powerMomentF_eq_zero_or_relation (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ) {d : ℕ}
    (h : orbitMomentF S c d = 0) :
    (∀ β ∈ piAntidiag (univ : Finset P) d, powerMomentF S c β = 0) ∨
      ∃ q : (P → ℕ) → ℤ, (∃ β ∈ piAntidiag (univ : Finset P) d, q β ≠ 0) ∧
        ∑ β ∈ piAntidiag univ d, (q β : ℝ) * ∏ p, logVec P p ^ β p = 0 := by
  by_cases hall : ∀ β ∈ piAntidiag (univ : Finset P) d, powerMomentF S c β = 0
  · exact Or.inl hall
  push Not at hall
  obtain ⟨β, hβ, hne⟩ := hall
  refine Or.inr ⟨fun β => Nat.multinomial univ β * powerMomentF S c β, ⟨β, hβ, ?_⟩, ?_⟩
  · exact mul_ne_zero (by exact_mod_cast (Nat.multinomial_pos _ _).ne') hne
  · rw [← h, orbitMomentF_eq]
    refine sum_congr rfl fun β _ => ?_
    push_cast
    ring

/-! ### Unisolvence of the simplex in `|P|` variables -/

/-- The moment functional `Q ↦ Σ_α c_α Q(α)`. -/
def momentFunF (S : Finset (P → ℕ)) (c : (P → ℕ) → ℤ) (Q : MvPolynomial P ℤ) : ℤ :=
  ∑ α ∈ S, c α * MvPolynomial.eval (fun p => (α p : ℤ)) Q

theorem momentFunF_eq_zero {S : Finset (P → ℕ)} {c : (P → ℕ) → ℤ} {D : ℕ}
    (hM : ∀ β : P → ℕ, ∑ p, β p ≤ D → powerMomentF S c β = 0) {Q : MvPolynomial P ℤ}
    (hQ : Q.totalDegree ≤ D) : momentFunF S c Q = 0 := by
  classical
  have hmono : ∀ s ∈ Q.support, momentFunF S c (MvPolynomial.monomial s (Q.coeff s)) = 0 := by
    intro s hs
    have hdeg : ∑ p, s p ≤ D := by
      have := MvPolynomial.le_totalDegree hs
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
      omega
    have h := hM s hdeg
    simp only [momentFunF, MvPolynomial.eval_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [powerMomentF] at h
    rw [← mul_zero (Q.coeff s), ← h, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    ring
  rw [MvPolynomial.as_sum Q]
  simp only [momentFunF, map_sum, mul_sum] at hmono ⊢
  rw [sum_comm]
  exact sum_eq_zero hmono

/-- The Lagrange polynomial of the simplex point `t`, `|t| ≤ D`. -/
def simplexLagrangeF (D : ℕ) (t : P → ℕ) : MvPolynomial P ℤ :=
  (∏ p, ∏ k ∈ range (t p), (MvPolynomial.X p - MvPolynomial.C (k : ℤ))) *
    ∏ k ∈ range (D - ∑ p, t p), (MvPolynomial.C ((D : ℤ) - k) - ∑ p, MvPolynomial.X p)

theorem totalDegree_simplexLagrangeF_le {D : ℕ} {t : P → ℕ} (ht : ∑ p, t p ≤ D) :
    (simplexLagrangeF D t).totalDegree ≤ D := by
  have hlin : ∀ (p : P) (k : ℤ),
      (MvPolynomial.X p - MvPolynomial.C k : MvPolynomial P ℤ).totalDegree ≤ 1 := fun p k =>
    (MvPolynomial.totalDegree_sub _ _).trans (max_le (by rw [MvPolynomial.totalDegree_X])
      (by rw [MvPolynomial.totalDegree_C]; exact zero_le_one))
  have hsumX : (∑ p, MvPolynomial.X p : MvPolynomial P ℤ).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_finsetSum_le fun p _ => ?_)
    rw [MvPolynomial.totalDegree_X]
  have hlin2 : ∀ k : ℤ, (MvPolynomial.C k - ∑ p, MvPolynomial.X p :
      MvPolynomial P ℤ).totalDegree ≤ 1 := fun k =>
    (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (by rw [MvPolynomial.totalDegree_C]; exact zero_le_one) hsumX)
  have h1 : (∏ p, ∏ k ∈ range (t p), (MvPolynomial.X p - MvPolynomial.C (k : ℤ)) :
      MvPolynomial P ℤ).totalDegree ≤ ∑ p, t p := by
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (sum_le_sum fun p _ => ?_)
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    simpa using sum_le_sum fun k (_ : k ∈ range (t p)) => hlin p k
  have h2 : (∏ k ∈ range (D - ∑ p, t p), (MvPolynomial.C ((D : ℤ) - k) -
      ∑ p, MvPolynomial.X p) : MvPolynomial P ℤ).totalDegree ≤ D - ∑ p, t p := by
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    simpa using sum_le_sum fun k (_ : k ∈ range (D - ∑ p, t p)) => hlin2 ((D : ℤ) - k)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  omega

theorem eval_simplexLagrangeF (D : ℕ) (t α : P → ℕ) :
    MvPolynomial.eval (fun p => (α p : ℤ)) (simplexLagrangeF D t) =
      (∏ p, ∏ k ∈ range (t p), ((α p : ℤ) - k)) *
        ∏ k ∈ range (D - ∑ p, t p), ((D : ℤ) - k - ∑ p, (α p : ℤ)) := by
  simp [simplexLagrangeF, map_prod]

theorem eval_simplexLagrangeF_eq_zero {D : ℕ} {t α : P → ℕ} (hα : ∑ p, α p ≤ D) (hne : α ≠ t) :
    MvPolynomial.eval (fun p => (α p : ℤ)) (simplexLagrangeF D t) = 0 := by
  rw [eval_simplexLagrangeF]
  by_cases hlow : ∃ p, α p < t p
  · obtain ⟨p, hp⟩ := hlow
    rw [prod_eq_zero (mem_univ p) (prod_eq_zero (mem_range.mpr hp) (by ring)), zero_mul]
  push Not at hlow
  have hgt : ∑ p, t p < ∑ p, α p := by
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hne
    exact sum_lt_sum (fun q _ => hlow q) ⟨p, mem_univ p, lt_of_le_of_ne (hlow p) (Ne.symm hp)⟩
  have hk : D - ∑ p, α p ∈ range (D - ∑ p, t p) := mem_range.mpr (by omega)
  rw [prod_eq_zero hk (by push_cast [Nat.cast_sub hα]; ring), mul_zero]

theorem eval_simplexLagrangeF_self_ne_zero (D : ℕ) (t : P → ℕ) :
    MvPolynomial.eval (fun p => (t p : ℤ)) (simplexLagrangeF D t) ≠ 0 := by
  rw [eval_simplexLagrangeF]
  refine mul_ne_zero ?_ ?_
  · rw [prod_ne_zero_iff]
    intro p _
    rw [prod_ne_zero_iff]
    intro k hk
    have := mem_range.mp hk
    omega
  · rw [prod_ne_zero_iff]
    intro k hk
    have := mem_range.mp hk
    have hcast : (∑ p, (t p : ℤ)) = ((∑ p, t p : ℕ) : ℤ) := by push_cast; rfl
    rw [hcast]
    omega

/-- **Unisolvence of the simplex.** A coefficient vector supported on `|α| ≤ D` whose power moments
of total order `≤ D` vanish is zero. -/
theorem eq_zero_of_powerMomentF_eq_zero {S : Finset (P → ℕ)} {c : (P → ℕ) → ℤ} {D : ℕ}
    (hsupp : ∀ α ∈ S, ∑ p, α p ≤ D) (hM : ∀ β : P → ℕ, ∑ p, β p ≤ D → powerMomentF S c β = 0) :
    ∀ α ∈ S, c α = 0 := by
  intro t ht
  have h0 := momentFunF_eq_zero hM (totalDegree_simplexLagrangeF_le (hsupp t ht))
  rw [momentFunF, sum_eq_single t] at h0
  · exact (mul_eq_zero.mp h0).resolve_right (eval_simplexLagrangeF_self_ne_zero D t)
  · intro α hα hne
    rw [eval_simplexLagrangeF_eq_zero (hsupp α hα) hne, mul_zero]
  · exact fun h => absurd ht h

/-! ### The dichotomy -/

/-- The logarithms of the primes of `P` satisfy a nonzero integer homogeneous relation of degree
`d`. -/
def LogRelation (P : Finset Nat.Primes) (d : ℕ) : Prop :=
  ∃ q : (P → ℕ) → ℤ, (∃ β ∈ piAntidiag (univ : Finset P) d, q β ≠ 0) ∧
    ∑ β ∈ piAntidiag univ d, (q β : ℝ) * ∏ p, logVec P p ^ β p = 0

/-- **The excess order is a relation among the logarithms.** A nonzero integer auxiliary vanishing
to orbit order `J` at `s = 0` has an exponent of total degree `≥ J`, or the logarithms of `P`
satisfy a nonzero integer homogeneous relation of degree `< J`. -/
theorem exists_large_or_relation {S : Finset (P → ℕ)} {c : (P → ℕ) → ℤ} {J : ℕ}
    (hmom : ∀ j < J, orbitMomentF S c j = 0) (hc : ∃ α ∈ S, c α ≠ 0) :
    (∃ α ∈ S, c α ≠ 0 ∧ J ≤ ∑ p, α p) ∨ ∃ d < J, LogRelation P d := by
  classical
  by_cases hrel : ∃ d < J, LogRelation P d
  · exact Or.inr hrel
  push Not at hrel
  left
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht, hct⟩ := hc
  set S' := S.filter (fun α => c α ≠ 0)
  have hJ : 0 < J := by have := hcon t ht hct; omega
  have hsupp : ∀ α ∈ S', ∑ p, α p ≤ J - 1 := by
    intro α hα
    rw [mem_filter] at hα
    have := hcon α hα.1 hα.2
    omega
  have hmom' : ∀ j < J, orbitMomentF S' c j = 0 := by
    intro j hj
    rw [← hmom j hj, orbitMomentF, orbitMomentF, sum_filter]
    refine sum_congr rfl fun α _ => ?_
    split_ifs with h
    · rfl
    · push Not at h; simp [h]
  have hM : ∀ β : P → ℕ, ∑ p, β p ≤ J - 1 → powerMomentF S' c β = 0 := by
    intro β hβ
    rcases powerMomentF_eq_zero_or_relation S' c (hmom' (∑ p, β p) (by omega)) with h | h
    · exact h β (mem_piAntidiag.mpr ⟨rfl, fun p _ => mem_univ p⟩)
    · exact absurd h (hrel _ (by omega))
  exact hct (eq_zero_of_powerMomentF_eq_zero hsupp hM t (mem_filter.mpr ⟨ht, hct⟩))

/-- In length: without a relation of degree `< J`, the auxiliary has a term `n_α ≥ 2^J`. -/
theorem exists_two_pow_le_or_relation {S : Finset (P → ℕ)} {c : (P → ℕ) → ℤ} {J : ℕ}
    (hmom : ∀ j < J, orbitMomentF S c j = 0) (hc : ∃ α ∈ S, c α ≠ 0) :
    (∃ α ∈ S, c α ≠ 0 ∧ 2 ^ J ≤ ∏ p : P, (((p : P) : Nat.Primes) : ℕ) ^ α p) ∨
      ∃ d < J, LogRelation P d := by
  rcases exists_large_or_relation hmom hc with ⟨α, hα, hcα, hJ⟩ | h
  · refine Or.inl ⟨α, hα, hcα, ?_⟩
    calc 2 ^ J ≤ 2 ^ ∑ p, α p := Nat.pow_le_pow_right (by norm_num) hJ
      _ = ∏ p, 2 ^ α p := (prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ p : P, (((p : P) : Nat.Primes) : ℕ) ^ α p :=
        prod_le_prod' fun p _ => Nat.pow_le_pow_left (p : Nat.Primes).2.two_le _
  · exact Or.inr h

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
