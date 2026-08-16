import GaloisForLFunctions.RHTower.FriableAuxiliary
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The edge coefficients of the friable auxiliary

Collecting the multinomial expansion of `(Σ_p m_p log p)^T` turns the derivative-at-one identity
into the card's displayed form

`F^{(T)}(1) = (−1)^T Σ_{|a| = T} C_a ∏_p (log p)^{a_p}`,
`C_a = multinomial(a) · Σ_m λ_m (∏_p m_p^{a_p}) / n_m`,

exhibiting `F^{(T)}(1)` as a linear form in the degree-`T` monomials of the prime logarithms with
explicitly computed coefficients.  This is the collection step between the word expansion
`primeLogDot_pow_wordExpansion` and the coefficient-surjectivity statement.

## Main results

* `primeLogDot_pow_collected` — the multinomial collection of `(Σ_p m_p log p)^T`;
* `iteratedDeriv_friableExponentDirichletExp_at_one_collected` — the edge identity with the
  coefficients `C_a` isolated;
* `friableSpace` — the auxiliary space `𝒜_{S,d}` as a `ℂ`-submodule.
-/

noncomputable section

namespace GaloisForLFunctions

open scoped BigOperators

/-- **Multinomial collection of the prime-log dot power.**  For an exponent vector supported in a
finite prime set `S`, the `T`-th power of `Σ_p m_p log p` is the degree-`T` log-monomial expansion
with multinomial coefficients. -/
theorem primeLogDot_pow_collected (S : Finset Nat.Primes) (T : ℕ)
    (m : Nat.Primes →₀ ℕ) (hm : m.support ⊆ S) :
    (m.sum fun p k => (k : ℂ) * (Real.log (p : ℕ) : ℂ)) ^ T =
      ∑ a ∈ Finset.piAntidiag S T,
        ((Nat.multinomial S a : ℕ) : ℂ) *
          (∏ p ∈ S, ((m p : ℕ) : ℂ) ^ (a p)) *
          (∏ p ∈ S, ((Real.log (p : ℕ) : ℂ)) ^ (a p)) := by
  classical
  have hrestrict : (m.sum fun p k => (k : ℂ) * (Real.log (p : ℕ) : ℂ))
      = ∑ p ∈ S, ((m p : ℕ) : ℂ) * (Real.log (p : ℕ) : ℂ) := by
    refine Finsupp.sum_of_support_subset m hm _ (fun p _ => by simp)
  rw [hrestrict, Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun p _ => mul_pow _ _ _)

/-- **The edge identity with the coefficients collected.**  The `T`-th derivative at `s = 1` of a
friable auxiliary supported on the prime set `S` is `(−1)^T` times a linear combination of the
degree-`T` prime-log monomials, with coefficients

`C_a = multinomial(a) · Σ_m λ_m (∏_p m_p^{a_p}) / n_m`. -/
theorem iteratedDeriv_friableExponentDirichletExp_at_one_collected
    (S : Finset Nat.Primes) (T : ℕ) (P : (Nat.Primes →₀ ℕ) →₀ ℂ)
    (hsupp : ∀ m ∈ P.support, m.support ⊆ S) :
    iteratedDeriv T (fun z : ℂ => friableExponentDirichletExp P z) 1 =
      (-1 : ℂ) ^ T *
        ∑ a ∈ Finset.piAntidiag S T,
          (((Nat.multinomial S a : ℕ) : ℂ) *
            (P.sum fun m c =>
              c * (∏ p ∈ S, ((m p : ℕ) : ℂ) ^ (a p)) * ((primeProduct m : ℕ) : ℂ)⁻¹)) *
            (∏ p ∈ S, ((Real.log (p : ℕ) : ℂ)) ^ (a p)) := by
  classical
  rw [iteratedDeriv_friableExponentDirichletExp_at_one]
  congr 1
  rw [Finsupp.sum]
  have hstep : ∀ m ∈ P.support,
      P m * ((m.sum fun p k => (k : ℂ) * (Real.log (p : ℕ) : ℂ)) ^ T) *
          ((primeProduct m : ℕ) : ℂ)⁻¹
        = ∑ a ∈ Finset.piAntidiag S T,
            (((Nat.multinomial S a : ℕ) : ℂ) *
              (P m * (∏ p ∈ S, ((m p : ℕ) : ℂ) ^ (a p)) * ((primeProduct m : ℕ) : ℂ)⁻¹)) *
              (∏ p ∈ S, ((Real.log (p : ℕ) : ℂ)) ^ (a p)) := by
    intro m hm
    rw [primeLogDot_pow_collected S T m (hsupp m hm), Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finsupp.sum, Finset.mul_sum, Finset.sum_mul]

/-! ### The friable auxiliary space `𝒜_{S,d}` -/

/-- **The friable auxiliary space `𝒜_{S,d}`.**  Coefficient families whose exponent vectors are
supported on the finite prime set `S` and have `ℓ¹`-degree at most `d`.  This is the native
auxiliary object of the Siegel–Shidlovsky race: a `ℂ`-submodule of all finite exponent-indexed
coefficient families. -/
def friableSpace (S : Finset Nat.Primes) (d : ℕ) :
    Submodule ℂ ((Nat.Primes →₀ ℕ) →₀ ℂ) where
  carrier := {P | ∀ m ∈ P.support, m.support ⊆ S ∧ (m.sum fun _ k => k) ≤ d}
  add_mem' {P Q} hP hQ := by
    intro m hm
    rcases Finset.mem_union.mp (Finsupp.support_add hm) with h | h
    · exact hP m h
    · exact hQ m h
  zero_mem' := by
    intro m hm
    simp only [Finsupp.support_zero, Finset.notMem_empty] at hm
  smul_mem' c P hP := by
    intro m hm
    exact hP m (Finsupp.support_smul hm)

theorem mem_friableSpace_iff {S : Finset Nat.Primes} {d : ℕ}
    {P : (Nat.Primes →₀ ℕ) →₀ ℂ} :
    P ∈ friableSpace S d ↔ ∀ m ∈ P.support, m.support ⊆ S ∧ (m.sum fun _ k => k) ≤ d :=
  Iff.rfl

/-- Every member of `𝒜_{S,d}` satisfies the collected edge identity: its `T`-th derivative at the
arithmetic edge is a linear form in the degree-`T` prime-log monomials. -/
theorem iteratedDeriv_at_one_collected_of_mem_friableSpace
    {S : Finset Nat.Primes} {d : ℕ} (T : ℕ) {P : (Nat.Primes →₀ ℕ) →₀ ℂ}
    (hP : P ∈ friableSpace S d) :
    iteratedDeriv T (fun z : ℂ => friableExponentDirichletExp P z) 1 =
      (-1 : ℂ) ^ T *
        ∑ a ∈ Finset.piAntidiag S T,
          (((Nat.multinomial S a : ℕ) : ℂ) *
            (P.sum fun m c =>
              c * (∏ p ∈ S, ((m p : ℕ) : ℂ) ^ (a p)) * ((primeProduct m : ℕ) : ℂ)⁻¹)) *
            (∏ p ∈ S, ((Real.log (p : ℕ) : ℂ)) ^ (a p)) :=
  iteratedDeriv_friableExponentDirichletExp_at_one_collected S T P
    (fun m hm => (mem_friableSpace_iff.mp hP m hm).1)

end GaloisForLFunctions
