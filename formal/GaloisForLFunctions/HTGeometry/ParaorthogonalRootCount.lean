import GaloisForLFunctions.HTGeometry.ParaorthogonalBlaschkeRoot
import GaloisForLFunctions.HTGeometry.FiniteOPUCRootLocation

/-!
# The paraorthogonal root set is full

Paraorthogonal root location says that *if* `z` is a root of `X · p - τ · conj(p)ᵣₑᵥ` and the roots
of `p` lie in the open disk, then `‖z‖ = 1`.  Nothing says such a root exists, so the statement is
compatible with there being none.  It is not: the terminal closure raises the degree by exactly one,
because reversal cannot increase the degree, so the polynomial splits into `deg p + 1` linear
factors and every one of them is unimodular.

* `natDegree_finiteParaorthogonalPolynomial`, `finiteParaorthogonalPolynomial_ne_zero`;
* `exists_isRoot_finiteParaorthogonalPolynomial`;
* **`finiteParaorthogonalPolynomial_roots_on_unitCircle`** — exactly `deg p + 1` roots, all on the
  unit circle;
* **`finiteOPUCParaorthogonalPolynomial_roots_on_unitCircle`** — the same for the terminal polynomial
  of a positive definite Toeplitz section, where the count is `N + 1`.
-/

open Polynomial
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry

variable {p : ℂ[X]} {τ : ℂ}

/-- The terminal closure raises the degree by exactly one: multiplication by `X` adds one, and the
reversed conjugate summand cannot reach that degree. -/
theorem natDegree_finiteParaorthogonalPolynomial (hp : p ≠ 0) (τ : ℂ) :
    (finiteParaorthogonalPolynomial p τ).natDegree = p.natDegree + 1 := by
  have hmap : (p.map (starRingEnd ℂ)).natDegree = p.natDegree :=
    natDegree_map_eq_of_injective (starRingEnd ℂ).injective p
  have hXp : (X * p).natDegree = p.natDegree + 1 := natDegree_X_mul hp
  have hlt : (C τ * (p.map (starRingEnd ℂ)).reverse).natDegree < (X * p).natDegree := by
    rw [hXp]
    calc (C τ * (p.map (starRingEnd ℂ)).reverse).natDegree
        ≤ (p.map (starRingEnd ℂ)).reverse.natDegree := natDegree_C_mul_le _ _
      _ ≤ (p.map (starRingEnd ℂ)).natDegree := reverse_natDegree_le _
      _ = p.natDegree := hmap
      _ < p.natDegree + 1 := Nat.lt_succ_self _
  show (X * p - C τ * (p.map (starRingEnd ℂ)).reverse).natDegree = p.natDegree + 1
  rw [natDegree_sub_eq_left_of_natDegree_lt hlt, natDegree_X_mul hp]

theorem finiteParaorthogonalPolynomial_ne_zero (hp : p ≠ 0) (τ : ℂ) :
    finiteParaorthogonalPolynomial p τ ≠ 0 := by
  intro h
  have := natDegree_finiteParaorthogonalPolynomial hp τ
  rw [h, natDegree_zero] at this
  exact absurd this.symm (Nat.succ_ne_zero _)

/-- The terminal closure always has a root. -/
theorem exists_isRoot_finiteParaorthogonalPolynomial (hp : p ≠ 0) (τ : ℂ) :
    ∃ z, (finiteParaorthogonalPolynomial p τ).IsRoot z := by
  refine Complex.exists_root (natDegree_pos_iff_degree_pos.mp ?_)
  rw [natDegree_finiteParaorthogonalPolynomial hp τ]
  exact Nat.succ_pos _

/-- The root multiset of the terminal closure has full length. -/
theorem card_roots_finiteParaorthogonalPolynomial (hp : p ≠ 0) (τ : ℂ) :
    Multiset.card (finiteParaorthogonalPolynomial p τ).roots = p.natDegree + 1 :=
  ((IsAlgClosed.splits _).natDegree_eq_card_roots).symm.trans
    (natDegree_finiteParaorthogonalPolynomial hp τ)

/-- **The paraorthogonal root set is full and unimodular.**  For a polynomial with all roots in the
open disk and a unimodular terminal parameter, the terminal closure has exactly `deg p + 1` roots
with multiplicity, and every one of them lies on the unit circle. -/
theorem finiteParaorthogonalPolynomial_roots_on_unitCircle (hp : p ≠ 0)
    (hroots : ∀ a ∈ p.roots, ‖a‖ < 1) (hτ : ‖τ‖ = 1) :
    Multiset.card (finiteParaorthogonalPolynomial p τ).roots = p.natDegree + 1 ∧
      ∀ z ∈ (finiteParaorthogonalPolynomial p τ).roots, ‖z‖ = 1 := by
  refine ⟨card_roots_finiteParaorthogonalPolynomial hp τ, fun z hz => ?_⟩
  exact finiteParaorthogonalPolynomial_isRoot_norm_eq_one hp hroots hτ
    ((mem_roots (finiteParaorthogonalPolynomial_ne_zero hp τ)).mp hz)

/-- The finite OPUC polynomial is nonzero: its top coefficient is the last entry of the OPUC
vector. -/
theorem finiteOPUCPolynomial_ne_zero {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) : finiteOPUCPolynomial c hG ≠ 0 := by
  have hcoeff : (finiteOPUCPolynomial c hG).coeff N ≠ 0 := by
    simpa [finiteOPUCPolynomial] using finiteOPUCVector_last_ne_zero c hG
  intro hp0
  apply hcoeff
  rw [hp0]
  simp

theorem finiteOPUCPolynomial_roots_norm_lt_one {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    ∀ a ∈ (finiteOPUCPolynomial c hG).roots, ‖a‖ < 1 := fun _ ha =>
  finiteOPUCPolynomial_isRoot_norm_lt_one c hG ((mem_roots (finiteOPUCPolynomial_ne_zero c hG)).mp ha)

/-- **The finite OPUC terminal polynomial splits on the unit circle.**  A positive definite Toeplitz
section of level `N` yields exactly `N + 1` paraorthogonal roots, all unimodular. -/
theorem finiteOPUCParaorthogonalPolynomial_roots_on_unitCircle {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (hτ : ‖τ‖ = 1) :
    Multiset.card
        (finiteParaorthogonalPolynomial (finiteOPUCPolynomial c hG) τ).roots = N + 1 ∧
      ∀ z ∈ (finiteParaorthogonalPolynomial (finiteOPUCPolynomial c hG) τ).roots, ‖z‖ = 1 := by
  have hdeg : (finiteOPUCPolynomial c hG).natDegree = N := finiteOPUCPolynomial_natDegree c hG
  obtain ⟨hcard, hall⟩ := finiteParaorthogonalPolynomial_roots_on_unitCircle
    (finiteOPUCPolynomial_ne_zero c hG) (finiteOPUCPolynomial_roots_norm_lt_one c hG) hτ
  exact ⟨by rw [hcard, hdeg], hall⟩

end GaloisForLFunctions.HTGeometry
