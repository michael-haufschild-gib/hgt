import GaloisForLFunctions.HTGeometry.MonomialValuation
import GaloisForLFunctions.HTGeometry.CohenMacaulayDepth

/-!
# Coordinate primes and the nonzerodivisor criterion for a Stanley–Reisner ring

Two ingredients of the Stanley–Reisner side of the Hankel degeneration.

First, the **coordinate ideal** `(X i : i ∈ T)` is prime.  The proof reuses the monomial valuation:
the `{0,1}`-weight of the chosen coordinates is additive on products (`minWeight_mul`), membership
in the ideal is exactly positivity of that weight on every monomial, and a product of two
polynomials each having a weight-zero monomial again has one.

Second, if an ideal is a **finite intersection of primes** — which is what
`stanleyReisnerIdeal_eq_inf_facetIdeal` supplies for a Stanley–Reisner ideal, the primes being the
coordinate ideals complementary to the facets — then an element lying outside every one of them is
a nonzerodivisor modulo it.  This is three lines and needs no primary decomposition.

```text
isPrime_span_X_image                the coordinate ideal is prime
isRegularOn_of_notMem_inf_primes    ** the nonzerodivisor criterion **
```

Together they say: a linear form whose support meets every facet is a nonzerodivisor on the
Stanley–Reisner ring — the first step of a regular sequence on the Hankel degeneration.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- The `{0,1}`-weight of a set of coordinates. -/
def coordinateWeight (T : Set σ) [DecidablePred (· ∈ T)] : σ → ℤ :=
  fun i => if i ∈ T then 1 else 0

theorem coordinateWeight_nonneg (T : Set σ) [DecidablePred (· ∈ T)] (e : σ →₀ ℕ) :
    0 ≤ Finsupp.weight (coordinateWeight T) e := by
  classical
  rw [Finsupp.weight_apply]
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [coordinateWeight, nsmul_eq_mul]
  positivity

theorem coordinateWeight_eq_zero_iff (T : Set σ) [DecidablePred (· ∈ T)] (e : σ →₀ ℕ) :
    Finsupp.weight (coordinateWeight T) e = 0 ↔ ∀ i ∈ T, e i = 0 := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by
    simp only [coordinateWeight, nsmul_eq_mul]; positivity)]
  constructor
  · intro h i hi
    by_contra hne
    have hmem : i ∈ e.support := Finsupp.mem_support_iff.mpr hne
    have := h i hmem
    simp only [coordinateWeight, if_pos hi, nsmul_eq_mul, mul_one] at this
    exact hne (by exact_mod_cast this)
  · intro h i hi
    by_cases hiT : i ∈ T
    · have := h i hiT
      simp [coordinateWeight, hiT, this]
    · simp [coordinateWeight, hiT]

theorem mem_span_X_image_iff_zero_lt_weight {T : Set σ} [DecidablePred (· ∈ T)]
    {p : MvPolynomial σ K} :
    p ∈ Ideal.span (MvPolynomial.X '' T : Set (MvPolynomial σ K)) ↔
      ∀ e ∈ p.support, Finsupp.weight (coordinateWeight T) e ≠ 0 := by
  classical
  rw [MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h e he hzero
    obtain ⟨i, hi, hne⟩ := h e he
    exact hne ((coordinateWeight_eq_zero_iff T e).mp hzero i hi)
  · intro h e he
    by_contra hcon
    push Not at hcon
    exact h e he ((coordinateWeight_eq_zero_iff T e).mpr fun i hi => hcon i hi)

/-- **A coordinate ideal is prime.**  The `{0,1}`-weight of the chosen coordinates is a monomial
valuation, so it is additive on products; membership in the ideal is exactly positivity of that
valuation, and positivity is preserved by products. -/
theorem isPrime_span_X_image (T : Set σ) [DecidablePred (· ∈ T)] :
    (Ideal.span (MvPolynomial.X '' T : Set (MvPolynomial σ K))).IsPrime := by
  classical
  set w := coordinateWeight (σ := σ) T with hw
  constructor
  · intro hone
    rw [Ideal.eq_top_iff_one] at hone
    rw [mem_span_X_image_iff_zero_lt_weight] at hone
    have h0 : (0 : σ →₀ ℕ) ∈ (1 : MvPolynomial σ K).support := by
      rw [MvPolynomial.support_one]; simp
    exact hone 0 h0 (by simp)
  · intro x y hxy
    by_contra hcon
    push Not at hcon
    obtain ⟨hx, hy⟩ := hcon
    rw [mem_span_X_image_iff_zero_lt_weight] at hx hy hxy
    push Not at hx hy
    obtain ⟨e, he, hez⟩ := hx
    obtain ⟨f, hf, hfz⟩ := hy
    have hx0 : x ≠ 0 := fun h => by simp [h] at he
    have hy0 : y ≠ 0 := fun h => by simp [h] at hf
    have hmx : minWeight w x = 0 := by
      refine le_antisymm ?_ (le_minWeight hx0 fun g _ => coordinateWeight_nonneg T g)
      rw [← hez]
      exact minWeight_le he
    have hmy : minWeight w y = 0 := by
      refine le_antisymm ?_ (le_minWeight hy0 fun g _ => coordinateWeight_nonneg T g)
      rw [← hfz]
      exact minWeight_le hf
    obtain ⟨g, hg, hgw⟩ :=
      exists_mem_support_weight_eq_minWeight (w := w) (mul_ne_zero hx0 hy0)
    rw [minWeight_mul hx0 hy0, hmx, hmy, add_zero] at hgw
    exact hxy g hg hgw

/-- **A finite intersection of primes gives a nonzerodivisor criterion.**  An element outside every
one of the primes is a nonzerodivisor modulo their intersection. -/
theorem isRegularOn_of_notMem_inf_primes {R : Type*} [CommRing R] {ι : Type*}
    {s : Finset ι} {P : ι → Ideal R} (hP : ∀ i ∈ s, (P i).IsPrime)
    {I : Ideal R} (hI : I = s.inf P) {x : R} (hx : ∀ i ∈ s, x ∉ P i) :
    IsRegularOn I x := by
  classical
  rw [IsRegularOn, mem_nonZeroDivisors_iff]
  have hmem : ∀ y : R, y ∈ I ↔ ∀ i ∈ s, y ∈ P i := by
    intro y
    rw [hI]
    simp [Finset.inf_eq_iInf, Submodule.mem_iInf]
  have key : ∀ y : R, x * y ∈ I → y ∈ I := by
    intro y hy
    rw [hmem] at hy ⊢
    intro i hi
    rcases ((hP i hi).mul_mem_iff_mem_or_mem).mp (hy i hi) with h | h
    · exact absurd h (hx i hi)
    · exact h
  constructor
  · intro z hz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact key y hz
  · intro z hz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact key y (by rwa [mul_comm] at hz)

end GaloisForLFunctions.HTGeometry
