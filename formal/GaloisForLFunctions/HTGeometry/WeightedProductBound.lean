import GaloisForLFunctions.HTGeometry.StandardRationalExpansion

/-!
# Products of weighted approximations

A monomial in the digamma jets is a product of factors of different sizes: the `i`-th jet is of size
`u^{i+1}` with `u = 1/t`, and is approximated to depth `K` with error `u^{i+1+K}`.  Multiplying such
approximations, the error of the product is the *sum of the weights plus the depth* — each error is
multiplied by the other factors, which are themselves small.

A uniform product bound would lose exactly that gain, so the estimate below carries the weights.
-/

open Filter Topology

namespace GaloisForLFunctions

/-- A product of weighted factors is bounded by the total weight. -/
theorem norm_prod_le_mul_pow {ι : Type*} (b : ι → ℂ) (w : ι → ℕ) {A u : ℝ}
    (hA : 1 ≤ A) (hu : 0 ≤ u) :
    ∀ s : Finset ι, (∀ i ∈ s, ‖b i‖ ≤ A * u ^ w i) →
      ‖∏ i ∈ s, b i‖ ≤ A ^ s.card * u ^ (∑ i ∈ s, w i) := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _; simp
  | insert x s hx ih =>
    intro hb
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ A * u ^ w i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hrec := ih hb'
    have hxb := hb x (Finset.mem_insert_self x s)
    rw [Finset.prod_insert hx, norm_mul, Finset.card_insert_of_notMem hx,
      Finset.sum_insert hx]
    have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
    calc ‖b x‖ * ‖∏ i ∈ s, b i‖
        ≤ (A * u ^ w x) * (A ^ s.card * u ^ (∑ i ∈ s, w i)) := by
          refine mul_le_mul hxb hrec (norm_nonneg _) (by positivity)
      _ = A ^ (s.card + 1) * u ^ (w x + ∑ i ∈ s, w i) := by
          rw [pow_succ, pow_add]
          ring

/-- **The weighted product estimate.**  Approximating each factor to depth `K` approximates the
product to the total weight plus `K`. -/
theorem norm_prod_sub_prod_mul_pow_le {ι : Type*} (a b : ι → ℂ) (w : ι → ℕ) {A u : ℝ}
    (hA : 1 ≤ A) (hu0 : 0 ≤ u) (K : ℕ) :
    ∀ s : Finset ι, (∀ i ∈ s, ‖a i‖ ≤ A * u ^ w i) → (∀ i ∈ s, ‖b i‖ ≤ A * u ^ w i) →
      (∀ i ∈ s, ‖a i - b i‖ ≤ A * u ^ (w i + K)) →
      ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ (s.card * A ^ s.card) * u ^ ((∑ i ∈ s, w i) + K) := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _ _ _; simp
  | insert x s hx ih =>
    intro ha hb hd
    have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
    have ha' : ∀ i ∈ s, ‖a i‖ ≤ A * u ^ w i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, ‖b i‖ ≤ A * u ^ w i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ s, ‖a i - b i‖ ≤ A * u ^ (w i + K) :=
      fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hrec := ih ha' hb' hd'
    have hprodb := norm_prod_le_mul_pow b w hA hu0 s hb'
    have hax := ha x (Finset.mem_insert_self x s)
    have hdx := hd x (Finset.mem_insert_self x s)
    have hsplit : (∏ i ∈ insert x s, a i) - ∏ i ∈ insert x s, b i
        = a x * ((∏ i ∈ s, a i) - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i := by
      rw [Finset.prod_insert hx, Finset.prod_insert hx]
      ring
    rw [Finset.card_insert_of_notMem hx, Finset.sum_insert hx]
    have hstep : ‖(∏ i ∈ insert x s, a i) - ∏ i ∈ insert x s, b i‖
        ≤ (A * u ^ w x) * ((s.card * A ^ s.card) * u ^ ((∑ i ∈ s, w i) + K))
          + (A * u ^ (w x + K)) * (A ^ s.card * u ^ (∑ i ∈ s, w i)) := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul]
      refine add_le_add (mul_le_mul hax hrec (norm_nonneg _) (by positivity))
        (mul_le_mul hdx hprodb (norm_nonneg _) (by positivity))
    refine le_trans hstep (le_of_eq ?_)
    have h1 : u ^ ((∑ i ∈ s, w i) + K) = u ^ (∑ i ∈ s, w i) * u ^ K := pow_add u _ _
    have h2 : u ^ (w x + K) = u ^ w x * u ^ K := pow_add u _ _
    have h3 : u ^ (w x + (∑ i ∈ s, w i) + K) = u ^ w x * u ^ (∑ i ∈ s, w i) * u ^ K := by
      rw [pow_add, pow_add]
    rw [h1, h2, h3, pow_succ]
    push_cast
    ring

end GaloisForLFunctions
