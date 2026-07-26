import GaloisForLFunctions.HTGeometry.EllipticPeriodicMonomial

/-!
# Uniform pole-order bounds over a finite set

The counting argument needs one clearing exponent that works at every pole representative at once.
This file extracts it: `orderBound g S` is the largest pole order of `g` over the finite set `S`,
read off through `WithTop.untopD`, and `neg_orderBound_le` says it is a lower bound for the order at
each point of `S`.

Two features make this painless.  A point where the order is `⊤` costs nothing, because `⊤` is above
every bound, so no finiteness argument is needed; and a point where the order is negative is
automatically not `⊤`, so the pole representatives themselves need no separate treatment.

* `orderBound`, **`neg_orderBound_le`**, `neg_le_meromorphicOrderAt_of_le`;
* **`nonneg_order_finset_sum`** — a finite sum of functions with nonnegative order has nonnegative
  order.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The largest pole order of `g` over a finite set of points. -/
noncomputable def orderBound (g : ℂ → ℂ) (S : Finset ℂ) : ℕ :=
  S.sup (fun p => (-(meromorphicOrderAt g p).untopD 0).toNat)

/-- **The uniform bound works at every point of the set.** -/
theorem neg_orderBound_le (g : ℂ → ℂ) {S : Finset ℂ} {p : ℂ} (hp : p ∈ S) :
    (-(orderBound g S : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt g p := by
  rcases eq_or_ne (meromorphicOrderAt g p) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
    have hle : (-(meromorphicOrderAt g p).untopD 0).toNat ≤ orderBound g S := by
      rw [orderBound]
      exact Finset.le_sup (f := fun q => (-(meromorphicOrderAt g q).untopD 0).toNat) hp
    have huntop : (meromorphicOrderAt g p).untopD 0 = k := by
      rw [← hk]
      simp
    rw [huntop] at hle
    have hk' : -k ≤ ((-k).toNat : ℤ) := Int.self_le_toNat (-k)
    have hcast : ((-k).toNat : ℤ) ≤ (orderBound g S : ℤ) := by exact_mod_cast hle
    have hfin : -(orderBound g S : ℤ) ≤ k := by omega
    rw [← hk]
    exact_mod_cast hfin

/-- A larger bound is still a bound. -/
theorem neg_le_meromorphicOrderAt_of_le {g : ℂ → ℂ} {p : ℂ} {m₁ m₂ : ℕ} (h : m₁ ≤ m₂)
    (hb : (-(m₁ : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt g p) :
    (-(m₂ : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt g p := by
  refine le_trans ?_ hb
  have hint : (-(m₂ : ℤ)) ≤ (-(m₁ : ℤ)) := by
    simp only [neg_le_neg_iff]
    exact_mod_cast h
  exact_mod_cast hint

/-- **A finite sum of functions with nonnegative order has nonnegative order.** -/
theorem nonneg_order_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ) {p : ℂ}
    (hmer : ∀ i ∈ s, MeromorphicAt (g i) p)
    (hord : ∀ i ∈ s, 0 ≤ meromorphicOrderAt (g i) p) :
    0 ≤ meromorphicOrderAt (fun z => ∑ i ∈ s, g i z) p := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hz : (fun z : ℂ => ∑ i ∈ (∅ : Finset ι), g i z) = fun _ => (0 : ℂ) := by
        funext z
        simp
      rw [hz, meromorphicOrderAt_const]
      simp
  | insert a t ha ih =>
      have hA : MeromorphicAt (g a) p := hmer a (Finset.mem_insert_self a t)
      have hT : ∀ i ∈ t, MeromorphicAt (g i) p := fun i hi =>
        hmer i (Finset.mem_insert_of_mem hi)
      have hoT : ∀ i ∈ t, 0 ≤ meromorphicOrderAt (g i) p := fun i hi =>
        hord i (Finset.mem_insert_of_mem hi)
      have hsplit : (fun z : ℂ => ∑ i ∈ insert a t, g i z)
          = g a + fun z : ℂ => ∑ i ∈ t, g i z := by
        funext z
        show ∑ i ∈ insert a t, g i z = g a z + ∑ i ∈ t, g i z
        rw [Finset.sum_insert ha]
      rw [hsplit]
      refine le_trans ?_ (meromorphicOrderAt_add hA (meromorphicAt_finset_sum t g hT))
      exact le_min (hord a (Finset.mem_insert_self a t)) (ih hT hoT)

end GaloisForLFunctions.HTGeometry
