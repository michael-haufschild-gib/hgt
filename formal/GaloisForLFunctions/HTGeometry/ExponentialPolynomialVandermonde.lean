import Mathlib

/-!
# Exponential sums with polynomial coefficients

An identity `∑ᵢ pᵢ(m) · zᵢ^m = 0` holding for every `m ≥ 1`, with pairwise distinct nonzero nodes
`zᵢ` and polynomial coefficients `pᵢ`, forces every `pᵢ` to vanish.

Subtracting `z_a` times the `m`-th equation from the `(m+1)`-st replaces `pᵢ` by
`pᵢ(X+1)·zᵢ − z_a·pᵢ`.  For `i ≠ a` this has the same degree, because its leading coefficient is
scaled by `zᵢ − z_a ≠ 0`; for `i = a` the leading terms cancel and the degree drops.  So the total
weight `∑ᵢ (deg pᵢ + 1)`, counting the zero polynomial as weight zero, strictly decreases, which
drives the induction.  This is the coefficient-polynomial refinement of the Vandermonde separation
of distinct nodes.

* `polyWeight` — the weight of a coefficient polynomial;
* `expPolySum_eq_zero` — the separation theorem.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The weight of a coefficient polynomial: zero for the zero polynomial, `deg + 1` otherwise. -/
noncomputable def polyWeight (p : Polynomial ℂ) : ℕ := if p = 0 then 0 else p.natDegree + 1

theorem polyWeight_eq_zero_iff {p : Polynomial ℂ} : polyWeight p = 0 ↔ p = 0 := by
  rw [polyWeight]
  by_cases h : p = 0 <;> simp [h]

/-- The shifted difference used by the induction. -/
noncomputable def vandermondeStep (p : Polynomial ℂ) (zi za : ℂ) : Polynomial ℂ :=
  p.comp (X + C 1) * C zi - C za * p

theorem eval_vandermondeStep (p : Polynomial ℂ) (zi za x : ℂ) :
    (vandermondeStep p zi za).eval x = p.eval (x + 1) * zi - za * p.eval x := by
  rw [vandermondeStep]
  simp [eval_comp]

theorem natDegree_comp_X_add_one (p : Polynomial ℂ) :
    (p.comp (X + C 1)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

theorem leadingCoeff_comp_X_add_one' (p : Polynomial ℂ) :
    (p.comp (X + C 1)).leadingCoeff = p.leadingCoeff := by
  rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero),
    leadingCoeff_X_add_C, one_pow, mul_one]

/-- Off the distinguished node the weight is unchanged. -/
theorem polyWeight_vandermondeStep_of_ne {p : Polynomial ℂ} {zi za : ℂ}
    (hz : zi ≠ za) (_hzi : zi ≠ 0) : polyWeight (vandermondeStep p zi za) = polyWeight p := by
  by_cases hp : p = 0
  · rw [vandermondeStep, hp]
    simp [polyWeight]
  have hlead : (vandermondeStep p zi za).coeff p.natDegree = p.leadingCoeff * (zi - za) := by
    rw [vandermondeStep, coeff_sub, coeff_mul_C, coeff_C_mul,
      ← natDegree_comp_X_add_one p, ← leadingCoeff, leadingCoeff_comp_X_add_one']
    rw [natDegree_comp_X_add_one]
    rw [leadingCoeff]
    ring
  have hne : (vandermondeStep p zi za).coeff p.natDegree ≠ 0 := by
    rw [hlead]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp) (sub_ne_zero.mpr hz)
  have hQne : vandermondeStep p zi za ≠ 0 := fun h => hne (by rw [h, coeff_zero])
  have hle : (vandermondeStep p zi za).natDegree ≤ p.natDegree := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
    rw [vandermondeStep, coeff_sub, coeff_mul_C, coeff_C_mul]
    have h1 : (p.comp (X + C 1)).coeff n = 0 := by
      refine coeff_eq_zero_of_natDegree_lt ?_
      rw [natDegree_comp_X_add_one]
      exact hn
    have h2 : p.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hn
    rw [h1, h2]
    ring
  have hge : p.natDegree ≤ (vandermondeStep p zi za).natDegree :=
    le_natDegree_of_ne_zero hne
  rw [polyWeight, polyWeight, if_neg hQne, if_neg hp, le_antisymm hle hge]

/-- At the distinguished node the weight strictly drops. -/
theorem polyWeight_vandermondeStep_self_lt {p : Polynomial ℂ} {za : ℂ}
    (hp : p ≠ 0) (hza : za ≠ 0) :
    polyWeight (vandermondeStep p za za) < polyWeight p := by
  have hstep : vandermondeStep p za za = C za * (p.comp (X + C 1) - p) := by
    rw [vandermondeStep]
    ring
  have hcompne : p.comp (X + C 1) ≠ 0 :=
    leadingCoeff_ne_zero.mp (by
      rw [leadingCoeff_comp_X_add_one']
      exact leadingCoeff_ne_zero.mpr hp)
  by_cases hdiff : p.comp (X + C 1) - p = 0
  · rw [hstep, hdiff, mul_zero, polyWeight, if_pos rfl, polyWeight, if_neg hp]
    omega
  have hdegeq : (p.comp (X + C 1)).degree = p.degree := by
    rw [degree_eq_natDegree hcompne, degree_eq_natDegree hp, natDegree_comp_X_add_one]
  have hdeg : (p.comp (X + C 1) - p).degree < p.degree := by
    have := degree_sub_lt hdegeq hcompne (leadingCoeff_comp_X_add_one' p)
    rwa [hdegeq] at this
  have hnat : (p.comp (X + C 1) - p).natDegree < p.natDegree :=
    natDegree_lt_natDegree hdiff hdeg
  have hQ : vandermondeStep p za za ≠ 0 := by
    rw [hstep]
    exact mul_ne_zero (by simpa using hza) hdiff
  rw [hstep] at hQ ⊢
  rw [polyWeight, polyWeight, if_neg hQ, if_neg hp, natDegree_C_mul (by simpa using hza)]
  omega

/-- **Distinct nonzero nodes separate polynomial coefficients.** -/
theorem expPolySum_eq_zero_aux {ι : Type*} [DecidableEq ι] (z : ι → ℂ) (S : Finset ι)
    (hinj : Set.InjOn z ↑S) (hz0 : ∀ i ∈ S, z i ≠ 0) :
    ∀ N : ℕ, ∀ p : ι → Polynomial ℂ, (∑ i ∈ S, polyWeight (p i)) ≤ N →
      (∀ m : ℕ, 1 ≤ m → ∑ i ∈ S, (p i).eval (m : ℂ) * z i ^ m = 0) →
      ∀ i ∈ S, p i = 0 := by
  intro N
  induction N with
  | zero =>
    intro p hsum _ i hi
    have hzero : polyWeight (p i) = 0 := by
      have := Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hsum)
      exact this i hi
    exact polyWeight_eq_zero_iff.mp hzero
  | succ N ih =>
    intro p hsum heq i hi
    by_cases hall : ∀ j ∈ S, p j = 0
    · exact hall i hi
    obtain ⟨a, ha, hpa⟩ : ∃ a ∈ S, p a ≠ 0 := by
      by_contra hcon
      refine hall fun j hj => ?_
      by_contra hpj
      exact hcon ⟨j, hj, hpj⟩
    set q : ι → Polynomial ℂ := fun j => vandermondeStep (p j) (z j) (z a) with hq
    have hqeq : ∀ m : ℕ, 1 ≤ m → ∑ j ∈ S, (q j).eval (m : ℂ) * z j ^ m = 0 := by
      intro m hm
      have h1 := heq (m + 1) (by omega)
      have h2 := heq m hm
      have hexp : ∑ j ∈ S, (q j).eval (m : ℂ) * z j ^ m
          = (∑ j ∈ S, (p j).eval ((m : ℂ) + 1) * z j ^ (m + 1))
            - z a * ∑ j ∈ S, (p j).eval (m : ℂ) * z j ^ m := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hq, eval_vandermondeStep]
        ring
      have hcast : ∑ j ∈ S, (p j).eval ((m : ℂ) + 1) * z j ^ (m + 1) = 0 := by
        have : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
        rw [← this]
        exact h1
      rw [hexp, hcast, h2]
      ring
    have hweight : (∑ j ∈ S, polyWeight (q j)) ≤ N := by
      have hsplit : (∑ j ∈ S, polyWeight (q j))
          = polyWeight (q a) + ∑ j ∈ S.erase a, polyWeight (q j) :=
        (Finset.add_sum_erase S _ ha).symm
      have hsplit' : (∑ j ∈ S, polyWeight (p j))
          = polyWeight (p a) + ∑ j ∈ S.erase a, polyWeight (p j) :=
        (Finset.add_sum_erase S _ ha).symm
      have hrest : ∑ j ∈ S.erase a, polyWeight (q j) = ∑ j ∈ S.erase a, polyWeight (p j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        obtain ⟨hja, hjS⟩ := Finset.mem_erase.mp hj
        rw [hq]
        exact polyWeight_vandermondeStep_of_ne
          (fun hzz => hja (hinj (Finset.mem_coe.mpr hjS) (Finset.mem_coe.mpr ha) hzz))
          (hz0 j hjS)
      have hlt : polyWeight (q a) < polyWeight (p a) := by
        rw [hq]
        exact polyWeight_vandermondeStep_self_lt hpa (hz0 a ha)
      rw [hsplit, hrest]
      rw [hsplit'] at hsum
      omega
    have hqzero := ih q hweight hqeq
    have hpzero : ∀ j ∈ S, j ≠ a → p j = 0 := by
      intro j hj hja
      have hq0 : vandermondeStep (p j) (z j) (z a) = 0 := hqzero j hj
      by_contra hpj
      have := polyWeight_vandermondeStep_of_ne
        (fun hzz => hja (hinj (Finset.mem_coe.mpr hj) (Finset.mem_coe.mpr ha) hzz))
        (hz0 j hj) (p := p j)
      rw [hq0, polyWeight, if_pos rfl, polyWeight, if_neg hpj] at this
      omega
    have hpa0 : p a = 0 := by
      have hroots : ∀ m : ℕ, 1 ≤ m → (p a).eval (m : ℂ) = 0 := by
        intro m hm
        have hsum0 := heq m hm
        have honly : ∑ j ∈ S, (p j).eval (m : ℂ) * z j ^ m
            = (p a).eval (m : ℂ) * z a ^ m := by
          rw [← Finset.add_sum_erase S _ ha]
          have : ∑ j ∈ S.erase a, (p j).eval (m : ℂ) * z j ^ m = 0 := by
            refine Finset.sum_eq_zero fun j hj => ?_
            obtain ⟨hja, hjS⟩ := Finset.mem_erase.mp hj
            rw [hpzero j hjS hja]
            simp
          rw [this, add_zero]
        rw [honly] at hsum0
        rcases mul_eq_zero.mp hsum0 with h | h
        · exact h
        · exact absurd h (pow_ne_zero _ (hz0 a ha))
      refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
      have hinjmap : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℂ)) := by
        intro n1 n2 h
        have h' : ((n1 + 1 : ℕ) : ℂ) = ((n2 + 1 : ℕ) : ℂ) := h
        have hcast : (n1 + 1 : ℕ) = (n2 + 1 : ℕ) := by exact_mod_cast h'
        omega
      have hsubset : Set.range (fun n : ℕ => ((n + 1 : ℕ) : ℂ))
          ⊆ {x : ℂ | (p a).IsRoot x} := by
        rintro x ⟨n, rfl⟩
        exact hroots (n + 1) (by omega)
      exact Set.Infinite.mono hsubset (Set.infinite_range_of_injective hinjmap)
    by_cases hia : i = a
    · rw [hia]; exact hpa0
    · exact hpzero i hi hia

/-- **Distinct nonzero nodes separate polynomial coefficients.** -/
theorem expPolySum_eq_zero {ι : Type*} [DecidableEq ι] (z : ι → ℂ) (S : Finset ι)
    (hinj : Set.InjOn z ↑S) (hz0 : ∀ i ∈ S, z i ≠ 0) (p : ι → Polynomial ℂ)
    (heq : ∀ m : ℕ, 1 ≤ m → ∑ i ∈ S, (p i).eval (m : ℂ) * z i ^ m = 0) :
    ∀ i ∈ S, p i = 0 :=
  expPolySum_eq_zero_aux z S hinj hz0 (∑ i ∈ S, polyWeight (p i)) p le_rfl heq

end GaloisForLFunctions.HTGeometry
