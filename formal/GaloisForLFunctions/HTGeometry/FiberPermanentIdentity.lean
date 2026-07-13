import GaloisForLFunctions.HTGeometry.MagnitudeDistinctSurvival
import GaloisForLFunctions.HTGeometry.PermanentCoefficientIdentity

/-!
# The fiber-permanent identity

For a single differential monomial `∏ₜ f^{(μ t)}` and an injective scale tuple `s` whose every entry
dominates every derivative order (`∀ i t, μ t ≤ s i`), the grouped integer weight `w_{key s}` — the
sum of `∏ₜ (l t + μ t).descFactorial (μ t)` over the antidiagonal fiber `{l : key (l + μ) = key s}` —
equals the **permanent** `∑_{π} ∏ₜ (s (π t)).descFactorial (μ t)` over all permutations of the
coordinates.  The fiber is in bijection with the symmetric group: `key (l + μ) = key s` forces
`l + μ` to be a rearrangement of `s` (equal index-multisets), and injectivity of `s` makes the
rearranging permutation unique.  This is the constant-derivative-order specialisation of the
distinct-index permanent identity, with no super-increasing hypothesis on the scales.
-/

open Finset PowerSeries

namespace GaloisForLFunctions

/-- The index-multiset `key g` reads off the multiplicity of each value: `key g n` is the number of
coordinates of `g` equal to `n`, i.e. the `Multiset.count` of `n` in the image multiset of `g`. -/
theorem key_count_map {D : ℕ} (g : Fin D → ℕ) (n : ℕ) :
    key g n = Multiset.count n (Multiset.map g Finset.univ.val) := by
  rw [key]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val, Finset.card_filter]
  simp only [eq_comm]

/-- **Fiber-permanent identity.**  The antidiagonal fiber weight over `{l : key (l + μ) = key s}`
equals the coordinate permanent `∑_π ∏ₜ (s (π t)).descFactorial (μ t)`, for injective scales `s`
dominating all orders `μ`. -/
theorem fiber_perm_single {D : ℕ} (s : Fin D → ℕ) (hs : Function.Injective s)
    (μ : Fin D → ℕ) (hsμ : ∀ i t, μ t ≤ s i) :
    ∑ l ∈ (Finset.univ.finsuppAntidiag (∑ t, (s t - μ t))).filter
        (fun l => key (fun t => l t + μ t) = key s),
      ∏ t, ((l t + μ t).descFactorial (μ t) : ℤ)
      = ∑ π : Equiv.Perm (Fin D), ∏ t, ((s (π t)).descFactorial (μ t) : ℤ) := by
  classical
  set lof : Equiv.Perm (Fin D) → (Fin D →₀ ℕ) :=
    fun π => Finsupp.onFinset Finset.univ (fun t => s (π t) - μ t) (fun _ _ => Finset.mem_univ _)
    with hlof
  have hlofapp : ∀ π t, lof π t = s (π t) - μ t := fun π t => by
    simp only [hlof, Finsupp.onFinset_apply]
  have hlofsrc : ∀ π t, lof π t + μ t = s (π t) := fun π t => by
    rw [hlofapp]; exact Nat.sub_add_cancel (hsμ (π t) t)
  set F := (Finset.univ.finsuppAntidiag (∑ t, (s t - μ t))).filter
      (fun l => key (fun t => l t + μ t) = key s) with hF
  have hmem : ∀ π, lof π ∈ F := by
    intro π
    rw [hF, Finset.mem_filter, Finset.mem_finsuppAntidiag]
    refine ⟨⟨?_, Finsupp.support_onFinset_subset⟩, ?_⟩
    · show Finset.univ.sum (lof π) = ∑ t, (s t - μ t)
      have css : ∀ (a : Fin D → ℕ), (∀ t, μ t ≤ a t) →
          ((∑ t, (a t - μ t) : ℕ) : ℤ) = (∑ t, (a t : ℤ)) - ∑ t, (μ t : ℤ) := by
        intro a ha
        rw [Nat.cast_sum, show (∑ t, ((a t - μ t : ℕ) : ℤ)) = ∑ t, ((a t : ℤ) - μ t) from
              Finset.sum_congr rfl (fun t _ => Nat.cast_sub (ha t)), Finset.sum_sub_distrib]
      have h1 : Finset.univ.sum (lof π) = ∑ t, (s (π t) - μ t) :=
        Finset.sum_congr rfl (fun t _ => hlofapp π t)
      have e3 : (∑ t, (s (π t) : ℤ)) = ∑ t, (s t : ℤ) := Equiv.sum_comp π (fun i => (s i : ℤ))
      rw [h1]
      refine Nat.cast_inj (R := ℤ) |>.mp ?_
      rw [css (fun t => s (π t)) (fun t => hsμ (π t) t), css s (fun t => hsμ t t), e3]
    · simp only [key]
      rw [Finset.sum_congr rfl (fun t _ => by rw [hlofsrc])]
      exact Equiv.sum_comp π (fun i => Finsupp.single (s i) 1)
  have hback : ∀ l ∈ F, ∃ π : Equiv.Perm (Fin D), ∀ t, l t + μ t = s (π t) := by
    intro l hl
    rw [hF, Finset.mem_filter] at hl
    have hkeys : Multiset.map (fun t => l t + μ t) Finset.univ.val
        = Multiset.map s Finset.univ.val := by
      apply Multiset.ext.mpr
      intro n
      rw [← key_count_map, ← key_count_map, hl.2]
    exact exists_perm_of_map_eq (fun t => l t + μ t) s hs hkeys
  refine (Finset.sum_bij' (fun π _ => lof π) (fun l hl => (hback l hl).choose) ?_ ?_ ?_ ?_ ?_).symm
  · intro π _; exact hmem π
  · intro l _; exact Finset.mem_univ _
  · intro π _
    have hσ := (hback (lof π) (hmem π)).choose_spec
    apply Equiv.ext; intro t
    exact hs ((hσ t).symm.trans (hlofsrc π t))
  · intro l hl
    have hσ := (hback l hl).choose_spec
    ext t
    rw [hlofapp, ← hσ t]; omega
  · intro π _
    exact Finset.prod_congr rfl (fun t _ => by rw [hlofsrc])

theorem perm_descFactorial_sum_pos {D : ℕ} (s : Fin D → ℕ) (μ : Fin D → ℕ)
    (hsμ : ∀ i t, μ t ≤ s i) :
    0 < ∑ π : Equiv.Perm (Fin D), ∏ t, ((s (π t)).descFactorial (μ t) : ℤ) := by
  apply Finset.sum_pos
  · intro π _
    apply Finset.prod_pos
    intro t _
    exact_mod_cast Nat.descFactorial_pos.mpr (hsμ (π t) t)
  · exact Finset.univ_nonempty

/-- The antidiagonal-fiber weight of a single differential monomial at an injective, order-dominating
scale is strictly positive: it equals the coordinate permanent (`fiber_perm_single`), a sum of
positive descending-factorial products. -/
theorem fiber_weight_pos {D : ℕ} (s : Fin D → ℕ) (hs : Function.Injective s)
    (μ : Fin D → ℕ) (hsμ : ∀ i t, μ t ≤ s i) :
    0 < ∑ l ∈ (Finset.univ.finsuppAntidiag (∑ t, (s t - μ t))).filter
        (fun l => key (fun t => l t + μ t) = key s),
      ∏ t, ((l t + μ t).descFactorial (μ t) : ℤ) := by
  rw [fiber_perm_single s hs μ hsμ]
  exact perm_descFactorial_sum_pos s μ hsμ

/-- Consequently the fiber weight is nonzero — the `w_ν ≠ 0` input feeding the minimal-valuation
domination in the magnitude-lacunary survival argument. -/
theorem fiber_weight_ne_zero {D : ℕ} (s : Fin D → ℕ) (hs : Function.Injective s)
    (μ : Fin D → ℕ) (hsμ : ∀ i t, μ t ≤ s i) :
    (∑ l ∈ (Finset.univ.finsuppAntidiag (∑ t, (s t - μ t))).filter
        (fun l => key (fun t => l t + μ t) = key s),
      ∏ t, ((l t + μ t).descFactorial (μ t) : ℤ)) ≠ 0 :=
  ne_of_gt (fiber_weight_pos s hs μ hsμ)

/-- When the atom `ν₀` has a singleton fiber `{p₀}` with nonzero coefficient, its grouped weight
is `c(p₀.1)·∏ descFactorial ≠ 0` — every derivative order is `≤` its shifted index. -/
theorem weight_singleton_ne_zero {D : ℕ} (N : ℕ) (S : Finset (Fin D → ℕ)) (c : (Fin D → ℕ) → ℤ)
    (ν₀ : ℕ →₀ ℕ) (p₀ : (Fin D → ℕ) × (Fin D →₀ ℕ))
    (hfiber : (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀) = {p₀})
    (hc : c p₀.1 ≠ 0) :
    (∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀),
      c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℤ)) ≠ 0 := by
  rw [hfiber, Finset.sum_singleton]
  refine mul_ne_zero hc ?_
  refine Finset.prod_ne_zero_iff.mpr (fun t _ => ?_)
  have hpos : 0 < (p₀.2 t + p₀.1 t).descFactorial (p₀.1 t) :=
    Nat.descFactorial_pos.mpr (Nat.le_add_left _ _)
  exact_mod_cast hpos.ne'

/-- Two tuples have equal index-multiset `key` iff equal image multisets. -/
theorem key_eq_iff_multiset {D : ℕ} (h h' : Fin D → ℕ) :
    key h = key h' ↔ Multiset.map h Finset.univ.val = Multiset.map h' Finset.univ.val := by
  constructor
  · intro hk; apply Multiset.ext.mpr; intro n; rw [← key_count_map, ← key_count_map, hk]
  · intro hm; ext n; rw [key_count_map, key_count_map, hm]

/-- Complex singleton-fiber weight: nonzero when the coefficient is nonzero. -/
theorem weight_singleton_ne_zero_complex {D : ℕ} (N : ℕ) (S : Finset (Fin D → ℕ))
    (c : (Fin D → ℕ) → ℂ) (ν₀ : ℕ →₀ ℕ) (p₀ : (Fin D → ℕ) × (Fin D →₀ ℕ))
    (hfiber : (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀) = {p₀})
    (hc : c p₀.1 ≠ 0) :
    (∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀),
      c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℂ)) ≠ 0 := by
  rw [hfiber, Finset.sum_singleton]
  refine mul_ne_zero hc ?_
  refine Finset.prod_ne_zero_iff.mpr (fun t _ => ?_)
  have hpos : 0 < (p₀.2 t + p₀.1 t).descFactorial (p₀.1 t) :=
    Nat.descFactorial_pos.mpr (Nat.le_add_left _ _)
  exact_mod_cast hpos.ne'

/-- **Single-derivative-order fiber weight.**  When every `(μ,l)` in an atom's fiber shares the
same order multi-index `μ₀` with nonzero coefficient, the weight `c μ₀ · ∑ ∏ descFactorial` is
nonzero. -/
theorem weight_single_mu_ne_zero_complex {D : ℕ} (N : ℕ) (S : Finset (Fin D → ℕ))
    (c : (Fin D → ℕ) → ℂ) (ν₀ : ℕ →₀ ℕ) (μ₀ : Fin D → ℕ)
    (hsingle : ∀ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀), p.1 = μ₀)
    (hne : ((S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀)).Nonempty)
    (hc : c μ₀ ≠ 0) :
    (∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀),
      c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℂ)) ≠ 0 := by
  classical
  have hEq : (∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀),
      c p.1 * ∏ t, ((p.2 t + p.1 t).descFactorial (p.1 t) : ℂ))
      = c μ₀ * ∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀),
        ∏ t, ((p.2 t + p.1 t).descFactorial (μ₀ t) : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => by rw [hsingle p hp])
  rw [hEq]
  refine mul_ne_zero hc ?_
  have hR : (∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀),
      ∏ t, ((p.2 t + p.1 t).descFactorial (μ₀ t) : ℂ))
      = (((∑ p ∈ (S ×ˢ (Finset.univ.finsuppAntidiag N)).filter
        (fun p => key (fun t => p.2 t + p.1 t) = ν₀),
      ∏ t, ((p.2 t + p.1 t).descFactorial (μ₀ t) : ℝ)) : ℝ) : ℂ) := by push_cast; rfl
  rw [hR]
  refine Complex.ofReal_ne_zero.mpr (ne_of_gt ?_)
  apply Finset.sum_pos
  · intro p hp
    apply Finset.prod_pos
    intro t _
    have hp2 : 0 < (p.2 t + p.1 t).descFactorial (μ₀ t) :=
      Nat.descFactorial_pos.mpr (by rw [← hsingle p hp]; exact Nat.le_add_left _ _)
    exact_mod_cast hp2
  · exact hne

end GaloisForLFunctions
