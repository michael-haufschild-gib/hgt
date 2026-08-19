import GaloisForLFunctions.HTGeometry.GammaMonomialClearedFactor

/-!
# Linear independence of Gamma monomials

The shift-and-subtract induction.  From a relation `∑_α R_α M_{e_α} = 0` with polynomial
coefficients, shifting by one and eliminating the distinguished index produces a strictly shorter
relation; the induction hypothesis kills its coefficients, and what is left is exactly the
statement that `R_α / R_{α₀}` has the shift ratio `∏_k (s+λ_k)^{e_{α₀,k} - e_{α,k}}`, which
`not_rational_shiftRatio_zpowShiftProd` forbids for distinct exponent vectors.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

theorem eval_comp_X_add_one (p : Polynomial ℂ) (s : ℂ) :
    Polynomial.eval s (p.comp (Polynomial.X + 1)) = Polynomial.eval (s + 1) p := by
  rw [Polynomial.eval_comp]
  simp

/-- The shift-difference coefficient that eliminates the distinguished index. -/
def shiftEliminate (Rz Rα Az Aα : Polynomial ℂ) : Polynomial ℂ :=
  Rz.comp (Polynomial.X + 1) * Az * Rα - Rz * (Rα.comp (Polynomial.X + 1)) * Aα

theorem eval_shiftEliminate (Rz Rα Az Aα : Polynomial ℂ) (s : ℂ) :
    Polynomial.eval s (shiftEliminate Rz Rα Az Aα)
      = Polynomial.eval (s + 1) Rz * Polynomial.eval s Az * Polynomial.eval s Rα
        - Polynomial.eval s Rz * Polynomial.eval (s + 1) Rα * Polynomial.eval s Aα := by
  rw [shiftEliminate]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, eval_comp_X_add_one]

theorem shiftEliminate_self (Rz Az : Polynomial ℂ) : shiftEliminate Rz Rz Az Az = 0 := by
  rw [shiftEliminate]
  ring


theorem polynomial_eq_zero_of_half_plane {R : ℝ} {p : Polynomial ℂ}
    (h : ∀ s : ℂ, R < s.re → Polynomial.eval s p = 0) : p = 0 := by
  refine Polynomial.eq_zero_of_infinite_isRoot p ?_
  have hsub : Set.range (fun t : ℕ => ((R + 1 + (t : ℝ) : ℝ) : ℂ)) ⊆ {x | p.IsRoot x} := by
    rintro _ ⟨t, rfl⟩
    refine h _ ?_
    rw [Complex.ofReal_re]
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  refine Set.Infinite.mono hsub (Set.infinite_range_of_injective ?_)
  intro a b hab
  have hab' : ((R + 1 + (a : ℝ) : ℝ) : ℂ) = ((R + 1 + (b : ℝ) : ℝ) : ℂ) := hab
  have h1 : (R + 1 + (a : ℝ)) = (R + 1 + (b : ℝ)) := by exact_mod_cast hab'
  have h2 : (a : ℝ) = (b : ℝ) := by linarith
  exact_mod_cast h2

/-- **Linear independence of Gamma monomials over the polynomials.** -/
theorem gammaMonomial_linearIndependent_of_threshold {r : ℕ} {ι : Type*} [DecidableEq ι]
    (lam : Fin r → ℂ)
    (hincong : ∀ k k' : Fin r, k ≠ k' → ∀ m : ℤ, lam k - lam k' ≠ (m : ℂ))
    (Rb : ℝ) (hRb : (∑ j, |(lam j).re|) ≤ Rb) :
    ∀ (N : ℕ) (T : Finset ι) (_ : T.card ≤ N) (e : ι → Fin r → ℤ)
      (_ : ∀ α ∈ T, ∀ β ∈ T, α ≠ β → e α ≠ e β) (Rc : ι → Polynomial ℂ)
      (_ : ∀ s : ℂ, Rb < s.re →
        ∑ α ∈ T, Polynomial.eval s (Rc α) * gammaMonomial lam (e α) s = 0),
      ∀ α ∈ T, Rc α = 0 := by
  classical
  intro N
  induction N with
  | zero =>
      intro T hcard e _ Rc _ α hα
      exact absurd (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard) ▸ hα) (by simp)
  | succ N ih =>
      intro T hcard e hdist Rc hid α hα
      by_cases hRz : ∀ β ∈ T, Rc β = 0
      · exact hRz α hα
      push_neg at hRz
      obtain ⟨α₀, hα₀T, hα₀⟩ := hRz
      obtain ⟨m, hm⟩ := exists_clearing_power T e
      set A : ι → Polynomial ℂ := fun β => clearedShiftFactor lam (e β) m with hA
      set C : ι → Polynomial ℂ := fun β => shiftEliminate (Rc α₀) (Rc β) (A α₀) (A β) with hC
      -- the shorter relation
      have hnew : ∀ s : ℂ, Rb < s.re →
          ∑ β ∈ T.erase α₀, Polynomial.eval s (C β) * gammaMonomial lam (e β) s = 0 := by
        intro s hs0
        have hs : (∑ j, |(lam j).re|) < s.re := lt_of_le_of_lt hRb hs0
        have hs1 : Rb < (s + 1).re := by
          rw [Complex.add_re, Complex.one_re]; linarith
        have hlam : ∀ k, s + lam k ≠ 0 := by
          intro k hk
          have := re_pos_of_gt_sum_abs lam hs k
          rw [hk] at this
          simp at this
        have hAeval : ∀ β ∈ T, Polynomial.eval s (A β)
            = (∏ k, (s + lam k) ^ ((m : ℤ))) * (∏ k, (s + lam k) ^ (e β k)) := by
          intro β hβ
          exact eval_clearedShiftFactor lam (e β) m hlam (hm β hβ)
        have h1 := hid (s + 1) hs1
        have h2 := hid s hs0
        have hshift : ∀ β ∈ T, gammaMonomial lam (e β) (s + 1)
            = (∏ k, (s + lam k) ^ (e β k)) * gammaMonomial lam (e β) s :=
          fun β _ => gammaMonomial_shift_of_re lam (e β) hs
        rw [Finset.sum_congr rfl fun β hβ => by rw [hshift β hβ]] at h1
        set X0 : ℂ := Polynomial.eval (s + 1) (Rc α₀) * (∏ k, (s + lam k) ^ ((m : ℤ)))
          * (∏ k, (s + lam k) ^ (e α₀ k)) with hX0
        set Y0 : ℂ := Polynomial.eval s (Rc α₀) * (∏ k, (s + lam k) ^ ((m : ℤ))) with hY0
        have hcomb : ∑ β ∈ T, Polynomial.eval s (C β) * gammaMonomial lam (e β) s
            = X0 * (∑ β ∈ T, Polynomial.eval s (Rc β) * gammaMonomial lam (e β) s)
              - Y0 * (∑ β ∈ T, Polynomial.eval (s + 1) (Rc β)
                * ((∏ k, (s + lam k) ^ (e β k)) * gammaMonomial lam (e β) s)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun β hβ => ?_
          rw [hC]
          simp only []
          rw [eval_shiftEliminate, hAeval α₀ hα₀T, hAeval β hβ, hX0, hY0]
          ring
        rw [h1, h2, mul_zero, mul_zero, sub_zero] at hcomb
        have hzero : Polynomial.eval s (C α₀) = 0 := by
          rw [hC]
          simp only []
          rw [shiftEliminate_self]
          simp
        have hsplit : ∑ β ∈ T.erase α₀, Polynomial.eval s (C β) * gammaMonomial lam (e β) s
            + Polynomial.eval s (C α₀) * gammaMonomial lam (e α₀) s
            = ∑ β ∈ T, Polynomial.eval s (C β) * gammaMonomial lam (e β) s :=
          Finset.sum_erase_add T _ hα₀T
        rw [hzero, zero_mul, add_zero] at hsplit
        rw [hsplit, hcomb]
      have hCzero : ∀ β ∈ T.erase α₀, C β = 0 := by
        refine ih (T.erase α₀) ?_ e ?_ C hnew
        · have := Finset.card_erase_of_mem hα₀T
          omega
        · intro β hβ γ hγ hne
          exact hdist β (Finset.mem_of_mem_erase hβ) γ (Finset.mem_of_mem_erase hγ) hne
      -- every other coefficient vanishes
      have hRrest : ∀ β ∈ T.erase α₀, Rc β = 0 := by
        intro β hβ
        by_contra hRβ
        have hβT : β ∈ T := Finset.mem_of_mem_erase hβ
        have hβne : β ≠ α₀ := Finset.ne_of_mem_erase hβ
        obtain ⟨k₀, hk₀⟩ : ∃ k, e α₀ k ≠ e β k := by
          by_contra hcon
          push_neg at hcon
          exact hdist α₀ hα₀T β hβT (Ne.symm hβne) (funext hcon)
        refine not_rational_shiftRatio_zpowShiftProd lam (fun k => e α₀ k - e β k) hincong k₀
          (by omega) (Rc β) (Rc α₀) hRβ hα₀ ?_
        have hCβ := hCzero β hβ
        rw [Filter.EventuallyEq, Filter.eventually_cofinite]
        refine Set.Finite.subset
          ((((Polynomial.finite_setOf_isRoot hα₀).union
            ((Polynomial.finite_setOf_isRoot hα₀).preimage
              ((add_left_injective (1 : ℂ)).injOn))).union (Set.finite_range
                fun k : Fin r => -lam k))) ?_
        intro s hsmem
        simp only [Set.mem_setOf_eq] at hsmem
        by_contra hcon
        simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage, Polynomial.IsRoot,
          Set.mem_range, not_or, not_exists] at hcon
        obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hcon
        have hlam : ∀ k, s + lam k ≠ 0 := fun k hk => hz3 k (by linear_combination -hk)
        have hAα₀ := eval_clearedShiftFactor lam (e α₀) m hlam (hm α₀ hα₀T)
        have hAβ := eval_clearedShiftFactor lam (e β) m hlam (hm β hβT)
        have hD : (∏ k, (s + lam k) ^ ((m : ℤ))) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hlam k)
        have hrhoβ : (∏ k, (s + lam k) ^ (e β k)) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hlam k)
        have hev := congrArg (Polynomial.eval s) hCβ
        rw [eval_shiftEliminate, hAα₀, hAβ] at hev
        simp only [Polynomial.eval_zero] at hev
        have hratio : (∏ k, (s + lam k) ^ (e α₀ k - e β k))
            = (∏ k, (s + lam k) ^ (e α₀ k)) / (∏ k, (s + lam k) ^ (e β k)) := by
          rw [← Finset.prod_div_distrib]
          exact Finset.prod_congr rfl fun k _ => zpow_sub₀ (hlam k) _ _
        have hcancel : Polynomial.eval (s + 1) (Rc α₀) * (∏ k, (s + lam k) ^ (e α₀ k))
              * Polynomial.eval s (Rc β)
            = Polynomial.eval s (Rc α₀) * Polynomial.eval (s + 1) (Rc β)
              * (∏ k, (s + lam k) ^ (e β k)) := by
          refine mul_left_cancel₀ hD ?_
          have hXY := sub_eq_zero.mp hev
          calc (∏ k, (s + lam k) ^ ((m : ℤ)))
                * ((Polynomial.eval (s + 1) (Rc α₀) * ∏ k, (s + lam k) ^ (e α₀ k))
                  * Polynomial.eval s (Rc β))
              = Polynomial.eval (s + 1) (Rc α₀)
                * ((∏ k, (s + lam k) ^ ((m : ℤ))) * ∏ k, (s + lam k) ^ (e α₀ k))
                * Polynomial.eval s (Rc β) := by ring
            _ = Polynomial.eval s (Rc α₀) * Polynomial.eval (s + 1) (Rc β)
                * ((∏ k, (s + lam k) ^ ((m : ℤ))) * ∏ k, (s + lam k) ^ (e β k)) := hXY
            _ = (∏ k, (s + lam k) ^ ((m : ℤ)))
                * (Polynomial.eval s (Rc α₀) * Polynomial.eval (s + 1) (Rc β)
                  * ∏ k, (s + lam k) ^ (e β k)) := by ring
        refine hsmem ?_
        rw [hratio, div_mul_div_comm,
          div_eq_div_iff hz2 (mul_ne_zero hrhoβ hz1)]
        calc Polynomial.eval (s + 1) (Rc β)
              * ((∏ k, (s + lam k) ^ (e β k)) * Polynomial.eval s (Rc α₀))
            = Polynomial.eval s (Rc α₀) * Polynomial.eval (s + 1) (Rc β)
              * ∏ k, (s + lam k) ^ (e β k) := by ring
          _ = (Polynomial.eval (s + 1) (Rc α₀) * ∏ k, (s + lam k) ^ (e α₀ k))
              * Polynomial.eval s (Rc β) := hcancel.symm
          _ = (∏ k, (s + lam k) ^ (e α₀ k)) * Polynomial.eval s (Rc β)
              * Polynomial.eval (s + 1) (Rc α₀) := by ring
      exfalso
      refine hα₀ (polynomial_eq_zero_of_half_plane (R := Rb) ?_)
      intro s hs0
      have hs : (∑ j, |(lam j).re|) < s.re := lt_of_le_of_lt hRb hs0
      have h2 := hid s hs0
      have hsplit : ∑ β ∈ T.erase α₀, Polynomial.eval s (Rc β) * gammaMonomial lam (e β) s
          + Polynomial.eval s (Rc α₀) * gammaMonomial lam (e α₀) s
          = ∑ β ∈ T, Polynomial.eval s (Rc β) * gammaMonomial lam (e β) s :=
        Finset.sum_erase_add T _ hα₀T
      have hz : ∑ β ∈ T.erase α₀, Polynomial.eval s (Rc β) * gammaMonomial lam (e β) s = 0 := by
        refine Finset.sum_eq_zero fun β hβ => ?_
        rw [hRrest β hβ]
        simp
      rw [hz, zero_add] at hsplit
      rw [← hsplit] at h2
      have hM : gammaMonomial lam (e α₀) s ≠ 0 :=
        gammaMonomial_ne_zero lam (e α₀) (fun k => re_pos_of_gt_sum_abs lam hs k)
      exact (mul_eq_zero.mp h2).resolve_right hM

/-- **Linear independence of Gamma monomials**, at the canonical threshold. -/
theorem gammaMonomial_linearIndependent {r : ℕ} {ι : Type*} [DecidableEq ι] (lam : Fin r → ℂ)
    (hincong : ∀ k k' : Fin r, k ≠ k' → ∀ m : ℤ, lam k - lam k' ≠ (m : ℂ)) :
    ∀ (N : ℕ) (T : Finset ι) (_ : T.card ≤ N) (e : ι → Fin r → ℤ)
      (_ : ∀ α ∈ T, ∀ β ∈ T, α ≠ β → e α ≠ e β) (Rc : ι → Polynomial ℂ)
      (_ : ∀ s : ℂ, (∑ j, |(lam j).re|) < s.re →
        ∑ α ∈ T, Polynomial.eval s (Rc α) * gammaMonomial lam (e α) s = 0),
      ∀ α ∈ T, Rc α = 0 :=
  gammaMonomial_linearIndependent_of_threshold lam hincong _ le_rfl

end

end GaloisForLFunctions.HTGeometry
