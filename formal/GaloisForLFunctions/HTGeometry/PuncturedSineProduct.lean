import Mathlib

/-!
# Shifted factorial products and the punctured Euler sine product

Euler's sine product vanishes at every nonzero integer, so the interesting object at `z = j` is the
product with the vanishing factor deleted.  That punctured product has an exact factorial closed
form

`∏_{1 ≤ m ≤ M, m ≠ j} (1 - j²/m²) = (-1)^{j-1}/2 · (M-j)!(M+j)!/(M!)²`,

which is proved by induction on `M` from the base case `M = j`.  The base case is the reflected
descending product, evaluated with `Finset.prod_range_reflect`.

No infinite-product convergence theory is used: the factorial ratio is an explicit finite product
of terms tending to one.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-! ## Two shifted factorial products -/

/-- The ascending shifted product. -/
theorem prod_range_add_shift (j : ℕ) :
    ∀ n : ℕ, (∏ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) + (j : ℝ))) * (j.factorial : ℝ) =
      ((n + j).factorial : ℝ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    have hstep : ((n + 1 + j).factorial : ℝ) =
        (((n + 1 : ℕ) : ℝ) + (j : ℝ)) * ((n + j).factorial : ℝ) := by
      have hidx : n + 1 + j = (n + j) + 1 := by omega
      rw [hidx, Nat.factorial_succ]
      push_cast
      ring
    rw [hstep, ← ih]
    ring

/-- The descending shifted product: reflecting `range n` turns `k + 1 - (n + 1)` into `-(n - k)`. -/
theorem prod_range_sub_shift (n : ℕ) :
    (∏ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) - (((n : ℕ) : ℝ) + 1))) =
      (-1) ^ n * (n.factorial : ℝ) := by
  have hterm : ∀ k ∈ Finset.range n,
      (((k + 1 : ℕ) : ℝ) - (((n : ℕ) : ℝ) + 1)) = (-1 : ℝ) * (((n - k : ℕ) : ℝ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hk)]
    rw [hcast]
    push_cast
    ring
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range]
  congr 1
  have hrefl := Finset.prod_range_reflect (fun k => ((n - k : ℕ) : ℝ)) n
  have hval : ∀ k ∈ Finset.range n, ((n - (n - 1 - k) : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    congr 1
    omega
  rw [Finset.prod_congr rfl hval] at hrefl
  rw [← hrefl]
  exact_mod_cast Finset.prod_range_add_one_eq_factorial n

/-! ## The punctured sine product -/

/-- The finite factorial ratio appearing in the punctured sine product. -/
noncomputable def puncturedRatio (j M : ℕ) : ℝ :=
  ((M - j).factorial : ℝ) * ((M + j).factorial : ℝ) /
    ((M.factorial : ℝ) * (M.factorial : ℝ))

theorem puncturedRatio_self (j : ℕ) :
    puncturedRatio j j = ((2 * j).factorial : ℝ) / ((j.factorial : ℝ) * (j.factorial : ℝ)) := by
  rw [puncturedRatio, Nat.sub_self, Nat.factorial_zero]
  have : j + j = 2 * j := by omega
  rw [this]
  push_cast
  ring

/-- **The punctured Euler sine product at the base index.** -/
theorem prod_punctured_sine_base (n : ℕ) :
    (∏ k ∈ Finset.range n,
        (1 - (((n : ℕ) : ℝ) + 1) ^ (2 : ℕ) / ((k + 1 : ℕ) : ℝ) ^ (2 : ℕ))) =
      (-1) ^ n / 2 * puncturedRatio (n + 1) (n + 1) := by
  have hne : ∀ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) ≠ 0 := by
    intro k _
    positivity
  have hsplit : ∀ k ∈ Finset.range n,
      (1 - (((n : ℕ) : ℝ) + 1) ^ (2 : ℕ) / ((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) =
        ((((k + 1 : ℕ) : ℝ) - (((n : ℕ) : ℝ) + 1)) *
          (((k + 1 : ℕ) : ℝ) + (((n : ℕ) : ℝ) + 1))) / (((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    have h := hne k hk
    field_simp
    ring
  rw [Finset.prod_congr rfl hsplit, Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  have hasc : (∏ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) + (((n : ℕ) : ℝ) + 1))) *
      (((n + 1).factorial : ℝ)) = ((n + (n + 1)).factorial : ℝ) := by
    have hcast : ∀ k ∈ Finset.range n,
        (((k + 1 : ℕ) : ℝ) + (((n : ℕ) : ℝ) + 1)) = (((k + 1 : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ)) := by
      intro k _
      push_cast
      ring
    rw [Finset.prod_congr rfl hcast]
    exact prod_range_add_shift (n + 1) n
  have hdesc := prod_range_sub_shift n
  have hbot : (∏ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ)) = (n.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  have hnfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1fac : ((n + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
  have hasc' : (∏ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) + (((n : ℕ) : ℝ) + 1))) =
      ((2 * n + 1).factorial : ℝ) / ((n + 1).factorial : ℝ) := by
    have hidx : n + (n + 1) = 2 * n + 1 := by omega
    rw [hidx] at hasc
    field_simp at hasc ⊢
    linarith [hasc]
  rw [hdesc, hasc', hbot, puncturedRatio_self]
  have h2n2 : ((2 * (n + 1)).factorial : ℝ) =
      ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1).factorial : ℝ) := by
    have hidx : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [hidx, Nat.factorial_succ]
    push_cast
    ring
  have hn1 : (((n + 1).factorial : ℕ) : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [h2n2, hn1]
  have hcast2 : ((2 * n + 2 : ℕ) : ℝ) = 2 * ((n : ℝ) + 1) := by push_cast; ring
  rw [hcast2]
  have hn1ne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-! ## The general index and the limit of the factorial ratio -/

/-- The ascending product of `j` consecutive integers above `a`. -/
noncomputable def ascProd (a j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (((a + i + 1 : ℕ) : ℝ))

theorem factorial_add_eq (a : ℕ) : ∀ j : ℕ, (((a + j).factorial : ℕ) : ℝ) =
    ((a.factorial : ℕ) : ℝ) * ascProd a j := by
  intro j
  induction j with
  | zero => simp [ascProd]
  | succ j ih =>
    have hidx : a + (j + 1) = (a + j) + 1 := by omega
    rw [hidx, Nat.factorial_succ, ascProd, Finset.prod_range_succ, ← ascProd]
    push_cast
    rw [ih]
    ring

theorem ascProd_pos (a j : ℕ) : 0 < ascProd a j := by
  refine Finset.prod_pos (fun i _ => ?_)
  positivity

/-- The factorial ratio is an explicit finite product of ratios of consecutive integers. -/
theorem puncturedRatio_eq_ascProd_div {j M : ℕ} (hj : j ≤ M) :
    puncturedRatio j M = ascProd M j / ascProd (M - j) j := by
  have hMfac : ((M.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)
  have hsub : ((M - j) + j) = M := by omega
  have h1 : (((M + j).factorial : ℕ) : ℝ) = ((M.factorial : ℕ) : ℝ) * ascProd M j :=
    factorial_add_eq M j
  have h2 : ((M.factorial : ℕ) : ℝ) = (((M - j).factorial : ℕ) : ℝ) * ascProd (M - j) j := by
    have := factorial_add_eq (M - j) j
    rwa [hsub] at this
  have hsubfac : (((M - j).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (M - j))
  have hasc : ascProd (M - j) j ≠ 0 := ne_of_gt (ascProd_pos _ _)
  rw [puncturedRatio, h1]
  field_simp
  nth_rewrite 1 [h2]
  ring

/-- **The factorial ratio tends to one.** -/
theorem tendsto_puncturedRatio (j : ℕ) :
    Filter.Tendsto (fun M => puncturedRatio j M) Filter.atTop (nhds 1) := by
  have hfac : ∀ i : ℕ, Filter.Tendsto
      (fun M : ℕ => (((M + i + 1 : ℕ) : ℝ)) / (((M - j) + i + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 1) := by
    intro i
    have heq : (fun M : ℕ => (((M + i + 1 : ℕ) : ℝ)) / (((M - j) + i + 1 : ℕ) : ℝ))
        =ᶠ[Filter.atTop] (fun M : ℕ => ((M : ℝ) + i + 1) / ((M : ℝ) - j + i + 1)) := by
      filter_upwards [Filter.eventually_ge_atTop j] with M hM
      have hc : (((M - j) + i + 1 : ℕ) : ℝ) = (M : ℝ) - j + i + 1 := by
        push_cast [Nat.cast_sub hM]
        ring
      rw [hc]
      push_cast
      ring
    refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) ?_
    have hnum : Filter.Tendsto (fun M : ℕ => ((M : ℝ) + i + 1) / ((M : ℝ) - j + i + 1))
        Filter.atTop (nhds 1) := by
      have hrw : ∀ M : ℕ, ((M : ℝ) + i + 1) = ((M : ℝ) - j + i + 1) + (j : ℝ) := by
        intro M; ring
      have hd : Filter.Tendsto (fun M : ℕ => ((M : ℝ) - j + i + 1)) Filter.atTop Filter.atTop := by
        have h0 : Filter.Tendsto (fun M : ℕ => (M : ℝ)) Filter.atTop Filter.atTop :=
          tendsto_natCast_atTop_atTop (R := ℝ)
        have h1 : Filter.Tendsto (fun M : ℕ => (M : ℝ) - (j : ℝ)) Filter.atTop Filter.atTop := by
          simpa [sub_eq_add_neg] using
            Filter.tendsto_atTop_add_const_right Filter.atTop (-(j : ℝ)) h0
        have h2 := Filter.tendsto_atTop_add_const_right Filter.atTop (i : ℝ) h1
        exact Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) h2
      have hone : Filter.Tendsto
          (fun M : ℕ => 1 + (j : ℝ) / ((M : ℝ) - j + i + 1)) Filter.atTop (nhds (1 + 0)) := by
        exact Filter.Tendsto.const_add 1 (Filter.Tendsto.div_atTop tendsto_const_nhds hd)
      rw [add_zero] at hone
      refine hone.congr' ?_
      filter_upwards [hd.eventually_gt_atTop 0] with M hM
      rw [hrw M]
      field_simp
    exact hnum
  have hprod : Filter.Tendsto
      (fun M : ℕ => ∏ i ∈ Finset.range j,
        (((M + i + 1 : ℕ) : ℝ)) / (((M - j) + i + 1 : ℕ) : ℝ))
      Filter.atTop (nhds (∏ _i ∈ Finset.range j, (1 : ℝ))) :=
    tendsto_finsetProd _ (fun i _ => hfac i)
  rw [Finset.prod_const_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop j] with M hM
  rw [puncturedRatio_eq_ascProd_div hM, ascProd, ascProd, ← Finset.prod_div_distrib]

/-! ## The punctured sine product at a general cutoff -/

/-- **The punctured Euler sine product in closed form.** -/
theorem prod_punctured_sine (n : ℕ) :
    ∀ M : ℕ, n ≤ M →
      (∏ k ∈ (Finset.range (M + 1)).erase n,
          (1 - (((n : ℕ) : ℝ) + 1) ^ (2 : ℕ) / ((k + 1 : ℕ) : ℝ) ^ (2 : ℕ))) =
        (-1) ^ n / 2 * puncturedRatio (n + 1) (M + 1) := by
  intro M
  induction M with
  | zero =>
    intro hn
    have hn0 : n = 0 := by omega
    subst hn0
    have hset : (Finset.range 1).erase 0 = (∅ : Finset ℕ) := by decide
    rw [hset, Finset.prod_empty]
    have := prod_punctured_sine_base 0
    rw [Finset.range_zero, Finset.prod_empty] at this
    exact this
  | succ M ih =>
    intro hn
    rcases Nat.lt_or_ge n (M + 1) with hlt | hge
    · have hnM : n ≤ M := by omega
      have hins : (Finset.range (M + 2)).erase n =
          insert (M + 1) ((Finset.range (M + 1)).erase n) := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]
        constructor
        · rintro ⟨hkn, hk⟩
          rcases Nat.lt_or_ge k (M + 1) with h | h
          · exact Or.inr ⟨hkn, h⟩
          · exact Or.inl (by omega)
        · rintro (rfl | ⟨hkn, hk⟩)
          · exact ⟨by omega, by omega⟩
          · exact ⟨hkn, by omega⟩
      have hnotmem : (M + 1) ∉ (Finset.range (M + 1)).erase n := by
        simp only [Finset.mem_erase, Finset.mem_range, not_and]
        intro _
        omega
      rw [hins, Finset.prod_insert hnotmem, ih hnM]
      have hstep : (1 - (((n : ℕ) : ℝ) + 1) ^ (2 : ℕ) / ((M + 1 + 1 : ℕ) : ℝ) ^ (2 : ℕ)) *
          puncturedRatio (n + 1) (M + 1) = puncturedRatio (n + 1) (M + 2) := by
        have e1 : M + 1 - (n + 1) = M - n := by omega
        have e2 : M + 2 - (n + 1) = (M - n) + 1 := by omega
        have e3 : M + 1 + (n + 1) = M + n + 2 := by omega
        have e4 : M + 2 + (n + 1) = (M + n + 2) + 1 := by omega
        have e5 : M + 2 = (M + 1) + 1 := by omega
        have hMn : ((M - n : ℕ) : ℝ) = (M : ℝ) - (n : ℝ) := by
          rw [Nat.cast_sub hnM]
        have hM1fac : (((M + 1).factorial : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (M + 1))
        have hMnfac : (((M - n).factorial : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (M - n))
        have hMn2fac : (((M + n + 2).factorial : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (M + n + 2))
        rw [puncturedRatio, puncturedRatio, e1, e2, e3, e4, e5,
          Nat.factorial_succ (M - n), Nat.factorial_succ (M + n + 2),
          Nat.factorial_succ (M + 1)]
        push_cast [hMn]
        field_simp
        ring
      rw [← hstep]
      ring
    · have hneq : n = M + 1 := by omega
      subst hneq
      have hset : (Finset.range (M + 1 + 1)).erase (M + 1) = Finset.range (M + 1) := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_range]
        constructor
        · rintro ⟨hkn, hk⟩; omega
        · intro hk; exact ⟨by omega, by omega⟩
      rw [hset]
      exact prod_punctured_sine_base (M + 1)


end GaloisForLFunctions.HTGeometry
