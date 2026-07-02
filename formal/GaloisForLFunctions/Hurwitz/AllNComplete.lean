/-
# The all-`N` Hurwitz independence capstone — one theorem, no analytic inputs

The single named endpoint of the Hurwitz program: an eventual degree-≤2 relation among the
genuine shifted Hurwitz values `{ζ(s+k, −n+e^z)}_{k ≤ N}` (in factored-tail form) forces every
coefficient polynomial to vanish.  Composition: `allN_blocks_vanish` separates the three
monodromy blocks (analyticity discharged by `allN_blockSum_analytic`); the linear+cross block
feeds `all_columns_close_of_poleRootInput`, whose pole-root input is the **proven**
`HurwitzMixedClose.harmonicPoleRootInput_proved`; the regular block then strands the constant
polynomial on infinitely many points.  Hypotheses: `1 < Re s`, `s ∉ ℤ`, `2s ∉ ℤ`, `q` symmetric.
-/
import GaloisForLFunctions.Hurwitz.AllNRowExtraction
import GaloisForLFunctions.Hurwitz.MixedClose

open Complex HurwitzN2Tail HurwitzAllNQuadFilt

namespace HurwitzAllNComplete

variable {N : ℕ}

/-- **The all-`N` Hurwitz independence — complete.**  Every eventual factored degree-≤2 relation
among the genuine shifted Hurwitz values kills all quadratic, linear, and constant coefficient
polynomials. -/
theorem hurwitz_allN_independence {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, (k : ℂ) ≠ s) (h2sZ : ∀ k : ℤ, (k : ℂ) ≠ 2 * s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ) (l : Fin (N + 1) → Polynomial ℂ)
    (cc : Polynomial ℂ) (hSymm : ∀ i j, q i j = q j i) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    (∀ i j, q i j = 0) ∧ (∀ j, l j = 0) ∧ cc = 0 := by
  have hlog : -1 < -Real.log 2 := by
    have := Real.log_two_lt_d9
    linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- separate the three monodromy blocks for every large n
  have hblocks : ∀ n, M ≤ n →
      (∀ z : ℂ, z.re < -Real.log 2 → PhiN s n q z = 0)
      ∧ (∀ z : ℂ, z.re < -Real.log 2 →
          PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0)
      ∧ (∀ z : ℂ, z.re < -Real.log 2 →
          ThetaN s n q l cc (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0) := by
    intro n hn
    set R : Fin (N + 1) → ℂ → ℂ := fun k z => tailFactored s (k : ℕ) n (Complex.exp z) with hRdef
    have hRper : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z :=
      fun k z => tailFactored_periodic s (k : ℕ) n z
    have hsplit : ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
        PhiN s n q z + PsiN s n q l R z + ThetaN s n q l cc R z = 0 := by
      intro z hz1 hz2 hz3
      rw [PhiN, PsiN, ThetaN]
      have hcoll := relation_collectN (s := s)
        (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp z))
        (fun k => (l k).eval (-(n : ℂ) + Complex.exp z))
        (cc.eval (-(n : ℂ) + Complex.exp z)) z (fun k => R k z)
      have hr := hrel n hn z hz1 hz2 hz3
      linear_combination hr - hcoll
    exact allN_blocks_vanish n hsZ h2sZ q l cc R hRper (z0 := -1) (B := -Real.log 2)
      (by simpa using hlog) (by simpa using hpi) (by simpa using hpi)
      (allN_blockSum_analytic hs1 n q l cc) hsplit
  -- the linear+cross block closes every column via the proven pole-root input
  have hsZ' : ∀ k : ℤ, s ≠ (k : ℂ) := fun k h => hsZ k h.symm
  have hql : (∀ i j : Fin (N + 1), q i j = 0) ∧ (∀ j : Fin (N + 1), l j = 0) :=
    HurwitzAllNRowExtraction.all_columns_close_of_poleRootInput (N := N) hs1 hsZ'
      (HurwitzMixedClose.harmonicPoleRootInput_proved hsZ') q l hSymm (M := M)
      (fun n hn => (hblocks n hn).2.1)
  obtain ⟨hq, hl⟩ := hql
  refine ⟨hq, hl, ?_⟩
  -- the regular block strands cc on infinitely many points
  have hTheta := (hblocks M le_rfl).2.2
  have hccpt : ∀ z : ℂ, z.re < -Real.log 2 → cc.eval (-(M : ℂ) + Complex.exp z) = 0 := by
    intro z hz
    have h0 := hTheta z hz
    rw [ThetaN] at h0
    have hqz : (∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        (q i j).eval (-(M : ℂ) + Complex.exp z)
          * (tailFactored s (i : ℕ) M (Complex.exp z)
            * tailFactored s (j : ℕ) M (Complex.exp z))) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [hq i j]
      simp
    have hlz : (∑ k : Fin (N + 1), (l k).eval (-(M : ℂ) + Complex.exp z)
        * tailFactored s (k : ℕ) M (Complex.exp z)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hl k]
      simp
    rw [hqz, hlz, zero_add, zero_add] at h0
    exact h0
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hexpval : ∀ j : ℕ,
      Complex.exp (((Real.log (1 / (4 + (j : ℝ)))) : ℂ)) = ((1 / (4 + (j : ℝ)) : ℝ) : ℂ) := by
    intro j
    rw [← Complex.ofReal_exp, Real.exp_log (by positivity)]
  have hroots : ∀ j : ℕ, cc.IsRoot (-(M : ℂ) + ((1 / (4 + (j : ℝ)) : ℝ) : ℂ)) := by
    intro j
    have h4j : (0 : ℝ) < 1 / (4 + (j : ℝ)) := by positivity
    have hlt : Real.log (1 / (4 + (j : ℝ))) < -Real.log 2 := by
      rw [one_div, Real.log_inv]
      have h2 : Real.log 2 < Real.log (4 + (j : ℝ)) := by
        apply Real.log_lt_log (by norm_num)
        have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      linarith
    have hre : (((Real.log (1 / (4 + (j : ℝ)))) : ℂ)).re < -Real.log 2 := by
      simpa using hlt
    have := hccpt _ hre
    rwa [hexpval j] at this
  apply Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => -(M : ℂ) + ((1 / (4 + (j : ℝ)) : ℝ) : ℂ))
  · intro a b hab
    have h1 : ((1 / (4 + (a : ℝ)) : ℝ) : ℂ) = ((1 / (4 + (b : ℝ)) : ℝ) : ℂ) := by
      linear_combination hab
    have h2 : (1 / (4 + (a : ℝ)) : ℝ) = 1 / (4 + (b : ℝ)) := Complex.ofReal_inj.mp h1
    have h3 : (4 + (a : ℝ)) = 4 + (b : ℝ) := by
      rw [div_eq_div_iff (by positivity) (by positivity)] at h2
      linarith
    exact_mod_cast (by linarith : (a : ℝ) = (b : ℝ))
  · intro j
    exact hroots j

end HurwitzAllNComplete
