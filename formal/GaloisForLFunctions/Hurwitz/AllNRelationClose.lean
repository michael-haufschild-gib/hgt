/-
# Hurwitz all-N — relation-level row close

This file connects the monodromy block separation to the row-descent theorem:
a genuine degree-≤2 local relation gives `Ψ_N = 0`, and the exact pole-root
tail input then closes every quadratic column and linear coefficient.
-/
import GaloisForLFunctions.Hurwitz.AllNHalfInteger
import GaloisForLFunctions.Hurwitz.AllNRowExtraction

open Complex Filter Topology HurwitzEncoding HurwitzSpine HurwitzN2Tail
open HurwitzAllNQuadFilt

namespace HurwitzAllNRelationClose

variable {N : ℕ}

/-- The singular linear+cross block `Ψ_N` vanishes for any genuine all-`N`
degree-≤2 relation and nonintegral `s`, including the half-integer branch. -/
theorem allN_psi_vanish_genuine_all_noninteger {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 →
      PsiN s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z = 0 := by
  intro n hn
  have hlog : -1 < -Real.log 2 := by have := Real.log_two_lt_d9; linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set R : Fin (N + 1) → ℂ → ℂ := fun k z => tailFactored s (k : ℕ) n (Complex.exp z) with hRdef
  have hRper : ∀ k z, R k (z + 2 * (Real.pi : ℂ) * Complex.I) = R k z :=
    fun k z => tailFactored_periodic s (k : ℕ) n z
  have hsplit : ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im → z.im < Real.pi →
      PhiN s n q z + PsiN s n q l R z + ThetaN s n q l cc R z = 0 := by
    intro z hz hz1 hz2
    rw [PhiN, PsiN, ThetaN]
    have hcoll := relation_collectN (s := s) (N := N)
      (fun i j => (q i j).eval (-(n : ℂ) + Complex.exp z))
      (fun k => (l k).eval (-(n : ℂ) + Complex.exp z))
      (cc.eval (-(n : ℂ) + Complex.exp z)) z (fun k => R k z)
    have hr := hrel n hn z hz hz1 hz2
    linear_combination hr - hcoll
  by_cases h2s : ∃ k : ℤ, 2 * s = (k : ℂ)
  · intro z hz
    exact (HurwitzAllNHalfInteger.allN_blocks_order_two_split (N := N) s n hsZ h2s q l cc R
      hRper (z0 := -1) (B := -Real.log 2)
      (by simpa using hlog) (by simpa using hpi) (by simpa using hpi)
      (allN_blockSum_analytic (N := N) hs1 n q l cc) hsplit).1 z hz
  · intro z hz
    have hsZ' : ∀ k : ℤ, (k : ℂ) ≠ s := by
      intro k hk
      exact hsZ k hk.symm
    have h2sZ : ∀ k : ℤ, (k : ℂ) ≠ 2 * s := by
      intro k hk
      exact h2s ⟨k, hk.symm⟩
    exact (allN_blocks_vanish (N := N) n hsZ' h2sZ q l cc R hRper
      (z0 := -1) (B := -Real.log 2)
      (by simpa using hlog) (by simpa using hpi) (by simpa using hpi)
      (allN_blockSum_analytic (N := N) hs1 n q l cc) hsplit).2.1 z hz

/-- Relation-level all-`N` column close: the genuine degree-≤2 relation gives
`Ψ_N = 0`; exact pole-root tail independence and finite descent then close all
quadratic columns and linear coefficients. -/
theorem all_columns_close_of_genuine_relation_poleRootInput {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (hSymm : ∀ i j, q i j = q j i) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    (∀ i j : Fin (N + 1), q i j = 0) ∧ (∀ j : Fin (N + 1), l j = 0) := by
  exact HurwitzAllNRowExtraction.all_columns_close_of_poleRootInput
    (N := N) (s := s) (M := M) hs1 hsZ hpole q l hSymm
    (allN_psi_vanish_genuine_all_noninteger (N := N) hs1 hsZ q l cc hrel)

end HurwitzAllNRelationClose

namespace HurwitzAllNRelationClose

/-- Full relation-level close for the all-`N` symmetric quadratic form: after the
relation gives `Ψ_N = 0`, finite column descent kills `q` and `l`; evaluating the
residual relation at one fixed deep point gives infinitely many shifted roots and
therefore kills `cc`. -/
theorem all_coefficients_close_of_genuine_relation_poleRootInput {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (hpole : HurwitzAllNTailIndependence.HurwitzZetaTail.HarmonicPoleRootInput N s)
    (q : Fin (N + 1) → Fin (N + 1) → Polynomial ℂ)
    (l : Fin (N + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (hSymm : ∀ i j, q i j = q j i) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (N + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    (∀ i j : Fin (N + 1), q i j = 0) ∧ (∀ j : Fin (N + 1), l j = 0) ∧ cc = 0 := by
  obtain ⟨hq, hl⟩ := all_columns_close_of_genuine_relation_poleRootInput
    (N := N) (s := s) (M := M) hs1 hsZ hpole q l cc hSymm hrel
  refine ⟨hq, hl, ?_⟩
  have hlog : -1 < -Real.log 2 := by have := Real.log_two_lt_d9; linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  apply HurwitzDescent.eq_zero_of_eventually_shifted_neg_nat_roots
    (p := cc) (N := M) (c := Complex.exp (-1 : ℂ))
  intro n hn
  rw [Polynomial.IsRoot]
  have hzre : ((-1 : ℂ).re) < -Real.log 2 := by simpa using hlog
  have hzim1 : -Real.pi < ((-1 : ℂ).im) := by
    have : -Real.pi < (0 : ℝ) := by linarith
    simpa using this
  have hzim2 : ((-1 : ℂ).im) < Real.pi := by simpa using hpi
  have hr := hrel n hn (-1 : ℂ) hzre hzim1 hzim2
  simpa [hq, hl] using hr

end HurwitzAllNRelationClose

namespace HurwitzAllNRelationClose

/-- Unconditional singleton-ladder close for a genuine local degree-`≤ 2` Hurwitz relation. This is the
`N = 0` base instance of the all-`N` relation-level theorem with the pole-root provider discharged by
`HurwitzZetaTail.harmonicPoleRootInput_zero`; it carries no extra analytic input beyond `Re(s)>1` and
`∀ k : ℤ, s ≠ k`. -/
theorem all_coefficients_close_of_genuine_relation_N0 {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (q : Fin (0 + 1) → Fin (0 + 1) → Polynomial ℂ)
    (l : Fin (0 + 1) → Polynomial ℂ) (cc : Polynomial ℂ)
    (hSymm : ∀ i j, q i j = q j i) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (0 + 1), ∑ j : Fin (0 + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (0 + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    (∀ i j : Fin (0 + 1), q i j = 0) ∧ (∀ j : Fin (0 + 1), l j = 0) ∧ cc = 0 := by
  exact all_coefficients_close_of_genuine_relation_poleRootInput
    (N := 0) (s := s) (M := M) hs1 hsZ
    (HurwitzAllNTailIndependence.HurwitzZetaTail.harmonicPoleRootInput_zero (s := s) hsZ)
    q l cc hSymm hrel

end HurwitzAllNRelationClose

namespace HurwitzAllNRelationClose

/-- Unconditional singleton-ladder relation close without a symmetry premise. For `N = 0`, the
quadratic coefficient matrix has only one entry, so the symmetric-form hypothesis used by the general
row-descent theorem is automatic. -/
theorem all_coefficients_close_of_genuine_relation_N0_noSymm {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (q : Fin (0 + 1) → Fin (0 + 1) → Polynomial ℂ)
    (l : Fin (0 + 1) → Polynomial ℂ) (cc : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (0 + 1), ∑ j : Fin (0 + 1), (q i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (0 + 1), (l k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    (∀ i j : Fin (0 + 1), q i j = 0) ∧ (∀ j : Fin (0 + 1), l j = 0) ∧ cc = 0 := by
  have hSymm : ∀ i j : Fin (0 + 1), q i j = q j i := by
    intro i j
    fin_cases i
    fin_cases j
    rfl
  exact all_coefficients_close_of_genuine_relation_N0 (s := s) (M := M)
    hs1 hsZ q l cc hSymm hrel

end HurwitzAllNRelationClose

namespace HurwitzAllNRelationClose

/-- Scalar singleton-ladder relation close. This is the `N = 0` theorem with the `Fin 1` coefficient
matrix unpacked to three ordinary polynomials `q`, `l`, and `cc`. -/
theorem all_coefficients_close_of_genuine_relation_N0_scalar {s : ℂ} (hs1 : 1 < s.re)
    (hsZ : ∀ k : ℤ, s ≠ (k : ℂ))
    (q l cc : Polynomial ℂ) {M : ℕ}
    (hrel : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      q.eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-s * z) + tailFactored s 0 n (Complex.exp z))
            * (Complex.exp (-s * z) + tailFactored s 0 n (Complex.exp z)))
        + l.eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-s * z) + tailFactored s 0 n (Complex.exp z))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0) :
    q = 0 ∧ l = 0 ∧ cc = 0 := by
  let qF : Fin (0 + 1) → Fin (0 + 1) → Polynomial ℂ := fun _ _ => q
  let lF : Fin (0 + 1) → Polynomial ℂ := fun _ => l
  have hrelF : ∀ n, M ≤ n → ∀ z : ℂ, z.re < -Real.log 2 → -Real.pi < z.im →
      z.im < Real.pi →
      (∑ i : Fin (0 + 1), ∑ j : Fin (0 + 1), (qF i j).eval (-(n : ℂ) + Complex.exp z)
          * ((Complex.exp (-(s + (i : ℂ)) * z) + tailFactored s (i : ℕ) n (Complex.exp z))
            * (Complex.exp (-(s + (j : ℂ)) * z) + tailFactored s (j : ℕ) n (Complex.exp z))))
        + (∑ k : Fin (0 + 1), (lF k).eval (-(n : ℂ) + Complex.exp z)
            * (Complex.exp (-(s + (k : ℂ)) * z) + tailFactored s (k : ℕ) n (Complex.exp z)))
        + cc.eval (-(n : ℂ) + Complex.exp z) = 0 := by
    intro n hn z hz hz1 hz2
    simpa [qF, lF] using hrel n hn z hz hz1 hz2
  obtain ⟨hq, hl, hcc⟩ := all_coefficients_close_of_genuine_relation_N0_noSymm
    (s := s) (M := M) hs1 hsZ qF lF cc hrelF
  exact ⟨hq 0 0, hl 0, hcc⟩

end HurwitzAllNRelationClose
