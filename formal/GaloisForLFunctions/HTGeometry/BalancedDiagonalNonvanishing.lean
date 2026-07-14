import Mathlib

/-!
# Balanced diagonal nonvanishing

The Step-1 keystone of the magnitude-hypertranscendence family: a nonzero multivariate polynomial
`W` over `ℂ` cannot vanish on an entire large *balanced* diagonal.  Concretely there is a fixed
natural offset `δ` and a threshold `Q₀` so that for every `q ≥ Q₀` the tuple `(q+δ₀, …, q+δ_{D-1})`
— whose coordinates all lie within `Finset.univ.sup δ` of one another — has `W(q+δ) ≠ 0`
(`exists_balanced_diagonal_ne_zero`).

The mechanism is: pick any natural tuple `k` with `W(k) ≠ 0` (available because `ℕ ↪ ℂ` has infinite
range, so `MvPolynomial.funext_set` on the box of natural values would otherwise force `W = 0`); the
univariate diagonal restriction through offset `δ = k` is then a nonzero polynomial (nonzero at
`q = 0`), and a nonzero univariate polynomial over `ℂ` is nonzero at all large natural arguments.

This supplies the balanced nonzero coefficient atom that the superlacunary valuation gap needs to
isolate, without any leading-symbol nondegeneracy hypothesis.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions

/-- A nonzero univariate polynomial over `ℂ` is eventually nonzero on natural-number arguments:
its complex roots are finite, so only finitely many naturals cast to a root. -/
theorem poly_eventually_ne_zero_nat (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, p.eval ((n : ℂ)) ≠ 0 := by
  have hfin : {n : ℕ | p.eval (n : ℂ) = 0}.Finite := by
    apply Set.Finite.ofFinset (p.roots.toFinset.preimage (Nat.cast : ℕ → ℂ)
      (Nat.cast_injective.injOn))
    intro n
    simp only [Finset.mem_preimage, Multiset.mem_toFinset, Set.mem_setOf_eq,
      Polynomial.mem_roots hp, Polynomial.IsRoot.def]
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, fun n hn hev => ?_⟩
  have hmem : n ∈ {n : ℕ | p.eval (n : ℂ) = 0} := hev
  have := hN hmem
  omega

/-- Evaluating an `aeval`-substituted multivariate polynomial at a point equals the multivariate
evaluation at the substituted coordinate values. -/
theorem eval_aeval_poly {D : ℕ} (W : MvPolynomial (Fin D) ℂ) (g : Fin D → Polynomial ℂ) (q : ℂ) :
    Polynomial.eval q (aeval g W) = eval (fun i => Polynomial.eval q (g i)) W := by
  induction W using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp => simp [hp]

/-- The univariate diagonal restriction of `W` through natural offsets `δ`: the polynomial
`q ↦ W(q+δ₀, …, q+δ_{D-1})`. -/
noncomputable def diagPoly {D : ℕ} (W : MvPolynomial (Fin D) ℂ) (δ : Fin D → ℕ) : Polynomial ℂ :=
  aeval (fun i => Polynomial.X + Polynomial.C ((δ i : ℂ))) W

/-- Evaluating the diagonal polynomial recovers the balanced multivariate value. -/
theorem diagPoly_eval {D : ℕ} (W : MvPolynomial (Fin D) ℂ) (δ : Fin D → ℕ) (q : ℂ) :
    (diagPoly W δ).eval q = eval (fun i => q + (δ i : ℂ)) W := by
  rw [diagPoly, eval_aeval_poly]
  simp

/-- **Nonzero at a natural tuple.**  A nonzero multivariate polynomial over `ℂ` has a nonzero
evaluation at some natural-number tuple: `ℕ ↪ ℂ` has infinite range, so `funext_set` on the box of
natural values would force `W = 0` otherwise. -/
theorem exists_nat_eval_ne_zero {D : ℕ} (W : MvPolynomial (Fin D) ℂ) (hW : W ≠ 0) :
    ∃ k : Fin D → ℕ, eval (fun i => (k i : ℂ)) W ≠ 0 := by
  by_contra hcon
  apply hW
  apply MvPolynomial.funext_set (p := W) (q := 0)
    (fun _ : Fin D => Set.range ((↑) : ℕ → ℂ))
    (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
  intro x hx
  rw [map_zero]
  choose k hk using fun i => hx i (Set.mem_univ i)
  have hxeq : x = (fun i => (k i : ℂ)) := funext (fun i => (hk i).symm)
  rw [hxeq]
  by_contra hne
  exact hcon ⟨k, hne⟩

/-- **Balanced diagonal nonvanishing (Step 1 keystone).**  For a nonzero multivariate polynomial
`W` over `ℂ` there is a fixed natural offset `δ` and threshold `Q₀` such that for every `q ≥ Q₀` the
*balanced* tuple `(q+δ₀, …, q+δ_{D-1})` — all coordinates within `Finset.univ.sup δ` of each other —
satisfies `W(q+δ) ≠ 0`.  Take any natural tuple `k` with `W(k) ≠ 0`; the diagonal through offset
`δ = k` is a nonzero univariate polynomial (nonzero at `q = 0`), hence eventually nonzero. -/
theorem exists_balanced_diagonal_ne_zero {D : ℕ} (W : MvPolynomial (Fin D) ℂ) (hW : W ≠ 0) :
    ∃ (δ : Fin D → ℕ) (Q₀ : ℕ), ∀ q ≥ Q₀, eval (fun i => ((q + δ i : ℕ) : ℂ)) W ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_nat_eval_ne_zero W hW
  have hp0 : diagPoly W k ≠ 0 := by
    intro h0
    apply hk
    have := diagPoly_eval W k 0
    rw [h0, Polynomial.eval_zero] at this
    simpa using this.symm
  obtain ⟨N, hN⟩ := poly_eventually_ne_zero_nat (diagPoly W k) hp0
  refine ⟨k, N, fun q hq hev => ?_⟩
  have hd := diagPoly_eval W k (q : ℂ)
  have hcast : (fun i => (q : ℂ) + (k i : ℂ)) = (fun i => ((q + k i : ℕ) : ℂ)) := by
    funext i; push_cast; ring
  rw [hcast, hev] at hd
  exact hN q hq hd

end GaloisForLFunctions
