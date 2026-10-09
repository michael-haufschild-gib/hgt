import GaloisForLFunctions.RHTower.LaguerreInequality

/-!
# Interlacing for the first-order Laguerre operator on real-rooted polynomials

For a real-rooted polynomial `p` of positive degree the first Laguerre form is strictly positive
off the zeros of `p`: peeling one linear factor, `L₁[(X − r)q] = q² + (X − r)²L₁[q]` with
`L₁[q] ≥ 0`, and `q(x) ≠ 0` wherever `p(x) ≠ 0`.  Hence the logarithmic derivative `p′/p` is
strictly decreasing on every interval free of zeros of `p`, and the equation `p − c p′ = 0`,
which there reads `p′/p = 1/c`, has at most one solution:

* `laguerreL1_eval_pos`: `p(x) ≠ 0 ⇒ L₁[p](x) > 0`;
* `exists_root_Icc_of_sub_C_mul_derivative`: if `p − c p′` vanishes at `γ < γ′`, then `p` has a
  zero in `[γ, γ′]`.
-/

open Polynomial Set

namespace RHTower

noncomputable section

/-- **Strict first Laguerre inequality** off the zeros of a real-rooted polynomial of positive
degree. -/
theorem laguerreL1_eval_pos {p : Polynomial ℝ} (hsp : p.Splits) (hdeg : 1 ≤ p.natDegree) {x : ℝ}
    (hx : p.eval x ≠ 0) : 0 < (laguerreL1 p).eval x := by
  have hfact : p = C p.leadingCoeff * (Multiset.map (fun a => X - C a) p.roots).prod :=
    hsp.eq_prod_roots
  have hroots : p.roots ≠ 0 := by
    intro h0
    have hc := (splits_iff_card_roots.mp hsp)
    rw [h0] at hc
    simp at hc
    omega
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hroots
  set q : Polynomial ℝ := (Multiset.map (fun a => X - C a) (p.roots.erase r)).prod with hq
  have hprod : (Multiset.map (fun a => X - C a) p.roots).prod = (X - C r) * q := by
    rw [← Multiset.cons_erase hr, Multiset.map_cons, Multiset.prod_cons]
  have hp0 : p ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hqx : q.eval x ≠ 0 := by
    intro h
    apply hx
    rw [hfact, hprod, eval_mul, eval_mul, h, mul_zero, mul_zero]
  have hnonneg : 0 ≤ (laguerreL1 q).eval x := laguerreL1_prod_eval_nonneg _ x
  rw [hfact, hprod, laguerreL1_C_mul, laguerreL1_linear_mul, eval_mul, eval_pow, eval_C,
    eval_add, eval_mul, eval_pow, eval_pow]
  have h1 : 0 < q.eval x ^ (2 : ℕ) := by positivity
  have h2 : 0 ≤ (X - C r).eval x ^ (2 : ℕ) * (laguerreL1 q).eval x :=
    mul_nonneg (sq_nonneg _) hnonneg
  have h3 : 0 < p.leadingCoeff ^ (2 : ℕ) := by positivity
  exact mul_pos h3 (by linarith)

/-- **Interlacing.** If `p − c p′` vanishes at two points `γ < γ′`, then `p` has a zero in
`[γ, γ′]`. -/
theorem exists_root_Icc_of_sub_C_mul_derivative {p : Polynomial ℝ} (hsp : p.Splits)
    (hdeg : 1 ≤ p.natDegree) {c γ γ' : ℝ} (hγ : γ < γ')
    (h1 : (p - C c * derivative p).eval γ = 0) (h2 : (p - C c * derivative p).eval γ' = 0) :
    ∃ x ∈ Icc γ γ', p.eval x = 0 := by
  by_contra hnot
  push Not at hnot
  have hne : ∀ x ∈ Icc γ γ', p.eval x ≠ 0 := hnot
  -- the logarithmic derivative is strictly antitone on the interval
  set f : ℝ → ℝ := fun x => (derivative p).eval x / p.eval x with hf
  have hderiv : ∀ x ∈ Icc γ γ', HasDerivAt f
      (((derivative (derivative p)).eval x * p.eval x - (derivative p).eval x *
        (derivative p).eval x) / p.eval x ^ 2) x := by
    intro x hx
    have := ((derivative p).hasDerivAt x).div (p.hasDerivAt x) (hne x hx)
    exact this
  have hneg : ∀ x ∈ interior (Icc γ γ'), deriv f x < 0 := by
    intro x hx
    have hxI : x ∈ Icc γ γ' := interior_subset hx
    rw [(hderiv x hxI).deriv]
    have hpos := laguerreL1_eval_pos hsp hdeg (hne x hxI)
    unfold laguerreL1 at hpos
    rw [eval_sub, eval_pow, eval_mul] at hpos
    have hp2 : 0 < p.eval x ^ 2 := by have := hne x hxI; positivity
    apply div_neg_of_neg_of_pos _ hp2
    nlinarith
  have hcont : ContinuousOn f (Icc γ γ') := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f (Icc γ γ') :=
    strictAntiOn_of_deriv_neg (convex_Icc γ γ') hcont hneg
  -- both endpoints satisfy `p′/p = 1/c`
  have hval : ∀ x ∈ Icc γ γ', (p - C c * derivative p).eval x = 0 → c ≠ 0 ∧ f x = 1 / c := by
    intro x hx h
    rw [eval_sub, eval_mul, eval_C] at h
    have hc : c ≠ 0 := by
      intro hc; rw [hc, zero_mul, sub_zero] at h; exact hne x hx h
    refine ⟨hc, ?_⟩
    simp only [hf]
    rw [div_eq_div_iff (hne x hx) hc]
    linarith
  have hγI : γ ∈ Icc γ γ' := ⟨le_rfl, hγ.le⟩
  have hγ'I : γ' ∈ Icc γ γ' := ⟨hγ.le, le_rfl⟩
  have e1 := (hval γ hγI h1).2
  have e2 := (hval γ' hγ'I h2).2
  have := hanti hγI hγ'I hγ
  rw [e1, e2] at this
  exact lt_irrefl _ this

end

end RHTower
