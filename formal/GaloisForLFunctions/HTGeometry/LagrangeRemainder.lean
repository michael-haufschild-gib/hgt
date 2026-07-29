import GaloisForLFunctions.HTGeometry.IteratedRolleVanishing
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Lagrange interpolation remainder

For a smooth real function `f` and its Lagrange interpolant `P` at `n + 1`
distinct nodes inside `[a, b]`, the interpolation error at any `x ∈ [a, b]`
obeys the classical factorial-divided bound

`|f x - P x| ≤ (sup_{[a,b]} |f^{(n+1)}|) / (n+1)! · ∏_i |x - xᵢ|`.

Proof: the auxiliary function `f - P - λ·W` (`W` the monic nodal polynomial,
`λ` normalized at `x`) vanishes at `n + 2` points, so by iterated Rolle its
`(n+1)`-st derivative vanishes somewhere in `[a, b]`; the interpolant
differentiates to zero at order `n + 1` and the nodal polynomial to `(n+1)!`,
which solves for `λ`.
-/

noncomputable section

namespace HTGeometry

open Set Polynomial

/-- Iterated derivatives of polynomial evaluation are evaluations of iterated
polynomial derivatives. -/
theorem iteratedDeriv_polynomial_eval (m : ℕ) :
    ∀ p : Polynomial ℝ, iteratedDeriv m (fun x : ℝ => p.eval x)
      = fun x => ((Polynomial.derivative (R := ℝ))^[m] p).eval x := by
  induction m with
  | zero =>
    intro p
    simp [iteratedDeriv_zero]
  | succ m ih =>
    intro p
    rw [iteratedDeriv_succ']
    have hd : deriv (fun x : ℝ => p.eval x)
        = fun x => (Polynomial.derivative p).eval x := by
      funext y
      exact Polynomial.deriv p
    rw [hd, ih (Polynomial.derivative p)]
    funext y
    rw [Function.iterate_succ_apply]

/-- Polynomial evaluation is smooth. -/
theorem contDiff_polynomial_eval (p : Polynomial ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun x : ℝ => p.eval x :=
  Polynomial.contDiff_aeval (𝕜 := ℝ) p n

/-- Iterated Rolle over a finite set of zeros. -/
theorem exists_iteratedDeriv_eq_zero_of_finset_zeros
    (k : ℕ) (g : ℝ → ℝ) (hg : ∀ j : ℕ, Continuous (iteratedDeriv j g))
    (s : Finset ℝ) (hcard : s.card = k + 1) (hz : ∀ t ∈ s, g t = 0)
    (hne : s.Nonempty) :
    ∃ ξ ∈ Set.Icc (s.min' hne) (s.max' hne), iteratedDeriv k g ξ = 0 := by
  set pts : Fin (k + 1) → ℝ := fun i => (s.orderIsoOfFin hcard i : ℝ) with hpts
  have hmono : StrictMono pts := by
    intro i j hij
    exact_mod_cast (s.orderIsoOfFin hcard).strictMono hij
  have hmem : ∀ i, pts i ∈ s := fun i => (s.orderIsoOfFin hcard i).2
  obtain ⟨ξ, hξmem, hξ⟩ :=
    exists_iteratedDeriv_eq_zero_of_zeros k g hg pts hmono
      (fun i => hz _ (hmem i))
  refine ⟨ξ, ⟨?_, ?_⟩, hξ⟩
  · exact le_trans (s.min'_le _ (hmem 0)) hξmem.1
  · exact le_trans hξmem.2 (s.le_max' _ (hmem (Fin.last k)))

/-- Iterated polynomial derivatives are additive. -/
theorem iterate_derivative_add' :
    ∀ (k : ℕ) (p q : Polynomial ℝ),
      (Polynomial.derivative (R := ℝ))^[k] (p + q)
        = (Polynomial.derivative (R := ℝ))^[k] p
          + (Polynomial.derivative (R := ℝ))^[k] q := by
  intro k
  induction k with
  | zero => intro p q; simp
  | succ k ihk =>
    intro p q
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, Polynomial.derivative_add]
    exact ihk _ _

/-- The `(n+1)`-st iterated polynomial derivative of the monic nodal
polynomial of `n + 1` nodes is the constant `(n+1)!`. -/
theorem iterate_derivative_nodal {s : Finset ℝ} {n : ℕ}
    (hcard : s.card = n + 1) :
    (Polynomial.derivative (R := ℝ))^[n + 1] (Lagrange.nodal s id)
      = Polynomial.C ((n + 1).factorial : ℝ) := by
  set W : Polynomial ℝ := Lagrange.nodal s id with hW
  have hmonic : W.Monic := Lagrange.nodal_monic
  have hdeg : W.natDegree = n + 1 := by
    rw [hW, Lagrange.natDegree_nodal, hcard]
  have hsplit : W.eraseLead + Polynomial.C W.leadingCoeff * X ^ W.natDegree
      = W := Polynomial.eraseLead_add_C_mul_X_pow W
  rw [hmonic.leadingCoeff, map_one, one_mul, hdeg] at hsplit
  have herase : (Polynomial.derivative (R := ℝ))^[n + 1] W.eraseLead = 0 := by
    apply Polynomial.iterate_derivative_eq_zero
    rcases Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero W with h | h
    · exact hdeg ▸ h
    · rw [h]
      simp
  have hXpow : (Polynomial.derivative (R := ℝ))^[n + 1] (X ^ (n + 1))
      = Polynomial.C ((n + 1).factorial : ℝ) := by
    rw [Polynomial.iterate_derivative_X_pow_eq_smul (n + 1) (n + 1)]
    rw [Nat.descFactorial_self, Nat.sub_self, pow_zero,
      Polynomial.smul_eq_C_mul, mul_one]
  calc (Polynomial.derivative (R := ℝ))^[n + 1] W
      = (Polynomial.derivative (R := ℝ))^[n + 1]
          (W.eraseLead + X ^ (n + 1)) := by rw [hsplit]
    _ = (Polynomial.derivative (R := ℝ))^[n + 1] W.eraseLead
        + (Polynomial.derivative (R := ℝ))^[n + 1] (X ^ (n + 1)) :=
        iterate_derivative_add' (n + 1) _ _
    _ = Polynomial.C ((n + 1).factorial : ℝ) := by
        rw [herase, hXpow, zero_add]

/-- The iterated derivative of `f` minus a polynomial evaluation splits
pointwise. -/
theorem iteratedDeriv_sub_polynomial_eval
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (Q : Polynomial ℝ) (j : ℕ) :
    iteratedDeriv j (fun t => f t - Q.eval t)
      = fun t => iteratedDeriv j f t
          - ((Polynomial.derivative (R := ℝ))^[j] Q).eval t := by
  funext t
  have h1 : ContDiffAt ℝ j f t := (hf.of_le (by exact_mod_cast le_top)).contDiffAt
  have h2 : ContDiffAt ℝ j (fun x : ℝ => Q.eval x) t :=
    (contDiff_polynomial_eval Q).contDiffAt
  have h3 := iteratedDeriv_sub h1 h2
  rw [show (fun t => f t - Q.eval t) = f - fun x : ℝ => Q.eval x from rfl, h3,
    congrFun (iteratedDeriv_polynomial_eval j Q) t]

/-- **Lagrange interpolation remainder**: for a smooth function and its
interpolant at `n + 1` nodes in `[a, b]`, the error at any point of `[a, b]`
is bounded by the sup of the `(n+1)`-st derivative divided by `(n+1)!`, times
the nodal product. -/
theorem abs_sub_eval_interpolate_le
    {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {s : Finset ℝ} (hcard : s.card = n + 1)
    {a b M : ℝ} (hsub : ↑s ⊆ Set.Icc a b)
    (hM : ∀ t ∈ Set.Icc a b, |iteratedDeriv (n + 1) f t| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |f x - (Lagrange.interpolate s id f).eval x|
      ≤ M / (n + 1).factorial * ∏ t ∈ s, |x - t| := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x hx)
  have hfact : (0:ℝ) < ((n + 1).factorial : ℝ) := by positivity
  by_cases hxs : x ∈ s
  · have h := Lagrange.eval_interpolate_at_node (s := s) (v := id) f (Set.injOn_id _) hxs
    simp only [id] at h
    rw [h, sub_self, abs_zero]
    positivity
  · set P : Polynomial ℝ := Lagrange.interpolate s id f with hP
    set W : Polynomial ℝ := Lagrange.nodal s id with hW
    have hWx : W.eval x = ∏ t ∈ s, (x - t) := by
      rw [hW, Lagrange.eval_nodal]
      simp
    have hWne : W.eval x ≠ 0 := by
      rw [hWx]
      apply Finset.prod_ne_zero_iff.2
      intro t hts
      exact sub_ne_zero.2 fun hxt => hxs (hxt ▸ hts)
    set lam : ℝ := (f x - P.eval x) / W.eval x with hlam
    set Q : Polynomial ℝ := P + Polynomial.C lam * W with hQ
    have hzeros : ∀ t ∈ insert x s, f t - Q.eval t = 0 := by
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | hts
      · rw [hQ]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        rw [hlam, div_mul_cancel₀ _ hWne]
        ring
      · have hPt : P.eval t = f t := by
          have h := Lagrange.eval_interpolate_at_node (s := s) (v := id) f (Set.injOn_id _) hts
          rw [hP]
          exact h
        have hWt : W.eval t = 0 := by
          have h := Lagrange.eval_nodal_at_node (v := id) hts
          simpa using h
        rw [hQ]
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          hPt, hWt]
    have hcard' : (insert x s).card = (n + 1) + 1 := by
      rw [Finset.card_insert_of_notMem hxs, hcard]
    have hne : (insert x s).Nonempty := ⟨x, Finset.mem_insert_self x s⟩
    have hφcont : ∀ j : ℕ,
        Continuous (iteratedDeriv j fun t => f t - Q.eval t) := by
      intro j
      rw [iteratedDeriv_sub_polynomial_eval hf Q j]
      exact (hf.continuous_iteratedDeriv j (by exact_mod_cast le_top)).sub
        (contDiff_polynomial_eval (n := 0) _).continuous
    obtain ⟨ξ, hξmem, hξ⟩ := exists_iteratedDeriv_eq_zero_of_finset_zeros
      (n + 1) _ hφcont (insert x s) hcard' hzeros hne
    have hinsIcc : ∀ t ∈ insert x s, t ∈ Set.Icc a b := by
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | hts
      · exact hx
      · exact hsub hts
    have hξab : ξ ∈ Set.Icc a b := by
      constructor
      · exact le_trans (hinsIcc _ ((insert x s).min'_mem hne)).1 hξmem.1
      · exact le_trans hξmem.2 (hinsIcc _ ((insert x s).max'_mem hne)).2
    have hQder : (Polynomial.derivative (R := ℝ))^[n + 1] Q
        = Polynomial.C (lam * ((n + 1).factorial : ℝ)) := by
      rw [hQ, iterate_derivative_add', Polynomial.iterate_derivative_C_mul,
        iterate_derivative_nodal hcard]
      have hPzero : (Polynomial.derivative (R := ℝ))^[n + 1] P = 0 := by
        by_cases hP0 : P = 0
        · rw [hP0]
          exact Function.iterate_fixed (by simp) (n + 1)
        · apply Polynomial.iterate_derivative_eq_zero
          have hdeg := Lagrange.degree_interpolate_lt (s := s) (v := id) f
            (Set.injOn_id _)
          rw [hcard] at hdeg
          exact (Polynomial.natDegree_lt_iff_degree_lt hP0).2
            (by exact_mod_cast hdeg)
      rw [hPzero, zero_add, ← Polynomial.C_mul]
    have hval := hξ
    rw [iteratedDeriv_sub_polynomial_eval hf Q (n + 1), hQder] at hval
    simp only [Polynomial.eval_C] at hval
    have hfne : ((n + 1).factorial : ℝ) ≠ 0 := hfact.ne'
    have hlamval : lam = iteratedDeriv (n + 1) f ξ / ((n + 1).factorial : ℝ) := by
      field_simp
      linarith
    have hfx : f x - P.eval x = lam * W.eval x := by
      rw [hlam, div_mul_cancel₀ _ hWne]
    rw [hfx]
    calc |lam * W.eval x| = |lam| * |W.eval x| := abs_mul _ _
      _ ≤ M / ((n + 1).factorial : ℝ) * |W.eval x| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          rw [hlamval, abs_div, abs_of_pos hfact]
          gcongr
          exact hM ξ hξab
      _ = M / ((n + 1).factorial : ℝ) * ∏ t ∈ s, |x - t| := by
          rw [hWx, Finset.abs_prod]

end HTGeometry
