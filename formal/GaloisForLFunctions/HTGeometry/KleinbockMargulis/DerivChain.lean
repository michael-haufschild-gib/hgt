import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Derivative chains, iterated Rolle and the Lagrange remainder

A *derivative chain* for `f` on a set `U` is a sequence `F` of functions with `F 0 = f` and
`F (j+1)` the derivative of `F j` at every point of `U`.  Working with a chain rather than with
`iteratedDeriv` avoids junk values and the `iteratedDerivWithin` bookkeeping, and is exactly what
Rolle-based arguments consume.

## Main results

* `exists_chain_eq_zero` — iterated Rolle: a chain member of order `k` vanishes between `k+1`
  zeros of `f`.
* `abs_sub_interpolate_le` — the Lagrange interpolation remainder for a chain.
* `abs_coeff_top_le` — the top Lagrange coefficient is a divided difference, hence controlled by
  the values at the nodes.
-/

open Set Polynomial

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

/-- `F` is a derivative chain of length `k` on `U`: each `F (j+1)`, for `j < k`, is the derivative
of `F j` on `U`.  Only finitely many links are required, so a `C^k` function supplies one. -/
def IsDerivChain (k : ℕ) (F : ℕ → ℝ → ℝ) (U : Set ℝ) : Prop :=
  ∀ j < k, ∀ x ∈ U, HasDerivAt (F j) (F (j + 1) x) x

theorem IsDerivChain.shift {k : ℕ} {F : ℕ → ℝ → ℝ} {U : Set ℝ}
    (hF : IsDerivChain (k + 1) F U) : IsDerivChain k (fun j => F (j + 1)) U :=
  fun j hj x hx => hF (j + 1) (by omega) x hx

theorem IsDerivChain.mono {k : ℕ} {F : ℕ → ℝ → ℝ} {U W : Set ℝ} (hF : IsDerivChain k F U)
    (h : W ⊆ U) : IsDerivChain k F W := fun j hj x hx => hF j hj x (h hx)

theorem IsDerivChain.mono_order {k k' : ℕ} {F : ℕ → ℝ → ℝ} {U : Set ℝ}
    (hF : IsDerivChain k F U) (h : k' ≤ k) : IsDerivChain k' F U :=
  fun j hj x hx => hF j (lt_of_lt_of_le hj h) x hx

theorem IsDerivChain.continuousOn {k : ℕ} {F : ℕ → ℝ → ℝ} {U : Set ℝ} (hF : IsDerivChain k F U)
    (j : ℕ) (hj : j < k) {s : Set ℝ} (hs : s ⊆ U) : ContinuousOn (F j) s :=
  fun x hx => ((hF j hj x (hs hx)).differentiableAt.continuousAt).continuousWithinAt

/-- **Iterated Rolle for a chain.** -/
theorem exists_chain_eq_zero {U : Set ℝ} (hUc : U.OrdConnected) :
    ∀ (k : ℕ) (F : ℕ → ℝ → ℝ), IsDerivChain k F U →
      ∀ (pts : Fin (k + 1) → ℝ), StrictMono pts → (∀ i, pts i ∈ U) →
      (∀ i, F 0 (pts i) = 0) → ∃ ξ ∈ Icc (pts 0) (pts (Fin.last k)), F k ξ = 0 := by
  intro k
  induction k with
  | zero =>
    intro F _ pts _ _ hz
    exact ⟨pts 0, ⟨le_rfl, le_rfl⟩, hz 0⟩
  | succ k ih =>
    intro F hF pts hmono hmem hz
    have hR : ∀ i : Fin (k + 1),
        ∃ c ∈ Ioo (pts i.castSucc) (pts i.succ), deriv (F 0) c = 0 := by
      intro i
      refine exists_deriv_eq_zero (hmono Fin.castSucc_lt_succ) ?_ ?_
      · refine hF.continuousOn 0 (by omega) ?_
        exact hUc.out (hmem i.castSucc) (hmem i.succ)
      · rw [hz i.castSucc, hz i.succ]
    choose qts hqmem hqz using hR
    have hqmem' : ∀ i, qts i ∈ U := by
      intro i
      exact hUc.out (hmem i.castSucc) (hmem i.succ) (Ioo_subset_Icc_self (hqmem i))
    have hqmono : StrictMono qts := by
      intro i j hij
      have h1 : qts i < pts i.succ := (hqmem i).2
      have h2 : pts j.castSucc < qts j := (hqmem j).1
      have h3 : pts i.succ ≤ pts j.castSucc := by
        refine hmono.monotone ?_
        rw [Fin.le_def]
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact Nat.succ_le_of_lt hij
      linarith
    have hqz' : ∀ i, F 1 (qts i) = 0 := by
      intro i
      rw [← (hF 0 (by omega) (qts i) (hqmem' i)).deriv]
      exact hqz i
    obtain ⟨ξ, hξmem, hξ⟩ := ih (fun j => F (j + 1)) hF.shift qts hqmono hqmem' hqz'
    refine ⟨ξ, ⟨le_of_lt ?_, le_of_lt ?_⟩, hξ⟩
    · calc pts 0 ≤ pts (Fin.castSucc 0) := by
            refine hmono.monotone ?_
            rw [Fin.le_def]
            simp
        _ < qts 0 := (hqmem 0).1
        _ ≤ ξ := hξmem.1
    · calc ξ ≤ qts (Fin.last k) := hξmem.2
        _ < pts (Fin.last k).succ := (hqmem (Fin.last k)).2
        _ ≤ pts (Fin.last (k + 1)) := by
            refine hmono.monotone ?_
            rw [Fin.le_def]
            simp


/-! ### Polynomial chains -/

/-- The evaluations of the iterated derivatives of a polynomial form a derivative chain. -/
theorem isDerivChain_polynomial (k : ℕ) (P : Polynomial ℝ) (U : Set ℝ) :
    IsDerivChain k (fun j x => ((Polynomial.derivative (R := ℝ))^[j] P).eval x) U := by
  intro j _ x _
  show HasDerivAt (fun y => ((Polynomial.derivative (R := ℝ))^[j] P).eval y)
    (((Polynomial.derivative (R := ℝ))^[j + 1] P).eval x) x
  rw [Function.iterate_succ_apply']
  exact Polynomial.hasDerivAt _ x

theorem IsDerivChain.sub_polynomial {k : ℕ} {F : ℕ → ℝ → ℝ} {U : Set ℝ}
    (hF : IsDerivChain k F U) (P : Polynomial ℝ) :
    IsDerivChain k (fun j x => F j x - ((Polynomial.derivative (R := ℝ))^[j] P).eval x) U := by
  intro j hj x hx
  exact (hF j hj x hx).sub (isDerivChain_polynomial k P U j hj x hx)

/-- The `k`-th derivative of a polynomial of degree at most `k` is the constant `k!` times the
top coefficient. -/
theorem eval_iterate_derivative_top {P : Polynomial ℝ} {k : ℕ} (hP : P.natDegree ≤ k) (x : ℝ) :
    ((Polynomial.derivative (R := ℝ))^[k] P).eval x = (k.factorial : ℝ) * P.coeff k := by
  have hdeg : ((Polynomial.derivative (R := ℝ))^[k] P).natDegree = 0 := by
    have h := Polynomial.natDegree_iterate_derivative (R := ℝ) P k
    omega
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hcoeff : ((Polynomial.derivative (R := ℝ))^[k] P).coeff 0
      = ((k.descFactorial k : ℕ) : ℝ) * P.coeff k := by
    have h := Polynomial.coeff_iterate_derivative (R := ℝ) (k := k) P 0
    simpa [nsmul_eq_mul] using h
  rw [hC, Polynomial.eval_C, hcoeff, Nat.descFactorial_self]

/-! ### The top Lagrange coefficient -/

/-- **The divided-difference mean value theorem.**  For `k+1` nodes, some chain value of order `k`
equals `k!` times the top coefficient of the Lagrange interpolant. -/
theorem exists_chain_eq_factorial_mul_coeff {U : Set ℝ} (hUc : U.OrdConnected) {F : ℕ → ℝ → ℝ}
    (k : ℕ) (hF : IsDerivChain k F U) (v : Fin (k + 1) → ℝ) (hmono : StrictMono v)
    (hmem : ∀ i, v i ∈ U) :
    ∃ ξ ∈ Icc (v 0) (v (Fin.last k)),
      F k ξ = (k.factorial : ℝ)
        * (Lagrange.interpolate Finset.univ v fun i => F 0 (v i)).coeff k := by
  classical
  set P : Polynomial ℝ := Lagrange.interpolate Finset.univ v fun i => F 0 (v i) with hP
  have hinj : Set.InjOn v (Finset.univ : Finset (Fin (k + 1))) := hmono.injective.injOn
  have hnodes : ∀ i, P.eval (v i) = F 0 (v i) := fun i =>
    Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)
  have hdeg : P.natDegree ≤ k := by
    have h1 : P.degree < ((Finset.univ : Finset (Fin (k + 1))).card : ℕ) :=
      Lagrange.degree_interpolate_lt _ hinj
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    rcases eq_or_ne P 0 with hzero | hPne
    · rw [hzero]; simp
    · rw [Polynomial.degree_eq_natDegree hPne] at h1
      exact Nat.lt_succ_iff.mp (by exact_mod_cast h1)
  obtain ⟨ξ, hξmem, hξ⟩ :=
    exists_chain_eq_zero hUc k _ (hF.sub_polynomial P) v hmono hmem
      (fun i => by simp [hnodes i])
  refine ⟨ξ, hξmem, ?_⟩
  have hξU : ξ ∈ U := hUc.out (hmem 0) (hmem (Fin.last k)) hξmem
  have := hξ
  simp only [sub_eq_zero] at this
  rw [this, eval_iterate_derivative_top hdeg]


/-! ### The Lagrange interpolation remainder -/

theorem iterate_derivative_add' (p q : Polynomial ℝ) (j : ℕ) :
    (Polynomial.derivative (R := ℝ))^[j] (p + q)
      = (Polynomial.derivative (R := ℝ))^[j] p + (Polynomial.derivative (R := ℝ))^[j] q := by
  induction j generalizing p q with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        Polynomial.derivative_add, ih]

/-- **Lagrange interpolation remainder for a chain.**  The error of the interpolant at `m` nodes
is at most `sup|F m| / m!` times the nodal product. -/
theorem abs_sub_interpolate_le {U : Set ℝ} (hUc : U.OrdConnected) {F : ℕ → ℝ → ℝ} {m : ℕ}
    (hF : IsDerivChain m F U) (v : Fin m → ℝ) (hmono : StrictMono v) (hmem : ∀ i, v i ∈ U)
    {M : ℝ} (hM : ∀ y ∈ U, |F m y| ≤ M) {x : ℝ} (hx : x ∈ U) :
    |F 0 x - (Lagrange.interpolate Finset.univ v fun i => F 0 (v i)).eval x|
      ≤ M / m.factorial * ∏ i, |x - v i| := by
  classical
  set P : Polynomial ℝ := Lagrange.interpolate Finset.univ v fun i => F 0 (v i) with hP
  have hinj : Set.InjOn v (Finset.univ : Finset (Fin m)) := hmono.injective.injOn
  have hnodes : ∀ i, P.eval (v i) = F 0 (v i) := fun i =>
    Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM x hx)
  have hfact : (0:ℝ) < (m.factorial : ℝ) := by positivity
  by_cases hxv : ∃ i, x = v i
  · obtain ⟨i, rfl⟩ := hxv
    rw [hnodes i, sub_self, abs_zero]
    have : (0:ℝ) ≤ ∏ i', |v i - v i'| := Finset.prod_nonneg fun _ _ => abs_nonneg _
    positivity
  · push Not at hxv
    set W : Polynomial ℝ := Lagrange.nodal Finset.univ v with hW
    have hWeval : ∀ y, W.eval y = ∏ i, (y - v i) := by
      intro y
      rw [hW, Lagrange.eval_nodal]
    have hWx : W.eval x ≠ 0 := by
      rw [hWeval]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hxv i)
    have hWnodes : ∀ i, W.eval (v i) = 0 := by
      intro i
      rw [hWeval]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    set lam : ℝ := (F 0 x - P.eval x) / W.eval x with hlam
    set Q : Polynomial ℝ := P + Polynomial.C lam * W with hQ
    -- `F 0 - Q` vanishes at the `m + 1` points
    set s : Finset ℝ := insert x (Finset.image v Finset.univ) with hs
    have hxnot : x ∉ Finset.image v Finset.univ := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      rintro ⟨i, hi⟩
      exact hxv i hi.symm
    have hcard : s.card = m + 1 := by
      rw [hs, Finset.card_insert_of_notMem hxnot,
        Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
    set pts : Fin (m + 1) → ℝ := fun i => ((s.orderIsoOfFin hcard i : ℝ)) with hpts
    have hptsmono : StrictMono pts := fun i j hij => (s.orderIsoOfFin hcard).strictMono hij
    have hptsmem : ∀ i, pts i ∈ s := fun i => (s.orderIsoOfFin hcard i).2
    have hsU : ∀ y ∈ s, y ∈ U := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact hx
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy'
        exact hmem i
    have hzeros : ∀ y ∈ s, F 0 y - Q.eval y = 0 := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · rw [hQ]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        rw [hlam, div_mul_cancel₀ _ hWx]
        ring
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy'
        rw [hQ]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        rw [hnodes i, hWnodes i]
        ring
    obtain ⟨ξ, hξmem, hξ⟩ :=
      exists_chain_eq_zero hUc m _ (hF.sub_polynomial Q) pts hptsmono
        (fun i => hsU _ (hptsmem i)) (fun i => by simpa using hzeros _ (hptsmem i))
    have hξU : ξ ∈ U := hUc.out (hsU _ (hptsmem 0)) (hsU _ (hptsmem (Fin.last m))) hξmem
    -- compute the `m`-th derivative of `Q`
    have hPzero : (Polynomial.derivative (R := ℝ))^[m] P = 0 := by
      have h1 : P.degree < ((Finset.univ : Finset (Fin m)).card : ℕ) :=
        Lagrange.degree_interpolate_lt _ hinj
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      exact Polynomial.iterate_derivative_eq_zero_of_degree_lt h1
    have hWmonic : W.Monic := by
      rw [hW, Lagrange.nodal_eq]
      exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
    have hWdeg : W.natDegree = m := by
      rw [hW, Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]
    have hWtop : ((Polynomial.derivative (R := ℝ))^[m] W).eval ξ = (m.factorial : ℝ) := by
      rw [eval_iterate_derivative_top (le_of_eq hWdeg)]
      have : W.coeff m = 1 := by
        rw [← hWdeg]
        exact hWmonic.coeff_natDegree
      rw [this, mul_one]
    have hQtop : ((Polynomial.derivative (R := ℝ))^[m] Q).eval ξ = lam * (m.factorial : ℝ) := by
      rw [hQ, iterate_derivative_add', hPzero,
        Polynomial.iterate_derivative_C_mul, Polynomial.eval_add, Polynomial.eval_zero,
        zero_add, Polynomial.eval_mul, Polynomial.eval_C, hWtop]
    have hFξ : F m ξ = lam * (m.factorial : ℝ) := by
      have := hξ
      simp only [sub_eq_zero] at this
      rw [this, hQtop]
    have hlamle : |lam| ≤ M / m.factorial := by
      rw [le_div_iff₀ hfact]
      have h1 : |lam| * (m.factorial : ℝ) = |F m ξ| := by
        rw [hFξ, abs_mul, abs_of_pos hfact]
      rw [h1]
      exact hM ξ hξU
    have hdiff : F 0 x - P.eval x = lam * W.eval x := by
      rw [hlam, div_mul_cancel₀ _ hWx]
    rw [hdiff, abs_mul, hWeval, Finset.abs_prod]
    exact mul_le_mul_of_nonneg_right hlamle (Finset.prod_nonneg fun _ _ => abs_nonneg _)

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
