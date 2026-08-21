/-
# Divided differences: the mean value theorem and denominator clearing

`Lemma 4` of Coleman--Zwald.  For `m + 1` increasing nodes the divided difference
`∑ i, f (t i) / ∏ j ≠ i, (t i - t j)` equals `f⁽ᵐ⁾(u) / m!` for some interior `u`.  Together with the
observation that the normalisation `∏ i, ∏ j ≠ i, (t i - t j)` clears every denominator, this is the
engine of the gap estimate in Hilbert's irreducibility theorem: at integer nodes carrying integer
values the normalised divided difference is a *nonzero integer*, hence at least one in absolute
value, which forces the nodes to be far apart once `f⁽ᵐ⁾` is small.

Derivatives are carried as an explicit sequence `D : ℕ → ℝ → ℝ` with `HasDerivAt (D j) (D (j+1) x) x`
on an open set; this avoids every `iteratedDeriv` regularity side condition.

Main results:
* `exists_iterated_rolle` — iterated Rolle for an explicit derivative sequence.
* `exists_dividedDiff_eq` — the divided-difference mean value theorem.
* `dividedDiff_mul_nodeProd` — denominator clearing.
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Order.Fin.Basic

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial Finset

/-- The divided difference of `f` at the nodes `t`. -/
noncomputable def dividedDiff {m : ℕ} (f : ℝ → ℝ) (t : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i, f (t i) / ∏ j ∈ Finset.univ.erase i, (t i - t j)

/-- The full node-difference product, which clears every denominator of `dividedDiff`. -/
noncomputable def nodeProd {m : ℕ} (t : Fin (m + 1) → ℝ) : ℝ :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, (t i - t j)

theorem prod_erase_ne_zero {m : ℕ} {t : Fin (m + 1) → ℝ} (hinj : Function.Injective t)
    (i : Fin (m + 1)) : (∏ j ∈ Finset.univ.erase i, (t i - t j)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  exact sub_ne_zero_of_ne fun h => (Finset.mem_erase.mp hj).1 (hinj h.symm)

/-- **Clearing denominators.**  `nodeProd` times the divided difference is a polynomial expression
in the values and the node differences. -/
theorem dividedDiff_mul_nodeProd {m : ℕ} (f : ℝ → ℝ) {t : Fin (m + 1) → ℝ}
    (hinj : Function.Injective t) :
    dividedDiff f t * nodeProd t
      = ∑ i, f (t i) * ∏ k ∈ Finset.univ.erase i, ∏ j ∈ Finset.univ.erase k, (t k - t j) := by
  classical
  rw [dividedDiff, nodeProd, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (∏ j ∈ Finset.univ.erase i, (t i - t j)) ≠ 0 := prod_erase_ne_zero hinj i
  have hsplit : (∏ k, ∏ j ∈ Finset.univ.erase k, (t k - t j))
      = (∏ j ∈ Finset.univ.erase i, (t i - t j))
        * ∏ k ∈ Finset.univ.erase i, ∏ j ∈ Finset.univ.erase k, (t k - t j) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  rw [hsplit, div_mul_eq_mul_div, mul_comm (∏ j ∈ Finset.univ.erase i, (t i - t j)),
    ← mul_assoc, mul_div_assoc, div_self hi, mul_one]

/-! ### Iterated Rolle -/

/-- One Rolle step: `m + 2` zeros of `E₀` give `m + 1` interior zeros of its derivative `E₁`. -/
theorem exists_rolle_step {m : ℕ} {U : Set ℝ} {E₀ E₁ : ℝ → ℝ}
    (hE : ∀ x ∈ U, HasDerivAt E₀ (E₁ x) x)
    (t : Fin (m + 2) → ℝ) (hmono : StrictMono t)
    (hsub : Set.Icc (t 0) (t (Fin.last (m + 1))) ⊆ U)
    (hzero : ∀ i, E₀ (t i) = 0) :
    ∃ c : Fin (m + 1) → ℝ, StrictMono c ∧ (∀ i, t 0 < c i ∧ c i < t (Fin.last (m + 1))) ∧
      ∀ i, E₁ (c i) = 0 := by
  classical
  have key : ∀ i : Fin (m + 1), ∃ x ∈ Set.Ioo (t i.castSucc) (t i.succ), E₁ x = 0 := by
    intro i
    have hlt : t i.castSucc < t i.succ := hmono Fin.castSucc_lt_succ
    have hIcc : Set.Icc (t i.castSucc) (t i.succ) ⊆ U := by
      refine subset_trans (Set.Icc_subset_Icc ?_ ?_) hsub
      · exact hmono.monotone (Fin.zero_le _)
      · exact hmono.monotone (Fin.le_last _)
    refine exists_hasDerivAt_eq_zero (f := E₀) (f' := E₁) hlt ?_ ?_ ?_
    · exact fun x hx => ((hE x (hIcc hx)).continuousAt).continuousWithinAt
    · rw [hzero, hzero]
    · exact fun x hx => hE x (hIcc (Set.Ioo_subset_Icc_self hx))
  choose c hc hc0 using key
  refine ⟨c, ?_, ?_, hc0⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    have h1 : c i.castSucc < t (i.castSucc).succ := (hc i.castSucc).2
    have h2 : t (i.succ).castSucc < c i.succ := (hc i.succ).1
    rw [Fin.succ_castSucc] at h1
    exact lt_trans h1 h2
  · intro i
    refine ⟨lt_of_le_of_lt ?_ (hc i).1, lt_of_lt_of_le (hc i).2 ?_⟩
    · exact hmono.monotone (Fin.zero_le _)
    · exact hmono.monotone (Fin.le_last _)

/-- **Iterated Rolle.**  If `E 0` vanishes at `m + 1` increasing nodes and `E (j+1)` is the
derivative of `E j` on an open set containing them, then `E m` has an interior zero. -/
theorem exists_iterated_rolle : ∀ (m : ℕ), 0 < m → ∀ {U : Set ℝ} (E : ℕ → ℝ → ℝ),
    (∀ j, j < m → ∀ x ∈ U, HasDerivAt (E j) (E (j + 1) x) x) →
    ∀ (t : Fin (m + 1) → ℝ), StrictMono t → Set.Icc (t 0) (t (Fin.last m)) ⊆ U →
    (∀ i, E 0 (t i) = 0) →
    ∃ u ∈ Set.Ioo (t 0) (t (Fin.last m)), E m u = 0 := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ k ih =>
    intro _ U E hE t hmono hsub hzero
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hlt : t 0 < t (Fin.last 1) := hmono (by decide)
      refine exists_hasDerivAt_eq_zero (f := E 0) (f' := E 1) hlt ?_ ?_ ?_
      · exact fun x hx => ((hE 0 (by omega) x (hsub hx)).continuousAt).continuousWithinAt
      · rw [hzero, hzero]
      · exact fun x hx => hE 0 (by omega) x (hsub (Set.Ioo_subset_Icc_self hx))
    · obtain ⟨c, hcmono, hcrange, hczero⟩ :=
        exists_rolle_step (m := k) (E₀ := E 0) (E₁ := E 1)
          (fun x hx => hE 0 (by omega) x hx) t hmono hsub hzero
      have hcsub : Set.Icc (c 0) (c (Fin.last k)) ⊆ U := by
        refine subset_trans (Set.Icc_subset_Icc ?_ ?_) hsub
        · exact le_of_lt (hcrange 0).1
        · exact le_of_lt (hcrange (Fin.last k)).2
      obtain ⟨u, hu, hu0⟩ :=
        ih hk (fun j => E (j + 1)) (fun j hj x hx => hE (j + 1) (by omega) x hx) c hcmono hcsub
          hczero
      refine ⟨u, ⟨?_, ?_⟩, hu0⟩
      · exact lt_trans (hcrange 0).1 hu.1
      · exact lt_trans hu.2 (hcrange (Fin.last k)).2

/-! ### The divided-difference mean value theorem -/

/-- The `m`-th derivative of a polynomial of degree at most `m` is the constant `m! * coeff m`. -/
theorem iterate_derivative_eq_C {m : ℕ} {P : ℝ[X]} (hP : P.natDegree ≤ m) :
    (Polynomial.derivative)^[m] P = C ((m.factorial : ℝ) * P.coeff m) := by
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_iterate_derivative]
  cases n with
  | zero => simp [Nat.descFactorial_self]
  | succ n =>
    have hz : P.coeff (n + 1 + m) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hz]

/-- **Divided-difference mean value theorem.**  `f[t₀,…,t_m] = f⁽ᵐ⁾(u)/m!` for some interior `u`. -/
theorem exists_dividedDiff_eq {m : ℕ} (hm : 0 < m) {U : Set ℝ} (D : ℕ → ℝ → ℝ)
    (hD : ∀ j, j < m → ∀ x ∈ U, HasDerivAt (D j) (D (j + 1) x) x)
    (t : Fin (m + 1) → ℝ) (hmono : StrictMono t)
    (hsub : Set.Icc (t 0) (t (Fin.last m)) ⊆ U) :
    ∃ u ∈ Set.Ioo (t 0) (t (Fin.last m)),
      dividedDiff (D 0) t = D m u / (m.factorial : ℝ) := by
  classical
  have hvs : Set.InjOn t (Finset.univ : Finset (Fin (m + 1))) := fun a _ b _ h =>
    hmono.injective h
  set P : ℝ[X] := Lagrange.interpolate Finset.univ t (fun i => D 0 (t i)) with hPdef
  have hcard : (Finset.univ : Finset (Fin (m + 1))).card = m + 1 := by simp
  have hPdeg : P.degree < ((Finset.univ : Finset (Fin (m + 1))).card : ℕ) :=
    Lagrange.degree_interpolate_lt _ hvs
  have hPeval : ∀ i, P.eval (t i) = D 0 (t i) := fun i =>
    Lagrange.eval_interpolate_at_node _ hvs (Finset.mem_univ i)
  have hPnat : P.natDegree ≤ m := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · have := Polynomial.degree_eq_natDegree hP0 ▸ hPdeg
      rw [hcard] at this
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hcoeff : dividedDiff (D 0) t = P.coeff m := by
    have := Lagrange.coeff_eq_sum (v := t) (s := (Finset.univ : Finset (Fin (m + 1)))) hvs
      (P := P) hPdeg
    rw [hcard] at this
    simp only [Nat.add_sub_cancel] at this
    rw [this, dividedDiff]
    exact Finset.sum_congr rfl fun i _ => by rw [hPeval i]
  have hEzero : ∀ i, (fun (j : ℕ) (x : ℝ) => D j x - Polynomial.eval x
      ((Polynomial.derivative)^[j] P)) 0 (t i) = 0 := by
    intro i
    simp only [Function.iterate_zero, id_eq]
    rw [hPeval i]
    ring
  have hEderiv : ∀ j, j < m → ∀ x ∈ U,
      HasDerivAt (fun y => D j y - Polynomial.eval y ((Polynomial.derivative)^[j] P))
        (D (j + 1) x - Polynomial.eval x ((Polynomial.derivative)^[j + 1] P)) x := by
    intro j hj x hx
    have h1 : HasDerivAt (D j) (D (j + 1) x) x := hD j hj x hx
    have h2 : HasDerivAt (fun y => Polynomial.eval y ((Polynomial.derivative)^[j] P))
        (Polynomial.eval x ((Polynomial.derivative)^[j + 1] P)) x := by
      rw [Function.iterate_succ_apply']
      exact Polynomial.hasDerivAt _ x
    exact h1.sub h2
  obtain ⟨u, hu, hu0⟩ := exists_iterated_rolle m hm
    (fun (j : ℕ) (x : ℝ) => D j x - Polynomial.eval x ((Polynomial.derivative)^[j] P))
    hEderiv t hmono hsub hEzero
  refine ⟨u, hu, ?_⟩
  have : D m u = (m.factorial : ℝ) * P.coeff m := by
    simp only [sub_eq_zero] at hu0
    rw [hu0, iterate_derivative_eq_C hPnat, Polynomial.eval_C]
  rw [hcoeff, this]
  field_simp

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
