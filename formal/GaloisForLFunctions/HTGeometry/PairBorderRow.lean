import GaloisForLFunctions.HTGeometry.CoordinateDerivationCommute
import GaloisForLFunctions.HTGeometry.PairChainRule

/-!
# The border row of the two-coordinate law

The row the whole determinant grows from is the gradient of `∑_(j<m) log p_j(X_j, X_(j+1))`.  In the
univariate law that gradient is diagonal — the `l`-th entry involves only `X_l` — but a
two-coordinate factor is seen by three consecutive coordinates, so the border row is genuinely
coupled.  What replaces diagonality is exactness: the row is a gradient, hence a closed form, and
`∂_k` of its `l`-th entry equals `∂_l` of its `k`-th.

That single symmetry is all the recursion needs.  Differentiating the law's value on the row and
using the chain rule turns the closed-form condition into the statement that the gradient of
`δ(∑ log p_j)` is the shifted border row — the same recursion the univariate peel runs on.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ}

/-! ## The logarithmic gradient of one factor -/

/-- The gradient of `log p_j(X_j, X_(j+1))` at the coordinate `l`. -/
noncomputable def pairLogTerm (p : ℕ → MvPolynomial (Fin 2) ℂ) (j l : ℕ) : CascadeField :=
  fpderiv l (pairFactor (p j) j) / pairFactor (p j) j

theorem pairLogTerm_eq_zero_of_ne {j l : ℕ} (h0 : l ≠ j) (h1 : l ≠ j + 1) :
    pairLogTerm p j l = 0 := by
  rw [pairLogTerm, fpderiv_pairFactor_of_ne h0 h1, zero_div]

theorem fpderiv_pairLogTerm_symm (j k l : ℕ) :
    fpderiv k (pairLogTerm p j l) = fpderiv l (pairLogTerm p j k) :=
  fpderiv_logDeriv_symm k l (pairFactor (p j) j)

theorem pairLogTerm_mem_pairLowSub {j m : ℕ} (h : j + 1 ≤ m) (l : ℕ) :
    pairLogTerm p j l ∈ pairLowSub p m := by
  rw [pairLogTerm, div_eq_mul_inv]
  exact Subalgebra.mul_mem _ (fpderiv_mem_pairLowSub l (pairFactor_mem_pairLowSub h))
    (inv_pairFactor_mem_pairLowSub h)

/-! ## The border row -/

/-- The border row at level `m`: the gradient of `∑_(j<m) log p_j(X_j, X_(j+1))`. -/
noncomputable def pairLogBorder (p : ℕ → MvPolynomial (Fin 2) ℂ) (m l : ℕ) : CascadeField :=
  ∑ j ∈ Finset.range m, pairLogTerm p j l

@[simp] theorem pairLogBorder_zero (p : ℕ → MvPolynomial (Fin 2) ℂ) (l : ℕ) :
    pairLogBorder p 0 l = 0 := by
  simp [pairLogBorder]

theorem pairLogBorder_succ (p : ℕ → MvPolynomial (Fin 2) ℂ) (m l : ℕ) :
    pairLogBorder p (m + 1) l = pairLogBorder p m l + pairLogTerm p m l := by
  rw [pairLogBorder, pairLogBorder, Finset.sum_range_succ]

/-- **Above the level the border row vanishes.** -/
theorem pairLogBorder_eq_zero_of_gt {m l : ℕ} (h : m < l) : pairLogBorder p m l = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjm : j < m := Finset.mem_range.mp hj
  exact pairLogTerm_eq_zero_of_ne (by omega) (by omega)

/-- **Raising the level does not change an entry that already fits.** -/
theorem pairLogBorder_of_le {m m' k : ℕ} (h : m ≤ m') (hk : k + 1 ≤ m) :
    pairLogBorder p m' k = pairLogBorder p m k := by
  have hsub : Finset.range m ⊆ Finset.range m' := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)
  refine (Finset.sum_subset hsub fun j hj hjn => ?_).symm
  have hjm : ¬ j < m := fun hc => hjn (Finset.mem_range.mpr hc)
  exact pairLogTerm_eq_zero_of_ne (by omega) (by omega)

/-- **The border row is a closed form.** -/
theorem fpderiv_pairLogBorder_symm (m k l : ℕ) :
    fpderiv k (pairLogBorder p m l) = fpderiv l (pairLogBorder p m k) := by
  rw [pairLogBorder, pairLogBorder, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => fpderiv_pairLogTerm_symm j k l

theorem pairLogBorder_mem_pairLowSub (m l : ℕ) : pairLogBorder p m l ∈ pairLowSub p m := by
  refine Subalgebra.sum_mem _ fun j hj => ?_
  have hjm : j < m := Finset.mem_range.mp hj
  exact pairLogTerm_mem_pairLowSub (by omega) l

/-! ## The response is the border row of its own level -/

/-- **Every response is the border row of its own level, times the jet.** -/
theorem pairResponse_eq_pairLogBorder (hne : ∀ j, pairFactor (p j) j ≠ 0) (k l : ℕ) :
    pairResponse p k l = pairLogBorder p l k * pairJet p l := by
  induction l with
  | zero => simp [pairResponse, pairJet_zero]
  | succ l ih =>
      have hF : pairFactor (p l) l ≠ 0 := hne l
      rw [pairResponse, pairJet_succ, Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [show fpderiv k (pairJet p l) = pairResponse p k l from rfl, ih,
        pairLogBorder_succ, pairLogTerm, div_eq_mul_inv]
      field_simp
      ring

/-! ## The law applied to the border row -/

/-- The law's value on the border row: `δ(∑_(j<m) log p_j)`. -/
noncomputable def pairLogSum (p : ℕ → MvPolynomial (Fin 2) ℂ) (m : ℕ) : CascadeField :=
  ∑ l ∈ Finset.range (m + 1), pairLogBorder p m l * pairJet p l

theorem pairLogSum_mem_pairLowSub (m : ℕ) : pairLogSum p m ∈ pairLowSub p m := by
  refine Subalgebra.sum_mem _ fun l hl => ?_
  have hlm : l < m + 1 := Finset.mem_range.mp hl
  exact Subalgebra.mul_mem _ (pairLogBorder_mem_pairLowSub m l)
    (pairJet_mem_pairLowSub (by omega))

/-- **The gradient of the law's value on the border row is the shifted border row.**  The whole
matrix therefore grows from one vector. -/
theorem gradient_pairLogSum_eq (m : ℕ) :
    (fun k => fpderiv k (pairLogSum p m)) = pairGradShift p m (pairLogBorder p m) := by
  funext k
  simp only [pairGradShift]
  rw [pairLogSum, map_sum]
  have hterm : ∀ l ∈ Finset.range (m + 1),
      fpderiv k (pairLogBorder p m l * pairJet p l)
        = pairJet p l * fpderiv l (pairLogBorder p m k)
          + pairResponse p k l * pairLogBorder p m l := by
    intro l _
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    rw [fpderiv_pairLogBorder_symm m k l, pairResponse]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  exact (pairDerivation_eq_sum (pairLogBorder_mem_pairLowSub m k)).symm

/-- **The gradient of an iterate of the law is an iterate of the shifted operator on the border
row.** -/
theorem gradient_iterate_pairLogSum (m r : ℕ) :
    (fun l => fpderiv l (((pairDerivation p : CascadeField → CascadeField)^[r])
        (pairLogSum p m)))
      = ((pairGradShift p m)^[r + 1]) (pairLogBorder p m) := by
  rw [gradient_iterate_pair_eq r (pairLogSum_mem_pairLowSub m),
    gradient_pairLogSum_eq, Function.iterate_succ_apply]

end GaloisForLFunctions.HTGeometry
