import GaloisForLFunctions.HTGeometry.PairCoordinateField
import GaloisForLFunctions.HTGeometry.PairBorderRow

/-!
# The border row with a head factor

The limit of the border row as the newest coordinate goes to infinity is not the border row one
level down: the last placed polynomial `p_(m−1)(X_(m−1), X_m)` behaves like
`a_(m−1)(X_(m−1))·X_m`, so its logarithm contributes `log a_(m−1)(X_(m−1))` in the limit.  The class
the peel runs on therefore carries one extra univariate factor at the newest coordinate — a *head*.

The head changes nothing structurally: `log g(X_m)` is again a logarithm, so the enlarged row is
again a gradient, hence a closed form, and the gradient of the law's value on it is again the
shifted row.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ}

theorem fpderiv_fact_self (q : Polynomial ℂ) (m : ℕ) :
    fpderiv m (fact q m) = fact q.derivative m := by
  rw [derivation_fact, fpderiv_fx_self, mul_one]

/-! ## The row -/

/-- The border row at level `m` with a head factor `g` at the newest coordinate: the gradient of
`∑_(j<m) log p_j(X_j, X_(j+1)) + log g(X_m)`. -/
noncomputable def headBorder (p : ℕ → MvPolynomial (Fin 2) ℂ) (g : Polynomial ℂ) (m l : ℕ) :
    CascadeField :=
  pairLogBorder p m l + fpderiv l (fact g m) / fact g m

theorem headBorder_of_ne {g : Polynomial ℂ} {m l : ℕ} (h : l ≠ m) :
    headBorder p g m l = pairLogBorder p m l := by
  rw [headBorder, fpderiv_fact_of_ne (fun hc => h hc.symm), zero_div, add_zero]

theorem headBorder_self (g : Polynomial ℂ) (m : ℕ) :
    headBorder p g m m = pairLogBorder p m m + logFactor g m := by
  rw [headBorder, fpderiv_fact_self, logFactor]

theorem headBorder_one (m l : ℕ) : headBorder p 1 m l = pairLogBorder p m l := by
  have h1 : fact (1 : Polynomial ℂ) m = 1 := by
    rw [fact, univFactor, map_one, map_one]
  rw [headBorder, h1, (fpderiv l).map_one_eq_zero, zero_div, add_zero]

theorem headBorder_eq_zero_of_gt {g : Polynomial ℂ} {m l : ℕ} (h : m < l) :
    headBorder p g m l = 0 := by
  rw [headBorder_of_ne (by omega), pairLogBorder_eq_zero_of_gt h]

/-- **The row with a head is still a closed form.** -/
theorem fpderiv_headBorder_symm (g : Polynomial ℂ) (m k l : ℕ) :
    fpderiv k (headBorder p g m l) = fpderiv l (headBorder p g m k) := by
  rw [headBorder, headBorder, map_add, map_add, fpderiv_pairLogBorder_symm m k l,
    fpderiv_logDeriv_symm k l (fact g m)]

theorem headBorder_mem_coordField (g : Polynomial ℂ) (m l : ℕ) :
    headBorder p g m l ∈ coordField m := by
  refine add_mem ?_ (div_mem (fpderiv_mem_coordField l (fact_mem_coordField (le_refl m) g))
    (fact_mem_coordField (le_refl m) g))
  refine sum_mem fun j hj => ?_
  have hjm : j < m := Finset.mem_range.mp hj
  exact div_mem (fpderiv_mem_coordField l (pairFactor_mem_coordField (by omega) (p j)))
    (pairFactor_mem_coordField (by omega) (p j))

/-! ## The law's value on the row -/

/-- The law's value on the row with a head. -/
noncomputable def headSum (p : ℕ → MvPolynomial (Fin 2) ℂ) (g : Polynomial ℂ) (m : ℕ) :
    CascadeField :=
  ∑ l ∈ Finset.range (m + 1), headBorder p g m l * pairJet p l

theorem headSum_mem_coordField (g : Polynomial ℂ) (m : ℕ) : headSum p g m ∈ coordField m := by
  refine sum_mem fun l hl => ?_
  have hlm : l < m + 1 := Finset.mem_range.mp hl
  exact mul_mem (headBorder_mem_coordField g m l) (pairJet_mem_coordField (by omega))

/-- **The gradient of the law's value on the row is the shifted row.** -/
theorem gradient_headSum_eq (g : Polynomial ℂ) (m : ℕ) :
    (fun k => fpderiv k (headSum p g m)) = pairGradShift p m (headBorder p g m) := by
  funext k
  simp only [pairGradShift]
  rw [headSum, map_sum]
  have hterm : ∀ l ∈ Finset.range (m + 1),
      fpderiv k (headBorder p g m l * pairJet p l)
        = pairJet p l * fpderiv l (headBorder p g m k)
          + pairResponse p k l * headBorder p g m l := by
    intro l _
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    rw [fpderiv_headBorder_symm g m k l, pairResponse]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  congr 1
  exact (pairDerivation_eq_sum_coordField (headBorder_mem_coordField g m k)).symm

/-- **The gradient of an iterate of the law is an iterate of the shifted operator on the row.** -/
theorem gradient_iterate_headSum (g : Polynomial ℂ) (m r : ℕ) :
    (fun l => fpderiv l (((pairDerivation p : CascadeField → CascadeField)^[r]) (headSum p g m)))
      = ((pairGradShift p m)^[r + 1]) (headBorder p g m) := by
  rw [gradient_iterate_pair_eq_coordField r (headSum_mem_coordField g m),
    gradient_headSum_eq, Function.iterate_succ_apply]

end GaloisForLFunctions.HTGeometry
