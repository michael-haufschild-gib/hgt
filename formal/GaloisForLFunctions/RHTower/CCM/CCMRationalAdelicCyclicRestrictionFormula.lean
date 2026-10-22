import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicMoritaTraceFormula

/-!
# Higher CCM restriction formula on independent adelic class-space variables

For a cyclic monomial tuple `(t_j U_{k_j})_{0≤j≤n}` and independent nonzero adelic bases
`b_j`, the generalized Morita trace is

`0` unless `∏j k_j = 1`, and otherwise

`∑_{q∈ℚˣ} ∏j t_j((∏_{i<j} k_i)⁻¹ q b_j)`.

This file defines that exact formula on the actual rational adelic Bruhat core and proves absolute
summability.  The proof uses one `ℓ¹` orbit factor and uniform `ℓ∞` bounds for every remaining
factor; no finite-matrix truncation or formal infinite sum is used.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling

/-- Nonzero adelic base used by the rational Morita fiber. -/
structure CCMRationalAdelicMoritaBase where
  bInf : ℝ
  bInf_ne_zero : bInf ≠ 0
  bFin : CCMRationalFiniteAdeleˣ

/-- Product of scaling labels strictly before cyclic position `j`. -/
def ccmRationalAdelicCyclicPrefix {n : ℕ}
    (k : Fin (n + 1) → Scale) (j : Fin (n + 1)) : Scale :=
  ∏ i ∈ Finset.univ.filter (fun i => i < j), k i

@[simp]
theorem ccmRationalAdelicCyclicPrefix_zero {n : ℕ}
    (k : Fin (n + 1) → Scale) :
    ccmRationalAdelicCyclicPrefix k 0 = 1 := by
  simp [ccmRationalAdelicCyclicPrefix]

/-- Total scaling label of a cyclic monomial tuple. -/
def ccmRationalAdelicCyclicTotalScale {n : ℕ}
    (k : Fin (n + 1) → Scale) : Scale :=
  ∏ j, k j

/-- Summand in the higher CCM generalized matrix trace. -/
def ccmRationalAdelicCyclicRestrictionTerm {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) : ℂ :=
  ∏ j, ccmRationalAdelicBruhatTensorOrbitCoefficient
    (t j) (base j).bInf (base j).bFin
    ((ccmRationalAdelicCyclicPrefix k j).val⁻¹ * q)

/-- Product of the uniform bounds for all cyclic factors after position zero. -/
def ccmRationalAdelicCyclicRestrictionTailBound {n : ℕ}
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase) : ℝ :=
  ∏ j : Fin n,
    ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound
      (t j.succ) (base j.succ).bInf (base j.succ).bFin

theorem ccmRationalAdelicCyclicRestrictionTailBound_nonneg {n : ℕ}
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase) :
    0 ≤ ccmRationalAdelicCyclicRestrictionTailBound t base := by
  apply Finset.prod_nonneg
  intro j hj
  exact ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound_nonneg
    (t j.succ) (base j.succ).bInf (base j.succ).bFin

/-- Pointwise domination by one summable orbit factor times a constant tail bound. -/
theorem ccmRationalAdelicCyclicRestrictionTerm_norm_le {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (q : CCMRationalUnit) :
    ‖ccmRationalAdelicCyclicRestrictionTerm k t base q‖ ≤
      ‖ccmRationalAdelicBruhatTensorOrbitCoefficient
        (t 0) (base 0).bInf (base 0).bFin q‖ *
        ccmRationalAdelicCyclicRestrictionTailBound t base := by
  rw [ccmRationalAdelicCyclicRestrictionTerm, norm_prod,
    Fin.prod_univ_succ]
  simp only [ccmRationalAdelicCyclicPrefix_zero, ccmRationalAdelicScaling_one_val,
    inv_one, one_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  change (∏ j : Fin n,
      ‖ccmRationalAdelicBruhatTensorOrbitCoefficient
        (t j.succ) (base j.succ).bInf (base j.succ).bFin
        ((ccmRationalAdelicCyclicPrefix k j.succ).val⁻¹ * q)‖) ≤
    ∏ j : Fin n,
      ccmRationalAdelicBruhatTensorOrbitCoefficientLOneBound
        (t j.succ) (base j.succ).bInf (base j.succ).bFin
  apply Finset.prod_le_prod
  · intro j hj
    exact norm_nonneg _
  · intro j hj
    exact ccmRationalAdelicBruhatTensorOrbitCoefficient_norm_le_lOneBound
      (t j.succ) (base j.succ).bInf_ne_zero (base j.succ).bFin _

/-- Absolute convergence of the full higher CCM monomial restriction formula. -/
theorem ccmRationalAdelicCyclicRestrictionTerm_summable_norm {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase) :
    Summable (fun q : CCMRationalUnit =>
      ‖ccmRationalAdelicCyclicRestrictionTerm k t base q‖) := by
  let C := ccmRationalAdelicCyclicRestrictionTailBound t base
  have hhead : Summable (fun q : CCMRationalUnit =>
      ‖ccmRationalAdelicBruhatTensorOrbitCoefficient
        (t 0) (base 0).bInf (base 0).bFin q‖) :=
    ccmRationalAdelicBruhatTensorOrbitCoefficient_summable
      (t 0) (base 0).bInf_ne_zero (base 0).bFin
  apply Summable.of_nonneg_of_le
    (fun q => norm_nonneg _)
    (fun q => ccmRationalAdelicCyclicRestrictionTerm_norm_le k t base q)
  exact hhead.mul_right C

theorem ccmRationalAdelicCyclicRestrictionTerm_summable {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase) :
    Summable (ccmRationalAdelicCyclicRestrictionTerm k t base) :=
  summable_norm_iff.mp
    (ccmRationalAdelicCyclicRestrictionTerm_summable_norm k t base)

/-- Exact convergent higher CCM restriction of a cyclic monomial tuple. -/
def ccmRationalAdelicCyclicRestrictionMonomial {n : ℕ}
    (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase) : ℂ :=
  if ccmRationalAdelicCyclicTotalScale k = 1 then
    ∑' q, ccmRationalAdelicCyclicRestrictionTerm k t base q
  else 0

theorem ccmRationalAdelicCyclicRestrictionMonomial_eq_zero_of_totalScale_ne_one
    {n : ℕ} (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (hscale : ccmRationalAdelicCyclicTotalScale k ≠ 1) :
    ccmRationalAdelicCyclicRestrictionMonomial k t base = 0 := by
  simp [ccmRationalAdelicCyclicRestrictionMonomial, hscale]

theorem ccmRationalAdelicCyclicRestrictionMonomial_eq_tsum_of_totalScale_eq_one
    {n : ℕ} (k : Fin (n + 1) → Scale)
    (t : Fin (n + 1) → Core)
    (base : Fin (n + 1) → CCMRationalAdelicMoritaBase)
    (hscale : ccmRationalAdelicCyclicTotalScale k = 1) :
    ccmRationalAdelicCyclicRestrictionMonomial k t base =
      ∑' q, ccmRationalAdelicCyclicRestrictionTerm k t base q := by
  simp [ccmRationalAdelicCyclicRestrictionMonomial, hscale]

end RHTower
end GaloisForLFunctions
