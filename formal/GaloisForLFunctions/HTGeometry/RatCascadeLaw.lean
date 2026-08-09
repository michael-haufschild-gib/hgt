import GaloisForLFunctions.HTGeometry.CommonClearedJets
import GaloisForLFunctions.HTGeometry.AffineOutputDeterminant
import GaloisForLFunctions.HTGeometry.ExpPolyCascade

/-!
# The cleared law of a rational first-order linear cascade

A cascade of maps solving `h' = a(z)·h + b(z)` with rational coefficients has, at each level, the
cleared equation

`(ld·cd)(z)·h' = (ln·cd)(z)·h + (cn·ld)(z)`,

a polynomial identity valid at every point — the denominators are cleared once and for all.  The
factor's numerator and denominator are then polynomials in two consecutive coordinates and in one
coordinate respectively, and the jet of a level is their product.

Multiplying by the coordinates the cascade does not reach turns that into the *single* common
denominator the transfer wants, simultaneously in the rational model and pointwise at the states.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace RatAffineFam

variable (R : RatAffineFam)

/-! ## The cleared factor -/

/-- The numerator of the factor at level `j`. -/
noncomputable def numFac (j : ℕ) : MvPolynomial ℕ ℂ :=
  univFactor (R.ln j * R.cd j) j * MvPolynomial.X (j + 1)
    + univFactor (R.cn j * R.ld j) j

/-- The denominator of the factor at level `j`. -/
noncomputable def denFac (j : ℕ) : MvPolynomial ℕ ℂ :=
  univFactor (R.ld j * R.cd j) j

theorem univFactor_mul (p q : Polynomial ℂ) (j : ℕ) :
    univFactor (p * q) j = univFactor p j * univFactor q j :=
  map_mul (Polynomial.aeval (MvPolynomial.X j)) p q

theorem denFac_ne_zero (j : ℕ) : R.denFac j ≠ 0 :=
  univFactor_ne_zero (mul_ne_zero (R.ld_ne_zero j) (R.cd_ne_zero j)) j

theorem algebraMap_numFac (j : ℕ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField (R.numFac j)
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (R.denFac j) * R.toAffineFam.fac j := by
  have hld : fact (R.ld j) j ≠ 0 := fact_ne_zero (R.ld_ne_zero j) j
  have hcd : fact (R.cd j) j ≠ 0 := fact_ne_zero (R.cd_ne_zero j) j
  have hnum : algebraMap (MvPolynomial ℕ ℂ) CascadeField (R.numFac j)
      = fact (R.ln j) j * fact (R.cd j) j * fx (j + 1)
        + fact (R.cn j) j * fact (R.ld j) j := by
    rw [numFac, map_add, map_mul, univFactor_mul, univFactor_mul, map_mul, map_mul]
    rfl
  have hden : algebraMap (MvPolynomial ℕ ℂ) CascadeField (R.denFac j)
      = fact (R.ld j) j * fact (R.cd j) j := by
    rw [denFac, univFactor_mul, map_mul]
    rfl
  rw [hnum, hden, AffineFam.fac, lead_eq, cnst_eq, ratFact, ratFact]
  field_simp

/-! ## The cleared jets -/

/-- The common denominator of the jets up to level `N`. -/
noncomputable def denTot (N : ℕ) : MvPolynomial ℕ ℂ := ∏ j ∈ Finset.range N, R.denFac j

/-- The cleared numerator of the jet of level `k`, against the common denominator. -/
noncomputable def clearedJet (N k : ℕ) : MvPolynomial ℕ ℂ :=
  (∏ j ∈ Finset.range k, R.numFac j) * ∏ j ∈ Finset.Ico k N, R.denFac j

theorem denTot_ne_zero (N : ℕ) : R.denTot N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => R.denFac_ne_zero j

theorem algebraMap_clearedJet {N k : ℕ} (hk : k ≤ N) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField (R.denTot N)
        * R.toAffineFam.toPairFam.jet k
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (R.clearedJet N k) := by
  have hsplit : R.denTot N
      = (∏ j ∈ Finset.range k, R.denFac j) * ∏ j ∈ Finset.Ico k N, R.denFac j := by
    rw [denTot, ← Finset.prod_range_mul_prod_Ico R.denFac hk]
  rw [hsplit, clearedJet, PairFam.jet, map_mul, map_mul, map_prod, map_prod, map_prod]
  rw [show (∏ j ∈ Finset.range k,
        algebraMap (MvPolynomial ℕ ℂ) CascadeField (R.denFac j))
      * (∏ j ∈ Finset.Ico k N, algebraMap (MvPolynomial ℕ ℂ) CascadeField (R.denFac j))
      * ∏ j ∈ Finset.range k, R.toAffineFam.toPairFam.fac j
      = (∏ j ∈ Finset.range k,
          (algebraMap (MvPolynomial ℕ ℂ) CascadeField (R.denFac j)
            * R.toAffineFam.toPairFam.fac j))
        * ∏ j ∈ Finset.Ico k N, algebraMap (MvPolynomial ℕ ℂ) CascadeField (R.denFac j) by
    rw [Finset.prod_mul_distrib]
    ring]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  exact (R.algebraMap_numFac j).symm

/-! ## Membership in the low polynomials -/

theorem univFactor_mem_lowPoly {j N : ℕ} (h : j ≤ N) (q : Polynomial ℂ) :
    univFactor q j ∈ lowPoly N := by
  induction q using Polynomial.induction_on with
  | C a =>
      have hc : univFactor (Polynomial.C a) j = MvPolynomial.C a := by
        simp [univFactor]
      rw [hc]
      exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq =>
      have hs : univFactor (p + q) j = univFactor p j + univFactor q j := by
        simp [univFactor]
      rw [hs]
      exact add_mem hp hq
  | monomial n a _ =>
      have hm : univFactor (Polynomial.C a * Polynomial.X ^ (n + 1)) j
          = MvPolynomial.C a * MvPolynomial.X j ^ (n + 1) := by
        simp [univFactor]
      rw [hm]
      exact mul_mem (Subalgebra.algebraMap_mem _ a) (pow_mem (X_mem_lowPoly h) (n + 1))

theorem numFac_mem_lowPoly {j N : ℕ} (h : j + 1 ≤ N) : R.numFac j ∈ lowPoly N :=
  add_mem (mul_mem (univFactor_mem_lowPoly (by omega) _) (X_mem_lowPoly h))
    (univFactor_mem_lowPoly (by omega) _)

theorem denFac_mem_lowPoly {j N : ℕ} (h : j ≤ N) : R.denFac j ∈ lowPoly N :=
  univFactor_mem_lowPoly h _

theorem denTot_mem_lowPoly (N : ℕ) : R.denTot N ∈ lowPoly N := by
  refine prod_mem fun j hj => ?_
  have hjm : j < N := Finset.mem_range.mp hj
  exact R.denFac_mem_lowPoly (by omega)

theorem clearedJet_mem_lowPoly {N k : ℕ} (hk : k ≤ N) : R.clearedJet N k ∈ lowPoly N := by
  refine mul_mem (prod_mem fun j hj => ?_) (prod_mem fun j hj => ?_)
  · have hjk : j < k := Finset.mem_range.mp hj
    exact R.numFac_mem_lowPoly (by omega)
  · have hjm := Finset.mem_Ico.mp hj
    exact R.denFac_mem_lowPoly (by omega)

end RatAffineFam

end GaloisForLFunctions.HTGeometry
