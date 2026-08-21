import GaloisForLFunctions.HTGeometry.BorelWeil.PairSplitting

/-!
# The weight of a cell equation

All the cell equations scale by the same Borel character, the one whose exponent at an index counts
the leading minors that involve it.  Since every cell equation divides the cover equation, the
product of the cell equations of a set of cells is a unit of the flag localization, semi-invariant
of that weight times the number of cells.  Multiplying by such a unit trades denominators along a
set of cells for a shift of the weight, and the shift is monotone along the simple root, so it
preserves the condition `⟨λ, α_i^∨⟩ ≥ −1`.

## Main definitions

* `weightD` — the weight of one cell equation.

## Main results

* `cellChar_eq_borelCharZ`, `algebraMap_denomOf_mem_flagSemiInv`, `isUnit_algebraMap_denomOf`
* `weightD_sub_nonneg` — the shift is nonnegative along a simple root.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k] [Infinite k]

/-- The weight by which one cell equation scales. -/
def weightD (N : ℕ) (l : Fin N) : ℤ :=
  ((Finset.univ.filter (fun j : Fin N => (l : ℕ) < (j : ℕ) + 1)).card : ℤ)

theorem weightD_sub_nonneg {i : Fin N} (hi : (i : ℕ) + 1 < N) :
    0 ≤ weightD N i - weightD N (⟨(i : ℕ) + 1, hi⟩ : Fin N) := by
  classical
  have hval : ((⟨(i : ℕ) + 1, hi⟩ : Fin N) : ℕ) = (i : ℕ) + 1 := rfl
  have hsub : (Finset.univ.filter (fun j : Fin N => ((⟨(i : ℕ) + 1, hi⟩ : Fin N) : ℕ)
      < (j : ℕ) + 1)) ⊆ Finset.univ.filter (fun j : Fin N => (i : ℕ) < (j : ℕ) + 1) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    have := hj.2
    omega
  have hcard : weightD N (⟨(i : ℕ) + 1, hi⟩ : Fin N) ≤ weightD N i := by
    rw [weightD, weightD]
    exact_mod_cast Finset.card_le_card hsub
  omega

theorem cellChar_eq_borelCharZ (σ : Equiv.Perm (Fin N)) (B : Matrix (Fin N) (Fin N) k) :
    cellChar N k σ B = borelCharZ (weightD N) B := by
  classical
  rw [cellChar, borelCharZ, Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [weightD, zpow_natCast, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem substRight_denomOf (J : Finset (Equiv.Perm (Fin N)))
    {B : Matrix (Fin N) (Fin N) k} (hB : B.BlockTriangular id) :
    substRight B (denomOf N k J)
      = MvPolynomial.C (∏ τ ∈ J, cellChar N k τ B) * denomOf N k J := by
  rw [denomOf, map_prod, map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => substRight_cellDenomPoly τ hB

theorem borelCharZ_nsmul (c : ℕ) (ν : Fin N → ℤ) (B : Matrix (Fin N) (Fin N) k) :
    borelCharZ (fun l => (c : ℤ) * ν l) B = (borelCharZ ν B) ^ c := by
  rw [borelCharZ, borelCharZ, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [mul_comm, zpow_mul, zpow_natCast]

theorem algebraMap_denomOf_mem_flagSemiInv (J : Finset (Equiv.Perm (Fin N))) :
    algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (denomOf N k J)
      ∈ flagSemiInv N k (fun l => (J.card : ℤ) * weightD N l) := by
  classical
  intro B hB
  have hchar : (∏ τ ∈ J, cellChar N k τ B) = borelCharZ (fun l => (J.card : ℤ) * weightD N l) B := by
    rw [borelCharZ_nsmul, ← Finset.prod_const]
    exact Finset.prod_congr rfl fun τ _ => cellChar_eq_borelCharZ τ B
  rw [substRightAway_algebraMap, substRight_denomOf J hB.1, hchar, map_mul, Algebra.smul_def,
    IsScalarTower.algebraMap_apply k (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)]
  simp only [MvPolynomial.algebraMap_eq]

theorem denomOf_dvd_totalDenom (J : Finset (Equiv.Perm (Fin N))) :
    denomOf N k J ∣ totalDenom N k := by
  classical
  rw [denomOf, totalDenom]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ J)

theorem isUnit_algebraMap_denomOf (J : Finset (Equiv.Perm (Fin N))) :
    IsUnit (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (denomOf N k J)) :=
  isUnit_of_dvd_unit (map_dvd _ (denomOf_dvd_totalDenom J)) isUnit_algebraMap_totalDenom

/-- The cell equations of a set of cells, as a unit of the localization. -/
noncomputable def denomUnit (N : ℕ) (k : Type*) [Field k] [Infinite k]
    (J : Finset (Equiv.Perm (Fin N))) : (FlagLoc N k)ˣ :=
  (isUnit_algebraMap_denomOf J).unit

@[simp] theorem coe_denomUnit (J : Finset (Equiv.Perm (Fin N))) :
    ((denomUnit N k J : (FlagLoc N k)ˣ) : FlagLoc N k)
      = algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (denomOf N k J) :=
  IsUnit.unit_spec _

end GaloisForLFunctions.HTGeometry.BorelWeil
