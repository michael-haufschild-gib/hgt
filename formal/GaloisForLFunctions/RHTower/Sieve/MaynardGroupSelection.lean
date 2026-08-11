import GaloisForLFunctions.RHTower.Sieve.MaynardGroupedFactor

/-!
# Multiplicative selection of a large Maynard group

The all-short argument does not need to choose an exponent partition.  A finite product which is
large relative to the product of its lengths forces one group in *every* finite grouping to be
large relative to that group's own multiplicative length.  This file proves that statement without
assuming any factor or group value is nonzero: positivity is forced by the global lower bound.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- Fibre of a finite grouping map. -/
abbrev GroupFibre {ι κ : Type*} (g : ι → κ) (j : κ) := {i : ι // g i = j}

/-- Product over one fibre of a grouping map. -/
def fibreProduct {ι κ M : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [CommMonoid M]
    (g : ι → κ) (f : ι → M) (j : κ) : M :=
  ∏ i : GroupFibre g j, f i

/-- Products over all fibres recover the original product, including when some fibres are empty. -/
theorem prod_fibreProduct {ι κ M : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [CommMonoid M]
    (g : ι → κ) (f : ι → M) :
    ∏ j, fibreProduct g f j = ∏ i, f i := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ g f]
  apply Finset.prod_congr rfl
  intro j _hj
  rw [fibreProduct, ← Finset.prod_subtype
    (Finset.univ.filter fun i => g i = j) (by simp) f]

/-- **Multiplicative pigeonhole.**  A positive product threshold forces one factor to cross its
own threshold.  Individual values need only be nonnegative; the global inequality rules out their
vanishing. -/
theorem exists_rpow_le_of_prod_rpow_le_prod
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (A v : ι → ℝ) (e : ℝ)
    (hA : ∀ i, 0 < A i) (hv : ∀ i, 0 ≤ v i)
    (hlarge : (∏ i, A i) ^ e ≤ ∏ i, v i) :
    ∃ i, A i ^ e ≤ v i := by
  have hAprod : 0 < ∏ i, A i := Finset.prod_pos fun i _ => hA i
  have hthreshold : 0 < (∏ i, A i) ^ e := Real.rpow_pos_of_pos hAprod e
  have hvprod : 0 < ∏ i, v i := hthreshold.trans_le hlarge
  have hvpos : ∀ i, 0 < v i := by
    intro i
    by_contra hnot
    have hzero : v i = 0 := le_antisymm (le_of_not_gt hnot) (hv i)
    have hprodzero : ∏ j, v j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hzero
    rw [hprodzero] at hvprod
    exact (lt_irrefl 0) hvprod
  by_contra hnone
  push Not at hnone
  have hstrict : (∏ i, v i) < ∏ i, A i ^ e :=
    Finset.prod_lt_prod_of_nonempty
      (fun i _ => hvpos i) (fun i _ => hnone i) Finset.univ_nonempty
  have hrpow : ∏ i, A i ^ e = (∏ i, A i) ^ e :=
    Real.finsetProd_rpow Finset.univ A (fun i _ => (hA i).le) e
  rw [hrpow] at hstrict
  exact (not_lt_of_ge hlarge) hstrict

/-- **Fibrewise multiplicative pigeonhole.**  For every finite grouping, some fibre inherits the
large-value threshold with its exact multiplicative length. -/
theorem exists_fibre_rpow_le
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (g : ι → κ) (A : ι → ℝ) (v : κ → ℝ) (e : ℝ)
    (hA : ∀ i, 0 < A i) (hv : ∀ j, 0 ≤ v j)
    (hlarge : (∏ i, A i) ^ e ≤ ∏ j, v j) :
    ∃ j, (fibreProduct g A j) ^ e ≤ v j := by
  have hAfibre : ∀ j, 0 < fibreProduct g A j := by
    intro j
    exact Finset.prod_pos fun i _ => hA i
  have hlarge' : (∏ j, fibreProduct g A j) ^ e ≤ ∏ j, v j := by
    rw [prod_fibreProduct]
    exact hlarge
  exact exists_rpow_le_of_prod_rpow_le_prod
    (fibreProduct g A) v e hAfibre hv hlarge'

/-- **Exact complex-product selection.**  If a literal Dirichlet-factor product is large, then for
any finite grouping one literal grouped product is large at its own multiplicative scale. -/
theorem exists_grouped_complex_product_large
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (g : ι → κ) (A : ι → ℝ) (z : ι → ℂ) (e : ℝ)
    (hA : ∀ i, 0 < A i)
    (hlarge : (∏ i, A i) ^ e ≤ ‖∏ i, z i‖) :
    ∃ j, (fibreProduct g A j) ^ e ≤ ‖fibreProduct g z j‖ := by
  apply exists_fibre_rpow_le g A (fun j => ‖fibreProduct g z j‖) e hA
    (fun j => norm_nonneg _)
  calc
    (∏ i, A i) ^ e ≤ ‖∏ i, z i‖ := hlarge
    _ = ‖∏ j, fibreProduct g z j‖ := by rw [prod_fibreProduct]
    _ = ∏ j, ‖fibreProduct g z j‖ := Complex.norm_prod _ _

/-- Literal Heath--Brown specialization of `exists_grouped_complex_product_large`.  The selected
fibre is expressed in exactly the shape consumed by `huxley_heathBrown_grouped_large_values`. -/
theorem exists_heathBrown_group_large
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (L X : ℕ) (kind : ι → HeathBrownFactorKind) (q : ι → ℕ) (g : ι → κ)
    (s : ℂ) (e : ℝ)
    (hlarge : (groupedDyadicLower q : ℝ) ^ e ≤
      ‖∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock (heathBrownFactorBase L X (kind i)) (q i))) s‖) :
    ∃ j, ((groupedDyadicLower (fun i : GroupFibre g j => q i) : ℕ) : ℝ) ^ e ≤
      ‖∏ i : GroupFibre g j, LSeries
        (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (kind i)) (q i))) s‖ := by
  have hlarge' : (∏ i, (((2 ^ q i : ℕ) : ℝ))) ^ e ≤
      ‖∏ i, LSeries
        (complexCoeff (arithmeticDyadicBlock (heathBrownFactorBase L X (kind i)) (q i))) s‖ := by
    simpa [groupedDyadicLower] using hlarge
  obtain ⟨j, hj⟩ := exists_grouped_complex_product_large g
    (fun i => (((2 ^ q i : ℕ) : ℝ)))
    (fun i => LSeries
      (complexCoeff (arithmeticDyadicBlock (heathBrownFactorBase L X (kind i)) (q i))) s)
    e (fun i => by positivity) hlarge'
  refine ⟨j, ?_⟩
  simpa [fibreProduct, groupedDyadicLower] using hj

end RHTower.Sieve
