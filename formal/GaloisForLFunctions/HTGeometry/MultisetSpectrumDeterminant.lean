/-
# The plain determinant of a multiset spectrum

The micro-spectrum construction produces finite *multisets* of eigenvalues, while the determinant
layer is indexed by a finite type.  Listing a multiset transports every product and every power sum
between the two presentations, so the plain-determinant identity holds verbatim for a multiset
spectrum.

Main results:
* `multiset_prod_eq_finProd`, `multiset_sum_eq_finSum` — listing transports products and sums.
* `multiset_schattenTracePower` — the power traces of the listed spectrum are the multiset moments.
* `multiset_prod_one_sub_eq_schattenDet_mul_exp` — **the plain determinant of a multiset spectrum**.
-/
import GaloisForLFunctions.HTGeometry.FiniteSpectrumPlainDeterminant

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The listing of a multiset as a family indexed by a finite type. -/
def multisetIndex (S : Multiset ℂ) : Fin S.toList.length → ℂ := fun i => S.toList.get i

theorem multiset_prod_eq_finProd (S : Multiset ℂ) (f : ℂ → ℂ) :
    (S.map f).prod = ∏ i, f (multisetIndex S i) := by
  conv_lhs => rw [← Multiset.coe_toList S]
  rw [Multiset.map_coe, Multiset.prod_coe]
  have hlist : S.toList.map f = List.ofFn (fun i : Fin S.toList.length => f (multisetIndex S i)) := by
    rw [show (fun i : Fin S.toList.length => f (multisetIndex S i)) = f ∘ S.toList.get from rfl,
      ← List.map_ofFn, List.ofFn_get]
  rw [hlist, List.prod_ofFn]

theorem multiset_sum_eq_finSum (S : Multiset ℂ) (f : ℂ → ℂ) :
    (S.map f).sum = ∑ i, f (multisetIndex S i) := by
  conv_lhs => rw [← Multiset.coe_toList S]
  rw [Multiset.map_coe, Multiset.sum_coe]
  have hlist : S.toList.map f = List.ofFn (fun i : Fin S.toList.length => f (multisetIndex S i)) := by
    rw [show (fun i : Fin S.toList.length => f (multisetIndex S i)) = f ∘ S.toList.get from rfl,
      ← List.map_ofFn, List.ofFn_get]
  rw [hlist, List.sum_ofFn]

theorem multiset_schattenTracePower (S : Multiset ℂ) (k : ℕ) :
    schattenTracePower (multisetIndex S) k = (S.map fun z => z ^ k).sum := by
  rw [schattenTracePower, tsum_fintype, multiset_sum_eq_finSum]

/-- **The plain determinant of a multiset spectrum.**  It is the order-`p` regularized determinant
of the listed spectrum times the exponential of the first `p − 1` multiset moments. -/
theorem multiset_prod_one_sub_eq_schattenDet_mul_exp {p : ℕ} (hp : 0 < p) (S : Multiset ℂ) {z : ℂ}
    (hz : ‖z‖ * Real.sqrt (matHSNormSq (Matrix.diagonal (multisetIndex S))) < 1) :
    (S.map fun μ => 1 - z * μ).prod
      = schattenDet p (multisetIndex S) z * Complex.exp (-∑ j ∈ Finset.range (p - 1),
          z ^ (j + 1) * (S.map fun μ => μ ^ (j + 1)).sum / ((j + 1 : ℕ) : ℂ)) := by
  rw [multiset_prod_eq_finProd, prod_one_sub_eq_schattenDet_mul_exp hp (multisetIndex S) hz]
  have hexp : (∑ j ∈ Finset.range (p - 1),
        z ^ (j + 1) * schattenTracePower (multisetIndex S) (j + 1) / ((j + 1 : ℕ) : ℂ))
      = ∑ j ∈ Finset.range (p - 1),
        z ^ (j + 1) * (S.map fun μ => μ ^ (j + 1)).sum / ((j + 1 : ℕ) : ℂ) :=
    Finset.sum_congr rfl fun j _ => by rw [multiset_schattenTracePower]
  rw [hexp]

end

end GaloisForLFunctions.HTGeometry
