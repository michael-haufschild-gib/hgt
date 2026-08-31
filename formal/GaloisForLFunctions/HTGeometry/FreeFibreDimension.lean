import GaloisForLFunctions.HTGeometry.FreeFibreCoordinates

/-!
# The fibre of a finite free module over the base line

```text
fibreBasisFun              the images of the basis vectors
fibre_span                 ** every class is the combination of them given by evaluation **
fibre_linearIndependent    and they are independent, because a constant in the ideal of a point is
                              zero
freeFibreBasis
finrank_quotient_finsupp   ** the fibre has the rank as its dimension, at every point **
```

Division by `X - lam` is evaluation at `lam`, so the coordinates of a class are the values of the
coordinates of any representative; that is both the spanning and the independence.  There are no
exceptional points here — a free module has the same fibre dimension everywhere — which is why only
the torsion of a finitely generated module can raise the fibre dimension above the rank.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Module
open scoped Pointwise

variable {K : Type*} [Field K]

/-- The candidate basis of the fibre of a finite free module over the base line. -/
noncomputable def fibreBasisFun (lam : K) (n : ℕ) (i : Fin n) :
    ((Fin n →₀ K[X]) ⧸
      (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] (Fin n →₀ K[X])))) :=
  Submodule.Quotient.mk (Finsupp.single i 1)

theorem smul_finsupp_coeff (c : K) (f : Fin n →₀ K[X]) (i : Fin n) :
    (c • f) i = C c * f i := by
  rw [Finsupp.smul_apply, Algebra.smul_def, algebraMap_eq]

theorem fibre_span (lam : K) (n : ℕ) (f : Fin n →₀ K[X]) :
    (Submodule.Quotient.mk f :
        ((Fin n →₀ K[X]) ⧸
          (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] (Fin n →₀ K[X])))))
      = ∑ i, ((f i).eval lam) • fibreBasisFun lam n i := by
  classical
  have hsum : (∑ i, ((f i).eval lam) • fibreBasisFun lam n i)
      = Submodule.mkQ _ (∑ i, ((f i).eval lam) • Finsupp.single i (1 : K[X])) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [hsum, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_smul_top_finsupp_iff]
  intro i
  have hcoeff : (f - ∑ j, ((f j).eval lam) • Finsupp.single j (1 : K[X])) i
      = f i - C ((f i).eval lam) := by
    rw [Finsupp.sub_apply, Finsupp.finsetSum_apply]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), smul_finsupp_coeff,
      Finsupp.single_eq_same, mul_one,
      show (∑ j ∈ Finset.univ.erase i, (((f j).eval lam) •
        Finsupp.single j (1 : K[X])) i) = 0 from ?_, add_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [smul_finsupp_coeff, Finsupp.single_eq_of_ne (Ne.symm (Finset.mem_erase.mp hj).1), mul_zero]
  rw [hcoeff]
  exact sub_eval_mem_span lam (f i)

theorem fibre_linearIndependent (lam : K) (n : ℕ) :
    LinearIndependent K (fibreBasisFun lam n) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hg' : Submodule.mkQ (Ideal.span {(X - C lam : K[X])} •
        (⊤ : Submodule K[X] (Fin n →₀ K[X])))
      (∑ j ∈ s, (g j) • Finsupp.single j (1 : K[X])) = 0 := by
    rw [map_sum]
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rfl
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_smul_top_finsupp_iff] at hg'
  have hcoeff : (∑ j ∈ s, (g j) • Finsupp.single j (1 : K[X])) i = C (g i) := by
    rw [Finsupp.finsetSum_apply, ← Finset.add_sum_erase _ _ hi, smul_finsupp_coeff,
      Finsupp.single_eq_same, mul_one,
      show (∑ j ∈ s.erase i, ((g j) • Finsupp.single j (1 : K[X])) i) = 0 from ?_, add_zero]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [smul_finsupp_coeff, Finsupp.single_eq_of_ne (Ne.symm (Finset.mem_erase.mp hj).1), mul_zero]
  have := hg' i
  rw [hcoeff, C_mem_span_iff] at this
  exact this

/-- The fibre of a finite free module over the base line has the rank as its dimension. -/
noncomputable def freeFibreBasis (lam : K) (n : ℕ) :
    Basis (Fin n) K
      ((Fin n →₀ K[X]) ⧸
        (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] (Fin n →₀ K[X])))) := by
  classical
  refine Basis.mk (fibre_linearIndependent lam n) ?_
  intro x _
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    rw [fibre_span]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The free half of the fibre count.** -/
theorem finrank_quotient_finsupp (lam : K) (n : ℕ) :
    finrank K
      ((Fin n →₀ K[X]) ⧸
        (Ideal.span {(X - C lam : K[X])} • (⊤ : Submodule K[X] (Fin n →₀ K[X])))) = n := by
  rw [finrank_eq_card_basis (freeFibreBasis lam n), Fintype.card_fin]

end GaloisForLFunctions.HTGeometry
