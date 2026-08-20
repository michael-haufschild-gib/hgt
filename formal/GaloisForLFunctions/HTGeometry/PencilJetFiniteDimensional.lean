/-
# The completion fibre of a pencil is exactly `Sym^k(V^*)`

The `k`-th powers of linear forms on a finite-dimensional parameter space span a
*finite-dimensional* space of functions -- expanding a power of a linear form writes it in the
finitely many coordinate words of length `k`.  A finite-dimensional subspace of a function space is
closed for pointwise convergence, so the pointwise limit of the `k`-th power traces of a family of
finite-rank pencils is again a homogeneous form of degree `k`.  That is the several-variable
statement that the completion fibre is exactly `⊕ₖ Sym^k(V^*)` and nothing larger.

Main results:
* `coordWordFunSet` — the finitely many coordinate words of length `k`.
* `clmPowSet_subset_span_coordWord` — a `k`-th power of a linear form is a combination of them.
* `finiteDimensional_span_clmPowSet` — **the span of `k`-th powers is finite-dimensional**.
* `jet_mem_span_of_tendsto_pencilTrace` — **the limiting jet is a homogeneous form**.
-/
import GaloisForLFunctions.HTGeometry.PencilTracePolynomial
import GaloisForLFunctions.HTGeometry.BoundedDegreeMvPolynomialLimit

open Filter Topology Finset ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-- The finitely many coordinate words of length `k` in `d` variables. -/
def coordWordFunSet (d k : ℕ) : Set ((Fin d → ℂ) → ℂ) :=
  Set.range fun j : Fin k → Fin d => fun v : Fin d → ℂ => ∏ r, v (j r)

theorem finite_coordWordFunSet (d k : ℕ) : (coordWordFunSet d k).Finite :=
  Set.finite_range _

/-- **A `k`-th power of a linear form is a combination of coordinate words.** -/
theorem clmPowSet_subset_span_coordWord (d k : ℕ) :
    clmPowSet (Fin d → ℂ) k ⊆ Submodule.span ℂ (coordWordFunSet d k) := by
  classical
  rintro _ ⟨ℓ, rfl⟩
  have hcoord : ∀ v : Fin d → ℂ, ℓ v = ∑ a, ℓ (Pi.single a 1) * v a := by
    intro v
    have hv : v = ∑ a, v a • (Pi.single a (1 : ℂ) : Fin d → ℂ) := by
      funext a
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hexp : (fun v : Fin d → ℂ => (ℓ v) ^ k)
      = ∑ j : Fin k → Fin d,
          (∏ r, ℓ (Pi.single (j r) 1)) • (fun v : Fin d → ℂ => ∏ r, v (j r)) := by
    funext v
    rw [hcoord v, Finset.sum_apply]
    rw [Finset.sum_pow' (Finset.univ : Finset (Fin d))
      (fun a => ℓ (Pi.single a 1) * v a) k]
    rw [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun j _ => ?_
    show (∏ r, ℓ (Pi.single (j r) 1) * v (j r))
      = ((∏ r, ℓ (Pi.single (j r) 1)) • fun v : Fin d → ℂ => ∏ r, v (j r)) v
    rw [Pi.smul_apply, smul_eq_mul, ← Finset.prod_mul_distrib]
  rw [hexp]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨j, rfl⟩

instance finiteDimensional_span_clmPowSet (d k : ℕ) :
    FiniteDimensional ℂ (Submodule.span ℂ (clmPowSet (Fin d → ℂ) k)) := by
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (coordWordFunSet d k)) :=
    FiniteDimensional.span_of_finite ℂ (finite_coordWordFunSet d k)
  exact Submodule.finiteDimensional_of_le
    (Submodule.span_le.mpr (clmPowSet_subset_span_coordWord d k))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The limiting jet is a homogeneous form.**  The pointwise limit of the `k`-th power traces of a
family of finite-rank pencils lies in the span of `k`-th powers of linear forms, i.e. in
`Sym^k(V^*)`. -/
theorem jet_mem_span_of_tendsto_pencilTrace {d k : ℕ} {F : ℕ → Fin d → (H →L[ℂ] H)}
    (hF : ∀ n : ℕ, ∃ N : ℕ, ∀ j, HasRankLE (F n j) N) {c : ℂ} {P : (Fin d → ℂ) → ℂ}
    (hP : ∀ v : Fin d → ℂ,
      Tendsto (fun n => c * opTrace ((pencilOperator (F n) v) ^ (k + 1))) atTop (nhds (P v))) :
    P ∈ Submodule.span ℂ (clmPowSet (Fin d → ℂ) (k + 1)) := by
  refine mem_of_tendsto_pointwise
    (S := Submodule.span ℂ (clmPowSet (Fin d → ℂ) (k + 1)))
    (f := fun n => fun v : Fin d → ℂ => c * opTrace ((pencilOperator (F n) v) ^ (k + 1)))
    (fun n => ?_) hP
  obtain ⟨N, hN⟩ := hF n
  have hmem := pencilTraceForm_mem_span (H := H) (k := k) hN
    (fun j => ContinuousLinearMap.proj j)
  exact Submodule.smul_mem _ c hmem

end

end GaloisForLFunctions.HTGeometry
