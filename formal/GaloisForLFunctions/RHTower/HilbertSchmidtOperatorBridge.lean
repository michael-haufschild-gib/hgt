/-
Hilbert–Schmidt operators inside the Schatten hierarchy, and the seam crossing tower in the
coordinate-free layer.

The basis truncations of a Hilbert–Schmidt operator have finite rank bounded by the number of
retained basis vectors, so the approximation numbers are dominated by square roots of tails of the
Hilbert–Schmidt series and tend to zero: Hilbert–Schmidt operators sit strictly inside the
compactness boundary that excludes the Sonin corners from every Schatten class.

The seam crossing kernels on `ℓ²(ℤ)` transfer along the kernel → operator bridge: each crossing
`B_r` becomes a genuine compact Hilbert–Schmidt operator with `‖B_r‖²_HS = r`, and the crossing
energy law `⟨B_r, B_s⟩_HS = r·δ_{r,s}` holds for the coordinate-free Hilbert–Schmidt inner
product.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix
import GaloisForLFunctions.RHTower.SchattenApproximation
import GaloisForLFunctions.RHTower.SeamCrossingHS

noncomputable section

namespace RHTower

open ContinuousLinearMap Filter

section Schatten

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Each basis truncation of an operator has rank at most the number of retained basis vectors:
its range lies in the span of the finitely many columns `T (b i)`, `i ∈ s`. -/
theorem hasRankLE_hsTruncation {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (s : Finset ι) : HasRankLE (hsTruncation b T s) s.card := by
  classical
  refine ⟨Submodule.span ℂ ((s.image fun i => T (b i) : Finset H) : Set H),
    FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _), ?_, ?_⟩
  · exact (finrank_span_finset_le_card _).trans Finset.card_image_le
  · intro x
    rw [hsTruncation_apply]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi)

/-- The approximation numbers of a Hilbert–Schmidt operator are dominated by the square roots of
the tails of its Hilbert–Schmidt series. -/
theorem approxNumber_le_hsTail {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    {ι : Type*} (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    approxNumber T s.card ≤ Real.sqrt (∑' i : {i // i ∉ s}, ‖T (b i)‖ ^ (2 : ℕ)) :=
  (approxNumber_le T s.card _ (hasRankLE_hsTruncation b T s)).trans
    (norm_sub_hsTruncation_le hT b s)

/-- **Hilbert–Schmidt operators have vanishing approximation numbers**: the tails of the
Hilbert–Schmidt series are arbitrarily small and the approximation numbers are antitone. -/
theorem tendsto_approxNumber_zero_of_isHilbertSchmidt {T : H →L[ℂ] H}
    (hT : IsHilbertSchmidt T) : Tendsto (approxNumber T) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨s, hs⟩ := hT.exists_tail_lt (hsBasis ℂ H) (show (0 : ℝ) < ε ^ (2 : ℕ) by positivity)
  refine ⟨s.card, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (approxNumber_nonneg T n)]
  calc approxNumber T n ≤ approxNumber T s.card := approxNumber_antitone T hn
    _ ≤ Real.sqrt (∑' i : {i // i ∉ s}, ‖T (hsBasis ℂ H i)‖ ^ (2 : ℕ)) :=
        approxNumber_le_hsTail hT (hsBasis ℂ H) s
    _ < ε := (Real.sqrt_lt' hε).mpr hs

end Schatten

section SeamCrossing

/-- The seam crossing operator on `ℓ²(ℤ)`: the crossing kernel realized as a coordinate-free
bounded operator. -/
def crossOperator (r : ℕ) : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  HilbertSchmidt.toOperator (isHS_crossKernel r)

/-- Each crossing operator is Hilbert–Schmidt in the coordinate-free sense. -/
theorem isHilbertSchmidt_crossOperator (r : ℕ) : (crossOperator r).IsHilbertSchmidt :=
  HilbertSchmidt.isHilbertSchmidt_toOperator (isHS_crossKernel r)

/-- The crossing self-energy in the coordinate-free layer: `‖B_r‖²_HS = r`. -/
theorem hsNormSq_crossOperator (r : ℕ) :
    ContinuousLinearMap.hsNormSq (crossOperator r) = r := by
  rw [crossOperator, HilbertSchmidt.hsNormSq_toOperator, hsNormSq_crossKernel]

/-- **The crossing energy law for the coordinate-free Hilbert–Schmidt inner product**:
`⟨B_r, B_s⟩_HS = r·δ_{r,s}` on operators, transported across the kernel → operator bridge. -/
theorem hsInner_crossOperator (r s : ℕ) :
    ContinuousLinearMap.hsInner (crossOperator r) (crossOperator s)
      = if r = s then (r : ℂ) else 0 := by
  rw [crossOperator, crossOperator, HilbertSchmidt.hsInner_toOperator, hsInner_crossKernel]

/-- Each crossing operator is compact. -/
theorem isCompactOperator_crossOperator (r : ℕ) : IsCompactOperator (crossOperator r) :=
  (isHilbertSchmidt_crossOperator r).isCompactOperator

end SeamCrossing

end RHTower
