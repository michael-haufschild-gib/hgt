import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FormSingleChartLocalization

/-! A regular form on the joined intersection can be written with
a regular scalar on the left and a regular form on the right. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

/-- The ratios inverted in passing from the right intersection to
the joined intersection have their inverses in the left chart ring. -/
theorem IsPd.exists_regularScalar_smul_omB_of_union (h : IsPd k x)
    {I J : Finset (Fin (d + 1))} (hJ : J.Nonempty)
    {p : ℕ} (w : ExteriorDifferentials k E p)
    (hw : (w : DR k E) ∈ omB k E (rB k E x (I ∪ J)) p) :
    ∃ (c : F) (v : ExteriorDifferentials k E p),
      c ∈ rA k x I ∧ (v : DR k E) ∈ omB k E (rB k E x J) p ∧ c • v = w := by
  obtain ⟨j, hj⟩ := hJ
  let z := ∏ l ∈ (I ∪ J) \ J, x l / x j
  have hz : z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun l _ => div_ne_zero (h.ne l) (h.ne j)
  have hinv : z⁻¹ ∈ rA k x I := by
    rw [show z⁻¹ = ∏ l ∈ (I ∪ J) \ J, x j / x l by
      simp only [z, ← Finset.prod_inv_distrib, inv_div]]
    refine Subalgebra.prod_mem _ fun l hl => ?_
    obtain ⟨hl', hnj⟩ := Finset.mem_sdiff.mp hl
    have hli := (Finset.mem_union.mp hl').resolve_right hnj
    exact Algebra.subset_adjoin ⟨l, hli, j, rfl⟩
  obtain ⟨N, hN⟩ := h.exists_smul_mem_omB_of_subset hj Finset.subset_union_right w hw
  refine ⟨z⁻¹ ^ N, z ^ N • w, (rA k x I).pow_mem hinv N, ?_, ?_⟩
  · change (algebraMap F E (z ^ N) • (w : DR k E)) ∈ _
    simpa only [map_pow] using hN
  · rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hz, one_pow, one_smul]

end GlobalTheory.PD
