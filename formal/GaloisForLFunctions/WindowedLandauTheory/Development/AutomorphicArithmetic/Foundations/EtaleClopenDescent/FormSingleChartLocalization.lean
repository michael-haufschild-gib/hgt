import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedIntersectionLocalization

/-! A form on an enlarged chart intersection has denominators given
by the new coordinate ratios. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

/-- Only the ratios for added indices are needed to clear the
denominators of a regular form on an enlarged intersection. -/
theorem IsPd.exists_smul_mem_omB_of_subset (h : IsPd k x)
    {I J : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I)
    (hIJ : I ⊆ J) {p : ℕ} (w : ExteriorDifferentials k E p)
    (hw : (w : DR k E) ∈ omB k E (rB k E x J) p) :
    ∃ N : ℕ, algebraMap F E (∏ j ∈ J \ I, x j / x i) ^ N • (w : DR k E) ∈
      omB k E (rB k E x I) p := by
  let s : F := chartDenominator k x I i
  let z : F := ∏ j ∈ J \ I, x j / x i
  have hs : (chartDenominator k x J i : F) = z * s := by
    exact (Finset.prod_sdiff hIJ).symm
  obtain ⟨N, hN⟩ :=
    (mem_omB_chartIntersection_iff (E := E) h (hIJ hi) w).mp hw
  let w' : ExteriorDifferentials k E p := algebraMap F E z ^ N • w
  have hreg : (w' : DR k E) ∈ omB k E (rB k E x I) p := by
    refine (mem_omB_chartIntersection_iff (E := E) h hi w').mpr ⟨N, ?_⟩
    change algebraMap F E s ^ N • (algebraMap F E z ^ N • (w : DR k E)) ∈ _
    rw [hs, map_mul, mul_pow] at hN
    rwa [smul_smul, mul_comm]
  exact ⟨N, hreg⟩

/-- For a single added chart, its coordinate ratio clears the
denominators of forms on the enlarged intersection. -/
theorem IsPd.exists_smul_mem_omB_of_insert (h : IsPd k x)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I)
    (j : Fin (d + 1)) {p : ℕ} (w : ExteriorDifferentials k E p)
    (hw : (w : DR k E) ∈ omB k E (rB k E x (insert j I)) p) :
    ∃ N : ℕ, algebraMap F E (x j / x i) ^ N • (w : DR k E) ∈
      omB k E (rB k E x I) p := by
  by_cases hj : j ∈ I
  · refine ⟨0, ?_⟩
    simpa only [pow_zero, one_smul, Finset.insert_eq_of_mem hj] using hw
  have he : insert j I \ I = {j} := by
    ext l
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h | h, hn⟩
      · exact h
      · exact (hn h).elim
    · rintro rfl
      exact ⟨Or.inl rfl, hj⟩
  simpa only [he, Finset.prod_singleton] using h.exists_smul_mem_omB_of_subset hi
    (Finset.subset_insert j I) w hw

end GlobalTheory.PD
