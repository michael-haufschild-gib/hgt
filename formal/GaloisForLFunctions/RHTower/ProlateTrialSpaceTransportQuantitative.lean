import GaloisForLFunctions.RHTower.ProlateTrialSpaceTransport
import GaloisForLFunctions.RHTower.ProlateHermiteTrialSpaceQuantitative

/-!
# Transporting the trial space at an explicit threshold

The three transport steps — disjointness from the orthogonal complement, the rank comparison, and
the specialisation to the even sector — are thin wrappers around the liveness of the trial space.
Each therefore inherits the threshold shape `T ≤ ε · c` from
`exists_threshold_hermiteTrial_rayleigh_gt`.  The rank of the trial span itself carries no margin,
so it is carried as a hypothesis and discharged separately.
-/

open Filter Topology Set MeasureTheory Finset GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

variable {j : ℕ}

/-- **The trial span avoids the orthogonal complement, at an explicit threshold.** -/
theorem exists_threshold_disjoint_hermiteTrialSpan
    (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν) (hν : ∀ i, Even (ν i))
    {Λ : ℝ} (hΛ : ∀ i, 2 * (ν i : ℝ) + 1 ≤ Λ) :
    ∃ T : ℝ, 0 < T ∧ ∀ ε c : ℝ, 0 < ε → ε ≤ 1 → T ≤ ε * c →
      Disjoint (hermiteTrialSpan ν c) (highProlateSpan c ((Λ + ε) * c))ᗮ := by
  obtain ⟨T, hT0, hT⟩ := exists_threshold_hermiteTrial_rayleigh_gt ν hinj hΛ
  refine ⟨T, hT0, fun ε c hε hε1 hεc => ?_⟩
  have hcpos : 0 < c := by
    by_contra hcon
    have hcon' : c ≤ 0 := not_lt.1 hcon
    have h : ε * c ≤ ε * 0 := mul_le_mul_of_nonneg_left hcon' hε.le
    rw [mul_zero] at h
    linarith
  have hlive := hT ε c hε hε1 hεc
  refine disjoint_trialSpace_orthogonal_highProlateSpan hcpos _ ?_
  intro w hw hwne
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
  have hane : ∃ i, a i ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    apply hwne
    rw [← ha]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [not_not.1 (hcon i), zero_smul]
  exact ⟨hermiteTrialVector ν a c, contDiff_hermiteTrialVector ν a c,
    even_hermiteTrialVector hν a c, ((bandClass_hermiteTrialVector ν a c).trans ha).symm,
    hlive a hane⟩

/-- **The rank comparison, at an explicit threshold.**  The rank of the trial span is margin-free
and enters as a hypothesis. -/
theorem exists_threshold_rank_highProlateSpan_ge
    (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν) (hν : ∀ i, Even (ν i))
    {Λ : ℝ} (hΛ : ∀ i, 2 * (ν i : ℝ) + 1 ≤ Λ) :
    ∃ T : ℝ, 0 < T ∧ ∀ ε c : ℝ, 0 < ε → ε ≤ 1 → T ≤ ε * c →
      Module.rank ℝ (hermiteTrialSpan ν c) = ((j : Cardinal) + 1) →
      ∀ _ : (highProlateSpan c ((Λ + ε) * c)).HasOrthogonalProjection,
        ((j : Cardinal) + 1) ≤ Module.rank ℝ (highProlateSpan c ((Λ + ε) * c)) := by
  obtain ⟨T, hT0, hT⟩ := exists_threshold_disjoint_hermiteTrialSpan ν hinj hν hΛ
  refine ⟨T, hT0, fun ε c hε hε1 hεc hrank hinst => ?_⟩
  haveI := hinst
  have hle := rank_le_of_disjoint_orthogonal (hermiteTrialSpan ν c) (hT ε c hε hε1 hεc)
  rwa [hrank] at hle

/-- The even rung family used by the even sector. -/
def evenRung (j : ℕ) : Fin (j + 1) → ℕ := fun i => 2 * (i : ℕ)

theorem evenRung_injective (j : ℕ) : Function.Injective (evenRung j) := by
  intro i k h
  have h' : 2 * (i : ℕ) = 2 * (k : ℕ) := h
  exact Fin.ext (by omega)

theorem even_evenRung (j : ℕ) (i : Fin (j + 1)) : Even (evenRung j i) :=
  ⟨(i : ℕ), by show 2 * (i : ℕ) = (i : ℕ) + (i : ℕ); ring⟩

theorem evenRung_le (j : ℕ) (i : Fin (j + 1)) :
    2 * ((evenRung j i : ℕ) : ℝ) + 1 ≤ 4 * (j : ℝ) + 1 := by
  have hi : ((i : ℕ) : ℝ) ≤ (j : ℝ) := by
    have := Nat.lt_succ_iff.1 i.isLt
    exact_mod_cast this
  show 2 * ((2 * (i : ℕ) : ℕ) : ℝ) + 1 ≤ 4 * (j : ℝ) + 1
  push_cast
  linarith

/-- **The even sector, at an explicit threshold.**  One constant `T` serves every margin
`0 < ε ≤ 1`: once `T ≤ ε · c`, there are at least `j+1` independent joint even modes with separation
constant below `4j+1+ε`. -/
theorem exists_threshold_rank_highProlateSpan_even_ge (j : ℕ) :
    ∃ T : ℝ, 0 < T ∧ ∀ ε c : ℝ, 0 < ε → ε ≤ 1 → T ≤ ε * c →
      Module.rank ℝ (hermiteTrialSpan (evenRung j) c) = ((j : Cardinal) + 1) →
      ∀ _ : (highProlateSpan c ((4 * (j : ℝ) + 1 + ε) * c)).HasOrthogonalProjection,
        ((j : Cardinal) + 1)
          ≤ Module.rank ℝ (highProlateSpan c ((4 * (j : ℝ) + 1 + ε) * c)) :=
  exists_threshold_rank_highProlateSpan_ge (evenRung j) (evenRung_injective j)
    (even_evenRung j) (evenRung_le j)

/-- The trial span of the even rung family has full rank at every large bandwidth. -/
theorem eventually_rank_hermiteTrialSpan_evenRung_eq (j : ℕ) :
    ∀ᶠ c in atTop, Module.rank ℝ (hermiteTrialSpan (evenRung j) c) = ((j : Cardinal) + 1) :=
  eventually_rank_hermiteTrialSpan_eq (evenRung j) (evenRung_injective j)

end RHTower

end
