import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBoundedPrimeSpectrumIsTheAdjunctionSpectrum

/-!
# Simple prime eigenlines converge to Ramanujan lines

Properness and separation isolate each arithmetic energy. The exact spectral
count leaves one actual eigenvector in that window. Its spectral projection
captures the normalized Ramanujan vector because the complement has a fixed gap.
-/

noncomputable section

open Filter Topology Finset
open scoped RealInnerProductSpace Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Every positive conductor has a neighborhood containing no other arithmetic energy. -/
theorem exists_isolating_adjunction_radius {m : ℕ} (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℕ, 0 < l →
      |ramanujanAdjunctionEnergy l - ramanujanAdjunctionEnergy m| < 2 * δ → l = m := by
  let S := adjunctionEnergySublevel (ramanujanAdjunctionEnergy m + 1)
  have hmS : m ∈ S := (mem_adjunctionEnergySublevel _ m).mpr ⟨hm, by linarith only⟩
  obtain ⟨s, hs, hs1, hsep⟩ := ArithmeticIncidencePositivity.exists_separation_finset
    (S.image ramanujanAdjunctionEnergy)
  refine ⟨s / 4, by positivity, fun l hl hclose => ?_⟩
  have hlS : l ∈ S := by
    apply (mem_adjunctionEnergySublevel _ l).mpr
    refine ⟨hl, ?_⟩
    have h := (abs_lt.mp hclose).2
    linarith only [h, hs1]
  by_contra hne
  have hE : ramanujanAdjunctionEnergy l ≠ ramanujanAdjunctionEnergy m := fun h =>
    hne (ramanujanAdjunctionEnergy_injectiveOn hl hm h)
  have h := hsep _ (mem_image.mpr ⟨l, hlS, rfl⟩) _ (mem_image.mpr ⟨m, hmS, rfl⟩) hE
  linarith only [h, hclose, hs]

/-- The half-open spectral window around a proposed limiting energy. -/
def fullPrimeEnergyWindow (N : ℕ) (E δ : ℝ) : Finset (PrimeHorizonIndex N) :=
  fullPrimeEnergySublevel N (E + δ) \ fullPrimeEnergySublevel N (E - δ)

theorem mem_fullPrimeEnergyWindow (N : ℕ) (E δ : ℝ) (i : PrimeHorizonIndex N) :
    i ∈ fullPrimeEnergyWindow N E δ ↔
      E - δ ≤ fullPrimeEnergyEigenvalue N i ∧ fullPrimeEnergyEigenvalue N i < E + δ := by
  simp only [fullPrimeEnergyWindow, Finset.mem_sdiff, fullPrimeEnergySublevel,
    Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  exact and_comm

private theorem isolated_adjunction_thresholds {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ l : ℕ, 0 < l →
      |ramanujanAdjunctionEnergy l - ramanujanAdjunctionEnergy m| < 2 * δ → l = m) :
    (∀ l : ℕ, 0 < l → ramanujanAdjunctionEnergy l ≠ ramanujanAdjunctionEnergy m - δ) ∧
    (∀ l : ℕ, 0 < l → ramanujanAdjunctionEnergy l ≠ ramanujanAdjunctionEnergy m + δ) := by
  constructor <;> intro l hl he
  · have heq := hiso l hl (abs_lt.mpr ⟨by linarith only [he, hδ], by linarith only [he, hδ]⟩)
    subst l
    linarith only [he, hδ]
  · have heq := hiso l hl (abs_lt.mpr ⟨by linarith only [he, hδ], by linarith only [he, hδ]⟩)
    subst l
    linarith only [he, hδ]

private theorem isolated_adjunction_sublevel_insert {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ l : ℕ, 0 < l →
      |ramanujanAdjunctionEnergy l - ramanujanAdjunctionEnergy m| < 2 * δ → l = m) :
    adjunctionEnergySublevel (ramanujanAdjunctionEnergy m + δ) =
      insert m (adjunctionEnergySublevel (ramanujanAdjunctionEnergy m - δ)) := by
  ext l
  constructor
  · intro hl
    obtain ⟨hl0, hlT⟩ := (mem_adjunctionEnergySublevel _ l).mp hl
    by_cases hlm : l = m
    · exact mem_insert.mpr (Or.inl hlm)
    · apply mem_insert_of_mem
      apply (mem_adjunctionEnergySublevel _ l).mpr
      refine ⟨hl0, ?_⟩
      by_contra hn
      have hlo : ramanujanAdjunctionEnergy m - δ ≤ ramanujanAdjunctionEnergy l := le_of_not_gt hn
      have hclose : |ramanujanAdjunctionEnergy l - ramanujanAdjunctionEnergy m| < 2 * δ :=
        abs_lt.mpr ⟨by linarith only [hlo, hδ], by linarith only [hlT, hδ]⟩
      exact hlm (hiso l hl0 hclose)
  · intro hl
    rcases mem_insert.mp hl with hlm | hl
    · subst l
      exact (mem_adjunctionEnergySublevel _ m).mpr ⟨hm, by linarith only [hδ]⟩
    · obtain ⟨hl0, hlT⟩ := (mem_adjunctionEnergySublevel _ l).mp hl
      exact (mem_adjunctionEnergySublevel _ l).mpr ⟨hl0, by linarith only [hlT, hδ]⟩

/-- An isolated arithmetic energy has exactly one actual spectral index eventually. -/
theorem eventually_fullPrimeEnergyWindow_card_one {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ l : ℕ, 0 < l →
      |ramanujanAdjunctionEnergy l - ramanujanAdjunctionEnergy m| < 2 * δ → l = m) :
    ∀ᶠ N : ℕ in atTop, (fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ).card = 1 := by
  obtain ⟨hminus, hplus⟩ := isolated_adjunction_thresholds hδ hiso
  have hnot : m ∉ adjunctionEnergySublevel (ramanujanAdjunctionEnergy m - δ) := by
    intro h
    have hlt := ((mem_adjunctionEnergySublevel _ m).mp h).2
    linarith only [hlt, hδ]
  have hcard : (adjunctionEnergySublevel (ramanujanAdjunctionEnergy m + δ)).card =
      (adjunctionEnergySublevel (ramanujanAdjunctionEnergy m - δ)).card + 1 := by
    rw [isolated_adjunction_sublevel_insert hm hδ hiso, Finset.card_insert_of_notMem hnot]
  filter_upwards [eventually_fullPrime_spectral_count_eq _ hminus,
    eventually_fullPrime_spectral_count_eq _ hplus] with N hNminus hNplus
  have hsub : fullPrimeEnergySublevel N (ramanujanAdjunctionEnergy m - δ) ⊆
      fullPrimeEnergySublevel N (ramanujanAdjunctionEnergy m + δ) := by
    intro i hi
    obtain ⟨_, hi⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_univ _, by linarith only [hi, hδ]⟩
  rw [fullPrimeEnergyWindow, card_sdiff_of_subset hsub, hNminus, hNplus, hcard]
  omega

theorem abs_fullPrimeEnergyEigenvalue_sub (m N : ℕ) (i : PrimeHorizonIndex N) :
    |fullPrimeEnergyEigenvalue N i - ramanujanAdjunctionEnergy m| =
      |(fullPrimeMatrix_isHermitian N).eigenvalues i -
        (Real.log N - ramanujanAdjunctionEnergy m)| := by
  rw [fullPrimeEnergyEigenvalue]
  have h : Real.log N - (fullPrimeMatrix_isHermitian N).eigenvalues i - ramanujanAdjunctionEnergy m =
      -((fullPrimeMatrix_isHermitian N).eigenvalues i - (Real.log N - ramanujanAdjunctionEnergy m)) := by ring
  rw [h, abs_neg]

/-- The single eigenvalue in an isolated window converges to its arithmetic energy. -/
theorem eventually_fullPrimeEnergyWindow_near {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ l : ℕ, 0 < l →
      |ramanujanAdjunctionEnergy l - ramanujanAdjunctionEnergy m| < 2 * δ → l = m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ,
      |fullPrimeEnergyEigenvalue N i - ramanujanAdjunctionEnergy m| < ε := by
  have hsmall : 0 < min ε (δ / 2) := lt_min hε (by positivity)
  filter_upwards [eventually_fullPrimeEnergyWindow_card_one hm hδ hiso,
    eventually_fullPrimeMatrix_eigenvalue_near hm hsmall] with N hcard hnear
  obtain ⟨j, hj⟩ := hnear
  rw [← abs_fullPrimeEnergyEigenvalue_sub m N j] at hj
  have hjδ : |fullPrimeEnergyEigenvalue N j - ramanujanAdjunctionEnergy m| < δ :=
    hj.trans_le ((min_le_right ε (δ / 2)).trans (by linarith only [hδ]))
  have hjmem : j ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ :=
    (mem_fullPrimeEnergyWindow _ _ _ _).mpr
      ⟨by have h := (abs_lt.mp hjδ).1; linarith only [h],
        by have h := (abs_lt.mp hjδ).2; linarith only [h]⟩
  intro i hi
  have hij : i = j := (card_le_one_iff.mp hcard.le) hi hjmem
  subst i
  exact hj.trans_le (min_le_left _ _)

/-- The Ramanujan vector projected onto its actual spectral window. -/
def ramanujanWindowProjection (m N : ℕ) (δ : ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  HTGeometry.hermitianEigenProjection (fullPrimeMatrix_isHermitian N)
    (fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ) (normalizedRamanujanHorizonVector m N)

/-- A fixed spectral window captures the Ramanujan quasimode in squared norm. -/
theorem tendsto_ramanujanWindowProjection_error_sq {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      ‖normalizedRamanujanHorizonVector m N - ramanujanWindowProjection m N δ‖ ^ 2)
      atTop (𝓝 0) := by
  have hbound (N : ℕ) :
      ‖normalizedRamanujanHorizonVector m N - ramanujanWindowProjection m N δ‖ ^ 2 ≤
        ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 /
            δ ^ 2 := by
    have hgap : ∀ i ∉ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ,
        δ ≤ |(fullPrimeMatrix_isHermitian N).eigenvalues i -
          (Real.log N - ramanujanAdjunctionEnergy m)| := by
      intro i hi
      rw [← abs_fullPrimeEnergyEigenvalue_sub m N i]
      by_contra hn
      have h := abs_lt.mp (lt_of_not_ge hn)
      apply hi
      apply (mem_fullPrimeEnergyWindow _ _ _ _).mpr
      exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
    have h := HTGeometry.gap_sq_mul_eigenProjection_error_le_residual_sq
      (fullPrimeMatrix_isHermitian N)
      (fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ)
      (normalizedRamanujanHorizonVector m N) (Real.log N - ramanujanAdjunctionEnergy m)
      δ hδ.le hgap
    rw [le_div_iff₀ (sq_pos_of_pos hδ)]
    simpa only [ramanujanWindowProjection, mul_comm] using h
  have hlim := ((tendsto_normalizedRamanujanHorizonVector_residual_norm hm).pow 2).div_const (δ ^ 2)
  apply squeeze_zero (fun N => sq_nonneg _) hbound
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] using hlim

/-- Every positive conductor yields one simple actual eigenline eventually;
its energy and projected Ramanujan vector converge at the full integer horizon. -/
theorem exists_simple_fullPrime_eigenline {m : ℕ} (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ N : ℕ in atTop,
        (fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ).card = 1) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ i ∈ fullPrimeEnergyWindow N (ramanujanAdjunctionEnergy m) δ,
          |fullPrimeEnergyEigenvalue N i - ramanujanAdjunctionEnergy m| < ε) ∧
      Tendsto (fun N : ℕ =>
        ‖normalizedRamanujanHorizonVector m N - ramanujanWindowProjection m N δ‖ ^ 2)
        atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hiso⟩ := exists_isolating_adjunction_radius hm
  exact ⟨δ, hδ, eventually_fullPrimeEnergyWindow_card_one hm hδ hiso,
    fun ε hε => eventually_fullPrimeEnergyWindow_near hm hδ hiso hε,
    tendsto_ramanujanWindowProjection_error_sq hm hδ⟩

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

