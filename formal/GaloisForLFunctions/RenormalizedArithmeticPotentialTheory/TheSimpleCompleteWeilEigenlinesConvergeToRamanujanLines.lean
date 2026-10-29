import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum

/-!
# Simple complete-Weil eigenlines converge to Ramanujan lines

The proper, distinct complete-Weil trial energies have isolating windows.
Exact spectral counts leave a one-dimensional eigenspace in each such window.
The actual norm residual and the complementary spectral gap force its
projection to capture the normalized Ramanujan vector.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Every positive conductor has a neighborhood containing no other arithmetic energy. -/
theorem exists_isolating_completeWeil_radius
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {m : ℕ} (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℕ, 0 < l →
      |completeWeilAdjunctionEnergy φ c l - completeWeilAdjunctionEnergy φ c m| < 2 * δ → l = m := by
  let S := completeWeilEnergySublevel φ c (completeWeilAdjunctionEnergy φ c m + 1)
  have hmS : m ∈ S := (mem_completeWeilEnergySublevel φ c _ m).mpr ⟨hm, by linarith only⟩
  obtain ⟨s, hs, hs1, hsep⟩ := ArithmeticIncidencePositivity.exists_separation_finset
    (S.image (completeWeilAdjunctionEnergy φ c))
  refine ⟨s / 4, by positivity, fun l hl hclose => ?_⟩
  have hlS : l ∈ S := by
    apply (mem_completeWeilEnergySublevel φ c _ l).mpr
    refine ⟨hl, ?_⟩
    have h := (abs_lt.mp hclose).2
    linarith only [h, hs1]
  by_contra hne
  have hE : completeWeilAdjunctionEnergy φ c l ≠ completeWeilAdjunctionEnergy φ c m := fun h =>
    hne (completeWeilAdjunctionEnergy_injectiveOn hφ.continuous hsupp hM hc0.le hc1 hl hm h)
  have h := hsep _ (mem_image.mpr ⟨l, hlS, rfl⟩) _ (mem_image.mpr ⟨m, hmS, rfl⟩) hE
  linarith only [h, hclose, hs]

/-- The half-open spectral window around a proposed limiting energy. -/
def completeWeilWindow (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (E δ : ℝ) : Finset (PrimeHorizonIndex N) :=
  completeWeilSpectralSublevel φ c N (E + δ) \ completeWeilSpectralSublevel φ c N (E - δ)

theorem mem_completeWeilWindow (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (E δ : ℝ) (i : PrimeHorizonIndex N) :
    i ∈ completeWeilWindow φ c N E δ ↔
      E - δ ≤ completeWeilEigenvalue φ c N i ∧ completeWeilEigenvalue φ c N i < E + δ := by
  simp only [completeWeilWindow, Finset.mem_sdiff, completeWeilSpectralSublevel,
    Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  exact and_comm

private theorem isolated_completeWeil_thresholds {φ : ℝ → ℝ} {c : ℝ} {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ l : ℕ, 0 < l →
      |completeWeilAdjunctionEnergy φ c l - completeWeilAdjunctionEnergy φ c m| < 2 * δ → l = m) :
    (∀ l : ℕ, 0 < l → completeWeilAdjunctionEnergy φ c l ≠ completeWeilAdjunctionEnergy φ c m - δ) ∧
    (∀ l : ℕ, 0 < l → completeWeilAdjunctionEnergy φ c l ≠ completeWeilAdjunctionEnergy φ c m + δ) := by
  constructor <;> intro l hl he
  · have heq := hiso l hl (abs_lt.mpr ⟨by linarith only [he, hδ], by linarith only [he, hδ]⟩)
    subst l
    linarith only [he, hδ]
  · have heq := hiso l hl (abs_lt.mpr ⟨by linarith only [he, hδ], by linarith only [he, hδ]⟩)
    subst l
    linarith only [he, hδ]

private theorem isolated_completeWeil_sublevel_insert {φ : ℝ → ℝ} {c : ℝ} {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ l : ℕ, 0 < l →
      |completeWeilAdjunctionEnergy φ c l - completeWeilAdjunctionEnergy φ c m| < 2 * δ → l = m) :
    completeWeilEnergySublevel φ c (completeWeilAdjunctionEnergy φ c m + δ) =
      insert m (completeWeilEnergySublevel φ c (completeWeilAdjunctionEnergy φ c m - δ)) := by
  ext l
  constructor
  · intro hl
    obtain ⟨hl0, hlT⟩ := (mem_completeWeilEnergySublevel φ c _ l).mp hl
    by_cases hlm : l = m
    · exact mem_insert.mpr (Or.inl hlm)
    · apply mem_insert_of_mem
      apply (mem_completeWeilEnergySublevel φ c _ l).mpr
      refine ⟨hl0, ?_⟩
      by_contra hn
      have hlo : completeWeilAdjunctionEnergy φ c m - δ ≤ completeWeilAdjunctionEnergy φ c l := le_of_not_gt hn
      have hclose : |completeWeilAdjunctionEnergy φ c l - completeWeilAdjunctionEnergy φ c m| < 2 * δ :=
        abs_lt.mpr ⟨by linarith only [hlo, hδ], by linarith only [hlT, hδ]⟩
      exact hlm (hiso l hl0 hclose)
  · intro hl
    rcases mem_insert.mp hl with hlm | hl
    · subst l
      exact (mem_completeWeilEnergySublevel φ c _ m).mpr ⟨hm, by linarith only [hδ]⟩
    · obtain ⟨hl0, hlT⟩ := (mem_completeWeilEnergySublevel φ c _ l).mp hl
      exact (mem_completeWeilEnergySublevel φ c _ l).mpr ⟨hl0, by linarith only [hlT, hδ]⟩

/-- An isolated arithmetic energy has exactly one actual spectral index eventually. -/
theorem eventually_completeWeilWindow_card_one
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ l : ℕ, 0 < l →
      |completeWeilAdjunctionEnergy φ c l - completeWeilAdjunctionEnergy φ c m| < 2 * δ → l = m) :
    ∀ᶠ N : ℕ in atTop, (completeWeilWindow φ c N (completeWeilAdjunctionEnergy φ c m) δ).card = 1 := by
  obtain ⟨hminus, hplus⟩ := isolated_completeWeil_thresholds hδ hiso
  have hnot : m ∉ completeWeilEnergySublevel φ c (completeWeilAdjunctionEnergy φ c m - δ) := by
    intro h
    have hlt := ((mem_completeWeilEnergySublevel φ c _ m).mp h).2
    linarith only [hlt, hδ]
  have hcard : (completeWeilEnergySublevel φ c (completeWeilAdjunctionEnergy φ c m + δ)).card =
      (completeWeilEnergySublevel φ c (completeWeilAdjunctionEnergy φ c m - δ)).card + 1 := by
    rw [isolated_completeWeil_sublevel_insert hm hδ hiso, Finset.card_insert_of_notMem hnot]
  filter_upwards [eventually_completeWeil_spectral_count_eq hφ hsupp hM hc0 hc1 _ hminus,
    eventually_completeWeil_spectral_count_eq hφ hsupp hM hc0 hc1 _ hplus] with N hNminus hNplus
  have hsub : completeWeilSpectralSublevel φ c N (completeWeilAdjunctionEnergy φ c m - δ) ⊆
      completeWeilSpectralSublevel φ c N (completeWeilAdjunctionEnergy φ c m + δ) := by
    intro i hi
    obtain ⟨_, hi⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_univ _, by linarith only [hi, hδ]⟩
  rw [completeWeilWindow, card_sdiff_of_subset hsub, hNminus, hNplus, hcard]
  omega

/-- The single eigenvalue in an isolated window converges to its arithmetic energy. -/
theorem eventually_completeWeilWindow_near
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ l : ℕ, 0 < l →
      |completeWeilAdjunctionEnergy φ c l - completeWeilAdjunctionEnergy φ c m| < 2 * δ → l = m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i ∈ completeWeilWindow φ c N (completeWeilAdjunctionEnergy φ c m) δ,
      |completeWeilEigenvalue φ c N i - completeWeilAdjunctionEnergy φ c m| < ε := by
  have hsmall : 0 < min ε (δ / 2) := lt_min hε (by positivity)
  filter_upwards [eventually_completeWeilWindow_card_one hφ hsupp hM hc0 hc1 hm hδ hiso,
    eventually_completeWeilMatrix_eigenvalue_near hφ hsupp hM hc0 hc1 hm hsmall] with N hcard hnear
  obtain ⟨j, hj⟩ := hnear
  have hjδ : |completeWeilEigenvalue φ c N j - completeWeilAdjunctionEnergy φ c m| < δ :=
    hj.trans_le ((min_le_right ε (δ / 2)).trans (by linarith only [hδ]))
  have hjmem : j ∈ completeWeilWindow φ c N (completeWeilAdjunctionEnergy φ c m) δ :=
    (mem_completeWeilWindow _ _ _ _ _ _).mpr
      ⟨by have h := (abs_lt.mp hjδ).1; linarith only [h],
        by have h := (abs_lt.mp hjδ).2; linarith only [h]⟩
  intro i hi
  have hij : i = j := (card_le_one_iff.mp hcard.le) hi hjmem
  subst i
  exact hj.trans_le (min_le_left _ _)

/-- The Ramanujan vector projected onto its actual spectral window. -/
def completeWeilWindowProjection (φ : ℝ → ℝ) (c : ℝ) (m N : ℕ) (δ : ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  HTGeometry.hermitianEigenProjection (completeWeilMatrix_isHermitian φ c N)
    (completeWeilWindow φ c N (completeWeilAdjunctionEnergy φ c m) δ) (normalizedRamanujanHorizonVector m N)

/-- A fixed spectral window captures the Ramanujan quasimode in squared norm. -/
theorem tendsto_completeWeilWindowProjection_error_sq
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      ‖normalizedRamanujanHorizonVector m N - completeWeilWindowProjection φ c m N δ‖ ^ 2)
      atTop (𝓝 0) := by
  have hbound (N : ℕ) :
      ‖normalizedRamanujanHorizonVector m N - completeWeilWindowProjection φ c m N δ‖ ^ 2 ≤
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          (completeWeilAdjunctionEnergy φ c m) • normalizedRamanujanHorizonVector m N‖ ^ 2 /
            δ ^ 2 := by
    have hgap : ∀ i ∉ completeWeilWindow φ c N (completeWeilAdjunctionEnergy φ c m) δ,
        δ ≤ |(completeWeilMatrix_isHermitian φ c N).eigenvalues i -
          (completeWeilAdjunctionEnergy φ c m)| := by
      intro i hi
      by_contra hn
      change ¬ δ ≤ |completeWeilEigenvalue φ c N i - completeWeilAdjunctionEnergy φ c m| at hn
      have h := abs_lt.mp (lt_of_not_ge hn)
      apply hi
      apply (mem_completeWeilWindow _ _ _ _ _ _).mpr
      exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
    have h := HTGeometry.gap_sq_mul_eigenProjection_error_le_residual_sq
      (completeWeilMatrix_isHermitian φ c N)
      (completeWeilWindow φ c N (completeWeilAdjunctionEnergy φ c m) δ)
      (normalizedRamanujanHorizonVector m N) (completeWeilAdjunctionEnergy φ c m)
      δ hδ.le hgap
    rw [le_div_iff₀ (sq_pos_of_pos hδ)]
    simpa only [completeWeilWindowProjection, mul_comm] using h
  have hlim := ((tendsto_completeWeilMatrix_ramanujan_residual_norm hφ hsupp hM hc0 hc1 hm).pow 2).div_const (δ ^ 2)
  apply squeeze_zero (fun N => sq_nonneg _) hbound
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] using hlim

/-- Every positive conductor yields one simple actual eigenline eventually;
its energy and projected Ramanujan vector converge at the full integer horizon. -/
theorem exists_simple_completeWeil_eigenline
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {m : ℕ} (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ N : ℕ in atTop,
        (completeWeilWindow φ c N (completeWeilAdjunctionEnergy φ c m) δ).card = 1) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        ∀ i ∈ completeWeilWindow φ c N (completeWeilAdjunctionEnergy φ c m) δ,
          |completeWeilEigenvalue φ c N i - completeWeilAdjunctionEnergy φ c m| < ε) ∧
      Tendsto (fun N : ℕ =>
        ‖normalizedRamanujanHorizonVector m N - completeWeilWindowProjection φ c m N δ‖ ^ 2)
        atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hiso⟩ := exists_isolating_completeWeil_radius hφ hsupp hM hc0 hc1 hm
  exact ⟨δ, hδ, eventually_completeWeilWindow_card_one hφ hsupp hM hc0 hc1 hm hδ hiso,
    fun ε hε => eventually_completeWeilWindow_near hφ hsupp hM hc0 hc1 hm hδ hiso hε,
    tendsto_completeWeilWindowProjection_error_sq hφ hsupp hM hc0 hc1 hm hδ⟩


end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
