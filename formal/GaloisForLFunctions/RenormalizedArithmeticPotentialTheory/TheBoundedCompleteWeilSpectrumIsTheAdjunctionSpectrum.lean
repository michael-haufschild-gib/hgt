import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedCompleteWeilEnergyHasFiniteRamanujanCoordinates
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixRealizesFiniteAdjunctionPackets
import GaloisForLFunctions.HTGeometry.HermitianLowerSpectralWindows

/-!
# Exact bounded spectral counts for the complete Weil matrix

Arithmetic packets supply the lower count. Coercivity gives finitely many
Ramanujan coordinates detecting every bounded-energy unit vector. Norm
residuals suppress the coordinates above a fixed threshold, and rank bounds
all remaining low spectral multiplicity by the exact arithmetic count.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Actual eigenvalues of the complete Weil matrix, with multiplicity. -/
def completeWeilEigenvalue (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (i : PrimeHorizonIndex N) : ℝ :=
  (completeWeilMatrix_isHermitian φ c N).eigenvalues i

/-- Actual complete-Weil spectral indices below a threshold. -/
def completeWeilSpectralSublevel (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (T : ℝ) :
    Finset (PrimeHorizonIndex N) :=
  univ.filter (fun i => completeWeilEigenvalue φ c N i < T)

/-- Every arithmetic energy strictly below a threshold contributes a distinct
actual eigenvalue below that threshold eventually. -/
theorem eventually_completeWeil_arithmetic_count_le_spectral_count
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (T : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (completeWeilEnergySublevel φ c T).card ≤ (completeWeilSpectralSublevel φ c N T).card := by
  let S := completeWeilEnergySublevel φ c T
  have hS : ∀ m ∈ S, 0 < m := fun m hm => (mem_completeWeilEnergySublevel φ c T m).mp hm |>.1
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_gap_above_completeWeilEnergySublevel φ c T
  filter_upwards [eventually_completeWeilMatrix_finite_adjunction_packet hφ hsupp hM hc0 hc1 S hS hδ]
    with N hN
  obtain ⟨eig, hinj, hspec, hnear⟩ := hN
  have hindices : ∀ m : S, ∃ i : PrimeHorizonIndex N,
      (completeWeilMatrix_isHermitian φ c N).eigenvalues i = eig m := by
    intro m
    have h := hspec m
    rw [(completeWeilMatrix_isHermitian φ c N).spectrum_real_eq_range_eigenvalues] at h
    exact h
  choose idx hidx using hindices
  have hmem (m : S) : idx m ∈ completeWeilSpectralSublevel φ c N T := by
    rw [completeWeilSpectralSublevel, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have h := (abs_lt.mp (hnear m)).2
    have hg := hgap m m.property
    rw [completeWeilEigenvalue, hidx]
    linarith only [h, hg]
  let f : S → ↥(completeWeilSpectralSublevel φ c N T) := fun m => ⟨idx m, hmem m⟩
  have hf : Function.Injective f := by
    intro m l hml
    apply hinj
    have hi : idx m = idx l := congrArg Subtype.val hml
    have he := congrArg (completeWeilMatrix_isHermitian φ c N).eigenvalues hi
    rwa [hidx, hidx] at he
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- No extra low spectral multiplicity survives away from the arithmetic energy set. -/
theorem eventually_completeWeil_spectral_count_le_arithmetic_count
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (T : ℝ)
    (hT : ∀ m : ℕ, 0 < m → completeWeilAdjunctionEnergy φ c m ≠ T) :
    ∀ᶠ N : ℕ in atTop,
      (completeWeilSpectralSublevel φ c N T).card ≤ (completeWeilEnergySublevel φ c T).card := by
  let S := completeWeilEnergySublevel φ c T
  obtain ⟨C, hC, hcert⟩ := exists_finite_completeWeil_ramanujan_coordinate_certificate hφ hsupp hM hc0 hc1 T
  let R : ℕ → ℕ → ℝ := fun m N =>
    ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
      (completeWeilAdjunctionEnergy φ c m) • normalizedRamanujanHorizonVector m N‖
  let F : ℕ → ℝ := fun N => ∑ m ∈ C,
    if m ∈ S then 0 else R m N ^ 2 / (completeWeilAdjunctionEnergy φ c m - T) ^ 2
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hi : ∀ m ∈ C, Tendsto (fun N : ℕ =>
        if m ∈ S then (0 : ℝ) else R m N ^ 2 / (completeWeilAdjunctionEnergy φ c m - T) ^ 2)
        atTop (𝓝 0) := by
      intro m hm
      by_cases hs : m ∈ S
      · simp only [if_pos hs]
        exact tendsto_const_nhds
      · simp only [if_neg hs]
        have hr := (tendsto_completeWeilMatrix_ramanujan_residual_norm hφ hsupp hM hc0 hc1 (hC m hm)).pow 2
        simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, R] using
          hr.div_const ((completeWeilAdjunctionEnergy φ c m - T) ^ 2)
    simpa only [F, sum_const_zero] using tendsto_finsetSum C hi
  have hsmall : ∀ᶠ N : ℕ in atTop, F N < 1 / 18 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 18))
  filter_upwards [hcert, hsmall] with N hcN hsmallN
  have hcount : (univ.filter (fun i : PrimeHorizonIndex N =>
      (completeWeilMatrix_isHermitian φ c N).eigenvalues i < T)).card ≤ Fintype.card S := by
    apply HTGeometry.lowerSpectralWindow_card_le_of_coordinates
      (completeWeilMatrix_isHermitian φ c N) T
      (fun m : S => normalizedRamanujanHorizonVector m N)
    intro x hx hlo
    by_contra hn
    push Not at hn
    have henergy : completeWeilEnergy φ c N x ≤ T := by
      have h := HTGeometry.hermitianEnergy_le_of_support
        (completeWeilMatrix_isHermitian φ c N) T x hlo
      simpa only [completeWeilEnergy, hx, one_pow, mul_one] using h
    have hmass := hcN x hx henergy
    have hsum : (∑ m ∈ C, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤ F N := by
      refine sum_le_sum fun m hm => ?_
      by_cases hs : m ∈ S
      · rw [if_pos hs, hn ⟨m, hs⟩, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      · rw [if_neg hs]
        have hnot : ¬ completeWeilAdjunctionEnergy φ c m < T := fun h =>
          hs ((mem_completeWeilEnergySublevel φ c T m).mpr ⟨hC m hm, h⟩)
        have hge : T ≤ completeWeilAdjunctionEnergy φ c m := le_of_not_gt hnot
        have hgt : T < completeWeilAdjunctionEnergy φ c m :=
          lt_of_le_of_ne hge (Ne.symm (hT m (hC m hm)))
        exact HTGeometry.inner_sq_le_residual_sq_div_upper_gap_sq
          (completeWeilMatrix_isHermitian φ c N) T (completeWeilAdjunctionEnergy φ c m)
          hgt x (normalizedRamanujanHorizonVector m N) hx hlo
    linarith only [hmass, hsum, hsmallN]
  simpa only [completeWeilSpectralSublevel, completeWeilEigenvalue, Fintype.card_coe] using hcount

/-- Every bounded window of the literal complete-Weil matrix is exhausted,
with multiplicity, by the simple arithmetic adjunction energies. -/
theorem eventually_completeWeil_spectral_count_eq
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (T : ℝ)
    (hT : ∀ m : ℕ, 0 < m → completeWeilAdjunctionEnergy φ c m ≠ T) :
    ∀ᶠ N : ℕ in atTop,
      (completeWeilSpectralSublevel φ c N T).card = (completeWeilEnergySublevel φ c T).card := by
  filter_upwards [eventually_completeWeil_spectral_count_le_arithmetic_count hφ hsupp hM hc0 hc1 T hT,
    eventually_completeWeil_arithmetic_count_le_spectral_count hφ hsupp hM hc0 hc1 T] with N hu hl
  exact Nat.le_antisymm hu hl


end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
