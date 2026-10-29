import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixHasRamanujanQuasimodes
import GaloisForLFunctions.ArithmeticIncidencePositivity.ArchimedeanBumpBridgeAndSelfEnergyAsymptotic

/-!
# Complete-Weil spectral points and finite arithmetic packets

The actual norm quasimodes force eigenvalues near each explicit arithmetic
energy. Distinct trial energies separate every fixed finite conductor packet,
so these nearby eigenvalues are simultaneously distinct.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Each positive conductor is approached by actual complete-Weil eigenvalues. -/
theorem eventually_completeWeilMatrix_eigenvalue_near
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ i : PrimeHorizonIndex N,
      |(completeWeilMatrix_isHermitian φ c N).eigenvalues i -
        completeWeilAdjunctionEnergy φ c m| < ε := by
  have hres := (tendsto_completeWeilMatrix_ramanujan_residual_norm hφ hsupp hM hc0 hc1 hm).pow 2
  have hnorm := (tendsto_normalizedRamanujanHorizonVector_norm_sq hm).const_mul (ε ^ 2)
  have hlt := hres.eventually_lt hnorm (by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_one] using pow_pos hε 2)
  filter_upwards [hlt] with N hN
  exact HTGeometry.exists_eigenvalue_abs_sub_lt_of_residual_sq_lt
    (completeWeilMatrix_isHermitian φ c N) (normalizedRamanujanHorizonVector m N)
    (completeWeilAdjunctionEnergy φ c m) hε.le hN

/-- Each fixed finite packet of positive conductors gives distinct actual spectral
points, with any prescribed accuracy, at every sufficiently large horizon. -/
theorem eventually_completeWeilMatrix_finite_adjunction_packet
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ eig : S → ℝ, Function.Injective eig ∧
      (∀ m, eig m ∈ spectrum ℝ (completeWeilMatrix φ c N)) ∧
      ∀ m, |eig m - (completeWeilAdjunctionEnergy φ c m)| < ε := by
  classical
  obtain ⟨s, hs, _, hsep⟩ := ArithmeticIncidencePositivity.exists_separation_finset
    (S.image (completeWeilAdjunctionEnergy φ c))
  let δ : ℝ := min ε (s / 4)
  have hδ : 0 < δ := lt_min hε (div_pos hs (by norm_num))
  have hδeps : δ ≤ ε := min_le_left _ _
  have hδs : δ ≤ s / 4 := min_le_right _ _
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ m : S, ∃ i : PrimeHorizonIndex N,
      |(completeWeilMatrix_isHermitian φ c N).eigenvalues i -
        (completeWeilAdjunctionEnergy φ c m)| < δ := by
    rw [Filter.eventually_all]
    intro m
    exact eventually_completeWeilMatrix_eigenvalue_near hφ hsupp hM hc0 hc1 (hS m m.property) hδ
  filter_upwards [hevent] with N hN
  choose i hi using hN
  let eig : S → ℝ := fun m => (completeWeilMatrix_isHermitian φ c N).eigenvalues (i m)
  refine ⟨eig, ?_, ?_, ?_⟩
  · intro a b hab
    by_contra hne
    have hEne : completeWeilAdjunctionEnergy φ c a ≠ completeWeilAdjunctionEnergy φ c b := by
      intro h
      exact hne (Subtype.ext (completeWeilAdjunctionEnergy_injectiveOn hφ.continuous hsupp hM hc0.le hc1
        (hS a a.property) (hS b b.property) h))
    have habsep := hsep _ (mem_image.mpr ⟨a, a.property, rfl⟩)
      _ (mem_image.mpr ⟨b, b.property, rfl⟩) hEne
    have hclose : |completeWeilAdjunctionEnergy φ c a - completeWeilAdjunctionEnergy φ c b| < 2 * δ := by
      calc
        _ = |(eig a - (completeWeilAdjunctionEnergy φ c a)) -
              (eig b - (completeWeilAdjunctionEnergy φ c b))| := by
          rw [hab]
          have heq : (eig b - completeWeilAdjunctionEnergy φ c a) -
              (eig b - completeWeilAdjunctionEnergy φ c b) =
                completeWeilAdjunctionEnergy φ c b - completeWeilAdjunctionEnergy φ c a := by ring
          rw [heq, abs_sub_comm]
        _ ≤ |eig a - (completeWeilAdjunctionEnergy φ c a)| +
              |eig b - (completeWeilAdjunctionEnergy φ c b)| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le (eig a - (completeWeilAdjunctionEnergy φ c a))
              (-(eig b - (completeWeilAdjunctionEnergy φ c b)))
        _ < δ + δ := add_lt_add (hi a) (hi b)
        _ = 2 * δ := by ring
    linarith only [habsep, hclose, hδs, hs]
  · intro m
    exact (completeWeilMatrix_isHermitian φ c N).eigenvalues_mem_spectrum_real (i m)
  · intro m
    exact (hi m).trans_le hδeps


/-- A finite strict sublevel stays a positive distance below its threshold. -/
theorem exists_pos_gap_above_completeWeilEnergySublevel (φ : ℝ → ℝ) (c T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m ∈ completeWeilEnergySublevel φ c T,
      completeWeilAdjunctionEnergy φ c m + δ < T := by
  have hfinite : ∀ S : Finset ℕ, (∀ m ∈ S, completeWeilAdjunctionEnergy φ c m < T) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ m ∈ S, completeWeilAdjunctionEnergy φ c m + δ < T := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, zero_lt_one, fun m hm => by simp at hm⟩
    | @insert m S hm ih =>
      intro hS
      obtain ⟨δ, hδ, hgap⟩ := ih (fun n hn => hS n (mem_insert_of_mem hn))
      have hmT := hS m (mem_insert_self m S)
      refine ⟨min δ ((T - completeWeilAdjunctionEnergy φ c m) / 2),
        lt_min hδ (by linarith only [hmT]), fun n hn => ?_⟩
      rcases mem_insert.mp hn with hnm | hn
      · subst n
        have h := min_le_right δ ((T - completeWeilAdjunctionEnergy φ c m) / 2)
        linarith only [h, hmT]
      · have h := min_le_left δ ((T - completeWeilAdjunctionEnergy φ c m) / 2)
        linarith only [h, hgap n hn]
  exact hfinite (completeWeilEnergySublevel φ c T) fun m hm => (mem_completeWeilEnergySublevel φ c T m).mp hm |>.2


end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
