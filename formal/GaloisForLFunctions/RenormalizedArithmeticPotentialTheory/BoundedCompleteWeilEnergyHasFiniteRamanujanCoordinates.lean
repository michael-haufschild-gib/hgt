import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilEnergyControlsThePrimeDefect
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates

/-!
# Bounded complete-Weil energy has finite Ramanujan coordinates

Complete-Weil coercivity bounds the literal prime defect. Arithmetic compactness
then supplies a fixed finite Ramanujan approximation on each bounded energy
sublevel. The asymptotic identity Gram matrix turns this approximation into a
uniform positive coordinate mass on every unit vector in that sublevel.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- One uniform prime-defect bound controls each bounded complete-Weil energy sublevel. -/
theorem eventually_poleDefect_le_of_completeWeilEnergy_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (T : ℝ) :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ‖x‖ = 1 → completeWeilEnergy φ c N x ≤ T →
        poleDefect N (primeHorizonExtension x) ≤ K := by
  obtain ⟨a, ha⟩ := eventually_completeWeilEnergy_ge_primeDefect hφ hsupp hM hc0 hc1
  have hk : 0 < (1 - c) / 4 := div_pos (sub_pos.mpr hc1) (by norm_num)
  refine ⟨max 0 ((T - a) / ((1 - c) / 4)), ?_⟩
  filter_upwards [ha] with N hN x hx henergy
  have h := hN x
  rw [hx, one_pow, mul_one] at h
  have hd : poleDefect N (primeHorizonExtension x) ≤ (T - a) / ((1 - c) / 4) := by
    rw [le_div_iff₀ hk]
    linarith only [h, henergy]
  exact hd.trans (le_max_right _ _)

/-- Every bounded actual energy sublevel is uniformly approximated by one fixed
finite Ramanujan span, with arbitrary prescribed squared error. -/
theorem exists_finite_ramanujan_approximation_of_completeWeilEnergy_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (T : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖x‖ = 1 → completeWeilEnergy φ c N x ≤ T →
          ∃ a : ℕ → ℝ, ‖x - ∑ m ∈ S, a m • ramanujanHorizonVector m N‖ ^ 2 ≤ η := by
  obtain ⟨K, hK⟩ := eventually_poleDefect_le_of_completeWeilEnergy_le hφ hsupp hM hc0 hc1 T
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le
    K hη
  refine ⟨S, hS, ?_⟩
  filter_upwards [hK]
    with N hN x hx henergy
  obtain ⟨a, ha⟩ := happ N (primeHorizonExtension x)
    (by rw [sum_primeHorizonExtension_sq, hx]; norm_num) (hN x hx henergy)
  refine ⟨a, ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [← sum_coe_sort (Icc 1 N) (fun n =>
    (primeHorizonExtension x n - ∑ m ∈ S, a m * ramanujanPoleProfile m n) ^ 2)] at ha
  convert ha using 1
  apply sum_congr rfl
  intro n _
  have hsum : (∑ m ∈ S, a m • ramanujanHorizonVector m N) n =
      ∑ m ∈ S, a m * ramanujanPoleProfile m n := by
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n) (∑ m ∈ S, a m • ramanujanHorizonVector m N) = _
    rw [map_sum]
    exact sum_congr rfl fun m _ => rfl
  simp only [PiLp.sub_apply, hsum, primeHorizonExtension_coe]


/-- Actual bounded-energy unit vectors have uniformly positive mass in a fixed
finite list of Ramanujan coordinates. No limiting operator is assumed. -/
theorem exists_finite_completeWeil_ramanujan_coordinate_certificate
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (T : ℝ) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖x‖ = 1 → completeWeilEnergy φ c N x ≤ T →
          1 / 18 ≤ ∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_completeWeilEnergy_le hφ hsupp hM hc0 hc1 T
    (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨S, hS, ?_⟩
  filter_upwards [happ, eventually_normalizedRamanujanHorizonVector_gram_close S hS,
    eventually_ge_atTop 2] with N haN hgram hN x hx henergy
  obtain ⟨a, ha⟩ := haN x hx henergy
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hs : Real.sqrt (Real.log N) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  let b : S → ℝ := fun m => a m * Real.sqrt (Real.log N)
  have heq : (∑ m : S, b m • normalizedRamanujanHorizonVector m N) =
      ∑ m ∈ S, a m • ramanujanHorizonVector m N := by
    rw [← sum_coe_sort S (fun m => a m • ramanujanHorizonVector m N)]
    refine sum_congr rfl fun m _ => ?_
    rw [normalizedRamanujanHorizonVector, smul_smul]
    congr 1
    dsimp only [b]
    field_simp
  have hcert := HTGeometry.coordinate_mass_ge_of_finite_approximation
    (fun m : S => normalizedRamanujanHorizonVector m N) hgram x hx b
    (by rw [heq]; exact ha)
  simpa only [sum_coe_sort S (fun m => ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2)] using hcert


end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
