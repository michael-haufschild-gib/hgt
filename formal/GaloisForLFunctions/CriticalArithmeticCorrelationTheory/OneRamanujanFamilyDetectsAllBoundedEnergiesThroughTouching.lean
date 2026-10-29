import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OnePrimeDefectReserveCoversEveryRatioThroughTouching
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedCompleteWeilEnergyHasFiniteRamanujanCoordinates

/-!
# Uniform arithmetic compactness through touching

The common complete-energy reserve bounds the prime defect at every ratio
up to one. Arithmetic compactness supplies one finite Ramanujan span and one
positive coordinate certificate for the whole bounded-energy family.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory

/-- One prime-defect bound covers every bounded actual energy sublevel through touching. -/
theorem eventually_poleDefect_le_uniformly_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (T : ℝ) :
    ∃ K : ℝ, ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖x‖ = 1 → completeWeilEnergy φ c N x ≤ T →
          poleDefect N (primeHorizonExtension x) ≤ K := by
  obtain ⟨hk, a, ha⟩ := exists_uniform_completeWeil_primeDefect_reserve_through_touching hφ hsupp hM
  refine ⟨max 0 ((T - a) / ((1 - completeWeilPoleShift φ 1) / 4)), ?_⟩
  filter_upwards [ha] with N hN
  intro c hc0 hc1 x hx henergy
  have h := hN c hc0 hc1 x
  rw [hx, one_pow, mul_one] at h
  have hd : poleDefect N (primeHorizonExtension x) ≤
      (T - a) / ((1 - completeWeilPoleShift φ 1) / 4) := by
    rw [le_div_iff₀ hk]
    linarith only [h, henergy]
  exact hd.trans (le_max_right _ _)

/-- One finite Ramanujan span approximates all unit vectors of bounded complete
energy, simultaneously at every ratio through one. -/
theorem exists_finite_ramanujan_approximation_uniformly_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (T : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          ‖x‖ = 1 → completeWeilEnergy φ c N x ≤ T →
            ∃ a : ℕ → ℝ, ‖x - ∑ m ∈ S, a m • ramanujanHorizonVector m N‖ ^ 2 ≤ η := by
  obtain ⟨K, hK⟩ := eventually_poleDefect_le_uniformly_at_touching hφ hsupp hM T
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_of_poleDefect_le K hη
  refine ⟨S, hS, ?_⟩
  filter_upwards [hK] with N hN
  intro c hc0 hc1 x hx henergy
  obtain ⟨a, ha⟩ := happ N (primeHorizonExtension x)
    (by rw [sum_primeHorizonExtension_sq, hx]; norm_num) (hN c hc0 hc1 x hx henergy)
  refine ⟨a, ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [← sum_coe_sort (Icc 1 N) (fun n =>
    (primeHorizonExtension x n - ∑ m ∈ S, a m * ramanujanPoleProfile m n) ^ 2)] at ha
  convert ha using 1
  apply sum_congr rfl
  intro n _
  have hsum : (∑ m ∈ S, a m • ramanujanHorizonVector m N) n =
      ∑ m ∈ S, a m * ramanujanPoleProfile m n := by
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
      (∑ m ∈ S, a m • ramanujanHorizonVector m N) = _
    rw [map_sum]
    exact sum_congr rfl fun m _ => rfl
  simp only [PiLp.sub_apply, hsum, primeHorizonExtension_coe]

/-- A fixed finite list of arithmetic modes detects all bounded-energy unit
vectors through touching with a positive coordinate mass. -/
theorem exists_finite_ramanujan_coordinate_certificate_uniformly_at_touching {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (T : ℝ) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ 1 →
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          ‖x‖ = 1 → completeWeilEnergy φ c N x ≤ T →
            1 / 18 ≤ ∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
  obtain ⟨S, hS, happ⟩ := exists_finite_ramanujan_approximation_uniformly_at_touching hφ hsupp hM T
    (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨S, hS, ?_⟩
  filter_upwards [happ, eventually_normalizedRamanujanHorizonVector_gram_close S hS,
    eventually_ge_atTop 2] with N haN hgram hN
  intro c hc0 hc1 x hx henergy
  obtain ⟨a, ha⟩ := haN c hc0 hc1 x hx henergy
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

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_finite_ramanujan_approximation_uniformly_at_touching
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_finite_ramanujan_coordinate_certificate_uniformly_at_touching
