import GaloisForLFunctions.BezoutValuationIncidence.FixedVaughanPacketsHaveTwoExplicitObstructions
import GaloisForLFunctions.BezoutValuationIncidence.TheParityPairAtTheLeadingExponent
import GaloisForLFunctions.BezoutValuationIncidence.TheMeanValueIsTheLeadingCoefficientOfTheReceiver

/-!
# Uniform cancellation for truncated Möbius receivers

Every finite truncation shares the same mean-zero partial-sum modulus. The finite
hyperbola estimate transfers that modulus to a common prefix and energy saving.
Thus arbitrary moving truncations have zero trivial density at every divergent horizon.
-/

open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A common mean-zero partial-sum modulus gives a common damped-prefix modulus. -/
theorem eventually_abs_patternPrefix_le_of_uniform_mean_zero {ι : Type*} {r : ι → ℕ → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hr : ∀ i d, |r i d| ≤ 1)
    (hmean : ∀ η : ℝ, 0 < η → ∃ X : ℕ,
      ∀ i x, X ≤ x → |∑ d ∈ Icc 1 x, r i d| ≤ η * x)
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, ∀ i, |patternPrefix ε (r i) n| ≤ θ * (n : ℝ) ^ (1 - ε) := by
  have h1ε : 0 < 1 - ε := by linarith only [hε2]
  let δ : ℝ := min 1 ((θ / 6) ^ (1 - ε)⁻¹)
  have hδ0 : 0 < δ := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδpow : δ ^ (1 - ε) ≤ θ / 6 := by
    calc δ ^ (1 - ε) ≤ ((θ / 6) ^ (1 - ε)⁻¹) ^ (1 - ε) :=
      Real.rpow_le_rpow hδ0.le (min_le_right _ _) h1ε.le
      _ = θ / 6 := Real.rpow_inv_rpow (by positivity) h1ε.ne'
  let η : ℝ := θ * ε * (δ / 2) ^ ε / 26
  have hη0 : 0 < η := by dsimp only [η]; positivity
  have hηslope : 13 / ε * η * (δ / 2) ^ (-ε) = θ / 2 := by
    have hp : 0 < (δ / 2) ^ ε := Real.rpow_pos_of_pos (by positivity) _
    dsimp only [η]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    ring
  obtain ⟨X₀, hX₀⟩ := hmean η hη0
  let X := max X₀ 1
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_max_right X₀ 1
  filter_upwards [eventually_ge_atTop ⌈2 * (X : ℝ) / δ⌉₊] with n hn
  intro i
  have hny : 2 * (X : ℝ) ≤ δ * n := by
    have h := (Nat.le_ceil (2 * (X : ℝ) / δ)).trans
      (by exact_mod_cast hn : (⌈2 * (X : ℝ) / δ⌉₊ : ℝ) ≤ n)
    rw [div_le_iff₀ hδ0] at h
    linarith only [h]
  let y : ℝ := δ * n
  have hn0 : (0 : ℝ) < n := by
    by_contra h
    have hz : (n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg n)
    rw [hz, mul_zero] at hny
    linarith only [hny, hX1]
  let D : ℕ := ⌊y⌋₊
  have hDy : (D : ℝ) ≤ y := Nat.floor_le (by dsimp only [y]; positivity)
  have hyD : y / 2 ≤ D := by
    have h := Nat.lt_floor_add_one y
    change y < (D : ℝ) + 1 at h
    change 2 * (X : ℝ) ≤ y at hny
    linarith only [h, hny, hX1]
  have hXD : X ≤ D := by
    have hny' : 2 * (X : ℝ) ≤ y := hny
    exact_mod_cast (by linarith only [hny', hyD] : (X : ℝ) ≤ D)
  have hD1 : 1 ≤ D := (le_max_right X₀ 1).trans hXD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hDn : D ≤ n := by
    have h : (D : ℝ) ≤ n := hDy.trans (by
      dsimp only [y]
      exact mul_le_of_le_one_left hn0.le hδ1)
    exact_mod_cast h
  have hA := abs_weightCenteredPrefix_dampedSign_le_of_linear_all_pos hη0.le hε hε2
    (hr i) hD1 hDn (fun x hx => hX₀ i x (((le_max_left X₀ 1).trans hXD).trans hx))
  have hT1 : 3 * (D : ℝ) ^ (1 - ε) ≤ θ / 2 * (n : ℝ) ^ (1 - ε) := by
    have h := Real.rpow_le_rpow hD0.le hDy h1ε.le
    dsimp only [y] at h
    rw [Real.mul_rpow hδ0.le hn0.le] at h
    have hp : 0 ≤ (n : ℝ) ^ (1 - ε) := Real.rpow_nonneg hn0.le _
    have hprod := mul_le_mul_of_nonneg_right hδpow hp
    linarith only [h, hprod]
  have hT2 : 13 / ε * η * n * (D : ℝ) ^ (-ε) ≤ θ / 2 * (n : ℝ) ^ (1 - ε) := by
    have h := Real.rpow_le_rpow_of_nonpos (by dsimp only [y]; positivity : 0 < y / 2)
      hyD (by linarith only [hε] : -ε ≤ 0)
    have hsplit : (y / 2) ^ (-ε) = (δ / 2) ^ (-ε) * (n : ℝ) ^ (-ε) := by
      dsimp only [y]
      rw [show δ * (n : ℝ) / 2 = δ / 2 * n by ring, Real.mul_rpow (by positivity) hn0.le]
    have hnn : (n : ℝ) * (n : ℝ) ^ (-ε) = (n : ℝ) ^ (1 - ε) := by
      rw [sub_eq_add_neg, Real.rpow_add hn0, Real.rpow_one]
    calc 13 / ε * η * n * (D : ℝ) ^ (-ε) ≤ 13 / ε * η * n * (y / 2) ^ (-ε) :=
      mul_le_mul_of_nonneg_left h (by positivity)
      _ = 13 / ε * η * (δ / 2) ^ (-ε) * ((n : ℝ) * (n : ℝ) ^ (-ε)) := by rw [hsplit]; ring
      _ = θ / 2 * (n : ℝ) ^ (1 - ε) := by rw [hηslope, hnn]
  exact hA.trans (by linarith only [hT1, hT2])

/-- Truncation changes a Möbius partial sum only by truncating its endpoint. -/
theorem sum_truncatedMoebius_eq_sum_min (U x : ℕ) :
    (∑ d ∈ Icc 1 x, Sieve.truncatedMoebius U d) = ∑ d ∈ Icc 1 (min U x), moebiusReal d := by
  simp only [Sieve.truncatedMoebius_apply, ← sum_filter]
  have heq : (Icc 1 x).filter (fun d => d ≤ U) = Icc 1 (min U x) := by
    ext d
    simp only [mem_filter, mem_Icc, le_min_iff]
    tauto
  rw [heq]
  rfl

/-- Every truncation of the Möbius pattern shares one mean-zero partial-sum modulus. -/
theorem uniform_mean_zero_truncatedMoebius (η : ℝ) (hη : 0 < η) :
    ∃ X : ℕ, ∀ U x : ℕ, X ≤ x →
      |∑ d ∈ Icc 1 x, Sieve.truncatedMoebius U d| ≤ η * x := by
  obtain ⟨D₀, hD₀⟩ := Metric.tendsto_atTop.mp hasMeanValue_moebiusReal η hη
  let D := max D₀ 1
  refine ⟨max D ⌈(D : ℝ) / η⌉₊, fun U x hx => ?_⟩
  rw [sum_truncatedMoebius_eq_sum_min]
  by_cases hm : D ≤ min U x
  · have hm1 : 1 ≤ min U x := (le_max_right D₀ 1).trans hm
    have hm0 : (0 : ℝ) < min U x := by exact_mod_cast hm1
    have h := hD₀ (min U x) ((le_max_left D₀ 1).trans hm)
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hm0, div_lt_iff₀ hm0] at h
    exact h.le.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right U x) hη.le)
  · have hsum : |∑ d ∈ Icc 1 (min U x), moebiusReal d| ≤ (min U x : ℕ) := by
      calc
        _ ≤ ∑ d ∈ Icc 1 (min U x), |moebiusReal d| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _d ∈ Icc 1 (min U x), (1 : ℝ) := sum_le_sum fun d _ => abs_moebiusReal_le_one' d
        _ = _ := by simp
    have hDx : (D : ℝ) ≤ η * x := by
      have h := (Nat.le_ceil ((D : ℝ) / η)).trans
        (by exact_mod_cast (le_max_right D ⌈(D : ℝ) / η⌉₊).trans hx :
          (⌈(D : ℝ) / η⌉₊ : ℝ) ≤ x)
      rw [div_le_iff₀ hη] at h
      simpa only [mul_comm] using h
    exact hsum.trans ((by exact_mod_cast (lt_of_not_ge hm).le : (min U x : ℕ) ≤ (D : ℝ)).trans hDx)

/-- Every truncated Möbius floor prefix is uniformly negligible at the smooth-power scale. -/
theorem eventually_abs_patternPrefix_truncatedMoebius_le {ε θ : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, ∀ U : ℕ,
      |patternPrefix ε (Sieve.truncatedMoebius U) n| ≤ θ * (n : ℝ) ^ (1 - ε) := by
  apply eventually_abs_patternPrefix_le_of_uniform_mean_zero hε hε2
    (fun U d => ?_) uniform_mean_zero_truncatedMoebius hθ
  simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d

/-- Uniform mean-zero cancellation also gives a common little-o receiver-energy modulus. -/
theorem eventually_patternReceiver_div_lt_of_uniform_mean_zero {ι : Type*} {r : ι → ℕ → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hr : ∀ i d, |r i d| ≤ 1)
    (hmean : ∀ η : ℝ, 0 < η → ∃ X : ℕ,
      ∀ i x, X ≤ x → |∑ d ∈ Icc 1 x, r i d| ≤ η * x)
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∀ᶠ T : ℕ in atTop, ∀ i, patternReceiver ε (r i) T / (T : ℝ) ^ (1 - 2 * ε) < ϑ := by
  have hβ : 0 < 1 - 2 * ε := by linarith only [hε2]
  have hTa : Tendsto (fun T : ℕ => (T : ℝ) ^ (1 - 2 * ε)) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  let θ := Real.sqrt ((1 - 2 * ε) * ϑ / 4)
  have hθ0 : 0 < θ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ ^ 2 = (1 - 2 * ε) * ϑ / 4 := Real.sq_sqrt (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (eventually_abs_patternPrefix_le_of_uniform_mean_zero hε hε2.le hr hmean hθ0)
  let K : ℝ := 1 + 1 / (1 - ε) + 1 / ε
  have hglobal (i : ι) (n : ℕ) (hn : 1 ≤ n) :
      |patternPrefix ε (r i) n| ≤ K * (n : ℝ) ^ (1 - ε) := by
    have hc : DampedClass 1 ε (dampedSignWeight (r i) ε) := by
      intro d
      rw [dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      exact mul_le_mul_of_nonneg_right (hr i d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    simpa only [one_mul, patternPrefix, K] using
      abs_weightCenteredPrefix_le_of_dampedClass hε (by linarith only [hε2]) hc hn
  let C₀ : ℝ := ∑ n ∈ Icc 1 N₀, K ^ 2 * (n : ℝ) ^ (-(2 * ε))
  have hE (T : ℕ) (i : ι) : patternReceiver ε (r i) T ≤
      C₀ + θ ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
    have hcell (n : ℕ) (hn : n ∈ Icc 1 T) :
        patternPrefix ε (r i) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
          (if n < N₀ then K ^ 2 * (n : ℝ) ^ (-(2 * ε)) else 0) +
            θ ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by
      have hn1 := (mem_Icc.mp hn).1
      split_ifs with h
      · exact (cell_le_of_abs_le_rpow hn1 (hglobal i n hn1)).trans
          (le_add_of_nonneg_right (by positivity))
      · rw [zero_add]
        exact cell_le_of_abs_le_rpow hn1 (hN₀ n (not_lt.mp h) i)
    calc
      patternReceiver ε (r i) T =
          ∑ n ∈ Icc 1 T, patternPrefix ε (r i) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := rfl
      _ ≤ ∑ n ∈ Icc 1 T,
          ((if n < N₀ then K ^ 2 * (n : ℝ) ^ (-(2 * ε)) else 0) +
            θ ^ 2 * (n : ℝ) ^ (-(2 * ε))) := sum_le_sum hcell
      _ = (∑ n ∈ Icc 1 T with n < N₀, K ^ 2 * (n : ℝ) ^ (-(2 * ε))) +
          θ ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * ε)) := by
            rw [sum_add_distrib, mul_sum, sum_filter]
      _ ≤ C₀ + θ ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
        apply add_le_add
        · exact sum_le_sum_of_subset_of_nonneg (fun n hn => by
            simp only [mem_filter, mem_Icc] at hn ⊢
            omega) (fun n _ _ => by positivity)
        · exact mul_le_mul_of_nonneg_left
            (sum_Icc_rpow_neg_two_mul_le_of_pos hε hε2 T) (sq_nonneg θ)
  filter_upwards [hTa.eventually_ge_atTop (4 * (C₀ + θ ^ 2) / ϑ),
    eventually_ge_atTop 1] with T hT hT1
  intro i
  have hp : 0 < (T : ℝ) ^ (1 - 2 * ε) := Real.rpow_pos_of_pos (by exact_mod_cast hT1) _
  have hfirst : (C₀ + θ ^ 2) / (T : ℝ) ^ (1 - 2 * ε) ≤ ϑ / 4 := by
    rw [div_le_iff₀ hp]
    rw [div_le_iff₀ hϑ] at hT
    linarith only [hT]
  have hsplit : (C₀ + θ ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε))) /
      (T : ℝ) ^ (1 - 2 * ε) = (C₀ + θ ^ 2) / (T : ℝ) ^ (1 - 2 * ε) +
        θ ^ 2 / (1 - 2 * ε) := by
    field_simp
    ring
  have hθ2 : θ ^ 2 / (1 - 2 * ε) = ϑ / 4 := by rw [hθsq]; field_simp
  calc
    patternReceiver ε (r i) T / (T : ℝ) ^ (1 - 2 * ε) ≤
        (C₀ + θ ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε))) /
          (T : ℝ) ^ (1 - 2 * ε) := div_le_div_of_nonneg_right (hE T i) hp.le
    _ = (C₀ + θ ^ 2) / (T : ℝ) ^ (1 - 2 * ε) + θ ^ 2 / (1 - 2 * ε) := hsplit
    _ < ϑ := by rw [hθ2]; linarith only [hfirst, hϑ]

/-- Every divergent horizon allows an arbitrary moving truncation. -/
theorem tendsto_patternReceiver_truncatedMoebius_div_at_horizon {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto (fun T : ℕ => patternReceiver ε (Sieve.truncatedMoebius (U T)) (H T) /
      (H T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hr (U d : ℕ) : |Sieve.truncatedMoebius U d| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d
  filter_upwards [hH.eventually (eventually_patternReceiver_div_lt_of_uniform_mean_zero
    hε hε2 hr uniform_mean_zero_truncatedMoebius hη)] with T hT
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg
    (patternReceiver_nonneg _ _ _) (Real.rpow_nonneg (Nat.cast_nonneg (H T)) _))]
  exact hT (U T)

/-- A moving truncation preserves the zero energy density of the Möbius family. -/
theorem tendsto_patternReceiver_truncatedMoebius_div {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U : ℕ → ℕ) :
    Tendsto (fun T : ℕ => patternReceiver ε (Sieve.truncatedMoebius (U T)) T /
      (T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) :=
  tendsto_patternReceiver_truncatedMoebius_div_at_horizon hε hε2 U id tendsto_id

/-- The same uniform estimate in pronic norm form. -/
theorem tendsto_pronicNorm_truncatedMoebius_div_at_horizon {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) (U H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto (fun T : ℕ => pronicNorm (patternPrefix ε (Sieve.truncatedMoebius (U T))) (H T) /
      Real.sqrt ((H T : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  have h := (tendsto_patternReceiver_truncatedMoebius_div_at_horizon hε hε2 U H hH).sqrt
  simpa only [Real.sqrt_div' _ (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    patternReceiver_eq_sq, Real.sqrt_sq (pronicNorm_nonneg _ _), Real.sqrt_zero] using h

/-- The reciprocal mean of a truncated damped pattern is the finite Vaughan mean. -/
theorem tsum_damped_truncatedMoebius_div {ε : ℝ} (hε : 0 < ε) (U : ℕ) :
    (∑' d : ℕ, dampedSignWeight (Sieve.truncatedMoebius U) ε d / d) =
      pmPronicVaughanSmallDensity ε U := by
  have hr (d : ℕ) : |Sieve.truncatedMoebius U d| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d
  have h₁ := tendsto_pmFloorAverage (summable_dampedSignWeight_div_of_abs_le_one hε hr)
  have h₂ := tendsto_pmPronicVaughanPiece_div_nat hε U 0 0
  simp only [pmPronicVaughanPiece_small_eq_floorAverage] at h₂
  exact tendsto_nhds_unique h₁ h₂

/-- A centered small leg is precisely the receiver prefix of its truncated Möbius pattern. -/
theorem pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix {ε : ℝ} (hε : 0 < ε)
    (U V n : ℕ) :
    pmPronicVaughanPiece ε U V n 0 - pmPronicVaughanMean ε U V 0 * n =
      patternPrefix ε (Sieve.truncatedMoebius U) n := by
  rw [patternPrefix, weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
    tsum_damped_truncatedMoebius_div hε]
  have h := pmPronicVaughanPiece_small_eq_floorAverage ε U V n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pmPronicVaughanPiece]
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    unfold pmFloorAverage at h
    have heq := congrArg (fun x : ℝ => x * n) h
    simp only [div_mul_cancel₀ _ hn0] at heq
    change pmPronicVaughanPiece ε U V n 0 - pmPronicVaughanSmallDensity ε U * n = _
    rw [heq]
    rfl

end GaloisForLFunctions.BezoutValuationIncidence
