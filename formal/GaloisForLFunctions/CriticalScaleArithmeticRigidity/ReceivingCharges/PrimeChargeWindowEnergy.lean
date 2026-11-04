import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.BoundedVariationDilationEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeTailPairing

/-!
# Energy carried by a terminal receiving contrast

A balanced terminal contrast has bounded variation and zero harmonic pole.
Its complete energy has leading term `log N` times its harmonic square
mass. After physical normalization its own energy therefore grows like
`log N`; small source energy does not force its mixed pairing to vanish.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory

private theorem window_indicator_eq_prefix_sub {A B : ℕ} (hAB : A ≤ B) (n : ℕ) :
    (if n ∈ Ioc A B then (1 : ℝ) else 0) =
      (if n ≤ B then 1 else 0) - (if n ≤ A then 1 else 0) := by
  by_cases hA : n ≤ A
  · have hB : n ≤ B := hA.trans hAB
    have hI : n ∉ Ioc A B := fun h => (Nat.not_lt.mpr hA) (mem_Ioc.mp h).1
    simp only [if_neg hI, if_pos hA, if_pos hB, sub_self]
  · by_cases hB : n ≤ B
    · have hI : n ∈ Ioc A B := mem_Ioc.mpr ⟨by omega, hB⟩
      simp only [if_pos hI, if_neg hA, if_pos hB, sub_zero]
    · have hI : n ∉ Ioc A B := fun h => hB (mem_Ioc.mp h).2
      simp only [if_neg hI, if_neg hA, if_neg hB, sub_self]

/-- The neutral contrast has at most twice the total absolute window amplitude in variation. -/
theorem primeChargeWindowContrast_variation_le {A B C : ℕ}
    (hAB : A ≤ B) (hBC : B ≤ C) (N : ℕ) :
    horizonVariation (primeChargeWindowContrast A B C) N ≤
      2 * (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) := by
  have hw {D E : ℕ} (hDE : D ≤ E) :
      horizonVariation (fun n => if n ∈ Ioc D E then (1 : ℝ) else 0) N ≤ 2 := by
    have he : (fun n => if n ∈ Ioc D E then (1 : ℝ) else 0) =
        (fun n => (if n ≤ E then 1 else 0) - (if n ≤ D then 1 else 0)) :=
      funext (window_indicator_eq_prefix_sub hDE)
    rw [he]
    exact (horizonVariation_sub_le _ _ N).trans
      ((add_le_add (horizonVariation_prefix_le E N) (horizonVariation_prefix_le D N)).trans_eq
        (by norm_num))
  have h := horizonVariation_sub_le
    (fun n => if n ∈ Ioc B C then (1 : ℝ) else 0)
    (fun n => (primeChargeWindowMass B C / primeChargeWindowMass A B) *
      (if n ∈ Ioc A B then (1 : ℝ) else 0)) N
  rw [horizonVariation_const_mul] at h
  exact h.trans ((add_le_add (hw hBC)
    (mul_le_mul_of_nonneg_left (hw hAB) (abs_nonneg _))).trans_eq (by ring))

/-- Both moments of the terminal contrast are bounded by its total absolute amplitude. -/
theorem primeChargeWindowContrast_moments (A B C N : ℕ) :
    (∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n ^ 2 / (n : ℝ)) ≤
      RenormalizedArithmeticPotentialTheory.harmonicSum N *
        (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) ^ 2 ∧
    (∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n ^ 2) ≤
      (N : ℝ) * (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) ^ 2 := by
  have hp (n : ℕ) : primeChargeWindowContrast A B C n ^ 2 ≤
      (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (abs_primeChargeWindowContrast_le A B C n) 2
  constructor
  · rw [RenormalizedArithmeticPotentialTheory.harmonicSum, sum_mul]
    apply sum_le_sum
    intro n _
    exact (div_le_div_of_nonneg_right (hp n) (Nat.cast_nonneg n)).trans_eq (by ring)
  · calc
      _ ≤ ∑ _n ∈ Icc 1 N,
          (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) ^ 2 :=
        sum_le_sum fun n _ => hp n
      _ = _ := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-- All complete-form corrections are lower order than the contrast's logarithmic square scale. -/
theorem exists_complete_primeChargeWindow_error_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (A B C N : ℕ) (c : ℝ),
      A < B → B ≤ C → C ≤ N → 1 ≤ N → 1 ≤ c → c / N ≤ 1 / 3 →
      |completeWeilEnergy φ c N (packetVector (primeChargeWindowContrast A B C) N) -
          Real.log N * (∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n ^ 2 / (n : ℝ))| ≤
        D * c ^ 3 * (Real.log N + 1) *
          (1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|) ^ 2 := by
  obtain ⟨U, V, hU, hV, hbound⟩ := exists_complete_packet_two_moment_bound hφ hφ0 hsupp hM
  let D₀ := (Real.log 8 + 4) + 4 * (Real.log 8 + 5)
  have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  refine ⟨U + V + D₀, by positivity, ?_⟩
  intro A B C N c hAB hBC hCN hN hc hw
  let g := primeChargeWindowContrast A B C
  let M := 1 + |primeChargeWindowMass B C / primeChargeWindowMass A B|
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hneutral := primeChargeWindowContrast_harmonic_neutral hAB (hBC.trans hCN) hCN
  have hmom := primeChargeWindowContrast_moments A B C N
  have hH : RenormalizedArithmeticPotentialTheory.harmonicSum N ≤ Real.log N + 1 := by
    have h := RenormalizedArithmeticPotentialTheory.harmonicSum_le N
    linarith only [h]
  have hmass : (∑ n ∈ Icc 1 N, g n ^ 2 / (n : ℝ)) ≤ (Real.log N + 1) * M ^ 2 :=
    hmom.1.trans (mul_le_mul_of_nonneg_right hH (sq_nonneg M))
  have hc23 : c ^ 2 ≤ c ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hc (sq_nonneg c)
    nlinarith only [h]
  have hc3 : 1 ≤ c ^ 3 := (show 1 ≤ c ^ 2 by nlinarith only [hc]).trans hc23
  have hcomplete : |completeWeilEnergy φ c N (packetVector g N) - jumpEnergy N g| ≤
      (U + V) * c ^ 3 * (Real.log N + 1) * M ^ 2 := by
    refine (hbound c N hc hN hw g hneutral).trans ?_
    calc
      _ ≤ U * c ^ 2 * ((Real.log N + 1) * M ^ 2) +
          (V * c ^ 3 * (Real.log N + 1) / N) * ((N : ℝ) * M ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity))
          (mul_le_mul_of_nonneg_left hmom.2 (by positivity))
      _ ≤ U * c ^ 3 * ((Real.log N + 1) * M ^ 2) +
          (V * c ^ 3 * (Real.log N + 1) / N) * ((N : ℝ) * M ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc23 hU) (by positivity)) le_rfl
      _ = _ := by field_simp [hN0.ne']
  have hjump : |jumpEnergy N g - Real.log N * (∑ n ∈ Icc 1 N, g n ^ 2 / (n : ℝ))| ≤
      D₀ * (Real.log N + 1) * M ^ 2 := by
    have hv := pow_le_pow_left₀ (horizonVariation_nonneg g N)
      (primeChargeWindowContrast_variation_le hAB.le hBC N) 2
    refine (abs_jumpEnergy_sub_log_mass_le_variation N g hneutral).trans ?_
    calc
      _ ≤ (Real.log 8 + 4) * ((Real.log N + 1) * M ^ 2) +
          (Real.log 8 + 5) * (Real.log N + 1) * (2 * M) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity))
          (mul_le_mul (mul_le_mul_of_nonneg_left hH (by positivity)) hv
            (sq_nonneg _) (by positivity))
      _ = _ := by dsimp only [D₀]; ring
  have hjump' : D₀ * (Real.log N + 1) * M ^ 2 ≤
      D₀ * c ^ 3 * (Real.log N + 1) * M ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hc3
      (show 0 ≤ D₀ * (Real.log N + 1) * M ^ 2 by positivity)
    simpa only [mul_one] using h.trans_eq (by ring)
  calc
    _ ≤ |completeWeilEnergy φ c N (packetVector g N) - jumpEnergy N g| +
        |jumpEnergy N g - Real.log N * (∑ n ∈ Icc 1 N, g n ^ 2 / (n : ℝ))| :=
      abs_sub_le _ _ _
    _ ≤ (U + V) * c ^ 3 * (Real.log N + 1) * M ^ 2 +
        D₀ * c ^ 3 * (Real.log N + 1) * M ^ 2 :=
      add_le_add hcomplete (hjump.trans hjump')
    _ = _ := by dsimp only [M]; ring

/-- Physical normalization divides the contrast energy by the horizon logarithm. -/
theorem primeChargeWindowVector_energy (φ : ℝ → ℝ) (c : ℝ) (A B C N : ℕ) :
    completeWeilEnergy φ c N (primeChargeWindowVector A B C N) =
      completeWeilEnergy φ c N (packetVector (primeChargeWindowContrast A B C) N) /
        Real.log N := by
  simp only [primeChargeWindowVector, completeWeilEnergy, map_smul,
    real_inner_smul_left, real_inner_smul_right]
  have hs : (Real.sqrt (Real.log (N : ℝ)))⁻¹ ^ 2 = (Real.log N)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  calc
    _ = (Real.sqrt (Real.log (N : ℝ)))⁻¹ ^ 2 *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N)
          (packetVector (primeChargeWindowContrast A B C) N),
          packetVector (primeChargeWindowContrast A B C) N⟫ := by ring
    _ = _ := by rw [hs]; ring

private theorem windowVector_norm_sq_eq_mass (A B C N : ℕ) :
    ‖primeChargeWindowVector A B C N‖ ^ 2 =
      (∑ n ∈ Icc 1 N, primeChargeWindowContrast A B C n ^ 2 / (n : ℝ)) /
        Real.log N := by
  rw [primeChargeWindowVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N), packetVector_norm_sq]
  ring

/-- The cubic complete-form correction is sublogarithmic at critical overlap. -/
theorem tendsto_primeChargeCriticalOverlap_cube_div_log (K : ℝ) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun X : ℕ => (2 * K * Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) ^ 3 /
      Real.log (X ^ d : ℕ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun X : ℕ => X ^ d) atTop atTop := tendsto_pow_atTop hd.ne'
  have hL := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hN
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 8)).comp hL).const_mul
    ((2 * K) ^ 3)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hLX : 0 < Real.log (X ^ d : ℕ) :=
    Real.log_pos (by exact_mod_cast (hX.trans (Nat.le_pow hd)))
  dsimp only [Function.comp_def]
  have he : (Real.log (X ^ d : ℕ) ^ (1 / 8 : ℝ)) ^ (3 : ℕ) /
      Real.log (X ^ d : ℕ) = Real.log (X ^ d : ℕ) ^ (-(5 / 8 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLX.le]
    norm_num only [Nat.cast_ofNat, show (1 / 8 : ℝ) * 3 = 3 / 8 by norm_num]
    rw [show (-(5 / 8 : ℝ)) = 3 / 8 - 1 by norm_num, Real.rpow_sub hLX,
      Real.rpow_one]
  rw [← he]
  ring

/-- A terminal contrast's own complete energy grows logarithmically, with its exact mass coefficient. -/
theorem tendsto_primeChargeWindowVector_complete_scaled {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) {a : ℕ} (ha : 0 < a) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ (a + 2) : ℕ) ^ (1 / 8 : ℝ))
        (X ^ (a + 2))
        (primeChargeWindowVector (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) (X ^ (a + 2))) /
          Real.log (X ^ (a + 2) : ℕ)) atTop (𝓝 (2 / ((a : ℝ) + 2))) := by
  obtain ⟨D, hD, hbound⟩ := exists_complete_primeChargeWindow_error_bound hφ hφ0 hsupp hM
  have hN : Tendsto (fun X : ℕ => X ^ (a + 2)) atTop atTop :=
    tendsto_pow_atTop (by omega)
  have hL := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hN
  have hpower := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 8)).comp hL
  have hratio := tendsto_primeChargeWindowRatio ha
  have hlim := ((((tendsto_const_nhds (x := (1 : ℝ))).add hratio.abs).pow 2).mul
    hpower).const_mul (2 * D * (2 * K) ^ 3)
  simp only [mul_zero] at hlim
  have herr : Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ (a + 2) : ℕ) ^ (1 / 8 : ℝ))
        (X ^ (a + 2))
        (primeChargeWindowVector (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) (X ^ (a + 2))) /
          Real.log (X ^ (a + 2) : ℕ) -
      ‖primeChargeWindowVector (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) (X ^ (a + 2))‖ ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 2,
      hN.eventually (eventually_primeCharge_criticalOverlap_facts hK),
      hL.eventually (eventually_ge_atTop 1)] with X hX hc hLX
    change 1 ≤ Real.log (X ^ (a + 2) : ℕ) at hLX
    let L := Real.log (X ^ (a + 2) : ℕ)
    let M := 1 + |primeChargeWindowMass (X ^ (a + 1)) (X ^ (a + 2)) /
      primeChargeWindowMass (X ^ a) (X ^ (a + 1))|
    have hL0 : 0 < L := zero_lt_one.trans_le hLX
    have hb := hbound (X ^ a) (X ^ (a + 1)) (X ^ (a + 2)) (X ^ (a + 2))
      (2 * K * L ^ (1 / 8 : ℝ))
      (Nat.pow_lt_pow_right (by omega) (by omega))
      (Nat.pow_le_pow_right (by omega) (by omega)) le_rfl
      (Nat.one_le_pow _ X (by omega)) hc.1 hc.2
    have he : (L ^ (1 / 8 : ℝ)) ^ (3 : ℕ) / L = L ^ (-(5 / 8 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      norm_num only [Nat.cast_ofNat, show (1 / 8 : ℝ) * 3 = 3 / 8 by norm_num]
      rw [show (-(5 / 8 : ℝ)) = 3 / 8 - 1 by norm_num, Real.rpow_sub hL0,
        Real.rpow_one]
    rw [primeChargeWindowVector_energy, windowVector_norm_sq_eq_mass]
    have hid (E H : ℝ) : E / L / L - H / L = (E - L * H) / L ^ 2 := by
      field_simp [hL0.ne']
    rw [hid, Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hL0)]
    refine (div_le_div_of_nonneg_right hb (sq_nonneg L)).trans ?_
    change D * (2 * K * L ^ (1 / 8 : ℝ)) ^ 3 * (L + 1) * M ^ 2 / L ^ 2 ≤
      2 * D * (2 * K) ^ 3 * (M ^ 2 * L ^ (-(5 / 8 : ℝ)))
    calc
      _ ≤ D * (2 * K * L ^ (1 / 8 : ℝ)) ^ 3 * (2 * L) * M ^ 2 / L ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg L)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg M)
        exact mul_le_mul_of_nonneg_left (by linarith only [hLX]) (by positivity)
      _ = _ := by
        rw [← he, mul_pow]
        field_simp [hL0.ne']
  have h := herr.add (tendsto_primeChargeWindowVector_norm_sq ha)
  simpa only [sub_add_cancel, zero_add] using h

#print axioms exists_complete_primeChargeWindow_error_bound
#print axioms tendsto_primeChargeWindowVector_complete_scaled

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
