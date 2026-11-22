import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorWeightedZeroPacket

/-! The zeta density estimate supplies the principal-character contribution to progression counts. -/

open Complex Filter Finset

noncomputable section

namespace QH.PrimeProgressions

open RHTower.Sieve

private theorem mem_density_packet {X : ℕ} {U σ : ℝ} {s : ℂ}
    (hU : 0 ≤ U) (hX : U ≤ (X : ℝ) - 2) (hσ : 7 / 10 ≤ σ) (hσ1 : σ < 1)
    (hs : σ ≤ s.re) (him : |s.im| ≤ U) (hz : riemannZeta s = 0) :
    s ∈ (inghamRouteTCommonZeroPacket X).filter (fun w => σ ≤ w.re) := by
  have hre1 : s.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hz
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at hre1
  have hcenter : inghamUniformGabrielCenter (7 / 10 : ℝ) ≤ σ :=
    (inghamUniformGabrielCenter_mono_on_routeT hσ).trans
      (inghamUniformGabrielCenter_le_self hσ1.le)
  have hcenter4 : inghamUniformGabrielCenter (7 / 10 : ℝ) ≤ 4 := by linarith
  refine mem_filter.mpr ⟨mem_zetaResidueUnitClosedRectangleZeros.mpr ⟨?_, ?_⟩, hs⟩
  · apply Complex.mem_reProdIm.mpr
    have hre : s.re ∈ Set.Icc (inghamUniformGabrielCenter (7 / 10 : ℝ)) 4 :=
      ⟨hcenter.trans hs, by linarith⟩
    have him' : s.im ∈ Set.Icc (-((X : ℝ) - 2)) ((X : ℝ) - 2) :=
      abs_le.mp (him.trans hX)
    have hends : -((X : ℝ) - 2) ≤ (X : ℝ) - 2 := by linarith
    exact ⟨by simpa [Set.uIcc_of_le hcenter4] using hre,
      by simpa [Set.uIcc_of_le hends] using him'⟩
  · by_contra hne
    exact (zetaResidueUnit_ne_zero_iff hs1).mp hne hz

/-- The number of distinct zeta zeros with `Re s ≥ σ ≥ 3/4` and `|Im s| ≤ U`
is bounded by `O(U^(24*(1-σ)) (log U)^16)`, uniformly in the two parameters. -/
theorem principal_zero_density :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U σ : ℝ) (F : Finset ℂ),
      6 ≤ U → 3 / 4 ≤ σ → σ < 1 →
      (∀ s ∈ F, σ ≤ s.re ∧ |s.im| ≤ U ∧ riemannZeta s = 0) →
      (F.card : ℝ) ≤ C * U ^ (24 * (1 - σ)) * Real.log U ^ (16 : ℕ) := by
  obtain ⟨K, hK, h⟩ := exists_eventually_zetaLittlewoodZeroCountAbove_le_linearExponent
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp h
  let A : ℝ := (X₀ : ℝ) + 2
  have hA : 2 ≤ A := by dsimp [A]; positivity
  let B : ℝ := 2 + Real.log A
  have hB : 0 ≤ B := by dsimp [B]; exact add_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  refine ⟨3 * K * A * B ^ 16, by positivity, fun U σ F hU hσ hσ1 hF => ?_⟩
  let X : ℕ := max X₀ (⌈U⌉₊ + 2)
  have hXe : U ≤ (X : ℝ) - 2 := by
    have hle : (⌈U⌉₊ : ℝ) + 2 ≤ X := by
      exact_mod_cast (le_max_right X₀ (⌈U⌉₊ + 2))
    linarith [Nat.le_ceil U]
  have hXR : (1 : ℝ) ≤ X := by linarith
  have hXU : (X : ℝ) ≤ A * U := by
    simp only [X, Nat.cast_max, Nat.cast_add, Nat.cast_ofNat]
    apply max_le
    · dsimp [A]
      have : (0 : ℝ) ≤ X₀ := Nat.cast_nonneg _
      nlinarith
    · have hceil : (⌈U⌉₊ : ℝ) < U + 1 := Nat.ceil_lt_add_one (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right hA (show 0 ≤ U by linarith)]
  have hlogU : 1 ≤ Real.log U := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  let L : ℝ := 1 + Real.log (X : ℝ)
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hXR]
  have hLU : L ≤ B * Real.log U := by
    have hlog := Real.log_le_log (show (0 : ℝ) < X by linarith) hXU
    rw [Real.log_mul (by linarith : A ≠ 0) (by linarith : U ≠ 0)] at hlog
    have hlogA : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
    dsimp [L, B]
    nlinarith [mul_nonneg hlogA (sub_nonneg.mpr hlogU)]
  let e : ℝ := (16 / 5 : ℝ) * (1 - σ)
  have he0 : 0 ≤ e := by dsimp [e]; linarith
  have he1 : e ≤ 1 := by dsimp [e]; linarith
  let P : ℝ := (X : ℝ) ^ e
  have hP : 1 ≤ P := Real.one_le_rpow hXR he0
  have hPU : P ≤ A * U ^ (24 * (1 - σ)) := by
    calc P ≤ (A * U) ^ e := Real.rpow_le_rpow (by linarith) hXU he0
      _ = A ^ e * U ^ e := Real.mul_rpow (by linarith) (by linarith)
      _ ≤ A * U ^ (24 * (1 - σ)) := by
        have hAe := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ A by linarith) he1
        rw [Real.rpow_one] at hAe
        bound [hAe, Real.rpow_le_rpow_of_exponent_le (show 1 ≤ U by linarith)
          (show e ≤ 24 * (1 - σ) by dsimp [e]; linarith)]
  have hσ0 : 7 / 10 ≤ σ := by linarith
  let R := (inghamRouteTCommonZeroPacket X).filter (fun w => σ ≤ w.re)
  have hFR : F ⊆ R := fun s hs => by
    obtain ⟨hre, him, hz⟩ := hF s hs
    exact mem_density_packet (by linarith) hXe hσ0 hσ1 hre him hz
  have hcard : (F.card : ℝ) ≤
      zetaLittlewoodZeroCountAbove (inghamUniformGabrielCenter σ) 4 ((X : ℝ) - 2) σ := by
    rw [zetaLittlewoodZeroCountAbove_eq_commonZeroPacket hσ0 hσ1]
    have hF' : (F.card : ℝ) ≤ ∑ s ∈ F, inghamRouteTZeroMultiplicity s := by
      rw [← mul_one (F.card : ℝ), ← nsmul_eq_mul]
      refine card_nsmul_le_sum _ _ _ fun s hs => ?_
      have hspos := inghamRouteTZeroMultiplicity_pos_of_mem_common (mem_filter.mp (hFR hs)).1
      unfold inghamRouteTZeroMultiplicity at hspos ⊢
      exact_mod_cast (show 1 ≤ (analyticOrderAt zetaResidueUnit s).toNat by exact_mod_cast hspos)
    exact hF'.trans (sum_le_sum_of_subset_of_nonneg hFR
      (fun s _ _ => inghamRouteTZeroMultiplicity_nonneg s))
  have hden := hX₀ X (le_max_left _ _) hσ0 hσ1
  have htail : 1 + P * L ^ 2 + L ^ 2 ≤ 3 * (P * L ^ 2) := by
    have hp := one_le_pow₀ (n := 2) hL
    linarith [one_le_mul_of_one_le_of_one_le hP hp, le_mul_of_one_le_left (sq_nonneg L) hP]
  calc (F.card : ℝ) ≤ K * L ^ 14 * (1 + P * L ^ 2 + L ^ 2) := hcard.trans hden
    _ ≤ K * L ^ 14 * (3 * (P * L ^ 2)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 3 * K * P * L ^ 16 := by ring
    _ ≤ 3 * K * (A * U ^ (24 * (1 - σ))) * (B * Real.log U) ^ 16 := by gcongr
    _ = _ := by ring

end QH.PrimeProgressions
