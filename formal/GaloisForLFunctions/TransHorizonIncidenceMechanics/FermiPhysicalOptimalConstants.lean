import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiPhysicalSineAsymptotics
import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabHorizonFiltrationAndSawtoothEvolution
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Optimal physical conditioning of the complete selected Fermi trace

The unrestricted and nonnegative physical inverse constants are suprema of
`sieveTotalPronicEnergy / fermiSelectedTotalPronicEnergy` over inputs with positive
selected energy. Their defining sets are bounded above; at horizons at least two,
the cosine family and zero extension also prove nonemptiness.

Both constants, divided by `(Real.logb 2 N)^2`, tend to `4 / Real.pi^2` along all
natural horizons. The dyadic limits use the uniform sine upper bound and the
admissible nonnegative cosine family. The all-horizon limits reuse the existing
Buchstab horizon-band identity to transfer both physical energies under coefficient
zero extension, then squeeze between consecutive dyadic horizons.

The finite-path sine inequality and scalar limit machinery are prior results.
This module closes their application to the literal complete pronic trace norms;
no coefficient-norm replacement or unproved analytic estimate is assumed.
-/

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open Filter Topology
open scoped BigOperators
open BezoutValuationIncidence

private def physicalRatios (N : ℕ) (D : Set (ℕ → ℝ)) : Set ℝ :=
  {t | ∃ c ∈ D, 0 < fermiSelectedTotalPronicEnergy N c ∧
    t = sieveTotalPronicEnergy N c / fermiSelectedTotalPronicEnergy N c}

private noncomputable def physicalConstantOn (N : ℕ) (D : Set (ℕ → ℝ)) : ℝ :=
  sSup (physicalRatios N D)

/-- Supremum of the physical sieve/selected-trace energy ratio over all real coefficients. -/
noncomputable def fermiPhysicalInverseConstant (N : ℕ) : ℝ :=
  physicalConstantOn N Set.univ

/-- The same physical ratio supremum restricted to pointwise nonnegative coefficients. -/
noncomputable def fermiNonnegativePhysicalInverseConstant (N : ℕ) : ℝ :=
  physicalConstantOn N {c | ∀ d : ℕ, 0 ≤ c d}

private theorem physical_ratios_bddAbove (N : ℕ) (D : Set (ℕ → ℝ)) :
    BddAbove (physicalRatios N D) := by
  let d := Nat.log 2 N + 1
  refine ⟨((d : ℝ) + 4) * ((d : ℝ) + 1), ?_⟩
  rintro t ⟨c, _, hQ, rfl⟩
  exact (div_le_iff₀ hQ).2 (sieveTotalPronicEnergy_le_depth_selected N c)

private theorem cosine_ratio_mem (L : ℕ) (D : Set (ℕ → ℝ))
    (hD : fermiDyadicCosineWeight L ∈ D) :
    sieveTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) /
      fermiSelectedTotalPronicEnergy (2^(L + 1)) (fermiDyadicCosineWeight L) ∈
        physicalRatios (2^(L + 1)) D :=
  ⟨fermiDyadicCosineWeight L, hD, fermiDyadicCosine_selected_pos L, rfl⟩

private theorem physical_constant_scaled_dyadic_limit (D : Set (ℕ → ℝ))
    (hD : ∀ L : ℕ, fermiDyadicCosineWeight L ∈ D) :
    Tendsto (fun L : ℕ => physicalConstantOn (2^(L + 1)) D / ((L + 1 : ℕ) : ℝ)^2)
      atTop (𝓝 (4 / Real.pi^2)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let ε := (4 / Real.pi^2 - a) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨R, hR⟩ := fermiDyadicCosine_asymptotic_lower ε hε
    refine eventually_atTop.2 ⟨R, fun L hL => ?_⟩
    have hQ := fermiDyadicCosine_selected_pos L
    have hlow := (le_div_iff₀ hQ).2 (hR L hL)
    have hsup := le_csSup (physical_ratios_bddAbove (2^(L + 1)) D) (cosine_ratio_mem L D (hD L))
    have hbound : 4 / Real.pi^2 - ε ≤
        physicalConstantOn (2^(L + 1)) D / ((L + 1 : ℕ) : ℝ)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < (L + 1 : ℕ)))).2
      exact hlow.trans hsup
    exact (show a < 4 / Real.pi^2 - ε by dsimp [ε]; linarith).trans_le hbound
  · intro a ha
    let ε := (a - 4 / Real.pi^2) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    obtain ⟨R, hR⟩ := sieveTotalPronicEnergy_asymptotic_upper ε hε
    refine eventually_atTop.2 ⟨R, fun L hL => ?_⟩
    have hne : (physicalRatios (2^(L + 1)) D).Nonempty := ⟨_, cosine_ratio_mem L D (hD L)⟩
    have hsup : physicalConstantOn (2^(L + 1)) D ≤
        (4 / Real.pi^2 + ε) * ((L + 1 : ℕ) : ℝ)^2 := by
      apply csSup_le hne
      rintro t ⟨c, _, hQ, rfl⟩
      exact (div_le_iff₀ hQ).2 (hR (L + 1) (by omega) c)
    have hbound : physicalConstantOn (2^(L + 1)) D / ((L + 1 : ℕ) : ℝ)^2 ≤ 4 / Real.pi^2 + ε :=
      (div_le_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < (L + 1 : ℕ)))).2 hsup
    exact hbound.trans_lt (show 4 / Real.pi^2 + ε < a by dsimp [ε]; linarith)

/-- The unrestricted optimal physical inverse constant has sharp dyadic leading coefficient `4/pi²`. -/
theorem fermiPhysicalInverseConstant_dyadic_limit :
    Tendsto (fun r : ℕ => fermiPhysicalInverseConstant (2^r) / (r : ℝ)^2)
      atTop (𝓝 (4 / Real.pi^2)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact physical_constant_scaled_dyadic_limit Set.univ (fun _ => Set.mem_univ _)

/-- Nonnegative coefficients attain the same sharp dyadic leading coefficient. -/
theorem fermiNonnegativePhysicalInverseConstant_dyadic_limit :
    Tendsto (fun r : ℕ => fermiNonnegativePhysicalInverseConstant (2^r) / (r : ℝ)^2)
      atTop (𝓝 (4 / Real.pi^2)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact physical_constant_scaled_dyadic_limit {c | ∀ d : ℕ, 0 ≤ c d} fermiDyadicCosineWeight_nonneg

private def horizonTruncate (M : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d ≤ M then c d else 0

private theorem sieve_horizon_truncate {M N : ℕ} (hMN : M ≤ N) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq N (horizonTruncate M c) k = sieveSeq M c k := by
  have hsmall : sieveSeq M (horizonTruncate M c) k = sieveSeq M c k := by
    unfold sieveSeq
    apply Finset.sum_congr rfl
    intro d hd
    exact if_pos (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
  have hband := sieveSeq_horizon_band_sub hMN (horizonTruncate M c) k
  have hzero : (∑ d ∈ (Finset.Ioc M N).filter (fun d => d ∣ k),
      horizonTruncate M c d) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    exact if_neg (not_le.mpr (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).1)
  rw [hzero, hsmall] at hband
  exact sub_eq_zero.mp hband

private theorem physical_energies_horizon_truncate {M N : ℕ} (hMN : M ≤ N) (c : ℕ → ℝ) :
    sieveTotalPronicEnergy N (horizonTruncate M c) = sieveTotalPronicEnergy M c ∧
      fermiSelectedTotalPronicEnergy N (horizonTruncate M c) =
        fermiSelectedTotalPronicEnergy M c := by
  constructor
  · apply tsum_congr
    intro m
    simp only [sievePairedPronicEnergy, sieve_horizon_truncate hMN]
  · apply tsum_congr
    intro m
    simp only [fermiSelectedPronicEnergy, Finset.sum_singleton]
    rw [show 4 * m + 4 = 2 * (2 * m + 1) + 2 by omega]
    simp only [fermiBoundaryJump_odd, fermiBoundaryJump_even, sieve_horizon_truncate hMN]

private theorem physical_ratios_horizon_mono {M N : ℕ} (hMN : M ≤ N)
    (D : Set (ℕ → ℝ)) (hD : ∀ M c, c ∈ D → horizonTruncate M c ∈ D) :
    physicalRatios M D ⊆ physicalRatios N D := by
  rintro t ⟨c, hc, hQ, rfl⟩
  obtain ⟨hP, hQeq⟩ := physical_energies_horizon_truncate hMN c
  refine ⟨horizonTruncate M c, hD M c hc, ?_, ?_⟩
  · rwa [hQeq]
  · rw [hP, hQeq]

private theorem physical_ratios_nonempty {N : ℕ} (hN : 2 ≤ N)
    (D : Set (ℕ → ℝ)) (hD : ∀ M c, c ∈ D → horizonTruncate M c ∈ D)
    (hc : fermiDyadicCosineWeight 0 ∈ D) : (physicalRatios N D).Nonempty := by
  have h := cosine_ratio_mem 0 D hc
  exact ⟨_, physical_ratios_horizon_mono hN D hD h⟩

private theorem physical_constant_horizon_mono {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N)
    (D : Set (ℕ → ℝ)) (hD : ∀ M c, c ∈ D → horizonTruncate M c ∈ D)
    (hc : fermiDyadicCosineWeight 0 ∈ D) :
    physicalConstantOn M D ≤ physicalConstantOn N D :=
  csSup_le_csSup (physical_ratios_bddAbove N D) (physical_ratios_nonempty hM D hD hc)
    (physical_ratios_horizon_mono hMN D hD)

private theorem dyadic_depth_tendsto : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.2
  intro r
  exact eventually_atTop.2 ⟨2^r, fun N hN => Nat.le_log_of_pow_le (by decide) hN⟩

private theorem dyadic_depth_div_logb_tendsto :
    Tendsto (fun N : ℕ => (Nat.log 2 N : ℝ) / Real.logb 2 (N : ℝ)) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => 1 / Real.logb 2 (N : ℝ)) atTop (𝓝 0) := by
    exact (tendsto_inv_atTop_zero.comp hlog).congr (fun N => by
      change (Real.logb 2 (N : ℝ))⁻¹ = 1 / Real.logb 2 (N : ℝ)
      rw [one_div])
  have hlo : Tendsto (fun N : ℕ => 1 - 1 / Real.logb 2 (N : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hr : 0 < (Nat.log 2 N : ℝ) := by
      exact_mod_cast Nat.log_pos (by decide : 1 < 2) hN
    have hx : 0 < Real.logb 2 (N : ℝ) := hr.trans_le (Real.natLog_le_logb N 2)
    have hf : Real.logb 2 (N : ℝ) < (Nat.log 2 N : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one (Real.logb 2 (N : ℝ))
      have heq : ⌊Real.logb 2 (N : ℝ)⌋₊ = Nat.log 2 N := Real.natFloor_logb_natCast 2 N
      rw [heq] at h
      exact h
    apply (le_div_iff₀ hx).2
    calc
      (1 - 1 / Real.logb 2 (N : ℝ)) * Real.logb 2 (N : ℝ) =
          Real.logb 2 (N : ℝ) - 1 := by field_simp
      _ ≤ (Nat.log 2 N : ℝ) := by linarith
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hr : 0 < (Nat.log 2 N : ℝ) := by
      exact_mod_cast Nat.log_pos (by decide : 1 < 2) hN
    have hx : 0 < Real.logb 2 (N : ℝ) := hr.trans_le (Real.natLog_le_logb N 2)
    exact (div_le_iff₀ hx).2 (by simpa using Real.natLog_le_logb N 2)

private theorem dyadic_depth_succ_div_logb_tendsto :
    Tendsto (fun N : ℕ => ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.logb 2 (N : ℝ))
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => 1 / Real.logb 2 (N : ℝ)) atTop (𝓝 0) := by
    exact (tendsto_inv_atTop_zero.comp hlog).congr (fun N => by
      change (Real.logb 2 (N : ℝ))⁻¹ = 1 / Real.logb 2 (N : ℝ)
      rw [one_div])
  simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero] using
    dyadic_depth_div_logb_tendsto.add hinv

private theorem physical_constant_logb_limit (D : Set (ℕ → ℝ))
    (hD : ∀ M c, c ∈ D → horizonTruncate M c ∈ D)
    (hc : ∀ L, fermiDyadicCosineWeight L ∈ D) :
    Tendsto (fun N : ℕ => physicalConstantOn N D / (Real.logb 2 (N : ℝ))^2)
      atTop (𝓝 (4 / Real.pi^2)) := by
  have hd : Tendsto (fun r : ℕ => physicalConstantOn (2^r) D / (r : ℝ)^2)
      atTop (𝓝 (4 / Real.pi^2)) :=
    (tendsto_add_atTop_iff_nat 1).mp (physical_constant_scaled_dyadic_limit D hc)
  have hs : Tendsto (fun N : ℕ => Nat.log 2 N + 1) atTop atTop :=
    (show Tendsto (fun r : ℕ => r + 1) atTop atTop from
      (tendsto_add_atTop_iff_nat 1).2 tendsto_id).comp dyadic_depth_tendsto
  have hlo : Tendsto (fun N : ℕ =>
      physicalConstantOn (2^(Nat.log 2 N)) D / (Real.logb 2 (N : ℝ))^2)
      atTop (𝓝 (4 / Real.pi^2)) := by
    have ht := (hd.comp dyadic_depth_tendsto).mul (dyadic_depth_div_logb_tendsto.pow 2)
    simp only [one_pow, mul_one] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hr : (Nat.log 2 N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.log_pos (by decide : 1 < 2) hN).ne'
    dsimp
    field_simp
  have hhi : Tendsto (fun N : ℕ =>
      physicalConstantOn (2^(Nat.log 2 N + 1)) D / (Real.logb 2 (N : ℝ))^2)
      atTop (𝓝 (4 / Real.pi^2)) := by
    have ht := (hd.comp hs).mul (dyadic_depth_succ_div_logb_tendsto.pow 2)
    simp only [one_pow, mul_one] at ht
    apply ht.congr'
    filter_upwards with N
    have hr : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hr : 0 < Nat.log 2 N := Nat.log_pos (by decide) hN
    have hbase : 2 ≤ 2^(Nat.log 2 N) := by
      calc
        2 ≤ 2^(Nat.log 2 N - 1) * 2 := by
          have : 0 < (2 : ℕ)^(Nat.log 2 N - 1) := by positivity
          omega
        _ = 2^(Nat.log 2 N) := by
          rw [← pow_succ]
          congr 1
          omega
    exact div_le_div_of_nonneg_right
      (physical_constant_horizon_mono hbase (Nat.pow_log_le_self 2 (by omega)) D hD (hc 0))
      (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact div_le_div_of_nonneg_right
      (physical_constant_horizon_mono hN (Nat.lt_pow_succ_log_self (by decide : 1 < 2) N).le
        D hD (hc 0)) (sq_nonneg _)

/-- Sharp logarithmic conditioning of the complete selected Fermi trace at all horizons. -/
theorem fermiPhysicalInverseConstant_logb_limit :
    Tendsto (fun N : ℕ => fermiPhysicalInverseConstant N / (Real.logb 2 (N : ℝ))^2)
      atTop (𝓝 (4 / Real.pi^2)) :=
  physical_constant_logb_limit Set.univ (fun _ _ _ => Set.mem_univ _)
    (fun _ => Set.mem_univ _)

/-- Nonnegative coefficients have the same sharp all-horizon logarithmic conditioning. -/
theorem fermiNonnegativePhysicalInverseConstant_logb_limit :
    Tendsto (fun N : ℕ => fermiNonnegativePhysicalInverseConstant N / (Real.logb 2 (N : ℝ))^2)
      atTop (𝓝 (4 / Real.pi^2)) := by
  apply physical_constant_logb_limit {c | ∀ d : ℕ, 0 ≤ c d} ?_ fermiDyadicCosineWeight_nonneg
  intro M c hc d
  dsimp only [horizonTruncate]
  split_ifs
  · exact hc d
  · exact le_rfl

end GaloisForLFunctions.TransHorizonIncidenceMechanics
