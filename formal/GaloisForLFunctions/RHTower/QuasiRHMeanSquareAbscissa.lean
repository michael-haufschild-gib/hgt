import GaloisForLFunctions.RHTower.QuasiRHDilationTailHyperbolaAndOutgoingPotentialAbscissaLaw

/-!
# Cumulative mean-square exponents and the zero abscissa

A prefix square bound supplies small samples in every power-length window. The existing
one-sided power-gap bootstrap therefore recovers the sharp exponent `Θ ≤ r / 2`.
Together with the unconditional growth bound at `Θ`, this identifies the infimum of
cumulative square exponents with `2 * Θ`. Numerical bounds for the target strips are
separate arithmetic obligations.
-/

open Real Filter Topology Finset
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.RHTower

/-- Cumulative squares supply a small sample in every sufficiently large power window. -/
theorem exists_powerGap_samples_of_sum_sq_le_rpow {f : ℕ → ℝ} {C r θ : ℝ}
    (hC : 0 ≤ C) (hr : 1 ≤ r) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hprefix : ∀ n : ℕ, 2 ≤ n → ∑ k ∈ Icc 2 n, (f k) ^ 2 ≤ C * (n : ℝ) ^ r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ k : ℕ,
      2 ≤ k ∧ k ≤ n ∧ (n : ℝ) - k ≤ (n : ℝ) ^ θ ∧
        |f k| ≤ D * (k : ℝ) ^ ((r - θ) / 2) := by
  classical
  let c := (r - θ) / 2
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 - θ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (hlim.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  refine ⟨(C + 1) * (2 : ℝ) ^ c, by positivity, max N₂ 4, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hhalf : (n : ℝ) ^ θ ≤ n / 2 := by
    have hsmall := hN₂ n ((le_max_left _ _).trans hn)
    have hsplit : (n : ℝ) ^ θ = (n : ℝ) ^ (-(1 - θ)) * n := by
      calc
        _ = (n : ℝ) ^ (-(1 - θ) + 1) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hn0, Real.rpow_one]
    rw [hsplit]
    nlinarith
  let d : ℕ := ⌊(n : ℝ) ^ θ⌋₊
  have hd : (d : ℝ) ≤ (n : ℝ) ^ θ := Nat.floor_le (by positivity)
  have hdhalf : (d : ℝ) ≤ n / 2 := hd.trans hhalf
  have hdn : d ≤ n := by exact_mod_cast (show (d : ℝ) ≤ n by linarith)
  have hlb : 2 ≤ n - d := by
    have : (2 : ℝ) ≤ (n - d : ℕ) := by rw [Nat.cast_sub hdn]; linarith
    exact_mod_cast this
  let J := Icc (n - d) n
  have hJ : J.Nonempty := ⟨n, by simp [J]⟩
  have hsubset : J ⊆ Icc 2 n := by
    intro k hk
    have hk' := mem_Icc.mp hk
    exact mem_Icc.mpr ⟨hlb.trans hk'.1, hk'.2⟩
  have hcard : J.card = d + 1 := by
    dsimp [J]
    rw [Nat.card_Icc]
    omega
  have hsize : (n : ℝ) ^ θ ≤ (J.card : ℝ) := by
    rw [hcard]
    simpa only [d, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((n : ℝ) ^ θ)).le
  have hsum : ∑ k ∈ J, (f k) ^ 2 ≤
      ∑ _k ∈ J, (C + 1) ^ 2 * (n : ℝ) ^ (r - θ) := by
    calc
      _ ≤ ∑ k ∈ Icc 2 n, (f k) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsubset (by intros; positivity)
      _ ≤ C * (n : ℝ) ^ r := hprefix n (by omega)
      _ ≤ (C + 1) ^ 2 * (n : ℝ) ^ r :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = (n : ℝ) ^ θ * ((C + 1) ^ 2 * (n : ℝ) ^ (r - θ)) := by
        rw [← mul_assoc, mul_comm ((n : ℝ) ^ θ), mul_assoc, ← Real.rpow_add hn0]
        congr 2
        ring
      _ ≤ (J.card : ℝ) * ((C + 1) ^ 2 * (n : ℝ) ^ (r - θ)) :=
        mul_le_mul_of_nonneg_right hsize (by positivity)
      _ = _ := by simp
  obtain ⟨k, hkJ, hkf⟩ := exists_le_of_sum_le hJ hsum
  have hk := mem_Icc.mp hkJ
  have hklb : ((n - d : ℕ) : ℝ) ≤ k := by exact_mod_cast hk.1
  rw [Nat.cast_sub hdn] at hklb
  have hnk : (n : ℝ) ≤ 2 * k := by linarith
  have hpow : ((n : ℝ) ^ c) ^ 2 = (n : ℝ) ^ (r - θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    dsimp [c]
    ring
  have habs : |f k| ≤ (C + 1) * (n : ℝ) ^ c := by
    have hright : 0 ≤ (C + 1) * (n : ℝ) ^ c := by positivity
    apply (sq_le_sq₀ (abs_nonneg _) hright).mp
    simpa only [sq_abs, mul_pow, hpow] using hkf
  refine ⟨k, hlb.trans hk.1, hk.2, by linarith, ?_⟩
  calc
    |f k| ≤ (C + 1) * (n : ℝ) ^ c := habs
    _ ≤ (C + 1) * (2 * (k : ℝ)) ^ c :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn0.le hnk hc) (by linarith)
    _ = (C + 1) * (2 : ℝ) ^ c * (k : ℝ) ^ c := by
      rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg k)]
      ring

/-- Summing a nonnegative power envelope preserves its expected cumulative exponent. -/
theorem sum_sq_le_rpow_of_abs_le_rpow {f : ℕ → ℝ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hf : ∀ k : ℕ, 2 ≤ k → |f k| ≤ C * (k : ℝ) ^ c)
    {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Icc 2 N, (f k) ^ 2 ≤ C ^ 2 * (N : ℝ) ^ (2 * c + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hterm : ∀ k ∈ Icc 2 N, (f k) ^ 2 ≤ C ^ 2 * (N : ℝ) ^ (2 * c) := by
    intro k hk
    have hk' := mem_Icc.mp hk
    have hp : (k : ℝ) ^ c ≤ (N : ℝ) ^ c :=
      Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast hk'.2) hc
    have habs := (hf k hk'.1).trans (mul_le_mul_of_nonneg_left hp hC)
    have hs := (sq_le_sq₀ (abs_nonneg (f k)) (by positivity : 0 ≤ C * (N : ℝ) ^ c)).mpr habs
    simpa only [sq_abs, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
      Nat.cast_ofNat, mul_comm c 2] using hs
  calc
    _ ≤ ∑ _k ∈ Icc 2 N, C ^ 2 * (N : ℝ) ^ (2 * c) := sum_le_sum hterm
    _ ≤ (N : ℝ) * (C ^ 2 * (N : ℝ) ^ (2 * c)) := by
      rw [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show (Icc 2 N).card ≤ N by rw [Nat.card_Icc]; omega)
    _ = _ := by rw [Real.rpow_add hN0, Real.rpow_one]; ring

/-- Literal cumulative energy of the normalized Möbius-divisor Abel source. -/
noncomputable def mobiusDivisorAbelMeanSquareEnergy (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 N, (mobiusDivisorSquareRootAbelMoment k / k) ^ 2

/-- Prefix averaging and power-gap transport recover the full half-power saving. -/
theorem zetaZeroAbscissa_le_half_of_mobiusDivisorAbelMeanSquareEnergy_le_rpow
    {C r : ℝ} (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hE : ∀ N : ℕ, 2 ≤ N → mobiusDivisorAbelMeanSquareEnergy N ≤ C * (N : ℝ) ^ r) :
    zetaZeroAbscissa ≤ r / 2 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let δ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  let θ := 1 - δ
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  obtain ⟨D, hD, N₀, hsamples⟩ := exists_powerGap_samples_of_sum_sq_le_rpow
    hC hr hθ hθ1 hE
  let c := (r - θ) / 2
  have hc : 0 ≤ c := by dsimp [c]; linarith
  let A : Set ℕ := {k | 2 ≤ k ∧
    |mobiusDivisorSquareRootAbelMoment k / k| ≤ D * (k : ℝ) ^ c}
  have hstrip := zetaZeroAbscissa_le_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    (A := A) (c := c) (K := 1) (N₀ := N₀) hD hδ (by norm_num)
    (fun k hk _ => (le_abs_self _).trans (hk.2.trans (by linarith)))
    (fun n hn => by
      obtain ⟨k, hk2, hkn, hgap, hkbound⟩ := hsamples n hn
      exact ⟨k, ⟨hk2, hkbound⟩, hkn, by simpa only [one_mul] using hgap⟩)
  rw [max_eq_right hc] at hstrip
  dsimp [c, θ] at hstrip
  linarith

/-- Unconditional cumulative upper growth at every exponent above `2 * Θ`. -/
theorem exists_mobiusDivisorAbelMeanSquareEnergy_le_rpow_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      mobiusDivisorAbelMeanSquareEnergy N ≤ C * (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa (ε / 2) (by positivity)
  refine ⟨C ^ 2, sq_nonneg _, fun N hN => ?_⟩
  have h := sum_sq_le_rpow_of_abs_le_rpow hC
    (by linarith [half_le_zetaZeroAbscissa] : 0 ≤ zetaZeroAbscissa - 1 / 2 + ε / 2) hbound hN
  simpa only [mobiusDivisorAbelMeanSquareEnergy,
    show 2 * (zetaZeroAbscissa - 1 / 2 + ε / 2) + 1 = 2 * zetaZeroAbscissa + ε by ring] using h

/-- The exact cumulative Abel-energy exponent is twice the actual zero abscissa. -/
theorem two_mul_zetaZeroAbscissa_eq_sInf_mobiusDivisorAbelMeanSquareEnergy_exponents :
    2 * zetaZeroAbscissa = sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 2 ≤ N → mobiusDivisorAbelMeanSquareEnergy N ≤ C * (N : ℝ) ^ r} := by
  let S : Set ℝ := {r | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 2 ≤ N → mobiusDivisorAbelMeanSquareEnergy N ≤ C * (N : ℝ) ^ r}
  have hmem : ∀ ε : ℝ, 0 < ε → 2 * zetaZeroAbscissa + ε ∈ S := by
    intro ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa],
      exists_mobiusDivisorAbelMeanSquareEnergy_le_rpow_zetaZeroAbscissa ε hε⟩
  have hne : S.Nonempty := ⟨2 * zetaZeroAbscissa + 1, hmem 1 (by norm_num)⟩
  have hbdd : BddBelow S := ⟨1, fun _ hr => hr.1⟩
  change 2 * zetaZeroAbscissa = sInf S
  apply le_antisymm
  · refine le_csInf hne fun r hr => ?_
    obtain ⟨hr, C, hC, hE⟩ := hr
    have := zetaZeroAbscissa_le_half_of_mobiusDivisorAbelMeanSquareEnergy_le_rpow hC hr hE
    linarith
  · exact le_of_forall_pos_le_add fun ε hε => csInf_le hbdd (hmem ε hε)

private theorem sum_sq_le_two_sum_sq_add_const {f g : ℕ → ℝ} {D : ℝ}
    (hD : 0 ≤ D) (hfg : ∀ k : ℕ, 2 ≤ k → |f k - g k| ≤ D)
    {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Icc 2 N, (f k) ^ 2 ≤ 2 * ∑ k ∈ Icc 2 N, (g k) ^ 2 + 2 * D ^ 2 * N := by
  have hterm : ∀ k ∈ Icc 2 N, (f k) ^ 2 ≤ 2 * (g k) ^ 2 + 2 * D ^ 2 := by
    intro k hk
    have hs := (sq_le_sq₀ (abs_nonneg (f k - g k)) hD).mpr (hfg k (mem_Icc.mp hk).1)
    rw [sq_abs] at hs
    nlinarith [sq_nonneg (f k - 2 * g k)]
  calc
    _ ≤ ∑ k ∈ Icc 2 N, (2 * (g k) ^ 2 + 2 * D ^ 2) := sum_le_sum hterm
    _ = 2 * ∑ k ∈ Icc 2 N, (g k) ^ 2 + ((Icc 2 N).card : ℝ) * (2 * D ^ 2) := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have hcard : ((Icc 2 N).card : ℝ) ≤ N := by
        exact_mod_cast (show (Icc 2 N).card ≤ N by rw [Nat.card_Icc]; omega)
      nlinarith [sq_nonneg D]

/-- The completed Suzuki source differs from the normalized literal Abel source by a constant. -/
theorem exists_abs_mobiusDivisorAbel_sub_completedSource_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 2 ≤ N →
      |mobiusDivisorSquareRootAbelMoment N / N - suzukiTransitionCoreCompletedAbelSource N| ≤ D := by
  refine ⟨2 * |Real.eulerMascheroniConstant| + 1 +
    |unitRieszSuzukiPolarUniformBound| + |unitRieszSuzukiArchUniformBound|, by positivity,
    fun N hN => ?_⟩
  have hU := abs_mobiusDivisorSquareRootAbel_div_sub_completedOutgoingCharge_le hN
  have hG := abs_suzukiCompletedLowerHardyAmplitude_sub_half_resolvent_le hN
  rw [suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource hN,
    ← unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN, abs_sub_comm] at hG
  have htriangle := abs_sub_le (mobiusDivisorSquareRootAbelMoment N / N)
    (unitRieszCoherentCompletedOutgoingCharge N) (suzukiTransitionCoreCompletedAbelSource N)
  linarith [le_abs_self unitRieszSuzukiPolarUniformBound,
    le_abs_self unitRieszSuzukiArchUniformBound]

/-- Cumulative square energy of the completed arithmetic source. -/
noncomputable def suzukiCompletedAbelMeanSquareEnergy (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 N, (suzukiTransitionCoreCompletedAbelSource k) ^ 2

/-- Local formation production controls the entire square prefix, including its initial value. -/
theorem suzukiCompletedAbelMeanSquareEnergy_formationEnergy_comparison {N : ℕ} (hN : 2 ≤ N) :
    suzukiCompletedAbelMeanSquareEnergy N ≤ (suzukiTransitionCoreCompletedAbelSource 2) ^ 2 +
      2 * (suzukiCompletedFormationEnergy N - suzukiCompletedFormationEnergy 2) ∧
    suzukiCompletedFormationEnergy N - suzukiCompletedFormationEnergy 2 ≤
      suzukiCompletedAbelMeanSquareEnergy N := by
  induction N, hN using Nat.le_induction with
  | base => simp [suzukiCompletedAbelMeanSquareEnergy, sq_nonneg]
  | succ N hN ih =>
    have hsum : suzukiCompletedAbelMeanSquareEnergy (N + 1) =
        suzukiCompletedAbelMeanSquareEnergy N + (suzukiTransitionCoreCompletedAbelSource (N + 1)) ^ 2 := by
      unfold suzukiCompletedAbelMeanSquareEnergy
      rw [sum_Icc_succ_top (by omega)]
    have hlocal := suzukiCompletedFormationEnergy_succ_sub_sandwich hN
    rw [suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource (by omega)] at hlocal
    rw [hsum]
    constructor <;> linarith [ih.1, ih.2, hlocal.1, hlocal.2]

/-- Sharp cumulative formation-energy receiver; no individual production bound is assumed. -/
theorem zetaZeroAbscissa_le_half_of_suzukiCompletedFormationEnergy_le_rpow
    {B r : ℝ} (hB : 0 ≤ B) (hr : 1 ≤ r)
    (hF : ∀ N : ℕ, 2 ≤ N → suzukiCompletedFormationEnergy N ≤ B * (N : ℝ) ^ r) :
    zetaZeroAbscissa ≤ r / 2 := by
  obtain ⟨D, hD, hdiff⟩ := exists_abs_mobiusDivisorAbel_sub_completedSource_le
  let K := 2 * (suzukiTransitionCoreCompletedAbelSource 2) ^ 2 +
    4 * |suzukiCompletedFormationEnergy 2|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply zetaZeroAbscissa_le_half_of_mobiusDivisorAbelMeanSquareEnergy_le_rpow
    (C := 4 * B + K + 2 * D ^ 2) (by positivity) hr
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hp1 : 1 ≤ (N : ℝ) ^ r := Real.one_le_rpow hN1 (by linarith)
  have hpN : (N : ℝ) ≤ (N : ℝ) ^ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 hr
  have hcompare : mobiusDivisorAbelMeanSquareEnergy N ≤
      4 * suzukiCompletedFormationEnergy N + K + 2 * D ^ 2 * N := by
    have hsum := sum_sq_le_two_sum_sq_add_const hD hdiff hN
    have hformation := (suzukiCompletedAbelMeanSquareEnergy_formationEnergy_comparison hN).1
    change mobiusDivisorAbelMeanSquareEnergy N ≤
      2 * suzukiCompletedAbelMeanSquareEnergy N + 2 * D ^ 2 * N at hsum
    dsimp [K]
    linarith [neg_le_abs (suzukiCompletedFormationEnergy 2)]
  calc
    _ ≤ 4 * suzukiCompletedFormationEnergy N + K + 2 * D ^ 2 * N := hcompare
    _ ≤ 4 * (B * (N : ℝ) ^ r) + K * (N : ℝ) ^ r + 2 * D ^ 2 * (N : ℝ) ^ r := by
      gcongr
      · exact hF N hN
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hp1 hK
    _ = _ := by ring

/-- Completed formation energy has every cumulative exponent strictly above `2 * Θ`. -/
theorem exists_suzukiCompletedFormationEnergy_le_rpow_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 2 ≤ N →
      suzukiCompletedFormationEnergy N ≤ B * (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_suzukiCompletedLowerHardyAmplitude_subpower_zetaZeroAbscissa (ε / 2) (by positivity)
  have hG : ∀ N : ℕ, 2 ≤ N → |suzukiTransitionCoreCompletedAbelSource N| ≤
      C * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / 2) := by
    intro N hN
    rw [← suzukiNaturalApertureCompletedLowerHardyAmplitude_eq_completedAbelSource hN]
    exact hbound N hN
  refine ⟨|suzukiCompletedFormationEnergy 2| + C ^ 2, by positivity, fun N hN => ?_⟩
  have hQ : suzukiCompletedAbelMeanSquareEnergy N ≤
      C ^ 2 * (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) := by
    have h := sum_sq_le_rpow_of_abs_le_rpow hC
      (by linarith [half_le_zetaZeroAbscissa] : 0 ≤ zetaZeroAbscissa - 1 / 2 + ε / 2) hG hN
    simpa only [suzukiCompletedAbelMeanSquareEnergy,
      show 2 * (zetaZeroAbscissa - 1 / 2 + ε / 2) + 1 = 2 * zetaZeroAbscissa + ε by ring] using h
  have hp : 1 ≤ (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N))
      (by linarith [half_le_zetaZeroAbscissa])
  have hconstant := mul_le_mul_of_nonneg_left hp (abs_nonneg (suzukiCompletedFormationEnergy 2))
  have hformation := (suzukiCompletedAbelMeanSquareEnergy_formationEnergy_comparison hN).2
  nlinarith [le_abs_self (suzukiCompletedFormationEnergy 2)]

/-- Exact exponent law for cumulative formation energy, including the endpoint infimum. -/
theorem two_mul_zetaZeroAbscissa_eq_sInf_suzukiCompletedFormationEnergy_exponents :
    2 * zetaZeroAbscissa = sInf {r : ℝ | 1 ≤ r ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ N : ℕ, 2 ≤ N → suzukiCompletedFormationEnergy N ≤ B * (N : ℝ) ^ r} := by
  let S : Set ℝ := {r | 1 ≤ r ∧ ∃ B : ℝ, 0 ≤ B ∧
    ∀ N : ℕ, 2 ≤ N → suzukiCompletedFormationEnergy N ≤ B * (N : ℝ) ^ r}
  have hmem : ∀ ε : ℝ, 0 < ε → 2 * zetaZeroAbscissa + ε ∈ S := by
    intro ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa],
      exists_suzukiCompletedFormationEnergy_le_rpow_zetaZeroAbscissa ε hε⟩
  have hne : S.Nonempty := ⟨2 * zetaZeroAbscissa + 1, hmem 1 (by norm_num)⟩
  have hbdd : BddBelow S := ⟨1, fun _ hr => hr.1⟩
  change 2 * zetaZeroAbscissa = sInf S
  apply le_antisymm
  · refine le_csInf hne fun r hr => ?_
    obtain ⟨hr, B, hB, hF⟩ := hr
    have := zetaZeroAbscissa_le_half_of_suzukiCompletedFormationEnergy_le_rpow hB hr hF
    linarith
  · exact le_of_forall_pos_le_add fun ε hε => csInf_le hbdd (hmem ε hε)

/-- Endpoint strip criterion for cumulative formation energy, with every positive epsilon. -/
theorem zetaZeroAbscissa_le_iff_suzukiCompletedFormationEnergy_subpower
    {b : ℝ} (hb : 1 / 2 ≤ b) :
    zetaZeroAbscissa ≤ b ↔ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ N : ℕ, 2 ≤ N → suzukiCompletedFormationEnergy N ≤ B * (N : ℝ) ^ (2 * b + ε) := by
  constructor
  · intro hstrip ε hε
    obtain ⟨B, hB, hbound⟩ := exists_suzukiCompletedFormationEnergy_le_rpow_zetaZeroAbscissa ε hε
    refine ⟨B, hB, fun N hN => (hbound N hN).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) (by linarith)) hB
  · intro hF
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨B, hB, hbound⟩ := hF (2 * ε) (by positivity)
    have := zetaZeroAbscissa_le_half_of_suzukiCompletedFormationEnergy_le_rpow
      hB (by linarith : 1 ≤ 2 * b + 2 * ε) hbound
    linarith

/-- Unconditional cumulative cost of the dilation head at a power cutoff. -/
theorem sum_sq_mobiusDivisorDilationHead_natFloor_rpow_div_le
    {φ : ℝ} (hφ : 1 / 2 ≤ φ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ Icc 2 N, (mobiusDivisorDilationHead k ⌊(k : ℝ) ^ φ⌋₊ / k) ^ 2 ≤
      (9 / 25 : ℝ) * (N : ℝ) ^ (2 * φ) := by
  have h := sum_sq_le_rpow_of_abs_le_rpow (by norm_num : (0 : ℝ) ≤ 3 / 5)
    (sub_nonneg.mpr hφ)
    (fun k (hk : 2 ≤ k) => abs_mobiusDivisorDilationHead_natFloor_rpow_div_le (by omega : 1 ≤ k) φ) hN
  simpa only [show 2 * (φ - 1 / 2) + 1 = 2 * φ by ring,
    show (3 / 5 : ℝ) ^ 2 = 9 / 25 by norm_num] using h

/-- Cumulative energy of the actual high-dilation tail. -/
noncomputable def mobiusDivisorDilationTailMeanSquareEnergy (φ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 N, (mobiusDivisorDilationTail k ⌊(k : ℝ) ^ φ⌋₊ / k) ^ 2

/-- Removing the paid dilation head changes mean-square growth only by its explicit budget. -/
theorem mobiusDivisorDilationTailMeanSquareEnergy_comparison
    {φ : ℝ} (hφ : 1 / 2 ≤ φ) {N : ℕ} (hN : 2 ≤ N) :
    mobiusDivisorAbelMeanSquareEnergy N ≤ 2 * mobiusDivisorDilationTailMeanSquareEnergy φ N +
      (18 / 25 : ℝ) * (N : ℝ) ^ (2 * φ) ∧
    mobiusDivisorDilationTailMeanSquareEnergy φ N ≤ 2 * mobiusDivisorAbelMeanSquareEnergy N +
      (18 / 25 : ℝ) * (N : ℝ) ^ (2 * φ) := by
  have hpoint (k : ℕ) :
      (mobiusDivisorSquareRootAbelMoment k / k) ^ 2 ≤
        2 * (mobiusDivisorDilationTail k ⌊(k : ℝ) ^ φ⌋₊ / k) ^ 2 +
        2 * (mobiusDivisorDilationHead k ⌊(k : ℝ) ^ φ⌋₊ / k) ^ 2 ∧
      (mobiusDivisorDilationTail k ⌊(k : ℝ) ^ φ⌋₊ / k) ^ 2 ≤
        2 * (mobiusDivisorSquareRootAbelMoment k / k) ^ 2 +
        2 * (mobiusDivisorDilationHead k ⌊(k : ℝ) ^ φ⌋₊ / k) ^ 2 := by
    have hid : mobiusDivisorSquareRootAbelMoment k / k =
        mobiusDivisorDilationHead k ⌊(k : ℝ) ^ φ⌋₊ / k +
        mobiusDivisorDilationTail k ⌊(k : ℝ) ^ φ⌋₊ / k := by
      rw [mobiusDivisorSquareRootAbelMoment_eq_dilationHead_add_dilationTail, add_div]
    rw [hid]
    constructor <;> nlinarith [sq_nonneg
      (mobiusDivisorDilationHead k ⌊(k : ℝ) ^ φ⌋₊ / k -
        mobiusDivisorDilationTail k ⌊(k : ℝ) ^ φ⌋₊ / k),
      sq_nonneg (2 * (mobiusDivisorDilationHead k ⌊(k : ℝ) ^ φ⌋₊ / k) +
        mobiusDivisorDilationTail k ⌊(k : ℝ) ^ φ⌋₊ / k)]
  have hhead := sum_sq_mobiusDivisorDilationHead_natFloor_rpow_div_le hφ hN
  have hU := sum_le_sum (s := Icc 2 N) (fun k _ => (hpoint k).1)
  have hT := sum_le_sum (s := Icc 2 N) (fun k _ => (hpoint k).2)
  simp only [sum_add_distrib, ← mul_sum] at hU hT
  change mobiusDivisorAbelMeanSquareEnergy N ≤
    2 * mobiusDivisorDilationTailMeanSquareEnergy φ N + _ at hU
  change mobiusDivisorDilationTailMeanSquareEnergy φ N ≤
    2 * mobiusDivisorAbelMeanSquareEnergy N + _ at hT
  constructor <;> linarith

end RHTower
