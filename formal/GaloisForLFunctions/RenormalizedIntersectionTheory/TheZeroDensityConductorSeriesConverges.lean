import GaloisForLFunctions.RenormalizedIntersectionTheory.TheConductorSeriesConvergesBelowAQuarter

/-!
# Conductor convergence at zero prime density

A vanishing logarithmic prime density lies below every positive linear envelope,
after a finite constant. The subquarter conductor estimate therefore applies
without any prescribed rate of density convergence. The same prime estimate
shows that inverse finite Euler densities grow more slowly than every positive
power of the logarithmic cutoff.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Zero logarithmic density admits every positive linear majorant, with a constant
absorbing the finitely many initial horizons. -/
theorem exists_primeSetLogMass_le_small_log_add (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → primeSetLogMass P N ≤ κ * Real.log N + C := by
  have hA (N : ℕ) : 0 ≤ primeSetLogMass P N := by
    change 0 ≤ ∑ p ∈ primeSetCutoff P N, Real.log p / p
    exact sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hevent := (Metric.tendsto_nhds.mp hP) (κ / 2) (by positivity)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hevent
  let M := max M₀ 3
  let C := ∑ n ∈ range M, primeSetLogMass P n
  have hC : 0 ≤ C := sum_nonneg fun n _ => hA n
  refine ⟨C, hC, fun N _ => ?_⟩
  by_cases hMN : M ≤ N
  · have hN3 : 3 ≤ N := (le_max_right _ _).trans hMN
    have hlog : 1 ≤ Real.log N := one_le_log_of_three_le hN3
    have h := hM₀ N ((le_max_left _ _).trans hMN)
    rw [Real.dist_eq, sub_zero] at h
    have hratio : primeSetLogMass P N / (1 + Real.log N) ≤ κ / 2 :=
      (le_abs_self _).trans (le_of_lt h)
    have hbound := (div_le_iff₀ (show 0 < 1 + Real.log N by linarith only [hlog])).mp hratio
    have hprod := mul_nonneg hκ.le (show 0 ≤ Real.log N - 1 by linarith only [hlog])
    nlinarith only [hbound, hprod, hC]
  · have hsmall : primeSetLogMass P N ≤ C :=
      single_le_sum (fun n _ => hA n) (mem_range.mpr (lt_of_not_ge hMN))
    exact hsmall.trans (le_add_of_nonneg_left (mul_nonneg hκ.le (Real.log_natCast_nonneg N)))

/-- The conductor series of every zero-density prime flip converges throughout the
positive resolvent interval, even when its Euler harmonic density vanishes. -/
theorem summable_zeroDensity_conductorSeries (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {s : ℝ} (hs : 0 ≤ s) (hs2 : s < 2 * Real.log 2) :
    Summable fun k : ℕ => primeSetSpectralWeight P (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - Real.eulerMascheroniConstant - s) := by
  obtain ⟨C, _, hC⟩ := exists_primeSetLogMass_le_small_log_add P hP
    (show (0 : ℝ) < 1 / 8 by norm_num)
  apply summable_conductorSeries P (κ := 1 / 8) (C := C) (α := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ hs hs2
  intro N hN
  simpa only [Real.rpow_zero, mul_one] using hC N hN

/-- At zero logarithmic density the reciprocal prime sum lies below every positive
multiple of `log log Q`, up to a constant. -/
theorem exists_primeSet_reciprocal_sum_le_small_logLog (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Q : ℕ, 3 ≤ Q →
      (∑ p ∈ primeSetCutoff P Q, 1 / (p : ℝ)) ≤ η * Real.log (Real.log Q) + K := by
  let κ := η / Real.exp 1
  have hκ : 0 < κ := div_pos hη (Real.exp_pos _)
  obtain ⟨C, _, hC⟩ := exists_primeSetLogMass_le_small_log_add P hP hκ
  obtain ⟨K, hK, hweighted⟩ := exists_sum_primeSetCutoff_rpow_le P (κ := κ) (C := C) (α := 0)
    hκ.le (by norm_num) (by norm_num)
    (fun N hN => by simpa only [Real.rpow_zero, mul_one] using hC N hN)
  refine ⟨Real.exp 1 * K, mul_nonneg (Real.exp_pos _).le hK, fun Q hQ => ?_⟩
  have hlog1 : 1 ≤ Real.log Q := one_le_log_of_three_le hQ
  have hlog : 0 < Real.log Q := zero_lt_one.trans_le hlog1
  have hW := hweighted (1 / Real.log Q) (by positivity)
    ((div_le_one hlog).mpr hlog1) Q
  rw [one_div_one_div] at hW
  have hterm (p : ℕ) (hp : p ∈ primeSetCutoff P Q) :
      1 / (p : ℝ) ≤ Real.exp 1 * (p : ℝ) ^ (-(1 + 1 / Real.log Q)) := by
    obtain ⟨⟨hpQ, hpp⟩, _⟩ := mem_primeSetCutoff.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlogp := Real.log_le_log hp0 (show (p : ℝ) ≤ Q by exact_mod_cast hpQ)
    have hquot : Real.log p / Real.log Q ≤ 1 := (div_le_one hlog).mpr hlogp
    have hweight : 1 ≤ Real.exp 1 * Real.exp (-(Real.log p / Real.log Q)) := by
      rw [← Real.exp_add]
      have h := Real.exp_le_exp.mpr (show 0 ≤ 1 + -(Real.log p / Real.log Q) by
        linarith only [hquot])
      simpa only [Real.exp_zero] using h
    have hpow : (p : ℝ) ^ (-(1 + 1 / Real.log Q)) =
        (1 / p) * Real.exp (-(Real.log p / Real.log Q)) := by
      rw [show -(1 + 1 / Real.log Q) = -1 + -(1 / Real.log Q) by ring,
        Real.rpow_add hp0, Real.rpow_neg_one, Real.rpow_def_of_pos hp0,
        show Real.log p * -(1 / Real.log Q) = -(Real.log p / Real.log Q) by ring, one_div]
    calc
      1 / (p : ℝ) ≤ (1 / (p : ℝ)) *
          (Real.exp 1 * Real.exp (-(Real.log p / Real.log Q))) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hweight (by positivity : (0 : ℝ) ≤ 1 / p)
      _ = _ := by rw [hpow]; ring
  calc
    _ ≤ Real.exp 1 * ∑ p ∈ primeSetCutoff P Q, (p : ℝ) ^ (-(1 + 1 / Real.log Q)) := by
      rw [mul_sum]
      exact sum_le_sum hterm
    _ ≤ Real.exp 1 * (κ * Real.log (Real.log Q) + K) :=
      mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le
    _ = _ := by dsimp only [κ]; field_simp [(Real.exp_pos 1).ne']

private theorem inv_sq_finiteFlipDensity_le_exp (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    1 / finiteFlipHarmonicDensity F ^ (2 : ℕ) ≤
      Real.exp (8 * ∑ p ∈ F, 1 / (p : ℝ)) := by
  have hfactor (p : ℕ) (hp : p ∈ F) :
      1 ≤ (((p : ℝ) - 1) / ((p : ℝ) + 1)) * Real.exp (4 * (1 / (p : ℝ))) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hF p hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith only [hp2]
    have hpm : 0 < (p : ℝ) - 1 := by linarith only [hp2]
    have hpp : 0 < (p : ℝ) + 1 := by linarith only [hp2]
    have hsmall : 2 / ((p : ℝ) - 1) ≤ 4 / (p : ℝ) := by
      rw [div_le_div_iff₀ hpm hp0]
      linarith only [hp2]
    have hratio : ((p : ℝ) + 1) / ((p : ℝ) - 1) = 1 + 2 / ((p : ℝ) - 1) := by
      field_simp [hpm.ne']; ring
    have he : ((p : ℝ) + 1) / ((p : ℝ) - 1) ≤ Real.exp (4 / (p : ℝ)) := by
      rw [hratio]
      have h := Real.add_one_le_exp (4 / (p : ℝ))
      linarith only [hsmall, h]
    have hmul := mul_le_mul_of_nonneg_left he (div_nonneg hpm.le hpp.le)
    have hcancel : (((p : ℝ) - 1) / ((p : ℝ) + 1)) *
        (((p : ℝ) + 1) / ((p : ℝ) - 1)) = 1 := by field_simp [hpm.ne', hpp.ne']
    rw [hcancel] at hmul
    simpa only [div_eq_mul_inv, one_mul] using hmul
  have hprod := prod_le_prod (fun p (_ : p ∈ F) => (zero_le_one : (0 : ℝ) ≤ 1)) hfactor
  simp only [prod_const_one] at hprod
  rw [prod_mul_distrib, ← Real.exp_sum, ← mul_sum] at hprod
  change 1 ≤ finiteFlipHarmonicDensity F * Real.exp (4 * ∑ p ∈ F, 1 / (p : ℝ)) at hprod
  have hraw := mul_le_mul hprod hprod zero_le_one (zero_le_one.trans hprod)
  have hsquare : 1 ≤ finiteFlipHarmonicDensity F ^ (2 : ℕ) *
      Real.exp (4 * ∑ p ∈ F, 1 / (p : ℝ)) ^ (2 : ℕ) := by nlinarith only [hraw]
  rw [← Real.exp_nat_mul,
    show ((2 : ℕ) : ℝ) * (4 * ∑ p ∈ F, 1 / (p : ℝ)) = 8 * ∑ p ∈ F, 1 / (p : ℝ) by ring] at hsquare
  exact (div_le_iff₀ (pow_pos (finiteFlipHarmonicDensity_pos hF) 2)).mpr
    (by simpa only [mul_comm] using hsquare)

/-- The inverse square finite Euler density grows more slowly than every positive
power of the logarithmic cutoff at zero prime density. -/
theorem exists_inv_sq_flipDensityBelow_le_rpow_log (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 3 ≤ Q →
      1 / flipDensityBelow (primeSetFlip P) Q ^ (2 : ℕ) ≤ C * Real.log Q ^ ε := by
  obtain ⟨K, _, hK⟩ := exists_primeSet_reciprocal_sum_le_small_logLog P hP
    (show 0 < ε / 8 by positivity)
  refine ⟨Real.exp (8 * K), Real.exp_pos _, fun Q hQ => ?_⟩
  have hsub : primeSetCutoff P (Q - 1) ⊆ primeSetCutoff P Q := by
    intro p hp
    obtain ⟨⟨hpQ, hpp⟩, hpP⟩ := mem_primeSetCutoff.mp hp
    exact mem_primeSetCutoff.mpr ⟨⟨hpQ.trans (Nat.sub_le Q 1), hpp⟩, hpP⟩
  have hsum : (∑ p ∈ primeSetCutoff P (Q - 1), 1 / (p : ℝ)) ≤
      ∑ p ∈ primeSetCutoff P Q, 1 / (p : ℝ) := sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
  have hmass : (∑ p ∈ primeSetCutoff P (Q - 1), 1 / (p : ℝ)) ≤
      (ε / 8) * Real.log (Real.log Q) + K := hsum.trans (hK Q hQ)
  have hlog : 0 < Real.log Q := zero_lt_one.trans_le (one_le_log_of_three_le hQ)
  rw [flipDensityBelow_eq P (by omega)]
  calc
    _ ≤ Real.exp (8 * ∑ p ∈ primeSetCutoff P (Q - 1), 1 / (p : ℝ)) :=
      inv_sq_finiteFlipDensity_le_exp _ (primeSetCutoff_prime' P _)
    _ ≤ Real.exp (8 * ((ε / 8) * Real.log (Real.log Q) + K)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmass (by norm_num))
    _ = _ := by
      rw [Real.rpow_def_of_pos hlog, ← Real.exp_add]
      congr 1
      ring

end GaloisForLFunctions.RenormalizedIntersectionTheory

