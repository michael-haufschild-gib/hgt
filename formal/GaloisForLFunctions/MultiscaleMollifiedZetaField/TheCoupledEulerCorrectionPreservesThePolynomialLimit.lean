import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCoupledPolynomialRowsConverge
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedCorrectionHasASummablePairMajorant

/-!
# The coupled Euler correction preserves the polynomial limit

The harmonic row has a bound independent of its retained dilation pair.
The absolute correction fibres give a summable pair majorant. Dominated
convergence then multiplies the common row limit by the correction's
unit mass, also for a varying normalized shift.
-/

open Filter Set Topology
open RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem harmonicMass_le_full {c N : ℕ} (hN : 1 < N) :
    normalizedHarmonicLogMoment 0 c N ≤ normalizedHarmonicLogMoment 0 1 N := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  simp only [normalizedHarmonicLogMoment, pow_zero, Nat.div_one]
  apply div_le_div_of_nonneg_right _ hlog.le
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (Nat.div_le_self _ _)⟩
  · intro d _ _
    positivity

private theorem harmonicProduct_abs_le (k : ℕ) {P Q : ℝ → ℝ} {N a b : ℕ}
    (hN : 1 < N) (ha : 0 < a) (hb : 0 < b) {v B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hP : ∀ u ∈ Icc (0 : ℝ) 1, |normalizedShiftedMobiusProfile P (Real.log N) u v| ≤ B)
    (hQ : ∀ u ∈ Icc (0 : ℝ) 1, |normalizedShiftedMobiusProfile Q (Real.log N) u v| ≤ D) :
    |normalizedHarmonicArray (max a b) N (fun d =>
      (Real.log d / Real.log N) ^ k *
        (normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) v *
          normalizedShiftedMobiusProfile Q (Real.log N) (dilatedLogProfileCoordinate b N d) v))| ≤
      B * D * normalizedHarmonicLogMoment 0 1 N := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  rw [normalizedHarmonicArray, abs_div, abs_of_pos hlog]
  calc
    _ ≤ (∑ d ∈ Finset.Icc 1 (N / max a b),
        |((Real.log d / Real.log N) ^ k *
          (normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) v *
            normalizedShiftedMobiusProfile Q (Real.log N) (dilatedLogProfileCoordinate b N d) v)) / (d : ℝ)|) / Real.log N :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hlog.le
    _ ≤ (∑ d ∈ Finset.Icc 1 (N / max a b), (B * D) / (d : ℝ)) / Real.log N := by
      apply div_le_div_of_nonneg_right _ hlog.le
      apply Finset.sum_le_sum
      intro d hd
      have ht := harmonicLogCoordinate_mem_unit hN hd
      have hprod : |normalizedShiftedMobiusProfile P (Real.log N) (dilatedLogProfileCoordinate a N d) v *
          normalizedShiftedMobiusProfile Q (Real.log N) (dilatedLogProfileCoordinate b N d) v| ≤ B * D := by
        rw [abs_mul]
        exact mul_le_mul (hP _ (dilatedLogProfileCoordinate_mem_unit ha (le_max_left _ _) hN hd))
          (hQ _ (dilatedLogProfileCoordinate_mem_unit hb (le_max_right _ _) hN hd))
          (abs_nonneg _) hB
      rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg ht.1 k),
        abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ht.1 ht.2) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hprod)
    _ = B * D * normalizedHarmonicLogMoment 0 (max a b) N := by
      simp only [normalizedHarmonicLogMoment, pow_zero, mul_one_div, Finset.mul_sum, mul_div_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonicMass_le_full hN) (mul_nonneg hB hD)

/-- The coupled row is bounded uniformly over every retained dilation pair. -/
theorem abs_shiftedProfileHarmonicRow_coupled_le (k : ℕ)
    {P Q : ℝ → ℝ} {N a b : ℕ} (hN : 1 < N) (ha : 0 < a) (hb : 0 < b)
    (haN : a ≤ N) (hbN : b ≤ N) {v V B D : ℝ} (hV : 0 ≤ V) (hv : v ∈ Icc (-V) V)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hP : ∀ u ∈ Icc (0 : ℝ) 1, |normalizedShiftedMobiusProfile P (Real.log N) u v| ≤ B)
    (hQ : ∀ u ∈ Icc (0 : ℝ) 1, |normalizedShiftedMobiusProfile Q (Real.log N) u v| ≤ D) :
    |shiftedProfileHarmonicRow P Q N a b (-2 * v) v k| ≤
      Real.exp (2 * V) * (B * D * normalizedHarmonicLogMoment 0 1 N) := by
  have hal := harmonicLogCoordinate_mem_unit hN
    (show a ∈ Finset.Icc 1 (N / 1) by simp only [Nat.div_one, Finset.mem_Icc]; exact ⟨ha, haN⟩)
  have hbl := harmonicLogCoordinate_mem_unit hN
    (show b ∈ Finset.Icc 1 (N / 1) by simp only [Nat.div_one, Finset.mem_Icc]; exact ⟨hb, hbN⟩)
  have he : v * (Real.log a + Real.log b) / Real.log N ≤ 2 * V := by
    have hs0 : 0 ≤ Real.log (a : ℝ) / Real.log N + Real.log b / Real.log N := add_nonneg hal.1 hbl.1
    have hs1 : Real.log (a : ℝ) / Real.log N + Real.log b / Real.log N ≤ 2 := by linarith only [hal.2, hbl.2]
    calc
      _ = v * (Real.log (a : ℝ) / Real.log N + Real.log b / Real.log N) := by ring
      _ ≤ V * (Real.log (a : ℝ) / Real.log N + Real.log b / Real.log N) :=
        mul_le_mul_of_nonneg_right hv.2 hs0
      _ ≤ V * 2 := mul_le_mul_of_nonneg_left hs1 hV
      _ = _ := by ring
  rw [shiftedProfileHarmonicRow_coupled P Q v k hN ha hb, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (abs_nonneg _)).trans
    (mul_le_mul_of_nonneg_left (harmonicProduct_abs_le k hN ha hb hB hD hP hQ) (Real.exp_nonneg _))

/-- The finite corrected sum of coupled principal rows. -/
def correctedCoupledProfileSum (P Q : ℝ → ℝ) (N : ℕ) (v : ℝ) (k : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
    shiftedSelbergCorrectionCoeff (-2 * v / Real.log N) a b *
      shiftedProfileHarmonicRow P Q N a b (-2 * v) v k

private def correctedProfilePair (P Q : ℝ → ℝ) (N : ℕ) (v : ℝ) (k : ℕ) (x : ℕ × ℕ) : ℝ :=
  if x.1 ∈ Finset.Icc 1 N ∧ x.2 ∈ Finset.Icc 1 N then
    shiftedSelbergCorrectionCoeff (-2 * v / Real.log N) x.1 x.2 *
      shiftedProfileHarmonicRow P Q N x.1 x.2 (-2 * v) v k else 0

private theorem tsum_correctedProfilePair (P Q : ℝ → ℝ) (N : ℕ) (v : ℝ) (k : ℕ) :
    (∑' x : ℕ × ℕ, correctedProfilePair P Q N v k x) = correctedCoupledProfileSum P Q N v k := by
  classical
  rw [tsum_eq_sum (s := (Finset.Icc 1 N).product (Finset.Icc 1 N))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp only [correctedProfilePair, if_pos ⟨ha, hb⟩, correctedCoupledProfileSum]
  · intro x hx
    exact if_neg (by simpa only [Finset.mem_product] using hx)

/-- The full Euler-corrected coupled polynomial row has the same integral as one principal row. -/
theorem tendsto_correctedCoupledProfileSum (P Q : ℝ[X])
    (hP0 : P.eval 0 = 0) (hQ0 : Q.eval 0 = 0)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (k : ℕ) :
    Tendsto (fun N : ℕ => correctedCoupledProfileSum P.eval Q.eval N (v N) k) atTop
      (𝓝 (∫ t : ℝ in 0..1, t ^ k *
        ((P.derivative.eval (1 - t) - v₀ * P.eval (1 - t)) *
          (Q.derivative.eval (1 - t) - v₀ * Q.eval (1 - t))))) := by
  let I : ℝ := ∫ t : ℝ in 0..1, t ^ k *
    ((P.derivative.eval (1 - t) - v₀ * P.eval (1 - t)) *
      (Q.derivative.eval (1 - t) - v₀ * Q.eval (1 - t)))
  let V : ℝ := |v₀| + 1
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hvbound : ∀ᶠ N : ℕ in atTop, v N ∈ Icc (-V) V := by
    have hh := hv.eventually (Metric.ball_mem_nhds v₀ zero_lt_one)
    filter_upwards [hh] with N hN
    rw [Real.dist_eq] at hN
    obtain ⟨hl, hu⟩ := abs_lt.mp hN
    constructor <;> dsimp only [V] <;> linarith only [hl, hu, neg_abs_le v₀, le_abs_self v₀]
  obtain ⟨B, hB, hPB⟩ := (normalizedShiftedMobiusProfile_compact_uniform P.hasDerivAt
    P.derivative.hasDerivAt P.derivative.derivative.continuous hP0 hV).1
  obtain ⟨D, hD, hQD⟩ := (normalizedShiftedMobiusProfile_compact_uniform Q.hasDerivAt
    Q.derivative.hasDerivAt Q.derivative.derivative.continuous hQ0 hV).1
  let K : ℝ := Real.exp (8 * V) * (Real.exp (2 * V) * (B * D * 2))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hs : Summable (fun x : ℕ × ℕ => K * absoluteSelbergCorrectionCoeff x.1 x.2) :=
    summable_absoluteSelbergCorrectionCoeff.mul_left K
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun N : ℕ => -2 * v N / Real.log N) atTop (𝓝 0) :=
    (hv.const_mul (-2)).div_atTop hlog
  have hp (x : ℕ × ℕ) : Tendsto (fun N : ℕ => correctedProfilePair P.eval Q.eval N (v N) k x)
      atTop (𝓝 (selbergEulerCorrectionCoeff x.1 x.2 * I)) := by
    by_cases hx0 : x.1 = 0 ∨ x.2 = 0
    · have hz : selbergEulerCorrectionCoeff x.1 x.2 = 0 := by
        simp only [selbergEulerCorrectionCoeff, if_pos hx0]
      rw [hz, zero_mul]
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) using 1
      funext N
      rcases hx0 with hx | hx <;> simp [correctedProfilePair, hx]
    · have ha : 0 < x.1 := Nat.pos_of_ne_zero (not_or.mp hx0).1
      have hb : 0 < x.2 := Nat.pos_of_ne_zero (not_or.mp hx0).2
      have hc := (continuous_shiftedSelbergCorrectionCoeff x.1 x.2).continuousAt.tendsto.comp hshift
      rw [shiftedSelbergCorrectionCoeff_zero] at hc
      have hh := hc.mul (tendsto_shiftedProfileHarmonicRow_coupled P Q hP0 hQ0 ha hb hv k)
      refine hh.congr' ?_
      filter_upwards [eventually_ge_atTop (max x.1 x.2)] with N hN
      have hx : x.1 ∈ Finset.Icc 1 N ∧ x.2 ∈ Finset.Icc 1 N :=
        ⟨Finset.mem_Icc.mpr ⟨ha, (le_max_left _ _).trans hN⟩,
          Finset.mem_Icc.mpr ⟨hb, (le_max_right _ _).trans hN⟩⟩
      simp only [Function.comp_def, correctedProfilePair, if_pos hx]
  have hmass : ∀ᶠ N : ℕ in atTop, normalizedHarmonicLogMoment 0 1 N ≤ 2 := by
    have hh := (tendsto_normalizedHarmonicLogMoment 0 (by omega : 0 < 1)).eventually_lt_const
      (show (1 : ℝ) / ((0 : ℕ) + 1) < 2 by norm_num)
    exact hh.mono (fun _ h => h.le)
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ × ℕ,
      ‖correctedProfilePair P.eval Q.eval N (v N) k x‖ ≤ K * absoluteSelbergCorrectionCoeff x.1 x.2 := by
    filter_upwards [eventually_ge_atTop 2, hvbound, hmass] with N hN hvN hm
    intro x
    by_cases hx : x.1 ∈ Finset.Icc 1 N ∧ x.2 ∈ Finset.Icc 1 N
    · have hx1 := Finset.mem_Icc.mp hx.1
      have hx2 := Finset.mem_Icc.mp hx.2
      have hCN : |-2 * v N| ≤ 2 * V := by
        rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
        exact mul_le_mul_of_nonneg_left (abs_le.mpr hvN) (by norm_num)
      have hcoeff := abs_shiftedSelbergCorrectionCoeff_le (by omega : 1 < N) (-2 * v N) hx1.2 hx2.2
      have hcoeff' : |shiftedSelbergCorrectionCoeff (-2 * v N / Real.log N) x.1 x.2| ≤
          Real.exp (8 * V) * absoluteSelbergCorrectionCoeff x.1 x.2 := by
        refine hcoeff.trans (mul_le_mul_of_nonneg_right ?_ (absoluteSelbergCorrectionCoeff_nonneg _ _))
        apply Real.exp_le_exp.mpr
        linarith only [hCN]
      have hrow := abs_shiftedProfileHarmonicRow_coupled_le k (by omega : 1 < N)
        hx1.1 hx2.1 hx1.2 hx2.2 hV hvN hB hD
        (fun u hu => hPB _ (Real.log_pos (by exact_mod_cast hN)) u hu _ hvN)
        (fun u hu => hQD _ (Real.log_pos (by exact_mod_cast hN)) u hu _ hvN)
      have hrow' : |shiftedProfileHarmonicRow P.eval Q.eval N x.1 x.2 (-2 * v N) (v N) k| ≤
          Real.exp (2 * V) * (B * D * 2) := hrow.trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (mul_nonneg hB hD)) (Real.exp_nonneg _))
      rw [correctedProfilePair, if_pos hx, Real.norm_eq_abs, abs_mul]
      have hh := mul_le_mul hcoeff' hrow' (abs_nonneg _) (by positivity)
      exact hh.trans_eq (by dsimp only [K]; ring)
    · simp only [correctedProfilePair, if_neg hx, norm_zero]
      exact mul_nonneg hK (absoluteSelbergCorrectionCoeff_nonneg _ _)
  have hh := tendsto_tsum_of_dominated_convergence hs hp hbound
  rw [tsum_mul_right, tsum_selbergEulerCorrectionCoeff, one_mul] at hh
  simpa only [tsum_correctedProfilePair] using hh

end GaloisForLFunctions.MultiscaleMollifiedZetaField
