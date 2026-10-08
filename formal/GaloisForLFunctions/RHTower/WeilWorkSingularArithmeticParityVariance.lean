import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticResidueEnergy
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticForwardVariance
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionPole

/-!
# Actual parity residue is charged to actual source variance

The odd/full ratio need not be assumed canonical. Its deviation from one
half is bounded by the residual logarithmic variance of the source.
-/

open Complex Filter Topology Set
noncomputable section
namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase

/-- The actual forward series has the residue supplied by its completion. -/
theorem forward_source_residue {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries (sourceCoeff lam) (s : ℂ))
      (𝓝[>] 1) (𝓝 (sourceCompletion hW 1)) := by
  obtain ⟨R, hRd, hReq, _⟩ := exists_forward_regularPart hW
  have hRc : ContinuousAt R (1 : ℂ) :=
    (hRd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))).continuousAt
  have hreal : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  have ht := ((hreal.sub_const 1).mul (hRc.tendsto.comp hreal)).add_const
    (sourceCompletion hW 1)
  simp only [sub_self, zero_mul, zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : (s : ℂ) - 1 ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.zero_re] at this
    change 1 < s at hs
    linarith
  simp only [Function.comp_apply]
  rw [hReq (s : ℂ) hs]
  field_simp [hs1]
  ring

private theorem alternating_summable {f : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) : LSeriesSummable (fun n => f n * (-1 : ℂ) ^ n) s := by
  rw [alternating_eq_sub_twice_oddPart]
  exact hf.sub ((summable_oddPart hf).smul 2)

private theorem alternating_LSeries {f : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) :
    LSeries (fun n => f n * (-1 : ℂ) ^ n) s =
      LSeries f s - 2 * LSeries (oddPart f) s := by
  rw [alternating_eq_sub_twice_oddPart,
    LSeries_sub hf ((summable_oddPart hf).smul 2), LSeries_smul]

private theorem alternating_one_residue_zero :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries (fun n => (-1 : ℂ) ^ n) (s : ℂ))
      (𝓝[>] 1) (𝓝 0) := by
  have hreal : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  have hpow := hreal.neg.const_cpow (a := (2 : ℂ)) (Or.inl (by norm_num))
  have hz : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (𝓝[>] 1) (𝓝 1) := by
    have hc : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1)
        (𝓝[{s : ℂ | 1 < s.re}] 1) :=
      continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (fun _ _ => by simp_all)
    apply (tendsto_sub_mul_tsum_nat_cpow.comp hc).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply]
    rw [zeta_eq_tsum_one_div_nat_cpow (s := (s : ℂ)) hs]
  have ht := ((hpow.const_sub 1).const_mul 2).const_sub 1 |>.mul hz
  norm_num [Complex.cpow_neg_one] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have ha := alternating_LSeries (s := (s : ℂ))
    (LSeriesSummable_one_iff.mpr (show 1 < (s : ℂ).re from hs))
  simp only [Pi.one_apply, one_mul] at ha
  rw [ha, LSeries_oddPart_one (s := (s : ℂ)) hs,
    LSeries_one_eq_riemannZeta (s := (s : ℂ)) hs]
  ring

/-- Full positivity alone supplies the actual variance and actual positive
odd/full ratio, with their sharp parity-energy inequality. -/
theorem exists_forward_parity_variance {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ V r : ℝ, 0 ≤ V ∧ 0 < r ∧
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, ‖forwardCoeff lam n - sourceCompletion hW 1‖ ^ 2 / n) /
          Real.log N) atTop (𝓝 V) ∧
      Tendsto (fun s : ℝ => LSeries (oddPart (sourceCoeff lam)) (s : ℂ) /
        LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (r : ℂ)) ∧
      ‖sourceCompletion hW 1‖ ^ 2 * (2 * r - 1) ^ 2 ≤ V := by
  obtain ⟨_, V, _, hV0, _, _, hV⟩ := exists_forwardCoeff_energy_variance hW
  obtain ⟨r, _, _, hr, _, _, hRatio, _⟩ := exists_odd_source_ratio_limit hW
  refine ⟨V, r, hV0, hr, hV, hRatio, ?_⟩
  let B : ℂ := sourceCompletion hW 1
  let f : ℕ → ℂ := fun n => (sourceCoeff lam n - B) * (-1 : ℂ) ^ n
  have hnorm (n : ℕ) : ‖f n‖ = ‖forwardCoeff lam n - B‖ := by
    simp [f, norm_pow, forwardCoeff_eq_sourceCoeff]
  have hE : Tendsto (fun N : ℕ =>
      weightPartialSum (fun n => ‖f n‖ ^ 2 / n) N / Real.log N) atTop (𝓝 V) := by
    apply hV.congr
    intro N
    congr 1
    unfold weightPartialSum
    simp only [hnorm]
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      have hn0 : n = 0 := by
        simp only [Finset.mem_Icc] at hn hn'
        omega
      simp [hn0]
  have hf (s : ℝ) (hs : 1 < s) : LSeriesSummable f (s : ℂ) := by
    have hc : LSeriesSummable (fun _ : ℕ => B) (s : ℂ) := by
      have he : B • (1 : ℕ → ℂ) = fun _ => B := by funext n; simp
      rw [← he]
      exact (LSeriesSummable_one_iff.mpr (show 1 < (s : ℂ).re from hs)).smul B
    exact alternating_summable ((sourceCoeff_LSeries hW (s := (s : ℂ)) hs).1.sub hc)
  have hFull := forward_source_residue hW
  have hOdd : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (oddPart (sourceCoeff lam)) (s : ℂ)) (𝓝[>] 1) (𝓝 ((r : ℂ) * B)) := by
    apply (hRatio.mul hFull).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hn : LSeries (sourceCoeff lam) (s : ℂ) ≠ 0 := by
      rw [(sourceCoeff_LSeries hW (s := (s : ℂ)) hs).2, IntegerMassRigidity.zetaOf]
      exact Complex.exp_ne_zero _
    field_simp [hn]
  have hRes : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries f (s : ℂ))
      (𝓝[>] 1) (𝓝 ((1 - 2 * (r : ℂ)) * B)) := by
    have ht := (hFull.sub (hOdd.const_mul 2)).sub
      (alternating_one_residue_zero.const_mul B)
    have he : sourceCompletion hW 1 - 2 * ((r : ℂ) * B) - B * 0 =
        (1 - 2 * (r : ℂ)) * B := by dsimp [B]; ring
    rw [he] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hfs : f = (fun n => sourceCoeff lam n * (-1 : ℂ) ^ n) -
        B • (fun n => (-1 : ℂ) ^ n) := by funext n; simp [f]; ring
    have hc : LSeriesSummable (fun n => (-1 : ℂ) ^ n) (s : ℂ) := by
      simpa only [Pi.one_apply, one_mul] using
        alternating_summable (LSeriesSummable_one_iff.mpr (show 1 < (s : ℂ).re from hs))
    have ha := (sourceCoeff_LSeries hW (s := (s : ℂ)) hs).1
    rw [hfs, LSeries_sub (alternating_summable ha) (hc.smul B), LSeries_smul,
      alternating_LSeries ha]
    ring
  have hb := norm_residue_sq_le_log_energy hV0 hE hf hRes
  have he : ‖(1 - 2 * (r : ℂ)) * B‖ ^ 2 = ‖B‖ ^ 2 * (2 * r - 1) ^ 2 := by
    rw [norm_mul, mul_pow,
      show 1 - 2 * (r : ℂ) = ((1 - 2 * r : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rwa [he] at hb

end RHTower.WeilSingularArithmetic
