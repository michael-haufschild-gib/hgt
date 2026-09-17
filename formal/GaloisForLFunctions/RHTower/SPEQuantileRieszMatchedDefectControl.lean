import GaloisForLFunctions.RHTower.SPEQuantileRieszParabolicBridge

/-!
# Uniform normalized control of SP-E matched Riesz quadrature defects

The completed SP-E--parabolic bridge leaves an explicit prefix of literal matched quadrature
defects.  This module proves that prefix is uniformly bounded after division by the aperture.
It does so by clipping the Riesz test only above every matched cell in the physical head; the
clipped and literal defects agree termwise on that head.  Thus the inherited Lipschitz estimate
controls the actual source defects rather than a substituted test function.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

private theorem hasDerivAt_speQuantileRieszProfile (M : ℕ) (h : ℝ) :
    HasDerivAt (speQuantileRieszProfile M)
      (Real.sqrt (M : ℝ) * Real.exp (h / 2) - 2 * Real.exp h) h := by
  unfold speQuantileRieszProfile
  have hhalf : HasDerivAt (fun x : ℝ => Real.exp (x / 2))
      (Real.exp (h / 2) * (1 / 2 : ℝ)) h := by
    convert ((Real.hasDerivAt_exp (h / 2)).comp h
      ((hasDerivAt_id h).div_const 2)) using 1 <;> rfl
  have hraw :=
    ((hhalf.const_mul (Real.sqrt (M : ℝ))).sub (Real.hasDerivAt_exp h)).const_mul 2
  change HasDerivAt (fun x : ℝ =>
    2 * (Real.sqrt (M : ℝ) * Real.exp (x / 2) - Real.exp x)) _ h
  apply HasDerivAt.congr_deriv hraw
  ring

private theorem abs_speQuantileRieszProfile_deriv_le
    {M : ℕ} (hM : 0 < M) {h : ℝ} (hh : h ≤ Real.log M + 2) :
    |Real.sqrt (M : ℝ) * Real.exp (h / 2) - 2 * Real.exp h| ≤
      (Real.exp 1 + 2 * Real.exp 2) * M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMR
  have hhalfwall : Real.exp (h / 2) ≤ Real.exp ((Real.log M + 2) / 2) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hwall : Real.exp h ≤ Real.exp (Real.log M + 2) := by
    exact Real.exp_le_exp.mpr hh
  have hloghalf : Real.exp (Real.log (M : ℝ) / 2) = Real.sqrt (M : ℝ) := by
    rw [← Real.log_sqrt hMR.le, Real.exp_log hsqrt]
  have hhalfwall_eq : Real.exp ((Real.log M + 2) / 2) =
      Real.exp 1 * Real.sqrt (M : ℝ) := by
    rw [show (Real.log M + 2) / 2 = Real.log M / 2 + 1 by ring,
      Real.exp_add, hloghalf]
    ring
  have hwall_eq : Real.exp (Real.log M + 2) = (M : ℝ) * Real.exp 2 := by
    rw [Real.exp_add, Real.exp_log hMR]
  calc
    |Real.sqrt (M : ℝ) * Real.exp (h / 2) - 2 * Real.exp h| ≤
        |Real.sqrt (M : ℝ) * Real.exp (h / 2)| + |2 * Real.exp h| := abs_sub _ _
    _ = Real.sqrt (M : ℝ) * Real.exp (h / 2) + 2 * Real.exp h := by
      rw [abs_of_nonneg (mul_nonneg hsqrt.le (Real.exp_nonneg _)),
        abs_of_nonneg (by positivity : 0 ≤ 2 * Real.exp h)]
    _ ≤ Real.sqrt (M : ℝ) * (Real.exp 1 * Real.sqrt (M : ℝ)) +
          2 * ((M : ℝ) * Real.exp 2) := by
      rw [← hhalfwall_eq, ← hwall_eq]
      gcongr
    _ = (Real.exp 1 + 2 * Real.exp 2) * M := by
      rw [show Real.sqrt (M : ℝ) * (Real.exp 1 * Real.sqrt (M : ℝ)) =
          Real.exp 1 * (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) by ring,
        Real.mul_self_sqrt hMR.le]
      ring

/-- Riesz profile clipped only above the physical matched-cell head. -/
def speQuantileRieszClippedProfile (M : ℕ) (h : ℝ) : ℝ :=
  speQuantileRieszProfile M (min (Real.log M + 2) h)

/-- A global Lipschitz budget for the clipped profile.  Its linear aperture growth is exactly
cancelled when the matched quadrature prefix is normalized by `M`. -/
def speQuantileRieszClippedLipschitzConstant (M : ℕ) : NNReal :=
  ⟨(Real.exp 1 + 2 * Real.exp 2) * M, by positivity⟩

theorem lipschitzWith_speQuantileRieszClippedProfile
    {M : ℕ} (hM : 0 < M) :
    LipschitzWith (speQuantileRieszClippedLipschitzConstant M)
      (speQuantileRieszClippedProfile M) := by
  let L : ℝ := Real.log M + 2
  let C : NNReal := speQuantileRieszClippedLipschitzConstant M
  let F : ℝ → ℝ := speQuantileRieszProfile M
  have hraw : LipschitzOnWith C F (Set.Iic L) := by
    apply (convex_Iic L).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (f' := fun h : ℝ =>
        Real.sqrt (M : ℝ) * Real.exp (h / 2) - 2 * Real.exp h)
    · intro h hh
      exact (hasDerivAt_speQuantileRieszProfile M h).hasDerivWithinAt
    · intro h hh
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      dsimp only [C, speQuantileRieszClippedLipschitzConstant]
      exact abs_speQuantileRieszProfile_deriv_le hM hh
  have hclip : LipschitzWith 1 (fun h : ℝ => min L h) := by
    simpa only [id_eq] using (LipschitzWith.const_min LipschitzWith.id L)
  have hcompOn : LipschitzOnWith (C * 1) (F ∘ fun h : ℝ => min L h) Set.univ :=
    hraw.comp hclip.lipschitzOnWith
      (by
        intro h hh
        change min L h ≤ L
        exact min_le_left _ _)
  have hcomp : LipschitzWith C (F ∘ fun h : ℝ => min L h) := by
    have h := lipschitzOnWith_univ.mp hcompOn
    simpa using h
  change LipschitzWith C (F ∘ fun h : ℝ => min L h)
  exact hcomp

private theorem speQuantileRieszClippedProfile_eq_profile_of_le
    (M : ℕ) {h : ℝ} (hh : h ≤ Real.log M + 2) :
    speQuantileRieszClippedProfile M h = speQuantileRieszProfile M h := by
  unfold speQuantileRieszClippedProfile
  rw [min_eq_right hh]

private theorem speQuantileRieszClippedProfile_eq_profile_on_matchedCell
    {M n : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M)
    {h : ℝ} (hh : h ∈ uIcc
      (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)
      (Real.log n + ccmActualHeadMatchedPrimePolarRadius n)) :
    speQuantileRieszClippedProfile M h = speQuantileRieszProfile M h := by
  have hnpos : 0 < n := by omega
  have hMpos : 0 < M := lt_of_lt_of_le hnpos hnM
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hcast : (n : ℝ) ≤ M := by exact_mod_cast hnM
  have hlog : Real.log (n : ℝ) ≤ Real.log M :=
    Real.strictMonoOn_log.monotoneOn (mem_Ioi.mpr hnR) (mem_Ioi.mpr hMR) hcast
  have hrho : 0 ≤ ccmActualHeadMatchedPrimePolarRadius n :=
    ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hrhoone : ccmActualHeadMatchedPrimePolarRadius n ≤ 1 :=
    ccmActualHeadMatchedPrimePolarRadius_le_one_of_one_le hn
  have horder : Real.log (n : ℝ) - ccmActualHeadMatchedPrimePolarRadius n ≤
      Real.log n + ccmActualHeadMatchedPrimePolarRadius n := by linarith
  rw [uIcc_of_le horder] at hh
  exact speQuantileRieszClippedProfile_eq_profile_of_le M (by
    linarith [hh.2])

/-- The clipped test has exactly the literal SP-E defect on every matched cell in the physical
head. -/
theorem ccmMatchedPrimePolarQuadratureDefect_speQuantileRieszProfile_eq_clipped
    {M n : ℕ} (hn : 1 ≤ n) (hnM : n ≤ M) :
    ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) n =
      ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszClippedProfile M) n := by
  have hnpos : 0 < n := by omega
  have hMpos : 0 < M := lt_of_lt_of_le hnpos hnM
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hcast : (n : ℝ) ≤ M := by exact_mod_cast hnM
  have hlog : Real.log (n : ℝ) ≤ Real.log M :=
    Real.strictMonoOn_log.monotoneOn (mem_Ioi.mpr hnR) (mem_Ioi.mpr hMR) hcast
  unfold ccmMatchedPrimePolarQuadratureDefect
  rw [speQuantileRieszClippedProfile_eq_profile_of_le M (by linarith)]
  congr 1
  apply intervalIntegral.integral_congr
  intro h hh
  change Real.exp (h / 2) * speQuantileRieszProfile M h =
    Real.exp (h / 2) * speQuantileRieszClippedProfile M h
  rw [speQuantileRieszClippedProfile_eq_profile_on_matchedCell hn hnM hh]

/-- Uniform bound for the literal matched Riesz-defect prefix after physical normalization. -/
theorem abs_normalized_speQuantileRieszMatchedQuadratureDefectPrefix_le
    {M : ℕ} (hM : 3 ≤ M) :
    |(∑ n ∈ Finset.range ((M - 3) + 1),
        ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) (n + 2)) /
        (M : ℝ)| ≤
      (Real.exp 1 + 2 * Real.exp 2) / 2 *
        ∑' n : ℕ, criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2) := by
  have hMpos : 0 < M := by omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hupper : (M - 3) + 2 = M - 1 := by omega
  have hprefix :
      (∑ n ∈ Finset.range ((M - 3) + 1),
        ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) (n + 2)) =
      ∑ n ∈ Finset.range ((M - 3) + 1),
        ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszClippedProfile M) (n + 2) := by
    rw [sum_range_shift_two_eq_sum_Icc_two,
      sum_range_shift_two_eq_sum_Icc_two]
    rw [hupper]
    apply Finset.sum_congr rfl
    intro n hn
    have hnmem := Finset.mem_Icc.mp hn
    exact ccmMatchedPrimePolarQuadratureDefect_speQuantileRieszProfile_eq_clipped
      (by omega) (by omega)
  rw [hprefix, sum_range_shift_two_eq_sum_Icc_two, hupper]
  have hbound := abs_sum_ccmMatchedPrimePolarQuadratureDefect_le
    (lipschitzWith_speQuantileRieszClippedProfile hMpos)
    (Finset.Icc 2 (M - 1))
  rw [abs_div, abs_of_pos hMR]
  calc
    |∑ n ∈ Finset.Icc 2 (M - 1),
        ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszClippedProfile M) n| / (M : ℝ) ≤
        ((speQuantileRieszClippedLipschitzConstant M : ℝ) / 2 *
          ∑' n : ℕ, criticalMellinAtomWeight n ^ 2 /
            Real.exp (Real.log n / 2)) / M :=
      div_le_div_of_nonneg_right hbound hMR.le
    _ = (Real.exp 1 + 2 * Real.exp 2) / 2 *
        ∑' n : ℕ, criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2) := by
      change (((Real.exp 1 + 2 * Real.exp 2) * (M : ℝ) / 2 *
        ∑' n : ℕ, criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2)) / (M : ℝ)) = _
      field_simp [hMR.ne']

end RHTower
