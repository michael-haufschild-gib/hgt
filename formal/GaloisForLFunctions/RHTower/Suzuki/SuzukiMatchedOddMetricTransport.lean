import GaloisForLFunctions.RHTower.Suzuki.SuzukiMatchedOddNeumannApproximation

open Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Exact norm transport and compression bound the prescribed interval shift. -/
theorem suzukiWeilIntervalShift_le_exp (a : SuzukiPositiveAperture) :
    boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) ≤
      (‖ccmArchimedeanRemainderScalar‖ + 47) * Real.exp a.1 := by
  have hn : ‖suzukiWeilIntervalBoundedRemainder a‖ ≤
      ‖ccmRestrictedWeilBoundedRemainder a‖ := by
    apply (suzukiWeilIntervalBoundedRemainder a).opNorm_le_bound
      (norm_nonneg (ccmRestrictedWeilBoundedRemainder a))
    intro f
    change ‖(suzukiApertureL2Equiv a).symm
      (ccmRestrictedWeilBoundedRemainder a ((suzukiApertureL2Equiv a) f))‖ ≤ _
    rw [(suzukiApertureL2Equiv a).symm.norm_map]
    simpa only [(suzukiApertureL2Equiv a).norm_map] using
      (ccmRestrictedWeilBoundedRemainder a).le_opNorm ((suzukiApertureL2Equiv a) f)
  have hb : ‖ccmRestrictedWeilBoundedRemainder a‖ ≤
      (‖ccmArchimedeanRemainderScalar‖ + 46) * Real.exp a.1 := by
    rw [ccmRestrictedWeilBoundedRemainder_eq_compressed_fullLine]
    exact (norm_ccmApertureCompression_le a _).trans (norm_ccmFullLineBoundedRemainder_le a)
  unfold boundedPerturbedFormShift
  linarith [hn.trans hb, Real.one_le_exp a.2.le]

private theorem norm_square_difference_le {E : Type*} [NormedAddCommGroup E]
    (f u : E) :
    |‖f‖ ^ 2 - ‖u‖ ^ 2| ≤ ‖f - u‖ * (2 * ‖u‖ + ‖f - u‖) := by
  have hf : ‖f‖ ≤ ‖f - u‖ + ‖u‖ := by
    calc
      _ = ‖(f - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  calc
    _ = |(‖f‖ - ‖u‖) * (‖f‖ + ‖u‖)| := congrArg abs (by ring)
    _ = |‖f‖ - ‖u‖| * (‖f‖ + ‖u‖) := by
      rw [abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    _ ≤ _ := mul_le_mul (abs_norm_sub_norm_le f u) (by linarith)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

/-- The prescribed shift pays no asymptotic error when the actual matched
odd physical mass is replaced by that of the literal finite Neumann vector. -/
theorem eventually_suzukiTaMatchedOdd_neumann_metric_error
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ⟨a, ha⟩) *
        |‖ccmArchimedeanFormToAperture ⟨a, ha⟩
          (suzukiTaToFormCLM ⟨a, ha⟩ (suzukiTaRawCoalescingOdd ⟨a, ha⟩ (1 / 2)))‖ ^ 2 -
          ‖ccmMatchedOddNeumannVector ⟨a, ha⟩ ⌈a⌉₊‖ ^ 2| < ε := by
  obtain ⟨M, E, hM, _, happ⟩ := eventually_ccmMatchedOddPoleSource_neumann_decay
  let C := ‖ccmArchimedeanRemainderScalar‖ + 47
  let δ := min 1 (ε / (2 * C * (4 * M + 1)))
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ * (2 * C * (4 * M + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  filter_upwards [happ,
    eventually_suzukiTaMatchedOdd_neumann_relative_error (δ ^ 2) (sq_pos_of_pos hδ)]
    with a haApp haError
  intro ha
  let ap : SuzukiPositiveAperture := ⟨a, ha⟩
  let f := ccmArchimedeanFormToAperture ap
    (suzukiTaToFormCLM ap (suzukiTaRawCoalescingOdd ap (1 / 2)))
  let u := ccmMatchedOddNeumannVector ap ⌈a⌉₊
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ap)
  let t := Real.exp (a / 2)
  have ht : 0 < t := Real.exp_pos _
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have ht2 : t ^ 2 = Real.exp a := by
    dsimp [t]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hu : ‖u‖ * c ≤ M * t := (le_div_iff₀ hc).1 (haApp ha).1
  have hulow := mul_le_mul_of_nonneg_right
    (exp_aperture_le_twice_suzukiWeilIntervalShift ap) (norm_nonneg u)
  have hU : t * ‖u‖ ≤ 2 * M := by
    apply le_of_mul_le_mul_left (a := t) ?_ ht
    change Real.exp a * ‖u‖ ≤ _ at hulow
    rw [← ht2] at hulow
    nlinarith only [hu, hulow]
  have he : t ^ 2 * ‖f - u‖ ^ 2 < δ ^ 2 := by
    rw [ht2]
    exact haError ha
  have hT0 : 0 ≤ t * ‖f - u‖ := mul_nonneg ht.le (norm_nonneg _)
  have hT : t * ‖f - u‖ < δ := by nlinarith only [he, hT0, hδ]
  have hproduct : (t * ‖f - u‖) * (2 * (t * ‖u‖) + t * ‖f - u‖) ≤
      δ * (4 * M + 1) :=
    mul_le_mul hT.le (by linarith)
      (by positivity) hδ.le
  have hdiff : Real.exp a * |‖f‖ ^ 2 - ‖u‖ ^ 2| ≤ δ * (4 * M + 1) := by
    calc
      _ ≤ Real.exp a * (‖f - u‖ * (2 * ‖u‖ + ‖f - u‖)) :=
        mul_le_mul_of_nonneg_left (norm_square_difference_le f u) (Real.exp_pos _).le
      _ = (t * ‖f - u‖) * (2 * (t * ‖u‖) + t * ‖f - u‖) := by rw [← ht2]; ring
      _ ≤ _ := hproduct
  calc
    _ ≤ (C * Real.exp a) * |‖f‖ ^ 2 - ‖u‖ ^ 2| :=
      mul_le_mul_of_nonneg_right (suzukiWeilIntervalShift_le_exp ap) (abs_nonneg _)
    _ = C * (Real.exp a * |‖f‖ ^ 2 - ‖u‖ ^ 2|) := by ring
    _ ≤ C * (δ * (4 * M + 1)) := mul_le_mul_of_nonneg_left hdiff hC.le
    _ < ε := by nlinarith only [hδ2, hε]

theorem tendsto_suzukiTaMatchedOdd_neumann_metric_error :
    Tendsto (fun a : SuzukiPositiveAperture =>
      boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) *
        |‖ccmArchimedeanFormToAperture a
          (suzukiTaToFormCLM a (suzukiTaRawCoalescingOdd a (1 / 2)))‖ ^ 2 -
          ‖ccmMatchedOddNeumannVector a ⌈a.1⌉₊‖ ^ 2|)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro ε hε
    exact Eventually.of_forall fun a => hε.trans_le
      (mul_nonneg (boundedPerturbedFormShift_pos _).le (abs_nonneg _))
  · intro ε hε
    have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
    filter_upwards [hv.eventually (eventually_suzukiTaMatchedOdd_neumann_metric_error ε hε)]
      with a ha
    exact ha a.2

end RHTower
end
