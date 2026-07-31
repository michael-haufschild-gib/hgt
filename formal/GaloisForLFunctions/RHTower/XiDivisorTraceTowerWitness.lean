import GaloisForLFunctions.RHTower.XiDivisorDiagonalTraceClass

/-!
# The divisor-side witness of the trace tower

The finite stages of the resolvent-square diagonal `K = diag(μ_q⁻²)` — its truncations to
finite divisor packets — converge to `K` in trace norm, so the abstract trace-tower limit
theorem applies with honest Xi divisor data:

* `xiDivisorResolvent`, `xiDivisorResolventStage`, `xiDivisorResolventTail` — the
  inverse-spectral diagonal, its finite-packet truncation, and the tail;
* `xiDivisorResolventSquare_sub_stage` — the exact tail factorization
  `K - K_s = tail_s ∘ tail_s`;
* `traceNorm_resolventSquare_sub_stage_le` — the trace-norm tail bound
  `‖K - K_s‖₁ ≤ Σ_{q ∉ s} 1/‖μ_q‖²`;
* `tendsto_traceNorm_resolventSquare_stage` — the stages converge in trace norm;
* `xiDivisorResolventSquare_traceTower` — **the witness**: `traceTower_limit` holds on the
  divisor — the finite-stage traces converge to the trace of the Schatten-1 limit.

This realizes the trace-tower card's limit passage on a concrete arithmetic carrier:
finite divisor packets exhaust the spectrum with a summable trace-norm error, exactly the
convergence pattern the conjectural Kähler–Riemann tower must reproduce on the source side.
Unconditional throughout.
-/

namespace RHTower

noncomputable section

open Complex ContinuousLinearMap

/-- The uniform spectral gap at the origin. -/
def xiDivisorSpectralGap : ℝ :=
  exists_uniform_norm_xiSpectralPoint_lowerBound.choose

theorem xiDivisorSpectralGap_pos : 0 < xiDivisorSpectralGap :=
  exists_uniform_norm_xiSpectralPoint_lowerBound.choose_spec.1

theorem xiDivisorSpectralGap_le (q : XiZeroCopy) :
    xiDivisorSpectralGap ≤ ‖xiSpectralPoint q‖ :=
  exists_uniform_norm_xiSpectralPoint_lowerBound.choose_spec.2 q

/-- The inverse-spectral weight family. -/
def xiDivisorInvWeight (q : XiZeroCopy) : ℂ := (xiSpectralPoint q)⁻¹

theorem norm_xiDivisorInvWeight_le (q : XiZeroCopy) :
    ‖xiDivisorInvWeight q‖ ≤ xiDivisorSpectralGap⁻¹ := by
  rw [xiDivisorInvWeight, norm_inv, inv_eq_one_div, inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) xiDivisorSpectralGap_pos
    (xiDivisorSpectralGap_le q)

theorem xiDivisorSpectralGap_inv_nonneg : (0 : ℝ) ≤ xiDivisorSpectralGap⁻¹ :=
  le_of_lt (inv_pos.mpr xiDivisorSpectralGap_pos)

/-- The truncated weight family of a finite divisor packet. -/
def xiDivisorTruncWeight (s : Finset XiZeroCopy) (q : XiZeroCopy) : ℂ :=
  if q ∈ s then xiDivisorInvWeight q else 0

/-- The tail weight family of a finite divisor packet. -/
def xiDivisorTailWeight (s : Finset XiZeroCopy) (q : XiZeroCopy) : ℂ :=
  if q ∈ s then 0 else xiDivisorInvWeight q

theorem norm_xiDivisorTruncWeight_le (s : Finset XiZeroCopy) (q : XiZeroCopy) :
    ‖xiDivisorTruncWeight s q‖ ≤ xiDivisorSpectralGap⁻¹ := by
  rw [xiDivisorTruncWeight]
  by_cases h : q ∈ s
  · rw [if_pos h]
    exact norm_xiDivisorInvWeight_le q
  · rw [if_neg h, norm_zero]
    exact xiDivisorSpectralGap_inv_nonneg

theorem norm_xiDivisorTailWeight_le (s : Finset XiZeroCopy) (q : XiZeroCopy) :
    ‖xiDivisorTailWeight s q‖ ≤ xiDivisorSpectralGap⁻¹ := by
  rw [xiDivisorTailWeight]
  by_cases h : q ∈ s
  · rw [if_pos h, norm_zero]
    exact xiDivisorSpectralGap_inv_nonneg
  · rw [if_neg h]
    exact norm_xiDivisorInvWeight_le q

/-- The inverse-spectral diagonal. -/
def xiDivisorResolvent : XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  xiDivisorDiagonal xiDivisorInvWeight xiDivisorSpectralGap_inv_nonneg
    norm_xiDivisorInvWeight_le

/-- The finite-packet truncation of the inverse-spectral diagonal. -/
def xiDivisorResolventStage (s : Finset XiZeroCopy) :
    XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  xiDivisorDiagonal (xiDivisorTruncWeight s) xiDivisorSpectralGap_inv_nonneg
    (norm_xiDivisorTruncWeight_le s)

/-- The tail of the inverse-spectral diagonal beyond a finite packet. -/
def xiDivisorResolventTail (s : Finset XiZeroCopy) :
    XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  xiDivisorDiagonal (xiDivisorTailWeight s) xiDivisorSpectralGap_inv_nonneg
    (norm_xiDivisorTailWeight_le s)

theorem xiDivisorResolvent_isHilbertSchmidt :
    IsHilbertSchmidt xiDivisorResolvent :=
  xiDivisorDiagonal_isHilbertSchmidt _ _ _ summable_norm_inv_xiSpectralPoint_sq

theorem summable_norm_truncWeight_sq (s : Finset XiZeroCopy) :
    Summable fun q => ‖xiDivisorTruncWeight s q‖ ^ 2 := by
  apply Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    summable_norm_inv_xiSpectralPoint_sq
  rw [xiDivisorTruncWeight]
  by_cases h : q ∈ s
  · rw [if_pos h]
    exact le_of_eq rfl
  · rw [if_neg h, norm_zero]
    rw [show ((0 : ℝ) ^ 2 : ℝ) = 0 by norm_num]
    positivity

theorem summable_norm_tailWeight_sq (s : Finset XiZeroCopy) :
    Summable fun q => ‖xiDivisorTailWeight s q‖ ^ 2 := by
  apply Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    summable_norm_inv_xiSpectralPoint_sq
  rw [xiDivisorTailWeight]
  by_cases h : q ∈ s
  · rw [if_pos h, norm_zero]
    rw [show ((0 : ℝ) ^ 2 : ℝ) = 0 by norm_num]
    positivity
  · rw [if_neg h]
    exact le_of_eq rfl

theorem xiDivisorResolventStage_isHilbertSchmidt (s : Finset XiZeroCopy) :
    IsHilbertSchmidt (xiDivisorResolventStage s) :=
  xiDivisorDiagonal_isHilbertSchmidt _ _ _ (summable_norm_truncWeight_sq s)

theorem xiDivisorResolventTail_isHilbertSchmidt (s : Finset XiZeroCopy) :
    IsHilbertSchmidt (xiDivisorResolventTail s) :=
  xiDivisorDiagonal_isHilbertSchmidt _ _ _ (summable_norm_tailWeight_sq s)

/-- **Exact tail factorization**: the difference between the resolvent square and its
finite-packet stage is the square of the tail diagonal. -/
theorem xiDivisorResolventSquare_sub_stage (s : Finset XiZeroCopy) :
    xiDivisorResolvent.comp xiDivisorResolvent -
        (xiDivisorResolventStage s).comp (xiDivisorResolventStage s) =
      (xiDivisorResolventTail s).comp (xiDivisorResolventTail s) := by
  apply ContinuousLinearMap.ext
  intro f
  ext q
  change xiDivisorInvWeight q * (xiDivisorInvWeight q * f q) -
      xiDivisorTruncWeight s q * (xiDivisorTruncWeight s q * f q) =
    xiDivisorTailWeight s q * (xiDivisorTailWeight s q * f q)
  rw [xiDivisorTruncWeight, xiDivisorTailWeight]
  by_cases h : q ∈ s
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- The Hilbert–Schmidt norm squared of the tail diagonal is the tail sum. -/
theorem hsNormSq_xiDivisorResolventTail (s : Finset XiZeroCopy) :
    ContinuousLinearMap.hsNormSq (xiDivisorResolventTail s) =
      ∑' q : {x : XiZeroCopy // x ∉ s}, ‖xiDivisorInvWeight (q : XiZeroCopy)‖ ^ 2 := by
  rw [ContinuousLinearMap.hsNormSq_eq
    (xiDivisorResolventTail_isHilbertSchmidt s) xiDivisorHilbertBasis]
  have hind : (fun i : XiZeroCopy =>
      ‖(xiDivisorResolventTail s) (xiDivisorHilbertBasis i)‖ ^ 2) =
      Set.indicator {x : XiZeroCopy | x ∉ s}
        (fun q => ‖xiDivisorInvWeight q‖ ^ 2) := by
    funext q
    simp only [xiDivisorResolventTail]
    rw [norm_xiDivisorDiagonal_basis, Set.indicator_apply]
    by_cases h : q ∈ s
    · rw [if_neg (by simpa using h), xiDivisorTailWeight, if_pos h, norm_zero]
      norm_num
    · rw [if_pos (by simpa using h), xiDivisorTailWeight, if_neg h]
  rw [hind, ← tsum_subtype]
  rfl

/-- **The trace-norm tail bound**: `‖K - K_s‖₁ ≤ Σ_{q ∉ s} 1/‖μ_q‖²`. -/
theorem traceNorm_resolventSquare_sub_stage_le (s : Finset XiZeroCopy) :
    traceNorm XiDivisorL2
        (xiDivisorResolvent.comp xiDivisorResolvent -
          (xiDivisorResolventStage s).comp (xiDivisorResolventStage s)) ≤
      ∑' q : {x : XiZeroCopy // x ∉ s}, ‖xiDivisorInvWeight (q : XiZeroCopy)‖ ^ 2 := by
  rw [xiDivisorResolventSquare_sub_stage]
  have h1 : traceNorm XiDivisorL2
      ((xiDivisorResolventTail s).comp (xiDivisorResolventTail s)) ≤
      ContinuousLinearMap.hsNorm (xiDivisorResolventTail s) *
        ContinuousLinearMap.hsNorm (xiDivisorResolventTail s) :=
    tsum_approxNumber_comp_le (xiDivisorResolventTail_isHilbertSchmidt s)
      (xiDivisorResolventTail_isHilbertSchmidt s)
  have h2 : ContinuousLinearMap.hsNorm (xiDivisorResolventTail s) *
      ContinuousLinearMap.hsNorm (xiDivisorResolventTail s) =
      ContinuousLinearMap.hsNormSq (xiDivisorResolventTail s) := by
    rw [ContinuousLinearMap.hsNorm]
    exact Real.mul_self_sqrt (ContinuousLinearMap.hsNormSq_nonneg _)
  rw [← hsNormSq_xiDivisorResolventTail s, ← h2]
  exact h1

/-- **The finite stages converge in trace norm.** -/
theorem tendsto_traceNorm_resolventSquare_stage :
    Filter.Tendsto (fun s : Finset XiZeroCopy =>
      traceNorm XiDivisorL2
        ((xiDivisorResolventStage s).comp (xiDivisorResolventStage s) -
          xiDivisorResolvent.comp xiDivisorResolvent))
      Filter.atTop (nhds 0) := by
  have hswap : ∀ s : Finset XiZeroCopy,
      traceNorm XiDivisorL2
          ((xiDivisorResolventStage s).comp (xiDivisorResolventStage s) -
            xiDivisorResolvent.comp xiDivisorResolvent) =
        traceNorm XiDivisorL2
          (xiDivisorResolvent.comp xiDivisorResolvent -
            (xiDivisorResolventStage s).comp (xiDivisorResolventStage s)) := by
    intro s
    rw [show (xiDivisorResolventStage s).comp (xiDivisorResolventStage s) -
        xiDivisorResolvent.comp xiDivisorResolvent =
      (-1 : ℂ) • (xiDivisorResolvent.comp xiDivisorResolvent -
        (xiDivisorResolventStage s).comp (xiDivisorResolventStage s)) from by
      rw [neg_one_smul]; abel]
    rw [traceNorm_smul]
    simp
  simp only [hswap]
  apply squeeze_zero (fun s => traceNorm_nonneg _)
    (fun s => traceNorm_resolventSquare_sub_stage_le s)
  exact tendsto_tsum_compl_atTop_zero
    (fun q : XiZeroCopy => ‖xiDivisorInvWeight q‖ ^ 2)

/-- **The divisor-side witness of the trace tower**: the finite-packet stages of the
resolvent-square diagonal converge in trace norm, the limit is Schatten-1, and the stage
traces converge to the trace of the limit — `traceTower_limit` realized on honest Xi divisor
data. -/
theorem xiDivisorResolventSquare_traceTower :
    MemSchattenClass 1 (xiDivisorResolvent.comp xiDivisorResolvent) ∧
      Filter.Tendsto (fun s : Finset XiZeroCopy =>
        opTrace ((xiDivisorResolventStage s).comp (xiDivisorResolventStage s)))
        Filter.atTop
        (nhds (opTrace (xiDivisorResolvent.comp xiDivisorResolvent))) := by
  apply traceTower_limit
  · intro s
    exact memSchattenClass_one_comp (xiDivisorResolventStage_isHilbertSchmidt s)
      (xiDivisorResolventStage_isHilbertSchmidt s)
  · intro s
    rw [show (xiDivisorResolventStage s).comp (xiDivisorResolventStage s) -
        xiDivisorResolvent.comp xiDivisorResolvent =
      (-1 : ℂ) • ((xiDivisorResolventTail s).comp (xiDivisorResolventTail s))
        from by rw [neg_one_smul, ← xiDivisorResolventSquare_sub_stage]; abel]
    have hmem := memSchattenClass_one_comp
      (xiDivisorResolventTail_isHilbertSchmidt s)
      (xiDivisorResolventTail_isHilbertSchmidt s)
    have hneg := hmem.one_neg
    rwa [neg_one_smul]
  · exact tendsto_traceNorm_resolventSquare_stage

end

end RHTower
