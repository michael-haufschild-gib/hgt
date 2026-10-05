import GaloisForLFunctions.RHTower.ThetaQuotientOppositeFrequencyBlocks

/-!
# The paired-block metric of the theta quotient

With `r_n = (Φ_{2k} − Φ_k)/Φ_k ∈ (0, 1)` (`k = n + 1`) the paired-block metric
`G₀ = ⊕_n [[1, r_n], [r_n, 1]]` (the identity on constants) is self-adjoint, uniformly positive
(`c ≤ G₀ ≤ 2` as quadratic forms) and boundedly invertible.  It symmetrizes every exact block:
`G₀ X_n` is a real multiple of `P_{e_k} − P_{e_{−k}}`, so `G₀ D₀ = D₀* G₀`.  Hence, with the full
cross-frequency operator `R = D − D₀`, the metric defect of `D` is exactly that of `R`:
`G₀ D − D* G₀ = G₀ R − R* G₀`.
-/

open MeasureTheory Set Filter Topology Module
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-! ## The swaps -/

/-- The swap `e_k ↔ e_{−k}` on `H_n`, zero on `H_n^⊥`. -/
def frequencySwap (n : ℕ) : ThetaL2 →L[ℂ] ThetaL2 :=
  rankOneMap (unitFourierBasis (blockPos n)) (unitFourierBasis (blockNeg n)) +
    rankOneMap (unitFourierBasis (blockNeg n)) (unitFourierBasis (blockPos n))

theorem frequencySwap_apply (n : ℕ) (x : ThetaL2) :
    frequencySwap n x = ⟪unitFourierBasis (blockPos n), x⟫_ℂ • unitFourierBasis (blockNeg n) +
      ⟪unitFourierBasis (blockNeg n), x⟫_ℂ • unitFourierBasis (blockPos n) := by
  simp [frequencySwap, rankOneMap_apply]

theorem pairProj_frequencySwap (n : ℕ) (x : ThetaL2) : pairProj n (frequencySwap n x) = frequencySwap n x := by
  rw [frequencySwap_apply, map_add, map_smul, map_smul, pairProj_unitFourierBasis_pos,
    pairProj_unitFourierBasis_neg]

theorem norm_frequencySwap_apply (n : ℕ) (x : ThetaL2) : ‖frequencySwap n x‖ = ‖pairProj n x‖ := by
  have horth : ⟪⟪unitFourierBasis (blockPos n), x⟫_ℂ • unitFourierBasis (blockNeg n),
      ⟪unitFourierBasis (blockNeg n), x⟫_ℂ • unitFourierBasis (blockPos n)⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, inner_unitFourierBasis, if_neg (Ne.symm (blockPos_ne_blockNeg n))]
    simp
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [← sq, ← sq, ← sq] at h
  have h2 : ‖frequencySwap n x‖ ^ 2 = ‖pairProj n x‖ ^ 2 := by
    rw [frequencySwap_apply, h, norm_sq_pairProj, norm_smul, norm_smul, unitFourierBasis.orthonormal.1,
      unitFourierBasis.orthonormal.1]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

theorem inner_frequencySwap_left (n : ℕ) (x y : ThetaL2) : ⟪frequencySwap n x, y⟫_ℂ = ⟪x, frequencySwap n y⟫_ℂ := by
  rw [frequencySwap_apply, frequencySwap_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, inner_conj_symm, inner_conj_symm]
  ring

/-! ## The metric -/

/-- The paired ratio `r_n = (Φ_{2k} − Φ_k)/Φ_k`, `k = n + 1`. -/
def pairRatio (n : ℕ) : ℝ := dyadicRatio (n + 1)

theorem pairRatio_mem_Ioo (n : ℕ) : pairRatio n ∈ Ioo (0 : ℝ) 1 := by
  have h := dyadicRatio_mem_Ioo (n := n + 1) (by omega)
  simpa [pairRatio, dyadicRatio] using h

theorem zero_le_pairRatio (n : ℕ) : 0 ≤ pairRatio n := (pairRatio_mem_Ioo n).1.le

theorem tendsto_pairRatio : Tendsto pairRatio atTop (𝓝 0) :=
  tendsto_dyadicRatio.comp (tendsto_add_atTop_nat 1)

/-- `δ_n = r_n α_n`. -/
theorem blockOff_eq_pairRatio_mul (n : ℕ) : blockOff n = pairRatio n * blockDiag n := by
  have hΦ := cdfAction_pos (n := n + 1) (by omega)
  push_cast at hΦ
  have hpi : 2 * Real.pi * ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [blockOff, pairRatio, dyadicRatio, blockDiag]
  push_cast
  field_simp

theorem isPairBlockFamily_pairMetric :
    IsPairBlockFamily (fun n => (pairRatio n : ℂ) • frequencySwap n) pairRatio := by
  refine ⟨fun n x => ?_, fun n x => ?_⟩
  · simp only [smul_apply, map_smul, pairProj_frequencySwap]
  · simp only [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_pairRatio n), norm_frequencySwap_apply]
    exact le_rfl

theorem summable_pairMetric : Summable fun n => (pairRatio n : ℂ) • frequencySwap n :=
  isPairBlockFamily_pairMetric.summable tendsto_pairRatio

/-- The off-diagonal part `⊕_n r_n S_n` of the metric. -/
def pairMetricOffDiag : ThetaL2 →L[ℂ] ThetaL2 := ∑' n, (pairRatio n : ℂ) • frequencySwap n

/-- **The paired-block metric** `G₀ = ⊕_n [[1, r_n], [r_n, 1]]`. -/
def pairedBlockMetric : ThetaL2 →L[ℂ] ThetaL2 := 1 + pairMetricOffDiag

theorem exists_norm_pairMetricOffDiag_le :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ‖pairMetricOffDiag‖ ≤ 1 - c := by
  obtain ⟨c, hc, hcn⟩ := exists_pos_le_one_sub_dyadicRatio
  have hc1 : c ≤ 1 := by
    have := (hcn 1 le_rfl).1
    have := (pairRatio_mem_Ioo 0).1
    simp only [pairRatio, zero_add] at this
    linarith
  refine ⟨c, hc, hc1, isPairBlockFamily_pairMetric.norm_tsum_le summable_pairMetric (by linarith) fun n => ?_⟩
  have := (hcn (n + 1) (by omega)).1
  simp only [pairRatio]
  linarith

theorem re_inner_pairedBlockMetric (x : ThetaL2) :
    RCLike.re ⟪x, pairedBlockMetric x⟫_ℂ = ‖x‖ ^ 2 + RCLike.re ⟪x, pairMetricOffDiag x⟫_ℂ := by
  rw [pairedBlockMetric, add_apply, one_apply_eq_self, inner_add_right,
    map_add, inner_self_eq_norm_sq]

/-- **Uniform positivity**: `c‖x‖² ≤ Re⟨x, G₀x⟩ ≤ 2‖x‖²`. -/
theorem exists_pairedBlockMetric_uniform :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ThetaL2,
      c * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, pairedBlockMetric x⟫_ℂ ∧ RCLike.re ⟪x, pairedBlockMetric x⟫_ℂ ≤ 2 * ‖x‖ ^ 2 := by
  obtain ⟨c, hc, hc1, hK⟩ := exists_norm_pairMetricOffDiag_le
  refine ⟨c, hc, fun x => ?_⟩
  rw [re_inner_pairedBlockMetric]
  have h1 : |RCLike.re ⟪x, pairMetricOffDiag x⟫_ℂ| ≤ (1 - c) * ‖x‖ ^ 2 := by
    calc |RCLike.re ⟪x, pairMetricOffDiag x⟫_ℂ| ≤ ‖⟪x, pairMetricOffDiag x⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖x‖ * ‖pairMetricOffDiag x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖pairMetricOffDiag‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (pairMetricOffDiag.le_opNorm x) (norm_nonneg _)
      _ ≤ ‖x‖ * ((1 - c) * ‖x‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) (norm_nonneg _)
      _ = (1 - c) * ‖x‖ ^ 2 := by ring
  have h2 := abs_le.1 h1
  have hx : 0 ≤ ‖x‖ ^ 2 := by positivity
  constructor <;> nlinarith [h2.1, h2.2]

/-- **Bounded invertibility**: `G₀` is a unit with `‖G₀⁻¹‖ ≤ 1/c`. -/
theorem exists_pairedBlockMetric_inverse :
    ∃ c : ℝ, 0 < c ∧ ∃ G : ThetaL2 →L[ℂ] ThetaL2,
      pairedBlockMetric * G = 1 ∧ G * pairedBlockMetric = 1 ∧ ‖G‖ ≤ 1 / c := by
  obtain ⟨c, hc, hc1, hK⟩ := exists_norm_pairMetricOffDiag_le
  obtain ⟨c', hc', hunif⟩ := exists_pairedBlockMetric_uniform
  have hlt : ‖-pairMetricOffDiag‖ < 1 := by rw [norm_neg]; linarith
  set u := Units.oneSub (-pairMetricOffDiag) hlt
  have hu : (u : ThetaL2 →L[ℂ] ThetaL2) = pairedBlockMetric := by
    rw [Units.val_oneSub, sub_neg_eq_add, pairedBlockMetric]
  refine ⟨c', hc', (↑u⁻¹ : ThetaL2 →L[ℂ] ThetaL2), ?_, ?_, ?_⟩
  · rw [← hu, Units.mul_inv]
  · rw [← hu, Units.inv_mul]
  · -- coercivity: `c'‖y‖ ≤ ‖G₀ y‖`
    have hcoer : ∀ y : ThetaL2, c' * ‖y‖ ≤ ‖pairedBlockMetric y‖ := by
      intro y
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
      have h1 := (hunif y).1
      have h2 : RCLike.re ⟪y, pairedBlockMetric y⟫_ℂ ≤ ‖y‖ * ‖pairedBlockMetric y‖ :=
        (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      nlinarith
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    have h := hcoer ((↑u⁻¹ : ThetaL2 →L[ℂ] ThetaL2) x)
    have hx : pairedBlockMetric ((↑u⁻¹ : ThetaL2 →L[ℂ] ThetaL2) x) = x := by
      rw [← hu, ← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
    rw [hx] at h
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc']
    linarith

/-! ## Self-adjointness -/

theorem isSelfAdjoint_of_inner {A : ThetaL2 →L[ℂ] ThetaL2} (h : ∀ x y, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) :
    IsSelfAdjoint A :=
  ContinuousLinearMap.isSelfAdjoint_iff'.2 ((ContinuousLinearMap.eq_adjoint_iff A A).2 h).symm

theorem isSelfAdjoint_tsum {f : ℕ → ThetaL2 →L[ℂ] ThetaL2} (hf : ∀ n, IsSelfAdjoint (f n)) :
    IsSelfAdjoint (∑' n, f n) := by
  rw [IsSelfAdjoint, tsum_star]
  exact tsum_congr fun n => (hf n).star_eq

theorem isSelfAdjoint_frequencySwap (n : ℕ) : IsSelfAdjoint (frequencySwap n) :=
  isSelfAdjoint_of_inner (inner_frequencySwap_left n)

theorem isSelfAdjoint_ofReal (r : ℝ) : IsSelfAdjoint (r : ℂ) := by
  rw [IsSelfAdjoint]; exact Complex.conj_ofReal r

theorem isSelfAdjoint_pairMetricOffDiag : IsSelfAdjoint pairMetricOffDiag := by
  unfold pairMetricOffDiag
  exact isSelfAdjoint_tsum fun n => IsSelfAdjoint.smul (isSelfAdjoint_ofReal _) (isSelfAdjoint_frequencySwap n)

theorem isSelfAdjoint_pairedBlockMetric : IsSelfAdjoint pairedBlockMetric := by
  unfold pairedBlockMetric
  exact (IsSelfAdjoint.one _).add isSelfAdjoint_pairMetricOffDiag

theorem isSelfAdjoint_rankOneMap_self (u : ThetaL2) : IsSelfAdjoint (rankOneMap u u) :=
  isSelfAdjoint_of_inner fun x y => by
    rw [rankOneMap_apply, rankOneMap_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
    ring

/-! ## Symmetrized blocks and the cross-frequency defect -/

/-- On `H_n`, the off-diagonal part acts as `r_n S_n`. -/
theorem pairMetricOffDiag_apply_of_mem {n : ℕ} {y : ThetaL2} (hy : pairProj n y = y) :
    pairMetricOffDiag y = (pairRatio n : ℂ) • frequencySwap n y := by
  rw [pairMetricOffDiag, IsPairBlockFamily.tsum_apply summable_pairMetric]
  refine (tsum_eq_single n fun m hm => ?_).trans rfl
  refine isPairBlockFamily_pairMetric.apply_eq_zero ?_
  rw [← hy, pairProj_pairProj_of_ne hm]

/-- **`G₀` symmetrizes the exact block**: `G₀X_n = (α_n − r_n δ_n)(P_{e_k} − P_{e_{−k}})`. -/
theorem pairedBlockMetric_comp_thetaDiagonalBlock (n : ℕ) :
    pairedBlockMetric ∘L thetaDiagonalBlock n =
      ((blockDiag n - pairRatio n * blockOff n : ℝ) : ℂ) •
        (rankOneMap (unitFourierBasis (blockPos n)) (unitFourierBasis (blockPos n)) -
          rankOneMap (unitFourierBasis (blockNeg n)) (unitFourierBasis (blockNeg n))) := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hmem : pairProj n (thetaDiagonalBlock n x) = thetaDiagonalBlock n x :=
    isPairBlockFamily_thetaDiagonalBlock.1 n x
  rw [ContinuousLinearMap.comp_apply, pairedBlockMetric, add_apply,
    one_apply_eq_self, pairMetricOffDiag_apply_of_mem hmem, frequencySwap_apply,
    thetaDiagonalBlock_eq]
  have hpp := inner_unitFourierBasis (blockPos n) (blockPos n)
  have hnn := inner_unitFourierBasis (blockNeg n) (blockNeg n)
  have hpn := inner_unitFourierBasis (blockPos n) (blockNeg n)
  have hnp := inner_unitFourierBasis (blockNeg n) (blockPos n)
  rw [if_pos rfl] at hpp hnn
  rw [if_neg (blockPos_ne_blockNeg n)] at hpn
  rw [if_neg (Ne.symm (blockPos_ne_blockNeg n))] at hnp
  simp only [add_apply, sub_apply, smul_apply,
    rankOneMap_apply, inner_add_right, inner_sub_right, inner_smul_right, hpp, hnn, hpn, hnp,
    blockOff_eq_pairRatio_mul]
  push_cast
  module

theorem isSelfAdjoint_pairedBlockMetric_comp_thetaDiagonalBlock (n : ℕ) :
    IsSelfAdjoint (pairedBlockMetric ∘L thetaDiagonalBlock n) := by
  rw [pairedBlockMetric_comp_thetaDiagonalBlock]
  refine IsSelfAdjoint.smul (isSelfAdjoint_ofReal _) ?_
  exact (isSelfAdjoint_rankOneMap_self _).sub (isSelfAdjoint_rankOneMap_self _)

/-- `G₀ D₀` is self-adjoint. -/
theorem isSelfAdjoint_pairedBlockMetric_comp_thetaBlockDiagonal :
    IsSelfAdjoint (pairedBlockMetric ∘L thetaBlockDiagonal) := by
  have h : pairedBlockMetric ∘L thetaBlockDiagonal = ∑' n, pairedBlockMetric ∘L thetaDiagonalBlock n :=
    (ContinuousLinearMap.compL ℂ ThetaL2 ThetaL2 ThetaL2 pairedBlockMetric).map_tsum summable_thetaDiagonalBlock
  rw [h]
  exact isSelfAdjoint_tsum isSelfAdjoint_pairedBlockMetric_comp_thetaDiagonalBlock

/-- **`G₀ D₀ = D₀* G₀`**: the paired-block metric symmetrizes the whole block part. -/
theorem pairedBlockMetric_comp_thetaBlockDiagonal :
    pairedBlockMetric ∘L thetaBlockDiagonal =
      ContinuousLinearMap.adjoint thetaBlockDiagonal ∘L pairedBlockMetric := by
  have h1 := ContinuousLinearMap.isSelfAdjoint_iff'.1 isSelfAdjoint_pairedBlockMetric_comp_thetaBlockDiagonal
  have h2 := ContinuousLinearMap.isSelfAdjoint_iff'.1 isSelfAdjoint_pairedBlockMetric
  rw [ContinuousLinearMap.adjoint_comp, h2] at h1
  exact h1.symm

/-- **The full cross-frequency operator** `R = D − D₀`. -/
def thetaCrossFrequencyOperator : ThetaL2 →L[ℂ] ThetaL2 := thetaQuotientOperator - thetaBlockDiagonal

theorem isCompactOperator_thetaCrossFrequencyOperator : IsCompactOperator thetaCrossFrequencyOperator :=
  isCompactOperator_thetaQuotientOperator.sub isCompactOperator_thetaBlockDiagonal

/-- **The exact remaining defect**: `G₀ D − D* G₀ = G₀ R − R* G₀`. -/
theorem pairedBlockMetric_defect_eq :
    pairedBlockMetric ∘L thetaQuotientOperator - ContinuousLinearMap.adjoint thetaQuotientOperator ∘L
        pairedBlockMetric =
      pairedBlockMetric ∘L thetaCrossFrequencyOperator -
        ContinuousLinearMap.adjoint thetaCrossFrequencyOperator ∘L pairedBlockMetric := by
  have hD : thetaQuotientOperator = thetaCrossFrequencyOperator + thetaBlockDiagonal := by
    rw [thetaCrossFrequencyOperator, sub_add_cancel]
  have h0 := pairedBlockMetric_comp_thetaBlockDiagonal
  conv_lhs => rw [hD]
  rw [map_add, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, h0]
  abel

end

end RHTower
