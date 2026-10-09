import GaloisForLFunctions.RHTower.RepPointPairCoreCompact

/-!
# The cusp splitting `L_φ = K + B`

With the cusp cutoff `ψ = ψ_Y` and the core cutoff `χ = χ_H`, `H = 2(4R + 2)Y`, the kernels of
`L_φ − ψ L_φ ψ` and of `χ L_φ χ − ψ χ L_φ χ ψ` carry the weights `1 − ψ(z)ψ(z')` and
`χ(z)χ(z')(1 − ψ(z)ψ(z'))`.  These agree on every pair `z, z' ∈ 𝒟` with `u(z, Bz') ≤ R`: if
`ψ(z)ψ(z') < 1` then one of the points lies below height `2Y`, and the heights of near points differ by
at most the factor `4R + 2`, so both lie below `H`, where `χ = 1`.  Hence (`ppL2_sub_cuspOp`)

  `L_φ − B_Y = χ L_φ χ − ψ (χ L_φ χ) ψ`,

which is compact because the core operator is (`isCompactOperator_ppL2_sub_cuspOp`).  Together with
the cusp bound this is the splitting `L_φ = K + B_Y`, `K` compact, `‖B_Y‖ ≤ h_{|φ|}(½)`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

section Weighted

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)

include hφc hφM in
theorem integrable_weightedTerm {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure)
    {a : ℍ → ℝ} (ha : Continuous a) (ha1 : ∀ z, |a z| ≤ 1) (z : ℍ) (B : SL(2, ℤ)) :
    Integrable (fun z' => ((φ (pairU z (B • z')) : ℝ) : ℂ) • ρ B (((a z' : ℝ) : ℂ) • F z'))
      cellMeasure := by
  have haF : MemLp (fun z' => ((a z' : ℝ) : ℂ) • F z') 2 cellMeasure :=
    hF.of_le ((Complex.continuous_ofReal.comp ha).aestronglyMeasurable.smul hF.1)
      (Eventually.of_forall fun z' => by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (ha1 z'))
  have hH1 : Integrable (fun z' => ρ B (((a z' : ℝ) : ℂ) • F z')) cellMeasure :=
    (ρ B).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (haF.integrable one_le_two)
  have hk : Continuous (fun z' : ℍ => ((φ (pairU z (B • z')) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφc.comp ((continuous_pairU_right z).comp (continuous_smul_int B)))
  refine hH1.bdd_smul M hk.aestronglyMeasurable (Eventually.of_forall fun z' => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hφM _

include hφc hφM in
/-- **Two weighted point-pair terms combine into one kernel.**  For `z ∈ ℍ`,
`c₁ (L_φ(a₁F))(z) − c₂ (L_φ(a₂F))(z) = ½ Σ_B ∫_𝒟 φ(u(z,Bz')) ρ(B)((c₁a₁(z') − c₂a₂(z')) F(z'))`,
the sum over the finite set of near translates. -/
theorem ppApply_weighted_sub {R : ℝ} (hφR : KernelSupport φ R) {F : ℍ → EuclideanSpace ℂ ι}
    (hF : MemLp F 2 cellMeasure) {a₁ a₂ : ℍ → ℝ} (ha₁ : Continuous a₁) (ha₂ : Continuous a₂)
    (ha₁1 : ∀ z, |a₁ z| ≤ 1) (ha₂1 : ∀ z, |a₂ z| ≤ 1) (c₁ c₂ : ℝ) (z : ℍ) :
    (c₁ : ℂ) • ppApply ρ φ (fun z' => ((a₁ z' : ℝ) : ℂ) • F z') z -
        (c₂ : ℂ) • ppApply ρ φ (fun z' => ((a₂ z' : ℝ) : ℂ) • F z') z =
      (1 / 2 : ℂ) • ∑ B ∈ ppNearSet z R, ∫ z' in fd, ((φ (pairU z (B • z')) : ℝ) : ℂ) •
        ρ B (((c₁ * a₁ z' - c₂ * a₂ z' : ℝ) : ℂ) • F z') := by
  unfold ppApply
  rw [tsum_ppTerm_eq_sum hφR, tsum_ppTerm_eq_sum hφR, smul_comm (c₁ : ℂ), smul_comm (c₂ : ℂ),
    ← smul_sub, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun B _ => ?_
  unfold ppTerm
  have hi₁ : Integrable (fun z' => (c₁ : ℂ) • (((φ (pairU z (B • z')) : ℝ) : ℂ) •
      ρ B (((a₁ z' : ℝ) : ℂ) • F z'))) cellMeasure :=
    (integrable_weightedTerm (ρ := ρ) hφc hφM hF ha₁ ha₁1 z B).smul (c₁ : ℂ)
  have hi₂ : Integrable (fun z' => (c₂ : ℂ) • (((φ (pairU z (B • z')) : ℝ) : ℂ) •
      ρ B (((a₂ z' : ℝ) : ℂ) • F z'))) cellMeasure :=
    (integrable_weightedTerm (ρ := ρ) hφc hφM hF ha₂ ha₂1 z B).smul (c₂ : ℂ)
  rw [← integral_smul, ← integral_smul]
  beta_reduce
  rw [← integral_sub hi₁ hi₂]
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  simp only [map_smul, smul_smul, ← sub_smul]
  congr 1
  push_cast
  ring

end Weighted

/-! ## The splitting -/

section Splitting

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M) (hR : 0 ≤ R)
  (hφR : KernelSupport φ R)

theorem cuspCutoff_lt_one {Y : ℝ} {z : ℍ} (h : cuspCutoff Y z < 1) (hY : 0 < Y) : z.im < 2 * Y := by
  by_contra hle
  push Not at hle
  rw [cuspCutoff_eq_one hY hle] at h
  exact lt_irrefl 1 h

include hR hφR in
/-- **The kernels of `L − ψLψ` and `χLχ − ψχLχψ` agree on near pairs of the cell.** -/
theorem splitting_weight_eq {Y : ℝ} (hY0 : 0 < Y) {z z' : ℍ} (hz : z ∈ fd) (hz' : z' ∈ fd)
    (B : SL(2, ℤ)) (G : EuclideanSpace ℂ ι) :
    ((φ (pairU z (B • z')) : ℝ) : ℂ) • ρ B ((((1 : ℝ) * 1 -
        cuspCutoff Y z * cuspCutoff Y z' : ℝ) : ℂ) • G) =
      ((φ (pairU z (B • z')) : ℝ) : ℂ) • ρ B (((coreCutoff (2 * (4 * R + 2) * Y) z *
        coreCutoff (2 * (4 * R + 2) * Y) z' - cuspCutoff Y z * coreCutoff (2 * (4 * R + 2) * Y) z *
          (coreCutoff (2 * (4 * R + 2) * Y) z' * cuspCutoff Y z') : ℝ) : ℂ) • G) := by
  by_cases hφ0 : φ (pairU z (B • z')) = 0
  · rw [hφ0, Complex.ofReal_zero, zero_smul, zero_smul]
  have hu : pairU z (B • z') ≤ R := not_lt.1 fun hlt => hφ0 (hφR _ hlt)
  have hQ : 0 < 4 * R + 2 := by linarith
  have hH : 0 < 2 * (4 * R + 2) * Y := by positivity
  by_cases h1 : cuspCutoff Y z * cuspCutoff Y z' = 1
  · have e : coreCutoff (2 * (4 * R + 2) * Y) z * coreCutoff (2 * (4 * R + 2) * Y) z' -
        cuspCutoff Y z * coreCutoff (2 * (4 * R + 2) * Y) z *
          (coreCutoff (2 * (4 * R + 2) * Y) z' * cuspCutoff Y z') =
        coreCutoff (2 * (4 * R + 2) * Y) z * coreCutoff (2 * (4 * R + 2) * Y) z' *
          (1 - cuspCutoff Y z * cuspCutoff Y z') := by ring
    rw [e, h1]
    simp
  have hlow : z.im < 2 * Y ∨ z'.im < 2 * Y := by
    by_contra hh
    push Not at hh
    exact h1 (by rw [cuspCutoff_eq_one hY0 hh.1, cuspCutoff_eq_one hY0 hh.2, one_mul])
  have hzi := im_le_of_pairU_le hz' hu
  have hzi' := im_le_of_pairU_le' hz hu
  have hboth : z.im ≤ 2 * (4 * R + 2) * Y ∧ z'.im ≤ 2 * (4 * R + 2) * Y := by
    rcases hlow with h | h
    · constructor
      · nlinarith
      · nlinarith
    · constructor
      · nlinarith
      · nlinarith
  rw [coreCutoff_eq_one hH hboth.1, coreCutoff_eq_one hH hboth.2]
  congr 3
  ring

/-- **The cusp splitting**: `L_φ − ψ_Y L_φ ψ_Y = χ_H L_φ χ_H − ψ_Y (χ_H L_φ χ_H) ψ_Y` with
`H = 2(4R + 2)Y`. -/
theorem ppL2_sub_cuspOp {Y : ℝ} (hY0 : 0 < Y) :
    ppL2 ρ hφc hφM hR hφR - cuspOp ρ hφc hφM hR hφR Y =
      coreOp ρ hφc hφM hR hφR (2 * (4 * R + 2) * Y) -
        cuspMul ι Y ∘L coreOp ρ hφc hφM hR hφR (2 * (4 * R + 2) * Y) ∘L cuspMul ι Y := by
  set H := 2 * (4 * R + 2) * Y with hH_def
  ext1 F
  rw [sub_apply, sub_apply]
  apply Lp.ext
  have hF : MemLp (F : ℍ → EuclideanSpace ℂ ι) 2 cellMeasure := Lp.memLp F
  -- the composite `ψ (χLχ) ψ`
  have hcomp : ((cuspMul ι Y ∘L coreOp ρ hφc hφM hR hφR H ∘L cuspMul ι Y) F :
      ℍ → EuclideanSpace ℂ ι) =ᵐ[cellMeasure] fun z =>
        ((cuspCutoff Y z * coreCutoff H z : ℝ) : ℂ) • ppApply ρ φ (fun z' =>
          ((coreCutoff H z' * cuspCutoff Y z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z') z := by
    have h1 := repMul_coeFn (ι := ι) (continuous_cuspCutoff Y).measurable (abs_cuspCutoff_le Y)
      (coreOp ρ hφc hφM hR hφR H (cuspMul ι Y F))
    have h2 := coreOp_coeFn hφc hφM hR hφR (ρ := ρ) H (cuspMul ι Y F)
    have h3 : ppApply ρ φ (fun z' => ((coreCutoff H z' : ℝ) : ℂ) •
        (cuspMul ι Y F : ℍ → EuclideanSpace ℂ ι) z') = ppApply ρ φ (fun z' =>
          ((coreCutoff H z' * cuspCutoff Y z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z') := by
      refine ppApply_congr_ae φ ?_
      filter_upwards [repMul_coeFn (ι := ι) (continuous_cuspCutoff Y).measurable
        (abs_cuspCutoff_le Y) F] with z' hz'
      change ((coreCutoff H z' : ℝ) : ℂ) • (repMul ι (continuous_cuspCutoff Y).measurable
        (abs_cuspCutoff_le Y) F : ℍ → EuclideanSpace ℂ ι) z' = _
      rw [hz', smul_smul, Complex.ofReal_mul]
    filter_upwards [h1, h2] with z hz1 hz2
    change (repMul ι (continuous_cuspCutoff Y).measurable (abs_cuspCutoff_le Y)
      (coreOp ρ hφc hφM hR hφR H (cuspMul ι Y F)) : ℍ → EuclideanSpace ℂ ι) z = _
    rw [hz1, hz2, h3, smul_smul, Complex.ofReal_mul]
  filter_upwards [Lp.coeFn_sub (ppL2 ρ hφc hφM hR hφR F) (cuspOp ρ hφc hφM hR hφR Y F),
    Lp.coeFn_sub (coreOp ρ hφc hφM hR hφR H F)
      ((cuspMul ι Y ∘L coreOp ρ hφc hφM hR hφR H ∘L cuspMul ι Y) F),
    ppL2_coeFn hφc hφM hR hφR (ρ := ρ) F, cuspOp_coeFn hφc hφM hR hφR Y F,
    coreOp_coeFn hφc hφM hR hφR (ρ := ρ) H F, hcomp,
    ae_restrict_mem (μ := volume) isClosed_fd.measurableSet] with z h1 h2 h3 h4 h5 h6 hz
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, h6]
  have e1 : ppApply ρ φ (F : ℍ → EuclideanSpace ℂ ι) z =
      ((1 : ℝ) : ℂ) • ppApply ρ φ (fun z' => (((1 : ℝ) : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z') z := by
    simp
  rw [e1, ppApply_weighted_sub hφc hφM hφR hF continuous_const (continuous_cuspCutoff Y)
      (fun _ => by norm_num) (abs_cuspCutoff_le Y),
    ppApply_weighted_sub (a₂ := fun z' => coreCutoff H z' * cuspCutoff Y z')
      (c₁ := coreCutoff H z) (c₂ := cuspCutoff Y z * coreCutoff H z) hφc hφM hφR hF
      (continuous_coreCutoff H)
      ((continuous_coreCutoff H).mul (continuous_cuspCutoff Y)) (abs_coreCutoff_le H)
      (fun z' => by
        rw [abs_mul]
        exact mul_le_one₀ (abs_coreCutoff_le H z') (abs_nonneg _) (abs_cuspCutoff_le Y z'))]
  congr 1
  refine Finset.sum_congr rfl fun B _ => ?_
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z' hz' => ?_
  exact splitting_weight_eq hR hφR hY0 hz hz' B _

/-- **The remainder `L_φ − ψ_Y L_φ ψ_Y` is compact.** -/
theorem isCompactOperator_ppL2_sub_cuspOp {Y : ℝ} (hY0 : 0 < Y) :
    IsCompactOperator (ppL2 ρ hφc hφM hR hφR - cuspOp ρ hφc hφM hR hφR Y) := by
  classical
  rw [ppL2_sub_cuspOp hφc hφM hR hφR hY0]
  have hQ : 0 < 4 * R + 2 := by linarith
  have hC := isCompactOperator_coreOp hφc hφM hR hφR (ρ := ρ)
    (H := 2 * (4 * R + 2) * Y) (by positivity)
  rw [FunLike.coe_sub, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact hC.sub ((hC.comp_clm (cuspMul ι Y)).clm_comp (cuspMul ι Y))

end Splitting

end

end GaloisForLFunctions.RHTower.RepPointPair
