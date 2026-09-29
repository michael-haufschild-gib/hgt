import GaloisForLFunctions.RHTower.DeckPointPairRegularity
import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichletPeriodization

/-!
# Gradient bounds for finite-deck point-pair operators

For a `C¹` profile `φ` supported in `[0, R]` the chart derivative of `L_φ F` is the finite sum of
the differentiated translates.  Since `|Im z · ∂ₓ u(z, w)| ≤ 2R + 1` and
`|Im z · ∂ᵧ u(z, w)| ≤ 3R + 2` on the kernel support, the hyperbolic gradients are dominated
pointwise by the point-pair operator of `|φ'|` applied to the scalar lift `‖F‖ e` of the norm
along a fixed unit deck vector `e`.  Hence `L_φ` maps finite-deck `L²` into the Dirichlet
pre-domain.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-- The normalized constant deck vector, fixed by every `ρ(B)`. -/
def deckUnitVec (N : ℕ) : DeckSpace N :=
  (WithLp.equiv 2 (Deck N → ℂ)).symm (fun _ => ((Real.sqrt (Fintype.card (Deck N)))⁻¹ : ℂ))

theorem deckRho_deckUnitVec (B : SL(2, ℤ)) : deckRho N B (deckUnitVec N) = deckUnitVec N := by
  ext q
  simp [deckRho, deckUnitVec, finiteRegularUnitary_apply]

theorem norm_deckUnitVec : ‖deckUnitVec N‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [deckUnitVec, WithLp.equiv_symm_apply, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hn : (0 : ℝ) < Fintype.card (Deck N) := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_pow, Real.sq_sqrt hn.le,
    mul_inv_cancel₀ hn.ne', Real.sqrt_one]

/-- The scalar lift `F♯(z) = ‖F(z)‖ e` of the pointwise norm. -/
def normLift (F : ℍ → DeckSpace N) (z : ℍ) : DeckSpace N := (‖F z‖ : ℂ) • deckUnitVec N

theorem norm_normLift (F : ℍ → DeckSpace N) (z : ℍ) : ‖normLift F z‖ = ‖F z‖ := by
  rw [normLift, norm_smul, norm_deckUnitVec, mul_one, Complex.norm_real, Real.norm_of_nonneg
    (norm_nonneg _)]

theorem memLp_normLift {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) :
    MemLp (normLift F) 2 cellMeasure := by
  refine hF.of_le ?_ (Eventually.of_forall fun z => by rw [norm_normLift])
  exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hF.1.norm).smul
    aestronglyMeasurable_const

/-- For a nonnegative kernel, `L_ψ F♯` is the scalar Schur integral times the unit vector. -/
theorem norm_ppApply_normLift {ψ : ℝ → ℝ} {M R : ℝ} (hψc : Continuous ψ) (hψM : ∀ u, |ψ u| ≤ M)
    (hψR : KernelSupport ψ R) (hψ0 : ∀ u, 0 ≤ ψ u) {F : ℍ → DeckSpace N}
    (hF : MemLp F 2 cellMeasure) (z : ℍ) :
    ‖ppApply ψ (normLift F) z‖ =
      1 / 2 * ∑ B ∈ ppNearSet z R, ∫ z' in fd, ψ (pairU z (B • z')) * ‖F z'‖ := by
  unfold ppApply
  rw [tsum_ppTerm_eq_sum hψR]
  have hterm : ∀ B : SL(2, ℤ), ppTerm ψ (normLift F) z B =
      ((∫ z' in fd, ψ (pairU z (B • z')) * ‖F z'‖ : ℝ) : ℂ) • deckUnitVec N := by
    intro B
    unfold ppTerm normLift
    have hint : Integrable (fun z' => ψ (pairU z (B • z')) * ‖F z'‖) cellMeasure := by
      have h := integrable_ppKernel_mul_norm hψc hψM hF z B
      refine h.congr (Eventually.of_forall fun z' => ?_)
      simp only [abs_of_nonneg (hψ0 _)]
    calc (∫ z' in fd, ((ψ (pairU z (B • z')) : ℝ) : ℂ) • deckRho N B ((‖F z'‖ : ℂ) • deckUnitVec N))
        = ∫ z' in fd, (ψ (pairU z (B • z')) * ‖F z'‖) • deckUnitVec N := by
          refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
          simp only [map_smul, deckRho_deckUnitVec, smul_smul]
          rw [← Complex.coe_smul]
          push_cast; ring_nf
      _ = (∫ z' in fd, ψ (pairU z (B • z')) * ‖F z'‖) • deckUnitVec N := integral_smul_const _ _
      _ = _ := (Complex.coe_smul _ _).symm
  simp_rw [hterm]
  rw [← Finset.sum_smul, smul_smul, norm_smul, norm_deckUnitVec, mul_one, ← Complex.ofReal_sum]
  rw [show ((1 / 2 : ℂ) * ((∑ B ∈ ppNearSet z R, ∫ z' in fd, ψ (pairU z (B • z')) * ‖F z'‖ : ℝ) : ℂ))
    = ((1 / 2 * ∑ B ∈ ppNearSet z R, ∫ z' in fd, ψ (pairU z (B • z')) * ‖F z'‖ : ℝ) : ℂ) by
      push_cast; ring]
  rw [Complex.norm_real, Real.norm_of_nonneg]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun B _ =>
    integral_nonneg fun z' => mul_nonneg (hψ0 _) (norm_nonneg _))

section Grad

variable {φ : ℝ → ℝ} {M M' R : ℝ} (hφd : Differentiable ℝ φ) (hφ'c : Continuous (deriv φ))
  (hφM : ∀ u, |φ u| ≤ M) (hφ'M : ∀ u, |deriv φ u| ≤ M') (hR : 0 ≤ R) (hφR : KernelSupport φ R)

include hφd hφ'c hφM hφ'M hR hφR in
theorem hasFDerivAt_chartFun_ppApply {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) (z : ℍ) :
    HasFDerivAt (chartFun (ppApply φ F)) ((1 / 2 : ℂ) • ∑ B ∈ ppNearSet z (2 * (1 + 2 * R)),
      ppTermcDeriv φ F B (z : ℂ)) (z : ℂ) := by
  set S := ppNearSet z (2 * (1 + 2 * R))
  have hz : 0 < (z : ℂ).im := z.im_pos
  have hg0 := (HasFDerivAt.sum (u := S) fun B _ =>
    hasFDerivAt_ppTermc hφd hφ'c hφM hφ'M hR hφR hF B hz).const_smul (1 / 2 : ℂ)
  have e : (fun ζ' => (1 / 2 : ℂ) • ∑ B ∈ S, ppTermc φ F B ζ') =
      (1 / 2 : ℂ) • ∑ i ∈ S, ppTermc φ F i := by
    funext ζ'; simp [Finset.sum_apply]
  have hg : HasFDerivAt (fun ζ' => (1 / 2 : ℂ) • ∑ B ∈ S, ppTermc φ F B ζ')
      ((1 / 2 : ℂ) • ∑ B ∈ S, ppTermcDeriv φ F B (z : ℂ)) (z : ℂ) := by rw [e]; exact hg0
  refine hg.congr_of_eventuallyEq ?_
  have hε : 0 < (z : ℂ).im / 2 := by linarith
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)] with ζ' hζ'
  rw [Metric.mem_ball, dist_eq_norm] at hζ'
  have := chartFun_ppApply_local hφR F hz hζ'
  rwa [UpperHalfPlane.ofComplex_apply] at this

include hφd hφ'c hφM hφ'M hR hφR in
theorem chartDeriv_ppApply {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) (z : ℍ) (v : ℂ) :
    MaassFiniteDeckDirichlet.chartDeriv (ppApply φ F) v z = (1 / 2 : ℂ) • ∑ B ∈ ppNearSet z (2 * (1 + 2 * R)),
      ppTermcDeriv φ F B (z : ℂ) v := by
  unfold MaassFiniteDeckDirichlet.chartDeriv
  rw [(hasFDerivAt_chartFun_ppApply hφd hφ'c hφM hφ'M hR hφR hF z).fderiv]
  simp


include hφ'c hφ'M hR hφR in
/-- **Per-translate hyperbolic gradient bound.**  For `v ∈ {1, i}` with
`|Im z ∂_v U| ≤ K` on the support, `‖Im z · dT_B(z)[v]‖ ≤ K ∫ |φ'(u(z,Bz'))| ‖F(z')‖`. -/
theorem norm_im_ppTermcDeriv_le {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) (z : ℍ)
    (B : SL(2, ℤ)) (v : ℂ) {K : ℝ}
    (hv : ∀ w : ℍ, pairUc (z : ℂ) w ≤ R → |z.im * pairUcDeriv (z : ℂ) w v| ≤ K) :
    ‖((z.im : ℝ) : ℂ) • ppTermcDeriv φ F B (z : ℂ) v‖ ≤
      K * ∫ z' in fd, |deriv φ (pairU z (B • z'))| * ‖F z'‖ := by
  have hz : 0 < (z : ℂ).im := z.im_pos
  have hF1 : Integrable (fun z' => deckRho N B (F z')) cellMeasure :=
    (deckRho N B).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (hF.integrable one_le_two)
  have hM' : 0 ≤ M' := (abs_nonneg _).trans (hφ'M 0)
  have hU : Continuous (fun z' : ℍ => pairUc (z : ℂ) (B • z')) :=
    (continuous_pairUc_right hz).comp (continuous_smul_int B)
  have hint : Integrable (fun z' => (deriv φ (pairUc (z : ℂ) (B • z')) •
      pairUcDeriv (z : ℂ) (B • z')).smulRight (deckRho N B (F z'))) cellMeasure := by
    have hre : Continuous (fun w : ℍ => w.re) := UpperHalfPlane.continuous_re
    have him : Continuous (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im
    have ha : Continuous (fun w : ℍ => ((z : ℂ).re - w.re) / (2 * (z : ℂ).im * w.im)) := by
      refine Continuous.div (by fun_prop) (by fun_prop) fun w => ?_
      have := w.im_pos; positivity
    have hb : Continuous (fun w : ℍ =>
        ((z : ℂ).im ^ 2 - w.im ^ 2 - ((z : ℂ).re - w.re) ^ 2) / (4 * (z : ℂ).im ^ 2 * w.im)) := by
      refine Continuous.div (by fun_prop) (by fun_prop) fun w => ?_
      have := w.im_pos; positivity
    have hD : Continuous (fun w : ℍ => pairUcDeriv (z : ℂ) w) :=
      (ha.smul continuous_const).add (hb.smul continuous_const)
    have hk : Continuous (fun z' : ℍ => deriv φ (pairUc (z : ℂ) (B • z')) •
        pairUcDeriv (z : ℂ) (B • z')) := (hφ'c.comp hU).smul (hD.comp (continuous_smul_int B))
    refine Integrable.mono' (hF1.norm.const_mul (M' * ((5 * R + 3) / (z : ℂ).im))) ?_
      (Eventually.of_forall fun z' => ?_)
    · exact (ContinuousLinearMap.smulRightL ℝ ℂ (DeckSpace N)).continuous₂.comp_aestronglyMeasurable₂
        hk.aestronglyMeasurable hF1.1
    · rw [ContinuousLinearMap.norm_smulRight_apply]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [norm_smul, Real.norm_eq_abs]
      by_cases hU' : pairUc (z : ℂ) (B • z') ≤ R
      · exact mul_le_mul (hφ'M _) (norm_pairUcDeriv_le hz hU') (norm_nonneg _) hM'
      · rw [deriv_eq_zero_of_kernelSupport hφR (lt_of_not_ge hU'), abs_zero, zero_mul]
        positivity
  unfold ppTermcDeriv
  rw [ContinuousLinearMap.integral_apply hint, ← integral_smul]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun z' => norm_nonneg _) ?_
    (Eventually.of_forall fun z' => ?_)
  · exact ((integrable_ppKernel_mul_norm (φ := deriv φ) hφ'c hφ'M hF z B).const_mul K)
  · simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [pairUc_ofComplex hz, UpperHalfPlane.ofComplex_apply]
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      LinearIsometryEquiv.norm_map]
    by_cases hU' : pairU z (B • z') ≤ R
    · have h1 := hv (B • z') (by rwa [pairUc_ofComplex hz, UpperHalfPlane.ofComplex_apply])
      calc |z.im| * (|deriv φ (pairU z (B • z')) * pairUcDeriv (z : ℂ) (B • z') v| * ‖F z'‖)
          = |deriv φ (pairU z (B • z'))| * |z.im * pairUcDeriv (z : ℂ) (B • z') v| * ‖F z'‖ := by
            rw [abs_mul, abs_mul]; ring
        _ ≤ |deriv φ (pairU z (B • z'))| * K * ‖F z'‖ := by gcongr
        _ = K * (|deriv φ (pairU z (B • z'))| * ‖F z'‖) := by ring
    · rw [deriv_eq_zero_of_kernelSupport hφR (lt_of_not_ge hU')]
      simp


omit hφd hφ'c hφM hφ'M hR in
include hφR in
theorem kernelSupport_abs_deriv : KernelSupport (fun u => |deriv φ u|) R := fun u hu => by
  simp [deriv_eq_zero_of_kernelSupport hφR hu]

omit hφd hφ'c hφM hφ'M hR in
include hφR in
/-- The two finite sums over the near translates agree for the derivative kernel. -/
theorem sum_nearSet_deriv_eq {F : ℍ → DeckSpace N} (z : ℍ) :
    ∑ B ∈ ppNearSet z (2 * (1 + 2 * R)), ∫ z' in fd, |deriv φ (pairU z (B • z'))| * ‖F z'‖ =
      ∑ B ∈ ppNearSet z R, ∫ z' in fd, |deriv φ (pairU z (B • z'))| * ‖F z'‖ := by
  have hR' : R ≤ 2 * (1 + 2 * R) ∨ R < 0 := by
    by_cases h : R < 0
    · exact Or.inr h
    · left; push Not at h; linarith
  symm
  refine Finset.sum_subset (fun B hB => ?_) (fun B _ hB => ?_)
  · rcases hR' with hR' | hR'
    · simp only [ppNearSet, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hB ⊢
      obtain ⟨z', hz', h⟩ := hB
      exact ⟨z', hz', h.trans hR'⟩
    · simp only [ppNearSet, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hB
      obtain ⟨z', -, h⟩ := hB
      exact absurd ((pairU_nonneg _ _).trans h) (not_le.2 hR')
  · refine setIntegral_eq_zero_of_forall_eq_zero fun z' hz' => ?_
    have : R < pairU z (B • z') := by
      by_contra h; push Not at h
      exact hB (by simpa [ppNearSet] using ⟨z', hz', h⟩)
    rw [deriv_eq_zero_of_kernelSupport hφR this, abs_zero, zero_mul]

include hφd hφ'c hφM hφ'M hR hφR in
/-- **Pointwise gradient bound**: `‖y ∂ₓ(L_φ F)(z)‖ ≤ (2R+1) ‖L_{|φ'|} F♯(z)‖`. -/
theorem norm_hypGradX_ppApply_le {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) (z : ℍ) :
    ‖MaassFiniteDeckDirichlet.hypGradX (ppApply φ F) z‖ ≤
      (2 * R + 1) * ‖ppApply (fun u => |deriv φ u|) (normLift F) z‖ := by
  rw [norm_ppApply_normLift (hφ'c.abs) (fun u => by rw [abs_abs]; exact hφ'M u)
    (kernelSupport_abs_deriv hφR) (fun u => abs_nonneg _) hF z]
  unfold MaassFiniteDeckDirichlet.hypGradX
  rw [chartDeriv_ppApply hφd hφ'c hφM hφ'M hR hφR hF z 1, smul_smul, mul_comm, ← smul_smul,
    Finset.smul_sum, norm_smul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf, ← sum_nearSet_deriv_eq hφR z]
  have hbound : ∀ B ∈ ppNearSet z (2 * (1 + 2 * R)),
      ‖((z.im : ℝ) : ℂ) • ppTermcDeriv φ F B (z : ℂ) 1‖ ≤
        (2 * R + 1) * ∫ z' in fd, |deriv φ (pairU z (B • z'))| * ‖F z'‖ := fun B _ =>
    norm_im_ppTermcDeriv_le hφ'c hφ'M hR hφR hF z B 1 fun w hw =>
      (pairUcDeriv_bounds z.im_pos hw).1
  calc 1 / 2 * ‖∑ B ∈ ppNearSet z (2 * (1 + 2 * R)), ((z.im : ℝ) : ℂ) • ppTermcDeriv φ F B (z : ℂ) 1‖
      ≤ 1 / 2 * ∑ B ∈ ppNearSet z (2 * (1 + 2 * R)),
          (2 * R + 1) * ∫ z' in fd, |deriv φ (pairU z (B • z'))| * ‖F z'‖ :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hbound)) (by norm_num)
    _ = (2 * R + 1) * (1 / 2 * ∑ B ∈ ppNearSet z (2 * (1 + 2 * R)),
          ∫ z' in fd, |deriv φ (pairU z (B • z'))| * ‖F z'‖) := by
        rw [← Finset.mul_sum]; ring

include hφd hφ'c hφM hφ'M hR hφR in
/-- **Pointwise gradient bound**: `‖y ∂ᵧ(L_φ F)(z)‖ ≤ (3R+2) ‖L_{|φ'|} F♯(z)‖`. -/
theorem norm_hypGradY_ppApply_le {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) (z : ℍ) :
    ‖MaassFiniteDeckDirichlet.hypGradY (ppApply φ F) z‖ ≤
      (3 * R + 2) * ‖ppApply (fun u => |deriv φ u|) (normLift F) z‖ := by
  rw [norm_ppApply_normLift (hφ'c.abs) (fun u => by rw [abs_abs]; exact hφ'M u)
    (kernelSupport_abs_deriv hφR) (fun u => abs_nonneg _) hF z]
  unfold MaassFiniteDeckDirichlet.hypGradY
  rw [chartDeriv_ppApply hφd hφ'c hφM hφ'M hR hφR hF z Complex.I, smul_smul, mul_comm, ← smul_smul,
    Finset.smul_sum, norm_smul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf, ← sum_nearSet_deriv_eq hφR z]
  have hbound : ∀ B ∈ ppNearSet z (2 * (1 + 2 * R)),
      ‖((z.im : ℝ) : ℂ) • ppTermcDeriv φ F B (z : ℂ) Complex.I‖ ≤
        (3 * R + 2) * ∫ z' in fd, |deriv φ (pairU z (B • z'))| * ‖F z'‖ := fun B _ =>
    norm_im_ppTermcDeriv_le hφ'c hφ'M hR hφR hF z B Complex.I fun w hw =>
      (pairUcDeriv_bounds z.im_pos hw).2
  calc 1 / 2 * ‖∑ B ∈ ppNearSet z (2 * (1 + 2 * R)),
        ((z.im : ℝ) : ℂ) • ppTermcDeriv φ F B (z : ℂ) Complex.I‖
      ≤ 1 / 2 * ∑ B ∈ ppNearSet z (2 * (1 + 2 * R)),
          (3 * R + 2) * ∫ z' in fd, |deriv φ (pairU z (B • z'))| * ‖F z'‖ :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hbound)) (by norm_num)
    _ = (3 * R + 2) * (1 / 2 * ∑ B ∈ ppNearSet z (2 * (1 + 2 * R)),
          ∫ z' in fd, |deriv φ (pairU z (B • z'))| * ‖F z'‖) := by
        rw [← Finset.mul_sum]; ring

include hφd hφ'c hφM hφ'M hR hφR in
theorem memLp_hypGradX_ppApply {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) :
    MemLp (MaassFiniteDeckDirichlet.hypGradX (ppApply φ F)) 2 cellMeasure :=
  (memLp_ppApply (φ := fun u => |deriv φ u|) hφ'c.abs (fun u => by rw [abs_abs]; exact hφ'M u) hR
      (kernelSupport_abs_deriv hφR) (memLp_normLift hF)).of_le_mul
    (continuous_hypGradX_vec (isChartC1_ppApply hφd hφ'c hφM hφ'M hR hφR hF)).aestronglyMeasurable
    (Eventually.of_forall fun z => norm_hypGradX_ppApply_le hφd hφ'c hφM hφ'M hR hφR hF z)

include hφd hφ'c hφM hφ'M hR hφR in
theorem memLp_hypGradY_ppApply {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) :
    MemLp (MaassFiniteDeckDirichlet.hypGradY (ppApply φ F)) 2 cellMeasure :=
  (memLp_ppApply (φ := fun u => |deriv φ u|) hφ'c.abs (fun u => by rw [abs_abs]; exact hφ'M u) hR
      (kernelSupport_abs_deriv hφR) (memLp_normLift hF)).of_le_mul
    (continuous_hypGradY_vec (isChartC1_ppApply hφd hφ'c hφM hφ'M hR hφR hF)).aestronglyMeasurable
    (Eventually.of_forall fun z => norm_hypGradY_ppApply_le hφd hφ'c hφM hφ'M hR hφR hF z)

include hφd hφ'c hφM hφ'M hR hφR in
/-- **`L_φ` maps finite-deck `L²` into the Dirichlet pre-domain.** -/
theorem ppApply_mem_formPreDomain {F : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure) :
    ppApply φ F ∈ formPreDomain N :=
  ⟨isChartC1_ppApply hφd hφ'c hφM hφ'M hR hφR hF, fun A z => ppApply_smul_point hφR F A z,
    memLp_ppApply hφd.continuous hφM hR hφR hF, memLp_hypGradX_ppApply hφd hφ'c hφM hφ'M hR hφR hF,
    memLp_hypGradY_ppApply hφd hφ'c hφM hφ'M hR hφR hF⟩

end Grad

end

end GaloisForLFunctions.RHTower.DeckPointPair
