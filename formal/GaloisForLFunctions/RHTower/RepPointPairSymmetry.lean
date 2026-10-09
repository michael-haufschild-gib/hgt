import GaloisForLFunctions.RHTower.RepPointPairOperator

/-!
# Symmetry of the twisted point-pair operators

The sesquilinear form of `L_φ` is `⟪F, L_φ G⟫ = ½ Σ_B ∫_𝒟 ∫_𝒟 φ(u(z,Bz')) ⟪F(z), ρ(B) G(z')⟫`
(`inner_ppL2`), the exchange of the translate sum and the outer integral being justified by the
arithmetic–geometric Schur bound (`tsum_lintegral_ppForm_lt_top`).  Swapping `z ↔ z'` and `B ↔ B⁻¹`
conjugates the kernel (`ppForm_swap`: `u(z',B⁻¹z) = u(z,Bz')`, `ρ(B⁻¹) = ρ(B)⁻¹`), so for real `φ` the
operator is symmetric (`ppL2_isSymmetric`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

variable (ρ) in
/-- The kernel of the sesquilinear form of `L_φ` against one translate. -/
def ppForm (φ : ℝ → ℝ) (f g : ℍ → EuclideanSpace ℂ ι) (B : SL(2, ℤ)) (z z' : ℍ) : ℂ :=
  ((φ (pairU z (B • z')) : ℝ) : ℂ) * ⟪f z, ρ B (g z')⟫_ℂ

theorem norm_ppForm_le (φ : ℝ → ℝ) (f g : ℍ → EuclideanSpace ℂ ι) (B : SL(2, ℤ)) (z z' : ℍ) :
    ‖ppForm ρ φ f g B z z'‖ ≤ |φ (pairU z (B • z'))| * (‖f z‖ * ‖g z'‖) := by
  unfold ppForm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
  rw [LinearIsometryEquiv.norm_map]

theorem rho_inv (B : SL(2, ℤ)) : ρ B⁻¹ = (ρ B).symm := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- `ppForm` along the swap `(z, z') ↦ (z', z)` and `B ↦ B⁻¹` is the conjugate of the reversed form. -/
theorem ppForm_swap (φ : ℝ → ℝ) (f g : ℍ → EuclideanSpace ℂ ι) (B : SL(2, ℤ)) (z z' : ℍ) :
    ppForm ρ φ g f B⁻¹ z' z = (starRingEnd ℂ) (ppForm ρ φ f g B z z') := by
  unfold ppForm
  rw [map_mul, Complex.conj_ofReal, inner_conj_symm]
  have hu : pairU z' (B⁻¹ • z) = pairU z (B • z') := by
    rw [pairU_comm, ← pairU_smul_int B, smul_inv_smul]
  rw [hu]
  congr 1
  rw [rho_inv, ← LinearIsometryEquiv.inner_map_map (ρ B), LinearIsometryEquiv.apply_symm_apply]

section Form

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M) (hR : 0 ≤ R)
  (hφR : KernelSupport φ R)
include hφc hφM

omit hφM in
theorem continuous_kernel_joint (B : SL(2, ℤ)) :
    Continuous (fun p : ℍ × ℍ => ((φ (pairU p.1 (B • p.2)) : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (hφc.comp (continuous_pairU.comp
    (continuous_fst.prodMk ((continuous_smul_int B).comp continuous_snd))))

theorem integrable_ppForm_right {f g : ℍ → EuclideanSpace ℂ ι} (hg : MemLp g 2 cellMeasure) (z : ℍ)
    (B : SL(2, ℤ)) : Integrable (fun z' => ppForm ρ φ f g B z z') cellMeasure := by
  have hmeas : AEStronglyMeasurable (fun z' => ppForm ρ φ f g B z z') cellMeasure := by
    unfold ppForm
    refine ((Complex.continuous_ofReal.comp (hφc.comp ((continuous_pairU_right z).comp
      (continuous_smul_int B)))).aestronglyMeasurable).mul ?_
    exact (aestronglyMeasurable_const.inner
      ((ρ B).continuous.comp_aestronglyMeasurable hg.1))
  refine Integrable.mono' (((hg.integrable one_le_two).norm).const_mul (M * ‖f z‖)) hmeas
    (Eventually.of_forall fun z' => ?_)
  refine (norm_ppForm_le φ f g B z z').trans ?_
  have := hφM (pairU z (B • z'))
  calc |φ (pairU z (B • z'))| * (‖f z‖ * ‖g z'‖) ≤ M * (‖f z‖ * ‖g z'‖) :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = M * ‖f z‖ * ‖g z'‖ := by ring

omit hφc hφM in
/-- The inner product against one translate is the integral of the form kernel. -/
theorem inner_ppTerm {f g : ℍ → EuclideanSpace ℂ ι} (z : ℍ)
    (B : SL(2, ℤ)) (hint : Integrable (fun z' => ((φ (pairU z (B • z')) : ℝ) : ℂ) •
      ρ B (g z')) cellMeasure) :
    ⟪f z, ppTerm ρ φ g z B⟫_ℂ = ∫ z' in fd, ppForm ρ φ f g B z z' := by
  unfold ppTerm
  rw [← integral_inner hint]
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  simp only [ppForm, inner_smul_right]

theorem integrable_ppTerm_integrand {g : ℍ → EuclideanSpace ℂ ι} (hg : MemLp g 2 cellMeasure) (z : ℍ)
    (B : SL(2, ℤ)) : Integrable (fun z' => ((φ (pairU z (B • z')) : ℝ) : ℂ) •
      ρ B (g z')) cellMeasure := by
  have hg1 : Integrable (fun z' => ρ B (g z')) cellMeasure :=
    (ρ B).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (hg.integrable one_le_two)
  refine hg1.bdd_smul M (Complex.continuous_ofReal.comp (hφc.comp ((continuous_pairU_right z).comp
    (continuous_smul_int B)))).aestronglyMeasurable (Eventually.of_forall fun z' => ?_)
  simp only [Function.comp_apply]
  rw [Complex.norm_real, Real.norm_eq_abs]; exact hφM _

/-- **Pointwise form identity.** `⟪f(z), (L_φ g)(z)⟫ = ½ Σ_B ∫_𝒟 ppForm B z z'`. -/
theorem inner_ppApply {f g : ℍ → EuclideanSpace ℂ ι} (hφR : KernelSupport φ R)
    (hg : MemLp g 2 cellMeasure) (z : ℍ) :
    ⟪f z, ppApply ρ φ g z⟫_ℂ = (1 / 2 : ℂ) * ∑' B : SL(2, ℤ), ∫ z' in fd, ppForm ρ φ f g B z z' := by
  unfold ppApply
  rw [inner_smul_right, tsum_ppTerm_eq_sum hφR, inner_sum]
  congr 1
  rw [tsum_eq_sum (s := ppNearSet z R)]
  · exact Finset.sum_congr rfl fun B _ =>
      inner_ppTerm z B (integrable_ppTerm_integrand hφc hφM hg z B)
  · intro B hB
    refine setIntegral_eq_zero_of_forall_eq_zero fun z' hz' => ?_
    have : R < pairU z (B • z') := by
      by_contra h; push Not at h
      exact hB (by simpa [ppNearSet] using ⟨z', hz', h⟩)
    simp only [ppForm]
    rw [hφR _ this]; simp

omit hφc hφM in
theorem ofReal_mul_le_half (a b : ℝ) :
    2 * ENNReal.ofReal (a * b) ≤ ENNReal.ofReal (a ^ 2) + ENNReal.ofReal (b ^ 2) := by
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a - b)])

/-- **The double-kernel mass is finite.** -/
theorem tsum_lintegral_ppForm_lt_top {f g : ℍ → EuclideanSpace ℂ ι} (hR : 0 ≤ R) (hφR : KernelSupport φ R)
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 cellMeasure) (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 cellMeasure) :
    ∑' B : SL(2, ℤ), ∫⁻ z in fd, ‖∫ z' in fd, ppForm ρ φ f g B z z'‖ₑ ≠ ∞ := by
  have hm := kernelMass_lt_top hR hφM hφR
  have hFf : ∫⁻ z in fd, ENNReal.ofReal (‖f z‖ ^ 2) < ∞ := by
    rw [← eLpNorm_two_sq_ofReal]; exact ENNReal.pow_lt_top hf.2
  have hFg : ∫⁻ z in fd, ENNReal.ofReal (‖g z‖ ^ 2) < ∞ := by
    rw [← eLpNorm_two_sq_ofReal]; exact ENNReal.pow_lt_top hg.2
  have hf2 : Measurable (fun z : ℍ => ENNReal.ofReal (‖f z‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hfm.measurable.norm).pow_const 2)
  have hg2 : Measurable (fun z : ℍ => ENNReal.ofReal (‖g z‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hgm.measurable.norm).pow_const 2)
  have hk : ∀ B : SL(2, ℤ), Measurable (fun p : ℍ × ℍ => ENNReal.ofReal |φ (pairU p.1 (B • p.2))|) :=
    fun B => (ENNReal.continuous_ofReal.comp ((hφc.comp (continuous_pairU.comp
      (continuous_fst.prodMk ((continuous_smul_int B).comp continuous_snd)))).abs)).measurable
  -- pointwise
  have hpt : ∀ (B : SL(2, ℤ)) (z : ℍ), 2 * ‖∫ z' in fd, ppForm ρ φ f g B z z'‖ₑ ≤
      (∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| * ENNReal.ofReal (‖f z‖ ^ 2)) +
      ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| * ENNReal.ofReal (‖g z'‖ ^ 2) := by
    intro B z
    have hmz : Measurable (fun z' : ℍ => ENNReal.ofReal |φ (pairU z (B • z'))| *
        ENNReal.ofReal (‖f z‖ ^ 2)) :=
      ((hk B).comp (measurable_const.prodMk measurable_id)).mul measurable_const
    rw [← lintegral_add_left hmz]
    refine (mul_le_mul_right (enorm_integral_le_lintegral_enorm _) 2).trans ?_
    rw [← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
    refine lintegral_mono fun z' => ?_
    have h1 : ‖ppForm ρ φ f g B z z'‖ₑ ≤ ENNReal.ofReal |φ (pairU z (B • z'))| *
        ENNReal.ofReal (‖f z‖ * ‖g z'‖) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_ppForm_le φ f g B z z')
    calc 2 * ‖ppForm ρ φ f g B z z'‖ₑ ≤ 2 * (ENNReal.ofReal |φ (pairU z (B • z'))| *
          ENNReal.ofReal (‖f z‖ * ‖g z'‖)) := mul_le_mul_right h1 2
      _ = ENNReal.ofReal |φ (pairU z (B • z'))| * (2 * ENNReal.ofReal (‖f z‖ * ‖g z'‖)) := by ring
      _ ≤ ENNReal.ofReal |φ (pairU z (B • z'))| * (ENNReal.ofReal (‖f z‖ ^ 2) +
          ENNReal.ofReal (‖g z'‖ ^ 2)) := mul_le_mul_right (ofReal_mul_le_half _ _) _
      _ = _ := by ring
  have hA : ∀ B : SL(2, ℤ), Measurable (fun z : ℍ => ∫⁻ z' in fd,
      ENNReal.ofReal |φ (pairU z (B • z'))| * ENNReal.ofReal (‖f z‖ ^ 2)) := fun B =>
    (((hk B).mul (hf2.comp measurable_fst)).lintegral_prod_right')
  have hG : ∀ B : SL(2, ℤ), Measurable (fun z : ℍ => ∫⁻ z' in fd,
      ENNReal.ofReal |φ (pairU z (B • z'))| * ENNReal.ofReal (‖g z'‖ ^ 2)) := fun B =>
    (((hk B).mul (hg2.comp measurable_snd)).lintegral_prod_right')
  have hle : ∑' B : SL(2, ℤ), ∫⁻ z in fd, ‖∫ z' in fd, ppForm ρ φ f g B z z'‖ₑ ≤
      ∑' B : SL(2, ℤ), ∫⁻ z in fd, ((∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| *
        ENNReal.ofReal (‖f z‖ ^ 2)) + ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| *
        ENNReal.ofReal (‖g z'‖ ^ 2)) := by
    refine ENNReal.tsum_le_tsum fun B => lintegral_mono fun z => ?_
    refine le_trans ?_ (hpt B z)
    exact le_mul_of_one_le_left (by positivity) (by norm_num)
  refine ne_top_of_le_ne_top ?_ hle
  simp_rw [lintegral_add_left (hA _), ENNReal.tsum_add]
  refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
  · rw [← lintegral_tsum fun B => (hA B).aemeasurable]
    have e : ∀ z : ℍ, ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| *
        ENNReal.ofReal (‖f z‖ ^ 2) = 2 * ppKernelMass φ * ENNReal.ofReal (‖f z‖ ^ 2) := by
      intro z
      calc ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| *
            ENNReal.ofReal (‖f z‖ ^ 2)
          = ∑' B : SL(2, ℤ), (∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))|) *
            ENNReal.ofReal (‖f z‖ ^ 2) :=
            tsum_congr fun B => lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
        _ = 2 * ppKernelMass φ * ENNReal.ofReal (‖f z‖ ^ 2) := by
            rw [ENNReal.tsum_mul_right, tsum_kernel_fd]
    simp_rw [e]
    rw [lintegral_const_mul _ hf2]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hm.ne) hFf.ne
  · rw [← lintegral_tsum fun B => (hG B).aemeasurable, lintegral_tsum_kernel_mul hφc hg2]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hm.ne) hFg.ne

omit hφM in
theorem stronglyMeasurable_ppForm_joint {f g : ℍ → EuclideanSpace ℂ ι} (hfm : StronglyMeasurable f)
    (hgm : StronglyMeasurable g) (B : SL(2, ℤ)) :
    StronglyMeasurable (fun p : ℍ × ℍ => ppForm ρ φ f g B p.1 p.2) := by
  unfold ppForm
  refine ((continuous_kernel_joint hφc B).stronglyMeasurable).mul ?_
  exact (hfm.comp_measurable measurable_fst).inner
    (((ρ B).continuous.comp_stronglyMeasurable (hgm.comp_measurable measurable_snd)))

/-- **The kernel formula for the sesquilinear form of `L_φ`.** -/
theorem inner_ppL2 (hR : 0 ≤ R) (hφR : KernelSupport φ R) (F G : RepL2 ι) :
    ⟪F, ppL2 ρ hφc hφM hR hφR G⟫_ℂ = (1 / 2 : ℂ) * ∑' B : SL(2, ℤ),
      ∫ z in fd, ∫ z' in fd, ppForm ρ φ (F : ℍ → EuclideanSpace ℂ ι) G B z z' := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : ∫ z, ⟪(F : ℍ → EuclideanSpace ℂ ι) z, (ppL2 ρ hφc hφM hR hφR G : ℍ → EuclideanSpace ℂ ι) z⟫_ℂ
      ∂cellMeasure = ∫ z, ⟪(F : ℍ → EuclideanSpace ℂ ι) z, ppApply ρ φ G z⟫_ℂ ∂cellMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [ppL2_coeFn hφc hφM hR hφR G] with z hz
    rw [hz]
  rw [h1]
  simp_rw [inner_ppApply hφc hφM hφR (Lp.memLp G)]
  rw [integral_const_mul]
  congr 1
  refine integral_tsum (fun B => ?_) ?_
  · exact ((stronglyMeasurable_ppForm_joint hφc (Lp.stronglyMeasurable F)
      (Lp.stronglyMeasurable G) B).integral_prod_right').aestronglyMeasurable
  · exact tsum_lintegral_ppForm_lt_top hφc hφM hR hφR (Lp.stronglyMeasurable F) (Lp.memLp F)
      (Lp.stronglyMeasurable G) (Lp.memLp G)

/-- **`L_φ` is symmetric.** -/
theorem ppL2_inner_symm (hR : 0 ≤ R) (hφR : KernelSupport φ R) (F G : RepL2 ι) :
    ⟪ppL2 ρ hφc hφM hR hφR F, G⟫_ℂ = ⟪F, ppL2 ρ hφc hφM hR hφR G⟫_ℂ := by
  rw [← inner_conj_symm, inner_ppL2 hφc hφM hR hφR G F, inner_ppL2 hφc hφM hR hφR F G, map_mul,
    Complex.conj_tsum]
  congr 1
  · simp only [one_div, map_inv₀]
    exact congrArg _ (map_ofNat (starRingEnd ℂ) 2)
  have key : ∀ B : SL(2, ℤ), (starRingEnd ℂ) (∫ z in fd, ∫ z' in fd,
      ppForm ρ φ (G : ℍ → EuclideanSpace ℂ ι) F B z z') =
      ∫ z in fd, ∫ z' in fd, ppForm ρ φ (F : ℍ → EuclideanSpace ℂ ι) G B⁻¹ z z' := by
    intro B
    have hint : Integrable (Function.uncurry fun z z' =>
        ppForm ρ φ (F : ℍ → EuclideanSpace ℂ ι) G B⁻¹ z' z) (cellMeasure.prod cellMeasure) := by
      have hFG : Integrable (fun p : ℍ × ℍ => ((M : ℝ) : ℂ) * (‖(G : ℍ → EuclideanSpace ℂ ι) p.1‖ : ℂ) *
          (‖(F : ℍ → EuclideanSpace ℂ ι) p.2‖ : ℂ)) (cellMeasure.prod cellMeasure) := by
        have hG1 : Integrable (fun z => ((M : ℝ) : ℂ) * (‖(G : ℍ → EuclideanSpace ℂ ι) z‖ : ℂ))
            cellMeasure := ((((Lp.memLp G).integrable one_le_two).norm).ofReal).const_mul _
        have hF1 : Integrable (fun z => (‖(F : ℍ → EuclideanSpace ℂ ι) z‖ : ℂ)) cellMeasure :=
          (((Lp.memLp F).integrable one_le_two).norm).ofReal
        exact hG1.mul_prod hF1
      refine hFG.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
      · exact ((stronglyMeasurable_ppForm_joint hφc (Lp.stronglyMeasurable F)
          (Lp.stronglyMeasurable G) B⁻¹).comp_measurable measurable_swap).aestronglyMeasurable
      · simp only [Function.uncurry]
        refine (norm_ppForm_le φ _ _ B⁻¹ p.2 p.1).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (norm_nonneg _)]
        have hM := hφM (pairU p.2 (B⁻¹ • p.1))
        have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
        rw [Real.norm_of_nonneg hM0]
        calc |φ (pairU p.2 (B⁻¹ • p.1))| * (‖(F : ℍ → EuclideanSpace ℂ ι) p.2‖ *
              ‖(G : ℍ → EuclideanSpace ℂ ι) p.1‖)
            ≤ M * (‖(F : ℍ → EuclideanSpace ℂ ι) p.2‖ * ‖(G : ℍ → EuclideanSpace ℂ ι) p.1‖) :=
              mul_le_mul_of_nonneg_right hM (by positivity)
          _ = M * ‖(G : ℍ → EuclideanSpace ℂ ι) p.1‖ * ‖(F : ℍ → EuclideanSpace ℂ ι) p.2‖ := by ring
    calc (starRingEnd ℂ) (∫ z in fd, ∫ z' in fd, ppForm ρ φ (G : ℍ → EuclideanSpace ℂ ι) F B z z')
        = ∫ z in fd, ∫ z' in fd, (starRingEnd ℂ) (ppForm ρ φ (G : ℍ → EuclideanSpace ℂ ι) F B z z') := by
          rw [← integral_conj]
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          exact integral_conj.symm
      _ = ∫ z in fd, ∫ z' in fd, ppForm ρ φ (F : ℍ → EuclideanSpace ℂ ι) G B⁻¹ z' z := by
          simp_rw [ppForm_swap]
      _ = ∫ z' in fd, ∫ z in fd, ppForm ρ φ (F : ℍ → EuclideanSpace ℂ ι) G B⁻¹ z' z :=
          integral_integral_swap hint
  rw [tsum_congr key]
  exact (Equiv.inv (SL(2, ℤ))).tsum_eq
    (fun B => ∫ z in fd, ∫ z' in fd, ppForm ρ φ (F : ℍ → EuclideanSpace ℂ ι) G B z z')

theorem ppL2_isSymmetric (hR : 0 ≤ R) (hφR : KernelSupport φ R) :
    ((ppL2 ρ hφc hφM hR hφR : RepL2 ι →L[ℂ] RepL2 ι) :
      RepL2 ι →ₗ[ℂ] RepL2 ι).IsSymmetric :=
  fun F G => ppL2_inner_symm hφc hφM hR hφR F G

end Form

end

end GaloisForLFunctions.RHTower.RepPointPair
