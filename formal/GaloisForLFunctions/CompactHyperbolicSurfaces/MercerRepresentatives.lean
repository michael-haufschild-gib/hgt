import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventSpectrum

/-!
# Continuous eigenfunctions of the difference operator

For `1 < a < b` the operator `P = T_a − T_b` has the continuous, bounded, `Γ`-invariant, symmetric
kernel `K(z, w) = Σ_γ D_{a,b}(u(z, γw))` (`diffKer`).  On the spectral family of `T_a`,
`P e_j = ν_j e_j` with `ν_j = 1/(λ_j + a(a−1)) − 1/(λ_j + b(b−1)) > 0` (`diffOp_specVec`), and `P`
kills every vector orthogonal to all `e_j` (`diffOp_eq_zero_of_orthogonal`).

The functions `z ↦ ∫_F K(z, w) f(w) dw` are continuous and `Γ`-invariant (`continuous_kerApply`);
a continuous invariant function vanishing almost everywhere on `F` vanishes identically
(`eq_zero_of_ae_eq_zero`).  Hence `ẽ_j = ν_j⁻¹ ∫_F K(·, w) e_j(w) dw` is a continuous invariant
representative of `e_j` (`ae_eq_specRep`), and `∫_F K(z, w) f(w) dw = 0` for every `z` when `f` is
orthogonal to the family (`kerApply_eq_zero_of_orthogonal`).
-/

open MeasureTheory Set Filter UpperHalfPlane Real Metric
open scoped ENNReal MatrixGroups Pointwise InnerProductSpace

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.SchurKernel

noncomputable section

namespace CompactQuotient

variable (X : CompactQuotient) {a b : ℝ} (ha : 1 < a) (hab : a < b)

/-- The continuous kernel `K(z, w) = Σ_γ D_{a,b}(u(z, γw))` of `T_a − T_b`. -/
def diffKer (a b : ℝ) (z w : ℍ) : ℝ := autR X.Γ (diffKernel a b) z w

include ha hab

theorem exists_diffKernel_bound' : ∃ C : ℝ, 0 ≤ C ∧
    ∀ u, 0 ≤ u → |diffKernel a b u| ≤ C * (1 + u) ^ (-a) := by
  obtain ⟨C, hC0, hC⟩ := exists_diffKernel_le ha hab.le
  refine ⟨C, hC0, fun u hu => ?_⟩
  rw [abs_of_nonneg (diffKernel_nonneg hab.le u)]
  exact hC u hu

theorem summable_diffKer (z w : ℍ) :
    Summable fun γ : X.Γ => diffKernel a b (pairU z ((γ : SL(2, ℝ)) • w)) := by
  obtain ⟨C, hC0, hC⟩ := exists_diffKernel_bound' ha hab
  refine ((X.cocompactFree.summable_rpow ha z w).mul_left C).of_nonneg_of_le
    (fun _ => diffKernel_nonneg hab.le _) fun γ => ?_
  have := hC _ (pairU_nonneg z ((γ : SL(2, ℝ)) • w))
  rwa [abs_of_nonneg (diffKernel_nonneg hab.le _)] at this

theorem autK_diffProfile_eq (z w : ℍ) :
    autK X.Γ (diffProfile a b) z w = ENNReal.ofReal (X.diffKer a b z w) :=
  (ENNReal.ofReal_tsum_of_nonneg (fun _ => diffKernel_nonneg hab.le _)
    (X.summable_diffKer ha hab z w)).symm

omit ha in
theorem diffKer_nonneg (z w : ℍ) : 0 ≤ X.diffKer a b z w :=
  tsum_nonneg fun _ => diffKernel_nonneg hab.le _

theorem diffOp_toFun (z w : ℍ) :
    (X.profileKernel (measurable_diffProfile ha hab) (lintegral_diffProfile_mass_lt_top ha hab)).toFun
      z w = ((X.diffKer a b z w : ℝ) : ℂ) := by
  rw [profileKernel_toFun, X.autK_diffProfile_eq ha hab, ENNReal.toReal_ofReal
    (X.diffKer_nonneg hab z w)]

theorem continuous_diffKer : Continuous fun p : ℍ × ℍ => X.diffKer a b p.1 p.2 := by
  obtain ⟨C, hC0, hC⟩ := exists_diffKernel_bound' ha hab
  exact X.cocompactFree.continuous_autR (continuous_diffKernel (by linarith) hab.le) ha hC

theorem exists_diffKer_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ z w : ℍ, X.diffKer a b z w ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_diffKernel_le ha hab.le
  obtain ⟨M, hM, hle⟩ := X.cocompactFree.exists_autK_le ha
  refine ⟨(ENNReal.ofReal C * M).toReal, ENNReal.toReal_nonneg, fun z w => ?_⟩
  have h := hle (k := diffProfile a b) (C := C) (fun u hu => ENNReal.ofReal_le_ofReal (hC u hu)) z w
  rw [X.autK_diffProfile_eq ha hab] at h
  exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM).ne).mp h

theorem diffKer_smul_left (γ : X.Γ) (z w : ℍ) :
    X.diffKer a b ((γ : SL(2, ℝ)) • z) w = X.diffKer a b z w := by
  have h := autK_smul_left (Γ := X.Γ) (diffProfile a b) z w γ
  rw [X.autK_diffProfile_eq ha hab, X.autK_diffProfile_eq ha hab] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (X.diffKer_nonneg hab _ _)
    (X.diffKer_nonneg hab _ _)).mp h

theorem diffKer_smul_right (γ : X.Γ) (z w : ℍ) :
    X.diffKer a b z ((γ : SL(2, ℝ)) • w) = X.diffKer a b z w := by
  have h := autK_smul_right (Γ := X.Γ) (diffProfile a b) z w γ
  rw [X.autK_diffProfile_eq ha hab, X.autK_diffProfile_eq ha hab] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (X.diffKer_nonneg hab _ _)
    (X.diffKer_nonneg hab _ _)).mp h

theorem diffKer_comm (z w : ℍ) : X.diffKer a b z w = X.diffKer a b w z := by
  have h := autK_comm (Γ := X.Γ) (diffProfile a b) z w
  rw [X.autK_diffProfile_eq ha hab, X.autK_diffProfile_eq ha hab] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (X.diffKer_nonneg hab _ _)
    (X.diffKer_nonneg hab _ _)).mp h

/-! ### The eigenvalues of `P` -/

/-- `ν_j = 1/(λ_j + a(a−1)) − 1/(λ_j + b(b−1))`. -/
def nu (j : X.SpecIndex ha) : ℝ :=
  1 / (X.spectralParam ha j + a * (a - 1)) - 1 / (X.spectralParam ha j + b * (b - 1))

omit hab in
theorem nu_def (j : X.SpecIndex ha) : X.nu ha (b := b) j =
    1 / (X.spectralParam ha j + a * (a - 1)) - 1 / (X.spectralParam ha j + b * (b - 1)) := rfl

theorem nu_pos (j : X.SpecIndex ha) : 0 < X.nu ha (b := b) j := by
  have hl := X.spectralParam_nonneg ha j
  have h1 : 0 < a * (a - 1) := by nlinarith
  have h2 : a * (a - 1) < b * (b - 1) := by nlinarith
  rw [nu_def, sub_pos]
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

theorem diffOp_specVec (j : X.SpecIndex ha) :
    X.diffOp ha hab (X.specVec ha j) = ((X.nu ha (b := b) j : ℝ) : ℂ) • X.specVec ha j := by
  rw [← X.resOp_sub ha hab, sub_apply, X.resOp_specVec_eq ha ha j,
    X.resOp_specVec_eq ha (lt_trans ha hab) j, ← sub_smul, nu_def]
  push_cast
  rfl

theorem diffOp_eq_zero_of_orthogonal {f : Lp ℂ 2 X.μ}
    (hf : ∀ j : X.SpecIndex ha, ⟪X.specVec ha j, f⟫_ℂ = 0) : X.diffOp ha hab f = 0 := by
  rw [← X.resOp_sub ha hab, sub_apply,
    X.resOp_eq_zero_of_orthogonal ha hf ha, X.resOp_eq_zero_of_orthogonal ha hf (lt_trans ha hab),
    sub_zero]

/-! ### Continuous representatives -/

/-- `z ↦ ∫_F K(z, w) f(w) dw`. -/
def kerApply (f : Lp ℂ 2 X.μ) (z : ℍ) : ℂ := ∫ w, ((X.diffKer a b z w : ℝ) : ℂ) * f w ∂X.μ

omit ha hab in
theorem integrable_Lp (f : Lp ℂ 2 X.μ) : Integrable (f : ℍ → ℂ) X.μ :=
  (Lp.memLp f).integrable (by norm_num)

theorem continuous_kerApply (f : Lp ℂ 2 X.μ) : Continuous (X.kerApply (a := a) (b := b) f) := by
  obtain ⟨B, hB0, hB⟩ := X.exists_diffKer_le ha hab
  refine continuous_of_dominated (bound := fun w => B * ‖(f : ℍ → ℂ) w‖) (fun z => ?_)
    (fun z => Eventually.of_forall fun w => ?_) ((X.integrable_Lp f).norm.const_mul B)
    (Eventually.of_forall fun w => ?_)
  · exact ((Complex.continuous_ofReal.comp ((X.continuous_diffKer ha hab).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (X.diffKer_nonneg hab _ _)]
    exact mul_le_mul_of_nonneg_right (hB z w) (norm_nonneg _)
  · exact (Complex.continuous_ofReal.comp ((X.continuous_diffKer ha hab).comp
      (continuous_id.prodMk continuous_const))).mul continuous_const

theorem kerApply_smul (f : Lp ℂ 2 X.μ) (γ : X.Γ) (z : ℍ) :
    X.kerApply (a := a) (b := b) f ((γ : SL(2, ℝ)) • z) = X.kerApply (a := a) (b := b) f z := by
  simp only [kerApply, X.diffKer_smul_left ha hab]

theorem diffOp_coeFn (f : Lp ℂ 2 X.μ) :
    (X.diffOp ha hab f : ℍ → ℂ) =ᵐ[X.μ] X.kerApply (a := a) (b := b) f := by
  filter_upwards [(X.profileKernel (measurable_diffProfile ha hab)
    (lintegral_diffProfile_mass_lt_top ha hab)).op_coeFn f] with z hz
  rw [diffOp, hz, apply, kerApply]
  simp only [X.diffOp_toFun ha hab]

omit ha hab in
/-- **Invariant continuous functions vanishing a.e. on `F` vanish.** -/
theorem eq_zero_of_ae_eq_zero {g : ℍ → ℂ} (hg : Continuous g)
    (hinv : ∀ (γ : X.Γ) z, g ((γ : SL(2, ℝ)) • z) = g z) (h0 : g =ᵐ[X.μ] 0) : g = 0 := by
  funext z₀
  by_contra hne
  set U := {z : ℍ | g z ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun hg continuous_const
  have hz₀ : z₀ ∈ U := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hpos : 0 < volume U :=
    lt_of_lt_of_le (volume_closedBall_pos z₀ (half_pos hε))
      (measure_mono ((closedBall_subset_ball (half_lt_self hε)).trans hball))
  -- some translate of `F` meets `U` in positive measure
  have hcover : volume U ≤ ∑' γ : X.Γ, volume (U ∩ (γ • X.F)) := by
    have hae := X.isFundamentalDomain.ae_covers
    calc volume U = volume (U ∩ ⋃ γ : X.Γ, γ⁻¹ • X.F) := by
          refine (measure_congr ?_).symm
          filter_upwards [hae] with z hz
          obtain ⟨γ, hγ⟩ := hz
          have : z ∈ ⋃ γ : X.Γ, γ⁻¹ • X.F :=
            mem_iUnion.mpr ⟨γ, by rw [mem_inv_smul_set_iff]; exact hγ⟩
          simp only [eq_iff_iff]
          exact ⟨fun h => h.1, fun h => ⟨h, this⟩⟩
      _ ≤ ∑' γ : X.Γ, volume (U ∩ γ⁻¹ • X.F) := by
          rw [inter_iUnion]; exact measure_iUnion_le _
      _ = ∑' γ : X.Γ, volume (U ∩ (γ • X.F)) :=
          (Equiv.inv X.Γ).tsum_eq (fun γ => volume (U ∩ γ • X.F))
  obtain ⟨γ, hγ⟩ : ∃ γ : X.Γ, 0 < volume (U ∩ γ • X.F) := by
    by_contra hall
    have hall' : ∀ γ : X.Γ, volume (U ∩ (γ • X.F)) = 0 := fun γ => by
      by_contra h; exact hall ⟨γ, pos_iff_ne_zero.mpr h⟩
    have : ∑' γ : X.Γ, volume (U ∩ (γ • X.F)) = 0 := ENNReal.tsum_eq_zero.mpr hall'
    rw [this] at hcover
    exact (lt_of_lt_of_le hpos hcover).ne' rfl
  -- translate back into `F`
  have hU_inv : (γ⁻¹ : X.Γ) • U = U := by
    ext z
    simp only [mem_smul_set_iff_inv_smul_mem, inv_inv, U, mem_setOf_eq]
    rw [Subgroup.smul_def, hinv]
  have hpre : volume (U ∩ X.F) = volume (U ∩ γ • X.F) := by
    rw [eq_comm, ← measure_smul volume (γ⁻¹ : X.Γ) (U ∩ γ • X.F), smul_set_inter, hU_inv,
      inv_smul_smul]
  have hμ : X.μ U = 0 := by
    have := ae_iff.mp h0
    have hsub : U ⊆ {z | ¬ g z = (0 : ℍ → ℂ) z} := fun z hz => hz
    exact measure_mono_null hsub this
  rw [Measure.restrict_apply hU.measurableSet] at hμ
  rw [hpre] at hμ
  exact hγ.ne' hμ

/-- The representative `ẽ_j = ν_j⁻¹ ∫_F K(·, w) e_j(w) dw`. -/
def specRep (j : X.SpecIndex ha) (z : ℍ) : ℂ :=
  ((X.nu ha (b := b) j)⁻¹ : ℂ) * X.kerApply (a := a) (b := b) (X.specVec ha j) z

theorem continuous_specRep (j : X.SpecIndex ha) : Continuous (X.specRep ha (b := b) j) :=
  continuous_const.mul (X.continuous_kerApply ha hab _)

theorem specRep_smul (j : X.SpecIndex ha) (γ : X.Γ) (z : ℍ) :
    X.specRep ha (b := b) j ((γ : SL(2, ℝ)) • z) = X.specRep ha (b := b) j z := by
  simp only [specRep, X.kerApply_smul ha hab]

theorem ae_eq_specRep (j : X.SpecIndex ha) :
    (X.specVec ha j : ℍ → ℂ) =ᵐ[X.μ] X.specRep ha (b := b) j := by
  have hν : ((X.nu ha (b := b) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (X.nu_pos ha hab j).ne'
  filter_upwards [X.diffOp_coeFn ha hab (X.specVec ha j),
    Lp.coeFn_smul (((X.nu ha (b := b) j : ℝ) : ℂ)) (X.specVec ha j)] with z h1 h2
  rw [X.diffOp_specVec ha hab, h2, Pi.smul_apply, smul_eq_mul] at h1
  rw [specRep, ← h1, ← mul_assoc, inv_mul_cancel₀ hν, one_mul]

/-- **Orthogonal vectors have vanishing continuous transform.** -/
theorem kerApply_eq_zero_of_orthogonal {f : Lp ℂ 2 X.μ}
    (hf : ∀ j : X.SpecIndex ha, ⟪X.specVec ha j, f⟫_ℂ = 0) (z : ℍ) :
    X.kerApply (a := a) (b := b) f z = 0 := by
  have h0 : X.kerApply (a := a) (b := b) f =ᵐ[X.μ] 0 := by
    filter_upwards [X.diffOp_coeFn ha hab f, Lp.coeFn_zero ℂ 2 X.μ] with z h1 h2
    rw [← h1, X.diffOp_eq_zero_of_orthogonal ha hab hf, h2]
  have := X.eq_zero_of_ae_eq_zero (X.continuous_kerApply ha hab f) (X.kerApply_smul ha hab f) h0
  exact congrFun this z

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
