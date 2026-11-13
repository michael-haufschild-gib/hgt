import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventCompactness
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenbasis

/-!
# The spectrum read off the resolvents

Fix `a > 1`.  The compact self-adjoint `T_a` has an orthonormal family of eigenvectors `e_j` with
nonzero eigenvalues `μ_j` (`HTGeometry.eigenVec`).  The resolvent identity gives, for every `s > 1`,

  `T_s e_j = e_j/(λ_j + s(s − 1))`,  `λ_j = 1/μ_j − a(a − 1)`   (`resOp_eigenVec`),

and boundedness of every `T_s` forces `λ_j ≥ 0` (`spectralParam_nonneg`): if `λ_j < 0` then
`s = ½ + √(¼ − λ_j) > 1` would make `1 + (s(s−1) − a(a−1)) μ_j = 0`.  A vector orthogonal to every
`e_j` is killed by every `T_s` (`resOp_eq_zero_of_orthogonal`).  These `λ_j` are the Laplace
eigenvalues of the surface; only finitely many lie below any bound (`finite_spectralParam_le`).
-/

open MeasureTheory Set Filter UpperHalfPlane Real
open scoped ENNReal MatrixGroups Pointwise InnerProductSpace

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

namespace CompactQuotient

variable (X : CompactQuotient)

/-- The resolvent identity in both orders: `T_s T_a = (T_a − T_s)/(s(s−1) − a(a−1))`, `s ≠ a`. -/
theorem resOp_comp_of_ne {a s : ℝ} (ha : 1 < a) (hs : 1 < s) (hne : s ≠ a) :
    X.resOp hs ∘L X.resOp ha =
      ((1 / (s * (s - 1) - a * (a - 1)) : ℝ) : ℂ) • (X.resOp ha - X.resOp hs) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hsc : (1 / (a * (a - 1) - s * (s - 1)) : ℝ) = -(1 / (s * (s - 1) - a * (a - 1))) := by
      rw [show a * (a - 1) - s * (s - 1) = -(s * (s - 1) - a * (a - 1)) by ring,
        one_div_neg_eq_neg_one_div]
    calc X.resOp hs ∘L X.resOp ha = X.resOp ha ∘L X.resOp hs := X.resOp_comm hs h
      _ = ((1 / (a * (a - 1) - s * (s - 1)) : ℝ) : ℂ) • (X.resOp hs - X.resOp ha) :=
          X.resOp_comp hs h
      _ = ((1 / (s * (s - 1) - a * (a - 1)) : ℝ) : ℂ) • (X.resOp ha - X.resOp hs) := by
          rw [hsc, Complex.ofReal_neg, ← neg_sub (X.resOp ha) (X.resOp hs), neg_smul_neg]
  · exact X.resOp_comp ha h

/-- On an eigenvector of `T_a` with eigenvalue `μ ≠ 0`, `T_s` acts by `μ/(1 + cμ)`, and
`1 + cμ ≠ 0`. -/
theorem resOp_apply_of_eigen {a s : ℝ} (ha : 1 < a) (hs : 1 < s) {e : Lp ℂ 2 X.μ} {μ : ℂ}
    (he : X.resOp ha e = μ • e) (hμ : μ ≠ 0) (he0 : e ≠ 0) :
    1 + ((s * (s - 1) - a * (a - 1) : ℝ) : ℂ) * μ ≠ 0 ∧
      X.resOp hs e = (μ / (1 + ((s * (s - 1) - a * (a - 1) : ℝ) : ℂ) * μ)) • e := by
  by_cases hsa : s = a
  · subst hsa
    simp only [sub_self, Complex.ofReal_zero, zero_mul, add_zero, div_one, ne_eq, one_ne_zero,
      not_false_eq_true, true_and]
    exact he
  have hc : s * (s - 1) - a * (a - 1) ≠ 0 := by
    intro h0
    have : (s - a) * (s + a - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hsa (by linarith)
    · linarith
  have hid := congrArg (fun T => T e) (X.resOp_comp_of_ne ha hs hsa)
  simp only [ContinuousLinearMap.comp_apply, he, map_smul, smul_apply, sub_apply] at hid
  -- `μ T_s e = c⁻¹ (μ e − T_s e)`, i.e. `(1 + cμ) T_s e = μ e`
  have key : (1 + ((s * (s - 1) - a * (a - 1) : ℝ) : ℂ) * μ) • X.resOp hs e = μ • e := by
    have h1 : ((s * (s - 1) - a * (a - 1) : ℝ) : ℂ) • (μ • X.resOp hs e) =
        μ • e - X.resOp hs e := by
      rw [hid, smul_smul, ← Complex.ofReal_mul, mul_one_div_cancel hc, Complex.ofReal_one, one_smul]
    rw [add_smul, one_smul, mul_smul, h1]
    abel
  have hne : 1 + ((s * (s - 1) - a * (a - 1) : ℝ) : ℂ) * μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at key
    exact he0 ((smul_eq_zero.mp key.symm).resolve_left hμ)
  refine ⟨hne, ?_⟩
  rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- `T_a f = 0` implies `T_s f = 0` for every `s`. -/
theorem resOp_eq_zero_of_resOp {a s : ℝ} (ha : 1 < a) (hs : 1 < s) {f : Lp ℂ 2 X.μ}
    (hf : X.resOp ha f = 0) : X.resOp hs f = 0 := by
  by_cases hsa : s = a
  · subst hsa; exact hf
  have hid := congrArg (fun T => T f) (X.resOp_comp_of_ne ha hs hsa)
  simp only [ContinuousLinearMap.comp_apply, hf, map_zero, smul_apply, sub_apply, zero_sub,
    smul_neg] at hid
  have hc : (((1 / (s * (s - 1) - a * (a - 1))) : ℝ) : ℂ) ≠ 0 := by
    have : s * (s - 1) - a * (a - 1) ≠ 0 := by
      intro h0
      have : (s - a) * (s + a - 1) = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · exact hsa (by linarith)
      · linarith
    exact_mod_cast one_div_ne_zero this
  have := neg_eq_zero.mp hid.symm
  exact (smul_eq_zero.mp this).resolve_left hc

section spectrum

variable {a : ℝ} (ha : 1 < a)
include ha

instance factCompact : Fact (IsCompactOperator (X.resOp ha)) := ⟨X.isCompactOperator_resOp ha⟩

theorem isSymmetric_resOp : ((X.resOp ha : Lp ℂ 2 X.μ →ₗ[ℂ] Lp ℂ 2 X.μ)).IsSymmetric :=
  (X.isSelfAdjoint_resOp ha).isSymmetric

/-- The index set of the spectral family. -/
abbrev SpecIndex := EigenIndex (X.resOp ha)

/-- The eigenvectors `e_j`. -/
abbrev specVec (j : X.SpecIndex ha) : Lp ℂ 2 X.μ := eigenVec (X.resOp ha) j

/-- The eigenvalues `μ_j` of `T_a`. -/
def specMu (j : X.SpecIndex ha) : ℝ := (j.1.1).re

/-- The spectral parameters `λ_j = 1/μ_j − a(a − 1)`. -/
def spectralParam (j : X.SpecIndex ha) : ℝ := 1 / X.specMu ha j - a * (a - 1)

theorem specMu_coe (j : X.SpecIndex ha) : ((X.specMu ha j : ℝ) : ℂ) = j.1.1 :=
  eigenValue_real (X.isSymmetric_resOp ha) j

theorem specMu_ne_zero (j : X.SpecIndex ha) : X.specMu ha j ≠ 0 := by
  intro h
  have := X.specMu_coe ha j
  rw [h, Complex.ofReal_zero] at this
  exact j.1.2 this.symm

theorem resOp_specVec (j : X.SpecIndex ha) :
    X.resOp ha (X.specVec ha j) = ((X.specMu ha j : ℝ) : ℂ) • X.specVec ha j := by
  rw [X.specMu_coe ha j]; exact apply_eigenVec _ j

theorem specVec_ne_zero (j : X.SpecIndex ha) : X.specVec ha j ≠ 0 :=
  (orthonormal_eigenVec (X.isSymmetric_resOp ha)).ne_zero j

/-- **Positivity of the spectrum.**  `λ_j ≥ 0`. -/
theorem spectralParam_nonneg (j : X.SpecIndex ha) : 0 ≤ X.spectralParam ha j := by
  by_contra hneg'
  have hneg : X.spectralParam ha j < 0 := lt_of_not_ge hneg'
  set lam := X.spectralParam ha j
  set s : ℝ := 1 / 2 + Real.sqrt (1 / 4 - lam)
  have hroot : Real.sqrt (1 / 4 - lam) ^ 2 = 1 / 4 - lam := Real.sq_sqrt (by linarith)
  have hsq : 1 / 2 < Real.sqrt (1 / 4 - lam) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hs : 1 < s := by simp only [s]; linarith
  have hss : s * (s - 1) = -lam := by simp only [s]; nlinarith [hroot]
  obtain ⟨hne, -⟩ := X.resOp_apply_of_eigen ha hs (X.resOp_specVec ha j)
    (by exact_mod_cast X.specMu_ne_zero ha j) (X.specVec_ne_zero ha j)
  apply hne
  have hμ := X.specMu_ne_zero ha j
  have hμc : ((X.specMu ha j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hμ
  rw [hss]
  have : lam = 1 / X.specMu ha j - a * (a - 1) := rfl
  rw [this]
  push_cast
  field_simp
  ring

theorem specMu_pos (j : X.SpecIndex ha) : 0 < X.specMu ha j := by
  have h := X.spectralParam_nonneg ha j
  have ha2 : 0 < a * (a - 1) := by nlinarith
  have h1 : 0 < 1 / X.specMu ha j := by unfold spectralParam at h; linarith
  exact one_div_pos.mp h1

theorem specMu_eq (j : X.SpecIndex ha) :
    X.specMu ha j = 1 / (X.spectralParam ha j + a * (a - 1)) := by
  rw [spectralParam, sub_add_cancel, one_div_one_div]

/-- **The resolvents on the spectral family.**  `T_s e_j = e_j/(λ_j + s(s − 1))`. -/
theorem resOp_specVec_eq {s : ℝ} (hs : 1 < s) (j : X.SpecIndex ha) :
    X.resOp hs (X.specVec ha j) =
      ((1 / (X.spectralParam ha j + s * (s - 1)) : ℝ) : ℂ) • X.specVec ha j := by
  obtain ⟨hne, h⟩ := X.resOp_apply_of_eigen ha hs (X.resOp_specVec ha j)
    (by exact_mod_cast X.specMu_ne_zero ha j) (X.specVec_ne_zero ha j)
  rw [h]
  congr 1
  have hμ := X.specMu_ne_zero ha j
  have hl := X.spectralParam_nonneg ha j
  have hs2 : 0 < s * (s - 1) := by nlinarith
  have hden : X.spectralParam ha j + s * (s - 1) ≠ 0 := by linarith
  have hne' : 1 + (s * (s - 1) - a * (a - 1)) * X.specMu ha j ≠ 0 := by exact_mod_cast hne
  have hreal : X.specMu ha j / (1 + (s * (s - 1) - a * (a - 1)) * X.specMu ha j) =
      1 / (X.spectralParam ha j + s * (s - 1)) := by
    rw [div_eq_div_iff hne' hden, spectralParam]
    field_simp
    ring
  rw [← hreal]
  push_cast
  rfl

/-- **Completeness.**  A vector orthogonal to every `e_j` is killed by every `T_s`. -/
theorem resOp_eq_zero_of_orthogonal {f : Lp ℂ 2 X.μ}
    (hf : ∀ j : X.SpecIndex ha, ⟪X.specVec ha j, f⟫_ℂ = 0) {s : ℝ} (hs : 1 < s) :
    X.resOp hs f = 0 := by
  refine X.resOp_eq_zero_of_resOp ha hs ?_
  set T := X.resOp ha
  have hsym := X.isSymmetric_resOp ha
  have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (X.isCompactOperator_resOp ha) hsym
  have hmem : T f ∈ (⨆ μ, Module.End.eigenspace (T : Lp ℂ 2 X.μ →ₗ[ℂ] Lp ℂ 2 X.μ) μ)ᗮ := by
    refine (Submodule.mem_orthogonal _ _).mpr fun v hv => ?_
    refine Submodule.iSup_induction _ (motive := fun v => ⟪v, T f⟫_ℂ = 0) hv ?_ (by simp)
      (fun x y hx hy => by rw [inner_add_left, hx, hy, add_zero])
    intro μ v hv
    have hTv : T v = μ • v := Module.End.mem_eigenspace_iff.mp hv
    have h1 : ⟪v, T f⟫_ℂ = ⟪T v, f⟫_ℂ := (hsym v f).symm
    rw [h1, hTv, inner_smul_left]
    by_cases hμ : μ = 0
    · simp [hμ]
    · have hspan := mem_span_eigenVec (T := T) ⟨μ, hμ⟩ v hv
      have : ⟪v, f⟫_ℂ = 0 := by
        refine Submodule.span_induction (p := fun v _ => ⟪v, f⟫_ℂ = 0) ?_ (by simp)
          (fun x y _ _ hx hy => by rw [inner_add_left, hx, hy, add_zero])
          (fun c x _ hx => by rw [inner_smul_left, hx, mul_zero]) hspan
        rintro _ ⟨j, rfl⟩
        exact hf j
      rw [this, mul_zero]
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

end spectrum

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
