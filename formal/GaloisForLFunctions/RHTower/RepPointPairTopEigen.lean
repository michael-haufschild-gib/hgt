import GaloisForLFunctions.RHTower.RepPointPairCuspSplitting
import GaloisForLFunctions.HTGeometry.CompactPerturbationInvariantSubspace

/-!
# The top eigenvalue of a point-pair operator above `h_φ(½)`

The constant fields with `ρ`-invariant values span a subspace `V` of `L²(𝒟; ℂ^ι)`.  `L_φ` acts on
it by the kernel mass `m_φ = ∫_ℍ φ(u(i, w)) dμ(w)` (`ppL2_constRep`), so `L_φ` preserves `V`.  With
the cusp splitting `L_φ = K + B_Y` (`K` compact, `‖B_Y‖ ≤ h_{|φ|}(½)`), the top-eigenvalue theorem
on `Vᗮ` gives (`exists_top_eigenvector`): if `re⟪L_φ F, F⟫ > h_{|φ|}(½) ‖F‖²` for some `F ⊥ V`, then
`L_φ` has an eigenvalue `M > h_{|φ|}(½)` with an eigenvector orthogonal to `V`.  `M` is the top of the
numerical range of `L_φ` on `Vᗮ`, and its eigenspace is finite-dimensional
(`finiteDimensional_eigenspace_ppL2`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology RCLike
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

/-- **The radial integral does not depend on the centre** (Bochner form):
`∫_ℍ f(u(z, w)) dμ(w) = ∫_ℍ f(u(i, w)) dμ(w)`. -/
theorem integral_pairU_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E)
    (z : ℍ) : ∫ w, f (pairU z w) = ∫ w, f (pairU UpperHalfPlane.I w) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) UpperHalfPlane.I z
  subst hg
  have hmp := measurePreserving_smul ((g : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have e : ∀ w : ℍ, ((g : GL (Fin 2) ℝ)) • w = g • w := fun w => rfl
  rw [← hmp.integral_comp (measurableEmbedding_const_smul _)]
  simp only [e, pairU_smul]

/-- The kernel mass `m_φ = ∫_ℍ φ(u(i, w)) dμ(w)`. -/
def kernelMassR (φ : ℝ → ℝ) : ℝ := ∫ w : ℍ, φ (pairU UpperHalfPlane.I w)

variable (ι) in
/-- The constant field with value `v`. -/
def constRep (v : EuclideanSpace ℂ ι) : RepL2 ι := toRepL2 (fun _ => v) (memLp_const v)

theorem constRep_coeFn (v : EuclideanSpace ℂ ι) :
    (constRep ι v : ℍ → EuclideanSpace ℂ ι) =ᵐ[cellMeasure] fun _ => v :=
  MemLp.coeFn_toLp (memLp_const v)

variable (ρ) in
/-- The span `V` of the constant fields with `ρ`-invariant values. -/
def invConst : Submodule ℂ (RepL2 ι) :=
  Submodule.span ℂ {F | ∃ v : EuclideanSpace ℂ ι, (∀ B, ρ B v = v) ∧ F = constRep ι v}

section Const

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M) (hR : 0 ≤ R)
  (hφR : KernelSupport φ R)

/-- **`L_φ` acts on invariant constants by the kernel mass.** -/
theorem ppL2_constRep {v : EuclideanSpace ℂ ι} (hv : ∀ B, ρ B v = v) :
    ppL2 ρ hφc hφM hR hφR (constRep ι v) = ((kernelMassR φ : ℝ) : ℂ) • constRep ι v := by
  apply Lp.ext
  have hc : ppApply ρ φ (constRep ι v : ℍ → EuclideanSpace ℂ ι) = ppApply ρ φ (fun _ => v) :=
    ppApply_congr_ae φ (constRep_coeFn v)
  have he : IsEquivariant ρ (fun _ : ℍ => v) := fun A _ => (hv A).symm
  filter_upwards [ppL2_coeFn hφc hφM hR hφR (ρ := ρ) (constRep ι v),
    Lp.coeFn_smul ((kernelMassR φ : ℝ) : ℂ) (constRep ι v), constRep_coeFn v] with z h1 h2 h3
  rw [h1, h2, hc, Pi.smul_apply, h3, ppApply_eq_integral hφc hφR continuous_const he,
    integral_smul_const, integral_complex_ofReal (f := fun w => φ (pairU z w)),
    integral_pairU_eq (fun u => φ u) z]
  rfl

/-- **`L_φ` preserves the invariant constants.** -/
theorem ppL2_mem_invConst {F : RepL2 ι} (hF : F ∈ invConst ρ) :
    ppL2 ρ hφc hφM hR hφR F ∈ invConst ρ := by
  have hle : (invConst ρ).map (ppL2 ρ hφc hφM hR hφR : RepL2 ι →ₗ[ℂ] RepL2 ι) ≤ invConst ρ := by
    rw [invConst, Submodule.map_span_le]
    rintro G ⟨v, hv, rfl⟩
    rw [ContinuousLinearMap.coe_coe, ppL2_constRep hφc hφM hR hφR hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, hv, rfl⟩)
  exact hle ⟨F, hF, rfl⟩

/-- **The top eigenvalue above `h_{|φ|}(½)`.**  If `re⟪L_φ F, F⟫ > h_{|φ|}(½) ‖F‖²` for some `F` orthogonal
to the invariant constants, then `L_φ` has an eigenvalue `M > h_{|φ|}(½)`, the top of its numerical
range on the orthogonal complement, with an eigenvector orthogonal to the invariant constants. -/
theorem exists_top_eigenvector {F : RepL2 ι} (hFV : F ∈ (invConst ρ)ᗮ)
    (hF : halfTransform (fun u => |φ u|) * ‖F‖ ^ 2 < re ⟪ppL2 ρ hφc hφM hR hφR F, F⟫_ℂ) :
    ∃ m : ℝ, halfTransform (fun u => |φ u|) < m ∧
      (∀ x ∈ (invConst ρ)ᗮ, re ⟪ppL2 ρ hφc hφM hR hφR x, x⟫_ℂ ≤ m * ‖x‖ ^ 2) ∧
      ∃ x ∈ (invConst ρ)ᗮ, x ≠ 0 ∧ ppL2 ρ hφc hφM hR hφR x = (m : ℂ) • x := by
  set Y : ℝ := 4 * R + 3
  have hY0 : 0 < Y := by positivity
  have hY : 4 * R + 2 < Y ^ 2 := by nlinarith
  exact exists_eigenvector_of_compact_add_orthogonal (ppL2_isSymmetric hφc hφM hR hφR)
    (isCompactOperator_ppL2_sub_cuspOp hφc hφM hR hφR hY0) (sub_add_cancel _ _).symm
    (halfTransform_abs_nonneg φ) (norm_cuspOp_le hφc hφM hR hφR hY0 hY)
    (fun _ hv => ppL2_mem_invConst hφc hφM hR hφR hv) hFV hF

/-- **The eigenspaces above `h_{|φ|}(½)` are finite-dimensional.** -/
theorem finiteDimensional_eigenspace_ppL2 {m : ℂ} (hm : halfTransform (fun u => |φ u|) < ‖m‖) :
    FiniteDimensional ℂ (Module.End.eigenspace
      ((ppL2 ρ hφc hφM hR hφR : RepL2 ι →L[ℂ] RepL2 ι) : Module.End ℂ (RepL2 ι)) m) := by
  set Y : ℝ := 4 * R + 3
  have hY0 : 0 < Y := by positivity
  have hY : 4 * R + 2 < Y ^ 2 := by nlinarith
  exact finiteDimensional_eigenspace_of_compact_add
    (isCompactOperator_ppL2_sub_cuspOp hφc hφM hR hφR hY0) (sub_add_cancel _ _).symm
    ((norm_cuspOp_le hφc hφM hR hφR hY0 hY).trans_lt hm)

end Const

end

end GaloisForLFunctions.RHTower.RepPointPair
