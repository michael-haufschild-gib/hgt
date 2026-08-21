import GaloisForLFunctions.HTGeometry.SimpleEigenvalueBorderedRCLike
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The differentiable simple eigenvalue branch over an arbitrary `RCLike` field

This is the `RCLike` companion of `SimpleEigenvalueBranch`.  A simple eigenvalue of a differentiable family of
symmetric operators on a `𝕜`-Hilbert space moves differentiably, together with its eigenvector.  The proof is
the implicit function theorem applied to the *eigen-residual*

```text
f (c, (phi, nu)) = (A c phi - nu • phi, ⟪psi_0, phi⟫ - 1),
```

whose zero set is exactly the set of eigenpairs normalized against the reference eigenvector.  Its partial
derivative in `(phi, nu)` is the bordered map of `SimpleEigenvalueBorderedRCLike`, invertible precisely because
the eigenvalue is simple.

Two things distinguish the `𝕜`-case from the real one.  First, the aperture parameter `c` is real while the
eigenvalue parameter is a `𝕜`-scalar, so the eigen-residual is a map `ℝ × (E × 𝕜) → E × 𝕜` which is only
`ℝ`-differentiable, and the bordered map must be inverted after restricting scalars to `ℝ`; being `𝕜`-linearly
invertible it certainly is.  Second, symmetry of `A c_0 - nu_0` needs the eigenvalue to be real, which is not
an assumption but a consequence of symmetry at the normalized eigenvector.

The branch is first produced with the *linear* normalization `⟪psi_0, psi c⟫ = 1`, which is what the implicit
function theorem gives; rescaling by the real scalar `‖psi c‖⁻¹` turns it into a genuinely normalized branch,
and that rescaling is differentiable because the norm does not vanish at the base point.
-/

noncomputable section

open scoped InnerProductSpace
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The derivative of an operator family in split form: `(delta c, delta phi) ↦ delta c • w + S delta phi`. -/
def familyDerivRC (S : E →L[𝕜] E) (w : E) : (ℝ × E) →L[ℝ] E :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ E) w +
    (S.restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem familyDerivRC_apply (S : E →L[𝕜] E) (w : E) (q : ℝ × E) :
    familyDerivRC S w q = q.1 • w + S q.2 := by
  simp [familyDerivRC]

/-- The eigen-residual: its zero set is the set of eigenpairs normalized against `psi_0`. -/
def eigenResidualRC (A : ℝ → E →L[𝕜] E) (ψ₀ : E) (q : ℝ × (E × 𝕜)) : E × 𝕜 :=
  (A q.1 q.2.1 - q.2.2 • q.2.1, ⟪ψ₀, q.2.1⟫_𝕜 - 1)

/-- The derivative of the eigen-residual: the family's motion in the aperture direction, plus the bordered map
in the eigenpair directions. -/
def eigenResidualDerivRC (T : E →L[𝕜] E) (ψ₀ w : E) : (ℝ × (E × 𝕜)) →L[ℝ] (E × 𝕜) :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ (E × 𝕜)) (w, (0 : 𝕜)) +
    ((borderedCLMRC T ψ₀).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜))

/-- The partial derivative of the eigen-residual in the eigenpair variables **is** the bordered map. -/
theorem eigenResidualDerivRC_comp_inr (T : E →L[𝕜] E) (ψ₀ w : E) :
    (eigenResidualDerivRC T ψ₀ w).comp (ContinuousLinearMap.inr ℝ ℝ (E × 𝕜))
      = (borderedCLMRC T ψ₀).restrictScalars ℝ := by
  refine ContinuousLinearMap.ext fun p => ?_
  simp [eigenResidualDerivRC]

/-- **The eigen-residual is strictly differentiable**, with the announced derivative. -/
theorem hasStrictFDerivAt_eigenResidualRC {A : ℝ → E →L[𝕜] E} {T : E →L[𝕜] E} {c₀ : ℝ} {ν₀ : 𝕜}
    {ψ₀ w : E}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDerivRC (A c₀) w) (c₀, ψ₀))
    (hT : ∀ x : E, T x = A c₀ x - ν₀ • x) :
    HasStrictFDerivAt (eigenResidualRC A ψ₀) (eigenResidualDerivRC T ψ₀ w) (c₀, (ψ₀, ν₀)) := by
  have hq2 : HasStrictFDerivAt (fun q : ℝ × (E × 𝕜) => q.2)
      (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜)) (c₀, (ψ₀, ν₀)) := hasStrictFDerivAt_snd
  have hφ := hq2.fst
  have hν := hq2.snd
  have hpair : HasStrictFDerivAt (fun q : ℝ × (E × 𝕜) => (q.1, q.2.1))
      ((ContinuousLinearMap.fst ℝ ℝ (E × 𝕜)).prod
        ((ContinuousLinearMap.fst ℝ E 𝕜).comp (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜))))
      (c₀, (ψ₀, ν₀)) := hasStrictFDerivAt_fst.prodMk hφ
  have h1 : HasStrictFDerivAt (fun q : ℝ × (E × 𝕜) => A q.1 q.2.1)
      ((familyDerivRC (A c₀) w).comp
        ((ContinuousLinearMap.fst ℝ ℝ (E × 𝕜)).prod
          ((ContinuousLinearMap.fst ℝ E 𝕜).comp (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜)))))
      (c₀, (ψ₀, ν₀)) := hA.comp (c₀, (ψ₀, ν₀)) hpair
  have h2 : HasStrictFDerivAt (fun q : ℝ × (E × 𝕜) => q.2.2 • q.2.1)
      (ν₀ • ((ContinuousLinearMap.fst ℝ E 𝕜).comp (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜))) +
        ((ContinuousLinearMap.snd ℝ E 𝕜).comp
          (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜))).smulRight ψ₀)
      (c₀, (ψ₀, ν₀)) := hν.smul hφ
  have h3 : HasStrictFDerivAt (fun q : ℝ × (E × 𝕜) => ⟪ψ₀, q.2.1⟫_𝕜 - 1)
      (((innerSL 𝕜 ψ₀).restrictScalars ℝ).comp
        ((ContinuousLinearMap.fst ℝ E 𝕜).comp (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜))))
      (c₀, (ψ₀, ν₀)) := by
    have h := (((innerSL 𝕜 ψ₀).restrictScalars ℝ).hasStrictFDerivAt
      (x := ψ₀)).comp (c₀, (ψ₀, ν₀)) hφ
    simpa using h.sub_const 1
  have hcomb := (h1.sub h2).prodMk h3
  have hEq : (((familyDerivRC (A c₀) w).comp
        ((ContinuousLinearMap.fst ℝ ℝ (E × 𝕜)).prod
          ((ContinuousLinearMap.fst ℝ E 𝕜).comp (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜)))) -
      (ν₀ • ((ContinuousLinearMap.fst ℝ E 𝕜).comp (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜))) +
        ((ContinuousLinearMap.snd ℝ E 𝕜).comp
          (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜))).smulRight ψ₀)).prod
      (((innerSL 𝕜 ψ₀).restrictScalars ℝ).comp
        ((ContinuousLinearMap.fst ℝ E 𝕜).comp (ContinuousLinearMap.snd ℝ ℝ (E × 𝕜)))))
      = eigenResidualDerivRC T ψ₀ w := by
    refine ContinuousLinearMap.ext fun q => Prod.ext ?_ ?_
    · simp [eigenResidualDerivRC, borderedMapRC, hT]
      abel
    · simp [eigenResidualDerivRC, borderedMapRC]
  rw [hEq] at hcomb
  exact hcomb

/-- **Existence of a differentiable simple eigenvalue branch over `𝕜`.**  For a strictly differentiable family
of operators, symmetric at the base point, with a simple normalized eigenvalue `nu_0` and a pseudo-inverse `R`
of `A c_0 - nu_0` modulo the eigendirection, there is a differentiable eigenpair branch through
`(psi_0, nu_0)`, normalized against `psi_0`. -/
theorem exists_differentiable_simple_eigen_branchRC [CompleteSpace E]
    {A : ℝ → E →L[𝕜] E} {R : E →L[𝕜] E} {c₀ : ℝ} {ν₀ : 𝕜} {ψ₀ w : E}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDerivRC (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : E, ⟪A c₀ u, v⟫_𝕜 = ⟪u, A c₀ v⟫_𝕜)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1)
    (hker : ∀ φ : E, A c₀ φ = ν₀ • φ → ∃ s : 𝕜, φ = s • ψ₀)
    (hR : ∀ y : E, A c₀ (R y) - ν₀ • R y = y - ⟪ψ₀, y⟫_𝕜 • ψ₀)
    (hRψ : ∀ y : E, ⟪ψ₀, R y⟫_𝕜 = 0) :
    ∃ (ψ : ℝ → E) (ν : ℝ → 𝕜), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      DifferentiableAt ℝ ψ c₀ ∧ DifferentiableAt ℝ ν c₀ ∧
      ∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ₀, ψ c⟫_𝕜 = 1 := by
  -- symmetry at the normalized eigenvector makes the eigenvalue real
  have hν₀real : (starRingEnd 𝕜) ν₀ = ν₀ := by
    have h1 : ⟪ψ₀, A c₀ ψ₀⟫_𝕜 = ν₀ := by rw [heig, inner_smul_right, hnorm, mul_one]
    have h2 : ⟪A c₀ ψ₀, ψ₀⟫_𝕜 = (starRingEnd 𝕜) ν₀ := by
      rw [heig, inner_smul_left, hnorm, mul_one]
    have h3 := hsymm ψ₀ ψ₀
    rw [h1, h2] at h3
    exact h3
  set T : E →L[𝕜] E := A c₀ - ν₀ • ContinuousLinearMap.id 𝕜 E with hTdef
  have hT : ∀ x : E, T x = A c₀ x - ν₀ • x := by
    intro x
    simp [hTdef]
  have hTψ : T ψ₀ = 0 := by rw [hT, heig, sub_self]
  have hTsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜 := by
    intro u v
    rw [hT, hT, inner_sub_left, inner_sub_right, hsymm u v, inner_smul_left, inner_smul_right,
      hν₀real]
  have hTker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ₀ := by
    intro φ hφ
    rw [hT, sub_eq_zero] at hφ
    exact hker φ hφ
  have hTR : ∀ y : E, T (R y) = y - ⟪ψ₀, y⟫_𝕜 • ψ₀ := by
    intro y
    rw [hT]
    exact hR y
  have hres := hasStrictFDerivAt_eigenResidualRC (ν₀ := ν₀) hA hT
  have hinv : ((eigenResidualDerivRC T ψ₀ w).comp
      (ContinuousLinearMap.inr ℝ ℝ (E × 𝕜))).IsInvertible := by
    rw [eigenResidualDerivRC_comp_inr]
    exact borderedCLMRC_restrictScalars_isInvertible hTsymm hTψ hnorm hTker hTR hRψ
  set g := hres.implicitFunctionOfProdDomain hinv with hg
  have hbase : g c₀ = (ψ₀, ν₀) :=
    (hres.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  have hstrict := hres.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  have hdiff : DifferentiableAt ℝ g c₀ := hstrict.differentiableAt
  have hev := hres.eventually_apply_implicitFunctionOfProdDomain hinv
  have hzero : eigenResidualRC A ψ₀ (c₀, (ψ₀, ν₀)) = (0, 0) := by
    have hunfold : eigenResidualRC A ψ₀ (c₀, (ψ₀, ν₀))
        = (A c₀ ψ₀ - ν₀ • ψ₀, ⟪ψ₀, ψ₀⟫_𝕜 - 1) := rfl
    rw [hunfold, heig, sub_self, hnorm, sub_self]
  refine ⟨fun c => (g c).1, fun c => (g c).2, ?_, ?_, hdiff.fst, hdiff.snd, ?_⟩
  · change (g c₀).1 = ψ₀
    rw [hbase]
  · change (g c₀).2 = ν₀
    rw [hbase]
  filter_upwards [hev] with c hc
  rw [hzero] at hc
  have h1 := congrArg Prod.fst hc
  have h2 := congrArg Prod.snd hc
  simp only [eigenResidualRC, sub_eq_zero] at h1 h2
  exact ⟨h1, h2⟩

/-- **The branch can be taken normalized.**  Rescaling by the real scalar `‖psi c‖⁻¹` preserves the
eigenrelation, makes the eigenfunction a unit vector, and is differentiable at the base point. -/
theorem exists_differentiable_normalized_simple_eigen_branchRC [CompleteSpace E]
    {A : ℝ → E →L[𝕜] E} {R : E →L[𝕜] E} {c₀ : ℝ} {ν₀ : 𝕜} {ψ₀ w : E}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDerivRC (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : E, ⟪A c₀ u, v⟫_𝕜 = ⟪u, A c₀ v⟫_𝕜)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1)
    (hker : ∀ φ : E, A c₀ φ = ν₀ • φ → ∃ s : 𝕜, φ = s • ψ₀)
    (hR : ∀ y : E, A c₀ (R y) - ν₀ • R y = y - ⟪ψ₀, y⟫_𝕜 • ψ₀)
    (hRψ : ∀ y : E, ⟪ψ₀, R y⟫_𝕜 = 0) :
    ∃ (ψ : ℝ → E) (ν : ℝ → 𝕜), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      DifferentiableAt ℝ ψ c₀ ∧ DifferentiableAt ℝ ν c₀ ∧
      ∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫_𝕜 = 1 := by
  obtain ⟨ψ, ν, hψ0, hν0, hdψ, hdν, hev⟩ :=
    exists_differentiable_simple_eigen_branchRC hA hsymm heig hnorm hker hR hRψ
  have hψ₀ne : ψ₀ ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hnorm
    exact zero_ne_one hnorm
  have hnψ₀ : ‖ψ₀‖ = 1 := by
    have h2 : RCLike.re (⟪ψ₀, ψ₀⟫_𝕜) = ‖ψ₀‖ ^ 2 := inner_self_eq_norm_sq ψ₀
    rw [hnorm] at h2
    simp at h2
    nlinarith [norm_nonneg ψ₀]
  have hne : ψ c₀ ≠ 0 := by rw [hψ0]; exact hψ₀ne
  have hdn : DifferentiableAt ℝ (fun c => ‖ψ c‖) c₀ := hdψ.norm 𝕜 hne
  have hnzero : ‖ψ c₀‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hdinv : DifferentiableAt ℝ (fun c => ‖ψ c‖⁻¹) c₀ := hdn.inv hnzero
  refine ⟨fun c => ‖ψ c‖⁻¹ • ψ c, ν, ?_, hν0, hdinv.smul hdψ, hdν, ?_⟩
  · show ‖ψ c₀‖⁻¹ • ψ c₀ = ψ₀
    rw [hψ0, hnψ₀, inv_one, one_smul]
  filter_upwards [hev] with c hc
  obtain ⟨hrel, hlin⟩ := hc
  have hcne : ψ c ≠ 0 := by
    intro h
    rw [h, inner_zero_right] at hlin
    exact zero_ne_one hlin
  have hcn : ‖ψ c‖ ≠ 0 := norm_ne_zero_iff.mpr hcne
  have hcn' : (((‖ψ c‖ : ℝ)) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hcn
  refine ⟨?_, ?_⟩
  · show A c (‖ψ c‖⁻¹ • ψ c) = ν c • (‖ψ c‖⁻¹ • ψ c)
    rw [(A c).map_smul_of_tower, hrel, smul_comm]
  · show ⟪‖ψ c‖⁻¹ • ψ c, ‖ψ c‖⁻¹ • ψ c⟫_𝕜 = 1
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K]
    push_cast
    field_simp

end GaloisForLFunctions.HTGeometry

end
