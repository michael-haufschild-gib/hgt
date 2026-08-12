import GaloisForLFunctions.HTGeometry.SimpleEigenvalueBordered
import GaloisForLFunctions.HTGeometry.HellmannFeynman
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-!
# The differentiable simple eigenvalue branch

A simple eigenvalue of a differentiable family of self-adjoint operators moves differentiably.  The proof here
is the implicit function theorem applied to the *eigen-residual*

```text
f (c, (phi, nu)) = (A c phi - nu • phi, ⟪psi_0, phi⟫ - 1),
```

whose zero set is exactly the set of eigenpairs normalized against the reference eigenvector.  The partial
derivative of `f` in `(phi, nu)` at an eigenpair is the bordered map

```text
(delta phi, delta nu) ↦ (T delta phi - delta nu • psi_0, ⟪psi_0, delta phi⟫),   T = A c_0 - nu_0,
```

which is invertible precisely because the eigenvalue is simple — that inversion is the content of
`SimpleEigenvalueBordered`.  So no compactness, no analytic Kato expansion and no contour integral is needed:
one bordered inverse plus the implicit function theorem produce the branch, its differentiability, and then —
via `hellmann_feynman_eventually` — the eigenvalue derivative.

The branch is first produced with the *linear* normalization `⟪psi_0, psi c⟫ = 1`, which is what the implicit
function theorem gives; rescaling by `‖psi c‖⁻¹` turns it into a genuinely normalized branch, and that
rescaling is differentiable because the norm does not vanish at the base point.
-/

noncomputable section

open RealInnerProductSpace Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The bordered map as a continuous linear map -/

/-- The bordered map of `SimpleEigenvalueBordered`, packaged as a continuous linear map on `E × ℝ`. -/
def borderedCLM (T : E →L[ℝ] E) (ψ : E) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (T.comp (ContinuousLinearMap.fst ℝ E ℝ) -
      ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ E ℝ) ψ).prod
    ((innerSL ℝ ψ).comp (ContinuousLinearMap.fst ℝ E ℝ))

@[simp] theorem borderedCLM_apply (T : E →L[ℝ] E) (ψ : E) (p : E × ℝ) :
    borderedCLM T ψ p = borderedMap T ψ p := by
  simp [borderedCLM, borderedMap]

/-- The explicit inverse, packaged as a continuous linear map. -/
def borderedInvCLM (R : E →L[ℝ] E) (ψ : E) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (R.comp (ContinuousLinearMap.fst ℝ E ℝ) +
      ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ E ℝ) ψ).prod
    (-(innerSL ℝ ψ).comp (ContinuousLinearMap.fst ℝ E ℝ))

@[simp] theorem borderedInvCLM_apply (R : E →L[ℝ] E) (ψ : E) (q : E × ℝ) :
    borderedInvCLM R ψ q = borderedInv R ψ q := by
  simp [borderedInvCLM, borderedInv]

/-- **The bordered continuous linear map is invertible at a simple eigenvalue.**  The inverse is the explicit
one, so no open mapping theorem and no completeness is used here. -/
theorem borderedCLM_isInvertible {T R : E →L[ℝ] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫ = ⟪u, T v⟫)
    (hTψ : T ψ = 0) (hnorm : ⟪ψ, ψ⟫ = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : ℝ, φ = s • ψ)
    (hR : ∀ y : E, T (R y) = y - ⟪ψ, y⟫ • ψ)
    (hRψ : ∀ y : E, ⟪ψ, R y⟫ = 0) :
    (borderedCLM T ψ).IsInvertible := by
  refine ⟨ContinuousLinearEquiv.equivOfInverse (borderedCLM T ψ) (borderedInvCLM R ψ) ?_ ?_, ?_⟩
  · intro p
    simp [borderedInv_borderedMap hsymm hTψ hnorm hker hR hRψ p]
  · intro q
    simp [borderedMap_borderedInv hTψ hnorm hR hRψ q]
  · rfl

/-! ## The eigen-residual and its derivative -/

/-- The derivative of an operator family in split form: `(delta c, delta phi) ↦ delta c • w + S delta phi`,
where `w` is the family's own motion `(dA/dc) psi` and `S` is the operator at the base point. -/
def familyDeriv (S : E →L[ℝ] E) (w : E) : (ℝ × E) →L[ℝ] E :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ E) w +
    S.comp (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem familyDeriv_apply (S : E →L[ℝ] E) (w : E) (q : ℝ × E) :
    familyDeriv S w q = q.1 • w + S q.2 := by
  simp [familyDeriv]

/-- The eigen-residual: its zero set is the set of eigenpairs normalized against `psi_0`. -/
def eigenResidual (A : ℝ → E →L[ℝ] E) (ψ₀ : E) (q : ℝ × (E × ℝ)) : E × ℝ :=
  (A q.1 q.2.1 - q.2.2 • q.2.1, ⟪ψ₀, q.2.1⟫ - 1)

/-- The derivative of the eigen-residual: the family's motion in the aperture direction, plus the bordered map
in the eigenpair directions. -/
def eigenResidualDeriv (T : E →L[ℝ] E) (ψ₀ w : E) : (ℝ × (E × ℝ)) →L[ℝ] (E × ℝ) :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ (E × ℝ)) (w, (0 : ℝ)) +
    (borderedCLM T ψ₀).comp (ContinuousLinearMap.snd ℝ ℝ (E × ℝ))

/-- The partial derivative of the eigen-residual in the eigenpair variables **is** the bordered map. -/
theorem eigenResidualDeriv_comp_inr (T : E →L[ℝ] E) (ψ₀ w : E) :
    (eigenResidualDeriv T ψ₀ w).comp (ContinuousLinearMap.inr ℝ ℝ (E × ℝ)) = borderedCLM T ψ₀ := by
  refine ContinuousLinearMap.ext fun p => ?_
  simp [eigenResidualDeriv]

/-- **The eigen-residual is strictly differentiable**, with the announced derivative.  The only input is
strict differentiability of the family `(c, phi) ↦ A c phi` in split form. -/
theorem hasStrictFDerivAt_eigenResidual {A : ℝ → E →L[ℝ] E} {T : E →L[ℝ] E} {c₀ ν₀ : ℝ} {ψ₀ w : E}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDeriv (A c₀) w) (c₀, ψ₀))
    (hT : ∀ x : E, T x = A c₀ x - ν₀ • x) :
    HasStrictFDerivAt (eigenResidual A ψ₀) (eigenResidualDeriv T ψ₀ w) (c₀, (ψ₀, ν₀)) := by
  have hq2 : HasStrictFDerivAt (fun q : ℝ × (E × ℝ) => q.2)
      (ContinuousLinearMap.snd ℝ ℝ (E × ℝ)) (c₀, (ψ₀, ν₀)) := hasStrictFDerivAt_snd
  have hφ := hq2.fst
  have hν := hq2.snd
  -- the two components
  have hpair : HasStrictFDerivAt (fun q : ℝ × (E × ℝ) => (q.1, q.2.1))
      ((ContinuousLinearMap.fst ℝ ℝ (E × ℝ)).prod
        ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E × ℝ))))
      (c₀, (ψ₀, ν₀)) := hasStrictFDerivAt_fst.prodMk hφ
  have h1 : HasStrictFDerivAt (fun q : ℝ × (E × ℝ) => A q.1 q.2.1)
      ((familyDeriv (A c₀) w).comp
        ((ContinuousLinearMap.fst ℝ ℝ (E × ℝ)).prod
          ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E × ℝ)))))
      (c₀, (ψ₀, ν₀)) := hA.comp (c₀, (ψ₀, ν₀)) hpair
  have h2 : HasStrictFDerivAt (fun q : ℝ × (E × ℝ) => q.2.2 • q.2.1)
      (ν₀ • ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E × ℝ))) +
        ((ContinuousLinearMap.snd ℝ E ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (E × ℝ))).smulRight ψ₀)
      (c₀, (ψ₀, ν₀)) := hν.smul hφ
  have h3 : HasStrictFDerivAt (fun q : ℝ × (E × ℝ) => ⟪ψ₀, q.2.1⟫ - 1)
      ((innerSL ℝ ψ₀).comp
        ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E × ℝ))))
      (c₀, (ψ₀, ν₀)) := by
    have h := ((innerSL ℝ ψ₀).hasStrictFDerivAt (x := ψ₀)).comp (c₀, (ψ₀, ν₀)) hφ
    simpa using h.sub_const 1
  have hcomb := (h1.sub h2).prodMk h3
  have hEq : (((familyDeriv (A c₀) w).comp
        ((ContinuousLinearMap.fst ℝ ℝ (E × ℝ)).prod
          ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E × ℝ)))) -
      (ν₀ • ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E × ℝ))) +
        ((ContinuousLinearMap.snd ℝ E ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (E × ℝ))).smulRight ψ₀)).prod
      ((innerSL ℝ ψ₀).comp
        ((ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (E × ℝ)))))
      = eigenResidualDeriv T ψ₀ w := by
    refine ContinuousLinearMap.ext fun q => Prod.ext ?_ ?_
    · simp [eigenResidualDeriv, borderedMap, hT]
      abel
    · simp [eigenResidualDeriv, borderedMap]
  rw [hEq] at hcomb
  exact hcomb

/-! ## The branch -/

/-- **Existence of a differentiable simple eigenvalue branch.**  For a strictly differentiable family of
symmetric operators with a simple normalized eigenvalue `nu_0` at aperture `c_0`, and a pseudo-inverse `R` of
`A c_0 - nu_0` modulo the eigendirection, there is a differentiable eigenpair branch through `(psi_0, nu_0)`,
normalized against `psi_0`.

The mechanism is the implicit function theorem for the eigen-residual, whose partial derivative in the
eigenpair variables is the bordered map — invertible by simplicity. -/
theorem exists_differentiable_simple_eigen_branch [CompleteSpace E]
    {A : ℝ → E →L[ℝ] E} {R : E →L[ℝ] E} {c₀ ν₀ : ℝ} {ψ₀ w : E}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDeriv (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : E, ⟪A c₀ u, v⟫ = ⟪u, A c₀ v⟫)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫ = 1)
    (hker : ∀ φ : E, A c₀ φ = ν₀ • φ → ∃ s : ℝ, φ = s • ψ₀)
    (hR : ∀ y : E, A c₀ (R y) - ν₀ • R y = y - ⟪ψ₀, y⟫ • ψ₀)
    (hRψ : ∀ y : E, ⟪ψ₀, R y⟫ = 0) :
    ∃ (ψ : ℝ → E) (ν : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      DifferentiableAt ℝ ψ c₀ ∧ DifferentiableAt ℝ ν c₀ ∧
      ∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ₀, ψ c⟫ = 1 := by
  set T : E →L[ℝ] E := A c₀ - ν₀ • ContinuousLinearMap.id ℝ E with hTdef
  have hT : ∀ x : E, T x = A c₀ x - ν₀ • x := by
    intro x
    simp [hTdef]
  have hTψ : T ψ₀ = 0 := by
    rw [hT, heig, sub_self]
  have hTsymm : ∀ u v : E, ⟪T u, v⟫ = ⟪u, T v⟫ := by
    intro u v
    rw [hT, hT, inner_sub_left, inner_sub_right, hsymm u v, real_inner_smul_left,
      real_inner_smul_right]
  have hTker : ∀ φ : E, T φ = 0 → ∃ s : ℝ, φ = s • ψ₀ := by
    intro φ hφ
    rw [hT, sub_eq_zero] at hφ
    exact hker φ hφ
  have hTR : ∀ y : E, T (R y) = y - ⟪ψ₀, y⟫ • ψ₀ := by
    intro y
    rw [hT]
    exact hR y
  have hres := hasStrictFDerivAt_eigenResidual (ν₀ := ν₀) hA hT
  have hinv : ((eigenResidualDeriv T ψ₀ w).comp
      (ContinuousLinearMap.inr ℝ ℝ (E × ℝ))).IsInvertible := by
    rw [eigenResidualDeriv_comp_inr]
    exact borderedCLM_isInvertible hTsymm hTψ hnorm hTker hTR hRψ
  set g := hres.implicitFunctionOfProdDomain hinv with hg
  have hbase : g c₀ = (ψ₀, ν₀) :=
    (hres.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  have hstrict := hres.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  have hdiff : DifferentiableAt ℝ g c₀ := hstrict.differentiableAt
  have hev := hres.eventually_apply_implicitFunctionOfProdDomain hinv
  have hzero : eigenResidual A ψ₀ (c₀, (ψ₀, ν₀)) = (0, 0) := by
    have hunfold : eigenResidual A ψ₀ (c₀, (ψ₀, ν₀)) = (A c₀ ψ₀ - ν₀ • ψ₀, ⟪ψ₀, ψ₀⟫ - 1) := rfl
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
  simp only [eigenResidual, sub_eq_zero] at h1 h2
  exact ⟨h1, h2⟩

/-- **The branch can be taken normalized.**  Rescaling the branch of
`exists_differentiable_simple_eigen_branch` by `‖psi c‖⁻¹` preserves the eigenrelation, makes the
eigenfunction a unit vector, and is differentiable at the base point because the norm is `1` there. -/
theorem exists_differentiable_normalized_simple_eigen_branch [CompleteSpace E]
    {A : ℝ → E →L[ℝ] E} {R : E →L[ℝ] E} {c₀ ν₀ : ℝ} {ψ₀ w : E}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDeriv (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : E, ⟪A c₀ u, v⟫ = ⟪u, A c₀ v⟫)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫ = 1)
    (hker : ∀ φ : E, A c₀ φ = ν₀ • φ → ∃ s : ℝ, φ = s • ψ₀)
    (hR : ∀ y : E, A c₀ (R y) - ν₀ • R y = y - ⟪ψ₀, y⟫ • ψ₀)
    (hRψ : ∀ y : E, ⟪ψ₀, R y⟫ = 0) :
    ∃ (ψ : ℝ → E) (ν : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      DifferentiableAt ℝ ψ c₀ ∧ DifferentiableAt ℝ ν c₀ ∧
      ∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫ = 1 := by
  obtain ⟨ψ, ν, hψ0, hν0, hdψ, hdν, hev⟩ :=
    exists_differentiable_simple_eigen_branch hA hsymm heig hnorm hker hR hRψ
  have hψ₀ne : ψ₀ ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hnorm
    exact zero_ne_one hnorm
  have hnψ₀ : ‖ψ₀‖ = 1 := by
    have h := real_inner_self_eq_norm_sq ψ₀
    rw [hnorm] at h
    nlinarith [norm_nonneg ψ₀]
  have hne : ψ c₀ ≠ 0 := by rw [hψ0]; exact hψ₀ne
  have hdn : DifferentiableAt ℝ (fun c => ‖ψ c‖) c₀ := hdψ.norm ℝ hne
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
  refine ⟨?_, ?_⟩
  · rw [map_smul, hrel, smul_comm]
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp

/-- **Hellmann–Feynman for a simple eigenvalue of a differentiable family**, with no branch input at all: the
branch is constructed, and its eigenvalue derivative is the expectation of the family's motion,

```text
nu'(c_0) = ⟪psi_0, w⟫.
```

This is the perturbation-theoretic statement that a differentiable simple eigenvalue branch exists *and*
obeys the Hellmann–Feynman law; the only structural inputs are symmetry, simplicity, and the pseudo-inverse
that simplicity provides. -/
theorem exists_normalized_branch_deriv_eq_expectation [CompleteSpace E]
    {A : ℝ → E →L[ℝ] E} {R : E →L[ℝ] E} {c₀ ν₀ : ℝ} {ψ₀ w : E}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDeriv (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : E, ⟪A c₀ u, v⟫ = ⟪u, A c₀ v⟫)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫ = 1)
    (hker : ∀ φ : E, A c₀ φ = ν₀ • φ → ∃ s : ℝ, φ = s • ψ₀)
    (hR : ∀ y : E, A c₀ (R y) - ν₀ • R y = y - ⟪ψ₀, y⟫ • ψ₀)
    (hRψ : ∀ y : E, ⟪ψ₀, R y⟫ = 0) :
    ∃ (ψ : ℝ → E) (ν : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫ = 1) ∧
      HasDerivAt ν ⟪ψ₀, w⟫ c₀ := by
  obtain ⟨ψ, ν, hψ0, hν0, hdψ, hdν, hev⟩ :=
    exists_differentiable_normalized_simple_eigen_branch hA hsymm heig hnorm hker hR hRψ
  refine ⟨ψ, ν, hψ0, hν0, hev, ?_⟩
  -- the branch derivatives
  set ψ' := deriv ψ c₀ with hψ'
  have hψd : HasDerivAt ψ ψ' c₀ := hdψ.hasDerivAt
  have hνd : HasDerivAt ν (deriv ν c₀) c₀ := hdν.hasDerivAt
  -- the family's motion along the branch
  have hcurve : HasDerivAt (fun t : ℝ => (t, ψ t)) (1, ψ') c₀ := (hasDerivAt_id c₀).prodMk hψd
  have hA' : HasFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDeriv (A c₀) w) (c₀, ψ c₀) := by
    rw [hψ0]
    exact hA.hasFDerivAt
  have hAψ : HasDerivAt (fun t => A t (ψ t)) (w + A c₀ ψ') c₀ := by
    have h := hA'.comp_hasDerivAt c₀ hcurve
    simpa [Function.comp_def] using h
  have hnorm' : ⟪ψ c₀, ψ c₀⟫ = 1 := by rw [hψ0]; exact hnorm
  have hsa : ⟪ψ c₀, A c₀ ψ'⟫ = ⟪A c₀ (ψ c₀), ψ'⟫ := by
    rw [hψ0]
    exact (hsymm ψ₀ ψ').symm
  have hkey := hellmann_feynman_eventually (A := fun t => (A t : E → E)) hnorm' hsa hνd hψd hAψ
    (hev.mono fun c hc => hc.1)
  rw [hψ0] at hkey
  rw [hkey] at hνd
  exact hνd

end GaloisForLFunctions.HTGeometry

end
