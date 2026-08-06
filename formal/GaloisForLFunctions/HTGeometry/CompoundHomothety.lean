import GaloisForLFunctions.HTGeometry.CompoundExponentialTransport

/-!
# The homothety contraction on the compound

Two exponential rays compared at time one, in the sense of Hermitian forms on the `k`-th compound,
stay compared at every earlier time with the bound raised to that power:

```text
Λᵏ Q₁ ≤ c Λᵏ P₁   →   Λᵏ Q_t ≤ c ^ t Λᵏ P_t     (0 ≤ t ≤ 1).
```

The compound of an exponential ray is again an exponential ray, so the comparison can be read in
the C⋆-algebra of operators, where operator monotonicity of the `t`-th power applies; the result is
read back as a comparison of forms.  Composed with the two Ky Fan lemmas this is the
log-majorization of the pencil spectra: every `k`-fold subset product at time `t` is at most the
`t`-th power of the bound at time one.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-! ## Exponential rays of matrices -/

/-- The exponential ray of a Hermitian matrix presented in diagonalised form. -/
noncomputable def expRayMat (V : Matrix ι ι ℂ) (p : ι → ℝ) (t : ℝ) : Matrix ι ι ℂ :=
  Vᴴ * (rdiag fun i => Real.exp (t * p i)) * V

omit [LinearOrder ι] in
theorem isHermitian_expRayMat (V : Matrix ι ι ℂ) (p : ι → ℝ) (t : ℝ) :
    (expRayMat V p t).IsHermitian :=
  isHermitian_conj_rdiag' _ _

theorem isHermitian_compound_expRayMat (k : ℕ) (V : Matrix ι ι ℂ) (p : ι → ℝ) (t : ℝ) :
    (compound k (expRayMat V p t)).IsHermitian :=
  compound_isHermitian (isHermitian_expRayMat V p t)

/-! ## The compound of an exponential ray, as an operator -/

/-- The generator that the compound of an exponential ray runs along. -/
noncomputable def compoundGenCLM (k : ℕ) (V : Matrix ι ι ℂ) (p : ι → ℝ) :
    EuclideanSpace ℂ (Set.powersetCard ι k) →L[ℂ] EuclideanSpace ℂ (Set.powersetCard ι k) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (compoundGen k V p)

theorem isSelfAdjoint_compoundGenCLM (k : ℕ) (V : Matrix ι ι ℂ) (p : ι → ℝ) :
    IsSelfAdjoint (compoundGenCLM k V p) :=
  isSelfAdjoint_toEuclideanCLM (isHermitian_compoundGen k V p)

theorem toEuclideanCLM_compound_expRayMat (k : ℕ) {V : Matrix ι ι ℂ}
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) (p : ι → ℝ) (t : ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (compound k (expRayMat V p t))
      = NormedSpace.exp (t • compoundGenCLM k V p) := by
  have hmat : compound k (expRayMat V p t) = NormedSpace.exp ((t : ℂ) • compoundGen k V p) := by
    rw [expRayMat, compound_conj_rdiag_exp, exp_smul_compoundGen k hV]
  rw [hmat, toEuclideanCLM_exp, map_smul, compoundGenCLM, coe_smul_clm]

/-! ## The contraction -/

/-- The comparison at time one, read in the operator order. -/
theorem exp_le_smul_exp_of_quadForm {k : ℕ} {V W : Matrix ι ι ℂ}
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) (hW : W ∈ Matrix.unitaryGroup ι ℂ)
    (p q : ι → ℝ) {c : ℝ}
    (h1 : ∀ x, (matQuadForm (compound k (expRayMat W q 1)) x).re
      ≤ c * (matQuadForm (compound k (expRayMat V p 1)) x).re) :
    NormedSpace.exp (compoundGenCLM k W q) ≤ c • NormedSpace.exp (compoundGenCLM k V p) := by
  have h := (toEuclideanCLM_smul_le_iff (isHermitian_compound_expRayMat k W q 1)
    (isHermitian_compound_expRayMat k V p 1) c).2 h1
  rwa [toEuclideanCLM_compound_expRayMat k hV p 1,
    toEuclideanCLM_compound_expRayMat k hW q 1, one_smul, one_smul] at h

/-- The comparison at time `t`, read back as forms. -/
theorem quadForm_le_of_exp_le {k : ℕ} {V W : Matrix ι ι ℂ}
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) (hW : W ∈ Matrix.unitaryGroup ι ℂ)
    (p q : ι → ℝ) {d t : ℝ}
    (hle : NormedSpace.exp (t • compoundGenCLM k W q)
      ≤ d • NormedSpace.exp (t • compoundGenCLM k V p))
    (x : Set.powersetCard ι k → ℂ) :
    (matQuadForm (compound k (expRayMat W q t)) x).re
      ≤ d * (matQuadForm (compound k (expRayMat V p t)) x).re := by
  rw [← toEuclideanCLM_compound_expRayMat k hV p t,
    ← toEuclideanCLM_compound_expRayMat k hW q t,
    toEuclideanCLM_smul_le_iff (isHermitian_compound_expRayMat k W q t)
      (isHermitian_compound_expRayMat k V p t) d] at hle
  exact hle x

/-- **The comparison of compound forms of two exponential rays contracts along the rays.** -/
theorem quadForm_compound_expRay_le {k : ℕ} {V W : Matrix ι ι ℂ}
    (hV : V ∈ Matrix.unitaryGroup ι ℂ) (hW : W ∈ Matrix.unitaryGroup ι ℂ)
    (p q : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (h1 : ∀ x, (matQuadForm (compound k (expRayMat W q 1)) x).re
      ≤ c * (matQuadForm (compound k (expRayMat V p 1)) x).re)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Set.powersetCard ι k → ℂ) :
    (matQuadForm (compound k (expRayMat W q t)) x).re
      ≤ c ^ t * (matQuadForm (compound k (expRayMat V p t)) x).re := by
  have hle1 : NormedSpace.exp (compoundGenCLM k W q)
      ≤ c • NormedSpace.exp (compoundGenCLM k V p) :=
    exp_le_smul_exp_of_quadForm hV hW p q h1
  have hle2 : NormedSpace.exp (t • compoundGenCLM k W q)
      ≤ (c ^ t) • NormedSpace.exp (t • compoundGenCLM k V p) :=
    exp_smul_le_of_exp_le (isSelfAdjoint_compoundGenCLM k V p)
      (isSelfAdjoint_compoundGenCLM k W q) hc hle1 ht0 ht1
  exact quadForm_le_of_exp_le hV hW p q hle2 x

end GaloisForLFunctions.HTGeometry
