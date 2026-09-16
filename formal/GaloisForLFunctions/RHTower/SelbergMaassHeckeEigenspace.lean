import GaloisForLFunctions.RHTower.SelbergMaassTraceBaseChange

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open scoped MatrixGroups ContDiff
open SelbergMaassTraceEnergy

noncomputable section

private theorem dir_add {F G : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) (v : ℂ) :
    dir v (fun w => F w + G w) z = dir v F z + dir v G z := by
  change (fderiv ℝ (F + G) z) v = dir v F z + dir v G z
  rw [fderiv_add hF hG]
  rfl

private theorem second_dir_add {F G : ℂ → ℂ} {z : ℂ}
    (hF : ContDiffAt ℝ 2 F z) (hG : ContDiffAt ℝ 2 G z) (v : ℂ) :
    dir v (dir v (F + G)) z =
      dir v (dir v F) z + dir v (dir v G) z := by
  have he : dir v (F + G) =ᶠ[𝓝 z]
      (fun w => dir v F w + dir v G w) := by
    filter_upwards [hF.eventually (by norm_num), hG.eventually (by norm_num)] with w hwF hwG
    exact dir_add (hwF.differentiableAt (by norm_num)) (hwG.differentiableAt (by norm_num)) v
  change fderiv ℝ (dir v (F + G)) z v = _
  rw [he.fderiv_eq]
  exact dir_add ((dir_contDiffAt hF v).differentiableAt (by norm_num))
    ((dir_contDiffAt hG v).differentiableAt (by norm_num)) v

private theorem dir_const_smul {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) (c v : ℂ) :
    dir v (fun w => c • F w) z = c • dir v F z := by
  change (fderiv ℝ (fun w => c • F w) z) v = c • fderiv ℝ F z v
  rw [fderiv_fun_const_smul hF]
  rfl

private theorem second_dir_const_smul {F : ℂ → ℂ} {z : ℂ}
    (hF : ContDiffAt ℝ 2 F z) (c v : ℂ) :
    dir v (dir v (c • F)) z = c • dir v (dir v F) z := by
  have he : dir v (c • F) =ᶠ[𝓝 z] (fun w => c • dir v F w) := by
    filter_upwards [hF.eventually (by norm_num)] with w hwF
    exact dir_const_smul (hwF.differentiableAt (by norm_num)) c v
  change fderiv ℝ (dir v (c • F)) z v = _
  rw [he.fderiv_eq]
  exact dir_const_smul ((dir_contDiffAt hF v).differentiableAt (by norm_num)) c v

/-- Zero-inclusive GL-invariant Maass cusp eigenspace at a fixed eigenvalue. -/
def glMaassCuspEigenspace (Γ : Subgroup (GL (Fin 2) ℝ)) (lam : ℝ) :
    Submodule ℂ (ℍ → ℂ) where
  carrier := {f | (∀ γ : Γ, ∀ z : ℍ, f (γ.1 • z) = f z) ∧
    IsMaassEigenfunction lam f ∧ IsCuspidalAtIntegralCusps f}
  zero_mem' := by
    constructor
    · intro γ z
      rfl
    constructor
    · constructor
      · exact contDiff_const.contDiffOn
      · intro z
        simp [positiveHyperbolicLaplacian]
    · intro σ
      exact tendsto_const_nhds
  add_mem' := by
    intro f g hf hg
    constructor
    · intro γ z
      simp only [Pi.add_apply, hf.1 γ z, hg.1 γ z]
    constructor
    · constructor
      · exact hf.2.1.1.add hg.2.1.1
      · intro z
        have hfz : ContDiffAt ℝ 2 (f ∘ ofComplex) (z : ℂ) :=
          hf.2.1.1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
        have hgz : ContDiffAt ℝ 2 (g ∘ ofComplex) (z : ℂ) :=
          hg.2.1.1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
        have he : positiveHyperbolicLaplacian (f + g) z =
            positiveHyperbolicLaplacian f z + positiveHyperbolicLaplacian g z := by
          change -(z.im : ℂ) ^ 2 *
              (dir 1 (dir 1 ((f ∘ ofComplex) + (g ∘ ofComplex))) (z : ℂ) +
                dir Complex.I (dir Complex.I ((f ∘ ofComplex) + (g ∘ ofComplex))) (z : ℂ)) =
            -(z.im : ℂ) ^ 2 *
              (dir 1 (dir 1 (f ∘ ofComplex)) (z : ℂ) +
                dir Complex.I (dir Complex.I (f ∘ ofComplex)) (z : ℂ)) +
            -(z.im : ℂ) ^ 2 *
              (dir 1 (dir 1 (g ∘ ofComplex)) (z : ℂ) +
                dir Complex.I (dir Complex.I (g ∘ ofComplex)) (z : ℂ))
          rw [second_dir_add hfz hgz, second_dir_add hfz hgz]
          ring
        rw [he, hf.2.1.2 z, hg.2.1.2 z]
        simp only [Pi.add_apply]
        ring
    · intro σ
      change Tendsto ((fun z : ℍ => f (integralSL2ToReal σ • z)) +
        fun z : ℍ => g (integralSL2ToReal σ • z)) atImInfty (𝓝 (0 : ℂ))
      exact (hf.2.2 σ).add (hg.2.2 σ)
  smul_mem' := by
    intro c f hf
    constructor
    · intro γ z
      simp only [Pi.smul_apply, hf.1 γ z]
    constructor
    · constructor
      · exact hf.2.1.1.const_smul c
      · intro z
        have hfz : ContDiffAt ℝ 2 (f ∘ ofComplex) (z : ℂ) :=
          hf.2.1.1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
        have he : positiveHyperbolicLaplacian (c • f) z =
            c • positiveHyperbolicLaplacian f z := by
          change -(z.im : ℂ) ^ 2 *
              (dir 1 (dir 1 (c • (f ∘ ofComplex))) (z : ℂ) +
                dir Complex.I (dir Complex.I (c • (f ∘ ofComplex))) (z : ℂ)) =
            c • (-(z.im : ℂ) ^ 2 *
              (dir 1 (dir 1 (f ∘ ofComplex)) (z : ℂ) +
                dir Complex.I (dir Complex.I (f ∘ ofComplex)) (z : ℂ)))
          rw [second_dir_const_smul hfz c, second_dir_const_smul hfz c]
          simp only [smul_eq_mul]
          ring
        rw [he, hf.2.1.2 z]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    · intro σ
      simpa only [IsZeroAtImInfty, ZeroAtFilter, Pi.smul_apply, smul_eq_mul, mul_zero] using
        (hf.2.2 σ).const_smul c


/-- Forget the eigenfunction and cusp conditions while retaining GL invariance. -/
def maassEigenspaceToInvariant
    {Γ : Subgroup (GL (Fin 2) ℝ)} {lam : ℝ}
    (f : glMaassCuspEigenspace Γ lam) : glUpperHalfPlaneInvariantFunctions Γ :=
  ⟨f.1, f.2.1⟩

/-- The finite principal trace of the zero invariant function is zero. -/
theorem principalMaassTrace_zero
    (N : ℕ) {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsFiniteRelIndex (principalCongruenceGL N)] :
    maassTraceFunction (H := principalCongruenceGL N)
      (0 : glUpperHalfPlaneInvariantFunctions Γ) = 0 :=
  congrArg Subtype.val
    ((maassTraceLinear (G := Γ) (H := principalCongruenceGL N)).map_zero)

/-- The finite principal trace as a linear map on the zero-inclusive fixed Maass eigenspace. -/
def principalMaassTraceLinear
    (N : ℕ) (lam : ℝ) {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsFiniteRelIndex (principalCongruenceGL N)] :
    glMaassCuspEigenspace Γ lam →ₗ[ℂ]
      glMaassCuspEigenspace (principalCongruenceGL N) lam where
  toFun f := ⟨maassTraceFunction (H := principalCongruenceGL N)
      (maassEigenspaceToInvariant f), by
    refine ⟨(maassTraceInvariant (H := principalCongruenceGL N)
      (maassEigenspaceToInvariant f)).2, ?_, ?_⟩
    · exact ⟨principalMaassTrace_smooth_of_data N lam
        (maassEigenspaceToInvariant f) f.2.2.1,
        principalMaassTrace_eigen_of_data N lam
          (maassEigenspaceToInvariant f) f.2.2.1⟩
    · exact principalMaassTrace_cuspidal_of_data N
        (maassEigenspaceToInvariant f) f.2.2.2⟩
  map_add' f g := by
    apply Subtype.ext
    change maassTraceFunction (H := principalCongruenceGL N) (maassEigenspaceToInvariant (f + g)) =
      maassTraceFunction (H := principalCongruenceGL N) (maassEigenspaceToInvariant f) +
        maassTraceFunction (H := principalCongruenceGL N) (maassEigenspaceToInvariant g)
    have hfg : maassEigenspaceToInvariant (f + g) = maassEigenspaceToInvariant f + maassEigenspaceToInvariant g := by
      apply Subtype.ext
      rfl
    rw [hfg]
    exact maassTraceFunction_add (maassEigenspaceToInvariant f) (maassEigenspaceToInvariant g)
  map_smul' c f := by
    apply Subtype.ext
    change maassTraceFunction (H := principalCongruenceGL N) (maassEigenspaceToInvariant (c • f)) =
      c • maassTraceFunction (H := principalCongruenceGL N) (maassEigenspaceToInvariant f)
    have hcf : maassEigenspaceToInvariant (c • f) = c • maassEigenspaceToInvariant f := by
      apply Subtype.ext
      rfl
    rw [hcf]
    exact maassTraceFunction_smul c (maassEigenspaceToInvariant f)

/-- Finite trace to a rationally conjugated principal group as a complex-linear
map of zero-inclusive Maass cusp eigenspaces. -/
def rationalConjugateMaassTraceLinear
    (N : ℕ) (g : GL (Fin 2) ℚ) (lam : ℝ) {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsFiniteRelIndex (rationalConjugateGroup N g)] :
    glMaassCuspEigenspace Γ lam →ₗ[ℂ]
      glMaassCuspEigenspace (rationalConjugateGroup N g) lam where
  toFun f := ⟨maassTraceFunction (H := rationalConjugateGroup N g)
      (maassEigenspaceToInvariant f), by
    refine ⟨(maassTraceInvariant (H := rationalConjugateGroup N g)
      (maassEigenspaceToInvariant f)).2, ?_, ?_⟩
    · exact ⟨rationalConjugateMaassTrace_smooth_of_data N g lam
        (maassEigenspaceToInvariant f) f.2.2.1,
        rationalConjugateMaassTrace_eigen_of_data N g lam
          (maassEigenspaceToInvariant f) f.2.2.1⟩
    · exact rationalConjugateMaassTrace_cuspidal_of_data N g
        (maassEigenspaceToInvariant f) f.2.2.2⟩
  map_add' f h := by
    apply Subtype.ext
    change maassTraceFunction (H := rationalConjugateGroup N g) (maassEigenspaceToInvariant (f + h)) =
      maassTraceFunction (H := rationalConjugateGroup N g) (maassEigenspaceToInvariant f) +
        maassTraceFunction (H := rationalConjugateGroup N g) (maassEigenspaceToInvariant h)
    have hfh : maassEigenspaceToInvariant (f + h) =
        maassEigenspaceToInvariant f + maassEigenspaceToInvariant h := by
      apply Subtype.ext
      rfl
    rw [hfh]
    exact maassTraceFunction_add (maassEigenspaceToInvariant f) (maassEigenspaceToInvariant h)
  map_smul' c f := by
    apply Subtype.ext
    change maassTraceFunction (H := rationalConjugateGroup N g) (maassEigenspaceToInvariant (c • f)) =
      c • maassTraceFunction (H := rationalConjugateGroup N g) (maassEigenspaceToInvariant f)
    have hcf : maassEigenspaceToInvariant (c • f) = c • maassEigenspaceToInvariant f := by
      apply Subtype.ext
      rfl
    rw [hcf]
    exact maassTraceFunction_smul c (maassEigenspaceToInvariant f)

/-- The finite trace between any two rational conjugates of one principal
congruence group is a linear Maass-eigenspace map. -/
def rationalConjugateGroupsTraceLinear
    (N : ℕ) (g h : GL (Fin 2) ℚ) (lam : ℝ) :
    glMaassCuspEigenspace (rationalConjugateGroup N g) lam →ₗ[ℂ]
      glMaassCuspEigenspace (rationalConjugateGroup N h) lam := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (rationalConjugateGroup N h) :=
    rationalConjugateGroups_isFiniteRelIndex N g h
  exact rationalConjugateMaassTraceLinear N h lam

/-- Positive rational pullback as a linear map of zero-inclusive Maass eigenspaces.
Unlike the finite trace, this construction is defined for every invariant subgroup. -/
def rationalMaassPullbackLinearOfGroup
    (Γ : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ) :
    glMaassCuspEigenspace Γ lam →ₗ[ℂ]
      glMaassCuspEigenspace (rationalPullbackConjugateGroup Γ g) lam where
  toFun f := ⟨fun z => f.1 (g.map (algebraMap ℚ ℝ) • z), by
    have hpull := rationalGL_maass_eigenfunction_cuspidal_pullback g hg lam f.1 f.2.2.1 f.2.2.2
    exact ⟨(rationalMaassPullbackInvariant_general Γ g
      (maassEigenspaceToInvariant f)).2, hpull.1, hpull.2⟩
  ⟩
  map_add' f h := by
    apply Subtype.ext
    funext z
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext z
    rfl

/-- Successive generic rational pullbacks have the same underlying function as
pullback by the product matrix. The target subgroup equality is recorded
separately by `rationalPullbackConjugateGroup_mul`. -/
theorem rationalMaassPullbackLinearOfGroup_comp_apply
    {Γ : Subgroup (GL (Fin 2) ℝ)} (g h : GL (Fin 2) ℚ) (lam : ℝ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det)
    (hh : 0 < (h.map (algebraMap ℚ ℝ)).val.det)
    (f : glMaassCuspEigenspace Γ lam) :
    ((rationalMaassPullbackLinearOfGroup (rationalPullbackConjugateGroup Γ g) h hh lam)
      ((rationalMaassPullbackLinearOfGroup Γ g hg lam) f)).1 =
      ((rationalMaassPullbackLinearOfGroup Γ (g * h)
        (rationalGL_map_det_mul_pos g h hg hh) lam) f).1 := by
  funext z
  change f.1 (g.map (algebraMap ℚ ℝ) • (h.map (algebraMap ℚ ℝ) • z)) =
    f.1 ((g * h).map (algebraMap ℚ ℝ) • z)
  rw [← mul_smul]
  rw [← Matrix.GeneralLinearGroup.map_mul]

/-- The principal-level rational pullback is the generic pullback specialized to
the principal congruence subgroup. -/
def rationalMaassPullbackLinear
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ) :
    glMaassCuspEigenspace (principalCongruenceGL N) lam →ₗ[ℂ]
      glMaassCuspEigenspace (rationalConjugateGroup N g) lam :=
  rationalMaassPullbackLinearOfGroup (principalCongruenceGL N) g hg lam

/-- Rational pullback followed by finite principal trace is a genuine linear endomorphism
of the fixed principal-level Maass eigenspace. -/
def rationalPrincipalTraceLinear
    (N : ℕ) (g : GL (Fin 2) ℚ)
    (hg : 0 < (g.map (algebraMap ℚ ℝ)).val.det) (lam : ℝ) :
    glMaassCuspEigenspace (principalCongruenceGL N) lam →ₗ[ℂ]
      glMaassCuspEigenspace (principalCongruenceGL N) lam := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  exact (principalMaassTraceLinear N lam (Γ := rationalConjugateGroup N g)).comp
    (rationalMaassPullbackLinear N g hg lam)

end
end GaloisForLFunctions.RHTower
