import GaloisForLFunctions.HTGeometry.LinearSpectralRelationOrbitPolynomial

/-!
# The labeling-orbit obstruction of an **affine** spectral relation

`LinearSpectralRelationOrbitPolynomial` builds the orbit obstruction of a homogeneous relation
`∑_i c_i X_i`.  A relation that is merely *constant* on a parameter chart — which is what
nondegeneracy of a spectral map rules out — is affine, `∑_i c_i X_i = target`, and its obstruction is

  `Ω_{c,t} = ∏_{σ ∈ S_I} (∑_i c_i X_{σ i} - t) ∈ MvPolynomial I K`.

Nothing changes: renaming fixes the constant, so the orbit is still symmetric, and the coefficient of
`X_i` in the affine form is still `c_i`, so the orbit is still nonzero for `c ≠ 0`, whatever the
target.

## Main results

* `affineRelationPoly`, `affineRelationOrbit`, `affineRelationOrbitValue` — the affine form, its
  labeling orbit, and the numerical value of the orbit.
* `affineRelationOrbit_isSymmetric`, `affineRelationOrbit_ne_zero`.
* `affineRelationCoefficient`, `eval_affineRelationCoefficient_esymm` — the obstruction as a
  polynomial in the elementary symmetric functions of the spectrum.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [CommRing K] [IsDomain K] {I : Type*} [Fintype I]

/-- The affine form of a spectral relation with a prescribed constant value. -/
def affineRelationPoly (c : I → K) (target : K) : MvPolynomial I K :=
  linearRelationPoly c - MvPolynomial.C target

omit [IsDomain K] in
@[simp] theorem affineRelationPoly_zero (c : I → K) :
    affineRelationPoly c 0 = linearRelationPoly c := by
  simp [affineRelationPoly]

/-- The product of the affine form over every relabeling. -/
def affineRelationOrbit (c : I → K) (target : K) : MvPolynomial I K := by
  classical
  exact ∏ σ : Equiv.Perm I, MvPolynomial.rename σ (affineRelationPoly c target)

/-- The numerical value of the affine orbit obstruction on a spectrum. -/
def affineRelationOrbitValue (c : I → K) (target : K) (energy : I → K) : K := by
  classical
  exact ∏ σ : Equiv.Perm I, ((∑ i, c i * energy (σ i)) - target)

theorem affineRelationOrbitValue_ne_zero_iff (c : I → K) (target : K) (energy : I → K) :
    affineRelationOrbitValue c target energy ≠ 0 ↔
      ∀ σ : Equiv.Perm I, ∑ i, c i * energy (σ i) ≠ target := by
  classical
  unfold affineRelationOrbitValue
  rw [Finset.prod_ne_zero_iff]
  simp [sub_eq_zero]

omit [IsDomain K] in
/-- The affine form is nonzero for a nonzero coefficient vector, whatever the target: the constant
contributes nothing to the coefficient of a single variable. -/
theorem affineRelationPoly_ne_zero [DecidableEq I] {c : I → K} (hc : c ≠ 0) (target : K) :
    affineRelationPoly c target ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    exact hc (funext fun i => by
      by_contra h
      exact hcon ⟨i, h⟩)
  intro h0
  have hlin : MvPolynomial.coeff (Finsupp.single i 1) (linearRelationPoly c) = c i := by
    unfold linearRelationPoly
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single i]
    · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    · intro j _ hji
      simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Finsupp.single_eq_single_iff]
      rw [if_neg (by simp [hji]), mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  have hconst : MvPolynomial.coeff (Finsupp.single i 1) (MvPolynomial.C target) = 0 := by
    rw [MvPolynomial.coeff_C, if_neg]
    intro hzero
    have := congrArg (fun f : I →₀ ℕ => f i) hzero
    simp at this
  have hcoeff :
      MvPolynomial.coeff (Finsupp.single i 1) (affineRelationPoly c target) = c i := by
    rw [affineRelationPoly, MvPolynomial.coeff_sub, hlin, hconst, sub_zero]
  rw [h0] at hcoeff
  simp at hcoeff
  exact hi hcoeff.symm

/-- The affine orbit obstruction is nonzero for a nonzero coefficient vector. -/
theorem affineRelationOrbit_ne_zero [DecidableEq I] {c : I → K} (hc : c ≠ 0) (target : K) :
    affineRelationOrbit c target ≠ 0 := by
  classical
  unfold affineRelationOrbit
  refine Finset.prod_ne_zero_iff.mpr fun σ _ => ?_
  intro h0
  exact affineRelationPoly_ne_zero hc target
    ((MvPolynomial.rename_injective (σ : I → I) σ.injective) (by simpa using h0))

omit [IsDomain K] in
/-- The affine orbit obstruction is a symmetric polynomial. -/
theorem affineRelationOrbit_isSymmetric (c : I → K) (target : K) :
    (affineRelationOrbit c target).IsSymmetric := by
  classical
  intro τ
  unfold affineRelationOrbit
  rw [map_prod]
  refine Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  rw [MvPolynomial.rename_rename]
  rfl

/-- The affine orbit obstruction rewritten in the elementary symmetric coordinates. -/
def affineRelationCoefficient (c : I → K) (target : K) :
    MvPolynomial (Fin (Fintype.card I)) K :=
  (MvPolynomial.esymmAlgEquiv I K rfl).symm
    ⟨affineRelationOrbit c target, affineRelationOrbit_isSymmetric c target⟩

omit [IsDomain K] in
theorem esymmAlgHom_affineRelationCoefficient (c : I → K) (target : K) :
    (MvPolynomial.esymmAlgHom I K (Fintype.card I) (affineRelationCoefficient c target)).1
      = affineRelationOrbit c target := by
  change
    ((MvPolynomial.esymmAlgEquiv I K rfl) (affineRelationCoefficient c target)).1
      = affineRelationOrbit c target
  simp [affineRelationCoefficient]

/-- **A nonzero affine relation has a nonzero obstruction already at the level of the unordered
characteristic coefficients.** -/
theorem affineRelationCoefficient_ne_zero [DecidableEq I] {c : I → K} (hc : c ≠ 0) (target : K) :
    affineRelationCoefficient c target ≠ 0 := by
  intro hzero
  refine affineRelationOrbit_ne_zero hc target ?_
  rw [← esymmAlgHom_affineRelationCoefficient c target, hzero]
  simp

omit [IsDomain K] in
theorem eval_affineRelationOrbit (c : I → K) (target : K) (energy : I → K) :
    MvPolynomial.eval energy (affineRelationOrbit c target)
      = affineRelationOrbitValue c target energy := by
  classical
  simp only [affineRelationOrbit, affineRelationOrbitValue, map_prod, MvPolynomial.eval_rename]
  refine Finset.prod_congr rfl fun σ _ => ?_
  simp [affineRelationPoly, linearRelationPoly, Function.comp_apply]

omit [IsDomain K] in
/-- **Evaluating the affine coefficient obstruction on elementary symmetric spectral data reproduces
the label-orbit obstruction.** -/
theorem eval_affineRelationCoefficient_esymm (c : I → K) (target : K) (energy : I → K) :
    MvPolynomial.eval
        (fun i : Fin (Fintype.card I) =>
          MvPolynomial.eval energy (MvPolynomial.esymm I K (i + 1)))
        (affineRelationCoefficient c target)
      = affineRelationOrbitValue c target energy := by
  have h := congrArg (MvPolynomial.aeval energy) (esymmAlgHom_affineRelationCoefficient c target)
  rw [MvPolynomial.esymmAlgHom_apply] at h
  simp only [MvPolynomial.comp_aeval_apply] at h
  have hid : algebraMap K K = RingHom.id K := by
    ext x
    rfl
  rw [← eval_affineRelationOrbit]
  simpa only [MvPolynomial.aeval_def, hid, MvPolynomial.eval₂_id] using h

end

end GaloisForLFunctions.HTGeometry
