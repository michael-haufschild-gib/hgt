import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic

/-!
# The labeling-orbit obstruction of a linear spectral relation, over any domain

The corpus already carries the labeling-orbit obstruction of an *integer* spectral character, as a
polynomial over `ℚ` (`SpectralRelationOrbitPolynomial`), and the *quadratic-rate* relation over an
arbitrary domain (`QuadraticRateOrbitPolynomialField`).  The real-relation rigidity that metric
recurrence exponents need is the **linear** relation over an arbitrary domain — in the application
`K = ℝ`: for `c : I → K`,

  `Ω_c = ∏_{σ ∈ S_I} ∑_i c_i X_{σ i} ∈ MvPolynomial I K`

is symmetric, and it is nonzero as soon as `c ≠ 0`.  Being symmetric it is a polynomial in the
elementary symmetric functions, hence a polynomial in the characteristic-polynomial coefficients of
a Hermitian family — so `∑_i c_i E_i ≡ 0` on any nonempty open set forces `Ω_c` to vanish
identically, which it does not.  That is what makes the real-relation statement **global**: it needs
no connectedness of the simple-spectrum locus.

## Main results

* `linearRelationPoly`, `linearRelationOrbit` — the linear form and its labeling orbit.
* `linearRelationOrbit_isSymmetric` — the orbit is a symmetric polynomial.
* `linearRelationOrbit_ne_zero` — it is nonzero for every nonzero coefficient vector.
* `linearRelationOrbitValue_ne_zero_iff` — its value is nonzero exactly when every relabeling of the
  relation is.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [CommRing K] [IsDomain K] {I : Type*} [Fintype I]

/-- The linear form of a real spectral relation. -/
def linearRelationPoly (c : I → K) : MvPolynomial I K :=
  ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i

/-- The product of the linear form over every relabeling. -/
def linearRelationOrbit (c : I → K) : MvPolynomial I K := by
  classical
  exact ∏ σ : Equiv.Perm I, MvPolynomial.rename σ (linearRelationPoly c)

/-- The numerical value of the orbit obstruction on a spectrum. -/
def linearRelationOrbitValue (c : I → K) (energy : I → K) : K := by
  classical
  exact ∏ σ : Equiv.Perm I, ∑ i, c i * energy (σ i)

theorem linearRelationOrbitValue_ne_zero_iff (c : I → K) (energy : I → K) :
    linearRelationOrbitValue c energy ≠ 0 ↔
      ∀ σ : Equiv.Perm I, ∑ i, c i * energy (σ i) ≠ 0 := by
  classical
  unfold linearRelationOrbitValue
  rw [Finset.prod_ne_zero_iff]
  simp

omit [IsDomain K] in
/-- The linear form is nonzero for a nonzero coefficient vector. -/
private theorem linearRelationPoly_ne_zero [DecidableEq I] {c : I → K} (hc : c ≠ 0) :
    linearRelationPoly c ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hcon
    exact hc (funext fun i => by
      by_contra h
      exact hcon ⟨i, h⟩)
  intro h0
  have hcoeff : MvPolynomial.coeff (Finsupp.single i 1) (linearRelationPoly c) = c i := by
    unfold linearRelationPoly
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single i]
    · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    · intro j _ hji
      simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Finsupp.single_eq_single_iff]
      rw [if_neg (by simp [hji]), mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ i) hmem
  rw [h0] at hcoeff
  simp at hcoeff
  exact hi hcoeff.symm

/-- The orbit obstruction is nonzero for a nonzero coefficient vector. -/
theorem linearRelationOrbit_ne_zero [DecidableEq I] {c : I → K} (hc : c ≠ 0) :
    linearRelationOrbit c ≠ 0 := by
  classical
  unfold linearRelationOrbit
  refine Finset.prod_ne_zero_iff.mpr fun σ _ => ?_
  intro h0
  exact linearRelationPoly_ne_zero hc
    ((MvPolynomial.rename_injective (σ : I → I) σ.injective) (by simpa using h0))

omit [IsDomain K] in
/-- The orbit obstruction is a symmetric polynomial. -/
theorem linearRelationOrbit_isSymmetric (c : I → K) :
    (linearRelationOrbit c).IsSymmetric := by
  classical
  intro τ
  unfold linearRelationOrbit
  rw [map_prod]
  refine Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  rw [MvPolynomial.rename_rename]
  rfl

/-! ### The obstruction as a polynomial in the characteristic coefficients

Being symmetric, the orbit obstruction is a polynomial in the elementary symmetric functions of the
spectrum — that is, in the coefficients of the characteristic polynomial, which are polynomials in
the Hamiltonian's parameters.  This is what makes "no identical real relation" a *global* statement:
the obstruction is a genuine polynomial function of the parameters, so it cannot vanish on a
nonempty open set without vanishing everywhere.
-/

/-- The orbit obstruction rewritten in the elementary symmetric coordinates. -/
def linearRelationCoefficient (c : I → K) : MvPolynomial (Fin (Fintype.card I)) K :=
  (MvPolynomial.esymmAlgEquiv I K rfl).symm
    ⟨linearRelationOrbit c, linearRelationOrbit_isSymmetric c⟩

omit [IsDomain K] in
theorem esymmAlgHom_linearRelationCoefficient (c : I → K) :
    (MvPolynomial.esymmAlgHom I K (Fintype.card I) (linearRelationCoefficient c)).1
      = linearRelationOrbit c := by
  change
    ((MvPolynomial.esymmAlgEquiv I K rfl) (linearRelationCoefficient c)).1
      = linearRelationOrbit c
  simp [linearRelationCoefficient]

/-- **A nonzero real relation has a nonzero obstruction already at the level of the unordered
characteristic coefficients.** -/
theorem linearRelationCoefficient_ne_zero [DecidableEq I] {c : I → K} (hc : c ≠ 0) :
    linearRelationCoefficient c ≠ 0 := by
  intro hzero
  refine linearRelationOrbit_ne_zero hc ?_
  rw [← esymmAlgHom_linearRelationCoefficient c, hzero]
  simp

omit [IsDomain K] in
theorem eval_linearRelationOrbit (c : I → K) (energy : I → K) :
    MvPolynomial.eval energy (linearRelationOrbit c) = linearRelationOrbitValue c energy := by
  classical
  simp only [linearRelationOrbit, linearRelationOrbitValue, map_prod, MvPolynomial.eval_rename]
  refine Finset.prod_congr rfl fun σ _ => ?_
  simp [linearRelationPoly, Function.comp_apply]

omit [IsDomain K] in
/-- **Evaluating the coefficient obstruction on elementary symmetric spectral data reproduces the
label-orbit obstruction.**  The left-hand side is a polynomial in the elementary symmetric
functions of the spectrum — that is, in the characteristic-polynomial coefficients. -/
theorem eval_linearRelationCoefficient_esymm (c : I → K) (energy : I → K) :
    MvPolynomial.eval
        (fun i : Fin (Fintype.card I) =>
          MvPolynomial.eval energy (MvPolynomial.esymm I K (i + 1)))
        (linearRelationCoefficient c)
      = linearRelationOrbitValue c energy := by
  have h := congrArg (MvPolynomial.aeval energy) (esymmAlgHom_linearRelationCoefficient c)
  rw [MvPolynomial.esymmAlgHom_apply] at h
  simp only [MvPolynomial.comp_aeval_apply] at h
  have hid : algebraMap K K = RingHom.id K := by
    ext x
    rfl
  rw [← eval_linearRelationOrbit]
  simpa only [MvPolynomial.aeval_def, hid, MvPolynomial.eval₂_id] using h

end

end GaloisForLFunctions.HTGeometry
