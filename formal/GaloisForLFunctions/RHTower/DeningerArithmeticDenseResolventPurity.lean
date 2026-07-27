import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Dense-resolvent transpose purity for Deninger cohomology

Meyer's literal zeta-zero eigenstates are continuous functionals on
the strong dual of the nuclear arithmetic quotient.  They need not
extend to bounded functionals on a Hodge Hilbert completion.

This file supplies the weaker algebraic bridge used by a rigged
Hilbert realization.  If an off-axis resolvent is surjective on a
source-dense invariant core, a transpose eigenfunctional with that
eigenvalue vanishes.  Thus nonzero Meyer functionals force the
weight-one line.
-/

open Complex

namespace RHTower

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/--
`DAC_DENSE_RESOLVENT_TRANSPOSE_PURITY`, algebraic kernel.

A transpose eigenfunctional vanishes whenever the corresponding
operator difference is surjective.
-/
theorem deningerTransposeEigenfunctional_eq_zero_of_sub_surjective
    (T : E →ₗ[ℂ] E)
    {lambda : ℂ}
    (ell : E →ₗ[ℂ] ℂ)
    (heigen : ∀ x : E, ell (T x) = lambda * ell x)
    (hsurj :
      Function.Surjective
        (T - lambda • (LinearMap.id : E →ₗ[ℂ] E))) :
    ell = 0 := by
  ext y
  obtain ⟨x, hx⟩ := hsurj y
  calc
    ell y =
        ell ((T - lambda • (LinearMap.id : E →ₗ[ℂ] E)) x) :=
      congrArg ell hx.symm
    _ = ell (T x) - lambda * ell x := by simp
    _ = 0 := by rw [heigen]; ring

/--
Every positive power of a surjective linear endomorphism remains
surjective.  This isolates the algebra needed for generalized
transpose eigenvectors.
-/
theorem deningerLinearMap_pow_surjective
    (L : E →ₗ[ℂ] E)
    (hL : Function.Surjective L) :
    ∀ n : ℕ, Function.Surjective (L ^ n) := by
  intro n
  induction n with
  | zero =>
      simpa using
        (Function.surjective_id : Function.Surjective (id : E → E))
  | succ n ih =>
      rw [pow_succ]
      exact ih.comp hL

/--
`DAC_DENSE_RESOLVENT_GENERALIZED_TRANSPOSE_PURITY`.

A generalized transpose eigenfunctional of any finite order vanishes
when the corresponding operator difference is surjective.
-/
theorem
    deningerGeneralizedTransposeEigenfunctional_eq_zero_of_sub_surjective
    (T : E →ₗ[ℂ] E)
    {lambda : ℂ}
    (ell : E →ₗ[ℂ] ℂ)
    (n : ℕ)
    (hgeneralized :
      ∀ x : E,
        ell
          (((T - lambda • (LinearMap.id : E →ₗ[ℂ] E)) ^ n) x) =
          0)
    (hsurj :
      Function.Surjective
        (T - lambda • (LinearMap.id : E →ₗ[ℂ] E))) :
    ell = 0 := by
  ext y
  obtain ⟨x, hx⟩ :=
    deningerLinearMap_pow_surjective
      (T - lambda • (LinearMap.id : E →ₗ[ℂ] E))
      hsurj n y
  calc
    ell y =
        ell
          (((T - lambda • (LinearMap.id : E →ₗ[ℂ] E)) ^ n) x) :=
      congrArg ell hx.symm
    _ = 0 := hgeneralized x

/--
A nonzero transpose eigenfunctional obstructs surjectivity of its
operator difference.  If every off-axis difference is surjective,
its centered eigenvalue has zero real part.
-/
theorem deningerSourceResolvent_transposeEigenvalue_re_eq_zero
    (T : E →ₗ[ℂ] E)
    {lambda : ℂ}
    (ell : E →ₗ[ℂ] ℂ)
    (hell : ell ≠ 0)
    (hresolvent :
      lambda.re ≠ 0 →
        Function.Surjective
          (T - lambda • (LinearMap.id : E →ₗ[ℂ] E)))
    (heigen : ∀ x : E, ell (T x) = lambda * ell x) :
    lambda.re = 0 := by
  by_contra hre
  exact hell
    (deningerTransposeEigenfunctional_eq_zero_of_sub_surjective
      T ell heigen (hresolvent hre))

/--
Weight-one form of dense-resolvent transpose purity.

Here `T` is the source-core realization of `Theta - 1/2`.
-/
theorem deningerSourceResolvent_transposeEigenvalue_re_eq_half
    (T : E →ₗ[ℂ] E)
    {rho : ℂ}
    (ell : E →ₗ[ℂ] ℂ)
    (hell : ell ≠ 0)
    (hresolvent :
      (rho - 1 / 2).re ≠ 0 →
        Function.Surjective
          (T - (rho - 1 / 2) •
            (LinearMap.id : E →ₗ[ℂ] E)))
    (heigen :
      ∀ x : E,
        ell (T x) = (rho - 1 / 2) * ell x) :
    rho.re = 1 / 2 := by
  have hcenter : (rho - 1 / 2).re = 0 :=
    deningerSourceResolvent_transposeEigenvalue_re_eq_zero
      T ell hell hresolvent heigen
  norm_num [Complex.sub_re] at hcenter ⊢
  linarith

/--
Source-core spectral comparison for Deninger's centered generator.

The intended carrier is a smooth arithmetic Hodge core whose map to
Meyer's nuclear quotient is dense.  Density ensures that each
nonzero Meyer functional restricts to the nonzero linear functional
recorded here.  Off-axis resolvent surjectivity is source regularity,
not a zero-indexed definition.
-/
structure DeningerHodgeSchwartzResolventXiSpectrum
    (E : Type*) [AddCommGroup E] [Module ℂ E] where
  centeredGenerator : E →ₗ[ℂ] E
  offAxis_resolvent_surjective :
    ∀ z : ℂ,
      z.re ≠ 0 →
        Function.Surjective
          (centeredGenerator -
            z • (LinearMap.id : E →ₗ[ℂ] E))
  evaluation :
    XiDivisorSupport → E →ₗ[ℂ] ℂ
  evaluation_ne_zero :
    ∀ q : XiDivisorSupport, evaluation q ≠ 0
  transpose_centeredGenerator :
    ∀ (q : XiDivisorSupport) (x : E),
      evaluation q (centeredGenerator x) =
        ((1 / 2 + Complex.I * xiSpectralPointSupport q) - 1 / 2) *
          evaluation q x

/--
A source-dense arithmetic Hodge core preserved by every off-axis
centered resolvent proves the Riemann hypothesis.
-/
theorem riemannHypothesis_of_hodgeSchwartzResolventXiSpectrum
    (Spectrum : DeningerHodgeSchwartzResolventXiSpectrum E) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  let q : XiDivisorSupport :=
    ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hhalf :
      (1 / 2 + Complex.I * xiSpectralPointSupport q).re = 1 / 2 :=
    deningerSourceResolvent_transposeEigenvalue_re_eq_half
      Spectrum.centeredGenerator
      (Spectrum.evaluation q)
      (Spectrum.evaluation_ne_zero q)
      (Spectrum.offAxis_resolvent_surjective
        ((1 / 2 + Complex.I * xiSpectralPointSupport q) - 1 / 2))
      (Spectrum.transpose_centeredGenerator q)
  have hzhalf : z.re = 1 / 2 := by
    dsimp only [q, xiSpectralPointSupport] at hhalf
    norm_num [Complex.mul_re] at hhalf
    linarith
  exact (ne_of_gt (mem_rightHalf.mp hz)) hzhalf

end

end RHTower
