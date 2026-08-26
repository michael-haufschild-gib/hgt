import GaloisForLFunctions.HTGeometry.AdjoinRootSpectrumHomeomorph
import GaloisForLFunctions.HTGeometry.ParametricRootBaseChange
import GaloisForLFunctions.HTGeometry.MonicCoefficientRootCovering
import GaloisForLFunctions.HTGeometry.AlgebraSpectrumFiniteProper
import GaloisForLFunctions.HTGeometry.MonicSeparableLocus
import GaloisForLFunctions.Bottcher.ProperLocalHomeoCovering

/-!
# Local covering theorem for monogenic complex spectra

A monic root algebra whose specializations at all complex base points are separable induces a local
homeomorphism on complex-point spectra.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Topology Set

noncomputable section

namespace AlgSpec

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- A positive-degree monic root algebra is spanned by the powers below its degree. -/
theorem adjoinRoot_moduleFinite_of_monic {A : Type*} [CommRing A] [Nontrivial A]
    (p : A[X]) (hp : p.Monic) (hdeg : 0 < p.natDegree) :
    Module.Finite A (AdjoinRoot p) := by
  let S : Set (AdjoinRoot p) := Set.range fun i : Fin p.natDegree =>
    AdjoinRoot.root p ^ (i : ℕ)
  have hspan : Submodule.span A S = ⊤ := by
    apply top_unique
    intro b _
    refine AdjoinRoot.induction_on p b ?_
    intro q
    let r := q %ₘ p
    have hp1 : p ≠ 1 := by
      intro heq
      rw [heq] at hdeg
      simp at hdeg
    have hrdeg : r.natDegree < p.natDegree :=
      Polynomial.natDegree_modByMonic_lt q hp hp1
    have hmk : AdjoinRoot.mk p q = AdjoinRoot.mk p r := by
      apply AdjoinRoot.mk_eq_mk.mpr
      refine ⟨q /ₘ p, ?_⟩
      have hdiv := Polynomial.modByMonic_add_div q p
      dsimp only [r]
      calc
        q - q %ₘ p = (q %ₘ p + p * (q /ₘ p)) - q %ₘ p :=
          congrArg (fun t => t - q %ₘ p) hdiv.symm
        _ = p * (q /ₘ p) := by abel
    rw [hmk]
    rw [← Polynomial.sum_C_mul_X_pow_eq r, Polynomial.sum_def, map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_mul, AdjoinRoot.mk_C, map_pow, AdjoinRoot.mk_X]
    rw [← AdjoinRoot.algebraMap_eq]
    rw [← Algebra.smul_def]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    have hi' : i < p.natDegree :=
      (Polynomial.le_natDegree_of_ne_zero
        (Polynomial.mem_support_iff.mp hi)).trans_lt hrdeg
    exact ⟨⟨i, hi'⟩, rfl⟩
  exact Module.Finite.of_fg_top (hspan ▸ Submodule.fg_span (Set.finite_range _))

/-- Lower-coefficient vector of a monic polynomial specialized at a complex point. -/
def adjoinRootCoeffMap (p : A[X]) (chi : AlgSpec A) : Fin p.natDegree → ℂ :=
  fun i => chi (p.coeff i)

theorem continuous_adjoinRootCoeffMap (p : A[X]) :
    Continuous (adjoinRootCoeffMap p) := by
  apply continuous_pi
  intro i
  exact continuous_eval (p.coeff i)

theorem monicCoeffRelation_adjoinRootCoeffMap (p : A[X]) (hp : p.Monic)
    (chi : AlgSpec A) (z : ℂ) :
    monicCoeffRelation p.natDegree (adjoinRootCoeffMap p chi, z) =
      Polynomial.eval₂ (pointRingHom chi) z p := by
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree]
  simp only [monicCoeffRelation, adjoinRootCoeffMap, pointRingHom_apply, map_one,
    one_mul]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => chi (p.coeff i) * z ^ i) p.natDegree]
  ac_rfl

theorem monicCoeffPolynomial_adjoinRootCoeffMap (p : A[X]) (hp : p.Monic)
    (chi : AlgSpec A) :
    monicCoeffPolynomial p.natDegree (adjoinRootCoeffMap p chi) =
      p.map (pointRingHom chi) := by
  apply Polynomial.funext
  intro z
  calc
    (monicCoeffPolynomial p.natDegree (adjoinRootCoeffMap p chi)).eval z =
        monicCoeffRelation p.natDegree (adjoinRootCoeffMap p chi, z) :=
      (monicCoeffRelation_eq_eval p.natDegree (adjoinRootCoeffMap p chi, z)).symm
    _ = Polynomial.eval₂ (pointRingHom chi) z p :=
      monicCoeffRelation_adjoinRootCoeffMap p hp chi z
    _ = (p.map (pointRingHom chi)).eval z := by rw [Polynomial.eval_map]

theorem adjoinRootLocus_eq_parametricRootBaseChange (p : A[X]) (hp : p.Monic) :
    AdjoinRootLocus p =
      ParametricRootBaseChange (monicCoeffRelation p.natDegree) (adjoinRootCoeffMap p) := by
  ext q
  change Polynomial.eval₂ (pointRingHom q.1) q.2 p = 0 ↔
    monicCoeffRelation p.natDegree (adjoinRootCoeffMap p q.1, q.2) = 0
  rw [monicCoeffRelation_adjoinRootCoeffMap p hp]

/-- Complex spectrum of a monogenic algebra identified with the continuous coefficient-family
root locus. -/
def adjoinRootSpectrumBaseChangeHomeomorph (p : A[X]) (hp : p.Monic) :
    AlgSpec (AdjoinRoot p) ≃ₜ
      ParametricRootBaseChange (monicCoeffRelation p.natDegree) (adjoinRootCoeffMap p) :=
  (adjoinRootSpectrumHomeomorph p).trans
    (Homeomorph.setCongr (adjoinRootLocus_eq_parametricRootBaseChange p hp))

/-- A chart of the monogenic spectrum projection at any point whose specialized polynomial is
separable.  No condition is imposed on other fibres. -/
theorem exists_chart_adjoinRootBase (p : A[X]) (hp : p.Monic)
    (q : AlgSpec (AdjoinRoot p))
    (hsep : (p.map (pointRingHom (adjoinRootBase p q))).Separable) :
    ∃ φ : OpenPartialHomeomorph (AlgSpec (AdjoinRoot p)) (AlgSpec A),
      q ∈ φ.source ∧ adjoinRootBase p = φ := by
  let H := adjoinRootSpectrumBaseChangeHomeomorph p hp
  obtain ⟨φ, hqφ, hφ⟩ := exists_chart_parametricRootBaseChangeProj
    (continuous_adjoinRootCoeffMap p) (H q)
    (analyticAt_monicCoeffRelation p.natDegree
      (adjoinRootCoeffMap p (adjoinRootBase p q), q (AdjoinRoot.root p)))
    (by
      change (fderiv ℂ (monicCoeffRelation p.natDegree)
        (adjoinRootCoeffMap p (adjoinRootBase p q), q (AdjoinRoot.root p))) (0, 1) ≠ 0
      rw [monicCoeffRelation_partial_snd]
      rw [monicCoeffPolynomial_adjoinRootCoeffMap p hp]
      apply hsep.eval₂_derivative_ne_zero (RingHom.id ℂ)
      have hroot : (p.map (pointRingHom (adjoinRootBase p q))).eval
          (q (AdjoinRoot.root p)) = 0 := by
        rw [Polynomial.eval_map]
        exact adjoinRootBase_eval₂_root p q
      simpa using hroot)
  let ψ : OpenPartialHomeomorph (AlgSpec (AdjoinRoot p)) (AlgSpec A) :=
    H.toOpenPartialHomeomorph.trans φ
  refine ⟨ψ, ?_, ?_⟩
  · simpa [ψ] using hqφ
  · funext x
    change parametricRootBaseChangeProj (H x) = φ (H x)
    rw [hφ]

/-- A monogenic algebra with separable specialization at every complex base point has locally
homeomorphic complex-point projection. -/
theorem isLocalHomeomorph_adjoinRootBase (p : A[X]) (hp : p.Monic)
    (hsep : ∀ chi : AlgSpec A, (p.map (pointRingHom chi)).Separable) :
    IsLocalHomeomorph (adjoinRootBase p) := by
  intro q
  exact exists_chart_adjoinRootBase p hp q (hsep (adjoinRootBase p q))

/-- The spectrum projection is a local homeomorphism precisely where its monic specialization is
separable. -/
theorem isLocalHomeomorphOn_adjoinRootBase_monicSeparableLocus
    (p : A[X]) (hp : p.Monic) :
    IsLocalHomeomorphOn (adjoinRootBase p)
      ((adjoinRootBase p) ⁻¹' monicSeparableLocus p) := by
  intro q hq
  exact exists_chart_adjoinRootBase p hp q hq

/-- The simple-fibre part of the monogenic spectrum is open. -/
theorem isOpen_adjoinRootBase_preimage_monicSeparableLocus
    (p : A[X]) (hp : p.Monic) :
    IsOpen ((adjoinRootBase p) ⁻¹' monicSeparableLocus p) :=
  (isOpen_monicSeparableLocus p hp).preimage (continuous_precomp _)

/-- A positive-degree monic root algebra induces a proper map on complex points. -/
theorem isProperMap_adjoinRootBase {A : Type*} [CommRing A] [IsDomain A] [Algebra ℂ A]
    (p : A[X]) (hp : p.Monic) (hdeg : 0 < p.natDegree)
    [CompactlyCoherentSpace (AlgSpec A)] :
    IsProperMap (adjoinRootBase p) := by
  letI : Module.Finite A (AdjoinRoot p) := adjoinRoot_moduleFinite_of_monic p hp hdeg
  letI : Nontrivial (AdjoinRoot p) := AdjoinRoot.nontrivial p (by
    rw [p.degree_eq_natDegree hp.ne_zero]
    exact_mod_cast Nat.ne_of_gt hdeg)
  exact isProperMap_precomp_of_finite

/-- A positive-degree monic algebra with everywhere-separable complex fibres is a covering on
complex points. -/
theorem isCoveringMap_adjoinRootBase {A : Type*} [CommRing A] [IsDomain A] [Algebra ℂ A]
    (p : A[X]) (hp : p.Monic) (hdeg : 0 < p.natDegree)
    [CompactlyCoherentSpace (AlgSpec A)]
    (hsep : ∀ chi : AlgSpec A, (p.map (pointRingHom chi)).Separable) :
    IsCoveringMap (adjoinRootBase p) := by
  exact isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    (isLocalHomeomorph_adjoinRootBase p hp hsep)
    (isProperMap_adjoinRootBase p hp hdeg)

end AlgSpec

end

end GaloisForLFunctions.HTGeometry
