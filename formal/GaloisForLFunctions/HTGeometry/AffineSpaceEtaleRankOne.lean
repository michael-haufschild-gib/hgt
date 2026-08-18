import GaloisForLFunctions.HTGeometry.EtaleRankOnePolynomialStep
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# `SCE_k`: affine space has no nontrivial connected finite étale cover

Over an algebraically closed field `K` of characteristic zero, a domain that is finite free over
`MvPolynomial (Fin k) K` and whose discriminant is a unit has rank one:

```text
rank_eq_one_of_isUnit_discr_mvPolynomial :
    IsUnit (Algebra.discr (MvPolynomial (Fin k) K) e)  →  n = 1
```

The induction is on the number of variables, using `MvPolynomial.finSuccEquiv` to present affine
`(k+1)`-space as the affine line over affine `k`-space, `hasEtaleRankOne_polynomial` for the step,
and `hasEtaleRankOne_isAlgClosed` for the base.  `hasEtaleRankOne_of_ringEquiv` transports the
property along a ring isomorphism of the base: a basis stays a basis and the discriminant is carried
by the inverse isomorphism, so unit-ness is preserved.

This is the general, non-monogenic form.  `AffineSpaceSimplyConnected.hasEtaleSplitting_mvPolynomial`
proves the monogenic form, which — as recorded on the projective-horizon card — can never be applied
to an abstract étale cover, because a nontrivial connected cover of affine space admits no monogenic
model with unit resultant.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

universe u

theorem hasEtaleRankOne_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (φ : R ≃+* S)
    (h : HasEtaleRankOne R) : HasEtaleRankOne S := by
  intro B _ _ _ _ _ n hn e hd
  classical
  letI algRB : Algebra R B := ((algebraMap S B).comp φ.toRingHom).toAlgebra
  have hsmul : ∀ (r : R) (b : B), r • b = (φ r) • b := by
    intro r b
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  have hli : LinearIndependent R (⇑e) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' : ∑ j, (φ (g j)) • e j = 0 := by
      rw [← hg]
      exact Finset.sum_congr rfl (fun j _ => (hsmul (g j) (e j)).symm)
    have hz := (Fintype.linearIndependent_iff.mp e.linearIndependent) _ hg' i
    exact φ.injective (by simpa using hz)
  have hsp : ⊤ ≤ Submodule.span R (Set.range ⇑e) := by
    intro b _
    have hb : ∑ i, (e.repr b i) • e i = b := e.sum_repr b
    rw [← hb]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have hrw : (e.repr b i) • e i = (φ.symm (e.repr b i)) • e i := by
      rw [hsmul, φ.apply_symm_apply]
    rw [hrw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  set e' : Module.Basis (Fin n) R B := Module.Basis.mk hli hsp with he'
  have he'apply : ∀ i, e' i = e i := fun i => Module.Basis.mk_apply _ _ _
  haveI : Module.Free R B := Module.Free.of_basis e'
  haveI : Module.Finite R B := Module.Finite.of_basis e'
  have hrepr : ∀ (b : B) (i : Fin n), e'.repr b i = φ.symm (e.repr b i) := by
    intro b i
    set c : Fin n → R := fun j => φ.symm (e.repr b j) with hc
    have hb : b = ∑ j, c j • e' j := by
      conv_lhs => rw [← e.sum_repr b]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [he'apply, hc, hsmul, φ.apply_symm_apply]
    have hci : φ.symm (e.repr b i) = c i := rfl
    rw [hci]
    conv_lhs => rw [hb]
    rw [repr_sum_apply]
  have htrace : ∀ x : B, Algebra.trace R B x = φ.symm (Algebra.trace S B x) := by
    intro x
    rw [Algebra.trace_eq_matrix_trace e', Algebra.trace_eq_matrix_trace e, Matrix.trace,
      Matrix.trace, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, he'apply, hrepr]
  have hdisc : IsUnit (Algebra.discr R e') := by
    have hmat : Algebra.traceMatrix R e'
        = (Algebra.traceMatrix S e).map (φ.symm : S →+* R) := by
      ext i j
      rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, he'apply, he'apply, htrace,
        Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
      rfl
    rw [Algebra.discr_def, hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hd).map (φ.symm : S →+* R)
  exact h hn e' hdisc


/-- **Algebraic simple connectedness of affine space, general form.**  Over an algebraically closed
field of characteristic zero, the polynomial ring in `k` variables has the étale rank-one
property. -/
theorem hasEtaleRankOne_mvPolynomial (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] :
    ∀ k : ℕ, HasEtaleRankOne (MvPolynomial (Fin k) K) := by
  intro k
  induction k with
  | zero =>
      have hφ : K ≃+* MvPolynomial (Fin 0) K :=
        (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).symm.toRingEquiv
      intro B _ _ _ _ _ n hn e hd
      exact hasEtaleRankOne_of_ringEquiv hφ (hasEtaleRankOne_isAlgClosed K) hn e hd
  | succ k ih =>
      have hstep : HasEtaleRankOne (Polynomial (MvPolynomial (Fin k) K)) :=
        hasEtaleRankOne_polynomial (MvPolynomial (Fin k) K) ih
      have hφ : Polynomial (MvPolynomial (Fin k) K) ≃+* MvPolynomial (Fin (k + 1)) K :=
        (MvPolynomial.finSuccEquiv K k).symm.toRingEquiv
      intro B _ _ _ _ _ n hn e hd
      exact hasEtaleRankOne_of_ringEquiv hφ hstep hn e hd

/-- **`SCE_k`.**  Over an algebraically closed field of characteristic zero, a domain that is finite
free over the polynomial ring in `k` variables with unit discriminant has rank one: affine space has
no nontrivial connected finite étale cover. -/
theorem rank_eq_one_of_isUnit_discr_mvPolynomial (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
    (k : ℕ) {B : Type u} [CommRing B] [IsDomain B] [Algebra (MvPolynomial (Fin k) K) B]
    [Module.Free (MvPolynomial (Fin k) K) B] [Module.Finite (MvPolynomial (Fin k) K) B]
    {n : ℕ} (hn : 1 ≤ n) (e : Module.Basis (Fin n) (MvPolynomial (Fin k) K) B)
    (hd : IsUnit (Algebra.discr (MvPolynomial (Fin k) K) e)) : n = 1 :=
  hasEtaleRankOne_mvPolynomial K k hn e hd

end GaloisForLFunctions.HTGeometry
