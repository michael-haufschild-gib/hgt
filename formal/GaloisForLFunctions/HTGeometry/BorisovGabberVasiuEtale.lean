import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.Algebra.CharP.Basic

/-!
# Characteristic-power endomorphisms are etale

The triangular characteristic-power maps used by Borisov--Gabber--Vasiu,
arXiv:2609.05746, remain etale when their leading coefficient vanishes.
The proof constructs unique lifts across square-zero ideals, then identifies
the resulting root algebra with the source polynomial ring. No monicity or
nonvanishing assumption on the leading coefficient is needed.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section
variable {R : Type*} [CommRing R]

/-- A one-variable equation underlying characteristic-power triangular endomorphisms. -/
def bgvEtaleEquation (p : ℕ) (a b : R) : Polynomial R :=
  X + C b * X ^ p - C a

/-- The characteristic-power term does not alter the derivative. -/
theorem bgvEtaleEquation_derivative (p : ℕ) [CharP R p] (a b : R) :
    (bgvEtaleEquation p a b).derivative = 1 := by
  simp [bgvEtaleEquation, Polynomial.derivative_pow]


/-- These equations are formally etale without requiring a monic leading coefficient. -/
theorem bgvEtaleEquation_formallyEtale (p : ℕ) [CharP R p] (a b : R) :
    Algebra.FormallyEtale R (AdjoinRoot (bgvEtaleEquation p a b)) := by
  let f := bgvEtaleEquation p a b
  have hd : f.derivative = 1 := bgvEtaleEquation_derivative p a b
  apply Algebra.FormallyEtale.iff_comp_bijective.mpr
  intro S _ _ I hI
  constructor
  · intro g h hgh
    apply AdjoinRoot.algHom_ext
    let x := g (AdjoinRoot.root f)
    let y := h (AdjoinRoot.root f)
    have he : y - x ∈ I := by
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem y x).mp
      exact (congrArg (fun k => k (AdjoinRoot.root f)) hgh).symm
    have hs : (y - x) ^ (2 : ℕ) = 0 := hI.le (Ideal.pow_mem_pow he 2)
    have hroot := AdjoinRoot.aeval_algHom_eq_zero f h
    have hTaylor := Polynomial.aeval_add_of_sq_eq_zero f x (y - x) hs
    have hxroot : Polynomial.aeval x f = 0 := AdjoinRoot.aeval_algHom_eq_zero f g
    have hyroot : Polynomial.aeval y f = 0 := hroot
    rw [hd, map_one, one_mul, hxroot, zero_add] at hTaylor
    rw [show x + (y - x) = y by ring, hyroot] at hTaylor
    exact (sub_eq_zero.mp hTaylor.symm).symm
  · intro g
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (g (AdjoinRoot.root f))
    have hxI : Polynomial.aeval x f ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [← Ideal.Quotient.mkₐ_eq_mk R, ← Polynomial.aeval_algHom_apply,
        Ideal.Quotient.mkₐ_eq_mk, hx]
      exact AdjoinRoot.aeval_algHom_eq_zero f g
    have hs : (-Polynomial.aeval x f) ^ (2 : ℕ) = 0 :=
      hI.le (Ideal.pow_mem_pow (I.neg_mem hxI) 2)
    have hroot : Polynomial.aeval (x + -Polynomial.aeval x f) f = 0 := by
      rw [Polynomial.aeval_add_of_sq_eq_zero f _ _ hs, hd, map_one, one_mul, add_neg_cancel]
    let lift := AdjoinRoot.liftAlgHom f (Algebra.ofId R S)
      (x + -Polynomial.aeval x f) hroot
    refine ⟨lift, AdjoinRoot.algHom_ext ?_⟩
    change Ideal.Quotient.mk I (lift (AdjoinRoot.root f)) = g (AdjoinRoot.root f)
    rw [AdjoinRoot.liftAlgHom_root, map_add, map_neg,
      Ideal.Quotient.eq_zero_iff_mem.mpr hxI, neg_zero, add_zero]
    exact hx

/-- The actual root algebra is etale, including nonmonic and varying-degree members. -/
theorem bgvEtaleEquation_etale (p : ℕ) [CharP R p] (a b : R) :
    Algebra.Etale R (AdjoinRoot (bgvEtaleEquation p a b)) := by
  letI := bgvEtaleEquation_formallyEtale p a b
  exact ⟨inferInstance, inferInstance⟩

/-- Pullback by the characteristic-power polynomial `x ↦ x + b x^p`. -/
def bgvPowerMap (p : ℕ) (b : R) : Polynomial R →ₐ[R] Polynomial R :=
  Polynomial.aeval (X + C b * X ^ p)

/-- Eliminating the target coordinate identifies the root algebra with the source affine line. -/
def bgvPowerMapEquiv (p : ℕ) (b : R) :
    AdjoinRoot (bgvEtaleEquation p (X : Polynomial R) (C b)) ≃ₐ[R] Polynomial R := by
  let Q := bgvEtaleEquation p (X : Polynomial R) (C b)
  have hroot : Q.eval₂ (bgvPowerMap p b).toRingHom X = 0 := by
    simp [Q, bgvEtaleEquation, bgvPowerMap]
  let forward : AdjoinRoot Q →ₐ[R] Polynomial R :=
    AdjoinRoot.liftAlgHom Q (bgvPowerMap p b) X hroot
  let backward : Polynomial R →ₐ[R] AdjoinRoot Q :=
    Polynomial.aeval (AdjoinRoot.root Q)
  have hrelation : AdjoinRoot.root Q + algebraMap R (AdjoinRoot Q) b *
      AdjoinRoot.root Q ^ p = AdjoinRoot.of Q X := by
    apply sub_eq_zero.mp
    have h := AdjoinRoot.eval₂_root Q
    change Polynomial.eval₂ (AdjoinRoot.of Q) (AdjoinRoot.root Q)
      (X + C (C b) * X ^ p - C X) = 0 at h
    simpa only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, eval₂_pow, AdjoinRoot.algebraMap_eq',
      RingHom.comp_apply, Polynomial.algebraMap_eq] using h
  have hbase : backward.comp (bgvPowerMap p b) = AdjoinRoot.ofAlgHom R Q := by
    apply Polynomial.algHom_ext
    simpa [backward, bgvPowerMap] using hrelation
  refine AlgEquiv.ofAlgHom forward backward ?_ ?_
  · apply Polynomial.algHom_ext
    simp [forward, backward]
  · apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change backward (forward (AdjoinRoot.of Q X)) = AdjoinRoot.of Q X
      rw [AdjoinRoot.liftAlgHom_of]
      exact congrArg (fun k => k X) hbase
    · change backward (forward (AdjoinRoot.root Q)) = AdjoinRoot.root Q
      change Polynomial.aeval (AdjoinRoot.root Q)
        (AdjoinRoot.liftAlgHom Q (bgvPowerMap p b) X hroot (AdjoinRoot.root Q)) = _
      rw [AdjoinRoot.liftAlgHom_root, Polynomial.aeval_X]

/-- The source identification intertwines the base-coordinate map with polynomial pullback. -/
theorem bgvPowerMapEquiv_of (p : ℕ) (b : R) (q : Polynomial R) :
    bgvPowerMapEquiv p b
      (algebraMap (Polynomial R) (AdjoinRoot (bgvEtaleEquation p (X : Polynomial R) (C b))) q) =
        bgvPowerMap p b q := by
  simp [bgvPowerMapEquiv, AdjoinRoot.liftAlgHom_of, AdjoinRoot.algebraMap_eq]

/-- The actual affine-line polynomial endomorphism is etale over its coefficient ring. -/
theorem bgvPowerMap_etale (p : ℕ) [CharP R p] (b : R) :
    letI := (bgvPowerMap p b).toRingHom.toAlgebra
    Algebra.Etale (Polynomial R) (Polynomial R) := by
  let Q := bgvEtaleEquation p (X : Polynomial R) (C b)
  let coefficientAlgebra : Algebra (Polynomial R) (AdjoinRoot Q) := inferInstance
  have hEtale : Algebra.Etale (Polynomial R) (AdjoinRoot Q) :=
    bgvEtaleEquation_etale (R := Polynomial R) p X (C b)
  letI := (bgvPowerMap p b).toRingHom.toAlgebra
  letI : Algebra (Polynomial R) (AdjoinRoot Q) := coefficientAlgebra
  let e : AdjoinRoot Q ≃ₐ[Polynomial R] Polynomial R :=
    { (bgvPowerMapEquiv p b).toRingEquiv with
      commutes' := by
        intro q
        change bgvPowerMapEquiv p b (algebraMap (Polynomial R) (AdjoinRoot Q) q) =
          bgvPowerMap p b q
        exact bgvPowerMapEquiv_of p b q }
  letI := hEtale
  exact Algebra.Etale.of_equiv e

/-- Formal etaleness of the polynomial pullback, in the ring-homomorphism interface. -/
theorem bgvPowerMap_formallyEtale (p : ℕ) [CharP R p] (b : R) :
    (bgvPowerMap p b).toRingHom.FormallyEtale := by
  letI := (bgvPowerMap p b).toRingHom.toAlgebra
  letI := bgvPowerMap_etale p b
  show Algebra.FormallyEtale (Polynomial R) (Polynomial R)
  infer_instance

end
end GaloisForLFunctions.HTGeometry
