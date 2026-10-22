import GaloisForLFunctions.HTGeometry.Critical.Coefficient.BaseChange

/-!
# Compatibility of critical-field constant extension

The rational-presentation scalar-extension equivalences agree exactly with coefficient extension
inside the common generic jet field.  Agreement is proved on the full source and observation
fields, not merely on their displayed generators.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Pure-left tensors followed by a scalar-extension field equivalence. -/
noncomputable def pureConstantBaseChangeAlgHom
    (F E : Type*) [Field F] [Field E] [Algebra k F] [Algebra K E]
    [Algebra k E] [IsScalarTower k K E]
    (e : FractionRing (F ⊗[k] K) ≃ₐ[K] E) : F →ₐ[k] E :=
  (e.toAlgHom.restrictScalars k).comp <|
    (IsScalarTower.toAlgHom k (F ⊗[k] K) (FractionRing (F ⊗[k] K))).comp <|
      Algebra.TensorProduct.includeLeft

@[simp] theorem pureConstantBaseChangeAlgHom_apply
    (F E : Type*) [Field F] [Field E] [Algebra k F] [Algebra K E]
    [Algebra k E] [IsScalarTower k K E]
    (e : FractionRing (F ⊗[k] K) ≃ₐ[K] E) (x : F) :
    pureConstantBaseChangeAlgHom (k := k) (K := K) F E e x =
      e (algebraMap (F ⊗[k] K) (FractionRing (F ⊗[k] K))
        (x ⊗ₜ[k] (1 : K))) := by
  rfl

theorem criticalSourcePureConstantBaseChange_eq
    [IsAlgClosed k] [CharZero k] [IsAlgClosed K] [CharZero K]
    (m n : ℕ) :
    pureConstantBaseChangeAlgHom (k := k) (K := K)
        (criticalSourceField k m n) (criticalSourceField K m n)
        (criticalSourceConstantBaseChange k K m n) =
      criticalSourceFieldBaseChange (k := k) (K := K) m n := by
  let f := pureConstantBaseChangeAlgHom (k := k) (K := K)
    (criticalSourceField k m n) (criticalSourceField K m n)
    (criticalSourceConstantBaseChange k K m n)
  let g := criticalSourceFieldBaseChange (k := k) (K := K) m n
  have hcomp : f.toRingHom.comp (criticalSourceFieldEquiv k m n).toRingEquiv.toRingHom =
      g.toRingHom.comp (criticalSourceFieldEquiv k m n).toRingEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext
      (A := MvPolynomial (Fin (m + n)) k)
    intro p
    let fp : MvPolynomial (Fin (m + n)) k →+* criticalSourceField K m n :=
      (f.toRingHom.comp (criticalSourceFieldEquiv k m n).toRingEquiv.toRingHom).comp
        (algebraMap (MvPolynomial (Fin (m + n)) k)
          (FractionRing (MvPolynomial (Fin (m + n)) k)))
    let gp : MvPolynomial (Fin (m + n)) k →+* criticalSourceField K m n :=
      (g.toRingHom.comp (criticalSourceFieldEquiv k m n).toRingEquiv.toRingHom).comp
        (algebraMap (MvPolynomial (Fin (m + n)) k)
          (FractionRing (MvPolynomial (Fin (m + n)) k)))
    have hpoly : fp = gp := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [fp, gp, f, g, criticalSourceFieldEquiv_algebraMap_apply]
      · intro i
        simp [fp, gp, f, g, criticalSourceFieldEquiv_algebraMap_apply]
    exact DFunLike.congr_fun hpoly p
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (criticalSourceFieldEquiv k m n).surjective x
  exact DFunLike.congr_fun hcomp y

theorem criticalObservationPureConstantBaseChange_eq
    [IsAlgClosed k] [CharZero k] [IsAlgClosed K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    pureConstantBaseChangeAlgHom (k := k) (K := K)
        (criticalObservationField k m n) (criticalObservationField K m n)
        (criticalObservationConstantBaseChange k K hm hn) =
      criticalObservationFieldBaseChange (k := k) (K := K) m n := by
  let f := pureConstantBaseChangeAlgHom (k := k) (K := K)
    (criticalObservationField k m n) (criticalObservationField K m n)
    (criticalObservationConstantBaseChange k K hm hn)
  let g := criticalObservationFieldBaseChange (k := k) (K := K) m n
  have hcomp :
      f.toRingHom.comp (criticalObservationFieldEquiv k hm hn).toRingEquiv.toRingHom =
        g.toRingHom.comp (criticalObservationFieldEquiv k hm hn).toRingEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext
      (A := MvPolynomial (Fin n ⊕ Fin m) k)
    intro p
    let fp : MvPolynomial (Fin n ⊕ Fin m) k →+* criticalObservationField K m n :=
      (f.toRingHom.comp
          (criticalObservationFieldEquiv k hm hn).toRingEquiv.toRingHom).comp
        (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
          (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k)))
    let gp : MvPolynomial (Fin n ⊕ Fin m) k →+* criticalObservationField K m n :=
      (g.toRingHom.comp
          (criticalObservationFieldEquiv k hm hn).toRingEquiv.toRingHom).comp
        (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
          (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k)))
    have hpoly : fp = gp := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change f ((criticalObservationFieldEquiv k hm hn)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
              (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))
              (MvPolynomial.C c))) =
          g ((criticalObservationFieldEquiv k hm hn)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
              (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))
              (MvPolynomial.C c)))
        have hc : (criticalObservationFieldEquiv k hm hn)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
              (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))
              (MvPolynomial.C c)) =
            algebraMap k (criticalObservationField k m n) c := by
          rw [show algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
              (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))
              (MvPolynomial.C c) =
              algebraMap k (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k)) c by
            rw [IsScalarTower.algebraMap_apply k
              (MvPolynomial (Fin n ⊕ Fin m) k)
              (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))]
            rfl]
          exact (criticalObservationFieldEquiv k hm hn).commutes c
        rw [hc, f.commutes, g.commutes]
      · intro s
        rcases s with i | j
        · change f ((criticalObservationFieldEquiv k hm hn)
              (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
                (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))
                (MvPolynomial.X (Sum.inl i)))) =
            g ((criticalObservationFieldEquiv k hm hn)
              (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
                (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))
                (MvPolynomial.X (Sum.inl i))))
          have hi : (criticalObservationFieldEquiv k hm hn)
              (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
                (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))
                (MvPolynomial.X (Sum.inl i))) =
              criticalObservationRaw k m n i := by
            rw [← criticalObservationFieldEquiv_symm_raw k hm hn i]
            exact (criticalObservationFieldEquiv k hm hn).apply_symm_apply _
          rw [hi]
          change criticalObservationConstantBaseChange k K hm hn
              (algebraMap (criticalObservationField k m n ⊗[k] K)
                (FractionRing (criticalObservationField k m n ⊗[k] K))
                (criticalObservationRaw k m n i ⊗ₜ[k] (1 : K))) =
            criticalObservationFieldBaseChange (k := k) (K := K) m n
              (criticalObservationRaw k m n i)
          rw [criticalObservationConstantBaseChange_raw]
          simpa [criticalObservationRaw, criticalFieldObservation] using
            (criticalObservationFieldBaseChange_coord (k := k) (K := K)
              m n (Sum.inl i)).symm
        · change f ((criticalObservationFieldEquiv k hm hn)
              (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
                (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))
                (MvPolynomial.X (Sum.inr j)))) =
            g ((criticalObservationFieldEquiv k hm hn)
              (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
                (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))
                (MvPolynomial.X (Sum.inr j))))
          have hj : (criticalObservationFieldEquiv k hm hn)
              (algebraMap (MvPolynomial (Fin n ⊕ Fin m) k)
                (FractionRing (MvPolynomial (Fin n ⊕ Fin m) k))
                (MvPolynomial.X (Sum.inr j))) =
              criticalObservationRecip k m n j := by
            rw [← criticalObservationFieldEquiv_symm_recip k hm hn j]
            exact (criticalObservationFieldEquiv k hm hn).apply_symm_apply _
          rw [hj]
          change criticalObservationConstantBaseChange k K hm hn
              (algebraMap (criticalObservationField k m n ⊗[k] K)
                (FractionRing (criticalObservationField k m n ⊗[k] K))
                (criticalObservationRecip k m n j ⊗ₜ[k] (1 : K))) =
            criticalObservationFieldBaseChange (k := k) (K := K) m n
              (criticalObservationRecip k m n j)
          rw [criticalObservationConstantBaseChange_recip]
          simpa [criticalObservationRecip, criticalFieldObservation] using
            (criticalObservationFieldBaseChange_coord (k := k) (K := K)
              m n (Sum.inr j)).symm
    exact DFunLike.congr_fun hpoly p
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := (criticalObservationFieldEquiv k hm hn).surjective x
  exact DFunLike.congr_fun hcomp y

end

end GaloisForLFunctions.HTGeometry
