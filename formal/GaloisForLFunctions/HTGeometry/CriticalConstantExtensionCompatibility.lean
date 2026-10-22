import GaloisForLFunctions.HTGeometry.ConstantScalarExtensionFractionRing
import GaloisForLFunctions.HTGeometry.Critical.Field.ConstantBaseChangeCompatibility

/-!
# Compatibility of the critical finite extension with constant base change

The scalar-extended critical source is identified with the critical source over enlarged
constants.  This identification commutes exactly with the corresponding observation-field
identification, so it can transport normal closures and their automorphism-cardinality.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 4000

variable {k K : Type*} [Field k] [IsAlgClosed k] [CharZero k]
  [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]

theorem criticalTensorBaseChange_compat
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (p : criticalObservationField k m n ⊗[k] K) :
    criticalSourceConstantBaseChange k K m n
        (algebraMap (criticalSourceField k m n ⊗[k] K)
          (FractionRing (criticalSourceField k m n ⊗[k] K))
          ((Algebra.TensorProduct.cancelBaseChange k
            (criticalObservationField k m n)
            (criticalSourceField k m n)
            (criticalSourceField k m n) K)
            ((1 : criticalSourceField k m n) ⊗ₜ[
              criticalObservationField k m n] p))) =
      algebraMap (criticalObservationField K m n)
        (criticalSourceField K m n)
        (criticalObservationConstantBaseChange k K hm hn
          (algebraMap (criticalObservationField k m n ⊗[k] K)
            (FractionRing (criticalObservationField k m n ⊗[k] K)) p)) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul x c =>
      rw [show (Algebra.TensorProduct.cancelBaseChange k
            (criticalObservationField k m n)
            (criticalSourceField k m n)
            (criticalSourceField k m n) K)
            ((1 : criticalSourceField k m n) ⊗ₜ[
              criticalObservationField k m n]
              (x ⊗ₜ[k] c)) =
          (algebraMap (criticalObservationField k m n)
            (criticalSourceField k m n) x) ⊗ₜ[k] c by
        simp [Algebra.smul_def]]
      rw [show (algebraMap (criticalObservationField k m n)
            (criticalSourceField k m n) x) ⊗ₜ[k] c =
          (algebraMap (criticalObservationField k m n)
            (criticalSourceField k m n) x ⊗ₜ[k] (1 : K)) *
            ((1 : criticalSourceField k m n) ⊗ₜ[k] c) by simp]
      rw [show x ⊗ₜ[k] c =
          (x ⊗ₜ[k] (1 : K)) *
            ((1 : criticalObservationField k m n) ⊗ₜ[k] c) by simp]
      rw [map_mul, map_mul]
      have hs := DFunLike.congr_fun
        (criticalSourcePureConstantBaseChange_eq
          (k := k) (K := K) m n)
        (algebraMap (criticalObservationField k m n)
          (criticalSourceField k m n) x)
      change criticalSourceConstantBaseChange k K m n
          (algebraMap (criticalSourceField k m n ⊗[k] K)
            (FractionRing (criticalSourceField k m n ⊗[k] K))
            ((algebraMap (criticalObservationField k m n)
              (criticalSourceField k m n) x) ⊗ₜ[k] (1 : K))) =
        criticalSourceFieldBaseChange (k := k) (K := K) m n
          (algebraMap (criticalObservationField k m n)
            (criticalSourceField k m n) x) at hs
      have ho := DFunLike.congr_fun
        (criticalObservationPureConstantBaseChange_eq
          (k := k) (K := K) hm hn) x
      change criticalObservationConstantBaseChange k K hm hn
          (algebraMap (criticalObservationField k m n ⊗[k] K)
            (FractionRing (criticalObservationField k m n ⊗[k] K))
            (x ⊗ₜ[k] (1 : K))) =
        criticalObservationFieldBaseChange (k := k) (K := K) m n x at ho
      have ho' := congrArg
        (algebraMap (criticalObservationField K m n)
          (criticalSourceField K m n)) ho
      have hsc : criticalSourceConstantBaseChange k K m n
          (algebraMap (criticalSourceField k m n ⊗[k] K)
            (FractionRing (criticalSourceField k m n ⊗[k] K))
            ((1 : criticalSourceField k m n) ⊗ₜ[k] c)) =
          algebraMap K (criticalSourceField K m n) c := by
        change criticalSourceConstantBaseChange k K m n
            (algebraMap K
              (FractionRing (criticalSourceField k m n ⊗[k] K)) c) = _
        exact (criticalSourceConstantBaseChange k K m n).commutes c
      have hoc : criticalObservationConstantBaseChange k K hm hn
          (algebraMap (criticalObservationField k m n ⊗[k] K)
            (FractionRing (criticalObservationField k m n ⊗[k] K))
            ((1 : criticalObservationField k m n) ⊗ₜ[k] c)) =
          algebraMap K (criticalObservationField K m n) c := by
        change criticalObservationConstantBaseChange k K hm hn
            (algebraMap K
              (FractionRing (criticalObservationField k m n ⊗[k] K)) c) = _
        exact (criticalObservationConstantBaseChange k K hm hn).commutes c
      have hoc' := congrArg
        (algebraMap (criticalObservationField K m n)
          (criticalSourceField K m n)) hoc
      have hinc :
          criticalSourceFieldBaseChange (k := k) (K := K) m n
              (algebraMap (criticalObservationField k m n)
                (criticalSourceField k m n) x) =
            algebraMap (criticalObservationField K m n)
              (criticalSourceField K m n)
              (criticalObservationFieldBaseChange
                (k := k) (K := K) m n x) := by
        rfl
      have hkc : algebraMap K (criticalSourceField K m n) c =
          algebraMap (criticalObservationField K m n)
            (criticalSourceField K m n)
            (algebraMap K (criticalObservationField K m n) c) := by
        rw [IsScalarTower.algebraMap_apply K
          (criticalObservationField K m n) (criticalSourceField K m n)]
      have hRhsMul :
          algebraMap (criticalObservationField K m n)
              (criticalSourceField K m n)
              (criticalObservationConstantBaseChange k K hm hn
                (algebraMap (criticalObservationField k m n ⊗[k] K)
                  (FractionRing
                    (criticalObservationField k m n ⊗[k] K))
                  ((x ⊗ₜ[k] (1 : K)) *
                    ((1 : criticalObservationField k m n) ⊗ₜ[k] c)))) =
            algebraMap (criticalObservationField K m n)
                (criticalSourceField K m n)
                (criticalObservationConstantBaseChange k K hm hn
                  (algebraMap (criticalObservationField k m n ⊗[k] K)
                    (FractionRing
                      (criticalObservationField k m n ⊗[k] K))
                    (x ⊗ₜ[k] (1 : K)))) *
              algebraMap (criticalObservationField K m n)
                (criticalSourceField K m n)
                (criticalObservationConstantBaseChange k K hm hn
                  (algebraMap (criticalObservationField k m n ⊗[k] K)
                    (FractionRing
                      (criticalObservationField k m n ⊗[k] K))
                    ((1 : criticalObservationField k m n) ⊗ₜ[k] c))) := by
        calc
          _ = algebraMap (criticalObservationField K m n)
                (criticalSourceField K m n)
                (criticalObservationConstantBaseChange k K hm hn
                  ((algebraMap
                    (criticalObservationField k m n ⊗[k] K)
                    (FractionRing
                      (criticalObservationField k m n ⊗[k] K))
                    (x ⊗ₜ[k] (1 : K))) *
                  (algebraMap
                    (criticalObservationField k m n ⊗[k] K)
                    (FractionRing
                      (criticalObservationField k m n ⊗[k] K))
                    ((1 : criticalObservationField k m n) ⊗ₜ[k] c)))) :=
              congrArg
                (fun z => algebraMap (criticalObservationField K m n)
                  (criticalSourceField K m n)
                  (criticalObservationConstantBaseChange k K hm hn z))
                ((algebraMap
                  (criticalObservationField k m n ⊗[k] K)
                  (FractionRing
                    (criticalObservationField k m n ⊗[k] K))).map_mul _ _)
          _ = algebraMap (criticalObservationField K m n)
                (criticalSourceField K m n)
                ((criticalObservationConstantBaseChange k K hm hn
                  (algebraMap (criticalObservationField k m n ⊗[k] K)
                    (FractionRing
                      (criticalObservationField k m n ⊗[k] K))
                    (x ⊗ₜ[k] (1 : K)))) *
                (criticalObservationConstantBaseChange k K hm hn
                  (algebraMap (criticalObservationField k m n ⊗[k] K)
                    (FractionRing
                      (criticalObservationField k m n ⊗[k] K))
                    ((1 : criticalObservationField k m n) ⊗ₜ[k] c)))) :=
              congrArg
                (algebraMap (criticalObservationField K m n)
                  (criticalSourceField K m n))
                ((criticalObservationConstantBaseChange k K hm hn).map_mul _ _)
          _ = _ :=
              (algebraMap (criticalObservationField K m n)
                (criticalSourceField K m n)).map_mul _ _
      exact calc
        _ = criticalSourceFieldBaseChange (k := k) (K := K) m n
                (algebraMap (criticalObservationField k m n)
                  (criticalSourceField k m n) x) *
              algebraMap K (criticalSourceField K m n) c :=
            congrArg₂ (· * ·) hs hsc
        _ = algebraMap (criticalObservationField K m n)
                (criticalSourceField K m n)
                (criticalObservationFieldBaseChange
                  (k := k) (K := K) m n x) *
              algebraMap (criticalObservationField K m n)
                (criticalSourceField K m n)
                (algebraMap K (criticalObservationField K m n) c) :=
            congrArg₂ (· * ·) hinc hkc
        _ = _ := (congrArg₂ (· * ·) ho'.symm hoc'.symm).trans hRhsMul.symm

/-- Scalar extension of the critical source over the critical observation field, identified with
the critical source over the enlarged constants. -/
noncomputable def criticalSourceConstantScalarExtensionRingEquiv
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    constantScalarExtension k (criticalObservationField k m n)
        (criticalSourceField k m n) K ≃+*
      criticalSourceField K m n :=
  by
    letI : FiniteDimensional (criticalObservationField k m n)
        (criticalSourceField k m n) :=
      criticalSourceField_finiteDimensional_criticalObservationField k hm hn
    exact (constantScalarExtensionFractionRingEquiv
        (k := k) (F := criticalObservationField k m n)
        (S := criticalSourceField k m n) (K := K)).trans
      (criticalSourceConstantBaseChange k K m n).toRingEquiv

/-- Critical observation/source field inclusions commute with constant extension. -/
theorem criticalConstantScalarExtensionRingEquiv_compat
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (algebraMap (criticalObservationField K m n)
        (criticalSourceField K m n)).comp
        (criticalObservationConstantBaseChange k K hm hn).toRingEquiv.toRingHom =
      (criticalSourceConstantScalarExtensionRingEquiv
        (k := k) (K := K) hm hn).toRingHom.comp
        (algebraMap
          (constantScalarBase k (criticalObservationField k m n) K)
          (constantScalarExtension k (criticalObservationField k m n)
            (criticalSourceField k m n) K)) := by
  letI : FiniteDimensional (criticalObservationField k m n)
      (criticalSourceField k m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField k hm hn
  apply fractionRing_ringHom_ext
  intro p
  simp only [RingHom.comp_apply]
  change algebraMap (criticalObservationField K m n)
        (criticalSourceField K m n)
        (criticalObservationConstantBaseChange k K hm hn
          (algebraMap (criticalObservationField k m n ⊗[k] K)
            (FractionRing (criticalObservationField k m n ⊗[k] K)) p)) =
      criticalSourceConstantBaseChange k K m n
        (constantScalarExtensionFractionRingEquiv
          (k := k) (F := criticalObservationField k m n)
          (S := criticalSourceField k m n) (K := K)
          (algebraMap
            (constantScalarBase k (criticalObservationField k m n) K)
            (constantScalarExtension k (criticalObservationField k m n)
              (criticalSourceField k m n) K)
            (algebraMap (criticalObservationField k m n ⊗[k] K)
              (constantScalarBase k (criticalObservationField k m n) K) p)))
  rw [constantScalarExtensionFractionRingEquiv_base]
  exact (criticalTensorBaseChange_compat
    (k := k) (K := K) hm hn p).symm

end

end GaloisForLFunctions.HTGeometry
