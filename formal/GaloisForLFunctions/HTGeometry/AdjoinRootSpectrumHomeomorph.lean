import GaloisForLFunctions.HTGeometry.AlgebraSpectrumEquiv

/-!
# Complex spectrum of a monogenic root algebra

Complex points of an `AdjoinRoot` algebra are homeomorphic to pairs consisting of a complex point
of the coefficient algebra and a root of the specialized polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Topology Set

noncomputable section

namespace AlgSpec

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Underlying ring homomorphism of a complex algebra point. -/
def pointRingHom (chi : AlgSpec A) : A →+* ℂ :=
  (show A →ₐ[ℂ] ℂ from chi).toRingHom

@[simp] theorem pointRingHom_apply (chi : AlgSpec A) (a : A) :
    pointRingHom chi a = chi a := rfl

/-- Pairs consisting of a complex point of the base and a root of the specialized polynomial. -/
def AdjoinRootLocus (p : A[X]) : Set (AlgSpec A × ℂ) :=
  {q | Polynomial.eval₂ (pointRingHom q.1) q.2 p = 0}

/-- Restriction of a root-algebra point to the coefficient algebra. -/
def adjoinRootBase (p : A[X]) (chi : AlgSpec (AdjoinRoot p)) : AlgSpec A :=
  precomp (IsScalarTower.toAlgHom ℂ A (AdjoinRoot p)) chi

theorem adjoinRootBase_eval₂_root (p : A[X]) (chi : AlgSpec (AdjoinRoot p)) :
    Polynomial.eval₂ (pointRingHom (adjoinRootBase p chi))
      (chi (AdjoinRoot.root p)) p = 0 := by
  have hbase : pointRingHom (adjoinRootBase p chi) =
      (pointRingHom chi).comp (AdjoinRoot.of p) := by
    ext a
    change chi ((algebraMap A (AdjoinRoot p)) a) = chi (AdjoinRoot.of p a)
    rw [AdjoinRoot.algebraMap_eq]
  have h := Polynomial.hom_eval₂ p (AdjoinRoot.of p) (pointRingHom chi)
    (AdjoinRoot.root p)
  rw [AdjoinRoot.eval₂_root, map_zero] at h
  rw [hbase]
  exact h.symm

/-- Complex point of a root algebra, recorded by its base point and distinguished root value. -/
def adjoinRootSpectrumToLocus (p : A[X]) (chi : AlgSpec (AdjoinRoot p)) :
    AdjoinRootLocus p :=
  ⟨(adjoinRootBase p chi, chi (AdjoinRoot.root p)), adjoinRootBase_eval₂_root p chi⟩

/-- Root-locus point extended to the unique complex point of the root algebra. -/
def adjoinRootLocusToSpectrum (p : A[X]) (q : AdjoinRootLocus p) :
    AlgSpec (AdjoinRoot p) where
  toRingHom := AdjoinRoot.lift
    (pointRingHom q.1.1) q.1.2 q.2
  commutes' z := by
    change (AdjoinRoot.lift
      (pointRingHom q.1.1) q.1.2 q.2)
        ((algebraMap ℂ (AdjoinRoot p)) z) = (algebraMap ℂ ℂ) z
    rw [IsScalarTower.algebraMap_apply ℂ A (AdjoinRoot p)]
    change (AdjoinRoot.lift
      (pointRingHom q.1.1) q.1.2 q.2)
        ((AdjoinRoot.of p) ((algebraMap ℂ A) z)) = (algebraMap ℂ ℂ) z
    rw [AdjoinRoot.lift_of]
    exact q.1.1.commutes z

theorem adjoinRootLocusToSpectrum_of (p : A[X]) (q : AdjoinRootLocus p) (a : A) :
    adjoinRootLocusToSpectrum p q (AdjoinRoot.of p a) = q.1.1 a := by
  exact AdjoinRoot.lift_of q.2

theorem adjoinRootLocusToSpectrum_root (p : A[X]) (q : AdjoinRootLocus p) :
    adjoinRootLocusToSpectrum p q (AdjoinRoot.root p) = q.1.2 := by
  exact AdjoinRoot.lift_root q.2

theorem adjoinRootSpectrumToLocus_left_inv (p : A[X])
    (chi : AlgSpec (AdjoinRoot p)) :
    adjoinRootLocusToSpectrum p (adjoinRootSpectrumToLocus p chi) = chi := by
  apply DFunLike.ext _ _
  have hr :
      pointRingHom (adjoinRootLocusToSpectrum p (adjoinRootSpectrumToLocus p chi)) =
      pointRingHom chi := by
    apply AdjoinRoot.ringHom_ext
    · ext a
      change adjoinRootLocusToSpectrum p (adjoinRootSpectrumToLocus p chi)
        (AdjoinRoot.of p a) = chi (AdjoinRoot.of p a)
      rw [adjoinRootLocusToSpectrum_of]
      rfl
    · change adjoinRootLocusToSpectrum p (adjoinRootSpectrumToLocus p chi)
        (AdjoinRoot.root p) = chi (AdjoinRoot.root p)
      rw [adjoinRootLocusToSpectrum_root]
      rfl
  exact fun b => DFunLike.congr_fun hr b

theorem adjoinRootSpectrumToLocus_right_inv (p : A[X])
    (q : AdjoinRootLocus p) :
    adjoinRootSpectrumToLocus p (adjoinRootLocusToSpectrum p q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · apply DFunLike.ext _ _
    intro a
    change adjoinRootLocusToSpectrum p q ((algebraMap A (AdjoinRoot p)) a) = q.1.1 a
    rw [AdjoinRoot.algebraMap_eq, adjoinRootLocusToSpectrum_of]
  · exact adjoinRootLocusToSpectrum_root p q

theorem continuous_adjoinRootSpectrumToLocus (p : A[X]) :
    Continuous (adjoinRootSpectrumToLocus p) := by
  apply Continuous.subtype_mk
  exact (continuous_precomp (IsScalarTower.toAlgHom ℂ A (AdjoinRoot p))).prodMk
    (continuous_eval (AdjoinRoot.root p))

private theorem continuous_adjoinRoot_eval₂ (p q : A[X]) :
    Continuous (fun z : AdjoinRootLocus p =>
      Polynomial.eval₂ (pointRingHom z.1.1) z.1.2 q) := by
  rw [show (fun z : AdjoinRootLocus p =>
      Polynomial.eval₂ (pointRingHom z.1.1) z.1.2 q) =
      fun z => ∑ i ∈ Finset.range (q.natDegree + 1), z.1.1 (q.coeff i) * z.1.2 ^ i by
    funext z
    rw [Polynomial.eval₂_eq_sum_range]
    simp only [pointRingHom_apply]]
  apply continuous_finsetSum
  intro i _
  exact ((continuous_eval (q.coeff i)).comp
      (continuous_fst.comp continuous_subtype_val)).mul
    ((continuous_snd.comp continuous_subtype_val).pow i)

theorem continuous_adjoinRootLocusToSpectrum (p : A[X]) :
    Continuous (adjoinRootLocusToSpectrum p) := by
  rw [isInducing_coe.continuous_iff]
  apply continuous_pi
  intro b
  refine AdjoinRoot.induction_on p b ?_
  intro q
  have heq : (fun z : AdjoinRootLocus p => adjoinRootLocusToSpectrum p z
      (AdjoinRoot.mk p q)) = fun z => Polynomial.eval₂
        (pointRingHom z.1.1) z.1.2 q := by
    funext z
    exact AdjoinRoot.lift_mk z.2 q
  change Continuous (fun z : AdjoinRootLocus p => adjoinRootLocusToSpectrum p z
    (AdjoinRoot.mk p q))
  rw [heq]
  exact continuous_adjoinRoot_eval₂ p q

/-- Complex points of a root algebra are homeomorphic to specialized roots over complex base
points. -/
def adjoinRootSpectrumHomeomorph (p : A[X]) :
    AlgSpec (AdjoinRoot p) ≃ₜ AdjoinRootLocus p :=
  Homeomorph.mk
    { toFun := adjoinRootSpectrumToLocus p
      invFun := adjoinRootLocusToSpectrum p
      left_inv := adjoinRootSpectrumToLocus_left_inv p
      right_inv := adjoinRootSpectrumToLocus_right_inv p }
    (continuous_adjoinRootSpectrumToLocus p)
    (continuous_adjoinRootLocusToSpectrum p)

end AlgSpec

end

end GaloisForLFunctions.HTGeometry
