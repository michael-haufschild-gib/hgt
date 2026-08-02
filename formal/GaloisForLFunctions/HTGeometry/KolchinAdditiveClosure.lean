import GaloisForLFunctions.HTGeometry.DifferentialKolchinClosure
import GaloisForLFunctions.HTGeometry.DifferentialAdjoinPairClassification

/-!
# Additive subgroups and Kolchin closure

Differential-polynomial translation and negation pull equations back along the additive group law.
These substitutions prove directly that the affine Kolchin closure of every additive subgroup is
again an additive subgroup.  No ambient topological-group instance or differential Nullstellensatz
is needed.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pull a differential polynomial back along translation by `a`. -/
def differentialPolynomialTranslate
    {ι K : Type*} [CommRing K] [Differential K] (a : ι → K) :
    DifferentialPolynomial ι K →ₐ[K] DifferentialPolynomial ι K :=
  MvPolynomial.aeval fun p : ι × ℕ =>
    MvPolynomial.X p + MvPolynomial.C (differentialJet p.2 (a p.1))

/-- Pull a differential polynomial back along additive inversion. -/
def differentialPolynomialNeg
    {ι K : Type*} [CommRing K] :
    DifferentialPolynomial ι K →ₐ[K] DifferentialPolynomial ι K :=
  MvPolynomial.aeval fun p : ι × ℕ => -MvPolynomial.X p

@[simp]
theorem differentialPolynomialTranslate_X
    {ι K : Type*} [CommRing K] [Differential K]
    (a : ι → K) (i : ι) (n : ℕ) :
    differentialPolynomialTranslate a (MvPolynomial.X (i, n)) =
      MvPolynomial.X (i, n) + MvPolynomial.C (differentialJet n (a i)) := by
  simp [differentialPolynomialTranslate]

@[simp]
theorem differentialPolynomialNeg_X
    {ι K : Type*} [CommRing K] (i : ι) (n : ℕ) :
    differentialPolynomialNeg (K := K) (MvPolynomial.X (i, n)) =
      -MvPolynomial.X (i, n) := by
  simp [differentialPolynomialNeg]

/-- Evaluation after polynomial translation is evaluation at the translated point. -/
theorem differentialPolynomialEvalOver_translate
    {ι K : Type*} [CommRing K] [Differential K]
    (x a : ι → K) (P : DifferentialPolynomial ι K) :
    differentialPolynomialEvalOver (K := K) x
        (differentialPolynomialTranslate a P) =
      differentialPolynomialEvalOver (K := K) (x + a) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [differentialPolynomialTranslate]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P p hP =>
      rcases p with ⟨i, n⟩
      rw [map_mul, map_mul, hP, differentialPolynomialTranslate_X,
        map_add, differentialPolynomialEvalOver_X,
        differentialPolynomialEvalOver_C, map_mul, differentialPolynomialEvalOver_X]
      simp [GaloisForLFunctions.differentialJet_add_apply]

/-- Evaluation after polynomial negation is evaluation at the negative point. -/
theorem differentialPolynomialEvalOver_neg
    {ι K : Type*} [CommRing K] [Differential K]
    (x : ι → K) (P : DifferentialPolynomial ι K) :
    differentialPolynomialEvalOver (K := K) x (differentialPolynomialNeg P) =
      differentialPolynomialEvalOver (K := K) (-x) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [differentialPolynomialNeg]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P p hP =>
      rcases p with ⟨i, n⟩
      rw [map_mul, map_mul, hP, differentialPolynomialNeg_X,
        map_neg, differentialPolynomialEvalOver_X, map_mul,
        differentialPolynomialEvalOver_X]
      simp [GaloisForLFunctions.differentialJet_neg_apply]

/-- The affine Kolchin closure of an additive subgroup is an additive subgroup. -/
def kolchinClosureAddSubgroup
    {ι K : Type*} [Field K] [Differential K]
    (H : AddSubgroup (ι → K)) : AddSubgroup (ι → K) where
  carrier := kolchinClosureOver K (H : Set (ι → K))
  zero_mem' := subset_kolchinClosureOver (K := K) (H : Set (ι → K)) H.zero_mem
  add_mem' := by
    intro x y hx hy P hP
    have hy_add (h : ι → K) (hh : h ∈ H) :
        differentialPolynomialEvalOver (K := K) (y + h) P = 0 := by
      have htranslate : differentialPolynomialTranslate h P ∈
          differentialVanishingIdealOver (H : Set (ι → K)) := by
        intro k hk
        rw [differentialPolynomialEvalOver_translate]
        exact hP (k + h) (H.add_mem hk hh)
      have hzero := hy (differentialPolynomialTranslate h P) htranslate
      rwa [differentialPolynomialEvalOver_translate] at hzero
    have htranslateY : differentialPolynomialTranslate y P ∈
        differentialVanishingIdealOver (H : Set (ι → K)) := by
      intro h hh
      rw [differentialPolynomialEvalOver_translate]
      simpa only [add_comm] using hy_add h hh
    have hzero := hx (differentialPolynomialTranslate y P) htranslateY
    rwa [differentialPolynomialEvalOver_translate] at hzero
  neg_mem' := by
    intro x hx P hP
    have hneg : differentialPolynomialNeg P ∈
        differentialVanishingIdealOver (H : Set (ι → K)) := by
      intro h hh
      rw [differentialPolynomialEvalOver_neg]
      exact hP (-h) (H.neg_mem hh)
    have hzero := hx (differentialPolynomialNeg P) hneg
    rwa [differentialPolynomialEvalOver_neg] at hzero

@[simp]
theorem coe_kolchinClosureAddSubgroup
    {ι K : Type*} [Field K] [Differential K]
    (H : AddSubgroup (ι → K)) :
    (kolchinClosureAddSubgroup H : Set (ι → K)) =
      kolchinClosureOver K (H : Set (ι → K)) :=
  rfl

/-- An additive subgroup is Kolchin dense in its closure, expressed in the constructed affine
Kolchin topology. -/
theorem closure_kolchinClosureAddSubgroup
    {ι K : Type*} [Field K] [Differential K]
    (H : AddSubgroup (ι → K)) :
    @closure (ι → K) (kolchinTopologicalSpace K) (H : Set (ι → K)) =
      (kolchinClosureAddSubgroup H : Set (ι → K)) := by
  exact closure_kolchinTopologicalSpace_eq_kolchinClosureOver (H : Set (ι → K))

end

end GaloisForLFunctions.HTGeometry
