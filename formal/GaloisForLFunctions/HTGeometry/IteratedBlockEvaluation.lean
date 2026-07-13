import GaloisForLFunctions.HTGeometry.IteratedUnitCoefficientBlockDimension

namespace GaloisForLFunctions.HTGeometry

noncomputable section

structure BlockEquationData
    (A T : Type) [CommRing A] [CommRing T] [Algebra A T] (n : ℕ) where
  polynomial : MvPolynomial (Fin n) A
  point : Fin n → T
  vanishes : MvPolynomial.eval₂ (algebraMap A T) point polynomial = 0

def blockEquationPolynomials
    {A T : Type} [CommRing A] [CommRing T] [Algebra A T] {n : ℕ}
    (D : List (BlockEquationData A T n)) : List (MvPolynomial (Fin n) A) :=
  D.map BlockEquationData.polynomial

def iteratedBlockEvaluation
    {A T : Type} [CommRing A] [CommRing T] [Algebra A T] {n : ℕ} :
    (D : List (BlockEquationData A T n)) →
      iteratedUnitCoefficientBlockRing A (blockEquationPolynomials D) →ₐ[A] T
  | [] => Algebra.ofId A T
  | d :: ds => by
      let B := iteratedUnitCoefficientBlockRing A (blockEquationPolynomials ds)
      let tail : B →ₐ[A] T := iteratedBlockEvaluation ds
      let f : MvPolynomial (Fin n) B →ₐ[A] T :=
        { MvPolynomial.eval₂Hom tail.toRingHom d.point with
          commutes' := by
            intro a
            simp [tail] }
      let I : Ideal (MvPolynomial (Fin n) B) :=
        Ideal.span {MvPolynomial.map (algebraMap A B) d.polynomial}
      exact Ideal.Quotient.liftₐ I f (by
        intro P hP
        apply (show I ≤ RingHom.ker f from ?_) hP
        rw [Ideal.span_le]
        intro Q hQ
        rcases hQ with ⟨rfl⟩
        change f (MvPolynomial.map (algebraMap A B) d.polynomial) = 0
        simpa [f, tail, MvPolynomial.eval₂_map] using d.vanishes)

@[simp] theorem iteratedBlockEvaluation_outer_X
    {A T : Type} [CommRing A] [CommRing T] [Algebra A T] {n : ℕ}
    (d : BlockEquationData A T n) (ds : List (BlockEquationData A T n)) (k : Fin n) :
    iteratedBlockEvaluation (d :: ds)
        (Ideal.Quotient.mk _ (MvPolynomial.X k)) = d.point k := by
  let B := iteratedUnitCoefficientBlockRing A (blockEquationPolynomials ds)
  let tail : B →ₐ[A] T := iteratedBlockEvaluation ds
  let f : MvPolynomial (Fin n) B →ₐ[A] T :=
    { MvPolynomial.eval₂Hom tail.toRingHom d.point with
      commutes' := by intro a; simp [tail] }
  let I : Ideal (MvPolynomial (Fin n) B) :=
    Ideal.span {MvPolynomial.map (algebraMap A B) d.polynomial}
  change Ideal.Quotient.lift I f.toRingHom _
      (Ideal.Quotient.mk I (MvPolynomial.X k)) = d.point k
  rw [Ideal.Quotient.lift_mk]
  simp [f]

@[simp] theorem iteratedBlockEvaluation_outer_algebraMap
    {A T : Type} [CommRing A] [CommRing T] [Algebra A T] {n : ℕ}
    (d : BlockEquationData A T n) (ds : List (BlockEquationData A T n))
    (b : iteratedUnitCoefficientBlockRing A (blockEquationPolynomials ds)) :
    iteratedBlockEvaluation (d :: ds)
        (Ideal.Quotient.mk _ (MvPolynomial.C b)) =
      iteratedBlockEvaluation ds b := by
  let B := iteratedUnitCoefficientBlockRing A (blockEquationPolynomials ds)
  let tail : B →ₐ[A] T := iteratedBlockEvaluation ds
  let f : MvPolynomial (Fin n) B →ₐ[A] T :=
    { MvPolynomial.eval₂Hom tail.toRingHom d.point with
      commutes' := by intro a; simp [tail] }
  let I : Ideal (MvPolynomial (Fin n) B) :=
    Ideal.span {MvPolynomial.map (algebraMap A B) d.polynomial}
  change Ideal.Quotient.lift I f.toRingHom _
      (Ideal.Quotient.mk I (MvPolynomial.C b)) = tail b
  rw [Ideal.Quotient.lift_mk]
  simp [f, tail]

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The `i`th packet coordinate inside an iterated disjoint-block quotient. Earlier packet
coordinates are outer variables; later coordinates are embedded recursively as constants. -/
def iteratedBlockCoordinate
    {A T : Type} [CommRing A] [CommRing T] [Algebra A T] {n : ℕ} :
    (D : List (BlockEquationData A T n)) →
      Fin D.length → Fin n →
        iteratedUnitCoefficientBlockRing A (blockEquationPolynomials D)
  | [], i, _ => Fin.elim0 i
  | _ :: ds, i, k =>
      Fin.cases
        (Ideal.Quotient.mk _ (MvPolynomial.X k))
        (fun i' => Ideal.Quotient.mk _
          (MvPolynomial.C (iteratedBlockCoordinate ds i' k))) i

/-- Evaluation sends each canonical nested-block coordinate to the corresponding prescribed
coordinate of that block's target point. -/
@[simp] theorem iteratedBlockEvaluation_iteratedBlockCoordinate
    {A T : Type} [CommRing A] [CommRing T] [Algebra A T] {n : ℕ}
    (D : List (BlockEquationData A T n)) (i : Fin D.length) (k : Fin n) :
    iteratedBlockEvaluation D (iteratedBlockCoordinate D i k) =
      (D.get i).point k := by
  induction D with
  | nil => exact Fin.elim0 i
  | cons d ds ih =>
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [iteratedBlockCoordinate]
      · simp [iteratedBlockCoordinate, ih]

end
end GaloisForLFunctions.HTGeometry
