import GaloisForLFunctions.HTGeometry.GenericSpecialLinearTorsor

/-!
# Coinvariance of the generic special-linear torsor

The generic gauge of the generic special-linear torsor is the torsor of the torsor: over the ring
`R = genericSL I N` one takes a *second* generic matrix `g` of determinant one, and the coaction
`Y ↦ g·Y` sends `R` into `Ω = genericSL R N`.

An element fixed by that generic gauge is a base scalar, and the proof is a one-line specialisation:
`Ω` is the coordinate ring of a *free* determinant-one matrix, so `g` may be specialised to `Y⁻¹`,
which is legitimate because the generic matrix has determinant one and is therefore invertible over
`R` itself.  Under that specialisation the coaction becomes evaluation at the identity point, whose
image is the base ring.

This is the hard half of the differential Galois correspondence for the generic torsor, obtained
without δ-simplicity, without a no-new-constants theorem, and without faithfully flat descent.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} [CommRing I] {N : ℕ}

/-! ### Evaluation of the torsor at a determinant-one point -/

/-- Evaluation of the generic coordinate ring at a matrix over another ring. -/
def slPointPoly {S : Type*} [CommRing S] (f : I →+* S) (g : Matrix (Fin N) (Fin N) S) :
    MvPolynomial (Fin N × Fin N) I →+* S :=
  eval₂Hom f (fun p : Fin N × Fin N => g p.1 p.2)

@[simp] theorem slPointPoly_C {S : Type*} [CommRing S] (f : I →+* S)
    (g : Matrix (Fin N) (Fin N) S) (a : I) : slPointPoly f g (C a) = f a := by
  simp [slPointPoly]

@[simp] theorem slPointPoly_X {S : Type*} [CommRing S] (f : I →+* S)
    (g : Matrix (Fin N) (Fin N) S) (i j : Fin N) :
    slPointPoly f g (X (i, j)) = g i j := by
  simp [slPointPoly]

theorem slPointPoly_det {S : Type*} [CommRing S] (f : I →+* S)
    (g : Matrix (Fin N) (Fin N) S) :
    slPointPoly f g ((fundamentalMatrix I N).det) = g.det := by
  have hmap : (fundamentalMatrix I N).map (slPointPoly f g) = g := by
    apply Matrix.ext
    intro i j
    show slPointPoly f g (X (i, j)) = _
    rw [slPointPoly_X]
  have hd : slPointPoly f g ((fundamentalMatrix I N).det)
      = ((fundamentalMatrix I N).map (slPointPoly f g)).det := by
    rw [RingHom.map_det (slPointPoly f g) (fundamentalMatrix I N), RingHom.mapMatrix_apply]
  rw [hd, hmap]

/-- Evaluation of the torsor coordinate ring at a determinant-one point. -/
def slPoint {S : Type*} [CommRing S] (f : I →+* S) (g : Matrix (Fin N) (Fin N) S)
    (hg : g.det = 1) : genericSL I N →+* S :=
  Ideal.Quotient.lift (slRelation I N) (slPointPoly f g) (by
    intro a ha
    rw [slRelation, Ideal.mem_span_singleton] at ha
    obtain ⟨r, rfl⟩ := ha
    rw [map_mul, map_sub, slPointPoly_det, hg, map_one, sub_self, zero_mul])

@[simp] theorem slPoint_mk {S : Type*} [CommRing S] (f : I →+* S)
    (g : Matrix (Fin N) (Fin N) S) (hg : g.det = 1) (p : MvPolynomial (Fin N × Fin N) I) :
    slPoint f g hg (Ideal.Quotient.mk (slRelation I N) p) = slPointPoly f g p := rfl

/-- The point evaluation on the generic matrix returns the point. -/
theorem map_slPoint_torsorMatrix {S : Type*} [CommRing S] (f : I →+* S)
    (g : Matrix (Fin N) (Fin N) S) (hg : g.det = 1) :
    (torsorMatrix I N).map (slPoint f g hg) = g := by
  apply Matrix.ext
  intro i j
  show slPoint f g hg (Ideal.Quotient.mk (slRelation I N) (X (i, j))) = _
  rw [slPoint_mk, slPointPoly_X]

/-! ### The generic gauge -/

/-- The base inclusion of the torsor coordinate ring. -/
def slBase (I : Type*) [CommRing I] (N : ℕ) : I →+* genericSL I N :=
  (Ideal.Quotient.mk (slRelation I N)).comp (C : I →+* MvPolynomial (Fin N × Fin N) I)

/-- The generic gauge ring: the torsor of the torsor. -/
abbrev genericGauge (I : Type*) [CommRing I] (N : ℕ) : Type _ := genericSL (genericSL I N) N

/-- The structure map of the generic gauge ring. -/
abbrev genericGaugeBase (I : Type*) [CommRing I] (N : ℕ) :
    genericSL I N →+* genericGauge I N := slBase (genericSL I N) N

/-- The generic gauge matrix. -/
abbrev genericGaugeMatrix (I : Type*) [CommRing I] (N : ℕ) :
    Matrix (Fin N) (Fin N) (genericGauge I N) := torsorMatrix (genericSL I N) N

/-- The generic matrix pushed into the gauge ring. -/
def torsorMatrixInGauge (I : Type*) [CommRing I] (N : ℕ) :
    Matrix (Fin N) (Fin N) (genericGauge I N) :=
  (torsorMatrix I N).map (genericGaugeBase I N)

theorem det_torsorMatrixInGauge : (torsorMatrixInGauge I N).det = 1 := by
  have hd : (torsorMatrixInGauge I N).det
      = genericGaugeBase I N ((torsorMatrix I N).det) := by
    rw [torsorMatrixInGauge, RingHom.map_det (genericGaugeBase I N) (torsorMatrix I N),
      RingHom.mapMatrix_apply]
  rw [hd, det_torsorMatrix, map_one]

theorem det_genericGauge_mul :
    (genericGaugeMatrix I N * torsorMatrixInGauge I N).det = 1 := by
  rw [Matrix.det_mul, det_torsorMatrix, det_torsorMatrixInGauge, one_mul]

/-- **The generic gauge coaction** `Y ↦ g·Y`, with `g` the generic gauge matrix. -/
def genericGaugeCoaction (I : Type*) [CommRing I] (N : ℕ) :
    genericSL I N →+* genericGauge I N :=
  slPoint ((genericGaugeBase I N).comp (slBase I N))
    (genericGaugeMatrix I N * torsorMatrixInGauge I N) det_genericGauge_mul

theorem det_torsorMatrix_inv : ((torsorMatrix I N)⁻¹).det = 1 := by
  rw [Matrix.det_nonsing_inv, det_torsorMatrix, Ring.inverse_one]

/-- The specialisation of the generic gauge at `g = Y⁻¹`. -/
def genericGaugeEval (I : Type*) [CommRing I] (N : ℕ) :
    genericGauge I N →+* genericSL I N :=
  slPoint (RingHom.id (genericSL I N)) ((torsorMatrix I N)⁻¹) det_torsorMatrix_inv

theorem genericGaugeEval_base (x : genericSL I N) :
    genericGaugeEval I N (genericGaugeBase I N x) = x := by
  show genericGaugeEval I N
      (Ideal.Quotient.mk (slRelation (genericSL I N) N) (C x)) = x
  rw [genericGaugeEval, slPoint_mk, slPointPoly_C, RingHom.id_apply]

theorem map_genericGaugeEval_gaugeMatrix :
    (genericGaugeMatrix I N).map (genericGaugeEval I N) = (torsorMatrix I N)⁻¹ :=
  map_slPoint_torsorMatrix _ _ _

theorem map_genericGaugeEval_torsorInGauge :
    (torsorMatrixInGauge I N).map (genericGaugeEval I N) = torsorMatrix I N := by
  apply Matrix.ext
  intro i j
  show genericGaugeEval I N (genericGaugeBase I N (torsorMatrix I N i j)) = _
  rw [genericGaugeEval_base]

theorem isUnit_det_torsorMatrix : IsUnit (torsorMatrix I N).det := by
  rw [det_torsorMatrix]; exact isUnit_one

theorem genericGaugeEval_comp_base :
    (genericGaugeEval I N).comp (genericGaugeBase I N) = RingHom.id (genericSL I N) := by
  refine RingHom.ext fun x => ?_
  exact genericGaugeEval_base x

/-- **Specialising the generic gauge at `g = Y⁻¹` evaluates at the identity point.** -/
theorem genericGaugeEval_coaction (x : genericSL I N) :
    genericGaugeEval I N (genericGaugeCoaction I N x)
      = slBase I N (slEvalOneQuot I N x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hpoint : ∀ q : Fin N × Fin N,
      genericGaugeEval I N
          ((genericGaugeMatrix I N * torsorMatrixInGauge I N) q.1 q.2)
        = (1 : Matrix (Fin N) (Fin N) (genericSL I N)) q.1 q.2 := by
    intro q
    have hmul := map_mul ((genericGaugeEval I N).mapMatrix)
      (genericGaugeMatrix I N) (torsorMatrixInGauge I N)
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      map_genericGaugeEval_gaugeMatrix, map_genericGaugeEval_torsorInGauge,
      Matrix.nonsing_inv_mul _ isUnit_det_torsorMatrix] at hmul
    exact congrFun (congrFun hmul q.1) q.2
  have hleft : genericGaugeEval I N (genericGaugeCoaction I N
      (Ideal.Quotient.mk (slRelation I N) p))
      = eval₂ (slBase I N)
          (fun q : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) (genericSL I N)) q.1 q.2) p := by
    show genericGaugeEval I N (slPointPoly ((genericGaugeBase I N).comp (slBase I N))
      (genericGaugeMatrix I N * torsorMatrixInGauge I N) p) = _
    rw [slPointPoly]
    show genericGaugeEval I N (eval₂ ((genericGaugeBase I N).comp (slBase I N))
      (fun q : Fin N × Fin N =>
        (genericGaugeMatrix I N * torsorMatrixInGauge I N) q.1 q.2) p) = _
    rw [MvPolynomial.eval₂_comp_left (genericGaugeEval I N)]
    congr 1
    · rw [← RingHom.comp_assoc, genericGaugeEval_comp_base, RingHom.id_comp]
    · funext q
      exact hpoint q
  have hright : slBase I N (slEvalOneQuot I N (Ideal.Quotient.mk (slRelation I N) p))
      = eval₂ (slBase I N)
          (fun q : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) (genericSL I N)) q.1 q.2) p := by
    show slBase I N (slEvalOne I N p) = _
    rw [slEvalOne]
    show slBase I N (eval₂ (RingHom.id I)
      (fun q : Fin N × Fin N => if q.1 = q.2 then (1 : I) else 0) p) = _
    rw [MvPolynomial.eval₂_comp_left (slBase I N)]
    have hcomp : (slBase I N).comp (RingHom.id I) = slBase I N := RingHom.comp_id _
    have hfun : (⇑(slBase I N) ∘ fun q : Fin N × Fin N => if q.1 = q.2 then (1 : I) else 0)
        = fun q : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) (genericSL I N)) q.1 q.2 := by
      funext q
      by_cases hq : q.1 = q.2 <;> simp [hq, Matrix.one_apply]
    rw [hcomp, hfun]
  rw [hleft, hright]

/-- **Generic-gauge coinvariance.**  An element of the generic special-linear torsor fixed by the
generic gauge already lies in the base ring.  This is the hard half of the differential Galois
correspondence for the generic torsor, proved by specialising the generic gauge at `g = Y⁻¹`. -/
theorem mem_range_slBase_of_genericGauge_invariant {x : genericSL I N}
    (hx : genericGaugeCoaction I N x = genericGaugeBase I N x) :
    x ∈ (slBase I N).range := by
  refine ⟨slEvalOneQuot I N x, ?_⟩
  have h := congrArg (genericGaugeEval I N) hx
  rw [genericGaugeEval_base, genericGaugeEval_coaction] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
