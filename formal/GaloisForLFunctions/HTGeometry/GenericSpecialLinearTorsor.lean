import GaloisForLFunctions.HTGeometry.DifferentialMatrixGauge
import GaloisForLFunctions.HTGeometry.DeterminantDerivation
import GaloisForLFunctions.HTGeometry.MvPolynomialTotalDerivation
import GaloisForLFunctions.HTGeometry.DifferenceCoordinateRing
import GaloisForLFunctions.HTGeometry.DifferentialDeltaQuotient

/-!
# The generic special-linear differential torsor

For a traceless system matrix `A` over a differential ring `I`, the polynomial ring in `N²`
indeterminates carries the derivation making the generic matrix a solution of `δ Y = Y A`.  Because
`A` is traceless the Wronskian is a constant of that derivation, so the relation `det Y = 1`
generates a differential ideal, and the quotient is the coordinate ring of the generic
special-linear torsor: a differential ring in which the generic matrix is a fundamental matrix of
determinant one.
-/

open scoped Differential
open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} [CommRing I] [Differential I] {N : ℕ}

/-- The derivation of the generic coordinate ring for which the generic matrix solves
`δ Y = Y A`. -/
def genericDerivation (A : Matrix (Fin N) (Fin N) I) :
    Derivation ℤ (MvPolynomial (Fin N × Fin N) I) (MvPolynomial (Fin N × Fin N) I) :=
  mvTotalDerivation (fun p : Fin N × Fin N => ∑ k, X (p.1, k) * C (A k p.2))

/-- The differential structure of the generic coordinate ring. -/
@[reducible] def genericDifferential (A : Matrix (Fin N) (Fin N) I) :
    Differential (MvPolynomial (Fin N × Fin N) I) := ⟨genericDerivation A⟩

@[simp] theorem genericDifferential_X (A : Matrix (Fin N) (Fin N) I) (i j : Fin N) :
    @Differential.deriv _ _ (genericDifferential A) (X (i, j))
      = ∑ k, X (i, k) * C (A k j) :=
  mvTotalDerivation_X _ _

@[simp] theorem genericDifferential_C (A : Matrix (Fin N) (Fin N) I) (a : I) :
    @Differential.deriv _ _ (genericDifferential A) (C a) = C (a′) :=
  mvTotalDerivation_C _ _

/-- **The generic matrix solves the system.** -/
theorem matDeriv_fundamentalMatrix (A : Matrix (Fin N) (Fin N) I) :
    @matDeriv _ _ (genericDifferential A) _ _ (fundamentalMatrix I N)
      = fundamentalMatrix I N * A.map (C : I →+* MvPolynomial (Fin N × Fin N) I) := by
  apply Matrix.ext
  intro i j
  show @Differential.deriv _ _ (genericDifferential A) (X (i, j)) = _
  rw [genericDifferential_X]
  simp [Matrix.mul_apply, fundamentalMatrix, Matrix.map_apply]

omit [Differential I] in
/-- The trace of the mapped system matrix. -/
theorem trace_map_C (A : Matrix (Fin N) (Fin N) I) :
    (A.map (C : I →+* MvPolynomial (Fin N × Fin N) I)).trace = C A.trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

/-- **A traceless system makes the Wronskian a constant.** -/
theorem deriv_det_fundamentalMatrix (A : Matrix (Fin N) (Fin N) I) (hA : A.trace = 0) :
    @Differential.deriv _ _ (genericDifferential A) ((fundamentalMatrix I N).det) = 0 := by
  have h := @deriv_det_of_system _ _ (genericDifferential A) N (fundamentalMatrix I N)
    (A.map (C : I →+* MvPolynomial (Fin N × Fin N) I))
    (fun i j => congrFun (congrFun (matDeriv_fundamentalMatrix A) i) j)
  rw [trace_map_C, hA, map_zero, mul_zero] at h
  exact h

/-- The relation cutting out the special-linear torsor. -/
def slRelation (I : Type*) [CommRing I] (N : ℕ) : Ideal (MvPolynomial (Fin N × Fin N) I) :=
  Ideal.span {(fundamentalMatrix I N).det - 1}

/-- **The special-linear relation is a differential ideal** for a traceless system. -/
theorem isDeltaIdeal_slRelation (A : Matrix (Fin N) (Fin N) I) (hA : A.trace = 0) :
    @IsDeltaIdeal _ _ (genericDifferential A) (slRelation I N) := by
  intro x hx
  rw [slRelation, Ideal.mem_span_singleton] at hx ⊢
  obtain ⟨r, rfl⟩ := hx
  refine ⟨@Differential.deriv _ _ (genericDifferential A) r, ?_⟩
  have hd : @Differential.deriv _ _ (genericDifferential A) ((fundamentalMatrix I N).det - 1) = 0 := by
    rw [map_sub, deriv_det_fundamentalMatrix A hA, Derivation.map_one_eq_zero, sub_zero]
  rw [Derivation.leibniz, hd]
  simp [smul_eq_mul]

/-! ### The torsor coordinate ring -/

/-- The coordinate ring of the generic special-linear torsor. -/
abbrev genericSL (I : Type*) [CommRing I] (N : ℕ) : Type _ :=
  MvPolynomial (Fin N × Fin N) I ⧸ slRelation I N

/-- The differential structure of the torsor coordinate ring. -/
@[reducible] def genericSLDifferential (A : Matrix (Fin N) (Fin N) I) (hA : A.trace = 0) :
    Differential (genericSL I N) :=
  @quotientDifferential _ _ (genericDifferential A) (slRelation I N)
    (isDeltaIdeal_slRelation A hA)

/-- The generic matrix read in the torsor coordinate ring. -/
def torsorMatrix (I : Type*) [CommRing I] (N : ℕ) : Matrix (Fin N) (Fin N) (genericSL I N) :=
  (fundamentalMatrix I N).map (Ideal.Quotient.mk (slRelation I N))

omit [Differential I] in
/-- **The generic matrix of the torsor has determinant one.** -/
theorem det_torsorMatrix : (torsorMatrix I N).det = 1 := by
  have hmap : (torsorMatrix I N).det
      = Ideal.Quotient.mk (slRelation I N) ((fundamentalMatrix I N).det) := by
    rw [torsorMatrix, RingHom.map_det (Ideal.Quotient.mk (slRelation I N)) (fundamentalMatrix I N),
      RingHom.mapMatrix_apply]
  rw [hmap, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (slRelation I N)), ← map_sub]
  exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _)

/-- **The generic matrix of the torsor is a fundamental matrix.** -/
theorem matDeriv_torsorMatrix (A : Matrix (Fin N) (Fin N) I) (hA : A.trace = 0) :
    @matDeriv _ _ (genericSLDifferential A hA) _ _ (torsorMatrix I N)
      = torsorMatrix I N *
        A.map (((Ideal.Quotient.mk (slRelation I N)).comp
          (C : I →+* MvPolynomial (Fin N × Fin N) I))) := by
  apply Matrix.ext
  intro i j
  show @Differential.deriv _ _ (genericSLDifferential A hA)
      (Ideal.Quotient.mk (slRelation I N) (X (i, j))) = _
  rw [@quotientDifferential_deriv_mk _ _ (genericDifferential A) (slRelation I N)
    (isDeltaIdeal_slRelation A hA) (X (i, j)), genericDifferential_X, map_sum]
  simp [Matrix.mul_apply, Matrix.map_apply, torsorMatrix, fundamentalMatrix]

/-! ### The gauge substitution -/

/-- The substitution `Y ↦ g Y` on the generic coordinate ring. -/
def gaugeHom (g : Matrix (Fin N) (Fin N) I) :
    MvPolynomial (Fin N × Fin N) I →+* MvPolynomial (Fin N × Fin N) I :=
  eval₂Hom (C : I →+* MvPolynomial (Fin N × Fin N) I)
    (fun p : Fin N × Fin N => ∑ k, C (g p.1 k) * X (k, p.2))

omit [Differential I] in
@[simp] theorem gaugeHom_C (g : Matrix (Fin N) (Fin N) I) (a : I) :
    gaugeHom g (C a) = C a := by simp [gaugeHom]

omit [Differential I] in
@[simp] theorem gaugeHom_X (g : Matrix (Fin N) (Fin N) I) (i j : Fin N) :
    gaugeHom g (X (i, j)) = ∑ k, C (g i k) * X (k, j) := by simp [gaugeHom]

omit [Differential I] in
/-- **The gauge substitution multiplies the generic matrix on the left.** -/
theorem map_gaugeHom_fundamentalMatrix (g : Matrix (Fin N) (Fin N) I) :
    (fundamentalMatrix I N).map (gaugeHom g)
      = (g.map (C : I →+* MvPolynomial (Fin N × Fin N) I)) * fundamentalMatrix I N := by
  apply Matrix.ext
  intro i j
  show gaugeHom g (X (i, j)) = _
  rw [gaugeHom_X]
  simp [Matrix.mul_apply, Matrix.map_apply, fundamentalMatrix]

omit [Differential I] in
/-- The gauge substitution scales the Wronskian by the determinant of the gauge. -/
theorem gaugeHom_det (g : Matrix (Fin N) (Fin N) I) :
    gaugeHom g ((fundamentalMatrix I N).det)
      = C g.det * (fundamentalMatrix I N).det := by
  have h1 : gaugeHom g ((fundamentalMatrix I N).det)
      = ((fundamentalMatrix I N).map (gaugeHom g)).det := by
    rw [RingHom.map_det (gaugeHom g) (fundamentalMatrix I N), RingHom.mapMatrix_apply]
  rw [h1, map_gaugeHom_fundamentalMatrix, Matrix.det_mul]
  congr 1
  rw [RingHom.map_det (C : I →+* MvPolynomial (Fin N × Fin N) I) g, RingHom.mapMatrix_apply]

omit [Differential I] in
/-- **The gauge substitutions compose contravariantly.** -/
theorem gaugeHom_comp (g h : Matrix (Fin N) (Fin N) I) :
    (gaugeHom g).comp (gaugeHom h) = gaugeHom (h * g) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · rintro ⟨i, j⟩
    show gaugeHom g (gaugeHom h (X (i, j))) = gaugeHom (h * g) (X (i, j))
    rw [gaugeHom_X, gaugeHom_X, map_sum]
    have hL : ∑ k, gaugeHom g (C (h i k) * X (k, j))
        = ∑ l, C ((h * g) i l) * X (l, j) := by
      have hstep : ∀ k, gaugeHom g (C (h i k) * X (k, j))
          = ∑ l, C (h i k) * C (g k l) * X (l, j) := by
        intro k
        rw [map_mul, gaugeHom_C, gaugeHom_X, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by rw [map_mul]
    exact hL

omit [Differential I] in
theorem gaugeHom_one : gaugeHom (1 : Matrix (Fin N) (Fin N) I) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp
  · rintro ⟨i, j⟩
    rw [gaugeHom_X]
    simp [Matrix.one_apply]

/-- **The gauge substitution commutes with the derivation** when the gauge is constant. -/
theorem gaugeHom_deriv (A g : Matrix (Fin N) (Fin N) I) (hg : ∀ i j, (g i j)′ = 0)
    (p : MvPolynomial (Fin N × Fin N) I) :
    gaugeHom g (@Differential.deriv _ _ (genericDifferential A) p)
      = @Differential.deriv _ _ (genericDifferential A) (gaugeHom g p) := by
  have hX : ∀ i j : Fin N, gaugeHom g (@Differential.deriv _ _ (genericDifferential A) (X (i, j)))
      = @Differential.deriv _ _ (genericDifferential A) (gaugeHom g (X (i, j))) := by
    intro i j
    rw [genericDifferential_X, gaugeHom_X, map_sum, map_sum]
    have hL : ∀ k : Fin N, gaugeHom g (X (i, k) * C (A k j))
        = ∑ l, C (g i l) * X (l, k) * C (A k j) := by
      intro k
      rw [map_mul, gaugeHom_X, gaugeHom_C, Finset.sum_mul]
    have hR : ∀ l : Fin N,
        @Differential.deriv _ _ (genericDifferential A) (C (g i l) * X (l, j))
          = ∑ k, C (g i l) * (X (l, k) * C (A k j)) := by
      intro l
      rw [Derivation.leibniz, genericDifferential_X, genericDifferential_C, hg i l]
      simp only [smul_eq_mul, map_zero, mul_zero, add_zero, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun k _ => hL k, Finset.sum_congr rfl fun l _ => hR l,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  induction p using MvPolynomial.induction_on with
  | C a => rw [genericDifferential_C, gaugeHom_C, gaugeHom_C, genericDifferential_C]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p pq hp =>
      obtain ⟨i, j⟩ := pq
      have hLHS : gaugeHom g (@Differential.deriv _ _ (genericDifferential A) (p * X (i, j)))
          = gaugeHom g p *
              gaugeHom g (@Differential.deriv _ _ (genericDifferential A) (X (i, j)))
            + gaugeHom g (X (i, j)) *
              gaugeHom g (@Differential.deriv _ _ (genericDifferential A) p) := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul, map_add, map_mul]
      have hRHS : @Differential.deriv _ _ (genericDifferential A) (gaugeHom g (p * X (i, j)))
          = gaugeHom g p *
              @Differential.deriv _ _ (genericDifferential A) (gaugeHom g (X (i, j)))
            + gaugeHom g (X (i, j)) *
              @Differential.deriv _ _ (genericDifferential A) (gaugeHom g p) := by
        rw [map_mul, Derivation.leibniz]
        simp only [smul_eq_mul]
      rw [hLHS, hRHS, hp, hX i j]

/-! ### The gauge automorphisms of the torsor -/

omit [Differential I] in
theorem gaugeHom_mem_slRelation (g : Matrix (Fin N) (Fin N) I) (hg1 : g.det = 1)
    {x : MvPolynomial (Fin N × Fin N) I} (hx : x ∈ slRelation I N) :
    gaugeHom g x ∈ slRelation I N := by
  rw [slRelation, Ideal.mem_span_singleton] at hx ⊢
  obtain ⟨r, rfl⟩ := hx
  refine ⟨gaugeHom g r, ?_⟩
  rw [map_mul, map_sub, gaugeHom_det, hg1, map_one, one_mul, map_one]

/-- The gauge substitution descended to the torsor coordinate ring. -/
def gaugeQuot (g : Matrix (Fin N) (Fin N) I) (hg1 : g.det = 1) :
    genericSL I N →+* genericSL I N :=
  Ideal.Quotient.lift (slRelation I N)
    ((Ideal.Quotient.mk (slRelation I N)).comp (gaugeHom g))
    (fun _ ha => (Ideal.Quotient.eq_zero_iff_mem).mpr (gaugeHom_mem_slRelation g hg1 ha))

omit [Differential I] in
@[simp] theorem gaugeQuot_mk (g : Matrix (Fin N) (Fin N) I) (hg1 : g.det = 1)
    (p : MvPolynomial (Fin N × Fin N) I) :
    gaugeQuot g hg1 (Ideal.Quotient.mk (slRelation I N) p)
      = Ideal.Quotient.mk (slRelation I N) (gaugeHom g p) := rfl

omit [Differential I] in
/-- **The gauge substitutions compose contravariantly on the torsor.** -/
theorem gaugeQuot_gaugeQuot (g h : Matrix (Fin N) (Fin N) I) (hg1 : g.det = 1) (hh1 : h.det = 1)
    (hgh : (h * g).det = 1) (z : genericSL I N) :
    gaugeQuot g hg1 (gaugeQuot h hh1 z) = gaugeQuot (h * g) hgh z := by
  induction z using Quotient.inductionOn' with
  | h p =>
      have hcomp : gaugeHom g (gaugeHom h p) = gaugeHom (h * g) p :=
        RingHom.congr_fun (gaugeHom_comp g h) p
      show Ideal.Quotient.mk (slRelation I N) (gaugeHom g (gaugeHom h p))
        = Ideal.Quotient.mk (slRelation I N) (gaugeHom (h * g) p)
      rw [hcomp]

omit [Differential I] in
theorem gaugeQuot_one (z : genericSL I N) :
    gaugeQuot (1 : Matrix (Fin N) (Fin N) I) Matrix.det_one z = z := by
  induction z using Quotient.inductionOn' with
  | h p =>
      show Ideal.Quotient.mk (slRelation I N) (gaugeHom 1 p) = _
      rw [gaugeHom_one]
      rfl

omit [Differential I] in
/-- The adjugate of a matrix of determinant one again has determinant one. -/
theorem det_adjugate_eq_one {g : Matrix (Fin N) (Fin N) I} (hg1 : g.det = 1) :
    (Matrix.adjugate g).det = 1 := by
  rw [Matrix.det_adjugate, hg1, one_pow]

/-- **The gauge automorphism of the torsor.** -/
def gaugeAut (g : Matrix (Fin N) (Fin N) I) (hg1 : g.det = 1) :
    genericSL I N ≃+* genericSL I N where
  toFun := gaugeQuot g hg1
  invFun := gaugeQuot (Matrix.adjugate g) (det_adjugate_eq_one hg1)
  left_inv := by
    intro z
    have hprod : (g * Matrix.adjugate g) = 1 := by
      rw [Matrix.mul_adjugate, hg1, one_smul]
    have h := gaugeQuot_gaugeQuot (Matrix.adjugate g) g (det_adjugate_eq_one hg1) hg1
      (by rw [hprod, Matrix.det_one]) z
    rw [h]
    simpa [hprod] using gaugeQuot_one (I := I) (N := N) z
  right_inv := by
    intro z
    have hprod : (Matrix.adjugate g * g) = 1 := by
      rw [Matrix.adjugate_mul, hg1, one_smul]
    have h := gaugeQuot_gaugeQuot g (Matrix.adjugate g) hg1 (det_adjugate_eq_one hg1)
      (by rw [hprod, Matrix.det_one]) z
    rw [h]
    simpa [hprod] using gaugeQuot_one (I := I) (N := N) z
  map_mul' := map_mul _
  map_add' := map_add _

omit [Differential I] in
@[simp] theorem gaugeAut_mk (g : Matrix (Fin N) (Fin N) I) (hg1 : g.det = 1)
    (p : MvPolynomial (Fin N × Fin N) I) :
    gaugeAut g hg1 (Ideal.Quotient.mk (slRelation I N) p)
      = Ideal.Quotient.mk (slRelation I N) (gaugeHom g p) := rfl

omit [Differential I] in
/-- **The gauge automorphism multiplies the fundamental matrix on the left.** -/
theorem map_gaugeAut_torsorMatrix (g : Matrix (Fin N) (Fin N) I) (hg1 : g.det = 1) :
    (torsorMatrix I N).map (gaugeAut g hg1 : genericSL I N →+* genericSL I N)
      = (g.map ((Ideal.Quotient.mk (slRelation I N)).comp
          (C : I →+* MvPolynomial (Fin N × Fin N) I))) * torsorMatrix I N := by
  apply Matrix.ext
  intro i j
  show gaugeAut g hg1 (Ideal.Quotient.mk (slRelation I N) (X (i, j))) = _
  rw [gaugeAut_mk, gaugeHom_X, map_sum]
  simp [Matrix.mul_apply, Matrix.map_apply, torsorMatrix, fundamentalMatrix]

/-- **The gauge automorphism is differential.** -/
theorem gaugeAut_deriv (A g : Matrix (Fin N) (Fin N) I) (hA : A.trace = 0)
    (hg : ∀ i j, (g i j)′ = 0) (hg1 : g.det = 1) (z : genericSL I N) :
    gaugeAut g hg1 (@Differential.deriv _ _ (genericSLDifferential A hA) z)
      = @Differential.deriv _ _ (genericSLDifferential A hA) (gaugeAut g hg1 z) := by
  induction z using Quotient.inductionOn' with
  | h p =>
      show gaugeAut g hg1 (@Differential.deriv _ _ (genericSLDifferential A hA)
          (Ideal.Quotient.mk (slRelation I N) p))
        = @Differential.deriv _ _ (genericSLDifferential A hA)
          (gaugeAut g hg1 (Ideal.Quotient.mk (slRelation I N) p))
      rw [@quotientDifferential_deriv_mk _ _ (genericDifferential A) (slRelation I N)
        (isDeltaIdeal_slRelation A hA) p, gaugeAut_mk, gaugeAut_mk,
        @quotientDifferential_deriv_mk _ _ (genericDifferential A) (slRelation I N)
        (isDeltaIdeal_slRelation A hA) (gaugeHom g p), gaugeHom_deriv A g hg p]

/-! ### The identity point and faithfulness -/

/-- Evaluation of the generic matrix at the identity matrix. -/
def slEvalOne (I : Type*) [CommRing I] (N : ℕ) : MvPolynomial (Fin N × Fin N) I →+* I :=
  eval₂Hom (RingHom.id I) (fun p : Fin N × Fin N => if p.1 = p.2 then 1 else 0)

omit [Differential I] in
@[simp] theorem slEvalOne_C (a : I) : slEvalOne I N (C a) = a := by simp [slEvalOne]

omit [Differential I] in
@[simp] theorem slEvalOne_X (i j : Fin N) :
    slEvalOne I N (X (i, j)) = if i = j then 1 else 0 := by simp [slEvalOne]

omit [Differential I] in
theorem slEvalOne_det : slEvalOne I N ((fundamentalMatrix I N).det) = 1 := by
  have hmap : (fundamentalMatrix I N).map (slEvalOne I N) = (1 : Matrix (Fin N) (Fin N) I) := by
    apply Matrix.ext
    intro i j
    show slEvalOne I N (X (i, j)) = _
    rw [slEvalOne_X]
    simp [Matrix.one_apply]
  have hd : slEvalOne I N ((fundamentalMatrix I N).det)
      = ((fundamentalMatrix I N).map (slEvalOne I N)).det := by
    rw [RingHom.map_det (slEvalOne I N) (fundamentalMatrix I N), RingHom.mapMatrix_apply]
  rw [hd, hmap, Matrix.det_one]

/-- The identity point of the torsor: a retraction of the base inclusion. -/
def slEvalOneQuot (I : Type*) [CommRing I] (N : ℕ) : genericSL I N →+* I :=
  Ideal.Quotient.lift (slRelation I N) (slEvalOne I N) (by
    intro a ha
    rw [slRelation, Ideal.mem_span_singleton] at ha
    obtain ⟨r, rfl⟩ := ha
    rw [map_mul, map_sub, slEvalOne_det, map_one, sub_self, zero_mul])

omit [Differential I] in
@[simp] theorem slEvalOneQuot_mk_C (a : I) :
    slEvalOneQuot I N (Ideal.Quotient.mk (slRelation I N) (C a)) = a := by
  show slEvalOne I N (C a) = a
  rw [slEvalOne_C]

omit [Differential I] in
/-- **Distinct gauges act differently.** -/
theorem gaugeAut_injective {g g' : Matrix (Fin N) (Fin N) I} (hg1 : g.det = 1) (hg1' : g'.det = 1)
    (h : ∀ z : genericSL I N, gaugeAut g hg1 z = gaugeAut g' hg1' z) : g = g' := by
  classical
  set c : I →+* genericSL I N :=
    (Ideal.Quotient.mk (slRelation I N)).comp (C : I →+* MvPolynomial (Fin N × Fin N) I) with hc
  have hmat : (g.map c) * torsorMatrix I N = (g'.map c) * torsorMatrix I N := by
    rw [← map_gaugeAut_torsorMatrix g hg1, ← map_gaugeAut_torsorMatrix g' hg1']
    apply Matrix.ext
    intro i j
    exact h _
  have hadj : torsorMatrix I N * Matrix.adjugate (torsorMatrix I N) = 1 := by
    rw [Matrix.mul_adjugate, det_torsorMatrix, one_smul]
  have hentry : g.map c = g'.map c := by
    have := congrArg (fun M => M * Matrix.adjugate (torsorMatrix I N)) hmat
    simpa [Matrix.mul_assoc, hadj] using this
  apply Matrix.ext
  intro i j
  have := congrFun (congrFun hentry i) j
  simp only [Matrix.map_apply] at this
  have h2 := congrArg (slEvalOneQuot I N) this
  simpa [hc] using h2

/-! ### The torsor theorem -/

omit [Differential I] in
/-- The gauge automorphism fixes the base. -/
@[simp] theorem gaugeAut_base (g : Matrix (Fin N) (Fin N) I) (hg1 : g.det = 1) (a : I) :
    gaugeAut g hg1 (Ideal.Quotient.mk (slRelation I N) (C a))
      = Ideal.Quotient.mk (slRelation I N) (C a) := by
  rw [gaugeAut_mk, gaugeHom_C]

/-- **The generic special-linear differential torsor.**  For a traceless system matrix `A` over a
differential ring `I` the coordinate ring `genericSL I N` carries a derivation for which the generic
matrix is a fundamental matrix of determinant one, and every constant gauge of determinant one acts
on it by a differential automorphism over `I`, by left multiplication on the fundamental matrix, and
distinct gauges act differently. -/
theorem generic_specialLinear_torsor (A : Matrix (Fin N) (Fin N) I) (hA : A.trace = 0) :
    (torsorMatrix I N).det = 1 ∧
    @matDeriv _ _ (genericSLDifferential A hA) _ _ (torsorMatrix I N)
      = torsorMatrix I N * A.map ((Ideal.Quotient.mk (slRelation I N)).comp
          (C : I →+* MvPolynomial (Fin N × Fin N) I)) ∧
    (∀ (g : Matrix (Fin N) (Fin N) I) (_ : ∀ i j, (g i j)′ = 0) (hg1 : g.det = 1),
      (∀ a : I, gaugeAut g hg1 (Ideal.Quotient.mk (slRelation I N) (C a))
          = Ideal.Quotient.mk (slRelation I N) (C a)) ∧
      (∀ z : genericSL I N, gaugeAut g hg1 (@Differential.deriv _ _ (genericSLDifferential A hA) z)
          = @Differential.deriv _ _ (genericSLDifferential A hA) (gaugeAut g hg1 z)) ∧
      (torsorMatrix I N).map (gaugeAut g hg1 : genericSL I N →+* genericSL I N)
          = (g.map ((Ideal.Quotient.mk (slRelation I N)).comp
              (C : I →+* MvPolynomial (Fin N × Fin N) I))) * torsorMatrix I N) ∧
    (∀ (g g' : Matrix (Fin N) (Fin N) I) (hg1 : g.det = 1) (hg1' : g'.det = 1),
      (∀ z : genericSL I N, gaugeAut g hg1 z = gaugeAut g' hg1' z) → g = g') := by
  refine ⟨det_torsorMatrix, matDeriv_torsorMatrix A hA, ?_, ?_⟩
  · intro g hg hg1
    exact ⟨gaugeAut_base g hg1, gaugeAut_deriv A g hA hg hg1,
      map_gaugeAut_torsorMatrix g hg1⟩
  · intro g g' hg1 hg1' h
    exact gaugeAut_injective hg1 hg1' h

/-- **Every differential automorphism of the torsor over the base is a constant gauge.**  This is
the cocycle half: the automorphism moves the fundamental matrix by left multiplication with a
constant matrix of determinant one. -/
theorem exists_gaugeCocycle_of_differentialAut (A : Matrix (Fin N) (Fin N) I) (hA : A.trace = 0)
    (φ : genericSL I N ≃+* genericSL I N)
    (hφ : ∀ x : genericSL I N,
      φ (@Differential.deriv _ _ (genericSLDifferential A hA) x)
        = @Differential.deriv _ _ (genericSLDifferential A hA) (φ x))
    (hbase : ∀ a : I, φ (Ideal.Quotient.mk (slRelation I N) (C a))
      = Ideal.Quotient.mk (slRelation I N) (C a)) :
    ∃ Z : Matrix (Fin N) (Fin N) (genericSL I N),
      (∀ i j, @Differential.deriv _ _ (genericSLDifferential A hA) (Z i j) = 0) ∧
      (torsorMatrix I N).map (φ : genericSL I N →+* genericSL I N) = Z * torsorMatrix I N ∧
      Z.det = 1 := by
  have hAfix : (A.map ((Ideal.Quotient.mk (slRelation I N)).comp
      (C : I →+* MvPolynomial (Fin N × Fin N) I))).map (φ : genericSL I N →+* genericSL I N)
      = A.map ((Ideal.Quotient.mk (slRelation I N)).comp
        (C : I →+* MvPolynomial (Fin N × Fin N) I)) := by
    apply Matrix.ext
    intro i j
    show φ (Ideal.Quotient.mk (slRelation I N) (C (A i j))) = _
    rw [hbase]
    rfl
  exact @exists_constantGauge_of_differentialAut _ _ (genericSLDifferential A hA) N
    (torsorMatrix I N)
    (A.map ((Ideal.Quotient.mk (slRelation I N)).comp
      (C : I →+* MvPolynomial (Fin N × Fin N) I)))
    (matDeriv_torsorMatrix A hA) det_torsorMatrix φ hφ hAfix

end

end GaloisForLFunctions.HTGeometry
