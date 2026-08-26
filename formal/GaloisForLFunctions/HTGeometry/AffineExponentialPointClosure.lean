import GaloisForLFunctions.HTGeometry.AffineExponentialPointEvaluation
import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedReduced
import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Zariski closure of additive-exponential point subgroups

The vanishing ideal of a subgroup of `Gₐⁿ × Gₘⁿ` is a radical Hopf ideal.  The proof is entirely
coordinate-algebraic.  Translated regular functions show directly that the common zero locus is a
subgroup.  For the coideal condition, evaluations of the defining subgroup jointly separate the
quotient, and a basis argument promotes joint separation to the tensor square.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace AffineExponentialPointClosure

noncomputable section

open AffineExponentialGroup AffineExponentialPointEvaluation

variable {k : Type*} [Field k]

/-- Regular functions vanishing on a set of additive-exponential points. -/
def vanishingIdeal {n : ℕ} (S : Set (Point k n)) : Ideal (CoordinateAlgebra k n) where
  carrier := {a | ∀ p ∈ S, eval (k := k) p a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb p hp
    simp [ha p hp, hb p hp]
  smul_mem' := by
    intro a b hb p hp
    simp [hb p hp]

@[simp] theorem mem_vanishingIdeal_iff {n : ℕ} {S : Set (Point k n)}
    {a : CoordinateAlgebra k n} :
    a ∈ vanishingIdeal S ↔ ∀ p ∈ S, eval (k := k) p a = 0 := Iff.rfl

/-- Common zero locus of an ideal in the mixed coordinate algebra. -/
def zeroLocus {n : ℕ} (I : Ideal (CoordinateAlgebra k n)) : Set (Point k n) :=
  {p | ∀ a ∈ I, eval (k := k) p a = 0}

@[simp] theorem mem_zeroLocus_iff {n : ℕ} {I : Ideal (CoordinateAlgebra k n)}
    {p : Point k n} :
    p ∈ zeroLocus I ↔ ∀ a ∈ I, eval (k := k) p a = 0 := Iff.rfl

/-- Torus evaluation at the identity point is the group-algebra counit. -/
theorem torusEval_one_point {n : ℕ} (a : TorusCoordinateAlgebra k n) :
    AlgebraicTorusCharacter.eval (k := k) (1 : Fin n → kˣ) a =
      Coalgebra.counit (R := k) a := by
  induction a using AddMonoidAlgebra.induction_on with
  | hM m => simp [AddMonoidAlgebra.of, AlgebraicTorusCharacter.eval,
      AlgebraicTorusCharacter.monoidHom]
  | hadd a b ha hb => simp [ha, hb]
  | hsmul c a ha => simp [ha]

/-- Additive evaluation at zero is the symmetric-algebra counit. -/
theorem additiveEval_zero_point {n : ℕ} (b : AdditiveCoordinateAlgebra k n) :
    additiveEval (k := k) (0 : Fin n → k) b = Coalgebra.counit (R := k) b := by
  let rhs : AdditiveCoordinateAlgebra k n →ₐ[k] k :=
    Bialgebra.counitAlgHom k (AdditiveCoordinateAlgebra k n)
  have hmaps : additiveEval (k := k) (0 : Fin n → k) = rhs := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    simp [rhs, additiveEval, additiveLinearEval, SymmetricAlgebra.algebraMapInv_ι]
  exact DFunLike.congr_fun hmaps b

/-- Full evaluation at the identity point is the Hopf counit. -/
theorem eval_one_point {n : ℕ} (w : CoordinateAlgebra k n) :
    eval (k := k) (1 : Point k n) w = Coalgebra.counit (R := k) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | tmul a b =>
      rw [eval_tmul]
      simp only [torusPart_one, additivePart_one]
      rw [torusEval_one_point, additiveEval_zero_point]
      simp [mul_comm]

/-- Evaluate the right tensor factor of a doubled coordinate function at a point. -/
def rightSlice {n : ℕ} (p : Point k n) :
    (CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) →ₐ[k]
      CoordinateAlgebra k n :=
  Algebra.TensorProduct.lift (AlgHom.id k (CoordinateAlgebra k n))
    ((Algebra.ofId k (CoordinateAlgebra k n)).comp (eval (k := k) p))
    (fun _ _ ↦ Commute.all _ _)

/-- Right translation of a regular function by a point, defined through comultiplication. -/
def rightTranslate {n : ℕ} (p : Point k n) :
    CoordinateAlgebra k n →ₐ[k] CoordinateAlgebra k n :=
  (rightSlice p).comp (Bialgebra.comulAlgHom k (CoordinateAlgebra k n))

/-- Evaluation commutes with the right tensor slice. -/
theorem eval_rightSlice {n : ℕ} (p q : Point k n)
    (u : CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n) :
    eval (k := k) q (rightSlice p u) =
      (Algebra.TensorProduct.lift (eval (k := k) q) (eval (k := k) p)
        (fun _ _ ↦ Commute.all _ _)) u := by
  induction u using TensorProduct.induction_on with
  | zero => simp [rightSlice]
  | add a b ha hb => simp [ha, hb]
  | tmul a b => simp [rightSlice]

/-- Evaluating a right translate at `q` equals evaluating the original function at `q * p`. -/
theorem eval_rightTranslate {n : ℕ} (p q : Point k n) (a : CoordinateAlgebra k n) :
    eval (k := k) q (rightTranslate p a) = eval (k := k) (q * p) a := by
  rw [rightTranslate, AlgHom.comp_apply, eval_rightSlice]
  exact (eval_mul_point q p a).symm

/-- Every set lies in the zero locus of its vanishing ideal. -/
theorem subset_zeroLocus_vanishingIdeal {n : ℕ} (S : Set (Point k n)) :
    S ⊆ zeroLocus (vanishingIdeal S) := by
  intro p hp a ha
  exact ha p hp

/-- The identity lies in the common zero locus of a subgroup's vanishing ideal. -/
theorem zeroLocus_vanishingIdeal_one_mem {n : ℕ} (S : Subgroup (Point k n)) :
    (1 : Point k n) ∈ zeroLocus (vanishingIdeal (S : Set (Point k n))) :=
  subset_zeroLocus_vanishingIdeal (S : Set (Point k n)) S.one_mem

/-- The common zero locus of a subgroup's vanishing ideal is closed under inversion. -/
theorem zeroLocus_vanishingIdeal_inv_mem {n : ℕ} (S : Subgroup (Point k n))
    {p : Point k n} (hp : p ∈ zeroLocus (vanishingIdeal (S : Set (Point k n)))) :
    p⁻¹ ∈ zeroLocus (vanishingIdeal (S : Set (Point k n))) := by
  intro a ha
  rw [eval_inv_point]
  exact hp _ (fun s hs => by
    rw [← eval_inv_point]
    exact ha s⁻¹ (S.inv_mem hs))

/-- The common zero locus of a subgroup's vanishing ideal is closed under multiplication. -/
theorem zeroLocus_vanishingIdeal_mul_mem {n : ℕ} (S : Subgroup (Point k n))
    {p q : Point k n}
    (hp : p ∈ zeroLocus (vanishingIdeal (S : Set (Point k n))))
    (hq : q ∈ zeroLocus (vanishingIdeal (S : Set (Point k n)))) :
    p * q ∈ zeroLocus (vanishingIdeal (S : Set (Point k n))) := by
  intro a ha
  have htranslateS : ∀ s ∈ S, rightTranslate s a ∈ vanishingIdeal (S : Set (Point k n)) := by
    intro s hs x hx
    rw [eval_rightTranslate]
    exact ha (x * s) (S.mul_mem hx hs)
  have hps : ∀ s ∈ S, eval (k := k) (p * s) a = 0 := by
    intro s hs
    rw [← eval_rightTranslate]
    exact hp _ (htranslateS s hs)
  have htranslateP : rightTranslate p a ∈ vanishingIdeal (S : Set (Point k n)) := by
    intro s hs
    rw [eval_rightTranslate]
    simpa [mul_comm] using hps s hs
  have hzero := hq _ htranslateP
  rw [eval_rightTranslate] at hzero
  simpa [mul_comm] using hzero

/-- Zariski closure of a point subgroup, bundled as a subgroup. -/
def closureSubgroup {n : ℕ} (S : Subgroup (Point k n)) : Subgroup (Point k n) where
  carrier := zeroLocus (vanishingIdeal (S : Set (Point k n)))
  one_mem' := zeroLocus_vanishingIdeal_one_mem S
  mul_mem' := zeroLocus_vanishingIdeal_mul_mem S
  inv_mem' := zeroLocus_vanishingIdeal_inv_mem S

/-- A point-set vanishing ideal over a field is radical. -/
theorem vanishingIdeal_isRadical {n : ℕ} (S : Set (Point k n)) :
    (vanishingIdeal S).IsRadical := by
  intro a ha
  obtain ⟨m, hm⟩ := ha
  intro p hp
  have hzero : (eval (k := k) p a) ^ m = 0 := by
    rw [← map_pow]
    exact hm p hp
  exact IsReduced.eq_zero _ ⟨m, hzero⟩

/-- Tensoring injective linear maps over a field preserves injectivity. -/
theorem tensorProduct_map_injective_of_injective
    {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [AddCommGroup Q]
    [Module k M] [Module k N] [Module k P] [Module k Q]
    (f : M →ₗ[k] P) (g : N →ₗ[k] Q)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  obtain ⟨f', hf'⟩ :=
    LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr hf)
  obtain ⟨g', hg'⟩ :=
    LinearMap.exists_leftInverse_of_injective g (LinearMap.ker_eq_bot.mpr hg)
  have hcomp : TensorProduct.map f' g' ∘ₗ TensorProduct.map f g = LinearMap.id := by
    rw [← TensorProduct.map_comp, hf', hg', TensorProduct.map_id]
  exact Function.LeftInverse.injective (g := TensorProduct.map f' g') fun x => by
    have hx := DFunLike.congr_fun hcomp x
    simpa using hx

/-- A jointly separating family of field-valued algebra maps remains jointly separating on the
tensor square. -/
theorem tensor_eq_zero_of_jointly_separating
    {E ι : Type*} [CommRing E] [Algebra k E]
    (χ : ι → E →ₐ[k] k)
    (hsep : ∀ x : E, (∀ i, χ i x = 0) → x = 0)
    {z : E ⊗[k] E}
    (hz : ∀ i j,
      (Algebra.TensorProduct.lift (χ i) (χ j) (fun _ _ ↦ Commute.all _ _)) z = 0) :
    z = 0 := by
  classical
  let bs := Module.Basis.ofVectorSpace k E
  obtain ⟨t, a, rfl⟩ := exists_basis_tmul_repr bs z
  have key : ∀ i, ∀ r ∈ t, χ i (a r) = 0 := by
    intro i
    let Φ : E ⊗[k] E →ₐ[k] E :=
      Algebra.TensorProduct.lift ((Algebra.ofId k E).comp (χ i)) (AlgHom.id k E)
        (fun _ _ ↦ Commute.all _ _)
    have hzero : Φ (∑ r ∈ t, a r ⊗ₜ[k] bs r) = 0 := by
      apply hsep
      intro j
      have hΦ : ∀ u : E ⊗[k] E,
          χ j (Φ u) =
            (Algebra.TensorProduct.lift (χ i) (χ j) (fun _ _ ↦ Commute.all _ _)) u := by
        intro u
        induction u using TensorProduct.induction_on with
        | zero => simp [Φ]
        | add x y hx hy => simp [hx, hy]
        | tmul x y => simp [Φ]
      rw [hΦ]
      exact hz i j
    rw [map_sum] at hzero
    have hexp : ∑ r ∈ t, Φ (a r ⊗ₜ[k] bs r) =
        ∑ r ∈ t, χ i (a r) • bs r := by
      refine Finset.sum_congr rfl fun r _ => ?_
      simp [Φ, Algebra.smul_def]
    rw [hexp] at hzero
    exact fun r hr =>
      linearIndependent_iff'.mp bs.linearIndependent t (fun r => χ i (a r)) hzero r hr
  have hazero : ∀ r ∈ t, a r = 0 := fun r hr => hsep _ (fun i => key i r hr)
  rw [Finset.sum_congr rfl (fun r hr => by rw [hazero r hr, TensorProduct.zero_tmul])]
  simp

/-- Evaluation of the vanishing-ideal quotient at a point of the defining set. -/
def quotientEval {n : ℕ} (S : Set (Point k n)) (p : S) :
    (CoordinateAlgebra k n ⧸ vanishingIdeal S) →ₐ[k] k :=
  Ideal.Quotient.liftₐ (vanishingIdeal S) (eval (k := k) p.1)
    (fun _a ha => ha p.1 p.2)

@[simp] theorem quotientEval_mk {n : ℕ} (S : Set (Point k n)) (p : S)
    (a : CoordinateAlgebra k n) :
    quotientEval S p (Ideal.Quotient.mk (vanishingIdeal S) a) = eval (k := k) p.1 a := by
  rfl

/-- Defining-set evaluations jointly separate its vanishing-ideal quotient. -/
theorem quotientEval_jointly_separating {n : ℕ} (S : Set (Point k n))
    (x : CoordinateAlgebra k n ⧸ vanishingIdeal S)
    (hx : ∀ p, quotientEval S p x = 0) : x = 0 := by
  induction x using Quotient.inductionOn with
  | _ a =>
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      intro p hp
      change eval (k := k) p a = 0
      rw [← quotientEval_mk S ⟨p, hp⟩ a]
      exact hx ⟨p, hp⟩

/-- The vanishing ideal of an additive-exponential point subgroup is a Hopf ideal. -/
theorem vanishingIdeal_isHopfIdeal {n : ℕ}
    (S : Subgroup (Point k n)) :
    (vanishingIdeal (S : Set (Point k n))).IsHopfIdeal k := by
  let I : Ideal (CoordinateAlgebra k n) := vanishingIdeal (S : Set (Point k n))
  refine { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_, antipode_mem := ?_ }
  · intro a ha
    change a ∈ I at ha
    rw [← eval_one_point]
    exact ha 1 S.one_mem
  · intro a ha
    change a ∈ I at ha
    let e := Submodule.Quotient.restrictScalarsEquiv k I
    apply tensorProduct_map_injective_of_injective e.toLinearMap e.toLinearMap
      e.injective e.injective
    simp only [map_zero]
    apply tensor_eq_zero_of_jointly_separating
      (χ := quotientEval (S : Set (Point k n)))
      (fun x hx => quotientEval_jointly_separating (S : Set (Point k n)) x hx)
    intro p q
    have hmap : ∀ u : CoordinateAlgebra k n ⊗[k] CoordinateAlgebra k n,
        (Algebra.TensorProduct.lift
          (quotientEval (S : Set (Point k n)) p)
          (quotientEval (S : Set (Point k n)) q)
          (fun _ _ ↦ Commute.all _ _))
            (TensorProduct.map e.toLinearMap e.toLinearMap
              (TensorProduct.map (I.restrictScalars k).mkQ
                (I.restrictScalars k).mkQ u)) =
          (Algebra.TensorProduct.lift (eval (k := k) p.1) (eval (k := k) q.1)
            (fun _ _ ↦ Commute.all _ _)) u := by
      intro u
      induction u using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [hx, hy]
      | tmul x y =>
          simp only [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
          change quotientEval (S : Set (Point k n)) p
              (Ideal.Quotient.mk I x) *
            quotientEval (S : Set (Point k n)) q
              (Ideal.Quotient.mk I y) =
            eval (k := k) p.1 x * eval (k := k) q.1 y
          rw [quotientEval_mk, quotientEval_mk]
    rw [hmap]
    change convolutionEval (k := k) p.1 q.1 a = 0
    rw [← eval_mul_point]
    exact ha (p.1 * q.1) (S.mul_mem p.2 q.2)
  · intro a ha
    change a ∈ I at ha
    change HopfAlgebra.antipode k a ∈ I
    intro p hp
    rw [← eval_inv_point]
    exact ha p⁻¹ (S.inv_mem hp)

end
end AffineExponentialPointClosure
end GaloisForLFunctions.HTGeometry
