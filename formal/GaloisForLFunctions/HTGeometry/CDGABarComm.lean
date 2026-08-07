import GaloisForLFunctions.HTGeometry.CDGABarSquare

/-!
# Multiplications at distance commute

The head of a bar differential multiplies the first two factors; the tail of a tail applies a
degree-one map inside the third and later ones.  They act on disjoint factors, so they commute, and
the two Koszul signs differ by one: the head raises the degree of the first slot by one before the
outer sign is taken.  That is the second of the two cancellations in `d² = 0`, the one that is not
associativity.

* `HTGeometry.barMulTail` : multiply the first two factors and act on the rest.
* `HTGeometry.barMulTail_cancel` : the two orders cancel.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))
  {W W' : Type u} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']

/-- **Multiply the first two of three adjacent factors and act on the third.** -/
noncomputable def barMulTail {p q m : ℕ} (h : p + q + 1 = m) (g : W →ₗ[R] W') :
    TensorProduct R (barShiftFamily ε p) (TensorProduct R (barShiftFamily ε q) W)
      →ₗ[R] TensorProduct R (barShiftFamily ε m) W' :=
  (TensorProduct.map (augIdealShiftMulOfTensor ε h) g).comp
    ((TensorProduct.assoc R (barShiftFamily ε p) (barShiftFamily ε q) W).symm.toLinearMap)

@[simp] theorem barMulTail_tmul {p q m : ℕ} (h : p + q + 1 = m) (g : W →ₗ[R] W')
    (x : barShiftFamily ε p) (y : barShiftFamily ε q) (z : W) :
    barMulTail ε h g (x ⊗ₜ[R] (y ⊗ₜ[R] z))
      = augIdealShiftMulOf ε h x y ⊗ₜ[R] g z := rfl

/-- **The two orders cancel.**  Both compose to the same map; the signs are `(-1)^{p+q}` for acting
first and `(-1)^{p+q+1}` for multiplying first, because the multiplication raises the degree of the
slot the outer sign reads. -/
theorem barMulTail_cancel {p q m : ℕ} (h : p + q + 1 = m) (g : W →ₗ[R] W')
    (T : TensorProduct R (barShiftFamily ε p) (TensorProduct R (barShiftFamily ε q) W)) :
    ((-1 : R)) ^ (p + q) • barMulTail ε h g T
      + ((-1 : R)) ^ m • barMulTail ε h g T = 0 := by
  rw [← add_smul]
  have hm : ((-1 : R)) ^ (p + q) + ((-1 : R)) ^ m = 0 := by
    subst h
    rw [pow_succ]
    ring
  rw [hm, zero_smul]

/-- Acting on the third factor and then multiplying the first two is the combined map. -/
theorem barMulTail_first {p q m : ℕ} (h : p + q + 1 = m) (g : W →ₗ[R] W')
    (T : TensorProduct R (barShiftFamily ε p) (TensorProduct R (barShiftFamily ε q) W)) :
    (TensorProduct.map (augIdealShiftMulOfTensor ε h) (LinearMap.id (R := R) (M := W')))
        ((TensorProduct.assoc R (barShiftFamily ε p) (barShiftFamily ε q) W').symm
          (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε p))
            (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε q)) g) T))
      = barMulTail ε h g T := by
  induction T using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add T T' hT hT' =>
      simp only [map_add]
      rw [hT, hT']
  | tmul x V =>
      induction V using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add V V' hV hV' =>
          simp only [TensorProduct.tmul_add, map_add]
          rw [hV, hV']
      | tmul y z => rfl

/-- Multiplying the first two factors and then acting on the third is the combined map. -/
theorem barMulTail_second {p q m : ℕ} (h : p + q + 1 = m) (g : W →ₗ[R] W')
    (T : TensorProduct R (barShiftFamily ε p) (TensorProduct R (barShiftFamily ε q) W)) :
    (TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε m)) g)
        ((TensorProduct.map (augIdealShiftMulOfTensor ε h) (LinearMap.id (R := R) (M := W)))
          ((TensorProduct.assoc R (barShiftFamily ε p) (barShiftFamily ε q) W).symm T))
      = barMulTail ε h g T := by
  induction T using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add T T' hT hT' =>
      simp only [map_add]
      rw [hT, hT']
  | tmul x V =>
      induction V using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add V V' hV hV' =>
          simp only [TensorProduct.tmul_add, map_add]
          rw [hV, hV']
      | tmul y z => rfl

end GaloisForLFunctions.HTGeometry
