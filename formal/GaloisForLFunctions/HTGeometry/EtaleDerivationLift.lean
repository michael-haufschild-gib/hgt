import GaloisForLFunctions.HTGeometry.TraceDualBasisSeparability

/-!
# Lifting a derivation along a finite free algebra with unit discriminant

Let `B` be a finite free `A`-algebra with a basis `e` whose discriminant is a unit, and let `A` be
an `R`-algebra with `B` an `R`-algebra over it.  Then every `R`-derivation of `A` lifts to a
**unique** `R`-derivation of `B`.

* Uniqueness is `TraceDualBasisSeparability.derivation_eq_zero` (the difference of two lifts is an
  `A`-derivation, hence zero), packaged here as `derivation_ext`.
* Existence is the classical Hochschild argument, carried out without tensor products.  Fix the
  basis and differentiate coordinates: `coeffDeriv b = ∑ᵢ d(e.repr b i) • eᵢ`.  Its failure to be a
  derivation is the symmetric `A`-bilinear defect
  `θ x y = coeffDeriv (xy) - x·coeffDeriv y - y·coeffDeriv x`, a Hochschild `2`-cocycle.  The
  separability identities `∑ᵢ eᵢ fᵢ = 1` and the swap `∑ᵢ β(x eᵢ, fᵢ) = ∑ᵢ β(eᵢ, x fᵢ)` make it a
  coboundary: `φ b = ∑ᵢ eᵢ · θ(fᵢ, b)` satisfies `x φ y + y φ x - φ(xy) = θ x y`, so
  `coeffDeriv + φ` is a derivation.

This is the derivation used by the multivariable simple connectedness of affine space: for a finite
étale algebra over `R[w]` the lift of `d/dw` is locally nilpotent, and the slice theorem then makes
the algebra constant in `w`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

section Swap

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B]
  {n : ℕ} (e : Module.Basis (Fin n) A B) (hd : IsUnit (Algebra.discr A e))

include hd in
/-- The separability identity, in the form of a swap between the two arguments of an
`A`-bilinear map. -/
theorem sum_swap_traceDual (β : B → B → B)
    (h1 : ∀ (a : A) (u v : B), β (a • u) v = a • β u v)
    (h3 : ∀ (a : A) (u v : B), β u (a • v) = a • β u v)
    (hadd1 : ∀ (u u' v : B), β (u + u') v = β u v + β u' v)
    (hadd2 : ∀ (u v v' : B), β u (v + v') = β u v + β u v')
    (hz1 : ∀ v : B, β 0 v = 0) (hz2 : ∀ u : B, β u 0 = 0)
    (b : B) :
    ∑ i, β (b * e i) (traceDual e i) = ∑ i, β (e i) (b * traceDual e i) := by
  classical
  have hsum1 : ∀ (c : Fin n → A) (v : B),
      β (∑ j, c j • e j) v = ∑ j, c j • β (e j) v := by
    intro c v
    induction (Finset.univ : Finset (Fin n)) using Finset.induction with
    | empty => simp [hz1]
    | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, hadd1, h1, ih]
  have hsum2 : ∀ (c : Fin n → A) (u : B),
      β u (∑ j, c j • traceDual e j) = ∑ j, c j • β u (traceDual e j) := by
    intro c u
    induction (Finset.univ : Finset (Fin n)) using Finset.induction with
    | empty => simp [hz2]
    | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, hadd2, h3, ih]
  have hL : ∀ i : Fin n, β (b * e i) (traceDual e i)
      = ∑ j, (e.repr (b * e i) j) • β (e j) (traceDual e i) := by
    intro i
    set c : Fin n → A := fun j => e.repr (b * e i) j with hc
    have hbe : b * e i = ∑ j, c j • e j := (e.sum_repr (b * e i)).symm
    rw [hbe, hsum1]
    exact Finset.sum_congr rfl (fun j _ => by rw [repr_sum_apply])
  have hR : ∀ i : Fin n, β (e i) (b * traceDual e i)
      = ∑ j, (e.repr (b * e j) i) • β (e i) (traceDual e j) := by
    intro i
    rw [mul_traceDual e hd b i, hsum2]
  rw [Finset.sum_congr rfl (fun i _ => hL i), Finset.sum_congr rfl (fun i _ => hR i),
    Finset.sum_comm]

end Swap


namespace Lift

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Module.Free A B] [Module.Finite A B]
  {n : ℕ} (e : Module.Basis (Fin n) A B) (hd : IsUnit (Algebra.discr A e))
  (d : Derivation R A A)

/-- Differentiate the coordinates of an element in a fixed basis. -/
noncomputable def coeffDeriv (b : B) : B := ∑ i, (d (e.repr b i)) • e i

theorem coeffDeriv_add (x y : B) :
    coeffDeriv e d (x + y) = coeffDeriv e d x + coeffDeriv e d y := by
  simp only [coeffDeriv, map_add, Finsupp.add_apply, add_smul]
  exact Finset.sum_add_distrib

theorem coeffDeriv_zero : coeffDeriv e d (0 : B) = 0 := by
  simp [coeffDeriv]

theorem coeffDeriv_smul (a : A) (x : B) :
    coeffDeriv e d (a • x) = (d a) • x + a • coeffDeriv e d x := by
  classical
  have hrepr : ∀ i, e.repr (a • x) i = a * e.repr x i := by
    intro i
    rw [map_smul]
    rfl
  simp only [coeffDeriv, hrepr]
  have hterm : ∀ i : Fin n, d (a * e.repr x i) • e i
      = (d a) • (e.repr x i • e i) + a • ((d (e.repr x i)) • e i) := by
    intro i
    rw [d.leibniz, add_smul, smul_smul, smul_smul, smul_eq_mul, smul_eq_mul,
      mul_comm (e.repr x i), add_comm]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.smul_sum,
    ← Finset.smul_sum, e.sum_repr x]

theorem coeffDeriv_smul_base (r : R) (x : B) :
    coeffDeriv e d (r • x) = r • coeffDeriv e d x := by
  have hr : (r • x) = (algebraMap R A r) • x := by
    rw [algebraMap_smul]
  rw [hr, coeffDeriv_smul, d.map_algebraMap, zero_smul, zero_add, algebraMap_smul]

/-- The Hochschild defect of `coeffDeriv`. -/
noncomputable def theta (x y : B) : B :=
  coeffDeriv e d (x * y) - x * coeffDeriv e d y - y * coeffDeriv e d x

theorem theta_symm (x y : B) : theta e d x y = theta e d y x := by
  simp only [theta, mul_comm x y]
  ring

theorem theta_smul_left (a : A) (x y : B) : theta e d (a • x) y = a • theta e d x y := by
  simp only [theta]
  rw [smul_mul_assoc, coeffDeriv_smul, coeffDeriv_smul, smul_mul_assoc, mul_add,
    mul_smul_comm, mul_smul_comm, smul_sub, smul_sub, mul_comm y x]
  abel

theorem theta_add_left (x x' y : B) :
    theta e d (x + x') y = theta e d x y + theta e d x' y := by
  simp only [theta, add_mul, coeffDeriv_add]
  ring

theorem theta_zero_left (y : B) : theta e d 0 y = 0 := by
  simp [theta, coeffDeriv_zero]

theorem theta_cocycle (x y z : B) :
    x * theta e d y z - theta e d (x * y) z + theta e d x (y * z) - z * theta e d x y = 0 := by
  simp only [theta]
  rw [mul_assoc x y z]
  ring

theorem theta_smul_right (a : A) (x y : B) : theta e d x (a • y) = a • theta e d x y := by
  rw [theta_symm, theta_smul_left, theta_symm]

theorem theta_add_right (x y y' : B) :
    theta e d x (y + y') = theta e d x y + theta e d x y' := by
  rw [theta_symm, theta_add_left, theta_symm e d y x, theta_symm e d y' x]

theorem theta_zero_right (x : B) : theta e d x 0 = 0 := by
  rw [theta_symm, theta_zero_left]

/-- The correction term making `coeffDeriv` a derivation. -/
noncomputable def phi (b : B) : B := ∑ i, e i * theta e d (traceDual e i) b

theorem phi_add (x y : B) : phi e d (x + y) = phi e d x + phi e d y := by
  simp only [phi, theta_add_right, mul_add]
  exact Finset.sum_add_distrib

theorem phi_smul (a : A) (x : B) : phi e d (a • x) = a • phi e d x := by
  simp only [phi, theta_smul_right, mul_smul_comm]
  exact (Finset.smul_sum).symm

include hd in
theorem phi_key (x y : B) :
    x * phi e d y + y * phi e d x - phi e d (x * y) = theta e d x y := by
  classical
  have hterm : ∀ i : Fin n,
      x * (e i * theta e d (traceDual e i) y) + y * (e i * theta e d (traceDual e i) x)
        - e i * theta e d (traceDual e i) (x * y)
      = ((x * e i) * theta e d (traceDual e i) y - e i * theta e d (x * traceDual e i) y)
        + (e i * traceDual e i) * theta e d x y := by
    intro i
    have hc := theta_cocycle e d (traceDual e i) x y
    have hsub : theta e d (traceDual e i) (x * y)
        = theta e d (traceDual e i * x) y + y * theta e d (traceDual e i) x
          - traceDual e i * theta e d x y := by linear_combination hc
    rw [hsub, mul_comm (traceDual e i) x]
    ring
  have hswap : ∑ i, (x * e i) * theta e d (traceDual e i) y
      = ∑ i, e i * theta e d (x * traceDual e i) y := by
    refine sum_swap_traceDual e hd (fun u v => u * theta e d v y) ?_ ?_ ?_ ?_ ?_ ?_ x
    · intro a u v; rw [smul_mul_assoc]
    · intro a u v; rw [theta_smul_left, mul_smul_comm]
    · intro u u' v; rw [add_mul]
    · intro u v v'; rw [theta_add_left, mul_add]
    · intro v; rw [zero_mul]
    · intro u; rw [theta_zero_left, mul_zero]
  simp only [phi, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib, hswap, sub_self, zero_add, ← Finset.sum_mul,
    sum_mul_traceDual e hd, one_mul]

/-- The lifted derivation, as a function. -/
noncomputable def liftFun (b : B) : B := coeffDeriv e d b + phi e d b

include hd in
theorem liftFun_leibniz (x y : B) :
    liftFun e d (x * y) = x * liftFun e d y + y * liftFun e d x := by
  have hk := phi_key e hd d x y
  simp only [liftFun, theta] at hk ⊢
  linear_combination -hk

include hd in
theorem liftFun_one : liftFun e d (1 : B) = 0 := by
  have h := liftFun_leibniz e hd d 1 1
  rw [one_mul, one_mul] at h
  have h2 : liftFun e d (1 : B) + 0 = liftFun e d (1 : B) + liftFun e d (1 : B) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

theorem liftFun_add (x y : B) :
    liftFun e d (x + y) = liftFun e d x + liftFun e d y := by
  simp only [liftFun, coeffDeriv_add, phi_add]
  ring

theorem liftFun_smul_base (r : R) (x : B) :
    liftFun e d (r • x) = r • liftFun e d x := by
  simp only [liftFun, smul_add]
  rw [coeffDeriv_smul_base]
  congr 1
  have hr : (r • x : B) = (algebraMap R A r) • x := (algebraMap_smul A r x).symm
  rw [hr, phi_smul, algebraMap_smul]

include hd in
/-- **A derivation of the base lifts to a finite free algebra with unit discriminant.** -/
noncomputable def liftDerivation : Derivation R B B where
  toFun := liftFun e d
  map_add' := liftFun_add e d
  map_smul' := fun r x => liftFun_smul_base e d r x
  map_one_eq_zero' := liftFun_one e hd d
  leibniz' := fun x y => by
    rw [smul_eq_mul, smul_eq_mul]
    exact liftFun_leibniz e hd d x y

include hd in
theorem liftDerivation_apply (b : B) : liftDerivation e hd d b = liftFun e d b := rfl

include hd in
theorem liftDerivation_algebraMap (a : A) :
    liftDerivation e hd d (algebraMap A B a) = algebraMap A B (d a) := by
  have h1 : (algebraMap A B a) = a • (1 : B) := Algebra.algebraMap_eq_smul_one a
  rw [liftDerivation_apply, h1]
  simp only [liftFun]
  rw [coeffDeriv_smul, phi_smul, add_assoc, ← smul_add]
  have h2 : coeffDeriv e d (1 : B) + phi e d (1 : B) = 0 := liftFun_one e hd d
  rw [h2, smul_zero, add_zero, ← Algebra.algebraMap_eq_smul_one]

include hd in
/-- **Uniqueness of the lift.**  Two `R`-derivations of `B` agreeing on the image of `A` are
equal. -/
theorem derivation_ext (D₁ D₂ : Derivation R B B)
    (h : ∀ a : A, D₁ (algebraMap A B a) = D₂ (algebraMap A B a)) : D₁ = D₂ := by
  set D : Derivation R B B := D₁ - D₂ with hD
  have hzero : ∀ a : A, D (algebraMap A B a) = 0 := by
    intro a
    rw [hD]
    show D₁ (algebraMap A B a) - D₂ (algebraMap A B a) = 0
    rw [h a, sub_self]
  have hDA : ∀ (a : A) (b : B), D (a • b) = a • D b := by
    intro a b
    have hsm : (a • b : B) = algebraMap A B a * b := Algebra.smul_def a b
    rw [hsm, D.leibniz, hzero a, smul_zero, add_zero, smul_eq_mul, ← Algebra.smul_def]
  let D' : Derivation A B B :=
    { toFun := fun b => D b
      map_add' := fun x y => map_add D x y
      map_smul' := fun a b => hDA a b
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := fun x y => D.leibniz x y }
  have hD'0 : D' = 0 := derivation_eq_zero e hd D'
  have hall : ∀ b : B, D b = 0 := by
    intro b
    have := congrArg (fun (F : Derivation A B B) => F b) hD'0
    simpa [D'] using this
  ext b
  have := hall b
  rw [hD] at this
  show D₁ b = D₂ b
  have h2 : D₁ b - D₂ b = 0 := this
  linear_combination h2

end Lift

end GaloisForLFunctions.HTGeometry
