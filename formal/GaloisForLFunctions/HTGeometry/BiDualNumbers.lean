import GaloisForLFunctions.HTGeometry.DifferentialEvalTransfer

/-!
# Two independent infinitesimals

`BiDual C` is `C[ε, η]/(ε², η²)`, written out as four coefficients `1, ε, η, εη`.  It is built
directly rather than as `DualNumber (DualNumber C)` because the iterated `TrivSqZeroExt` carries an
instance diamond — its `CommSemiring` is reached both through `TrivSqZeroExt.commSemiring` and
through `CommRing.toCommSemiring`, and the derivation of the `Differential` instance cannot then be
applied to its elements at all.

Two independent infinitesimals are what makes the commutator visible:
`(1 + ηX)(1 + εY)(1 − ηX) = 1 + εY + εη(XY − YX)`, since `ε² = η² = 0` while `εη ≠ 0`.

* `BiDual`, its `CommRing`, `Algebra C`, `Differential` and `DifferentialAlgebra C` instances;
* `epsHom`, `etaHom` — the two layer inclusions of the dual numbers, as ring maps;
* `deriv_epsHom`, `deriv_etaHom`, `epsHom_algebraMap`, `etaHom_algebraMap`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential
open GaloisForLFunctions

/-- `C[ε, η]/(ε², η²)`, by its four coefficients. -/
@[ext]
structure BiDual (C : Type*) where
  /-- the coefficient of `1` -/
  re : C
  /-- the coefficient of `ε` -/
  ep : C
  /-- the coefficient of `η` -/
  et : C
  /-- the coefficient of `εη` -/
  mx : C

namespace BiDual

variable {C : Type*} [CommRing C]

instance : Add (BiDual C) :=
  ⟨fun x y => ⟨x.re + y.re, x.ep + y.ep, x.et + y.et, x.mx + y.mx⟩⟩

instance : Zero (BiDual C) := ⟨⟨0, 0, 0, 0⟩⟩

instance : Neg (BiDual C) := ⟨fun x => ⟨-x.re, -x.ep, -x.et, -x.mx⟩⟩

instance : One (BiDual C) := ⟨⟨1, 0, 0, 0⟩⟩

instance : Mul (BiDual C) :=
  ⟨fun x y => ⟨x.re * y.re, x.re * y.ep + x.ep * y.re, x.re * y.et + x.et * y.re,
    x.re * y.mx + x.mx * y.re + x.ep * y.et + x.et * y.ep⟩⟩

@[simp] theorem add_re (x y : BiDual C) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_ep (x y : BiDual C) : (x + y).ep = x.ep + y.ep := rfl
@[simp] theorem add_et (x y : BiDual C) : (x + y).et = x.et + y.et := rfl
@[simp] theorem add_mx (x y : BiDual C) : (x + y).mx = x.mx + y.mx := rfl
@[simp] theorem zero_re : (0 : BiDual C).re = 0 := rfl
@[simp] theorem zero_ep : (0 : BiDual C).ep = 0 := rfl
@[simp] theorem zero_et : (0 : BiDual C).et = 0 := rfl
@[simp] theorem zero_mx : (0 : BiDual C).mx = 0 := rfl
@[simp] theorem neg_re (x : BiDual C) : (-x).re = -x.re := rfl
@[simp] theorem neg_ep (x : BiDual C) : (-x).ep = -x.ep := rfl
@[simp] theorem neg_et (x : BiDual C) : (-x).et = -x.et := rfl
@[simp] theorem neg_mx (x : BiDual C) : (-x).mx = -x.mx := rfl
@[simp] theorem one_re : (1 : BiDual C).re = 1 := rfl
@[simp] theorem one_ep : (1 : BiDual C).ep = 0 := rfl
@[simp] theorem one_et : (1 : BiDual C).et = 0 := rfl
@[simp] theorem one_mx : (1 : BiDual C).mx = 0 := rfl
@[simp] theorem mul_re (x y : BiDual C) : (x * y).re = x.re * y.re := rfl
@[simp] theorem mul_ep (x y : BiDual C) : (x * y).ep = x.re * y.ep + x.ep * y.re := rfl
@[simp] theorem mul_et (x y : BiDual C) : (x * y).et = x.re * y.et + x.et * y.re := rfl
@[simp] theorem mul_mx (x y : BiDual C) :
    (x * y).mx = x.re * y.mx + x.mx * y.re + x.ep * y.et + x.et * y.ep := rfl

instance : CommRing (BiDual C) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  mul := (· * ·)
  one := 1
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  mul_comm := by intros; ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- The base inclusion `a ↦ a`. -/
def coeff (a : C) : BiDual C := ⟨a, 0, 0, 0⟩

@[simp] theorem coeff_re (a : C) : (coeff a).re = a := rfl
@[simp] theorem coeff_ep (a : C) : (coeff a).ep = 0 := rfl
@[simp] theorem coeff_et (a : C) : (coeff a).et = 0 := rfl
@[simp] theorem coeff_mx (a : C) : (coeff a).mx = 0 := rfl

/-- The base inclusion, as a ring map. -/
def coeffHom : C →+* BiDual C where
  toFun := coeff
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

instance : Algebra C (BiDual C) := (coeffHom : C →+* BiDual C).toAlgebra

theorem algebraMap_eq (a : C) : algebraMap C (BiDual C) a = coeff a := rfl

variable [Differential C]

/-- The componentwise derivation. -/
def derivFun (x : BiDual C) : BiDual C := ⟨x.re′, x.ep′, x.et′, x.mx′⟩

@[simp] theorem derivFun_re (x : BiDual C) : (derivFun x).re = x.re′ := rfl
@[simp] theorem derivFun_ep (x : BiDual C) : (derivFun x).ep = x.ep′ := rfl
@[simp] theorem derivFun_et (x : BiDual C) : (derivFun x).et = x.et′ := rfl
@[simp] theorem derivFun_mx (x : BiDual C) : (derivFun x).mx = x.mx′ := rfl

/-- The componentwise derivation, as a derivation. -/
def derivMap : Derivation ℤ (BiDual C) (BiDual C) where
  toLinearMap := (AddMonoidHom.mk' derivFun (fun x y => by ext <;> simp)).toIntLinearMap
  map_one_eq_zero' := by ext <;> simp
  leibniz' x y := by
    ext <;> simp [Derivation.leibniz, smul_eq_mul] <;> ring

instance : Differential (BiDual C) := ⟨derivMap⟩

@[simp] theorem deriv_re (x : BiDual C) : (x′).re = x.re′ := rfl
@[simp] theorem deriv_ep (x : BiDual C) : (x′).ep = x.ep′ := rfl
@[simp] theorem deriv_et (x : BiDual C) : (x′).et = x.et′ := rfl
@[simp] theorem deriv_mx (x : BiDual C) : (x′).mx = x.mx′ := rfl

instance : DifferentialAlgebra C (BiDual C) := by
  refine ⟨fun a => ?_⟩
  rw [algebraMap_eq, algebraMap_eq]
  ext <;> simp [coeff]

/-! ### The two layer inclusions -/

/-- `a + ηb ↦ a + εb`. -/
def epsFun (x : DualNumber C) : BiDual C := ⟨x.fst, x.snd, 0, 0⟩

/-- `a + ηb ↦ a + ηb`. -/
def etaFun (x : DualNumber C) : BiDual C := ⟨x.fst, 0, x.snd, 0⟩

/-- `a + ηb ↦ a + εb`, as a ring map. -/
def epsHom : DualNumber C →+* BiDual C where
  toFun := epsFun
  map_one' := by ext <;> simp [epsFun]
  map_mul' x y := by
    ext <;> simp [epsFun, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop]
  map_zero' := by ext <;> simp [epsFun]
  map_add' x y := by ext <;> simp [epsFun, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]

/-- `a + ηb ↦ a + ηb`, as a ring map. -/
def etaHom : DualNumber C →+* BiDual C where
  toFun := etaFun
  map_one' := by ext <;> simp [etaFun]
  map_mul' x y := by
    ext <;> simp [etaFun, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop]
  map_zero' := by ext <;> simp [etaFun]
  map_add' x y := by ext <;> simp [etaFun, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]

omit [Differential C] in
@[simp] theorem epsHom_apply (x : DualNumber C) : epsHom x = epsFun x := rfl

omit [Differential C] in
@[simp] theorem etaHom_apply (x : DualNumber C) : etaHom x = etaFun x := rfl

theorem deriv_epsHom (x : DualNumber C) :
    epsFun (x′) = (epsFun x)′ := by
  ext <;> simp [epsFun]

theorem deriv_etaHom (x : DualNumber C) :
    etaFun (x′) = (etaFun x)′ := by
  ext <;> simp [etaFun]

omit [Differential C] in
theorem epsHom_algebraMap (a : C) :
    epsFun (algebraMap C (DualNumber C) a) = algebraMap C (BiDual C) a := by
  rw [TrivSqZeroExt.algebraMap_eq_inl, algebraMap_eq]
  ext <;> simp [epsFun, coeff]

omit [Differential C] in
theorem etaHom_algebraMap (a : C) :
    etaFun (algebraMap C (DualNumber C) a) = algebraMap C (BiDual C) a := by
  rw [TrivSqZeroExt.algebraMap_eq_inl, algebraMap_eq]
  ext <;> simp [etaFun, coeff]

end BiDual

end GaloisForLFunctions.HTGeometry
