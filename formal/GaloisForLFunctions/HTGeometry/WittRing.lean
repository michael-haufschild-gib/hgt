import GaloisForLFunctions.HTGeometry.MilnorKTheory
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.RingQuot
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The Witt ring of a field

The Witt ring of a field is presented as the group ring of the square classes modulo the two Witt
relations: `⟨a⟩ + ⟨-a⟩ = 0`, and `⟨a⟩ + ⟨b⟩ = ⟨a+b⟩ + ⟨ab(a+b)⟩` whenever `a + b ≠ 0`.  The first
Witt relation — invariance under multiplication by squares — is already built into the group
quotient, so it costs nothing here.

The dimension modulo two is well defined on the presentation, because each relation has as many
generators on the left as on the right.  Its kernel is the fundamental ideal, whose powers are the
filtration used to compare the Witt ring with Milnor `K`-theory.

* `WittRing` : the Witt ring, as a quotient of the group ring of the square classes.
* `wittClass`, `wittClass_mul`, `wittClass_add_neg`, `wittClass_add` : the generators and relations.
* `wittDim` : the dimension modulo two.
* `fundamentalIdeal` : its kernel, and `fundamentalIdeal ^ n` its powers.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Witt

variable (F : Type*) [Field F]

/-- The subgroup of squares of the unit group. -/
def squaresSubgroup : Subgroup Fˣ :=
  MonoidHom.range (powMonoidHom 2 : Fˣ →* Fˣ)

instance : (squaresSubgroup F).Normal := Subgroup.normal_of_isMulCommutative _

/-- The square classes of a field. -/
abbrev SquareClass : Type _ := Fˣ ⧸ squaresSubgroup F

instance : CommGroup (SquareClass F) := QuotientGroup.Quotient.commGroup _

/-- The generator `⟨a⟩` in the group ring of the square classes. -/
def wittGen (a : Fˣ) : MonoidAlgebra ℤ (SquareClass F) :=
  MonoidAlgebra.single (QuotientGroup.mk a) 1

variable {F}

/-- The unit `a + b`, available whenever the sum is nonzero. -/
def addUnit {a b : Fˣ} (hab : (a : F) + (b : F) ≠ 0) : Fˣ :=
  Units.mk0 ((a : F) + (b : F)) hab

@[simp]
theorem addUnit_val {a b : Fˣ} (hab : (a : F) + (b : F) ≠ 0) :
    ((addUnit hab : Fˣ) : F) = (a : F) + (b : F) := rfl

variable (F)

/-- **The two Witt relations.** -/
inductive WittRel : MonoidAlgebra ℤ (SquareClass F) → MonoidAlgebra ℤ (SquareClass F) → Prop
  | neg (a : Fˣ) : WittRel (wittGen F a + wittGen F (-a)) 0
  | add (a b : Fˣ) (hab : (a : F) + (b : F) ≠ 0) :
      WittRel (wittGen F a + wittGen F b)
        (wittGen F (addUnit hab) + wittGen F (a * b * addUnit hab))

/-- **The Witt ring of a field.** -/
abbrev WittRing : Type _ := RingQuot (WittRel F)

/-- The quotient map onto the Witt ring. -/
def wittMk : MonoidAlgebra ℤ (SquareClass F) →ₐ[ℤ] WittRing F :=
  RingQuot.mkAlgHom ℤ (WittRel F)

/-- The class `⟨a⟩` of a unit in the Witt ring. -/
def wittClass (a : Fˣ) : WittRing F :=
  wittMk F (wittGen F a)

variable {F}

/-- **Multiplicativity of the classes**: `⟨a⟩⟨b⟩ = ⟨ab⟩`. -/
theorem wittClass_mul (a b : Fˣ) :
    wittClass F a * wittClass F b = wittClass F (a * b) := by
  rw [wittClass, wittClass, wittClass, ← map_mul]
  congr 1
  rw [wittGen, wittGen, wittGen, MonoidAlgebra.single_mul_single, mul_one]
  rfl

/-- **Invariance under squares**: `⟨ab²⟩ = ⟨a⟩`.  This is the first Witt relation, and it holds
already in the group ring because the square classes are a quotient by the squares. -/
theorem wittClass_mul_sq (a b : Fˣ) : wittClass F (a * b ^ 2) = wittClass F a := by
  have hq : (QuotientGroup.mk (a * b ^ 2) : SquareClass F) = QuotientGroup.mk a := by
    refine QuotientGroup.eq.2 ⟨b⁻¹, ?_⟩
    show b⁻¹ ^ 2 = (a * b ^ 2)⁻¹ * a
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, ← inv_pow]
  rw [wittClass, wittClass, wittGen, wittGen, hq]

/-- **The first Witt relation**: `⟨a⟩ + ⟨-a⟩ = 0`. -/
theorem wittClass_add_neg (a : Fˣ) : wittClass F a + wittClass F (-a) = 0 := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (WittRel.neg (F := F) a)
  rw [wittClass, wittClass, wittMk, ← map_add, h, map_zero]

/-- **The second Witt relation**: `⟨a⟩ + ⟨b⟩ = ⟨a+b⟩ + ⟨ab(a+b)⟩` whenever `a + b ≠ 0`. -/
theorem wittClass_add {a b : Fˣ} (hab : (a : F) + (b : F) ≠ 0) :
    wittClass F a + wittClass F b =
      wittClass F (addUnit hab) + wittClass F (a * b * addUnit hab) := by
  have h := RingQuot.mkAlgHom_rel (S := ℤ) (WittRel.add (F := F) a b hab)
  rw [wittClass, wittClass, wittClass, wittClass, wittMk, ← map_add, h, map_add]

variable (F)

/-- The constant monoid map used to define the dimension modulo two. -/
def wittDimHom : SquareClass F →* ZMod 2 where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := (one_mul 1).symm

/-- The dimension modulo two, before passing to the quotient. -/
def wittDimAux : MonoidAlgebra ℤ (SquareClass F) →ₐ[ℤ] ZMod 2 :=
  MonoidAlgebra.lift ℤ (ZMod 2) (SquareClass F) (wittDimHom F)

@[simp]
theorem wittDimAux_gen (a : Fˣ) : wittDimAux F (wittGen F a) = 1 := by
  rw [wittGen, wittDimAux, MonoidAlgebra.lift_single]
  show (1 : ℤ) • (1 : ZMod 2) = 1
  rw [one_smul]

theorem wittDimAux_rel :
    ∀ x y : MonoidAlgebra ℤ (SquareClass F), WittRel F x y →
      wittDimAux F x = wittDimAux F y := by
  rintro _ _ (⟨a⟩ | ⟨a, b, hab⟩)
  · rw [map_add, wittDimAux_gen, wittDimAux_gen, map_zero]
    decide
  · rw [map_add, map_add, wittDimAux_gen, wittDimAux_gen, wittDimAux_gen, wittDimAux_gen]

/-- **The dimension modulo two.**  Each Witt relation has as many generators on each side, so the
count descends to the Witt ring. -/
def wittDim : WittRing F →ₐ[ℤ] ZMod 2 :=
  RingQuot.liftAlgHom ℤ ⟨wittDimAux F, wittDimAux_rel F⟩

@[simp]
theorem wittDim_class (a : Fˣ) : wittDim F (wittClass F a) = 1 := by
  rw [wittDim, wittClass, wittMk, RingQuot.liftAlgHom_mkAlgHom_apply]
  exact wittDimAux_gen F a

/-- **The fundamental ideal** of the Witt ring: the even-dimensional classes. -/
def fundamentalIdeal : Ideal (WittRing F) :=
  RingHom.ker (wittDim F : WittRing F →+* ZMod 2)

theorem mem_fundamentalIdeal {x : WittRing F} :
    x ∈ fundamentalIdeal F ↔ wittDim F x = 0 := Iff.rfl

variable {F}

/-- **The difference of two classes is even-dimensional**, so it lies in the fundamental ideal.
These differences are the classical generators of the fundamental ideal. -/
theorem sub_wittClass_mem_fundamentalIdeal (a b : Fˣ) :
    wittClass F a - wittClass F b ∈ fundamentalIdeal F := by
  rw [mem_fundamentalIdeal, map_sub, wittDim_class, wittDim_class, sub_self]

variable (F)

/-- The one-fold Pfister form `⟨⟨a⟩⟩ = ⟨1⟩ - ⟨a⟩`. -/
def pfisterOne (a : Fˣ) : WittRing F := wittClass F 1 - wittClass F a

theorem pfisterOne_mem (a : Fˣ) : pfisterOne F a ∈ fundamentalIdeal F :=
  sub_wittClass_mem_fundamentalIdeal 1 a

theorem wittClass_neg_one : wittClass F (-1) = -wittClass F 1 :=
  eq_neg_of_add_eq_zero_right (wittClass_add_neg 1)

/-- Twice the unit class is a one-fold Pfister form, so it is even-dimensional. -/
theorem wittClass_one_add_one : wittClass F 1 + wittClass F 1 = pfisterOne F (-1) := by
  rw [pfisterOne, wittClass_neg_one, sub_neg_eq_add]

/-- **Every Witt class is an integer multiple of `⟨1⟩` modulo the one-fold Pfister forms.** -/
theorem exists_int_sub_mem_span (x : WittRing F) :
    ∃ n : ℤ, x - (n : WittRing F) * wittClass F 1 ∈
      Ideal.span (Set.range (pfisterOne F)) := by
  obtain ⟨w, rfl⟩ := RingQuot.mkAlgHom_surjective ℤ (WittRel F) x
  induction w using MonoidAlgebra.induction_on with
  | hM g =>
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨1, ?_⟩
    have hval : RingQuot.mkAlgHom ℤ (WittRel F) (MonoidAlgebra.of ℤ (SquareClass F)
        (QuotientGroup.mk a)) = wittClass F a := rfl
    rw [hval, show wittClass F a - ((1 : ℤ) : WittRing F) * wittClass F 1 =
      -pfisterOne F a by rw [pfisterOne]; push_cast; ring]
    exact neg_mem (Ideal.subset_span ⟨a, rfl⟩)
  | hadd f g hf hg =>
    obtain ⟨m, hm⟩ := hf
    obtain ⟨n, hn⟩ := hg
    refine ⟨m + n, ?_⟩
    have hsum : RingQuot.mkAlgHom ℤ (WittRel F) (f + g) -
        (((m + n : ℤ)) : WittRing F) * wittClass F 1 =
        (RingQuot.mkAlgHom ℤ (WittRel F) f - ((m : ℤ) : WittRing F) * wittClass F 1) +
          (RingQuot.mkAlgHom ℤ (WittRel F) g - ((n : ℤ) : WittRing F) * wittClass F 1) := by
      rw [map_add]
      push_cast
      ring
    rw [hsum]
    exact Ideal.add_mem _ hm hn
  | hsmul r f hf =>
    obtain ⟨n, hn⟩ := hf
    refine ⟨r * n, ?_⟩
    have hmap : RingQuot.mkAlgHom ℤ (WittRel F) (r • f) =
        ((r : ℤ) : WittRing F) * RingQuot.mkAlgHom ℤ (WittRel F) f := by
      rw [map_zsmul, zsmul_eq_mul]
    have hsm : RingQuot.mkAlgHom ℤ (WittRel F) (r • f) -
        (((r * n : ℤ)) : WittRing F) * wittClass F 1 =
        ((r : ℤ) : WittRing F) *
          (RingQuot.mkAlgHom ℤ (WittRel F) f - ((n : ℤ) : WittRing F) * wittClass F 1) := by
      rw [hmap]
      push_cast
      ring
    rw [hsm]
    exact Ideal.mul_mem_left _ _ hn

/-- **The fundamental ideal is generated by the one-fold Pfister forms.**  An even-dimensional
class is an even multiple of `⟨1⟩` modulo those forms, and twice `⟨1⟩` is itself one of them. -/
theorem fundamentalIdeal_eq_span :
    fundamentalIdeal F = Ideal.span (Set.range (pfisterOne F)) := by
  have hle : Ideal.span (Set.range (pfisterOne F)) ≤ fundamentalIdeal F := by
    rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact pfisterOne_mem F a
  refine le_antisymm (fun x hx => ?_) hle
  obtain ⟨n, hn⟩ := exists_int_sub_mem_span F x
  have hdim : ((n : ℤ) : ZMod 2) = 0 := by
    have h1 : wittDim F x = 0 := hx
    have h2 : wittDim F (x - ((n : ℤ) : WittRing F) * wittClass F 1) = 0 := hle hn
    rw [map_sub, h1, map_mul, wittDim_class, mul_one, zero_sub, neg_eq_zero,
      map_intCast] at h2
    exact h2
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).1 hdim
  have hmul : ((n : ℤ) : WittRing F) * wittClass F 1 ∈
      Ideal.span (Set.range (pfisterOne F)) := by
    have hrw : ((n : ℤ) : WittRing F) * wittClass F 1 =
        ((k : ℤ) : WittRing F) * (wittClass F 1 + wittClass F 1) := by
      rw [hk]
      push_cast
      ring
    rw [hrw, wittClass_one_add_one]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨-1, rfl⟩)
  have hx2 : x = (x - ((n : ℤ) : WittRing F) * wittClass F 1) +
      ((n : ℤ) : WittRing F) * wittClass F 1 := by ring
  rw [hx2]
  exact Ideal.add_mem _ hn hmul

/-- **The class of `1` is the unit of the Witt ring.** -/
theorem wittClass_one : wittClass F 1 = 1 := by
  have hgen : wittGen F 1 = (1 : MonoidAlgebra ℤ (SquareClass F)) := by
    rw [wittGen, MonoidAlgebra.one_def]
    congr 1
  rw [wittClass, hgen, map_one]

/-- **The one-fold Pfister forms are additive up to their product**:
`⟨⟨ab⟩⟩ = ⟨⟨a⟩⟩ + ⟨⟨b⟩⟩ - ⟨⟨a⟩⟩⟨⟨b⟩⟩`.  This exact identity is what makes `a ↦ ⟨⟨a⟩⟩` additive
modulo the square of the fundamental ideal. -/
theorem pfisterOne_mul (a b : Fˣ) :
    pfisterOne F (a * b) = pfisterOne F a + pfisterOne F b - pfisterOne F a * pfisterOne F b := by
  rw [pfisterOne, pfisterOne, pfisterOne, wittClass_one, ← wittClass_mul a b]
  ring

/-- The product of two one-fold Pfister forms lies in the square of the fundamental ideal. -/
theorem pfisterOne_mul_mem_sq (a b : Fˣ) :
    pfisterOne F a * pfisterOne F b ∈ fundamentalIdeal F ^ 2 := by
  rw [pow_two]
  exact Ideal.mul_mem_mul (pfisterOne_mem F a) (pfisterOne_mem F b)

/-- **The first Milnor map exists**: the one-fold Pfister form is additive modulo the square of the
fundamental ideal.  This is the degree-one comparison `Fˣ → I/I²` between Milnor `K`-theory and the
Pfister filtration of the Witt ring. -/
theorem pfisterOne_mul_sub_mem_sq (a b : Fˣ) :
    pfisterOne F (a * b) - (pfisterOne F a + pfisterOne F b) ∈ fundamentalIdeal F ^ 2 := by
  have h : pfisterOne F (a * b) - (pfisterOne F a + pfisterOne F b) =
      -(pfisterOne F a * pfisterOne F b) := by
    rw [pfisterOne_mul]
    ring
  rw [h]
  exact neg_mem (pfisterOne_mul_mem_sq F a b)

/-- The product of two one-fold Pfister forms, expanded. -/
theorem pfisterOne_mul_pfisterOne (a b : Fˣ) :
    pfisterOne F a * pfisterOne F b =
      1 - wittClass F a - wittClass F b + wittClass F (a * b) := by
  rw [pfisterOne, pfisterOne, wittClass_one, ← wittClass_mul a b]
  ring

/-- **The class of `-a` is minus the class of `a`.** -/
theorem wittClass_neg (a : Fˣ) : wittClass F (-a) = -wittClass F a := by
  have h : (-a : Fˣ) = (-1 : Fˣ) * a := by
    refine Units.ext ?_
    simp
  rw [h, ← wittClass_mul, wittClass_neg_one, wittClass_one]
  ring

/-- **The Steinberg relation in the Witt ring**: the two-fold Pfister form `⟨⟨a, 1-a⟩⟩` vanishes.
It is the second Witt relation applied to the pair `a`, `1 - a`, whose sum is `1`. -/
theorem pfisterOne_mul_oneSub {a : Fˣ} (ha : (a : F) ≠ 1) :
    pfisterOne F a * pfisterOne F (oneSubUnit ha) = 0 := by
  have hsum : (a : F) + ((oneSubUnit ha : Fˣ) : F) ≠ 0 := by
    rw [oneSubUnit_val]
    intro h
    have hone : (a : F) + (1 - (a : F)) = 1 := by ring
    rw [hone] at h
    exact one_ne_zero h
  have hone : addUnit hsum = 1 := by
    refine Units.ext ?_
    rw [addUnit_val, oneSubUnit_val, Units.val_one]
    ring
  have hrel := wittClass_add hsum
  rw [hone, mul_one, wittClass_one] at hrel
  rw [pfisterOne_mul_pfisterOne]
  rw [show (1 : WittRing F) - wittClass F a - wittClass F (oneSubUnit ha) +
      wittClass F (a * oneSubUnit ha) =
      1 - (wittClass F a + wittClass F (oneSubUnit ha)) +
        wittClass F (a * oneSubUnit ha) by ring, hrel]
  ring

/-- **`⟨⟨a, -a⟩⟩` vanishes**, the Witt-ring counterpart of `{a, -a} = 0` in Milnor `K`-theory. -/
theorem pfisterOne_mul_neg_self (a : Fˣ) :
    pfisterOne F a * pfisterOne F (-a) = 0 := by
  rw [pfisterOne_mul_pfisterOne, wittClass_neg]
  have hsq : (a * -a : Fˣ) = (-1 : Fˣ) * a ^ 2 := by
    refine Units.ext ?_
    simp
    ring
  rw [hsq, wittClass_mul_sq, wittClass_neg_one, wittClass_one]
  ring

end Witt

end

end GaloisForLFunctions.HTGeometry
