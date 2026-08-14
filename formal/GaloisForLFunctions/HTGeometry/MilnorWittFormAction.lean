import GaloisForLFunctions.HTGeometry.MilnorWittGradedIso
import GaloisForLFunctions.HTGeometry.MilnorWittGradedCollapse

/-!
# The action of the unit forms on graded Milnor--Witt `K`-theory

The degree-zero element `⟨a⟩ = 1 + η[a]` is a unit of the Milnor--Witt `K`-ring, and multiplication
by it is an automorphism of every graded piece.  On a word it prepends `a` with one extra power of
`η`, so it is left multiplication by the degree-zero word `η[a]` added to the identity.  Twisted
multiplicativity in the prepended slot says exactly that these automorphisms compose according to
multiplication of units, and `[1] = 0` says the unit acts trivially: the unit forms act on
`K_n^{MW}(F)` through the group of units of `F`.

* `mwFormAct` : **multiplication by `⟨a⟩` on `K_n^{MW}(F)`.**
* `mwFormAct_one`, `mwFormAct_mul` : it is an action of `Fˣ`.
* `mwFormActEquiv` : **each `⟨a⟩` acts by an automorphism.**
* `mwFormMulAction` : the unit group acts.
-/

namespace GaloisForLFunctions.HTGeometry

section FormAction

variable {F : Type*} [Field F]

/-- Transport of a word class along an equality of degrees. -/
theorem mwDegCongr_class' {n m : ℤ} (h : n = m) (w : MWWordDeg F n) (w' : MWWordDeg F m)
    (hw : w.val = w'.val) : mwDegCongr h (mwClassDeg F n w) = mwClassDeg F m w' := by
  subst h
  show mwClassDeg F n w = mwClassDeg F n w'
  exact congrArg (mwClassDeg F n) (Subtype.ext hw)

/-- The degree-zero word `η[a]`. -/
def mwFormWord (a : Fˣ) : MWWordDeg F 0 := ⟨(1, [a]), by simp⟩

/-- **Multiplication by the unit form `⟨a⟩ = 1 + η[a]`** on the degree-`n` part. -/
def mwFormAct (a : Fˣ) (n : ℤ) : MilnorWittKDeg F n →+ MilnorWittKDeg F n :=
  AddMonoidHom.id _ + (mwDegCongr (zero_add n)).comp (mwMulRight (mwFormWord a) n)

theorem mwFormAct_class (a : Fˣ) {n : ℤ} (k : ℕ) (l : List Fˣ)
    (p : ((l.length : ℤ)) - k = n) (q : (((a :: l).length : ℤ)) - (1 + k) = n) :
    mwFormAct a n (mwClassDeg F n ⟨(k, l), p⟩)
      = mwClassDeg F n ⟨(k, l), p⟩ + mwClassDeg F n ⟨(1 + k, a :: l), q⟩ := by
  show mwClassDeg F n ⟨(k, l), p⟩
      + mwDegCongr (zero_add n) (mwMulRight (mwFormWord a) n (mwClassDeg F n ⟨(k, l), p⟩)) = _
  rw [mwMulRight_class]
  refine congrArg (fun z => mwClassDeg F n ⟨(k, l), p⟩ + z) ?_
  exact mwDegCongr_class' (zero_add n) _ ⟨(1 + k, a :: l), q⟩ rfl

/-- **The unit form of `1` acts trivially**, because `[1] = 0`. -/
theorem mwFormAct_one (n : ℤ) : mwFormAct (1 : Fˣ) n = AddMonoidHom.id _ := by
  refine mwKDeg_hom_ext F fun w => ?_
  obtain ⟨⟨k, l⟩, p⟩ := w
  have q : ((((1 : Fˣ) :: l).length : ℤ)) - (1 + k) = n := by
    simp only [List.length_cons]
    push_cast at p ⊢
    omega
  rw [mwFormAct_class (1 : Fˣ) k l p q]
  have hzero : mwClassDeg F n ⟨(1 + k, (1 : Fˣ) :: l), q⟩ = 0 :=
    mwUnitSymbol_zero (1 + k) [] l q
  rw [hzero, add_zero]
  rfl

/-- **The unit forms compose according to multiplication of units**: this is twisted
multiplicativity in the prepended slot. -/
theorem mwFormAct_mul (a b : Fˣ) (n : ℤ) :
    (mwFormAct a n).comp (mwFormAct b n) = mwFormAct (a * b) n := by
  refine mwKDeg_hom_ext F fun w => ?_
  obtain ⟨⟨k, l⟩, p⟩ := w
  have qb : (((b :: l).length : ℤ)) - (1 + k) = n := by
    simp only [List.length_cons]; push_cast at p ⊢; omega
  have qa : (((a :: l).length : ℤ)) - (1 + k) = n := by
    simp only [List.length_cons]; push_cast at p ⊢; omega
  have qab : ((((a * b) :: l).length : ℤ)) - (1 + k) = n := by
    simp only [List.length_cons]; push_cast at p ⊢; omega
  have qab2 : (((a :: b :: l).length : ℤ)) - (1 + (1 + k)) = n := by
    simp only [List.length_cons]; push_cast at p ⊢; omega
  show mwFormAct a n (mwFormAct b n (mwClassDeg F n ⟨(k, l), p⟩)) = _
  rw [mwFormAct_class b k l p qb, map_add, mwFormAct_class a k l p qa,
    mwFormAct_class a (1 + k) (b :: l) qb qab2, mwFormAct_class (a * b) k l p qab]
  have htw : mwClassDeg F n ⟨(1 + k, (a * b) :: l), qab⟩
      = mwClassDeg F n ⟨(1 + k, a :: l), qa⟩ + mwClassDeg F n ⟨(1 + k, b :: l), qb⟩
        + mwClassDeg F n ⟨(1 + (1 + k), a :: b :: l), qab2⟩ :=
    mwClassDeg_twisted' (1 + k) a b [] l (Nat.add_comm 1 (1 + k)) rfl rfl rfl rfl qab qa qb qab2
  rw [htw]
  abel

/-- **Each unit form acts by an automorphism** of the degree-`n` part. -/
def mwFormActEquiv (a : Fˣ) (n : ℤ) : MilnorWittKDeg F n ≃+ MilnorWittKDeg F n where
  toFun := mwFormAct a n
  invFun := mwFormAct a⁻¹ n
  left_inv x := by
    have h := mwFormAct_mul (F := F) a⁻¹ a n
    rw [inv_mul_cancel, mwFormAct_one] at h
    exact congrArg (fun f : MilnorWittKDeg F n →+ MilnorWittKDeg F n => f x) h
  right_inv x := by
    have h := mwFormAct_mul (F := F) a a⁻¹ n
    rw [mul_inv_cancel, mwFormAct_one] at h
    exact congrArg (fun f : MilnorWittKDeg F n →+ MilnorWittKDeg F n => f x) h
  map_add' := map_add _

@[simp]
theorem mwFormActEquiv_apply (a : Fˣ) (n : ℤ) (x : MilnorWittKDeg F n) :
    mwFormActEquiv a n x = mwFormAct a n x := rfl

/-- **The unit forms act on `K_n^{MW}(F)` through `Fˣ`.** -/
@[reducible] def mwFormMulAction (n : ℤ) : MulAction Fˣ (MilnorWittKDeg F n) where
  smul a x := mwFormAct a n x
  one_smul x := by
    show mwFormAct (1 : Fˣ) n x = x
    rw [mwFormAct_one]
    rfl
  mul_smul a b x := by
    show mwFormAct (a * b) n x = mwFormAct a n (mwFormAct b n x)
    rw [← mwFormAct_mul a b n]
    rfl

end FormAction

end GaloisForLFunctions.HTGeometry
