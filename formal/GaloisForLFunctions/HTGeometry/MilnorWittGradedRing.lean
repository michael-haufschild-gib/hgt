import GaloisForLFunctions.HTGeometry.MilnorWittFormAction
import GaloisForLFunctions.HTGeometry.MilnorWittGradedSquare

/-!
# The graded ring structure of Milnor--Witt `K`-theory

Concatenation of words is associative and the empty word is a two-sided unit, so the graded product
`mwMul` makes `⨁_n K_n^{MW}(F)` a graded ring — up to the transport along the associativity and
unit laws of the grading, which is what `mwDegCongr` provides.  Multiplication by the unit form
`⟨a⟩` is then literally multiplication by `1 + η[a]`.

* `mwOne` : the unit.
* `mwMul_assoc` : **the graded product is associative.**
* `mwOne_mul`, `mwMul_one` : **the empty word is a two-sided unit.**
* `mwFormAct_eq` : **the unit-form action is multiplication by `1 + η[a]`.**
-/

namespace GaloisForLFunctions.HTGeometry

section GradedRing

variable {F : Type*} [Field F]

/-- The unit of Milnor--Witt `K`-theory: the class of the empty word. -/
def mwOne : MilnorWittKDeg F 0 := mwClassDeg F 0 ⟨(0, []), by simp⟩

/-- Concatenation of words is associative. -/
theorem mwWordMul_assoc {m n p : ℤ} (u : MWWordDeg F m) (v : MWWordDeg F n) (w : MWWordDeg F p) :
    (mwWordMul (mwWordMul u v) w).val = (mwWordMul u (mwWordMul v w)).val := by
  show ((u.val.1 + v.val.1 + w.val.1, (u.val.2 ++ v.val.2) ++ w.val.2) : ℕ × List Fˣ)
      = (u.val.1 + (v.val.1 + w.val.1), u.val.2 ++ (v.val.2 ++ w.val.2))
  rw [Nat.add_assoc, List.append_assoc]

theorem mwMul_assoc_word {m n p : ℤ} (u : MWWordDeg F m) (v : MWWordDeg F n) (w : MWWordDeg F p) :
    mwDegCongr (add_assoc m n p)
        (mwMul (m + n) p (mwMul m n (mwClassDeg F m u) (mwClassDeg F n v)) (mwClassDeg F p w))
      = mwMul m (n + p) (mwClassDeg F m u) (mwMul n p (mwClassDeg F n v) (mwClassDeg F p w)) := by
  rw [mwMul_class, mwMul_class, mwMul_class, mwMul_class]
  exact mwDegCongr_class' _ _ _ (mwWordMul_assoc u v w)

theorem mwMul_assoc_left {m n p : ℤ} (v : MWWordDeg F n) (w : MWWordDeg F p)
    (x : MilnorWittKDeg F m) :
    mwDegCongr (add_assoc m n p)
        (mwMul (m + n) p (mwMul m n x (mwClassDeg F n v)) (mwClassDeg F p w))
      = mwMul m (n + p) x (mwMul n p (mwClassDeg F n v) (mwClassDeg F p w)) := by
  have hext : ((mwDegCongr (add_assoc m n p)).comp
        ((mwMul (m + n) p).flip (mwClassDeg F p w))).comp ((mwMul m n).flip (mwClassDeg F n v))
      = (mwMul m (n + p)).flip (mwMul n p (mwClassDeg F n v) (mwClassDeg F p w)) :=
    mwKDeg_hom_ext F fun u => mwMul_assoc_word u v w
  exact DFunLike.congr_fun hext x

theorem mwMul_assoc_mid {m n p : ℤ} (w : MWWordDeg F p) (x : MilnorWittKDeg F m)
    (y : MilnorWittKDeg F n) :
    mwDegCongr (add_assoc m n p) (mwMul (m + n) p (mwMul m n x y) (mwClassDeg F p w))
      = mwMul m (n + p) x (mwMul n p y (mwClassDeg F p w)) := by
  have hext : ((mwDegCongr (add_assoc m n p)).comp
        ((mwMul (m + n) p).flip (mwClassDeg F p w))).comp (mwMul m n x)
      = (mwMul m (n + p) x).comp ((mwMul n p).flip (mwClassDeg F p w)) :=
    mwKDeg_hom_ext F fun v => mwMul_assoc_left v w x
  exact DFunLike.congr_fun hext y

/-- **The graded product of Milnor--Witt `K`-theory is associative.** -/
theorem mwMul_assoc {m n p : ℤ} (x : MilnorWittKDeg F m) (y : MilnorWittKDeg F n)
    (z : MilnorWittKDeg F p) :
    mwDegCongr (add_assoc m n p) (mwMul (m + n) p (mwMul m n x y) z)
      = mwMul m (n + p) x (mwMul n p y z) := by
  have hext : (mwDegCongr (add_assoc m n p)).comp (mwMul (m + n) p (mwMul m n x y))
      = (mwMul m (n + p) x).comp (mwMul n p y) :=
    mwKDeg_hom_ext F fun w => mwMul_assoc_mid w x y
  exact DFunLike.congr_fun hext z

/-- **The empty word is a left unit.** -/
theorem mwOne_mul {n : ℤ} (x : MilnorWittKDeg F n) :
    mwDegCongr (zero_add n) (mwMul 0 n (mwOne : MilnorWittKDeg F 0) x) = x := by
  have hext : (mwDegCongr (zero_add n)).comp (mwMul 0 n (mwOne : MilnorWittKDeg F 0))
      = AddMonoidHom.id _ := by
    refine mwKDeg_hom_ext F fun w => ?_
    show mwDegCongr (zero_add n)
        (mwMul 0 n (mwClassDeg F 0 (⟨(0, []), by simp⟩ : MWWordDeg F 0)) (mwClassDeg F n w))
      = mwClassDeg F n w
    rw [mwMul_class]
    refine mwDegCongr_class' _ _ w ?_
    show ((0 + w.val.1, [] ++ w.val.2) : ℕ × List Fˣ) = w.val
    rw [Nat.zero_add, List.nil_append]
  exact DFunLike.congr_fun hext x

/-- **The empty word is a right unit.** -/
theorem mwMul_one {n : ℤ} (x : MilnorWittKDeg F n) :
    mwDegCongr (add_zero n) (mwMul n 0 x (mwOne : MilnorWittKDeg F 0)) = x := by
  have hext : (mwDegCongr (add_zero n)).comp ((mwMul n 0).flip (mwOne : MilnorWittKDeg F 0))
      = AddMonoidHom.id _ := by
    refine mwKDeg_hom_ext F fun w => ?_
    show mwDegCongr (add_zero n)
        (mwMul n 0 (mwClassDeg F n w) (mwClassDeg F 0 (⟨(0, []), by simp⟩ : MWWordDeg F 0)))
      = mwClassDeg F n w
    rw [mwMul_class]
    refine mwDegCongr_class' _ _ w ?_
    show ((w.val.1 + 0, w.val.2 ++ []) : ℕ × List Fˣ) = w.val
    rw [Nat.add_zero, List.append_nil]
  exact DFunLike.congr_fun hext x

/-- **The unit-form action is multiplication by `⟨a⟩ = 1 + η[a]`.** -/
theorem mwFormAct_eq {n : ℤ} (a : Fˣ) (x : MilnorWittKDeg F n) :
    mwFormAct a n x = x + mwDegCongr (zero_add n) (mwMul 0 n (mwEtaSymbol a) x) := by
  show x + mwDegCongr (zero_add n) (mwMulRight (mwFormWord a) n x) = _
  rw [show (mwMul 0 n (mwEtaSymbol a : MilnorWittKDeg F 0)) = mwMulRight (mwFormWord a) n from
    mwMul_class_left 0 n (mwFormWord a)]

end GradedRing

end GaloisForLFunctions.HTGeometry
