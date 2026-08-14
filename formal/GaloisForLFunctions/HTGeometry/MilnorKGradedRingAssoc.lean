import GaloisForLFunctions.HTGeometry.MilnorKGradedRing
import GaloisForLFunctions.HTGeometry.MilnorWittWittComparison

/-!
# The graded ring structure of Milnor `K`-theory

The product of Milnor `K`-theory is induced by concatenation of symbols, so it is associative and
the empty symbol is a two-sided unit — up to the transport along the associativity and unit laws of
the grading, which is what `milnorDegCongr` provides.  This is what a residue map out of Milnor
`K`-theory needs of its target.

* `milnorDegCongr` : transport along an equality of degrees.
* `milnorMul_assoc` : **the graded product is associative.**
* `milnorOne_mul`, `milnorMul_one` : **the empty symbol is a two-sided unit.**
-/

namespace GaloisForLFunctions.HTGeometry

section GradedRing

variable {F : Type*} [Field F]

/-- Transport along an equality of degrees. -/
def milnorDegCongr {m n : ℕ} (h : m = n) : MilnorKDeg F m →+ MilnorKDeg F n := by
  subst h
  exact AddMonoidHom.id _

theorem milnorDegCongr_class {m n : ℕ} (h : m = n) (s : MilnorSymbolDeg F m)
    (t : MilnorSymbolDeg F n) (hst : s.val = t.val) :
    milnorDegCongr h (milnorClassDeg F m s) = milnorClassDeg F n t := by
  subst h
  show milnorClassDeg F m s = milnorClassDeg F m t
  exact congrArg _ (Subtype.ext hst)

/-- The unit of Milnor `K`-theory: the class of the empty symbol. -/
def milnorOne : MilnorKDeg F 0 := milnorClassDeg F 0 ⟨[], rfl⟩

/-- Concatenation of symbols is associative. -/
theorem milnorSymbolAppend_assoc {m n p : ℕ} (s : MilnorSymbolDeg F m) (t : MilnorSymbolDeg F n)
    (u : MilnorSymbolDeg F p) :
    (milnorSymbolAppend F (milnorSymbolAppend F s t) u).val
      = (milnorSymbolAppend F s (milnorSymbolAppend F t u)).val := by
  show (s.val ++ t.val) ++ u.val = s.val ++ (t.val ++ u.val)
  rw [List.append_assoc]

theorem milnorMul_assoc_symbol {m n p : ℕ} (s : MilnorSymbolDeg F m) (t : MilnorSymbolDeg F n)
    (u : MilnorSymbolDeg F p) :
    milnorDegCongr (Nat.add_assoc m n p)
        (milnorMul F (m + n) p (milnorMul F m n (milnorClassDeg F m s) (milnorClassDeg F n t))
          (milnorClassDeg F p u))
      = milnorMul F m (n + p) (milnorClassDeg F m s)
          (milnorMul F n p (milnorClassDeg F n t) (milnorClassDeg F p u)) := by
  rw [milnorMul_class, milnorMul_class, milnorMul_class, milnorMul_class]
  exact milnorDegCongr_class _ _ _ (milnorSymbolAppend_assoc s t u)

theorem milnorMul_assoc_left {m n p : ℕ} (t : MilnorSymbolDeg F n) (u : MilnorSymbolDeg F p)
    (x : MilnorKDeg F m) :
    milnorDegCongr (Nat.add_assoc m n p)
        (milnorMul F (m + n) p (milnorMul F m n x (milnorClassDeg F n t)) (milnorClassDeg F p u))
      = milnorMul F m (n + p) x (milnorMul F n p (milnorClassDeg F n t) (milnorClassDeg F p u)) := by
  have hext : ((milnorDegCongr (Nat.add_assoc m n p)).comp
        ((milnorMul F (m + n) p).flip (milnorClassDeg F p u))).comp
          ((milnorMul F m n).flip (milnorClassDeg F n t))
      = (milnorMul F m (n + p)).flip
          (milnorMul F n p (milnorClassDeg F n t) (milnorClassDeg F p u)) :=
    milnorKDeg_hom_ext F fun s => milnorMul_assoc_symbol s t u
  exact DFunLike.congr_fun hext x

theorem milnorMul_assoc_mid {m n p : ℕ} (u : MilnorSymbolDeg F p) (x : MilnorKDeg F m)
    (y : MilnorKDeg F n) :
    milnorDegCongr (Nat.add_assoc m n p)
        (milnorMul F (m + n) p (milnorMul F m n x y) (milnorClassDeg F p u))
      = milnorMul F m (n + p) x (milnorMul F n p y (milnorClassDeg F p u)) := by
  have hext : ((milnorDegCongr (Nat.add_assoc m n p)).comp
        ((milnorMul F (m + n) p).flip (milnorClassDeg F p u))).comp (milnorMul F m n x)
      = (milnorMul F m (n + p) x).comp ((milnorMul F n p).flip (milnorClassDeg F p u)) :=
    milnorKDeg_hom_ext F fun t => milnorMul_assoc_left t u x
  exact DFunLike.congr_fun hext y

/-- **The graded product of Milnor `K`-theory is associative.** -/
theorem milnorMul_assoc {m n p : ℕ} (x : MilnorKDeg F m) (y : MilnorKDeg F n)
    (z : MilnorKDeg F p) :
    milnorDegCongr (Nat.add_assoc m n p) (milnorMul F (m + n) p (milnorMul F m n x y) z)
      = milnorMul F m (n + p) x (milnorMul F n p y z) := by
  have hext : (milnorDegCongr (Nat.add_assoc m n p)).comp
        (milnorMul F (m + n) p (milnorMul F m n x y))
      = (milnorMul F m (n + p) x).comp (milnorMul F n p y) :=
    milnorKDeg_hom_ext F fun u => milnorMul_assoc_mid u x y
  exact DFunLike.congr_fun hext z

/-- **The empty symbol is a left unit.** -/
theorem milnorOne_mul {n : ℕ} (x : MilnorKDeg F n) :
    milnorDegCongr (Nat.zero_add n) (milnorMul F 0 n (milnorOne : MilnorKDeg F 0) x) = x := by
  have hext : (milnorDegCongr (Nat.zero_add n)).comp
        (milnorMul F 0 n (milnorOne : MilnorKDeg F 0)) = AddMonoidHom.id _ := by
    refine milnorKDeg_hom_ext F fun s => ?_
    show milnorDegCongr (Nat.zero_add n)
        (milnorMul F 0 n (milnorClassDeg F 0 ⟨[], rfl⟩) (milnorClassDeg F n s))
      = milnorClassDeg F n s
    rw [milnorMul_class]
    exact milnorDegCongr_class _ _ _ (List.nil_append s.val)
  exact DFunLike.congr_fun hext x

/-- **The empty symbol is a right unit.** -/
theorem milnorMul_one {n : ℕ} (x : MilnorKDeg F n) :
    milnorMul F n 0 x (milnorOne : MilnorKDeg F 0) = x := by
  have hext : (milnorMul F n 0).flip (milnorOne : MilnorKDeg F 0) = AddMonoidHom.id _ := by
    refine milnorKDeg_hom_ext F fun s => ?_
    show milnorMul F n 0 (milnorClassDeg F n s) (milnorClassDeg F 0 ⟨[], rfl⟩)
      = milnorClassDeg F n s
    exact milnorMul_one_right F n s
  exact DFunLike.congr_fun hext x

end GradedRing

end GaloisForLFunctions.HTGeometry
