import GaloisForLFunctions.HTGeometry.MilnorKGrading
import GaloisForLFunctions.HTGeometry.MilnorKDegFunctoriality
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Milnor `K`-theory of a finite field

Every degree-two symbol of a field is a multiple of `{g, g}` for a generator `g` of the unit group,
and `{g, g} = -{g, -1}` is killed by two.  Over a finite field it is also killed by an odd number:
there is a nonsquare `a` whose complement `1 - a` is a nonsquare, and the Steinberg relation
`{a, 1-a} = 0` reads `ij·{g,g} = 0` with `i` and `j` odd.  Two and an odd number are coprime, so
`{g,g}` vanishes and with it the whole group.

The existence of the nonsquare pair is a counting argument: if `a ↦ 1 - a` sent every nonsquare to
a nonzero square it would be an injection between two sets of the same size — the quadratic
character sums to zero — hence a bijection, and the preimage of `1` would be `0`.

* `milnorSymTwo` : the degree-two symbol, with its bilinearity.
* `two_smul_milnorSymTwo_self` : **`{a,a}` is killed by two.**
* `exists_nonsquare_oneSub_nonsquare` : **a nonsquare whose complement to one is a nonsquare.**
* `milnorKDegTwo_eq_zero_of_finite`, `milnorKDeg_eq_zero_of_finite` : **Milnor `K`-theory of a
  finite field vanishes in every degree at least two.**
-/

namespace GaloisForLFunctions.HTGeometry

section SymTwo

variable {F : Type*} [Field F]

/-- The degree-two Milnor symbol. -/
def milnorSymTwo (x y : Fˣ) : MilnorKDeg F 2 := milnorPairClass F [] [] x y

theorem milnorSymTwo_eq (x y : Fˣ) :
    milnorSymTwo x y = milnorClassDeg F 2 ⟨[x, y], rfl⟩ := rfl

theorem milnorSymTwo_mul_left (a b y : Fˣ) :
    milnorSymTwo (a * b) y = milnorSymTwo a y + milnorSymTwo b y :=
  milnorPairClass_mul_left [] [] a b y

theorem milnorSymTwo_mul_right (x a b : Fˣ) :
    milnorSymTwo x (a * b) = milnorSymTwo x a + milnorSymTwo x b :=
  milnorPairClass_mul_right [] [] x a b

theorem milnorSymTwo_one_left (y : Fˣ) : milnorSymTwo (1 : Fˣ) y = 0 :=
  milnorPairClass_one_left [] [] y

theorem milnorSymTwo_one_right (x : Fˣ) : milnorSymTwo x (1 : Fˣ) = 0 :=
  milnorPairClass_one_right [] [] x

theorem milnorSymTwo_steinberg {a : Fˣ} (ha : (a : F) ≠ 1) :
    milnorSymTwo a (oneSubUnit ha) = 0 :=
  milnorPairClass_steinberg [] [] ha

theorem milnorSymTwo_neg_self (a : Fˣ) : milnorSymTwo a (-a) = 0 :=
  milnorPairClass_neg_self [] [] a

/-- The symbol as an additive homomorphism in its second entry. -/
def milnorSymTwoRight (x : Fˣ) : Additive Fˣ →+ MilnorKDeg F 2 where
  toFun y := milnorSymTwo x (Additive.toMul y)
  map_zero' := milnorSymTwo_one_right x
  map_add' _ _ := milnorSymTwo_mul_right x _ _

/-- The symbol as an additive homomorphism in its first entry. -/
def milnorSymTwoLeft (y : Fˣ) : Additive Fˣ →+ MilnorKDeg F 2 where
  toFun x := milnorSymTwo (Additive.toMul x) y
  map_zero' := milnorSymTwo_one_left y
  map_add' _ _ := milnorSymTwo_mul_left _ _ y

theorem milnorSymTwo_zpow_right (x y : Fˣ) (j : ℤ) :
    milnorSymTwo x (y ^ j) = j • milnorSymTwo x y := by
  have h := map_zsmul (milnorSymTwoRight x) j (Additive.ofMul y)
  exact h

theorem milnorSymTwo_zpow_left (x y : Fˣ) (i : ℤ) :
    milnorSymTwo (x ^ i) y = i • milnorSymTwo x y :=
  map_zsmul (milnorSymTwoLeft y) i (Additive.ofMul x)

theorem milnorSymTwo_zpow (g : Fˣ) (i j : ℤ) :
    milnorSymTwo (g ^ i) (g ^ j) = (i * j) • milnorSymTwo g g := by
  rw [milnorSymTwo_zpow_right, milnorSymTwo_zpow_left, smul_smul, mul_comm]

/-- **`{a, a}` is killed by two.**  It is `-{a,-1}`, and `{a,-1}` is two-torsion. -/
theorem two_smul_milnorSymTwo_self (a : Fˣ) : (2 : ℤ) • milnorSymTwo a a = 0 := by
  have hneg : (-a : Fˣ) = (-1 : Fˣ) * a := by
    refine Units.ext ?_
    simp
  have hsplit : milnorSymTwo a (-1 : Fˣ) + milnorSymTwo a a = 0 := by
    have h := milnorSymTwo_mul_right a (-1 : Fˣ) a
    rw [← hneg, milnorSymTwo_neg_self] at h
    exact h.symm
  have hsq : milnorSymTwo a (-1 : Fˣ) + milnorSymTwo a (-1 : Fˣ) = 0 := by
    have h := milnorSymTwo_mul_right a (-1 : Fˣ) (-1 : Fˣ)
    rw [show (-1 : Fˣ) * (-1 : Fˣ) = 1 by simp, milnorSymTwo_one_right] at h
    exact h.symm
  have hself : milnorSymTwo a a = -milnorSymTwo a (-1 : Fˣ) :=
    (neg_eq_of_add_eq_zero_right hsplit).symm
  rw [hself, two_smul, ← neg_add, hsq, neg_zero]

end SymTwo

open Finset

section Counting

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **In a finite field of odd characteristic there is a nonsquare whose complement to one is
also a nonsquare.**  Otherwise `a ↦ 1 - a` would be a bijection from the nonsquares onto the
nonzero squares, and `1` would have a preimage, forcing `0` to be a nonsquare. -/
theorem exists_nonsquare_oneSub_nonsquare (hF : ringChar F ≠ 2) :
    ∃ a : F, ¬ IsSquare a ∧ ¬ IsSquare (1 - a) := by
  by_contra hcon
  push Not at hcon
  classical
  set A : Finset F := univ.filter (fun a => quadraticChar F a = 1) with hA
  set B : Finset F := univ.filter (fun a => quadraticChar F a = -1) with hB
  have hval : ∀ a : F, quadraticChar F a
      = (if quadraticChar F a = 1 then (1 : ℤ) else 0)
        - (if quadraticChar F a = -1 then (1 : ℤ) else 0) := by
    intro a
    rcases quadraticChar_isQuadratic F a with h | h | h <;> simp [h]
  have hsum : (0 : ℤ) = (A.card : ℤ) - B.card := by
    rw [← quadraticChar_sum_zero (F := F) hF, Finset.sum_congr rfl (fun a _ => hval a),
      Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  have hcard : B.card = A.card := by omega
  have hmemB : ∀ a ∈ B, ¬ IsSquare a := by
    intro a haB
    rw [hB, Finset.mem_filter] at haB
    exact quadraticChar_neg_one_iff_not_isSquare.1 haB.2
  have hmap : ∀ a ∈ B, (1 - a) ∈ A := by
    intro a haB
    have hns := hmemB a haB
    have hsq : IsSquare (1 - a) := hcon a hns
    have hne : (1 : F) - a ≠ 0 := by
      intro h
      exact hns (by rw [show a = 1 by linear_combination -h]; exact ⟨1, (one_mul 1).symm⟩)
    rw [hA, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (quadraticChar_one_iff_isSquare hne).2 hsq⟩
  have hinj : Set.InjOn (fun a : F => 1 - a) B := by
    intro a _ b _ hab
    exact by linear_combination -hab
  have hsub : B.image (fun a : F => 1 - a) ⊆ A := by
    intro y hy
    obtain ⟨a, haB, rfl⟩ := Finset.mem_image.1 hy
    exact hmap a haB
  have heq : B.image (fun a : F => 1 - a) = A :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_image_of_injOn hinj, hcard])
  have h1A : (1 : F) ∈ A := by
    rw [hA, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, MulChar.map_one _⟩
  rw [← heq] at h1A
  obtain ⟨u, huB, hu1⟩ := Finset.mem_image.1 h1A
  have hu0 : u = 0 := by linear_combination -hu1
  rw [hB, Finset.mem_filter] at huB
  rw [hu0, quadraticChar_zero] at huB
  exact absurd huB.2 (by decide)

end Counting

section Vanishing

variable {F : Type*} [Field F]

theorem milnorSymTwo_self_eq_neg (a : Fˣ) :
    milnorSymTwo a a = -milnorSymTwo a (-1 : Fˣ) := by
  have hneg : (-a : Fˣ) = (-1 : Fˣ) * a := by
    refine Units.ext ?_
    simp
  have hsplit : milnorSymTwo a (-1 : Fˣ) + milnorSymTwo a a = 0 := by
    have h := milnorSymTwo_mul_right a (-1 : Fˣ) a
    rw [← hneg, milnorSymTwo_neg_self] at h
    exact h.symm
  exact (neg_eq_of_add_eq_zero_right hsplit).symm

theorem milnorSymTwo_self_eq_zero_of_char_two (h2 : ringChar F = 2) (a : Fˣ) :
    milnorSymTwo a a = 0 := by
  have hz : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).2 (by rw [h2])
  have hone : (1 : F) + 1 = 0 := by push_cast at hz; linear_combination hz
  have hneg : (-1 : Fˣ) = 1 := by
    refine Units.ext ?_
    show (-1 : F) = 1
    linear_combination -hone
  rw [milnorSymTwo_self_eq_neg, hneg, milnorSymTwo_one_right, neg_zero]

theorem odd_of_not_isSquare_zpow {G : Type*} [CommGroup G] {g : G} {i : ℤ}
    (h : ¬ IsSquare (g ^ i)) : Odd i := by
  rcases Int.even_or_odd i with ⟨m, hm⟩ | ho
  · exact absurd ⟨g ^ m, by rw [hm, zpow_add]⟩ h
  · exact ho

variable [Fintype F]

/-- **The square of a generator of the unit group is zero in degree two.** -/
theorem milnorSymTwo_gen_eq_zero (g : Fˣ) (hg : ∀ a : Fˣ, ∃ i : ℤ, g ^ i = a) :
    milnorSymTwo g g = 0 := by
  classical
  by_cases h2 : ringChar F = 2
  · exact milnorSymTwo_self_eq_zero_of_char_two h2 g
  · obtain ⟨a, hns, hns'⟩ := exists_nonsquare_oneSub_nonsquare (F := F) h2
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hns ⟨0, by ring⟩
    set u : Fˣ := Units.mk0 a ha0 with hu
    have hu1 : (u : F) ≠ 1 := by
      intro h
      exact hns (by rw [show a = 1 from h]; exact ⟨1, (one_mul 1).symm⟩)
    have hnsu : ¬ IsSquare u := by
      rintro ⟨v, hv⟩
      exact hns ⟨(v : F), congrArg Units.val hv⟩
    have hnsv : ¬ IsSquare (oneSubUnit hu1) := by
      rintro ⟨v, hv⟩
      exact hns' ⟨(v : F), congrArg Units.val hv⟩
    obtain ⟨i, hi⟩ := hg u
    obtain ⟨j, hj⟩ := hg (oneSubUnit hu1)
    have hoi : Odd i := odd_of_not_isSquare_zpow (by rw [hi]; exact hnsu)
    have hoj : Odd j := odd_of_not_isSquare_zpow (by rw [hj]; exact hnsv)
    have hst : ((i * j : ℤ)) • milnorSymTwo g g = 0 := by
      rw [← milnorSymTwo_zpow, hi, hj]
      exact milnorSymTwo_steinberg hu1
    have h2t := two_smul_milnorSymTwo_self g
    obtain ⟨m, hm⟩ := hoi.mul hoj
    set N : ℤ := i * j with hN
    have hone : N - 2 * m = 1 := by omega
    calc milnorSymTwo g g
        = (N - 2 * m) • milnorSymTwo g g := by rw [hone, one_smul]
      _ = N • milnorSymTwo g g - (2 * m : ℤ) • milnorSymTwo g g := sub_smul _ _ _
      _ = 0 - m • ((2 : ℤ) • milnorSymTwo g g) := by
            rw [hst, mul_comm (2 : ℤ) m, mul_smul]
      _ = 0 := by rw [h2t, smul_zero, sub_zero]

/-- **Milnor `K`-theory of a finite field vanishes in degree two.** -/
theorem milnorKDegTwo_eq_zero_of_finite (x : MilnorKDeg F 2) : x = 0 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgen : ∀ a : Fˣ, ∃ i : ℤ, g ^ i = a := fun a => Subgroup.mem_zpowers_iff.1 (hg a)
  have hθ := milnorSymTwo_gen_eq_zero g hgen
  have hmem : x ∈ (⊥ : AddSubgroup (MilnorKDeg F 2)) := by
    refine milnorKDeg_mem_of_gen _ (fun s => ?_) x
    obtain ⟨a, b, hs⟩ := List.length_eq_two.1 s.property
    have hsym : milnorClassDeg F 2 s = milnorSymTwo a b := by
      rw [milnorSymTwo_eq]
      exact congrArg _ (Subtype.ext hs)
    obtain ⟨i, hi⟩ := hgen a
    obtain ⟨j, hj⟩ := hgen b
    rw [hsym, ← hi, ← hj, milnorSymTwo_zpow, hθ, smul_zero]
    exact AddSubgroup.zero_mem _
  simpa using hmem

/-- **Milnor `K`-theory of a finite field vanishes in every degree at least two.** -/
theorem milnorKDeg_eq_zero_of_finite (k : ℕ) (x : MilnorKDeg F (2 + k)) : x = 0 := by
  have hmem : x ∈ (⊥ : AddSubgroup (MilnorKDeg F (2 + k))) := by
    refine milnorKDeg_mem_of_gen _ (fun s => ?_) x
    obtain ⟨s₁, s₂, hsplit⟩ : ∃ (s₁ : MilnorSymbolDeg F 2) (s₂ : MilnorSymbolDeg F k),
        s.val = s₁.val ++ s₂.val := by
      refine ⟨⟨s.val.take 2, ?_⟩, ⟨s.val.drop 2, ?_⟩, ?_⟩
      · rw [List.length_take, s.property]
        omega
      · rw [List.length_drop, s.property]
        omega
      · exact (List.take_append_drop 2 s.val).symm
    rw [milnorClassDeg_split F k s s₁ s₂ hsplit,
      milnorKDegTwo_eq_zero_of_finite (milnorClassDeg F 2 s₁), map_zero,
      AddMonoidHom.zero_apply]
    exact AddSubgroup.zero_mem _
  simpa using hmem

end Vanishing

end GaloisForLFunctions.HTGeometry
