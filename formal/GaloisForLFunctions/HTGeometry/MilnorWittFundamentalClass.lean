import GaloisForLFunctions.HTGeometry.MilnorWittTwist
import GaloisForLFunctions.HTGeometry.MilnorWittGradedRing
import GaloisForLFunctions.HTGeometry.MilnorWittWittComparison

/-!
# The oriented Milnor--Witt fundamental class of a line

The fundamental class of a codimension-one regular immersion is a Milnor--Witt class twisted by the
determinant of the conormal line, so it is an element of the twist of `K_0^{MW}` by that line.  The
unit quadratic orientation is the class `⟨1⟩ = 1` placed at a generator.

Its rank is what compares it with an ordinary cycle: the rank of a degree-zero Milnor--Witt class
kills every word with an `η` and sends the empty word to `1`, so `⟨u⟩ = 1 + η[u]` has rank one for
every unit `u`.  Consequently the oriented fundamental class has rank one *whichever* generator of
the determinant line is used to trivialize the twist — the choice moves the class by a unit form,
and unit forms are invisible to the rank.  This is the forgetful statement: the oriented class
covers the ordinary fundamental cycle with multiplicity one.

* `mwRank` : the rank of degree-zero Milnor--Witt `K`-theory.
* `mwFormAct_mwOne` : **`⟨a⟩ = 1 + η[a]`.**
* `mwRank_formAct_mwOne` : **every unit form has rank one.**
* `mwFundamentalClass` : **the oriented fundamental class of a line.**
* `mwRank_fundamentalClass`, `mwTwistRank_fundamentalClass` : **its rank is one.**
-/

namespace GaloisForLFunctions.HTGeometry

section Rank

variable {F : Type*} [Field F]

/-- **The unit form**: `⟨a⟩ = 1 + η[a]`. -/
theorem mwFormAct_mwOne (a : Fˣ) :
    mwFormAct a 0 (mwOne : MilnorWittKDeg F 0) = mwOne + mwEtaSymbol a := by
  rw [mwOne, mwFormAct_class a 0 [] (by simp) (by simp)]
  rfl

/-- **The rank of a degree-zero Milnor--Witt class.** -/
def mwRank : MilnorWittKDeg F 0 →+ ℤ :=
  (milnorDegZeroEquiv F).toAddMonoidHom.comp
    ((mwForget 0).comp (mwDegCongr (show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num)))

@[simp]
theorem mwRank_mwOne : mwRank (mwOne : MilnorWittKDeg F 0) = 1 := by
  have h1 : mwDegCongr (show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num) (mwOne : MilnorWittKDeg F 0)
      = mwClassDeg F ((0 : ℕ) : ℤ) (⟨(0, []), by simp⟩ : MWWordDeg F ((0 : ℕ) : ℤ)) :=
    mwDegCongr_class' _ (⟨(0, []), by simp⟩ : MWWordDeg F (0 : ℤ)) _ rfl
  show milnorDegZeroHom F (mwForget 0
      (mwDegCongr (show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num) (mwOne : MilnorWittKDeg F 0))) = 1
  rw [h1, mwForget_class]
  exact milnorDegZeroHom_class F _

/-- **A word with an `η` has rank zero.** -/
theorem mwRank_class_succ (k : ℕ) (l : List Fˣ) (p : ((l.length : ℤ)) - (k + 1) = 0) :
    mwRank (mwClassDeg F 0 ⟨(k + 1, l), p⟩) = 0 := by
  have h1 : mwDegCongr (show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num)
        (mwClassDeg F 0 (⟨(k + 1, l), p⟩ : MWWordDeg F (0 : ℤ)))
      = mwClassDeg F ((0 : ℕ) : ℤ)
        (⟨(k + 1, l), by rw [Nat.cast_zero]; exact p⟩ : MWWordDeg F ((0 : ℕ) : ℤ)) :=
    mwDegCongr_class' _ _ _ rfl
  show milnorDegZeroHom F (mwForget 0
      (mwDegCongr (show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num)
        (mwClassDeg F 0 (⟨(k + 1, l), p⟩ : MWWordDeg F (0 : ℤ))))) = 0
  rw [h1, mwForget_class]
  show milnorDegZeroHom F (0 : MilnorKDeg F 0) = 0
  rw [map_zero]

@[simp]
theorem mwRank_etaSymbol (a : Fˣ) : mwRank (mwEtaSymbol a : MilnorWittKDeg F 0) = 0 :=
  mwRank_class_succ 0 [a] (by simp)

/-- **Every unit form has rank one**: the rank does not see the quadratic orientation. -/
theorem mwRank_formAct_mwOne (a : Fˣ) :
    mwRank (mwFormAct a 0 (mwOne : MilnorWittKDeg F 0)) = 1 := by
  rw [mwFormAct_mwOne, map_add, mwRank_mwOne, mwRank_etaSymbol, add_zero]


/-- **The rank is invariant under the unit forms.**  Multiplying by `⟨u⟩` adds a word with one more
`η`, and every such word has rank zero.  So the rank of a twisted class does not depend on the
trivialization. -/
theorem mwRank_formAct (u : Fˣ) (x : MilnorWittKDeg F 0) :
    mwRank (mwFormAct u 0 x) = mwRank x := by
  have hext : (mwRank : MilnorWittKDeg F 0 →+ ℤ).comp (mwFormAct u 0)
      = (mwRank : MilnorWittKDeg F 0 →+ ℤ) := by
    refine mwKDeg_hom_ext F fun w => ?_
    obtain ⟨⟨k, l⟩, p⟩ := w
    have q : (((u :: l).length : ℤ)) - (1 + k) = 0 := by
      simp only [List.length_cons]; push_cast at p ⊢; omega
    have q' : (((u :: l).length : ℤ)) - (k + 1) = 0 := by
      simp only [List.length_cons]; push_cast at p ⊢; omega
    show mwRank (mwFormAct u 0 (mwClassDeg F 0 ⟨(k, l), p⟩))
      = mwRank (mwClassDeg F 0 ⟨(k, l), p⟩)
    rw [mwFormAct_class u k l p q, map_add,
      show mwClassDeg F 0 (⟨(1 + k, u :: l), q⟩ : MWWordDeg F 0)
        = mwClassDeg F 0 (⟨(k + 1, u :: l), q'⟩ : MWWordDeg F 0) from
        congrArg _ (Subtype.ext (show ((1 + k, u :: l) : ℕ × List Fˣ) = (k + 1, u :: l) by
          rw [Nat.add_comm 1 k])),
      mwRank_class_succ k (u :: l) q', add_zero]
  exact DFunLike.congr_fun hext x

end Rank

section TwistRank

variable {F : Type*} [Field F] {T : Type*} [MulAction Fˣ T]

/-- The rank on finitely supported families. -/
noncomputable def mwTwistRankPre : (T →₀ MilnorWittKDeg F 0) →+ ℤ :=
  Finsupp.liftAddHom fun _ => (mwRank : MilnorWittKDeg F 0 →+ ℤ)

omit [MulAction Fˣ T] in
theorem mwTwistRankPre_single (t : T) (m : MilnorWittKDeg F 0) :
    mwTwistRankPre (Finsupp.single t m) = mwRank m :=
  Finsupp.liftAddHom_apply_single _ _ _

theorem mwTwistRankPre_rel : mwTwistRel F 0 T ≤ (mwTwistRankPre (F := F) (T := T)).ker := by
  rw [mwTwistRel, AddSubgroup.closure_le]
  rintro x ⟨u, t, m, rfl⟩
  show mwTwistRankPre (Finsupp.single (u • t) m - Finsupp.single t (mwFormAct u 0 m)) = 0
  rw [map_sub, mwTwistRankPre_single, mwTwistRankPre_single, sub_eq_zero, mwRank_formAct]

/-- **The rank of a twisted Milnor--Witt class**, with no trivialization chosen: the twist relations
move a class by a unit form, and the rank does not see unit forms. -/
noncomputable def mwTwistRank : MWTwist F 0 T →+ ℤ :=
  QuotientAddGroup.lift _ mwTwistRankPre mwTwistRankPre_rel

@[simp]
theorem mwTwistRank_mk (t : T) (m : MilnorWittKDeg F 0) :
    mwTwistRank (mwTwistMk F 0 T t m) = mwRank m := by
  show mwTwistRankPre (Finsupp.single t m) = _
  rw [mwTwistRankPre_single]

end TwistRank

section FundamentalClass

variable (F : Type*) [Field F] (L : Type*) [AddCommGroup L] [Module F L]

/-- **The oriented Milnor--Witt fundamental class** of a line: the unit quadratic orientation
placed at a generator of the line. -/
noncomputable def mwFundamentalClass (e : L) (he : e ≠ 0) : MWLineTwist F 0 L :=
  mwTwistMk F 0 (MWLinePoints F L) ⟨e, he⟩ mwOne

variable {F L}

/-- The generator used to build the class trivializes it to the unit orientation. -/
theorem mwFundamentalClass_triv (e : L) (he : e ≠ 0) (hspan : ∀ v : L, ∃ c : F, v = c • e) :
    mwLineTwistEquiv e he hspan (mwFundamentalClass F L e he) = mwOne := by
  show mwTwistTriv (⟨e, he⟩ : MWLinePoints F L) (MWLinePoints.exists_smul e he hspan)
      (MWLinePoints.smul_left_injective e he)
      (mwTwistMk F 0 (MWLinePoints F L) ⟨e, he⟩ mwOne) = mwOne
  rw [mwTwistTriv_mk_base]

/-- **Another generator moves the class by the unit form of the ratio.** -/
theorem mwFundamentalClass_smul (e : L) (he : e ≠ 0) (hspan : ∀ v : L, ∃ c : F, v = c • e)
    (u : Fˣ) (hu : ((u : F) • e) ≠ 0) :
    mwLineTwistEquiv e he hspan (mwFundamentalClass F L ((u : F) • e) hu)
      = mwFormAct u 0 (mwOne : MilnorWittKDeg F 0) := by
  have hpt : (⟨(u : F) • e, hu⟩ : MWLinePoints F L) = u • (⟨e, he⟩ : MWLinePoints F L) :=
    MWLinePoints.ext_vec rfl
  show mwLineTwistEquiv e he hspan
      (mwTwistMk F 0 (MWLinePoints F L) ⟨(u : F) • e, hu⟩ mwOne) = _
  rw [hpt]
  exact mwLineTwistEquiv_smul e he hspan u mwOne

/-- **The oriented fundamental class has rank one for every choice of generators.**  The class
built from one generator, read through the trivialization by another, differs from the unit
orientation by a unit form, and unit forms have rank one.  This is the forgetful statement: the
oriented class covers the ordinary fundamental cycle with multiplicity one. -/
theorem mwRank_fundamentalClass (e e' : L) (he : e ≠ 0) (he' : e' ≠ 0)
    (hspan : ∀ v : L, ∃ c : F, v = c • e) :
    mwRank (mwLineTwistEquiv e he hspan (mwFundamentalClass F L e' he')) = 1 := by
  obtain ⟨u, hu⟩ :=
    MWLinePoints.exists_smul e he hspan (⟨e', he'⟩ : MWLinePoints F L)
  show mwRank (mwLineTwistEquiv e he hspan
      (mwTwistMk F 0 (MWLinePoints F L) ⟨e', he'⟩ mwOne)) = 1
  rw [hu, mwLineTwistEquiv_smul]
  exact mwRank_formAct_mwOne u

/-- **The oriented fundamental class has rank one, with no trivialization chosen.**  This is the
forgetful statement in its basis-free form: the oriented class covers the ordinary fundamental cycle
with multiplicity one. -/
theorem mwTwistRank_fundamentalClass (e : L) (he : e ≠ 0) :
    mwTwistRank (mwFundamentalClass F L e he) = 1 := by
  show mwTwistRank (mwTwistMk F 0 (MWLinePoints F L) ⟨e, he⟩ mwOne) = 1
  rw [mwTwistRank_mk, mwRank_mwOne]

end FundamentalClass

end GaloisForLFunctions.HTGeometry
