import GaloisForLFunctions.HTGeometry.MilnorWittGradedCollapse

/-!
# `η[a²] = 0` in graded Milnor--Witt `K`-theory

In degree zero the element `η[a]` is `⟨a⟩ - 1`, the deviation of the one-dimensional form `a` from
the unit.  Twisted multiplicativity makes `η[ab]` and `η[a] + η[b]` differ by `η²[a][b]`, the
hyperbolic relation computes `η²[-1][a]`, and `[a][-a] = 0` kills `η²[a][-a]`.  Together they force

  `η[a²] = 0`,

which over a quadratically closed field says that `η` annihilates every symbol.

* `mwEtaSymbol`, `mwEtaSymbol₂`, `mwEtaSymbol₃` : the degree-zero words `η[a]`, `η²[a][b]`,
  `η³[a][b][c]`.
* `mwEtaSymbol_mul` : `η[ab] = η[a] + η[b] + η²[a][b]`.
* `mwEtaSymbol_add_neg` : `η[a] + η[-a] = η[-1]`.
* `mwEtaSymbol_sq` : **`η[a²] = 0`**.
* `mwEtaSymbol_eq_zero` : over a quadratically closed field, `η[u] = 0` for every unit.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWittGradedSquare

variable {F : Type*} [Field F]

/-- The degree-zero word `η[a]`. -/
def mwEtaSymbol (a : Fˣ) : MilnorWittKDeg F 0 := mwClassDeg F 0 ⟨(1, [a]), by simp⟩

/-- The degree-zero word `η²[a][b]`. -/
def mwEtaSymbol₂ (a b : Fˣ) : MilnorWittKDeg F 0 := mwClassDeg F 0 ⟨(2, [a, b]), by simp⟩

/-- The degree-zero word `η³[a][b][c]`. -/
def mwEtaSymbol₃ (a b c : Fˣ) : MilnorWittKDeg F 0 :=
  mwClassDeg F 0 ⟨(3, [a, b, c]), by simp⟩

/-- The degree-one word `η[a][b]`. -/
def mwSymbolPair (a b : Fˣ) : MilnorWittKDeg F 1 := mwClassDeg F 1 ⟨(1, [a, b]), by simp⟩

/-- The degree-one word `η²[a][b][c]`. -/
def mwSymbolTriple (a b c : Fˣ) : MilnorWittKDeg F 1 :=
  mwClassDeg F 1 ⟨(2, [a, b, c]), by simp⟩

theorem mwSymMulRight_etaSymbol (h : (1 : ℤ) = 0 + 1) (a u : Fˣ) :
    mwSymMulRight (F := F) h u (mwEtaSymbol a) = mwSymbolPair a u := by
  simp only [mwEtaSymbol, mwSymbolPair, mwSymMulRight_class]
  rfl

theorem mwSymMulRight_etaSymbol₂ (h : (1 : ℤ) = 0 + 1) (a b u : Fˣ) :
    mwSymMulRight (F := F) h u (mwEtaSymbol₂ a b) = mwSymbolTriple a b u := by
  simp only [mwEtaSymbol₂, mwSymbolTriple, mwSymMulRight_class]
  rfl

theorem mwEtaMul_symbolPair (h : (1 : ℤ) = 0 + 1) (a b : Fˣ) :
    mwEtaMul (F := F) h (mwSymbolPair a b) = mwEtaSymbol₂ a b := by
  simp only [mwSymbolPair, mwEtaSymbol₂, mwEtaMul_class]
  rfl

theorem mwEtaMul_symbolTriple (h : (1 : ℤ) = 0 + 1) (a b c : Fˣ) :
    mwEtaMul (F := F) h (mwSymbolTriple a b c) = mwEtaSymbol₃ a b c := by
  simp only [mwSymbolTriple, mwEtaSymbol₃, mwEtaMul_class]
  rfl

/-- **Twisted multiplicativity in degree zero**: `η[ab] = η[a] + η[b] + η²[a][b]`. -/
theorem mwEtaSymbol_mul (a b : Fˣ) :
    (mwEtaSymbol (a * b) : MilnorWittKDeg F 0) =
      mwEtaSymbol a + mwEtaSymbol b + mwEtaSymbol₂ a b :=
  mwClassDeg_twisted (F := F) 1 a b [] [] rfl rfl rfl rfl _ _ _ _

/-- **The hyperbolic relation in degree zero**: `η²[-1][a] + 2η[a] = 0`. -/
theorem mwEtaSymbol₂_neg_one (a : Fˣ) :
    (mwEtaSymbol₂ (-1) a : MilnorWittKDeg F 0) + (mwEtaSymbol a + mwEtaSymbol a) = 0 :=
  mwClassDeg_hyperbolic (F := F) 0 [] [a] rfl rfl _ _

/-- **`η²[a][-a] = 0`.** -/
theorem mwEtaSymbol₂_neg_self (a : Fˣ) : (mwEtaSymbol₂ a (-a) : MilnorWittKDeg F 0) = 0 :=
  mwSymbol_mul_neg_self (F := F) 2 [] a _

/-- **`η[a] + η[-a] = η[-1]`.** -/
theorem mwEtaSymbol_add_neg (a : Fˣ) :
    (mwEtaSymbol a : MilnorWittKDeg F 0) + mwEtaSymbol (-a) = mwEtaSymbol (-1) := by
  have hneg : (-1 : Fˣ) * a = -a := by
    refine Units.ext ?_
    push_cast
    ring
  have h := mwEtaSymbol_mul (F := F) (-1) a
  rw [hneg] at h
  have h2 := mwEtaSymbol₂_neg_one (F := F) a
  have h3 : (mwEtaSymbol₂ (-1) a : MilnorWittKDeg F 0) =
      -(mwEtaSymbol a + mwEtaSymbol a) := eq_neg_of_add_eq_zero_left h2
  rw [h3] at h
  rw [h]
  abel

/-- **`η[a²] = 0`.**  The two expansions of `η[a·(-a)] = η[(-1)·a²]` and the hyperbolic relation
leave `η²[a²][-1]`, which the hyperbolic relation again forces to vanish. -/
theorem mwEtaSymbol_sq (a : Fˣ) : (mwEtaSymbol (a * a) : MilnorWittKDeg F 0) = 0 := by
  have hprod : a * (-a) = (-1 : Fˣ) * (a * a) := by
    refine Units.ext ?_
    push_cast
    ring
  have h1 := mwEtaSymbol_mul (F := F) a (-a)
  rw [mwEtaSymbol₂_neg_self, add_zero, mwEtaSymbol_add_neg, hprod] at h1
  have h2raw := mwEtaSymbol_mul (F := F) (-1) (a * a)
  have h4raw := mwEtaSymbol_mul (F := F) (a * a) (-1)
  have h5 : (a * a) * (-1 : Fˣ) = (-1 : Fˣ) * (a * a) := mul_comm _ _
  rw [h5] at h4raw
  have hcomm : (mwEtaSymbol₂ (-1) (a * a) : MilnorWittKDeg F 0) = mwEtaSymbol₂ (a * a) (-1) := by
    calc (mwEtaSymbol₂ (-1) (a * a) : MilnorWittKDeg F 0)
        = (mwEtaSymbol (-1) + mwEtaSymbol (a * a) + mwEtaSymbol₂ (-1) (a * a)) -
            (mwEtaSymbol (-1) + mwEtaSymbol (a * a)) := by abel
      _ = (mwEtaSymbol (a * a) + mwEtaSymbol (-1) + mwEtaSymbol₂ (a * a) (-1)) -
            (mwEtaSymbol (-1) + mwEtaSymbol (a * a)) := by rw [← h2raw, ← h4raw]
      _ = mwEtaSymbol₂ (a * a) (-1) := by abel
  have h2 : (mwEtaSymbol (-1) : MilnorWittKDeg F 0) =
      mwEtaSymbol (-1) + mwEtaSymbol (a * a) + mwEtaSymbol₂ (-1) (a * a) := by
    rw [← h2raw, h1]
  have hR : (mwEtaSymbol (a * a) : MilnorWittKDeg F 0) + mwEtaSymbol₂ (a * a) (-1) = 0 := by
    rw [← hcomm]
    calc (mwEtaSymbol (a * a) : MilnorWittKDeg F 0) + mwEtaSymbol₂ (-1) (a * a)
        = (mwEtaSymbol (-1) + mwEtaSymbol (a * a) + mwEtaSymbol₂ (-1) (a * a)) -
            mwEtaSymbol (-1) := by abel
      _ = mwEtaSymbol (-1) - mwEtaSymbol (-1) := by rw [← h2]
      _ = 0 := sub_self _
  have hhyp : (mwEtaSymbol₃ (a * a) (-1) (-1) : MilnorWittKDeg F 0) +
      (mwEtaSymbol₂ (a * a) (-1) + mwEtaSymbol₂ (a * a) (-1)) = 0 :=
    mwClassDeg_hyperbolic (F := F) 1 [a * a, -1] [] rfl rfl _ _
  have hstep : (mwSymbolPair (a * a) (-1) : MilnorWittKDeg F 1) +
      mwSymbolTriple (a * a) (-1) (-1) = 0 := by
    have h := congrArg (mwSymMulRight (F := F) (by ring : (1 : ℤ) = 0 + 1) (-1 : Fˣ)) hR
    rw [map_add, map_zero, mwSymMulRight_etaSymbol, mwSymMulRight_etaSymbol₂] at h
    exact h
  have hstep2 : (mwEtaSymbol₂ (a * a) (-1) : MilnorWittKDeg F 0) +
      mwEtaSymbol₃ (a * a) (-1) (-1) = 0 := by
    have h := congrArg (mwEtaMul (F := F) (by ring : (1 : ℤ) = 0 + 1)) hstep
    rw [map_add, map_zero, mwEtaMul_symbolPair, mwEtaMul_symbolTriple] at h
    exact h
  have hzero : (mwEtaSymbol₂ (a * a) (-1) : MilnorWittKDeg F 0) = 0 := by
    calc (mwEtaSymbol₂ (a * a) (-1) : MilnorWittKDeg F 0)
        = (mwEtaSymbol₃ (a * a) (-1) (-1) +
            (mwEtaSymbol₂ (a * a) (-1) + mwEtaSymbol₂ (a * a) (-1))) -
              (mwEtaSymbol₂ (a * a) (-1) + mwEtaSymbol₃ (a * a) (-1) (-1)) := by abel
      _ = 0 - 0 := by rw [hhyp, hstep2]
      _ = 0 := sub_self _
  rw [hzero, add_zero] at hR
  exact hR

/-! ### Quadratically closed fields -/

/-- **Over a quadratically closed field `η` annihilates every symbol.** -/
theorem mwEtaSymbol_eq_zero (hsq : ∀ x : F, ∃ y : F, x = y * y) (u : Fˣ) :
    (mwEtaSymbol u : MilnorWittKDeg F 0) = 0 := by
  obtain ⟨b, hb⟩ := exists_unit_sq F hsq u
  rw [hb, pow_two]
  exact mwEtaSymbol_sq b

end MilnorWittGradedSquare

end GaloisForLFunctions.HTGeometry
