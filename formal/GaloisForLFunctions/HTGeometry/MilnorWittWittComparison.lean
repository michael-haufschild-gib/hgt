import GaloisForLFunctions.HTGeometry.MilnorWittKTheory
import GaloisForLFunctions.HTGeometry.WittRing
import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Milnor--Witt `K`-theory maps to the Witt ring

Sending the Milnor--Witt symbol `[u]` to the one-fold Pfister form `⟨⟨u⟩⟩` and the generator `η` to
`-1` respects all four of Morel's relations.  Two of the checks are the Witt-side theorems already
proved: the Steinberg relation `⟨⟨a, 1-a⟩⟩ = 0`, and the expansion
`⟨⟨uv⟩⟩ = ⟨⟨u⟩⟩ + ⟨⟨v⟩⟩ - ⟨⟨u⟩⟩⟨⟨v⟩⟩`, whose sign is exactly the value `-1` assigned to `η`.  The
hyperbolic relation holds because `⟨⟨-1⟩⟩ = 2`.

Together with the forgetful morphism onto Milnor `K`-theory this gives both maps out of Milnor--Witt
`K`-theory in the fundamental cartesian square.

* `milnorWittToWitt` : the ring map onto the Witt ring.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Comparison

variable (F : Type*) [Field F]

/-- **The one-fold Pfister form at `-1` is `2`.** -/
theorem pfisterOne_neg_one : pfisterOne F (-1) = 2 := by
  rw [pfisterOne, wittClass_neg_one, wittClass_one]
  ring

/-- The generator values of the comparison map: `η` goes to `-1` and `[u]` to `⟨⟨u⟩⟩`. -/
def milnorWittToWittGen : MWGen F → WittRing F
  | MWGen.eta => -1
  | MWGen.sym u => pfisterOne F u

theorem milnorWittToWitt_rel :
    ∀ x y : FreeAlgebra ℤ (MWGen F), MilnorWittRel F x y →
      FreeAlgebra.lift ℤ (milnorWittToWittGen F) x =
        FreeAlgebra.lift ℤ (milnorWittToWittGen F) y := by
  rintro _ _ (⟨a, ha⟩ | ⟨u, v⟩ | ⟨u⟩ | _)
  · rw [map_mul, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, map_zero]
    exact pfisterOne_mul_oneSub F ha
  · rw [FreeAlgebra.lift_ι_apply, map_add, map_add, map_mul, map_mul,
      FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
    show pfisterOne F (u * v) =
      pfisterOne F u + pfisterOne F v + -1 * pfisterOne F u * pfisterOne F v
    rw [pfisterOne_mul]
    ring
  · rw [map_mul, map_mul, FreeAlgebra.lift_ι_apply, FreeAlgebra.lift_ι_apply]
    show pfisterOne F u * (-1) = -1 * pfisterOne F u
    ring
  · rw [map_mul, map_zero, map_add, map_mul, FreeAlgebra.lift_ι_apply,
      FreeAlgebra.lift_ι_apply, map_ofNat]
    show (-1 : WittRing F) * (-1 * pfisterOne F (-1) + 2) = 0
    rw [pfisterOne_neg_one]
    ring

/-- **The comparison map onto the Witt ring.**  The value `-1` for `η` is forced by the sign in the
expansion of `⟨⟨uv⟩⟩`, and the Steinberg and hyperbolic relations then hold on the nose. -/
def milnorWittToWitt : MilnorWittK F →ₐ[ℤ] WittRing F :=
  RingQuot.liftAlgHom ℤ ⟨FreeAlgebra.lift ℤ (milnorWittToWittGen F), milnorWittToWitt_rel F⟩

@[simp]
theorem milnorWittToWitt_symbol (u : Fˣ) :
    milnorWittToWitt F (milnorWittSymbol u) = pfisterOne F u := by
  rw [milnorWittToWitt, milnorWittSymbol, milnorWittMk, RingQuot.liftAlgHom_mkAlgHom_apply]
  exact FreeAlgebra.lift_ι_apply _ _

@[simp]
theorem milnorWittToWitt_eta : milnorWittToWitt F (milnorWittEta F) = -1 := by
  rw [milnorWittToWitt, milnorWittEta, milnorWittMk, RingQuot.liftAlgHom_mkAlgHom_apply]
  exact FreeAlgebra.lift_ι_apply _ _

/-- **The comparison map lands in the fundamental ideal on symbols**, which is why the square
compares Milnor--Witt `K`-theory with the Pfister filtration rather than with the whole Witt ring. -/
theorem milnorWittToWitt_symbol_mem (u : Fˣ) :
    milnorWittToWitt F (milnorWittSymbol u) ∈ fundamentalIdeal F := by
  rw [milnorWittToWitt_symbol]
  exact pfisterOne_mem F u

/-- The one-fold Pfister form at `1` vanishes. -/
theorem pfisterOne_one : pfisterOne F 1 = 0 := by
  rw [pfisterOne, sub_self]

/-- The one-fold Pfister form read modulo the square of the fundamental ideal. -/
def pfisterMod2 (a : Fˣ) : WittRing F ⧸ fundamentalIdeal F ^ 2 :=
  Ideal.Quotient.mk (fundamentalIdeal F ^ 2) (pfisterOne F a)

@[simp]
theorem pfisterMod2_one : pfisterMod2 F 1 = 0 := by
  rw [pfisterMod2, pfisterOne_one, map_zero]

/-- **Additivity modulo the square of the fundamental ideal.** -/
theorem pfisterMod2_mul (a b : Fˣ) :
    pfisterMod2 F (a * b) = pfisterMod2 F a + pfisterMod2 F b := by
  rw [pfisterMod2, pfisterMod2, pfisterMod2, ← map_add, ← sub_eq_zero, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (pfisterOne_mul_sub_mem_sq F a b)

/-- **The first Milnor map** `Fˣ → I/I²`, sending a unit to its one-fold Pfister form.  This is the
degree-one bottom edge of the fundamental cartesian square. -/
def milnorFirstMap : Fˣ →* Multiplicative (WittRing F ⧸ fundamentalIdeal F ^ 2) where
  toFun a := Multiplicative.ofAdd (pfisterMod2 F a)
  map_one' := by
    show Multiplicative.ofAdd (pfisterMod2 F 1) = 1
    rw [pfisterMod2_one]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (pfisterMod2 F (a * b)) =
      Multiplicative.ofAdd (pfisterMod2 F a) * Multiplicative.ofAdd (pfisterMod2 F b)
    rw [pfisterMod2_mul]
    rfl

@[simp]
theorem milnorFirstMap_apply (a : Fˣ) :
    milnorFirstMap F a = Multiplicative.ofAdd (pfisterMod2 F a) := rfl

/-- **The fundamental square commutes on symbols.**  Sending a Milnor--Witt symbol down to the Witt
ring and then into `I/I²` gives the first Milnor map of the same unit, which is where the forgetful
morphism sends that symbol. -/
theorem square_commutes_on_symbol (u : Fˣ) :
    Ideal.Quotient.mk (fundamentalIdeal F ^ 2)
        (milnorWittToWitt F (milnorWittSymbol u)) = pfisterMod2 F u := by
  rw [milnorWittToWitt_symbol, pfisterMod2]

/-- The forgetful morphism sends the same symbol to the Milnor symbol, so the two composites of the
square agree on generators. -/
theorem square_forget_on_symbol (u : Fˣ) :
    milnorWittForget F (milnorWittSymbol u) = milnorSymbol u :=
  milnorWittForget_symbol u

/-! ### Higher Pfister forms -/

/-- The `n`-fold Pfister form of a list of units. -/
def pfisterList : List Fˣ → WittRing F
  | [] => 1
  | a :: l => pfisterOne F a * pfisterList l

@[simp]
theorem pfisterList_nil : pfisterList F [] = 1 := rfl

@[simp]
theorem pfisterList_cons (a : Fˣ) (l : List Fˣ) :
    pfisterList F (a :: l) = pfisterOne F a * pfisterList F l := rfl

/-- **An `n`-fold Pfister form lies in the `n`-th power of the fundamental ideal.** -/
theorem pfisterList_mem : ∀ l : List Fˣ,
    pfisterList F l ∈ fundamentalIdeal F ^ l.length
  | [] => by
    rw [pfisterList_nil, List.length_nil]
    have htop : fundamentalIdeal F ^ 0 = ⊤ := by simp
    rw [htop]
    exact Submodule.mem_top
  | a :: l => by
    rw [pfisterList_cons, List.length_cons]
    have hpow : fundamentalIdeal F ^ (l.length + 1) =
        fundamentalIdeal F ^ 1 * fundamentalIdeal F ^ l.length := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow, pow_one]
    exact Ideal.mul_mem_mul (pfisterOne_mem F a) (pfisterList_mem l)

/-- **The Steinberg relation for higher Pfister forms**: a form with two consecutive entries `a`
and `1 - a` vanishes. -/
theorem pfisterList_steinberg {a : Fˣ} (ha : (a : F) ≠ 1) (l : List Fˣ) :
    pfisterList F (a :: oneSubUnit ha :: l) = 0 := by
  rw [pfisterList_cons, pfisterList_cons, ← mul_assoc, pfisterOne_mul_oneSub F ha, zero_mul]

/-- **Additivity in the leading slot, modulo one more power of the fundamental ideal.**  Together
with the Steinberg vanishing this is the well-definedness of the degree-`n` comparison map from
Milnor `K`-theory to `I^n/I^{n+1}`. -/
theorem pfisterList_mul_slot (a b : Fˣ) (l : List Fˣ) :
    pfisterList F ((a * b) :: l) - (pfisterList F (a :: l) + pfisterList F (b :: l)) ∈
      fundamentalIdeal F ^ (l.length + 2) := by
  have hrw : pfisterList F ((a * b) :: l) -
      (pfisterList F (a :: l) + pfisterList F (b :: l)) =
      -(pfisterOne F a * pfisterOne F b * pfisterList F l) := by
    rw [pfisterList_cons, pfisterList_cons, pfisterList_cons, pfisterOne_mul]
    ring
  rw [hrw]
  refine neg_mem ?_
  have hpow : fundamentalIdeal F ^ (l.length + 2) =
      fundamentalIdeal F ^ 2 * fundamentalIdeal F ^ l.length := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  exact Ideal.mul_mem_mul (pfisterOne_mul_mem_sq F a b) (pfisterList_mem F l)

/-- The `n`-fold Pfister form as a product over the list. -/
theorem pfisterList_eq_prod : ∀ l : List Fˣ,
    pfisterList F l = (l.map (pfisterOne F)).prod
  | [] => by rw [pfisterList_nil, List.map_nil, List.prod_nil]
  | a :: l => by
    rw [pfisterList_cons, List.map_cons, List.prod_cons, pfisterList_eq_prod l]

/-- **The `n`-fold Pfister form only depends on the multiset of its entries.**  The Witt ring is
commutative, so reordering the entries does not change the form.  This is what turns the statements
about the leading entry into statements about an arbitrary slot. -/
theorem pfisterList_perm {l l' : List Fˣ} (h : l.Perm l') :
    pfisterList F l = pfisterList F l' := by
  rw [pfisterList_eq_prod, pfisterList_eq_prod]
  exact (h.map (pfisterOne F)).prod_eq

/-- **Steinberg vanishing at arbitrary positions**: a Pfister form whose entries include `a` and
`1 - a`, in any order and anywhere in the list, vanishes. -/
theorem pfisterList_eq_zero_of_perm {a : Fˣ} (ha : (a : F) ≠ 1) {l l' : List Fˣ}
    (h : l.Perm (a :: oneSubUnit ha :: l')) : pfisterList F l = 0 := by
  rw [pfisterList_perm F h, pfisterList_steinberg]

/-- **Slot additivity at an arbitrary position.**  Reorder the chosen slot to the front and apply
the leading-slot statement. -/
theorem pfisterList_mul_slot_perm (a b : Fˣ) {l la lb lab : List Fˣ}
    (hab : lab.Perm ((a * b) :: l)) (hla : la.Perm (a :: l)) (hlb : lb.Perm (b :: l)) :
    pfisterList F lab - (pfisterList F la + pfisterList F lb) ∈
      fundamentalIdeal F ^ (l.length + 2) := by
  rw [pfisterList_perm F hab, pfisterList_perm F hla, pfisterList_perm F hlb]
  exact pfisterList_mul_slot F a b l

/-- **Twice an `n`-fold Pfister form lies one power deeper.**  The reason is that `2` is itself a
one-fold Pfister form, namely `⟨⟨-1⟩⟩`. -/
theorem two_mul_pfisterList_mem (l : List Fˣ) :
    2 * pfisterList F l ∈ fundamentalIdeal F ^ (l.length + 1) := by
  have hpow : fundamentalIdeal F ^ (l.length + 1) =
      fundamentalIdeal F ^ 1 * fundamentalIdeal F ^ l.length := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, pow_one, ← pfisterOne_neg_one]
  exact Ideal.mul_mem_mul (pfisterOne_mem F (-1)) (pfisterList_mem F l)

/-- **The sign of graded commutativity is invisible modulo one further power.**  Milnor `K`-theory
is graded-commutative, so a transposition of two entries changes the sign of a symbol; the Pfister
form is genuinely commutative instead.  The two conventions agree modulo `I^{n+1}` because twice a
form already lies there.

With slot additivity and the Steinberg vanishing, this completes the relation checks a degree-`n`
comparison map `K_n^M(F) → I^n/I^{n+1}` has to satisfy. -/
theorem pfisterList_add_perm_mem {l l' : List Fˣ} (h : l.Perm l') :
    pfisterList F l + pfisterList F l' ∈ fundamentalIdeal F ^ (l.length + 1) := by
  have hsum : pfisterList F l + pfisterList F l' = 2 * pfisterList F l := by
    rw [← pfisterList_perm F h]
    ring
  rw [hsum]
  exact two_mul_pfisterList_mem F l

/-! ### The relations in the form the definition of `K_n^M` uses -/

/-- Moving an entry to the front does not change the form. -/
theorem pfisterList_middle (x : Fˣ) (l₁ l₂ : List Fˣ) :
    pfisterList F (l₁ ++ x :: l₂) = pfisterList F (x :: (l₁ ++ l₂)) :=
  pfisterList_perm F List.perm_middle

/-- **Slot additivity at an interior position**, in the shape the multilinearity relation of
`K_n^M` is stated in. -/
theorem pfisterList_mul_middle (a b : Fˣ) (l₁ l₂ : List Fˣ) :
    pfisterList F (l₁ ++ (a * b) :: l₂) -
        (pfisterList F (l₁ ++ a :: l₂) + pfisterList F (l₁ ++ b :: l₂)) ∈
      fundamentalIdeal F ^ ((l₁ ++ l₂).length + 2) := by
  rw [pfisterList_middle, pfisterList_middle, pfisterList_middle]
  exact pfisterList_mul_slot F a b (l₁ ++ l₂)

/-- **Steinberg vanishing at interior positions**, in the shape the Steinberg relation of `K_n^M`
is stated in. -/
theorem pfisterList_steinberg_middle {a : Fˣ} (ha : (a : F) ≠ 1) (l₁ l₂ : List Fˣ) :
    pfisterList F (l₁ ++ a :: oneSubUnit ha :: l₂) = 0 := by
  refine pfisterList_eq_zero_of_perm F ha (l' := l₁ ++ l₂) ?_
  exact List.Perm.trans List.perm_middle (List.Perm.cons a List.perm_middle)

/-! ### The comparison map on formal sums of symbols -/

/-- The additive map on formal sums of symbols, landing in `W(F)/I^m`. -/
def pfisterLift (m : ℕ) :
    FreeAbelianGroup (List Fˣ) →+ (WittRing F ⧸ fundamentalIdeal F ^ m) :=
  FreeAbelianGroup.lift fun l => Ideal.Quotient.mk (fundamentalIdeal F ^ m) (pfisterList F l)

@[simp]
theorem pfisterLift_of (m : ℕ) (l : List Fˣ) :
    pfisterLift F m (FreeAbelianGroup.of l) =
      Ideal.Quotient.mk (fundamentalIdeal F ^ m) (pfisterList F l) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The multilinearity relation is killed.**  In degree `n` the target is `W(F)/I^{n+1}`, and the
defect of additivity in a slot lies in `I^{n+1}`. -/
theorem pfisterLift_mul_relation (a b : Fˣ) (l₁ l₂ : List Fˣ) :
    pfisterLift F ((l₁ ++ l₂).length + 2)
        (FreeAbelianGroup.of (l₁ ++ (a * b) :: l₂) - FreeAbelianGroup.of (l₁ ++ a :: l₂) -
          FreeAbelianGroup.of (l₁ ++ b :: l₂)) = 0 := by
  rw [map_sub, map_sub, pfisterLift_of, pfisterLift_of, pfisterLift_of, ← map_sub, ← map_sub]
  refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
  have hrw : pfisterList F (l₁ ++ (a * b) :: l₂) - pfisterList F (l₁ ++ a :: l₂) -
      pfisterList F (l₁ ++ b :: l₂) =
      pfisterList F (l₁ ++ (a * b) :: l₂) -
        (pfisterList F (l₁ ++ a :: l₂) + pfisterList F (l₁ ++ b :: l₂)) := by ring
  rw [hrw]
  exact pfisterList_mul_middle F a b l₁ l₂

/-- **The Steinberg relation is killed**, in every degree. -/
theorem pfisterLift_steinberg_relation {a : Fˣ} (ha : (a : F) ≠ 1) (l₁ l₂ : List Fˣ) (m : ℕ) :
    pfisterLift F m (FreeAbelianGroup.of (l₁ ++ a :: oneSubUnit ha :: l₂)) = 0 := by
  rw [pfisterLift_of, pfisterList_steinberg_middle, map_zero]

/-- **The comparison map is well defined on the defining relations of Milnor `K`-theory.**  Both
relation families lie in the kernel, so the assignment `{a₁,…,aₙ} ↦ ⟨⟨a₁,…,aₙ⟩⟩ mod I^{n+1}`
descends to any quotient of the free abelian group on symbols by those relations. -/
theorem pfisterLift_kills_relations (a b : Fˣ) (l₁ l₂ : List Fˣ)
    {c : Fˣ} (hc : (c : F) ≠ 1) (l₃ l₄ : List Fˣ) (m : ℕ) :
    pfisterLift F ((l₁ ++ l₂).length + 2)
        (FreeAbelianGroup.of (l₁ ++ (a * b) :: l₂) - FreeAbelianGroup.of (l₁ ++ a :: l₂) -
          FreeAbelianGroup.of (l₁ ++ b :: l₂)) = 0 ∧
      pfisterLift F m (FreeAbelianGroup.of (l₃ ++ c :: oneSubUnit hc :: l₄)) = 0 :=
  ⟨pfisterLift_mul_relation F a b l₁ l₂, pfisterLift_steinberg_relation F hc l₃ l₄ m⟩

/-! ### Milnor `K`-theory in degree `n`, and the comparison map -/

theorem length_middle (x : Fˣ) (l₁ l₂ : List Fˣ) :
    (l₁ ++ x :: l₂).length = (l₁ ++ l₂).length + 1 := by
  simp [List.length_append]
  omega

/-- Symbols of degree `n`: lists of exactly `n` units. -/
def MilnorSymbolDeg (n : ℕ) : Type _ := {l : List Fˣ // l.length = n}

/-- The defining relations of Milnor `K`-theory on symbols of degree `n`. -/
def milnorRelSubgroupDeg (n : ℕ) : AddSubgroup (FreeAbelianGroup (MilnorSymbolDeg F n)) :=
  AddSubgroup.closure
    ({x | ∃ (a b : Fˣ) (l₁ l₂ : List Fˣ) (h : (l₁ ++ l₂).length + 1 = n),
        x = FreeAbelianGroup.of ⟨l₁ ++ (a * b) :: l₂, by rw [length_middle]; exact h⟩ -
          FreeAbelianGroup.of ⟨l₁ ++ a :: l₂, by rw [length_middle]; exact h⟩ -
          FreeAbelianGroup.of ⟨l₁ ++ b :: l₂, by rw [length_middle]; exact h⟩} ∪
      {x | ∃ (a : Fˣ) (ha : (a : F) ≠ 1) (l₁ l₂ : List Fˣ)
          (h : (l₁ ++ l₂).length + 2 = n),
        x = FreeAbelianGroup.of ⟨l₁ ++ a :: oneSubUnit ha :: l₂, by
          rw [length_middle, length_middle]; exact h⟩})

/-- **Milnor `K`-theory in degree `n`**: formal sums of symbols of length `n`, modulo
multilinearity in each slot and the Steinberg relation. -/
def MilnorKDeg (n : ℕ) : Type _ :=
  FreeAbelianGroup (MilnorSymbolDeg F n) ⧸ milnorRelSubgroupDeg F n

instance (n : ℕ) : AddCommGroup (MilnorKDeg F n) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- The class of a symbol of degree `n`. -/
def milnorClassDeg (n : ℕ) (s : MilnorSymbolDeg F n) : MilnorKDeg F n :=
  QuotientAddGroup.mk (FreeAbelianGroup.of s)

/-- The class of a symbol depends only on the underlying list. -/
theorem milnorClassDeg_congr {n : ℕ} {l l' : List Fˣ} (hl : l.length = n) (hl' : l'.length = n)
    (h : l = l') : milnorClassDeg F n ⟨l, hl⟩ = milnorClassDeg F n ⟨l', hl'⟩ :=
  congrArg _ (Subtype.ext h)

/-- **Multilinearity at an interior slot, read in the quotient.**  The three lists are given up to
an equality so that the lemma applies after any reassociation of the surrounding concatenation. -/
theorem milnorClassDeg_mul_of_eq {n : ℕ} (a b : Fˣ) (l₁ l₂ : List Fˣ)
    {Lab La Lb : List Fˣ} (hab : Lab = l₁ ++ (a * b) :: l₂) (ha : La = l₁ ++ a :: l₂)
    (hb : Lb = l₁ ++ b :: l₂)
    (pab : Lab.length = n) (pa : La.length = n) (pb : Lb.length = n) :
    milnorClassDeg F n ⟨Lab, pab⟩ =
      milnorClassDeg F n ⟨La, pa⟩ + milnorClassDeg F n ⟨Lb, pb⟩ := by
  subst hab
  subst ha
  subst hb
  have h : (l₁ ++ l₂).length + 1 = n := by rw [← pab, length_middle]
  have hmem : (FreeAbelianGroup.of
        (⟨l₁ ++ (a * b) :: l₂, by rw [length_middle]; exact h⟩ : MilnorSymbolDeg F n) -
      FreeAbelianGroup.of (⟨l₁ ++ a :: l₂, by rw [length_middle]; exact h⟩ :
        MilnorSymbolDeg F n) -
      FreeAbelianGroup.of (⟨l₁ ++ b :: l₂, by rw [length_middle]; exact h⟩ :
        MilnorSymbolDeg F n)) ∈ milnorRelSubgroupDeg F n :=
    AddSubgroup.subset_closure (Or.inl ⟨a, b, l₁, l₂, h, rfl⟩)
  have h0 : (QuotientAddGroup.mk' (milnorRelSubgroupDeg F n))
        (FreeAbelianGroup.of
          (⟨l₁ ++ (a * b) :: l₂, by rw [length_middle]; exact h⟩ : MilnorSymbolDeg F n)) -
      (QuotientAddGroup.mk' (milnorRelSubgroupDeg F n))
        (FreeAbelianGroup.of (⟨l₁ ++ a :: l₂, by rw [length_middle]; exact h⟩ :
          MilnorSymbolDeg F n)) -
      (QuotientAddGroup.mk' (milnorRelSubgroupDeg F n))
        (FreeAbelianGroup.of (⟨l₁ ++ b :: l₂, by rw [length_middle]; exact h⟩ :
          MilnorSymbolDeg F n)) = 0 := by
    rw [← map_sub, ← map_sub]
    exact (QuotientAddGroup.eq_zero_iff _).2 hmem
  rw [sub_sub, sub_eq_zero] at h0
  exact h0

/-- **The Steinberg relation, read in the quotient**, with the list given up to an equality. -/
theorem milnorClassDeg_steinberg_of_eq {n : ℕ} {a : Fˣ} (ha : (a : F) ≠ 1) (l₁ l₂ : List Fˣ)
    {L : List Fˣ} (hL : L = l₁ ++ a :: oneSubUnit ha :: l₂) (pL : L.length = n) :
    milnorClassDeg F n ⟨L, pL⟩ = 0 := by
  subst hL
  have h : (l₁ ++ l₂).length + 2 = n := by rw [← pL, length_middle, length_middle]
  exact (QuotientAddGroup.eq_zero_iff _).2
    (AddSubgroup.subset_closure (Or.inr ⟨a, ha, l₁, l₂, h, rfl⟩))

/-- **Extensionality for `K_n^M`**: two additive maps out of it agree as soon as they agree on the
classes of symbols, which generate. -/
theorem milnorKDeg_hom_ext {A : Type*} [AddCommGroup A] {n : ℕ} {f g : MilnorKDeg F n →+ A}
    (h : ∀ s : MilnorSymbolDeg F n, f (milnorClassDeg F n s) = g (milnorClassDeg F n s)) :
    f = g := by
  refine AddMonoidHom.ext fun x => ?_
  refine QuotientAddGroup.induction_on x fun w => ?_
  induction w using FreeAbelianGroup.induction_on with
  | zero =>
    show f (0 : MilnorKDeg F n) = g 0
    rw [map_zero, map_zero]
  | of s => exact h s
  | neg s ih =>
    have hmk : (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) (-FreeAbelianGroup.of s)) =
        -(QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) (FreeAbelianGroup.of s)) := rfl
    have hf : f (-(QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n)
          (FreeAbelianGroup.of s))) =
        -f (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) (FreeAbelianGroup.of s)) :=
      map_neg _ _
    have hg : g (-(QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n)
          (FreeAbelianGroup.of s))) =
        -g (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) (FreeAbelianGroup.of s)) :=
      map_neg _ _
    rw [hmk, hf, hg, ih]
  | add u v hu hv =>
    have hmk : (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) (u + v)) =
        QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) u +
          QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) v := rfl
    have hf : f (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) u +
          QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) v) =
        f (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) u) +
          f (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) v) := map_add _ _ _
    have hg : g (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) u +
          QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) v) =
        g (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) u) +
          g (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F n) v) := map_add _ _ _
    rw [hmk, hf, hg, hu, hv]

/-- The Pfister lift on symbols of a fixed degree. -/
def pfisterLiftDeg (n : ℕ) :
    FreeAbelianGroup (MilnorSymbolDeg F n) →+ (WittRing F ⧸ fundamentalIdeal F ^ (n + 1)) :=
  FreeAbelianGroup.lift fun s =>
    Ideal.Quotient.mk (fundamentalIdeal F ^ (n + 1)) (pfisterList F s.val)

@[simp]
theorem pfisterLiftDeg_of (n : ℕ) (s : MilnorSymbolDeg F n) :
    pfisterLiftDeg F n (FreeAbelianGroup.of s) =
      Ideal.Quotient.mk (fundamentalIdeal F ^ (n + 1)) (pfisterList F s.val) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The defining relations lie in the kernel of the Pfister lift.** -/
theorem milnorRelSubgroupDeg_le_ker (n : ℕ) :
    milnorRelSubgroupDeg F n ≤ (pfisterLiftDeg F n).ker := by
  rw [milnorRelSubgroupDeg, AddSubgroup.closure_le]
  rintro x (⟨a, b, l₁, l₂, h, rfl⟩ | ⟨a, ha, l₁, l₂, h, rfl⟩)
  · show pfisterLiftDeg F n _ = 0
    rw [map_sub, map_sub, pfisterLiftDeg_of, pfisterLiftDeg_of, pfisterLiftDeg_of,
      ← map_sub, ← map_sub]
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    have hrw : pfisterList F (l₁ ++ (a * b) :: l₂) - pfisterList F (l₁ ++ a :: l₂) -
        pfisterList F (l₁ ++ b :: l₂) =
        pfisterList F (l₁ ++ (a * b) :: l₂) -
          (pfisterList F (l₁ ++ a :: l₂) + pfisterList F (l₁ ++ b :: l₂)) := by ring
    rw [hrw]
    have hmem := pfisterList_mul_middle F a b l₁ l₂
    have hn : (l₁ ++ l₂).length + 2 = n + 1 := by omega
    rwa [hn] at hmem
  · show pfisterLiftDeg F n _ = 0
    rw [pfisterLiftDeg_of]
    show Ideal.Quotient.mk _ (pfisterList F (l₁ ++ a :: oneSubUnit ha :: l₂)) = 0
    rw [pfisterList_steinberg_middle, map_zero]

/-- **The degree-`n` comparison map** `K_n^M(F) → W(F)/I^{n+1}`.  Its existence is the bottom edge
of the fundamental cartesian square. -/
def milnorPfisterMap (n : ℕ) :
    MilnorKDeg F n →+ (WittRing F ⧸ fundamentalIdeal F ^ (n + 1)) :=
  QuotientAddGroup.lift _ (pfisterLiftDeg F n) (milnorRelSubgroupDeg_le_ker F n)

@[simp]
theorem milnorPfisterMap_class (n : ℕ) (s : MilnorSymbolDeg F n) :
    milnorPfisterMap F n (milnorClassDeg F n s) =
      Ideal.Quotient.mk (fundamentalIdeal F ^ (n + 1)) (pfisterList F s.val) := by
  show pfisterLiftDeg F n (FreeAbelianGroup.of s) = _
  rw [pfisterLiftDeg_of]

/-! ### Commutativity of the fundamental square -/

/-- The product of Milnor--Witt symbols along a list. -/
def milnorWittSymbolList : List Fˣ → MilnorWittK F
  | [] => 1
  | a :: l => milnorWittSymbol a * milnorWittSymbolList l

@[simp]
theorem milnorWittSymbolList_nil : milnorWittSymbolList F [] = 1 := rfl

@[simp]
theorem milnorWittSymbolList_cons (a : Fˣ) (l : List Fˣ) :
    milnorWittSymbolList F (a :: l) = milnorWittSymbol a * milnorWittSymbolList F l := rfl

/-- The product of Milnor symbols along a list. -/
def milnorSymbolList : List Fˣ → MilnorK F
  | [] => 1
  | a :: l => milnorSymbol a * milnorSymbolList l

/-- **The comparison map carries a product of symbols to the Pfister form.** -/
theorem milnorWittToWitt_symbolList : ∀ l : List Fˣ,
    milnorWittToWitt F (milnorWittSymbolList F l) = pfisterList F l
  | [] => by
    rw [milnorWittSymbolList_nil, map_one, pfisterList_nil]
  | a :: l => by
    rw [milnorWittSymbolList_cons, map_mul, milnorWittToWitt_symbol, pfisterList_cons,
      milnorWittToWitt_symbolList l]

/-- **The forgetful morphism carries a product of Milnor--Witt symbols to the Milnor symbol
product.** -/
theorem milnorWittForget_symbolList : ∀ l : List Fˣ,
    milnorWittForget F (milnorWittSymbolList F l) = milnorSymbolList F l
  | [] => by
    rw [milnorWittSymbolList_nil, map_one]
    rfl
  | a :: l => by
    rw [milnorWittSymbolList_cons, map_mul, milnorWittForget_symbol,
      milnorWittForget_symbolList l]
    rfl

/-- **The fundamental square commutes on products of symbols.**  Sending a product of Milnor--Witt
symbols down to the Witt ring and projecting into `W(F)/I^{n+1}` gives the same class as sending it
across to Milnor `K`-theory and applying the degree-`n` comparison map.  Both routes produce the
Pfister form of the same list. -/
theorem square_commutes (n : ℕ) (s : MilnorSymbolDeg F n) :
    Ideal.Quotient.mk (fundamentalIdeal F ^ (n + 1))
        (milnorWittToWitt F (milnorWittSymbolList F s.val)) =
      milnorPfisterMap F n (milnorClassDeg F n s) := by
  rw [milnorWittToWitt_symbolList, milnorPfisterMap_class]

/-! ### The first Milnor `K`-group -/

/-- The unit underlying a degree-one symbol. -/
def degOneUnit (s : MilnorSymbolDeg F 1) : Fˣ := s.val.headI

theorem degOneUnit_spec (s : MilnorSymbolDeg F 1) : s.val = [degOneUnit F s] := by
  rcases s with ⟨l, hl⟩
  match l, hl with
  | [_], _ => rfl

/-- The map sending a degree-one symbol to its unit. -/
def milnorDegOneLift : FreeAbelianGroup (MilnorSymbolDeg F 1) →+ Additive Fˣ :=
  FreeAbelianGroup.lift fun s => Additive.ofMul (degOneUnit F s)

@[simp]
theorem milnorDegOneLift_of (s : MilnorSymbolDeg F 1) :
    milnorDegOneLift F (FreeAbelianGroup.of s) = Additive.ofMul (degOneUnit F s) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **In degree one there are no Steinberg relations**, and multilinearity is exactly the
multiplicativity of the unit group. -/
theorem milnorDegOneLift_ker : milnorRelSubgroupDeg F 1 ≤ (milnorDegOneLift F).ker := by
  rw [milnorRelSubgroupDeg, AddSubgroup.closure_le]
  rintro x (⟨a, b, l₁, l₂, h, rfl⟩ | ⟨a, ha, l₁, l₂, h, rfl⟩)
  · rw [List.length_append] at h
    have hl₁ : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hl₂ : l₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hl₁
    subst hl₂
    show milnorDegOneLift F _ = 0
    rw [map_sub, map_sub, milnorDegOneLift_of, milnorDegOneLift_of, milnorDegOneLift_of]
    show Additive.ofMul (a * b) - Additive.ofMul a - Additive.ofMul b = 0
    have hmul : Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b := rfl
    rw [hmul]
    abel
  · rw [List.length_append] at h
    exact absurd h (by omega)

/-- The comparison of the first Milnor `K`-group with the unit group. -/
def milnorDegOneHom : MilnorKDeg F 1 →+ Additive Fˣ :=
  QuotientAddGroup.lift _ (milnorDegOneLift F) (milnorDegOneLift_ker F)

@[simp]
theorem milnorDegOneHom_class (s : MilnorSymbolDeg F 1) :
    milnorDegOneHom F (milnorClassDeg F 1 s) = Additive.ofMul (degOneUnit F s) := by
  show milnorDegOneLift F (FreeAbelianGroup.of s) = _
  rw [milnorDegOneLift_of]

/-- **Additivity of the degree-one class map**: the multilinearity relation, read in the
quotient. -/
theorem milnorClassDeg_one_mul (a b : Fˣ) :
    milnorClassDeg F 1 ⟨[a * b], rfl⟩ =
      milnorClassDeg F 1 ⟨[a], rfl⟩ + milnorClassDeg F 1 ⟨[b], rfl⟩ := by
  have hmem : (FreeAbelianGroup.of (⟨[a * b], rfl⟩ : MilnorSymbolDeg F 1) -
      FreeAbelianGroup.of (⟨[a], rfl⟩ : MilnorSymbolDeg F 1) -
      FreeAbelianGroup.of (⟨[b], rfl⟩ : MilnorSymbolDeg F 1)) ∈ milnorRelSubgroupDeg F 1 :=
    AddSubgroup.subset_closure (Or.inl ⟨a, b, [], [], rfl, rfl⟩)
  have h0 : (QuotientAddGroup.mk' (milnorRelSubgroupDeg F 1))
        (FreeAbelianGroup.of (⟨[a * b], rfl⟩ : MilnorSymbolDeg F 1)) -
      (QuotientAddGroup.mk' (milnorRelSubgroupDeg F 1))
        (FreeAbelianGroup.of (⟨[a], rfl⟩ : MilnorSymbolDeg F 1)) -
      (QuotientAddGroup.mk' (milnorRelSubgroupDeg F 1))
        (FreeAbelianGroup.of (⟨[b], rfl⟩ : MilnorSymbolDeg F 1)) = 0 := by
    rw [← map_sub, ← map_sub]
    exact (QuotientAddGroup.eq_zero_iff _).2 hmem
  rw [sub_sub, sub_eq_zero] at h0
  exact h0

/-- The section of the degree-one comparison, sending a unit to its symbol. -/
def milnorDegOneInv : Additive Fˣ →+ MilnorKDeg F 1 :=
  AddMonoidHom.mk' (fun a => milnorClassDeg F 1 ⟨[Additive.toMul a], rfl⟩)
    fun a b => milnorClassDeg_one_mul F (Additive.toMul a) (Additive.toMul b)

@[simp]
theorem milnorDegOneInv_apply (a : Fˣ) :
    milnorDegOneInv F (Additive.ofMul a) = milnorClassDeg F 1 ⟨[a], rfl⟩ := rfl

/-- **The degree-one comparison is split surjective**: the section sends a unit to its symbol, and
reading the unit off that symbol returns it.  So `K_1^M(F)` surjects onto the unit group with an
explicit section. -/
theorem milnorDegOneHom_inv (a : Additive Fˣ) :
    milnorDegOneHom F (milnorDegOneInv F a) = a := by
  show milnorDegOneHom F (milnorClassDeg F 1 ⟨[Additive.toMul a], rfl⟩) = a
  rw [milnorDegOneHom_class]
  rfl

theorem milnorDegOneHom_surjective : Function.Surjective (milnorDegOneHom F) :=
  fun a => ⟨milnorDegOneInv F a, milnorDegOneHom_inv F a⟩

theorem milnorDegOneInv_hom_class (s : MilnorSymbolDeg F 1) :
    milnorDegOneInv F (milnorDegOneHom F (milnorClassDeg F 1 s)) = milnorClassDeg F 1 s := by
  rw [milnorDegOneHom_class, milnorDegOneInv_apply]
  congr 1
  exact Subtype.ext (degOneUnit_spec F s).symm

theorem milnorDegOneInv_hom (x : MilnorKDeg F 1) :
    milnorDegOneInv F (milnorDegOneHom F x) = x := by
  refine QuotientAddGroup.induction_on x fun w => ?_
  induction w using FreeAbelianGroup.induction_on with
  | zero =>
    show milnorDegOneInv F (milnorDegOneHom F (0 : MilnorKDeg F 1)) = 0
    rw [map_zero, map_zero]
  | of s => exact milnorDegOneInv_hom_class F s
  | neg s ih =>
    show milnorDegOneInv F (milnorDegOneHom F (-(milnorClassDeg F 1 s))) =
      -(milnorClassDeg F 1 s)
    rw [map_neg, map_neg, milnorDegOneInv_hom_class]
  | add u v hu hv =>
    have hmk : (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) (u + v)) =
        QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) u +
          QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) v := rfl
    have h1 : milnorDegOneHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) u +
          QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) v) =
        milnorDegOneHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) u) +
          milnorDegOneHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) v) :=
      map_add _ _ _
    have h2 : milnorDegOneInv F
          (milnorDegOneHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) u) +
            milnorDegOneHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) v)) =
        milnorDegOneInv F
            (milnorDegOneHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) u)) +
          milnorDegOneInv F
            (milnorDegOneHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 1) v)) :=
      map_add _ _ _
    rw [hmk, h1, h2, hu, hv]
    rfl

/-- **`K_1^M(F) ≅ Fˣ`.**  In degree one the Steinberg relations are vacuous and multilinearity is
exactly the multiplicativity of the unit group, so the first Milnor `K`-group is the unit group
written additively. -/
def milnorDegOneEquiv : MilnorKDeg F 1 ≃+ Additive Fˣ where
  toFun := milnorDegOneHom F
  invFun := milnorDegOneInv F
  left_inv := milnorDegOneInv_hom F
  right_inv := milnorDegOneHom_inv F
  map_add' := map_add _

@[simp]
theorem milnorDegOneEquiv_class (s : MilnorSymbolDeg F 1) :
    milnorDegOneEquiv F (milnorClassDeg F 1 s) = Additive.ofMul (degOneUnit F s) :=
  milnorDegOneHom_class F s

/-! ### The zeroth Milnor `K`-group -/

theorem milnorSymbolDegZero_eq (s : MilnorSymbolDeg F 0) :
    s = (⟨[], rfl⟩ : MilnorSymbolDeg F 0) :=
  Subtype.ext (List.eq_nil_of_length_eq_zero s.property)

/-- Counting symbols, before passing to the quotient. -/
def milnorDegZeroLift : FreeAbelianGroup (MilnorSymbolDeg F 0) →+ ℤ :=
  FreeAbelianGroup.lift fun _ => (1 : ℤ)

@[simp]
theorem milnorDegZeroLift_of (s : MilnorSymbolDeg F 0) :
    milnorDegZeroLift F (FreeAbelianGroup.of s) = 1 :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **In degree zero both relation families are vacuous**: their index conditions ask for a list of
negative length. -/
theorem milnorDegZeroLift_ker : milnorRelSubgroupDeg F 0 ≤ (milnorDegZeroLift F).ker := by
  rw [milnorRelSubgroupDeg, AddSubgroup.closure_le]
  rintro x (⟨a, b, l₁, l₂, h, rfl⟩ | ⟨a, ha, l₁, l₂, h, rfl⟩)
  · exact absurd h (by omega)
  · exact absurd h (by omega)

/-- The rank of a degree-zero Milnor class. -/
def milnorDegZeroHom : MilnorKDeg F 0 →+ ℤ :=
  QuotientAddGroup.lift _ (milnorDegZeroLift F) (milnorDegZeroLift_ker F)

@[simp]
theorem milnorDegZeroHom_class (s : MilnorSymbolDeg F 0) :
    milnorDegZeroHom F (milnorClassDeg F 0 s) = 1 := by
  show milnorDegZeroLift F (FreeAbelianGroup.of s) = 1
  rw [milnorDegZeroLift_of]

/-- The inverse, sending `n` to `n` copies of the empty symbol. -/
def milnorDegZeroInv : ℤ →+ MilnorKDeg F 0 :=
  zmultiplesHom (MilnorKDeg F 0) (milnorClassDeg F 0 ⟨[], rfl⟩)

theorem milnorDegZeroHom_inv (n : ℤ) : milnorDegZeroHom F (milnorDegZeroInv F n) = n := by
  show milnorDegZeroHom F (n • milnorClassDeg F 0 ⟨[], rfl⟩) = n
  rw [map_zsmul, milnorDegZeroHom_class, smul_eq_mul, mul_one]

theorem milnorDegZeroInv_hom (x : MilnorKDeg F 0) :
    milnorDegZeroInv F (milnorDegZeroHom F x) = x := by
  refine QuotientAddGroup.induction_on x fun w => ?_
  induction w using FreeAbelianGroup.induction_on with
  | zero =>
    show milnorDegZeroInv F (milnorDegZeroHom F (0 : MilnorKDeg F 0)) = 0
    rw [map_zero, map_zero]
  | of s =>
    rw [milnorSymbolDegZero_eq F s]
    show milnorDegZeroInv F (milnorDegZeroHom F (milnorClassDeg F 0 ⟨[], rfl⟩)) = _
    rw [milnorDegZeroHom_class]
    show (1 : ℤ) • milnorClassDeg F 0 ⟨[], rfl⟩ = _
    rw [one_zsmul]
    rfl
  | neg s ih =>
    have hmk : (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0)
          (-FreeAbelianGroup.of s)) =
        -(QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) (FreeAbelianGroup.of s)) := rfl
    have h1 : milnorDegZeroHom F (-(QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0)
          (FreeAbelianGroup.of s))) =
        -milnorDegZeroHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0)
          (FreeAbelianGroup.of s)) := map_neg _ _
    have h2 : milnorDegZeroInv F (-milnorDegZeroHom F
          (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) (FreeAbelianGroup.of s))) =
        -milnorDegZeroInv F (milnorDegZeroHom F
          (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) (FreeAbelianGroup.of s))) :=
      map_neg _ _
    rw [hmk, h1, h2, ih]
    rfl
  | add u v hu hv =>
    have hmk : (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) (u + v)) =
        QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) u +
          QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) v := rfl
    have h1 : milnorDegZeroHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) u +
          QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) v) =
        milnorDegZeroHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) u) +
          milnorDegZeroHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) v) :=
      map_add _ _ _
    have h2 : milnorDegZeroInv F
          (milnorDegZeroHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) u) +
            milnorDegZeroHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) v)) =
        milnorDegZeroInv F
            (milnorDegZeroHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) u)) +
          milnorDegZeroInv F
            (milnorDegZeroHom F (QuotientAddGroup.mk (s := milnorRelSubgroupDeg F 0) v)) :=
      map_add _ _ _
    rw [hmk, h1, h2, hu, hv]
    rfl

/-- **`K_0^M(F) ≅ ℤ`.**  In degree zero there is one symbol, the empty one, and no relations at all:
both relation families ask for a list of negative length. -/
def milnorDegZeroEquiv : MilnorKDeg F 0 ≃+ ℤ where
  toFun := milnorDegZeroHom F
  invFun := milnorDegZeroInv F
  left_inv := milnorDegZeroInv_hom F
  right_inv := milnorDegZeroHom_inv F
  map_add' := map_add _

end Comparison

end

end GaloisForLFunctions.HTGeometry
