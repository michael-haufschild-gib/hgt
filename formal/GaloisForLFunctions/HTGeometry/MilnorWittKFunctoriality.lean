import GaloisForLFunctions.HTGeometry.MilnorWittGradedOperations
import GaloisForLFunctions.HTGeometry.MilnorKFunctoriality

/-!
# Functoriality of graded Milnor--Witt `K`-theory

A field homomorphism acts entrywise on the words `η^k[a_1]⋯[a_m]`, leaving the `η`-exponent and the
length alone, so it preserves the degree.  It carries each of the three defining relation families
to itself: the Steinberg relation because `f(1 - a) = 1 - f(a)`, twisted multiplicativity because
`f` is multiplicative on units, and the hyperbolic relation because `f(-1) = -1`.  Hence it descends
to every graded piece, compatibly with the product and with multiplication by `η`.

* `mwKDegMap` : **the map on `K_n^{MW}` induced by a field homomorphism.**
* `mwKDegMap_id`, `mwKDegMap_comp` : functoriality.
* `mwKDegMap_mul` : **the induced map is multiplicative for the graded product.**
* `mwKDegMap_etaMul` : the induced map commutes with multiplication by `η`.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWittFunctoriality

variable {F E G : Type*} [Field F] [Field E] [Field G]

/-- A field homomorphism carries the unit `-1` to the unit `-1`. -/
theorem milnorUnitMap_neg_one (f : F →+* E) : milnorUnitMap f (-1 : Fˣ) = (-1 : Eˣ) := by
  refine Units.ext ?_
  rw [milnorUnitMap_val]
  show f (-1 : F) = (-1 : E)
  rw [map_neg, map_one]

/-- The entrywise image of a word under a field homomorphism. -/
def mwWordDegMap (f : F →+* E) (n : ℤ) (w : MWWordDeg F n) : MWWordDeg E n :=
  ⟨(w.val.1, w.val.2.map (milnorUnitMap f)), by
    rw [List.length_map]; exact w.property⟩

@[simp]
theorem mwWordDegMap_fst (f : F →+* E) (n : ℤ) (w : MWWordDeg F n) :
    (mwWordDegMap f n w).val.1 = w.val.1 := rfl

@[simp]
theorem mwWordDegMap_snd (f : F →+* E) (n : ℤ) (w : MWWordDeg F n) :
    (mwWordDegMap f n w).val.2 = w.val.2.map (milnorUnitMap f) := rfl

/-- The induced map on formal sums of words. -/
def mwKDegPreMap (f : F →+* E) (n : ℤ) :
    FreeAbelianGroup (MWWordDeg F n) →+ MilnorWittKDeg E n :=
  FreeAbelianGroup.lift fun w => mwClassDeg E n (mwWordDegMap f n w)

@[simp]
theorem mwKDegPreMap_of (f : F →+* E) (n : ℤ) (w : MWWordDeg F n) :
    mwKDegPreMap f n (FreeAbelianGroup.of w) = mwClassDeg E n (mwWordDegMap f n w) := by
  rw [mwKDegPreMap, FreeAbelianGroup.lift_apply_of]

/-- **The three relation families are preserved.** -/
theorem mwKDegPreMap_rel (f : F →+* E) (n : ℤ) : mwRelDeg F n ≤ (mwKDegPreMap f n).ker := by
  rw [mwRelDeg, AddSubgroup.closure_le]
  rintro x ((⟨k, a, ha, l₁, l₂, h, rfl⟩ | ⟨k, a, b, l₁, l₂, hab, hpa, hpb, hpe, rfl⟩) |
    ⟨k, l₁, l₂, h1, h2, rfl⟩)
  · show mwKDegPreMap f n _ = 0
    rw [mwKDegPreMap_of]
    refine mwClassDeg_steinberg k (milnorUnitMap_ne_one f ha) (l₁.map (milnorUnitMap f))
      (l₂.map (milnorUnitMap f)) ?_ _
    show (l₁ ++ a :: oneSubUnit ha :: l₂).map (milnorUnitMap f) = _
    rw [List.map_append, List.map_cons, List.map_cons, milnorUnitMap_oneSubUnit]
  · show mwKDegPreMap f n _ = 0
    rw [map_sub, map_sub, map_sub, mwKDegPreMap_of, mwKDegPreMap_of, mwKDegPreMap_of,
      mwKDegPreMap_of, sub_sub, sub_sub, sub_eq_zero]
    refine Eq.trans ?_ (add_assoc _ _ _)
    refine mwClassDeg_twisted k (milnorUnitMap f a) (milnorUnitMap f b)
      (l₁.map (milnorUnitMap f)) (l₂.map (milnorUnitMap f)) ?_ ?_ ?_ ?_ _ _ _ _
    · show (l₁ ++ (a * b) :: l₂).map (milnorUnitMap f) = _
      rw [List.map_append, List.map_cons, map_mul]
    · show (l₁ ++ a :: l₂).map (milnorUnitMap f) = _
      rw [List.map_append, List.map_cons]
    · show (l₁ ++ b :: l₂).map (milnorUnitMap f) = _
      rw [List.map_append, List.map_cons]
    · show (l₁ ++ a :: b :: l₂).map (milnorUnitMap f) = _
      rw [List.map_append, List.map_cons, List.map_cons]
  · show mwKDegPreMap f n _ = 0
    rw [map_add, map_add, mwKDegPreMap_of, mwKDegPreMap_of, add_assoc]
    refine mwClassDeg_hyperbolic k (l₁.map (milnorUnitMap f)) (l₂.map (milnorUnitMap f)) ?_ ?_ _ _
    · show (l₁ ++ (-1 : Fˣ) :: l₂).map (milnorUnitMap f) = _
      rw [List.map_append, List.map_cons, milnorUnitMap_neg_one]
    · show (l₁ ++ l₂).map (milnorUnitMap f) = _
      rw [List.map_append]

/-- **The map on `K_n^{MW}` induced by a field homomorphism.** -/
def mwKDegMap (f : F →+* E) (n : ℤ) : MilnorWittKDeg F n →+ MilnorWittKDeg E n :=
  QuotientAddGroup.lift _ (mwKDegPreMap f n) (mwKDegPreMap_rel f n)

@[simp]
theorem mwKDegMap_class (f : F →+* E) (n : ℤ) (w : MWWordDeg F n) :
    mwKDegMap f n (mwClassDeg F n w) = mwClassDeg E n (mwWordDegMap f n w) := by
  show mwKDegPreMap f n (FreeAbelianGroup.of w) = _
  rw [mwKDegPreMap_of]

end MilnorWittFunctoriality

section Functorial

variable {F E G : Type*} [Field F] [Field E] [Field G]

theorem mwWordDegMap_id {n : ℤ} (w : MWWordDeg F n) : mwWordDegMap (RingHom.id F) n w = w := by
  have hl : w.val.2.map (milnorUnitMap (RingHom.id F)) = w.val.2 := by
    conv_rhs => rw [← List.map_id w.val.2]
    exact List.map_congr_left fun a _ => Units.ext rfl
  refine Subtype.ext ?_
  show ((w.val.1, w.val.2.map (milnorUnitMap (RingHom.id F))) : ℕ × List Fˣ) = w.val
  rw [hl]

theorem mwWordDegMap_comp (g : E →+* G) (f : F →+* E) {n : ℤ} (w : MWWordDeg F n) :
    mwWordDegMap g n (mwWordDegMap f n w) = mwWordDegMap (g.comp f) n w := by
  refine Subtype.ext ?_
  show ((w.val.1, (w.val.2.map (milnorUnitMap f)).map (milnorUnitMap g)) : ℕ × List Gˣ)
      = (w.val.1, w.val.2.map (milnorUnitMap (g.comp f)))
  rw [List.map_map]
  refine congrArg (Prod.mk w.val.1) ?_
  exact List.map_congr_left fun a _ => Units.ext rfl

/-- **The identity induces the identity.** -/
theorem mwKDegMap_id (n : ℤ) : mwKDegMap (RingHom.id F) n = AddMonoidHom.id _ :=
  mwKDeg_hom_ext F fun w => by rw [mwKDegMap_class, mwWordDegMap_id]; rfl

/-- **Composition of field homomorphisms induces composition.** -/
theorem mwKDegMap_comp (g : E →+* G) (f : F →+* E) (n : ℤ) :
    (mwKDegMap g n).comp (mwKDegMap f n) = mwKDegMap (g.comp f) n :=
  mwKDeg_hom_ext F fun w => by
    show mwKDegMap g n (mwKDegMap f n (mwClassDeg F n w)) = _
    rw [mwKDegMap_class, mwKDegMap_class, mwKDegMap_class, mwWordDegMap_comp]

end Functorial

section Multiplicative

variable {F E : Type*} [Field F] [Field E]

theorem mwWordDegMap_mul (f : F →+* E) {m n : ℤ} (v : MWWordDeg F m) (w : MWWordDeg F n) :
    mwWordDegMap f (m + n) (mwWordMul v w)
      = mwWordMul (mwWordDegMap f m v) (mwWordDegMap f n w) := by
  refine Subtype.ext ?_
  show ((v.val.1 + w.val.1, (v.val.2 ++ w.val.2).map (milnorUnitMap f)) : ℕ × List Eˣ)
      = (v.val.1 + w.val.1, v.val.2.map (milnorUnitMap f) ++ w.val.2.map (milnorUnitMap f))
  rw [List.map_append]

/-- **The induced map is multiplicative for the graded product.** -/
theorem mwKDegMap_mul (f : F →+* E) (m n : ℤ) (x : MilnorWittKDeg F m) (y : MilnorWittKDeg F n) :
    mwKDegMap f (m + n) (mwMul m n x y)
      = mwMul m n (mwKDegMap f m x) (mwKDegMap f n y) := by
  have hword : ∀ (v : MWWordDeg F m) (z : MilnorWittKDeg F n),
      mwKDegMap f (m + n) (mwMul m n (mwClassDeg F m v) z)
        = mwMul m n (mwKDegMap f m (mwClassDeg F m v)) (mwKDegMap f n z) := by
    intro v z
    have hext : (mwKDegMap f (m + n)).comp (mwMul m n (mwClassDeg F m v))
        = (mwMul m n (mwKDegMap f m (mwClassDeg F m v))).comp (mwKDegMap f n) := by
      refine mwKDeg_hom_ext F fun w => ?_
      show mwKDegMap f (m + n) (mwMul m n (mwClassDeg F m v) (mwClassDeg F n w))
          = mwMul m n (mwKDegMap f m (mwClassDeg F m v)) (mwKDegMap f n (mwClassDeg F n w))
      rw [mwMul_class, mwKDegMap_class, mwKDegMap_class, mwKDegMap_class, mwMul_class,
        mwWordDegMap_mul]
    exact DFunLike.congr_fun hext z
  have hext : (mwKDegMap f (m + n)).comp ((mwMul m n).flip y)
      = ((mwMul m n).flip (mwKDegMap f n y)).comp (mwKDegMap f m) := by
    refine mwKDeg_hom_ext F fun v => ?_
    show mwKDegMap f (m + n) (mwMul m n (mwClassDeg F m v) y)
        = mwMul m n (mwKDegMap f m (mwClassDeg F m v)) (mwKDegMap f n y)
    exact hword v y
  exact DFunLike.congr_fun hext x

theorem mwWordDegMap_etaWord (f : F →+* E) {n m : ℤ} (h : n = m + 1) (w : MWWordDeg F n) :
    mwWordDegMap f m (mwEtaWord h w) = mwEtaWord h (mwWordDegMap f n w) :=
  Subtype.ext rfl

/-- **The induced map commutes with multiplication by `η`.** -/
theorem mwKDegMap_etaMul (f : F →+* E) {n m : ℤ} (h : n = m + 1) (x : MilnorWittKDeg F n) :
    mwKDegMap f m (mwEtaMul h x) = mwEtaMul h (mwKDegMap f n x) := by
  have hext : (mwKDegMap f m).comp (mwEtaMul h)
      = (mwEtaMul h).comp (mwKDegMap f n) := by
    refine mwKDeg_hom_ext F fun w => ?_
    show mwKDegMap f m (mwEtaMul h (mwClassDeg F n w))
        = mwEtaMul h (mwKDegMap f n (mwClassDeg F n w))
    rw [mwEtaMul_class, mwKDegMap_class, mwKDegMap_class, mwEtaMul_class,
      mwWordDegMap_etaWord]
  exact DFunLike.congr_fun hext x

end Multiplicative

end GaloisForLFunctions.HTGeometry
