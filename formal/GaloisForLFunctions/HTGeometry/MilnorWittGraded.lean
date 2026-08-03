import GaloisForLFunctions.HTGeometry.MilnorWittFormIdentities
import GaloisForLFunctions.HTGeometry.MilnorKGradedRing

/-!
# Graded Milnor--Witt `K`-theory

Milnor--Witt `K`-theory is `ℤ`-graded: the symbols `[a]` sit in degree one and `η` sits in degree
minus one.  Because `η` is central, every word is `η^k[a_1]⋯[a_m]`, of degree `m - k`, so the
degree-`n` part is presented by the words of that shape modulo the three homogeneous relation
families — Steinberg, twisted multiplicativity with its degree-shifted `η`-correction, and the
hyperbolic relation.

* `MWWordDeg` : the words of a fixed degree.
* `MilnorWittKDeg` : `K_n^{MW}(F)`.
* `mwClassDeg_steinberg`, `mwClassDeg_twisted`, `mwClassDeg_hyperbolic` : the three relations, read
  in the quotient and stated up to an equality of lists so that they survive reassociation.
* `mwKDeg_hom_ext` : the classes of words generate.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWittGraded

variable (F : Type*) [Field F]

/-- The word `η^k[a_1]⋯[a_m]`, recorded as the pair `(k, l)`, in degree `m - k`. -/
def MWWordDeg (n : ℤ) : Type _ := {p : ℕ × List Fˣ // (p.2.length : ℤ) - p.1 = n}

/-- The defining relations of Milnor--Witt `K`-theory in degree `n`. -/
def mwRelDeg (n : ℤ) : AddSubgroup (FreeAbelianGroup (MWWordDeg F n)) :=
  AddSubgroup.closure
    ({x | ∃ (k : ℕ) (a : Fˣ) (ha : (a : F) ≠ 1) (l₁ l₂ : List Fˣ)
        (h : (((l₁ ++ a :: oneSubUnit ha :: l₂).length : ℤ)) - k = n),
        x = FreeAbelianGroup.of ⟨(k, l₁ ++ a :: oneSubUnit ha :: l₂), h⟩} ∪
      {x | ∃ (k : ℕ) (a b : Fˣ) (l₁ l₂ : List Fˣ)
        (hab : (((l₁ ++ (a * b) :: l₂).length : ℤ)) - k = n)
        (ha : (((l₁ ++ a :: l₂).length : ℤ)) - k = n)
        (hb : (((l₁ ++ b :: l₂).length : ℤ)) - k = n)
        (he : (((l₁ ++ a :: b :: l₂).length : ℤ)) - (k + 1) = n),
        x = FreeAbelianGroup.of ⟨(k, l₁ ++ (a * b) :: l₂), hab⟩ -
            FreeAbelianGroup.of ⟨(k, l₁ ++ a :: l₂), ha⟩ -
            FreeAbelianGroup.of ⟨(k, l₁ ++ b :: l₂), hb⟩ -
            FreeAbelianGroup.of ⟨(k + 1, l₁ ++ a :: b :: l₂), he⟩} ∪
      {x | ∃ (k : ℕ) (l₁ l₂ : List Fˣ)
        (h1 : (((l₁ ++ (-1 : Fˣ) :: l₂).length : ℤ)) - (k + 2) = n)
        (h2 : (((l₁ ++ l₂).length : ℤ)) - (k + 1) = n),
        x = FreeAbelianGroup.of ⟨(k + 2, l₁ ++ (-1 : Fˣ) :: l₂), h1⟩ +
            FreeAbelianGroup.of ⟨(k + 1, l₁ ++ l₂), h2⟩ +
            FreeAbelianGroup.of ⟨(k + 1, l₁ ++ l₂), h2⟩})

/-- **Milnor--Witt `K`-theory in degree `n`.** -/
def MilnorWittKDeg (n : ℤ) : Type _ :=
  FreeAbelianGroup (MWWordDeg F n) ⧸ mwRelDeg F n

instance (n : ℤ) : AddCommGroup (MilnorWittKDeg F n) :=
  QuotientAddGroup.Quotient.addCommGroup _

/-- The class of a word. -/
def mwClassDeg (n : ℤ) (w : MWWordDeg F n) : MilnorWittKDeg F n :=
  QuotientAddGroup.mk (FreeAbelianGroup.of w)

/-- **Extensionality**: two additive maps out of `K_n^{MW}` agree once they agree on the classes of
words. -/
theorem mwKDeg_hom_ext {A : Type*} [AddCommGroup A] {n : ℤ} {f g : MilnorWittKDeg F n →+ A}
    (h : ∀ w : MWWordDeg F n, f (mwClassDeg F n w) = g (mwClassDeg F n w)) : f = g := by
  refine AddMonoidHom.ext fun x => ?_
  refine QuotientAddGroup.induction_on x fun v => ?_
  induction v using FreeAbelianGroup.induction_on with
  | zero =>
    show f (0 : MilnorWittKDeg F n) = g 0
    rw [map_zero, map_zero]
  | of w => exact h w
  | neg w ih =>
    have hmk : (QuotientAddGroup.mk (s := mwRelDeg F n) (-FreeAbelianGroup.of w)) =
        -(QuotientAddGroup.mk (s := mwRelDeg F n) (FreeAbelianGroup.of w)) := rfl
    have hf : f (-(QuotientAddGroup.mk (s := mwRelDeg F n) (FreeAbelianGroup.of w))) =
        -f (QuotientAddGroup.mk (s := mwRelDeg F n) (FreeAbelianGroup.of w)) := map_neg _ _
    have hg : g (-(QuotientAddGroup.mk (s := mwRelDeg F n) (FreeAbelianGroup.of w))) =
        -g (QuotientAddGroup.mk (s := mwRelDeg F n) (FreeAbelianGroup.of w)) := map_neg _ _
    rw [hmk, hf, hg, ih]
  | add u v hu hv =>
    have hmk : (QuotientAddGroup.mk (s := mwRelDeg F n) (u + v)) =
        QuotientAddGroup.mk (s := mwRelDeg F n) u +
          QuotientAddGroup.mk (s := mwRelDeg F n) v := rfl
    have hf : f (QuotientAddGroup.mk (s := mwRelDeg F n) u +
          QuotientAddGroup.mk (s := mwRelDeg F n) v) =
        f (QuotientAddGroup.mk (s := mwRelDeg F n) u) +
          f (QuotientAddGroup.mk (s := mwRelDeg F n) v) := map_add _ _ _
    have hg : g (QuotientAddGroup.mk (s := mwRelDeg F n) u +
          QuotientAddGroup.mk (s := mwRelDeg F n) v) =
        g (QuotientAddGroup.mk (s := mwRelDeg F n) u) +
          g (QuotientAddGroup.mk (s := mwRelDeg F n) v) := map_add _ _ _
    rw [hmk, hf, hg, hu, hv]

variable {F}

/-- The class of a word depends only on the pair. -/
theorem mwClassDeg_congr {n : ℤ} {k : ℕ} {l l' : List Fˣ}
    (p : ((l.length : ℤ)) - k = n) (p' : ((l'.length : ℤ)) - k = n) (h : l = l') :
    mwClassDeg F n ⟨(k, l), p⟩ = mwClassDeg F n ⟨(k, l'), p'⟩ := by
  subst h
  rfl

/-- **The Steinberg relation in degree `n`.** -/
theorem mwClassDeg_steinberg {n : ℤ} (k : ℕ) {a : Fˣ} (ha : (a : F) ≠ 1) (l₁ l₂ : List Fˣ)
    {L : List Fˣ} (hL : L = l₁ ++ a :: oneSubUnit ha :: l₂)
    (p : ((L.length : ℤ)) - k = n) : mwClassDeg F n ⟨(k, L), p⟩ = 0 := by
  subst hL
  exact (QuotientAddGroup.eq_zero_iff _).2
    (AddSubgroup.subset_closure (Or.inl (Or.inl ⟨k, a, ha, l₁, l₂, p, rfl⟩)))

/-- **Twisted multiplicativity in degree `n`**: the correction term sits one `η`-power higher. -/
theorem mwClassDeg_twisted {n : ℤ} (k : ℕ) (a b : Fˣ) (l₁ l₂ : List Fˣ)
    {Lab La Lb Le : List Fˣ} (hab : Lab = l₁ ++ (a * b) :: l₂) (hla : La = l₁ ++ a :: l₂)
    (hlb : Lb = l₁ ++ b :: l₂) (hle : Le = l₁ ++ a :: b :: l₂)
    (pab : ((Lab.length : ℤ)) - k = n) (pa : ((La.length : ℤ)) - k = n)
    (pb : ((Lb.length : ℤ)) - k = n) (pe : ((Le.length : ℤ)) - (k + 1) = n) :
    mwClassDeg F n ⟨(k, Lab), pab⟩ =
      mwClassDeg F n ⟨(k, La), pa⟩ + mwClassDeg F n ⟨(k, Lb), pb⟩ +
        mwClassDeg F n ⟨(k + 1, Le), pe⟩ := by
  subst hab
  subst hla
  subst hlb
  subst hle
  have hmem : (FreeAbelianGroup.of (⟨(k, l₁ ++ (a * b) :: l₂), pab⟩ : MWWordDeg F n) -
      FreeAbelianGroup.of (⟨(k, l₁ ++ a :: l₂), pa⟩ : MWWordDeg F n) -
      FreeAbelianGroup.of (⟨(k, l₁ ++ b :: l₂), pb⟩ : MWWordDeg F n) -
      FreeAbelianGroup.of (⟨(k + 1, l₁ ++ a :: b :: l₂), pe⟩ : MWWordDeg F n)) ∈
      mwRelDeg F n :=
    AddSubgroup.subset_closure (Or.inl (Or.inr ⟨k, a, b, l₁, l₂, pab, pa, pb, pe, rfl⟩))
  have h0 : mwClassDeg F n ⟨(k, l₁ ++ (a * b) :: l₂), pab⟩ -
      mwClassDeg F n ⟨(k, l₁ ++ a :: l₂), pa⟩ -
      mwClassDeg F n ⟨(k, l₁ ++ b :: l₂), pb⟩ -
      mwClassDeg F n ⟨(k + 1, l₁ ++ a :: b :: l₂), pe⟩ = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 hmem
  rw [sub_sub, sub_sub] at h0
  rw [sub_eq_zero.mp h0]
  abel

/-- **The hyperbolic relation in degree `n`**: `η²[-1] + 2η = 0`, inserted into a word. -/
theorem mwClassDeg_hyperbolic {n : ℤ} (k : ℕ) (l₁ l₂ : List Fˣ)
    {L M : List Fˣ} (hL : L = l₁ ++ (-1 : Fˣ) :: l₂) (hM : M = l₁ ++ l₂)
    (p1 : ((L.length : ℤ)) - (k + 2) = n) (p2 : ((M.length : ℤ)) - (k + 1) = n) :
    mwClassDeg F n ⟨(k + 2, L), p1⟩ +
      (mwClassDeg F n ⟨(k + 1, M), p2⟩ + mwClassDeg F n ⟨(k + 1, M), p2⟩) = 0 := by
  subst hL
  subst hM
  have hmem : (FreeAbelianGroup.of (⟨(k + 2, l₁ ++ (-1 : Fˣ) :: l₂), p1⟩ : MWWordDeg F n) +
      FreeAbelianGroup.of (⟨(k + 1, l₁ ++ l₂), p2⟩ : MWWordDeg F n) +
      FreeAbelianGroup.of (⟨(k + 1, l₁ ++ l₂), p2⟩ : MWWordDeg F n)) ∈ mwRelDeg F n :=
    AddSubgroup.subset_closure (Or.inr ⟨k, l₁, l₂, p1, p2, rfl⟩)
  have h0 : mwClassDeg F n ⟨(k + 2, l₁ ++ (-1 : Fˣ) :: l₂), p1⟩ +
      mwClassDeg F n ⟨(k + 1, l₁ ++ l₂), p2⟩ +
      mwClassDeg F n ⟨(k + 1, l₁ ++ l₂), p2⟩ = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 hmem
  rw [← add_assoc]
  exact h0

end MilnorWittGraded

section MilnorWittGradedMul

variable {F : Type*} [Field F]

/-- Twisted multiplicativity with the `η`-exponent of the correction term given up to an
equality. -/
theorem mwClassDeg_twisted' {n : ℤ} (k : ℕ) (a b : Fˣ) (l₁ l₂ : List Fˣ) {ke : ℕ}
    (hke : ke = k + 1) {Lab La Lb Le : List Fˣ} (hab : Lab = l₁ ++ (a * b) :: l₂)
    (hla : La = l₁ ++ a :: l₂) (hlb : Lb = l₁ ++ b :: l₂) (hle : Le = l₁ ++ a :: b :: l₂)
    (pab : ((Lab.length : ℤ)) - k = n) (pa : ((La.length : ℤ)) - k = n)
    (pb : ((Lb.length : ℤ)) - k = n) (pe : ((Le.length : ℤ)) - ke = n) :
    mwClassDeg F n ⟨(k, Lab), pab⟩ =
      mwClassDeg F n ⟨(k, La), pa⟩ + mwClassDeg F n ⟨(k, Lb), pb⟩ +
        mwClassDeg F n ⟨(ke, Le), pe⟩ := by
  subst hke
  exact mwClassDeg_twisted k a b l₁ l₂ hab hla hlb hle pab pa pb pe

/-- The hyperbolic relation with both `η`-exponents given up to an equality. -/
theorem mwClassDeg_hyperbolic' {n : ℤ} (k : ℕ) (l₁ l₂ : List Fˣ) {k1 k2 : ℕ}
    (hk1 : k1 = k + 2) (hk2 : k2 = k + 1) {L M : List Fˣ}
    (hL : L = l₁ ++ (-1 : Fˣ) :: l₂) (hM : M = l₁ ++ l₂)
    (p1 : ((L.length : ℤ)) - k1 = n) (p2 : ((M.length : ℤ)) - k2 = n) :
    mwClassDeg F n ⟨(k1, L), p1⟩ +
      (mwClassDeg F n ⟨(k2, M), p2⟩ + mwClassDeg F n ⟨(k2, M), p2⟩) = 0 := by
  subst hk1
  subst hk2
  exact mwClassDeg_hyperbolic k l₁ l₂ hL hM p1 p2

/-- Concatenation of words, which is the product of Milnor--Witt `K`-theory. -/
def mwWordMul {m n : ℤ} (v : MWWordDeg F m) (w : MWWordDeg F n) : MWWordDeg F (m + n) :=
  ⟨(v.val.1 + w.val.1, v.val.2 ++ w.val.2), by
    have hv := v.property
    have hw := w.property
    simp only [List.length_append]
    push_cast at hv hw ⊢
    omega⟩

/-- Left multiplication by a fixed word, before descending in the second variable. -/
def mwMulRightLift {m : ℤ} (v : MWWordDeg F m) (n : ℤ) :
    FreeAbelianGroup (MWWordDeg F n) →+ MilnorWittKDeg F (m + n) :=
  FreeAbelianGroup.lift fun w => mwClassDeg F (m + n) (mwWordMul v w)

@[simp]
theorem mwMulRightLift_of {m : ℤ} (v : MWWordDeg F m) (n : ℤ) (w : MWWordDeg F n) :
    mwMulRightLift v n (FreeAbelianGroup.of w) = mwClassDeg F (m + n) (mwWordMul v w) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The relations survive a prefix.** -/
theorem mwMulRightLift_ker {m : ℤ} (v : MWWordDeg F m) (n : ℤ) :
    mwRelDeg F n ≤ (mwMulRightLift v n).ker := by
  rw [mwRelDeg, AddSubgroup.closure_le]
  rintro x ((⟨k, a, ha, l₁, l₂, h, rfl⟩ | ⟨k, a, b, l₁, l₂, hab, hpa, hpb, hpe, rfl⟩) |
    ⟨k, l₁, l₂, h1, h2, rfl⟩)
  · show mwMulRightLift v n _ = 0
    rw [mwMulRightLift_of]
    exact mwClassDeg_steinberg (v.val.1 + k) ha (v.val.2 ++ l₁) l₂
      (List.append_assoc v.val.2 l₁ (a :: oneSubUnit ha :: l₂)).symm _
  · show mwMulRightLift v n _ = 0
    rw [map_sub, map_sub, map_sub, mwMulRightLift_of, mwMulRightLift_of, mwMulRightLift_of,
      mwMulRightLift_of, sub_sub, sub_sub, sub_eq_zero]
    refine Eq.trans ?_ (add_assoc _ _ _)
    exact mwClassDeg_twisted' (v.val.1 + k) a b (v.val.2 ++ l₁) l₂ rfl
      (List.append_assoc v.val.2 l₁ ((a * b) :: l₂)).symm
      (List.append_assoc v.val.2 l₁ (a :: l₂)).symm
      (List.append_assoc v.val.2 l₁ (b :: l₂)).symm
      (List.append_assoc v.val.2 l₁ (a :: b :: l₂)).symm _ _ _ _
  · show mwMulRightLift v n _ = 0
    rw [map_add, map_add, mwMulRightLift_of, mwMulRightLift_of, add_assoc]
    exact mwClassDeg_hyperbolic' (v.val.1 + k) (v.val.2 ++ l₁) l₂ rfl rfl
      (List.append_assoc v.val.2 l₁ ((-1 : Fˣ) :: l₂)).symm
      (List.append_assoc v.val.2 l₁ l₂).symm _ _

/-- Left multiplication by a fixed word. -/
def mwMulRight {m : ℤ} (v : MWWordDeg F m) (n : ℤ) :
    MilnorWittKDeg F n →+ MilnorWittKDeg F (m + n) :=
  QuotientAddGroup.lift _ (mwMulRightLift v n) (mwMulRightLift_ker v n)

@[simp]
theorem mwMulRight_class {m : ℤ} (v : MWWordDeg F m) (n : ℤ) (w : MWWordDeg F n) :
    mwMulRight v n (mwClassDeg F n w) = mwClassDeg F (m + n) (mwWordMul v w) := by
  show mwMulRightLift v n (FreeAbelianGroup.of w) = _
  rw [mwMulRightLift_of]

/-- The product on formal sums in the first variable. -/
def mwMulLift (m n : ℤ) :
    FreeAbelianGroup (MWWordDeg F m) →+ (MilnorWittKDeg F n →+ MilnorWittKDeg F (m + n)) :=
  FreeAbelianGroup.lift fun v => mwMulRight v n

/-- **The relations survive a suffix.** -/
theorem mwMulLift_ker (m n : ℤ) : mwRelDeg F m ≤ (mwMulLift m n).ker := by
  rw [mwRelDeg, AddSubgroup.closure_le]
  rintro x ((⟨k, a, ha, l₁, l₂, h, rfl⟩ | ⟨k, a, b, l₁, l₂, hab, hpa, hpb, hpe, rfl⟩) |
    ⟨k, l₁, l₂, h1, h2, rfl⟩)
  · show mwMulLift m n _ = 0
    rw [mwMulLift, FreeAbelianGroup.lift_apply_of]
    refine mwKDeg_hom_ext F fun w => ?_
    rw [AddMonoidHom.zero_apply, mwMulRight_class]
    exact mwClassDeg_steinberg (k + w.val.1) ha l₁ (l₂ ++ w.val.2)
      (List.append_assoc l₁ (a :: oneSubUnit ha :: l₂) w.val.2) _
  · show mwMulLift m n _ = 0
    rw [mwMulLift, map_sub, map_sub, map_sub, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    refine mwKDeg_hom_ext F fun w => ?_
    rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, AddMonoidHom.sub_apply,
      AddMonoidHom.zero_apply, mwMulRight_class, mwMulRight_class, mwMulRight_class,
      mwMulRight_class, sub_sub, sub_sub, sub_eq_zero]
    refine Eq.trans ?_ (add_assoc _ _ _)
    exact mwClassDeg_twisted' (k + w.val.1) a b l₁ (l₂ ++ w.val.2)
      (add_right_comm k 1 w.val.1)
      (List.append_assoc l₁ ((a * b) :: l₂) w.val.2)
      (List.append_assoc l₁ (a :: l₂) w.val.2)
      (List.append_assoc l₁ (b :: l₂) w.val.2)
      (List.append_assoc l₁ (a :: b :: l₂) w.val.2) _ _ _ _
  · show mwMulLift m n _ = 0
    rw [mwMulLift, map_add, map_add, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    refine mwKDeg_hom_ext F fun w => ?_
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, AddMonoidHom.zero_apply,
      mwMulRight_class, mwMulRight_class, add_assoc]
    exact mwClassDeg_hyperbolic' (k + w.val.1) l₁ (l₂ ++ w.val.2)
      (add_right_comm k 2 w.val.1) (add_right_comm k 1 w.val.1)
      (List.append_assoc l₁ ((-1 : Fˣ) :: l₂) w.val.2)
      (List.append_assoc l₁ l₂ w.val.2) _ _

/-- **The product of Milnor--Witt `K`-theory**, `K_m^{MW}(F) × K_n^{MW}(F) → K_{m+n}^{MW}(F)`,
induced by concatenation of words. -/
def mwMul (m n : ℤ) :
    MilnorWittKDeg F m →+ (MilnorWittKDeg F n →+ MilnorWittKDeg F (m + n)) :=
  QuotientAddGroup.lift _ (mwMulLift m n) (mwMulLift_ker m n)

@[simp]
theorem mwMul_class (m n : ℤ) (v : MWWordDeg F m) (w : MWWordDeg F n) :
    mwMul m n (mwClassDeg F m v) (mwClassDeg F n w) = mwClassDeg F (m + n) (mwWordMul v w) := by
  show mwMulRight v n (mwClassDeg F n w) = _
  rw [mwMulRight_class]

end MilnorWittGradedMul

end GaloisForLFunctions.HTGeometry
