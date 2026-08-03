import GaloisForLFunctions.HTGeometry.MilnorWittGraded

/-!
# Multiplying by `η` and by a single symbol in graded Milnor--Witt `K`-theory

The identities of Milnor--Witt `K`-theory are derived by multiplying relations by `η` and by single
symbols.  In the graded presentation those two operations are the maps that raise the `η`-exponent
of a word, and that append a symbol to it; both send relations to relations, so both descend.

Because the degree of the target is fixed by an equation rather than computed, the maps compose
without any coercion between `n - 1` and the literal degree one is working in.

* `mwEtaMul` : multiplication by `η`, lowering the degree by one.
* `mwSymMulRight` : multiplication by `[u]` on the right, raising the degree by one.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWittGradedOperations

variable {F : Type*} [Field F]

/-- The word `η^{k+1}[l]`, of degree one lower. -/
def mwEtaWord {n m : ℤ} (h : n = m + 1) (w : MWWordDeg F n) : MWWordDeg F m :=
  ⟨(w.val.1 + 1, w.val.2), by
    have hw := w.property
    push_cast at hw ⊢
    omega⟩

/-- The word `η^k[l][u]`, of degree one higher. -/
def mwSymRightWord {n m : ℤ} (h : m = n + 1) (u : Fˣ) (w : MWWordDeg F n) : MWWordDeg F m :=
  ⟨(w.val.1, w.val.2 ++ [u]), by
    have hw := w.property
    simp only [List.length_append, List.length_cons, List.length_nil]
    push_cast at hw ⊢
    omega⟩

/-- Multiplication by `η`, before descending. -/
def mwEtaLift {n m : ℤ} (h : n = m + 1) :
    FreeAbelianGroup (MWWordDeg F n) →+ MilnorWittKDeg F m :=
  FreeAbelianGroup.lift fun w => mwClassDeg F m (mwEtaWord h w)

@[simp]
theorem mwEtaLift_of {n m : ℤ} (h : n = m + 1) (w : MWWordDeg F n) :
    mwEtaLift h (FreeAbelianGroup.of w) = mwClassDeg F m (mwEtaWord h w) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem mwEtaLift_ker {n m : ℤ} (h : n = m + 1) : mwRelDeg F n ≤ (mwEtaLift h).ker := by
  rw [mwRelDeg, AddSubgroup.closure_le]
  rintro x ((⟨k, a, ha, l₁, l₂, hp, rfl⟩ | ⟨k, a, b, l₁, l₂, hab, hpa, hpb, hpe, rfl⟩) |
    ⟨k, l₁, l₂, h1, h2, rfl⟩)
  · show mwEtaLift h _ = 0
    rw [mwEtaLift_of]
    exact mwClassDeg_steinberg (k + 1) ha l₁ l₂ rfl _
  · show mwEtaLift h _ = 0
    rw [map_sub, map_sub, map_sub, mwEtaLift_of, mwEtaLift_of, mwEtaLift_of, mwEtaLift_of,
      sub_sub, sub_sub, sub_eq_zero]
    refine Eq.trans ?_ (add_assoc _ _ _)
    exact mwClassDeg_twisted (k + 1) a b l₁ l₂ rfl rfl rfl rfl _ _ _ _
  · show mwEtaLift h _ = 0
    rw [map_add, map_add, mwEtaLift_of, mwEtaLift_of, add_assoc]
    exact mwClassDeg_hyperbolic (k + 1) l₁ l₂ rfl rfl _ _

/-- **Multiplication by `η`**, lowering the degree by one. -/
def mwEtaMul {n m : ℤ} (h : n = m + 1) : MilnorWittKDeg F n →+ MilnorWittKDeg F m :=
  QuotientAddGroup.lift _ (mwEtaLift h) (mwEtaLift_ker h)

@[simp]
theorem mwEtaMul_class {n m : ℤ} (h : n = m + 1) (w : MWWordDeg F n) :
    mwEtaMul h (mwClassDeg F n w) = mwClassDeg F m (mwEtaWord h w) := by
  show mwEtaLift h (FreeAbelianGroup.of w) = _
  rw [mwEtaLift_of]

/-- Multiplication by a symbol on the right, before descending. -/
def mwSymRightLift {n m : ℤ} (h : m = n + 1) (u : Fˣ) :
    FreeAbelianGroup (MWWordDeg F n) →+ MilnorWittKDeg F m :=
  FreeAbelianGroup.lift fun w => mwClassDeg F m (mwSymRightWord h u w)

@[simp]
theorem mwSymRightLift_of {n m : ℤ} (h : m = n + 1) (u : Fˣ) (w : MWWordDeg F n) :
    mwSymRightLift h u (FreeAbelianGroup.of w) = mwClassDeg F m (mwSymRightWord h u w) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem mwSymRightLift_ker {n m : ℤ} (h : m = n + 1) (u : Fˣ) :
    mwRelDeg F n ≤ (mwSymRightLift h u).ker := by
  rw [mwRelDeg, AddSubgroup.closure_le]
  rintro x ((⟨k, a, ha, l₁, l₂, hp, rfl⟩ | ⟨k, a, b, l₁, l₂, hab, hpa, hpb, hpe, rfl⟩) |
    ⟨k, l₁, l₂, h1, h2, rfl⟩)
  · show mwSymRightLift h u _ = 0
    rw [mwSymRightLift_of]
    exact mwClassDeg_steinberg k ha l₁ (l₂ ++ [u])
      (List.append_assoc l₁ (a :: oneSubUnit ha :: l₂) [u]) _
  · show mwSymRightLift h u _ = 0
    rw [map_sub, map_sub, map_sub, mwSymRightLift_of, mwSymRightLift_of, mwSymRightLift_of,
      mwSymRightLift_of, sub_sub, sub_sub, sub_eq_zero]
    refine Eq.trans ?_ (add_assoc _ _ _)
    exact mwClassDeg_twisted k a b l₁ (l₂ ++ [u])
      (List.append_assoc l₁ ((a * b) :: l₂) [u])
      (List.append_assoc l₁ (a :: l₂) [u])
      (List.append_assoc l₁ (b :: l₂) [u])
      (List.append_assoc l₁ (a :: b :: l₂) [u]) _ _ _ _
  · show mwSymRightLift h u _ = 0
    rw [map_add, map_add, mwSymRightLift_of, mwSymRightLift_of, add_assoc]
    exact mwClassDeg_hyperbolic k l₁ (l₂ ++ [u])
      (List.append_assoc l₁ ((-1 : Fˣ) :: l₂) [u]) (List.append_assoc l₁ l₂ [u]) _ _

/-- **Multiplication by a symbol on the right**, raising the degree by one. -/
def mwSymMulRight {n m : ℤ} (h : m = n + 1) (u : Fˣ) :
    MilnorWittKDeg F n →+ MilnorWittKDeg F m :=
  QuotientAddGroup.lift _ (mwSymRightLift h u) (mwSymRightLift_ker h u)

@[simp]
theorem mwSymMulRight_class {n m : ℤ} (h : m = n + 1) (u : Fˣ) (w : MWWordDeg F n) :
    mwSymMulRight h u (mwClassDeg F n w) = mwClassDeg F m (mwSymRightWord h u w) := by
  show mwSymRightLift h u (FreeAbelianGroup.of w) = _
  rw [mwSymRightLift_of]

/-- Multiplication by `η`, on a word class, with the target word given up to an equality of
exponents. -/
theorem mwEtaMul_class' {n m : ℤ} (h : n = m + 1) {k j : ℕ} {M : List Fˣ}
    (p : ((M.length : ℤ)) - k = n) (q : ((M.length : ℤ)) - j = m) (hkj : j = k + 1) :
    mwEtaMul h (mwClassDeg F n ⟨(k, M), p⟩) = mwClassDeg F m ⟨(j, M), q⟩ := by
  subst hkj
  rw [mwEtaMul_class]
  rfl

/-- Multiplication by a symbol on the right, on a word class, with the target word given up to an
equality of lists. -/
theorem mwSymMulRight_class' {n m : ℤ} (h : m = n + 1) (u : Fˣ) {k : ℕ} {M N : List Fˣ}
    (p : ((M.length : ℤ)) - k = n) (q : ((N.length : ℤ)) - k = m) (hMN : N = M ++ [u]) :
    mwSymMulRight h u (mwClassDeg F n ⟨(k, M), p⟩) = mwClassDeg F m ⟨(k, N), q⟩ := by
  subst hMN
  rw [mwSymMulRight_class]
  rfl

end MilnorWittGradedOperations

end GaloisForLFunctions.HTGeometry
