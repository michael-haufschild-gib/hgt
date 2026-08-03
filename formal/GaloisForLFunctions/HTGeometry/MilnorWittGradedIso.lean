import GaloisForLFunctions.HTGeometry.MilnorWittGradedSquare

/-!
# Words with an `η` vanish over a quadratically closed field

Over a field in which every element is a square, `η[u] = 0` for every unit.  Every word
`η^k[a_1]⋯[a_m]` with `k ≥ 1` and `m ≥ 1` is that element multiplied by the rest of the word, so it
vanishes too.

* `mwDegCongr` : transport along an equality of degrees.
* `mwMul_class_left` : the product with a word class is left multiplication by that word.
* `mwClassDeg_eq_zero_of_eta` : a word with a positive `η`-exponent and at least one symbol is zero.
-/

namespace GaloisForLFunctions.HTGeometry

section MilnorWittGradedIso

variable {F : Type*} [Field F]

/-- Transport along an equality of degrees. -/
def mwDegCongr {n m : ℤ} (h : n = m) : MilnorWittKDeg F n →+ MilnorWittKDeg F m := by
  subst h
  exact AddMonoidHom.id _

@[simp]
theorem mwDegCongr_class {n m : ℤ} (h : n = m) {k : ℕ} {l : List Fˣ}
    (p : ((l.length : ℤ)) - k = n) (q : ((l.length : ℤ)) - k = m) :
    mwDegCongr h (mwClassDeg F n ⟨(k, l), p⟩) = mwClassDeg F m ⟨(k, l), q⟩ := by
  subst h
  rfl

/-- **The product with a word class is left multiplication by that word.** -/
theorem mwMul_class_left (m n : ℤ) (v : MWWordDeg F m) :
    mwMul m n (mwClassDeg F m v) = mwMulRight v n := by
  show mwMulLift m n (FreeAbelianGroup.of v) = _
  rw [mwMulLift, FreeAbelianGroup.lift_apply_of]

/-- **A word with a positive `η`-exponent and at least one symbol vanishes** over a quadratically
closed field. -/
theorem mwClassDeg_eq_zero_of_eta (hsq : ∀ x : F, ∃ y : F, x = y * y) {n : ℤ} (k : ℕ)
    (u : Fˣ) (l : List Fˣ) (p : ((((u :: l).length : ℤ))) - (k + 1) = n) :
    mwClassDeg F n ⟨(k + 1, u :: l), p⟩ = 0 := by
  have pv : (((([u] : List Fˣ).length : ℤ))) - (1 : ℕ) = 0 := by simp
  have hv : mwClassDeg F 0 (⟨(1, [u]), pv⟩ : MWWordDeg F 0) = 0 := mwEtaSymbol_eq_zero hsq u
  have pl : (((l.length : ℤ))) - k = (l.length : ℤ) - k := rfl
  have hmul : mwMul 0 ((l.length : ℤ) - k) (mwClassDeg F 0 (⟨(1, [u]), pv⟩ : MWWordDeg F 0)) = 0 := by
    rw [hv, map_zero]
  have hval := congrArg
    (fun f : MilnorWittKDeg F ((l.length : ℤ) - k) →+ MilnorWittKDeg F (0 + ((l.length : ℤ) - k)) =>
      f (mwClassDeg F ((l.length : ℤ) - k) ⟨(k, l), pl⟩)) hmul
  simp only [AddMonoidHom.zero_apply, mwMul_class] at hval
  have hn : (0 : ℤ) + ((l.length : ℤ) - k) = n := by
    simp only [List.length_cons] at p
    push_cast at p ⊢
    omega
  have hq : (((([u] ++ l).length : ℤ))) - (1 + k : ℕ) = 0 + ((l.length : ℤ) - k) := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    push_cast
    ring
  have hq' : (((([u] ++ l).length : ℤ))) - (1 + k : ℕ) = n := by rw [hq, hn]
  have hword : mwWordMul (⟨(1, [u]), pv⟩ : MWWordDeg F 0) (⟨(k, l), pl⟩ :
      MWWordDeg F ((l.length : ℤ) - k)) = ⟨(1 + k, [u] ++ l), hq⟩ := rfl
  rw [hword] at hval
  have hcong := congrArg (mwDegCongr (F := F) hn) hval
  rw [map_zero, mwDegCongr_class hn hq hq'] at hcong
  have hw : (⟨(1 + k, [u] ++ l), hq'⟩ : MWWordDeg F n) = ⟨(k + 1, u :: l), p⟩ :=
    Subtype.ext (by
      show ((1 + k, [u] ++ l) : ℕ × List Fˣ) = (k + 1, u :: l)
      congr 1
      exact Nat.add_comm 1 k)
  rw [hw] at hcong
  exact hcong

end MilnorWittGradedIso

section MilnorWittForgetIso

variable {F : Type*} [Field F]

/-- **A word with a positive `η`-exponent and a nonempty list vanishes.** -/
theorem mwClassDeg_eq_zero_of_eta' (hsq : ∀ x : F, ∃ y : F, x = y * y) {n : ℤ} (k : ℕ)
    (l : List Fˣ) (hl : l ≠ []) (p : (((l.length : ℤ))) - (k + 1) = n) :
    mwClassDeg F n ⟨(k + 1, l), p⟩ = 0 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons u t => exact mwClassDeg_eq_zero_of_eta hsq k u t p

/-- The forgetful map on words: a word with an `η` dies, and an `η`-free word becomes the Milnor
symbol of the same list. -/
def mwForgetWord (n : ℕ) : MWWordDeg F (n : ℤ) → MilnorKDeg F n
  | ⟨(0, l), p⟩ => milnorClassDeg F n ⟨l, by
      have h : ((l.length : ℤ)) = (n : ℤ) := by
        push_cast at p ⊢
        omega
      exact_mod_cast h⟩
  | ⟨(_ + 1, _), _⟩ => 0

/-- The forgetful map on formal sums of words. -/
def mwForgetLift (n : ℕ) : FreeAbelianGroup (MWWordDeg F (n : ℤ)) →+ MilnorKDeg F n :=
  FreeAbelianGroup.lift (mwForgetWord n)

@[simp]
theorem mwForgetLift_of (n : ℕ) (w : MWWordDeg F (n : ℤ)) :
    mwForgetLift n (FreeAbelianGroup.of w) = mwForgetWord n w :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The Milnor--Witt relations lie in the kernel of the forgetful map.**  With `η` killed,
twisted multiplicativity is Milnor multiplicativity, the Steinberg relations agree, and the
hyperbolic relation involves only words with an `η`. -/
theorem mwForgetLift_ker (n : ℕ) : mwRelDeg F (n : ℤ) ≤ (mwForgetLift (F := F) n).ker := by
  rw [mwRelDeg, AddSubgroup.closure_le]
  rintro x ((⟨k, a, ha, l₁, l₂, hp, rfl⟩ | ⟨k, a, b, l₁, l₂, hab, hpa, hpb, hpe, rfl⟩) |
    ⟨k, l₁, l₂, h1, h2, rfl⟩)
  · show mwForgetLift n _ = 0
    rw [mwForgetLift_of]
    cases k with
    | zero => exact milnorClassDeg_steinberg_of_eq F ha l₁ l₂ rfl _
    | succ k => rfl
  · show mwForgetLift n _ = 0
    rw [map_sub, map_sub, map_sub, mwForgetLift_of, mwForgetLift_of, mwForgetLift_of,
      mwForgetLift_of]
    cases k with
    | zero =>
      show milnorClassDeg F n _ - milnorClassDeg F n _ - milnorClassDeg F n _ - 0 = 0
      rw [sub_zero, sub_sub, sub_eq_zero]
      exact milnorClassDeg_mul_of_eq F a b l₁ l₂ rfl rfl rfl _ _ _
    | succ k =>
      show (0 : MilnorKDeg F n) - 0 - 0 - 0 = 0
      abel
  · show mwForgetLift n _ = 0
    rw [map_add, map_add, mwForgetLift_of, mwForgetLift_of]
    show (0 : MilnorKDeg F n) + 0 + 0 = 0
    abel

/-- **The forgetful morphism** `K_n^{MW}(F) → K_n^M(F)`. -/
def mwForget (n : ℕ) : MilnorWittKDeg F (n : ℤ) →+ MilnorKDeg F n :=
  QuotientAddGroup.lift _ (mwForgetLift n) (mwForgetLift_ker n)

@[simp]
theorem mwForget_class (n : ℕ) (w : MWWordDeg F (n : ℤ)) :
    mwForget n (mwClassDeg F n w) = mwForgetWord n w := by
  show mwForgetLift n (FreeAbelianGroup.of w) = _
  rw [mwForgetLift_of]

/-- The Milnor symbol, read as an `η`-free Milnor--Witt word. -/
def mwLiftWord (n : ℕ) (s : MilnorSymbolDeg F n) : MilnorWittKDeg F (n : ℤ) :=
  mwClassDeg F n ⟨(0, s.val), by
    have h := s.property
    push_cast
    rw [h]
    ring⟩

/-- The same, on formal sums of symbols. -/
def mwLiftFree (n : ℕ) : FreeAbelianGroup (MilnorSymbolDeg F n) →+ MilnorWittKDeg F (n : ℤ) :=
  FreeAbelianGroup.lift (mwLiftWord n)

@[simp]
theorem mwLiftFree_of (n : ℕ) (s : MilnorSymbolDeg F n) :
    mwLiftFree n (FreeAbelianGroup.of s) = mwLiftWord n s :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The Milnor relations lie in the kernel of the lift**, over a quadratically closed field: the
`η`-correction of twisted multiplicativity is a word with an `η` and a nonempty list. -/
theorem mwLiftFree_ker (hsq : ∀ x : F, ∃ y : F, x = y * y) (n : ℕ) :
    milnorRelSubgroupDeg F n ≤ (mwLiftFree (F := F) n).ker := by
  rw [milnorRelSubgroupDeg, AddSubgroup.closure_le]
  rintro x (⟨a, b, l₁, l₂, h, rfl⟩ | ⟨a, ha, l₁, l₂, h, rfl⟩)
  · show mwLiftFree n _ = 0
    rw [map_sub, map_sub, mwLiftFree_of, mwLiftFree_of, mwLiftFree_of, sub_sub, sub_eq_zero]
    have hne : l₁ ++ a :: b :: l₂ ≠ [] := by
      cases l₁ <;> simp
    have hzero : mwClassDeg F (n : ℤ)
        ⟨(0 + 1, l₁ ++ a :: b :: l₂), (by simp only [length_middle]; push_cast; omega :
          ((((l₁ ++ a :: b :: l₂).length : ℤ))) - ((0 : ℕ) + 1) = (n : ℤ))⟩ = 0 :=
      mwClassDeg_eq_zero_of_eta' hsq 0 _ hne _
    show mwClassDeg F (n : ℤ) ⟨(0, l₁ ++ (a * b) :: l₂), _⟩ =
      mwClassDeg F (n : ℤ) ⟨(0, l₁ ++ a :: l₂), _⟩ + mwClassDeg F (n : ℤ) ⟨(0, l₁ ++ b :: l₂), _⟩
    rw [mwClassDeg_twisted (F := F) 0 a b l₁ l₂ rfl rfl rfl rfl _ _ _
      (by simp only [length_middle]; push_cast; omega :
        ((((l₁ ++ a :: b :: l₂).length : ℤ))) - ((0 : ℕ) + 1) = (n : ℤ)),
      hzero, add_zero]
  · show mwLiftFree n _ = 0
    rw [mwLiftFree_of]
    exact mwClassDeg_steinberg (F := F) 0 ha l₁ l₂ rfl _

/-- **The inverse of the forgetful morphism** over a quadratically closed field. -/
def mwLift (hsq : ∀ x : F, ∃ y : F, x = y * y) (n : ℕ) :
    MilnorKDeg F n →+ MilnorWittKDeg F (n : ℤ) :=
  QuotientAddGroup.lift _ (mwLiftFree n) (mwLiftFree_ker hsq n)

@[simp]
theorem mwLift_class (hsq : ∀ x : F, ∃ y : F, x = y * y) (n : ℕ) (s : MilnorSymbolDeg F n) :
    mwLift hsq n (milnorClassDeg F n s) = mwLiftWord n s := by
  show mwLiftFree n (FreeAbelianGroup.of s) = _
  rw [mwLiftFree_of]

theorem mwForget_comp_mwLift (hsq : ∀ x : F, ∃ y : F, x = y * y) (n : ℕ) :
    (mwForget n).comp (mwLift hsq n) = AddMonoidHom.id (MilnorKDeg F n) := by
  refine milnorKDeg_hom_ext F fun s => ?_
  rw [AddMonoidHom.comp_apply, mwLift_class, mwLiftWord, mwForget_class, AddMonoidHom.id_apply]
  rfl

theorem mwLift_comp_mwForget (hsq : ∀ x : F, ∃ y : F, x = y * y) (n : ℕ) :
    (mwLift hsq n).comp (mwForget n) = AddMonoidHom.id (MilnorWittKDeg F (n : ℤ)) := by
  refine mwKDeg_hom_ext F fun w => ?_
  rw [AddMonoidHom.comp_apply, mwForget_class, AddMonoidHom.id_apply]
  obtain ⟨⟨k, l⟩, p⟩ := w
  cases k with
  | zero =>
    show mwLift hsq n (milnorClassDeg F n ⟨l, _⟩) = _
    rw [mwLift_class]
    rfl
  | succ k =>
    have hne : l ≠ [] := by
      intro hl
      rw [hl] at p
      simp only [List.length_nil] at p
      push_cast at p
      omega
    show mwLift hsq n 0 = _
    rw [map_zero]
    exact (mwClassDeg_eq_zero_of_eta' hsq k l hne p).symm

/-- **`K_n^{MW}(F) ≅ K_n^M(F)` over a quadratically closed field**, for every `n ≥ 0`.  Every word
with an `η` dies, so the Milnor--Witt presentation collapses to the Milnor one. -/
def mwForgetEquiv (hsq : ∀ x : F, ∃ y : F, x = y * y) (n : ℕ) :
    MilnorWittKDeg F (n : ℤ) ≃+ MilnorKDeg F n where
  toFun := mwForget n
  invFun := mwLift hsq n
  left_inv := fun x => by
    have h := DFunLike.congr_fun (mwLift_comp_mwForget hsq n) x
    rwa [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h
  right_inv := fun x => by
    have h := DFunLike.congr_fun (mwForget_comp_mwLift hsq n) x
    rwa [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h
  map_add' := map_add _

/-- **`K_0^{MW}(F) ≅ ℤ`** over a quadratically closed field: the degree-zero Milnor--Witt group is
the Grothendieck--Witt group, and rank is its only invariant. -/
def mwForgetEquivZero (hsq : ∀ x : F, ∃ y : F, x = y * y) :
    MilnorWittKDeg F ((0 : ℕ) : ℤ) ≃+ ℤ :=
  (mwForgetEquiv hsq 0).trans (milnorDegZeroEquiv F)

/-- **`K_1^{MW}(F) ≅ Fˣ`** over a quadratically closed field. -/
def mwForgetEquivOne (hsq : ∀ x : F, ∃ y : F, x = y * y) :
    MilnorWittKDeg F ((1 : ℕ) : ℤ) ≃+ Additive Fˣ :=
  (mwForgetEquiv hsq 1).trans (milnorDegOneEquiv F)

end MilnorWittForgetIso

end GaloisForLFunctions.HTGeometry
