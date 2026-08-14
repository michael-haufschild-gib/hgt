import GaloisForLFunctions.HTGeometry.MilnorKResidueSteinberg

/-!
# The residue homomorphism of Milnor `K`-theory

Milnor's residue attached to a discrete valuation with a chosen uniformizer is the `ξ`-component of
the fold of multiplication by `[ū_a] + v(a)ξ` over a symbol.  The fold is additive in each entry and
kills a Steinberg pair, so it descends from formal sums of symbols to Milnor `K`-theory.  Indexing
the fold by the *length* rather than by the list keeps the type of its value independent of the
list, which is what makes the two relations statable without transport.

* `resPairAt` : the fold of the residue steps over a list of a given length.
* `resPairAt_mul`, `resPairAt_steinberg` : **it kills both defining relations.**
* `milnorResPair`, `milnorResidue`, `milnorSpecialization` : **the residue and the
  specialization, as homomorphisms out of `K_n^M(K)`.**
* `milnorResidue_one` : the residue of a degree-one symbol is its valuation.
* `milnorResidue_two` : **the residue in degree two is the tame symbol.**
-/

namespace GaloisForLFunctions.HTGeometry

section ResidueMap

variable {K : Type*} [Field K] {k : Type*} [Field k] (D : ResidueData K k)

/-- The residue fold of a list of the given length, indexed by the length rather than by the
list, so that the type of the value does not depend on the list. -/
noncomputable def resPairAt : ∀ (n : ℕ) (l : List Kˣ), l.length = n →
    MilnorKDeg k n × MilnorKDeg k (n - 1)
  | 0, _, _ => (milnorOne, 0)
  | (_ + 1), [], h => by simp at h
  | (n + 1), (a :: l), h =>
      resStepHom D a n (resPairAt n l (by simpa using h))

@[simp]
theorem resPairAt_zero (l : List Kˣ) (h : l.length = 0) :
    resPairAt D 0 l h = (milnorOne, 0) := rfl

@[simp]
theorem resPairAt_cons (n : ℕ) (a : Kˣ) (l : List Kˣ) (h : (a :: l).length = n + 1) :
    resPairAt D (n + 1) (a :: l) h
      = resStepHom D a n (resPairAt D n l (by simpa using h)) := rfl

/-- **Multilinearity of the residue fold at an interior slot.** -/
theorem resPairAt_mul (a b : Kˣ) (l₁ l₂ : List Kˣ) :
    ∀ (n : ℕ) (pab : (l₁ ++ (a * b) :: l₂).length = n) (pa : (l₁ ++ a :: l₂).length = n)
      (pb : (l₁ ++ b :: l₂).length = n),
      resPairAt D n (l₁ ++ (a * b) :: l₂) pab
        = resPairAt D n (l₁ ++ a :: l₂) pa + resPairAt D n (l₁ ++ b :: l₂) pb := by
  induction l₁ with
  | nil =>
      intro n pab pa pb
      cases n with
      | zero => exact absurd pab (by simp)
      | succ m =>
          show resPairAt D (m + 1) ((a * b) :: l₂) pab
            = resPairAt D (m + 1) (a :: l₂) pa + resPairAt D (m + 1) (b :: l₂) pb
          rw [resPairAt_cons, resPairAt_cons, resPairAt_cons, resStepHom_mul,
            AddMonoidHom.add_apply]
          rfl
  | cons c t ih =>
      intro n pab pa pb
      cases n with
      | zero => exact absurd pab (by simp)
      | succ m =>
          show resPairAt D (m + 1) (c :: (t ++ (a * b) :: l₂)) pab
            = resPairAt D (m + 1) (c :: (t ++ a :: l₂)) pa
              + resPairAt D (m + 1) (c :: (t ++ b :: l₂)) pb
          rw [resPairAt_cons, resPairAt_cons, resPairAt_cons, ih m _ _ _, map_add]
          rfl

/-- **The Steinberg relation for the residue fold.** -/
theorem resPairAt_steinberg {a : Kˣ} (ha : (a : K) ≠ 1) (l₁ l₂ : List Kˣ) :
    ∀ (n : ℕ) (p : (l₁ ++ a :: oneSubUnit ha :: l₂).length = n),
      resPairAt D n (l₁ ++ a :: oneSubUnit ha :: l₂) p = 0 := by
  induction l₁ with
  | nil =>
      intro n p
      cases n with
      | zero => exact absurd p (by simp)
      | succ m =>
          cases m with
          | zero => exact absurd p (by simp)
          | succ m' =>
              show resPairAt D (m' + 1 + 1) (a :: oneSubUnit ha :: l₂) p = 0
              rw [resPairAt_cons, resPairAt_cons]
              exact DFunLike.congr_fun (resStepHom_steinberg D ha m') _
  | cons c t ih =>
      intro n p
      cases n with
      | zero => exact absurd p (by simp)
      | succ m =>
          show resPairAt D (m + 1) (c :: (t ++ a :: oneSubUnit ha :: l₂)) p = 0
          rw [resPairAt_cons, ih m _, map_zero]
          rfl

/-- The residue pair on formal sums of symbols. -/
noncomputable def resPre (n : ℕ) :
    FreeAbelianGroup (MilnorSymbolDeg K n) →+ (MilnorKDeg k n × MilnorKDeg k (n - 1)) :=
  FreeAbelianGroup.lift fun s => resPairAt D n s.val s.property

@[simp]
theorem resPre_of (n : ℕ) (s : MilnorSymbolDeg K n) :
    resPre D n (FreeAbelianGroup.of s) = resPairAt D n s.val s.property :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The residue pair kills the defining relations of Milnor `K`-theory.** -/
theorem resPre_ker (n : ℕ) : milnorRelSubgroupDeg K n ≤ (resPre D n).ker := by
  rw [milnorRelSubgroupDeg, AddSubgroup.closure_le]
  rintro x (⟨a, b, l₁, l₂, h, rfl⟩ | ⟨a, ha, l₁, l₂, h, rfl⟩)
  · show resPre D n _ = 0
    rw [map_sub, map_sub, resPre_of, resPre_of, resPre_of, sub_sub, sub_eq_zero]
    exact resPairAt_mul D a b l₁ l₂ n _ _ _
  · show resPre D n _ = 0
    rw [resPre_of, resPairAt_steinberg]

/-- **The specialization and the residue**, as a single homomorphism into the pair. -/
noncomputable def milnorResPair (n : ℕ) :
    MilnorKDeg K n →+ (MilnorKDeg k n × MilnorKDeg k (n - 1)) :=
  QuotientAddGroup.lift _ (resPre D n) (resPre_ker D n)

@[simp]
theorem milnorResPair_class (n : ℕ) (s : MilnorSymbolDeg K n) :
    milnorResPair D n (milnorClassDeg K n s) = resPairAt D n s.val s.property := by
  show resPre D n (FreeAbelianGroup.of s) = _
  exact resPre_of D n s

/-- **The residue homomorphism.** -/
noncomputable def milnorResidue (n : ℕ) : MilnorKDeg K n →+ MilnorKDeg k (n - 1) :=
  (AddMonoidHom.snd _ _).comp (milnorResPair D n)

/-- **The specialization homomorphism attached to the uniformizer.** -/
noncomputable def milnorSpecialization (n : ℕ) : MilnorKDeg K n →+ MilnorKDeg k n :=
  (AddMonoidHom.fst _ _).comp (milnorResPair D n)

theorem milnorResidue_class (n : ℕ) (s : MilnorSymbolDeg K n) :
    milnorResidue D n (milnorClassDeg K n s) = (resPairAt D n s.val s.property).2 :=
  congrArg Prod.snd (milnorResPair_class D n s)

theorem milnorSpecialization_class (n : ℕ) (s : MilnorSymbolDeg K n) :
    milnorSpecialization D n (milnorClassDeg K n s) = (resPairAt D n s.val s.property).1 :=
  congrArg Prod.fst (milnorResPair_class D n s)

/-- **The residue of a degree-one symbol is its valuation.** -/
theorem milnorResidue_one (a : Kˣ) :
    milnorResidue D 1 (milnorClassDeg K 1 ⟨[a], rfl⟩) = D.val' a • milnorOne :=
  milnorResidue_class D 1 ⟨[a], rfl⟩

/-- **The specialization of a degree-one symbol is the residue of its unit part.** -/
theorem milnorSpecialization_one (a : Kˣ) :
    milnorSpecialization D 1 (milnorClassDeg K 1 ⟨[a], rfl⟩)
      = mulSymbol (D.residueUnit a) 0 milnorOne :=
  milnorSpecialization_class D 1 ⟨[a], rfl⟩

/-- **The residue in degree two is the tame symbol**, written additively:
`∂{a,b} = v(b)[ū_a] - v(a)[ū_b] + v(a)v(b)[-1]`. -/
theorem milnorResidue_two (a b : Kˣ) :
    milnorResidue D 2 (milnorClassDeg K 2 ⟨[a, b], rfl⟩)
      = mulSymbol (D.residueUnit a) 0 (D.val' b • milnorOne)
        + ((-1 : ℤ) * D.val' a) • mulSymbol (D.residueUnit b) 0 milnorOne
        + D.val' a • mulSymbol (-1 : kˣ) 0 (D.val' b • milnorOne) := by
  rw [milnorResidue_class]
  show (resStepHom D a 1 (resPairAt D 1 [b] rfl)).2 = _
  rw [resStepHom_succ_apply]
  simp only [pow_zero, one_mul]
  rfl

end ResidueMap

end GaloisForLFunctions.HTGeometry
