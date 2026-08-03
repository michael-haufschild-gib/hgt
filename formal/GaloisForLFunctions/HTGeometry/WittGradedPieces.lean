import GaloisForLFunctions.HTGeometry.QuadraticallyClosedWittRing

/-!
# The graded pieces of the Pfister filtration

The bottom right corner of the fundamental cartesian square of Milnor--Witt `K`-theory is the
associated graded ring `Ī^n = I^n/I^{n+1}` of the fundamental ideal, not the coarser quotient
`W(F)/I^{n+1}`.  This file constructs `Ī^n` and refines the degree-`n` comparison map to land in
it, which is the edge the square actually has.

The graded piece is realized as the image of `I^n` in `W(F)/I^{n+1}`, which is the same subquotient
and makes the comparison with the coarse map an inclusion.

* `WittGraded` : `Ī^n = I^n/I^{n+1}`.
* `milnorGradedMap` : the degree-`n` comparison `K_n^M(F) → Ī^n`.
* `wittGradedVal`, `wittGradedVal_injective`, `wittGradedVal_comp` : the comparison with the coarse
  map `K_n^M(F) → W(F)/I^{n+1}`.
* `wittGradedIdeal_zero` : in degree zero the graded piece is all of `W(F)/I`.
* `wittGraded_subsingleton`, `milnorGradedMap_eq_zero` : the collapse over a quadratically closed
  field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section WittGraded

variable (F : Type*) [Field F]

/-- **The graded pieces of the Pfister filtration**, `Ī^n = I^n/I^{n+1}`, realized as the image of
`I^n` in `W(F)/I^{n+1}`. -/
def wittGradedIdeal (n : ℕ) : Ideal (WittRing F ⧸ fundamentalIdeal F ^ (n + 1)) :=
  (fundamentalIdeal F ^ n).map (Ideal.Quotient.mk (fundamentalIdeal F ^ (n + 1)))

/-- The `n`-th graded piece as a type. -/
abbrev WittGraded (n : ℕ) : Type _ := ↥(wittGradedIdeal F n)

/-- **In degree zero the graded piece is everything**: `I^0 = W(F)`, so `Ī^0 = W(F)/I`. -/
theorem wittGradedIdeal_zero : wittGradedIdeal F 0 = ⊤ := by
  have h0 : fundamentalIdeal F ^ 0 = ⊤ := by simp
  rw [wittGradedIdeal, h0, Ideal.map_top]

/-- Two additive maps out of a free abelian group agree once they agree on the generators. -/
theorem freeAbelianGroup_hom_ext {X : Type*} {A : Type*} [AddCommGroup A]
    {f g : FreeAbelianGroup X →+ A}
    (h : ∀ x, f (FreeAbelianGroup.of x) = g (FreeAbelianGroup.of x)) : f = g := by
  refine AddMonoidHom.ext fun w => ?_
  induction w using FreeAbelianGroup.induction_on with
  | zero => rw [map_zero, map_zero]
  | of x => exact h x
  | neg x ih => rw [map_neg, map_neg, ih]
  | add u v hu hv => rw [map_add, map_add, hu, hv]

/-- The inclusion of the graded piece into the coarse quotient. -/
def wittGradedVal (n : ℕ) : WittGraded F n →+ (WittRing F ⧸ fundamentalIdeal F ^ (n + 1)) :=
  AddMonoidHom.mk' (fun x => (x : WittRing F ⧸ fundamentalIdeal F ^ (n + 1))) fun _ _ => rfl

theorem wittGradedVal_injective (n : ℕ) : Function.Injective (wittGradedVal F n) :=
  fun _ _ h => Subtype.ext h

/-! ### The refined comparison map -/

/-- The `n`-fold Pfister form of a degree-`n` symbol, as an element of `Ī^n`. -/
def pfisterGraded (n : ℕ) (s : MilnorSymbolDeg F n) : WittGraded F n :=
  ⟨Ideal.Quotient.mk (fundamentalIdeal F ^ (n + 1)) (pfisterList F s.val),
    Ideal.mem_map_of_mem _ (by
      have h := pfisterList_mem F s.val
      rwa [s.property] at h)⟩

@[simp]
theorem pfisterGraded_val (n : ℕ) (s : MilnorSymbolDeg F n) :
    wittGradedVal F n (pfisterGraded F n s) =
      Ideal.Quotient.mk (fundamentalIdeal F ^ (n + 1)) (pfisterList F s.val) := rfl

/-- The refined Pfister lift on formal sums of degree-`n` symbols. -/
def pfisterGradedLift (n : ℕ) :
    FreeAbelianGroup (MilnorSymbolDeg F n) →+ WittGraded F n :=
  FreeAbelianGroup.lift (pfisterGraded F n)

@[simp]
theorem pfisterGradedLift_of (n : ℕ) (s : MilnorSymbolDeg F n) :
    pfisterGradedLift F n (FreeAbelianGroup.of s) = pfisterGraded F n s :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The refined lift is the coarse lift**, read inside the graded piece. -/
theorem wittGradedVal_pfisterGradedLift (n : ℕ) (w : FreeAbelianGroup (MilnorSymbolDeg F n)) :
    wittGradedVal F n (pfisterGradedLift F n w) = pfisterLiftDeg F n w := by
  have h : (wittGradedVal F n).comp (pfisterGradedLift F n) = pfisterLiftDeg F n :=
    freeAbelianGroup_hom_ext fun s => by
      rw [AddMonoidHom.comp_apply, pfisterGradedLift_of, pfisterGraded_val, pfisterLiftDeg_of]
  exact congrArg (fun m : FreeAbelianGroup (MilnorSymbolDeg F n) →+ _ => m w) h

/-- **The defining relations of `K_n^M` lie in the kernel of the refined Pfister lift.**  The
graded piece sits inside the coarse quotient, where this is already known. -/
theorem milnorRelSubgroupDeg_le_ker_graded (n : ℕ) :
    milnorRelSubgroupDeg F n ≤ (pfisterGradedLift F n).ker := by
  intro x hx
  have h0 : pfisterLiftDeg F n x = 0 := milnorRelSubgroupDeg_le_ker F n hx
  refine wittGradedVal_injective F n ?_
  rw [wittGradedVal_pfisterGradedLift, h0, map_zero]

/-- **The degree-`n` comparison map into the graded piece**, `K_n^M(F) → I^n/I^{n+1}`.  This is the
bottom edge of the fundamental cartesian square. -/
def milnorGradedMap (n : ℕ) : MilnorKDeg F n →+ WittGraded F n :=
  QuotientAddGroup.lift _ (pfisterGradedLift F n) (milnorRelSubgroupDeg_le_ker_graded F n)

@[simp]
theorem milnorGradedMap_class (n : ℕ) (s : MilnorSymbolDeg F n) :
    milnorGradedMap F n (milnorClassDeg F n s) = pfisterGraded F n s := by
  show pfisterGradedLift F n (FreeAbelianGroup.of s) = _
  rw [pfisterGradedLift_of]

/-- **The refined comparison map lifts the coarse one.** -/
theorem wittGradedVal_comp (n : ℕ) :
    (wittGradedVal F n).comp (milnorGradedMap F n) = milnorPfisterMap F n := by
  refine milnorKDeg_hom_ext F fun s => ?_
  rw [AddMonoidHom.comp_apply, milnorGradedMap_class, pfisterGraded_val, milnorPfisterMap_class]

/-! ### Collapse over a quadratically closed field -/

/-- **Every positive graded piece vanishes** over a quadratically closed field: the Pfister
filtration is already zero at step one, so `I^n` itself is zero for `n ≥ 1`. -/
theorem wittGradedIdeal_eq_bot (hsq : ∀ x : F, ∃ y : F, x = y * y) {n : ℕ} (hn : n ≠ 0) :
    wittGradedIdeal F n = ⊥ := by
  rw [wittGradedIdeal, fundamentalIdeal_pow_eq_bot F hsq hn, Ideal.map_bot]

theorem wittGraded_subsingleton (hsq : ∀ x : F, ∃ y : F, x = y * y) {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (WittGraded F n) := by
  have hb := wittGradedIdeal_eq_bot F hsq hn
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx : (x : WittRing F ⧸ fundamentalIdeal F ^ (n + 1)) = 0 :=
    Ideal.mem_bot.1 (hb.le x.property)
  have hy : (y : WittRing F ⧸ fundamentalIdeal F ^ (n + 1)) = 0 :=
    Ideal.mem_bot.1 (hb.le y.property)
  rw [hx, hy]

/-- **The bottom edge of the fundamental square is zero in every positive degree** over a
quadratically closed field, so the square carries no quadratic information on such a chart. -/
theorem milnorGradedMap_eq_zero (hsq : ∀ x : F, ∃ y : F, x = y * y) {n : ℕ} (hn : n ≠ 0)
    (x : MilnorKDeg F n) : milnorGradedMap F n x = 0 :=
  @Subsingleton.elim _ (wittGraded_subsingleton F hsq hn) _ _

end WittGraded

end

end GaloisForLFunctions.HTGeometry
