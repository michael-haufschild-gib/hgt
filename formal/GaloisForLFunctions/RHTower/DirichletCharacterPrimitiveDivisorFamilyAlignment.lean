import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveConductorFamilyTransport
import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveFamilyPackets

/-!
# Alignment with the existing primitive-divisor zero-density aggregate

`DirichletCharacterPrimitiveConductorFamilyTransport` builds a literal
divisor-indexed primitive family.  This file proves it is equivalent, at each
positive divisor conductor, to the corpus's established primitive
nonprincipal family at index `d - 1`.  It therefore identifies the new finite
family sum with `completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount`.

Combining that equality with the closed injective reindexing proves CGL's
all-character-to-primitive-divisor centered-window count reduction on every
certified positive window.
-/

noncomputable section

namespace RHTower

private theorem cglDivisor_sub_one_add_one
    {n : ℕ} (d : (n + 1).divisors) : d.1 - 1 + 1 = d.1 := by
  apply Nat.sub_add_cancel
  by_contra hnot
  have hzero : d.1 = 0 := by omega
  rcases (Nat.mem_divisors.mp d.2).1 with ⟨k, hk⟩
  have hqzero : n + 1 = 0 := by
    calc
      n + 1 = d.1 * k := hk
      _ = 0 := by rw [hzero, zero_mul]
  exact (Nat.mem_divisors.mp d.2).2 hqzero

private noncomputable def cglPrimitiveDivisorMemberToFamily
    {n : ℕ} (d : (n + 1).divisors)
    (ψ : CGLPrimitiveNonprincipalCharacterAtDivisor d) :
    CGLPrimitiveNonprincipalCharacterFamily (d.1 - 1) := by
  let h : d.1 - 1 + 1 = d.1 := cglDivisor_sub_one_add_one d
  let ψ' : DirichletCharacter ℂ (d.1 - 1 + 1) := h.symm ▸ ψ.character
  have hnonprincipal : ψ' ≠ 1 := by
    have transport : ∀ {a b : ℕ} (hab : a = b)
        (η : DirichletCharacter ℂ a), η ≠ 1 → (hab ▸ η) ≠ 1 := by
      intro a b hab η hη
      cases hab
      exact hη
    exact transport h.symm ψ.character ψ.nonprincipal
  refine ⟨⟨ψ', hnonprincipal⟩, ?_⟩
  simp only [cglPrimitiveNonprincipalCharacterFamily, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have transport : ∀ {a b : ℕ} (hab : a = b)
      (η : DirichletCharacter ℂ a), DirichletCharacter.IsPrimitive η →
        DirichletCharacter.IsPrimitive (hab ▸ η) := by
    intro a b hab η hη
    cases hab
    exact hη
  exact transport h.symm ψ.character ψ.primitive

private noncomputable def cglPrimitiveDivisorMemberFromFamily
    {n : ℕ} (d : (n + 1).divisors)
    (ψ : CGLPrimitiveNonprincipalCharacterFamily (d.1 - 1)) :
    CGLPrimitiveNonprincipalCharacterAtDivisor d := by
  let h : d.1 - 1 + 1 = d.1 := cglDivisor_sub_one_add_one d
  let ψ' : DirichletCharacter ℂ d.1 := h ▸ ψ.1.1
  have hnonprincipal : ψ' ≠ 1 := by
    have transport : ∀ {a b : ℕ} (hab : a = b)
        (η : DirichletCharacter ℂ a), η ≠ 1 → (hab ▸ η) ≠ 1 := by
      intro a b hab η hη
      cases hab
      exact hη
    exact transport h ψ.1.1 ψ.1.2
  have hprimitive : DirichletCharacter.IsPrimitive ψ' := by
    classical
    have transport : ∀ {a b : ℕ} (hab : a = b)
        (η : DirichletCharacter ℂ a), DirichletCharacter.IsPrimitive η →
          DirichletCharacter.IsPrimitive (hab ▸ η) := by
      intro a b hab η hη
      cases hab
      exact hη
    exact transport h ψ.1.1 (Finset.mem_filter.mp ψ.2).2
  exact ⟨ψ', hnonprincipal, hprimitive⟩

private theorem cglPrimitiveDivisorMember_ext
    {n : ℕ} {d : (n + 1).divisors}
    (ψ φ : CGLPrimitiveNonprincipalCharacterAtDivisor d)
    (h : ψ.character = φ.character) : ψ = φ := by
  cases ψ
  cases φ
  cases h
  rfl

private theorem cgl_transport_roundtrip_forward
    {a b : ℕ} (h : a = b) (η : DirichletCharacter ℂ b) :
    h ▸ (h.symm ▸ η) = η := by
  cases h
  rfl

private theorem cgl_transport_roundtrip_backward
    {a b : ℕ} (h : a = b) (η : DirichletCharacter ℂ a) :
    h.symm ▸ (h ▸ η) = η := by
  cases h
  rfl

private theorem cglPrimitiveDivisorMember_from_to_character
    {n : ℕ} (d : (n + 1).divisors)
    (ψ : CGLPrimitiveNonprincipalCharacterAtDivisor d) :
    (cglPrimitiveDivisorMemberFromFamily d
      (cglPrimitiveDivisorMemberToFamily d ψ)).character = ψ.character := by
  let h : d.1 - 1 + 1 = d.1 := cglDivisor_sub_one_add_one d
  change h ▸ (h.symm ▸ ψ.character) = ψ.character
  exact cgl_transport_roundtrip_forward h ψ.character

private theorem cglPrimitiveDivisorMember_to_from_character
    {n : ℕ} (d : (n + 1).divisors)
    (ψ : CGLPrimitiveNonprincipalCharacterFamily (d.1 - 1)) :
    ((cglPrimitiveDivisorMemberToFamily d
      (cglPrimitiveDivisorMemberFromFamily d ψ)).1).1 = ψ.1.1 := by
  let h : d.1 - 1 + 1 = d.1 := cglDivisor_sub_one_add_one d
  change h.symm ▸ (h ▸ ψ.1.1) = ψ.1.1
  exact cgl_transport_roundtrip_backward h ψ.1.1

private noncomputable def cglPrimitiveDivisorFamilyEquiv
    {n : ℕ} (d : (n + 1).divisors) :
    CGLPrimitiveNonprincipalCharacterAtDivisor d ≃
      CGLPrimitiveNonprincipalCharacterFamily (d.1 - 1) where
  toFun := cglPrimitiveDivisorMemberToFamily d
  invFun := cglPrimitiveDivisorMemberFromFamily d
  left_inv := by
    intro ψ
    apply cglPrimitiveDivisorMember_ext
    exact cglPrimitiveDivisorMember_from_to_character d ψ
  right_inv := by
    intro ψ
    apply Subtype.ext
    apply Subtype.ext
    exact cglPrimitiveDivisorMember_to_from_character d ψ

private theorem cgl_completedLFunction_transport
    {a b : ℕ} [NeZero a] [NeZero b] (h : a = b)
    (η : DirichletCharacter ℂ a) :
    DirichletCharacter.completedLFunction (h ▸ η) =
      DirichletCharacter.completedLFunction η := by
  cases h
  rfl

private theorem cglPrimitiveDivisorMemberToFamily_character
    {n : ℕ} (d : (n + 1).divisors)
    (ψ : CGLPrimitiveNonprincipalCharacterAtDivisor d) :
    (cglPrimitiveDivisorMemberToFamily d ψ).1.1 =
      (cglDivisor_sub_one_add_one d).symm ▸ ψ.character :=
  rfl

private theorem cglPrimitiveDivisorMember_count_eq_family
    {n : ℕ} (d : (n + 1).divisors)
    (ψ : CGLPrimitiveNonprincipalCharacterAtDivisor d)
    (W : CGLPositiveZeroDensityVerticalWindow) :
    cglPrimitiveDivisorCompletedWindowCount d ψ W =
      completedLFunctionZeroDensityVerticalWindowCount (d.1 - 1)
        (cglPrimitiveDivisorMemberToFamily d ψ).1 W.sigma W.center W.halfWidth := by
  have hfun : DirichletCharacter.completedLFunction
      (cglPrimitiveDivisorMemberToFamily d ψ).1.1 =
        DirichletCharacter.completedLFunction ψ.character := by
    rw [cglPrimitiveDivisorMemberToFamily_character]
    exact cgl_completedLFunction_transport
      (cglDivisor_sub_one_add_one d).symm ψ.character
  unfold cglPrimitiveDivisorCompletedWindowCount
    completedLFunctionZeroDensityVerticalWindowCount
  exact (congrArg (fun f : ℂ → ℂ =>
    (↑(∑ᶠ z, MeromorphicOn.divisor f W.carrier z) : ℝ)) hfun).symm

private theorem cglPrimitiveDivisorFamily_sum_eq_existing
    {n : ℕ} (d : (n + 1).divisors)
    (W : CGLPositiveZeroDensityVerticalWindow) :
    (∑ ψ : CGLPrimitiveNonprincipalCharacterAtDivisor d,
      cglPrimitiveDivisorCompletedWindowCount d ψ W) =
      completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount
        (d.1 - 1) W.sigma W.center W.halfWidth := by
  let e := cglPrimitiveDivisorFamilyEquiv d
  let g : CGLPrimitiveNonprincipalCharacterFamily (d.1 - 1) → ℝ :=
    fun ψ => completedLFunctionZeroDensityVerticalWindowCount (d.1 - 1)
      ψ.1 W.sigma W.center W.halfWidth
  calc
    (∑ ψ : CGLPrimitiveNonprincipalCharacterAtDivisor d,
      cglPrimitiveDivisorCompletedWindowCount d ψ W) =
        ∑ ψ : CGLPrimitiveNonprincipalCharacterAtDivisor d, g (e ψ) := by
      apply Finset.sum_congr rfl
      intro ψ hψ
      exact cglPrimitiveDivisorMember_count_eq_family d ψ W
    _ = ∑ ψ : CGLPrimitiveNonprincipalCharacterFamily (d.1 - 1), g ψ :=
      Equiv.sum_comp e g
    _ = cglPrimitiveNonprincipalFamilyZeroDensityVerticalWindowCount
        (d.1 - 1) W.sigma W.center W.halfWidth := rfl
    _ = completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount
        (d.1 - 1) W.sigma W.center W.halfWidth :=
      cglPrimitiveNonprincipalFamilyZeroDensityVerticalWindowCount_eq
        (d.1 - 1) W.sigma W.center W.halfWidth

/-- The literal primitive divisor family has exactly the same positive-window
count as the corpus's established primitive-divisor aggregate. -/
theorem cglPrimitiveDivisorFamilyWindowCount_eq_existing
    (n : ℕ) (W : CGLPositiveZeroDensityVerticalWindow) :
    cglPrimitiveDivisorFamilyWindowCount n W =
      completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount
        (n + 1) W.sigma W.center W.halfWidth := by
  classical
  let S := (n + 1).divisors
  have hattach : (Finset.univ : Finset (↑S)) = S.attach := by
    ext d
    simp
  unfold cglPrimitiveDivisorFamilyWindowCount
    completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount
  rw [Fintype.sum_sigma]
  calc
    (∑ x : ↑S, ∑ ψ : CGLPrimitiveNonprincipalCharacterAtDivisor x,
      cglPrimitiveDivisorCompletedWindowCount x ψ W) =
        ∑ x : ↑S, completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount
          (x.1 - 1) W.sigma W.center W.halfWidth := by
      apply Finset.sum_congr rfl
      intro x hx
      exact cglPrimitiveDivisorFamily_sum_eq_existing x W
    _ = ∑ x ∈ S, completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount
        (x - 1) W.sigma W.center W.halfWidth := by
      rw [hattach]
      exact Finset.sum_attach S (fun x =>
        completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount
          (x - 1) W.sigma W.center W.halfWidth)

/-- For every certified positive window, the full ambient nonprincipal family
count is bounded by the existing primitive-divisor aggregate at the ambient
modulus. -/
theorem cgl_nonprincipalFamily_zeroDensityVerticalWindowCount_le_existingPrimitiveDivisor
    (n : ℕ) (W : CGLPositiveZeroDensityVerticalWindow) :
    (∑ χ : NonprincipalDirichletCharacter n,
      completedLFunctionZeroDensityVerticalWindowCount n χ W.sigma W.center W.halfWidth) ≤
      completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount
        (n + 1) W.sigma W.center W.halfWidth := by
  calc
    (∑ χ : NonprincipalDirichletCharacter n,
      completedLFunctionZeroDensityVerticalWindowCount n χ W.sigma W.center W.halfWidth) ≤
        cglPrimitiveDivisorFamilyWindowCount n W :=
      cgl_nonprincipalFamily_zeroDensityVerticalWindowCount_le_primitiveDivisorFamily n W
    _ = completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount
        (n + 1) W.sigma W.center W.halfWidth :=
      cglPrimitiveDivisorFamilyWindowCount_eq_existing n W

end RHTower
