import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.SelectedBlockCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ListParabolicDoubleCosets
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalRadicalReindex
import GaloisForLFunctions.RHTower.Artin.ArtinMonomialSpan

/-! When a flag is allocated to two blocks without splits, the overlap
projects onto the two flag parabolics of the selected sublists. -/

noncomputable section
open GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g a b : ℕ} [Fact g.Prime]
variable (L : List (Pc g)) (hL : degL L = a + b) (S : Finset (Fin L.length))
variable (hA : degL (selectBlocks L S) = a) (hB : degL (selectBlocks L Sᶜ) = b)

local notation "L₁" => selectBlocks L S
local notation "L₂" => selectBlocks L Sᶜ
local notation "P" => listParabolicAt L hL
local notation "P₁" => listParabolicAt L₁ hA
local notation "P₂" => listParabolicAt L₂ hB
local notation "Q" => twoBlockParabolic g a b
local notation "σ" => splitBlockPermutation L hL S hA hB
local notation "w" => permutationUnit (g := g) σ
local notation "O" => doubleCosetOverlap P Q w
local notation "C" => doubleCosetOverlapConj P Q w

private theorem leftLevi_mem (u : O) : (twoBlockLevi (C u)).1 ∈ P₁ := by
  apply (mem_listParabolicAt_iff L₁ hA _).mpr
  intro i j hij
  change tl a (w⁻¹ * u.val.val * w : Gn g (a + b)).val i j = 0
  rw [tl_apply_add, permutationUnit_conj_apply,
    splitBlockPermutation_castAdd, splitBlockPermutation_castAdd]
  apply (mem_listParabolicAt_iff L hL _).mp u.val.property
  rw [listBlockOfAt_selectBlockCoordinate, listBlockOfAt_selectBlockCoordinate]
  exact (selectedBlockIndex L S).strictMono hij

private theorem rightLevi_mem (u : O) : (twoBlockLevi (C u)).2 ∈ P₂ := by
  apply (mem_listParabolicAt_iff L₂ hB _).mpr
  intro i j hij
  change br a b (w⁻¹ * u.val.val * w : Gn g (a + b)).val i j = 0
  rw [br_apply_add, permutationUnit_conj_apply,
    splitBlockPermutation_natAdd, splitBlockPermutation_natAdd]
  apply (mem_listParabolicAt_iff L hL _).mp u.val.property
  rw [listBlockOfAt_selectBlockCoordinate, listBlockOfAt_selectBlockCoordinate]
  exact (selectedBlockIndex L Sᶜ).strictMono hij

/-- Conjugation followed by the two-block Levi projection restricts to
the flag parabolics on the two selected lists. -/
def splitOverlapProjection : O →* P₁ × P₂ where
  toFun u := (⟨(twoBlockLevi (C u)).1, leftLevi_mem L hL S hA hB u⟩,
    ⟨(twoBlockLevi (C u)).2, rightLevi_mem L hL S hA hB u⟩)
  map_one' := by
    have h := map_one (twoBlockLevi.comp C)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  map_mul' u v := by
    have h := map_mul (twoBlockLevi.comp C) u v
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- Block diagonal matrices give a section of the projected overlap. -/
theorem splitOverlapProjection_surjective :
    Function.Surjective (splitOverlapProjection L hL S hA hB) := by
  rintro ⟨A, B⟩
  let y := upperBlockUnit A.val 0 B.val
  let x := w * y * w⁻¹
  have hy : y ∈ Q := inPar_upperBlockMatrix _ _ _
  have hxy : w⁻¹ * x * w = y := by
    dsimp only [x]
    group
  have he (i j : Fin (a + b)) : x.val (σ i) (σ j) = y.val i j := by
    rw [← hxy, permutationUnit_conj_apply]
  have hx : x ∈ P := by
    apply (mem_listParabolicAt_iff L hL x).mpr
    intro i j hij
    obtain ⟨i, rfl⟩ := Equiv.surjective σ i
    obtain ⟨j, rfl⟩ := Equiv.surjective σ j
    rw [he]
    change upperBlockMatrix A.val.val 0 B.val.val i j = 0
    revert hij
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro h
      simp only [splitBlockPermutation_castAdd, listBlockOfAt_selectBlockCoordinate] at h
      have hj := (selectedBlockIndex L S).strictMono.lt_iff_lt.mp h
      simpa [upperBlockMatrix] using (mem_listParabolicAt_iff L₁ hA _).mp A.property i j hj
    · intro _
      simp [upperBlockMatrix]
    · intro _
      simp [upperBlockMatrix]
    · intro h
      simp only [splitBlockPermutation_natAdd, listBlockOfAt_selectBlockCoordinate] at h
      have hj := (selectedBlockIndex L Sᶜ).strictMono.lt_iff_lt.mp h
      simpa [upperBlockMatrix] using (mem_listParabolicAt_iff L₂ hB _).mp B.property i j hj
  let u : O := ⟨⟨x, hx⟩, (mem_doubleCosetOverlap P Q w ⟨x, hx⟩).mpr (hxy.symm ▸ hy)⟩
  have hu : C u = ⟨y, hy⟩ := Subtype.ext hxy
  have h : twoBlockLevi (C u) = (A.val, B.val) := by
    rw [hu]
    exact twoBlockLevi_upperBlockUnit A.val 0 B.val
  exact ⟨u, Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))⟩

/-- The left projected block is the corresponding original block in its
original coordinates. -/
theorem splitOverlapProjection_left_apply (u : O) (k : Fin (L₁).length)
    (i j : Fin ((L₁).get k).1) :
    (listBlockLeviAt L₁ hA k (splitOverlapProjection L hL S hA hB u).1).val i j =
      (listBlockLeviAt L hL (selectedBlockIndex L S k) u.val).val
        (Fin.cast (congrArg Sigma.fst (selectBlocks_get L S k)) i)
        (Fin.cast (congrArg Sigma.fst (selectBlocks_get L S k)) j) := by
  rw [listBlockLeviAt_apply, listBlockLeviAt_apply]
  change tl a (w⁻¹ * u.val.val * w : Gn g (a + b)).val
    (listBlockEmbeddingAt L₁ hA k i) (listBlockEmbeddingAt L₁ hA k j) = _
  rw [tl_apply_add, permutationUnit_conj_apply, splitBlockPermutation_castAdd,
    splitBlockPermutation_castAdd, selectBlockCoordinate_apply, selectBlockCoordinate_apply]

/-- The right projected block is the corresponding original block in its
original coordinates. -/
theorem splitOverlapProjection_right_apply (u : O) (k : Fin (L₂).length)
    (i j : Fin ((L₂).get k).1) :
    (listBlockLeviAt L₂ hB k (splitOverlapProjection L hL S hA hB u).2).val i j =
      (listBlockLeviAt L hL (selectedBlockIndex L Sᶜ k) u.val).val
        (Fin.cast (congrArg Sigma.fst (selectBlocks_get L Sᶜ k)) i)
        (Fin.cast (congrArg Sigma.fst (selectBlocks_get L Sᶜ k)) j) := by
  rw [listBlockLeviAt_apply, listBlockLeviAt_apply]
  change br a b (w⁻¹ * u.val.val * w : Gn g (a + b)).val
    (listBlockEmbeddingAt L₂ hB k i) (listBlockEmbeddingAt L₂ hB k j) = _
  rw [br_apply_add, permutationUnit_conj_apply, splitBlockPermutation_natAdd,
    splitBlockPermutation_natAdd, selectBlockCoordinate_apply, selectBlockCoordinate_apply]

omit [Fact g.Prime] in
private theorem block_character_eq_of_entries {p q : Pc g} (h : p = q)
    (X : Gn g p.1) (Y : Gn g q.1) (he : ∀ i j : Fin p.1,
      X.val i j = Y.val (Fin.cast (congrArg Sigma.fst h) i) (Fin.cast (congrArg Sigma.fst h) j)) :
    p.2 X = q.2 Y := by
  subst q
  exact congrArg p.2 (Units.ext (Matrix.ext he))

/-- On the overlap, the original inducing character is the product of
the inducing characters of the selected flags. -/
theorem listParabolicCharacterAt_splitOverlapProjection (u : O) :
    listParabolicCharacterAt L hL u.val =
      listParabolicCharacterAt L₁ hA (splitOverlapProjection L hL S hA hB u).1 *
        listParabolicCharacterAt L₂ hB (splitOverlapProjection L hL S hA hB u).2 := by
  let f (k : Fin L.length) := (L.get k).2 (listBlockLeviAt L hL k u.val)
  let π := splitOverlapProjection L hL S hA hB
  have h₁ : listParabolicCharacterAt L₁ hA (π u).1 = ∏ k ∈ S, f k := by
    rw [listParabolicCharacterAt_eq_prod, ← prod_selectedBlockIndex L S f]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact block_character_eq_of_entries (selectBlocks_get L S k) _ _
      (splitOverlapProjection_left_apply L hL S hA hB u k)
  have h₂ : listParabolicCharacterAt L₂ hB (π u).2 = ∏ k ∈ Sᶜ, f k := by
    rw [listParabolicCharacterAt_eq_prod, ← prod_selectedBlockIndex L Sᶜ f]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact block_character_eq_of_entries (selectBlocks_get L Sᶜ k) _ _
      (splitOverlapProjection_right_apply L hL S hA hB u k)
  change listParabolicCharacterAt L hL u.val =
    listParabolicCharacterAt L₁ hA (π u).1 * listParabolicCharacterAt L₂ hB (π u).2
  rw [h₁, h₂, listParabolicCharacterAt_eq_prod]
  have ha : Finset.univ.filter (fun k => k ∈ S) = S := by ext k; simp
  have hb : Finset.univ.filter (fun k => k ∉ S) = Sᶜ := by ext k; simp
  simpa only [ha, hb] using
    (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => k ∈ S) f).symm

/-- The kernel of the split overlap projection cancels in the normalized
pairing, leaving the product of the two pairings on the selected flags. -/
theorem doubleCosetPairing_splitBlockPermutation (φ : Gn g a → ℂ) (ψ : Gn g b → ℂ) :
    doubleCosetPairing P Q (listParabolicCharacterAt L hL)
      (fun q => φ (twoBlockLevi q).1 * ψ (twoBlockLevi q).2) w =
      characterPairing P₁ (listParabolicCharacterAt L₁ hA) (fun u => φ u.val) *
        characterPairing P₂ (listParabolicCharacterAt L₂ hB) (fun u => ψ u.val) := by
  letI : Fintype O := Fintype.ofFinite _
  let π := splitOverlapProjection L hL S hA hB
  have hπ : Function.Surjective π := splitOverlapProjection_surjective L hL S hA hB
  let c := (Nat.card π.ker : ℂ)
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcard : (Nat.card O : ℂ) = c * (Nat.card (P₁ × P₂) : ℂ) := by
    have h := sum_comp_surjective_hom π hπ (fun _ => (1 : ℂ))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card] using h
  let f (u : P₁) := φ u.val * listParabolicCharacterAt L₁ hA u⁻¹
  let h (v : P₂) := ψ v.val * listParabolicCharacterAt L₂ hB v⁻¹
  let F (z : P₁ × P₂) := f z.1 * h z.2
  have hF (u : O) :
      (φ (twoBlockLevi (C u)).1 * ψ (twoBlockLevi (C u)).2) *
        listParabolicCharacterAt L hL (u⁻¹ : O).val = F (π u) := by
    rw [listParabolicCharacterAt_splitOverlapProjection L hL S hA hB (u⁻¹)]
    change _ * (listParabolicCharacterAt L₁ hA (π u⁻¹).1 *
      listParabolicCharacterAt L₂ hB (π u⁻¹).2) = _
    rw [map_inv]
    change (φ (π u).1.val * ψ (π u).2.val) *
      (listParabolicCharacterAt L₁ hA (π u).1⁻¹ * listParabolicCharacterAt L₂ hB (π u).2⁻¹) =
        (φ (π u).1.val * listParabolicCharacterAt L₁ hA (π u).1⁻¹) *
        (ψ (π u).2.val * listParabolicCharacterAt L₂ hB (π u).2⁻¹)
    ring
  rw [doubleCosetPairing_eq_pairing]
  unfold characterPairing
  have hs : (∑ u : O, (φ (twoBlockLevi (C u)).1 * ψ (twoBlockLevi (C u)).2) *
      listParabolicCharacterAt L hL (u⁻¹ : O).val) = ∑ u : O, F (π u) :=
    Finset.sum_congr rfl fun u _ => hF u
  rw [hs, sum_comp_surjective_hom π hπ F, hcard,
    mul_inv, mul_comm (c⁻¹), mul_assoc, inv_mul_cancel_left₀ hc]
  rw [Nat.card_prod, Nat.cast_mul, mul_inv, Fintype.sum_prod_type]
  change _ * (∑ u : P₁, ∑ v : P₂, f u * h v) = ((Nat.card P₁ : ℂ)⁻¹ * ∑ u : P₁, f u) *
    ((Nat.card P₂ : ℂ)⁻¹ * ∑ v : P₂, h v)
  rw [← Finset.sum_mul_sum]
  ring

end GlobalTheory.GLq
