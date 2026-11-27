import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSupportOrthogonality
import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactorOfAnInflatedRepresentation

/-! For a list of pairwise distinct cuspidals, only the identity double
coset contributes to the norm. Its contribution is the product of the block norms. -/

noncomputable section
open scoped Classical
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private theorem sum_irr_inverse_mul {d : ℕ} {χ : Gn g d → ℂ} (hχ : IsIrr χ) :
    ∑ x : Gn g d, χ x * χ x⁻¹ = (Nat.card (Gn g d) : ℂ) := by
  obtain ⟨V, hV, hEq⟩ := hχ
  have hs : χ ∈ CuspGL.simpleCharacterSet (Gn g d) := ⟨V, hV, funext hEq⟩
  have he : characterPairing (Gn g d) χ χ = 1 := (CuspGL.pairing_simple hs hs).trans (if_pos rfl)
  let c : ℂ := Nat.card (Gn g d)
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  change c⁻¹ * (∑ x : Gn g d, χ x * χ x⁻¹) = 1 at he
  calc
    _ = c * (c⁻¹ * ∑ x : Gn g d, χ x * χ x⁻¹) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    _ = c := by rw [he, mul_one]

private theorem listParabolicPairing_one_eq_one (L : List (Pc g)) (hL : degL L = n)
    (hI : ∀ k : Fin L.length, IsIrr (L.get k).2) :
    doubleCosetPairing (listParabolicAt L hL) (listParabolicAt L hL)
      (listParabolicCharacterAt L hL) (listParabolicCharacterAt L hL) 1 = 1 := by
  let P := listParabolicAt L hL
  let O := doubleCosetOverlap P P 1
  letI : Fintype O := Fintype.ofFinite O
  let C := doubleCosetOverlapConj P P 1
  let π : O →* listLeviGroup L := (listLeviProjectionAt L hL).comp O.subtype
  let α := listParabolicCharacterAt L hL
  have hm (u : P) : u ∈ O := (mem_doubleCosetOverlap P P 1 u).mpr (by simp)
  have hs : Function.Surjective π := fun x =>
    ⟨⟨listDiagonalUnitAt L hL x, hm (listDiagonalUnitAt L hL x)⟩,
      funext fun k => listBlockLeviAt_listDiagonalUnitAt L hL x k⟩
  have hC (u : O) : C u = u.val := by
    apply Subtype.ext
    change (1 : Gn g n)⁻¹ * u.val.val * 1 = u.val.val
    simp
  let f (k : Fin L.length) (x : Gn g (L.get k).1) := (L.get k).2 x * (L.get k).2 x⁻¹
  let F (x : listLeviGroup L) := ∏ k : Fin L.length, f k (x k)
  have hF (u : O) : α (C u) * α u.val⁻¹ = F (π u) := by
    rw [hC]
    simp only [α, listParabolicCharacterAt_eq_prod, ← Finset.prod_mul_distrib, map_inv]
    rfl
  have hsum : ∑ x : listLeviGroup L, F x = (Nat.card (listLeviGroup L) : ℂ) := by
    calc
      _ = ∏ k : Fin L.length, ∑ x : Gn g (L.get k).1, f k x := (Fintype.prod_sum f).symm
      _ = ∏ k : Fin L.length, (Nat.card (Gn g (L.get k).1) : ℂ) :=
        Finset.prod_congr rfl fun k _ => sum_irr_inverse_mul (hI k)
      _ = _ := by simp only [Nat.card_eq_fintype_card, Fintype.card_pi, Nat.cast_prod]
  rw [doubleCosetPairing_eq_pairing]
  change (Nat.card O : ℂ)⁻¹ * (∑ u : O, α (C u) * α u.val⁻¹) = 1
  rw [Finset.sum_congr rfl (fun u _ => hF u),
    inv_card_mul_sum_comp_surjective π hs F, hsum,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

/-- The Harish–Chandra product of pairwise distinct cuspidals has norm one. -/
theorem characterPairing_hcL_self_eq_one_of_nodup (L : List (Pc g)) (hL : degL L = n)
    (hχ : ∀ p ∈ L, IsCusp p.2) (hnd : L.Nodup) :
    characterPairing (Gn g n) (hcL L n) (hcL L n) = 1 := by
  let P := listParabolicAt L hL
  let α := listParabolicCharacterAt L hL
  let Q := DoubleCoset.Quotient (P : Set (Gn g n)) P
  letI : Fintype Q := mixedDoubleCosetFintype P P
  let q₀ : Q := DoubleCoset.mk P P 1
  let F (q : Q) := doubleCosetPairing P P α α q.out
  have hchar (p : Pc g) (hp : p ∈ L) : IsChar p.2 := isChar_of_cuspidal (hχ p hp)
  obtain ⟨V, hV⟩ := isChar_listParabolicCharacterAt L hL hchar
  have hα : IsClass α := fun u v =>
    (hV (v * u * v⁻¹)).symm.trans ((V.char_conj u v).trans (hV u))
  have hcus (k : Fin L.length) : IsCusp (L.get k).2 := hχ _ (List.get_mem _ _)
  have hzero (q : Q) (hq : q ≠ q₀) : F q = 0 := by
    by_contra hn
    obtain ⟨σ, hσ⟩ := exists_listParabolic_permutation_rep L L hL hL q.out
    let w : Gn g n := permutationUnit σ
    have hn' : doubleCosetPairing P P α α w ≠ 0 := fun h =>
      hn ((doubleCosetPairing_eq_of_mk_eq P P α α hα hα hσ).symm.trans h)
    obtain ⟨e, he, hlab⟩ := aligned_labels_of_listParabolicPairing_ne_zero L L hL hL σ hcus hcus hn'
    have heq (k : Fin L.length) : e k = k := (List.nodup_iff_injective_get.mp hnd) (hlab k).symm
    have hpres (i : Fin n) : listBlockOfAt L hL (σ i) = listBlockOfAt L hL i := by
      have h := (heq (listBlockOfAt L hL (σ i))).symm.trans (he (σ i))
      simpa only [permutedListBlockOf, σ.symm_apply_apply] using h
    have hw : w ∈ P := (mem_listParabolicAt_iff L hL w).mpr fun i j h => by
      have hij : i ≠ σ j := fun e => (ne_of_lt h)
        (((congrArg (listBlockOfAt L hL) e).trans (hpres j)).symm)
      simp [w, monomialUnit, signedMonomialMatrix, hij]
    have hq₀ : DoubleCoset.mk P P (1 : Gn g n) = DoubleCoset.mk P P w :=
      (DoubleCoset.eq P P _ _).mpr ⟨w, hw, 1, P.one_mem, by simp⟩
    exact hq ((DoubleCoset.out_eq' P P q).symm.trans (hσ.symm.trans hq₀.symm))
  rw [characterPairing_hcL_eq_sum_doubleCosets L L hL hL hchar hchar]
  change ∑ q : Q, F q = 1
  rw [Finset.sum_eq_single q₀ (fun q _ hq => hzero q hq)
    (fun h => (h (Finset.mem_univ q₀)).elim)]
  calc
    F q₀ = doubleCosetPairing P P α α 1 :=
      doubleCosetPairing_eq_of_mk_eq P P α α hα hα (DoubleCoset.out_eq' P P q₀)
    _ = 1 := listParabolicPairing_one_eq_one L hL (fun k => (hcus k).2.1)

/-- Parabolic induction of pairwise distinct cuspidal characters is irreducible. -/
theorem isIrr_hcL_of_nodup (L : List (Pc g)) (hL : degL L = n)
    (hχ : ∀ p ∈ L, IsCusp p.2) (hnd : L.Nodup) : IsIrr (hcL L n) := by
  have hchar : IsChar (hcL L n) := by
    rw [← hL]
    exact isChar_hcL L (fun p hp => isChar_of_cuspidal (hχ p hp))
  obtain ⟨V, hV⟩ := hchar
  have hnorm := characterPairing_hcL_self_eq_one_of_nodup L hL hχ hnd
  rw [← funext hV] at hnorm
  let c : ℂ := Nat.card (Gn g n)
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  change c⁻¹ * (∑ x : Gn g n, V.character x * V.character x⁻¹) = 1 at hnorm
  refine ⟨V, (FDRep.simple_iff_char_is_norm_one V).mpr ?_, hV⟩
  calc
    _ = c * (c⁻¹ * ∑ x : Gn g n, V.character x * V.character x⁻¹) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    _ = c := by rw [hnorm, mul_one]

end GlobalTheory.GLq
