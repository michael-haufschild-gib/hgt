import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalWhittaker
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerHarishChandraProduct
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.SimpleCharacterExpansion

/-! Iterated induction of cuspidal characters has an irreducible constituent
with nonzero standard Whittaker trace. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions

namespace GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

/-- A genuine character with nonzero Whittaker trace has a generic irreducible constituent. -/
theorem exists_generic_constituent_of_wh_ne_zero {n : ℕ} (ψ : AddChar (ZMod g) ℂ)
    {χ : Gn g n → ℂ} (hχ : IsChar χ) (hwh : wh ψ χ ≠ 0) :
    ∃ η : Gn g n → ℂ, IsIrr η ∧ wh ψ η ≠ 0 ∧ ip χ η ≠ 0 := by
  have hclass : IsClass χ := by
    obtain ⟨V, hV⟩ := hχ
    intro x y
    exact (hV (y * x * y⁻¹)).symm.trans ((V.char_conj x y).trans (hV x))
  have hPair (α β : Gn g n → ℂ) : ip α β = characterPairing (Gn g n) β α := by
    rw [ip, characterPairing, Nat.card_eq_fintype_card]
  have hvirt : gg ψ n ∈ virtualCharacterGroup (Gn g n) := by
    rw [gg_eq_monomialCharacter]
    exact genuineCharacterMonoid_le_virtualCharacterGroup _
      (monomialGenuineCharacter _ _ (whittakerCharacter ψ n)).property
  have hne : characterPairing (Gn g n) (gg ψ n) χ ≠ 0 := by
    rw [← hPair χ (gg ψ n), ip_gg ψ n χ hclass]
    exact hwh
  obtain ⟨η, ⟨V, hV, he⟩, hGη, hχη⟩ := CuspGL.exists_common_simple_of_pairing_ne_zero hvirt hne
  have hη : IsClass η := fun x y =>
    (congrFun he (y * x * y⁻¹)).symm.trans ((V.char_conj x y).trans (congrFun he x))
  refine ⟨η, ⟨V, hV, congrFun he⟩, ?_, ?_⟩
  · rw [← ip_gg ψ n η hη, hPair η (gg ψ n)]
    exact hGη
  · rw [hPair χ η, characterPairing_comm _ η χ]
    exact hχη

private theorem isChar_of_cusp {n : ℕ} {χ : Gn g n → ℂ} (hχ : IsCusp χ) : IsChar χ := by
  obtain ⟨V, _, hV⟩ := hχ.2.1
  exact ⟨V, hV⟩

private theorem wh_empty_product_ne_zero (ψ : AddChar (ZMod g) ℂ) :
    wh ψ (hcL ([] : List (Pc g)) 0) ≠ 0 := by
  let V : FDRep ℂ (Gn g 0) := FDRep.of (Representation.trivial ℂ (Gn g 0) ℂ)
  have hV : V.character = hcL ([] : List (Pc g)) 0 := by
    funext x
    change LinearMap.trace ℂ ℂ ((Representation.trivial ℂ (Gn g 0) ℂ) x) = 1
    simp [Representation.trivial]
  rw [← hV]
  apply wh_ne_zero_of_vector ψ V (1 : ℂ) one_ne_zero
  intro u
  have hu : u = 1 := Subsingleton.elim _ _
  rw [hu]
  simp

theorem stdAddChar_ne_one : (ZMod.stdAddChar : AddChar (ZMod g) ℂ) ≠ 1 := by
  intro h
  have he : ZMod.stdAddChar (1 : ZMod g) = (ZMod.stdAddChar : AddChar (ZMod g) ℂ) 0 := by simp [h]
  exact one_ne_zero (ZMod.injective_stdAddChar he)

/-- Nonzero standard Whittaker trace persists under iterated induction of cuspidals. -/
theorem wh_hcL_ne_zero_of_cusp (L : List (Pc g)) (hL : ∀ p ∈ L, IsCusp p.2) :
    wh ZMod.stdAddChar (hcL L (degL L)) ≠ 0 := by
  induction L with
  | nil => exact wh_empty_product_ne_zero ZMod.stdAddChar
  | cons p L ih =>
    have hp := hL p List.mem_cons_self
    have ht (q : Pc g) (hq : q ∈ L) : IsCusp q.2 := hL q (List.mem_cons_of_mem p hq)
    change wh ZMod.stdAddChar (hc p.1 (degL L) p.2 (hcL L (degL L)) (p.1 + degL L)) ≠ 0
    rw [wh_hc_mul ZMod.stdAddChar (stdAddChar_ne_one (g := g)) (isChar_of_cusp hp)
      (isChar_hcL L (fun q hq => isChar_of_cusp (ht q hq)))]
    exact mul_ne_zero (wh_std_ne_zero_of_cuspidal hp) (ih ht)

/-- Every Harish–Chandra product of cuspidals has a generic irreducible constituent. -/
theorem exists_generic_constituent_hcL (L : List (Pc g)) (hL : ∀ p ∈ L, IsCusp p.2) :
    ∃ η : Gn g (degL L) → ℂ, IsIrr η ∧ wh ZMod.stdAddChar η ≠ 0 ∧ ip (hcL L (degL L)) η ≠ 0 :=
  exists_generic_constituent_of_wh_ne_zero ZMod.stdAddChar
    (isChar_hcL L (fun p hp => isChar_of_cusp (hL p hp))) (wh_hcL_ne_zero_of_cusp L hL)

end GlobalTheory.GLq
