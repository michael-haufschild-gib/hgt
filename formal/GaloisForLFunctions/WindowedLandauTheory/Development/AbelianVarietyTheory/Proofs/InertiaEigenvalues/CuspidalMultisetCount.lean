import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalInductionGenericConstituents
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GelfandGraevNorm
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CuspidalSupportOrthogonality

/-! Distinct cuspidal multisets have disjoint Harish–Chandra series. Choosing
one generic constituent of each injects the multisets into the Gelfand–Graev support. -/

noncomputable section
open scoped Classical
open GaloisForLFunctions

namespace GlobalTheory.GLq

private theorem degL_toList {g : ℕ} (M : Multiset (Pc g)) :
    degL M.toList = (M.map fun p => p.1).sum := by
  unfold degL
  conv_rhs => rw [← Multiset.coe_toList M]
  rw [Multiset.map_coe, Multiset.sum_coe]

/-- The number of distinct cuspidal multisets of total dimension `n` is
at most the squared Gelfand–Graev norm in that dimension. -/
theorem card_cuspidal_multisets_le (g n : ℕ) [Fact g.Prime] (hn : 0 < n)
    (S : Finset (Multiset (Pc g)))
    (hS : ∀ M ∈ S, (M.map fun p => p.1).sum = n ∧ ∀ p ∈ M, IsCusp p.2) :
    S.card ≤ g ^ n - g ^ (n - 1) := by
  have hd (M : S) : degL M.val.toList = n := (degL_toList M.val).trans (hS M.val M.property).1
  have hc (M : S) (p : Pc g) (hp : p ∈ M.val.toList) : IsCusp p.2 :=
    (hS M.val M.property).2 p (Multiset.mem_toList.mp hp)
  have hf (M : S) : ∃ η : Gn g n → ℂ, IsIrr η ∧ wh ZMod.stdAddChar η ≠ 0 ∧
      ip (hcL M.val.toList n) η ≠ 0 := by
    rw [← hd M]
    exact exists_generic_constituent_hcL _ (hc M)
  let f (M : S) := Classical.choose (hf M)
  have hprop (M : S) : IsIrr (f M) ∧ wh ZMod.stdAddChar (f M) ≠ 0 ∧
      ip (hcL M.val.toList n) (f M) ≠ 0 := Classical.choose_spec (hf M)
  have hchar (M : S) : IsChar (hcL M.val.toList n) := by
    rw [← hd M]
    apply isChar_hcL
    intro p hp
    obtain ⟨V, _, hV⟩ := (hc M p hp).2.1
    exact ⟨V, hV⟩
  let gen (M : S) : GenuineCharacter (Gn g n) :=
    ⟨hcL M.val.toList n, by
      obtain ⟨V, hV⟩ := hchar M
      exact AddSubmonoid.subset_closure ⟨V, funext hV⟩⟩
  have hip (α β : Gn g n → ℂ) : characterPairing (Gn g n) α β = ip α β := by
    rw [characterPairing_comm _ α β, characterPairing, ip, Nat.card_eq_fintype_card]
  have hinj : Function.Injective f := by
    intro M M' he
    apply Subtype.ext
    by_contra hn
    obtain ⟨V, hV, hVeq⟩ := (hprop M').1
    have hα : f M' ∈ CuspGL.simpleCharacterSet (Gn g n) := ⟨V, hV, funext hVeq⟩
    have h1 : characterPairing (Gn g n) (gen M).val (f M') ≠ 0 := by
      change characterPairing (Gn g n) (hcL M.val.toList n) (f M') ≠ 0
      rw [hip, ← he]
      exact (hprop M).2.2
    have h2 : characterPairing (Gn g n) (gen M').val (f M') ≠ 0 := by
      change characterPairing (Gn g n) (hcL M'.val.toList n) (f M') ≠ 0
      rw [hip]
      exact (hprop M').2.2
    exact (CuspGL.pairing_ne_zero_of_common_simple (gen M) (gen M') hα h1 h2)
      (characterPairing_hcL_eq_zero_of_multiset_ne M.val.toList M'.val.toList
        (hd M) (hd M') (hc M) (hc M') (by simpa only [Multiset.coe_toList] using hn))
  have hcard : (S.attach.image f).card = S.card := by
    rw [Finset.card_image_of_injective S.attach hinj, Finset.card_attach]
  rw [← hcard]
  apply GGNorm.card_generic_le ZMod.stdAddChar (stdAddChar_ne_one (g := g)) n hn
  intro η hη
  obtain ⟨M, _, rfl⟩ := Finset.mem_image.mp hη
  exact ⟨(hprop M).1, (hprop M).2.1⟩

end GlobalTheory.GLq
