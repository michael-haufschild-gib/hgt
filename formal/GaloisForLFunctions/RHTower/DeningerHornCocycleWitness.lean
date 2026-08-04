import GaloisForLFunctions.RHTower.DeningerSimplexOfFun

/-!
# The cocycle identity from a fourth vertex

When no vertex avoids three given vertices and the horn index, the cocycle identity for those three
still holds: apply it to the three triangles they span with a fourth vertex, where a witness always
exists, and cancel the edge to that fourth vertex.  This is where invertibility is used, and it is
what makes the outer horns of a three dimensional simplex fill.

* `deningerHornEdgeElt_comp_above` : the fourth vertex above the three.
* `deningerHornEdgeElt_comp_below` : the fourth vertex below the three.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

variable {G : Type u} [Group G] {m : ℕ} {i : Fin (m + 1)}

/-- **The cocycle identity from a fourth vertex above.** -/
theorem deningerHornEdgeElt_comp_above (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G)
    {a b c w : Fin (m + 1)} (hab : a ≤ b) (hbc : b ≤ c) (hcw : c ≤ w)
    (hai : a ≠ i) (hbi : b ≠ i) (hci : c ≠ i)
    (hnab : a ≠ b) (hnac : a ≠ c) (hnaw : a ≠ w) (hnbc : b ≠ c) (hnbw : b ≠ w) (hncw : c ≠ w) :
    deningerEdgeElt u ⟨deningerStdEdgeOf (hab.trans hbc),
        deningerEdgeOf_mem_horn i (hab.trans hbc) b hbi (Ne.symm hnab) hnbc⟩ =
      deningerEdgeElt u ⟨deningerStdEdgeOf hbc,
          deningerEdgeOf_mem_horn i hbc a hai hnab hnac⟩ *
        deningerEdgeElt u ⟨deningerStdEdgeOf hab,
          deningerEdgeOf_mem_horn i hab c hci (Ne.symm hnac) (Ne.symm hnbc)⟩ := by
  have h1 := deningerHornEdgeElt_comp u hab (hbc.trans hcw) c hci (Ne.symm hnac)
    (Ne.symm hnbc) hncw
  have h2 := deningerHornEdgeElt_comp u hbc hcw a hai hnab hnac hnaw
  have h3 := deningerHornEdgeElt_comp u (hab.trans hbc) hcw b hbi (Ne.symm hnab) hnbc hnbw
  refine mul_left_cancel (a := deningerEdgeElt u ⟨deningerStdEdgeOf hcw,
    deningerEdgeOf_mem_horn i hcw a hai hnac hnaw⟩) ?_
  rw [← h3, h1, h2, mul_assoc]

/-- **The cocycle identity from a fourth vertex below.** -/
theorem deningerHornEdgeElt_comp_below (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G)
    {w a b c : Fin (m + 1)} (hwa : w ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hai : a ≠ i) (hbi : b ≠ i) (hci : c ≠ i)
    (hnwa : w ≠ a) (hnwb : w ≠ b) (hnwc : w ≠ c) (hnab : a ≠ b) (hnac : a ≠ c) (hnbc : b ≠ c) :
    deningerEdgeElt u ⟨deningerStdEdgeOf (hab.trans hbc),
        deningerEdgeOf_mem_horn i (hab.trans hbc) b hbi (Ne.symm hnab) hnbc⟩ =
      deningerEdgeElt u ⟨deningerStdEdgeOf hbc,
          deningerEdgeOf_mem_horn i hbc a hai hnab hnac⟩ *
        deningerEdgeElt u ⟨deningerStdEdgeOf hab,
          deningerEdgeOf_mem_horn i hab c hci (Ne.symm hnac) (Ne.symm hnbc)⟩ := by
  have h1 := deningerHornEdgeElt_comp u hwa hab c hci (Ne.symm hnwc) (Ne.symm hnac)
    (Ne.symm hnbc)
  have h2 := deningerHornEdgeElt_comp u (hwa.trans hab) hbc a hai (Ne.symm hnwa) hnab hnac
  have h3 := deningerHornEdgeElt_comp u hwa (hab.trans hbc) b hbi (Ne.symm hnwb) (Ne.symm hnab)
    hnbc
  refine mul_right_cancel (b := deningerEdgeElt u ⟨deningerStdEdgeOf hwa,
    deningerEdgeOf_mem_horn i hwa c hci (Ne.symm hnwc) (Ne.symm hnac)⟩) ?_
  rw [← h3, h2, h1, mul_assoc]

/-- **The cocycle identity from a fourth vertex between the first two.** -/
theorem deningerHornEdgeElt_comp_midLeft (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G)
    {a w b c : Fin (m + 1)} (haw : a ≤ w) (hwb : w ≤ b) (hbc : b ≤ c)
    (hai : a ≠ i) (hbi : b ≠ i) (hci : c ≠ i)
    (hnaw : a ≠ w) (hnab : a ≠ b) (hnac : a ≠ c) (hnwb : w ≠ b) (hnwc : w ≠ c) (hnbc : b ≠ c) :
    deningerEdgeElt u ⟨deningerStdEdgeOf ((haw.trans hwb).trans hbc),
        deningerEdgeOf_mem_horn i ((haw.trans hwb).trans hbc) b hbi (Ne.symm hnab) hnbc⟩ =
      deningerEdgeElt u ⟨deningerStdEdgeOf hbc,
          deningerEdgeOf_mem_horn i hbc a hai hnab hnac⟩ *
        deningerEdgeElt u ⟨deningerStdEdgeOf (haw.trans hwb),
          deningerEdgeOf_mem_horn i (haw.trans hwb) c hci (Ne.symm hnac) (Ne.symm hnbc)⟩ := by
  have h1 := deningerHornEdgeElt_comp u haw hwb c hci (Ne.symm hnac) (Ne.symm hnwc)
    (Ne.symm hnbc)
  have h2 := deningerHornEdgeElt_comp u haw (hwb.trans hbc) b hbi (Ne.symm hnab)
    (Ne.symm hnwb) hnbc
  have h3 := deningerHornEdgeElt_comp u hwb hbc a hai hnaw hnab hnac
  rw [h2, h3, h1, mul_assoc]

/-- **The cocycle identity from a fourth vertex between the last two.** -/
theorem deningerHornEdgeElt_comp_midRight (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G)
    {a b w c : Fin (m + 1)} (hab : a ≤ b) (hbw : b ≤ w) (hwc : w ≤ c)
    (hai : a ≠ i) (hbi : b ≠ i) (hci : c ≠ i)
    (hnab : a ≠ b) (hnaw : a ≠ w) (hnac : a ≠ c) (hnbw : b ≠ w) (hnbc : b ≠ c) (hnwc : w ≠ c) :
    deningerEdgeElt u ⟨deningerStdEdgeOf (hab.trans (hbw.trans hwc)),
        deningerEdgeOf_mem_horn i (hab.trans (hbw.trans hwc)) b hbi (Ne.symm hnab) hnbc⟩ =
      deningerEdgeElt u ⟨deningerStdEdgeOf (hbw.trans hwc),
          deningerEdgeOf_mem_horn i (hbw.trans hwc) a hai hnab hnac⟩ *
        deningerEdgeElt u ⟨deningerStdEdgeOf hab,
          deningerEdgeOf_mem_horn i hab c hci (Ne.symm hnac) (Ne.symm hnbc)⟩ := by
  have h1 := deningerHornEdgeElt_comp u hab hbw c hci (Ne.symm hnac) (Ne.symm hnbc)
    (Ne.symm hnwc)
  have h2 := deningerHornEdgeElt_comp u (hab.trans hbw) hwc b hbi (Ne.symm hnab) hnbw hnbc
  have h3 := deningerHornEdgeElt_comp u hbw hwc a hai hnab hnaw hnac
  rw [h2, h3, h1, mul_assoc]

/-- **The cocycle identity holds for any three vertices**, for a simplex with at least four
vertices: either some vertex avoids the three and the horn index, or the horn index is the fourth
vertex and the identity follows from the three triangles it spans with them. -/
theorem deningerHornEdgeElt_comp_general (hm : 3 ≤ m)
    (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G) {a b c : Fin (m + 1)}
    (hab : a ≤ b) (hbc : b ≤ c) (hnab : a ≠ b) (hnbc : b ≠ c) (hnac : a ≠ c)
    (mac : deningerStdEdgeOf.{u} (hab.trans hbc) ∈ (horn.{u} m i).obj (op (mk 1)))
    (mbc : deningerStdEdgeOf.{u} hbc ∈ (horn.{u} m i).obj (op (mk 1)))
    (mab : deningerStdEdgeOf.{u} hab ∈ (horn.{u} m i).obj (op (mk 1))) :
    deningerEdgeElt u ⟨deningerStdEdgeOf (hab.trans hbc), mac⟩ =
      deningerEdgeElt u ⟨deningerStdEdgeOf hbc, mbc⟩ *
        deningerEdgeElt u ⟨deningerStdEdgeOf hab, mab⟩ := by
  by_cases hex : ∃ w : Fin (m + 1), w ≠ i ∧ w ≠ a ∧ w ≠ b ∧ w ≠ c
  · obtain ⟨w, hwi, hwa, hwb, hwc⟩ := hex
    exact deningerHornEdgeElt_comp u hab hbc w hwi hwa hwb hwc
  · push Not at hex
    have hval : ∀ t : ℕ, t < m + 1 →
        t = (i : ℕ) ∨ t = (a : ℕ) ∨ t = (b : ℕ) ∨ t = (c : ℕ) := by
      intro t ht
      by_cases h1 : (⟨t, ht⟩ : Fin (m + 1)) = i
      · exact Or.inl (congrArg Fin.val h1)
      by_cases h2 : (⟨t, ht⟩ : Fin (m + 1)) = a
      · exact Or.inr (Or.inl (congrArg Fin.val h2))
      by_cases h3 : (⟨t, ht⟩ : Fin (m + 1)) = b
      · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val h3)))
      · exact Or.inr (Or.inr (Or.inr (congrArg Fin.val (hex _ h1 h2 h3))))
    have hab' : (a : ℕ) < (b : ℕ) := lt_of_le_of_ne hab (fun h => hnab (Fin.ext h))
    have hbc' : (b : ℕ) < (c : ℕ) := lt_of_le_of_ne hbc (fun h => hnbc (Fin.ext h))
    have h0 := hval 0 (by omega)
    have h1 := hval 1 (by omega)
    have h2 := hval 2 (by omega)
    have h3 := hval 3 (by omega)
    have hia : (i : ℕ) ≠ (a : ℕ) := by omega
    have hib : (i : ℕ) ≠ (b : ℕ) := by omega
    have hic : (i : ℕ) ≠ (c : ℕ) := by omega
    have hai : a ≠ i := fun h => hia (congrArg Fin.val h).symm
    have hbi : b ≠ i := fun h => hib (congrArg Fin.val h).symm
    have hci : c ≠ i := fun h => hic (congrArg Fin.val h).symm
    rcases Nat.lt_trichotomy (i : ℕ) (a : ℕ) with hlt | heq | hgt
    · exact deningerHornEdgeElt_comp_below u (le_of_lt hlt) hab hbc hai hbi hci
        (fun h => hia (congrArg Fin.val h)) (fun h => hib (congrArg Fin.val h))
        (fun h => hic (congrArg Fin.val h)) hnab hnac hnbc
    · exact absurd heq hia
    · rcases Nat.lt_trichotomy (i : ℕ) (b : ℕ) with hlt2 | heq2 | hgt2
      · exact deningerHornEdgeElt_comp_midLeft u (le_of_lt hgt) (le_of_lt hlt2) hbc hai hbi hci
          (fun h => hia (congrArg Fin.val h).symm) hnab hnac
          (fun h => hib (congrArg Fin.val h)) (fun h => hic (congrArg Fin.val h)) hnbc
      · exact absurd heq2 hib
      · rcases Nat.lt_trichotomy (i : ℕ) (c : ℕ) with hlt3 | heq3 | hgt3
        · exact deningerHornEdgeElt_comp_midRight u hab (le_of_lt hgt2) (le_of_lt hlt3) hai hbi hci
            hnab (fun h => hia (congrArg Fin.val h).symm) hnac
            (fun h => hib (congrArg Fin.val h).symm) hnbc
            (fun h => hic (congrArg Fin.val h))
        · exact absurd heq3 hic
        · exact deningerHornEdgeElt_comp_above u hab hbc (le_of_lt hgt3) hai hbi hci hnab hnac
            (fun h => hia (congrArg Fin.val h).symm) hnbc
            (fun h => hib (congrArg Fin.val h).symm) (fun h => hic (congrArg Fin.val h).symm)

end RHTower
