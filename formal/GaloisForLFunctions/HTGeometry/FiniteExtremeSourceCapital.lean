import GaloisForLFunctions.HTGeometry.FiniteExtremeNodePersistence

/-!
# Finite-block centered-source capital across degree

Finite outer interlacing does more than preserve a super-apex sign. At fixed positive mass, the
moving-apex centered residue `(y*x)^2 - 1` at one next-degree outer node is strictly larger than
the residue at every current positive Gauss node.
-/

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Strict centered-source degree capital.** Some next Gauss node has strictly larger
moving-apex residue than every current positive Gauss node. -/
theorem exists_gaussNode_apexCenteredResidue_above_all_below
    {N m : ℕ} (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N)
    {y : ℝ} (hy : 0 < y)
    (hnodes : ∀ x ∈ gaussNodes s m, 0 < x) :
    ∃ z ∈ gaussNodes s (m + 1), 0 < z ∧
      ∀ x ∈ gaussNodes s m, (y * x) ^ 2 - 1 < (y * z) ^ 2 - 1 := by
  classical
  obtain ⟨z, hzmem, hzall⟩ := exists_gaussNode_above_all_below h hmN
  have hcard : (gaussNodes s m).card = m + 1 :=
    gaussNodes_card_below h m (by omega)
  have hnonempty : (gaussNodes s m).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty] at hcard
    omega
  obtain ⟨x0, hx0mem⟩ := hnonempty
  have hzpos : 0 < z := (hnodes x0 hx0mem).trans (hzall x0 hx0mem)
  refine ⟨z, hzmem, hzpos, ?_⟩
  intro x hxmem
  have hxpos : 0 < x := hnodes x hxmem
  have hyxz : y * x < y * z := mul_lt_mul_of_pos_left (hzall x hxmem) hy
  nlinarith [mul_pos hy hxpos, mul_pos hy hzpos]

end HTGeometry

