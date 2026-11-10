import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitContents

/-!
# Orientation of three residue classes

Two choices of origin cannot put three distinct residues in opposite cyclic
orders. Subtracting the largest residue and taking complementary representatives
reduces this fact to ordinary integer inequalities.
-/

namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

/-- Moving the origin of cyclic residue coordinates cannot reverse the order of three classes. -/
theorem not_reversed_cyclic_order {s : ℕ} [NeZero s] (a b c h r : ZMod s)
    (hac : (a - h).val < (c - h).val) (hcb : (c - h).val < (b - h).val) :
    ¬ ((b - r).val < (c - r).val ∧ (c - r).val < (a - r).val) := by
  rintro ⟨hbc, hca⟩
  have eba : (b - a).val = (b - h).val - (a - h).val := by
    rw [show b - a = (b - h) - (a - h) by ring, ZMod.val_sub (hac.trans hcb).le]
  have ebc : (b - c).val = (b - h).val - (c - h).val := by
    rw [show b - c = (b - h) - (c - h) by ring, ZMod.val_sub hcb.le]
  have eab : (a - b).val = (a - r).val - (b - r).val := by
    rw [show a - b = (a - r) - (b - r) by ring, ZMod.val_sub (hbc.trans hca).le]
  have ecb : (c - b).val = (c - r).val - (b - r).val := by
    rw [show c - b = (c - r) - (b - r) by ring, ZMod.val_sub hbc.le]
  have hab : a - b ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    subst a
    omega
  have hcb0 : c - b ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    subst c
    omega
  have enab : (b - a).val = s - (a - b).val := by
    rw [show b - a = -(a - b) by ring, ZMod.neg_val, if_neg hab]
  have encb : (b - c).val = s - (c - b).val := by
    rw [show b - c = -(c - b) by ring, ZMod.neg_val, if_neg hcb0]
  have hablt := ZMod.val_lt (a - b)
  have hcblt := ZMod.val_lt (c - b)
  omega

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.not_reversed_cyclic_order
