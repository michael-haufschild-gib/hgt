import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Nodes

/-! # A uniform lower bound on the remote probability -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset

/-- Even a closed endpoint prescription retains a fixed fraction of the tail probability beyond the next node. -/
theorem remote_residue_lower {m : ℕ} (b : PrefixData m) (k : ℕ) (hk : 1 ≤ k) :
    (occupationWeight m-occupationWeight (m+1))^m ≤ nodeResidue b k (Fin.last m) := by
  let a := nativeNode m k
  let i := Fin.last m
  have hden : (∏ l ∈ univ.erase i, (a i-a l)) = ∏ j : Fin m, (a i-a j.castSucc) := by
    have hu : univ.erase i = univ.map i.succAboveEmb := by
      conv_lhs => rw [Fin.univ_succAbove m i]
      simp
    rw [hu,Finset.prod_map]
    change (∏ j : Fin m, (a i-a (i.succAbove j))) = _
    simp only [i,Fin.succAbove_last]
  have hi : a i = occupationWeight (m+k) := congrArg occupationWeight (nodeIndex_last m k)
  have hj (j : Fin m) : a j.castSucc = occupationWeight j.val := congrArg occupationWeight (nodeIndex_head k j)
  change _ ≤ (∏ j, (a i-(b j).val)) / ∏ l ∈ univ.erase i, (a i-a l)
  rw [hden,← Finset.prod_div_distrib]
  have hg := occupationWeight_strictAnti (Nat.lt_succ_self m)
  have he := occupationWeight_antitone (show m+1 ≤ m+k by omega)
  have hfactor (j : Fin m) : occupationWeight m-occupationWeight (m+1) ≤ (a i-(b j).val)/(a i-a j.castSucc) := by
    rw [hi,hj,← neg_sub (b j).val,← neg_sub (occupationWeight j.val),neg_div_neg_eq]
    have hden' := occupationWeight_strictAnti (show j.val < m+k from j.isLt.trans_le (Nat.le_add_right _ _))
    apply (le_div_iff₀ (sub_pos.mpr hden')).mpr
    have h1 : occupationWeight j.val-occupationWeight (m+k) ≤ 1 :=
      (sub_le_self _ (occupationWeight_pos _).le).trans (occupation_in_unit _).2
    have hlow := (occupationWeight_antitone (show j.val+1 ≤ m from j.isLt)).trans (b j).property.1
    exact (mul_le_of_le_one_right (sub_nonneg.mpr hg.le) h1).trans (sub_le_sub hlow he)
  simpa only [prod_const,card_univ,Fintype.card_fin] using
    (Finset.prod_le_prod (s := univ) (fun _ _ => sub_nonneg.mpr hg.le) (fun j _ => hfactor j))

#print axioms remote_residue_lower

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
