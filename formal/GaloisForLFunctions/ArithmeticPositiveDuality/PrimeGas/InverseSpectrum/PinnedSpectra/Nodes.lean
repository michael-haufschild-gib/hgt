import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.Closure

/-! # Secular residues with a movable last native level -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set Finset

/-- The full closed box of prescriptions for the first m surviving levels. -/
abbrev PrefixData (m : ℕ) := (j : Fin m) → Icc (occupationWeight (j.val+1)) (occupationWeight j.val)

def StrictPrefix {m : ℕ} (b : PrefixData m) : Prop :=
  ∀ j, occupationWeight (j.val+1) < (b j).val ∧ (b j).val < occupationWeight j.val

/-- Every closed prescription is a limit of strict prescriptions, with all coordinates approaching together. -/
theorem strict_prefix_limit {m : ℕ} (b : PrefixData m) :
    ∃ c : ℕ → PrefixData m, (∀ n, StrictPrefix (c n)) ∧ Tendsto c atTop (𝓝 b) := by
  let mid (j : Fin m) := (occupationWeight (j.val+1)+occupationWeight j.val)/2
  let x (n : ℕ) (j : Fin m) := (1-occupationWeight n)*(b j).val+occupationWeight n*mid j
  have hs (n : ℕ) (j : Fin m) : occupationWeight (j.val+1) < x n j ∧ x n j < occupationWeight j.val := by
    have hg := occupationWeight_strictAnti (Nat.lt_succ_self j.val)
    have hmid : occupationWeight (j.val+1) < mid j ∧ mid j < occupationWeight j.val := by
      dsimp only [mid]
      constructor <;> linarith only [hg]
    have hn := occupationWeight_pos n
    have h1 := sub_nonneg.mpr (occupation_in_unit n).2
    have he (y : ℝ) : (1-occupationWeight n)*y+occupationWeight n*y=y := by ring
    exact ⟨(he _).symm.trans_lt (add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (b j).property.1 h1)
      (mul_lt_mul_of_pos_left hmid.1 hn)),(add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (b j).property.2 h1)
      (mul_lt_mul_of_pos_left hmid.2 hn)).trans_eq (he _)⟩
  refine ⟨fun n j => ⟨x n j,(hs n j).1.le,(hs n j).2.le⟩,hs,tendsto_pi_nhds.mpr (fun j => tendsto_subtype_rng.mpr ?_)⟩
  simpa only [sub_zero,one_mul,zero_mul,add_zero] using
    ((occupationWeight_tendsto.const_sub 1).mul_const (b j).val).add (occupationWeight_tendsto.mul_const (mid j))

/-- Use the first m native levels and one remote level at m+k. -/
def nodeIndex (m k : ℕ) (i : Fin (m+1)) : ℕ := if i.val < m then i.val else m+k

theorem nodeIndex_head {m : ℕ} (k : ℕ) (i : Fin m) : nodeIndex m k i.castSucc = i.val := if_pos i.isLt
theorem nodeIndex_last (m k : ℕ) : nodeIndex m k (Fin.last m) = m+k := if_neg (Nat.lt_irrefl m)

def nativeNode (m k : ℕ) (i : Fin (m+1)) := occupationWeight (nodeIndex m k i)

theorem nativeNode_anti (m k : ℕ) : StrictAnti (nativeNode m k) := by
  intro i j hij
  apply occupationWeight_strictAnti
  have h : i.val < j.val := hij
  have hj := j.isLt
  unfold nodeIndex
  split_ifs <;> omega

def nodeResidue {m : ℕ} (b : PrefixData m) (k : ℕ) := residueMass (nativeNode m k) (fun j => (b j).val)

theorem nodeResidue_continuous {m : ℕ} (k : ℕ) (i : Fin (m+1)) :
    Continuous (fun b : PrefixData m => nodeResidue b k i) := by
  unfold nodeResidue residueMass
  apply Continuous.div_const
  exact continuous_finsetProd _ (fun j _ => continuous_const.sub (continuous_subtype_val.comp (continuous_apply j)))

private theorem strict_node_gaps {m : ℕ} {b : PrefixData m} (hb : StrictPrefix b) (k : ℕ) (j : Fin m) :
    nativeNode m k j.succ < (b j).val ∧ (b j).val < nativeNode m k j.castSucc := by
  have hi : j.val+1 ≤ nodeIndex m k j.succ := by
    unfold nodeIndex
    have hj := j.isLt
    change j.val+1 ≤ if j.val+1 < m then j.val+1 else m+k
    split_ifs <;> omega
  exact ⟨(occupationWeight_antitone hi).trans_lt (hb j).1,(hb j).2.trans_eq (congrArg occupationWeight (nodeIndex_head k j)).symm⟩

theorem nodeResidue_sum {m : ℕ} (b : PrefixData m) (k : ℕ) : ∑ i, nodeResidue b k i = 1 :=
  sum_residueMass (nativeNode_anti m k).injective _

theorem nodeResidue_nonneg {m : ℕ} (b : PrefixData m) (k : ℕ) (i : Fin (m+1)) : 0 ≤ nodeResidue b k i := by
  obtain ⟨c,hs,ht⟩ := strict_prefix_limit b
  exact ge_of_tendsto' (((nodeResidue_continuous k i).tendsto b).comp ht)
    (fun n => (residueMass_pos (nativeNode_anti m k) (strict_node_gaps (hs n) k) i).le)

theorem nodeResidue_le_one {m : ℕ} (b : PrefixData m) (k : ℕ) (i : Fin (m+1)) : nodeResidue b k i ≤ 1 :=
  (Finset.single_le_sum (fun j _ => nodeResidue_nonneg b k j) (mem_univ i)).trans_eq (nodeResidue_sum b k)

theorem nodeResidue_secular {m : ℕ} {b : PrefixData m} (hb : StrictPrefix b) (k : ℕ) (j : Fin m) :
    ∑ i, nodeResidue b k i / (nativeNode m k i-(b j).val) = 0 :=
  residueMass_secular (nativeNode_anti m k) (strict_node_gaps hb k) j

#print axioms strict_prefix_limit
#print axioms nodeResidue_nonneg
#print axioms nodeResidue_secular

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
