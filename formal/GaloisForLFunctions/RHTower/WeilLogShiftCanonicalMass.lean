import GaloisForLFunctions.RHTower.WeilLogShiftMassRigidity
import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalQuadrature
import Mathlib.Algebra.BigOperators.Fin

/-! The canonical absolute mass equals two exactly at orders zero and one. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilCanonicalCluster_mass_eq_two_of_le_one (r k : ℕ) (hr : r ≤ 1) :
    finiteWeilAbsMass (finiteWeilCanonicalCluster r k) = 2 := by
  have hm := finiteWeil_zero_sum_unit_mass _ (finiteWeilCanonicalCluster_spec r k).1
    (finiteWeilCanonicalCluster_sum_zero r k)
  have hr' : r = 0 ∨ r = 1 := by omega
  rcases hr' with rfl | rfl
  · have hz := finiteWeilCanonicalCluster_sum_zero 0 k
    have h1 : 0 < finiteWeilCanonicalCluster 0 k 1 :=
      (finiteWeilCanonicalCluster_alternation 0 k).1
    have h01 : finiteWeilCanonicalCluster 0 k 0 * finiteWeilCanonicalCluster 0 k 1 < 0 :=
      (finiteWeilCanonicalCluster_alternation 0 k).2 0
    have h0 : finiteWeilCanonicalCluster 0 k 0 < 0 := by
      rcases mul_neg_iff.mp h01 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> linarith
    have hn : |finiteWeilCanonicalCluster 0 k 1| ≤ 1 := by
      simpa only [Real.norm_eq_abs, (finiteWeilCanonicalCluster_spec 0 k).1] using
        norm_le_pi_norm (finiteWeilCanonicalCluster 0 k) 1
    have he : finiteWeilAbsMass (finiteWeilCanonicalCluster 0 k) =
        -finiteWeilCanonicalCluster 0 k 0 + finiteWeilCanonicalCluster 0 k 1 := by
      unfold finiteWeilAbsMass
      rw [Fin.sum_univ_two, abs_of_neg h0, abs_of_pos h1]
    rw [Fin.sum_univ_two] at hz
    rw [abs_of_pos h1] at hn
    linarith only [hm, hz, hn, he]
  · have hz := finiteWeilCanonicalCluster_sum_zero 1 k
    have h2 : 0 < finiteWeilCanonicalCluster 1 k 2 :=
      (finiteWeilCanonicalCluster_alternation 1 k).1
    have h12 : finiteWeilCanonicalCluster 1 k 1 * finiteWeilCanonicalCluster 1 k 2 < 0 :=
      (finiteWeilCanonicalCluster_alternation 1 k).2 1
    have h01 : finiteWeilCanonicalCluster 1 k 0 * finiteWeilCanonicalCluster 1 k 1 < 0 :=
      (finiteWeilCanonicalCluster_alternation 1 k).2 0
    have h1 : finiteWeilCanonicalCluster 1 k 1 < 0 := by
      rcases mul_neg_iff.mp h12 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> linarith
    have h0 : 0 < finiteWeilCanonicalCluster 1 k 0 := by
      rcases mul_neg_iff.mp h01 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> linarith
    have hn : |finiteWeilCanonicalCluster 1 k 1| ≤ 1 := by
      simpa only [Real.norm_eq_abs, (finiteWeilCanonicalCluster_spec 1 k).1] using
        norm_le_pi_norm (finiteWeilCanonicalCluster 1 k) 1
    have he : finiteWeilAbsMass (finiteWeilCanonicalCluster 1 k) =
        finiteWeilCanonicalCluster 1 k 0 - finiteWeilCanonicalCluster 1 k 1 +
          finiteWeilCanonicalCluster 1 k 2 := by
      unfold finiteWeilAbsMass
      rw [Fin.sum_univ_three, abs_of_pos h0, abs_of_neg h1, abs_of_pos h2]
      ring
    rw [Fin.sum_univ_three] at hz
    rw [abs_of_neg h1] at hn
    linarith only [hm, hz, hn, he]

theorem finiteWeilCanonicalCluster_two_lt_mass (r k : ℕ) (hr : 2 ≤ r) :
    2 < finiteWeilAbsMass (finiteWeilCanonicalCluster r k) := by
  have hm := finiteWeil_zero_sum_unit_mass _ (finiteWeilCanonicalCluster_spec r k).1
    (finiteWeilCanonicalCluster_sum_zero r k)
  by_contra h
  have heq : finiteWeilAbsMass (finiteWeilCanonicalCluster r k) = 2 :=
    le_antisymm (le_of_not_gt h) hm
  obtain ⟨i, hi, hopp⟩ := finiteWeil_mass_two_sign_rigidity _
    (finiteWeilCanonicalCluster_spec r k).1 (finiteWeilCanonicalCluster_sum_zero r k) heq
  have hpair (a : Fin (r + 1)) (ha : a.castSucc ≠ i) (hb : a.succ ≠ i) : False := by
    have ha' := hopp a.castSucc ha
    have hb' := hopp a.succ hb
    have hn : 0 ≤ finiteWeilCanonicalCluster r k a.castSucc *
        finiteWeilCanonicalCluster r k a.succ := by
      rcases abs_eq_abs.mp (show |finiteWeilCanonicalCluster r k i| = |(1 : ℝ)| by
        simpa using hi) with hi | hi
      · rw [hi, one_mul] at ha' hb'
        exact mul_nonneg_of_nonpos_of_nonpos ha' hb'
      · rw [hi, neg_one_mul] at ha' hb'
        exact mul_nonneg (by linarith only [ha']) (by linarith only [hb'])
    have hneg := (finiteWeilCanonicalCluster_alternation r k).2 a
    linarith only [hn, hneg]
  have hmod : 1 % (r + 1 + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  by_cases hi2 : (i : ℕ) < 2
  · apply hpair ⟨2, by omega⟩
    · intro he
      have := congrArg Fin.val he
      dsimp at this
      omega
    · intro he
      have := congrArg Fin.val he
      dsimp at this
      omega
  · apply hpair ⟨0, by omega⟩
    · intro he
      have := congrArg Fin.val he
      dsimp at this
      omega
    · intro he
      have := congrArg Fin.val he
      dsimp at this
      omega

/-- The low-order boundary is exact and independent of cluster position. -/
theorem finiteWeilCanonicalCluster_mass_eq_two_iff (r k : ℕ) :
    finiteWeilAbsMass (finiteWeilCanonicalCluster r k) = 2 ↔ r ≤ 1 := by
  constructor
  · intro h
    by_contra hr
    have hs := finiteWeilCanonicalCluster_two_lt_mass r k (by omega)
    linarith only [h, hs]
  · exact finiteWeilCanonicalCluster_mass_eq_two_of_le_one r k

end RHTower
