import GaloisForLFunctions.BiScaleUncertainty.UniversalRamanujanCovarianceAndBiScaleRigidity
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Positive coercivity on clipped integer windows

Binary-parent paths give a `2*N` estimate, including incomplete final generations.
Each parent edge is controlled by the native additive and doubling edges. Hence every
multiplicative horizon containing 2 has anchored coercivity constant at most `6*N`.
All sums use edges inside the requested integer window; N=0 and N=1 are included.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
set_option autoImplicit false

/-- Binary parents between the node and the root; the root itself is omitted. -/
def binaryAncestors (n : ℕ) : Finset ℕ :=
  if hn : 2 ≤ n then insert n (binaryAncestors (n / 2)) else ∅
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

private theorem ancestors_step (n : ℕ) (hn : 2 ≤ n) :
    binaryAncestors n = insert n (binaryAncestors (n / 2)) := by
  rw [binaryAncestors]
  simp [hn]

private theorem ancestors_small (n : ℕ) (hn : n ≤ 1) : binaryAncestors n = ∅ := by
  rw [binaryAncestors]
  simp [show ¬2 ≤ n by omega]

private theorem ancestor_bounds (n : ℕ) : ∀ k ∈ binaryAncestors n, 2 ≤ k ∧ k ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hk
    by_cases hn : 2 ≤ n
    · rw [ancestors_step n hn] at hk
      rcases mem_insert.mp hk with rfl | hk
      · exact ⟨hn, le_rfl⟩
      · have hp : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
        have h := ih (n / 2) hp k hk
        exact ⟨h.1, by omega⟩
    · rw [ancestors_small n (by omega)] at hk
      simp at hk

private theorem self_not_parent_ancestors (n : ℕ) (hn : 2 ≤ n) :
    n ∉ binaryAncestors (n / 2) := by
  intro h
  have hb := (ancestor_bounds (n / 2) n h).2
  have hp : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
  omega

/-- The reciprocal path budget is strictly below one. -/
theorem binary_ancestor_reciprocal_sum (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ binaryAncestors n, 1 / (k : ℝ)) ≤ 1 - 1 / (n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : 2 ≤ n
    · have hp : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have hp1 : 1 ≤ n / 2 := by omega
      have hparent := ih (n / 2) hp hp1
      rw [ancestors_step n hn2, sum_insert (self_not_parent_ancestors n hn2)]
      have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hpR : (0 : ℝ) < (n / 2 : ℕ) := by exact_mod_cast (show 0 < n / 2 by omega)
      have htwo : 2 / (n : ℝ) ≤ 1 / (n / 2 : ℕ) := by
        apply (div_le_div_iff₀ hnR hpR).mpr
        have h := Nat.div_mul_le_self n 2
        have hr : (n / 2 : ℕ) * (2 : ℝ) ≤ n := by exact_mod_cast h
        nlinarith
      rw [show 2 / (n : ℝ) = 2 * (1 / (n : ℝ)) by ring] at htwo
      linarith
    · have hn1 : n = 1 := by omega
      subst n
      simp [ancestors_small]

private theorem sum_binary_increments (f : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ binaryAncestors n, (f k - f (k / 2))) = f n - f 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : 2 ≤ n
    · have hp : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      rw [ancestors_step n hn2, sum_insert (self_not_parent_ancestors n hn2), ih (n / 2) hp (by omega)]
      ring
    · have hn1 : n = 1 := by omega
      subst n
      simp [ancestors_small]

/-- Weighted Cauchy spends one unit of reciprocal budget along each parent path. -/
theorem binary_parent_point_bound (f : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (f n - f 1) ^ 2 ≤ ∑ k ∈ binaryAncestors n, (k : ℝ) * (f k - f (k / 2)) ^ 2 := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (binaryAncestors n)
    (r := fun k => f k - f (k / 2)) (f := fun k => 1 / (k : ℝ))
    (g := fun k => (k : ℝ) * (f k - f (k / 2)) ^ 2)
    (fun k _ => by positivity) (fun k _ => by positivity) (by
      intro k hk
      have hkR : (0 : ℝ) < k := by
        exact_mod_cast (show 0 < k by have := (ancestor_bounds n k hk).1; omega)
      field_simp
      exact le_rfl
    )
  rw [sum_binary_increments f n hn] at hcs
  have hrec := binary_ancestor_reciprocal_sum n hn
  have hrec1 : (∑ k ∈ binaryAncestors n, 1 / (k : ℝ)) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have hg : 0 ≤ ∑ k ∈ binaryAncestors n, (k : ℝ) * (f k - f (k / 2)) ^ 2 := by positivity
  exact hcs.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hrec1 hg)

private theorem ancestor_quotient (n : ℕ) :
    ∀ k ∈ binaryAncestors n, ∃ r : ℕ, n / 2 ^ r = k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hk
    by_cases hn : 2 ≤ n
    · rw [ancestors_step n hn] at hk
      rcases mem_insert.mp hk with rfl | hk
      · exact ⟨0, by simp⟩
      · have hp : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
        obtain ⟨r, hr⟩ := ih (n / 2) hp k hk
        refine ⟨r + 1, ?_⟩
        simpa only [pow_succ', Nat.div_div_eq_div_mul] using hr
    · rw [ancestors_small n (by omega)] at hk
      simp at hk

/-- A binary ancestor's integer-window descendants spend at most twice the window budget. -/
theorem binary_descendant_card_bound (N k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N) :
    k * ((Icc 1 N).filter (fun n => k ∈ binaryAncestors n)).card ≤ 2 * N := by
  let L := Nat.log 2 (N / k) + 1
  let F := fun r : ℕ => (Icc 1 N).filter (fun n => n / 2 ^ r = k)
  have hk0 : 0 < k := by omega
  have hquot : N / k ≠ 0 := (Nat.div_pos hkN hk0).ne'
  have hcover : (Icc 1 N).filter (fun n => k ∈ binaryAncestors n) ⊆
      (range L).biUnion F := by
    intro n hn
    obtain ⟨hnN, hanc⟩ := mem_filter.mp hn
    obtain ⟨r, hr⟩ := ancestor_quotient n k hanc
    have hprod := Nat.div_mul_le_self n (2 ^ r)
    rw [hr] at hprod
    have hpow : 2 ^ r ≤ N / k := (Nat.le_div_iff_mul_le hk0).mpr (by
      have hnle := (mem_Icc.mp hnN).2
      nlinarith)
    have hlog := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
    refine mem_biUnion.mpr ⟨r, mem_range.mpr ?_, mem_filter.mpr ⟨hnN, hr⟩⟩
    dsimp [L]
    omega
  have hfiber (r : ℕ) : (F r).card ≤ 2 ^ r := by
    have hsub : F r ⊆ Ico (k * 2 ^ r) ((k + 1) * 2 ^ r) := by
      intro n hn
      obtain ⟨_, heq⟩ := mem_filter.mp hn
      have hprod := Nat.div_mul_le_self n (2 ^ r)
      rw [heq] at hprod
      have hp0 : 0 < 2 ^ r := by positivity
      have hupper : n < (k + 1) * 2 ^ r :=
        (Nat.div_lt_iff_lt_mul hp0).mp (by omega)
      exact mem_Ico.mpr ⟨hprod, hupper⟩
    simpa only [Nat.card_Ico, add_mul, one_mul, Nat.add_sub_cancel_left] using card_le_card hsub
  have hcard : ((Icc 1 N).filter (fun n => k ∈ binaryAncestors n)).card ≤
      ∑ r ∈ range L, 2 ^ r := by
    exact ((card_le_card hcover).trans card_biUnion_le).trans (sum_le_sum (fun r _ => hfiber r))
  have hsum : (∑ r ∈ range L, 2 ^ r) ≤ 2 * (N / k) := by
    calc
      (∑ r ∈ range L, 2 ^ r) = 2 ^ L - 1 := by
        simpa using Nat.geomSum_eq (by norm_num : 2 ≤ 2) L
      _ ≤ 2 ^ L := Nat.sub_le _ _
      _ = 2 * 2 ^ Nat.log 2 (N / k) := by dsimp [L]; rw [pow_succ']
      _ ≤ 2 * (N / k) := Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hquot)
  calc
    k * ((Icc 1 N).filter (fun n => k ∈ binaryAncestors n)).card ≤ k * (2 * (N / k)) :=
      Nat.mul_le_mul_left k (hcard.trans hsum)
    _ ≤ 2 * N := by nlinarith [Nat.div_mul_le_self N k]

/-- The actual finite binary-parent graph has a linear anchor bound. -/
theorem binary_parent_window_bound (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, (f n - f 1) ^ 2) ≤
      2 * (N : ℝ) * (∑ k ∈ Icc 2 N, (f k - f (k / 2)) ^ 2) := by
  let F := fun k : ℕ => (k : ℝ) * (f k - f (k / 2)) ^ 2
  have heach (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ k ∈ binaryAncestors n, F k) =
        ∑ k ∈ Icc 2 N, if k ∈ binaryAncestors n then F k else 0 := by
    rw [← sum_filter]
    congr 1
    ext k
    simp only [mem_filter, mem_Icc]
    constructor
    · intro hk
      have hb := ancestor_bounds n k hk
      exact ⟨⟨hb.1, hb.2.trans (mem_Icc.mp hn).2⟩, hk⟩
    · exact fun hk => hk.2
  have hinner (k : ℕ) (hk : k ∈ Icc 2 N) :
      (∑ n ∈ Icc 1 N, if k ∈ binaryAncestors n then F k else 0) ≤
        2 * (N : ℝ) * (f k - f (k / 2)) ^ 2 := by
    have hb : (k : ℝ) * (((Icc 1 N).filter (fun n => k ∈ binaryAncestors n)).card : ℝ) ≤
        2 * (N : ℝ) := by
      exact_mod_cast binary_descendant_card_bound N k (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
    calc
      (∑ n ∈ Icc 1 N, if k ∈ binaryAncestors n then F k else 0) =
          (k : ℝ) * (((Icc 1 N).filter (fun n => k ∈ binaryAncestors n)).card : ℝ) *
            (f k - f (k / 2)) ^ 2 := by
        rw [← sum_filter]
        simp only [sum_const, nsmul_eq_mul, F]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  calc
    (∑ n ∈ Icc 1 N, (f n - f 1) ^ 2) ≤
        ∑ n ∈ Icc 1 N, ∑ k ∈ binaryAncestors n, F k :=
      sum_le_sum (fun n hn => binary_parent_point_bound f n (mem_Icc.mp hn).1)
    _ = ∑ n ∈ Icc 1 N, ∑ k ∈ Icc 2 N, if k ∈ binaryAncestors n then F k else 0 :=
      sum_congr rfl (fun n hn => heach n hn)
    _ = ∑ k ∈ Icc 2 N, ∑ n ∈ Icc 1 N, if k ∈ binaryAncestors n then F k else 0 := sum_comm
    _ ≤ ∑ k ∈ Icc 2 N, 2 * (N : ℝ) * (f k - f (k / 2)) ^ 2 := sum_le_sum hinner
    _ = _ := by rw [mul_sum]

private theorem binary_energy_le_joint (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 2 N, (f n - f (n / 2)) ^ 2) ≤ 3 * biScaleJointEnergy 2 N f := by
  let b := fun n : ℕ => (f n - f (n / 2)) ^ 2
  let h := fun n : ℕ => (f (n + 1) - f n) ^ 2
  have hfib := sum_fiberwise_eq_sum_filter (Icc 2 N) (Icc 1 (N / 2)) (fun n => n / 2) b
  have hfilter : (Icc 2 N).filter (fun n => n / 2 ∈ Icc 1 (N / 2)) = Icc 2 N := by
    ext n
    simp only [mem_filter, mem_Icc]
    omega
  rw [hfilter] at hfib
  have hpair (m : ℕ) (hm : m ∈ Icc 1 (N / 2)) :
      (∑ n ∈ (Icc 2 N).filter (fun n => n / 2 = m), b n) ≤
        3 * (f (2 * m) - f m) ^ 2 + 2 * (if 2 * m + 1 ≤ N then h (2 * m) else 0) := by
    obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
    have hdiv : (2 * m) / 2 = m := by omega
    have hdiv' : (2 * m + 1) / 2 = m := by omega
    by_cases hodd : 2 * m + 1 ≤ N
    · have hf : (Icc 2 N).filter (fun n => n / 2 = m) = {2 * m, 2 * m + 1} := by
        ext n
        simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
        omega
      rw [hf, sum_insert (by simp), sum_singleton, if_pos hodd]
      dsimp [b, h]
      rw [hdiv, hdiv']
      nlinarith [sq_nonneg ((f (2 * m) - f m) - (f (2 * m + 1) - f (2 * m)))]
    · have hf : (Icc 2 N).filter (fun n => n / 2 = m) = {2 * m} := by
        ext n
        simp only [mem_filter, mem_Icc, mem_singleton]
        omega
      rw [hf, sum_singleton, if_neg hodd]
      dsimp [b]
      rw [hdiv]
      nlinarith [sq_nonneg (f (2 * m) - f m)]
  have hodd : (∑ m ∈ Icc 1 (N / 2), if 2 * m + 1 ≤ N then h (2 * m) else 0) ≤
      additiveStepEnergy N f := by
    rw [← sum_filter]
    let S := (Icc 1 (N / 2)).filter (fun m => 2 * m + 1 ≤ N)
    change (∑ m ∈ S, h (2 * m)) ≤ additiveStepEnergy N f
    have hsub : S.image (fun m => 2 * m) ⊆ Ico 1 N := by
      intro n hn
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
      obtain ⟨hmI, hmN⟩ := mem_filter.mp hm
      have hm1 := (mem_Icc.mp hmI).1
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    calc
      (∑ m ∈ S, h (2 * m)) = ∑ n ∈ S.image (fun m => 2 * m), h n := by
        rw [sum_image (by intro a _ b _ hab; change 2 * a = 2 * b at hab; omega)]
      _ ≤ ∑ n ∈ Ico 1 N, h n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg _)
      _ = additiveStepEnergy N f := rfl
  have hsum : (∑ n ∈ Icc 2 N, b n) ≤
      3 * (∑ m ∈ Icc 1 (N / 2), (f (2 * m) - f m) ^ 2) +
        2 * (∑ m ∈ Icc 1 (N / 2), if 2 * m + 1 ≤ N then h (2 * m) else 0) := by
    rw [← hfib, mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum hpair
  have hdil : multiplicativeScaleEnergy 2 N f =
      ∑ m ∈ Icc 1 (N / 2), (f (2 * m) - f m) ^ 2 := by simp [multiplicativeScaleEnergy]
  rw [← hdil] at hsum
  change (∑ n ∈ Icc 2 N, b n) ≤ 3 * biScaleJointEnergy 2 N f
  rw [biScaleJointEnergy]
  nlinarith [additiveStepEnergy_nonneg N f]

/-- The exact positive bound uses only native edges inside the requested window. -/
theorem doubling_window_coercivity (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, (f n - f 1) ^ 2) ≤ 6 * (N : ℝ) * biScaleJointEnergy 2 N f := by
  calc
    (∑ n ∈ Icc 1 N, (f n - f 1) ^ 2) ≤
        2 * (N : ℝ) * (∑ k ∈ Icc 2 N, (f k - f (k / 2)) ^ 2) := binary_parent_window_bound N f
    _ ≤ 2 * (N : ℝ) * (3 * biScaleJointEnergy 2 N f) :=
      mul_le_mul_of_nonneg_left (binary_energy_le_joint N f) (by positivity)
    _ = _ := by ring

/-- Every horizon containing doubling inherits the same finite-window estimate. -/
theorem window_coercivity (K N : ℕ) (hK : 2 ≤ K) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, (f n - f 1) ^ 2) ≤ 6 * (N : ℝ) * biScaleJointEnergy K N f := by
  have hdil : multiplicativeScaleEnergy 2 N f ≤ multiplicativeScaleEnergy K N f := by
    unfold multiplicativeScaleEnergy
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨hk2, hkK⟩ := mem_Icc.mp hk
      exact mem_Icc.mpr ⟨hk2, hkK.trans hK⟩
    · intro k _ _
      exact sum_nonneg (fun n _ => sq_nonneg _)
  have he : biScaleJointEnergy 2 N f ≤ biScaleJointEnergy K N f := by
    unfold biScaleJointEnergy
    linarith
  exact (doubling_window_coercivity N f).trans
    (mul_le_mul_of_nonneg_left he (by positivity))

end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
