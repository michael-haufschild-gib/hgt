import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.BalancedDigits
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.OccupationDominance

/-!
# The heat boundary of balanced occupation cutoffs

The positive cutoffs where coarse and replicated fine counts agree form
a subsequence of the original Hamiltonian spectrum. Its counting exponent
and absolute heat boundary both equal the binary isometry exponent.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

/-- Cutoffs whose coarse count exactly equals the replicated fine count. -/
abbrev BalancedCutoff (t : ExceptionalTime) (j : ℕ) :=
  {X : ℕ // Nat.card (countingStates t j X) = ((tailRadix t j).val+1)*Nat.card (countingStates t (j+1) X)}

private abbrev base (t : ExceptionalTime) (j : ℕ) : {c : ℕ // 1 < c} := ⟨(tailRadix t j).val,radix_gt_one t j⟩

/-- Read base-C digits in base C² to enumerate the physically balanced cutoffs. -/
def balancedCutoffEquiv (t : ExceptionalTime) (j : ℕ) : ℕ ≃ BalancedCutoff t j :=
  (stretchEquiv (base t j)).trans (Equiv.subtypeEquivRight fun n => (adjacent_count_equality t j n).symm)

/-- Exactly Cᵏ cutoffs below C^(2k) are balanced, counting zero. -/
theorem balanced_cutoff_count (t : ExceptionalTime) (j k : ℕ) :
    Nat.card {x : BalancedCutoff t j // x.val < ((tailRadix t j).val^2)^k} = (tailRadix t j).val^k := by
  let C := base t j
  let e := (balancedCutoffEquiv t j).subtypeEquiv (p := fun n => n < C.val^k)
    (q := fun x => x.val < (C.val^2)^k) (fun n => (stretch_lt_power C n k).symm)
  let f : Fin (C.val^k) ≃ {n : ℕ // n < C.val^k} :=
    ⟨fun n => ⟨n.val,n.isLt⟩,fun n => ⟨n.val,n.property⟩,fun _ => rfl,fun _ => rfl⟩
  exact (Nat.card_congr (f.trans e)).symm.trans (Nat.card_fin _)

private theorem stretch_pos (C : {c : ℕ // 1 < c}) (n : ℕ) : 0 < n ↔ 0 < stretchDigits C.val n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [stretchDigits]
  · have hu := (stretch_quadratic_bounds C n).1
    have hp := Nat.mul_pos hn (show 0 < n+2 by omega)
    exact iff_of_true hn (by by_contra! h; rw [Nat.eq_zero_of_le_zero h,mul_zero] at hu; omega)

/-- Balanced cutoffs that carry an energy log X. -/
abbrev PositiveBalancedCutoff (t : ExceptionalTime) (j : ℕ) := {x : BalancedCutoff t j // 0 < x.val}

private def positiveEquiv (t : ExceptionalTime) (j : ℕ) : ℕ+ ≃ PositiveBalancedCutoff t j := by
  change {n : ℕ // 0 < n} ≃ {x : BalancedCutoff t j // 0 < x.val}
  exact (balancedCutoffEquiv t j).subtypeEquiv (p := fun n : ℕ => 0 < n)
    (q := fun x : BalancedCutoff t j => 0 < x.val) (stretch_pos (base t j))

def balancedHeat (t : ExceptionalTime) (j : ℕ) (s : ℂ) (x : PositiveBalancedCutoff t j) : ℂ :=
  heat s ⟨x.val.val,x.property⟩

private theorem heat_antitone {s : ℂ} (hs : 0 ≤ s.re) {a b : ℕ+} (hab : a.val ≤ b.val) :
    ‖heat s b‖ ≤ ‖heat s a‖ := by
  simp only [norm_heat,Real.exp_le_exp]
  exact mul_le_mul_of_nonpos_left (Real.log_le_log (by exact_mod_cast a.pos) (by exact_mod_cast hab)) (neg_nonpos.mpr hs)

/-- The unregularized positive heat on the balance set has abscissa exactly one half. -/
theorem balanced_heat_summable_iff (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    (Summable fun x => ‖balancedHeat t j s x‖) ↔ 1/2 < s.re := by
  let C := base t j
  let K : ℕ+ := ⟨C.val+1,Nat.succ_pos _⟩
  let F (n : ℕ+) : ℕ+ := ⟨stretchDigits C.val n.val,(stretch_pos C n.val).mp n.pos⟩
  rw [← (positiveEquiv t j).summable_iff]
  change (Summable fun n : ℕ+ => ‖heat s (F n)‖) ↔ _
  constructor
  · intro h
    by_contra! hs
    let u : ℂ := 1/2
    have hu : u.re = 1/2 := by norm_num [u]
    have hn (n : ℕ+) : ‖heat u n‖^2 ≤ ‖heat s (F n)‖ := by
      have hsq : (F n).val ≤ (n*n).val := by
        change stretchDigits C.val n.val ≤ n.val*n.val
        exact (stretch_quadratic_bounds C n.val).2.trans_eq (pow_two n.val)
      have h₁ := heat_antitone (s := u) (by rw [hu]; norm_num) (a := F n) (b := n*n) hsq
      rw [heat_mul,norm_mul,← pow_two] at h₁
      apply h₁.trans
      simp only [norm_heat,Real.exp_le_exp,hu]
      have hF : 1 ≤ (F n).val := (F n).pos
      exact mul_le_mul_of_nonneg_right (neg_le_neg hs) (Real.log_nonneg (by exact_mod_cast hF))
    have habs := (summable_heat_sq_iff u).mp (h.of_nonneg_of_le (fun _ => sq_nonneg _) hn)
    rw [hu] at habs
    exact (lt_irrefl _) habs
  · intro hs
    have h := ((summable_heat_sq_iff s).mpr hs).div_const ‖heat s K‖
    have hK : 0 < ‖heat s K‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
    apply h.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro n
    apply (le_div_iff₀ hK).mpr
    have hlow := (stretch_quadratic_bounds C n.val).1
    have hnn : n.val*n.val ≤ K.val*(F n).val :=
      (Nat.mul_le_mul_left n.val (by omega : n.val ≤ n.val+2)).trans hlow
    have hh := heat_antitone (s := s) (by linarith only [hs]) (a := n*n) (b := K*F n) hnn
    simpa only [heat_mul,norm_mul,pow_two,mul_comm] using hh

/-- Using the two-copy energy 2 log X moves the same absolute heat boundary to one quarter. -/
theorem balanced_pair_heat_summable_iff (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    (Summable fun x => ‖balancedHeat t j s x * balancedHeat t j s x‖) ↔ 1/4 < s.re := by
  have h := balanced_heat_summable_iff t j (s+s)
  simp only [balancedHeat,heat_add,Complex.add_re] at h
  unfold balancedHeat
  rw [h]
  constructor <;> intro hs <;> linarith only [hs]

/-- The transition from divergent to summable balanced heat is exactly isometric composition. -/
theorem balanced_heat_boundary_iff_split (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    (∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split s f x) ↔
      ¬(Summable fun x => ‖balancedHeat t j s x‖) ∧
        ∀ ε : {r : ℝ // 0 < r}, Summable fun x => ‖balancedHeat t j (s+(ε.val:ℂ)) x‖ := by
  simp only [split_isometric_iff,balanced_heat_summable_iff,not_lt,Complex.add_re,Complex.ofReal_re]
  constructor
  · intro he
    exact ⟨he.le,fun ε => by rw [he]; exact lt_add_of_pos_right _ ε.property⟩
  · rintro ⟨hs,hshift⟩
    apply le_antisymm hs
    by_contra! hl
    have h := hshift ⟨(1/2-s.re)/2,by linarith only [hl]⟩
    change 1/2 < s.re+(1/2-s.re)/2 at h
    linarith only [hl,h]

#print axioms balanced_cutoff_count
#print axioms balanced_heat_summable_iff
#print axioms balanced_pair_heat_summable_iff
#print axioms balanced_heat_boundary_iff_split

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
