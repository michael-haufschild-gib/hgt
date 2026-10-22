import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarRelativeDisplacement
import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# First contact for the actual nonlinear prime moment

For the full von Mangoldt mass `M_n = primeMassHalf n`, put
`U_n = sqrt(n) * (M_n + 2) - n - psi(n) - 1` and
`D_n = M_n + M_n^2 / 4 - psi(n)`. Their difference is an exact square.

A discrete valley of `U` can occur only at a prime-power entry, where that
square is smaller than one quarter of the squared entering weight.
For every real `A`, a strict descent below `A-1` forces a later `D < A`:
otherwise there is no next valley, every subsequent mass increment spends
at least half its weight from `D`, and divergent actual prime mass gives a
contradiction. Thus `D >= A` on a tail forces `U >= min(U_start,A-1)` there.

No RH assumption is used. Existence of arbitrarily deep descents and the
required eventual forcing sign are separate problems, not conclusions here.
-/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace RHTower


/-- The integer-head Abel potential, with the complete prime cumulative retained. -/
def ccmPrimeMomentPotential (n : ℕ) : ℝ :=
  Real.sqrt n * (primeMassHalf n + 2) - n - Chebyshev.psi n - 1

/-- The actual unnormalized nonlinear forcing in the prime age-moment balance. -/
def ccmPrimeMomentDiscrepancy (n : ℕ) : ℝ :=
  primeMassHalf n + primeMassHalf n ^ 2 / 4 - Chebyshev.psi n

/-- Exact separation of the Abel potential and the nonnegative displacement square. -/
theorem ccmPrimeMomentDiscrepancy_eq_potential_add_square (n : ℕ) :
    ccmPrimeMomentDiscrepancy n = ccmPrimeMomentPotential n +
      (1 + primeMassHalf n / 2 - Real.sqrt n) ^ 2 := by
  unfold ccmPrimeMomentDiscrepancy ccmPrimeMomentPotential
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)]

private theorem mass_succ (n : ℕ) :
    primeMassHalf ((n+1 : ℕ) : ℝ) = primeMassHalf n + criticalMellinAtomWeight (n+1) := by
  simp only [primeMassHalf, Nat.floor_natCast, criticalMellinAtomWeight_eq_div_sqrt]
  rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ n+1)]

private theorem psi_succ (n : ℕ) :
    Chebyshev.psi ((n+1 : ℕ) : ℝ) = Chebyshev.psi n + ArithmeticFunction.vonMangoldt (n+1) := by
  simp only [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ n+1)]

private theorem sqrt_weight_succ (n : ℕ) :
    Real.sqrt (n+1 : ℕ) * criticalMellinAtomWeight (n+1) =
      ArithmeticFunction.vonMangoldt (n+1) := by
  rw [criticalMellinAtomWeight_eq_div_sqrt]
  have hn : Real.sqrt (n+1 : ℕ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp

private theorem sqrt_gap_pos (n : ℕ) :
    0 < Real.sqrt (n+1 : ℕ) - Real.sqrt n := by
  apply sub_pos.mpr
  apply Real.sqrt_lt_sqrt (Nat.cast_nonneg (α := ℝ) n)
  push_cast
  linarith

/-- Prime jumps cancel from the potential increment; the pre-entry mass remains. -/
theorem ccmPrimeMomentPotential_succ_sub (n : ℕ) :
    ccmPrimeMomentPotential (n+1) - ccmPrimeMomentPotential n =
      (Real.sqrt (n+1 : ℕ) - Real.sqrt n) *
        (primeMassHalf n + 2 - Real.sqrt (n+1 : ℕ) - Real.sqrt n) := by
  unfold ccmPrimeMomentPotential
  rw [mass_succ, psi_succ]
  have hw := sqrt_weight_succ n
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hs' := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+1))
  push_cast at *
  nlinarith

/-- A discrete valley is exactly a crossing of the adjacent square-root midpoints. -/
theorem ccmPrimeMomentPotential_valley_iff (n : ℕ) :
    (ccmPrimeMomentPotential (n+1) ≤ ccmPrimeMomentPotential n ∧
      ccmPrimeMomentPotential (n+1) ≤ ccmPrimeMomentPotential (n+2)) ↔
    (primeMassHalf n + 2 ≤ Real.sqrt (n+1 : ℕ) + Real.sqrt n ∧
      Real.sqrt (n+2 : ℕ) + Real.sqrt (n+1 : ℕ) ≤ primeMassHalf (n+1 : ℕ) + 2) := by
  have h₁ := ccmPrimeMomentPotential_succ_sub n
  have h₂ := ccmPrimeMomentPotential_succ_sub (n+1)
  have hp₁ := sqrt_gap_pos n
  have hp₂ := sqrt_gap_pos (n+1)
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · have : (Real.sqrt (n+1 : ℕ)-Real.sqrt n) *
          (primeMassHalf n+2-Real.sqrt (n+1 : ℕ)-Real.sqrt n) ≤ 0 := by linarith
      nlinarith
    · have : 0 ≤ (Real.sqrt (n+2 : ℕ)-Real.sqrt (n+1 : ℕ)) *
          (primeMassHalf (n+1 : ℕ)+2-Real.sqrt (n+2 : ℕ)-Real.sqrt (n+1 : ℕ)) := by
        linarith
      have := (mul_nonneg_iff_of_pos_left hp₂).mp this
      linarith
  · rintro ⟨hl,hr⟩
    have hn₁ : (Real.sqrt (n+1 : ℕ)-Real.sqrt n) *
        (primeMassHalf n+2-Real.sqrt (n+1 : ℕ)-Real.sqrt n) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hp₁.le (by linarith)
    have hn₂ : 0 ≤ (Real.sqrt (n+2 : ℕ)-Real.sqrt (n+1 : ℕ)) *
        (primeMassHalf (n+1 : ℕ)+2-Real.sqrt (n+2 : ℕ)-Real.sqrt (n+1 : ℕ)) :=
      mul_nonneg hp₂.le (by linarith)
    constructor <;> linarith

/-- Every discrete valley occurs at a genuine prime-power admission. -/
theorem ccmPrimeMomentPotential_valley_primePower (n : ℕ)
    (hl : ccmPrimeMomentPotential (n+1) ≤ ccmPrimeMomentPotential n)
    (hr : ccmPrimeMomentPotential (n+1) ≤ ccmPrimeMomentPotential (n+2)) :
    IsPrimePow (n+1) := by
  obtain ⟨hl',hr'⟩ := (ccmPrimeMomentPotential_valley_iff n).mp ⟨hl,hr⟩
  by_contra hn
  have hz : criticalMellinAtomWeight (n+1) = 0 := by
    rw [criticalMellinAtomWeight_eq_div_sqrt,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]
  rw [mass_succ, hz, add_zero] at hr'
  have hp₁ := sqrt_gap_pos n
  have hp₂ := sqrt_gap_pos (n+1)
  linarith

/-- At a valley the positive square is strictly smaller than the entering atom square. -/
theorem ccmPrimeMomentDiscrepancy_lt_valley_add_atom_square (n : ℕ)
    (hl : ccmPrimeMomentPotential (n+1) ≤ ccmPrimeMomentPotential n)
    (hr : ccmPrimeMomentPotential (n+1) ≤ ccmPrimeMomentPotential (n+2)) :
    ccmPrimeMomentDiscrepancy (n+1) < ccmPrimeMomentPotential (n+1) +
      criticalMellinAtomWeight (n+1) ^ 2 / 4 := by
  obtain ⟨hl',hr'⟩ := (ccmPrimeMomentPotential_valley_iff n).mp ⟨hl,hr⟩
  have hp₁ := sqrt_gap_pos n
  have hp₂ := sqrt_gap_pos (n+1)
  have hm := mass_succ n
  have hy : 0 < 1 + primeMassHalf (n+1 : ℕ)/2 - Real.sqrt (n+1 : ℕ) := by linarith
  have hyw : 1 + primeMassHalf (n+1 : ℕ)/2 - Real.sqrt (n+1 : ℕ) <
      criticalMellinAtomWeight (n+1)/2 := by linarith
  rw [ccmPrimeMomentDiscrepancy_eq_potential_add_square]
  nlinarith

private theorem atom_nonneg (n : ℕ) : 0 ≤ criticalMellinAtomWeight n := by
  rw [criticalMellinAtomWeight_eq_div_sqrt]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

private theorem sqrt_gap_le_one (n : ℕ) :
    Real.sqrt (n+1 : ℕ) - Real.sqrt n ≤ 1 := by
  have h₀ := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have h₁ := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (n+1))
  have hp := sqrt_gap_pos n
  push_cast at *
  nlinarith [Real.sqrt_nonneg (n : ℝ),
    sq_nonneg (Real.sqrt ((n : ℝ)+1)-Real.sqrt n-1)]

private theorem discrepancy_step (n : ℕ) :
    ccmPrimeMomentDiscrepancy (n+1)-ccmPrimeMomentDiscrepancy n =
      criticalMellinAtomWeight (n+1) *
        (1+primeMassHalf n/2-Real.sqrt (n+1 : ℕ)) +
          criticalMellinAtomWeight (n+1)^2/4 := by
  unfold ccmPrimeMomentDiscrepancy
  rw [mass_succ, psi_succ]
  linear_combination sqrt_weight_succ n

private theorem tendsto_mass_nat_atTop :
    Tendsto (fun n : ℕ => primeMassHalf n) atTop atTop := by
  have hs := Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hc : 0 < Real.log 2 / 2 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  apply tendsto_atTop_mono' atTop ?_ (hs.const_mul_atTop hc)
  change ∀ᶠ n : ℕ in atTop, (Real.log 2/2)*Real.sqrt (n : ℝ) ≤ primeMassHalf n
  exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    eventually_sqrt_le_primeMassHalf

/-- A deep potential descent forces the actual nonlinear discrepancy below any
prescribed level; divergent admitted mass rules out a permanently descending tail. -/
theorem ccmPrimeMoment_forcing_lt_of_deep_descent (A : ℝ) (n : ℕ)
    (hdown : ccmPrimeMomentPotential (n+1) < ccmPrimeMomentPotential n)
    (hdeep : ccmPrimeMomentPotential (n+1) < A-1) :
    ∃ k : ℕ, n+1 ≤ k ∧ ccmPrimeMomentDiscrepancy k < A := by
  by_contra! hpos
  have hchain : ∀ k : ℕ,
      ccmPrimeMomentPotential (n+k+1) < ccmPrimeMomentPotential (n+k) ∧
      ccmPrimeMomentPotential (n+k+1) < A-1 := by
    intro k
    induction k with
    | zero => simpa using And.intro hdown hdeep
    | succ k ih =>
      have hnext : ccmPrimeMomentPotential (n+k+2) < ccmPrimeMomentPotential (n+k+1) := by
        by_contra! hh
        have hv := ccmPrimeMomentDiscrepancy_lt_valley_add_atom_square (n+k) ih.1.le hh
        have hw := criticalMellinAtomWeight_le_two_of_pos (Nat.succ_pos (n+k))
        have hw0 := atom_nonneg (n+k+1)
        have hd := hpos (n+k+1) (by omega)
        nlinarith
      constructor
      · simpa only [Nat.add_assoc] using hnext
      · simpa only [Nat.add_assoc] using hnext.trans ih.2
  have hy (k : ℕ) : 1+primeMassHalf (n+k+1 : ℕ)/2-Real.sqrt (n+k+1 : ℕ) < -1 := by
    have hdeepk := (hchain k).2
    have hdec := (hchain (k+1)).1
    have hid := ccmPrimeMomentPotential_succ_sub (n+k+1)
    have hgap := sqrt_gap_pos (n+k+1)
    have hgap1 := sqrt_gap_le_one (n+k+1)
    have hmass : primeMassHalf (n+k+1 : ℕ)+2 <
        Real.sqrt (n+k+2 : ℕ)+Real.sqrt (n+k+1 : ℕ) := by
      by_contra! hm
      have hp : 0 ≤ (Real.sqrt (n+k+2 : ℕ)-Real.sqrt (n+k+1 : ℕ)) *
          (primeMassHalf (n+k+1 : ℕ)+2-Real.sqrt (n+k+2 : ℕ)-Real.sqrt (n+k+1 : ℕ)) :=
        mul_nonneg hgap.le (by linarith)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hdec hid hp
      linarith
    have hd := hpos (n+k+1) (by omega)
    rw [ccmPrimeMomentDiscrepancy_eq_potential_add_square] at hd
    nlinarith
  have hbudget : ∀ k : ℕ,
      ccmPrimeMomentDiscrepancy (n+k+1)+primeMassHalf (n+k+1 : ℕ)/2 ≤
        ccmPrimeMomentDiscrepancy (n+1)+primeMassHalf (n+1 : ℕ)/2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := discrepancy_step (n+k+1)
      have hm := mass_succ (n+k+1)
      have hw := criticalMellinAtomWeight_le_two_of_pos (Nat.succ_pos (n+k+1))
      have hw0 := atom_nonneg (n+k+2)
      have hgap := sqrt_gap_pos (n+k+1)
      have hprod : criticalMellinAtomWeight (n+k+2) *
          (1+primeMassHalf (n+k+1 : ℕ)/2-Real.sqrt (n+k+2 : ℕ)) ≤
            -criticalMellinAtomWeight (n+k+2) := by
        have hb := mul_le_mul_of_nonneg_left (hy k).le hw0
        nlinarith [mul_nonneg hw0 hgap.le]
      simp only [Nat.add_assoc, Nat.reduceAdd, Nat.succ_eq_add_one] at *
      nlinarith
  let B := 2*ccmPrimeMomentDiscrepancy (n+1)+primeMassHalf (n+1 : ℕ)-2*A
  have hmhigh := tendsto_mass_nat_atTop.eventually_gt_atTop B
  obtain ⟨k,hk,hlarge⟩ := ((eventually_ge_atTop (n+1)).and hmhigh).exists
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  have hb := hbudget j
  have hd := hpos (n+1+j) (by omega)
  dsimp [B] at hlarge
  have hidx : n+1+j = n+j+1 := by omega
  rw [hidx] at hlarge hd
  linarith

/-- A descent below the unit contact barrier forces later negative forcing. -/
theorem ccmPrimeMoment_negative_forcing_of_deep_descent (n : ℕ)
    (hdown : ccmPrimeMomentPotential (n+1) < ccmPrimeMomentPotential n)
    (hdeep : ccmPrimeMomentPotential (n+1) < -1) :
    ∃ k : ℕ, n+1 ≤ k ∧ ccmPrimeMomentDiscrepancy k < 0 :=
  ccmPrimeMoment_forcing_lt_of_deep_descent 0 n hdown (by simpa using hdeep)

/-- A lower bound on actual forcing imposes the corresponding exact minimum
principle on its Abel potential. -/
theorem ccmPrimeMomentPotential_lower_of_forcing_lower (A : ℝ) (N : ℕ)
    (hpos : ∀ k : ℕ, N ≤ k → A ≤ ccmPrimeMomentDiscrepancy k) :
    ∀ k : ℕ, N ≤ k → min (ccmPrimeMomentPotential N) (A-1) ≤
      ccmPrimeMomentPotential k := by
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction j with
  | zero => simp
  | succ j ih =>
    by_contra! hbad
    have hd : ccmPrimeMomentPotential (N+j+1) < ccmPrimeMomentPotential (N+j) := by
      exact hbad.trans_le ih
    have hdeep : ccmPrimeMomentPotential (N+j+1) < A-1 :=
      hbad.trans_le (min_le_right _ _)
    obtain ⟨l, hl, hneg⟩ := ccmPrimeMoment_forcing_lt_of_deep_descent A (N+j) hd hdeep
    exact (not_lt_of_ge (hpos l (by omega))) hneg

/-- Nonnegative actual forcing prevents a potential crossing below its initial
value and the unit contact barrier. -/
theorem ccmPrimeMomentPotential_lower_of_forcing_nonneg (N : ℕ)
    (hpos : ∀ k : ℕ, N ≤ k → 0 ≤ ccmPrimeMomentDiscrepancy k) :
    ∀ k : ℕ, N ≤ k → min (ccmPrimeMomentPotential N) (-1) ≤
      ccmPrimeMomentPotential k := by
  simpa using ccmPrimeMomentPotential_lower_of_forcing_lower 0 N hpos

end RHTower
