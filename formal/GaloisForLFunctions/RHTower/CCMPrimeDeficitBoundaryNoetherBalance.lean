import GaloisForLFunctions.RHTower.CCMPrimeDeficitBoundaryOscillator

/-!
# Exact arithmetic forcing of the boundary Noether charge

Every entry changes the charge by signed cross work plus a diagonal
square. The actual Möbius diagonal over the entire thick boundary shell
is at most one. Thus the full charge-minus-cross-work balance is bounded,
while the signed cross work itself remains an explicit open target.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

theorem ccmPrimeDeficitBoundaryPosition_eq_ramp_sum (m k : ℕ) (t : ℝ) :
    ccmPrimeDeficitBoundaryPosition m k t = Real.exp (-(t / 2)) *
      ∑ n ∈ Finset.Icc 1 (m + 3 * k), logarithmicLongTail m moebiusCoeff n *
        logarithmicExponentialRamp (t - Real.log n) := by
  unfold ccmPrimeDeficitBoundaryPosition ccmPrimeDeficitBoundaryExpProfile
    ccmPrimeDeficitBoundaryCountProfile logarithmicFiniteEntryProfile
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : Real.log n ≤ t
  · rw [logarithmicExponentialRamp_of_nonneg (sub_nonneg.mpr hn)]
    simp only [Set.mem_Ici, hn, Set.indicator_of_mem, mul_one]
    ring
  · have hneg : t - Real.log n ≤ 0 := by linarith
    simp [Set.indicator, hn, logarithmicExponentialRamp_of_nonpos hneg]

/-- Position is continuous across every actual arithmetic impulse. -/
theorem continuous_ccmPrimeDeficitBoundaryPosition (m k : ℕ) :
    Continuous (ccmPrimeDeficitBoundaryPosition m k) := by
  change Continuous (fun t => ccmPrimeDeficitBoundaryPosition m k t)
  simp_rw [ccmPrimeDeficitBoundaryPosition_eq_ramp_sum]
  unfold logarithmicExponentialRamp
  fun_prop

/-- Between entries, the reflected energy density is the derivative of
a bilocal current. Arithmetic impulses account for the missing jumps. -/
theorem hasDerivAt_mellinPrefix_reflectedCurrent
    (w v : ℕ → ℝ) (N M : ℕ) (T t : ℝ) :
    HasDerivAt (fun s => mellinPrefixPosition w N s * mellinPrefixMomentum v M (T - s))
      (mellinPrefixMomentum w N t * mellinPrefixMomentum v M (T - t) -
        mellinPrefixPosition w N t * mellinPrefixPosition v M (T - t) / 4) t := by
  have hp := (hasDerivAt_mellinPrefixMomentum v M (T - t)).comp t
    ((hasDerivAt_const t T).sub (hasDerivAt_id t))
  apply ((hasDerivAt_mellinPrefixPosition w N t).mul hp).congr_deriv
  simp only [Function.comp_apply]
  ring

/-- Opposite time directions preserve this bilocal charge on each fixed
prefix segment; it is distinct from the reflected energy density. -/
theorem hasDerivAt_mellinPrefix_reflectedCharge
    (w v : ℕ → ℝ) (N M : ℕ) (T t : ℝ) :
    HasDerivAt (fun s => mellinPrefixMomentum w N s * mellinPrefixMomentum v M (T - s) +
      mellinPrefixPosition w N s * mellinPrefixPosition v M (T - s) / 4) 0 t := by
  have hp := (hasDerivAt_mellinPrefixMomentum v M (T - t)).comp t
    ((hasDerivAt_const t T).sub (hasDerivAt_id t))
  have hq := (hasDerivAt_mellinPrefixPosition v M (T - t)).comp t
    ((hasDerivAt_const t T).sub (hasDerivAt_id t))
  apply (((hasDerivAt_mellinPrefixMomentum w N t).mul hp).add
    (((hasDerivAt_mellinPrefixPosition w N t).mul hq).div_const 4)).congr_deriv
  simp only [Function.comp_apply]
  ring

def mellinPrefixNoetherCrossWork (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    w n * (mellinPrefixReciprocal w (n - 1) + mellinPrefixMass w (n - 1) / n)

def mellinPrefixNoetherDiagonal (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, w n ^ 2 / n

theorem mellinPrefix_noether_balance (w : ℕ → ℝ) (N : ℕ) :
    mellinPrefixReciprocal w N * mellinPrefixMass w N =
      mellinPrefixNoetherCrossWork w N + mellinPrefixNoetherDiagonal w N := by
  induction N with
  | zero => simp [mellinPrefixReciprocal, mellinPrefixMass,
      mellinPrefixNoetherCrossWork, mellinPrefixNoetherDiagonal]
  | succ N ih =>
    have hc := mellinPrefix_noether_energy_jump w N
    have hw : mellinPrefixNoetherCrossWork w (N + 1) = mellinPrefixNoetherCrossWork w N +
        w (N + 1) * (mellinPrefixReciprocal w N + mellinPrefixMass w N / (N + 1 : ℕ)) := by
      unfold mellinPrefixNoetherCrossWork
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp only [Nat.add_sub_cancel]
    have hd : mellinPrefixNoetherDiagonal w (N + 1) = mellinPrefixNoetherDiagonal w N +
        w (N + 1) ^ 2 / (N + 1 : ℕ) := by
      exact Finset.sum_Icc_succ_top (by omega) (fun n => w n ^ 2 / n)
    rw [hw, hd]
    linarith only [hc, ih]

theorem mellinPrefixNoetherDiagonal_nonneg (w : ℕ → ℝ) (N : ℕ) :
    0 ≤ mellinPrefixNoetherDiagonal w N :=
  Finset.sum_nonneg (fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n))

theorem mellinPrefixNoetherDiagonal_mobius_tail_le
    {m k N : ℕ} (hm : 0 < m) (hN : N ≤ m + 3 * k) :
    mellinPrefixNoetherDiagonal (logarithmicLongTail m moebiusCoeff) N ≤ 3 * (k : ℝ) / m := by
  let w := logarithmicLongTail m moebiusCoeff
  have hsubN : Finset.Icc 1 N ⊆ Finset.Icc 1 (m + 3 * k) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hN⟩
  have hsubJ : Finset.Icc (m + 1) (m + 3 * k) ⊆ Finset.Icc 1 (m + 3 * k) := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hn).1; omega, (Finset.mem_Icc.mp hn).2⟩
  have hstrip : (∑ n ∈ Finset.Icc 1 (m + 3 * k), w n ^ 2 / n) =
      ∑ n ∈ Finset.Icc (m + 1) (m + 3 * k), w n ^ 2 / n := by
    symm
    apply Finset.sum_subset hsubJ
    intro n hn hnot
    have hmnot : ¬ m < n := by
      have := (Finset.mem_Icc.mp hn).2
      simp only [Finset.mem_Icc] at hnot
      omega
    simp [w, logarithmicLongTail, hmnot]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc (m + 1) (m + 3 * k)) : w n ^ 2 / n ≤ 1 / m := by
    have hmn : (m : ℝ) ≤ n := by exact_mod_cast (show m ≤ n by have := (Finset.mem_Icc.mp hn).1; omega)
    have hw : w n ^ 2 ≤ 1 := by
      exact (sq_le_one_iff_abs_le_one _).mpr (abs_logarithmicLongTail_moebiusCoeff_le_one m n)
    calc
      _ ≤ 1 / (n : ℝ) := div_le_div_of_nonneg_right hw (Nat.cast_nonneg n)
      _ ≤ _ := one_div_le_one_div_of_le hmR hmn
  change (∑ n ∈ Finset.Icc 1 N, w n ^ 2 / n) ≤ _
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (m + 3 * k), w n ^ 2 / n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubN (fun n _ _ => by positivity)
    _ = ∑ n ∈ Finset.Icc (m + 1) (m + 3 * k), w n ^ 2 / n := hstrip
    _ ≤ ∑ _n ∈ Finset.Icc (m + 1) (m + 3 * k), (1 : ℝ) / m := Finset.sum_le_sum hterm
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Icc,
        show m + 3 * k + 1 - (m + 1) = 3 * k by omega, nsmul_eq_mul,
        Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- All actual entry impulses are included: the surviving diagonal forcing
has total size at most one over a thick shell. -/
theorem abs_ccmPrimeDeficitBoundary_noether_energy_sub_crossWork_le_one
    {m k : ℕ} (hm : 0 < m) (hk : 3 * k ≤ m) (t : ℝ) :
    |ccmPrimeDeficitBoundaryMomentum m k t ^ 2 - ccmPrimeDeficitBoundaryPosition m k t ^ 2 / 4 -
      mellinPrefixNoetherCrossWork (logarithmicLongTail m moebiusCoeff)
        (min (m + 3 * k) ⌊Real.exp t⌋₊)| ≤ 1 := by
  rw [ccmPrimeDeficitBoundary_noether_energy, mellinPrefix_noether_balance,
    add_sub_cancel_left,
    abs_of_nonneg (mellinPrefixNoetherDiagonal_nonneg _ _)]
  calc
    _ ≤ 3 * (k : ℝ) / m := mellinPrefixNoetherDiagonal_mobius_tail_le hm (min_le_left _ _)
    _ ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hm : (0 : ℝ) < m)]
      exact_mod_cast hk

end RHTower
