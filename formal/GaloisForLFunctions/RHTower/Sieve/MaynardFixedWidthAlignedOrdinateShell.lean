import GaloisForLFunctions.RHTower.Sieve.MaynardFixedWidthPrimeGapRungCover

/-!
# Dyadically aligned ordinate shells for fixed-width Route T

The arbitrary lower endpoint in a stopped dyadic ordinate ladder can leave one terminal shell
shorter than the unit-two cell geometry required by selected-cell extraction.  Moving that lower
endpoint upward by less than a factor two makes the endpoint ratio an exact dyadic power.  Every
nonterminal shell is then exactly `[T,2T]`; terminal indices define zero interval packets.
-/

noncomputable section
namespace RHTower.Sieve

/-- A lower ordinate can be moved upward by less than factor two so its ratio to the upper cutoff
is an exact dyadic power.  Every nonterminal stopped shell then has length at least the aligned
lower ordinate, while all later shells are exactly degenerate. -/
theorem exists_routeT_dyadicallyAlignedOrdinateLowerCutoff
    {A V : ℝ} (hA : 0 < A) (hAV : 2 * A ≤ V) :
    ∃ n : ℕ, ∃ U : ℝ,
      0 < n ∧ U = V / (((2 ^ n : ℕ) : ℝ)) ∧
      A ≤ U ∧ U < 2 * A ∧ U ≤ V ∧
      (∀ j < n,
        U ≤ routeTComparableWidthLadder U V (j + 1) ∧
        routeTComparableWidthLadder U V j =
          2 * routeTComparableWidthLadder U V (j + 1)) ∧
      (∀ j, n ≤ j → routeTComparableWidthLadder U V j = U) := by
  have hV : 0 < V := by linarith
  have hratio : 1 ≤ V / A := by
    apply (le_div_iff₀ hA).2
    linarith
  obtain ⟨n, hbelow, habove⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  let U : ℝ := V / (((2 ^ n : ℕ) : ℝ))
  have hpN : 0 < (((2 ^ n : ℕ) : ℝ)) := by positivity
  have hn : 0 < n := by
    by_contra hn0
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num at habove
    have hratioTwo : 2 ≤ V / A := by
      exact (le_div_iff₀ hA).2 (by simpa [mul_comm] using hAV)
    linarith
  have hUA : A ≤ U := by
    dsimp only [U]
    apply (le_div_iff₀ hpN).2
    have hmul := (le_div_iff₀ hA).mp hbelow
    simpa only [Nat.cast_pow, Nat.cast_ofNat, mul_comm] using hmul
  have hUtwoA : U < 2 * A := by
    dsimp only [U]
    apply (div_lt_iff₀ hpN).2
    have hmul := (div_lt_iff₀ hA).mp habove
    rw [show (2 : ℝ) ^ (n + 1) = 2 * (((2 ^ n : ℕ) : ℝ)) by
      norm_num [pow_succ, Nat.cast_pow]
      ring] at hmul
    nlinarith
  have hpOne : (1 : ℝ) ≤ (((2 ^ n : ℕ) : ℝ)) := by
    exact_mod_cast Nat.one_le_two_pow
  have hUV : U ≤ V := by
    dsimp only [U]
    apply (div_le_iff₀ hpN).2
    nlinarith
  have hterminal : ∀ j, n ≤ j → routeTComparableWidthLadder U V j = U := by
    intro j hnj
    rw [routeTComparableWidthLadder, max_eq_left_iff]
    dsimp only [U]
    have hpowNat : 2 ^ n ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num) hnj
    have hpow : (((2 ^ n : ℕ) : ℝ)) ≤ (((2 ^ j : ℕ) : ℝ)) := by
      exact_mod_cast hpowNat
    have hpJ : 0 < (((2 ^ j : ℕ) : ℝ)) := by positivity
    apply (div_le_div_iff₀ hpJ hpN).2
    exact mul_le_mul_of_nonneg_left hpow hV.le
  have hshell : ∀ j < n,
      U ≤ routeTComparableWidthLadder U V (j + 1) ∧
      routeTComparableWidthLadder U V j =
        2 * routeTComparableWidthLadder U V (j + 1) := by
    intro j hj
    have hjOne : j + 1 ≤ n := by omega
    have hpowNextNat : 2 ^ (j + 1) ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) hjOne
    have hpowNext : (((2 ^ (j + 1) : ℕ) : ℝ)) ≤
        (((2 ^ n : ℕ) : ℝ)) := by exact_mod_cast hpowNextNat
    have hpowJNat : 2 ^ j ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpowJ : (((2 ^ j : ℕ) : ℝ)) ≤ (((2 ^ n : ℕ) : ℝ)) := by
      exact_mod_cast hpowJNat
    have hpNext : 0 < (((2 ^ (j + 1) : ℕ) : ℝ)) := by positivity
    have hpJ : 0 < (((2 ^ j : ℕ) : ℝ)) := by positivity
    have hUnext : U ≤ V / (((2 ^ (j + 1) : ℕ) : ℝ)) := by
      dsimp only [U]
      apply (div_le_div_iff₀ hpN hpNext).2
      exact mul_le_mul_of_nonneg_left hpowNext hV.le
    have hUj : U ≤ V / (((2 ^ j : ℕ) : ℝ)) := by
      dsimp only [U]
      apply (div_le_div_iff₀ hpN hpJ).2
      exact mul_le_mul_of_nonneg_left hpowJ hV.le
    have hWnext : routeTComparableWidthLadder U V (j + 1) =
        V / (((2 ^ (j + 1) : ℕ) : ℝ)) := by
      rw [routeTComparableWidthLadder, max_eq_right hUnext]
    have hWj : routeTComparableWidthLadder U V j =
        V / (((2 ^ j : ℕ) : ℝ)) := by
      rw [routeTComparableWidthLadder, max_eq_right hUj]
    constructor
    · simpa only [hWnext] using hUnext
    · rw [hWj, hWnext]
      have hpowSucc : (((2 ^ (j + 1) : ℕ) : ℝ)) =
          2 * (((2 ^ j : ℕ) : ℝ)) := by
        push_cast
        simp [pow_succ, mul_comm]
      rw [hpowSucc]
      field_simp
  exact ⟨n, U, hn, rfl, hUA, hUtwoA, hUV, hshell, hterminal⟩

/-- A stopped shell after the exact dyadic endpoint is a genuinely zero interval packet. -/
theorem routeTFixedSourceReparametrizedOrdinateShellPacket_eq_zero_of_terminal
    (L X k : ℕ) (T₀ mu₀ M N R H sigma U V : ℝ) {n j : ℕ}
    (hterminal : ∀ i, n ≤ i → routeTComparableWidthLadder U V i = U)
    (hj : n ≤ j) :
    routeTFixedSourceReparametrizedOrdinateShellPacket
      L X k T₀ mu₀ M N R H sigma U V j = 0 := by
  have hjnext : n ≤ j + 1 := hj.trans (Nat.le_succ j)
  simp only [routeTFixedSourceReparametrizedOrdinateShellPacket,
    hterminal j hj, hterminal (j + 1) hjnext,
    routeTFixedSourceAdjacentIntervalPacket, intervalIntegral.integral_same]

/-- Under aligned cutoff, every positive-defect selected shell is nonterminal, begins above the
prescribed floor, and is exactly a full dyadic interval `[T,2T]`.  Hence a floor at least two
eliminates the short-shell residual required by even-cell extraction. -/
theorem routeT_aligned_positiveDefect_shell_fullDyadic
    (L X k : ℕ) (T₀ mu₀ M N R H sigma U V B : ℝ) {n j : ℕ}
    (hB : 0 < B) (hfloor : 2 ≤ U)
    (hshell : ∀ i < n,
      U ≤ routeTComparableWidthLadder U V (i + 1) ∧
      routeTComparableWidthLadder U V i =
        2 * routeTComparableWidthLadder U V (i + 1))
    (hterminal : ∀ i, n ≤ i → routeTComparableWidthLadder U V i = U)
    (hlarge : B ≤ ‖routeTFixedSourceReparametrizedOrdinateShellPacket
      L X k T₀ mu₀ M N R H sigma U V j‖) :
    j < n ∧
      routeTComparableWidthLadder U V (j + 1) + 2 ≤
        routeTComparableWidthLadder U V j ∧
      routeTComparableWidthLadder U V j =
        2 * routeTComparableWidthLadder U V (j + 1) := by
  have hj : j < n := by
    by_contra hjnot
    have hnj : n ≤ j := Nat.le_of_not_gt hjnot
    have hzero :=
      routeTFixedSourceReparametrizedOrdinateShellPacket_eq_zero_of_terminal
        L X k T₀ mu₀ M N R H sigma U V hterminal hnj
    rw [hzero, norm_zero] at hlarge
    linarith
  have hgeom := hshell j hj
  refine ⟨hj, ?_, hgeom.2⟩
  rw [hgeom.2]
  linarith

end RHTower.Sieve
