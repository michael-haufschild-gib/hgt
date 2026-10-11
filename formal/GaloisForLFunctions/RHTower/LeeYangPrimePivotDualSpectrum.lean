import GaloisForLFunctions.RHTower.RiemannSiegelLeeYangChain
import Mathlib.Data.Nat.Prime.Basic

/-!
# Dual frequencies at prime pivots

At a prime Γ-site pivot `M`, the two-wall frequency `log (b/a)` with
`2 ≤ a < b < M` belongs to the frozen Riemann–Siegel dual alphabet
`log ℕ ∪ log (M/ℕ)` exactly when `a ∣ b`.  The second alphabet branch is
excluded by primality: `b ∣ M a` would force `b ∣ a`.
-/

namespace RHTower.LeeYangChain

/-- Rational Γ-site field base; its logarithm is `gammaFreq`. -/
def gammaSiteRatio (i : ℕ) : ℚ := ((i + 2 : ℕ) : ℚ) / (i + 1)

/-- A minus-spin interval between walls `j < k` has frequency base
`(k+2)/(j+2)`. -/
theorem prod_gammaSiteRatio_Ico (j k : ℕ) (hjk : j ≤ k) :
    ∏ i ∈ Finset.Ico (j + 1) (k + 1), gammaSiteRatio i =
      ((k + 2 : ℕ) : ℚ) / (j + 2) := by
  induction k with
  | zero =>
    have hj : j = 0 := by omega
    subst j
    simp
  | succ k ih =>
    by_cases hj : j ≤ k
    · rw [Finset.prod_Ico_succ_top (by omega), ih hj]
      unfold gammaSiteRatio
      push_cast
      have hden : (((j + 2 : ℕ) : ℚ) ≠ 0) := by positivity
      have hmid : (((k + 2 : ℕ) : ℚ) ≠ 0) := by positivity
      field_simp
      ring
    · have hjeq : j = k + 1 := by omega
      subst j
      simp only [Finset.Ico_self, Finset.prod_empty]
      have hden : (((k + 1 + 2 : ℕ) : ℚ) ≠ 0) := by positivity
      simpa only [Nat.cast_add, Nat.cast_ofNat] using (div_self hden).symm

/-- A positive rational frequency lies in the integer or pivot-dual branch. -/
def InPrimePivotDualAlphabet (M : ℕ) (q : ℚ) : Prop :=
  (∃ n : ℕ, 0 < n ∧ q = n) ∨
    (∃ n : ℕ, 0 < n ∧ q = (M : ℚ) / n)

theorem primePivot_twoWall_ratio_mem_iff_dvd (M a b : ℕ)
    (hM : M.Prime) (ha : 2 ≤ a) (hab : a < b) (hb : b < M) :
    InPrimePivotDualAlphabet M ((b : ℚ) / a) ↔ a ∣ b := by
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  constructor
  · rintro (⟨n, hn, heq⟩ | ⟨n, hn, heq⟩)
    · have hn' : b = a * n := by
        have hq : (b : ℚ) = (a : ℚ) * n := by
          have h := (div_eq_iff (Nat.cast_ne_zero.mpr ha0)).mp heq
          simpa [mul_comm] using h
        exact_mod_cast hq
      exact ⟨n, hn'⟩
    · have hn0 : n ≠ 0 := by omega
      have hq : (b : ℚ) * n = (M : ℚ) * a := by
        apply (div_eq_div_iff (Nat.cast_ne_zero.mpr ha0)
          (Nat.cast_ne_zero.mpr hn0)).mp at heq
        simpa [mul_comm] using heq
      have hnat : b * n = M * a := by exact_mod_cast hq
      have hdiv : b ∣ M * a := ⟨n, hnat.symm⟩
      have hcop : b.Coprime M :=
        (Nat.coprime_of_lt_prime hb0 hb hM).symm
      have hba : b ∣ a := hcop.dvd_of_dvd_mul_left hdiv
      have hle : b ≤ a := Nat.le_of_dvd (by omega) hba
      omega
  · rintro ⟨n, rfl⟩
    have hn : 0 < n := by
      by_contra h
      have hn0 : n = 0 := by omega
      simp [hn0] at hab
    left
    refine ⟨n, hn, ?_⟩
    rw [Nat.cast_mul, mul_div_cancel_left₀]
    exact Nat.cast_ne_zero.mpr ha0

/-- For an interior two-wall spin word at a prime pivot, dual-spectrum
admission is equivalent to divisibility of the two wall labels. -/
theorem primePivot_twoWall_gammaSpectrum_iff_dvd (M j k : ℕ)
    (hM : M.Prime) (hjk : j < k) (hk : k + 2 < M) :
    InPrimePivotDualAlphabet M
      (∏ i ∈ Finset.Ico (j + 1) (k + 1), gammaSiteRatio i) ↔
      j + 2 ∣ k + 2 := by
  rw [prod_gammaSiteRatio_Ico j k hjk.le]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (primePivot_twoWall_ratio_mem_iff_dvd M (j + 2) (k + 2)
      hM (by omega) (by omega) hk)

/-- Pairwise admission of two-wall frequencies at a prime pivot is exactly an
ordered divisibility chain. -/
theorem primePivot_pairwise_dual_iff_divisibility_chain (M : ℕ) (hM : M.Prime)
    (W : Finset ℕ) (hW : ∀ a ∈ W, 2 ≤ a ∧ a < M) :
    (∀ a ∈ W, ∀ b ∈ W, a < b →
      InPrimePivotDualAlphabet M ((b : ℚ) / a)) ↔
      (∀ a ∈ W, ∀ b ∈ W, a < b → a ∣ b) := by
  constructor
  · intro h a ha b hb hab
    exact (primePivot_twoWall_ratio_mem_iff_dvd M a b hM (hW a ha).1 hab
      (hW b hb).2).mp (h a ha b hb hab)
  · intro h a ha b hb hab
    exact (primePivot_twoWall_ratio_mem_iff_dvd M a b hM (hW a ha).1 hab
      (hW b hb).2).mpr (h a ha b hb hab)

/-- A wall occurs where neighbouring spins have different signs.  A finite
set records the sites with negative spin. -/
def GammaSpinWallAt (S : Finset ℕ) (i : ℕ) : Prop :=
  (i ∈ S ∧ i + 1 ∉ S) ∨ (i ∉ S ∧ i + 1 ∈ S)

/-- Spin words supported on sites `0,…,N` using only permitted walls. -/
def GammaSpinWordAllowed (N : ℕ) (W S : Finset ℕ) : Prop :=
  S ⊆ Finset.range (N + 1) ∧
    ∀ i < N, GammaSpinWallAt S i → i ∈ W

/-- Frequency base of a Γ-site spin word. -/
def gammaSpinWordRatio (S : Finset ℕ) : ℚ :=
  ∏ i ∈ S, gammaSiteRatio i

/-- The interval of negative spins between two walls has exactly those two
walls. -/
theorem gammaSpinWallAt_interval_iff (j k i : ℕ) (hjk : j < k) :
    GammaSpinWallAt (Finset.Ico (j + 1) (k + 1)) i ↔ i = j ∨ i = k := by
  simp only [GammaSpinWallAt, Finset.mem_Ico]
  omega

theorem gammaSpinWord_interval_allowed (N : ℕ) (W : Finset ℕ)
    {j k : ℕ} (hjk : j < k) (hkN : k < N) (hjW : j ∈ W) (hkW : k ∈ W) :
    GammaSpinWordAllowed N W (Finset.Ico (j + 1) (k + 1)) := by
  constructor
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [Finset.mem_range]
    omega
  · intro i hi hwall
    rcases (gammaSpinWallAt_interval_iff j k i hjk).mp hwall with rfl | rfl
    · exact hjW
    · exact hkW

/-- The field frequency of the interval spin word is the two-wall rational
frequency. -/
theorem gammaSpinWordRatio_interval (j k : ℕ) (hjk : j ≤ k) :
    gammaSpinWordRatio (Finset.Ico (j + 1) (k + 1)) =
      ((k + 2 : ℕ) : ℚ) / (j + 2) :=
  prod_gammaSiteRatio_Ico j k hjk

/-- If every permitted spin word stays in the dual alphabet at a prime pivot,
the active walls form an ordered divisibility chain. -/
theorem primePivot_spinSpectrum_forces_divisibility_chain (N : ℕ)
    (hM : (N + 2).Prime) (W : Finset ℕ) (hW : W ⊆ Finset.range N)
    (hdual : ∀ S, GammaSpinWordAllowed N W S →
      InPrimePivotDualAlphabet (N + 2) (gammaSpinWordRatio S)) :
    ∀ j ∈ W, ∀ k ∈ W, j < k → j + 2 ∣ k + 2 := by
  intro j hj k hk hjk
  have hkN : k < N := Finset.mem_range.mp (hW hk)
  have hallowed := gammaSpinWord_interval_allowed N W hjk hkN hj hk
  have hspectrum := hdual _ hallowed
  rw [gammaSpinWordRatio_interval j k hjk.le] at hspectrum
  have hspectrum' : InPrimePivotDualAlphabet (N + 2)
      (((k + 2 : ℕ) : ℚ) / ((j + 2 : ℕ) : ℚ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hspectrum
  exact (primePivot_twoWall_ratio_mem_iff_dvd (N + 2) (j + 2) (k + 2)
    hM (by omega) (by omega) (by omega)).mp hspectrum'

end RHTower.LeeYangChain
