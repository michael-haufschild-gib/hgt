import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsHaveUniformKernelBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheWeightedAffineShellErrorsVanishInHarmonicNorm

/-!
# The upward prime rows realize the completed shell correction

For every fixed overlap and conductor, the literal infinite upward prime-power
row acts on the Ramanujan profile by its signed shell correction, with residual
norm tending to zero after logarithmic normalization.

Exact offset reindexing retains both horizon cutoffs. The logarithmic kernel
is replaced by its reciprocal-offset kernel with a summed geometric error
`O(mertensSum(N+B)/N)`. Moving the cutoffs costs only the vanishing reciprocal
Mangoldt mass of a bounded prime-index window about `N/n`. The remaining
source is exactly the pair of positive and reflected affine shell readings;
their common signed mean and harmonic norm limits complete the proof.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The normalized logarithmic kernel, including the square-root conductor Jacobian. -/
def logarithmicUpwardKernel (φ : ℝ → ℝ) (c : ℝ) (N T j : ℕ) : ℝ :=
  Real.sqrt T / Real.sqrt j * shellAutocorr φ ((N : ℝ) / c * (Real.log j - Real.log T))

private theorem normalized_bumpCorr_atomDilate_signed {φ : ℝ → ℝ} {w : ℝ} (hw : 0 < w) (s : ℝ) :
    bumpCorr (atomDilate φ w) s / (∫ u, atomDilate φ w u ^ 2) =
      shellAutocorr φ (s / w) / (∫ u, φ u ^ 2) := by
  have h := integral_atomDilate_mul_shift (φ := φ) hw (-s)
  simp only [sub_neg_eq_add, neg_div, shellAutocorr_neg] at h
  change bumpCorr (atomDilate φ w) s = w * shellAutocorr φ (s / w) at h
  rw [h, integral_atomDilate_sq hw, mul_div_mul_left _ _ hw.ne']

/-- Exact square-root normalization of one literal upward prime-power term. -/
theorem sqrt_mul_upward_offset_factor {φ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    {N k n j : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hn : 1 ≤ n) (hj : 1 ≤ j) (m : ℕ) :
    Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
      (ramanujanLagCoefficient m j / Real.sqrt j *
        bumpCorr (atomDilate φ (c / N)) (Real.log (k * n : ℕ) - Real.log j)) /
      (∫ u, atomDilate φ (c / N) u ^ 2)) =
      1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
        ramanujanLagCoefficient m j * logarithmicUpwardKernel φ c N (k * n) j) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hsk : Real.sqrt k ≠ 0 := (Real.sqrt_pos.mpr hk0).ne'
  have hsj : Real.sqrt j ≠ 0 := (Real.sqrt_pos.mpr hj0).ne'
  have hΛ : _root_.RHTower.vonMangoldtAtom k = (ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k := by
    by_cases hk2 : 2 ≤ k
    · exact vonMangoldtAtom_eq hk2
    · have hk1 : k = 1 := by omega
      subst k
      simp [RHTower.vonMangoldtAtom]
  have hcorr : bumpCorr (atomDilate φ (c / N)) (Real.log (k * n : ℕ) - Real.log j) /
      (∫ u, atomDilate φ (c / N) u ^ 2) =
      shellAutocorr φ ((N : ℝ) / c * (Real.log j - Real.log (k * n : ℕ))) / (∫ u, φ u ^ 2) := by
    rw [normalized_bumpCorr_atomDilate_signed (div_pos hc hN0)]
    have heq : (Real.log (k * n : ℕ) - Real.log j) / (c / N) =
        -((N : ℝ) / c * (Real.log j - Real.log (k * n : ℕ))) := by field_simp; ring
    rw [heq, shellAutocorr_neg]
  have hfactor : Real.sqrt n * ((ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k) *
      (ramanujanLagCoefficient m j / Real.sqrt j) =
      (ArithmeticFunction.vonMangoldt k : ℝ) / k * ramanujanLagCoefficient m j *
        (Real.sqrt (k * n : ℕ) / Real.sqrt j) := by
    rw [Nat.cast_mul, Real.sqrt_mul hk0.le]
    field_simp [hsk, hsj, hk0.ne']
    rw [Real.sq_sqrt hk0.le]
    ring
  calc
    _ = (Real.sqrt n * ((ArithmeticFunction.vonMangoldt k : ℝ) / Real.sqrt k) *
        (ramanujanLagCoefficient m j / Real.sqrt j)) *
        (bumpCorr (atomDilate φ (c / N)) (Real.log (k * n : ℕ) - Real.log j) /
          (∫ u, atomDilate φ (c / N) u ^ 2)) := by rw [hΛ]; ring
    _ = _ := by rw [hfactor, hcorr]; dsimp only [logarithmicUpwardKernel]; ring

/-- Both logarithmic offsets of one prime power, with their actual cutoffs. -/
def logarithmicUpwardOffset (φ : ℝ → ℝ) (c : ℝ) (N m n k h : ℕ) : ℝ :=
  (if k * n + h ≤ N then ramanujanLagCoefficient m (k * n + h) *
    logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0) +
  (if h < k * n ∧ k * n - h ≤ N then ramanujanLagCoefficient m (k * n - h) *
    logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0)

/-- The finite logarithmic source after square-root normalization of the conductor row. -/
def logarithmicUpwardCoefficient (φ : ℝ → ℝ) (c : ℝ) (B N m n : ℕ) : ℝ :=
  1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B), (ArithmeticFunction.vonMangoldt k : ℝ) / k *
    ∑ h ∈ Icc 1 B, logarithmicUpwardOffset φ c N m n k h

/-- Replace only the logarithmic kernel, retaining both actual horizon cutoffs. -/
def linearizedUpwardOffset (φ : ℝ → ℝ) (c : ℝ) (N m n k h : ℕ) : ℝ :=
  ((if k * n + h ≤ N then ramanujanLagCoefficient m (k * n + h) else 0) +
    (if h < k * n ∧ k * n - h ≤ N then ramanujanLagCoefficient m (k * n - h) else 0)) *
    shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ)))

def linearizedUpwardCoefficient (φ : ℝ → ℝ) (c : ℝ) (B N m n : ℕ) : ℝ :=
  1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B), (ArithmeticFunction.vonMangoldt k : ℝ) / k *
    ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h

/-- Exact finite-source normalization of the literal upward Ramanujan row. -/
theorem sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient {φ : ℝ → ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N n : ℕ} (hn : n ∈ Icc 1 N) (m : ℕ) :
    Real.sqrt n * (upwardPrimeRow (atomDilate φ (c / N)) N
      (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
        (∫ u, atomDilate φ (c / N) u ^ 2)) =
      logarithmicUpwardCoefficient φ c (exteriorPrimeStrip c) N m n := by
  have hN : 1 ≤ N := (mem_Icc.mp hn).1.trans (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := by
    intro u hu
    change φ (u / (c / N)) = 0
    apply hsupp
    intro hv
    apply hu
    refine ⟨?_, ?_⟩
    · simpa only [zero_mul] using (le_div_iff₀ (div_pos hc hN0)).mp hv.1
    · simpa only [one_mul] using (div_le_iff₀ (div_pos hc hN0)).mp hv.2
  have hterm (k : ℕ) (hk : k ∈ Icc 1 (N + exteriorPrimeStrip c)) (h : ℕ)
      (hh : h ∈ Icc 1 (exteriorPrimeStrip c)) :
      Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
        (positiveUpwardOffset (atomDilate φ (c / N)) N m n k h +
          negativeUpwardOffset (atomDilate φ (c / N)) N m n k h) /
          (∫ u, atomDilate φ (c / N) u ^ 2)) =
      1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
        logarithmicUpwardOffset φ c N m n k h) := by
    have hk1 := (mem_Icc.mp hk).1
    have hn1 := (mem_Icc.mp hn).1
    have hh1 := (mem_Icc.mp hh).1
    have hp : Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
        positiveUpwardOffset (atomDilate φ (c / N)) N m n k h /
          (∫ u, atomDilate φ (c / N) u ^ 2)) =
        1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
          (if k * n + h ≤ N then ramanujanLagCoefficient m (k * n + h) *
            logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0)) := by
      dsimp only [positiveUpwardOffset]
      split_ifs
      · simpa only [mul_assoc] using sqrt_mul_upward_offset_factor hc hN hk1 hn1
          (show 1 ≤ k * n + h by omega) m
      · simp only [mul_zero, zero_div]
    have hm : Real.sqrt n * (_root_.RHTower.vonMangoldtAtom k *
        negativeUpwardOffset (atomDilate φ (c / N)) N m n k h /
          (∫ u, atomDilate φ (c / N) u ^ 2)) =
        1 / (∫ u, φ u ^ 2) * ((ArithmeticFunction.vonMangoldt k : ℝ) / k *
          (if h < k * n ∧ k * n - h ≤ N then ramanujanLagCoefficient m (k * n - h) *
            logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0)) := by
      dsimp only [negativeUpwardOffset]
      split_ifs with hhT
      · simpa only [mul_assoc] using sqrt_mul_upward_offset_factor hc hN hk1 hn1
          (show 1 ≤ k * n - h by omega) m
      · simp only [mul_zero, zero_div]
    dsimp only [logarithmicUpwardOffset]
    linear_combination hp + hm
  rw [upwardRamanujanRow_eq_offsets hc hn hg, logarithmicUpwardCoefficient]
  simp only [sum_div, mul_sum]
  exact sum_congr rfl fun k hk => sum_congr rfl fun h hh => hterm k hk h hh

/-- The literal finite logarithmic source differs from the same source with reciprocal
weights by a vanishing geometric error; every prime power and cutoff is retained. -/
theorem exists_logarithmicUpwardCoefficient_error_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (B m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, 1 ≤ n →
      |logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n| ≤
        D * mertensSum (N + B) / N := by
  obtain ⟨C, hC, N₀, hker⟩ := exists_logPrimeKernel_linearization_bound hφ hsupp hc B
  let D := 2 * (B : ℝ) * m.totient * C / (∫ u, φ u ^ 2)
  refine ⟨D, by dsimp only [D]; positivity, max 1 N₀, ?_⟩
  intro N hN n hn
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNN : N₀ ≤ N := (le_max_right _ _).trans hN
  have hpoint (k : ℕ) (hk : k ∈ Icc 1 (N + B)) (h : ℕ) (hh : h ∈ Icc 1 B) :
      |logarithmicUpwardOffset φ c N m n k h - linearizedUpwardOffset φ c N m n k h| ≤
        2 * m.totient * C / N := by
    have hk1 := (mem_Icc.mp hk).1
    have hh1 := (mem_Icc.mp hh).1
    have hhB := (mem_Icc.mp hh).2
    have hT : 1 ≤ k * n := Nat.mul_pos hk1 hn
    have hgap : |((k * n + h : ℕ) : ℝ) - (k * n : ℕ)| ≤ B := by
      simp only [Nat.cast_add, add_sub_cancel_left, abs_of_nonneg (show (0 : ℝ) ≤ h from Nat.cast_nonneg h)]
      exact_mod_cast hhB
    have hpker : |logarithmicUpwardKernel φ c N (k * n) (k * n + h) -
        shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ)))| ≤ C / N := by
      have h := hker N hNN (k * n) (k * n + h) hT (by omega) (by omega) hgap
      simpa only [logarithmicUpwardKernel, Nat.cast_add, add_sub_cancel_left] using h
    have hnp : 0 ≤ (m.totient : ℝ) * (C / N) := by positivity
    have hp : |(if k * n + h ≤ N then ramanujanLagCoefficient m (k * n + h) *
          logarithmicUpwardKernel φ c N (k * n) (k * n + h) else 0) -
        (if k * n + h ≤ N then ramanujanLagCoefficient m (k * n + h) else 0) *
          shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ)))| ≤
        (m.totient : ℝ) * (C / N) := by
      by_cases hcut : k * n + h ≤ N
      · rw [if_pos hcut, if_pos hcut, ← mul_sub, abs_mul]
        exact mul_le_mul
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m (k * n + h))
          hpker (abs_nonneg _) (Nat.cast_nonneg _)
      · simpa only [if_neg hcut, zero_mul, sub_zero, abs_zero] using hnp
    have hm : |(if h < k * n ∧ k * n - h ≤ N then ramanujanLagCoefficient m (k * n - h) *
          logarithmicUpwardKernel φ c N (k * n) (k * n - h) else 0) -
        (if h < k * n ∧ k * n - h ≤ N then ramanujanLagCoefficient m (k * n - h) else 0) *
          shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ)))| ≤
        (m.totient : ℝ) * (C / N) := by
      by_cases hcut : h < k * n ∧ k * n - h ≤ N
      · have hgap' : |((k * n - h : ℕ) : ℝ) - (k * n : ℕ)| ≤ B := by
          rw [Nat.cast_sub hcut.1.le, sub_sub_cancel_left, abs_neg,
            abs_of_nonneg (show (0 : ℝ) ≤ h from Nat.cast_nonneg h)]
          exact_mod_cast hhB
        have hkerm := hker N hNN (k * n) (k * n - h) hT (by omega) (by omega) hgap'
        have heq : (N : ℝ) / c * ((((k * n - h : ℕ) : ℝ) - (k * n : ℕ)) / (k * n : ℕ)) =
            -((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ))) := by
          rw [Nat.cast_sub hcut.1.le]
          ring
        rw [heq, shellAutocorr_neg] at hkerm
        rw [if_pos hcut, if_pos hcut, ← mul_sub, abs_mul]
        exact mul_le_mul
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m (k * n - h))
          hkerm (abs_nonneg _) (Nat.cast_nonneg _)
      · simpa only [if_neg hcut, zero_mul, sub_zero, abs_zero] using hnp
    dsimp only [logarithmicUpwardOffset, linearizedUpwardOffset]
    rw [add_mul, add_sub_add_comm]
    exact (abs_add_le _ _).trans ((add_le_add hp hm).trans_eq (by ring))
  unfold logarithmicUpwardCoefficient linearizedUpwardCoefficient
  rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hM)]
  calc
    _ ≤ 1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
        |(ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, logarithmicUpwardOffset φ c N m n k h -
          (ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ 1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
        (ArithmeticFunction.vonMangoldt k : ℝ) / k * ((B : ℝ) * (2 * m.totient * C / N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro k hk
      rw [← mul_sub, ← sum_sub_distrib, abs_mul,
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h := (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun h hh => hpoint k hk h hh)
      simpa only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] using h
    _ = D * mertensSum (N + B) / N := by
      rw [← sum_mul]
      dsimp only [D, mertensSum]
      ring

/-- The reciprocal source with the product cutoff `kn≤N` and the reflected negative shift. -/
def reciprocalUpwardOffset (φ : ℝ → ℝ) (c : ℝ) (N m n k h : ℕ) : ℝ :=
  (if k * n ≤ N then ramanujanLagCoefficient m (k * n + h) +
    ramanujanLagCoefficient m (k * n + reflectedAffineShift m h) else 0) *
    shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ)))

def reciprocalUpwardCoefficient (φ : ℝ → ℝ) (c : ℝ) (B N m n : ℕ) : ℝ :=
  1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B), (ArithmeticFunction.vonMangoldt k : ℝ) / k *
    ∑ h ∈ Icc 1 B, reciprocalUpwardOffset φ c N m n k h

private theorem reciprocal_shell_zero_of_small_product {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N T h : ℕ} (hN : c ≤ N) (hT : 1 ≤ T) (hh : T ≤ h) :
    shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / T)) = 0 := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hNc : (1 : ℝ) ≤ (N : ℝ) / c := (one_le_div hc).mpr hN
  have hhT : (1 : ℝ) ≤ (h : ℝ) / T := (one_le_div hT0).mpr (by exact_mod_cast hh)
  apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
  exact (one_le_mul_of_one_le_of_one_le hNc hhT).trans (le_abs_self _)

/-- The cutoff discrepancy is supported only on the bounded prime-index boundary window. -/
theorem linearizedUpwardOffset_eq_reciprocal_of_not_boundary {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {B N m n k h : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hh : h ∈ Icc 1 B) (hN : c ≤ N)
    (hout : k ∉ Icc (N / n - B) (N / n + B + 1)) :
    linearizedUpwardOffset φ c N m n k h = reciprocalUpwardOffset φ c N m n k h := by
  have hhB := (mem_Icc.mp hh).2
  have hT : 1 ≤ k * n := Nat.mul_pos hk hn
  by_cases hhT : h < k * n
  · have hfar : k * n + B < N ∨ N + B < k * n := by
      by_contra h
      have hlow : N ≤ k * n + B := by omega
      have hhigh : k * n ≤ N + B := by omega
      have hgap : |(k : ℝ) * n - N| ≤ B := by
        apply abs_le.mpr
        have hlo : (N : ℝ) ≤ (k : ℝ) * n + B := by exact_mod_cast hlow
        have hhi : (k : ℝ) * n ≤ N + B := by exact_mod_cast hhigh
        constructor <;> linarith only [hlo, hhi]
      exact hout (prime_product_boundary_mem hn hgap)
    rcases hfar with hfar | hfar
    · have hp : k * n + h ≤ N := by omega
      have hncut : h < k * n ∧ k * n - h ≤ N := ⟨hhT, by omega⟩
      have hkcut : k * n ≤ N := by omega
      simp only [linearizedUpwardOffset, reciprocalUpwardOffset, if_pos hp, if_pos hncut,
        if_pos hkcut, ramanujanLagCoefficient_sub_eq_reflected hm hhT.le]
    · have hp : ¬ k * n + h ≤ N := by omega
      have hncut : ¬ (h < k * n ∧ k * n - h ≤ N) := by omega
      have hkcut : ¬ k * n ≤ N := by omega
      simp only [linearizedUpwardOffset, reciprocalUpwardOffset, if_neg hp, if_neg hncut,
        if_neg hkcut, add_zero]
  · have hz := reciprocal_shell_zero_of_small_product hφ hsupp hc hN hT (by omega : k * n ≤ h)
    simp only [linearizedUpwardOffset, reciprocalUpwardOffset, hz, mul_zero]

/-- Both cutoff orientations have bounded absolute conductor mass. -/
theorem abs_linearizedUpwardOffset_sub_reciprocal_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (c : ℝ) (N m n k h : ℕ) :
    |linearizedUpwardOffset φ c N m n k h - reciprocalUpwardOffset φ c N m n k h| ≤
      4 * m.totient * (∫ u, φ u ^ 2) := by
  have hA : (0 : ℝ) ≤ m.totient := Nat.cast_nonneg _
  have hb (p : Prop) [Decidable p] (j : ℕ) :
      |if p then ramanujanLagCoefficient m j else 0| ≤ (m.totient : ℝ) := by
    split_ifs
    · exact BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j
    · simpa only [abs_zero] using hA
  have hp := hb (k * n + h ≤ N) (k * n + h)
  have hm := hb (h < k * n ∧ k * n - h ≤ N) (k * n - h)
  have hi : |if k * n ≤ N then ramanujanLagCoefficient m (k * n + h) +
      ramanujanLagCoefficient m (k * n + reflectedAffineShift m h) else 0| ≤ 2 * (m.totient : ℝ) := by
    split_ifs
    · exact (abs_add_le _ _).trans ((add_le_add
        (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m (k * n + h))
        (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m
          (k * n + reflectedAffineShift m h))).trans_eq (by ring))
    · simp only [abs_zero]
      positivity
  have hcoef : |((if k * n + h ≤ N then ramanujanLagCoefficient m (k * n + h) else 0) +
      (if h < k * n ∧ k * n - h ≤ N then ramanujanLagCoefficient m (k * n - h) else 0)) -
      (if k * n ≤ N then ramanujanLagCoefficient m (k * n + h) +
        ramanujanLagCoefficient m (k * n + reflectedAffineShift m h) else 0)| ≤ 4 * (m.totient : ℝ) := by
    exact (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hp hm)) hi).trans_eq (by ring))
  unfold linearizedUpwardOffset reciprocalUpwardOffset
  rw [← sub_mul, abs_mul]
  exact mul_le_mul hcoef
    (abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) _) (abs_nonneg _) (by positivity)

/-- Moving the two actual offset cutoffs to `kn≤N` costs only a vanishing
prime-index boundary mass at the complementary horizon. -/
theorem abs_linearizedUpwardCoefficient_sub_reciprocal_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {B N m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hN : c ≤ N) :
    |linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n| ≤
      4 * B * m.totient * primeIndexBoundaryMass B (N / n) := by
  let S := Icc (N / n - B) (N / n + B + 1)
  let L : ℝ := (B : ℝ) * (4 * m.totient * (∫ u, φ u ^ 2))
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hpoint (k : ℕ) (hk : k ∈ Icc 1 (N + B)) :
      |∑ h ∈ Icc 1 B, (linearizedUpwardOffset φ c N m n k h -
        reciprocalUpwardOffset φ c N m n k h)| ≤ if k ∈ S then L else 0 := by
    by_cases hkS : k ∈ S
    · rw [if_pos hkS]
      have h := (abs_sum_le_sum_abs _ (Icc 1 B)).trans
        (sum_le_sum fun h _ => abs_linearizedUpwardOffset_sub_reciprocal_le hφ hsupp c N m n k h)
      simpa only [L, sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] using h
    · rw [if_neg hkS]
      have hz : (∑ h ∈ Icc 1 B, (linearizedUpwardOffset φ c N m n k h -
          reciprocalUpwardOffset φ c N m n k h)) = 0 := by
        apply sum_eq_zero
        intro h hh
        rw [linearizedUpwardOffset_eq_reciprocal_of_not_boundary hφ hsupp hc hm hn
          (mem_Icc.mp hk).1 hh hN hkS, sub_self]
      rw [hz, abs_zero]
  have hsub : (Icc 1 (N + B)).filter (fun k => k ∈ S) ⊆ S :=
    fun k hk => (mem_filter.mp hk).2
  have hmass : (∑ k ∈ (Icc 1 (N + B)).filter (fun k => k ∈ S),
      (ArithmeticFunction.vonMangoldt k : ℝ) / k) ≤ primeIndexBoundaryMass B (N / n) :=
    sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
  unfold linearizedUpwardCoefficient reciprocalUpwardCoefficient
  rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hM)]
  calc
    _ ≤ 1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
        |(ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h -
          (ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, reciprocalUpwardOffset φ c N m n k h| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ 1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
        if k ∈ S then (ArithmeticFunction.vonMangoldt k : ℝ) / k * L else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro k hk
      rw [← mul_sub, ← sum_sub_distrib, abs_mul,
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))]
      have hw : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt k : ℝ) / k :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
      have ht := mul_le_mul_of_nonneg_left (hpoint k hk) hw
      simpa only [mul_ite, mul_zero] using ht
    _ = 1 / (∫ u, φ u ^ 2) *
        ((∑ k ∈ (Icc 1 (N + B)).filter (fun k => k ∈ S),
          (ArithmeticFunction.vonMangoldt k : ℝ) / k) * L) := by simp only [sum_filter, sum_mul, ite_mul, zero_mul]
    _ ≤ 1 / (∫ u, φ u ^ 2) * (primeIndexBoundaryMass B (N / n) * L) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmass hL) (by positivity)
    _ = _ := by
      dsimp only [L]
      field_simp

private theorem tendsto_mertensSum_add_div_self (B : ℕ) :
    Tendsto (fun N : ℕ => mertensSum (N + B) / N) atTop (𝓝 0) := by
  have hadd : Tendsto (fun N : ℕ => N + B) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have herr := (tendsto_mertensSum_sub_log.comp hadd).div_atTop
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hlogReal : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlog := hlogReal.comp (tendsto_natCast_atTop_atTop.comp hadd)
  have hratio : Tendsto (fun N : ℕ => ((N + B : ℕ) : ℝ) / N) atTop (𝓝 1) := by
    have hz : Tendsto (fun N : ℕ => (B : ℝ) / N) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (B : ℝ)
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hz
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [Nat.cast_add, add_div, div_self hN0]
  have hlim := herr.add (hlog.mul hratio)
  simp only [zero_mul, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNB0 : ((N + B : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show N + B ≠ 0 by omega)
  dsimp only [Function.comp_apply]
  field_simp
  ring

private theorem product_cutoff_filter_eq_real_horizon (N B n : ℕ) (hn : 1 ≤ n) :
    (Icc 1 (N + B)).filter (fun k => k * n ≤ N) = Icc 1 ⌊(N : ℝ) / n⌋₊ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hX0 : (0 : ℝ) ≤ (N : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn0.le
  apply Finset.ext
  intro k
  constructor
  · intro hk
    obtain ⟨hkN, hprod⟩ := mem_filter.mp hk
    apply mem_Icc.mpr
    refine ⟨(mem_Icc.mp hkN).1, Nat.le_floor ?_⟩
    rw [le_div_iff₀ hn0]
    exact_mod_cast hprod
  · intro hk
    obtain ⟨hk1, hkX⟩ := mem_Icc.mp hk
    have hkR : (k : ℝ) ≤ (N : ℝ) / n :=
      (by exact_mod_cast hkX : (k : ℝ) ≤ (⌊(N : ℝ) / n⌋₊ : ℝ)).trans (Nat.floor_le hX0)
    have hprod : k * n ≤ N := by
      rw [le_div_iff₀ hn0] at hkR
      exact_mod_cast hkR
    have hkn : k ≤ k * n := by simpa only [mul_one] using Nat.mul_le_mul_left k hn
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hk1, by omega⟩, hprod⟩

/-- The reciprocal finite source is exactly the pair of positive and reflected affine readings. -/
theorem reciprocalUpwardCoefficient_eq_affine_sums (φ : ℝ → ℝ) (c : ℝ) (B N m n : ℕ)
    (hn : 1 ≤ n) :
    reciprocalUpwardCoefficient φ c B N m n = 1 / (∫ u, φ u ^ 2) *
      ((∑ h ∈ Icc 1 B, affineRamanujanPrimeShell m n h φ c h ((N : ℝ) / n)) +
        ∑ h ∈ Icc 1 B, affineRamanujanPrimeShell m n (reflectedAffineShift m h) φ c h ((N : ℝ) / n)) := by
  have harg (k h : ℕ) : (N : ℝ) / c * ((h : ℝ) / (k * n : ℕ)) =
      (h : ℝ) * ((N : ℝ) / n) / (c * k) := by
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  have hcut : reciprocalUpwardCoefficient φ c B N m n =
      1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊,
        (ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B,
          (ramanujanLagCoefficient m (k * n + h) +
            ramanujanLagCoefficient m (k * n + reflectedAffineShift m h)) *
          shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / (k * n : ℕ))) := by
    unfold reciprocalUpwardCoefficient reciprocalUpwardOffset
    rw [← product_cutoff_filter_eq_real_horizon N B n hn, sum_filter]
    congr 1
    apply sum_congr rfl
    intro k _
    by_cases hk : k * n ≤ N
    · simp only [if_pos hk]
    · simp only [if_neg hk, zero_mul, sum_const_zero, mul_zero]
  rw [hcut]
  calc
    _ = 1 / (∫ u, φ u ^ 2) * ∑ h ∈ Icc 1 B, ∑ k ∈ Icc 1 ⌊(N : ℝ) / n⌋₊,
        ((ArithmeticFunction.vonMangoldt k : ℝ) / k * ramanujanLagCoefficient m (k * n + h) *
            shellAutocorr φ ((h : ℝ) * ((N : ℝ) / n) / (c * k)) +
          (ArithmeticFunction.vonMangoldt k : ℝ) / k *
            ramanujanLagCoefficient m (k * n + reflectedAffineShift m h) *
            shellAutocorr φ ((h : ℝ) * ((N : ℝ) / n) / (c * k))) := by
      congr 1
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun h _ => sum_congr rfl fun k _ => by rw [harg]; ring
    _ = _ := by simp only [sum_add_distrib, affineRamanujanPrimeShell]

private theorem affineRamanujanPrimeShell_eq_zero_of_large_offset {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) (q n b h : ℕ) {X : ℝ} (hX : 0 ≤ X) (hh : c ≤ h) :
    affineRamanujanPrimeShell q n b φ c h X = 0 := by
  unfold affineRamanujanPrimeShell
  apply sum_eq_zero
  intro k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
  have hkX : (k : ℝ) ≤ X :=
    (by exact_mod_cast (mem_Icc.mp hk).2 : (k : ℝ) ≤ (⌊X⌋₊ : ℝ)).trans (Nat.floor_le hX)
  have hprod : c * k ≤ (h : ℝ) * X :=
    mul_le_mul hh hkX hk0.le (Nat.cast_nonneg h)
  have harg : 1 ≤ |(h : ℝ) * X / (c * k)| :=
    ((one_le_div (mul_pos hc hk0)).mpr hprod).trans (le_abs_self _)
  rw [shellAutocorr_eq_zero_of_one_le_abs hφ hsupp harg, mul_zero]

/-- Shells beyond the autocorrelation support contribute exactly zero. -/
theorem reciprocalUpwardCoefficient_eq_shifted_corrections {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {B : ℕ} (hB : ⌈c⌉₊ ≤ B) (N m n : ℕ) (hn : 1 ≤ n) :
    reciprocalUpwardCoefficient φ c B N m n =
      (affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) +
        affinePrimeShellCorrectionOfShift m n (reflectedAffineShift m) φ c ((N : ℝ) / n)) / 2 := by
  have hsub : Ico 1 ⌈c⌉₊ ⊆ Icc 1 B := by
    intro h hh
    exact mem_Icc.mpr ⟨(mem_Ico.mp hh).1, (mem_Ico.mp hh).2.le.trans hB⟩
  have hext (shift : ℕ → ℕ) :
      (∑ h ∈ Icc 1 B, affineRamanujanPrimeShell m n (shift h) φ c h ((N : ℝ) / n)) =
        ∑ h ∈ Ico 1 ⌈c⌉₊, affineRamanujanPrimeShell m n (shift h) φ c h ((N : ℝ) / n) := by
    symm
    apply sum_subset hsub
    intro h hh hnot
    have hhceil : ⌈c⌉₊ ≤ h := by
      by_contra hlow
      exact hnot (mem_Ico.mpr ⟨(mem_Icc.mp hh).1, by omega⟩)
    have hch : c ≤ (h : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hhceil)
    exact affineRamanujanPrimeShell_eq_zero_of_large_offset hφ hsupp hc m n (shift h) h
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hch
  rw [reciprocalUpwardCoefficient_eq_affine_sums φ c B N m n hn]
  have hid := hext id
  simp only [id_eq] at hid
  rw [hid, hext (reflectedAffineShift m)]
  unfold affinePrimeShellCorrectionOfShift
  simp only [id_eq]
  ring

/-- The geometric source error has vanishing squared row norm at logarithmic scale. -/
theorem tendsto_logarithmicUpwardCoefficient_error_sq_div_log {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (B m : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N,
      ((logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) /
        Real.sqrt n) ^ 2) / Real.log N) atTop (𝓝 0) := by
  obtain ⟨D, hD, N₀, hbound⟩ := exists_logarithmicUpwardCoefficient_error_bound hφ hsupp hM hc B m
  let a : ℕ → ℝ := fun N => D * mertensSum (N + B) / N
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, mul_div_assoc, mul_zero] using (tendsto_mertensSum_add_div_self B).const_mul D
  have hlim := (ha.pow 2).mul GaloisForLFunctions.tendsto_harmonic_div_log
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hlim
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Real.log_natCast_nonneg N)) _ hlim
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hsum : (∑ n ∈ Icc 1 N,
      ((logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) /
        Real.sqrt n) ^ 2) ≤ a N ^ 2 * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, a N ^ 2 / (n : ℝ) := by
        apply sum_le_sum
        intro n hn
        have hb := hbound N hN n (mem_Icc.mp hn).1
        have hsq := mul_self_le_mul_self (abs_nonneg _) hb
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        simpa only [← sq, sq_abs] using hsq
      _ = a N ^ 2 * (harmonic N : ℝ) := by
        rw [← RHTower.Sieve.sum_Icc_one_div_eq_harmonic, mul_sum]
        exact sum_congr rfl fun n _ => by ring
  exact (div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)).trans_eq (by ring)

/-- The actual cutoff discrepancy vanishes in squared harmonic norm. -/
theorem tendsto_linearizedUpwardCoefficient_boundary_sq_div_log {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (B : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N,
      ((linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) /
        Real.sqrt n) ^ 2) / Real.log N) atTop (𝓝 0) := by
  let f : ℕ → ℝ := fun Y => 4 * B * m.totient * primeIndexBoundaryMass B Y
  let R : ℕ → ℕ → ℝ := fun N n => if c ≤ (N : ℝ) then
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
    else 0
  have hf : Tendsto f atTop (𝓝 0) := by
    simpa only [f, mul_zero] using (tendsto_primeIndexBoundaryMass B).const_mul (4 * B * m.totient : ℝ)
  have hR : ∀ N n, n ∈ Icc 1 N → |R N n| ≤ f (N / n) / Real.sqrt n := by
    intro N n hn
    by_cases hNc : c ≤ (N : ℝ)
    · dsimp only [R]
      rw [if_pos hNc, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
      exact div_le_div_of_nonneg_right
        (abs_linearizedUpwardCoefficient_sub_reciprocal_le hφ hsupp hM hc hm (mem_Icc.mp hn).1 hNc)
        (Real.sqrt_nonneg n)
    · dsimp only [R]
      rw [if_neg hNc, abs_zero]
      have hmass : 0 ≤ primeIndexBoundaryMass B (N / n) :=
        sum_nonneg fun k _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
      exact div_nonneg (by dsimp only [f]; positivity) (Real.sqrt_nonneg n)
  have hlim := HTGeometry.tendsto_harmonicQuotient_square_error hf R hR
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop ⌈c⌉₊] with N hN
  have hNc : c ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  simp only [R, if_pos hNc]

/-- The symmetric reciprocal source has the exact shell correction in harmonic norm. -/
theorem tendsto_reciprocalUpwardCoefficient_shell_sq_div_log {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {B : ℕ} (hB : ⌈c⌉₊ ≤ B)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N,
      ((reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) /
      Real.log N) atTop (𝓝 0) := by
  have hid : shellCorrectionOfShift φ c m id = shellCorrection φ c m := rfl
  have hrow (N n : ℕ) (hn : 1 ≤ n) :
      (reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n =
      (shiftedReciprocalUpwardRowError φ c id N m n +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n) / 2 := by
    rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc hB N m n hn]
    dsimp only [shiftedReciprocalUpwardRowError]
    rw [hid, shellCorrectionOfShift_reflected hm]
    ring
  have hp := tendsto_shiftedReciprocalUpwardRowError_sq_div_log hm hφ hsupp hM hc id
  have hm' := tendsto_shiftedReciprocalUpwardRowError_sq_div_log hm hφ hsupp hM hc (reflectedAffineShift m)
  have hlim := (hp.add hm').div_const 2
  simp only [add_zero, zero_div] at hlim
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Real.log_natCast_nonneg N)) _ hlim
  apply Eventually.of_forall
  intro N
  have hsum : (∑ n ∈ Icc 1 N,
      ((reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) ≤
      ∑ n ∈ Icc 1 N, (shiftedReciprocalUpwardRowError φ c id N m n ^ 2 +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n ^ 2) / 2 := by
    apply sum_le_sum
    intro n hn
    rw [hrow N n (mem_Icc.mp hn).1]
    nlinarith only [sq_nonneg (shiftedReciprocalUpwardRowError φ c id N m n -
      shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n)]
  refine (div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)).trans_eq ?_
  rw [← sum_div, sum_add_distrib]
  ring

/-- Residual of the literal infinite upward action on an unnormalized conductor row. -/
def actualUpwardRowError (φ : ℝ → ℝ) (c : ℝ) (N m n : ℕ) : ℝ :=
  upwardPrimeRow (atomDilate φ (c / N)) N
      (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
        (∫ u, atomDilate φ (c / N) u ^ 2) -
    shellCorrection φ c m * ramanujanLagCoefficient m n / Real.sqrt n

/-- The literal upward prime-power source has the completed shell correction in squared norm. -/
theorem tendsto_actualUpwardRowError_sq_div_log {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) /
      Real.log N) atTop (𝓝 0) := by
  let B := exteriorPrimeStrip c
  have hB : ⌈c⌉₊ ≤ B := by
    apply Nat.ceil_le.mpr
    have he : c ≤ c * Real.exp c := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr hc.le) hc.le
    exact he.trans (Nat.le_ceil _)
  let a : ℕ → ℕ → ℝ := fun N n =>
    (logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n
  let b : ℕ → ℕ → ℝ := fun N n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let d : ℕ → ℕ → ℝ := fun N n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  have hrow (N n : ℕ) (hn : n ∈ Icc 1 N) :
      actualUpwardRowError φ c N m n = a N n + b N n + d N n := by
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < n)).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt n := by
      apply (eq_div_iff hs).mpr
      simpa only [mul_comm] using sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient hsupp hc hn m
    rw [actualUpwardRowError, hu]
    dsimp only [a, b, d]
    ring
  have ha : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a N n ^ 2) / Real.log N) atTop (𝓝 0) :=
    tendsto_logarithmicUpwardCoefficient_error_sq_div_log hφ hsupp hM hc B m
  have hb : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, b N n ^ 2) / Real.log N) atTop (𝓝 0) :=
    tendsto_linearizedUpwardCoefficient_boundary_sq_div_log hφ hsupp hM hc B hm
  have hd : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, d N n ^ 2) / Real.log N) atTop (𝓝 0) :=
    tendsto_reciprocalUpwardCoefficient_shell_sq_div_log hφ hsupp hM hc hB hm
  have hlim := ((ha.add hb).add hd).const_mul 3
  simp only [zero_add, mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Real.log_natCast_nonneg N)) _ hlim
  apply Eventually.of_forall
  intro N
  have hsum : (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) ≤
      ∑ n ∈ Icc 1 N, 3 * (a N n ^ 2 + b N n ^ 2 + d N n ^ 2) := by
    apply sum_le_sum
    intro n hn
    rw [hrow N n hn]
    nlinarith only [sq_nonneg (a N n - b N n), sq_nonneg (a N n - d N n),
      sq_nonneg (b N n - d N n)]
  refine (div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)).trans_eq ?_
  rw [← mul_sum, sum_add_distrib, sum_add_distrib]
  ring

/-- The actual upward source residual on the logarithmically normalized conductor vector. -/
def normalizedUpwardPrimeResidual (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => actualUpwardRowError φ c N m n / Real.sqrt (Real.log N))

theorem normalizedUpwardPrimeResidual_norm_sq (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    ‖normalizedUpwardPrimeResidual φ c N m‖ ^ 2 =
      (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) / Real.log N := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ n : PrimeHorizonIndex N,
    (actualUpwardRowError φ c N m n / Real.sqrt (Real.log N)) ^ 2) = _
  simp only [div_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← sum_div]
  congr 1
  exact sum_coe_sort (Icc 1 N) (fun n => actualUpwardRowError φ c N m n ^ 2)

/-- Every fixed conductor has its signed shell correction under the literal upward action. -/
theorem tendsto_normalizedUpwardPrimeResidual_norm {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ => ‖normalizedUpwardPrimeResidual φ c N m‖) atTop (𝓝 0) := by
  have h := (tendsto_actualUpwardRowError_sq_div_log hφ hsupp hM hc hm).sqrt
  simpa only [← normalizedUpwardPrimeResidual_norm_sq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using h

/-- The explicit tilted spline realizes every completed shell correction in source norm. -/
theorem tendsto_tiltedUnitSpline_normalizedUpwardPrimeResidual_norm {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ => ‖normalizedUpwardPrimeResidual tiltedUnitSpline c N m‖) atTop (𝓝 0) :=
  tendsto_normalizedUpwardPrimeResidual_norm contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
    integral_tiltedUnitSpline_sq_pos hc hm

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_normalizedUpwardPrimeResidual_norm

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_tiltedUnitSpline_normalizedUpwardPrimeResidual_norm

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.reciprocalUpwardCoefficient_eq_shifted_corrections
