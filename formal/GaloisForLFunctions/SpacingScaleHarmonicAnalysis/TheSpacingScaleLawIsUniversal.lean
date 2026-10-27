import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheStabilityLawAtTheSpacingScale

/-!
# The spacing-scale law is universal

The stability law at the spacing scale uses the prime place only through the size of its
coefficients. Below the spacing every prime pairing of an atomic test is an exact Hecke pairing,
`∫ f_x(t) f_x(t ∓ log k) dt = ‖g‖² Σ_{m = nk} x_m x_n` (resp. `n = mk`), so a twisted prime sum with
coefficients `ω(k) Λ(k)`, `|ω(k)| ≤ 1`, is dominated by `‖g‖² P_N(|x|)`
(`twistedPrimeSum_atomicTest_le`). The tilted rows bound `P_N(|x|)` with the same squares as
`P_N(x)`.

* **Universal spacing-scale law** (`twistedMarkov_atomicTest_ge_spacing_of_abs_le`,
  `twistedMarkov_atomicTest_nonneg_spacing_of_abs_le`): for every real twist `|ω| ≤ 1` —
  multiplicative or not, signed or not — and every real `C²` bump,
  `archForm f_x − twistedPrimeSum ω f_x ≥ (2θ′(0) + log(1/w) − log N − C)‖f_x‖²` at `w ≤ c₁ δ_N`,
  and it is nonnegative at `w ≤ c₀ δ_N`.

So the law is blind not only to the gauge but to every arithmetic property of the coefficients
beyond `|a(k)| ≤ Λ(k)`: no selectivity of any kind lives in the separated regime of the Markov form.
-/

noncomputable section

open MeasureTheory Finset RHTower
open scoped Real

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ} {ω : ArithmeticFunction ℝ}

/-- The two Hecke pairings of an atomic test below the spacing, at order `k`. -/
theorem pairings_atomicTest_below_spacing (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hw : w < atomSpacing N) (x : ℕ → ℝ)
    {k : ℕ} (hk : 1 ≤ k) :
    (∫ t, atomicTest N x g t * atomicTest N x g (t - Real.log k)) +
        ∫ t, atomicTest N x g t * atomicTest N x g (t + Real.log k) =
      (∫ u, g u ^ 2) * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        ((if m = n * k then x m * x n else 0) + (if n = m * k then x m * x n else 0)) := by
  rw [integral_atomicTest_mul_shift_neg hg hgc hgsupp hw x hk,
    integral_atomicTest_mul_shift_pos hg hgc hgsupp hw x hk, ← add_mul, mul_comm,
    ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun m _ => by rw [← sum_add_distrib]

/-- `|Σ [m = nk] x_m x_n + Σ [n = mk] x_m x_n| ≤` the same with `|x|`. -/
theorem abs_heckePairs_le (N k : ℕ) (x : ℕ → ℝ) :
    |∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        ((if m = n * k then x m * x n else 0) + (if n = m * k then x m * x n else 0))| ≤
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        ((if m = n * k then |x m| * |x n| else 0) + (if n = m * k then |x m| * |x n| else 0)) := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;>
  · split_ifs
    · rw [abs_mul]
    · simp

/-- **Twisted prime sums are dominated below the spacing**: for every real twist `|ω| ≤ 1`,
`twistedPrimeSum ω f_x ≤ ‖g‖² P_N(|x|)`. -/
theorem twistedPrimeSum_atomicTest_le (hω : ∀ k, |ω k| ≤ 1) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ}
    (hw : w < atomSpacing N) (x : ℕ → ℝ) :
    twistedPrimeSum ω (atomicTest N x g) ≤
      (∫ u, g u ^ 2) * atomicWeilForm N (fun n => |x n|) := by
  set G2 := ∫ u, g u ^ 2
  have hG2 : 0 ≤ G2 := integral_nonneg fun u => sq_nonneg _
  set A : ℕ → (ℕ → ℝ) → ℝ := fun k y => ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
    ((if m = n * k then y m * y n else 0) + (if n = m * k then y m * y n else 0))
  -- orders `k > N` pair no atoms
  have hA0 : ∀ y : ℕ → ℝ, ∀ k ∉ range (N + 1), A k y = 0 := by
    intro y k hk
    have hkN : N < k := by simpa using hk
    refine sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_
    have hm1 := mem_Icc.mp hm
    have hn1 := mem_Icc.mp hn
    rw [if_neg (by intro h; nlinarith), if_neg (by intro h; nlinarith), add_zero]
  have hterm : ∀ y : ℕ → ℝ, ∀ k : ℕ, vonMangoldtAtom k *
      ((∫ t, atomicTest N y g t * atomicTest N y g (t - Real.log k)) +
        ∫ t, atomicTest N y g t * atomicTest N y g (t + Real.log k)) =
      vonMangoldtAtom k * (G2 * A k y) := by
    intro y k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [vonMangoldtAtom]
    rw [pairings_atomicTest_below_spacing hg hgc hgsupp hw y hk]
  have hΛ : ∀ k, 0 ≤ vonMangoldtAtom k := fun k => by
    unfold vonMangoldtAtom
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  have htw : twistedPrimeSum ω (atomicTest N x g) =
      ∑ k ∈ range (N + 1), ω k * vonMangoldtAtom k * (G2 * A k x) := by
    rw [twistedPrimeSum]
    rw [show (fun k : ℕ => ω k * vonMangoldtAtom k *
        ((∫ t, atomicTest N x g t * atomicTest N x g (t - Real.log k)) +
          ∫ t, atomicTest N x g t * atomicTest N x g (t + Real.log k))) =
        fun k => ω k * vonMangoldtAtom k * (G2 * A k x) by
      funext k; rw [mul_assoc, hterm x k, ← mul_assoc]]
    exact tsum_eq_sum fun k hk => by rw [hA0 x k hk, mul_zero, mul_zero]
  have hab : primeSum (atomicTest N (fun n => |x n|) g) =
      ∑ k ∈ range (N + 1), vonMangoldtAtom k * (G2 * A k fun n => |x n|) := by
    rw [primeSum]
    rw [show (fun k : ℕ => vonMangoldtAtom k *
        ((∫ t, atomicTest N (fun n => |x n|) g t *
            atomicTest N (fun n => |x n|) g (t - Real.log k)) +
          ∫ t, atomicTest N (fun n => |x n|) g t *
            atomicTest N (fun n => |x n|) g (t + Real.log k))) =
        fun k => vonMangoldtAtom k * (G2 * A k fun n => |x n|) by
      funext k; rw [hterm]]
    exact tsum_eq_sum fun k hk => by rw [hA0 _ k hk, mul_zero, mul_zero]
  rw [htw, ← primeSum_atomicTest hg hgc hgsupp hw, hab]
  refine sum_le_sum fun k _ => ?_
  have hAbs := abs_heckePairs_le N k x
  calc ω k * vonMangoldtAtom k * (G2 * A k x)
      ≤ |ω k * vonMangoldtAtom k * (G2 * A k x)| := le_abs_self _
    _ = |ω k| * vonMangoldtAtom k * (G2 * |A k x|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hΛ k), abs_of_nonneg hG2]
    _ ≤ 1 * vonMangoldtAtom k * (G2 * A k fun n => |x n|) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hω k) (hΛ k))
          (mul_le_mul_of_nonneg_left hAbs hG2) (mul_nonneg hG2 (abs_nonneg _))
          (by rw [one_mul]; exact hΛ k)
    _ = vonMangoldtAtom k * (G2 * A k fun n => |x n|) := by ring

/-- **The universal spacing-scale law, quantitative form**: for every real twist `|ω| ≤ 1` and
every real `C²` bump, `archForm f_x − twistedPrimeSum ω f_x ≥ (2θ′(0) + log(1/w) − log N − C)‖f_x‖²`
at `0 < w ≤ c₁ δ_N`. -/
theorem twistedMarkov_atomicTest_ge_spacing_of_abs_le (hω : ∀ k, |ω k| ≤ 1)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w) (hw : w ≤ spacingRatio * atomSpacing N) (x : ℕ → ℝ) :
    (2 * gammaHardyPhaseRate 0 + Real.log (1 / w) - Real.log N - spacingConstant) *
        ∫ u, atomicTest N x g u ^ 2 ≤
      archForm (atomicTest N x g) - twistedPrimeSum ω (atomicTest N x g) := by
  have hw' : w < atomSpacing N := by
    nlinarith [spacingRatio_lt_half, spacingRatio_pos, atomSpacing_pos hN]
  have h := levy_sub_atomicWeilForm_ge hg hgc hgsupp hN hw0 hw x (fun n => |x n|)
    fun m _ => sq_abs (x m)
  have htw := twistedPrimeSum_atomicTest_le hω hg hgc hgsupp hw' x
  rw [archForm_eq_levyEnergy (contDiff_atomicTest hg N x) (hasCompactSupport_atomicTest hgsupp N x)]
  linarith

/-- **The universal spacing-scale law**: for every real twist `|ω| ≤ 1` and every real `C²` bump of
width at most `c₀ δ_N`, `archForm f_x − twistedPrimeSum ω f_x ≥ 0`. -/
theorem twistedMarkov_atomicTest_nonneg_spacing_of_abs_le (hω : ∀ k, |ω k| ≤ 1)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w) (hw : w ≤ spacingWidthRatio * atomSpacing N)
    (x : ℕ → ℝ) :
    0 ≤ archForm (atomicTest N x g) - twistedPrimeSum ω (atomicTest N x g) := by
  have hw' : w ≤ spacingRatio * atomSpacing N :=
    hw.trans (mul_le_mul_of_nonneg_right spacingWidthRatio_le (atomSpacing_pos hN).le)
  have h := twistedMarkov_atomicTest_ge_spacing_of_abs_le hω hg hgc hgsupp hN hw0 hw' x
  have hint : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  exact le_trans (mul_nonneg (spacingGain_nonneg hN hw0 hw) hint) h

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
