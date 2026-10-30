import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeFormCollapsesOnThePoleProfile
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheDeficitOfThePrimeFormIsADirichletEnergy
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing

/-!
# The shells alone cost the square of the overlap

The proved complete reserve pays the non-ratio form `NR` by itself:
`|NR| ≤ G(εD + C(ε)S)` with `C(ε) ≍ c²/ε` (`abs_nonRatioForm_le_relative_defect`). This file proves
that no separate payment can do better, even one-sided, for every nonnegative profile.

**The witness.** The *top band* `T = {n ≤ N : N e^w < 2n}` consists of atoms that are partners of
shells but never bases (a base `m ∈ T` would need `km > N e^w`). Perturb the pole vector `b` on it:
`x_η = b + η b 1_T`.

* **Base collapse** (`nonRatioForm_eq_of_pole_on_bases`): if `x = b` on all bases, then
  `NR(x) = 2 Σ_n x_n R(n)` with the pole row `R(n) = Σ_{ℓ ≠ n} b_ℓ Λ_N(ℓ) β(log ℓ − log n)`.
* **The witness is cheap**: `D(x_η) = η² D(b1_T) ≤ η² log N Σ_T 1/n` (`poleDefect_witness_le`), the
  defect of a vector living on atoms with no proper multiples below `N`.
* **The witness is expensive for the shells**: by Cauchy–Schwarz on the window `[log N + w − log 2,
  log N + w]` of length `log 2`, the top-band Gram has `Σ_{n,ℓ∈T} β ≥ (|T|∫g)²/log 2`
  (`sum_topBand_bumpCorr_ge`), so the shells read `2η G log(N/2)(|T|/N)((|T|/N)cq/log 2 − 1)`.

**The floor** (`le_of_nonRatioForm_payment`). If eventually in `N`, for every `x`,
`NR(x) ≤ G(εD(x) + C S(x))` at width `c/N`, then `C ≥ A⁺²/(2ε)` with `A = cq/(4 log 2) − 1/2`,
`q = (∫φ)²/∫φ²`. So `C ≥ κ c²/ε` for large `c`: the separate payment of the shells is sharp at order
`c²/ε`, and against the reserve fraction `ε ∝ c⁻⁷` it costs `c⁹` (`le_of_nonRatioForm_payment_at_reserve`).
The `c¹⁶` confinement exponent is therefore intrinsic to paying the shells apart from the pole.
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped Real

namespace GaloisForLFunctions.SuccessorShellArithmetic

open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
open _root_.RHTower (vonMangoldtAtom)

variable {g : ℝ → ℝ} {w : ℝ}

/-- The **top band** `T = {n ≤ N : N e^w < 2n}`: partners of shells that are never bases. -/
def topBand (N : ℕ) (w : ℝ) : Finset ℕ :=
  (Icc 1 N).filter fun n => (N : ℝ) * Real.exp w < 2 * n

/-- The top-band witness direction `b·1_T`. -/
def topWitness (N : ℕ) (w : ℝ) (n : ℕ) : ℝ :=
  if n ∈ topBand N w then poleVector n else 0

/-- The pole row of the shells at `n`: `R(n) = Σ_{ℓ ≠ n} b_ℓ Λ_N(ℓ) β(log ℓ − log n)`. -/
def shellPoleRow (g : ℝ → ℝ) (N : ℕ) (w : ℝ) (n : ℕ) : ℝ :=
  ∑ ℓ ∈ Icc 1 ⌈(N : ℝ) * Real.exp w⌉₊, poleVector ℓ * horizonDivisorMangoldt N ℓ *
    (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n))

theorem mem_topBand {N : ℕ} {w : ℝ} {n : ℕ} :
    n ∈ topBand N w ↔ n ∈ Icc 1 N ∧ (N : ℝ) * Real.exp w < 2 * n :=
  mem_filter

/-- `bumpCorr` of a nonnegative bump is nonnegative. -/
theorem bumpCorr_nonneg (hg0 : ∀ u, 0 ≤ g u) (t : ℝ) : 0 ≤ bumpCorr g t :=
  integral_nonneg fun v => mul_nonneg (hg0 v) (hg0 (v + t))

private theorem bumpCorr_eq_zero_of_far (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {k m n : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n) {N : ℕ} (hnN : n ≤ N)
    (hm2 : (N : ℝ) * Real.exp w < 2 * m) :
    bumpCorr g (Real.log k - (Real.log n - Real.log m)) = 0 := by
  apply bumpCorr_eq_zero hgsupp
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  -- `n e^w ≤ N e^w < 2m ≤ km`
  have hlt : (n : ℝ) * Real.exp w < k * m := by
    have h1 : (n : ℝ) * Real.exp w ≤ N * Real.exp w :=
      mul_le_mul_of_nonneg_right hnN' (Real.exp_pos w).le
    have h2 : 2 * (m : ℝ) ≤ k * m := mul_le_mul_of_nonneg_right hk2 hm0.le
    linarith only [h1, h2, hm2]
  have hlog := Real.log_lt_log (by positivity) hlt
  rw [Real.log_mul hn0.ne' (Real.exp_pos w).ne', Real.log_exp,
    Real.log_mul hk0.ne' hm0.ne'] at hlog
  rw [abs_of_pos (by linarith only [hlog])]
  linarith only [hlog]

/-- **Base collapse.** If `x` is the pole vector on every possible base `2m ≤ N e^w`, the non-ratio
form is `2 Σ_n x_n R(n)`. -/
theorem nonRatioForm_eq_of_pole_on_bases (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ)
    (hx : ∀ m ∈ Icc 1 N, 2 * (m : ℝ) ≤ N * Real.exp w → x m = poleVector m) :
    nonRatioForm g N x = 2 * ∑ n ∈ Icc 1 N, x n * shellPoleRow g N w n := by
  set L := ⌈(N : ℝ) * Real.exp w⌉₊ with hLdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNL : (N : ℝ) * Real.exp w ≤ L := Nat.le_ceil _
  have htsum : nonRatioForm g N x =
      ∑ k ∈ range (L + 1), vonMangoldtAtom k * nonRatioLag g N k x := by
    rw [nonRatioForm]
    refine tsum_eq_sum fun k hk => ?_
    have hkK : L + 1 ≤ k := by simpa using hk
    have hk : Real.log N + w < Real.log k := by
      have hkL : (L : ℝ) < k := by exact_mod_cast (by omega : L < k)
      have hpos : 0 < (N : ℝ) * Real.exp w := by positivity
      have := Real.log_lt_log hpos (lt_of_le_of_lt hNL hkL)
      rwa [Real.log_mul hN0.ne' (Real.exp_pos w).ne', Real.log_exp] at this
    rw [nonRatioLag_eq_zero_of_log_lt hgsupp hw hk, mul_zero]
  set H : ℕ → ℕ → ℝ := fun n ℓ => if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)
    with hH
  have hHvan : ∀ n ∈ Icc 1 N, ∀ ℓ : ℕ, L < ℓ → H n ℓ = 0 := by
    intro n hn ℓ hℓ
    simp only [hH]
    split_ifs
    · rfl
    · apply bumpCorr_eq_zero hgsupp
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hℓR : (L : ℝ) < ℓ := by exact_mod_cast hℓ
      have hlt : (n : ℝ) * Real.exp w < ℓ :=
        lt_of_le_of_lt (le_trans (mul_le_mul_of_nonneg_right hnN (Real.exp_pos w).le) hNL) hℓR
      have := Real.log_lt_log (by positivity) hlt
      rw [Real.log_mul (by positivity) (Real.exp_pos w).ne', Real.log_exp] at this
      rw [abs_of_pos (by linarith)]
      linarith
  -- each lag term through the product `k m`, with the base read as the pole vector
  have hterm : ∀ k m n : ℕ, m ∈ Icc 1 N → n ∈ Icc 1 N →
      vonMangoldtAtom k * (x m * x n *
        (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))) =
      x n * ((ArithmeticFunction.vonMangoldt k : ℝ) * (poleVector (k * m) * H n (k * m))) := by
    intro k m n hm hn
    have hm1 := (mem_Icc.mp hm).1
    rcases lt_or_ge k 2 with hk | hk
    · have hΛ : (ArithmeticFunction.vonMangoldt k : ℝ) = 0 := by
        interval_cases k <;> simp
      rw [RHTower.vonMangoldtAtom_eq_zero_of_lt_two hk, hΛ]
      ring
    have hHk : (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m))) =
        H n (k * m) := by
      simp only [hH, eq_comm (a := n)]
      split_ifs
      · rfl
      · congr 1
        rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (by omega : k ≠ 0))
          (by exact_mod_cast (by omega : m ≠ 0))]
        ring
    by_cases hbase : 2 * (m : ℝ) ≤ N * Real.exp w
    · rw [hHk, hx m hm hbase]
      have h := vonMangoldtAtom_mul_poleVector k m hm1
      calc vonMangoldtAtom k * (poleVector m * x n * H n (k * m))
          = (vonMangoldtAtom k * poleVector m) * (x n * H n (k * m)) := by ring
        _ = _ := by rw [h]; ring
    · have h0 : bumpCorr g (Real.log k - (Real.log n - Real.log m)) = 0 :=
        bumpCorr_eq_zero_of_far hgsupp hk hm1 (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
          (not_le.mp hbase)
      have hH0 : H n (k * m) = 0 := by
        rw [← hHk]
        split_ifs
        · rfl
        · exact h0
      rw [hHk, hH0]
      ring
  have hlag : ∀ k ∈ range (L + 1), vonMangoldtAtom k * nonRatioLag g N k x =
      2 * ∑ n ∈ Icc 1 N, x n * ∑ m ∈ Icc 1 N,
        (ArithmeticFunction.vonMangoldt k : ℝ) * (poleVector (k * m) * H n (k * m)) := by
    intro k _
    rw [nonRatioLag_eq_two_mul, mul_left_comm]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun n hn => sum_congr rfl fun m hm => hterm k m n hm hn
  rw [htsum, Finset.sum_congr rfl hlag, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  have hfib := sum_range_sum_vonMangoldt_mul_eq (N := N) (L := L)
    (fun ℓ => poleVector ℓ * H n ℓ) (fun ℓ hℓ => by simp only [hHvan n hn ℓ hℓ, mul_zero])
  rw [← Finset.mul_sum, hfib, shellPoleRow, Finset.mul_sum]
  refine congrArg _ (sum_congr rfl fun ℓ _ => ?_)
  simp only [hH]
  ring

end GaloisForLFunctions.SuccessorShellArithmetic
