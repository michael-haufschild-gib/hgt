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
  exact lt_of_lt_of_le (by linarith only [hlog]) (le_abs_self _)

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
      have hA : vonMangoldtAtom k = 0 := by
        simp [vonMangoldtAtom, show ¬ 2 ≤ k by omega]
      rw [hA, hΛ]
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
  rw [← Finset.mul_sum, hfib, shellPoleRow]
  congr 1
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [hH]
  ring

/-! ### The witness -/

/-- The witness `x_η = b + η b 1_T`. -/
def topWitnessVector (N : ℕ) (w η : ℝ) (n : ℕ) : ℝ :=
  poleVector n + η * topWitness N w n

theorem half_lt_of_mem_topBand (hw : 0 ≤ w) {N n : ℕ} (hn : n ∈ topBand N w) :
    (N : ℝ) < 2 * n := by
  have h := (mem_topBand.mp hn).2
  have he : (N : ℝ) ≤ N * Real.exp w := le_mul_of_one_le_right (Nat.cast_nonneg N)
    (Real.one_le_exp_iff.mpr hw)
  linarith only [h, he]

/-- The witness agrees with the pole vector on every base. -/
theorem topWitnessVector_eq_on_bases {N : ℕ} {w η : ℝ} {m : ℕ}
    (hm : 2 * (m : ℝ) ≤ N * Real.exp w) : topWitnessVector N w η m = poleVector m := by
  have hT : m ∉ topBand N w := fun h => by
    have := (mem_topBand.mp h).2
    linarith only [this, hm]
  simp [topWitnessVector, topWitness, hT]

theorem shellPoleRow_nonneg (hg0 : ∀ u, 0 ≤ g u) (N : ℕ) (w : ℝ) (n : ℕ) :
    0 ≤ shellPoleRow g N w n := by
  unfold shellPoleRow
  refine sum_nonneg fun ℓ _ => mul_nonneg (mul_nonneg ?_ (horizonDivisorMangoldt_nonneg N ℓ)) ?_
  · unfold poleVector; positivity
  · split_ifs
    · exact le_rfl
    · exact bumpCorr_nonneg hg0 _

/-- **The shells on the witness**: `NR(x_η) = NR(b) + 2η Σ_{n∈T} b_n R(n)`. -/
theorem nonRatioForm_topWitnessVector (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    {N : ℕ} (hN : 1 ≤ N) (η : ℝ) :
    nonRatioForm g N (topWitnessVector N w η) = nonRatioForm g N poleVector +
      2 * η * ∑ n ∈ topBand N w, poleVector n * shellPoleRow g N w n := by
  rw [nonRatioForm_eq_of_pole_on_bases hgsupp hw hN _ fun m _ hm => topWitnessVector_eq_on_bases hm,
    nonRatioForm_eq_of_pole_on_bases hgsupp hw hN _ fun m _ _ => rfl]
  have hsplit : ∑ n ∈ Icc 1 N, topWitness N w n * shellPoleRow g N w n =
      ∑ n ∈ topBand N w, poleVector n * shellPoleRow g N w n := by
    rw [topBand, sum_filter]
    refine sum_congr rfl fun n hn => ?_
    simp only [topWitness, mem_topBand, hn, true_and]
    split_ifs <;> simp
  simp only [topWitnessVector, add_mul, sum_add_distrib, mul_assoc, ← mul_sum, hsplit]
  ring

/-- The pole vector has nonnegative shells for a nonnegative bump. -/
theorem nonRatioForm_poleVector_nonneg (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    (hg0 : ∀ u, 0 ≤ g u) {N : ℕ} (hN : 1 ≤ N) : 0 ≤ nonRatioForm g N poleVector := by
  rw [nonRatioForm_eq_of_pole_on_bases hgsupp hw hN _ fun m _ _ => rfl]
  refine mul_nonneg zero_le_two (sum_nonneg fun n _ => mul_nonneg ?_ (shellPoleRow_nonneg hg0 N w n))
  unfold poleVector; positivity

/-- **Row bound.** On the top band each row reads at least `log(N/2)/√N` per unit of top-band
autocorrelation. -/
theorem sum_topBand_shellPoleRow_ge (hw : 0 ≤ w) (hg0 : ∀ u, 0 ≤ g u) {N : ℕ} (hN : 2 ≤ N) :
    Real.log (N / 2) / N * ∑ n ∈ topBand N w, ∑ ℓ ∈ topBand N w,
        (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) ≤
      ∑ n ∈ topBand N w, poleVector n * shellPoleRow g N w n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 0 ≤ Real.log (N / 2) :=
    Real.log_nonneg (by rw [le_div_iff₀ two_pos]; exact_mod_cast (by omega : 1 * 2 ≤ N))
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hb : ∀ n ∈ topBand N w, 1 / Real.sqrt N ≤ poleVector n := by
    intro n hn
    have hn1 := (mem_Icc.mp (mem_topBand.mp hn).1)
    unfold poleVector
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by exact_mod_cast hn1.1))
      (Real.sqrt_le_sqrt (by exact_mod_cast hn1.2))
  have hlog : ∀ ℓ ∈ topBand N w, Real.log (N / 2) ≤ horizonDivisorMangoldt N ℓ := by
    intro ℓ hℓ
    have hℓ1 := (mem_Icc.mp (mem_topBand.mp hℓ).1)
    rw [horizonDivisorMangoldt_of_le hℓ1.2]
    have h2 := half_lt_of_mem_topBand hw hℓ
    exact Real.log_le_log (by positivity) (by linarith only [h2])
  have hsub : topBand N w ⊆ Icc 1 ⌈(N : ℝ) * Real.exp w⌉₊ := by
    intro ℓ hℓ
    have hℓ1 := mem_Icc.mp (mem_topBand.mp hℓ).1
    refine mem_Icc.mpr ⟨hℓ1.1, ?_⟩
    have h1 : (ℓ : ℝ) ≤ N * Real.exp w :=
      (by exact_mod_cast hℓ1.2 : (ℓ : ℝ) ≤ N).trans
        (le_mul_of_one_le_right (Nat.cast_nonneg N) (Real.one_le_exp_iff.mpr hw))
    exact_mod_cast h1.trans (Nat.le_ceil _)
  have hH : ∀ n ℓ : ℕ, 0 ≤ (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) :=
    fun n ℓ => by split_ifs; exacts [le_rfl, bumpCorr_nonneg hg0 _]
  rw [mul_sum]
  refine sum_le_sum fun n hn => ?_
  have hR : 1 / Real.sqrt N * Real.log (N / 2) * ∑ ℓ ∈ topBand N w,
      (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) ≤ shellPoleRow g N w n := by
    rw [mul_sum]
    refine (sum_le_sum fun ℓ hℓ => ?_).trans (sum_le_sum_of_subset_of_nonneg hsub fun ℓ _ _ =>
      mul_nonneg (mul_nonneg (by unfold poleVector; positivity)
        (horizonDivisorMangoldt_nonneg N ℓ)) (hH n ℓ))
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hb ℓ hℓ) (hlog ℓ hℓ) hlogN
      (by unfold poleVector; positivity)) (hH n ℓ)
  have hRn : 0 ≤ 1 / Real.sqrt N * Real.log (N / 2) * ∑ ℓ ∈ topBand N w,
      (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) :=
    mul_nonneg (mul_nonneg (by positivity) hlogN) (sum_nonneg fun ℓ _ => hH n ℓ)
  calc
    _ = 1 / Real.sqrt N * (1 / Real.sqrt N * Real.log (N / 2) * ∑ ℓ ∈ topBand N w,
        (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n))) := by
      field_simp
      rw [Real.sq_sqrt hN0.le]
    _ ≤ poleVector n * shellPoleRow g N w n := mul_le_mul (hb n hn) hR hRn
      (by unfold poleVector; positivity)

end GaloisForLFunctions.SuccessorShellArithmetic
