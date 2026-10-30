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
      ring
    _ ≤ poleVector n * shellPoleRow g N w n := mul_le_mul (hb n hn) hR hRn
      (by unfold poleVector; positivity)

/-! ### The top-band Gram -/

/-- **Top-band Gram.** The atoms of the top band sit in a window of length `log 2`, so by
Cauchy–Schwarz their Gram sum is at least `(|T|∫g)²/log 2`. -/
theorem sum_topBand_bumpCorr_ge (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) :
    ((topBand N w).card * ∫ u, g u) ^ 2 / Real.log 2 ≤
      ∑ n ∈ topBand N w, ∑ ℓ ∈ topBand N w, bumpCorr g (Real.log ℓ - Real.log n) := by
  set T := topBand N w with hT
  let χ : ℕ → ℝ := fun n => if n ∈ T then 1 else 0
  let F : ℝ → ℝ := atomicTest N χ g
  have hFc : Continuous F := continuous_finsetSum _ fun n _ =>
    continuous_const.mul (hg.comp (continuous_sub_right _))
  have hTsub : T ⊆ Icc 1 N := filter_subset _ _
  have hfT : (Icc 1 N).filter (· ∈ T) = T := by
    ext n; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hTsub h, h⟩⟩
  -- the Gram identity on the top band
  have hgram : ∫ u, F u ^ 2 = ∑ n ∈ T, ∑ ℓ ∈ T, bumpCorr g (Real.log ℓ - Real.log n) := by
    rw [integral_atomicTest_sq_eq_gram hg hgc N χ]
    have h1 : ∀ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        χ m * χ n * bumpCorr g (-(Real.log n - Real.log m)) =
        if m ∈ T then ∑ n ∈ T, bumpCorr g (Real.log m - Real.log n) else 0 := by
      intro m _
      by_cases hm : m ∈ T
      · rw [if_pos hm]
        have hrow : ∀ n ∈ Icc 1 N, χ m * χ n * bumpCorr g (-(Real.log n - Real.log m)) =
            if n ∈ T then bumpCorr g (Real.log m - Real.log n) else 0 := by
          intro n _
          simp only [χ, if_pos hm, one_mul, neg_sub]
          split_ifs <;> simp
        rw [sum_congr rfl hrow, ← sum_filter, hfT]
      · rw [if_neg hm]
        exact sum_eq_zero fun n _ => by simp [χ, hm]
    rw [sum_congr rfl h1, ← sum_filter, hfT, sum_comm]
  -- the total mass
  have hint : ∫ u, F u = T.card * ∫ u, g u := by
    have hi : ∀ n ∈ Icc 1 N, Integrable fun u => χ n * g (u - Real.log n) := fun n _ =>
      ((continuous_const.mul (hg.comp (continuous_sub_right _))).integrable_of_hasCompactSupport
        ((hgc.comp_homeomorph (Homeomorph.subRight (Real.log n))).mul_left))
    simp only [F, atomicTest]
    rw [integral_finsetSum _ hi]
    simp_rw [integral_const_mul, integral_sub_right_eq_self]
    rw [← sum_mul]
    congr 1
    rw [← sum_filter, hfT, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- the window of length `log 2`
  set a := Real.log N + w - Real.log 2 with ha
  have hwin : ∀ u, u ∉ Set.Icc 0 (Real.log 2) → F (u + a) = 0 := by
    intro u hu
    simp only [F, atomicTest]
    refine sum_eq_zero fun n _ => ?_
    by_cases hn : n ∈ T
    · have hn' := mem_topBand.mp hn
      have hn1 := mem_Icc.mp hn'.1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1.1
      have hlo : a < Real.log n := by
        have h := Real.log_lt_log
          (mul_pos (by exact_mod_cast (by omega : 0 < N)) (Real.exp_pos w)) hn'.2
        rw [Real.log_mul (by exact_mod_cast (by omega : N ≠ 0)) (Real.exp_pos w).ne',
          Real.log_exp, Real.log_mul two_ne_zero hn0.ne'] at h
        rw [ha]; linarith only [h]
      have hhi : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hn1.2)
      have hg0 : g (u + a - Real.log n) = 0 := by
        apply hgsupp
        intro hmem
        apply hu
        rw [ha] at hmem hlo
        exact ⟨by linarith only [hmem.1, hlo], by linarith only [hmem.2, hhi]⟩
      rw [hg0, mul_zero]
    · simp [χ, hn]
  -- Cauchy–Schwarz on the window
  let F' : ℝ → ℝ := fun u => F (u + a)
  have hcs := ArithmeticLorentzianGeometry.sq_integral_abs_le (g := F')
    (hFc.comp (continuous_add_const a)) hwin (Real.log_pos one_lt_two)
  have h1 : ∫ u, |F' u| = ∫ u, |F u| := integral_add_right_eq_self (fun u => |F u|) a
  have h2 : ∫ u, F' u ^ 2 = ∫ u, F u ^ 2 := integral_add_right_eq_self (fun u => F u ^ 2) a
  have h3 : (∫ u, F u) ^ 2 ≤ (∫ u, |F u|) ^ 2 := by
    have h : |∫ u, F u| ≤ ∫ u, |F u| := abs_integral_le_integral_abs
    rw [← sq_abs (∫ u, F u)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [hint] at h3
  rw [h1, h2, hgram] at hcs
  rw [div_le_iff₀ (Real.log_pos one_lt_two)]
  linarith only [h3, hcs, mul_comm (Real.log 2)
    (∑ n ∈ T, ∑ ℓ ∈ T, bumpCorr g (Real.log ℓ - Real.log n))]

/-! ### Defect and mass of the witness -/

theorem poleVector_mul_eq (m t : ℕ) : poleVector (m * t) = poleVector m / Real.sqrt t := by
  unfold poleVector
  rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m), one_div, one_div, mul_inv, div_eq_mul_inv]

/-- The pole vector satisfies every pole relation, so the witness only pays for its direction. -/
theorem poleDefect_topWitnessVector (N : ℕ) (w η : ℝ) :
    poleDefect N (topWitnessVector N w η) = η ^ 2 * poleDefect N (topWitness N w) := by
  unfold poleDefect
  rw [mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun t _ => ?_
  simp only [topWitnessVector, poleVector_mul_eq m t]
  ring

/-- The divisors of `n ≤ N` regroup the prime edges: `Σ_m Σ_{t ≤ N/m} Λ(t) F(mt) = Σ_n F(n) log n`. -/
theorem sum_edges_eq_sum_log {N : ℕ} (F : ℕ → ℝ) (hF : ∀ n, N < n → F n = 0) :
    ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), (ArithmeticFunction.vonMangoldt t : ℝ) * F (m * t) =
      ∑ n ∈ Icc 1 N, Real.log n * F n := by
  have hext : ∀ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), (ArithmeticFunction.vonMangoldt t : ℝ) * F (m * t) =
      ∑ k ∈ range (N + 1), (ArithmeticFunction.vonMangoldt k : ℝ) * F (k * m) := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    refine sum_subset (fun t ht => mem_range.mpr (Nat.lt_succ_of_le
      ((mem_Icc.mp ht).2.trans (Nat.div_le_self N m)))) (fun k _ hk => ?_) |>.trans
      (sum_congr rfl fun k _ => by rw [mul_comm m k])
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · have hlt : N / m < k := by
        by_contra h
        exact hk (mem_Icc.mpr ⟨hk0, not_lt.mp h⟩)
      rw [hF _ ((Nat.div_lt_iff_lt_mul (by omega)).mp hlt |>.trans_eq (mul_comm k m)), mul_zero]
  rw [sum_congr rfl hext, sum_comm, sum_range_sum_vonMangoldt_mul_eq (L := N) F hF]
  exact sum_congr rfl fun n hn => by rw [horizonDivisorMangoldt_of_le (mem_Icc.mp hn).2]

/-- **The witness is cheap**: its defect is at most `log N Σ_T 1/n`. -/
theorem poleDefect_topWitness_le (hw : 0 ≤ w) (N : ℕ) :
    poleDefect N (topWitness N w) ≤ Real.log N * ∑ n ∈ topBand N w, 1 / (n : ℝ) := by
  have hterm : ∀ m ∈ Icc 1 N, ∀ t ∈ Icc 1 (N / m),
      (ArithmeticFunction.vonMangoldt t : ℝ) * (topWitness N w (m * t) -
        topWitness N w m / Real.sqrt t) ^ 2 ≤
      (ArithmeticFunction.vonMangoldt t : ℝ) * topWitness N w (m * t) ^ 2 := by
    intro m hm t ht
    by_cases hmT : m ∈ topBand N w
    · -- a top-band base has only the trivial edge `t = 1`
      have h2 := half_lt_of_mem_topBand hw hmT
      have hm1 := (mem_Icc.mp hm).1
      have htle : t * m ≤ N := by
        have := Nat.div_mul_le_self N m
        exact (Nat.mul_le_mul_right m (mem_Icc.mp ht).2).trans this
      have ht1 : t = 1 := by
        have ht1' := (mem_Icc.mp ht).1
        by_contra hne
        have : 2 * m ≤ t * m := Nat.mul_le_mul_right m (by omega)
        have hR : (2 * m : ℝ) ≤ N := by exact_mod_cast this.trans htle
        linarith only [hR, h2]
      subst ht1
      simp
    · simp only [topWitness, hmT, if_false, zero_div, sub_zero]
      exact le_rfl
  have hD : poleDefect N (topWitness N w) ≤ ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
      (ArithmeticFunction.vonMangoldt t : ℝ) * topWitness N w (m * t) ^ 2 := by
    unfold poleDefect
    exact sum_le_sum fun m hm => sum_le_sum fun t ht => hterm m hm t ht
  calc
    poleDefect N (topWitness N w) ≤ ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
        (ArithmeticFunction.vonMangoldt t : ℝ) * topWitness N w (m * t) ^ 2 := hD
    _ = ∑ n ∈ Icc 1 N, Real.log n * topWitness N w n ^ 2 := by
      refine sum_edges_eq_sum_log (fun n => topWitness N w n ^ 2) fun n hn => ?_
      have : n ∉ topBand N w := fun h => by
        have := (mem_Icc.mp (mem_topBand.mp h).1).2; omega
      simp [topWitness, this]
    _ ≤ ∑ n ∈ Icc 1 N, Real.log N * topWitness N w n ^ 2 := by
      refine sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hn1 := mem_Icc.mp hn
      exact Real.log_le_log (by exact_mod_cast hn1.1) (by exact_mod_cast hn1.2)
    _ = Real.log N * ∑ n ∈ topBand N w, 1 / (n : ℝ) := by
      rw [← mul_sum, topBand, sum_filter]
      congr 1
      refine sum_congr rfl fun n _ => ?_
      simp only [topWitness, topBand, mem_filter]
      split_ifs with h1 h2 h2
      · rw [poleVector_sq]
      · exact absurd h1.2 h2
      · exact absurd ⟨by assumption, h2⟩ h1
      · simp

/-- The mass of the witness. -/
theorem sum_topWitnessVector_sq (N : ℕ) (w η : ℝ) :
    ∑ n ∈ Icc 1 N, topWitnessVector N w η n ^ 2 =
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ) + (2 * η + η ^ 2) * ∑ n ∈ topBand N w, 1 / (n : ℝ) := by
  have hT : ∑ n ∈ topBand N w, 1 / (n : ℝ) =
      ∑ n ∈ Icc 1 N, (if n ∈ topBand N w then 1 / (n : ℝ) else 0) := by
    rw [← sum_filter]
    congr 1
    ext n
    simp only [mem_filter]
    exact ⟨fun h => ⟨(mem_topBand.mp h).1, h⟩, fun h => h.2⟩
  rw [hT, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  simp only [topWitnessVector, topWitness]
  split_ifs
  · rw [show (poleVector n + η * poleVector n) ^ 2 = (1 + η) ^ 2 * poleVector n ^ 2 by ring,
      poleVector_sq]
    ring
  · rw [mul_zero, add_zero, poleVector_sq, mul_zero, add_zero]

/-- `Σ_{n∈T} 1/n ≤ 2`: every top-band atom exceeds `N/2`. -/
theorem sum_topBand_inv_le_two (hw : 0 ≤ w) (N : ℕ) :
    ∑ n ∈ topBand N w, 1 / (n : ℝ) ≤ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [topBand]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑ _n ∈ topBand N w, 2 / (N : ℝ) := by
      refine sum_le_sum fun n hn => ?_
      have h2 := half_lt_of_mem_topBand hw hn
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (mem_Icc.mp (mem_topBand.mp hn).1).1
      rw [div_le_div_iff₀ hn0 hN0]
      linarith only [h2]
    _ = (topBand N w).card * (2 / (N : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ N * (2 / (N : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hc : (topBand N w).card ≤ N := by
        have := card_le_card (filter_subset _ _ : topBand N w ⊆ Icc 1 N)
        rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
      exact_mod_cast hc
    _ = 2 := by field_simp

/-- The top band holds at least `N(1 − e^w/2)` atoms. -/
theorem card_topBand_ge (N : ℕ) (w : ℝ) :
    (N : ℝ) * (1 - Real.exp w / 2) ≤ (topBand N w).card := by
  set y := (N : ℝ) * Real.exp w / 2
  have hy : 0 ≤ y := by positivity
  have hsub : Icc (⌊y⌋₊ + 1) N ⊆ topBand N w := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Icc.mp hn
    refine mem_topBand.mpr ⟨mem_Icc.mpr ⟨by omega, h2⟩, ?_⟩
    have := Nat.lt_floor_add_one y
    have hn' : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
    push_cast at hn'
    dsimp only [y] at this
    linarith only [this, hn']
  have hcard := card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hfl := Nat.floor_le hy
  rcases le_or_gt ⌊y⌋₊ N with hle | hlt
  · have : ((N + 1 - (⌊y⌋₊ + 1) : ℕ) : ℝ) = N - ⌊y⌋₊ := by
      rw [show N + 1 - (⌊y⌋₊ + 1) = N - ⌊y⌋₊ by omega, Nat.cast_sub hle]
    have hc : (N : ℝ) - ⌊y⌋₊ ≤ (topBand N w).card := by
      rw [← this]; exact_mod_cast hcard
    dsimp only [y] at hfl
    linarith only [hc, hfl]
  · have : (N : ℝ) < ⌊y⌋₊ := by exact_mod_cast hlt
    dsimp only [y] at hfl
    linarith only [this, hfl, (Nat.cast_nonneg _ : (0 : ℝ) ≤ (topBand N w).card)]

/-- The top band holds at most `N/2 + 1` atoms. -/
theorem card_topBand_le (hw : 0 ≤ w) (N : ℕ) :
    ((topBand N w).card : ℝ) ≤ N / 2 + 1 := by
  have hsub : topBand N w ⊆ Icc (N / 2 + 1) N := by
    intro n hn
    have h2 := half_lt_of_mem_topBand hw hn
    have hn1 := mem_Icc.mp (mem_topBand.mp hn).1
    have h2' : N < 2 * n := by exact_mod_cast h2
    exact mem_Icc.mpr ⟨by omega, hn1.2⟩
  have hcard := card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have h : 2 * (N + 1 - (N / 2 + 1)) ≤ N + 2 := by omega
  have hR : (2 : ℝ) * (topBand N w).card ≤ N + 2 := by exact_mod_cast (Nat.mul_le_mul_left 2 hcard).trans h
  linarith only [hR]

/-! ### The floor -/

/-- The coefficient `A = cq/(4 log 2) − 1/2`, `q = (∫φ)²/∫φ²`, of the top-band shell reading. -/
def shellFloorCoefficient (φ : ℝ → ℝ) (c : ℝ) : ℝ :=
  c * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) / (4 * Real.log 2) - 1 / 2

private theorem harmonic_sum_bounds (N : ℕ) :
    Real.log N ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ∧ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ≤ 1 + Real.log N := by
  have hlo : Real.log N ≤ (harmonic N : ℝ) := by
    simpa only [Nat.floor_natCast] using log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg N)
  have hup := harmonic_le_one_add_log N
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlo hup
  simp only [← one_div] at hlo hup
  exact ⟨hlo, hup⟩

/-- One horizon of the floor: the payment hypothesis at `x_η`, divided by `G log N`. -/
private theorem floor_inequality_at {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c ε C η : ℝ} (hc : 0 < c) (hε : 0 < ε) (hη : 0 ≤ η) {N : ℕ} (hN : 2 ≤ N)
    (hpay : nonRatioForm (atomDilate φ (c / N)) N (topWitnessVector N (c / N) η) ≤
      (∫ u, atomDilate φ (c / N) u ^ 2) * (ε * poleDefect N (topWitnessVector N (c / N) η) +
        C * ∑ n ∈ Icc 1 N, topWitnessVector N (c / N) η n ^ 2)) :
    2 * η * (Real.log (N / 2) / Real.log N) *
        (((topBand N (c / N)).card / (N : ℝ)) ^ 2 *
          (c * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2)) / Real.log 2 -
          (topBand N (c / N)).card / (N : ℝ)) ≤
      2 * ε * η ^ 2 + C * ((∑ n ∈ Icc 1 N, 1 / (n : ℝ)) / Real.log N) +
        C * (2 * η + η ^ 2) * ((∑ n ∈ topBand N (c / N), 1 / (n : ℝ)) / Real.log N) := by
  set w := c / (N : ℝ) with hwdef
  set g := atomDilate φ w with hgdef
  set T := topBand N w with hT
  set M := ∫ u, φ u ^ 2 with hMdef
  set I := ∫ u, φ u with hIdef
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : 1 ≤ N := by omega
  have hw : 0 < w := div_pos hc hN0
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  -- the atom
  have hgc : Continuous g := hφ.comp (continuous_id.div_const w)
  have hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0 := by
    intro u hu
    apply hsupp
    intro h
    apply hu
    rw [Set.mem_Icc, le_div_iff₀ hw, div_le_iff₀ hw] at h
    constructor <;> nlinarith only [h.1, h.2, hw]
  have hgcs : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc fun u hu => hgsupp u hu
  have hg0 : ∀ u, 0 ≤ g u := fun u => hφ0 _
  have hG : (∫ u, g u ^ 2) = w * M := integral_atomDilate_sq hw
  have hI : (∫ u, g u) = w * I := by
    rw [hgdef, hIdef]
    simpa only [atomDilate, smul_eq_mul, abs_of_pos hw] using
      MeasureTheory.Measure.integral_comp_div φ w
  -- the shells on the witness
  have hNR := nonRatioForm_topWitnessVector hgsupp hw.le hN1 η
  have hNRb := nonRatioForm_poleVector_nonneg hgsupp hw.le hg0 hN1
  have hrow := sum_topBand_shellPoleRow_ge (g := g) hw.le hg0 hN
  have hgram := sum_topBand_bumpCorr_ge hgc hgcs hgsupp (w := w) N
  have hoff : ∑ n ∈ T, ∑ ℓ ∈ T, (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) =
      ∑ n ∈ T, ∑ ℓ ∈ T, bumpCorr g (Real.log ℓ - Real.log n) - T.card * (w * M) := by
    have hd : ∀ n ∈ T, ∑ ℓ ∈ T, (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) =
        ∑ ℓ ∈ T, bumpCorr g (Real.log ℓ - Real.log n) - w * M := by
      intro n hn
      rw [← hG, ← bumpCorr_zero g]
      have := sum_erase_add T (fun ℓ => bumpCorr g (Real.log ℓ - Real.log n)) hn
      rw [sub_self] at this
      rw [← this, add_sub_cancel_right, ← sum_erase_add T _ hn, if_pos rfl, add_zero]
      exact sum_congr rfl fun ℓ hℓ => by rw [if_neg (ne_of_mem_erase hℓ)]
    rw [sum_congr rfl hd, sum_sub_distrib, sum_const, nsmul_eq_mul]
  -- defect and mass
  have hD := poleDefect_topWitness_le hw.le N
  have hDη := poleDefect_topWitnessVector N w η
  have hS := sum_topWitnessVector_sq N w η
  have hST := sum_topBand_inv_le_two hw.le N
  have hST0 : 0 ≤ ∑ n ∈ T, 1 / (n : ℝ) := sum_nonneg fun n _ => by positivity
  -- assemble
  set τ : ℝ := (T.card : ℝ)
  set R := ∑ n ∈ T, poleVector n * shellPoleRow g N w n
  set Gr := ∑ n ∈ T, ∑ ℓ ∈ T, bumpCorr g (Real.log ℓ - Real.log n)
  have hlogN2 : 0 ≤ Real.log (N / 2) :=
    Real.log_nonneg (by rw [le_div_iff₀ two_pos]; exact_mod_cast (by omega : 1 * 2 ≤ N))
  have hgram' : (τ * (w * I)) ^ 2 ≤ Gr * Real.log 2 := by
    rw [← hI]
    exact (div_le_iff₀ (Real.log_pos one_lt_two)).mp hgram
  -- lower bound on the shells
  have hlow : 2 * η * (Real.log (N / 2) / N * ((τ * (w * I)) ^ 2 / Real.log 2 - τ * (w * M))) ≤
      nonRatioForm g N (topWitnessVector N w η) := by
    have h1 : (τ * (w * I)) ^ 2 / Real.log 2 - τ * (w * M) ≤ Gr - τ * (w * M) := by
      have := (div_le_iff₀ (Real.log_pos one_lt_two)).mpr hgram'
      linarith only [this]
    have h2 : Real.log (N / 2) / N * (Gr - τ * (w * M)) ≤ R := by
      rw [← hoff]; exact hrow
    have h3 := mul_le_mul_of_nonneg_left h1 (div_nonneg hlogN2 hN0.le)
    rw [hNR]
    nlinarith only [h2, h3, hNRb, hη]
  -- upper bound on the payment
  have hup : (∫ u, g u ^ 2) * (ε * poleDefect N (topWitnessVector N w η) +
        C * ∑ n ∈ Icc 1 N, topWitnessVector N w η n ^ 2) ≤
      w * M * (ε * η ^ 2 * (Real.log N * 2) + C * ((∑ n ∈ Icc 1 N, 1 / (n : ℝ)) +
        (2 * η + η ^ 2) * ∑ n ∈ T, 1 / (n : ℝ))) := by
    rw [hG, hDη, hS]
    have hwM : 0 ≤ w * M := (mul_pos hw hM).le
    refine mul_le_mul_of_nonneg_left ?_ hwM
    have hεη : 0 ≤ ε * η ^ 2 := mul_nonneg hε.le (sq_nonneg η)
    have hD2 : poleDefect N (topWitness N w) ≤ Real.log N * 2 :=
      hD.trans (mul_le_mul_of_nonneg_left hST hL.le)
    nlinarith only [mul_le_mul_of_nonneg_left hD2 hεη]
  have hchain := (hlow.trans hpay).trans hup
  -- divide by `w M log N`
  have hpos : 0 < w * M * Real.log N := mul_pos (mul_pos hw hM) hL
  rw [← mul_le_mul_iff_of_pos_left hpos]
  have hwN : w * N = c := by rw [hwdef]; field_simp
  have heq : w * M * Real.log N * (2 * η * (Real.log (N / 2) / Real.log N) *
      ((τ / N) ^ 2 * (c * (I ^ 2 / M)) / Real.log 2 - τ / N)) =
      2 * η * (Real.log (N / 2) / N * ((τ * (w * I)) ^ 2 / Real.log 2 - τ * (w * M))) := by
    rw [← hwN]
    field_simp
  have heq2 : w * M * Real.log N * (2 * ε * η ^ 2 + C * ((∑ n ∈ Icc 1 N, 1 / (n : ℝ)) /
      Real.log N) + C * (2 * η + η ^ 2) * ((∑ n ∈ T, 1 / (n : ℝ)) / Real.log N)) =
      w * M * (ε * η ^ 2 * (Real.log N * 2) + C * ((∑ n ∈ Icc 1 N, 1 / (n : ℝ)) +
        (2 * η + η ^ 2) * ∑ n ∈ T, 1 / (n : ℝ))) := by
    field_simp
    ring
  rw [heq, heq2]
  exact hchain

/-- **The shells alone cost the square of the overlap.** For a nonnegative profile, if the
non-ratio form is paid by itself at defect fraction `ε` and mass cost `C` at every large horizon,
`NR(x) ≤ G(εD(x) + C S(x))`, then `C ≥ A⁺²/(2ε)`, `A = cq/(4 log 2) − 1/2`. -/
theorem le_of_nonRatioForm_payment {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c ε C : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hpay : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      nonRatioForm (atomDilate φ (c / N)) N x ≤
        (∫ u, atomDilate φ (c / N) u ^ 2) *
          (ε * poleDefect N x + C * ∑ n ∈ Icc 1 N, x n ^ 2)) :
    max (shellFloorCoefficient φ c) 0 ^ 2 / (2 * ε) ≤ C := by
  set q := (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 with hq
  set A := shellFloorCoefficient φ c with hA
  set η := max A 0 / (2 * ε) with hηdef
  have hη : 0 ≤ η := div_nonneg (le_max_right _ _) (by positivity)
  -- the top band fills half the horizon
  have hexp : Tendsto (fun N : ℕ => Real.exp (c / N)) atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).div_atTop
        tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def, Real.exp_zero] using h
  have hinvN : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hτ : Tendsto (fun N : ℕ => ((topBand N (c / N)).card : ℝ) / N) atTop (𝓝 (1 / 2)) := by
    have hlo : Tendsto (fun N : ℕ => 1 - Real.exp (c / N) / 2) atTop (𝓝 (1 / 2)) := by
      have := (hexp.div_const 2).const_sub 1
      convert this using 2; norm_num
    have hhi : Tendsto (fun N : ℕ => 1 / 2 + 1 / (N : ℝ)) atTop (𝓝 (1 / 2)) := by
      simpa only [add_zero] using hinvN.const_add (1 / 2)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [le_div_iff₀ hN0]
      have := card_topBand_ge N (c / N)
      linarith only [this]
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_iff₀ hN0]
      have := card_topBand_le (div_nonneg hc.le hN0.le) N
      have h1 : (1 / 2 + 1 / (N : ℝ)) * N = N / 2 + 1 := by field_simp
      linarith only [this, h1]
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun N : ℕ => Real.log ((N : ℝ) / 2) / Real.log N) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := Real.log 2)).div_atTop hlogN
    have h' := h.const_sub 1
    rw [sub_zero] at h'
    refine h'.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    rw [Real.log_div (by positivity) two_ne_zero]
    field_simp
  have hH : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) / Real.log N) atTop (𝓝 1) := by
    have hhi : Tendsto (fun N : ℕ => 1 + 1 / Real.log N) atTop (𝓝 1) := by
      simpa only [add_zero] using (tendsto_const_nhds.div_atTop hlogN).const_add 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi ?_ ?_
    · filter_upwards [eventually_gt_atTop 1] with N hN
      have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
      rw [le_div_iff₀ hL, one_mul]
      exact (harmonic_sum_bounds N).1
    · filter_upwards [eventually_gt_atTop 1] with N hN
      have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
      rw [div_le_iff₀ hL, add_mul, one_mul, div_mul_cancel₀ _ hL.ne']
      linarith only [(harmonic_sum_bounds N).2]
  have hS0 : Tendsto (fun N : ℕ => (∑ n ∈ topBand N (c / N), 1 / (n : ℝ)) / Real.log N)
      atTop (𝓝 0) := by
    have hhi : Tendsto (fun N : ℕ => 2 / Real.log N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlogN
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi ?_ ?_
    all_goals filter_upwards [eventually_gt_atTop 1] with N hN
    all_goals have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    · exact div_nonneg (sum_nonneg fun n _ => by positivity) hL.le
    · exact div_le_div_of_nonneg_right
        (sum_topBand_inv_le_two (div_nonneg hc.le (by positivity)) N) hL.le
  -- the two sides converge
  have hleft : Tendsto (fun N : ℕ => 2 * η * (Real.log ((N : ℝ) / 2) / Real.log N) *
      ((((topBand N (c / N)).card : ℝ) / N) ^ 2 * (c * q) / Real.log 2 -
        ((topBand N (c / N)).card : ℝ) / N)) atTop
      (𝓝 (2 * η * 1 * ((1 / 2) ^ 2 * (c * q) / Real.log 2 - 1 / 2))) :=
    ((tendsto_const_nhds.mul hratio).mul
      ((((hτ.pow 2).mul_const (c * q)).div_const (Real.log 2)).sub hτ))
  have hright : Tendsto (fun N : ℕ => 2 * ε * η ^ 2 +
      C * ((∑ n ∈ Icc 1 N, 1 / (n : ℝ)) / Real.log N) +
      C * (2 * η + η ^ 2) * ((∑ n ∈ topBand N (c / N), 1 / (n : ℝ)) / Real.log N)) atTop
      (𝓝 (2 * ε * η ^ 2 + C * 1 + C * (2 * η + η ^ 2) * 0)) :=
    (tendsto_const_nhds.add (hH.const_mul C)).add (hS0.const_mul _)
  have hlim := le_of_tendsto_of_tendsto hleft hright (by
    filter_upwards [hpay, eventually_ge_atTop 2] with N hN hN2
    exact floor_inequality_at hφ hφ0 hsupp hM hc hε hη hN2 (hN _))
  -- optimize in `η`
  have hAq : (1 / 2) ^ 2 * (c * q) / Real.log 2 - 1 / 2 = A := by
    rw [hA, shellFloorCoefficient, hq]
    field_simp
    ring
  rw [hAq] at hlim
  have hmax : max A 0 * A = max A 0 ^ 2 := by
    rcases le_total A 0 with h | h
    · rw [max_eq_right h]; ring
    · rw [max_eq_left h]; ring
  have hkey : 2 * η * 1 * A - 2 * ε * η ^ 2 = max A 0 ^ 2 / (2 * ε) := by
    rw [hηdef]
    field_simp
    rw [← hmax]
    ring
  linarith only [hlim, hkey]

/-- **Against the reserve fraction.** A separate payment at the defect fraction `a c⁻⁷` of the
complete reserve costs `C ≥ A⁺² c⁷/(2a)`: order `c⁹`. -/
theorem le_of_nonRatioForm_payment_at_reserve {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφ0 : ∀ u, 0 ≤ φ u) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c a C : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hpay : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      nonRatioForm (atomDilate φ (c / N)) N x ≤
        (∫ u, atomDilate φ (c / N) u ^ 2) *
          (a / c ^ 7 * poleDefect N x + C * ∑ n ∈ Icc 1 N, x n ^ 2)) :
    max (shellFloorCoefficient φ c) 0 ^ 2 * c ^ 7 / (2 * a) ≤ C := by
  have h := le_of_nonRatioForm_payment hφ hφ0 hsupp hM hc (by positivity : 0 < a / c ^ 7) hpay
  have hc7 : 0 < c ^ 7 := by positivity
  calc
    _ = max (shellFloorCoefficient φ c) 0 ^ 2 / (2 * (a / c ^ 7)) := by
      field_simp
    _ ≤ C := h

end GaloisForLFunctions.SuccessorShellArithmetic

#print axioms GaloisForLFunctions.SuccessorShellArithmetic.le_of_nonRatioForm_payment
#print axioms GaloisForLFunctions.SuccessorShellArithmetic.le_of_nonRatioForm_payment_at_reserve
