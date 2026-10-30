import GaloisForLFunctions.SuccessorShellArithmetic.TheNonRatioFormIsAFiniteSumOfShells

/-!
# The twin defect is a successor-disagreement shell

Let `ω` be a completely multiplicative sign gauge (the Liouville function, a real character off a
prime, …). Its twin replaces `Λ(k)` by `ω(k)Λ(k)` in the prime form. The gauge defect identity
(`twistedPrimeSum_sub_primeSum_gauge_eq_of_supp`) weights each lag term by `ω(k) − ω(m)ω(n)`,
which vanishes on ratio pairs. In shell coordinates `n = km + h` this factor is

`ω(k) − ω(m)ω(km + h) = ω(k)(1 − σ_h(km))`,  `σ_h(ℓ) = ω(ℓ)ω(ℓ + h)`,

the **successor sign** of the product at shift `h`; `1 − σ_h ∈ {0, 2}` is twice the disagreement
indicator.

* **Twin defect = disagreement shells** (`twistedPrimeSum_sub_primeSum_eq_sum_twinShellForm`): the
  twin's prime form minus `ζ`'s prime form of the gauged vector is a sum over the shifts
  `0 < |h| ≤ N(e^w − 1)` of shell forms carried by the pairs `(m, km + h)` whose product `km` and
  partner `km + h` have opposite signs.
* **Agreeing shifts are invisible** (`twinShellForm_eq_zero_of_agree`): a shift on which the gauge
  agrees with its successor contributes nothing.
* **Below the spacing the twins coincide** (`twistedPrimeSum_eq_of_shellRange_eq_zero`).

So a selective inequality that separates `ζ` from its twins must read the shells, and only through
the successor signs of the gauge: the object of Signed Successor Arithmetic.
-/

noncomputable section

open Finset RHTower

namespace GaloisForLFunctions.SuccessorShellArithmetic

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

variable {g : ℝ → ℝ} {w : ℝ} {ω : ArithmeticFunction ℝ}

/-- The twin shell of shift `h`: the pairs `n = km + h`, weighted by `ω(k)` and the successor
disagreement `1 − ω(km)ω(n)`. -/
def twinShellForm (g : ℝ → ℝ) (N : ℕ) (ω : ArithmeticFunction ℝ) (h : ℤ) (x : ℕ → ℝ) : ℝ :=
  2 * ∑' k : ℕ, ω k * vonMangoldtAtom k * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
    if (n : ℤ) = k * m + h then
      (1 - ω (k * m) * ω n) * x m * x n * bumpCorr g (Real.log k - (Real.log n - Real.log m))
    else 0

/-- Weighted shell decomposition of the upward non-ratio terms of one prime power. -/
private theorem upward_weighted_eq_sum_shifts (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N k : ℕ} (hk : 1 ≤ k) (F : ℕ → ℕ → ℝ) :
    (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (if n = k * m then 0 else F m n * bumpCorr g (Real.log k - (Real.log n - Real.log m)))) =
      ∑ h ∈ shellShifts N w, ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if (n : ℤ) = k * m + h then
          F m n * bumpCorr g (Real.log k - (Real.log n - Real.log m)) else 0 := by
  symm
  rw [Finset.sum_comm]
  refine sum_congr rfl fun m hm => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun n hn => ?_
  have hiff : ∀ h : ℤ, ((n : ℤ) = k * m + h) ↔ ((n : ℤ) - k * m = h) := fun h => by
    constructor <;> intro h' <;> linarith only [h']
  simp_rw [hiff]
  rw [sum_ite_eq]
  by_cases hne : n = k * m
  · have h0 : (n : ℤ) - k * m ∉ shellShifts N w := by
      rw [hne]; push_cast; simp [shellShifts]
    rw [if_pos hne, if_neg h0]
  · rw [if_neg hne]
    by_cases hβ : bumpCorr g (Real.log k - (Real.log n - Real.log m)) = 0
    · rw [hβ, mul_zero]; split_ifs <;> rfl
    · have hmem : (n : ℤ) - k * m ∈ shellShifts N w := by
        have hm1 := (mem_Icc.mp hm).1
        obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
        have hb := (abs_shift_le_of_bumpCorr_ne_zero hgsupp hk hm1 hn1 hβ).1
        have hw : 0 ≤ w := by
          by_contra hw
          exact hβ (bumpCorr_eq_zero hgsupp (lt_of_lt_of_le (not_le.mp hw) (abs_nonneg _)))
        have he : 0 ≤ Real.exp w - 1 := by linarith only [Real.add_one_le_exp w, hw]
        have hbN : |(n : ℝ) - k * m| ≤ (N : ℝ) * (Real.exp w - 1) :=
          hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) he)
        set z : ℤ := (n : ℤ) - k * m with hz
        have hcast : (((|z|).toNat : ℕ) : ℝ) = |(n : ℝ) - k * m| := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg z), Int.cast_abs, hz]
          push_cast
          rfl
        have hnat : (|z|).toNat ≤ shellRange N w := by
          apply Nat.le_floor
          rw [hcast]
          exact hbN
        have htn := Int.toNat_of_nonneg (abs_nonneg z)
        have hfloor : |z| ≤ (shellRange N w : ℤ) := by omega
        refine mem_erase.mpr ⟨fun h0 => hne ?_, mem_Icc.mpr (abs_le.mp hfloor)⟩
        exact_mod_cast (sub_eq_zero.mp h0)
      rw [if_pos hmem]

/-- The gauge factor in successor form: `ω(k) − ω(m)ω(n) = ω(k)(1 − ω(km)ω(n))`. -/
theorem gaugeFactor_eq_successor (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) {k : ℕ} (hk : 0 < k) (m n : ℕ) :
    ω k - ω m * ω n = ω k * (1 - ω (k * m) * ω n) := by
  have hsq : ω k * ω k = 1 := by
    rcases hsign k hk with h | h <;> rw [h] <;> norm_num
  rw [hω]
  linear_combination (ω m * ω n) * hsq

/-- **The twin defect is a sum of successor-disagreement shells.** -/
theorem twistedPrimeSum_sub_primeSum_eq_sum_twinShellForm (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) (N : ℕ) (x : ℕ → ℝ) :
    twistedPrimeSum ω (atomicTest N x g) - primeSum (atomicTest N (fun n => ω n * x n) g) =
      ∑ h ∈ shellShifts N w, twinShellForm g N ω h x := by
  rw [twistedPrimeSum_sub_primeSum_gauge_eq_of_supp hω hsign hg hgc hgsupp hw N x]
  -- one prime power at a time
  have hterm : ∀ k : ℕ, vonMangoldtAtom k * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (ω k - ω m * ω n) * x m * x n *
        ((if m = k * n then 0 else bumpCorr g (-Real.log k - (Real.log n - Real.log m))) +
          (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))) =
      ∑ h ∈ shellShifts N w, 2 * (ω k * vonMangoldtAtom k * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if (n : ℤ) = k * m + h then
          (1 - ω (k * m) * ω n) * x m * x n *
            bumpCorr g (Real.log k - (Real.log n - Real.log m)) else 0) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [vonMangoldtAtom]
    -- the two orientations carry the same pairs
    have hsym : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (ω k - ω m * ω n) * x m * x n *
        ((if m = k * n then 0 else bumpCorr g (-Real.log k - (Real.log n - Real.log m))) +
          (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m))))) =
        2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if n = k * m then 0 else
          ((ω k - ω m * ω n) * x m * x n) * bumpCorr g (Real.log k - (Real.log n - Real.log m))) := by
      simp only [mul_add, sum_add_distrib]
      have hdown : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (ω k - ω m * ω n) * x m * x n *
          (if m = k * n then 0 else bumpCorr g (-Real.log k - (Real.log n - Real.log m)))) =
          ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if n = k * m then 0 else
            ((ω k - ω m * ω n) * x m * x n) *
              bumpCorr g (Real.log k - (Real.log n - Real.log m))) := by
        rw [Finset.sum_comm]
        refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
        split_ifs
        · ring
        · rw [show -Real.log k - (Real.log m - Real.log n) =
            -(Real.log k - (Real.log n - Real.log m)) by ring, bumpCorr_neg]
          ring
      have hup : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (ω k - ω m * ω n) * x m * x n *
          (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))) =
          ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if n = k * m then 0 else
            ((ω k - ω m * ω n) * x m * x n) *
              bumpCorr g (Real.log k - (Real.log n - Real.log m))) :=
        sum_congr rfl fun m _ => sum_congr rfl fun n _ => by split_ifs <;> ring
      rw [hdown, hup]
      ring
    rw [hsym, upward_weighted_eq_sum_shifts hgsupp hk, mul_sum, mul_sum]
    refine sum_congr rfl fun h _ => ?_
    simp_rw [mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    split_ifs
    · rw [gaugeFactor_eq_successor hω hsign hk]
      ring
    · ring
  have hsumm : ∀ h ∈ shellShifts N w, Summable fun k : ℕ =>
      2 * (ω k * vonMangoldtAtom k * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        if (n : ℤ) = k * m + h then
          (1 - ω (k * m) * ω n) * x m * x n *
            bumpCorr g (Real.log k - (Real.log n - Real.log m)) else 0) := by
    intro h _
    refine summable_of_ne_finset_zero (s := range (⌈(N : ℝ) * Real.exp w⌉₊ + 1)) fun k hk => ?_
    have hk' : ⌈(N : ℝ) * Real.exp w⌉₊ + 1 ≤ k := by simpa only [mem_range, not_lt] using hk
    have hlt : (N : ℝ) * Real.exp w < k := by
      have hc := Nat.le_ceil ((N : ℝ) * Real.exp w)
      have hkR : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk'
      push_cast at hkR
      linarith only [hc, hkR]
    have hk1 : 1 ≤ k := by
      have : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hlt
      exact_mod_cast this
    have hzero : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N,
        (if (n : ℤ) = k * m + h then
          (1 - ω (k * m) * ω n) * x m * x n *
            bumpCorr g (Real.log k - (Real.log n - Real.log m)) else 0) = 0 := by
      intro m hm n hn
      split_ifs with hh
      · by_cases hβ : bumpCorr g (Real.log k - (Real.log n - Real.log m)) = 0
        · rw [hβ, mul_zero]
        · exfalso
          obtain ⟨hm1, -⟩ := mem_Icc.mp hm
          obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
          have hb := (abs_shift_le_of_bumpCorr_ne_zero hgsupp hk1 hm1 hn1 hβ).1
          have hkm : (k : ℝ) * m ≤ n * Real.exp w := by
            have := (abs_le.mp hb).1
            linarith only [this]
          have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
          have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith only [hkm, hm1', hnN', hlt, Real.exp_pos w, hk0]
      · rfl
    rw [sum_eq_zero fun m hm => sum_eq_zero fun n hn => hzero m hm n hn, mul_zero, mul_zero]
  rw [tsum_congr hterm, Summable.tsum_finsetSum hsumm]
  refine sum_congr rfl fun h _ => ?_
  rw [twinShellForm, tsum_mul_left]

/-- **Agreeing shifts are invisible**: if the gauge agrees with its `h`-successor on every product
`km ≤ N`, the `h`-shell of the twin defect vanishes. -/
theorem twinShellForm_eq_zero_of_agree {N : ℕ} {h : ℤ} (x : ℕ → ℝ)
    (hagree : ∀ ℓ n : ℕ, 1 ≤ n → n ≤ N → (n : ℤ) = ℓ + h → ω ℓ * ω n = 1) :
    twinShellForm g N ω h x = 0 := by
  unfold twinShellForm
  rw [show (∑' k : ℕ, ω k * vonMangoldtAtom k * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      if (n : ℤ) = k * m + h then
        (1 - ω (k * m) * ω n) * x m * x n *
          bumpCorr g (Real.log k - (Real.log n - Real.log m)) else 0) = 0 from ?_, mul_zero]
  refine (tsum_congr fun k => ?_).trans tsum_zero
  rw [sum_eq_zero fun m _ => sum_eq_zero fun n hn => ?_, mul_zero]
  split_ifs with hh
  · obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    rw [hagree (k * m) n hn1 hnN (by push_cast; exact hh)]
    ring
  · rfl

/-- **Below the spacing the twins coincide**: with no shifts the twin's prime form is `ζ`'s prime
form of the gauged vector. -/
theorem twistedPrimeSum_eq_of_shellRange_eq_zero (hω : ∀ a b, ω (a * b) = ω a * ω b)
    (hsign : ∀ n, 0 < n → ω n = 1 ∨ ω n = -1) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w) {N : ℕ} (hH : shellRange N w = 0)
    (x : ℕ → ℝ) :
    twistedPrimeSum ω (atomicTest N x g) = primeSum (atomicTest N (fun n => ω n * x n) g) := by
  have h := twistedPrimeSum_sub_primeSum_eq_sum_twinShellForm hω hsign hg hgc hgsupp hw N x
  rw [shellShifts, hH] at h
  simp only [CharP.cast_eq_zero, neg_zero, Icc_self, erase_singleton, sum_empty] at h
  linarith only [h]

end GaloisForLFunctions.SuccessorShellArithmetic

#print axioms GaloisForLFunctions.SuccessorShellArithmetic.twistedPrimeSum_sub_primeSum_eq_sum_twinShellForm
#print axioms GaloisForLFunctions.SuccessorShellArithmetic.twinShellForm_eq_zero_of_agree
