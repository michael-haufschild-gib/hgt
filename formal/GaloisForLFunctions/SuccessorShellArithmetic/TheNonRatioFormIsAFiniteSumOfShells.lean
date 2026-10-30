import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap

/-!
# The non-ratio form is a finite sum of successor shells

At width `w` the non-ratio prime form pairs an atom `m`, a prime power `k` and a partner `n` with
`n ≠ km` and `|log(km/n)| ≤ w`. Each such pair has a unique **shift** `h = n − km ∈ ℤ ∖ {0}`; the
pairs of one shift form the **successor shell** `Sh_h`.

* **One orientation suffices** (`nonRatioLag_eq_two_mul_upward`): the two orientations of a
  non-ratio lag carry the same pairs, `nonRatioLag_k = 2 Σ_{n ≠ km} x_m x_n β(log k − log(n/m))`.
* **Shift bound** (`abs_shift_le_of_bumpCorr_ne_zero`): a pair of nonzero weight has
  `|n − km| ≤ min(n, km)(e^w − 1)`.
* **Shell decomposition** (`nonRatioForm_eq_sum_shellForm`): `NR = Σ_{0 < |h| ≤ H} Sh_h` with
  `H = ⌊N(e^w − 1)⌋`. At `w = c/N` there are at most `2c e^{c/N}` shells (`card_shellShifts_le`),
  and exactly `2⌊c⌋` at every large horizon (`eventually_shellRange_eq_floor`).
* **Top band** (`shellLag_eq_zero_of_vanish_on_band`): the shell of shift `h` reads only partners
  `n ≥ |h|/(e^w − 1)`; at `w = c/N` this is `n ≥ |h|N/(c e^{c/N})`.
* **Below the spacing** (`nonRatioForm_eq_zero_of_shellRange_eq_zero`): when `N(e^w − 1) < 1` there
  are no shells and the non-ratio form vanishes.
-/

noncomputable section

open Finset RHTower

namespace GaloisForLFunctions.SuccessorShellArithmetic

open SpacingScaleHarmonicAnalysis

variable {g : ℝ → ℝ} {w : ℝ}

/-- The shell of order `k` and shift `h`: the pairs `n = km + h`, weighted by the atom
autocorrelation `β(log k − log(n/m))`. -/
def shellLag (g : ℝ → ℝ) (N k : ℕ) (h : ℤ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
    if (n : ℤ) = k * m + h then
      x m * x n * bumpCorr g (Real.log k - (Real.log n - Real.log m)) else 0

/-- The **successor-shell form** of shift `h`: `Sh_h(x) = 2 Σ_k Λ(k) k^{−1/2} shellLag_{k,h}(x)`. -/
def shellForm (g : ℝ → ℝ) (N : ℕ) (h : ℤ) (x : ℕ → ℝ) : ℝ :=
  2 * ∑' k : ℕ, vonMangoldtAtom k * shellLag g N k h x

/-- The largest shift present at width `w`: `H = ⌊N(e^w − 1)⌋`. -/
def shellRange (N : ℕ) (w : ℝ) : ℕ :=
  ⌊(N : ℝ) * (Real.exp w - 1)⌋₊

/-- The shifts `0 < |h| ≤ H`. -/
def shellShifts (N : ℕ) (w : ℝ) : Finset ℤ :=
  (Icc (-(shellRange N w : ℤ)) (shellRange N w)).erase 0

/-! ### One orientation -/

/-- **One orientation suffices**: the downward terms of a non-ratio lag are its upward terms with
the atoms exchanged. -/
theorem nonRatioLag_eq_two_mul_upward (N k : ℕ) (x : ℕ → ℝ) :
    nonRatioLag g N k x = 2 * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (if n = k * m then 0 else
        x m * x n * bumpCorr g (Real.log k - (Real.log n - Real.log m))) := by
  have hdown : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n *
      (if m = k * n then 0 else bumpCorr g (-Real.log k - (Real.log n - Real.log m)))) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if n = k * m then 0 else
          x m * x n * bumpCorr g (Real.log k - (Real.log n - Real.log m))) := by
    rw [sum_comm]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    split_ifs with h
    · ring
    · rw [show -Real.log k - (Real.log m - Real.log n) =
        -(Real.log k - (Real.log n - Real.log m)) by ring, bumpCorr_neg]
      ring
  have hup : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n *
      (if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (if n = k * m then 0 else
          x m * x n * bumpCorr g (Real.log k - (Real.log n - Real.log m))) :=
    sum_congr rfl fun m _ => sum_congr rfl fun n _ => by split_ifs <;> ring
  unfold nonRatioLag
  simp only [mul_add, sum_add_distrib]
  rw [hdown, hup]
  ring

/-! ### The shift bound -/

/-- **Shift bound.** A pair of nonzero weight has `|n − km| ≤ n(e^w − 1)` and
`|n − km| ≤ km(e^w − 1)`. -/
theorem abs_shift_le_of_bumpCorr_ne_zero (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {k m n : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hβ : bumpCorr g (Real.log k - (Real.log n - Real.log m)) ≠ 0) :
    |(n : ℝ) - k * m| ≤ n * (Real.exp w - 1) ∧
      |(n : ℝ) - k * m| ≤ k * m * (Real.exp w - 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hkm0 : (0 : ℝ) < k * m := mul_pos hk0 hm0
  have hlog : |Real.log k - (Real.log n - Real.log m)| ≤ w :=
    not_lt.mp fun hlt => hβ (bumpCorr_eq_zero hgsupp hlt)
  have hkm : Real.log (k * m) = Real.log k + Real.log m := Real.log_mul hk0.ne' hm0.ne'
  obtain ⟨hlo, hhi⟩ := abs_le.mp hlog
  -- `n ≤ km e^w` and `km ≤ n e^w`
  have h1 : (n : ℝ) ≤ k * m * Real.exp w := by
    have : Real.log n ≤ Real.log (k * m) + w := by rw [hkm]; linarith only [hlo]
    rw [← Real.exp_le_exp, Real.exp_log hn0, Real.exp_add, Real.exp_log hkm0] at this
    exact this
  have h2 : (k : ℝ) * m ≤ n * Real.exp w := by
    have : Real.log (k * m) ≤ Real.log n + w := by rw [hkm]; linarith only [hhi]
    rw [← Real.exp_le_exp, Real.exp_log hkm0, Real.exp_add, Real.exp_log hn0] at this
    exact this
  have he : 1 ≤ Real.exp w := by
    have := Real.add_one_le_exp w
    have hw : 0 ≤ w := le_trans (abs_nonneg _) hlog
    linarith only [this, hw]
  have he0 : 0 ≤ Real.exp w - 1 := sub_nonneg.mpr he
  rcases le_total (n : ℝ) (k * m) with hle | hle
  · rw [abs_of_nonpos (by linarith only [hle])]
    have hA : -((n : ℝ) - k * m) ≤ n * (Real.exp w - 1) := by linarith only [h2]
    exact ⟨hA, hA.trans (mul_le_mul_of_nonneg_right hle he0)⟩
  · rw [abs_of_nonneg (by linarith only [hle])]
    have hB : (n : ℝ) - k * m ≤ k * m * (Real.exp w - 1) := by linarith only [h1]
    exact ⟨hB.trans (mul_le_mul_of_nonneg_right hle he0), hB⟩

/-! ### The shell decomposition -/

private theorem shift_mem_shellShifts (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N k m n : ℕ} (hk : 1 ≤ k) (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hne : n ≠ k * m)
    (hβ : bumpCorr g (Real.log k - (Real.log n - Real.log m)) ≠ 0) :
    (n : ℤ) - k * m ∈ shellShifts N w := by
  have hm1 := (mem_Icc.mp hm).1
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hb := (abs_shift_le_of_bumpCorr_ne_zero hgsupp hk hm1 hn1 hβ).1
  have he : 0 ≤ Real.exp w - 1 := by
    have hw : 0 ≤ w := by
      by_contra hw
      exact hβ (bumpCorr_eq_zero hgsupp (lt_of_lt_of_le (not_le.mp hw) (abs_nonneg _)))
    linarith only [Real.add_one_le_exp w, hw]
  have hbN : |(n : ℝ) - k * m| ≤ (N : ℝ) * (Real.exp w - 1) :=
    hb.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) he)
  have hfloor : |(n : ℤ) - k * m| ≤ (shellRange N w : ℤ) := by
    set z : ℤ := (n : ℤ) - k * m with hz
    have hcast : (((|z|).toNat : ℕ) : ℝ) = |(n : ℝ) - k * m| := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg z), Int.cast_abs, hz]
      push_cast
      rfl
    have hnat : (|z|).toNat ≤ shellRange N w := by
      apply Nat.le_floor
      rw [hcast]
      exact hbN
    have := Int.toNat_of_nonneg (abs_nonneg z)
    omega
  refine mem_erase.mpr ⟨fun h0 => hne ?_, mem_Icc.mpr (abs_le.mp hfloor)⟩
  exact_mod_cast (sub_eq_zero.mp h0)

/-- For each prime power, the upward non-ratio terms are the sum of their shells. -/
theorem upward_eq_sum_shellLag (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N k : ℕ} (hk : 1 ≤ k) (x : ℕ → ℝ) :
    (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
      (if n = k * m then 0 else
        x m * x n * bumpCorr g (Real.log k - (Real.log n - Real.log m)))) =
      ∑ h ∈ shellShifts N w, shellLag g N k h x := by
  unfold shellLag
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
    · rw [if_pos (shift_mem_shellShifts hgsupp hk hm hn hne hβ)]

/-- A shell of order `k` is empty once `k > N e^w`. -/
theorem shellLag_eq_zero_of_lt (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N k : ℕ} (hk : (N : ℝ) * Real.exp w < k) (h : ℤ) (x : ℕ → ℝ) :
    shellLag g N k h x = 0 := by
  have hk1 : 1 ≤ k := by
    have : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
    exact_mod_cast this
  unfold shellLag
  refine sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_
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
      nlinarith only [hkm, hm1', hnN', hk, Real.exp_pos w, hk0]
  · rfl

private theorem summable_shellLag (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (N : ℕ) (h : ℤ) (x : ℕ → ℝ) :
    Summable fun k : ℕ => vonMangoldtAtom k * shellLag g N k h x := by
  refine summable_of_ne_finset_zero (s := range (⌈(N : ℝ) * Real.exp w⌉₊ + 1)) fun k hk => ?_
  have hk' : ⌈(N : ℝ) * Real.exp w⌉₊ + 1 ≤ k := by simpa only [mem_range, not_lt] using hk
  have hlt : (N : ℝ) * Real.exp w < k := by
    have hc := Nat.le_ceil ((N : ℝ) * Real.exp w)
    have hkR : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk'
    push_cast at hkR
    linarith only [hc, hkR]
  rw [shellLag_eq_zero_of_lt hgsupp hlt, mul_zero]

/-- **Shell decomposition.** The non-ratio prime form is the sum of the successor-shell forms of
the shifts `0 < |h| ≤ ⌊N(e^w − 1)⌋`. -/
theorem nonRatioForm_eq_sum_shellForm (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (N : ℕ) (x : ℕ → ℝ) :
    nonRatioForm g N x = ∑ h ∈ shellShifts N w, shellForm g N h x := by
  have hterm : ∀ k : ℕ, vonMangoldtAtom k * nonRatioLag g N k x =
      ∑ h ∈ shellShifts N w, 2 * (vonMangoldtAtom k * shellLag g N k h x) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [vonMangoldtAtom]
    · rw [nonRatioLag_eq_two_mul_upward, upward_eq_sum_shellLag hgsupp hk, mul_sum, mul_sum]
      exact sum_congr rfl fun h _ => by ring
  unfold nonRatioForm shellForm
  rw [tsum_congr hterm, Summable.tsum_finsetSum fun h _ =>
    (summable_shellLag hgsupp N h x).mul_left 2]
  exact sum_congr rfl fun h _ => tsum_mul_left

/-! ### Counting the shells -/

theorem card_shellShifts (N : ℕ) (w : ℝ) : (shellShifts N w).card = 2 * shellRange N w := by
  have h0 : (0 : ℤ) ∈ Icc (-(shellRange N w : ℤ)) (shellRange N w) := by
    simp only [mem_Icc]; omega
  rw [shellShifts, card_erase_of_mem h0, Int.card_Icc]
  omega

/-- `N(e^{c/N} − 1) ≤ c e^{c/N}`: at width `c/N` the shifts are at most `c e^{c/N}`. -/
theorem shellRange_le {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 ≤ c) :
    (shellRange N (c / N) : ℝ) ≤ c * Real.exp (c / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ c / N := div_nonneg hc hN0.le
  -- `e^x − 1 ≤ x e^x`, from `1 − x ≤ e^{−x}`
  have hkey : Real.exp (c / N) - 1 ≤ c / N * Real.exp (c / N) := by
    have h := Real.add_one_le_exp (-(c / N))
    have hmul : Real.exp (-(c / N)) * Real.exp (c / N) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith only [h, hmul, Real.exp_pos (c / N)]
  have hfl : (shellRange N (c / N) : ℝ) ≤ (N : ℝ) * (Real.exp (c / N) - 1) := by
    unfold shellRange
    apply Nat.floor_le
    have := Real.add_one_le_exp (c / N)
    exact mul_nonneg hN0.le (by linarith only [this, hx])
  calc
    _ ≤ (N : ℝ) * (Real.exp (c / N) - 1) := hfl
    _ ≤ (N : ℝ) * (c / N * Real.exp (c / N)) := mul_le_mul_of_nonneg_left hkey hN0.le
    _ = c * Real.exp (c / N) := by field_simp

/-- At width `c/N` there are at most `2c e^{c/N}` successor shells. -/
theorem card_shellShifts_le {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 ≤ c) :
    ((shellShifts N (c / N)).card : ℝ) ≤ 2 * c * Real.exp (c / N) := by
  rw [card_shellShifts]
  push_cast
  linarith only [shellRange_le hN hc]

/-- **Exact shell count.** At overlap `c > 0` and every large horizon the shifts are exactly
`0 < |h| ≤ ⌊c⌋`: `c ≤ N(e^{c/N} − 1) ≤ c e^{c/N} < ⌊c⌋ + 1`. -/
theorem eventually_shellRange_eq_floor {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in Filter.atTop, shellRange N (c / N) = ⌊c⌋₊ := by
  have hlim : Filter.Tendsto (fun N : ℕ => c * Real.exp (c / N)) Filter.atTop (nhds c) := by
    have h := ((Real.continuous_exp.tendsto 0).comp
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds c)).div_atTop
        tendsto_natCast_atTop_atTop)).const_mul c
    simpa only [Function.comp_def, Real.exp_zero, mul_one] using h
  filter_upwards [hlim.eventually (gt_mem_nhds (Nat.lt_floor_add_one c)),
    Filter.eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  apply le_antisymm
  · apply Nat.le_of_lt_succ
    rw [shellRange, Nat.floor_lt (mul_nonneg hN0.le (by
      linarith only [Real.add_one_le_exp (c / N), div_nonneg hc.le hN0.le]))]
    push_cast
    exact lt_of_le_of_lt (by exact_mod_cast shellRange_le hN1 hc.le |>.trans_eq' (by
      unfold shellRange; rfl) |> fun _ => (by
        have hkey : Real.exp (c / N) - 1 ≤ c / N * Real.exp (c / N) := by
          have h1 := Real.add_one_le_exp (-(c / N))
          have hmul : Real.exp (-(c / N)) * Real.exp (c / N) = 1 := by
            rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
          nlinarith only [h1, hmul, Real.exp_pos (c / N)]
        calc (N : ℝ) * (Real.exp (c / N) - 1) ≤ N * (c / N * Real.exp (c / N)) :=
              mul_le_mul_of_nonneg_left hkey hN0.le
          _ = c * Real.exp (c / N) := by field_simp)) hN
  · unfold shellRange
    apply Nat.floor_le_floor
    have h := Real.add_one_le_exp (c / N)
    calc c = N * (c / N) := by field_simp
      _ ≤ N * (Real.exp (c / N) - 1) := mul_le_mul_of_nonneg_left (by linarith only [h]) hN0.le

/-! ### The top band -/

/-- **Top band.** The shell of shift `h` reads only partners `n` with `|h| ≤ n(e^w − 1)`. -/
theorem shellLag_eq_zero_of_vanish_on_band (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N k : ℕ} (hk : 1 ≤ k) (h : ℤ) {x : ℕ → ℝ}
    (hx : ∀ n : ℕ, (|h| : ℝ) ≤ n * (Real.exp w - 1) → x n = 0) :
    shellLag g N k h x = 0 := by
  unfold shellLag
  refine sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_
  split_ifs with hh
  · by_cases hβ : bumpCorr g (Real.log k - (Real.log n - Real.log m)) = 0
    · rw [hβ, mul_zero]
    · have hb := (abs_shift_le_of_bumpCorr_ne_zero hgsupp hk (mem_Icc.mp hm).1
        (mem_Icc.mp hn).1 hβ).1
      have hhR : (h : ℝ) = (n : ℝ) - k * m := by
        have : (h : ℤ) = (n : ℤ) - k * m := by linarith only [hh]
        exact_mod_cast this
      rw [hx n (by rw [hhR]; exact hb), mul_zero, zero_mul]
  · rfl

/-- At width `c/N` the shell of shift `h` reads only `n ≥ |h|N/(c e^{c/N})`. -/
theorem shellForm_eq_zero_of_vanish_on_top_band {N : ℕ} {c : ℝ}
    (hgsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0) (hN : 1 ≤ N) (hc : 0 < c) (h : ℤ) {x : ℕ → ℝ}
    (hx : ∀ n : ℕ, (|h| : ℝ) * N / (c * Real.exp (c / N)) ≤ n → x n = 0) :
    shellForm g N h x = 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hband : ∀ n : ℕ, (|h| : ℝ) ≤ n * (Real.exp (c / N) - 1) → x n = 0 := by
    intro n hn
    apply hx n
    have hkey : Real.exp (c / N) - 1 ≤ c / N * Real.exp (c / N) := by
      have h1 := Real.add_one_le_exp (-(c / N))
      have hmul : Real.exp (-(c / N)) * Real.exp (c / N) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      nlinarith only [h1, hmul, Real.exp_pos (c / N)]
    have hpos : 0 < c * Real.exp (c / N) := mul_pos hc (Real.exp_pos _)
    rw [div_le_iff₀ hpos]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc
      (|h| : ℝ) * N ≤ n * (Real.exp (c / N) - 1) * N := mul_le_mul_of_nonneg_right hn hN0.le
      _ ≤ n * (c / N * Real.exp (c / N)) * N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hn0) hN0.le
      _ = n * (c * Real.exp (c / N)) := by field_simp
  unfold shellForm
  rw [show (∑' k : ℕ, vonMangoldtAtom k * shellLag g N k h x) = 0 from ?_, mul_zero]
  refine (tsum_congr fun k => ?_).trans tsum_zero
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [vonMangoldtAtom]
  · rw [shellLag_eq_zero_of_vanish_on_band hgsupp hk h hband, mul_zero]

/-- **Below the spacing** there are no shifts, and the non-ratio form vanishes. -/
theorem nonRatioForm_eq_zero_of_shellRange_eq_zero (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    {N : ℕ} (hH : shellRange N w = 0) (x : ℕ → ℝ) : nonRatioForm g N x = 0 := by
  rw [nonRatioForm_eq_sum_shellForm hgsupp, shellShifts, hH]
  simp

end GaloisForLFunctions.SuccessorShellArithmetic

#print axioms GaloisForLFunctions.SuccessorShellArithmetic.nonRatioForm_eq_sum_shellForm
#print axioms GaloisForLFunctions.SuccessorShellArithmetic.card_shellShifts_le
#print axioms GaloisForLFunctions.SuccessorShellArithmetic.shellForm_eq_zero_of_vanish_on_top_band
