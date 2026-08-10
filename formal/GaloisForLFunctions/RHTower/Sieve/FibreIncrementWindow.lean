import GaloisForLFunctions.RHTower.Sieve.FibreWindowVanish

/-!
# The shift-uniform majorant sums to `O(h)` across the window

Across `[⌊√x/2⌋ − 2, ⌈√x + h⌉ + 3]`:

* `kernelDiff` lies in `[−16h, 4h]`, so each of its two variation terms is at most `40h`;
* the overshoot telescopes to its value at the left edge, `≤ 4h + 8`;
* the shortfall telescopes to its value at the right edge, `≤ h + 6`.

Hence the total is `85h + 14`.  Every one of these is `O(h)` only because of the truncation: the
untruncated endpoints each swing by `≍ √x` across the same window.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The length of the window. -/
def fibreWinLen (x h : ℝ) : ℕ := fibreWinHi x h + 1 - fibreWinLo x

/-- On the window the smooth kernel is at most `4h`. -/
theorem kernelDiff_le_of_window {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {k n : ℕ}
    (hn : Real.sqrt x / 4 ≤ (n : ℝ)) (hs : (8 : ℝ) ≤ Real.sqrt x) :
    kernelDiff x h k n ≤ 4 * h := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hc : (0 : ℝ) ≤ x + h * Real.sqrt x := by
    have : (0 : ℝ) ≤ h * Real.sqrt x := mul_nonneg hh (Real.sqrt_nonneg x)
    linarith
  have hstep : (x + h * Real.sqrt x) / ((n : ℝ) + (k : ℝ)) ≤ (x + h * Real.sqrt x) / (n : ℝ) := by
    refine div_le_div_of_nonneg_left hc hn0 (by linarith)
  have hsplit : (x + h * Real.sqrt x) / (n : ℝ) - x / (n : ℝ)
      = h * Real.sqrt x / (n : ℝ) := by
    field_simp
    ring
  have hfin : h * Real.sqrt x / (n : ℝ) ≤ 4 * h := by
    rw [div_le_iff₀ hn0]
    nlinarith [hn, hh, hs]
  rw [kernelDiff]
  linarith

/-- On the window the smooth kernel is at least `−16h`. -/
theorem neg_le_kernelDiff_of_window {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) {k n : ℕ}
    (hkh : (k : ℝ) ≤ h) (hn : Real.sqrt x / 4 ≤ (n : ℝ)) (hs : (8 : ℝ) ≤ Real.sqrt x)
    (hsq : Real.sqrt x * Real.sqrt x = x) :
    -(16 * h) ≤ kernelDiff x h k n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hnk0 : (0 : ℝ) < (n : ℝ) + (k : ℝ) := by linarith
  have hlow : x / ((n : ℝ) + (k : ℝ)) ≤ (x + h * Real.sqrt x) / ((n : ℝ) + (k : ℝ)) := by
    gcongr
    nlinarith [mul_nonneg hh (Real.sqrt_nonneg x)]
  have hgap : x / (n : ℝ) - x / ((n : ℝ) + (k : ℝ))
      = x * (k : ℝ) / ((n : ℝ) * ((n : ℝ) + (k : ℝ))) := by
    field_simp
    ring
  have hbound : x * (k : ℝ) / ((n : ℝ) * ((n : ℝ) + (k : ℝ))) ≤ 16 * h := by
    rw [div_le_iff₀ (by positivity)]
    have hnk4 : Real.sqrt x / 4 ≤ (n : ℝ) + (k : ℝ) := by linarith
    have hprod : (Real.sqrt x / 4) * (Real.sqrt x / 4) ≤ (n : ℝ) * ((n : ℝ) + (k : ℝ)) := by
      refine mul_le_mul hn hnk4 (by linarith) (by linarith)
    have hx16 : x / 16 ≤ (n : ℝ) * ((n : ℝ) + (k : ℝ)) := by nlinarith [hprod, hsq]
    have hstep1 : 16 * h * (x / 16) ≤ 16 * h * ((n : ℝ) * ((n : ℝ) + (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hx16 (by linarith)
    have hstep2 : x * (k : ℝ) ≤ x * h := mul_le_mul_of_nonneg_left hkh hx
    linarith
  rw [kernelDiff]
  linarith

/-- **The variation of the smooth kernel across the window.** -/
theorem kernelDiff_window_variation_le {x h : ℝ} (hx : 64 ≤ x) (hh : 0 ≤ h) {k : ℕ} (hk : 1 ≤ k)
    (hkh : (k : ℝ) ≤ h) (jlo Nw : ℕ) (hjlo : Real.sqrt x / 4 ≤ (jlo : ℝ) + 1) :
    ∑ i ∈ Finset.range Nw, |kernelDiff x h k (jlo + i + 2) - kernelDiff x h k (jlo + i + 1)|
      ≤ 2 * (4 * h - -(16 * h)) := by
  have hs : (8 : ℝ) ≤ Real.sqrt x := eight_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  obtain ⟨c, hcN, hup, hdown⟩ :=
    kernelDiff_bimonotone (x := x) (h := h) (by linarith) hh hk (jlo + Nw)
  have hqc : QuasiConcaveOn (fun j => kernelDiff x h k (j + 1)) (jlo + Nw) :=
    quasiConcaveOn_of_bimonotone hcN hup hdown
  have hqc' : QuasiConcaveOn (fun i => kernelDiff x h k (jlo + i + 1)) Nw :=
    quasiConcaveOn_shift (w := fun j => kernelDiff x h k (j + 1)) (n₀ := jlo) (N := Nw) hqc
  have hmem : ∀ i : ℕ, Real.sqrt x / 4 ≤ ((jlo + i + 1 : ℕ) : ℝ) := by
    intro i
    have : ((jlo : ℕ) : ℝ) + 1 ≤ ((jlo + i + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) i]
    linarith
  have hbase := variation_le_two_range_of_quasiConcave hqc' (L := -(16 * h)) (U := 4 * h)
    (fun i _ => neg_le_kernelDiff_of_window (by linarith) hh hkh (hmem i) hs hsq)
    (fun i _ => kernelDiff_le_of_window (by linarith) hh (hmem i) hs)
  exact hbase

/-- **The overshoot telescopes across the window.** -/
theorem sum_fibreOver_window_le {x h : ℝ} (hx : 64 ≤ x) (hh : 0 ≤ h) (jlo Nw : ℕ)
    (hjlo : Real.sqrt x / 2 - 1 ≤ (jlo : ℝ) + 2) :
    ∑ i ∈ Finset.range Nw,
        (fibreOver x h 1 (jlo + i + 1) - fibreOver x h 1 (jlo + i + 2)) ≤ 4 * h + 8 := by
  have hs : (8 : ℝ) ≤ Real.sqrt x := eight_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have htel : ∑ i ∈ Finset.range Nw,
      (fibreOver x h 1 (jlo + i + 1) - fibreOver x h 1 (jlo + i + 2))
      = fibreOver x h 1 (jlo + 0 + 1) - fibreOver x h 1 (jlo + Nw + 1) :=
    Finset.sum_range_sub' (fun i => fibreOver x h 1 (jlo + i + 1)) Nw
  rw [htel]
  have htail : 0 ≤ fibreOver x h 1 (jlo + Nw + 1) := fibreOver_nonneg x h 1 (jlo + Nw + 1)
  have hcast : (((jlo + 0 + 1 : ℕ)) : ℝ) + ((1 : ℕ) : ℝ) = (jlo : ℝ) + 2 := by push_cast; ring
  have hhead : fibreOver x h 1 (jlo + 0 + 1)
      = max ((x + h * Real.sqrt x) / ((jlo : ℝ) + 2) - 2 * Real.sqrt x) 0 := by
    rw [fibreOver, hcast]
  rw [hhead]
  have hm : (0 : ℝ) < (jlo : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) jlo]
  have hbnd : (x + h * Real.sqrt x) / ((jlo : ℝ) + 2) - 2 * Real.sqrt x ≤ 4 * h + 8 := by
    rw [sub_le_iff_le_add, div_le_iff₀ hm]
    nlinarith [hjlo, hs, hsq, hh]
  have := max_le hbnd (by linarith : (0:ℝ) ≤ 4 * h + 8)
  linarith

/-- **The shortfall telescopes across the window.** -/
theorem sum_fibreUnder_window_le {x h : ℝ} (hx : 64 ≤ x) (hh : 0 ≤ h) (jlo Nw : ℕ)
    (hhi : (((jlo + Nw + 1 : ℕ)) : ℝ) ≤ Real.sqrt x + h + 6) :
    ∑ i ∈ Finset.range Nw,
        (fibreUnder x (jlo + i + 2) - fibreUnder x (jlo + i + 1)) ≤ h + 6 := by
  have hs : (8 : ℝ) ≤ Real.sqrt x := eight_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have htel : ∑ i ∈ Finset.range Nw,
      (fibreUnder x (jlo + i + 2) - fibreUnder x (jlo + i + 1))
      = fibreUnder x (jlo + Nw + 1) - fibreUnder x (jlo + 0 + 1) :=
    Finset.sum_range_sub (fun i => fibreUnder x (jlo + i + 1)) Nw
  rw [htel]
  have hhead : 0 ≤ fibreUnder x (jlo + 0 + 1) := fibreUnder_nonneg x (jlo + 0 + 1)
  have hn1 : (1 : ℝ) ≤ (((jlo + Nw + 1 : ℕ)) : ℝ) := by
    have : (1 : ℕ) ≤ jlo + Nw + 1 := by omega
    exact_mod_cast this
  have hbnd : Real.sqrt x - x / (((jlo + Nw + 1 : ℕ)) : ℝ) ≤ h + 6 := by
    have hdiv : x / (Real.sqrt x + h + 6) ≤ x / (((jlo + Nw + 1 : ℕ)) : ℝ) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) hhi
    have hval : Real.sqrt x - x / (Real.sqrt x + h + 6) ≤ h + 6 := by
      rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by linarith)]
      nlinarith [hs, hsq, hh]
    linarith
  have hmax := max_le hbnd (by linarith : (0:ℝ) ≤ h + 6)
  rw [fibreUnder]
  linarith

/-- **The shift-uniform majorant sums to `O(h)` across the window.** -/
theorem sum_fibreIncrRaw_window_le {x h : ℝ} (hx : 64 ≤ x) (hh : 0 ≤ h) {K : ℕ} (hK : 1 ≤ K)
    (hKh : (K : ℝ) ≤ h) (jlo Nw : ℕ)
    (hjlo4 : Real.sqrt x / 4 ≤ (jlo : ℝ) + 1)
    (hjlo2 : Real.sqrt x / 2 - 1 ≤ (jlo : ℝ) + 2)
    (hhi : (((jlo + Nw + 1 : ℕ)) : ℝ) ≤ Real.sqrt x + h + 6) :
    ∑ i ∈ Finset.range Nw, fibreIncrRaw x h K (jlo + i) ≤ 85 * h + 14 := by
  have hsplit : ∑ i ∈ Finset.range Nw, fibreIncrRaw x h K (jlo + i)
      = ((∑ i ∈ Finset.range Nw,
            |kernelDiff x h 1 (jlo + i + 2) - kernelDiff x h 1 (jlo + i + 1)|)
          + (∑ i ∈ Finset.range Nw,
            |kernelDiff x h K (jlo + i + 2) - kernelDiff x h K (jlo + i + 1)|)
          + (∑ i ∈ Finset.range Nw,
            (fibreOver x h 1 (jlo + i + 1) - fibreOver x h 1 (jlo + i + 2))))
        + ∑ i ∈ Finset.range Nw,
            (fibreUnder x (jlo + i + 2) - fibreUnder x (jlo + i + 1)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [hsplit]
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hone : ((1 : ℕ) : ℝ) ≤ h := by push_cast; linarith
  have hv1 := kernelDiff_window_variation_le hx hh (le_refl 1) hone jlo Nw hjlo4
  have hv2 := kernelDiff_window_variation_le hx hh hK hKh jlo Nw hjlo4
  have hv3 := sum_fibreOver_window_le hx hh jlo Nw hjlo2
  have hv4 := sum_fibreUnder_window_le hx hh jlo Nw hhi
  linarith

/-- The shift-uniform increment majorant, cut off outside the window. -/
def fibreIncr (x h : ℝ) (K j : ℕ) : ℝ :=
  if fibreWinLo x ≤ j ∧ j < fibreWinLo x + fibreWinLen x h then fibreIncrRaw x h K j else 0

theorem fibreIncr_nonneg {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (K j : ℕ) :
    0 ≤ fibreIncr x h K j := by
  rw [fibreIncr]
  split
  · exact fibreIncrRaw_nonneg hx hh K j
  · exact le_rfl

theorem fibreWinLo_le_succ_fibreWinHi {x h : ℝ} (hx : 64 ≤ x) (hh : 0 ≤ h) :
    fibreWinLo x ≤ fibreWinHi x h + 1 := by
  have hs : (8 : ℝ) ≤ Real.sqrt x := eight_le_sqrt hx
  have hkey : ⌊Real.sqrt x / 2⌋₊ ≤ ⌈Real.sqrt x + h⌉₊ := by
    have h1 : ((⌊Real.sqrt x / 2⌋₊ : ℕ) : ℝ) ≤ Real.sqrt x / 2 := Nat.floor_le (by positivity)
    have h2 : Real.sqrt x + h ≤ ((⌈Real.sqrt x + h⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have : ((⌊Real.sqrt x / 2⌋₊ : ℕ) : ℝ) ≤ ((⌈Real.sqrt x + h⌉₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  rw [fibreWinLo, fibreWinHi]
  omega

/-- **The cut-off majorant dominates every increment, at every shift.** -/
theorem abs_fibreSmooth_increment_le_fibreIncr {x h : ℝ} (hx : 64 ≤ x) (hh : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {k K : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K) (j : ℕ) :
    |fibreSmooth x h k (j + 2) - fibreSmooth x h k (j + 1)| ≤ fibreIncr x h K j := by
  rw [fibreIncr]
  split
  · exact abs_fibreSmooth_increment_le (by linarith) hh hk hkK j
  · rename_i hout
    have hzero : fibreSmooth x h k (j + 2) - fibreSmooth x h k (j + 1) = 0 := by
      rcases Nat.lt_or_ge j (fibreWinLo x) with hlow | hhigh
      · exact fibreSmooth_increment_zero_below hx k hlow
      · have hgt : fibreWinHi x h < j := by
          rw [fibreWinLen] at hout
          have hle := fibreWinLo_le_succ_fibreWinHi (x := x) (h := h) hx hh
          omega
        exact fibreSmooth_increment_zero_above hx hh hhx hk hgt
    rw [hzero]
    simp

/-- **The cut-off majorant sums to `O(h)`.** -/
theorem sum_fibreIncr_le {x h : ℝ} (hx : 64 ≤ x) (hh : 0 ≤ h) {K : ℕ} (hK : 1 ≤ K)
    (hKh : (K : ℝ) ≤ h) (m : ℕ) :
    ∑ j ∈ Finset.range m, fibreIncr x h K j ≤ 85 * h + 14 := by
  classical
  have hs : (8 : ℝ) ≤ Real.sqrt x := eight_le_sqrt hx
  set jlo := fibreWinLo x with hjlodef
  set Nw := fibreWinLen x h with hNwdef
  -- the cut-off sum is at most the window sum
  have hstep1 : ∑ j ∈ Finset.range m, fibreIncr x h K j
      ≤ ∑ j ∈ Finset.Ico jlo (jlo + Nw), fibreIncrRaw x h K j := by
    have hfilter : ∑ j ∈ Finset.range m, fibreIncr x h K j
        = ∑ j ∈ (Finset.range m).filter (fun j => jlo ≤ j ∧ j < jlo + Nw),
            fibreIncrRaw x h K j := by
      rw [Finset.sum_filter]
      rfl
    rw [hfilter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hj ⊢
      exact hj.2
    · intro j _ _
      exact fibreIncrRaw_nonneg (by linarith) hh K j
  have hreindex : ∑ j ∈ Finset.Ico jlo (jlo + Nw), fibreIncrRaw x h K j
      = ∑ i ∈ Finset.range Nw, fibreIncrRaw x h K (jlo + i) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  rw [hreindex] at hstep1
  refine le_trans hstep1 ?_
  -- the three window hypotheses
  have hfl2 : 4 ≤ ⌊Real.sqrt x / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hjloR : ((jlo : ℕ) : ℝ) = ((⌊Real.sqrt x / 2⌋₊ : ℕ) : ℝ) - 2 := by
    rw [hjlodef, fibreWinLo, Nat.cast_sub (by omega)]
    norm_num
  have hfloor : Real.sqrt x / 2 - 1 < ((⌊Real.sqrt x / 2⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor _
  have hjlo4 : Real.sqrt x / 4 ≤ (jlo : ℝ) + 1 := by rw [hjloR]; linarith
  have hjlo2 : Real.sqrt x / 2 - 1 ≤ (jlo : ℝ) + 2 := by rw [hjloR]; linarith
  have hsum : jlo + Nw = fibreWinHi x h + 1 := by
    rw [hjlodef, hNwdef, fibreWinLen]
    have := fibreWinLo_le_succ_fibreWinHi (x := x) (h := h) hx hh
    omega
  have hceilR : ((⌈Real.sqrt x + h⌉₊ : ℕ) : ℝ) < Real.sqrt x + h + 1 :=
    Nat.ceil_lt_add_one (by linarith [Real.sqrt_nonneg x])
  have hhi : (((jlo + Nw + 1 : ℕ)) : ℝ) ≤ Real.sqrt x + h + 6 := by
    rw [hsum, fibreWinHi]
    push_cast
    linarith
  exact sum_fibreIncrRaw_window_le hx hh hK hKh jlo Nw hjlo4 hjlo2 hhi

end RHTower.Sieve

end
