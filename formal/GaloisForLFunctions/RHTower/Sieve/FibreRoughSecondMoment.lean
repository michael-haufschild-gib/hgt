import GaloisForLFunctions.RHTower.Sieve.WeightRemovalFibre
import GaloisForLFunctions.RHTower.Sieve.FibreKernelBand

/-!
# The second moment of a sparse set over the fibres

The integers a short-interval argument has to discard — those carrying no designated prime factor —
must not be bounded by the window length times their count.  Doing so costs their *density*; taking
the second moment directly costs the density *squared*, and that single factor is the difference
between `1/log h` and `(log h)^{-2}`.

The second moment over the fibres is an exact double count against the fibre kernel, and the kernel
is supported on a band of width `2h` and bounded by `2h + 1`.  So the whole cost is a shifted pair
count for the discarded set — a two-dimensional sieve problem, and nothing else.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The second moment of a set over the fibres is the double count against the kernel.** -/
theorem sum_sq_card_fibre_inter_eq {x h : ℝ} (hx : 4 ≤ x) (T : Finset ℕ) :
    ∑ a ∈ outerBlock x h, (((innerFibre x h a ∩ T).card : ℝ)) ^ 2
      = ∑ m ∈ T ∩ fibreDyadicIndex x h, ∑ n ∈ T ∩ fibreDyadicIndex x h,
          (((outerBlock x h).filter
            (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)).card : ℝ) := by
  classical
  set D : Finset ℕ := fibreDyadicIndex x h with hD
  have hcard : ∀ a ∈ outerBlock x h, ((innerFibre x h a ∩ T).card : ℝ)
      = ∑ m ∈ T ∩ D, (if m ∈ innerFibre x h a then (1 : ℝ) else 0) := by
    intro a ha
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    have hsub : innerFibre x h a ⊆ D := innerFibre_subset_fibreDyadicIndex hx ha
    apply Finset.card_bij (fun p _ => p)
    · intro p hp
      rw [Finset.mem_inter] at hp
      exact Finset.mem_filter.2 ⟨Finset.mem_inter.2 ⟨hp.2, hsub hp.1⟩, hp.1⟩
    · intro p _ q _ hpq
      exact hpq
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_inter] at hp
      exact ⟨p, Finset.mem_inter.2 ⟨hp.2, hp.1.1⟩, rfl⟩
  rw [Finset.sum_congr rfl fun a ha => by rw [hcard a ha]]
  have hexpand : ∀ a : ℕ,
      (∑ m ∈ T ∩ D, (if m ∈ innerFibre x h a then (1 : ℝ) else 0)) ^ 2
        = ∑ m ∈ T ∩ D, ∑ n ∈ T ∩ D,
            (if (m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a) then (1 : ℝ) else 0) := by
    intro a
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    by_cases hm : m ∈ innerFibre x h a <;> by_cases hn : n ∈ innerFibre x h a <;>
      simp [hm, hn]
  rw [Finset.sum_congr rfl fun a _ => hexpand a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The kernel is supported on a band of width `h`.**  Two indices sharing a fibre satisfy
`a·max ≤ x + h√x` and `a·min ≥ x` for the same outer factor `a ≥ √x`, so they differ by at most
`h√x/a ≤ h`. -/
theorem fibre_kernel_band_width {x h : ℝ} (hx : 4 ≤ x) {m n : ℕ}
    (hne : ((outerBlock x h).filter
      (fun a => m ∈ innerFibre x h a ∧ n ∈ innerFibre x h a)).Nonempty) :
    ((max m n : ℕ) : ℝ) - ((min m n : ℕ) : ℝ) ≤ h := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  obtain ⟨a, ha⟩ := hne
  rw [Finset.mem_filter] at ha
  obtain ⟨haO, hma, hna⟩ := ha
  have halo : Real.sqrt x ≤ (a : ℝ) := by
    rw [outerBlock, Finset.mem_filter] at haO
    exact haO.2.1
  have ha0 : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le hsx halo
  rw [mem_innerFibre] at hma hna
  have hcm : ((a * m : ℕ) : ℝ) = (a : ℝ) * (m : ℝ) := by push_cast; ring
  have hcn : ((a * n : ℕ) : ℝ) = (a : ℝ) * (n : ℝ) := by push_cast; ring
  rw [hcm] at hma
  rw [hcn] at hna
  have hmaxle : (a : ℝ) * ((max m n : ℕ) : ℝ) ≤ x + h * Real.sqrt x := by
    rcases le_total m n with hle | hle
    · rw [max_eq_right hle]
      exact hna.2.2
    · rw [max_eq_left hle]
      exact hma.2.2
  have hminge : x ≤ (a : ℝ) * ((min m n : ℕ) : ℝ) := by
    rcases le_total m n with hle | hle
    · rw [min_eq_left hle]
      exact hma.2.1
    · rw [min_eq_right hle]
      exact hna.2.1
  have hdiff : (a : ℝ) * (((max m n : ℕ) : ℝ) - ((min m n : ℕ) : ℝ)) ≤ h * Real.sqrt x := by
    nlinarith [hmaxle, hminge]
  have hΔ0 : (0 : ℝ) ≤ ((max m n : ℕ) : ℝ) - ((min m n : ℕ) : ℝ) := by
    have : (min m n : ℕ) ≤ (max m n : ℕ) := min_le_max
    have hcast : (((min m n : ℕ)) : ℝ) ≤ (((max m n : ℕ)) : ℝ) := by exact_mod_cast this
    linarith
  nlinarith [hdiff, halo, ha0, hsx, hΔ0]

/-- Every index of the fibre block is at least `√x/2`. -/
theorem fibreDyadicIndex_ge {x h : ℝ} (hx : 4 ≤ x) {b : ℕ} (hb : b ∈ fibreDyadicIndex x h) :
    Real.sqrt x / 2 ≤ (b : ℝ) ∧ 1 ≤ b := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [fibreDyadicIndex, Finset.mem_Icc] at hb
  have h1 : 1 ≤ ⌈Real.sqrt x / 2⌉₊ := Nat.one_le_ceil_iff.2 (by positivity)
  refine ⟨?_, by omega⟩
  have hceil : Real.sqrt x / 2 ≤ ((⌈Real.sqrt x / 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have : ((⌈Real.sqrt x / 2⌉₊ : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb.1
  linarith

/-- **The second moment of a set over the fibres is a banded shifted pair count.**  The whole cost
of discarding a set is the number of its pairs at distance at most `h`, times `2h + 1`. -/
theorem sum_sq_card_fibre_inter_le_band {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h) (T : Finset ℕ) :
    ∑ a ∈ outerBlock x h, (((innerFibre x h a ∩ T).card : ℝ)) ^ 2
      ≤ (2 * h + 1)
        * (((((T ∩ fibreDyadicIndex x h) ×ˢ (T ∩ fibreDyadicIndex x h)).filter
            (fun p => ((max p.1 p.2 : ℕ) : ℝ) - ((min p.1 p.2 : ℕ) : ℝ) ≤ h)).card : ℝ)) := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  set A : Finset ℕ := T ∩ fibreDyadicIndex x h with hA
  set K : ℕ × ℕ → ℝ := fun p =>
    (((outerBlock x h).filter
      (fun a => p.1 ∈ innerFibre x h a ∧ p.2 ∈ innerFibre x h a)).card : ℝ) with hK
  have hstep := sum_sq_card_fibre_inter_eq (x := x) (h := h) hx T
  rw [hstep, ← hA]
  have hprod : (∑ m ∈ A, ∑ n ∈ A, K (m, n)) = ∑ p ∈ A ×ˢ A, K p :=
    (Finset.sum_product (s := A) (t := A) (f := K)).symm
  rw [hprod]
  set F : Finset (ℕ × ℕ) := (A ×ˢ A).filter
    (fun p => ((max p.1 p.2 : ℕ) : ℝ) - ((min p.1 p.2 : ℕ) : ℝ) ≤ h) with hF
  have hzero : ∀ p ∈ A ×ˢ A, p ∉ F → K p = 0 := by
    intro p hp hpF
    rw [hF, Finset.mem_filter] at hpF
    have hband : ¬ (((max p.1 p.2 : ℕ) : ℝ) - ((min p.1 p.2 : ℕ) : ℝ) ≤ h) := fun hc => hpF ⟨hp, hc⟩
    rw [hK]
    by_contra hne
    have hcard : ((outerBlock x h).filter
        (fun a => p.1 ∈ innerFibre x h a ∧ p.2 ∈ innerFibre x h a)).card ≠ 0 := by
      intro hc
      refine hne ?_
      show ((({a ∈ outerBlock x h | p.1 ∈ innerFibre x h a ∧ p.2 ∈ innerFibre x h a}).card : ℕ)
        : ℝ) = 0
      rw [hc]
      norm_num
    have hnonempty := Finset.card_pos.1 (Nat.pos_of_ne_zero hcard)
    exact hband (fibre_kernel_band_width hx hnonempty)
  have hsplit : (∑ p ∈ A ×ˢ A, K p) = ∑ p ∈ F, K p :=
    (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
  rw [hsplit]
  have hterm : ∀ p ∈ F, K p ≤ 2 * h + 1 := by
    intro p hp
    rw [hF, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, -⟩ := hp
    rw [hA, Finset.mem_inter] at hp1 hp2
    obtain ⟨h1lo, h1⟩ := fibreDyadicIndex_ge hx hp1.2
    obtain ⟨h2lo, h2⟩ := fibreDyadicIndex_ge hx hp2.2
    have hmin : Real.sqrt x / 2 ≤ ((min p.1 p.2 : ℕ) : ℝ) := by
      rcases le_total p.1 p.2 with hle | hle
      · rw [min_eq_left hle]
        exact h1lo
      · rw [min_eq_right hle]
        exact h2lo
    exact fibre_kernel_le_two_h hx0.le hh0 h1 h2 hmin
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end

end RHTower.Sieve
