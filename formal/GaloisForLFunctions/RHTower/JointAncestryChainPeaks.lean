import GaloisForLFunctions.RHTower.JointAncestryIsolatedRealPartPeaks
import GaloisForLFunctions.RHTower.JointAncestryChainFreeHalfPlane
import GaloisForLFunctions.RHTower.PrimeLagLandauWeights

/-!
# An off-line chain has isolated real-part peaks at every height

If the off-line zeros form a chain (`JasOffLineChain`: every off-line zero has a farther one),
then for every off-line zero `ρ₀` with `Re ρ₀ > ½` and every height `H` there is a zero `ρ` with
`Re ρ ≥ Re ρ₀` and `Im ρ ≥ H` that is a local maximum of the real part in the window
`|Im ρ′ − Im ρ| ≤ (Im ρ)^c` (`exists_isolated_rePeak_of_chain`).

The chain supplies infinitely many zeros of strictly increasing distance from the line.  Only finitely
many zeros lie in any bounded height window, so these zeros climb to infinity.  By the
functional equation and conjugation they can be moved to the upper right quarter of the strip.
The density walk of `JointAncestryIsolatedRealPartPeaks` then stops at an isolated peak.

So a hypothetical chain never prevents the target selection of the JAS chain attack: the
obstruction to excluding chains lies entirely in the interference of near-tied zeros at the
selected peak and in prime sums at large height offsets.
-/

open Complex

namespace RHTower

noncomputable section

/-- A zero copy at the mirror position `1 − ρ̄`, which has the same height and the opposite
distance from the critical line. -/
theorem exists_xiZeroCopy_mirror (q : XiZeroCopy) :
    ∃ q' : XiZeroCopy, ((q'.1 : ℂ)).re = 1 - ((q.1 : ℂ)).re ∧
      ((q'.1 : ℂ)).im = ((q.1 : ℂ)).im := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_conj q
  refine ⟨xiZeroCopyReflectEquiv q₁, ?_, ?_⟩
  · rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re, hq₁, Complex.conj_re]
  · rw [xiZeroCopy_reflect_val, Complex.sub_im, Complex.one_im, hq₁, Complex.conj_im]; ring

/-- **A chain climbs.**  Under a chain, beyond any off-line zero there are strictly farther zeros at
arbitrarily large positive height, on the right of the critical line. -/
theorem exists_farther_high_of_chain (hch : JasOffLineChain) (q₀ : XiZeroCopy)
    (hoff : ((q₀.1 : ℂ)).re ≠ 1 / 2) (H : ℝ) :
    ∃ q : XiZeroCopy, |((q₀.1 : ℂ)).re - 1 / 2| < ((q.1 : ℂ)).re - 1 / 2 ∧
      H < ((q.1 : ℂ)).im := by
  classical
  have hstep : ∀ q : XiZeroCopy, ((q.1 : ℂ)).re ≠ 1 / 2 →
      ∃ q' : XiZeroCopy, |((q.1 : ℂ)).re - 1 / 2| < |((q'.1 : ℂ)).re - 1 / 2| := hch.2
  -- farther zeros are off the line
  have hoff' : ∀ q q' : XiZeroCopy, |((q.1 : ℂ)).re - 1 / 2| < |((q'.1 : ℂ)).re - 1 / 2| →
      ((q'.1 : ℂ)).re ≠ 1 / 2 := by
    intro q q' h heq
    rw [heq, sub_self, abs_zero] at h
    exact absurd h (not_lt.mpr (abs_nonneg _))
  let nxt : XiZeroCopy → XiZeroCopy := fun q =>
    if h : ((q.1 : ℂ)).re ≠ 1 / 2 then (hstep q h).choose else q
  let s : ℕ → XiZeroCopy := fun k => nxt^[k] q₀
  have hs_succ : ∀ k, s (k + 1) = nxt (s k) := fun k => Function.iterate_succ_apply' nxt k q₀
  have hs_off : ∀ k, ((s k).1 : ℂ).re ≠ 1 / 2 ∧
      |((s k).1 : ℂ).re - 1 / 2| < |((s (k + 1)).1 : ℂ).re - 1 / 2| := by
    intro k
    induction k with
    | zero =>
      refine ⟨hoff, ?_⟩
      rw [hs_succ]
      simp only [s, Function.iterate_zero, id, nxt, dif_pos hoff]
      exact (hstep q₀ hoff).choose_spec
    | succ k ih =>
      have hk1 : ((s (k + 1)).1 : ℂ).re ≠ 1 / 2 := hoff' _ _ ih.2
      refine ⟨hk1, ?_⟩
      rw [hs_succ (k + 1)]
      simp only [nxt, dif_pos hk1]
      exact (hstep _ hk1).choose_spec
  have hmono : ∀ i j, i < j → |((s i).1 : ℂ).re - 1 / 2| < |((s j).1 : ℂ).re - 1 / 2| := by
    intro i j hij
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact lt_trans (ih h) (hs_off j).2
      · rw [h]; exact (hs_off j).2
  have hinj : Function.Injective s := by
    intro i j h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hmono i j hlt; rw [h] at this; exact lt_irrefl _ this
    · have := hmono j i hlt; rw [h] at this; exact lt_irrefl _ this
  -- unbounded height
  obtain ⟨k, hk⟩ : ∃ k, max H 0 < |((s (k + 1)).1 : ℂ).im| := by
    by_contra hbd
    push Not at hbd
    have hfin := finite_xiOrdinateWindow (max H 0) 0
    have hmem : ∀ k, s (k + 1) ∈ xiOrdinateWindow (max H 0) 0 := by
      intro k
      show |((s (k + 1)).1 : ℂ).im - 0| ≤ max H 0
      rw [sub_zero]; exact hbd k
    exact Set.infinite_of_injective_forall_mem
      (fun i j h => by have := hinj h; omega) hmem hfin
  set q₁ := s (k + 1)
  have hfar : |((q₀.1 : ℂ)).re - 1 / 2| < |((q₁.1 : ℂ)).re - 1 / 2| := by
    have := hmono 0 (k + 1) (by omega)
    have h0 : s 0 = q₀ := rfl
    rw [h0] at this
    exact this
  -- move to the upper right quarter
  have hH : H < |((q₁.1 : ℂ)).im| := lt_of_le_of_lt (le_max_left _ _) hk
  obtain ⟨q₂, hq₂re, hq₂im⟩ : ∃ q₂ : XiZeroCopy, ((q₂.1 : ℂ)).re - 1 / 2 =
      |((q₁.1 : ℂ)).re - 1 / 2| ∧ ((q₂.1 : ℂ)).im = ((q₁.1 : ℂ)).im := by
    rcases le_or_gt (1 / 2) ((q₁.1 : ℂ)).re with hle | hlt
    · exact ⟨q₁, by rw [abs_of_nonneg (by linarith)], rfl⟩
    · obtain ⟨q', hre, him⟩ := exists_xiZeroCopy_mirror q₁
      exact ⟨q', by rw [hre, abs_of_neg (by linarith)]; ring, him⟩
  rcases le_or_gt 0 ((q₂.1 : ℂ)).im with him0 | him0
  · refine ⟨q₂, by rw [hq₂re]; exact hfar, ?_⟩
    rw [hq₂im]; rw [← hq₂im, abs_of_nonneg him0] at hH; rwa [← hq₂im]
  · obtain ⟨q₃, hq₃⟩ := exists_xiZeroCopy_conj q₂
    refine ⟨q₃, ?_, ?_⟩
    · rw [hq₃, Complex.conj_re, hq₂re]; exact hfar
    · rw [hq₃, Complex.conj_im]
      rw [← hq₂im, abs_of_neg him0] at hH
      exact hH

/-- **Chains have isolated real-part peaks at every height.** -/
theorem exists_isolated_rePeak_of_chain (hch : JasOffLineChain) (q₀ : XiZeroCopy)
    (hq₀ : 1 / 2 < ((q₀.1 : ℂ)).re) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ H : ℝ, ∃ q : XiZeroCopy,
      ((q₀.1 : ℂ)).re ≤ ((q.1 : ℂ)).re ∧ H ≤ ((q.1 : ℂ)).im ∧
        ∀ q' : XiZeroCopy, |((q'.1 : ℂ)).im - ((q.1 : ℂ)).im| ≤ ((q.1 : ℂ)).im ^ c →
          ((q'.1 : ℂ)).re ≤ ((q.1 : ℂ)).re := by
  have hlt1 := (xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q₀.1)).2
  obtain ⟨c, hc0, hc1, G₀, hG₀, hpeak⟩ := exists_isolated_rePeak hq₀ hlt1
  refine ⟨c, hc0, hc1, fun H => ?_⟩
  set G := max G₀ H with hG
  obtain ⟨q₁, hfar, hhigh⟩ :=
    exists_farther_high_of_chain hch q₀ (by linarith) (2 * G)
  have hre1 : ((q₀.1 : ℂ)).re ≤ ((q₁.1 : ℂ)).re := by
    rw [abs_of_pos (by linarith)] at hfar; linarith
  obtain ⟨q, hqre, hqim, hqmax⟩ := hpeak G (le_max_left _ _) q₁ (by linarith) hhigh.le
  exact ⟨q, le_trans hre1 hqre, le_trans (le_max_right _ _) hqim, hqmax⟩

end

end RHTower
