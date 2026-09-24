import GaloisForLFunctions.RHTower.LorentzianZeroMass

/-!
# The local zero count of the Xi divisor

The Lorentzian zero mass `Σ_ρ 1/(1 + (t − γ)²)` is bounded by `C + log(|t| + 4)`.  Every divisor
copy whose ordinate lies within `w` of the height `t` contributes at least `1/(1 + w²)` to that
mass, so only finitely many copies can lie in such a window and their number is bounded by
`(1 + w²)` times the mass.  This is the local form of the Riemann–von Mangoldt counting estimate:

`#{ρ : |Im ρ − t| ≤ w} ≤ 8(1 + w²)(C + log(|t| + 4))`,

in particular `#{ρ : |Im ρ − t| ≤ 1} ≪ log(|t| + 4)`.  Finiteness of the window is a consequence,
not a hypothesis: an infinite window would contain finite subsets of arbitrary cardinality, each of
which already exceeds the mass.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The copies of the Xi divisor whose ordinate lies within `w` of the height `t`. -/
def xiOrdinateWindow (w t : ℝ) : Set XiZeroCopy := {q | |(q.1 : ℂ).im - t| ≤ w}

theorem mem_xiOrdinateWindow_iff {w t : ℝ} {q : XiZeroCopy} :
    q ∈ xiOrdinateWindow w t ↔ |(q.1 : ℂ).im - t| ≤ w := Iff.rfl

/-- Each copy in the window carries at least `1/(1 + w²)` of the Lorentzian mass. -/
theorem lorentzMassTerm_ge_of_mem_xiOrdinateWindow {w t : ℝ} {q : XiZeroCopy}
    (hq : q ∈ xiOrdinateWindow w t) :
    1 / (1 + w ^ 2) ≤ lorentzMassTerm t q := by
  have habs : |(q.1 : ℂ).im - t| ≤ w := hq
  have hsq : (t - (q.1 : ℂ).im) ^ 2 ≤ w ^ 2 := by
    have h1 : |(q.1 : ℂ).im - t| ^ 2 = (t - (q.1 : ℂ).im) ^ 2 := by
      rw [sq_abs]
      ring
    have h2 : (0 : ℝ) ≤ |(q.1 : ℂ).im - t| := abs_nonneg _
    nlinarith [habs, h2, h1]
  unfold lorentzMassTerm
  refine one_div_le_one_div_of_le (by positivity) ?_
  linarith

/-- Any finite family of window copies is paid for by the Lorentzian mass. -/
private theorem card_mul_le_lorentzMass (w t : ℝ) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, q ∈ xiOrdinateWindow w t) :
    (F.card : ℝ) * (1 / (1 + w ^ 2)) ≤ lorentzMass t := by
  have hconst : (F.card : ℝ) * (1 / (1 + w ^ 2)) = ∑ _q ∈ F, (1 / (1 + w ^ 2) : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  refine le_trans (Finset.sum_le_sum (fun q hq =>
    lorentzMassTerm_ge_of_mem_xiOrdinateWindow (hF q hq))) ?_
  exact Summable.sum_le_tsum F (fun q _ => lorentzMassTerm_nonneg t q)
    (summable_lorentzMassTerm t)

/-- **The ordinate window is finite.**  No hypothesis: an infinite window would contain finite
subsets of arbitrary cardinality, each of which already exceeds the Lorentzian mass. -/
theorem finite_xiOrdinateWindow (w t : ℝ) : (xiOrdinateWindow w t).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set N : ℕ := ⌈lorentzMass t * (1 + w ^ 2)⌉₊ + 1 with hN
  obtain ⟨F, hFsub, hFcard⟩ := hinf.exists_subset_card_eq N
  have hle := card_mul_le_lorentzMass w t F (fun q hq => hFsub hq)
  rw [hFcard] at hle
  have hw : (0 : ℝ) < 1 + w ^ 2 := by positivity
  have hceil : lorentzMass t * (1 + w ^ 2) ≤ (⌈lorentzMass t * (1 + w ^ 2)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hNgt : lorentzMass t * (1 + w ^ 2) < (N : ℝ) := by
    rw [hN]
    push_cast
    linarith
  have hkey : lorentzMass t < (N : ℝ) * (1 / (1 + w ^ 2)) := by
    rw [mul_one_div, lt_div_iff₀ hw]
    exact hNgt
  linarith

/-- **The window count is bounded by the Lorentzian mass.** -/
theorem ncard_xiOrdinateWindow_mul_le (w t : ℝ) :
    (((xiOrdinateWindow w t).ncard : ℝ)) * (1 / (1 + w ^ 2)) ≤ lorentzMass t := by
  have hfin := finite_xiOrdinateWindow w t
  have hcard : ((xiOrdinateWindow w t).ncard : ℝ) = (hfin.toFinset.card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
  rw [hcard]
  refine card_mul_le_lorentzMass w t hfin.toFinset (fun q hq => ?_)
  simpa using hq

/-- **Local Riemann–von Mangoldt count.**  The number of divisor copies with ordinate within `w`
of `t` is at most `8(1 + w²)(C + log(|t| + 4))`. -/
theorem ncard_xiOrdinateWindow_le_log (w t : ℝ) :
    (((xiOrdinateWindow w t).ncard : ℝ))
      ≤ 8 * (1 + w ^ 2) * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := by
  have hw : (0 : ℝ) < 1 + w ^ 2 := by positivity
  have h1 := ncard_xiOrdinateWindow_mul_le w t
  have h2 := lorentzMass_le_log t
  have h3 : (((xiOrdinateWindow w t).ncard : ℝ)) * (1 / (1 + w ^ 2))
      ≤ 8 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := le_trans h1 h2
  have h4 := mul_le_mul_of_nonneg_right h3 hw.le
  rw [mul_assoc, one_div, inv_mul_cancel₀ (ne_of_gt hw), mul_one] at h4
  linarith [h4]

/-- The unit-window form. -/
theorem ncard_xiOrdinateWindow_one_le_log (t : ℝ) :
    (((xiOrdinateWindow 1 t).ncard : ℝ))
      ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := by
  have h := ncard_xiOrdinateWindow_le_log 1 t
  norm_num at h
  linarith

end

end RHTower
