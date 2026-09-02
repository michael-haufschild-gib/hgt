import Zeta23.FinalMult
import GaloisForLFunctions.RHTower.XiCardGateUnification
import GaloisForLFunctions.RHTower.WeilCriticalMellinLogBridge
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.SeamStripRamification
import GaloisForLFunctions.RHTower.SuzukiWeilNormDefiniteness

/-!
# Unconditional simple-critical density and bounded-support Weil uniqueness

Alpöge--Furman's unconditional, multiplicity-aware two-thirds theorem is stated for Mathlib's
`riemannZeta`.  This module identifies its cumulative counting functions with this project's
completed-`xi` census, including analytic multiplicities.  It then closes the exact density gate
used by the bounded-support Weil card and discharges the card's literal Mellin-transform theorem.

The external theorem is imported from the immutable, axiom-audited Zeta23 revision pinned in the
Lake manifest.  Its Lean and Mathlib revisions are exactly those of this project.
-/

open Complex Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower

/-! ## Exact equality of the two cumulative censuses -/

/-- Zeta23's nontrivial zeta-zero window `(0,T]` is exactly this project's finite completed-Xi
window. -/
theorem zeta23_zerosIn_zero_toFinset_eq_stripFinsetPos (T : ℝ) :
    (Zeta23.zerosIn_finite 0 T).toFinset = stripFinsetPos T := by
  classical
  ext z
  rw [Set.Finite.mem_toFinset, mem_stripFinsetPos]
  simp only [Zeta23.zerosIn, Zeta23.IsNontrivialZero, Set.mem_setOf_eq, zero_lt_one_mul]
  constructor
  · rintro ⟨⟨hzeta, hre0, hre1⟩, him0, himT⟩
    exact ⟨hre0, hre1, him0, himT,
      (xi_zero_iff_zeta_zero_of_mem_strip ⟨hre0, hre1⟩).2 hzeta⟩
  · rintro ⟨hre0, hre1, him0, himT, hxi⟩
    exact ⟨⟨(xi_zero_iff_zeta_zero_of_mem_strip ⟨hre0, hre1⟩).1 hxi, hre0, hre1⟩,
      him0, himT⟩

/-- Zeta23's cumulative multiplicity count is definitionally the same divisor count after the
zeta/Xi unit-factor bridge in the open strip. -/
theorem zeta23_Ncount_zero_eq_xiPosZeroCount (T : ℝ) :
    Zeta23.Ncount 0 T = xiPosZeroCount T := by
  classical
  rw [Zeta23.Ncount, ← finsum_mem_coe_finset, Set.Finite.coe_toFinset,
    zeta23_zerosIn_zero_toFinset_eq_stripFinsetPos, xiPosZeroCount]
  apply Finset.sum_congr rfl
  intro z hz
  unfold Zeta23.zeroMult
  rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
    ⟨(mem_stripFinsetPos.mp hz).1, (mem_stripFinsetPos.mp hz).2.1⟩]

/-- Zeta23's cumulative simple-critical count is exactly this project's completed-Xi count. -/
theorem zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount (T : ℝ) :
    Zeta23.N0simple 0 T = xiSimpleCriticalZeroCount T := by
  classical
  unfold Zeta23.N0simple xiSimpleCriticalZeroCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
    Zeta23.zerosIn, Zeta23.IsNontrivialZero, Zeta23.zeroMult, zero_lt_one_mul]
  constructor
  · rintro ⟨⟨⟨⟨hzeta, hre0, hre1⟩, him0, himT⟩, hline⟩, hmult⟩
    have horder := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre0, hre1⟩
    refine ⟨mem_stripFinsetPos.mpr ⟨hre0, hre1, him0, himT, ?_⟩, hline, ?_⟩
    · exact (xi_zero_iff_zeta_zero_of_mem_strip ⟨hre0, hre1⟩).2 hzeta
    · rwa [horder]
  · rintro ⟨hz, hline, hmult⟩
    obtain ⟨hre0, hre1, him0, himT, hxi⟩ := mem_stripFinsetPos.mp hz
    have horder := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre0, hre1⟩
    refine ⟨⟨⟨⟨?_, hre0, hre1⟩, him0, himT⟩, hline⟩, ?_⟩
    · exact (xi_zero_iff_zeta_zero_of_mem_strip ⟨hre0, hre1⟩).1 hxi
    · rwa [← horder]

/-! ## The closed density theorem -/

/-- Alpöge--Furman's cumulative two-thirds theorem, transported without loss to the Xi census. -/
theorem two_thirds_simpleCritical_epsilon :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (xiPosZeroCount T : ℝ) ≤ xiSimpleCriticalZeroCount T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := Zeta23.thmB₀_mult_cumulative ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  simpa only [zeta23_Ncount_zero_eq_xiPosZeroCount,
    zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount] using hT₀ T hT

/-- **Unconditional two-thirds density of simple critical Xi zeros.** -/
theorem two_thirds_le_liminf_xiSimpleCriticalRatio :
    (2 / 3 : ℝ) ≤ liminf xiSimpleCriticalRatio atTop := by
  have hcob : IsCoboundedUnder (fun x y : ℝ => x ≥ y) atTop xiSimpleCriticalRatio :=
    (isBoundedUnder_of ⟨1, fun T => xiSimpleCriticalRatio_le_one T⟩).isCoboundedUnder_ge
  by_contra hnot
  have hlt : liminf xiSimpleCriticalRatio atTop < (2 / 3 : ℝ) := lt_of_not_ge hnot
  let b : ℝ := (liminf xiSimpleCriticalRatio atTop + 2 / 3) / 2
  have hlim_b : liminf xiSimpleCriticalRatio atTop < b := by
    dsimp [b]
    linarith
  have hb_two : b < (2 / 3 : ℝ) := by
    dsimp [b]
    linarith
  let ε : ℝ := 2 / 3 - b
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨T₀, hT₀⟩ := two_thirds_simpleCritical_epsilon ε hε
  have hev : ∀ᶠ T : ℝ in atTop, b ≤ xiSimpleCriticalRatio T := by
    filter_upwards [eventually_ge_atTop T₀, eventually_pos_xiPosZeroCount]
      with T hT hN
    rw [xiSimpleCriticalRatio, le_div_iff₀ hN]
    have hbound := hT₀ T hT
    dsimp [ε] at hbound
    convert hbound using 1 <;> ring
  have hb_liminf : b ≤ liminf xiSimpleCriticalRatio atTop := le_liminf_of_le hcob hev
  linarith

/-- Closed positive-density provider shared by the zero-divisor-geometry cards. -/
theorem exists_pos_le_liminf_xiSimpleCriticalRatio :
    ∃ c : ℝ, 0 < c ∧ c ≤ liminf xiSimpleCriticalRatio atTop :=
  ⟨2 / 3, by norm_num, two_thirds_le_liminf_xiSimpleCriticalRatio⟩

/-! ## Literal bounded-support Mellin uniqueness -/

/-- **Bounded-support Weil critical-tail uniqueness, unconditional.**

A continuous multiplicative test supported in `[exp(-a), exp(a)]` whose critical-line Mellin
transform vanishes at all but finitely many simple critical Xi zeros is the zero test. -/
theorem weilTest_eq_zero_of_cofinite_simpleCritical_mellin_zero
    {a : ℝ} (ha : 0 ≤ a) (g : ℝ → ℂ) (hg : Continuous g)
    (hsupp : Function.support g ⊆ Icc (Real.exp (-a)) (Real.exp a))
    (E : Finset ℝ)
    (hvanish : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 →
        mellin g ((1 / 2 : ℂ) + (t : ℂ) * I) = 0) :
    g = 0 := by
  let f : SoninL2 := weilCriticalLogProfileL2 a g hg hsupp
  have hcut : suzukiCutoff a f = 0 := by
    apply suzukiCutoff_eq_zero_of_le_liminf_xiSimpleCriticalRatio
      (c := (2 / 3 : ℝ)) (by norm_num) two_thirds_le_liminf_xiSimpleCriticalRatio ha f E
    intro t htE htpos htxi htmult
    rw [← mellin_criticalLine_eq_suzukiCompactL2Fourier g hg hsupp]
    exact hvanish t htE htpos htxi htmult
  have hcut_zero : ((suzukiCutoff a f : SoninL2) : ℝ → ℂ) =ᵐ[volume] 0 := by
    rw [hcut]
    exact Filter.Eventually.of_forall fun _ => rfl
  have hprofile_ae : ∀ᵐ x : ℝ, weilCriticalLogProfile g x = 0 := by
    filter_upwards [suzukiCutoff_weilCriticalLogProfileL2_ae g hg hsupp, hcut_zero]
      with x hx hzero
    rw [← hx]
    exact hzero
  have hprofile : weilCriticalLogProfile g = 0 := by
    funext x
    exact eq_zero_of_ae_zero_of_continuousAt hprofile_ae
      (continuous_weilCriticalLogProfile hg).continuousAt
  funext y
  by_cases hy : 0 < y
  · have hp := congrFun hprofile (Real.log y)
    rw [Pi.zero_apply, weilCriticalLogProfile, Real.exp_log hy] at hp
    exact (mul_eq_zero.mp hp).resolve_left
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  · by_contra hgy
    have hymem := hsupp hgy
    have hexp : 0 < Real.exp (-a) := Real.exp_pos _
    linarith [hymem.1]

end RHTower

end
