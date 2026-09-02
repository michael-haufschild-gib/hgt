import Zeta23.FinalMult
import GaloisForLFunctions.RHTower.HorizontalSingletonFiberCharging
import GaloisForLFunctions.RHTower.XiSimpleCriticalSuperlinearConsumer
import GaloisForLFunctions.RHTower.WeilCriticalMellinLogBridge
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.SeamStripRamification
import GaloisForLFunctions.HTGeometry.InfiniteSupportCayleyGram

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
  simp only [Zeta23.zerosIn, Zeta23.IsNontrivialZero, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hzeta, hre0, hre1⟩, him0, himT⟩
    exact ⟨hre0, hre1, him0, himT,
      (xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).2 hzeta⟩
  · rintro ⟨hre0, hre1, him0, himT, hxi⟩
    exact ⟨⟨(xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).1 hxi, hre0, hre1⟩,
      him0, himT⟩

/-- Zeta23's cumulative multiplicity count is definitionally the same divisor count after the
zeta/Xi unit-factor bridge in the open strip. -/
theorem zeta23_Ncount_zero_eq_xiPosZeroCount (T : ℝ) :
    Zeta23.Ncount 0 T = xiPosZeroCount T := by
  classical
  calc
    Zeta23.Ncount 0 T =
        ∑ z ∈ (Zeta23.zerosIn_finite 0 T).toFinset, Zeta23.zeroMult z := by
      rw [Zeta23.Ncount, ← finsum_mem_coe_finset, Set.Finite.coe_toFinset]
    _ = ∑ z ∈ stripFinsetPos T, (analyticOrderAt xi z).toNat := by
      rw [zeta23_zerosIn_zero_toFinset_eq_stripFinsetPos]
      apply Finset.sum_congr rfl
      intro z hz
      unfold Zeta23.zeroMult
      rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
        ⟨(mem_stripFinsetPos.mp hz).1, (mem_stripFinsetPos.mp hz).2.1⟩]
    _ = xiPosZeroCount T := rfl

/-- Zeta23's cumulative simple-critical count is exactly this project's completed-Xi count. -/
theorem zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount (T : ℝ) :
    Zeta23.N0simple 0 T = xiSimpleCriticalZeroCount T := by
  classical
  unfold Zeta23.N0simple xiSimpleCriticalZeroCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
    Zeta23.zerosIn, Zeta23.IsNontrivialZero, Zeta23.zeroMult]
  constructor
  · rintro ⟨⟨⟨⟨hzeta, hre0, hre1⟩, him0, himT⟩, hline⟩, hmult⟩
    have horder := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre0, hre1⟩
    refine ⟨mem_stripFinsetPos.mpr ⟨hre0, hre1, him0, himT, ?_⟩, hline, ?_⟩
    · exact (xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).2 hzeta
    · rwa [horder]
  · rintro ⟨hz, hline, hmult⟩
    obtain ⟨hre0, hre1, him0, himT, hxi⟩ := mem_stripFinsetPos.mp hz
    have horder := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre0, hre1⟩
    refine ⟨⟨⟨⟨?_, hre0, hre1⟩, him0, himT⟩, hline⟩, ?_⟩
    · exact (xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).1 hxi
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

/-- The Xi census is eventually positive, derived here from Zeta23's closed Riemann--von Mangoldt
instance so the external and internal RvM implementations need not be imported together. -/
theorem eventually_pos_xiPosZeroCount_of_zeta23 :
    ∀ᶠ T : ℝ in atTop, 0 < (xiPosZeroCount T : ℝ) := by
  have htop : Tendsto (fun T => (Zeta23.Ncount 0 T : ℝ)) atTop atTop :=
    Zeta23.tendsto_Ncount_zero_atTop Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
  filter_upwards [htop.eventually_gt_atTop 0] with T hT
  rwa [zeta23_Ncount_zero_eq_xiPosZeroCount] at hT

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
    filter_upwards [eventually_ge_atTop T₀, eventually_pos_xiPosZeroCount_of_zeta23]
      with T hT hN
    rw [xiSimpleCriticalRatio, le_div_iff₀ hN]
    have hbound := hT₀ T hT
    have heq : (2 / 3 : ℝ) - ((2 / 3 : ℝ) - b) = b := by ring
    rwa [show ε = (2 / 3 : ℝ) - b by rfl, heq] at hbound
  have hb_liminf : b ≤ liminf xiSimpleCriticalRatio atTop := le_liminf_of_le hcob hev
  linarith

/-- Closed positive-density provider shared by the zero-divisor-geometry cards. -/
theorem exists_pos_le_liminf_xiSimpleCriticalRatio :
    ∃ c : ℝ, 0 < c ∧ c ≤ liminf xiSimpleCriticalRatio atTop :=
  ⟨2 / 3, by norm_num, two_thirds_le_liminf_xiSimpleCriticalRatio⟩

/-- A closed superlinear lower bound on simple critical Xi zeros.  This is the exact analytic
provider consumed by the bounded-support uniqueness engine. -/
theorem eventually_superlinear_xiSimpleCriticalZeroCount :
    ∀ᶠ T : ℝ in atTop,
      1 / (72 * Real.pi) * T * Real.log T ≤ (xiSimpleCriticalZeroCount T : ℝ) := by
  obtain ⟨T₀, hsimple⟩ := Zeta23.thmB₀_mult (1 / 3) (by norm_num)
  have hsimple_ev : ∀ᶠ S : ℝ in atTop,
      (1 / 3 : ℝ) * (Zeta23.Ncount S (2 * S) : ℝ) ≤ Zeta23.N0simple S (2 * S) := by
    filter_upwards [eventually_ge_atTop T₀] with S hS
    have h := hsimple S hS
    norm_num at h ⊢
    exact h
  have hN_ev : ∀ᶠ S : ℝ in atTop,
      S * Zeta23.l S / (4 * Real.pi) ≤ (Zeta23.Ncount S (2 * S) : ℝ) := by
    simpa only [Zeta23.zetaZeroConfig_N] using
      Zeta23.Assembly.eventually_N_ge Zeta23.zetaZeroConfig Zeta23.paperInputs_zeta.RvM
  have hscale : Tendsto (fun T : ℝ => T / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hsimple_half := hscale.eventually hsimple_ev
  have hN_half := hscale.eventually hN_ev
  have hlog_half := hscale.eventually Zeta23.Assembly.eventually_log_le_two_l
  have hl_half : ∀ᶠ T : ℝ in atTop, Real.log 2 ≤ Zeta23.l (T / 2) :=
    (Zeta23.Assembly.tendsto_l_atTop.comp hscale).eventually_ge_atTop (Real.log 2)
  filter_upwards [hsimple_half, hN_half, hlog_half, hl_half,
    eventually_ge_atTop (2 : ℝ)] with T hsimpleT hNT hlogT hlT hT2
  have hTpos : 0 < T := by linarith
  have hhalfpos : 0 < T / 2 := by positivity
  have htwo : 2 * (T / 2) = T := by ring
  rw [htwo] at hsimpleT hNT
  have hadd := Zeta23.N0simple_add' Zeta23.zetaSeam
    (a := 0) (b := T / 2) (d := T) (by linarith) (by linarith)
  have hwindow_le : (Zeta23.N0simple (T / 2) T : ℝ) ≤ Zeta23.N0simple 0 T := by
    rw [hadd]
    exact_mod_cast Nat.le_add_left _ _
  have hlog_two : Real.log T = Real.log (T / 2) + Real.log 2 := by
    calc
      Real.log T = Real.log (2 * (T / 2)) := by congr 1; ring
      _ = Real.log 2 + Real.log (T / 2) :=
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : T / 2 ≠ 0)
      _ = Real.log (T / 2) + Real.log 2 := by ring
  have hlog_le : Real.log T ≤ 3 * Zeta23.l (T / 2) := by
    rw [hlog_two]
    linarith
  have hlpos : 0 < Zeta23.l (T / 2) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hmain : 1 / (72 * Real.pi) * T * Real.log T
      ≤ (1 / 3 : ℝ) * ((T / 2) * Zeta23.l (T / 2) / (4 * Real.pi)) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    calc
      1 / (72 * Real.pi) * T * Real.log T
          ≤ 1 / (72 * Real.pi) * T * (3 * Zeta23.l (T / 2)) := by
            gcongr
      _ = (1 / 3 : ℝ) * ((T / 2) * Zeta23.l (T / 2) / (4 * Real.pi)) := by
            field_simp
            ring
  rw [← zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount]
  exact hmain.trans ((mul_le_mul_of_nonneg_left hNT (by norm_num)).trans
    (hsimpleT.trans hwindow_le))

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
    apply suzukiCutoff_eq_zero_of_superlinear_simpleCritical
      (c := 1 / (72 * Real.pi)) (by positivity)
      eventually_superlinear_xiSimpleCriticalZeroCount ha f E
    intro t htE htpos htxi htmult
    rw [← mellin_criticalLine_eq_suzukiCompactL2Fourier g hg hsupp]
    exact hvanish t htE htpos htxi htmult
  have hprofile_ae : ∀ᵐ x : ℝ, weilCriticalLogProfile g x = 0 := by
    have h := (suzukiCutoff_weilCriticalLogProfileL2_ae g hg hsupp).symm
    rw [hcut] at h
    filter_upwards [h] with x hx
    rw [hx]
    simp
  have hprofile : weilCriticalLogProfile g = 0 := by
    funext x
    apply GaloisForLFunctions.HTGeometry.continuous_eq_zero_on_support_of_ae_eq_zero
      volume (weilCriticalLogProfile g) (continuous_weilCriticalLogProfile hg) hprofile_ae x
    rw [MeasureTheory.Measure.support_eq_univ]
    exact Set.mem_univ x
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
