import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheEvolutionStartsPositive
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheContinuumMarginIsTheDyadicLimit

/-!
# Forbidding lattice zero modes is RH

A lattice window is **degenerate** when it is positive definite up to size `n + 1` and the next margin
vanishes; its zero mode is then unique, a palindrome up to sign, with `n + 1` simple angles on the unit
circle, and the window is a curve window (`degenerate_window_is_curve`).

* **Off RH a lattice degenerates exactly** (`exists_degenerate_lattice_of_not_riemannHypothesis`).
  Take a short generic bump `ψ` (a dilated bump whose transform vanishes at no zero of `ζ`,
  `exists_short_generic`). Its two-site margins `E_1(ψ, s) = c(0) − c(s)²/c(0)` are positive for
  `s ≤ 1/2` (short windows are positive), and off RH the Hasse–Weil bound `|c(t)| ≤ c(0)` fails at some
  scale along its orbit (AOG: one generic orbit decides the line). The orbit correlation `c` is
  continuous (`continuous_weilOrbitCorr`), so `E_1(ψ, ·)` vanishes at some step `s*`: the two-site
  lattice of `ψ` at step `s*` is degenerate.
* **RH is the absence of lattice zero modes** (`riemannHypothesis_iff_no_degenerate_lattice`): RH holds
  iff no lattice window of Spec ℤ degenerates. A unique-continuation principle that forbids the zero
  modes of the window tower — which, at a first critical length, carry mass on both collars and are
  determined by either end collar (`zeroMode_eq_of_eq_on_collar`) — is exactly RH.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry SpacingScaleHarmonicAnalysis Zeta23

/-- The orbit correlation is even: `c(−v) = c(v)`. -/
theorem weilOrbitCorr_neg (φ : ℝ → ℝ) (v : ℝ) : weilOrbitCorr φ (-v) = weilOrbitCorr φ v := by
  rw [weilOrbitCorr, weilOrbitCorr, ← weilPair_scaleShift_same v (scaleShift (-v) φ) φ,
    ← scaleShift_add, add_neg_cancel, scaleShift_zero, weilPair_comm]

/-- The first Weil datum of a lattice is the orbit correlation at the step. -/
theorem weilSeq_one (φ : ℝ → ℝ) (h : ℝ) : weilSeq φ h 1 = weilOrbitCorr φ h := by
  rw [weilSeq, latticeTranslate_eq_scaleShift', weilPair_comm, ← weilOrbitCorr_neg φ h]
  simp only [weilOrbitCorr, Int.cast_one, one_mul]

/-- The two-site margin: `E_1 = c(0) − c(h)²/c(0)`. -/
theorem levinsonErr_one (φ : ℝ → ℝ) (h : ℝ) :
    levinsonErr (weilSeq φ h) 1 = weilQuad φ - weilOrbitCorr φ h ^ 2 / weilQuad φ := by
  rw [levinsonErr_succ, levinsonErr_zero]
  have h0 : weilSeq φ h 0 = weilQuad φ := by rw [weilSeq, latticeTranslate_zero]; rfl
  have hs : schurParam (weilSeq φ h) 0 = weilOrbitCorr φ h := by
    simp only [schurParam, schurCoupling, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      Nat.cast_zero, zero_add]
    exact weilSeq_one φ h
  rw [h0, hs]

/-- The orbit correlation of a scaling cycle is the orbit correlation of its test. -/
theorem zeta_orbitCorr_eq (x : ScalingCycle) (t : ℝ) :
    zetaScalingDatum.orbitCorr x t = weilOrbitCorr x.2.2 t := by
  have hf : (x.2.2 : ℝ → ℝ) ∈ realTests := x.2.2.2
  have hs := scaleShift_mem t hf
  rw [← configScalingDatum_zeta_orbitCorr, configScalingDatum_orbitCorr_eq,
    tsum_exp_Wsummand_eq_W, RHTower.zeta_W_eq_weilFullFunctional_mixed (cx_contDiff hs.1)
      (cx_hasCompactSupport hs.2) (cx_contDiff hf.1) (cx_hasCompactSupport hf.2)]
  rfl

/-! ### A short generic bump -/

/-- **Short generic bumps exist**: a bump supported in `[−4l, 0]`, `l < 1/20`, whose transform vanishes
at no zero of `ζ`. -/
theorem exists_short_generic :
    ∃ ψ ∈ realTests, ψ ≠ 0 ∧ (∀ y, y ∉ Icc (-(1 / 5 : ℝ)) 0 → ψ y = 0) ∧
      RealSpectrallyGeneric zetaZeroConfig ψ := by
  have hd : Differentiable ℂ (paperFT (cx realBump)) :=
    RHTower.EvenSector.differentiable_paperFT_of_compact (cx_contDiff realBump_mem.1).continuous
      (cx_hasCompactSupport realBump_mem.2)
  have hcount := HTGeometry.countable_zeros_of_entire_nonzero hd paperFT_realBump_zero
  set B : Set ℝ := {0} ∪ ⋃ ρ ∈ zetaZeroConfig.carrier,
    (fun l : ℝ => (l : ℂ) * SquareRootThreshold.gammaOf ρ) ⁻¹' {t | paperFT (cx realBump) t = 0}
  have hBc : B.Countable := by
    refine (Set.countable_singleton 0).union
      ((SquareRootThreshold.carrier_countable zetaZeroConfig).biUnion fun ρ _ => ?_)
    by_cases hγ : SquareRootThreshold.gammaOf ρ = 0
    · refine Set.Countable.mono (fun l hl => ?_) (Set.countable_empty : (∅ : Set ℝ).Countable)
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hγ, mul_zero] at hl
      exact paperFT_realBump_zero hl
    · exact hcount.preimage fun a b h => by simpa [mul_left_inj' hγ] using h
  -- a small dilation off the countable bad set
  obtain ⟨l, hlI, hlB⟩ : ∃ l ∈ Ioo (0 : ℝ) (1 / 20), l ∉ B := by
    by_contra hc
    push Not at hc
    have h0 := hBc.measure_zero volume
    have : volume (Ioo (0 : ℝ) (1 / 20)) ≤ volume B := measure_mono fun l hl => hc l hl
    rw [Real.volume_Ioo, h0] at this
    norm_num at this
  have hl0 : l ≠ 0 := hlI.1.ne'
  set g := dilateTest l realBump
  have hg := dilateTest_mem hl0 realBump_mem
  set ψ : ℝ → ℝ := fun u => g (u - (-(2 * l)))
  have hψ : ψ ∈ realTests :=
    ⟨hg.1.comp (contDiff_id.sub contDiff_const), hg.2.comp_homeomorph (Homeomorph.subRight _)⟩
  have hbump0 : ∀ u, 2 ≤ |u| → realBump u = 0 := fun u hu =>
    ContDiffBump.zero_of_le_dist _ (by simpa [Real.dist_eq] using hu)
  refine ⟨ψ, hψ, fun h0 => ?_, fun y hy => ?_, fun ρ hρ hz => hlB (Or.inr ?_)⟩
  · -- `ψ(−2l) = realBump 0 = 1`
    have h1 : realBump (l⁻¹ * (-(2 * l) - -(2 * l))) = 0 := congrFun h0 _
    rw [sub_self, mul_zero] at h1
    have h2 : realBump 0 = 1 :=
      ContDiffBump.one_of_mem_closedBall _ (Metric.mem_closedBall_self (ContDiffBump.rIn_pos _).le)
    rw [h2] at h1
    exact one_ne_zero h1
  · -- the bump vanishes outside `[−4l, 0] ⊆ [−1/5, 0]`
    show realBump (l⁻¹ * (y - -(2 * l))) = 0
    apply hbump0
    rw [abs_mul, abs_inv, abs_of_pos hlI.1, inv_mul_eq_div, le_div_iff₀ hlI.1]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with hy | hy
    · rw [abs_of_neg (by linarith [hlI.2])]; linarith [hlI.2]
    · rw [abs_of_pos (by linarith [hlI.1])]; linarith [hlI.1]
  · -- a translate of a generic test is generic
    have htr := RHTower.OddResolvent.paperFT_comp_sub_const (cx g) (-(2 * l))
      (SquareRootThreshold.gammaOf ρ)
    have hcx : cx ψ = fun u => cx g (u - -(2 * l)) := rfl
    rw [← hcx, hz, paperFT_dilateTest hl0] at htr
    have habs : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hl0
    have := (mul_eq_zero.mp htr.symm).resolve_left (Complex.exp_ne_zero _)
    exact Set.mem_biUnion hρ ((mul_eq_zero.mp this).resolve_left habs)

/-! ### Off RH a lattice degenerates exactly -/

/-- **Off RH some lattice window of Spec ℤ is exactly degenerate**: a short generic bump has a step at
which its two-site lattice is positive definite on one site and has vanishing second margin. -/
theorem exists_degenerate_lattice_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ ψ ∈ realTests, ψ ≠ 0 ∧ ∃ s : ℝ, 0 < s ∧ ToeplitzPosDef (weilSeq ψ s) 1 ∧
      levinsonErr (weilSeq ψ s) 1 = 0 := by
  obtain ⟨ψ, hψ, hψ0, hsupp, hgen⟩ := exists_short_generic
  set c := weilOrbitCorr ψ
  have hc := continuous_weilOrbitCorr hψ
  -- `c(0) = Q(ψ) > 0`: short tests are positive
  have hQ : 0 < weilQuad ψ := weilQuad_pos_of_short hψ hψ0 (c := 0) (L := 1 / 5)
    (by norm_num) (by simpa using hsupp)
  have hc0 : c 0 = weilQuad ψ := by
    show weilPair (scaleShift 0 ψ) ψ = weilQuad ψ
    rw [scaleShift_zero]; rfl
  -- off RH the Hasse–Weil bound fails along the orbit of `ψ`
  set x : ScalingCycle := (0, 0, ⟨ψ, hψ⟩)
  have hHW := (riemannHypothesis_iff_hasseWeil_of_generic x hgen).not.mp hRH
  push Not at hHW
  obtain ⟨t₁, ht₁⟩ := hHW
  simp only [ScalingDatum.HasseWeilAt, not_le, zeta_orbitCorr_eq] at ht₁
  change c 0 < |c t₁| at ht₁
  set s₁ := |t₁|
  have hcs₁ : |c s₁| = |c t₁| := by
    rcases abs_choice t₁ with h | h
    · rw [show s₁ = t₁ from h]
    · rw [show s₁ = -t₁ from h, weilOrbitCorr_neg]
  -- the margin function `E₁(s) = c(0) − c(s)²/c(0)`
  set F : ℝ → ℝ := fun s => weilQuad ψ - c s ^ 2 / weilQuad ψ
  have hF : ∀ s, levinsonErr (weilSeq ψ s) 1 = F s := fun s => levinsonErr_one ψ s
  have hFc : Continuous F := continuous_const.sub ((hc.pow 2).div_const _)
  -- small steps keep the two-site lattice positive
  have hsmall : 0 < F (1 / 2) := by
    rw [← hF]
    exact levinsonErr_pos_of_short hψ hψ0 hsupp (by norm_num : (0 : ℝ) < 1 / 2)
      (n := 1) (by norm_num) 1 le_rfl
  -- at `s₁` the margin is negative
  have hneg : F s₁ < 0 := by
    have h1 : weilQuad ψ < |c s₁| := by rw [hcs₁, ← hc0]; exact ht₁
    have h2 : weilQuad ψ ^ 2 < c s₁ ^ 2 := by
      rw [← sq_abs (c s₁)]; exact pow_lt_pow_left₀ h1 hQ.le two_ne_zero
    show weilQuad ψ - c s₁ ^ 2 / weilQuad ψ < 0
    rw [sub_neg, lt_div_iff₀ hQ]
    nlinarith
  have hs₁ : 1 / 2 < s₁ := by
    by_contra hle
    push Not at hle
    have hs₁pos : 0 < s₁ := by
      rcases (abs_nonneg t₁).lt_or_eq with h | h
      · exact h
      · exfalso
        have ht0 : t₁ = 0 := abs_eq_zero.mp h.symm
        rw [ht0, hc0, abs_of_pos hQ] at ht₁
        exact lt_irrefl _ ht₁
    have := levinsonErr_pos_of_short hψ hψ0 hsupp hs₁pos (n := 1) (by norm_num; linarith) 1 le_rfl
    rw [hF] at this
    linarith
  -- the intermediate value theorem
  obtain ⟨s, hsI, hs0⟩ := intermediate_value_Icc' hs₁.le hFc.continuousOn ⟨hneg.le, hsmall.le⟩
  have hspos : 0 < s := by linarith [hsI.1]
  refine ⟨ψ, hψ, hψ0, s, hspos, ?_, by rw [hF]; exact hs0⟩
  rw [toeplitzForm_posDef_iff (weilSeq_isEven ψ s) 0]
  intro k hk
  rw [Nat.le_zero.mp hk, levinsonErr_zero]
  have : weilSeq ψ s 0 = weilQuad ψ := by rw [weilSeq, latticeTranslate_zero]; rfl
  rw [this]
  exact hQ

/-- **RH is the absence of lattice zero modes.** RH holds iff no lattice window of Spec ℤ is
degenerate: whenever a lattice window is positive definite, the next margin does not vanish. -/
theorem riemannHypothesis_iff_no_degenerate_lattice :
    RiemannHypothesis ↔
      ∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h → ∀ n : ℕ, ToeplitzPosDef (weilSeq φ h) (n + 1) →
        levinsonErr (weilSeq φ h) (n + 1) ≠ 0 := by
  constructor
  · intro hRH φ hφ hφ0 h hh n hpd h0
    exact not_riemannHypothesis_of_first_critical hφ hφ0 hh hpd h0 hRH
  · intro H
    by_contra hRH
    obtain ⟨ψ, hψ, hψ0, s, hs, hpd, h0⟩ := exists_degenerate_lattice_of_not_riemannHypothesis hRH
    exact H ψ hψ hψ0 s hs 0 hpd h0

end GaloisForLFunctions.GrowingWindowsOfSpecZ
