import GaloisForLFunctions.HTGeometry.QuantileRearrangementEnergy
import GaloisForLFunctions.RHTower.DilationFreeSetMeasure
import GaloisForLFunctions.RHTower.WeilArchReLevyPoleForm

/-!
# Prime-blind positivity on the nonnegative cone reduces to one window

For a real test `h` write the pole and archimedean part of the Weil functional as
`A(0)‖h‖² + J(h) + 2P(h)`, with `A(0) = gammaBracket 0 < 0`, the jump energy
`J(h) = ∫_{x>0} ω(x) ∫ (h(u) − h(u+x))² du dx` (`ω = archLevyDensity`) and the pole energy
`P(h) = ∫∫ h(u) h(v) cosh((u − v)/2)`. `WeilEnergyNonneg h` is the inequality
`|A(0)| ‖h‖² ≤ J(h) + 2P(h)` in `[0, ∞]`.

`weilEnergyNonneg_of_primeBlind`: if the inequality holds for every bounded measurable `h ≥ 0`
vanishing off `(0, log 2)` (`WindowPositive`), then it holds for every bounded integrable `g ≥ 0`
whose autocorrelation vanishes at every `log n`, `n ≥ 2`.

Proof. Such a `g` is positive on a set `S` of measure at most `log 2` (dilation-free support). The
quantile transport moves `g` onto `(0, |S|) ⊆ (0, log 2)`; it keeps `‖g‖₂`, does not increase the
jump energy (`ω` decreases), and does not increase the pole energy (`cosh` increases).

`weilArchRe_nonneg_of_primeBlind`: under the same window hypothesis, every nonnegative `C²`
compactly supported prime-blind test has nonnegative pole and archimedean part.
-/

open MeasureTheory Set Filter Topology
open scoped FourierTransform
open Zeta23
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.NonnegativeCone

noncomputable section

/-- The jump energy `∫_{x>0} ω(x) ∫ (h(u) − h(u+x))² du dx`. -/
def jumpEnergy (h : ℝ → ℝ) : ENNReal :=
  ∫⁻ x in Ioi 0, ENNReal.ofReal (archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2)

/-- The pole energy `∫∫ h(u) h(v) cosh((u − v)/2)`. -/
def poleEnergy (h : ℝ → ℝ) : ENNReal :=
  ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (h p.1 * h p.2 * Real.cosh (|p.1 - p.2| / 2))

/-- The Weil energy inequality `|A(0)| ‖h‖² ≤ J(h) + 2P(h)`. -/
def WeilEnergyNonneg (h : ℝ → ℝ) : Prop :=
  ENNReal.ofReal (-EF.gammaBracket 0 * ∫ u, h u ^ 2) ≤ jumpEnergy h + 2 * poleEnergy h

/-- **Window positivity**: the Weil energy inequality for every bounded measurable `h ≥ 0`
vanishing off `(0, log 2)`. -/
def WindowPositive : Prop :=
  ∀ h : ℝ → ℝ, Measurable h → (∀ x, 0 ≤ h x) → (∃ C, ∀ x, h x ≤ C) →
    (∀ x ∉ Ioo 0 (Real.log 2), h x = 0) → WeilEnergyNonneg h

/-! ### The kernels -/

/-- The jump kernel, cut off to `0` on `(−∞, 0]`. -/
def jumpKernel (x : ℝ) : ℝ := max (archLevyDensity x) 0

theorem measurable_jumpKernel : Measurable jumpKernel :=
  measurable_archLevyDensity.max measurable_const

theorem jumpKernel_nonneg (x : ℝ) : 0 ≤ jumpKernel x := le_max_right _ _

theorem jumpKernel_of_pos {x : ℝ} (hx : 0 < x) : jumpKernel x = archLevyDensity x :=
  max_eq_left (archLevyDensity_pos hx).le

theorem antitoneOn_archLevyDensity : AntitoneOn archLevyDensity (Ioi 0) := by
  intro a ha b hb hab
  unfold archLevyDensity
  have hda : 0 < 1 - Real.exp (-2 * a) := by
    have : Real.exp (-2 * a) < 1 := by
      have := Real.exp_lt_exp.mpr (show -2 * a < 0 by linarith [mem_Ioi.mp ha])
      rwa [Real.exp_zero] at this
    linarith
  have hdb : 1 - Real.exp (-2 * a) ≤ 1 - Real.exp (-2 * b) := by
    have := Real.exp_le_exp.mpr (show -2 * b ≤ -2 * a by linarith)
    linarith
  exact div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) hda hdb

theorem antitoneOn_jumpKernel : AntitoneOn jumpKernel (Ioi 0) := fun a ha b hb hab => by
  rw [jumpKernel_of_pos ha, jumpKernel_of_pos hb]
  exact antitoneOn_archLevyDensity ha hb hab

theorem integrableOn_min_jumpKernel (n : ℕ) :
    IntegrableOn (fun x => min (jumpKernel x) n) (Ioi 0) := by
  have hexp : IntegrableOn (fun x : ℝ => ((n : ℝ) * Real.exp (1 / 2) + 2) * Real.exp (-(1 / 2) * x))
      (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul _
  refine hexp.mono' ((measurable_jumpKernel.min measurable_const).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_))
  have hx : 0 < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (jumpKernel_nonneg x) n.cast_nonneg)]
  have hE : 0 < Real.exp (-(1 / 2) * x) := Real.exp_pos _
  rcases le_or_gt x 1 with hx1 | hx1
  · have : (n : ℝ) ≤ (n : ℝ) * Real.exp (1 / 2) * Real.exp (-(1 / 2) * x) := by
      rw [mul_assoc, ← Real.exp_add]
      have : 0 ≤ 1 / 2 + -(1 / 2) * x := by linarith
      exact le_mul_of_one_le_right n.cast_nonneg (Real.one_le_exp this)
    calc min (jumpKernel x) n ≤ n := min_le_right _ _
      _ ≤ (n : ℝ) * Real.exp (1 / 2) * Real.exp (-(1 / 2) * x) := this
      _ ≤ ((n : ℝ) * Real.exp (1 / 2) + 2) * Real.exp (-(1 / 2) * x) := by nlinarith
  · have hden : 1 / 2 ≤ 1 - Real.exp (-2 * x) := by
      have : Real.exp (-2 * x) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
      have : Real.exp (-2) < 1 / 2 := by
        have := Real.exp_one_gt_d9
        rw [show (-2 : ℝ) = -(2 : ℝ) by ring, Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
        calc (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
          _ < Real.exp 1 := by linarith
          _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      linarith
    have hω : archLevyDensity x ≤ 2 * Real.exp (-(1 / 2) * x) := by
      unfold archLevyDensity
      rw [div_le_iff₀ (by linarith), show -x / 2 = -(1 / 2) * x by ring]
      nlinarith [Real.exp_pos (-(1 / 2) * x)]
    calc min (jumpKernel x) n ≤ jumpKernel x := min_le_left _ _
      _ = archLevyDensity x := jumpKernel_of_pos hx
      _ ≤ 2 * Real.exp (-(1 / 2) * x) := hω
      _ ≤ ((n : ℝ) * Real.exp (1 / 2) + 2) * Real.exp (-(1 / 2) * x) := by
          have : 0 ≤ (n : ℝ) * Real.exp (1 / 2) := by positivity
          nlinarith

theorem jumpEnergy_eq (h : ℝ → ℝ) :
    jumpEnergy h = ∫⁻ x in Ioi 0, ENNReal.ofReal (jumpKernel x * ∫ u, (h u - h (u + x)) ^ 2) :=
  setLIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [jumpKernel_of_pos hx]

/-- The pole kernel `cosh(r/2)`. -/
theorem monotoneOn_coshHalf : MonotoneOn (fun r : ℝ => Real.cosh (r / 2)) (Ici 0) :=
  fun a ha b hb hab => Real.cosh_le_cosh.mpr (by
    rw [abs_of_nonneg (by linarith [mem_Ici.mp ha]), abs_of_nonneg (by linarith [mem_Ici.mp hb])]
    linarith)

/-! ### The reduction -/

/-- **Reduction of prime-blind positivity on the nonnegative cone to one window.** If the Weil
energy inequality holds for every bounded measurable `h ≥ 0` vanishing off `(0, log 2)`, then it
holds for every bounded integrable `g ≥ 0` whose autocorrelation vanishes at every `log n`,
`n ≥ 2`. -/
theorem weilEnergyNonneg_of_primeBlind (hW : WindowPositive) {g : ℝ → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) {C : ℝ} (hgC : ∀ x, g x ≤ C) (hgi : Integrable g)
    (hblind : ∀ n : ℕ, 2 ≤ n → ∫ x, g (x + Real.log n) * g x = 0) : WeilEnergyNonneg g := by
  set S := {x | 0 < g x}
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hg
  have hprod : ∀ n : ℕ, 2 ≤ n → Integrable fun x => g (x + Real.log n) * g x := fun n _ => by
    have := hgi.bdd_mul (c := C) (f := fun x => g (x + Real.log n))
      (hg.comp (measurable_id.add_const _)).aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]; exact hgC _)
    exact this
  have hSvol := DilationFree.volume_pos_le_log_two_of_primeBlind hg hg0 hprod hblind
  have hS : volume S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSvol
  have hgB : BddSupp S g C :=
    { meas := hg
      bound := fun x => by rw [abs_of_nonneg (hg0 x)]; exact hgC x
      supp := fun x hx => le_antisymm (not_lt.mp hx) (hg0 x)
      setm := hSm
      fin := hS }
  have hL : (volume S).toReal ≤ Real.log 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hSvol
    rwa [ENNReal.toReal_ofReal (Real.log_pos (by norm_num)).le] at this
  have hTB := transport_bddSupp hSm hS hgB
  have hTsupp : ∀ x ∉ Ioo 0 (Real.log 2), transport hSm hS g x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun hx' => hx ⟨hx'.1, hx'.2.trans_le hL⟩) _
  have hTW := hW (transport hSm hS g) hTB.meas (transport_nonneg hSm hS hg0)
    ⟨C, fun x => (le_abs_self _).trans (hTB.bound x)⟩ hTsupp
  unfold WeilEnergyNonneg at hTW ⊢
  rw [integral_sq_transport hSm hS hgB] at hTW
  refine hTW.trans (add_le_add ?_ ?_)
  · rw [jumpEnergy_eq, jumpEnergy_eq]
    exact lintegral_jump_transport_le hSm hS hgB hg0 measurable_jumpKernel jumpKernel_nonneg
      antitoneOn_jumpKernel integrableOn_min_jumpKernel
  · gcongr
    exact lintegral_pair_transport_le hSm hS hgB hg0 (κ := fun r => Real.cosh (r / 2))
      (Real.continuous_cosh.comp (continuous_id.div_const 2)).measurable
      (fun r => (Real.cosh_pos _).le) monotoneOn_coshHalf

/-! ### Smooth tests -/

/-- The jump energy of a `C²` compactly supported test is finite. -/
theorem jumpEnergy_ne_top_of_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    jumpEnergy f ≠ ⊤ := by
  set F : ℝ → ℂ := fun u => (f u : ℂ) with hFdef
  have hFc : Continuous F := Complex.continuous_ofReal.comp hf.continuous
  have hFcs : HasCompactSupport F := hfc.comp_left Complex.ofReal_zero
  have hF2 : ContDiff ℝ 2 F := Complex.ofRealCLM.contDiff.comp hf
  have hF1 : Integrable F := hFc.integrable_of_hasCompactSupport hFcs
  have hFL2 : MemLp F 2 := hFc.memLp_of_hasCompactSupport hFcs
  have hk : ∀ z : ℂ, paperFT (EF.weilTest F F) z =
      paperFT F z * (starRingEnd ℂ) (paperFT F ((starRingEnd ℂ) z)) :=
    EF.paperFT_weilTest hFc hFc hFcs hFcs
  have hreal : ∀ r : ℝ, paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ) =
      ((‖paperFT F r‖ ^ 2 * EF.gammaBracket r : ℝ) : ℂ) := fun r => by
    rw [hk, Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hintC := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket hF2 hFcs hF2 hFcs
  have hintR : Integrable fun r : ℝ => ‖paperFT F r‖ ^ 2 * EF.gammaBracket r := by
    refine hintC.re.congr (Eventually.of_forall fun r => ?_)
    show (paperFT (EF.weilTest F F) r * (EF.gammaBracket r : ℂ)).re = _
    rw [hreal, Complex.ofReal_re]
  have hint : Integrable fun ξ : ℝ => gammaHardyPhaseRate (2 * Real.pi * ξ) * ‖𝓕 F ξ‖ ^ 2 := by
    have h := (hintR.comp_mul_left' (R := -(2 * Real.pi)) (by
      have := Real.pi_pos; intro h; linarith)).div_const 2
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [fourier_eq_paperFT_neg_two_pi_mul, WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
      show -(2 * Real.pi) * ξ = -(2 * Real.pi * ξ) by ring, gammaHardyPhaseRate_neg]
    ring
  have h := lintegral_archLevyDirichlet_ne_top hF1 hFL2 hint
  convert h using 1
  unfold jumpEnergy
  refine lintegral_congr fun x => ?_
  congr 3
  funext u
  simp only [hFdef]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The pole energy of a nonnegative continuous compactly supported test as a Bochner integral. -/
theorem poleEnergy_eq_ofReal {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) :
    poleEnergy f = ENNReal.ofReal (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)) := by
  have hcs : HasCompactSupport fun p : ℝ × ℝ => f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) := by
    refine HasCompactSupport.intro (hfc.isCompact.prod hfc.isCompact) fun p hp => ?_
    rcases not_and_or.mp (show ¬(p.1 ∈ tsupport f ∧ p.2 ∈ tsupport f) from hp) with h1 | h2
    · rw [image_eq_zero_of_notMem_tsupport h1]; ring
    · rw [image_eq_zero_of_notMem_tsupport h2]; ring
  have hcont : Continuous fun p : ℝ × ℝ => f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) := by
    fun_prop
  rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrable_of_hasCompactSupport hcs)
    (ae_of_all _ fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _)) (Real.cosh_pos _).le)]
  unfold poleEnergy
  refine lintegral_congr fun p => ?_
  rw [show |p.1 - p.2| / 2 = |(p.1 - p.2) / 2| by rw [abs_div, abs_two], Real.cosh_abs]

/-- **Prime-blind positivity for nonnegative smooth tests, given one window.** If the Weil energy
inequality holds on `(0, log 2)` for nonnegative tests, then every nonnegative `C²` compactly
supported `f` whose autocorrelation vanishes at every `log n`, `n ≥ 2`, has nonnegative pole and
archimedean part of the Weil functional. -/
theorem weilArchRe_nonneg_of_primeBlind (hW : WindowPositive) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x)
    (hblind : ∀ n : ℕ, 2 ≤ n → ∫ x, f (x + Real.log n) * f x = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hc := hf.continuous
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, f x ≤ C := by
    obtain ⟨C, hC⟩ := hc.bddAbove_range_of_hasCompactSupport hfc
    exact ⟨C, fun x => hC ⟨x, rfl⟩⟩
  have hE := weilEnergyNonneg_of_primeBlind hW hc.measurable hf0 hC
    (hc.integrable_of_hasCompactSupport hfc) hblind
  rw [WeilLevyPole.weilArchRe_eq_levy_pole hf hfc]
  unfold WeilEnergyNonneg at hE
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  rw [poleEnergy_eq_ofReal hc hfc hf0, ← ENNReal.ofReal_toReal hJ] at hE
  set J := (jumpEnergy f).toReal with hJdef
  set P := ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) with hPdef
  have hP0 : 0 ≤ P :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _)) (Real.cosh_pos _).le
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  rw [show (2 : ENNReal) * ENNReal.ofReal P = ENNReal.ofReal (2 * P) by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_add hJ0 (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hE
  change 0 ≤ EF.gammaBracket 0 * (∫ u, f u ^ 2) + J + 2 * P
  linarith

end

end RHTower.NonnegativeCone
