import GaloisForLFunctions.RHTower.ThetaCuspHawkingModularBoostEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingCausalHardyIndexEndpoint
import GaloisForLFunctions.RHTower.XiSquaredEulerRayCubicAmplification
import GaloisForLFunctions.RHTower.XiSquaredEulerDiagonalCorrelationUniversalityLaw

/-!
# Stimulated Hawking cubic unmasking endpoint

The modular gain used here is the literal reduced one-sector gain
`cosh(r)^(2 : ℕ)` of the theta-source two-mode Hawking squeeze.  This module asks
whether that genuine bosonic amplification can expose the first possible
three-shell obstruction hidden by the complete Xi divisor.

Two sharply different laws result.

* `[PROVED NO-GO]` A common modular boost multiplies every entry of the full
  response kernel by the same positive gain.  Its three-shell determinant is
  multiplied by `cosh(r)^(6 : ℕ)`, so its sign never changes.  Common stimulated
  amplification cannot unmask a resonance hidden by the other Xi orbits.
* `[PROVED SURVIVOR]` If the same physical gain is coupled selectively to one
  divisor orbit, the family begins at the unmodified full kernel at `r = 0`.
  The gain is unbounded, and every off-critical orbit eventually forces a
  strictly negative determinant on every fixed ordered positive triple.
* `[PROVED BRIDGE]` The selector is not merely a label: every off-critical
  divisor orbit canonically gives an upper theta-Hawking resonance, up to the
  physical reflection, whose causal Hardy scattering defect has rank one.
* `[PROVED REDUCTION]` Stability of all such source-pure selective stimulated
  families implies RH.

The distinction is physical, not decorative: stimulated Hawking radiation is
controlled by Bogoliubov gain, while resonant superradiance can concentrate
amplification at long-lived modes (see arXiv:2110.06796 and arXiv:2204.05335).
Those works do not provide the arithmetic orbit selector used here.

`[LOCAL-RESEARCH] [NOVELTY UNVERIFIED]` This endpoint does not claim exact
theta-mirror dynamics already implements the selective kernel.  It proves the
mathematical target that such dynamics would need to select.  The remaining
RH-bearing producer is now narrower: derive the coupling of modular gain to
the canonical rank-one causal Hardy defect with the squared-Euler reweighting
law.  A common modular boost, even with arbitrarily large gain, is formally
insufficient.
-/

open Complex Real Filter Topology Set

noncomputable section

namespace RHTower

theorem thetaCuspHawkingModularGain_pos (r : ℝ) :
    0 < thetaCuspHawkingModularGain r := by
  rw [thetaCuspHawkingModularGain]
  exact sq_pos_of_pos (Real.cosh_pos r)

theorem thetaCuspHawkingModularGain_one_le (r : ℝ) :
    1 ≤ thetaCuspHawkingModularGain r := by
  rw [thetaCuspHawkingModularGain]
  nlinarith [Real.one_le_cosh r]

/-- Genuine two-mode-squeeze gain is unbounded with rapidity. -/
theorem tendsto_thetaCuspHawkingModularGain_atTop :
    Tendsto thetaCuspHawkingModularGain atTop atTop := by
  have hexp : Tendsto (fun r : ℝ => Real.exp r / 2) atTop atTop :=
    Real.tendsto_exp_atTop.atTop_div_const (by norm_num)
  refine tendsto_atTop_mono (fun r => ?_) hexp
  rw [thetaCuspHawkingModularGain, Real.cosh_eq]
  have hnegexp : 0 < Real.exp (-r) := Real.exp_pos _
  have hcosh : 1 ≤ (Real.exp r + Real.exp (-r)) / 2 := by
    simpa only [← Real.cosh_eq] using Real.one_le_cosh r
  have hlower : Real.exp r / 2 ≤
      (Real.exp r + Real.exp (-r)) / 2 := by
    linarith
  nlinarith

/-- Uniform application of the physical Hawking modular gain to the complete
Xi response kernel. -/
def thetaCuspHawkingCommonModularGainKernel (r x y : ℝ) : ℝ :=
  thetaCuspHawkingModularGain r * xiSquaredEulerFullKernel x y

/-- A common boost only scales the cubic response determinant. -/
theorem symmetricThreePointDet_thetaCuspHawkingCommonModularGainKernel
    (r x y z : ℝ) :
    symmetricThreePointDet
        (thetaCuspHawkingCommonModularGainKernel r) x y z =
      thetaCuspHawkingModularGain r ^ (3 : ℕ) *
        symmetricThreePointDet xiSquaredEulerFullKernel x y z := by
  unfold thetaCuspHawkingCommonModularGainKernel symmetricThreePointDet
  ring

/-- **Common-gain no-go.** Uniform Hawking amplification preserves the exact
three-shell sign. -/
theorem thetaCuspHawkingCommonModularGainKernel_threePointDet_nonneg_iff
    (r x y z : ℝ) :
    0 ≤ symmetricThreePointDet
        (thetaCuspHawkingCommonModularGainKernel r) x y z ↔
      0 ≤ symmetricThreePointDet xiSquaredEulerFullKernel x y z := by
  rw [symmetricThreePointDet_thetaCuspHawkingCommonModularGainKernel]
  exact mul_nonneg_iff_of_pos_left
    (pow_pos (thetaCuspHawkingModularGain_pos r) 3)

/-- Apply physical modular gain to one selected Xi resonance orbit while
retaining every other orbit at its physical weight. -/
def thetaCuspHawkingSelectiveModularGainKernel
    (q : XiZeroCopy) (r x y : ℝ) : ℝ :=
  xiSquaredEulerReweightedFullKernel q
    (thetaCuspHawkingModularGain r) x y

/-- The selective family is source-faithfully anchored at the complete
physical response before stimulation. -/
theorem thetaCuspHawkingSelectiveModularGainKernel_zero
    (q : XiZeroCopy) (x y : ℝ) :
    thetaCuspHawkingSelectiveModularGainKernel q 0 x y =
      xiSquaredEulerFullKernel x y := by
  simp [thetaCuspHawkingSelectiveModularGainKernel,
    xiSquaredEulerReweightedFullKernel, thetaCuspHawkingModularGain]

/-- Canonical backreaction resonance carried by one multiplicity-exact Xi
divisor copy. -/
def thetaCuspHawkingXiOrbitResonantMode (q : XiZeroCopy) :
    ThetaCuspHawkingBackreactionResonantMode :=
  ⟨xiSpectralPoint q,
    (xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance
      (xiSpectralPoint q)).mp (XiC_xiSpectralPoint_eq_zero q)⟩

theorem thetaCuspHawkingXiOrbitResonantMode_value (q : XiZeroCopy) :
    (thetaCuspHawkingXiOrbitResonantMode q).1 = xiSpectralPoint q := rfl

/-- Every off-critical divisor orbit has a canonically associated upper
Hawking resonance, choosing only the physical reflected orientation when
necessary. -/
theorem exists_upper_thetaCuspHawkingXiOrbitResonantMode
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ (r : ThetaCuspHawkingBackreactionResonantMode),
      0 < r.1.im ∧
        (r = thetaCuspHawkingXiOrbitResonantMode q ∨
          r = thetaCuspHawkingBackreactionReflectedResonantMode
            (thetaCuspHawkingXiOrbitResonantMode q)) := by
  have him : (xiSpectralPoint q).im ≠ 0 := by
    rw [xiSpectralPoint]
    simpa using sub_ne_zero.mpr hoff.symm
  rcases lt_or_gt_of_ne him with hneg | hpos
  · refine ⟨thetaCuspHawkingBackreactionReflectedResonantMode
      (thetaCuspHawkingXiOrbitResonantMode q), ?_, Or.inr rfl⟩
    rw [thetaCuspHawkingBackreactionReflectedResonantMode_im,
      thetaCuspHawkingXiOrbitResonantMode_value]
    linarith
  · have hr : 0 < (thetaCuspHawkingXiOrbitResonantMode q).1.im := by
      rw [thetaCuspHawkingXiOrbitResonantMode_value]
      exact hpos
    exact ⟨thetaCuspHawkingXiOrbitResonantMode q, hr, Or.inl rfl⟩

/-- The source-selected upper resonance carries an exact one-dimensional
causal Hardy defect: a canonical resonance selector candidate. -/
theorem exists_rankOne_causalHardySelector_of_offCriticalXiOrbit
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ (r : ThetaCuspHawkingBackreactionResonantMode) (hr : 0 < r.1.im),
      (r = thetaCuspHawkingXiOrbitResonantMode q ∨
          r = thetaCuspHawkingBackreactionReflectedResonantMode
            (thetaCuspHawkingXiOrbitResonantMode q)) ∧
        Module.finrank ℂ ((thetaCuspHawkingCausalHardyRange r hr)ᗮ) = 1 := by
  obtain ⟨r, hr, horient⟩ :=
    exists_upper_thetaCuspHawkingXiOrbitResonantMode q hoff
  exact ⟨r, hr, horient,
    finrank_thetaCuspHawkingCausalHardyDefect_eq_one r hr⟩

/-- **Selective stimulated-unmasking law.** Every off-critical resonance
eventually makes every fixed ordered three-shell response determinant
negative under genuine unbounded Hawking modular gain. -/
theorem exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
      symmetricThreePointDet
        (thetaCuspHawkingSelectiveModularGainKernel q r) x y z < 0 := by
  obtain ⟨L, hL, hdet⟩ :=
    exists_xiSquaredEulerReweightedFullKernel_threePointDet_neg
      q hoff hx hxy hyz
  have hevent : ∀ᶠ r : ℝ in atTop,
      L < thetaCuspHawkingModularGain r := by
    have hbase :=
      tendsto_atTop.1 tendsto_thetaCuspHawkingModularGain_atTop (L + 1)
    filter_upwards [hbase] with r hr
    linarith
  obtain ⟨R, hR⟩ := eventually_atTop.1 hevent
  refine ⟨R, ?_⟩
  intro r hr
  have hneg := hdet (thetaCuspHawkingModularGain r) (hR r hr)
  change symmetricThreePointDet
    (xiSquaredEulerReweightedFullKernel q
      (thetaCuspHawkingModularGain r)) x y z < 0
  exact hneg

/-- Each off-critical orbit simultaneously carries a canonical rank-one
causal scattering selector and an eventually negative selectively stimulated
three-shell response.  The unproved dynamics must identify these two pieces. -/
theorem exists_rankOne_causalHardySelector_and_eventually_negative_stimulatedCubic
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ (mode : ThetaCuspHawkingBackreactionResonantMode)
        (hmode : 0 < mode.1.im),
      (mode = thetaCuspHawkingXiOrbitResonantMode q ∨
          mode = thetaCuspHawkingBackreactionReflectedResonantMode
            (thetaCuspHawkingXiOrbitResonantMode q)) ∧
        Module.finrank ℂ
          ((thetaCuspHawkingCausalHardyRange mode hmode)ᗮ) = 1 ∧
        ∃ R : ℝ, ∀ r : ℝ, R ≤ r →
          symmetricThreePointDet
            (thetaCuspHawkingSelectiveModularGainKernel q r) x y z < 0 := by
  obtain ⟨mode, hmode, horient, hfinrank⟩ :=
    exists_rankOne_causalHardySelector_of_offCriticalXiOrbit q hoff
  refine ⟨mode, hmode, horient, hfinrank, ?_⟩
  exact
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff hx hxy hyz

/-- Every source-pure selectively stimulated Xi resonance remains on the
nonnegative side of every ordered three-shell determinant wall. -/
def ThetaCuspHawkingSelectiveModularCubicStable : Prop :=
  ∀ (q : XiZeroCopy) (x y z r : ℝ),
    0 < x → x < y → y < z →
      0 ≤ symmetricThreePointDet
        (thetaCuspHawkingSelectiveModularGainKernel q r) x y z

/-- **RH-producing survivor.** Stability under source-pure selective Hawking
modular amplification forces every Xi orbit to have zero transverse charge,
hence proves RH. -/
theorem riemannHypothesis_of_thetaCuspHawkingSelectiveModularCubicStable
    (hstable : ThetaCuspHawkingSelectiveModularCubicStable) :
    RiemannHypothesis := by
  apply xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis.1
  intro q
  apply (xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff q).2
  by_contra hoff
  obtain ⟨R, hR⟩ :=
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff (x := 1) (y := 2) (z := 3)
        (by norm_num) (by norm_num) (by norm_num)
  have hneg := hR R le_rfl
  have hnonneg := hstable q 1 2 3 R
    (by norm_num) (by norm_num) (by norm_num)
  linarith

end RHTower
