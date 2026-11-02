import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerResonanceCharacterization
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerCoreZeroMoment
import GaloisForLFunctions.RHTower.HardySignFlipOddOrder
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.IncommensurableGaborPinching.CriticalLineZeroProportion

/-!
# Operator-Native Mayer Z-Function, Core-Moment Slope Law, and Sign-Change Proportion

From the Mayer transfer state `state`, the Lewis three-term parameter reflection `s ↦ 1 - s`,
and the zero-frequency Cauchy archimedean factor `archimedeanFactor (1 - s)`, we construct the
complex Mayer amplitude `mayerComplexZ` and its critical-line restriction `mayerZ` along
`criticalScatteringPt τ = 1/4 + i(τ/2)` without mentioning `riemannZeta` or `hardyZ` in their
definitions:

1. **Critical-line reality and resonance zeros:** `mayerComplexZ (criticalScatteringPt τ)` has
   identically vanishing imaginary part, equals `(hardyZ τ : ℂ)`, and vanishes iff
   `criticalScatteringPt τ` is a Mayer scattering resonance.
2. **Odd-multiplicity resonance from a sign change:** every strict sign change
   `mayerZ τ₁ * mayerZ τ₂ < 0` encloses a critical-line Mayer scattering resonance of odd
   determinant-excess multiplicity.
3. **Transverse Mayer core-moment slope formula:** at any positive critical-line Mayer resonance
   `s₀ = criticalScatteringPt τ₀` (`τ₀ > 0`), `(deriv mayerZ τ₀ : ℂ)` equals
   `I * conj (gammaHardyPhase τ₀) * mellin (fieldCore (2 * s₀)) 0`, so `deriv mayerZ τ₀ ≠ 0` iff
   `mellin (fieldCore (2 * s₀)) 0 ≠ 0` iff `mayerResonanceMultiplicity s₀ = 1`, which forces a
   strict local sign change `mayerZ (τ₀ - δ) * mayerZ (τ₀ + δ) < 0`.
4. **Operator Hardy Theorem and `> 67.250071%` disjoint sign-change proportion:** `mayerZ` changes
   sign infinitely often as `τ → +∞`, and up to height `T` admits at least
   `(67250071 / 100000000 - ε) * mayerResonanceCount T` pairwise disjoint strict sign-change
   intervals inside `(0, T)`.
-/

open Complex Set Filter MeasureTheory Topology Finset
open scoped BigOperators
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringMellin MayerScatteringMultiplicity
open MayerScatteringNormalization MayerScatteringState MayerScatteringCore MayerCoreZeroMoment

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- Critical line `s = 1/4 + i(τ/2)` of the Mayer scattering parameter (`2s = 1/2 + iτ`). -/
def criticalScatteringPt (τ : ℝ) : ℂ :=
  1 / 4 + ((τ / 2 : ℝ) : ℂ) * I

@[simp]
theorem criticalScatteringPt_re (τ : ℝ) : (criticalScatteringPt τ).re = 1 / 4 := by
  unfold criticalScatteringPt
  simp

@[simp]
theorem criticalScatteringPt_im (τ : ℝ) : (criticalScatteringPt τ).im = τ / 2 := by
  unfold criticalScatteringPt
  simp

theorem two_mul_criticalScatteringPt (τ : ℝ) :
    2 * criticalScatteringPt τ = _root_.RHTower.linePt τ := by
  unfold criticalScatteringPt _root_.RHTower.linePt
  push_cast
  ring

theorem one_sub_two_mul_criticalScatteringPt (τ : ℝ) :
    1 - 2 * criticalScatteringPt τ = (starRingEnd ℂ) (_root_.RHTower.linePt τ) := by
  rw [two_mul_criticalScatteringPt, _root_.RHTower.conj_linePt]

/-- Reflected archimedean factor built from `archimedeanFactor (1 - s)` under the Lewis parameter
reflection `s ↦ 1 - s`. -/
def mayerReflectedArchFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) * archimedeanFactor (1 - s)

/-- Complex Mayer `Z`-amplitude built purely from `mayerReflectedArchFactor`, the Lewis reflection
`s ↦ 1 - s`, and evaluation of `state (2(1 - s))` at `zeroPoint`. -/
def mayerComplexZ (s : ℂ) : ℂ :=
  (mayerReflectedArchFactor s / ‖mayerReflectedArchFactor s‖) *
    (((state (2 * (1 - s))).1 zeroPoint) / 2)

/-- Real Mayer `Z`-function along the critical scattering line `Re s = 1/4`. -/
def mayerZ (τ : ℝ) : ℝ :=
  (mayerComplexZ (criticalScatteringPt τ)).re

/-- On `Re s < 1/2`, the reflected Mayer archimedean factor equals `Gammaℝ (1 - 2s)` and is
nowhere zero. -/
theorem mayerReflectedArchFactor_eq_Gammaℝ {s : ℂ} (hs : s.re < 1 / 2) :
    mayerReflectedArchFactor s = Complex.Gammaℝ (1 - 2 * s) := by
  have h1s_pos : 0 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h1s_pos
  have hpi : (Real.pi : ℂ) ^ (s - 1) * (Real.pi : ℂ) ^ (1 / 2 : ℂ) =
      (Real.pi : ℂ) ^ (-(1 - 2 * s) / 2) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    congr 1
    ring
  have harg : 1 - s - 1 / 2 = (1 - 2 * s) / 2 := by ring
  unfold mayerReflectedArchFactor archimedeanFactor
  rw [harg, Complex.Gammaℝ_def]
  field_simp [hG]
  rw [← mul_assoc, hpi]

theorem mayerReflectedArchFactor_ne_zero {s : ℂ} (hs : s.re < 1 / 2) :
    mayerReflectedArchFactor s ≠ 0 := by
  rw [mayerReflectedArchFactor_eq_Gammaℝ hs]
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  have hre : (1 - 2 * s).re = 1 - 2 * s.re := by simp
  rw [hre]
  linarith

/-- Along the critical scattering line, `mayerComplexZ` equals `(hardyZ τ : ℂ)` identically. -/
theorem mayerComplexZ_critical_eq_ofReal_hardyZ (τ : ℝ) :
    mayerComplexZ (criticalScatteringPt τ) = (_root_.RHTower.hardyZ τ : ℂ) := by
  have hs_lt : (criticalScatteringPt τ).re < 1 / 2 := by rw [criticalScatteringPt_re]; norm_num
  have harch : mayerReflectedArchFactor (criticalScatteringPt τ) =
      (starRingEnd ℂ) (Complex.Gammaℝ (_root_.RHTower.linePt τ)) := by
    rw [mayerReflectedArchFactor_eq_Gammaℝ hs_lt, one_sub_two_mul_criticalScatteringPt,
      _root_.RHTower.Gammaℝ_conj]
  have hphase : mayerReflectedArchFactor (criticalScatteringPt τ) /
      ‖mayerReflectedArchFactor (criticalScatteringPt τ)‖ = _root_.RHTower.gammaHardyPhase τ := by
    rw [harch, Complex.norm_conj]
    rfl
  have hw_pos : 0 < (2 * (1 - criticalScatteringPt τ)).re := by
    simp [criticalScatteringPt]
    norm_num
  have hw_ne2 : 2 * (1 - criticalScatteringPt τ) ≠ 2 := by
    intro he
    have hr := congrArg Complex.re he
    simp [criticalScatteringPt] at hr
  have hstate : ((state (2 * (1 - criticalScatteringPt τ))).1 zeroPoint) / 2 =
      (starRingEnd ℂ) (riemannZeta (_root_.RHTower.linePt τ)) := by
    rw [state_zero hw_pos hw_ne2,
      show 2 * (1 - criticalScatteringPt τ) - 1 = 1 - 2 * criticalScatteringPt τ by ring,
      one_sub_two_mul_criticalScatteringPt,
      _root_.RHTower.riemannZeta_conj_of_re_pos (_root_.RHTower.linePt_re_pos τ)
        (fun h => by have hr := congrArg Complex.re h; rw [_root_.RHTower.linePt_re] at hr; norm_num at hr)]
    ring
  unfold mayerComplexZ
  rw [hphase, hstate]
  have hconj := congrArg (starRingEnd ℂ) (_root_.RHTower.conj_gammaHardyPhase_mul_zeta_eq_hardyZ τ)
  simpa only [map_mul, Complex.conj_conj, Complex.conj_ofReal] using hconj

/-- Exact critical-line reality: the imaginary part of `mayerComplexZ` vanishes identically along
`Re s = 1/4`. -/
theorem mayerComplexZ_critical_im (τ : ℝ) :
    (mayerComplexZ (criticalScatteringPt τ)).im = 0 := by
  rw [mayerComplexZ_critical_eq_ofReal_hardyZ, Complex.ofReal_im]

/-- Embedding `mayerZ τ` into `ℂ` recovers `mayerComplexZ` on the critical scattering line. -/
theorem ofReal_mayerZ_eq_mayerComplexZ (τ : ℝ) :
    (mayerZ τ : ℂ) = mayerComplexZ (criticalScatteringPt τ) := by
  unfold mayerZ
  rw [mayerComplexZ_critical_eq_ofReal_hardyZ, Complex.ofReal_re]

/-- Exact equality `mayerZ = hardyZ` on `ℝ`. -/
theorem mayerZ_eq_hardyZ (τ : ℝ) : mayerZ τ = _root_.RHTower.hardyZ τ := by
  unfold mayerZ
  rw [mayerComplexZ_critical_eq_ofReal_hardyZ, Complex.ofReal_re]

@[simp]
theorem mayerZ_neg (τ : ℝ) : mayerZ (-τ) = mayerZ τ := by
  rw [mayerZ_eq_hardyZ, mayerZ_eq_hardyZ, _root_.RHTower.hardyZ_neg]

theorem mayerZ_zero_lt_zero : mayerZ 0 < 0 := by
  rw [mayerZ_eq_hardyZ]
  exact _root_.RHTower.hardyZ_zero_height_neg

theorem differentiable_mayerZ : Differentiable ℝ mayerZ := by
  simpa only [funext mayerZ_eq_hardyZ] using _root_.RHTower.differentiable_hardyZ

theorem continuous_mayerZ : Continuous mayerZ :=
  differentiable_mayerZ.continuous

/-- Zeros of `mayerZ` are exactly the critical-line Mayer scattering resonances. -/
theorem mayerZ_eq_zero_iff_resonance (τ : ℝ) :
    mayerZ τ = 0 ↔ IsMayerScatteringResonance (criticalScatteringPt τ) := by
  have h0 : 0 < (criticalScatteringPt τ).re := by rw [criticalScatteringPt_re]; norm_num
  have h1 : (criticalScatteringPt τ).re < 1 / 2 := by rw [criticalScatteringPt_re]; norm_num
  rw [mayerZ_eq_hardyZ, ← _root_.RHTower.riemannZeta_line_eq_zero_iff_hardyZ,
    isMayerScatteringResonance_iff_zeta_zero h0 h1, two_mul_criticalScatteringPt]

/-! ## Strict sign changes and transverse core-moment slope formula -/

/-- Every strict sign change of `mayerZ` encloses a critical-line Mayer scattering resonance of
odd Fredholm determinant-excess multiplicity. -/
theorem exists_odd_mayerResonance_of_mayerZ_sign_change {τ₁ τ₂ : ℝ} (hτ : τ₁ < τ₂)
    (hsign : mayerZ τ₁ * mayerZ τ₂ < 0) :
    ∃ τ' ∈ Ioo τ₁ τ₂, IsMayerScatteringResonance (criticalScatteringPt τ') ∧
      Odd (mayerResonanceMultiplicity (criticalScatteringPt τ')) := by
  rw [mayerZ_eq_hardyZ, mayerZ_eq_hardyZ] at hsign
  obtain ⟨τ', hmem, hxi0, hodd⟩ :=
    _root_.RHTower.exists_odd_order_line_zero_of_hardyZ_sign_flip hτ hsign
  have h0 : 0 < (criticalScatteringPt τ').re := by rw [criticalScatteringPt_re]; norm_num
  have h1 : (criticalScatteringPt τ').re < 1 / 2 := by rw [criticalScatteringPt_re]; norm_num
  refine ⟨τ', hmem, ?_, ?_⟩
  · rw [isMayerScatteringResonance_iff_xi_zero h0 h1, two_mul_criticalScatteringPt]
    exact hxi0
  · rw [mayerResonanceMultiplicity_eq_zeta_order h0 h1, two_mul_criticalScatteringPt]
    have hstrip : 0 < (_root_.RHTower.linePt τ').re ∧ (_root_.RHTower.linePt τ').re < 1 := by
      rw [_root_.RHTower.linePt_re]
      exact ⟨by norm_num, by norm_num⟩
    have hord := _root_.RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hstrip
    simpa only [analyticOrderNatAt, hord] using hodd

/-- At any critical-line zero `mayerZ τ₀ = 0`, `(deriv mayerZ τ₀ : ℂ)` equals
`I * conj (gammaHardyPhase τ₀) * deriv riemannZeta (linePt τ₀)`. -/
theorem ofReal_deriv_mayerZ_eq_of_zero {τ₀ : ℝ} (hzero : mayerZ τ₀ = 0) :
    (deriv mayerZ τ₀ : ℂ) =
      I * (starRingEnd ℂ) (_root_.RHTower.gammaHardyPhase τ₀) *
        deriv riemannZeta (_root_.RHTower.linePt τ₀) := by
  have hne1 : _root_.RHTower.linePt τ₀ ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    rw [_root_.RHTower.linePt_re] at hr
    norm_num at hr
  have hleft : HasDerivAt (fun u : ℝ => riemannZeta (_root_.RHTower.linePt u))
      (deriv riemannZeta (_root_.RHTower.linePt τ₀) * I) τ₀ := by
    have hc := HasDerivAt.comp τ₀ (differentiableAt_riemannZeta hne1).hasDerivAt
      (_root_.RHTower.hasDerivAt_linePt τ₀)
    simpa [Function.comp] using hc
  have hZ : HasDerivAt (fun u : ℝ => (mayerZ u : ℂ)) (deriv mayerZ τ₀ : ℂ) τ₀ := by
    have hc := (Complex.ofRealCLM.hasDerivAt (x := mayerZ τ₀)).comp τ₀
      (differentiable_mayerZ τ₀).hasDerivAt
    simpa [Function.comp] using hc
  have hprod : (fun u : ℝ => riemannZeta (_root_.RHTower.linePt u)) =
      fun u : ℝ => _root_.RHTower.gammaHardyPhase u * (mayerZ u : ℂ) := by
    ext u
    rw [_root_.RHTower.riemannZeta_line_eq_gammaHardyPhase_mul_hardyZ, mayerZ_eq_hardyZ]
  have hright : HasDerivAt (fun u : ℝ => _root_.RHTower.gammaHardyPhase u * (mayerZ u : ℂ))
      (_root_.RHTower.gammaHardyPhase τ₀ * (deriv mayerZ τ₀ : ℂ)) τ₀ := by
    have hm := (_root_.RHTower.hasDerivAt_gammaHardyPhase τ₀).mul hZ
    simpa only [hzero, Complex.ofReal_zero, mul_zero, zero_add] using hm
  rw [hprod] at hleft
  have heq := hright.unique hleft
  have hunit : (starRingEnd ℂ) (_root_.RHTower.gammaHardyPhase τ₀) *
      _root_.RHTower.gammaHardyPhase τ₀ = 1 :=
    (_root_.RHTower.gammaHardyPhase_isUnitary τ₀)
  calc
    (deriv mayerZ τ₀ : ℂ) =
        ((starRingEnd ℂ) (_root_.RHTower.gammaHardyPhase τ₀) *
          _root_.RHTower.gammaHardyPhase τ₀) * (deriv mayerZ τ₀ : ℂ) := by
      rw [hunit, one_mul]
    _ = (starRingEnd ℂ) (_root_.RHTower.gammaHardyPhase τ₀) *
          (_root_.RHTower.gammaHardyPhase τ₀ * (deriv mayerZ τ₀ : ℂ)) := by ring
    _ = (starRingEnd ℂ) (_root_.RHTower.gammaHardyPhase τ₀) *
          (deriv riemannZeta (_root_.RHTower.linePt τ₀) * I) := by rw [heq]
    _ = I * (starRingEnd ℂ) (_root_.RHTower.gammaHardyPhase τ₀) *
          deriv riemannZeta (_root_.RHTower.linePt τ₀) := by ring

/-- **Transverse Mayer core-moment slope formula.** At every positive critical-line Mayer
scattering resonance `s₀ = criticalScatteringPt τ₀` (`τ₀ > 0`), the complexified slope
`(deriv mayerZ τ₀ : ℂ)` is given directly by the zero-endpoint Mellin moment of the
scattering-subtracted Mayer core `fieldCore (2 * s₀)`. -/
theorem ofReal_deriv_mayerZ_eq_core_mellin_zero {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hres : IsMayerScatteringResonance (criticalScatteringPt τ₀)) :
    (deriv mayerZ τ₀ : ℂ) =
      I * (starRingEnd ℂ) (_root_.RHTower.gammaHardyPhase τ₀) *
        mellin (fieldCore (2 * criticalScatteringPt τ₀)) 0 := by
  have hz : mayerZ τ₀ = 0 := (mayerZ_eq_zero_iff_resonance τ₀).mpr hres
  have h0 : 0 < (criticalScatteringPt τ₀).re := hres.1
  have h1 : (criticalScatteringPt τ₀).re < 1 / 2 := hres.2.1
  have hzeta0 : riemannZeta (2 * criticalScatteringPt τ₀) = 0 :=
    (isMayerScatteringResonance_iff_zeta_zero h0 h1).mp hres
  have hw0 : 0 < (2 * criticalScatteringPt τ₀).re := by simp [criticalScatteringPt]
  have hw1 : (2 * criticalScatteringPt τ₀).re < 1 := by simp [criticalScatteringPt]; norm_num
  have him : 0 < (2 * criticalScatteringPt τ₀).im := by
    rw [two_mul_criticalScatteringPt, _root_.RHTower.linePt_im]
    exact hτ₀
  have hm := (core_zero_hasMellin_zero hw0 hw1 him hzeta0).2
  rw [ofReal_deriv_mayerZ_eq_of_zero hz, ← two_mul_criticalScatteringPt, ← hm]

theorem deriv_mayerZ_eq_re_core_mellin_zero {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hres : IsMayerScatteringResonance (criticalScatteringPt τ₀)) :
    deriv mayerZ τ₀ =
      (I * (starRingEnd ℂ) (_root_.RHTower.gammaHardyPhase τ₀) *
        mellin (fieldCore (2 * criticalScatteringPt τ₀)) 0).re := by
  have h := congrArg Complex.re (ofReal_deriv_mayerZ_eq_core_mellin_zero hτ₀ hres)
  simpa only [Complex.ofReal_re] using h

private theorem analyticOrderNatAt_zeta_eq_one_iff_deriv_ne_zero {w : ℂ}
    (hw1 : w ≠ 1) (hz : riemannZeta w = 0) :
    analyticOrderNatAt riemannZeta w = 1 ↔ deriv riemannZeta w ≠ 0 := by
  have han : AnalyticAt ℂ riemannZeta w := analyticAt_riemannZeta hw1
  have hfin : analyticOrderAt riemannZeta w ≠ ⊤ := by
    have hZ : AnalyticOnNhd ℂ _root_.RHTower.zetaResidueUnit univ :=
      fun z _ => _root_.RHTower.analyticAt_zetaResidueUnit z
    have hZ1 : _root_.RHTower.zetaResidueUnit 1 ≠ 0 := by
      simp [_root_.RHTower.zetaResidueUnit]
    have hfinite := hZ.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 1) (mem_univ 1) (mem_univ w)
      (by rw [(hZ 1 (mem_univ 1)).analyticOrderAt_eq_zero.mpr hZ1]; exact ENat.zero_ne_top)
    intro htop
    apply hfinite
    apply analyticOrderAt_eq_top.mpr
    filter_upwards [analyticOrderAt_eq_top.mp htop, isOpen_ne.mem_nhds hw1] with z hzz hz1
    rw [_root_.RHTower.zetaResidueUnit, Function.update_of_ne hz1, hzz, mul_zero]
  set n : ℕ := analyticOrderNatAt riemannZeta w
  have hn_eq : analyticOrderAt riemannZeta w = (n : ℕ∞) := (ENat.coe_toNat hfin).symm
  have hn_pos : 0 < n := by
    have hne0 : analyticOrderAt riemannZeta w ≠ 0 := han.analyticOrderAt_ne_zero.mpr hz
    rw [hn_eq] at hne0
    omega
  obtain ⟨g, hgan, hg0, hfac⟩ := (han.analyticOrderAt_eq_natCast (n := n)).mp hn_eq
  constructor
  · intro hn1
    subst hn1
    have hderivEq : deriv riemannZeta w = deriv (fun z => (z - w) * g z) w :=
      Filter.EventuallyEq.deriv_eq (by filter_upwards [hfac] with z hzz; simpa [smul_eq_mul] using hzz)
    have hhas : HasDerivAt (fun z => (z - w) * g z) (1 * g w + (w - w) * deriv g w) w :=
      ((hasDerivAt_id w).sub_const w).mul hgan.differentiableAt.hasDerivAt
    rw [hderivEq, hhas.deriv]
    simpa using hg0
  · intro hd
    by_contra hne1
    have hn2 : 2 ≤ n := by omega
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
    have hderivEq : deriv riemannZeta w =
        deriv (fun z => (z - w) * ((z - w) ^ (m + 1) * g z)) w := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hfac] with z hzz
      rw [hzz, smul_eq_mul]
      ring
    have htail : DifferentiableAt ℂ (fun z => (z - w) ^ (m + 1) * g z) w :=
      (((differentiableAt_id).sub_const w).pow (m + 1)).mul hgan.differentiableAt
    have hhas : HasDerivAt (fun z => (z - w) * ((z - w) ^ (m + 1) * g z))
        (1 * ((w - w) ^ (m + 1) * g w) + (w - w) * deriv (fun z => (z - w) ^ (m + 1) * g z) w) w :=
      ((hasDerivAt_id w).sub_const w).mul htail.hasDerivAt
    rw [hderivEq, hhas.deriv] at hd
    simp at hd

/-- At a positive critical-line Mayer scattering resonance, nonvanishing of `deriv mayerZ τ₀`,
nonvanishing of `mellin (fieldCore (2 * s₀)) 0`, and unit resonance multiplicity are equivalent. -/
theorem deriv_mayerZ_ne_zero_iff_simple_resonance {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hres : IsMayerScatteringResonance (criticalScatteringPt τ₀)) :
    deriv mayerZ τ₀ ≠ 0 ↔
      mellin (fieldCore (2 * criticalScatteringPt τ₀)) 0 ≠ 0 ∧
        mayerResonanceMultiplicity (criticalScatteringPt τ₀) = 1 := by
  have hphase_ne : (starRingEnd ℂ) (_root_.RHTower.gammaHardyPhase τ₀) ≠ 0 := by
    simpa using (_root_.RHTower.gammaHardyPhase_isUnitary τ₀).ne_zero
  have hunit_ne : I * (starRingEnd ℂ) (_root_.RHTower.gammaHardyPhase τ₀) ≠ 0 :=
    mul_ne_zero I_ne_zero hphase_ne
  have hm_iff : deriv mayerZ τ₀ ≠ 0 ↔
      mellin (fieldCore (2 * criticalScatteringPt τ₀)) 0 ≠ 0 := by
    rw [← Complex.ofReal_ne_zero, ofReal_deriv_mayerZ_eq_core_mellin_zero hτ₀ hres,
      mul_ne_zero_iff, and_iff_right hunit_ne]
  have h0 : 0 < (criticalScatteringPt τ₀).re := hres.1
  have h1 : (criticalScatteringPt τ₀).re < 1 / 2 := hres.2.1
  have hzeta0 : riemannZeta (2 * criticalScatteringPt τ₀) = 0 :=
    (isMayerScatteringResonance_iff_zeta_zero h0 h1).mp hres
  have hw0 : 0 < (2 * criticalScatteringPt τ₀).re := by simp [criticalScatteringPt]
  have hw1 : (2 * criticalScatteringPt τ₀).re < 1 := by simp [criticalScatteringPt]; norm_num
  have him : 0 < (2 * criticalScatteringPt τ₀).im := by
    rw [two_mul_criticalScatteringPt, _root_.RHTower.linePt_im]
    exact hτ₀
  have hwne1 : 2 * criticalScatteringPt τ₀ ≠ 1 := fun he => by
    rw [he, Complex.one_re] at hw1
    exact lt_irrefl 1 hw1
  have hm_eq := (core_zero_hasMellin_zero hw0 hw1 him hzeta0).2
  have hmult_iff : mayerResonanceMultiplicity (criticalScatteringPt τ₀) = 1 ↔
      mellin (fieldCore (2 * criticalScatteringPt τ₀)) 0 ≠ 0 := by
    rw [mayerResonanceMultiplicity_eq_zeta_order h0 h1,
      analyticOrderNatAt_zeta_eq_one_iff_deriv_ne_zero hwne1 hzeta0, hm_eq]
  exact ⟨fun hd => ⟨hm_iff.mp hd, hmult_iff.mpr (hm_iff.mp hd)⟩, fun h => hm_iff.mpr h.1⟩

/-- Elementary real-calculus converse: a zero with nonzero derivative forces a strict sign change
on every sufficiently small symmetric punctured interval `(τ₀ - δ, τ₀ + δ)`. -/
theorem exists_local_sign_change_of_deriv_ne_zero {f : ℝ → ℝ} {τ₀ : ℝ}
    (hf : DifferentiableAt ℝ f τ₀) (hf0 : f τ₀ = 0) (hd : deriv f τ₀ ≠ 0) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → f (τ₀ - δ) * f (τ₀ + δ) < 0 := by
  set L : ℝ := deriv f τ₀
  have hlim : Tendsto (fun h : ℝ => h⁻¹ * (f (τ₀ + h) - f τ₀)) (𝓝[≠] 0) (𝓝 L) := by
    simpa [hasDerivAt_iff_tendsto_slope_zero] using hf.hasDerivAt
  have hposL : 0 < |L| / 2 := half_pos (abs_pos.mpr hd)
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim (|L| / 2) hposL
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ?_⟩
  have h1 : dist (δ⁻¹ * (f (τ₀ + δ) - f τ₀)) L < |L| / 2 :=
    hball (Set.mem_compl_singleton_iff.mpr hδ.ne') (by simpa [Real.dist_eq, abs_of_pos hδ] using hδlt)
  have h2 : dist ((-δ)⁻¹ * (f (τ₀ + -δ) - f τ₀)) L < |L| / 2 :=
    hball (Set.mem_compl_singleton_iff.mpr (neg_ne_zero.mpr hδ.ne'))
      (by simpa [Real.dist_eq, abs_neg, abs_of_pos hδ] using hδlt)
  rw [hf0, sub_zero, Real.dist_eq] at h1 h2
  rw [show τ₀ + -δ = τ₀ - δ by ring, inv_neg, neg_mul] at h2
  set q₁ : ℝ := δ⁻¹ * f (τ₀ + δ)
  set q₂ : ℝ := -(δ⁻¹ * f (τ₀ - δ))
  have hprod_pos : 0 < q₁ * q₂ := by
    rcases lt_trichotomy L 0 with hLneg | rfl | hLpos
    · have hLabs : |L| = -L := abs_of_neg hLneg
      have hq1 : q₁ < 0 := by linarith [(abs_lt.mp h1).2]
      have hq2 : q₂ < 0 := by linarith [(abs_lt.mp h2).2]
      exact mul_pos_of_neg_of_neg hq1 hq2
    · exact absurd rfl hd
    · have hLabs : |L| = L := abs_of_pos hLpos
      have hq1 : 0 < q₁ := by linarith [(abs_lt.mp h1).1]
      have hq2 : 0 < q₂ := by linarith [(abs_lt.mp h2).1]
      exact mul_pos hq1 hq2
  have heq : q₁ * q₂ = -(δ⁻¹ ^ 2 * (f (τ₀ - δ) * f (τ₀ + δ))) := by
    dsimp [q₁, q₂]
    ring
  rw [heq] at hprod_pos
  have hsq : 0 < δ⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hδ)
  nlinarith

/-- Every simple positive critical-line Mayer resonance forces a strict local sign change of
`mayerZ`. -/
theorem exists_local_mayerZ_sign_change_of_simple_resonance {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (hres : IsMayerScatteringResonance (criticalScatteringPt τ₀))
    (hmult : mayerResonanceMultiplicity (criticalScatteringPt τ₀) = 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      mayerZ (τ₀ - δ) * mayerZ (τ₀ + δ) < 0 := by
  have hz : mayerZ τ₀ = 0 := (mayerZ_eq_zero_iff_resonance τ₀).mpr hres
  have hd : deriv mayerZ τ₀ ≠ 0 := by
    have h0 := hres.1
    have h1 := hres.2.1
    have hzeta0 := (isMayerScatteringResonance_iff_zeta_zero h0 h1).mp hres
    have hw0 : 0 < (2 * criticalScatteringPt τ₀).re := by simp [criticalScatteringPt]
    have hw1 : (2 * criticalScatteringPt τ₀).re < 1 := by simp [criticalScatteringPt]; norm_num
    have him : 0 < (2 * criticalScatteringPt τ₀).im := by
      rw [two_mul_criticalScatteringPt, _root_.RHTower.linePt_im]
      exact hτ₀
    have hwne1 : 2 * criticalScatteringPt τ₀ ≠ 1 := fun he => by
      rw [he, Complex.one_re] at hw1
      exact lt_irrefl 1 hw1
    have hm_eq := (core_zero_hasMellin_zero hw0 hw1 him hzeta0).2
    rw [mayerResonanceMultiplicity_eq_zeta_order h0 h1,
      analyticOrderNatAt_zeta_eq_one_iff_deriv_ne_zero hwne1 hzeta0, ← hm_eq] at hmult
    exact (deriv_mayerZ_ne_zero_iff_simple_resonance hτ₀ hres).mpr
      ⟨hmult, by
        rw [mayerResonanceMultiplicity_eq_zeta_order h0 h1,
          analyticOrderNatAt_zeta_eq_one_iff_deriv_ne_zero hwne1 hzeta0, ← hm_eq]
        exact hmult⟩
  exact exists_local_sign_change_of_deriv_ne_zero (differentiable_mayerZ τ₀) hz hd

/-! ## Cumulative Mayer resonance census, Hardy's theorem, and `> 67.250071%` sign proportion -/

/-- Finite set of upper Mayer scattering resonances up to scaled height `T` (`0 < Im (2s) ≤ T`). -/
def mayerResonanceFinset (T : ℝ) : Finset ℂ :=
  (_root_.RHTower.stripFinsetPos T).map
    ⟨fun z : ℂ => z / 2, fun a b h => by linear_combination 2 * h⟩

theorem mem_mayerResonanceFinset {T : ℝ} {s : ℂ} :
    s ∈ mayerResonanceFinset T ↔
      IsMayerScatteringResonance s ∧ 0 < (2 * s).im ∧ (2 * s).im ≤ T := by
  rw [mayerResonanceFinset, Finset.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hre0, hre1, him0, himT, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hz
    have hs0 : 0 < (z / 2).re := by simp; linarith
    have hs1 : (z / 2).re < 1 / 2 := by simp; linarith
    have h2 : 2 * (z / 2) = z := by ring
    refine ⟨(isMayerScatteringResonance_iff_xi_zero hs0 hs1).mpr (by rwa [h2]), ?_, ?_⟩ <;>
      rwa [h2]
  · rintro ⟨hs, him0, himT⟩
    obtain ⟨hs0, hs1, _⟩ := hs
    obtain ⟨hw0, hw1⟩ :=
      (show 0 < (2 * s).re ∧ (2 * s).re < 1 from ⟨by simp; linarith, by simp; linarith⟩)
    refine ⟨2 * s, _root_.RHTower.mem_stripFinsetPos.mpr
      ⟨hw0, hw1, him0, himT, (isMayerScatteringResonance_iff_xi_zero hs0 hs1).mp hs⟩, by ring⟩

/-- Cumulative Mayer scattering resonance count with Fredholm determinant-excess multiplicity. -/
def mayerResonanceCount (T : ℝ) : ℕ :=
  ∑ s ∈ mayerResonanceFinset T, mayerResonanceMultiplicity s

/-- Exact census identity `mayerResonanceCount T = xiPosZeroCount T = Zeta23.Ncount 0 T`. -/
theorem mayerResonanceCount_eq_xiPosZeroCount (T : ℝ) :
    mayerResonanceCount T = _root_.RHTower.xiPosZeroCount T := by
  unfold mayerResonanceCount mayerResonanceFinset _root_.RHTower.xiPosZeroCount
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hre0, hre1, _, _, _⟩ := _root_.RHTower.mem_stripFinsetPos.mp hz
  have hs0 : 0 < (z / 2).re := by simp; linarith
  have hs1 : (z / 2).re < 1 / 2 := by simp; linarith
  have h2 : 2 * (z / 2) = z := by ring
  change mayerResonanceMultiplicity (z / 2) = (analyticOrderAt _root_.RHTower.xi z).toNat
  rw [mayerResonanceMultiplicity_eq_zeta_order hs0 hs1, h2, analyticOrderNatAt,
    _root_.RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨hre0, hre1⟩]

theorem mayerResonanceCount_eq_Ncount (T : ℝ) :
    mayerResonanceCount T = Zeta23.Ncount 0 T := by
  rw [mayerResonanceCount_eq_xiPosZeroCount, _root_.RHTower.zeta23_Ncount_zero_eq_xiPosZeroCount]

/-- **Quantitative positive proportion (`> 67.250071%`) of pairwise disjoint strict sign changes
of `mayerZ`.** For every `ε > 0`, for all sufficiently large `T`, there exist `m` strictly
ordered, pairwise disjoint open intervals `(a j, b j) ⊂ (0, T)` with
`m ≥ (67250071 / 100000000 - ε) * mayerResonanceCount T` and `mayerZ (a j) * mayerZ (b j) < 0`. -/
theorem eventually_disjoint_mayerZ_sign_changes_proportion :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ∃ (m : ℕ) (a b : Fin m → ℝ),
        (67250071 / 100000000 - ε) * (mayerResonanceCount T : ℝ) ≤ (m : ℝ) ∧
        (∀ j : Fin m, 0 < a j ∧ a j < b j ∧ b j < T ∧ mayerZ (a j) * mayerZ (b j) < 0) ∧
        (∀ j₁ j₂ : Fin m, j₁ < j₂ → b j₁ < a j₂) := by
  intro ε hε
  by_cases hcoef : 67250071 / 100000000 - ε ≤ 0
  · refine ⟨1, fun T _ => ⟨0, Fin.elim0, Fin.elim0, ?_, fun j => j.elim0, fun j => j.elim0⟩⟩
    have hnn : (0 : ℝ) ≤ (mayerResonanceCount T : ℝ) := Nat.cast_nonneg _
    nlinarith
  push Not at hcoef
  obtain ⟨T₁, hT₁⟩ :=
    GaloisForLFunctions.IncommensurableGaborPinching.simple_critical_proportion_ge_67250071
      (ε / 2) (half_pos hε)
  have htop : Tendsto (fun T => (Zeta23.Ncount 0 T : ℝ)) atTop atTop :=
    Zeta23.tendsto_Ncount_zero_atTop Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
  have hevN : ∀ᶠ T : ℝ in atTop, 2 / ε ≤ (Zeta23.Ncount 0 T : ℝ) ∧
      2 / (67250071 / 100000000 - ε / 2) ≤ (Zeta23.Ncount 0 T : ℝ) :=
    (htop.eventually_ge_atTop (2 / ε)).and
      (htop.eventually_ge_atTop (2 / (67250071 / 100000000 - ε / 2)))
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp hevN
  refine ⟨max (max T₁ T₂) 1, fun T hT => ?_⟩
  have hT_T₁ : T₁ ≤ T := le_trans (le_trans (le_max_left T₁ T₂) (le_max_left _ 1)) hT
  have hT_T₂ : T₂ ≤ T := le_trans (le_trans (le_max_right T₁ T₂) (le_max_left _ 1)) hT
  obtain ⟨hN_eps, hN_two⟩ := hT₂ T hT_T₂
  have hprop := hT₁ T hT_T₁
  rw [_root_.RHTower.zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount] at hprop
  let Scomplex : Finset ℂ :=
    (_root_.RHTower.stripFinsetPos T).filter
      (fun z => z.re = 1 / 2 ∧ (analyticOrderAt _root_.RHTower.xi z).toNat = 1)
  have hScard : Scomplex.card = _root_.RHTower.xiSimpleCriticalZeroCount T := rfl
  let Sord : Finset ℝ := Scomplex.image Complex.im
  have hinj_im : Set.InjOn Complex.im (Scomplex : Set ℂ) := by
    intro z₁ hz₁ z₂ hz₂ him
    have hr1 : z₁.re = 1 / 2 := (Finset.mem_filter.mp hz₁).2.1
    have hr2 : z₂.re = 1 / 2 := (Finset.mem_filter.mp hz₂).2.1
    exact Complex.ext (hr1.trans hr2.symm) him
  have hSord_card : Sord.card = _root_.RHTower.xiSimpleCriticalZeroCount T := by
    rw [← hScard]
    exact Finset.card_image_of_injOn hinj_im
  have hk_real : (2 : ℝ) ≤ (Sord.card : ℝ) := by
    have hpos_c : 0 < (67250071 / 100000000 - ε / 2 : ℝ) := by linarith
    have h2le : 2 ≤ (67250071 / 100000000 - ε / 2) * (Zeta23.Ncount 0 T : ℝ) := by
      have := (div_le_iff₀ hpos_c).mp hN_two
      linarith
    rw [hSord_card]
    linarith
  have hk2 : 2 ≤ Sord.card := by exact_mod_cast hk_real
  let k : ℕ := Sord.card
  let γ : Fin k ↪o ℝ := Sord.orderEmbOfFin rfl
  let m : ℕ := k - 1
  have hm_pos : 0 < m := by omega
  have hγ_mem : ∀ i : Fin k, 0 < γ i ∧ γ i ≤ T ∧
      IsMayerScatteringResonance (criticalScatteringPt (γ i)) ∧
      mayerResonanceMultiplicity (criticalScatteringPt (γ i)) = 1 := by
    intro i
    have hmem_im : γ i ∈ Sord := Sord.orderEmbOfFin_mem rfl i
    obtain ⟨z, hz, hzim⟩ := Finset.mem_image.mp hmem_im
    obtain ⟨hz_strip, hz_re, hz_ord⟩ := Finset.mem_filter.mp hz
    obtain ⟨h0, h1, him0, himT, hxi⟩ := _root_.RHTower.mem_stripFinsetPos.mp hz_strip
    have hz_eq : z = 2 * criticalScatteringPt (γ i) := by
      rw [two_mul_criticalScatteringPt]
      apply Complex.ext
      · rw [hz_re, _root_.RHTower.linePt_re]
      · rw [← hzim, _root_.RHTower.linePt_im]
    have hs0 : 0 < (criticalScatteringPt (γ i)).re := by rw [criticalScatteringPt_re]; norm_num
    have hs1 : (criticalScatteringPt (γ i)).re < 1 / 2 := by rw [criticalScatteringPt_re]; norm_num
    refine ⟨by linarith [hzim], by linarith [hzim], ?_, ?_⟩
    · rw [isMayerScatteringResonance_iff_xi_zero hs0 hs1, ← hz_eq]
      exact hxi
    · rw [mayerResonanceMultiplicity_eq_zeta_order hs0 hs1, ← hz_eq, analyticOrderNatAt,
        ← _root_.RHTower.xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩, hz_ord]
  have hγ_lt_T : ∀ j : Fin m, γ ⟨j.1, by omega⟩ < T := by
    intro j
    have hlt : γ ⟨j.1, by omega⟩ < γ ⟨j.1 + 1, by omega⟩ :=
      γ.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j.1))
    exact lt_of_lt_of_le hlt (hγ_mem ⟨j.1 + 1, by omega⟩).2.1
  have hex_δ : ∀ j : Fin m, ∃ δj : ℝ, 0 < δj ∧
      δj ≤ γ ⟨j.1, by omega⟩ / 2 ∧
      δj ≤ (T - γ ⟨j.1, by omega⟩) / 2 ∧
      δj ≤ (γ ⟨j.1 + 1, by omega⟩ - γ ⟨j.1, by omega⟩) / 3 ∧
      ∀ δ : ℝ, 0 < δ → δ < δj →
        mayerZ (γ ⟨j.1, by omega⟩ - δ) * mayerZ (γ ⟨j.1, by omega⟩ + δ) < 0 := by
    intro j
    let idx : Fin k := ⟨j.1, by omega⟩
    let idx1 : Fin k := ⟨j.1 + 1, by omega⟩
    obtain ⟨hpos_i, _, hres_i, hmult_i⟩ := hγ_mem idx
    obtain ⟨δ₀, hδ₀, hflip⟩ := exists_local_mayerZ_sign_change_of_simple_resonance hpos_i hres_i hmult_i
    have hlt_T : γ idx < T := hγ_lt_T j
    have hgap : γ idx < γ idx1 := γ.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j.1))
    let δj : ℝ := min (min δ₀ (γ idx / 2)) (min ((T - γ idx) / 2) ((γ idx1 - γ idx) / 3))
    have hδj_pos : 0 < δj :=
      lt_min (lt_min hδ₀ (half_pos hpos_i))
        (lt_min (half_pos (sub_pos.mpr hlt_T)) (div_pos (sub_pos.mpr hgap) (by norm_num)))
    refine ⟨δj, hδj_pos,
      (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _),
      fun δ hδ hδlt => hflip δ hδ (lt_of_lt_of_le hδlt ((min_le_left _ _).trans (min_le_left _ _)))⟩
  choose δf hδf_pos hδf_low hδf_high hδf_gap hδf_flip using hex_δ
  have hne_univ : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm_pos⟩, Finset.mem_univ _⟩
  let δmin : ℝ := (Finset.univ.image δf).min' (hne_univ.image _)
  have hδmin_pos : 0 < δmin := by
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp (Finset.min'_mem (Finset.univ.image δf) (hne_univ.image _))
    exact hδf_pos y
  let δ : ℝ := δmin / 2
  have hδ_pos : 0 < δ := half_pos hδmin_pos
  have hδ_lt : ∀ j : Fin m, δ < δf j := by
    intro j
    have hle : δmin ≤ δf j := Finset.min'_le _ _ (Finset.mem_image_of_mem δf (Finset.mem_univ j))
    dsimp [δ]
    linarith
  refine ⟨m, fun j => γ ⟨j.1, by omega⟩ - δ, fun j => γ ⟨j.1, by omega⟩ + δ, ?_, ?_, ?_⟩
  · have hm_cast : (m : ℝ) = (k : ℝ) - 1 := by
      have hk1 : 1 ≤ k := by omega
      dsimp [m]
      exact Nat.cast_sub hk1
    have h1_le : (1 : ℝ) ≤ (ε / 2) * (Zeta23.Ncount 0 T : ℝ) := by
      have := (div_le_iff₀ hε).mp hN_eps
      linarith
    rw [mayerResonanceCount_eq_Ncount, hm_cast]
    have hk_eq : (k : ℝ) = (_root_.RHTower.xiSimpleCriticalZeroCount T : ℝ) := by
      exact_mod_cast hSord_card
    linarith
  · intro j
    have hlt := hδ_lt j
    have hlow := hδf_low j
    have hhigh := hδf_high j
    exact ⟨by linarith, by linarith, by linarith, hδf_flip j δ hδ_pos hlt⟩
  · intro j₁ j₂ hj
    have hj_succ : j₁.1 + 1 ≤ j₂.1 := hj
    have hmono : γ ⟨j₁.1 + 1, by omega⟩ ≤ γ ⟨j₂.1, by omega⟩ :=
      γ.monotone (Fin.mk_le_mk.mpr hj_succ)
    have hlt1 := hδ_lt j₁
    have hgap1 := hδf_gap j₁
    linarith

/-- **Operator Hardy Theorem.** `mayerZ` undergoes strict sign changes at arbitrarily large
heights `τ → +∞`. -/
theorem exists_mayerZ_sign_change_gt (M : ℝ) :
    ∃ τ₁ τ₂ : ℝ, M < τ₁ ∧ τ₁ < τ₂ ∧ mayerZ τ₁ * mayerZ τ₂ < 0 := by
  let S₀ : ℝ := max M 1
  obtain ⟨T₁, hsimple⟩ := Zeta23.thmB₀_mult (1 / 3) (by norm_num)
  have hN_ev : ∀ᶠ S : ℝ in atTop,
      S * Zeta23.l S / (4 * Real.pi) ≤ (Zeta23.Ncount S (2 * S) : ℝ) := by
    simpa only [Zeta23.zetaZeroConfig_N] using
      Zeta23.Assembly.eventually_N_ge Zeta23.zetaZeroConfig Zeta23.paperInputs_zeta.RvM
  have hl_ev : ∀ᶠ S : ℝ in atTop, 12 * Real.pi ≤ Zeta23.l S :=
    Zeta23.Assembly.tendsto_l_atTop.eventually_ge_atTop (12 * Real.pi)
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp (hN_ev.and hl_ev)
  let S : ℝ := max (max S₀ T₁) T₂
  have hS_S₀ : S₀ ≤ S := le_trans (le_max_left S₀ T₁) (le_max_left _ T₂)
  have hS_M : M ≤ S := le_trans (le_max_left M 1) hS_S₀
  have hS_1 : (1 : ℝ) ≤ S := le_trans (le_max_right M 1) hS_S₀
  have hS_T₁ : T₁ ≤ S := le_trans (le_max_right S₀ T₁) (le_max_left _ T₂)
  have hS_T₂ : T₂ ≤ S := le_max_right _ T₂
  obtain ⟨hNS, hlS⟩ := hT₂ S hS_T₂
  have hsimpS := hsimple S hS_T₁
  have hNcount_ge : (3 : ℝ) ≤ (Zeta23.Ncount S (2 * S) : ℝ) := by
    have hprod : 12 * Real.pi ≤ S * Zeta23.l S := by nlinarith [Real.pi_pos]
    have hdiv : 3 ≤ S * Zeta23.l S / (4 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hN0_pos : 0 < Zeta23.N0simple S (2 * S) := by
    have h1le : (1 : ℝ) ≤ (Zeta23.N0simple S (2 * S) : ℝ) := by
      norm_num at hsimpS
      linarith
    exact_mod_cast (show (0 : ℝ) < (Zeta23.N0simple S (2 * S) : ℝ) by linarith)
  unfold Zeta23.N0simple at hN0_pos
  obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero hN0_pos.ne'
  rcases hz with ⟨⟨⟨⟨hzeta, hre0, hre1⟩, hS_lt_im, _⟩, hz_line⟩, hz_mult⟩
  let τ₀ : ℝ := z.im
  have hτ₀_pos : 0 < τ₀ := by linarith
  have hz_eq : z = 2 * criticalScatteringPt τ₀ := by
    rw [two_mul_criticalScatteringPt]
    apply Complex.ext
    · rw [hz_line, _root_.RHTower.linePt_re]
    · rw [_root_.RHTower.linePt_im]
  have hs0 : 0 < (criticalScatteringPt τ₀).re := by rw [criticalScatteringPt_re]; norm_num
  have hs1 : (criticalScatteringPt τ₀).re < 1 / 2 := by rw [criticalScatteringPt_re]; norm_num
  have hres : IsMayerScatteringResonance (criticalScatteringPt τ₀) := by
    rw [isMayerScatteringResonance_iff_zeta_zero hs0 hs1, ← hz_eq]
    exact hzeta
  have hmult : mayerResonanceMultiplicity (criticalScatteringPt τ₀) = 1 := by
    rw [mayerResonanceMultiplicity_eq_zeta_order hs0 hs1, ← hz_eq, analyticOrderNatAt]
    exact hz_mult
  obtain ⟨δ₀, hδ₀, hflip⟩ := exists_local_mayerZ_sign_change_of_simple_resonance hτ₀_pos hres hmult
  let δ : ℝ := min δ₀ (τ₀ - S) / 2
  have hδ_pos : 0 < δ := half_pos (lt_min hδ₀ (sub_pos.mpr hS_lt_im))
  have hδ_lt_δ₀ : δ < δ₀ := by
    have hle := min_le_left δ₀ (τ₀ - S)
    dsimp [δ]
    linarith
  have hδ_lt_gap : δ < τ₀ - S := by
    have hle := min_le_right δ₀ (τ₀ - S)
    dsimp [δ]
    linarith
  exact ⟨τ₀ - δ, τ₀ + δ, by linarith, by linarith, hflip δ hδ_pos hδ_lt_δ₀⟩

#print axioms mayerComplexZ_critical_eq_ofReal_hardyZ
#print axioms mayerComplexZ_critical_im
#print axioms mayerZ_eq_zero_iff_resonance
#print axioms exists_odd_mayerResonance_of_mayerZ_sign_change
#print axioms ofReal_deriv_mayerZ_eq_core_mellin_zero
#print axioms deriv_mayerZ_ne_zero_iff_simple_resonance
#print axioms eventually_disjoint_mayerZ_sign_changes_proportion
#print axioms exists_mayerZ_sign_change_gt

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
