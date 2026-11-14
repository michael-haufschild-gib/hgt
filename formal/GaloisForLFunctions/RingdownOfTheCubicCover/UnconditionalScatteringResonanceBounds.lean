import GaloisForLFunctions.RingdownOfTheCubicCover.BianchiHorizonRingdownEquivalence
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerResonanceCharacterization
import GaloisForLFunctions.FamilyContinuationTheory.TheSevenEighthsGeometryIsAVertex
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheTwoModeEnergiesRingDownAtTheZeroFreeRate
import GaloisForLFunctions.CountingHolography.ThermalizationFasterThanTheSquareRootIsAZeroFreeStrip
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateOfTheCuspEnergy
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

set_option autoImplicit false

/-!
# Unconditional Scattering Resonance Bounds and Horizon Ringdown Corollaries

Combining the metaplectic cubic Möbius cancellation on `SL₂(ℤ[ω])\ℍ³`
(`MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_seven_eighths_lt_re` and
`LFunction_ne_zero_of_seven_eighths_lt_re`) with the Bianchi and modular horizon ringdown
equivalences establishes unconditionally:

1. **Critical-strip confinement (`[1/8, 7/8]`) and zero abscissa bounds (`[1/2, 7/8]`)**:
   - Every nontrivial zero of `ζ(s)`, `L(s, χ₋₃)`, and `ζ_{ℚ(√−3)}(s) = ζ(s) L(s, χ₋₃)` (equivalently
     `xiBianchi` or `heckeLFunction (trivialModulus K) 1` for `K = ℚ(ζ₃)`) has real part in
     `[1/8, 7/8]` (`bianchiZeta_zero_mem_quasiRH_strip`, `xiBianchi_zero_mem_quasiRH_strip`).
   - Both global zero abscissas satisfy `1/2 ≤ Θ ≤ 7/8`
     (`zetaZeroAbscissa_mem_Icc`, `zeroAbscissa_chi3D_mem_Icc`).

2. **Mayer scattering resonance confinement (`Re s ∈ [1/16, 7/16]`)**:
   - Every Mayer scattering resonance (`IsMayerScatteringResonance s`) of `PSL₂(ℤ)\ℍ²` lies in the
     closed strip `1/16 ≤ Re s ≤ 7/16` (`isMayerScatteringResonance_re_mem_Icc`).
   - Outside `[1/16, 7/16]` inside `(0, 1/2)`, the Fredholm determinant-excess multiplicity
     `mayerResonanceMultiplicity s` vanishes identically and the Poincaré scattering entry has
     non-negative meromorphic order (`scatteringEntry_holomorphicOrder_nonneg_outside_strip`).

3. **Unconditional horizon ringdown and thermalization (`δ = 1/16`, `α = 9/16`)**:
   - Reflected compact pulses on the Bianchi horizon `SL₂(ℤ[ω])\ℍ³` and on the modular horizon
     `PSL₂(ℤ)\ℍ²` decay unconditionally as `O(e^{-(1/16 - ε)τ})` for every `ε > 0`
     (`bianchi_pulse_ringdown_one_sixteenth`, `modular_pulse_ringdown_one_sixteenth`).
   - Pseudo-Eisenstein horocycle means, Farey depth counts, Maass cusp-form horocycle energies, and
     all two-mode cuspidal cavity energies converge on `(0, 1]` at the unconditional polynomially
     accelerated rate `O(y^{9/16 - ε})` (strictly faster than Sarnak's `y^{1/2}` barrier).

4. **Horizon vertex balance at `δ = 1/16` (`σ₀ = 7/8`) and binding-bin upgrade threshold**:
   - At the published probe geometry `(lx, ly, ℓ) = (17/48, 23/48, 1/6)` along the dual-length face
     `lx + ly + ℓ = 1`, `lowBoundary = 7/8` (`δ = 1/16`) and the binding-bin exponent at
     `δ_bin = 79/204` equals `(13/16) · (R - 443/663)`, pinned at `-(7/30672) < 0` by
     `rowCount (79/204) (1/2) = 21766/32589 < 443/663` (`horizon_ringdown_vertex_balance`).
   - Along the dual-length edge `(17/48 - h/2, 23/48 - h/2, 1/6 + h)` (`0 < h < 17/24`), the low
     boundary shifts to `7/8 - h/4` (ringdown rate `1/16 + h/8 > 1/16`) and the binding-bin high
     exponent is strictly negative if and only if `R < (443 - 270 h) / (663 + 1224 h)`
     (`binding_bin_saving_iff_faster_ringdown`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.RingdownOfTheCubicCover

open GaloisForLFunctions.FamilyContinuationTheory
open GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
  (riemannZeta_ne_zero_of_seven_eighths_lt_re riemannZeta_ne_zero_of_re_lt_one_eighth
   riemannZeta_zero_mem_quasiRH_strip)
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-! ## 1. Unconditional `[1/8, 7/8]` Zero Confinement and Zero Abscissa Bounds -/

/-- `L(s, χ₋₃)` has no zeros in the half-plane `Re s > 7/8` (including `s = 1`, since `χ₋₃ ≠ 1`). -/
theorem LFunction_chi3D_ne_zero_of_seven_eighths_lt_re {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    _root_.DirichletCharacter.LFunction chi3D s ≠ 0 :=
  GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
    chi3D hs (fun h => chi3D_ne_one h.1)

/-- Functional-equation reflection gives `L(s, χ₋₃) ≠ 0` on `0 < Re s < 1/8`. -/
theorem LFunction_chi3D_ne_zero_of_re_lt_one_eighth {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < (1 / 8 : ℝ)) :
    _root_.DirichletCharacter.LFunction chi3D s ≠ 0 := by
  intro hz
  have hs0 : s ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hgf := gammaFactor_chi3D_ne_zero_of_re_pos h0
  have hcomp : _root_.DirichletCharacter.completedLFunction chi3D s = 0 := by
    rw [completedLFunction_chi3D_eq_mul hs0 hgf, hz, zero_mul]
  have hcomp1 : _root_.DirichletCharacter.completedLFunction chi3D (1 - s) = 0 := by
    rw [completedLFunction_chi3D_one_sub s, hcomp, mul_zero]
  have h1re : (7 / 8 : ℝ) < (1 - s).re := by simp; linarith
  have h1pos : 0 < (1 - s).re := by linarith
  have h1ne0 : 1 - s ≠ 0 := fun h => by rw [h] at h1pos; simp at h1pos
  have hgf1 := gammaFactor_chi3D_ne_zero_of_re_pos h1pos
  rw [completedLFunction_chi3D_eq_mul h1ne0 hgf1] at hcomp1
  exact LFunction_chi3D_ne_zero_of_seven_eighths_lt_re h1re
    ((mul_eq_zero.mp hcomp1).resolve_right hgf1)

/-- Every zero of `L(s, χ₋₃)` with `Re s > 0` satisfies `1/8 ≤ Re s ≤ 7/8`. -/
theorem LFunction_chi3D_zero_mem_quasiRH_strip {s : ℂ}
    (h0 : 0 < s.re) (hz : _root_.DirichletCharacter.LFunction chi3D s = 0) :
    s.re ∈ Icc (1 / 8 : ℝ) (7 / 8 : ℝ) :=
  ⟨le_of_not_gt fun h => LFunction_chi3D_ne_zero_of_re_lt_one_eighth h0 h hz,
   le_of_not_gt fun h => LFunction_chi3D_ne_zero_of_seven_eighths_lt_re h hz⟩

/-- The Dedekind product `ζ(s) L(s, χ₋₃)` of `ℚ(√−3)` has no zeros on `Re s > 7/8`. -/
theorem bianchiZeta_ne_zero_of_seven_eighths_lt_re {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    riemannZeta s * _root_.DirichletCharacter.LFunction chi3D s ≠ 0 :=
  mul_ne_zero (riemannZeta_ne_zero_of_seven_eighths_lt_re hs)
    (LFunction_chi3D_ne_zero_of_seven_eighths_lt_re hs)

/-- Every zero of `ζ(s) L(s, χ₋₃)` with `Re s > 0` lies in `[1/8, 7/8]`. -/
theorem bianchiZeta_zero_mem_quasiRH_strip {s : ℂ}
    (h0 : 0 < s.re) (hz : riemannZeta s * _root_.DirichletCharacter.LFunction chi3D s = 0) :
    s.re ∈ Icc (1 / 8 : ℝ) (7 / 8 : ℝ) := by
  rcases mul_eq_zero.mp hz with hζ | hL
  · exact riemannZeta_zero_mem_quasiRH_strip h0 hζ
  · exact LFunction_chi3D_zero_mem_quasiRH_strip h0 hL

/-- Every zero of the entire Bianchi completion `xiBianchi` lies in `[1/8, 7/8]`. -/
theorem xiBianchi_zero_mem_quasiRH_strip {s : ℂ} (hz : xiBianchi s = 0) :
    s.re ∈ Icc (1 / 8 : ℝ) (7 / 8 : ℝ) := by
  obtain ⟨h0, h1⟩ := zero_mem_openStrip_of_xiBianchi_eq_zero hz
  have hne1 : s ≠ 1 := fun h => by rw [h, one_re] at h1; exact lt_irrefl _ h1
  exact bianchiZeta_zero_mem_quasiRH_strip h0 ((xiBianchi_eq_zero_iff h0 hne1).mp hz)

/-- For any third cyclotomic field `K` (`ℚ(ζ₃) = ℚ(√−3)`), every zero of the Dedekind Hecke
`L`-function `heckeLFunction (trivialModulus K) 1` in `Re s > 0` (`s ≠ 1`) lies in `[1/8, 7/8]`. -/
theorem heckeLFunction_thirdCyclotomic_zero_mem_quasiRH_strip
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {s : ℂ} (hne1 : s ≠ 1) (h0 : 0 < s.re)
    (hz : HeckeLFunctions.heckeLFunction (HeckeLFunctions.trivialModulus K) 1 s = 0) :
    s.re ∈ Icc (1 / 8 : ℝ) (7 / 8 : ℝ) := by
  rw [heckeLFunction_thirdCyclotomic_trivial K hne1] at hz
  exact bianchiZeta_zero_mem_quasiRH_strip h0 hz

/-- Unconditional confinement of the Riemann zero abscissa: `1/2 ≤ zetaZeroAbscissa ≤ 7/8`. -/
theorem zetaZeroAbscissa_mem_Icc :
    _root_.RHTower.zetaZeroAbscissa ∈ Icc (1 / 2 : ℝ) (7 / 8 : ℝ) := by
  refine ⟨_root_.RHTower.half_le_zetaZeroAbscissa,
    csSup_le _root_.RHTower.zetaZeroReSet_nonempty fun x hx => ?_⟩
  obtain ⟨ρ, h0, rfl⟩ := hx
  rcases le_or_gt ρ.re 0 with hle | hgt
  · linarith
  · exact (riemannZeta_zero_mem_quasiRH_strip hgt h0).2

/-- Unconditional confinement of the `χ₋₃` zero abscissa: `1/2 ≤ zeroAbscissa chi3D ≤ 7/8`. -/
theorem zeroAbscissa_chi3D_mem_Icc :
    _root_.RHTower.zeroAbscissa chi3D ∈ Icc (1 / 2 : ℝ) (7 / 8 : ℝ) := by
  refine ⟨_root_.RHTower.half_le_zeroAbscissa chi3D_ne_one isPrimitive_chi3D, ?_⟩
  have hz : ∀ ρ : ℂ, riemannZeta ρ * _root_.DirichletCharacter.LFunction chi3D ρ = 0 →
      0 < ρ.re → ρ.re ≤ 1 - 2 * (1 / 16 : ℝ) := fun ρ hρ h0 => by
    have := (bianchiZeta_zero_mem_quasiRH_strip h0 hρ).2
    linarith
  have hle := zeroAbscissa_chi3D_le_of_zeroFree (δ := 1 / 16) (by norm_num) hz
  linarith

/-! ## 2. Unconditional Bounds on Mayer Scattering Resonances (`Re s ∈ [1/16, 7/16]`) -/

/-- Every Mayer scattering resonance of `PSL₂(ℤ)\ℍ²` satisfies `1/16 ≤ Re s ≤ 7/16`. -/
theorem isMayerScatteringResonance_re_mem_Icc {s : ℂ} (hs : IsMayerScatteringResonance s) :
    s.re ∈ Icc (1 / 16 : ℝ) (7 / 16 : ℝ) := by
  have h0 : 0 < s.re := hs.1
  have h1 : s.re < 1 / 2 := hs.2.1
  have hz : riemannZeta (2 * s) = 0 := (isMayerScatteringResonance_iff_zeta_zero h0 h1).mp hs
  have h2pos : 0 < (2 * s).re := by simp; linarith
  have hmem := riemannZeta_zero_mem_quasiRH_strip h2pos hz
  have h2re : (2 * s).re = 2 * s.re := by simp
  rw [h2re] at hmem
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

/-- No Mayer scattering resonance exists with `Re s < 1/16`. -/
theorem not_isMayerScatteringResonance_of_re_lt_one_sixteenth {s : ℂ} (hs : s.re < 1 / 16) :
    ¬IsMayerScatteringResonance s := fun h => by
  linarith [(isMayerScatteringResonance_re_mem_Icc h).1]

/-- No Mayer scattering resonance exists with `7/16 < Re s`. -/
theorem not_isMayerScatteringResonance_of_seven_sixteenths_lt_re {s : ℂ} (hs : 7 / 16 < s.re) :
    ¬IsMayerScatteringResonance s := fun h => by
  linarith [(isMayerScatteringResonance_re_mem_Icc h).2]

/-- Outside `[1/16, 7/16]` inside the scattering strip `(0, 1/2)`, the Fredholm determinant-excess
resonance multiplicity vanishes identically. -/
theorem mayerResonanceMultiplicity_eq_zero_outside_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1 / 2) (hout : s.re < 1 / 16 ∨ 7 / 16 < s.re) :
    mayerResonanceMultiplicity s = 0 := by
  by_contra hne
  have hpos : 0 < mayerResonanceMultiplicity s := Nat.pos_of_ne_zero hne
  have hres := (mayerResonanceMultiplicity_pos_iff h0 h1).mp hpos
  rcases hout with hlt | hgt
  · exact not_isMayerScatteringResonance_of_re_lt_one_sixteenth hlt hres
  · exact not_isMayerScatteringResonance_of_seven_sixteenths_lt_re hgt hres

/-- Outside `[1/16, 7/16]` inside `(0, 1/2)`, the Poincaré scattering entry has no poles
(`0 ≤ meromorphicOrderAt scatteringEntry s`). -/
theorem scatteringEntry_holomorphicOrder_nonneg_outside_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1 / 2) (hout : s.re < 1 / 16 ∨ 7 / 16 < s.re) :
    0 ≤ meromorphicOrderAt
      GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScatteringNormalization.scatteringEntry s := by
  by_contra hneg
  rw [not_le] at hneg
  have hres := (isMayerScatteringResonance_iff_scatteringEntry_pole h0 h1).mpr hneg
  rcases hout with hlt | hgt
  · exact not_isMayerScatteringResonance_of_re_lt_one_sixteenth hlt hres
  · exact not_isMayerScatteringResonance_of_seven_sixteenths_lt_re hgt hres

/-! ## 3. Unconditional Horizon Ringdown at Rate `δ = 1/16` (`SL₂(ℤ[ω])\ℍ³` and `PSL₂(ℤ)\ℍ²`) -/

/-- **Unconditional Bianchi Horizon Ringdown.** Every smooth compactly supported wavepacket reflected
off the Bianchi horizon `SL₂(ℤ[ω])\ℍ³` decays at late times as `O(e^{-(1/16 - ε)τ})` for every
`ε > 0`. -/
theorem bianchi_pulse_ringdown_one_sixteenth {ε : ℝ} (hε : 0 < ε)
    (h : GaloisForLFunctions.BlackHoleRingdown.CompactPulse) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖bianchiReflectedField h τ‖ ≤ C * Real.exp (-(1 / 16 - ε) * τ) := by
  have hz : ∀ ρ : ℂ, riemannZeta ρ * _root_.DirichletCharacter.LFunction chi3D ρ = 0 →
      0 < ρ.re → ρ.re ≤ 1 - 2 * (1 / 16 : ℝ) := fun ρ hρ h0 => by
    have := (bianchiZeta_zero_mem_quasiRH_strip h0 hρ).2
    linarith
  exact (bianchi_zeroFreeStrip_iff_pulse_ringdown (δ := 1 / 16) (by norm_num) (by norm_num)).mp
    hz ε hε h

/-- **Unconditional Modular Horizon Ringdown.** Every smooth compactly supported pulse on the
modular horizon `PSL₂(ℤ)\ℍ²` (with mean growth removed) decays as `O(e^{-(1/16 - ε)τ})` for every
`ε > 0` at every point `(x, Y)` (`Y > 0`). -/
theorem modular_pulse_ringdown_one_sixteenth {ε : ℝ} (hε : 0 < ε)
    (h : GaloisForLFunctions.BlackHoleRingdown.CompactPulse)
    (x Y : ℝ) (hY : 0 < Y) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖GaloisForLFunctions.BlackHoleRingdown.pulseField h τ x Y‖ ≤
        C * Real.exp (-(1 / 16 - ε) * τ) := by
  have hz : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re ≤ 1 - 2 * (1 / 16 : ℝ) := fun ρ hρ h0 => by
    have := (riemannZeta_zero_mem_quasiRH_strip h0 hρ).2
    linarith
  exact (GaloisForLFunctions.BlackHoleRingdown.RingdownRate.zeroFreeStrip_iff_pulse_ringdown
    (δ := 1 / 16) (by norm_num) (by norm_num)).mp hz ε hε h x Y hY

/-! ## 4. Unconditional `O(y^{9/16 - ε})` Horocycle, Farey, Cusp-Energy, and Cavity Rates -/

/-- `ξ(z) ≠ 0` unconditionally for `Re z > 7/8`. -/
theorem xi_ne_zero_of_seven_eighths_lt_re {z : ℂ} (hz : (7 / 8 : ℝ) < z.re) :
    _root_.RHTower.xi z ≠ 0 := by
  rcases lt_or_ge z.re 1 with hlt | hge
  · have hne1 : z ≠ 1 := fun h => by rw [h, one_re] at hlt; exact lt_irrefl _ hlt
    rw [Ne, _root_.RHTower.xi_eq_zero_iff (by linarith) hne1]
    exact riemannZeta_ne_zero_of_seven_eighths_lt_re hz
  · exact _root_.RHTower.xi_ne_zero_of_one_le_re hge

/-- Polynomial growth of `(riemannZeta z)⁻¹` on every vertical strip `7/8 + δ ≤ Re z ≤ d`,
`2 ≤ |Im z|` (`δ > 0`). -/
theorem exists_invZeta_poly_seven_eighths {δ : ℝ} (hδ : 0 < δ) (d : ℝ) :
    ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, 7 / 8 + δ ≤ z.re → z.re ≤ d → 2 ≤ |z.im| →
      ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N := by
  set δ' : ℝ := min δ (1 / 16)
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hδ'16 : δ' ≤ 1 / 16 := min_le_right _ _
  obtain ⟨κ, hκ, hlb⟩ :=
    _root_.RHTower.exists_zeta_lower_bound_subpolynomial_of_zeroFree
      (Θ := 7 / 8) (by norm_num) (by norm_num)
      (fun z hz => riemannZeta_ne_zero_of_seven_eighths_lt_re hz)
      (δ := δ') hδ'0 (by linarith) (ε := 1) one_pos
  set box : Set ℂ :=
    (Icc (7 / 8 + δ) (max d (7 / 8 + δ)) ×ℂ Icc (-6 : ℝ) 6) ∩ {z : ℂ | 2 ≤ |z.im|}
  have hbox : IsCompact box :=
    (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hcont : ContinuousOn (fun z : ℂ => (riemannZeta z)⁻¹) box := by
    intro z hz
    have hne1 : z ≠ 1 := fun h1 => by
      have := hz.2; rw [h1] at this; simp at this; linarith
    have hz0 : riemannZeta z ≠ 0 :=
      riemannZeta_ne_zero_of_seven_eighths_lt_re (by linarith [hz.1.1.1])
    exact ((differentiableAt_riemannZeta hne1).continuousAt.inv₀ hz0).continuousWithinAt
  obtain ⟨M, hM⟩ := hbox.exists_bound_of_continuousOn hcont
  refine ⟨max (max M 0) (2 / κ), 1, by positivity, fun z hz1 hz2 hzt => ?_⟩
  have hpow1 : (1 : ℝ) ≤ |z.im| ^ 1 := by simpa using (by linarith : (1 : ℝ) ≤ |z.im|)
  rcases le_or_gt |z.im| 6 with hsmall | hbig
  · have hmem : z ∈ box :=
      ⟨⟨⟨hz1, hz2.trans (le_max_left _ _)⟩, ⟨by linarith [neg_abs_le z.im],
        (le_abs_self _).trans hsmall⟩⟩, hzt⟩
    calc ‖(riemannZeta z)⁻¹‖ ≤ M := hM z hmem
      _ ≤ max (max M 0) (2 / κ) * 1 := by
          rw [mul_one]; exact (le_max_left M 0).trans (le_max_left _ _)
      _ ≤ max (max M 0) (2 / κ) * |z.im| ^ 1 :=
          mul_le_mul_of_nonneg_left hpow1 (by positivity)
  · have hb := hlb z (by linarith) hbig.le
    rw [Real.rpow_neg_one] at hb
    have hpos : 0 < 2 + |z.im| := by positivity
    have hinv : ‖(riemannZeta z)⁻¹‖ ≤ (2 + |z.im|) / κ := by
      rw [norm_inv]
      have hκinv : 0 < κ * (2 + |z.im|)⁻¹ := by positivity
      have h1 := inv_anti₀ hκinv hb
      rwa [mul_inv, inv_inv, ← div_eq_inv_mul] at h1
    calc ‖(riemannZeta z)⁻¹‖ ≤ (2 + |z.im|) / κ := hinv
      _ ≤ (2 * |z.im|) / κ := by gcongr; linarith
      _ = (2 / κ) * |z.im| ^ 1 := by ring
      _ ≤ max (max M 0) (2 / κ) * |z.im| ^ 1 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **Unconditional `y^{9/16 - ε}` Horocycle Equidistribution Rate.** Every smooth pseudo-Eisenstein
horocycle mean supported above height `1` converges to `(6/π) ∫ φ(t) t^{-2} dt` at rate
`O(y^{9/16 - ε})` on `(0, 1]`. -/
theorem horocycleMean_rate_nine_sixteenths {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖GaloisForLFunctions.BlackHoleRingdown.horocycleMean
        (GaloisForLFunctions.BlackHoleRingdown.pseudoEisenstein fun t => (φ t : ℂ)) y -
        6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ ≤ C * y ^ (9 / 16 - ε) := by
  obtain ⟨a, b, ha, hab, hφa, hφb⟩ :=
    GaloisForLFunctions.BlackHoleRingdown.exists_band_of_tsupport hc hs
  have hψ := GaloisForLFunctions.BlackHoleRingdown.isTest_of_band
    hφ (by linarith) hab hφa hφb
  have h := GaloisForLFunctions.BlackHoleRingdown.norm_horocycleMean_sub_le_of_zeroFree
    hψ ha (θ := 7 / 8) (by norm_num) (by norm_num)
    (fun z hz => xi_ne_zero_of_seven_eighths_lt_re hz)
    (fun δ hδ d => exists_invZeta_poly_seven_eighths hδ d) hε hε1
  rwa [GaloisForLFunctions.BlackHoleRingdown.residueConst_eq,
    show (1 : ℝ) - (7 / 8) / 2 - ε = 9 / 16 - ε by ring] at h

/-- **Unconditional `y^{9/16 - ε}` Farey Thermalization Rate.** Every smooth Farey count supported
above depth `1` converges to `(6/π) ∫ φ(t) t^{-2} dt` at rate `O(y^{9/16 - ε})` on `(0, 1]`. -/
theorem fareyCount_rate_nine_sixteenths {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖GaloisForLFunctions.CountingHolography.fareyCount (fun t => (φ t : ℂ)) y -
        6 / Real.pi * mellin (fun t => (φ t : ℂ)) (-1)‖ ≤ C * y ^ (9 / 16 - ε) := by
  obtain ⟨C, hC, hrate⟩ := horocycleMean_rate_nine_sixteenths hφ hc hs hε hε1
  refine ⟨C, hC, fun y hy hy1 => ?_⟩
  rw [← GaloisForLFunctions.CountingHolography.horocycleMean_eq_fareyCount hφ hc hs hy hy1]
  exact hrate y hy hy1

/-- **Unconditional `y^{9/16 - ε}` Cusp-Form Horocycle Energy Rate.** For every Maass cusp form `g`
on `PSL₂(ℤ)\ℍ²`, its horocycle energy slice converges to `(3/π) ‖g‖²` at rate `O(y^{9/16 - ε})` on
`(0, 1]` (`0 < ε < 1/2`). -/
theorem cusp_energy_rate_nine_sixteenths {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}
    (hg : g ∈ GaloisForLFunctions.BlackHoleRingdown.HeckeCusp.cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y →
      GaloisForLFunctions.BlackHoleRingdown.HeckeCusp.fourierCoeff g n y =
        ρ n * (Real.sqrt y : ℂ) *
          GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
            (2 * Real.pi * |(n : ℝ)| * y)
            (GaloisForLFunctions.BlackHoleRingdown.CuspL.nu lamE))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      |GaloisForLFunctions.BlackHoleRingdown.WeylUpper.slice g y -
        3 / Real.pi * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2| ≤ C * y ^ (9 / 16 - ε) := by
  obtain ⟨C, hC, h⟩ := GaloisForLFunctions.BlackHoleRingdown.CuspHRate.norm_mass_sub_le_of_zeroFree
    hg hρ0 hρ (θ := 7 / 8) (by norm_num) (by norm_num)
    (fun z hz => xi_ne_zero_of_seven_eighths_lt_re hz)
    (fun δ hδ d => exists_invZeta_poly_seven_eighths hδ d) hε hε1
  have hγ : (0 : ℝ) < 1 - (7 / 8) / 2 - ε := by linarith
  have hc := GaloisForLFunctions.BlackHoleRingdown.CuspHRate.rateConst_eq hg hρ0 hρ hγ h
  refine ⟨C, hC, fun y hy hy1 => ?_⟩
  have hy_bd := h y hy hy1
  rw [hc, GaloisForLFunctions.BlackHoleRingdown.CuspHR.mass, ← ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, show (1 : ℝ) - (7 / 8) / 2 - ε = 9 / 16 - ε by ring] at hy_bd
  exact hy_bd

/-- **Unconditional `y^{9/16 - ε}` Two-Mode Cuspidal Cavity Rate.** Every two-mode state
`maassForm i + c · maassForm l` of the cuspidal eigenbasis rings down on closed horocycles at rate
`O(y^{9/16 - ε})` on `(0, 1]` for every `ε > 0`. -/
theorem twoMode_cavity_rate_nine_sixteenths
    (i l : GaloisForLFunctions.RHTower.DeckPointPair.CuspEigenIndex 0) (c : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : ℂ) (C : ℝ), ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.response
        (GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.twoModeEnergy
          (GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.maassForm i)
          (GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.maassForm l) c) y - a‖ ≤
        C * y ^ (9 / 16 - ε) := by
  set ε' : ℝ := min ε (1 / 4)
  have hε' : 0 < ε' := lt_min hε (by norm_num)
  obtain ⟨a, C, h⟩ :=
    GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.twoMode_rate_of_zeroFree
      (GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.maassForm_mem i)
      (GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.maassForm_mem l)
      c (Θ := 7 / 8) (by norm_num) (by norm_num)
      (fun z hz => riemannZeta_ne_zero_of_seven_eighths_lt_re hz)
      hε' (by linarith [min_le_right ε (1 / 4)])
  refine ⟨a, max C 0, fun y hy hy1 => ?_⟩
  have hmono : y ^ (1 - (7 / 8 : ℝ) / 2 - ε') ≤ y ^ (9 / 16 - ε) :=
    Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith [min_le_left ε (1 / 4)])
  calc _ ≤ C * y ^ (1 - (7 / 8 : ℝ) / 2 - ε') := h y hy hy1
    _ ≤ max C 0 * y ^ (1 - (7 / 8 : ℝ) / 2 - ε') :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.le _)
    _ ≤ max C 0 * y ^ (9 / 16 - ε) := mul_le_mul_of_nonneg_left hmono (le_max_right _ _)

/-! ## 5. Horizon Vertex Balance at `δ = 1/16` (`σ₀ = 7/8`) and Binding-Bin Upgrade Threshold -/

section VertexBalance

open GaloisForLFunctions.FamilyContinuationTheory.Budget

/-- Exact horizon balance at the published cubic-probe geometry `(17/48, 23/48, 1/6)`:
1. `lowBoundary (17/48) (23/48) (1/6) = 7/8` (horizon ringdown rate `δ = (1 - 7/8)/2 = 1/16`);
2. in the binding bin `δ_bin = 79/204` (`q = 79/408`), the top-row exponent equals
   `(13/16) · (R - 443/663)`;
3. `rowCount (79/204) (1/2) = 21766/32589 < 443/663`, giving binding-bin slack `-(7/30672) < 0`;
4. for any geometry `(lx, ly, ℓ)` with `lx ≤ 1` whose zero-free strip corresponds to a faster
   ringdown rate `δ ≥ 1/16 + 1/8000` (`lowBoundary lx ly ℓ ≤ 7/8 - 1/4000`), the binding-bin
   exponent at the published row count is strictly positive. -/
theorem horizon_ringdown_vertex_balance :
    lowBoundary (17 / 48) (23 / 48) (1 / 6) = 1 - 2 * (1 / 16 : ℝ) ∧
    (∀ R : ℝ, endpointExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) (79 / 204) (79 / 408) R =
      (13 / 16) * (R - 443 / 663)) ∧
    rowCount (79 / 204) (1 / 2) = 21766 / 32589 ∧
    endpointExponent (17 / 48) (23 / 48) (1 / 6) (7 / 8) (79 / 204) (79 / 408)
      (rowCount (79 / 204) (1 / 2)) = -(7 / 30672) ∧
    (∀ {lx ly ℓ : ℝ}, lx ≤ 1 → lowBoundary lx ly ℓ ≤ 1 - 2 * (1 / 16 + 1 / 8000 : ℝ) →
      0 < endpointExponent lx ly ℓ (lowBoundary lx ly ℓ) (79 / 204) (79 / 408)
        (rowCount (79 / 204) (1 / 2))) := by
  refine ⟨by rw [lowBoundary_published]; norm_num, fun R => by unfold endpointExponent; ring,
    rowCount_binding, endpoint_binding_bin, fun hlx hσ => ?_⟩
  exact endpointExponent_pos_of_lowBoundary_le hlx (by linarith)

/-- Along the dual-length edge `(lx, ly, ℓ) = (17/48 - h/2, 23/48 - h/2, 1/6 + h)` (`0 < h`),
the low boundary shifts strictly below `7/8` to `7/8 - h/4 = 1 - 2(1/16 + h/8)` (faster horizon
ringdown rate `δ(h) = 1/16 + h/8 > 1/16`), and the binding-bin top-row exponent at `δ_bin = 79/204`
is strictly negative if and only if the binding-bin row-count exponent satisfies
`R < (443 - 270 h) / (663 + 1224 h)`. -/
theorem binding_bin_saving_iff_faster_ringdown {h R : ℝ} (hh : 0 < h) :
    lowBoundary (17 / 48 - h / 2) (23 / 48 - h / 2) (1 / 6 + h) =
      1 - 2 * (1 / 16 + h / 8) ∧
    (endpointExponent (17 / 48 - h / 2) (23 / 48 - h / 2) (1 / 6 + h)
      (1 - 2 * (1 / 16 + h / 8)) (79 / 204) (79 / 408) R < 0 ↔
      R < (443 - 270 * h) / (663 + 1224 * h)) := by
  have hlb : lowBoundary (17 / 48 - h / 2) (23 / 48 - h / 2) (1 / 6 + h) =
      1 - 2 * (1 / 16 + h / 8) := by
    unfold lowBoundary
    rw [show (17 / 48 - h / 2) + (23 / 48 - h / 2) + (1 / 6 + h) - 1 = 0 by ring, max_self]
    ring
  have hexp : endpointExponent (17 / 48 - h / 2) (23 / 48 - h / 2) (1 / 6 + h)
      (1 - 2 * (1 / 16 + h / 8)) (79 / 204) (79 / 408) R =
      ((663 + 1224 * h) * R - (443 - 270 * h)) / 816 := by
    unfold endpointExponent
    ring
  have hden : 0 < 663 + 1224 * h := by linarith
  refine ⟨hlb, ?_⟩
  rw [hexp, div_lt_iff₀ (by norm_num : (0 : ℝ) < 816), zero_mul]
  constructor
  · intro hlt
    rw [lt_div_iff₀ hden]
    linarith
  · intro hR
    rw [lt_div_iff₀ hden] at hR
    linarith

end VertexBalance

end GaloisForLFunctions.RingdownOfTheCubicCover

end
