import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerScatteringState
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerBoundaryResolvent
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerGlobalPeriods
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheLoopEisensteinReflectionCarriesTheHodgeDefect
import GaloisForLFunctions.RHTower.HardyZ

/-!
# Operator-Native Characterization of Mayer Scattering Resonances

In the open scattering strip `0 < Re s < 1/2` (Mayer exponent `w = 2s` with `0 < Re w < 1`),
scattering resonances are defined directly from the renormalized Mayer source operator and its
Mellin-continued lattice response: `source (2s) (state (2s)) = state (2s)`.

This pure operator fixed-point condition is unconditionally equivalent to:
1. strict excess of the Fredholm source determinant order over its signed cofactor order at `2s`,
2. a pole of the constant-mode boundary resolvent `positiveBoundary` at `2s`,
3. a pole of the Poincaré scattering entry `scatteringEntry` at `s`,
4. vanishing of `riemannZeta (2s)` (and `RHTower.xi (2s)`).

Every Mayer scattering resonance is strictly non-real (`s.im ≠ 0`), extends to an analytic `+1`
Lewis period function on `Re a > 0` nonvanishing at `a = 1`, and is preserved by complex
conjugation and by the Riemann–Mayer reflection `s ↦ 1/2 - conj s`. Counting right-half
resonances `1/4 < Re s < 1/2` recovers `boostPolarIndex ratCorr` directly, and `2` times the
cardinality of upper right-half resonances (`Im s > 0`, `1/4 < Re s < 1/2`) equals
`boostPolarIndex ratCorr`.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.AdelicKreinGeometry GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringMellin MayerScatteringMultiplicity
open MayerBoundaryResolvent MayerScatteringState MayerGlobalPeriods

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- Pure Mayer-operator definition of a strip scattering resonance: `0 < Re s < 1/2` and the
Mellin-continued lattice state `state (2s)` is fixed by the renormalized Mayer source operator. -/
def IsMayerScatteringResonance (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1 / 2 ∧ source (2 * s) (state (2 * s)) = state (2 * s)

/-- Excess multiplicity of the Mayer source determinant over its signed cofactor at `w = 2s`. -/
def mayerResonanceMultiplicity (s : ℂ) : ℕ :=
  analyticOrderNatAt (fun v => sourceDeterminant v 1) (2 * s) -
    analyticOrderNatAt (fun v => MayerPole.polePart v 1) (2 * s)

/-- Global Lewis period function associated to the Mayer scattering state at parameter `s`. -/
def resonantLewisPeriod (s : ℂ) (a : ℂ) : ℂ :=
  period (2 * s) 1 0 (state (2 * s)) a

/-- The Riemann–Mayer spectral reflection `s ↦ 1/2 - conj s` fixing the critical line `Re s = 1/4`. -/
def riemannMayerReflect (s : ℂ) : ℂ :=
  1 / 2 - (starRingEnd ℂ) s

@[simp]
theorem riemannMayerReflect_involutive (s : ℂ) :
    riemannMayerReflect (riemannMayerReflect s) = s := by
  unfold riemannMayerReflect
  rw [map_sub, map_div₀, map_one, map_ofNat, Complex.conj_conj]
  ring

@[simp]
theorem riemannMayerReflect_re (s : ℂ) :
    (riemannMayerReflect s).re = 1 / 2 - s.re := by
  unfold riemannMayerReflect
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.conj_re]

@[simp]
theorem riemannMayerReflect_im (s : ℂ) :
    (riemannMayerReflect s).im = s.im := by
  unfold riemannMayerReflect
  simp

theorem riemannMayerReflect_eq_self_iff (s : ℂ) :
    riemannMayerReflect s = s ↔ s.re = 1 / 2 - s.re := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    rw [riemannMayerReflect_re] at hr
    exact hr.symm
  · intro hr
    apply Complex.ext
    · rw [riemannMayerReflect_re]
      exact hr.symm
    · exact riemannMayerReflect_im s

theorem riemannMayerReflect_fixed_iff (s : ℂ) :
    riemannMayerReflect s = s ↔ s.re = 1 / 4 := by
  rw [riemannMayerReflect_eq_self_iff]
  constructor <;> intro h <;> linarith

private theorem two_mul_re_bounds {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1 / 2) :
    0 < (2 * s).re ∧ (2 * s).re < 1 := by
  have hre : (2 * s).re = 2 * s.re := by simp
  rw [hre]
  exact ⟨by linarith, by linarith⟩

private theorem constant_one_ne_zero : (constant 1 : DiscSpace) ≠ 0 := by
  intro h
  have hn := norm_constant 1
  rw [h, norm_zero, norm_one] at hn
  exact zero_ne_one hn

/-- In `0 < Re s < 1/2`, the pure Mayer fixed-point condition `source (2s) (state (2s)) = state (2s)`
is unconditionally equivalent to `riemannZeta (2s) = 0`. -/
theorem isMayerScatteringResonance_iff_zeta_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1 / 2) :
    IsMayerScatteringResonance s ↔ riemannZeta (2 * s) = 0 := by
  obtain ⟨hw0, hw1⟩ := two_mul_re_bounds h0 h1
  have hne1 : 2 * s ≠ 1 := fun he => by rw [he, Complex.one_re] at hw1; exact lt_irrefl 1 hw1
  have hne2 : 2 * s ≠ 2 := fun he => by rw [he] at hw1; norm_num at hw1
  have hstate := state_equation hw0 hne1 hne2
  unfold IsMayerScatteringResonance
  rw [and_iff_right h0, and_iff_right h1]
  constructor
  · intro hfix
    rw [hfix, sub_self, eq_comm, smul_eq_zero] at hstate
    exact hstate.resolve_right constant_one_ne_zero
  · intro hz
    rw [hz, zero_smul, sub_eq_zero] at hstate
    exact hstate.symm

/-- Equivalence with the completed `ξ`-zero locus in the scattering strip. -/
theorem isMayerScatteringResonance_iff_xi_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1 / 2) :
    IsMayerScatteringResonance s ↔ _root_.RHTower.xi (2 * s) = 0 := by
  obtain ⟨hw0, hw1⟩ := two_mul_re_bounds h0 h1
  have hne1 : 2 * s ≠ 1 := fun he => by rw [he, Complex.one_re] at hw1; exact lt_irrefl 1 hw1
  rw [isMayerScatteringResonance_iff_zeta_zero h0 h1,
    (_root_.RHTower.xi_eq_zero_iff hw0 hne1).symm]

/-- Exact multiplicity identity: the Fredholm determinant excess over its cofactor equals the
analytic zero order of `riemannZeta` at `2s`. -/
theorem mayerResonanceMultiplicity_eq_zeta_order {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1 / 2) :
    mayerResonanceMultiplicity s = analyticOrderNatAt riemannZeta (2 * s) := by
  obtain ⟨hw0, hw1⟩ := two_mul_re_bounds h0 h1
  unfold mayerResonanceMultiplicity
  rw [determinant_orderNat hw0 hw1, Nat.add_sub_cancel_left]

/-- Pure resolvent characterization: `s` is a Mayer scattering resonance iff `positiveBoundary`
has a pole at `2s`. -/
theorem isMayerScatteringResonance_iff_positiveBoundary_pole {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1 / 2) :
    IsMayerScatteringResonance s ↔ meromorphicOrderAt positiveBoundary (2 * s) < 0 := by
  obtain ⟨hw0, hw1⟩ := two_mul_re_bounds h0 h1
  rw [isMayerScatteringResonance_iff_zeta_zero h0 h1, positiveBoundary_pole_iff hw0 hw1]

/-- Positive determinant-excess multiplicity characterizes Mayer scattering resonances. -/
theorem mayerResonanceMultiplicity_pos_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1 / 2) :
    0 < mayerResonanceMultiplicity s ↔ IsMayerScatteringResonance s := by
  obtain ⟨hw0, hw1⟩ := two_mul_re_bounds h0 h1
  rw [mayerResonanceMultiplicity_eq_zeta_order h0 h1,
    isMayerScatteringResonance_iff_positiveBoundary_pole h0 h1, positiveBoundary_order hw0 hw1]
  norm_cast
  omega

/-- Pure Fredholm characterization: `s` is a Mayer scattering resonance iff the source determinant
vanishes to strictly higher order than its signed cofactor at `2s`. -/
theorem isMayerScatteringResonance_iff_determinant_excess {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1 / 2) :
    IsMayerScatteringResonance s ↔
      analyticOrderAt (fun v => MayerPole.polePart v 1) (2 * s) <
        analyticOrderAt (fun v => sourceDeterminant v 1) (2 * s) := by
  obtain ⟨hw0, hw1⟩ := two_mul_re_bounds h0 h1
  have hBfin : analyticOrderAt (fun v => MayerPole.polePart v 1) (2 * s) ≠ ⊤ :=
    cofactor_order_ne_top hw0
  have hDfin : analyticOrderAt (fun v => sourceDeterminant v 1) (2 * s) ≠ ⊤ :=
    determinant_order_ne_top hw0 hw1
  have hZfin : analyticOrderAt riemannZeta (2 * s) ≠ ⊤ := by
    intro ht
    have hd := determinant_order hw0 hw1
    rw [ht, add_top] at hd
    exact hDfin hd
  rw [← mayerResonanceMultiplicity_pos_iff h0 h1, mayerResonanceMultiplicity_eq_zeta_order h0 h1,
    determinant_order hw0 hw1, ← ENat.coe_toNat hBfin, ← ENat.coe_toNat hZfin]
  change 0 < (analyticOrderAt riemannZeta (2 * s)).toNat ↔ _
  rw [← Nat.cast_add]
  norm_cast
  omega

/-- Pure Poincaré scattering characterization: `s` is a Mayer scattering resonance iff
`scatteringEntry` has a pole at `s`. -/
theorem isMayerScatteringResonance_iff_scatteringEntry_pole {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1 / 2) :
    IsMayerScatteringResonance s ↔
      meromorphicOrderAt MayerScatteringNormalization.scatteringEntry s < 0 := by
  obtain ⟨hw0, hw1⟩ := two_mul_re_bounds h0 h1
  have hs : (2 * s) / 2 = s := by ring
  rw [isMayerScatteringResonance_iff_zeta_zero h0 h1, ← scattering_pole_iff hw0 hw1, hs]

/-- Every strip Mayer scattering resonance has nonzero imaginary part (`ξ(2σ) > 0` on `(0, 1)`). -/
theorem im_ne_zero_of_isMayerScatteringResonance {s : ℂ} (hs : IsMayerScatteringResonance s) :
    s.im ≠ 0 := by
  have h0 : 0 < s.re := hs.1
  have h1 : s.re < 1 / 2 := hs.2.1
  have hxi := (isMayerScatteringResonance_iff_xi_zero h0 h1).mp hs
  intro him
  have heq : 2 * s = ((2 * s.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [heq] at hxi
  have hpos := _root_.RHTower.xi_pos_on_real_anchor (σ := 2 * s.re) (by linarith) (by linarith)
  rw [hxi, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- Complex conjugation preserves Mayer scattering resonances. -/
theorem isMayerScatteringResonance_conj_iff {s : ℂ} :
    IsMayerScatteringResonance ((starRingEnd ℂ) s) ↔ IsMayerScatteringResonance s := by
  by_cases hstrip : 0 < s.re ∧ s.re < 1 / 2
  · obtain ⟨h0, h1⟩ := hstrip
    have hc0 : 0 < ((starRingEnd ℂ) s).re := by simpa using h0
    have hc1 : ((starRingEnd ℂ) s).re < 1 / 2 := by simpa using h1
    obtain ⟨hw0, hw1⟩ := two_mul_re_bounds h0 h1
    have hwne1 : 2 * s ≠ 1 := fun he => by rw [he, Complex.one_re] at hw1; exact lt_irrefl 1 hw1
    have hconj2 : 2 * (starRingEnd ℂ) s = (starRingEnd ℂ) (2 * s) := by
      rw [map_mul, map_ofNat]
    rw [isMayerScatteringResonance_iff_zeta_zero hc0 hc1,
      isMayerScatteringResonance_iff_zeta_zero h0 h1, hconj2,
      _root_.RHTower.riemannZeta_conj_eq_zero_iff_of_re_pos hw0 hwne1]
  · constructor <;> intro hs
    · exfalso
      apply hstrip
      exact ⟨by simpa using hs.1, by simpa using hs.2.1⟩
    · exact absurd ⟨hs.1, hs.2.1⟩ hstrip

/-- The Riemann–Mayer reflection `s ↦ 1/2 - conj s` preserves Mayer scattering resonances. -/
theorem isMayerScatteringResonance_reflect_iff {s : ℂ} :
    IsMayerScatteringResonance (riemannMayerReflect s) ↔ IsMayerScatteringResonance s := by
  by_cases hstrip : 0 < s.re ∧ s.re < 1 / 2
  · obtain ⟨h0, h1⟩ := hstrip
    have hr0 : 0 < (riemannMayerReflect s).re := by rw [riemannMayerReflect_re]; linarith
    have hr1 : (riemannMayerReflect s).re < 1 / 2 := by rw [riemannMayerReflect_re]; linarith
    rw [isMayerScatteringResonance_iff_xi_zero hr0 hr1,
      isMayerScatteringResonance_iff_xi_zero h0 h1]
    have harg : 2 * riemannMayerReflect s = 1 - 2 * (starRingEnd ℂ) s := by
      unfold riemannMayerReflect
      ring
    have hconj2 : 2 * (starRingEnd ℂ) s = (starRingEnd ℂ) (2 * s) := by
      rw [map_mul, map_ofNat]
    rw [harg, _root_.RHTower.xi_one_sub, hconj2, _root_.RHTower.xi_conj, map_eq_zero]
  · constructor <;> intro hs
    · exfalso
      apply hstrip
      have hre := riemannMayerReflect_re s
      exact ⟨by linarith [hs.2.1, hre], by linarith [hs.1, hre]⟩
    · exact absurd ⟨hs.1, hs.2.1⟩ hstrip

/-- Analyticity of the resonant Lewis period function on the open right half-plane `Re a > 0`. -/
theorem resonantLewisPeriod_analytic {s : ℂ} (h0 : 0 < s.re) :
    AnalyticOnNhd ℂ (resonantLewisPeriod s) {a : ℂ | 0 < a.re} := by
  have hw0 : 0 < (2 * s).re := by simp; linarith
  have hdom_open : IsOpen MayerGlobalPeriods.domain :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro a ha
  change 0 < a.re at ha
  have hd : a - 1 ∈ MayerGlobalPeriods.domain := by
    change -1 < (a - 1).re
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hh := (extension_differentiableOn hw0 1 0 (state (2 * s))).differentiableAt
    (hdom_open.mem_nhds hd)
  exact (hh.comp a (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => u - 1) a)).differentiableWithinAt

private theorem resonant_regularized_eq {s : ℂ} (hs : IsMayerScatteringResonance s) :
    regularized (2 * s) (two_mul_re_bounds hs.1 hs.2.1).1 (state (2 * s)) =
      (1 : ℂ) • state (2 * s) + constant 0 := by
  obtain ⟨h0, h1, hfix⟩ := hs
  have hw0 := (two_mul_re_bounds h0 h1).1
  have hconst0 : (constant 0 : DiscSpace) = 0 := by
    apply norm_eq_zero.mp
    rw [norm_constant, norm_zero]
  rw [← source_eq hw0, hfix, one_smul, hconst0, add_zero]

/-- At every Mayer scattering resonance `s`, `resonantLewisPeriod s` satisfies the `+1` modular
inversion law `ψ(a) = a^(-2s) ψ(a⁻¹)` for all `Re a > 0`. -/
theorem resonantLewisPeriod_reciprocity {s a : ℂ} (hs : IsMayerScatteringResonance s)
    (ha : 0 < a.re) :
    resonantLewisPeriod s a = a ^ (-(2 * s)) * resonantLewisPeriod s a⁻¹ := by
  have hw0 := (two_mul_re_bounds hs.1 hs.2.1).1
  have hrec := MayerGlobalPeriods.reciprocity hw0 (by norm_num : (1 : ℂ) ^ 2 = 1)
    (state (2 * s)) (resonant_regularized_eq hs) ha
  simpa only [resonantLewisPeriod, one_mul] using hrec

/-- At every Mayer scattering resonance `s`, `resonantLewisPeriod s` satisfies the global Lewis
three-term functional equation across `Re a > 0`. -/
theorem resonantLewisPeriod_three_term {s a : ℂ} (hs : IsMayerScatteringResonance s)
    (ha : 0 < a.re) :
    resonantLewisPeriod s a =
      resonantLewisPeriod s (a + 1) +
        (a + 1) ^ (-(2 * s)) * resonantLewisPeriod s (a / (a + 1)) :=
  MayerGlobalPeriods.three_term (two_mul_re_bounds hs.1 hs.2.1).1 (by norm_num)
    (state (2 * s)) (resonant_regularized_eq hs) ha

/-- At `a = 1`, `resonantLewisPeriod s 1 = 2 * riemannZeta (2s - 1)` is strictly nonzero at every
strip Mayer scattering resonance. -/
theorem resonantLewisPeriod_one_eq {s : ℂ} (hs : IsMayerScatteringResonance s) :
    resonantLewisPeriod s 1 = 2 * riemannZeta (2 * s - 1) := by
  obtain ⟨hw0, hw1⟩ := two_mul_re_bounds hs.1 hs.2.1
  have hw2 : 2 * s ≠ 2 := fun he => by rw [he] at hw1; norm_num at hw1
  have h0in : (0 : ℂ) ∈ MayerCutoff.inner := by
    norm_num [MayerCutoff.inner, Metric.mem_ball, dist_eq_norm]
  calc
    resonantLewisPeriod s 1 = extension (2 * s) 1 0 (state (2 * s)) 0 := by
      simp [resonantLewisPeriod, period]
    _ = plane (state (2 * s)) 0 :=
      extension_eq_plane hw0 (by norm_num) (state (2 * s)) (resonant_regularized_eq hs) h0in
    _ = (state (2 * s)).1 zeroPoint := plane_eq (state (2 * s)) zeroPoint
    _ = 2 * riemannZeta (2 * s - 1) := state_zero hw0 hw2

theorem resonantLewisPeriod_one_ne_zero {s : ℂ} (hs : IsMayerScatteringResonance s) :
    resonantLewisPeriod s 1 ≠ 0 := by
  obtain ⟨hw0, hw1⟩ := two_mul_re_bounds hs.1 hs.2.1
  rw [resonantLewisPeriod_one_eq hs]
  exact mul_ne_zero two_ne_zero (shifted_zeta_ne_zero hw0 hw1)

/-! ## Right-half Mayer resonances and the Weil–Hodge polar defect -/

/-- Mayer scattering resonances strictly right of the critical line `Re s = 1/4`. -/
def rightMayerResonances : Set ℂ :=
  {s | 1 / 4 < s.re ∧ IsMayerScatteringResonance s}

/-- Upper-half-plane Mayer scattering resonances strictly right of `Re s = 1/4`. -/
def upperRightMayerResonances : Set ℂ :=
  {s | 1 / 4 < s.re ∧ 0 < s.im ∧ IsMayerScatteringResonance s}

private theorem image_rightMayerResonances :
    (fun s : ℂ => 2 * s - 1) '' rightMayerResonances = reflectionPoles := by
  ext z
  simp only [Set.mem_image, rightMayerResonances, reflectionPoles, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, ⟨hquarter, hs⟩, rfl⟩
    have h0 : 0 < s.re := hs.1
    have h1 : s.re < 1 / 2 := hs.2.1
    obtain ⟨hw0, _⟩ := two_mul_re_bounds h0 h1
    have hζ := (isMayerScatteringResonance_iff_zeta_zero h0 h1).mp hs
    have hre_2s : (2 * s - 1).re = 2 * s.re - 1 := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [show 2 * s - 1 + 1 = 2 * s by ring]
      exact (completedRiemannZeta_eq_zero_iff hw0).mpr hζ
    · rw [hre_2s]; linarith
    · rw [hre_2s]; linarith
  · rintro ⟨hΛ, hre_low, hre_high⟩
    refine ⟨(z + 1) / 2, ?_, by ring⟩
    have hs_q : 1 / 4 < ((z + 1) / 2).re := by
      simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
      linarith
    have hs_0 : 0 < ((z + 1) / 2).re := by linarith
    have hs_1 : ((z + 1) / 2).re < 1 / 2 := by
      simp only [Complex.div_ofNat_re, Complex.add_re, Complex.one_re]
      linarith
    have h2 : 2 * ((z + 1) / 2) = z + 1 := by ring
    have hz1_pos : 0 < (z + 1).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    refine ⟨hs_q, (isMayerScatteringResonance_iff_zeta_zero hs_0 hs_1).mpr ?_⟩
    rw [h2]
    exact (completedRiemannZeta_eq_zero_iff hz1_pos).mp hΛ

/-- The Weil–Hodge polar defect equals the extended cardinality of right-half Mayer resonances. -/
theorem boostPolarIndex_ratCorr_eq_encard_rightMayerResonances :
    boostPolarIndex ratCorr = rightMayerResonances.encard := by
  have hinj : Function.Injective (fun s : ℂ => 2 * s - 1) := fun a b h => by
    linear_combination (1 / 2 : ℂ) * h
  rw [boostPolarIndex_ratCorr_eq_encard_reflectionPoles, ← image_rightMayerResonances,
    hinj.injOn.encard_image]

/-- Since every strip Mayer resonance is non-real and conjugation-symmetric, the Weil–Hodge
polar defect is exactly twice the cardinality of upper right-half Mayer resonances. -/
theorem boostPolarIndex_ratCorr_eq_two_mul_encard_upperRightMayerResonances :
    boostPolarIndex ratCorr = 2 * upperRightMayerResonances.encard := by
  have hsplit : rightMayerResonances =
      upperRightMayerResonances ∪ (starRingEnd ℂ) '' upperRightMayerResonances := by
    ext s
    simp only [rightMayerResonances, upperRightMayerResonances, Set.mem_union, Set.mem_setOf_eq,
      Set.mem_image]
    constructor
    · rintro ⟨hq, hs⟩
      have him := im_ne_zero_of_isMayerScatteringResonance hs
      rcases lt_or_gt_of_ne him with hneg | hpos
      · right
        refine ⟨(starRingEnd ℂ) s, ⟨by simpa using hq, ?_,
          isMayerScatteringResonance_conj_iff.mpr hs⟩, Complex.conj_conj s⟩
        simp only [Complex.conj_im]
        linarith
      · exact Or.inl ⟨hq, hpos, hs⟩
    · rintro (⟨hq, _, hs⟩ | ⟨u, ⟨hq, _, hu⟩, rfl⟩)
      · exact ⟨hq, hs⟩
      · exact ⟨by simpa using hq, isMayerScatteringResonance_conj_iff.mpr hu⟩
  have hdisj : Disjoint upperRightMayerResonances ((starRingEnd ℂ) '' upperRightMayerResonances) := by
    rw [Set.disjoint_left]
    rintro s ⟨_, hs_pos, _⟩ ⟨u, ⟨_, hu_pos, _⟩, rfl⟩
    simp only [Complex.conj_im] at hs_pos
    linarith
  rw [boostPolarIndex_ratCorr_eq_encard_rightMayerResonances, hsplit,
    Set.encard_union_eq hdisj, (RingHom.injective (starRingEnd ℂ)).injOn.encard_image, two_mul]

/-- The Riemann Hypothesis holds iff every Mayer scattering resonance lies on `Re s = 1/4`. -/
theorem riemannHypothesis_iff_forall_isMayerScatteringResonance_re :
    RiemannHypothesis ↔ ∀ s : ℂ, IsMayerScatteringResonance s → s.re = 1 / 4 := by
  rw [riemannHypothesis_iff_renormalizedHodgeIndex, RenormalizedHodgeIndex,
    boostPolarIndex_ratCorr_eq_encard_rightMayerResonances, Set.encard_eq_zero,
    Set.eq_empty_iff_forall_notMem]
  constructor
  · intro hemp s hs
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have href : riemannMayerReflect s ∈ rightMayerResonances := by
        refine ⟨?_, isMayerScatteringResonance_reflect_iff.mpr hs⟩
        rw [riemannMayerReflect_re]
        linarith
      exact hemp (riemannMayerReflect s) href
    · exact hemp s ⟨hgt, hs⟩
  · intro hall s ⟨hgt, hs⟩
    have heq := hall s hs
    linarith

#print axioms isMayerScatteringResonance_iff_zeta_zero
#print axioms isMayerScatteringResonance_iff_determinant_excess
#print axioms isMayerScatteringResonance_iff_positiveBoundary_pole
#print axioms isMayerScatteringResonance_iff_scatteringEntry_pole
#print axioms im_ne_zero_of_isMayerScatteringResonance
#print axioms resonantLewisPeriod_reciprocity
#print axioms resonantLewisPeriod_three_term
#print axioms resonantLewisPeriod_one_ne_zero
#print axioms boostPolarIndex_ratCorr_eq_two_mul_encard_upperRightMayerResonances
#print axioms riemannHypothesis_iff_forall_isMayerScatteringResonance_re

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
