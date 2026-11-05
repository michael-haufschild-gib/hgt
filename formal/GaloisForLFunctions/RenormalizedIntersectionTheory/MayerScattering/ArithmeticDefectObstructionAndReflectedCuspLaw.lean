import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.TheRetainedHeckeChannelReadsTheQuarterLine
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.TheEisensteinPeriodIsAHeckeEigenfunctionForEveryPrime
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.PhysicalCuspKreinResidue
import GaloisForLFunctions.RHTower.XiCriticalZeroLinearNodes
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Arithmetic Defect Identities, Critical-Line Obstructions, and Reflected Cusp Energy

At every Mayer scattering resonance `s` (`0 < Re s < 1/2`), the co-isometry defect
`lewisCoIsometryDefect s ψ_s = ‖ψ_s‖²_LP - ‖I_{1/2 - conj s} ψ_s‖²_LP` of the resonant global Lewis
period `ψ_s = resonantLewisPeriod s` satisfies `D_s(ψ_s) ≤ 0`, with `D_s(ψ_s) = 0 ↔ Re s = 1/4`
and `D_s(ψ_s) < 0 ↔ Re s ≠ 1/4`. This module establishes both its exact arithmetic representations
through source Hecke operators and the Lewis three-term resonance equation, and the structural
obstructions governing any nonnegative cusp-energy or Hecke-norm expression:

1. **Nonvanishing strip Hecke eigenvalues, prime-Hecke defect identity, and three-term resonance
   identity** (`heckeEigenvalue_ne_zero_of_isMayerScatteringResonance`,
   `resonantLewisPeriod_coIsometryDefect_eq_hecke`,
   `resonantLewisPeriod_add_one_eq_sub`,
   `neg_resonantLewisPeriod_coIsometryDefect_arithmetic`). At every Mayer resonance `s` and every
   prime `p`, `‖p^{1 - 2s}‖ = p^{1 - 2 Re s} > 1`, so `1 + p^{1 - 2s} ≠ 0` unconditionally across
   the entire strip. Substituting the prime-Hecke eigenrelation `T_{p, s} ψ_s = (1 + p^{1-2s}) ψ_s`
   and the Lewis three-term resonance identity
   `ψ_s(x + 1) = ψ_s(x) - (x + 1)^{-2s} ψ_s(x / (x + 1))` expresses `-D_s(ψ_s) ≥ 0` identically as
   a manifestly nonnegative arithmetic integral through every prime's Hecke operator `T_{p, s} ψ_s`
   and through the parabolic three-term shift difference on `(0, ∞)`.

2. **Infinitely many critical-line resonances with `D_s(ψ_s) = 0` versus strictly positive cusp and
   Hecke norms** (`criticalUpperMayerResonances_infinite`,
   `criticalResonance_defect_zero_vs_positive_norms`). Unconditionally, infinitely many upper Mayer
   resonances lie on `Re s = 1/4`. At every such critical resonance, `D_s(ψ_s) = 0`, whereas the
   `H_LP` norm `‖ψ_s‖²_LP`, the renormalized physical cusp energy
   `lim_{T → ∞} (mayerCuspEnergy (b_s) T - mayerCuspCounterterm (b_s) T) / T = 1`, the outgoing
   cusp charge `‖mayerCuspCharge s‖²`, and the `T₂` retained boundary charge
   `‖mayerPeriodCore s 2‖²` are all strictly positive.

3. **Reflection-parity obstruction and reflected physical cusp Krein law**
   (`defect_reflection_parity_and_cusp_obstruction`, `mayerDefect_nonneg_representation_iff`).
   For every off-line resonance `s ∈ upperMayerResonances` (`Re s ≠ 1/4`), `D_s(ψ_s) < 0` and
   `D_{s^♯}(ψ_{s^♯}) < 0` have the same strict negative sign on both halves of the strip, whereas
   the `T₂` retained Hecke channel `u_s = core_s(2) · 1_{(0, 1)}` reverses sign under
   `s ↦ s^♯ = 1/2 - conj s` (`D_s(u_s) · D_{s^♯}(u_{s^♯}) < 0`), and the single-mode physical cusp
   mean energy `(mayerKreinForm b_s b_s).re = 0` vanishes identically off `Re s = 1/4` while taking
   value `-2 < 0` on the reflected cusp pair `b_s - b_{s^♯}`. Globally across all resonances,
   existence of any nonnegative representation `D_s(ψ_s) = E(s) ≥ 0` is unconditionally equivalent
   to `∀ s, D_s(ψ_s) = 0`, to nonnegativity of the renormalized physical cusp mean energy on
   `mayerPeriodKreinSpace`, to `∀ s : upperMayerResonances, s.1.re = 1/4`, and to `RiemannHypothesis`.
-/

set_option autoImplicit false
noncomputable section

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCutoff MayerParameter MayerScatteringMellin MayerScatteringState
open MayerScatteringPeriod MayerGlobalPeriods

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-! ### 1. Defect weight kernel, prime-Hecke defect identity, and three-term resonance identity -/

/-- The nonnegative strip reflection kernel
`(b + b⁻¹)^{-6} b^{2σ - 1} (b^{2σ - 1/2} + b^{-(2σ - 1/2)}) (b^{2σ - 1/2} - b^{-(2σ - 1/2)})²`
governing `lewisCoIsometryDefect` on `(1, ∞)`. -/
def mayerDefectWeight (σ b : ℝ) : ℝ :=
  (b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * σ - 1) *
    (b ^ (2 * σ - 1 / 2) + b ^ (-(2 * σ - 1 / 2))) *
    (b ^ (2 * σ - 1 / 2) - b ^ (-(2 * σ - 1 / 2))) ^ 2

theorem mayerDefectWeight_nonneg {σ b : ℝ} (hb : 0 < b) :
    0 ≤ mayerDefectWeight σ b := by
  unfold mayerDefectWeight
  have h1 : 0 ≤ (b + b⁻¹) ^ (-6 : ℝ) :=
    (Real.rpow_pos_of_pos (add_pos hb (inv_pos.mpr hb)) _).le
  have h2 : 0 ≤ b ^ (2 * σ - 1) := (Real.rpow_pos_of_pos hb _).le
  have h3 : 0 ≤ b ^ (2 * σ - 1 / 2) + b ^ (-(2 * σ - 1 / 2)) :=
    add_nonneg (Real.rpow_pos_of_pos hb _).le (Real.rpow_pos_of_pos hb _).le
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) (sq_nonneg _)

theorem mayerDefectWeight_quarter (b : ℝ) :
    mayerDefectWeight (1 / 4) b = 0 := by
  unfold mayerDefectWeight
  rw [show (2 * (1 / 4 : ℝ) - 1 / 2) = 0 by norm_num, neg_zero]
  simp [sub_self]

/-- At every Mayer scattering resonance `s` (`0 < Re s < 1/2`) and every prime `p`,
`1 < ‖(p : ℂ) ^ (1 - 2 * s)‖` and hence the source Hecke eigenvalue `1 + p^{1 - 2s}` is strictly
nonzero. -/
theorem heckeEigenvalue_ne_zero_of_isMayerScatteringResonance {p : ℕ} [hp : Fact p.Prime]
    {s : ℂ} (hs : IsMayerScatteringResonance s) :
    1 < ‖(p : ℂ) ^ (1 - 2 * s)‖ ∧ 1 + (p : ℂ) ^ (1 - 2 * s) ≠ 0 := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hexp_pos : 0 < (1 - 2 * s).re := by
    have hre : (1 - 2 * s).re = 1 - 2 * s.re := by simp
    rw [hre]; linarith [hs.2.1]
  have hnorm : ‖(p : ℂ) ^ (1 - 2 * s)‖ = (p : ℝ) ^ (1 - 2 * s).re := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast]
    exact Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (1 - 2 * s)
  have hgt1 : 1 < ‖(p : ℂ) ^ (1 - 2 * s)‖ := by
    rw [hnorm]
    exact Real.one_lt_rpow hp_gt1 hexp_pos
  refine ⟨hgt1, fun hzero => ?_⟩
  have heq : (p : ℂ) ^ (1 - 2 * s) = -1 := eq_neg_of_add_eq_zero_right hzero
  rw [heq, norm_neg, norm_one] at hgt1
  exact lt_irrefl 1 hgt1

/-- **Prime-Hecke arithmetic identity for `D_s(ψ_s)`.** At every Mayer resonance `s` and every
prime `p`, `D_s(ψ_s)` is expressed directly through the source Hecke action `T_{p, s} ψ_s` with
strictly positive normalizing factor `‖1 + p^{1 - 2s}‖⁻²`. -/
theorem resonantLewisPeriod_coIsometryDefect_eq_hecke {p : ℕ} [hp : Fact p.Prime]
    {s : ℂ} (hs : IsMayerScatteringResonance s) :
    lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) =
      -(‖1 + (p : ℂ) ^ (1 - 2 * s)‖ ^ 2)⁻¹ *
        ∫ b in Ioi (1 : ℝ),
          mayerDefectWeight s.re b *
            ‖lewisHeckeOperator p s (fun x => resonantLewisPeriod s x) b‖ ^ 2 := by
  have hnz := (heckeEigenvalue_ne_zero_of_isMayerScatteringResonance (p := p) hs).2
  have hsq_pos : 0 < ‖1 + (p : ℂ) ^ (1 - 2 * s)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hnz)
  rw [resonantLewisPeriod_coIsometryDefect_eq hs]
  have hcongr :
      (∫ b in Ioi (1 : ℝ),
          mayerDefectWeight s.re b *
            ‖lewisHeckeOperator p s (fun x => resonantLewisPeriod s x) b‖ ^ 2) =
        ‖1 + (p : ℂ) ^ (1 - 2 * s)‖ ^ 2 *
          ∫ b in Ioi (1 : ℝ),
            (b + b⁻¹) ^ (-6 : ℝ) * b ^ (2 * s.re - 1) *
              (b ^ (2 * s.re - 1 / 2) + b ^ (-(2 * s.re - 1 / 2))) *
              (b ^ (2 * s.re - 1 / 2) - b ^ (-(2 * s.re - 1 / 2))) ^ 2 *
              ‖resonantLewisPeriod s b‖ ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun b hb => ?_
    have hb0 : 0 < b := zero_lt_one.trans hb
    rw [resonantLewisPeriod_lewisHecke (p := p) hs hb0, norm_mul, mul_pow]
    unfold mayerDefectWeight
    ring
  rw [hcongr, neg_mul, inv_mul_cancel_left₀ hsq_pos.ne']

/-- **Lewis three-term shift identity on `(0, ∞)`.** At every Mayer resonance `s` and every `x > 0`,
`ψ_s(x + 1) = ψ_s(x) - (x + 1)^{-2s} ψ_s(x / (x + 1))`. -/
theorem resonantLewisPeriod_add_one_eq_sub {s : ℂ} (hs : IsMayerScatteringResonance s)
    {x : ℝ} (hx : 0 < x) :
    resonantLewisPeriod s (x + 1 : ℝ) =
      resonantLewisPeriod s x -
        ((x + 1 : ℝ) : ℂ) ^ (-(2 * s)) * resonantLewisPeriod s (x / (x + 1) : ℝ) := by
  have h := resonantLewisPeriod_three_term (a := (x : ℂ)) hs (by simpa using hx)
  rw [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one]
  exact eq_sub_of_add_eq h.symm

/-- Change of variables `b = x + 1` mapping `(0, ∞)` onto `(1, ∞)`. -/
theorem integral_Ioi_one_eq_shift_zero (g : ℝ → ℝ) :
    (∫ b in Ioi (1 : ℝ), g b) = ∫ x in Ioi (0 : ℝ), g (x + 1) := by
  have himg : (fun x : ℝ => x + 1) '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
    ext b
    simp only [mem_image, mem_Ioi]
    exact ⟨fun ⟨x, hx, heq⟩ => by linarith, fun hb => ⟨b - 1, by linarith, sub_add_cancel b 1⟩⟩
  have hinj : InjOn (fun x : ℝ => x + 1) (Ioi 0) := fun _ _ _ _ h => add_right_cancel h
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => u + 1) 1 (Ioi 0) x :=
    fun x _ => ((hasDerivAt_id x).add_const 1).hasDerivWithinAt
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj g
  rw [himg] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp

/-- **Three-term resonance representation of `D_s(ψ_s)` and manifest nonnegativity of `-D_s(ψ_s)`.**
At every Mayer scattering resonance `s`, `-D_s(ψ_s)` equals both the prime-Hecke weighted norm
square on `(1, ∞)` (for every prime `p`) and the parabolic three-term shift norm square on `(0, ∞)`,
each with pointwise nonnegative integrand, and `-D_s(ψ_s) ≥ 0` (strictly positive iff `s.re ≠ 1/4`). -/
theorem neg_resonantLewisPeriod_coIsometryDefect_arithmetic {p : ℕ} [hp : Fact p.Prime]
    {s : ℂ} (hs : IsMayerScatteringResonance s) :
    -lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) =
        (‖1 + (p : ℂ) ^ (1 - 2 * s)‖ ^ 2)⁻¹ *
          ∫ b in Ioi (1 : ℝ),
            mayerDefectWeight s.re b *
              ‖lewisHeckeOperator p s (fun x => resonantLewisPeriod s x) b‖ ^ 2 ∧
      -lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) =
        ∫ x in Ioi (0 : ℝ),
          mayerDefectWeight s.re (x + 1) *
            ‖resonantLewisPeriod s x -
              ((x + 1 : ℝ) : ℂ) ^ (-(2 * s)) * resonantLewisPeriod s (x / (x + 1) : ℝ)‖ ^ 2 ∧
      0 ≤ -lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) ∧
      (0 < -lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) ↔ s.re ≠ 1 / 4) := by
  have hhecke : -lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) =
      (‖1 + (p : ℂ) ^ (1 - 2 * s)‖ ^ 2)⁻¹ *
        ∫ b in Ioi (1 : ℝ),
          mayerDefectWeight s.re b *
            ‖lewisHeckeOperator p s (fun x => resonantLewisPeriod s x) b‖ ^ 2 := by
    rw [resonantLewisPeriod_coIsometryDefect_eq_hecke (p := p) hs, neg_mul, neg_neg]
  have h3term : -lewisCoIsometryDefect s (fun a : ℝ => resonantLewisPeriod s a) =
      ∫ x in Ioi (0 : ℝ),
        mayerDefectWeight s.re (x + 1) *
          ‖resonantLewisPeriod s x -
            ((x + 1 : ℝ) : ℂ) ^ (-(2 * s)) * resonantLewisPeriod s (x / (x + 1) : ℝ)‖ ^ 2 := by
    rw [resonantLewisPeriod_coIsometryDefect_eq hs, neg_neg, integral_Ioi_one_eq_shift_zero]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [resonantLewisPeriod_add_one_eq_sub hs hx]
    unfold mayerDefectWeight
    rfl
  exact ⟨hhecke, h3term, neg_nonneg.mpr (resonantLewisPeriod_coIsometryDefect_nonpos hs),
    neg_pos.trans (resonantLewisPeriod_coIsometryDefect_lt_zero_iff hs)⟩

/-! ### 2. Infinitely many critical-line resonances with `D_s(ψ_s) = 0` versus positive norms -/

private theorem isMayerResonance_quarter_of_Xi_eq_zero {τ : ℝ} (hXi : _root_.RHTower.Xi τ = 0) :
    IsMayerScatteringResonance ((1 / 4 : ℂ) + ((τ / 2 : ℝ) : ℂ) * I) := by
  have hre : ((1 / 4 : ℂ) + ((τ / 2 : ℝ) : ℂ) * I).re = 1 / 4 := by simp
  refine (isMayerScatteringResonance_iff_zeta_zero
    (by rw [hre]; norm_num) (by rw [hre]; norm_num)).mpr ?_
  have hxi : _root_.RHTower.xi (2 * ((1 / 4 : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)) = 0 := by
    have heq : _root_.RHTower.xi (2 * ((1 / 4 : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)) =
        _root_.RHTower.XiC (τ : ℂ) := by
      unfold _root_.RHTower.XiC
      congr 1
      apply Complex.ext <;> simp <;> ring
    rw [heq, _root_.RHTower.XiC_ofReal, hXi, Complex.ofReal_zero]
  have h2re : (2 * ((1 / 4 : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)).re = 1 / 2 := by simp; norm_num
  exact (_root_.RHTower.xi_zero_iff_zeta_zero_of_mem_strip
    (by rw [h2re]; norm_num) (by rw [h2re]; norm_num)).mp hxi

/-- **Unconditional infinitude of critical-line upper Mayer resonances.** There are infinitely many
upper Mayer scattering resonances `s ∈ upperMayerResonances` on `Re s = 1/4`. -/
theorem criticalUpperMayerResonances_infinite :
    {s : upperMayerResonances | s.1.re = 1 / 4}.Infinite := by
  classical
  intro hfin
  obtain ⟨c₀, hc₀, T₀, hT₀, hmany⟩ := _root_.RHTower.exists_many_critical_ordinates_dyadic
  set M : ℕ := hfin.toFinset.card
  set T : ℝ := max T₀ (Real.exp (((M : ℝ) + 1) / c₀))
  have hTT₀ : T₀ ≤ T := le_max_left _ _
  have hT1 : 1 ≤ T := hT₀.trans hTT₀
  have hTe : Real.exp (((M : ℝ) + 1) / c₀) ≤ T := le_max_right _ _
  have hlog : ((M : ℝ) + 1) / c₀ ≤ Real.log T := by
    rw [← Real.log_exp (((M : ℝ) + 1) / c₀)]
    exact Real.log_le_log (Real.exp_pos _) hTe
  have hclog : (M : ℝ) + 1 ≤ c₀ * Real.log T := by
    rw [mul_comm]
    exact (div_le_iff₀ hc₀).mp hlog
  have hMlt : (M : ℝ) < c₀ * (T * Real.log T) := by
    have hlog0 : 0 < Real.log T := lt_of_lt_of_le (by positivity) hlog
    have hle_T : c₀ * Real.log T ≤ c₀ * (T * Real.log T) := by
      rw [← mul_assoc, mul_comm c₀ T, mul_assoc]
      exact le_mul_of_one_le_left (mul_pos hc₀ hlog0).le hT1
    linarith only [hclog, hle_T]
  obtain ⟨τS, hτS, hcard⟩ := hmany T hTT₀
  let embed : ℝ → upperMayerResonances := fun τ =>
    if h : 0 < τ ∧ _root_.RHTower.Xi τ = 0 then
      ⟨(1 / 4 : ℂ) + ((τ / 2 : ℝ) : ℂ) * I,
        ⟨by simp; linarith [h.1], isMayerResonance_quarter_of_Xi_eq_zero h.2⟩⟩
    else
      Classical.choice (by
        obtain ⟨τ₀, hτ₀⟩ := Finset.card_pos.mp (by
          have : (0 : ℝ) < τS.card := lt_of_le_of_lt (Nat.cast_nonneg M) (hMlt.trans_le hcard)
          exact_mod_cast this)
        obtain ⟨hgt, _, hXi⟩ := hτS τ₀ hτ₀
        exact ⟨⟨(1 / 4 : ℂ) + ((τ₀ / 2 : ℝ) : ℂ) * I,
          ⟨by simp; linarith, isMayerResonance_quarter_of_Xi_eq_zero hXi⟩⟩⟩)
  have hmaps : ∀ τ ∈ τS, embed τ ∈ hfin.toFinset := by
    intro τ hτ
    obtain ⟨hgt, _, hXi⟩ := hτS τ hτ
    have hcond : 0 < τ ∧ _root_.RHTower.Xi τ = 0 := ⟨by linarith, hXi⟩
    rw [Set.Finite.mem_toFinset, mem_setOf_eq]
    dsimp only [embed]
    rw [dif_pos hcond]
    simp
  have hinj : InjOn embed τS := by
    intro τ₁ hτ₁ τ₂ hτ₂ heq
    obtain ⟨hgt₁, _, hXi₁⟩ := hτS τ₁ hτ₁
    obtain ⟨hgt₂, _, hXi₂⟩ := hτS τ₂ hτ₂
    have hc₁ : 0 < τ₁ ∧ _root_.RHTower.Xi τ₁ = 0 := ⟨by linarith, hXi₁⟩
    have hc₂ : 0 < τ₂ ∧ _root_.RHTower.Xi τ₂ = 0 := ⟨by linarith, hXi₂⟩
    dsimp only [embed] at heq
    rw [dif_pos hc₁, dif_pos hc₂] at heq
    have him := congrArg (fun u : upperMayerResonances => u.1.im) heq
    simp only [add_im, div_ofNat_im, one_im, zero_div, mul_im, ofReal_re, I_im, mul_one,
      ofReal_im, I_re, mul_zero, add_zero] at him
    linarith
  have hleM : τS.card ≤ M := Finset.card_le_card_of_injOn embed hmaps hinj
  have hleMr : (τS.card : ℝ) ≤ M := by exact_mod_cast hleM
  linarith

/-- Strict positivity of `lewisCriticalNormSq` on every resonant global Lewis period function. -/
theorem resonantLewisPeriod_lewisCriticalNormSq_pos {s : ℂ} (hs : IsMayerScatteringResonance s) :
    0 < lewisCriticalNormSq (fun a : ℝ => resonantLewisPeriod s a) :=
  resonantLewisPeriod_pos_lewisCriticalNormSq hs

/-- **Critical-line vanishing of `D_s(ψ_s)` versus strict positivity of physical cusp and Hecke norms.**
At every critical-line resonance `s ∈ upperMayerResonances` (`s.1.re = 1/4`), `D_s(ψ_s) = 0` and
`D_s(u_s) = 0`, whereas `‖ψ_s‖²_LP > 0`, the renormalized physical cusp mean energy of `b_s`
converges to `1 > 0`, `‖mayerCuspCharge s‖² > 0`, and `‖mayerPeriodCore s 2‖² > 0`. -/
theorem criticalResonance_defect_zero_vs_positive_norms (s : upperMayerResonances)
    (hcrit : s.1.re = 1 / 4) :
    lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a) = 0 ∧
      lewisCoIsometryDefect s.1 (heckeBoundaryChannel (mayerPeriodCore s.1 2)) = 0 ∧
      0 < lewisCriticalNormSq (fun a : ℝ => resonantLewisPeriod s.1 a) ∧
      (mayerKreinForm (mayerPeriodBasis s) (mayerPeriodBasis s)).re = 1 ∧
      Tendsto (fun T : ℝ =>
          (mayerCuspEnergy (mayerPeriodBasis s) T -
            mayerCuspCounterterm (mayerPeriodBasis s) T) / T)
        atTop (𝓝 1) ∧
      0 < ‖mayerCuspCharge s‖ ^ 2 ∧
      0 < ‖mayerPeriodCore s.1 2‖ ^ 2 := by
  have hd0 := (resonantLewisPeriod_coIsometryDefect_eq_zero_iff s.2.2).mpr hcrit
  have hu0 := (retainedHeckeChannel_defect_sign s).2.2.1.mpr hcrit
  have hnorm := resonantLewisPeriod_lewisCriticalNormSq_pos s.2.2
  have hrefl : s = reflectUpperResonance s :=
    ((reflectUpperResonance_eq_self_iff s).mpr hcrit).symm
  have hkrein : (mayerKreinForm (mayerPeriodBasis s) (mayerPeriodBasis s)).re = 1 := by
    rw [mayerKreinForm_basis, if_pos hrefl, one_re]
  have hcusp := mayerCuspEnergy_renormalized_mean (mayerPeriodBasis s)
  rw [hkrein] at hcusp
  exact ⟨hd0, hu0, hnorm, hkrein, hcusp,
    sq_pos_of_pos (norm_pos_iff.mpr (mayerCuspCharge_ne_zero s)),
    sq_pos_of_pos (norm_pos_iff.mpr (mayerPeriodCore_two_ne_zero s.2))⟩

/-! ### 3. Off-line reflection-parity obstruction and global RH equivalence -/

/-- **Reflection-parity separation and reflected physical cusp obstruction.** At every off-line
resonance `s ∈ upperMayerResonances` (`s.1.re ≠ 1/4`):
1. both `D_s(ψ_s) < 0` and `D_{s^♯}(ψ_{s^♯}) < 0` (even-sign strict negativity on both sides of
   `Re s = 1/4`);
2. the `T₂` retained Hecke channel `u_s = core_s(2) · 1_{(0, 1)}` has strictly opposite signs on
   `(s, s^♯)`: `D_s(u_s) * D_{s^♯}(u_{s^♯}) < 0`;
3. the single-mode physical cusp mean energy `(mayerKreinForm b_s b_s).re` vanishes identically
   (`= 0`), while the reflected cusp pair `mayerOffLineNegativeState s = b_s - b_{s^♯}` has
   renormalized physical cusp mean energy `-2 < 0`. -/
theorem defect_reflection_parity_and_cusp_obstruction {s : upperMayerResonances}
    (hoff : s.1.re ≠ 1 / 4) :
    lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a) < 0 ∧
      lewisCoIsometryDefect (reflectUpperResonance s).1
        (fun a : ℝ => resonantLewisPeriod (reflectUpperResonance s).1 a) < 0 ∧
      lewisCoIsometryDefect s.1 (heckeBoundaryChannel (mayerPeriodCore s.1 2)) *
        lewisCoIsometryDefect (reflectUpperResonance s).1
          (heckeBoundaryChannel (mayerPeriodCore (reflectUpperResonance s).1 2)) < 0 ∧
      (mayerKreinForm (mayerPeriodBasis s) (mayerPeriodBasis s)).re = 0 ∧
      Tendsto (fun T : ℝ =>
          (mayerCuspEnergy (mayerOffLineNegativeState s) T -
            mayerCuspCounterterm (mayerOffLineNegativeState s) T) / T)
        atTop (𝓝 (-2)) := by
  have hoff_refl : (reflectUpperResonance s).1.re ≠ 1 / 4 := by
    rw [reflectUpperResonance_coe, riemannMayerReflect_re]
    intro h; apply hoff; linarith
  have hd1 := (resonantLewisPeriod_coIsometryDefect_lt_zero_iff s.2.2).mpr hoff
  have hd2 := (resonantLewisPeriod_coIsometryDefect_lt_zero_iff (reflectUpperResonance s).2.2).mpr
    hoff_refl
  have hprod :
      lewisCoIsometryDefect s.1 (heckeBoundaryChannel (mayerPeriodCore s.1 2)) *
        lewisCoIsometryDefect (reflectUpperResonance s).1
          (heckeBoundaryChannel (mayerPeriodCore (reflectUpperResonance s).1 2)) < 0 := by
    rcases lt_or_gt_of_ne hoff with hlt | hgt
    · have hp := (retainedHeckeChannel_defect_sign s).2.1.mpr hlt
      have hn := (retainedHeckeChannel_defect_reflect s).mp hp
      exact mul_neg_of_pos_of_neg hp hn
    · have hn := (retainedHeckeChannel_defect_sign s).2.2.2.mpr hgt
      have hlt_refl : (reflectUpperResonance s).1.re < 1 / 4 := by
        rw [reflectUpperResonance_coe, riemannMayerReflect_re]; linarith
      have hp := (retainedHeckeChannel_defect_sign (reflectUpperResonance s)).2.1.mpr hlt_refl
      exact mul_neg_of_neg_of_pos hn hp
  have hne_refl : s ≠ reflectUpperResonance s :=
    fun h => hoff ((reflectUpperResonance_eq_self_iff s).mp h.symm)
  have hsingle0 : (mayerKreinForm (mayerPeriodBasis s) (mayerPeriodBasis s)).re = 0 := by
    rw [mayerKreinForm_basis, if_neg hne_refl, zero_re]
  have hpair_lim := mayerCuspEnergy_renormalized_mean (mayerOffLineNegativeState s)
  have hpair_re : (mayerKreinForm (mayerOffLineNegativeState s) (mayerOffLineNegativeState s)).re =
      -2 := by
    rw [mayerKreinForm_offLineNegativeState_self hoff]
    norm_num
  rw [hpair_re] at hpair_lim
  exact ⟨hd1, hd2, hprod, hsingle0, hpair_lim⟩

/-- **Complete unconditional characterization of nonnegative representations of `D_s(ψ_s)` across
all upper Mayer resonances.** The following are unconditionally equivalent:
1. `D_s(ψ_s)` admits a nonnegative expression `E(s) ≥ 0` across all `s ∈ upperMayerResonances`;
2. `0 ≤ D_s(ψ_s)` for all `s ∈ upperMayerResonances`;
3. `D_s(ψ_s) = 0` for all `s ∈ upperMayerResonances`;
4. for every `v ∈ mayerPeriodKreinSpace`, the renormalized physical cusp mean energy
   `lim_{T → ∞} (mayerCuspEnergy v T - mayerCuspCounterterm v T) / T` is nonnegative;
5. `s.1.re = 1/4` for all `s ∈ upperMayerResonances`;
6. `RiemannHypothesis`. -/
theorem mayerDefect_nonneg_representation_iff :
    ((∃ E : upperMayerResonances → ℝ,
        (∀ s, 0 ≤ E s) ∧
        ∀ s, lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a) = E s) ↔
      (∀ s : upperMayerResonances,
        0 ≤ lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a))) ∧
    ((∀ s : upperMayerResonances,
        0 ≤ lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a)) ↔
      (∀ s : upperMayerResonances,
        lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a) = 0)) ∧
    ((∀ s : upperMayerResonances,
        lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a) = 0) ↔
      (∀ v : mayerPeriodKreinSpace, ∃ L : ℝ, 0 ≤ L ∧
        Tendsto (fun T : ℝ => (mayerCuspEnergy v T - mayerCuspCounterterm v T) / T)
          atTop (𝓝 L))) ∧
    ((∀ v : mayerPeriodKreinSpace, ∃ L : ℝ, 0 ≤ L ∧
        Tendsto (fun T : ℝ => (mayerCuspEnergy v T - mayerCuspCounterterm v T) / T)
          atTop (𝓝 L)) ↔
      (∀ s : upperMayerResonances, s.1.re = 1 / 4)) ∧
    ((∀ s : upperMayerResonances, s.1.re = 1 / 4) ↔ RiemannHypothesis) := by
  have h12 :
      (∃ E : upperMayerResonances → ℝ,
        (∀ s, 0 ≤ E s) ∧
        ∀ s, lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a) = E s) ↔
      (∀ s : upperMayerResonances,
        0 ≤ lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a)) :=
    ⟨fun ⟨E, hEnn, hEeq⟩ s => (hEeq s).symm ▸ hEnn s,
     fun hnn => ⟨fun s => lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a),
       hnn, fun _ => rfl⟩⟩
  have h23 :
      (∀ s : upperMayerResonances,
        0 ≤ lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a)) ↔
      (∀ s : upperMayerResonances,
        lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a) = 0) :=
    ⟨fun hnn s => le_antisymm (resonantLewisPeriod_coIsometryDefect_nonpos s.2.2) (hnn s),
     fun hz s => (hz s).ge⟩
  have h35 :
      (∀ s : upperMayerResonances,
        lewisCoIsometryDefect s.1 (fun a : ℝ => resonantLewisPeriod s.1 a) = 0) ↔
      (∀ s : upperMayerResonances, s.1.re = 1 / 4) :=
    forall_congr' fun s => resonantLewisPeriod_coIsometryDefect_eq_zero_iff s.2.2
  have h45 :
      (∀ v : mayerPeriodKreinSpace, ∃ L : ℝ, 0 ≤ L ∧
        Tendsto (fun T : ℝ => (mayerCuspEnergy v T - mayerCuspCounterterm v T) / T)
          atTop (𝓝 L)) ↔
      (∀ s : upperMayerResonances, s.1.re = 1 / 4) := by
    rw [← mayerKreinPositivity_iff_upperResonances_critical]
    constructor
    · intro hlim v
      obtain ⟨L, hLnn, hLt⟩ := hlim v
      have heq := tendsto_nhds_unique (mayerCuspEnergy_renormalized_mean v) hLt
      rwa [heq]
    · intro hpos v
      exact ⟨(mayerKreinForm v v).re, hpos v, mayerCuspEnergy_renormalized_mean v⟩
  exact ⟨h12, h23, h35.trans h45.symm, h45,
    mayerKreinPositivity_iff_upperResonances_critical.symm.trans
      mayerKreinPositivity_iff_riemannHypothesis⟩

#print axioms heckeEigenvalue_ne_zero_of_isMayerScatteringResonance
#print axioms resonantLewisPeriod_coIsometryDefect_eq_hecke
#print axioms resonantLewisPeriod_add_one_eq_sub
#print axioms neg_resonantLewisPeriod_coIsometryDefect_arithmetic
#print axioms criticalUpperMayerResonances_infinite
#print axioms criticalResonance_defect_zero_vs_positive_norms
#print axioms defect_reflection_parity_and_cusp_obstruction
#print axioms mayerDefect_nonneg_representation_iff

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

end
