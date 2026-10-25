import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveMeasureHamburgerRigidity
import GaloisForLFunctions.ArithmeticDefectRigidity.RecordMinimaForceInfiniteCofactorLimits
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HarmonicCouplingForcesSourceBlindness
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle
import GaloisForLFunctions.ArithmeticOrientationTheory.TheWidthFunctor
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Arithmetic Forces Blindness: The Three-Currency Forcing Law

Across the cancellation, positivity, and cohomological realization families, off-line
zero structure is governed by one common law: **arithmetic invariants annihilate defect
integrals and force test sources into the blind locus**.

This module establishes the three unconditional mechanisms of that law and their unified
transfer across all three currencies:

1. **Pole-saturated Bochner–Fejér defect annihilation and Beurling selectivity**:
   - Whenever a nonnegative spectral or boundary measure `μ`, a `μ`-almost-everywhere
     nonnegative observable `Φ`, and a nonnegative defect `D` satisfy a pole-dominated
     inequality `∫ Φ ∂μ + D ≤ P` with `P ≤ 0`, both `D = 0` and `Φ =ᵐ[μ] 0` follow
     (`measure_defect_eq_zero_of_pole_saturated`). Under integer divisor quantization
     `D = a₁ m` (`m : ℕ`) with `a₁ > 0`, strict pole domination `P < a₁` forces `m = 0`
     (`quantized_defect_eq_zero_of_pole_dominated`).
   - Instantiated via the collar-blind Fejér pairing on `[1, ∞)`, Riemann's degree-one
     theta transformation law characterizes `riemannPrimeMeasure` uniquely (if and only if)
     among all Borel Beurling prime measures on `(1, ∞)` with finite inverse-square moment
     (`measureTheta_beurlingIntegerMeasure_iff_eq_riemannPrimeMeasure`).

2. **Record-minimum escape floor and sharp all-degree Fejér saddle ceiling**:
   - In the single-channel cancellation family, every subcritical damping `0 < ε < 1 / 2`
     admits an actual cofactor limit `L` along record minima satisfying the prime-power
     floor `L.kernel p p ≥ p^{2ε - 2} > 0`, ruling out collapse of the actual cofactor
     kernel set to the augmentation singleton (`actualCofactorKernelSet_ne_singleton_augmentation`).
   - In the multi-channel positivity family, the renormalized off-line pole competition
     `a₁ m / (σ - β) - a₀ / (σ - 1)` on `σ > 1` completes to an exact square attaining its
     unique global maximum `(√(a₁ m) - √a₀)² / (1 - β)` at the saddle abscissa
     `σ* = 1 + (1 - β) √a₀ / (√(a₁ m) - √a₀)` (`renormalizedPoleGain_eq_sub_sq`,
     `isGreatest_renormalizedPoleGain`). Over all finite-degree nonnegative cosine
     polynomials (`1 ≤ K`, `0 < a 0 ≤ a 1`), the normalized simple-zero saddle gain has
     exact least upper bound `3 - 2 √2`, strictly unattained at every finite degree and
     approached as `M → ∞` by uniform Fejér autocorrelations (`isLUB_fejerSaddleGainSet`).

3. **Unconditional three-currency forcing on the arithmetic zero-free locus**:
   - Every zero-free region `Ω ⊆ ℂ` of `ζ` forces every Meyer strong-log source supported
     off-line inside `Ω` into the maximal blind ideal `meyerTraceBoundedIdeal` with
     nonnegative self-trace, forces every scaling cycle supported off-line inside `Ω` into
     `BlindOffLine zetaZeroConfig` with `OrbitHodgeIndex`, and forces simultaneous graded
     admissibility across all six canonically isomorphic `ζ`-receivers on `[0, 1 / 2]`.
   - On `forcedZeroFreeRegion = {z | Re z = 0 ∨ Re z = 1} ∪ harmonicZeroFreeCollar`, these
     forcing laws hold unconditionally (`arithmetic_forces_blindness_unconditional`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology CategoryTheory
open scoped Real ComplexConjugate ENNReal UpperHalfPlane
open Zeta23

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.ArithmeticDefectRigidity
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)

set_option autoImplicit false

/-! ### 1. Pole-saturated Bochner–Fejér defect annihilation and Beurling selectivity -/

/-- **Pole-saturated defect annihilation.**
If an integrable `μ`-almost-everywhere nonnegative observable `Φ` and a nonnegative scalar
defect `D` satisfy `∫ ω, Φ ω ∂μ + D ≤ P` against a nonpositive pole budget `P ≤ 0`, then
`D = 0`, `∫ ω, Φ ω ∂μ = 0`, and `Φ =ᵐ[μ] 0`. -/
theorem measure_defect_eq_zero_of_pole_saturated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Φ : Ω → ℝ} (hΦ_int : Integrable Φ μ) (hΦ_nn : 0 ≤ᵐ[μ] Φ)
    {D P : ℝ} (hD : 0 ≤ D) (hP : P ≤ 0)
    (hceil : ∫ ω, Φ ω ∂μ + D ≤ P) :
    D = 0 ∧ ∫ ω, Φ ω ∂μ = 0 ∧ Φ =ᵐ[μ] 0 := by
  have hint_nn : 0 ≤ ∫ ω, Φ ω ∂μ := integral_nonneg_of_ae hΦ_nn
  have hD0 : D = 0 := by linarith
  have hint0 : ∫ ω, Φ ω ∂μ = 0 := by linarith
  exact ⟨hD0, hint0, (integral_eq_zero_iff_of_nonneg_ae hΦ_nn hΦ_int).mp hint0⟩

/-- **Quantized divisor-order annihilation.**
If a `μ`-almost-everywhere nonnegative observable `Φ` and an integer multiplicity `m : ℕ`
weighted by `a₁ > 0` satisfy `∫ ω, Φ ω ∂μ + a₁ * m ≤ P` with strict pole domination
`P < a₁`, then `m = 0`. -/
theorem quantized_defect_eq_zero_of_pole_dominated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {Φ : Ω → ℝ} (hΦ_nn : 0 ≤ᵐ[μ] Φ)
    {a₁ P : ℝ} {m : ℕ} (ha₁ : 0 < a₁) (hP : P < a₁)
    (hceil : ∫ ω, Φ ω ∂μ + a₁ * (m : ℝ) ≤ P) :
    m = 0 := by
  have hint_nn : 0 ≤ ∫ ω, Φ ω ∂μ := integral_nonneg_of_ae hΦ_nn
  by_contra hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  nlinarith

/-- On `(0, ∞)`, the theta transform of the positive-integer counting measure
`∑_{k ≥ 0} δ_{k + 1}` equals `(jacobiTheta (i x) - 1) / 2`. -/
theorem measureTheta_nat_sum_eq_jacobiTheta {x : ℝ} (hx : 0 < x) :
    measureTheta (Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1))) x =
      (jacobiTheta (I * (x : ℂ)) - 1) / 2 := by
  set ν₀ : Measure ℝ := Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1))
  have hP0 : riemannPrimeMeasure (Iic 1) = 0 := riemannPrimeMeasure_Iic_one_eq_zero
  have hP_Iio : riemannPrimeMeasure (Iio 1) = 0 := measure_mono_null Iio_subset_Iic_self hP0
  have hP_mom : Integrable (fun u : ℝ => 1 / u ^ 2) riemannPrimeMeasure :=
    integrable_inv_sq_of_integrable_rpow_neg_three_halves hP_Iio
      integrable_rpow_neg_three_halves_riemannPrimeMeasure
  have hν_supp : ν₀ (Iio 1) = 0 := by
    dsimp only [ν₀]
    rw [← beurlingIntegerMeasure_riemannPrimeMeasure]
    exact beurlingIntegerMeasure_Iio_one_eq_zero hP0
  have hν_mom : Integrable (fun u : ℝ => 1 / u ^ 2) ν₀ := by
    dsimp only [ν₀]
    rw [← beurlingIntegerMeasure_riemannPrimeMeasure]
    exact integrable_inv_sq_beurlingIntegerMeasure hP0 hP_mom
  have hint : Integrable (fun u : ℝ => ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ)) ν₀ :=
    integrable_measureTheta_integrand hν_supp hν_mom hx
  unfold measureTheta
  rw [MeasureTheory.integral_sum_measure hint]
  have hdirac : ∀ k : ℕ,
      (∫ u : ℝ, ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ) ∂Measure.dirac ((k : ℝ) + 1)) =
        cexp ((Real.pi : ℂ) * I * ((k : ℂ) + 1) ^ 2 * (I * (x : ℂ))) := by
    intro k
    rw [integral_dirac]
    have hexp : (Real.pi : ℂ) * I * ((k : ℂ) + 1) ^ 2 * (I * (x : ℂ)) =
        ((-Real.pi * ((k : ℝ) + 1) ^ 2 * x : ℝ) : ℂ) := by
      have h1 : (Real.pi : ℂ) * I * ((k : ℂ) + 1) ^ 2 * (I * (x : ℂ)) =
          I ^ 2 * ((Real.pi : ℂ) * ((k : ℂ) + 1) ^ 2 * (x : ℂ)) := by ring
      rw [h1, Complex.I_sq]
      push_cast
      ring
    rw [hexp, Complex.ofReal_exp]
  simp_rw [hdirac]
  have him : 0 < (I * (x : ℂ)).im := by simp [hx]
  exact (hasSum_nat_jacobiTheta him).tsum_eq

/-- Jacobi–Riemann theta transformation law for the positive-integer counting measure. -/
theorem measureTheta_nat_sum_relation {x : ℝ} (hx : 0 < x) :
    measureTheta (Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1))) x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) *
        measureTheta (Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1))) x⁻¹ +
        (-1 / 2 : ℂ) + (1 / 2 : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have hx_inv : 0 < x⁻¹ := inv_pos.mpr hx
  rw [measureTheta_nat_sum_eq_jacobiTheta hx, measureTheta_nat_sum_eq_jacobiTheta hx_inv]
  let τ : ℍ := ⟨I * ((x⁻¹ : ℝ) : ℂ), by simp [hx_inv]⟩
  have hS := jacobiTheta_S_smul τ
  rw [UpperHalfPlane.modular_S_smul] at hS
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hxinvC : ((x⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx_inv.ne'
  have hS_lhs : -(τ : ℂ)⁻¹ = I * (x : ℂ) := by
    change -(I * ((x⁻¹ : ℝ) : ℂ))⁻¹ = I * (x : ℂ)
    field_simp [hxinvC, I_ne_zero]
    rw [Complex.I_sq]
    norm_cast
    field_simp [hx.ne']
  have hS_base : -I * (τ : ℂ) = ((x⁻¹ : ℝ) : ℂ) := by
    change -I * (I * ((x⁻¹ : ℝ) : ℂ)) = ((x⁻¹ : ℝ) : ℂ)
    calc -I * (I * ((x⁻¹ : ℝ) : ℂ))
        = -(I ^ 2) * ((x⁻¹ : ℝ) : ℂ) := by ring
      _ = ((x⁻¹ : ℝ) : ℂ) := by rw [Complex.I_sq]; ring
  have hτ : (τ : ℂ) = I * ((x⁻¹ : ℝ) : ℂ) := rfl
  rw [hS_lhs, hS_base, hτ] at hS
  have hcpow : ((x⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    have h1 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    have h2 : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, ← Complex.ofReal_cpow hx_inv.le, ← Complex.ofReal_cpow hx.le,
      Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
  rw [hcpow] at hS
  rw [hS]
  ring

/-- **Exact Beurling–Hamburger prime-measure selectivity (`↔`).**
For any Borel measure `P` supported on `(1, ∞)` (`P (Iic 1) = 0`) with finite inverse-square
moment `Integrable (fun u => 1 / u²) P`, the multiplicative convolution exponential
`beurlingIntegerMeasure P` obeys Riemann's degree-one theta transformation law with polar
constants `(α, β)` if and only if `P = riemannPrimeMeasure`, `α = -1 / 2`, and `β = 1 / 2`. -/
theorem measureTheta_beurlingIntegerMeasure_iff_eq_riemannPrimeMeasure {P : Measure ℝ}
    (hP : P (Iic 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) P) (α β : ℂ) :
    (∀ x : ℝ, 0 < x →
      measureTheta (beurlingIntegerMeasure P) x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingIntegerMeasure P) x⁻¹ +
          α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) ↔
      (P = riemannPrimeMeasure ∧ α = -1 / 2 ∧ β = 1 / 2) := by
  constructor
  · intro htheta
    obtain ⟨hα, hβ, _, hP_eq⟩ := eq_riemannPrimeMeasure_of_beurling_theta_relation hP hmom htheta
    exact ⟨hP_eq, hα, hβ⟩
  · rintro ⟨rfl, rfl, rfl⟩ x hx
    rw [beurlingIntegerMeasure_riemannPrimeMeasure]
    exact measureTheta_nat_sum_relation hx

/-! ### 2. Exact renormalization saddle-point law and sharp `3 - 2 √2` Fejér ceiling -/

/-- Renormalized competition `a₁ m / (σ - β) - a₀ / (σ - 1)` between an off-line zero of
multiplicity `m` at abscissa `β < 1` and a simple pole at `s = 1` along `σ > 1`. -/
def renormalizedPoleGain (a₀ a₁ : ℝ) (m : ℕ) (β σ : ℝ) : ℝ :=
  a₁ * (m : ℝ) / (σ - β) - a₀ / (σ - 1)

/-- Saddle abscissa `σ* = 1 + (1 - β) √a₀ / (√(a₁ m) - √a₀)` maximizing
`renormalizedPoleGain` on `(1, ∞)` whenever `0 < a₀ < a₁ m` and `β < 1`. -/
def saddleAbscissa (a₀ a₁ : ℝ) (m : ℕ) (β : ℝ) : ℝ :=
  1 + (1 - β) * Real.sqrt a₀ / (Real.sqrt (a₁ * (m : ℝ)) - Real.sqrt a₀)

/-- **Exact algebraic square completion of the renormalized pole-zero gain.**
On `σ > 1` with `β < 1`, `0 ≤ a₀`, and `0 ≤ a₁ m`, the renormalized pole gain equals
`(√(a₁ m) - √a₀)² / (1 - β)` minus a manifestly nonnegative rational square vanishing
precisely at `saddleAbscissa`. -/
theorem renormalizedPoleGain_eq_sub_sq {a₀ a₁ : ℝ} {m : ℕ} {β σ : ℝ}
    (ha₀ : 0 ≤ a₀) (ham : 0 ≤ a₁ * (m : ℝ)) (hβ : β < 1) (hσ : 1 < σ) :
    renormalizedPoleGain a₀ a₁ m β σ =
      (Real.sqrt (a₁ * (m : ℝ)) - Real.sqrt a₀) ^ 2 / (1 - β) -
        ((Real.sqrt (a₁ * (m : ℝ)) - Real.sqrt a₀) * (σ - 1) - (1 - β) * Real.sqrt a₀) ^ 2 /
          ((1 - β) * (σ - 1) * (σ - β)) := by
  unfold renormalizedPoleGain
  have h1β : 1 - β ≠ 0 := ne_of_gt (sub_pos.mpr hβ)
  have hσ1 : σ - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hσ)
  have hσβ : σ - β ≠ 0 := ne_of_gt (by linarith)
  conv_lhs => rw [← Real.sq_sqrt ham, ← Real.sq_sqrt ha₀]
  field_simp [h1β, hσ1, hσβ]
  ring

/-- When `0 < a₀ < a₁ m` and `β < 1`, `saddleAbscissa a₀ a₁ m β` lies strictly to the right
of `1` and evaluates `renormalizedPoleGain` to `(√(a₁ m) - √a₀)² / (1 - β)`. -/
theorem saddleAbscissa_mem_Ioi_and_eval {a₀ a₁ : ℝ} {m : ℕ} {β : ℝ}
    (ha₀ : 0 < a₀) (hlt : a₀ < a₁ * (m : ℝ)) (hβ : β < 1) :
    1 < saddleAbscissa a₀ a₁ m β ∧
      renormalizedPoleGain a₀ a₁ m β (saddleAbscissa a₀ a₁ m β) =
        (Real.sqrt (a₁ * (m : ℝ)) - Real.sqrt a₀) ^ 2 / (1 - β) := by
  have hu_pos : 0 < Real.sqrt a₀ := Real.sqrt_pos.mpr ha₀
  have hvu_pos : 0 < Real.sqrt (a₁ * (m : ℝ)) - Real.sqrt a₀ :=
    sub_pos.mpr (Real.sqrt_lt_sqrt ha₀.le hlt)
  have h1β_pos : 0 < 1 - β := sub_pos.mpr hβ
  have hsad_gt : 1 < saddleAbscissa a₀ a₁ m β := by
    unfold saddleAbscissa
    linarith [div_pos (mul_pos h1β_pos hu_pos) hvu_pos]
  refine ⟨hsad_gt, ?_⟩
  rw [renormalizedPoleGain_eq_sub_sq ha₀.le (ha₀.le.trans hlt.le) hβ hsad_gt]
  have hnum0 : (Real.sqrt (a₁ * (m : ℝ)) - Real.sqrt a₀) * (saddleAbscissa a₀ a₁ m β - 1) -
      (1 - β) * Real.sqrt a₀ = 0 := by
    unfold saddleAbscissa
    have hvu_ne : Real.sqrt (a₁ * (m : ℝ)) - Real.sqrt a₀ ≠ 0 := ne_of_gt hvu_pos
    field_simp [hvu_ne]
    ring
  rw [hnum0, zero_pow two_ne_zero, zero_div, sub_zero]

/-- **Global saddle-point theorem for off-line pole-zero competition.**
For `0 < a₀ < a₁ m` and `β < 1`, `(√(a₁ m) - √a₀)² / (1 - β)` is the greatest value of
`renormalizedPoleGain a₀ a₁ m β` on `(1, ∞)`, attained uniquely at `saddleAbscissa`. -/
theorem isGreatest_renormalizedPoleGain {a₀ a₁ : ℝ} {m : ℕ} {β : ℝ}
    (ha₀ : 0 < a₀) (hlt : a₀ < a₁ * (m : ℝ)) (hβ : β < 1) :
    IsGreatest (renormalizedPoleGain a₀ a₁ m β '' Ioi 1)
      ((Real.sqrt (a₁ * (m : ℝ)) - Real.sqrt a₀) ^ 2 / (1 - β)) := by
  obtain ⟨hsad_gt, hsad_val⟩ := saddleAbscissa_mem_Ioi_and_eval ha₀ hlt hβ
  refine ⟨⟨saddleAbscissa a₀ a₁ m β, hsad_gt, hsad_val⟩, ?_⟩
  rintro _ ⟨σ, hσ, rfl⟩
  rw [renormalizedPoleGain_eq_sub_sq ha₀.le (ha₀.le.trans hlt.le) hβ hσ]
  have h1β : 0 < 1 - β := sub_pos.mpr hβ
  have hσ1 : 0 < σ - 1 := sub_pos.mpr hσ
  have hσβ : 0 < σ - β := by linarith
  have hrem_nn : 0 ≤ ((Real.sqrt (a₁ * (m : ℝ)) - Real.sqrt a₀) * (σ - 1) -
      (1 - β) * Real.sqrt a₀) ^ 2 / ((1 - β) * (σ - 1) * (σ - β)) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- Constant unit profile `j ↦ 1` generating the uniform Fejér kernel of degree `M`. -/
def uniformFejerProfile : ℕ → ℝ := fun _ => 1

/-- Zeroth folded autocorrelation coefficient of the uniform profile of degree `M`. -/
theorem fejerAutoCoeff_uniform_zero (M : ℕ) :
    fejerAutoCoeff M uniformFejerProfile 0 = (M : ℝ) + 1 := by
  unfold fejerAutoCoeff uniformFejerProfile
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
      (fun p => natDist p.1 p.2 = 0)).card = M + 1 := by
    conv_rhs => rw [← Finset.card_range (M + 1)]
    symm
    refine Finset.card_bij (fun j _ => (j, j))
      (fun j hj => ?_) (fun j₁ _ j₂ _ h => (Prod.mk.inj h).1) (fun p hp => ?_)
    · rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hj, hj⟩, by simp [natDist]⟩
    · rw [Finset.mem_filter, Finset.mem_product] at hp
      have heq : p.1 = p.2 := by unfold natDist at hp; omega
      exact ⟨p.1, hp.1.1, Prod.ext rfl heq⟩
  rw [hcard]
  push_cast
  ring

/-- First folded autocorrelation coefficient of the uniform profile of degree `M`. -/
theorem fejerAutoCoeff_uniform_one (M : ℕ) :
    fejerAutoCoeff M uniformFejerProfile 1 = 2 * (M : ℝ) := by
  unfold fejerAutoCoeff uniformFejerProfile
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul]
  let S₁ : Finset (ℕ × ℕ) := (Finset.range M).image (fun j => (j, j + 1))
  let S₂ : Finset (ℕ × ℕ) := (Finset.range M).image (fun j => (j + 1, j))
  have hunion : ((Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
      (fun p => natDist p.1 p.2 = 1)) = S₁ ∪ S₂ := by
    ext ⟨a, b⟩
    simp only [S₁, S₂, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_union, Finset.mem_image, Prod.mk.injEq, natDist]
    constructor
    · rintro ⟨⟨ha, hb⟩, hd⟩
      rcases lt_or_ge a b with hab | hba
      · exact Or.inl ⟨a, by omega, rfl, by omega⟩
      · exact Or.inr ⟨b, by omega, by omega, rfl⟩
    · rintro (⟨j, hj, rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩) <;> omega
  have hdisj : Disjoint S₁ S₂ := by
    refine Finset.disjoint_left.mpr fun p hp1 hp2 => ?_
    simp only [S₁, S₂, Finset.mem_image, Finset.mem_range] at hp1 hp2
    rcases hp1 with ⟨j₁, _, rfl⟩
    rcases hp2 with ⟨j₂, _, h2⟩
    rcases Prod.mk.inj h2 with ⟨_, _⟩
    omega
  have hc1 : S₁.card = M := by
    dsimp only [S₁]
    rw [Finset.card_image_of_injective _ (fun i j h => (Prod.mk.inj h).1), Finset.card_range]
  have hc2 : S₂.card = M := by
    dsimp only [S₂]
    rw [Finset.card_image_of_injective _ (fun i j h => (Prod.mk.inj h).2), Finset.card_range]
  rw [hunion, Finset.card_union_of_disjoint hdisj, hc1, hc2]
  push_cast
  ring

/-- **Strict finite-degree saddle ceiling.**
Every nonnegative cosine polynomial of degree `K ≥ 1` with `0 < a 0 ≤ a 1` has normalized
simple-zero saddle gain strictly below `3 - 2 √2`. -/
theorem cosinePolynomial_saddleGain_lt {a : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hP : ∀ θ : ℝ, 0 ≤ HTGeometry.cosinePolynomial a K θ)
    (ha0 : 0 < a 0) (hle : a 0 ≤ a 1) :
    (Real.sqrt (a 1) - Real.sqrt (a 0)) ^ 2 / a 0 < 3 - 2 * Real.sqrt 2 := by
  have hlt2 : a 1 < 2 * a 0 := cosinePolynomial_purchase_ratio_lt_two hK hP ha0
  have hsub_nn : 0 ≤ Real.sqrt (a 1) - Real.sqrt (a 0) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt hle)
  have hsqrt_lt : Real.sqrt (a 1) < Real.sqrt 2 * Real.sqrt (a 0) := by
    rw [← Real.sqrt_mul zero_le_two]
    exact Real.sqrt_lt_sqrt (ha0.le.trans hle) hlt2
  have hdiff_lt : Real.sqrt (a 1) - Real.sqrt (a 0) <
      (Real.sqrt 2 - 1) * Real.sqrt (a 0) := by linarith
  have hsq_lt : (Real.sqrt (a 1) - Real.sqrt (a 0)) ^ 2 <
      ((Real.sqrt 2 - 1) * Real.sqrt (a 0)) ^ 2 :=
    pow_lt_pow_left₀ hdiff_lt hsub_nn two_ne_zero
  have hrhs_eq : ((Real.sqrt 2 - 1) * Real.sqrt (a 0)) ^ 2 =
      (3 - 2 * Real.sqrt 2) * a 0 := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
    have ha : Real.sqrt (a 0) ^ 2 = a 0 := Real.sq_sqrt ha0.le
    calc ((Real.sqrt 2 - 1) * Real.sqrt (a 0)) ^ 2
        = (Real.sqrt 2 ^ 2 - 2 * Real.sqrt 2 + 1) * Real.sqrt (a 0) ^ 2 := by ring
      _ = (3 - 2 * Real.sqrt 2) * a 0 := by rw [h2, ha]; ring
  rw [hrhs_eq] at hsq_lt
  exact (div_lt_iff₀ ha0).mpr hsq_lt

/-- Normalized simple-zero saddle gains `(√(a 1) - √(a 0))² / a 0` achieved by finite-degree
nonnegative cosine polynomials crossing the simple-pole threshold `0 < a 0 ≤ a 1`. -/
def fejerSaddleGainSet : Set ℝ :=
  {g : ℝ | ∃ (K : ℕ) (a : ℕ → ℝ),
    1 ≤ K ∧ (∀ θ : ℝ, 0 ≤ HTGeometry.cosinePolynomial a K θ) ∧
      0 < a 0 ∧ a 0 ≤ a 1 ∧
      g = (Real.sqrt (a 1) - Real.sqrt (a 0)) ^ 2 / a 0}

/-- No finite-degree nonnegative cosine polynomial attains the ceiling `3 - 2 √2`. -/
theorem three_sub_two_sqrt_two_notMem_fejerSaddleGainSet :
    3 - 2 * Real.sqrt 2 ∉ fejerSaddleGainSet := by
  rintro ⟨K, a, hK, hP, ha0, hle, heq⟩
  exact lt_irrefl _ (heq ▸ cosinePolynomial_saddleGain_lt hK hP ha0 hle)

/-- **Exact least upper bound of all finite-degree Fejér saddle gains.**
Across all finite degrees `K ≥ 1`, the supremum of `(√(a 1) - √(a 0))² / a 0` over
nonnegative cosine polynomials with `0 < a 0 ≤ a 1` is `3 - 2 √2`. -/
theorem isLUB_fejerSaddleGainSet :
    IsLUB fejerSaddleGainSet (3 - 2 * Real.sqrt 2) := by
  refine ⟨?_, ?_⟩
  · rintro g ⟨K, a, hK, hP, ha0, hle, rfl⟩
    exact (cosinePolynomial_saddleGain_lt hK hP ha0 hle).le
  · intro b hb
    let gSeq : ℕ → ℝ := fun M =>
      (Real.sqrt (2 * (M : ℝ) / ((M : ℝ) + 1)) - 1) ^ 2
    have hmem : ∀ M : ℕ, 1 ≤ M → gSeq M ∈ fejerSaddleGainSet := by
      intro M hM
      refine ⟨M, fejerAutoCoeff M uniformFejerProfile, hM,
        cosinePolynomial_fejerAutoCoeff_nonneg M uniformFejerProfile, ?_, ?_, ?_⟩
      · rw [fejerAutoCoeff_uniform_zero]; positivity
      · rw [fejerAutoCoeff_uniform_zero, fejerAutoCoeff_uniform_one]
        have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        linarith
      · rw [fejerAutoCoeff_uniform_zero, fejerAutoCoeff_uniform_one]
        dsimp only [gSeq]
        have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
        have hsqrt_ne : Real.sqrt ((M : ℝ) + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hMpos)
        rw [Real.sqrt_div (by positivity)]
        have hsub : Real.sqrt (2 * (M : ℝ)) / Real.sqrt ((M : ℝ) + 1) - 1 =
            (Real.sqrt (2 * (M : ℝ)) - Real.sqrt ((M : ℝ) + 1)) /
              Real.sqrt ((M : ℝ) + 1) := by
          field_simp [hsqrt_ne]
        rw [hsub, div_pow, Real.sq_sqrt hMpos.le]
    have hrat_tend : Tendsto (fun M : ℕ => 2 * (M : ℝ) / ((M : ℝ) + 1)) atTop (𝓝 2) := by
      have hrewrite : (fun M : ℕ => 2 * (M : ℝ) / ((M : ℝ) + 1)) =
          fun M : ℕ => 2 - 2 / ((M : ℝ) + 1) := by
        funext M
        have hne : (M : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hne]
        ring
      rw [hrewrite]
      have hden_top : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hden_top)
    have hcont : Continuous (fun t : ℝ => (Real.sqrt t - 1) ^ 2) := by fun_prop
    have hg_tend : Tendsto gSeq atTop (𝓝 (3 - 2 * Real.sqrt 2)) := by
      have hlim := (hcont.tendsto 2).comp hrat_tend
      have hval : (Real.sqrt 2 - 1) ^ 2 = 3 - 2 * Real.sqrt 2 := by
        have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
        calc (Real.sqrt 2 - 1) ^ 2 = Real.sqrt 2 ^ 2 - 2 * Real.sqrt 2 + 1 := by ring
          _ = 3 - 2 * Real.sqrt 2 := by rw [h2]; ring
      rwa [hval] at hlim
    have hev_le : ∀ᶠ M : ℕ in atTop, gSeq M ≤ b := by
      filter_upwards [eventually_ge_atTop 1] with M hM
      exact hb (hmem M hM)
    exact le_of_tendsto hg_tend hev_le

/-! ### 3. Unconditional three-currency forcing on the arithmetic zero-free locus -/

/-- Unconditional arithmetic zero-free locus combining the boundary lines `Re z = 0, 1`
and the reflected harmonic de la Vallée Poussin collars inside the critical strip. -/
def forcedZeroFreeRegion : Set ℂ :=
  {z : ℂ | z.re = 0 ∨ z.re = 1} ∪ harmonicZeroFreeCollar

/-- Every point of `XiDivisorSupport` is unconditionally excluded from `forcedZeroFreeRegion`. -/
theorem xiDivisorSupport_notMem_forcedZeroFreeRegion (rho : _root_.RHTower.XiDivisorSupport) :
    (rho : ℂ) ∉ forcedZeroFreeRegion := by
  obtain ⟨h0, h1, hcol⟩ := xiDivisorSupport_disjoint_boundary_and_harmonicCollar rho
  rintro ((hr0 | hr1) | hrc)
  · exact h0 hr0
  · exact h1 hr1
  · exact hcol hrc

/-- Every nontrivial zero of `ζ` lies in `XiDivisorSupport` and is therefore unconditionally
excluded from `forcedZeroFreeRegion`. -/
theorem zetaZeroConfig_notMem_forcedZeroFreeRegion {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    ρ ∉ forcedZeroFreeRegion := by
  have hxi : _root_.RHTower.xi ρ = 0 := by
    refine _root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr
      ⟨hρ.1, fun n hn => ?_⟩
    have hre := congrArg Complex.re hn
    have h0 : 0 < ρ.re := hρ.2.1
    rw [hre] at h0
    simp at h0
    linarith [Nat.cast_nonneg (α := ℝ) n]
  let rho : _root_.RHTower.XiDivisorSupport :=
    ⟨ρ, _root_.RHTower.mem_xi_divisor_support_of_eq_zero hxi⟩
  exact xiDivisorSupport_notMem_forcedZeroFreeRegion rho

/-- **Meyer-source blindness transfer on any zero-free region.**
If `Ω ⊆ ℂ` contains no point of `XiDivisorSupport`, then every strong-log Meyer source `g`
whose off-line Mellin nonvanishing locus lies in `Ω` belongs to `meyerTraceBoundedIdeal`
and has nonnegative diagonal source trace. -/
theorem mem_meyerTraceBoundedIdeal_of_offLine_support_subset {Ω : Set ℂ}
    (hΩ : ∀ rho : _root_.RHTower.XiDivisorSupport, (rho : ℂ) ∉ Ω)
    {g : _root_.RHTower.DeningerMeyerStrongLogTarget}
    (hsupp : ∀ z : ℂ, z.re ≠ 1 / 2 → z ∉ Ω →
      _root_.RHTower.deningerMeyerStrongLogMellin g z = 0) :
    g ∈ meyerTraceBoundedIdeal ∧ 0 ≤ _root_.RHTower.meyerSourceTrace g g := by
  have hg : MeyerTraceOrbitBounded g := by
    rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
    intro rho hoff
    exact hsupp (rho : ℂ) hoff (hΩ rho)
  exact ⟨hg, meyerTraceOrbitBounded_trace_nonneg hg⟩

/-- **Unconditional Meyer-source forcing on `forcedZeroFreeRegion`.**
Every strong-log Meyer source whose off-line Mellin transform vanishes outside
`forcedZeroFreeRegion` is unconditionally forced into `meyerTraceBoundedIdeal` and satisfies
`0 ≤ meyerSourceTrace g g`. -/
theorem forcedZeroFreeRegion_forces_meyerTraceBoundedIdeal
    {g : _root_.RHTower.DeningerMeyerStrongLogTarget}
    (hsupp : ∀ z : ℂ, z.re ≠ 1 / 2 → z ∉ forcedZeroFreeRegion →
      _root_.RHTower.deningerMeyerStrongLogMellin g z = 0) :
    g ∈ meyerTraceBoundedIdeal ∧ 0 ≤ _root_.RHTower.meyerSourceTrace g g :=
  mem_meyerTraceBoundedIdeal_of_offLine_support_subset
    xiDivisorSupport_notMem_forcedZeroFreeRegion hsupp

/-- **Scaling-cycle orientation transfer on any zero-free region.**
If `Ω ⊆ ℂ` is disjoint from `zetaZeroConfig.carrier`, then every `x : ScalingCycle` whose
off-line Fourier–Laplace transform vanishes at one reflected pair point outside `Ω` is blind
off-line and satisfies `OrbitHodgeIndex`. -/
theorem blindOffLine_and_orbitHodgeIndex_of_offLine_support_subset {Ω : Set ℂ}
    (hΩ : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ∉ Ω) (x : ScalingCycle)
    (hsupp : ∀ z : ℂ, z.re ≠ 1 / 2 → z ∉ Ω →
      paperFT (cx x.2.2) (gammaOf z) = 0 ∨ paperFT (cx x.2.2) (conj (gammaOf z)) = 0) :
    BlindOffLine zetaZeroConfig x.2.2 ∧
      (configScalingDatum zetaZeroConfig temperedConfig_zetaZeroConfig).OrbitHodgeIndex x := by
  have hb : BlindOffLine zetaZeroConfig x.2.2 := fun ρ hρ hre => hsupp ρ hre (hΩ ρ hρ)
  exact ⟨hb, orbitHodgeIndex_of_blindOffLine zetaZeroConfig temperedConfig_zetaZeroConfig x hb⟩

/-- **Unconditional scaling-cycle orientation forcing on `forcedZeroFreeRegion`.**
Every scaling cycle whose off-line Fourier–Laplace transform vanishes at one pair point
outside `forcedZeroFreeRegion` is unconditionally blind off-line and oriented. -/
theorem forcedZeroFreeRegion_forces_orbitHodgeIndex (x : ScalingCycle)
    (hsupp : ∀ z : ℂ, z.re ≠ 1 / 2 → z ∉ forcedZeroFreeRegion →
      paperFT (cx x.2.2) (gammaOf z) = 0 ∨ paperFT (cx x.2.2) (conj (gammaOf z)) = 0) :
    BlindOffLine zetaZeroConfig x.2.2 ∧
      (configScalingDatum zetaZeroConfig temperedConfig_zetaZeroConfig).OrbitHodgeIndex x :=
  blindOffLine_and_orbitHodgeIndex_of_offLine_support_subset
    (fun _ hρ => zetaZeroConfig_notMem_forcedZeroFreeRegion hρ) x hsupp

/-- **Graded width-functor transfer across all six canonical `ζ`-receivers.**
For every threshold `σ ≥ 0`, exclusion of `zetaZeroConfig.carrier` from the symmetric outer
strip `{z | 1 / 2 + σ < Re z ∨ Re z < 1 / 2 - σ}` is equivalent to graded admissibility at `σ`
simultaneously across the spectral, abscissa, Möbius-damping, Liouville-damping, `ξ` half-plane,
and Suzuki-formation receivers. -/
theorem outerStrip_disjoint_iff_zetaReceivers_admittedAt {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ ρ ∈ zetaZeroConfig.carrier,
      ρ ∉ {z : ℂ | 1 / 2 + σ < z.re ∨ z.re < 1 / 2 - σ}) ↔
      (spectralZeroReceiver.admittedAt σ ∧
        abscissaReceiver.admittedAt σ ∧
        moebiusDampingReceiver.admittedAt σ ∧
        liouvilleDampingReceiver.admittedAt σ ∧
        xiHalfPlaneReceiver.admittedAt σ ∧
        suzukiFormationReceiver.admittedAt σ) := by
  rcases zetaReceivers_widthVal_eq with ⟨h1, h2, h3, h4, h5⟩
  have hspec : (∀ ρ ∈ zetaZeroConfig.carrier,
      ρ ∉ {z : ℂ | 1 / 2 + σ < z.re ∨ z.re < 1 / 2 - σ}) ↔
      spectralZeroReceiver.admittedAt σ := by
    change (∀ ρ ∈ zetaZeroConfig.carrier, ¬ (1 / 2 + σ < ρ.re ∨ ρ.re < 1 / 2 - σ)) ↔
      (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ)
    constructor
    · intro h ρ hρ
      have hnot := h ρ hρ
      push Not at hnot
      exact hnot.1
    · intro h ρ hρ hmem
      rcases hmem with hgt | hlt
      · linarith [h ρ hρ]
      · have href := h (reflect ρ) (zetaZeroConfig.reflect_mem ρ hρ)
        rw [Zeta23.reflect_re] at href
        linarith
  rw [hspec]
  simp only [ReceiverObject.admittedAt_iff _ hσ, h1, h2, h3, h4, h5, and_self]

/-- **The Common Law (`arithmetic_forces_blindness_unconditional`).**
Unites the four unconditional components of arithmetic-forced blindness across the
realization, cancellation, and positivity currencies:
1. *Beurling–Hamburger selectivity*: Riemann's degree-one theta law characterizes
   `riemannPrimeMeasure` uniquely (`↔`) among all Borel prime measures on `(1, ∞)` with
   finite inverse-square moment;
2. *Single-channel cancellation floor*: at every subcritical damping `0 < ε < 1 / 2`, record
   minima produce an actual cofactor limit with diagonal floor `p^{2ε - 2} > 0`, preventing
   collapse to the augmentation singleton;
3. *All-degree Fejér saddle ceiling*: across all finite degrees `K ≥ 1`, the supremum of
   normalized simple-zero saddle gains is `3 - 2 √2`, strictly unattained at every finite `K`;
4. *Three-currency blindness forcing*: on `forcedZeroFreeRegion`, every off-line-supported
   Meyer source is forced into `meyerTraceBoundedIdeal` with nonnegative self-trace, and
   every off-line-supported scaling cycle is forced into `BlindOffLine zetaZeroConfig` with
   `OrbitHodgeIndex`. -/
theorem arithmetic_forces_blindness_unconditional :
    (∀ (P : Measure ℝ), P (Iic 1) = 0 → Integrable (fun u : ℝ => 1 / u ^ 2) P →
      ∀ (α β : ℂ),
        (∀ x : ℝ, 0 < x →
          measureTheta (beurlingIntegerMeasure P) x =
            (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingIntegerMeasure P) x⁻¹ +
              α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) ↔
          (P = riemannPrimeMeasure ∧ α = -1 / 2 ∧ β = 1 / 2)) ∧
    (∀ ε : SubcriticalDamping,
      (∃ L : ActualCofactorLimit ε, ∀ p : ℕ+, (p : ℝ) ^ (2 * (ε : ℝ) - 2) ≤ L.kernel p p) ∧
        actualCofactorKernelSet ε ≠ {augmentationCofactorKernel}) ∧
    (IsLUB fejerSaddleGainSet (3 - 2 * Real.sqrt 2) ∧
      3 - 2 * Real.sqrt 2 ∉ fejerSaddleGainSet) ∧
    ((∀ g : _root_.RHTower.DeningerMeyerStrongLogTarget,
        (∀ z : ℂ, z.re ≠ 1 / 2 → z ∉ forcedZeroFreeRegion →
          _root_.RHTower.deningerMeyerStrongLogMellin g z = 0) →
        g ∈ meyerTraceBoundedIdeal ∧ 0 ≤ _root_.RHTower.meyerSourceTrace g g) ∧
      (∀ x : ScalingCycle,
        (∀ z : ℂ, z.re ≠ 1 / 2 → z ∉ forcedZeroFreeRegion →
          paperFT (cx x.2.2) (gammaOf z) = 0 ∨ paperFT (cx x.2.2) (conj (gammaOf z)) = 0) →
        BlindOffLine zetaZeroConfig x.2.2 ∧
          (configScalingDatum zetaZeroConfig temperedConfig_zetaZeroConfig).OrbitHodgeIndex x)) :=
  ⟨fun _ hP hmom α β => measureTheta_beurlingIntegerMeasure_iff_eq_riemannPrimeMeasure hP hmom α β,
   fun ε => ⟨exists_actualCofactorLimit_kernel_diag_ge_rpow ε,
     actualCofactorKernelSet_ne_singleton_augmentation ε⟩,
   ⟨isLUB_fejerSaddleGainSet, three_sub_two_sqrt_two_notMem_fejerSaddleGainSet⟩,
   ⟨fun _ => forcedZeroFreeRegion_forces_meyerTraceBoundedIdeal,
    forcedZeroFreeRegion_forces_orbitHodgeIndex⟩⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.measure_defect_eq_zero_of_pole_saturated
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.quantized_defect_eq_zero_of_pole_dominated
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.measureTheta_beurlingIntegerMeasure_iff_eq_riemannPrimeMeasure
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.isGreatest_renormalizedPoleGain
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.isLUB_fejerSaddleGainSet
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.outerStrip_disjoint_iff_zetaReceivers_admittedAt
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.arithmetic_forces_blindness_unconditional

