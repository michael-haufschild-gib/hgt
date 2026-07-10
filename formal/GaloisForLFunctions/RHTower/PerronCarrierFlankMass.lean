import GaloisForLFunctions.RHTower.PerronBoundaryCharge

/-!
# Coefficient-independent Perron flank mass

The quantitative part of Perron boundary charge is carried entirely by the left vertical edge.
This module separates it from the qualitative escape of the other three edges.  The carrier-only
weight

`A_M(F) = integral |F(-M+it)| / (1+t^2) dt`

contains no coefficient index and no Perron knot width.  Quadratic decay of the regularized Perron
kernel converts this mass into the normalized boundary charge.  A second interface shows that
vertical `L²` energy supplies the weighted `L¹` mass by Hölder, preserving geometric growth radius.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set
open scoped Topology Interval

/-- **Uniform left-flank Perron bound.**  At depth `M ≥ 2`, every variable-width regularization is
bounded by the coefficient-independent height weight `(1+y²)⁻¹`, with all arithmetic dependence
isolated in `4 * (n-δ)^(1-M)`. -/
theorem perronEAt_left_flank_norm_le
    {n M : ℕ} {δ y : ℝ}
    (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    ‖perronEAt n δ (↑(-(M : ℝ)) + ↑y * I)‖ ≤
      4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) / (1 + y ^ 2) := by
  let s : ℂ := ↑(-(M : ℝ)) + ↑y * I
  let D : ℝ := perronSupportScaleAt n δ
  have hD : D = (n : ℝ) - δ := rfl
  have hDpos : 0 < D := by rw [hD]; linarith
  have hMreal : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hexp : 1 - (M : ℝ) ≤ 0 := by linarith
  have hsre : s.re + 1 = 1 - (M : ℝ) := by simp [s]; ring
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [s] at hre
    linarith
  have hs1 : s ≠ -1 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [s] at hre
    linarith
  have hbasePlus : D ≤ (n : ℝ) + δ := by rw [hD]; linarith
  have hbaseN : D ≤ (n : ℝ) := by rw [hD]; linarith
  have hplus : ((n : ℝ) + δ) ^ (1 - (M : ℝ)) ≤ D ^ (1 - (M : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hDpos hbasePlus hexp
  have hnterm : ((n : ℝ)) ^ (1 - (M : ℝ)) ≤ D ^ (1 - (M : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hDpos hbaseN hexp
  have hkink : ‖perronKinkAt n δ s‖ ≤ 4 * D ^ (1 - (M : ℝ)) := by
    calc
      ‖perronKinkAt n δ s‖ ≤
          ((n : ℝ) + δ) ^ (s.re + 1) + ((n : ℝ) - δ) ^ (s.re + 1) +
            2 * (n : ℝ) ^ (s.re + 1) := perronKinkAt_norm_le hn hδ0 hδn s
      _ = ((n : ℝ) + δ) ^ (1 - (M : ℝ)) + D ^ (1 - (M : ℝ)) +
            2 * (n : ℝ) ^ (1 - (M : ℝ)) := by rw [hsre, hD]
      _ ≤ D ^ (1 - (M : ℝ)) + D ^ (1 - (M : ℝ)) +
            2 * D ^ (1 - (M : ℝ)) := by gcongr
      _ = 4 * D ^ (1 - (M : ℝ)) := by ring
  have hsNorm : Real.sqrt (1 + y ^ 2) ≤ ‖s‖ := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _), Real.sq_sqrt (by positivity),
      Complex.sq_norm]
    simp [Complex.normSq_apply, s]
    nlinarith
  have hs1Norm : Real.sqrt (1 + y ^ 2) ≤ ‖s + 1‖ := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _), Real.sq_sqrt (by positivity),
      Complex.sq_norm]
    simp [Complex.normSq_apply, s]
    nlinarith
  have hden : 1 + y ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul]
    calc
      1 + y ^ 2 = Real.sqrt (1 + y ^ 2) * Real.sqrt (1 + y ^ 2) := by
        rw [Real.mul_self_sqrt (by positivity)]
      _ ≤ ‖s‖ * ‖s + 1‖ := mul_le_mul hsNorm hs1Norm (Real.sqrt_nonneg _) (norm_nonneg _)
  have hdenpos : 0 < 1 + y ^ 2 := by positivity
  rw [perronEAt_eq n δ hs0 hs1, norm_div]
  simpa [D] using (div_le_div₀ (by positivity) hkink hdenpos hden)

/-- Qualitative escape of the three contour edges which do not carry the flank-growth bound. -/
def HasPerronBoundaryEscapeAt (F : ℂ → ℂ) (c : ℝ) (n : ℕ) (δ : ℝ)
    (M : ℕ) : Prop :=
  ∃ T : ℕ → ℝ,
    Tendsto T atTop atTop ∧
    (∀ k, 0 ≤ T k) ∧
    Tendsto (fun k => ∫ y in (-(T k))..(T k),
      perronContourIntegrand F n δ (↑c + ↑y * I)) atTop
      (𝓝 (∫ y : ℝ, perronContourIntegrand F n δ (↑c + ↑y * I))) ∧
    Tendsto (fun k => ∫ x in (-(M : ℝ))..c,
      perronContourIntegrand F n δ (↑x + ↑(T k) * I)) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ x in (-(M : ℝ))..c,
      perronContourIntegrand F n δ (↑x + ↑(-(T k)) * I)) atTop (𝓝 0)

/-- The coefficient-independent weighted mass density of the carrier on the left line `Re s=-M`. -/
def perronCarrierFlankWeight (F : ℂ → ℂ) (M : ℕ) (y : ℝ) : ℝ :=
  ‖F (↑(-(M : ℝ)) + ↑y * I)‖ / (1 + y ^ 2)

/-- The carrier's full weighted left-line mass exists and is at most `A`. -/
def HasPerronCarrierFlankMassAt (F : ℂ → ℂ) (M : ℕ) (A : ℝ) : Prop :=
  Integrable (perronCarrierFlankWeight F M) ∧
  (∫ y : ℝ, perronCarrierFlankWeight F M y) ≤ A

/-- Carrier flank mass supplies the quantitative left charge once the other three edges escape. -/
theorem hasPerronBoundaryChargeAt_of_escape_of_carrierFlankMassAt
    {F : ℂ → ℂ} {c δ A : ℝ} {n M : ℕ}
    (hF : Differentiable ℂ F) (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hδ0 : 0 < δ) (hδn : δ < (n : ℝ))
    (hescape : HasPerronBoundaryEscapeAt F c n δ M)
    (hmass : HasPerronCarrierFlankMassAt F M A) :
    HasPerronBoundaryChargeAt F c n δ M
      (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) * A) := by
  rcases hescape with ⟨T, hTtop, hTnonneg, hright, htop, hbot⟩
  refine ⟨T, hTtop, hright, htop, hbot, ?_⟩
  intro k
  let C : ℝ := 4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ))
  have hDpos : 0 < perronSupportScaleAt n δ := by
    rw [perronSupportScaleAt]
    linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hDpos.le _)
  have hpoint : ∀ y : ℝ,
      ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖ ≤
        C * perronCarrierFlankWeight F M y := by
    intro y
    rw [perronContourIntegrand, norm_mul]
    have hE := perronEAt_left_flank_norm_le hn hM hδ0 hδn (y := y)
    calc
      ‖F (↑(-(M : ℝ)) + ↑y * I)‖ *
          ‖perronEAt n δ (↑(-(M : ℝ)) + ↑y * I)‖ ≤
          ‖F (↑(-(M : ℝ)) + ↑y * I)‖ *
            (C / (1 + y ^ 2)) := mul_le_mul_of_nonneg_left hE (norm_nonneg _)
      _ = C * perronCarrierFlankWeight F M y := by
        unfold perronCarrierFlankWeight
        ring
  have hGmeas : AEStronglyMeasurable (fun y : ℝ =>
      ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖) :=
    (((hF.mul (perronEAt_differentiable hn hδ0 hδn)).continuous.comp
      (by fun_prop)).norm).aestronglyMeasurable
  have hCint : Integrable (fun y : ℝ => C * perronCarrierFlankWeight F M y) :=
    hmass.1.const_mul C
  have hGint : Integrable (fun y : ℝ =>
      ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖) :=
    hCint.mono' hGmeas (Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hpoint y)
  calc
    ‖∫ y in (-(T k))..(T k),
        perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖
        ≤ ∫ y in (-(T k))..(T k),
            ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith [hTnonneg k])
    _ = ∫ y in Ioc (-(T k)) (T k),
            ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖ :=
          intervalIntegral.integral_of_le (by linarith [hTnonneg k])
    _ ≤ ∫ y : ℝ,
            ‖perronContourIntegrand F n δ (↑(-(M : ℝ)) + ↑y * I)‖ :=
          setIntegral_le_integral hGint (Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ∫ y : ℝ, C * perronCarrierFlankWeight F M y :=
          integral_mono hGint hCint hpoint
    _ = C * ∫ y : ℝ, perronCarrierFlankWeight F M y :=
          integral_const_mul C _
    _ ≤ C * A := mul_le_mul_of_nonneg_left hmass.2 hC
    _ = 4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) * A := rfl

/-- Qualitative boundary escape for every admissible knot width and eventually every depth. -/
def HasVariablePerronBoundaryEscape (F : ℂ → ℂ) (c : ℝ) (n : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → δ < (n : ℝ) →
    ∀ᶠ M : ℕ in atTop, HasPerronBoundaryEscapeAt F c n δ M

/-- The carrier-only flank mass is eventually bounded by `(π/2)H(M)`.  This normalization makes
the induced Perron boundary charge exactly `2π H(M)(n-δ)^(1-M)`. -/
def HasPerronCarrierFlankMass (F : ℂ → ℂ) (H : ℕ → ℝ) : Prop :=
  ∀ᶠ M : ℕ in atTop,
    HasPerronCarrierFlankMassAt F M ((Real.pi / 2) * H M)

/-- Carrier mass plus qualitative escape discharges the kernel-dependent boundary-charge Prop. -/
theorem HasPerronCarrierFlankMass.hasVariablePerronBoundaryCharge
    {F : ℂ → ℂ} {c : ℝ} {H : ℕ → ℝ} {n : ℕ}
    (hmass : HasPerronCarrierFlankMass F H)
    (hescape : HasVariablePerronBoundaryEscape F c n)
    (hF : Differentiable ℂ F) (hn : 1 ≤ n) :
    HasVariablePerronBoundaryCharge F c H n := by
  intro δ hδ0 hδ1 hδn
  filter_upwards [hmass, hescape δ hδ0 hδ1 hδn,
    (eventually_ge_atTop (2 : ℕ))] with M hmassM hescapeM hM
  have hcharge := hasPerronBoundaryChargeAt_of_escape_of_carrierFlankMassAt hF hn hM hδ0 hδn
    hescapeM hmassM
  rw [show 2 * Real.pi * H M * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) =
      4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) *
        ((Real.pi / 2) * H M) by ring]
  exact hcharge

/-- Carrier mass plus escape directly supplies the exact variable-knot coefficient estimate. -/
theorem HasPerronCarrierFlankMass.hasVariableQuietFlankCoefficientBound
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ}
    (hmass : HasPerronCarrierFlankMass F H)
    (hescape : HasVariablePerronBoundaryEscape F c n)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s) (hn : 1 ≤ n) :
    HasVariableQuietFlankCoefficientBound a H n := by
  exact (HasPerronCarrierFlankMass.hasVariablePerronBoundaryCharge hmass hescape hF hn).hasVariableQuietFlankCoefficientBound
    hc0 hsum hF hFeq hn

/-- **Carrier-flank exact support theorem.**  A geometric carrier-mass radius bounds every nonzero
Dirichlet coefficient index exactly. -/
theorem coefficient_index_le_exact_flank_radius_of_carrierFlankMass
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (hmass : HasPerronCarrierFlankMass F H)
    (hescape : HasVariablePerronBoundaryEscape F c n)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M)
    (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M)
    (han : a n ≠ 0) :
    (n : ℝ) ≤ R := by
  exact coefficient_index_le_exact_flank_radius_of_boundaryCharge
    (HasPerronCarrierFlankMass.hasVariablePerronBoundaryCharge hmass hescape hF hn)
    hc0 hsum hF hFeq hn hR hH0 hH han

/-- Square-integrable vertical carrier trace with `L²` norm at most `B`. -/
def HasPerronCarrierFlankL2EnergyAt (F : ℂ → ℂ) (M : ℕ) (B : ℝ) : Prop :=
  Integrable (fun y : ℝ => ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ^ 2) ∧
  Real.sqrt (∫ y : ℝ, ‖F (↑(-(M : ℝ)) + ↑y * I)‖ ^ 2) ≤ B

/-- Vertical `L²` energy gives weighted `L¹` flank mass with loss exactly `sqrt π`. -/
theorem HasPerronCarrierFlankL2EnergyAt.hasPerronCarrierFlankMassAt
    {F : ℂ → ℂ} {M : ℕ} {B : ℝ}
    (hF : Differentiable ℂ F)
    (henergy : HasPerronCarrierFlankL2EnergyAt F M B) :
    HasPerronCarrierFlankMassAt F M (B * Real.sqrt Real.pi) := by
  let f : ℝ → ℝ := fun y => ‖F (↑(-(M : ℝ)) + ↑y * I)‖
  let w : ℝ → ℝ := fun y => (1 + y ^ 2)⁻¹
  have hfmeas : AEStronglyMeasurable f := by
    exact ((hF.continuous.comp (by fun_prop)).norm).aestronglyMeasurable
  have hwcont : Continuous w := by
    dsimp [w]
    refine (continuous_const.add (continuous_id.pow 2)).inv₀ ?_
    intro y
    change 1 + y ^ 2 ≠ 0
    nlinarith [sq_nonneg y]
  have hwmeas : AEStronglyMeasurable w := hwcont.aestronglyMeasurable
  have hwpos : ∀ y : ℝ, 0 < w y := by
    intro y
    dsimp [w]
    positivity
  have hwle : ∀ y : ℝ, w y ≤ 1 := by
    intro y
    dsimp [w]
    exact (inv_le_one₀ (by nlinarith [sq_nonneg y] : 0 < 1 + y ^ 2)).2
      (by nlinarith [sq_nonneg y])
  have hwsqle : ∀ y : ℝ, w y ^ 2 ≤ w y := by
    intro y
    nlinarith [hwpos y, hwle y]
  have hwInt : Integrable w := by
    simpa only [w] using integrable_inv_one_add_sq
  have hwsqInt : Integrable (fun y : ℝ => w y ^ 2) :=
    hwInt.mono' (hwmeas.aemeasurable.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (w y))]
      exact hwsqle y)
  have hfLp : MemLp f 2 :=
    (memLp_two_iff_integrable_sq hfmeas).2 (by simpa only [f] using henergy.1)
  have hwLp : MemLp w 2 := (memLp_two_iff_integrable_sq hwmeas).2 hwsqInt
  have hmassInt : Integrable (perronCarrierFlankWeight F M) := by
    have hprod : Integrable (f * w) := hfLp.integrable_mul hwLp
    simpa only [perronCarrierFlankWeight, f, w, Pi.mul_apply, div_eq_mul_inv] using hprod
  refine ⟨hmassInt, ?_⟩
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := f) (g := w) Real.HolderConjugate.two_two
    (Eventually.of_forall fun y => norm_nonneg _)
    (Eventually.of_forall fun y => (hwpos y).le)
    (by simpa using hfLp) (by simpa using hwLp)
  have hholder' :
      (∫ y : ℝ, perronCarrierFlankWeight F M y) ≤
        Real.sqrt (∫ y : ℝ, f y ^ 2) * Real.sqrt (∫ y : ℝ, w y ^ 2) := by
    simpa only [perronCarrierFlankWeight, f, w, div_eq_mul_inv,
      Real.sqrt_eq_rpow, Real.rpow_two] using hholder
  have hwSqBound : (∫ y : ℝ, w y ^ 2) ≤ Real.pi := by
    calc
      (∫ y : ℝ, w y ^ 2) ≤ ∫ y : ℝ, w y :=
        integral_mono hwsqInt hwInt hwsqle
      _ = Real.pi := by simpa only [w] using integral_univ_inv_one_add_sq
  have hsqrtw : Real.sqrt (∫ y : ℝ, w y ^ 2) ≤ Real.sqrt Real.pi :=
    Real.sqrt_le_sqrt hwSqBound
  calc
    (∫ y : ℝ, perronCarrierFlankWeight F M y) ≤
        Real.sqrt (∫ y : ℝ, f y ^ 2) * Real.sqrt (∫ y : ℝ, w y ^ 2) := hholder'
    _ ≤ B * Real.sqrt Real.pi := by
      apply mul_le_mul
      · simpa only [f] using henergy.2
      · exact hsqrtw
      · exact Real.sqrt_nonneg _
      · exact le_trans (Real.sqrt_nonneg _) henergy.2

/-- **Pointwise Perron charge from vertical `L²` energy.**  The weighted flank-mass Prop is
constructed internally by Cauchy--Schwarz, leaving only the concrete energy and boundary-escape
data. -/
theorem hasPerronBoundaryChargeAt_of_escape_of_carrierFlankL2EnergyAt
    {F : ℂ → ℂ} {c δ B : ℝ} {n M : ℕ}
    (hF : Differentiable ℂ F) (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hδ0 : 0 < δ) (hδn : δ < (n : ℝ))
    (hescape : HasPerronBoundaryEscapeAt F c n δ M)
    (henergy : HasPerronCarrierFlankL2EnergyAt F M B) :
    HasPerronBoundaryChargeAt F c n δ M
      (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) * (B * Real.sqrt Real.pi)) :=
  hasPerronBoundaryChargeAt_of_escape_of_carrierFlankMassAt hF hn hM hδ0 hδn hescape
    (HasPerronCarrierFlankL2EnergyAt.hasPerronCarrierFlankMassAt hF henergy)

/-- **Right-edge Perron bound from vertical `L²` energy.**  Both the intermediate flank-mass and
boundary-charge interfaces are discharged. -/
theorem perron_right_integral_norm_le_of_escape_of_carrierFlankL2EnergyAt
    {F : ℂ → ℂ} {c δ B : ℝ} {n M : ℕ}
    (hF : Differentiable ℂ F) (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hδ0 : 0 < δ) (hδn : δ < (n : ℝ))
    (hescape : HasPerronBoundaryEscapeAt F c n δ M)
    (henergy : HasPerronCarrierFlankL2EnergyAt F M B) :
    ‖∫ y : ℝ, perronContourIntegrand F n δ (↑c + ↑y * I)‖ ≤
      4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) * (B * Real.sqrt Real.pi) :=
  perron_right_integral_norm_le_of_boundaryChargeAt hF
    (perronEAt_differentiable hn hδ0 hδn)
    (hasPerronBoundaryChargeAt_of_escape_of_carrierFlankL2EnergyAt
      hF hn hM hδ0 hδn hescape henergy)

/-- Normalization transporting an `L²` majorant into the project's flank majorant. -/
def perronFlankL2Constant : ℝ := 2 * Real.sqrt Real.pi / Real.pi

/-- The `L²`-to-flank normalization is strictly positive. -/
theorem perronFlankL2Constant_pos : 0 < perronFlankL2Constant := by
  unfold perronFlankL2Constant
  positivity

/-- Eventual vertical `L²` energy majorant on the negative-integer flank. -/
def HasPerronCarrierFlankL2Energy (F : ℂ → ℂ) (B : ℕ → ℝ) : Prop :=
  ∀ᶠ M : ℕ in atTop, HasPerronCarrierFlankL2EnergyAt F M (B M)

/-- The Hilbert flank-energy interface produces coefficient-independent Perron carrier mass. -/
theorem HasPerronCarrierFlankL2Energy.hasPerronCarrierFlankMass
    {F : ℂ → ℂ} {B : ℕ → ℝ}
    (hF : Differentiable ℂ F)
    (henergy : HasPerronCarrierFlankL2Energy F B) :
    HasPerronCarrierFlankMass F (fun M => perronFlankL2Constant * B M) := by
  filter_upwards [henergy] with M hM
  have hmass := HasPerronCarrierFlankL2EnergyAt.hasPerronCarrierFlankMassAt hF hM
  rw [show (Real.pi / 2) * (perronFlankL2Constant * B M) =
      B M * Real.sqrt Real.pi by
    unfold perronFlankL2Constant
    field_simp [Real.pi_ne_zero]
  ]
  exact hmass

/-- **Hilbert-source exact support theorem.**  Geometric vertical `L²` energy and qualitative
boundary escape force every nonzero coefficient index below the same geometric radius. -/
theorem coefficient_index_le_exact_flank_radius_of_carrierFlankL2Energy
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {B : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (henergy : HasPerronCarrierFlankL2Energy F B)
    (hescape : HasVariablePerronBoundaryEscape F c n)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hB0 : ∀ᶠ M : ℕ in atTop, 0 ≤ B M)
    (hB : ∀ᶠ M : ℕ in atTop, B M ≤ C * R ^ M)
    (han : a n ≠ 0) :
    (n : ℝ) ≤ R := by
  have hκ0 : 0 ≤ perronFlankL2Constant := perronFlankL2Constant_pos.le
  have hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ perronFlankL2Constant * B M := by
    filter_upwards [hB0] with M hBM
    exact mul_nonneg hκ0 hBM
  have hH : ∀ᶠ M : ℕ in atTop,
      perronFlankL2Constant * B M ≤
        (perronFlankL2Constant * C) * R ^ M := by
    filter_upwards [hB] with M hBM
    calc
      perronFlankL2Constant * B M ≤
          perronFlankL2Constant * (C * R ^ M) :=
        mul_le_mul_of_nonneg_left hBM hκ0
      _ = (perronFlankL2Constant * C) * R ^ M := by ring
  exact coefficient_index_le_exact_flank_radius_of_carrierFlankMass
    (HasPerronCarrierFlankL2Energy.hasPerronCarrierFlankMass hF henergy) hescape
    hc0 hsum hF hFeq hn hR hH0 hH han

/-- On the absolutely convergent Dirichlet-series line, the complete variable Perron contour
integrand is automatically integrable.  Thus right-edge convergence is not an independent escape
hypothesis. -/
theorem perronContourIntegrand_right_integrable
    {F : ℂ → ℂ} {a : ℕ → ℂ} {c δ : ℝ} {n : ℕ}
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    Integrable (fun t : ℝ => perronContourIntegrand F n δ (↑c + ↑t * I)) := by
  obtain ⟨B, hB⟩ := lseries_bounded_on_halfplane hsum
  let K : ℝ := ((n : ℝ) + δ) ^ (c + 1) + ((n : ℝ) - δ) ^ (c + 1) +
    2 * (n : ℝ) ^ (c + 1)
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxp : 0 < (n : ℝ) + δ := by linarith
  have hxm : 0 < (n : ℝ) - δ := by linarith
  have hxn : 0 < (n : ℝ) := by linarith
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB ↑c (by rw [Complex.ofReal_re]))
  have hKernelInt : Integrable (fun t : ℝ => mellin perronKernelG (↑c + ↑t * I)) :=
    perronKernel_verticalIntegrable hc0
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      perronContourIntegrand F n δ (↑c + ↑t * I)) :=
    ((hF.mul (perronEAt_differentiable hn hδ0 hδn)).continuous.comp
      (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ t : ℝ,
      ‖perronContourIntegrand F n δ (↑c + ↑t * I)‖ ≤
        (B * K) * ‖mellin perronKernelG (↑c + ↑t * I)‖ := by
    intro t
    let s : ℂ := ↑c + ↑t * I
    have hsre : s.re = c := by simp [s]
    have hspos : 0 < s.re := by rw [hsre]; exact hc0
    have hs0 : s ≠ 0 := by
      intro hs
      have hre := congrArg Complex.re hs
      simp [s] at hre
      linarith
    have hs1 : s ≠ -1 := by
      intro hs
      have hre := congrArg Complex.re hs
      simp [s] at hre
      linarith
    have hFbound : ‖F s‖ ≤ B := by
      rw [hFeq s (by rw [hsre])]
      exact hB s (by rw [hsre])
    have hkink : ‖perronKinkAt n δ s‖ ≤ K := by
      simpa only [K, hsre] using perronKinkAt_norm_le hn hδ0 hδn s
    have hEbound : ‖perronEAt n δ s‖ ≤ K * ‖mellin perronKernelG s‖ := by
      rw [perronEAt_eq n δ hs0 hs1, norm_div, div_eq_mul_inv,
        perronKernel_mellin hspos, one_div, norm_inv]
      exact mul_le_mul_of_nonneg_right hkink (inv_nonneg.mpr (norm_nonneg _))
    rw [perronContourIntegrand, norm_mul]
    calc
      ‖F s‖ * ‖perronEAt n δ s‖ ≤ B * (K * ‖mellin perronKernelG s‖) :=
        mul_le_mul hFbound hEbound (norm_nonneg _) hB0
      _ = (B * K) * ‖mellin perronKernelG s‖ := by ring
  exact (hKernelInt.norm.const_mul (B * K)).mono' hmeas
    (Eventually.of_forall hbound)

/-- Horizontal escape without separately assuming right-edge convergence. -/
def HasPerronHorizontalEscapeAt (F : ℂ → ℂ) (c : ℝ) (n : ℕ) (δ : ℝ)
    (M : ℕ) : Prop :=
  ∃ T : ℕ → ℝ,
    Tendsto T atTop atTop ∧
    (∀ k, 0 ≤ T k) ∧
    Tendsto (fun k => ∫ x in (-(M : ℝ))..c,
      perronContourIntegrand F n δ (↑x + ↑(T k) * I)) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ x in (-(M : ℝ))..c,
      perronContourIntegrand F n δ (↑x + ↑(-(T k)) * I)) atTop (𝓝 0)

/-- Absolute Dirichlet convergence upgrades horizontal escape to full qualitative boundary escape. -/
theorem hasPerronBoundaryEscapeAt_of_horizontalEscape
    {F : ℂ → ℂ} {a : ℕ → ℂ} {c δ : ℝ} {n M : ℕ}
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ))
    (hhor : HasPerronHorizontalEscapeAt F c n δ M) :
    HasPerronBoundaryEscapeAt F c n δ M := by
  rcases hhor with ⟨T, hTtop, hTnonneg, htop, hbot⟩
  refine ⟨T, hTtop, hTnonneg, ?_, htop, hbot⟩
  exact intervalIntegral_tendsto_integral
    (perronContourIntegrand_right_integrable hc0 hsum hF hFeq hn hδ0 hδn)
    (tendsto_neg_atBot_iff.mpr hTtop) hTtop

/-- Eventual horizontal escape for every admissible variable Perron knot width. -/
def HasVariablePerronHorizontalEscape (F : ℂ → ℂ) (c : ℝ) (n : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → δ < (n : ℝ) →
    ∀ᶠ M : ℕ in atTop, HasPerronHorizontalEscapeAt F c n δ M

/-- The Dirichlet-series identity discharges the right-edge part of variable boundary escape. -/
theorem HasVariablePerronHorizontalEscape.hasVariablePerronBoundaryEscape
    {F : ℂ → ℂ} {a : ℕ → ℂ} {c : ℝ} {n : ℕ}
    (hhor : HasVariablePerronHorizontalEscape F c n)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s) (hn : 1 ≤ n) :
    HasVariablePerronBoundaryEscape F c n := by
  intro δ hδ0 hδ1 hδn
  filter_upwards [hhor δ hδ0 hδ1 hδn] with M hM
  exact hasPerronBoundaryEscapeAt_of_horizontalEscape hc0 hsum hF hFeq hn hδ0 hδn hM

/-- Carrier flank mass and horizontal escape are sufficient for normalized boundary charge; right
convergence is automatic on the Dirichlet half-plane. -/
theorem HasPerronCarrierFlankMass.hasVariablePerronBoundaryCharge_of_horizontalEscape
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ}
    (hmass : HasPerronCarrierFlankMass F H)
    (hhor : HasVariablePerronHorizontalEscape F c n)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s) (hn : 1 ≤ n) :
    HasVariablePerronBoundaryCharge F c H n := by
  exact hmass.hasVariablePerronBoundaryCharge
    (hhor.hasVariablePerronBoundaryEscape hc0 hsum hF hFeq hn) hF hn

/-- The coefficient-estimate Prop follows from carrier mass and horizontal escape alone. -/
theorem HasPerronCarrierFlankMass.hasVariableQuietFlankCoefficientBound_of_horizontalEscape
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ}
    (hmass : HasPerronCarrierFlankMass F H)
    (hhor : HasVariablePerronHorizontalEscape F c n)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s) (hn : 1 ≤ n) :
    HasVariableQuietFlankCoefficientBound a H n := by
  exact (hmass.hasVariablePerronBoundaryCharge_of_horizontalEscape
    hhor hc0 hsum hF hFeq hn).hasVariableQuietFlankCoefficientBound
      hc0 hsum hF hFeq hn

/-- **Carrier-mass/horizontal-escape support theorem.**  The quantitative source datum is now
coefficient-independent and the only remaining contour datum is qualitative horizontal escape. -/
theorem coefficient_index_le_exact_flank_radius_of_carrierFlankMass_horizontalEscape
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (hmass : HasPerronCarrierFlankMass F H)
    (hhor : HasVariablePerronHorizontalEscape F c n)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M)
    (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M)
    (han : a n ≠ 0) :
    (n : ℝ) ≤ R := by
  exact coefficient_index_le_exact_flank_radius_of_carrierFlankMass hmass
    (hhor.hasVariablePerronBoundaryEscape hc0 hsum hF hFeq hn)
    hc0 hsum hF hFeq hn hR hH0 hH han

/-- **Hilbert-source/horizontal-escape support theorem.**  Geometric vertical `L²` energy plus
qualitative horizontal escape bounds every nonzero coefficient index by the same radius. -/
theorem coefficient_index_le_exact_flank_radius_of_carrierFlankL2Energy_horizontalEscape
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {B : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (henergy : HasPerronCarrierFlankL2Energy F B)
    (hhor : HasVariablePerronHorizontalEscape F c n)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hB0 : ∀ᶠ M : ℕ in atTop, 0 ≤ B M)
    (hB : ∀ᶠ M : ℕ in atTop, B M ≤ C * R ^ M)
    (han : a n ≠ 0) :
    (n : ℝ) ≤ R := by
  exact coefficient_index_le_exact_flank_radius_of_carrierFlankL2Energy henergy
    (hhor.hasVariablePerronBoundaryEscape hc0 hsum hF hFeq hn)
    hc0 hsum hF hFeq hn hR hB0 hB han

/-- A positive real power on an exponent interval is bounded by the sum of its endpoint powers,
uniformly across the cases `b≤1` and `1≤b`. -/
theorem rpow_between_le_endpoint_sum
    {b u v x : ℝ} (hb : 0 < b) (hux : u ≤ x) (hxv : x ≤ v) :
    b ^ x ≤ b ^ u + b ^ v := by
  rcases le_total 1 b with hb1 | hb1
  · have h : b ^ x ≤ b ^ v := Real.rpow_le_rpow_of_exponent_le hb1 hxv
    exact h.trans (le_add_of_nonneg_left (Real.rpow_nonneg hb.le _))
  · have h : b ^ x ≤ b ^ u := Real.rpow_le_rpow_of_exponent_ge hb hb1 hux
    exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg hb.le _))

/-- Explicit height-independent numerator envelope for the Perron kernel on `-M≤Re s≤c`. -/
def perronStripKernelEnvelope (n M : ℕ) (δ c : ℝ) : ℝ :=
  2 *
    ((((n : ℝ) + δ) ^ (1 - (M : ℝ)) + ((n : ℝ) + δ) ^ (c + 1)) +
      (((n : ℝ) - δ) ^ (1 - (M : ℝ)) + ((n : ℝ) - δ) ^ (c + 1)) +
      2 * ((n : ℝ) ^ (1 - (M : ℝ)) + (n : ℝ) ^ (c + 1)))

/-- **Uniform quadratic strip decay.**  Above unit height, the entire variable Perron
regularization is bounded by an explicit constant times `(1+y²)⁻¹`, uniformly across the strip. -/
theorem perronEAt_strip_high_norm_le
    {n M : ℕ} {δ c x y : ℝ}
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ))
    (hxlo : -(M : ℝ) ≤ x) (hxhi : x ≤ c) (hy : 1 ≤ |y|) :
    ‖perronEAt n δ (↑x + ↑y * I)‖ ≤
      perronStripKernelEnvelope n M δ c / (1 + y ^ 2) := by
  let s : ℂ := ↑x + ↑y * I
  let Qp : ℝ := ((n : ℝ) + δ) ^ (1 - (M : ℝ)) + ((n : ℝ) + δ) ^ (c + 1)
  let Qm : ℝ := ((n : ℝ) - δ) ^ (1 - (M : ℝ)) + ((n : ℝ) - δ) ^ (c + 1)
  let Qn : ℝ := (n : ℝ) ^ (1 - (M : ℝ)) + (n : ℝ) ^ (c + 1)
  let N : ℝ := Qp + Qm + 2 * Qn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hbp : 0 < (n : ℝ) + δ := by linarith
  have hbm : 0 < (n : ℝ) - δ := by linarith
  have hbn : 0 < (n : ℝ) := by linarith
  have hexplo : 1 - (M : ℝ) ≤ x + 1 := by linarith
  have hexphi : x + 1 ≤ c + 1 := by linarith
  have hQp : ((n : ℝ) + δ) ^ (x + 1) ≤ Qp :=
    rpow_between_le_endpoint_sum hbp hexplo hexphi
  have hQm : ((n : ℝ) - δ) ^ (x + 1) ≤ Qm :=
    rpow_between_le_endpoint_sum hbm hexplo hexphi
  have hQn : (n : ℝ) ^ (x + 1) ≤ Qn :=
    rpow_between_le_endpoint_sum hbn hexplo hexphi
  have hQp0 : 0 ≤ Qp := by dsimp [Qp]; positivity
  have hQm0 : 0 ≤ Qm := by dsimp [Qm]; positivity
  have hQn0 : 0 ≤ Qn := by dsimp [Qn]; positivity
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hsre : s.re = x := by simp [s]
  have hsim : s.im = y := by simp [s]
  have hy0 : y ≠ 0 := by
    intro hy0
    norm_num [hy0] at hy
  have hs0 : s ≠ 0 := by
    intro hs
    have him := congrArg Complex.im hs
    rw [hsim] at him
    simp at him
    exact hy0 him
  have hs1 : s ≠ -1 := by
    intro hs
    have him := congrArg Complex.im hs
    rw [hsim] at him
    simp at him
    exact hy0 him
  have hkink : ‖perronKinkAt n δ s‖ ≤ N := by
    calc
      ‖perronKinkAt n δ s‖ ≤
          ((n : ℝ) + δ) ^ (s.re + 1) + ((n : ℝ) - δ) ^ (s.re + 1) +
            2 * (n : ℝ) ^ (s.re + 1) := perronKinkAt_norm_le hn hδ0 hδn s
      _ = ((n : ℝ) + δ) ^ (x + 1) + ((n : ℝ) - δ) ^ (x + 1) +
            2 * (n : ℝ) ^ (x + 1) := by rw [hsre]
      _ ≤ Qp + Qm + 2 * Qn := by gcongr
      _ = N := rfl
  have hyNormS : |y| ≤ ‖s‖ := by simpa [hsim] using Complex.abs_im_le_norm s
  have hyNormS1 : |y| ≤ ‖s + 1‖ := by
    have him : (s + 1).im = y := by simp [hsim]
    simpa [him] using Complex.abs_im_le_norm (s + 1)
  have hySq : y ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul]
    calc
      y ^ 2 = |y| * |y| := by rw [← sq_abs, pow_two]
      _ ≤ ‖s‖ * ‖s + 1‖ := mul_le_mul hyNormS hyNormS1 (abs_nonneg _) (norm_nonneg _)
  have honeSq : 1 ≤ y ^ 2 := by nlinarith [sq_abs y]
  have hhalf : (1 + y ^ 2) / 2 ≤ ‖s * (s + 1)‖ := by linarith
  have hhalfpos : 0 < (1 + y ^ 2) / 2 := by positivity
  rw [perronEAt_eq n δ hs0 hs1, norm_div]
  have hdiv := div_le_div₀ hN0 hkink hhalfpos hhalf
  have henv : perronStripKernelEnvelope n M δ c = 2 * N := by
    simp only [perronStripKernelEnvelope, N, Qp, Qm, Qn]
  rw [henv]
  calc
    ‖perronKinkAt n δ s‖ / ‖s * (s + 1)‖ ≤ N / ((1 + y ^ 2) / 2) := hdiv
    _ = 2 * N / (1 + y ^ 2) := by field_simp

/-- Coefficient-independent weighted horizontal carrier mass at height `T`. -/
def perronCarrierHorizontalWeight
    (F : ℂ → ℂ) (c : ℝ) (M : ℕ) (T : ℝ) : ℝ :=
  ∫ x in (-(M : ℝ))..c,
    (‖F (↑x + ↑T * I)‖ + ‖F (↑x + ↑(-T) * I)‖) / (1 + T ^ 2)

/-- Integrable weighted horizontal carrier mass above unit height at one contour depth. -/
def HasPerronCarrierHorizontalMassAt
    (F : ℂ → ℂ) (c : ℝ) (M : ℕ) : Prop :=
  IntegrableOn (perronCarrierHorizontalWeight F c M) (Ioi 1)

/-- Weighted carrier strip mass produces a quiet horizontal exhaustion for every Perron kernel. -/
theorem HasPerronCarrierHorizontalMassAt.hasPerronHorizontalEscapeAt
    {F : ℂ → ℂ} {c δ : ℝ} {n M : ℕ}
    (hF : Differentiable ℂ F) (hc0 : 0 < c)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ))
    (hmass : HasPerronCarrierHorizontalMassAt F c M) :
    HasPerronHorizontalEscapeAt F c n δ M := by
  let K : ℝ := perronStripKernelEnvelope n M δ c
  let u : ℝ → ℝ := fun T =>
    ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑T * I)‖ +
    ‖∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(-T) * I)‖
  have hMc : -(M : ℝ) ≤ c := by
    have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hK0 : 0 ≤ K := by
    dsimp [K, perronStripKernelEnvelope]
    positivity
  have hGcont : Continuous (perronContourIntegrand F n δ) :=
    (hF.mul (perronEAt_differentiable hn hδ0 hδn)).continuous
  have htopcont : Continuous (fun T : ℝ =>
      ∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑T * I)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hGcont.comp (by fun_prop)
  have hbotcont : Continuous (fun T : ℝ =>
      ∫ x in (-(M : ℝ))..c, perronContourIntegrand F n δ (↑x + ↑(-T) * I)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hGcont.comp (by fun_prop)
  have hucont : Continuous u := htopcont.norm.add hbotcont.norm
  have hhigh : ∀ T : ℝ, 1 < T →
      u T ≤ K * perronCarrierHorizontalWeight F c M T := by
    intro T hT
    have hTabs : 1 ≤ |T| := le_trans hT.le (le_abs_self T)
    have hnegTabs : 1 ≤ |-T| := by simpa using hTabs
    let ftop : ℝ → ℝ := fun x =>
      ‖perronContourIntegrand F n δ (↑x + ↑T * I)‖
    let fbot : ℝ → ℝ := fun x =>
      ‖perronContourIntegrand F n δ (↑x + ↑(-T) * I)‖
    let gtop : ℝ → ℝ := fun x => K * ‖F (↑x + ↑T * I)‖ / (1 + T ^ 2)
    let gbot : ℝ → ℝ := fun x => K * ‖F (↑x + ↑(-T) * I)‖ / (1 + T ^ 2)
    have hftop : IntervalIntegrable ftop volume (-(M : ℝ)) c := by
      exact (hGcont.comp (by fun_prop)).norm.intervalIntegrable _ _
    have hfbot : IntervalIntegrable fbot volume (-(M : ℝ)) c := by
      exact (hGcont.comp (by fun_prop)).norm.intervalIntegrable _ _
    have hgtop : IntervalIntegrable gtop volume (-(M : ℝ)) c := by
      have hgcont : Continuous gtop := by
        dsimp [gtop]
        have hline : Continuous (fun x : ℝ => F (↑x + ↑T * I)) :=
          hF.continuous.comp (by fun_prop)
        exact (continuous_const.mul hline.norm).div_const _
      exact hgcont.intervalIntegrable _ _
    have hgbot : IntervalIntegrable gbot volume (-(M : ℝ)) c := by
      have hgcont : Continuous gbot := by
        dsimp [gbot]
        have hline : Continuous (fun x : ℝ => F (↑x + ↑(-T) * I)) :=
          hF.continuous.comp (by fun_prop)
        exact (continuous_const.mul hline.norm).div_const _
      exact hgcont.intervalIntegrable _ _
    have htopPoint : ∀ x ∈ Icc (-(M : ℝ)) c, ftop x ≤ gtop x := by
      intro x hx
      have hE := perronEAt_strip_high_norm_le hn hδ0 hδn hx.1 hx.2 hTabs
      dsimp [ftop, gtop]
      rw [perronContourIntegrand, norm_mul]
      calc
        ‖F (↑x + ↑T * I)‖ * ‖perronEAt n δ (↑x + ↑T * I)‖ ≤
            ‖F (↑x + ↑T * I)‖ * (K / (1 + T ^ 2)) :=
          mul_le_mul_of_nonneg_left hE (norm_nonneg _)
        _ = K * ‖F (↑x + ↑T * I)‖ / (1 + T ^ 2) := by ring
    have hbotPoint : ∀ x ∈ Icc (-(M : ℝ)) c, fbot x ≤ gbot x := by
      intro x hx
      have hE := perronEAt_strip_high_norm_le hn hδ0 hδn hx.1 hx.2 hnegTabs
      dsimp [fbot, gbot]
      rw [perronContourIntegrand, norm_mul]
      calc
        ‖F (↑x + ↑(-T) * I)‖ * ‖perronEAt n δ (↑x + ↑(-T) * I)‖ ≤
            ‖F (↑x + ↑(-T) * I)‖ * (K / (1 + (-T) ^ 2)) :=
          mul_le_mul_of_nonneg_left hE (norm_nonneg _)
        _ = K * ‖F (↑x + ↑(-T) * I)‖ / (1 + T ^ 2) := by ring
    calc
      u T ≤ (∫ x in (-(M : ℝ))..c, ftop x) +
          ∫ x in (-(M : ℝ))..c, fbot x := by
        dsimp [u, ftop, fbot]
        gcongr <;> exact intervalIntegral.norm_integral_le_integral_norm hMc
      _ ≤ (∫ x in (-(M : ℝ))..c, gtop x) +
          ∫ x in (-(M : ℝ))..c, gbot x := by
        gcongr
        · exact intervalIntegral.integral_mono_on hMc hftop hgtop htopPoint
        · exact intervalIntegral.integral_mono_on hMc hfbot hgbot hbotPoint
      _ = K * perronCarrierHorizontalWeight F c M T := by
        unfold perronCarrierHorizontalWeight
        dsimp [gtop, gbot]
        rw [← intervalIntegral.integral_add hgtop hgbot]
        rw [← intervalIntegral.integral_const_mul]
        congr 1
        funext x
        ring
  have huHigh : IntegrableOn u (Ioi 1) := by
    have hKmass : IntegrableOn (fun T => K * perronCarrierHorizontalWeight F c M T)
        (Ioi 1) := hmass.const_mul K
    refine hKmass.mono' hucont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [u]; positivity)]
    exact hhigh T hT
  have huLow : IntegrableOn u (Ioc 0 1) := hucont.integrableOn_Ioc
  have huInt : IntegrableOn u (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact huLow.union huHigh
  obtain ⟨T, hTtop, hTnonneg, huT⟩ :=
    exists_seq_atTop_tendsto_zero_of_continuous_integrableOn_Ioi hucont huInt
  refine ⟨T, hTtop, hTnonneg, ?_, ?_⟩
  · apply squeeze_zero_norm (fun k => ?_) huT
    exact le_add_of_nonneg_right (norm_nonneg _)
  · apply squeeze_zero_norm (fun k => ?_) huT
    exact le_add_of_nonneg_left (norm_nonneg _)

/-- **Boundary escape from horizontal carrier mass.**  The intermediate horizontal-escape Prop is
constructed internally from the weighted strip mass. -/
theorem hasPerronBoundaryEscapeAt_of_carrierHorizontalMassAt
    {F : ℂ → ℂ} {a : ℕ → ℂ} {c δ : ℝ} {n M : ℕ}
    (hmass : HasPerronCarrierHorizontalMassAt F c M)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    HasPerronBoundaryEscapeAt F c n δ M :=
  hasPerronBoundaryEscapeAt_of_horizontalEscape hc0 hsum hF hFeq hn hδ0 hδn
    (HasPerronCarrierHorizontalMassAt.hasPerronHorizontalEscapeAt
      hF hc0 hn hδ0 hδn hmass)

/-- **Pointwise Perron charge from the two carrier masses.**  Vertical `L²` energy supplies flank
mass and horizontal weighted mass supplies boundary escape; neither intermediate interface appears. -/
theorem hasPerronBoundaryChargeAt_of_carrierL2StripMassAt
    {F : ℂ → ℂ} {a : ℕ → ℂ} {c δ B : ℝ} {n M : ℕ}
    (henergy : HasPerronCarrierFlankL2EnergyAt F M B)
    (hhorizontal : HasPerronCarrierHorizontalMassAt F c M)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    HasPerronBoundaryChargeAt F c n δ M
      (4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) * (B * Real.sqrt Real.pi)) :=
  hasPerronBoundaryChargeAt_of_escape_of_carrierFlankL2EnergyAt hF hn hM hδ0 hδn
    (hasPerronBoundaryEscapeAt_of_carrierHorizontalMassAt
      hhorizontal hc0 hsum hF hFeq hn hδ0 hδn)
    henergy

/-- **Interface-free pointwise Perron contour bound from the two carrier masses.**  The flank-mass,
horizontal-escape, boundary-escape, and boundary-charge Props are all constructed internally. -/
theorem perron_right_integral_norm_le_of_carrierL2StripMassAt
    {F : ℂ → ℂ} {a : ℕ → ℂ} {c δ B : ℝ} {n M : ℕ}
    (henergy : HasPerronCarrierFlankL2EnergyAt F M B)
    (hhorizontal : HasPerronCarrierHorizontalMassAt F c M)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hM : 2 ≤ M) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    ‖∫ y : ℝ, perronContourIntegrand F n δ (↑c + ↑y * I)‖ ≤
      4 * perronSupportScaleAt n δ ^ (1 - (M : ℝ)) * (B * Real.sqrt Real.pi) :=
  perron_right_integral_norm_le_of_boundaryChargeAt hF
    (perronEAt_differentiable hn hδ0 hδn)
    (hasPerronBoundaryChargeAt_of_carrierL2StripMassAt
      henergy hhorizontal hc0 hsum hF hFeq hn hM hδ0 hδn)

/-- Eventual coefficient-independent horizontal carrier mass at every negative-integer depth. -/
def HasPerronCarrierHorizontalMass (F : ℂ → ℂ) (c : ℝ) : Prop :=
  ∀ᶠ M : ℕ in atTop, HasPerronCarrierHorizontalMassAt F c M

/-- Carrier horizontal mass discharges variable horizontal escape for every coefficient index. -/
theorem HasPerronCarrierHorizontalMass.hasVariablePerronHorizontalEscape
    {F : ℂ → ℂ} {c : ℝ} {n : ℕ}
    (hmass : HasPerronCarrierHorizontalMass F c)
    (hF : Differentiable ℂ F) (hc0 : 0 < c) (hn : 1 ≤ n) :
    HasVariablePerronHorizontalEscape F c n := by
  intro δ hδ0 hδ1 hδn
  filter_upwards [hmass] with M hM
  exact HasPerronCarrierHorizontalMassAt.hasPerronHorizontalEscapeAt hF hc0 hn hδ0 hδn hM

/-- The two coefficient-independent carrier masses discharge normalized Perron boundary charge:
weighted left-flank mass supplies growth, while weighted horizontal mass supplies escape. -/
theorem HasPerronCarrierFlankMass.hasVariablePerronBoundaryCharge_of_carrierHorizontalMass
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ}
    (hflank : HasPerronCarrierFlankMass F H)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s) (hn : 1 ≤ n) :
    HasVariablePerronBoundaryCharge F c H n := by
  exact hflank.hasVariablePerronBoundaryCharge_of_horizontalEscape
    (hhorizontal.hasVariablePerronHorizontalEscape hF hc0 hn)
    hc0 hsum hF hFeq hn

/-- The coefficient-bound Prop is fully discharged by coefficient-independent carrier masses. -/
theorem HasPerronCarrierFlankMass.hasVariableQuietFlankCoefficientBound_of_carrierHorizontalMass
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ}
    (hflank : HasPerronCarrierFlankMass F H)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s) (hn : 1 ≤ n) :
    HasVariableQuietFlankCoefficientBound a H n := by
  exact (hflank.hasVariablePerronBoundaryCharge_of_carrierHorizontalMass
    hhorizontal hc0 hsum hF hFeq hn).hasVariableQuietFlankCoefficientBound
      hc0 hsum hF hFeq hn

/-- **Coefficient-independent carrier-mass support theorem.**  Geometric left-flank mass and
finite weighted horizontal mass force every nonzero coefficient index below the flank radius. -/
theorem coefficient_index_le_exact_flank_radius_of_carrierMass
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {H : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (hflank : HasPerronCarrierFlankMass F H)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M)
    (hH : ∀ᶠ M : ℕ in atTop, H M ≤ C * R ^ M)
    (han : a n ≠ 0) :
    (n : ℝ) ≤ R := by
  exact coefficient_index_le_exact_flank_radius_of_carrierFlankMass_horizontalEscape
    hflank (hhorizontal.hasVariablePerronHorizontalEscape hF hc0 hn)
    hc0 hsum hF hFeq hn hR hH0 hH han

/-- **Hilbert carrier-mass support theorem.**  Geometric vertical `L²` energy and finite weighted
horizontal carrier mass force every nonzero coefficient index below the same geometric radius. -/
theorem coefficient_index_le_exact_flank_radius_of_carrierL2StripMass
    {F : ℂ → ℂ} {c : ℝ} {a : ℕ → ℂ} {B : ℕ → ℝ} {n : ℕ} {C R : ℝ}
    (henergy : HasPerronCarrierFlankL2Energy F B)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hB0 : ∀ᶠ M : ℕ in atTop, 0 ≤ B M)
    (hB : ∀ᶠ M : ℕ in atTop, B M ≤ C * R ^ M)
    (han : a n ≠ 0) :
    (n : ℝ) ≤ R := by
  exact coefficient_index_le_exact_flank_radius_of_carrierFlankL2Energy_horizontalEscape
    henergy (hhorizontal.hasVariablePerronHorizontalEscape hF hc0 hn)
    hc0 hsum hF hFeq hn hR hB0 hB han

end RHTower
