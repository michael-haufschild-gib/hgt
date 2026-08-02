import GaloisForLFunctions.RHTower.SuzukiParityResolventTransportBudget
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Suzuki cross-parity spectral-pair transport

The finite parity transport budget must be stated on the literal source spectral measures of
Suzuki's restricted-Weil operator. This module supplies that measure-level carrier.

For even node `t`, odd node `s`, source weights `a,b`, and a shift below the spectrum, the exact
cross-parity kernel is

`a b (s-t) / ((t-lambda)^2 (s-lambda)^2)`.

Fubini factorization proves that its product-measure integral is exactly the cross-Wronskian
`E' O - E O'`. After normalization it is the parity hazard `E'/E-O'/O`. Its positive and
negative parts therefore have a literal meaning: lower-even-pair credit and odd-below-even
spectral-inversion debt. Positive transport occurs exactly when credit exceeds debt. This allows
arbitrarily many local spectral reversals and makes no global monotone-likelihood assumption.

The product-integral algebra is classical. Its role is to expose the exact infinite spectral
quantity that the Suzuki prime--archimedean source must control. No Riemann-hypothesis assumption
or numerical computation occurs.
-/

open MeasureTheory

namespace RHTower

noncomputable section

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Stieltjes energy of one weighted source spectral measure. -/
def suzukiParitySpectralEnergy
    (μ : Measure α) (node weight : α → ℝ) (lambda : ℝ) : ℝ :=
  ∫ x, weight x * suzukiShiftResolventKernel node lambda x ∂μ

/-- Squared-resolvent velocity of one weighted source spectral measure. -/
def suzukiParitySquaredSpectralEnergy
    (μ : Measure α) (node weight : α → ℝ) (lambda : ℝ) : ℝ :=
  ∫ x, weight x * suzukiShiftResolventKernel node lambda x ^ 2 ∂μ

/-- Pointwise signed odd-minus-even spectral-gap contribution. -/
def suzukiParitySpectralCrossGapKernel
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ) (z : α × β) : ℝ :=
  evenWeight z.1 * oddWeight z.2 * (oddNode z.2 - evenNode z.1) /
    ((evenNode z.1 - lambda) ^ 2 * (oddNode z.2 - lambda) ^ 2)

/-- Total signed cross-parity spectral-gap mass. -/
def suzukiParitySpectralCrossGapMass
    (μ : Measure α) (ν : Measure β)
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ) : ℝ :=
  ∫ z, suzukiParitySpectralCrossGapKernel
    evenNode evenWeight oddNode oddWeight lambda z ∂μ.prod ν

/-- Difference of the normalized even and odd squared-resolvent responses. -/
def suzukiParitySpectralHazardGap
    (μ : Measure α) (ν : Measure β)
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ) : ℝ :=
  suzukiParitySquaredSpectralEnergy μ evenNode evenWeight lambda /
      suzukiParitySpectralEnergy μ evenNode evenWeight lambda -
    suzukiParitySquaredSpectralEnergy ν oddNode oddWeight lambda /
      suzukiParitySpectralEnergy ν oddNode oddWeight lambda

/-- Positive Jordan mass of the signed pair kernel: lower-even-pair transport credit. -/
def suzukiParitySpectralLowerPairCredit
    (μ : Measure α) (ν : Measure β)
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ) : ℝ :=
  ∫ z, (suzukiParitySpectralCrossGapKernel
    evenNode evenWeight oddNode oddWeight lambda z)⁺ ∂μ.prod ν

/-- Negative Jordan mass of the signed pair kernel: odd-below-even spectral-inversion debt. -/
def suzukiParitySpectralInversionDebt
    (μ : Measure α) (ν : Measure β)
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ) : ℝ :=
  ∫ z, (suzukiParitySpectralCrossGapKernel
    evenNode evenWeight oddNode oddWeight lambda z)⁻ ∂μ.prod ν

omit [MeasurableSpace α] [MeasurableSpace β] in
/-- Pointwise rational identity behind the cross-parity product integral. -/
theorem suzukiParitySpectralCrossGapKernel_eq_crossProduct
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ) (z : α × β) :
    suzukiParitySpectralCrossGapKernel
        evenNode evenWeight oddNode oddWeight lambda z =
      (evenWeight z.1 * suzukiShiftResolventKernel evenNode lambda z.1 ^ 2) *
          (oddWeight z.2 * suzukiShiftResolventKernel oddNode lambda z.2) -
        (evenWeight z.1 * suzukiShiftResolventKernel evenNode lambda z.1) *
          (oddWeight z.2 * suzukiShiftResolventKernel oddNode lambda z.2 ^ 2) := by
  simp only [suzukiParitySpectralCrossGapKernel, suzukiShiftResolventKernel]
  field_simp
  ring

/-- **Measure-level cross-parity Wronskian law.** Under the exact four one-variable
integrability hypotheses, the cross-Wronskian is the signed product-measure spectral-gap mass. -/
theorem suzukiParitySpectral_crossWronskian_eq_crossGapIntegral
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ)
    (heven : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x) μ)
    (hevenSq : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x ^ 2) μ)
    (hodd : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y) ν)
    (hoddSq : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y ^ 2) ν) :
    suzukiParitySquaredSpectralEnergy μ evenNode evenWeight lambda *
          suzukiParitySpectralEnergy ν oddNode oddWeight lambda -
        suzukiParitySpectralEnergy μ evenNode evenWeight lambda *
          suzukiParitySquaredSpectralEnergy ν oddNode oddWeight lambda =
      suzukiParitySpectralCrossGapMass
        μ ν evenNode evenWeight oddNode oddWeight lambda := by
  let even : α → ℝ := fun x =>
    evenWeight x * suzukiShiftResolventKernel evenNode lambda x
  let evenSq : α → ℝ := fun x =>
    evenWeight x * suzukiShiftResolventKernel evenNode lambda x ^ 2
  let odd : β → ℝ := fun y =>
    oddWeight y * suzukiShiftResolventKernel oddNode lambda y
  let oddSq : β → ℝ := fun y =>
    oddWeight y * suzukiShiftResolventKernel oddNode lambda y ^ 2
  have hprod₁ : Integrable (fun z : α × β => evenSq z.1 * odd z.2) (μ.prod ν) :=
    hevenSq.mul_prod hodd
  have hprod₂ : Integrable (fun z : α × β => even z.1 * oddSq z.2) (μ.prod ν) :=
    heven.mul_prod hoddSq
  have hkernel :
      (fun z => suzukiParitySpectralCrossGapKernel
          evenNode evenWeight oddNode oddWeight lambda z) =
        (fun z : α × β => evenSq z.1 * odd z.2 - even z.1 * oddSq z.2) := by
    funext z
    exact suzukiParitySpectralCrossGapKernel_eq_crossProduct
      evenNode evenWeight oddNode oddWeight lambda z
  rw [suzukiParitySpectralCrossGapMass, hkernel]
  change
    (∫ x, evenSq x ∂μ) * (∫ y, odd y ∂ν) -
          (∫ x, even x ∂μ) * (∫ y, oddSq y ∂ν) =
      ∫ z, ((fun z : α × β => evenSq z.1 * odd z.2) -
        (fun z : α × β => even z.1 * oddSq z.2)) z ∂μ.prod ν
  rw [integral_sub' hprod₁ hprod₂]
  rw [integral_prod_mul evenSq odd, integral_prod_mul even oddSq]

/-- The four one-variable hypotheses automatically make the signed pair kernel integrable. -/
theorem integrable_suzukiParitySpectralCrossGapKernel
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ)
    (heven : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x) μ)
    (hevenSq : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x ^ 2) μ)
    (hodd : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y) ν)
    (hoddSq : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y ^ 2) ν) :
    Integrable (suzukiParitySpectralCrossGapKernel
      evenNode evenWeight oddNode oddWeight lambda) (μ.prod ν) := by
  let even : α → ℝ := fun x =>
    evenWeight x * suzukiShiftResolventKernel evenNode lambda x
  let evenSq : α → ℝ := fun x =>
    evenWeight x * suzukiShiftResolventKernel evenNode lambda x ^ 2
  let odd : β → ℝ := fun y =>
    oddWeight y * suzukiShiftResolventKernel oddNode lambda y
  let oddSq : β → ℝ := fun y =>
    oddWeight y * suzukiShiftResolventKernel oddNode lambda y ^ 2
  have hprod₁ : Integrable (fun z : α × β => evenSq z.1 * odd z.2) (μ.prod ν) :=
    hevenSq.mul_prod hodd
  have hprod₂ : Integrable (fun z : α × β => even z.1 * oddSq z.2) (μ.prod ν) :=
    heven.mul_prod hoddSq
  have hkernel :
      (fun z => suzukiParitySpectralCrossGapKernel
          evenNode evenWeight oddNode oddWeight lambda z) =
        (fun z : α × β => evenSq z.1 * odd z.2 - even z.1 * oddSq z.2) := by
    funext z
    exact suzukiParitySpectralCrossGapKernel_eq_crossProduct
      evenNode evenWeight oddNode oddWeight lambda z
  change Integrable
    (fun z => suzukiParitySpectralCrossGapKernel
      evenNode evenWeight oddNode oddWeight lambda z) (μ.prod ν)
  rw [hkernel]
  exact hprod₁.sub hprod₂

/-- The measure-level parity hazard is the signed pair mass normalized by both parity energies. -/
theorem suzukiParitySpectral_hazardGap_eq_crossGapMass_div
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ)
    (heven : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x) μ)
    (hevenSq : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x ^ 2) μ)
    (hodd : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y) ν)
    (hoddSq : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y ^ 2) ν)
    (heven0 : suzukiParitySpectralEnergy μ evenNode evenWeight lambda ≠ 0)
    (hodd0 : suzukiParitySpectralEnergy ν oddNode oddWeight lambda ≠ 0) :
    suzukiParitySpectralHazardGap
        μ ν evenNode evenWeight oddNode oddWeight lambda =
      suzukiParitySpectralCrossGapMass
          μ ν evenNode evenWeight oddNode oddWeight lambda /
        (suzukiParitySpectralEnergy μ evenNode evenWeight lambda *
          suzukiParitySpectralEnergy ν oddNode oddWeight lambda) := by
  rw [suzukiParitySpectralHazardGap]
  have hcross :=
    suzukiParitySpectral_crossWronskian_eq_crossGapIntegral
      evenNode evenWeight oddNode oddWeight lambda heven hevenSq hodd hoddSq
  field_simp [heven0, hodd0]
  linear_combination hcross

/-- Jordan decomposition of the signed spectral carrier into credit minus inversion debt. -/
theorem suzukiParitySpectralCrossGapMass_eq_credit_sub_inversionDebt
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ)
    (heven : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x) μ)
    (hevenSq : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x ^ 2) μ)
    (hodd : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y) ν)
    (hoddSq : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y ^ 2) ν) :
    suzukiParitySpectralCrossGapMass
        μ ν evenNode evenWeight oddNode oddWeight lambda =
      suzukiParitySpectralLowerPairCredit
          μ ν evenNode evenWeight oddNode oddWeight lambda -
        suzukiParitySpectralInversionDebt
          μ ν evenNode evenWeight oddNode oddWeight lambda := by
  have hkernel :=
    integrable_suzukiParitySpectralCrossGapKernel
      evenNode evenWeight oddNode oddWeight lambda heven hevenSq hodd hoddSq
  have hpos : Integrable
      (fun z => (suzukiParitySpectralCrossGapKernel
        evenNode evenWeight oddNode oddWeight lambda z)⁺) (μ.prod ν) := by
    exact (hkernel.sup (integrable_zero _ _ (μ.prod ν))).congr
      (ae_of_all _ fun z => rfl)
  have hneg : Integrable
      (fun z => (suzukiParitySpectralCrossGapKernel
        evenNode evenWeight oddNode oddWeight lambda z)⁻) (μ.prod ν) := by
    exact (hkernel.neg.sup (integrable_zero _ _ (μ.prod ν))).congr
      (ae_of_all _ fun z => rfl)
  have hfun :
      suzukiParitySpectralCrossGapKernel
          evenNode evenWeight oddNode oddWeight lambda =
        (fun z => (suzukiParitySpectralCrossGapKernel
            evenNode evenWeight oddNode oddWeight lambda z)⁺) -
          (fun z => (suzukiParitySpectralCrossGapKernel
            evenNode evenWeight oddNode oddWeight lambda z)⁻) := by
    funext z
    exact (posPart_sub_negPart _).symm
  rw [suzukiParitySpectralCrossGapMass, hfun]
  change
    (∫ z, ((fun z => (suzukiParitySpectralCrossGapKernel
          evenNode evenWeight oddNode oddWeight lambda z)⁺) -
        (fun z => (suzukiParitySpectralCrossGapKernel
          evenNode evenWeight oddNode oddWeight lambda z)⁻)) z ∂μ.prod ν) =
      (∫ z, (suzukiParitySpectralCrossGapKernel
          evenNode evenWeight oddNode oddWeight lambda z)⁺ ∂μ.prod ν) -
        ∫ z, (suzukiParitySpectralCrossGapKernel
          evenNode evenWeight oddNode oddWeight lambda z)⁻ ∂μ.prod ν
  rw [integral_sub' hpos hneg]

/-- **Measure-level credit/debt law.** Positive parity transport occurs exactly when the complete
lower-even-pair credit exceeds all odd-below-even spectral-inversion debt. -/
theorem suzukiParitySpectral_hazardGap_pos_iff_inversionDebt_lt_credit
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ)
    (heven : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x) μ)
    (hevenSq : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x ^ 2) μ)
    (hodd : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y) ν)
    (hoddSq : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y ^ 2) ν)
    (hevenPos : 0 < suzukiParitySpectralEnergy μ evenNode evenWeight lambda)
    (hoddPos : 0 < suzukiParitySpectralEnergy ν oddNode oddWeight lambda) :
    0 < suzukiParitySpectralHazardGap
        μ ν evenNode evenWeight oddNode oddWeight lambda ↔
      suzukiParitySpectralInversionDebt
          μ ν evenNode evenWeight oddNode oddWeight lambda <
        suzukiParitySpectralLowerPairCredit
          μ ν evenNode evenWeight oddNode oddWeight lambda := by
  rw [suzukiParitySpectral_hazardGap_eq_crossGapMass_div
    evenNode evenWeight oddNode oddWeight lambda heven hevenSq hodd hoddSq
    hevenPos.ne' hoddPos.ne']
  rw [div_pos_iff]
  rw [suzukiParitySpectralCrossGapMass_eq_credit_sub_inversionDebt
    evenNode evenWeight oddNode oddWeight lambda heven hevenSq hodd hoddSq]
  constructor
  · intro h
    rcases h with h | h
    · exact sub_pos.mp h.1
    · exact False.elim ((not_lt_of_ge (mul_pos hevenPos hoddPos).le) h.2)
  · intro h
    exact Or.inl ⟨sub_pos.mpr h, mul_pos hevenPos hoddPos⟩

/-- Vanishing transport is exactly balance of lower-pair credit and inversion debt. -/
theorem suzukiParitySpectral_hazardGap_eq_zero_iff_inversionDebt_eq_credit
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ)
    (heven : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x) μ)
    (hevenSq : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x ^ 2) μ)
    (hodd : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y) ν)
    (hoddSq : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y ^ 2) ν)
    (hevenPos : 0 < suzukiParitySpectralEnergy μ evenNode evenWeight lambda)
    (hoddPos : 0 < suzukiParitySpectralEnergy ν oddNode oddWeight lambda) :
    suzukiParitySpectralHazardGap
          μ ν evenNode evenWeight oddNode oddWeight lambda = 0 ↔
      suzukiParitySpectralInversionDebt
          μ ν evenNode evenWeight oddNode oddWeight lambda =
        suzukiParitySpectralLowerPairCredit
          μ ν evenNode evenWeight oddNode oddWeight lambda := by
  rw [suzukiParitySpectral_hazardGap_eq_crossGapMass_div
    evenNode evenWeight oddNode oddWeight lambda heven hevenSq hodd hoddSq
    hevenPos.ne' hoddPos.ne']
  rw [div_eq_zero_iff]
  simp only [mul_eq_zero, hevenPos.ne', hoddPos.ne', or_false]
  rw [suzukiParitySpectralCrossGapMass_eq_credit_sub_inversionDebt
    evenNode evenWeight oddNode oddWeight lambda heven hevenSq hodd hoddSq]
  exact sub_eq_zero.trans eq_comm

/-- Negative transport is exactly strict domination of lower-pair credit by inversion debt. -/
theorem suzukiParitySpectral_hazardGap_neg_iff_credit_lt_inversionDebt
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (evenNode evenWeight : α → ℝ) (oddNode oddWeight : β → ℝ)
    (lambda : ℝ)
    (heven : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x) μ)
    (hevenSq : Integrable
      (fun x => evenWeight x * suzukiShiftResolventKernel evenNode lambda x ^ 2) μ)
    (hodd : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y) ν)
    (hoddSq : Integrable
      (fun y => oddWeight y * suzukiShiftResolventKernel oddNode lambda y ^ 2) ν)
    (hevenPos : 0 < suzukiParitySpectralEnergy μ evenNode evenWeight lambda)
    (hoddPos : 0 < suzukiParitySpectralEnergy ν oddNode oddWeight lambda) :
    suzukiParitySpectralHazardGap
          μ ν evenNode evenWeight oddNode oddWeight lambda < 0 ↔
      suzukiParitySpectralLowerPairCredit
          μ ν evenNode evenWeight oddNode oddWeight lambda <
        suzukiParitySpectralInversionDebt
          μ ν evenNode evenWeight oddNode oddWeight lambda := by
  rw [suzukiParitySpectral_hazardGap_eq_crossGapMass_div
    evenNode evenWeight oddNode oddWeight lambda heven hevenSq hodd hoddSq
    hevenPos.ne' hoddPos.ne']
  rw [div_neg_iff]
  rw [suzukiParitySpectralCrossGapMass_eq_credit_sub_inversionDebt
    evenNode evenWeight oddNode oddWeight lambda heven hevenSq hodd hoddSq]
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim ((not_lt_of_ge (mul_pos hevenPos hoddPos).le) h.2)
    · exact sub_neg.mp h.1
  · intro h
    exact Or.inr ⟨sub_neg.mpr h, mul_pos hevenPos hoddPos⟩

end

end RHTower
