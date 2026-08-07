import GaloisForLFunctions.RHTower.BurnolCartierZeroTransferHeadGain

/-!
# Fixed two-head polarization of Burnol's Cartier zero-transfer

The fixed aperture head is an intrinsic bounded reading: average against the indicator of the
aperture.  Together with its cosine mate it gives a positive, divisor-independent two-head
polarization.  On the fixed co-Poisson atom, Cartier zero-transfer acts on these two readings by
the reciprocal gains already computed in `BurnolCartierZeroTransferHeadGain`.

This module proves a strict new rigidity law.  At every hypothetical right-half Xi divisor, the
zero-transfer strictly amplifies the unweighted sum of the two head energies, although it is an
isometry on the ambient `L²` space.  Consequently a pre-divisor Euler--Gamma--Stokes theorem need
only prove non-amplification of this fixed positive two-head reading.  That one-sided inequality
derives the previously required separate forward-head conservation and hence RH.

No head conservation, critical-line placement, Stokes sewing, or RH is assumed here.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Canonical aperture-head readings -/

/-- Intrinsic forward aperture-head coefficient: average against the aperture indicator.  On a
vector that is constant on the head, this recovers the literal constant. -/
def burnolSoninForwardHeadCoefficient (a : ℝ) (f : evenSubspace) : ℂ :=
  inner ℂ (soninHeadIndicator a) ((f : evenSubspace) : SoninL2) * (a : ℂ)⁻¹

/-- Cosine-oriented mate of the intrinsic forward aperture-head coefficient. -/
def burnolSoninCosineHeadCoefficient (a : ℝ) (f : evenSubspace) : ℂ :=
  burnolSoninForwardHeadCoefficient a (soninCosineUnitary f)

/-- Fixed positive polarization carried by the two Gamma orientations at one aperture. -/
def burnolSoninGammaHeadEnergy (a : ℝ) (f : evenSubspace) : ℝ :=
  ‖burnolSoninForwardHeadCoefficient a f‖ ^ 2 +
    ‖burnolSoninCosineHeadCoefficient a f‖ ^ 2

/-- The intrinsic average recovers every literal constant forward head. -/
theorem burnolSoninForwardHeadCoefficient_eq_of_headEquals
    {a : ℝ} (ha : 0 < a) (f : evenSubspace) {c : ℂ}
    (hc : BurnolSoninHeadEquals a f c) :
    burnolSoninForwardHeadCoefficient a f = c := by
  rw [burnolSoninForwardHeadCoefficient, inner_soninHeadIndicator]
  have hint :
      (∫ x in Ioo (0 : ℝ) a,
        (((f : evenSubspace) : SoninL2) : ℝ → ℂ) x) = c * (a : ℂ) := by
    rw [integral_congr_ae hc, setIntegral_const]
    simp [ha.le]
    ring
  rw [hint]
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne']

/-- The cosine-oriented intrinsic average likewise recovers its literal constant head. -/
theorem burnolSoninCosineHeadCoefficient_eq_of_headEquals
    {a : ℝ} (ha : 0 < a) (f : evenSubspace) {c : ℂ}
    (hc : BurnolSoninHeadEquals a (soninCosineUnitary f) c) :
    burnolSoninCosineHeadCoefficient a f = c :=
  burnolSoninForwardHeadCoefficient_eq_of_headEquals ha _ hc

/-! ## Exact fixed-source values -/

@[simp] theorem burnolSoninForwardHeadCoefficient_fixedSubWindowSourceAtom :
    burnolSoninForwardHeadCoefficient (1 / 2) burnolFixedSubWindowSourceAtom = -1 :=
  burnolSoninForwardHeadCoefficient_eq_of_headEquals (by norm_num)
    _ burnolFixedSubWindowSourceAtom_head

@[simp] theorem burnolSoninCosineHeadCoefficient_fixedSubWindowSourceAtom :
    burnolSoninCosineHeadCoefficient (1 / 2) burnolFixedSubWindowSourceAtom =
      -(Real.log 2 : ℂ) :=
  burnolSoninCosineHeadCoefficient_eq_of_headEquals (by norm_num)
    _ soninCosineUnitary_burnolFixedSubWindowSourceAtom_head

/-- Forward head of the actual Xi zero-transfer source lift, read by the intrinsic coefficient. -/
theorem xiDivisor_burnolSoninForwardHeadCoefficient_cartierZeroTransfer
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninForwardHeadCoefficient (1 / 2)
        (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) =
      -burnolCartierForwardHeadGain (rho : ℂ) :=
  burnolSoninForwardHeadCoefficient_eq_of_headEquals (by norm_num) _
    (xiDivisor_burnolCartierZeroTransfer_fixed_head rho h)

/-- Cosine head of the same actual Xi zero-transfer source lift. -/
theorem xiDivisor_burnolSoninCosineHeadCoefficient_cartierZeroTransfer
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninCosineHeadCoefficient (1 / 2)
        (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) =
      -(Real.log 2 : ℂ) * burnolCartierCosineHeadGain (rho : ℂ) :=
  burnolSoninCosineHeadCoefficient_eq_of_headEquals (by norm_num) _
    (xiDivisor_burnolCartierZeroTransfer_fixed_cosine_head rho h)

/-- The pre-transfer fixed source has explicit two-head energy `1 + (log 2)²`. -/
theorem burnolSoninGammaHeadEnergy_fixedSubWindowSourceAtom :
    burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom =
      1 + (Real.log 2) ^ 2 := by
  rw [burnolSoninGammaHeadEnergy,
    burnolSoninForwardHeadCoefficient_fixedSubWindowSourceAtom,
    burnolSoninCosineHeadCoefficient_fixedSubWindowSourceAtom]
  rw [norm_neg, norm_one, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.log_pos one_lt_two)]
  norm_num

/-- Exact post-transfer value of the fixed two-head polarization. -/
theorem xiDivisor_burnolSoninGammaHeadEnergy_cartierZeroTransfer
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninGammaHeadEnergy (1 / 2)
        (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) =
      ‖burnolCartierForwardHeadGain (rho : ℂ)‖ ^ 2 +
        (Real.log 2) ^ 2 * ‖burnolCartierCosineHeadGain (rho : ℂ)‖ ^ 2 := by
  rw [burnolSoninGammaHeadEnergy,
    xiDivisor_burnolSoninForwardHeadCoefficient_cartierZeroTransfer rho h,
    xiDivisor_burnolSoninCosineHeadCoefficient_cartierZeroTransfer rho h,
    norm_neg, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos one_lt_two)]
  ring

/-! ## Reciprocal-polarization rigidity -/

/-- **Strict two-head amplification.**  Every hypothetical right-half Xi divisor makes the
Cartier zero-transfer strictly increase the fixed, unweighted sum of forward and cosine aperture
head energies.  This isolates exactly what ambient `L²` isometry moves into and out of the tails. -/
theorem xiDivisor_burnolCartierZeroTransfer_strictly_amplifies_gammaHeadEnergy
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom <
      burnolSoninGammaHeadEnergy (1 / 2)
        (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) := by
  rw [burnolSoninGammaHeadEnergy_fixedSubWindowSourceAtom,
    xiDivisor_burnolSoninGammaHeadEnergy_cartierZeroTransfer rho h]
  let x : ℝ := ‖burnolCartierForwardHeadGain (rho : ℂ)‖
  let y : ℝ := ‖burnolCartierCosineHeadGain (rho : ℂ)‖
  let L : ℝ := Real.log 2
  have hx : 1 < x := by
    exact one_lt_norm_burnolCartierForwardHeadGain h
      (xiDivisor_re_lt_one_of_half_lt rho h)
  have hy : y < 1 := by
    exact norm_burnolCartierCosineHeadGain_lt_one h
      (xiDivisor_re_lt_one_of_half_lt rho h)
  have hxy : y * x = 1 := by
    exact norm_burnolCartierCosineHeadGain_mul_forward_eq_one h
      (xiDivisor_re_lt_one_of_half_lt rho h)
  have hy0 : 0 ≤ y := norm_nonneg _
  have hyne : y ≠ 0 := by
    intro hyz
    rw [hyz, zero_mul] at hxy
    norm_num at hxy
  have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hyne)
  have hLpos : 0 < L := Real.log_pos one_lt_two
  have hLlt : L < 1 := by
    dsimp [L]
    linarith [Real.log_two_lt_d9]
  have hLsq : L ^ 2 < 1 := by nlinarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  have hweighted : L ^ 2 * y ^ 2 < 1 := by
    calc
      L ^ 2 * y ^ 2 < 1 * y ^ 2 :=
        mul_lt_mul_of_pos_right hLsq (sq_pos_of_pos hypos)
      _ = y ^ 2 := one_mul _
      _ < 1 := hy2
  have hsqprod : y ^ 2 * x ^ 2 = 1 := by
    calc
      y ^ 2 * x ^ 2 = (y * x) ^ 2 := by ring
      _ = 1 := by rw [hxy]; norm_num
  have hyrel : y ^ 2 - 1 = -y ^ 2 * (x ^ 2 - 1) := by
    calc
      y ^ 2 - 1 = y ^ 2 - y ^ 2 * x ^ 2 := by rw [hsqprod]
      _ = -y ^ 2 * (x ^ 2 - 1) := by ring
  have hfactor :
      x ^ 2 + L ^ 2 * y ^ 2 - (1 + L ^ 2) =
        (x ^ 2 - 1) * (1 - L ^ 2 * y ^ 2) := by
    calc
      x ^ 2 + L ^ 2 * y ^ 2 - (1 + L ^ 2) =
          (x ^ 2 - 1) + L ^ 2 * (y ^ 2 - 1) := by ring
      _ = (x ^ 2 - 1) * (1 - L ^ 2 * y ^ 2) := by rw [hyrel]; ring
  have hpos : 0 < (x ^ 2 - 1) * (1 - L ^ 2 * y ^ 2) :=
    mul_pos (by nlinarith) (sub_pos.mpr hweighted)
  change 1 + L ^ 2 < x ^ 2 + L ^ 2 * y ^ 2
  nlinarith

/-! ## Smaller source producer and Route R endpoint -/

/-- Source-native producer now sufficient for Route R: the pre-divisor Stokes comparison need
only make the fixed two-Gamma-head positive reading non-amplifying.  It need not preserve either
head separately and need not identify a full physical metric. -/
def BurnolXiCartierZeroTransferGammaHeadEnergyNonamplification : Prop :=
  ∀ (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re),
    burnolSoninGammaHeadEnergy (1 / 2)
        (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom) ≤
      burnolSoninGammaHeadEnergy (1 / 2) burnolFixedSubWindowSourceAtom

/-- Two-head source non-amplification derives the formerly missing separate forward-head norm
conservation. -/
theorem burnolXiCartierZeroTransferForwardHeadNormConservation_of_gammaHeadEnergyNonamplification
    (hnonamp : BurnolXiCartierZeroTransferGammaHeadEnergyNonamplification) :
    BurnolXiCartierZeroTransferForwardHeadNormConservation := by
  intro rho h
  exact False.elim ((not_lt_of_ge (hnonamp rho h))
    (xiDivisor_burnolCartierZeroTransfer_strictly_amplifies_gammaHeadEnergy rho h))

/-- Route R closes from the fixed two-Gamma-head Stokes contraction. -/
theorem riemannHypothesis_of_burnolXiCartierZeroTransferGammaHeadEnergyNonamplification
    (hnonamp : BurnolXiCartierZeroTransferGammaHeadEnergyNonamplification) :
    RiemannHypothesis :=
  riemannHypothesis_of_burnolXiCartierZeroTransferForwardHeadNormConservation
    (burnolXiCartierZeroTransferForwardHeadNormConservation_of_gammaHeadEnergyNonamplification
      hnonamp)

end RHTower
