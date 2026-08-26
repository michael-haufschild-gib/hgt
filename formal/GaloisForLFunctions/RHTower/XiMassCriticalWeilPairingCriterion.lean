import GaloisForLFunctions.RHTower.XiMassCriticalHalfDensityWeilPairing
import GaloisForLFunctions.RHTower.XiMassSharpSpacelikeConeSummability
import GaloisForLFunctions.RHTower.XiMassCriticalIntegerFace

/-!
# Fixed critical Weil-source pairing criterion

The finite Route T cone is only a localization device.  This module proves that its complement in
the complete critical half-density Weil pairing is uniformly bounded in vertical height.  Hence
the moving cutoff can be removed completely: RH is equivalent to boundedness of one fixed locally
finite source measure tested against the mass cross orbit.

The key point is geometric.  The rounded cutoff has slope `d/(d-1/2)`, strictly larger than the
horizontal-strip limiting slope and therefore larger than the sharp curved-contour slope.  Every
atom beyond the cutoff lies in one fixed absolutely summable spacelike cone.
-/

open Complex Real MeasureTheory

namespace RHTower

noncomputable section

/-- Natural-number parametrization of all integers `n ≥ 2`. -/
def natEquivDeningerPrimePowerIndex : ℕ ≃ DeningerPrimePowerIndex where
  toFun k := ⟨k + 2, by omega⟩
  invFun n := (n : ℕ) - 2
  left_inv k := by simp
  right_inv n := by
    apply Subtype.ext
    exact Nat.sub_add_cancel n.property

/-- Positive-time critical prime atom in the shifted natural-number coordinate `n=k+2`. -/
def xiMassCriticalHalfDensityPrimeAtomNat
    (a sigma u : ℝ) (k : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt (k + 2) : ℝ) : ℂ) *
    xiMassCriticalDampedFourierProfile a sigma u (Real.log ((k : ℝ) + 2))

/-- The measure-theoretic atom and the damped Route T atom are literally the same coefficient. -/
theorem xiMassCriticalHalfDensityCrossAtom_equiv_eq_primeAtomNat
    (a sigma u : ℝ) (k : ℕ) :
    xiMassCriticalHalfDensityCrossAtom a sigma u
        (natEquivDeningerPrimePowerIndex k) =
      xiMassCriticalHalfDensityPrimeAtomNat a sigma u k := by
  have hx : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hpow : ((k : ℝ) + 2) ^ (-1 / 2 : ℝ) =
      Real.exp (-Real.log ((k : ℝ) + 2) / 2) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring_nf
  have hweight : criticalMellinAtomWeight (k + 2) =
      ArithmeticFunction.vonMangoldt (k + 2) *
        Real.exp (-Real.log ((k : ℝ) + 2) / 2) := by
    rw [criticalMellinAtomWeight]
    push_cast
    rw [hpow]
    ring
  simp only [xiMassCriticalHalfDensityCrossAtom,
    xiMassCriticalHalfDensityPrimeAtomNat,
    natEquivDeningerPrimePowerIndex, Equiv.coe_fn_mk,
    deningerPrimePowerTime, Nat.cast_add, Nat.cast_ofNat]
  rw [hweight, xiMassCriticalDampedFourierProfile,
    xiMassSpectralCrossProfile_eq_stripFourier]
  push_cast
  ring

/-- The full source pairing is the shifted natural-number prime-atom series. -/
theorem xiMassCriticalHalfDensityCrossSeries_eq_tsum_primeAtomNat
    (a sigma u : ℝ) :
    xiMassCriticalHalfDensityCrossSeries a sigma u =
      ∑' k : ℕ, xiMassCriticalHalfDensityPrimeAtomNat a sigma u k := by
  rw [xiMassCriticalHalfDensityCrossSeries]
  calc
    (∑' n : DeningerPrimePowerIndex,
      xiMassCriticalHalfDensityCrossAtom a sigma u n) =
        ∑' k : ℕ, xiMassCriticalHalfDensityCrossAtom a sigma u
          (natEquivDeningerPrimePowerIndex k) := by
      symm
      exact Equiv.tsum_eq natEquivDeningerPrimePowerIndex
        (xiMassCriticalHalfDensityCrossAtom a sigma u)
    _ = _ := tsum_congr fun k =>
      xiMassCriticalHalfDensityCrossAtom_equiv_eq_primeAtomNat a sigma u k

theorem summable_norm_xiMassCriticalHalfDensityPrimeAtomNat
    {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) (u : ℝ) :
    Summable (fun k : ℕ =>
      ‖xiMassCriticalHalfDensityPrimeAtomNat a sigma u k‖) := by
  have h := summable_norm_xiMassCriticalHalfDensityCrossAtom ha hsigma u
  have he := h.comp_injective natEquivDeningerPrimePowerIndex.injective
  exact he.congr fun k => by
    change ‖xiMassCriticalHalfDensityCrossAtom a sigma u
      (natEquivDeningerPrimePowerIndex k)‖ = _
    rw [xiMassCriticalHalfDensityCrossAtom_equiv_eq_primeAtomNat]

/-- A prime atom in a fixed sharp spacelike cone is bounded by C33's coefficient-faithful
majorant. -/
theorem norm_xiMassCriticalHalfDensityPrimeAtomNat_le_majorant
    {a sigma alpha u : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hsharp : xiMassSpacelikeSharpSlope a < alpha) (hu : 0 ≤ u)
    (k : ℕ) (hcone : alpha * u ≤ Real.log ((k : ℝ) + 2)) :
    ‖xiMassCriticalHalfDensityPrimeAtomNat a sigma u k‖ ≤
      xiMassSharpSpacelikeCenteredMajorant a alpha k := by
  let x : ℝ := (k : ℝ) + 2
  let p : ℝ := xiMassSharpSpacelikeDirichletExponent a alpha
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have halpha : 1 < alpha :=
    (one_lt_xiMassSpacelikeSharpSlope ha).trans hsharp
  have hx : 0 < x := by dsimp only [x]; positivity
  have hlogTwo : Real.log 2 ≤ Real.log x := by
    apply Real.log_le_log (by norm_num)
    dsimp only [x]
    norm_num
  have hprofile := norm_xiMassCriticalDampedFourierProfile_le_sharpSpacelike
    ha hsigma hsharp hu hcone hlogTwo
  have hrpow : Real.exp (-(p * Real.log x)) = x ^ (-p) := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring_nf
  change ‖((ArithmeticFunction.vonMangoldt (k + 2) : ℝ) : ℂ) *
      xiMassCriticalDampedFourierProfile a sigma u (Real.log x)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  change ArithmeticFunction.vonMangoldt (k + 2) *
      ‖xiMassCriticalDampedFourierProfile a sigma u (Real.log x)‖ ≤
    xiMassSharpSpacelikeProfileConstant a alpha *
      ((ArithmeticFunction.vonMangoldt (k + 2) + 1) * x ^ (-p))
  rw [hrpow] at hprofile
  have hLambda := ArithmeticFunction.vonMangoldt_nonneg (n := k + 2)
  have hC := xiMassSharpSpacelikeProfileConstant_nonneg ha0 halpha
  have hpow : 0 ≤ x ^ (-p) := Real.rpow_nonneg hx.le _
  calc
    ArithmeticFunction.vonMangoldt (k + 2) *
        ‖xiMassCriticalDampedFourierProfile a sigma u (Real.log x)‖ ≤
      ArithmeticFunction.vonMangoldt (k + 2) *
        (xiMassSharpSpacelikeProfileConstant a alpha * x ^ (-p)) :=
      mul_le_mul_of_nonneg_left hprofile hLambda
    _ ≤ (ArithmeticFunction.vonMangoldt (k + 2) + 1) *
        (xiMassSharpSpacelikeProfileConstant a alpha * x ^ (-p)) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hC hpow)
    _ = xiMassSharpSpacelikeProfileConstant a alpha *
        ((ArithmeticFunction.vonMangoldt (k + 2) + 1) * x ^ (-p)) := by ring

/-- Every atom after the rounded Route T cutoff lies in the fixed cone given by the horizontal
limiting slope. -/
theorem xiMassPrimeAtomNat_after_cutoff_mem_horizontalSpacelikeCone
    {a d u : ℝ} (ha : 1 / 2 < a) (hdhalf : 1 / 2 < d)
    (hda : d < a) (hu : 0 ≤ u) (i : ℕ) :
    let H := d * u / (d - 1 / 2)
    let M := ⌊Real.exp H⌋₊
    xiMassHorizontalStripLimitingSlope a * u ≤
      Real.log ((((i + (M - 1) : ℕ) : ℝ) + 2)) := by
  let H : ℝ := d * u / (d - 1 / 2)
  let M : ℕ := ⌊Real.exp H⌋₊
  have hdDen : 0 < d - 1 / 2 := sub_pos.mpr hdhalf
  have haDen : 0 < a - 1 / 2 := sub_pos.mpr ha
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity
  have hMone : 1 ≤ M := by
    apply Nat.le_floor
    simpa only [Nat.cast_one, ← Real.exp_zero] using Real.exp_le_exp.mpr hH0
  have hupper : Real.exp H < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hslope : xiMassHorizontalStripLimitingSlope a < d / (d - 1 / 2) := by
    rw [xiMassHorizontalStripLimitingSlope,
      div_lt_div_iff₀ haDen hdDen]
    nlinarith
  have hslopeH : xiMassHorizontalStripLimitingSlope a * u ≤ H := by
    have hmul := mul_le_mul_of_nonneg_right hslope.le hu
    dsimp only [H]
    simpa only [div_mul_eq_mul_div] using hmul
  have hindex : ((((i + (M - 1) : ℕ) : ℕ) : ℝ) + 2) =
      (i : ℝ) + (M : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hMone]
    push_cast
    ring
  have hxLower : (M : ℝ) + 1 ≤ (i : ℝ) + (M : ℝ) + 1 := by
    have hi : 0 ≤ (i : ℝ) := by positivity
    linarith
  have hlog : H < Real.log ((i : ℝ) + (M : ℝ) + 1) := by
    have h := Real.log_lt_log (Real.exp_pos H) (hupper.trans_le hxLower)
    simpa only [Real.log_exp] using h
  dsimp only
  rw [hindex]
  exact hslopeH.trans hlog.le

/-- Complete source pairing differs from the moving prime cone by one uniformly bounded spacelike
tail. -/
theorem norm_xiMassCriticalHalfDensityWeilPairing_sub_primeAtomConeSum_le
    {a sigma d u : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hdhalf : 1 / 2 < d) (hda : d < a) (hu : 0 ≤ u) :
    ‖xiMassCriticalHalfDensityWeilPairing a sigma u -
        xiMassCriticalPrimeAtomConeSum a sigma d u‖ ≤
      ∑' k : ℕ, xiMassSharpSpacelikeCenteredMajorant a
        (xiMassHorizontalStripLimitingSlope a) k := by
  let alpha := xiMassHorizontalStripLimitingSlope a
  let H := d * u / (d - 1 / 2)
  let M := ⌊Real.exp H⌋₊
  let N := M - 1
  let f : ℕ → ℂ := xiMassCriticalHalfDensityPrimeAtomNat a sigma u
  let g : ℕ → ℝ := xiMassSharpSpacelikeCenteredMajorant a alpha
  have hsharp : xiMassSpacelikeSharpSlope a < alpha := by
    simpa only [alpha] using
      xiMassSpacelikeSharpSlope_lt_horizontalStripLimitingSlope ha
  have hfNorm := summable_norm_xiMassCriticalHalfDensityPrimeAtomNat ha hsigma u
  have hf : Summable f := hfNorm.of_norm
  have hadd : Function.Injective (fun i : ℕ => i + N) := by
    intro i j hij
    exact Nat.add_right_cancel hij
  have hg : Summable g := by
    simpa only [g, alpha] using
      summable_xiMassSharpSpacelikeCenteredMajorant ha hsharp
  have hdecomp := hf.sum_add_tsum_nat_add N
  have hpair : xiMassCriticalHalfDensityWeilPairing a sigma u = ∑' k, f k := by
    rw [xiMassCriticalHalfDensityWeilPairing_eq_crossSeries ha hsigma,
      xiMassCriticalHalfDensityCrossSeries_eq_tsum_primeAtomNat]
  have hfinite : xiMassCriticalPrimeAtomConeSum a sigma d u =
      ∑ k ∈ Finset.range N, f k := by
    rfl
  have htail : xiMassCriticalHalfDensityWeilPairing a sigma u -
      xiMassCriticalPrimeAtomConeSum a sigma d u =
        ∑' i : ℕ, f (i + N) := by
    rw [hpair, hfinite]
    rw [← hdecomp]
    ring
  rw [htail]
  calc
    ‖∑' i : ℕ, f (i + N)‖ ≤ ∑' i : ℕ, ‖f (i + N)‖ :=
      norm_tsum_le_tsum_norm (hfNorm.comp_injective hadd)
    _ ≤ ∑' i : ℕ, g (i + N) := by
      apply Summable.tsum_le_tsum
      · intro i
        dsimp only [f, g, alpha, N, M, H]
        apply norm_xiMassCriticalHalfDensityPrimeAtomNat_le_majorant
          ha hsigma hsharp hu
        exact xiMassPrimeAtomNat_after_cutoff_mem_horizontalSpacelikeCone
          ha hdhalf hda hu i
      · exact hfNorm.comp_injective hadd
      · exact hg.comp_injective hadd
    _ ≤ ∑' k : ℕ, g k := by
      have hsplit := hg.sum_add_tsum_nat_add N
      have hhead : 0 ≤ ∑ k ∈ Finset.range N, g k := by
        exact Finset.sum_nonneg fun k _ =>
          xiMassSharpSpacelikeCenteredMajorant_nonneg
            (lt_trans (by norm_num) ha)
            ((one_lt_xiMassSpacelikeSharpSlope ha).trans hsharp) k
      linarith
    _ = ∑' k : ℕ, xiMassSharpSpacelikeCenteredMajorant a
        (xiMassHorizontalStripLimitingSlope a) k := rfl

/-- Height-uniform boundedness of the fixed critical Weil-source mass orbit. -/
def XiMassCriticalHalfDensityWeilPairingLineBound (a sigma : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassCriticalHalfDensityWeilPairing a sigma u‖ ≤ C

theorem xiMassCriticalHalfDensityWeilPairingLineBound_iff_primeAtomCone
    {a sigma d : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hdhalf : 1 / 2 < d) (hda : d < a) :
    XiMassCriticalHalfDensityWeilPairingLineBound a sigma ↔
      XiMassCriticalPrimeAtomConeLineBound a sigma d := by
  let B := ∑' k : ℕ, xiMassSharpSpacelikeCenteredMajorant a
    (xiMassHorizontalStripLimitingSlope a) k
  have htail : ∀ u : ℝ, 0 ≤ u →
      ‖xiMassCriticalHalfDensityWeilPairing a sigma u -
          xiMassCriticalPrimeAtomConeSum a sigma d u‖ ≤ B :=
    fun u hu => norm_xiMassCriticalHalfDensityWeilPairing_sub_primeAtomConeSum_le
      ha hsigma hdhalf hda hu
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    have hsolve : xiMassCriticalPrimeAtomConeSum a sigma d u =
        xiMassCriticalHalfDensityWeilPairing a sigma u -
          (xiMassCriticalHalfDensityWeilPairing a sigma u -
            xiMassCriticalPrimeAtomConeSum a sigma d u) := by ring
    rw [hsolve]
    exact (norm_sub_le _ _).trans (add_le_add (hC u hu) (htail u hu))
  · rintro ⟨C, hC⟩
    refine ⟨C + B, fun u hu => ?_⟩
    have hsolve : xiMassCriticalHalfDensityWeilPairing a sigma u =
        xiMassCriticalPrimeAtomConeSum a sigma d u +
          (xiMassCriticalHalfDensityWeilPairing a sigma u -
            xiMassCriticalPrimeAtomConeSum a sigma d u) := by ring
    rw [hsolve]
    exact (norm_add_le _ _).trans (add_le_add (hC u hu) (htail u hu))

/-- **C38 capstone.**  RH is equivalent to uniform boundedness of one fixed unsquared critical
Weil measure paired with the non-diagonal mass cross orbit.  No moving cutoff remains. -/
theorem riemannHypothesis_iff_xiMassCriticalHalfDensityWeilPairingLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔ XiMassCriticalHalfDensityWeilPairingLineBound a sigma := by
  exact (riemannHypothesis_iff_xiMassCriticalPrimeAtomConeLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassCriticalHalfDensityWeilPairingLineBound_iff_primeAtomCone
        (lt_trans hhalf hca) hsigma hdhalf hda).symm

/-! ## Eventual fixed-source criterion -/

/-- One critical half-density source atom has an explicit absolute majorant after shifting to any
strict interior line.  This is used only on compact height intervals; the exponential factor is
not a candidate for the remaining high-height cancellation. -/
theorem norm_xiMassCriticalHalfDensityCrossAtom_le_exp_majorant
    {a sigma d : ℝ} (hd0 : 0 ≤ d) (hda : d < a) (hsigma : 0 < sigma)
    (u : ℝ) (n : DeningerPrimePowerIndex) :
    ‖xiMassCriticalHalfDensityCrossAtom a sigma u n‖ ≤
      (Real.exp (|u| * d) * ∫ x : ℝ, Real.exp (-(sigma * |x|))) *
        (ArithmeticFunction.vonMangoldt (n : ℕ) *
          ((n : ℕ) : ℝ) ^ (-(1 / 2 + d))) := by
  have hnPos : (0 : ℝ) < (n : ℕ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_two n.property
  have hF := norm_stripFourier_xiMass_deepShift_le
    (a := a) (σ := sigma) (d := d) hd0 hda hsigma u
      (deningerPrimePowerTime n)
  have hF' :
      ‖xiMassSpectralCrossProfile a sigma u (deningerPrimePowerTime n)‖ ≤
        Real.exp (|u| * d) * ((n : ℕ) : ℝ) ^ (-d) *
          ∫ x : ℝ, Real.exp (-(sigma * |x|)) := by
    rw [← xiMassSpectralCrossProfile_eq_stripFourier] at hF
    have hexp :
        Real.exp (|u| * d - deningerPrimePowerTime n * d) =
          Real.exp (|u| * d) * ((n : ℕ) : ℝ) ^ (-d) := by
      rw [deningerPrimePowerTime, Real.rpow_def_of_pos hnPos, ← Real.exp_add]
      congr 1
      ring_nf
    simpa only [hexp, mul_assoc] using hF
  have hweight :
      criticalMellinAtomWeight (n : ℕ) =
        ArithmeticFunction.vonMangoldt (n : ℕ) *
          ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [criticalMellinAtomWeight]
    ring_nf
  rw [xiMassCriticalHalfDensityCrossAtom, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, hweight,
    abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg hnPos.le _))]
  have hpowHalf : 0 ≤ ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hnPos.le _
  have hLambda : 0 ≤ ArithmeticFunction.vonMangoldt (n : ℕ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hmul := mul_le_mul_of_nonneg_left hF'
    (mul_nonneg hLambda hpowHalf)
  calc
    ArithmeticFunction.vonMangoldt (n : ℕ) * ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        ‖xiMassSpectralCrossProfile a sigma u (deningerPrimePowerTime n)‖ ≤
      ArithmeticFunction.vonMangoldt (n : ℕ) * ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (|u| * d) * ((n : ℕ) : ℝ) ^ (-d) *
          ∫ x : ℝ, Real.exp (-(sigma * |x|))) := hmul
    _ = (Real.exp (|u| * d) * ∫ x : ℝ, Real.exp (-(sigma * |x|))) *
        (ArithmeticFunction.vonMangoldt (n : ℕ) *
          (((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℕ) : ℝ) ^ (-d))) := by
      ring
    _ = (Real.exp (|u| * d) * ∫ x : ℝ, Real.exp (-(sigma * |x|))) *
        (ArithmeticFunction.vonMangoldt (n : ℕ) *
          ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) + -d)) := by
      rw [Real.rpow_add hnPos]
    _ = (Real.exp (|u| * d) * ∫ x : ℝ, Real.exp (-(sigma * |x|))) *
        (ArithmeticFunction.vonMangoldt (n : ℕ) *
          ((n : ℕ) : ℝ) ^ (-(1 / 2 + d))) := by
      congr 3
      ring

/-- Explicit absolute majorant for the complete fixed-source pairing at one height.  Its arithmetic
series lies strictly to the right of the von Mangoldt absolute-convergence abscissa. -/
theorem norm_xiMassCriticalHalfDensityWeilPairing_le_exp_majorant
    {a sigma d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma)
    (u : ℝ) :
    ‖xiMassCriticalHalfDensityWeilPairing a sigma u‖ ≤
      (Real.exp (|u| * d) * ∫ x : ℝ, Real.exp (-(sigma * |x|))) *
        ∑' n : DeningerPrimePowerIndex,
          ArithmeticFunction.vonMangoldt (n : ℕ) *
            ((n : ℕ) : ℝ) ^ (-(1 / 2 + d)) := by
  let base : DeningerPrimePowerIndex → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt (n : ℕ) *
      ((n : ℕ) : ℝ) ^ (-(1 / 2 + d))
  let K : ℝ := Real.exp (|u| * d) * ∫ x : ℝ, Real.exp (-(sigma * |x|))
  have ha : 1 / 2 < a := hdhalf.trans hda
  have hp : 1 < 1 / 2 + d := by linarith
  have hbaseNat : Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 / 2 + d))) :=
    summable_vonMangoldt_mul_rpow hp
  have hbase : Summable base := by
    exact hbaseNat.subtype {n : ℕ | 2 ≤ n}
  have hmajorant : Summable (fun n => K * base n) := hbase.mul_left K
  have hnorm := summable_norm_xiMassCriticalHalfDensityCrossAtom ha hsigma u
  rw [xiMassCriticalHalfDensityWeilPairing_eq_crossSeries ha hsigma,
    xiMassCriticalHalfDensityCrossSeries]
  calc
    ‖∑' n : DeningerPrimePowerIndex,
        xiMassCriticalHalfDensityCrossAtom a sigma u n‖ ≤
      ∑' n : DeningerPrimePowerIndex,
        ‖xiMassCriticalHalfDensityCrossAtom a sigma u n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : DeningerPrimePowerIndex, K * base n := by
      apply Summable.tsum_le_tsum
      · intro n
        simpa only [K, base] using
          norm_xiMassCriticalHalfDensityCrossAtom_le_exp_majorant
            (a := a) (sigma := sigma) (d := d) (by linarith) hda hsigma u n
      · exact hnorm
      · exact hmajorant
    _ = K * ∑' n : DeningerPrimePowerIndex, base n := tsum_mul_left
    _ = _ := rfl

/-- Eventual height-uniform boundedness of the fixed critical Weil-source orbit. -/
def XiMassCriticalHalfDensityWeilPairingTailBound (a sigma : ℝ) : Prop :=
  ∃ U C : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u →
    ‖xiMassCriticalHalfDensityWeilPairing a sigma u‖ ≤ C

/-- Finite heights cost nothing: full nonnegative-line boundedness is equivalent to one uniform
bound beyond an unspecified nonnegative height. -/
theorem xiMassCriticalHalfDensityWeilPairingLineBound_iff_tailBound
    {a sigma d : ℝ} (hdhalf : 1 / 2 < d) (hda : d < a) (hsigma : 0 < sigma) :
    XiMassCriticalHalfDensityWeilPairingLineBound a sigma ↔
      XiMassCriticalHalfDensityWeilPairingTailBound a sigma := by
  let base : DeningerPrimePowerIndex → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt (n : ℕ) *
      ((n : ℕ) : ℝ) ^ (-(1 / 2 + d))
  let J : ℝ := ∫ x : ℝ, Real.exp (-(sigma * |x|))
  let S : ℝ := ∑' n : DeningerPrimePowerIndex, base n
  have hd0 : 0 ≤ d := by linarith
  have hJ : 0 ≤ J := integral_nonneg fun _ => Real.exp_nonneg _
  have hbaseNonneg : ∀ n, 0 ≤ base n := fun n => by
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (by positivity) _)
  have hS : 0 ≤ S := tsum_nonneg hbaseNonneg
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨0, C, le_rfl, fun u hu => hC u hu⟩
  · rintro ⟨U, C, hU, hC⟩
    let B : ℝ := Real.exp (U * d) * J * S
    refine ⟨max C B, fun u hu => ?_⟩
    by_cases htail : U ≤ u
    · exact (hC u htail).trans (le_max_left _ _)
    · have huU : u ≤ U := le_of_not_ge htail
      have hexp : Real.exp (|u| * d) ≤ Real.exp (U * d) := by
        rw [abs_of_nonneg hu]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right huU hd0)
      have hpoint := norm_xiMassCriticalHalfDensityWeilPairing_le_exp_majorant
        hdhalf hda hsigma u
      calc
        ‖xiMassCriticalHalfDensityWeilPairing a sigma u‖ ≤
            (Real.exp (|u| * d) * J) * S := by
          simpa only [J, S, base] using hpoint
        _ ≤ (Real.exp (U * d) * J) * S :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hexp hJ) hS
        _ = B := rfl
        _ ≤ max C B := le_max_right _ _

/-- **Eventual fixed-source exact open core.**  RH is equivalent to boundedness of the one fixed
critical half-density Weil-source pairing after some finite height.  No low-height, moving-cutoff,
Gamma, floor, or superluminal-tail premise remains. -/
theorem riemannHypothesis_iff_xiMassCriticalHalfDensityWeilPairingTailBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔
      XiMassCriticalHalfDensityWeilPairingTailBound a sigma := by
  exact (riemannHypothesis_iff_xiMassCriticalHalfDensityWeilPairingLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassCriticalHalfDensityWeilPairingLineBound_iff_tailBound
        hdhalf hda hsigma)

/-- Failure of RH forces genuine recurrent escape of the fixed source: after every height and above
every proposed ceiling, a later response exceeds that ceiling.  Thus no finite exceptional band can
carry the obstruction. -/
theorem not_riemannHypothesis_iff_xiMassCriticalHalfDensityWeilPairing_cofinally_unbounded
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    ¬ RiemannHypothesis ↔
      ∀ U C : ℝ, 0 ≤ U → ∃ u : ℝ, U ≤ u ∧
        C < ‖xiMassCriticalHalfDensityWeilPairing a sigma u‖ := by
  rw [riemannHypothesis_iff_xiMassCriticalHalfDensityWeilPairingTailBound
    hhalf hca hsigma hdhalf hda]
  constructor
  · intro hnot U C hU
    by_contra hex
    push Not at hex
    exact hnot ⟨U, C, hU, hex⟩
  · rintro hcofinal ⟨U, C, hU, hC⟩
    obtain ⟨u, hu, hgt⟩ := hcofinal U C hU
    exact (not_lt_of_ge (hC u hu)) hgt

end

end RHTower
