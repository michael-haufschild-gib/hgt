import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCanonicalSchwarzTransportExtinctionClassification

/-!
# Literal-source FE cocycle and fixed-Peierls rigidity

The literal unit-seed Birmingham--Mokhtari source determines a canonical anti-linear
functional-equation transport on each Xi basis fibre.  Its scalar is normalized to `1` at source
extinction and otherwise is the reflected source divided by the conjugate source.

This transport is source-faithful, uniquely so away from the critical wall, and is an involution
without assuming RH.  The transported pairing is therefore not the missing input.  The hard
distinction is the original, untransported complex-bilinear Peierls pairing: preserving that fixed
pairing requires the cocycle square to be `1`.  The two possible signs reduce to conjugate cubic
carrier equations.  One factors through the centered real coordinate; the other contradicts
nonzero Xi height.  Fixed-pairing compatibility is consequently equivalent to critical-line
support on each fibre and equivalent to RH globally.

Thus source-derived FE transport exists unconditionally, while identifying its transported
Peierls form with the fixed physical form is exactly the remaining Ward/RH producer burden.

`[NEW] [FE COCYCLE] [SOURCE-FAITHFUL] [FIXED-PAIRING RIGIDITY] [RH EQUIVALENCE]`
-/

open Complex

namespace RHTower

noncomputable section

private theorem unitSource_reflect_eq_zero_iff (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
        (xiZeroCopyReflectEquiv q) = 0 ↔
      d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0 := by
  rw [d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero,
    d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero,
    xiZeroCopyReflect_re_eq_one_sub]
  constructor <;> intro h <;> linarith

/-- Canonical unit-source scalar for anti-linear functional-equation transport. -/
def hbXiPeierlsUnitSourceFECocycle (q : XiZeroCopy) : ℂ :=
  if d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0 then 1
  else
    d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
        (xiZeroCopyReflectEquiv q) /
      (starRingEnd ℂ) (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)

/-- The canonical FE cocycle transports the literal unit source to its reflected copy. -/
theorem hbXiPeierlsUnitSourceFECocycle_sourceTransport (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFECocycle q *
        (starRingEnd ℂ) (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) =
      d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
        (xiZeroCopyReflectEquiv q) := by
  by_cases hq : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0
  · have hRq := unitSource_reflect_eq_zero_iff q |>.mpr hq
    simp [hbXiPeierlsUnitSourceFECocycle, hq, hRq]
  · rw [hbXiPeierlsUnitSourceFECocycle, if_neg hq]
    exact div_mul_cancel₀ _ ((map_ne_zero (starRingEnd ℂ)).mpr hq)

/-- Source compatibility is unique off wall and unconstrained only at source extinction. -/
theorem hbXiPeierlsUnitSourceFE_compatible_iff
    (q : XiZeroCopy) (kappa : ℂ) :
    kappa * (starRingEnd ℂ)
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) =
          d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
            (xiZeroCopyReflectEquiv q) ↔
      (q.1 : ℂ).re = 1 / 2 ∨
        kappa = hbXiPeierlsUnitSourceFECocycle q := by
  by_cases hline : (q.1 : ℂ).re = 1 / 2
  · have hq :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hline
    have hRq := unitSource_reflect_eq_zero_iff q |>.mpr hq
    simp [hline, hq, hRq]
  · have hq : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q ≠ 0 :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).not.mpr hline
    constructor
    · intro h
      right
      rw [hbXiPeierlsUnitSourceFECocycle, if_neg hq]
      apply (mul_right_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hq))
      rw [div_mul_cancel₀ _ ((map_ne_zero (starRingEnd ℂ)).mpr hq)]
      exact h
    · rintro (h | h)
      · exact False.elim (hline h)
      · rw [h]
        exact hbXiPeierlsUnitSourceFECocycle_sourceTransport q

/-- The source-derived anti-linear FE scalar is a genuine reflection cocycle. -/
theorem hbXiPeierlsUnitSourceFECocycle_involutive (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
        (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) = 1 := by
  by_cases hq : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0
  · have hRq := unitSource_reflect_eq_zero_iff q |>.mpr hq
    simp [hbXiPeierlsUnitSourceFECocycle, hq, hRq]
  · have hRq : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
        (xiZeroCopyReflectEquiv q) ≠ 0 :=
      (unitSource_reflect_eq_zero_iff q).not.mpr hq
    rw [hbXiPeierlsUnitSourceFECocycle, if_neg hRq,
      hbXiPeierlsUnitSourceFECocycle, if_neg hq,
      xiZeroCopyReflectEquiv_apply_apply, map_div₀]
    have hcc :
        (starRingEnd ℂ) ((starRingEnd ℂ)
          (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)) =
        d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q := by simp
    rw [hcc]
    field_simp
    exact div_self ((map_ne_zero (starRingEnd ℂ)).mpr hRq)

private theorem star_mixing_eq_neg (q : XiZeroCopy) :
    (starRingEnd ℂ) (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) =
      -d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q := by
  rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq]
  simp

private theorem unitSource_reflection_eq_neg_conj_forces_criticalLine
    (q : XiZeroCopy)
    (hsource :
      d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
          (xiZeroCopyReflectEquiv q) =
        -(starRingEnd ℂ)
          (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hline
  have hmix : d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q ≠ 0 :=
    (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).not.mpr hline
  rw [d4BMXiSecondHarmonicPolarizedSourceAmplitude,
    d4BMXiSecondHarmonicPolarizedSourceAmplitude,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect,
    map_mul, star_mixing_eq_neg] at hsource
  have hcarrier :
      d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
        (starRingEnd ℂ)
          (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
            (xiSpectralPoint q)) := by
    apply mul_left_cancel₀ hmix
    simpa only [neg_neg, neg_mul] using hsource
  rw [d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq,
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq] at hcarrier
  have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) :=
    xiZeroReflectEquiv_apply q.1
  rw [href] at hcarrier
  simp only [one_pow, one_mul, map_mul, map_add, map_one, map_div₀,
    map_ofNat, map_pow] at hcarrier
  let s : ℂ := q.1
  let u : ℂ := 1 - s
  let v : ℂ := (starRingEnd ℂ) s
  have hpoly : (1 + u / 2) * (u / 2) ^ (2 : ℕ) =
      (1 + v / 2) * (v / 2) ^ (2 : ℕ) := by
    simpa [s, u, v] using hcarrier
  have hfactor :
      (u - v) * (u ^ (2 : ℕ) + u * v + v ^ (2 : ℕ) + 2 * (u + v)) = 0 := by
    linear_combination 8 * hpoly
  rcases mul_eq_zero.mp hfactor with huv | hquad
  · have hre := congrArg Complex.re huv
    simp [u, v, s] at hre
    exact hline (by linarith)
  · have him := congrArg Complex.im hquad
    norm_num [u, v, s, pow_two, Complex.mul_re, Complex.mul_im] at him
    have hheight := xi_divisor_support_im_ne_zero q.1
    have hzero : (q.1 : ℂ).im = 0 := by nlinarith
    exact hheight hzero

private theorem unitSource_reflection_eq_conj_forces_criticalLine
    (q : XiZeroCopy)
    (hsource :
      d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
          (xiZeroCopyReflectEquiv q) =
        (starRingEnd ℂ)
          (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)) :
    (q.1 : ℂ).re = 1 / 2 := by
  by_contra hline
  have hmix : d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q ≠ 0 :=
    (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).not.mpr hline
  rw [d4BMXiSecondHarmonicPolarizedSourceAmplitude,
    d4BMXiSecondHarmonicPolarizedSourceAmplitude,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect,
    map_mul, star_mixing_eq_neg] at hsource
  have hcarrier :
      d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
        -(starRingEnd ℂ)
          (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
            (xiSpectralPoint q)) := by
    apply mul_left_cancel₀ hmix
    calc
      d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q *
          d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
            (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
          -d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q *
            (starRingEnd ℂ)
              (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
                (xiSpectralPoint q)) := hsource
      _ = d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q *
          -(starRingEnd ℂ)
            (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
              (xiSpectralPoint q)) := by ring
  rw [d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq,
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq] at hcarrier
  have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) :=
    xiZeroReflectEquiv_apply q.1
  rw [href] at hcarrier
  simp only [one_pow, one_mul, map_mul, map_add, map_one, map_div₀,
    map_ofNat, map_pow] at hcarrier
  let s : ℂ := q.1
  let u : ℂ := 1 - s
  let v : ℂ := (starRingEnd ℂ) s
  have hpoly : (1 + u / 2) * (u / 2) ^ (2 : ℕ) =
      -((1 + v / 2) * (v / 2) ^ (2 : ℕ)) := by
    simpa [s, u, v] using hcarrier
  have hre := congrArg Complex.re hpoly
  have him := congrArg Complex.im hpoly
  norm_num [u, v, s, pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have hheight := xi_divisor_support_im_ne_zero q.1
  have himfactor :
      (q.1 : ℂ).im *
          (2 * (q.1 : ℂ).im ^ (2 : ℕ) - 6 * (q.1 : ℂ).re ^ (2 : ℕ) +
            6 * (q.1 : ℂ).re - 7) = 0 := by
    nlinarith
  have himcore :
      2 * (q.1 : ℂ).im ^ (2 : ℕ) - 6 * (q.1 : ℂ).re ^ (2 : ℕ) +
          6 * (q.1 : ℂ).re - 7 = 0 :=
    (mul_eq_zero.mp himfactor).resolve_left hheight
  nlinarith [sq_nonneg ((q.1 : ℂ).re - 1 / 2)]

/-- Fixed bilinear-pairing isometry of the source FE cocycle occurs exactly on critical wall. -/
theorem hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFECocycle q ^ (2 : ℕ) = 1 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hsquare
    have hfactor :
        (hbXiPeierlsUnitSourceFECocycle q - 1) *
            (hbXiPeierlsUnitSourceFECocycle q + 1) = 0 := by
      linear_combination hsquare
    rcases mul_eq_zero.mp hfactor with hplus | hminus
    · have hkappa : hbXiPeierlsUnitSourceFECocycle q = 1 := sub_eq_zero.mp hplus
      have htransport := hbXiPeierlsUnitSourceFECocycle_sourceTransport q
      rw [hkappa, one_mul] at htransport
      exact unitSource_reflection_eq_conj_forces_criticalLine q htransport.symm
    · have hkappa : hbXiPeierlsUnitSourceFECocycle q = -1 := by
        exact eq_neg_of_add_eq_zero_left hminus
      have htransport := hbXiPeierlsUnitSourceFECocycle_sourceTransport q
      rw [hkappa, neg_mul, one_mul] at htransport
      exact unitSource_reflection_eq_neg_conj_forces_criticalLine q htransport.symm
  · intro hline
    have hsource :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hline
    simp [hbXiPeierlsUnitSourceFECocycle, hsource]

/-- Anti-linear FE transport of one Xi basis coefficient. -/
def hbXiPeierlsUnitSourceFEBasisTransport
    (q : XiZeroCopy) (c : ℂ) : HBXiPeierlsPacket :=
  Finsupp.single (xiZeroCopyReflectEquiv q)
    (hbXiPeierlsUnitSourceFECocycle q * (starRingEnd ℂ) c)

/-- Basis transport carries the literal unit source coefficient to its reflected source. -/
theorem hbXiPeierlsUnitSourceFEBasisTransport_source (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFEBasisTransport q
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) =
      Finsupp.single (xiZeroCopyReflectEquiv q)
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
          (xiZeroCopyReflectEquiv q)) := by
  rw [hbXiPeierlsUnitSourceFEBasisTransport,
    hbXiPeierlsUnitSourceFECocycle_sourceTransport]

/-- The source FE basis transport is an anti-linear involution. -/
theorem hbXiPeierlsUnitSourceFEBasisTransport_involutive
    (q : XiZeroCopy) (c : ℂ) :
    hbXiPeierlsUnitSourceFEBasisTransport (xiZeroCopyReflectEquiv q)
        (hbXiPeierlsUnitSourceFECocycle q * (starRingEnd ℂ) c) =
      Finsupp.single q c := by
  classical
  rw [hbXiPeierlsUnitSourceFEBasisTransport,
    xiZeroCopyReflectEquiv_apply_apply, map_mul]
  have hcc : (starRingEnd ℂ) ((starRingEnd ℂ) c) = c := by simp
  rw [hcc, ← mul_assoc, hbXiPeierlsUnitSourceFECocycle_involutive, one_mul]

/-- Actual fixed Peierls basis pairing is preserved exactly on critical wall. -/
theorem hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff
    (q : XiZeroCopy) :
    hbXiPeierlsDot (hbXiPeierlsUnitSourceFEBasisTransport q 1)
        (hbXiPeierlsUnitSourceFEBasisTransport q 1) =
          (starRingEnd ℂ)
            (hbXiPeierlsDot (Finsupp.single q 1) (Finsupp.single q 1)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  classical
  rw [hbXiPeierlsUnitSourceFEBasisTransport, hbXiPeierlsDot_single,
    hbXiPeierlsDot_single]
  simp only [map_one, mul_one, Finsupp.single_eq_same]
  simpa only [pow_two] using hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff q

/-- Universal source-FE fixed-pairing compatibility is exactly RH. -/
theorem forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh :
    (∀ q : XiZeroCopy,
      hbXiPeierlsDot (hbXiPeierlsUnitSourceFEBasisTransport q 1)
          (hbXiPeierlsUnitSourceFEBasisTransport q 1) =
        (starRingEnd ℂ)
          (hbXiPeierlsDot (Finsupp.single q 1) (Finsupp.single q 1))) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis
      0).mp
    intro q
    apply (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff 0 q).mpr
    exact (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp (h q)
  · intro hRH q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    have hselector :=
      (forall_d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff_riemannHypothesis
        0).mpr hRH q
    exact (d4BMXiPlusPlusCanonicalPhysicalHorizonSelector_eq_zero_iff 0 q).mp hselector

end

end RHTower
