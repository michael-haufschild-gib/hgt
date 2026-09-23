import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFELineConjPermutationKernelNoGo

/-!
# Spectral-fibre locality rigidity for literal source-FE Peierls kernels

The literal BM source-FE cocycle descends from multiplicity copies to Xi divisor support.  Hence
reflection reality and the Ward law force every nonzero same-support coefficient onto the critical
line, even when a kernel mixes arbitrary multiplicity copies over that support.  Every tilted row
therefore vanishes and its basis packet lies in the left radical.

Consequently spectral-fibre locality plus trivial left radical closes HC54's arbitrary-kernel
loophole: full packet covariance is equivalent to RH.  The canonical line-conjugate survivor from
HC54 is spectrally local exactly under RH, proving that its unconditional nondegeneracy is genuinely
cross-spectral away from the wall.

`[NEW] [SPECTRAL LOCALITY] [MULTIPLICITY MIXING] [ROW EXTINCTION] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Literal BM unit source is constant across multiplicity copies over one Xi zero. -/
theorem d4BMXiSecondHarmonicUnitSource_eq_of_fst_eq
    {q r : XiZeroCopy} (hqr : q.1 = r.1) :
    d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q =
      d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 r := by
  have hspectral : xiSpectralPoint q = xiSpectralPoint r := by
    simp [xiSpectralPoint, hqr]
  rw [d4BMXiSecondHarmonicPolarizedSourceAmplitude,
    d4BMXiSecondHarmonicPolarizedSourceAmplitude,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq,
    hspectral]

/-- The normalized source-FE cocycle descends from multiplicity copies to Xi support. -/
theorem hbXiPeierlsUnitSourceFECocycle_eq_of_fst_eq
    {q r : XiZeroCopy} (hqr : q.1 = r.1) :
    hbXiPeierlsUnitSourceFECocycle q = hbXiPeierlsUnitSourceFECocycle r := by
  have hreflect : (xiZeroCopyReflectEquiv q).1 =
      (xiZeroCopyReflectEquiv r).1 := by
    simp only [xiZeroCopyReflectEquiv_fst]
    rw [hqr]
  rw [hbXiPeierlsUnitSourceFECocycle,
    hbXiPeierlsUnitSourceFECocycle,
    d4BMXiSecondHarmonicUnitSource_eq_of_fst_eq hqr,
    d4BMXiSecondHarmonicUnitSource_eq_of_fst_eq hreflect]

/-- A kernel is spectrally local when every nonzero coefficient stays inside one Xi support
fibre. Multiplicity copies inside that fibre may be mixed arbitrarily. -/
def HBXiPeierlsSpectralFibreLocalKernel
    (K : XiZeroCopy → XiZeroCopy → ℂ) : Prop :=
  ∀ q r : XiZeroCopy, K q r ≠ 0 → q.1 = r.1

/-- Any nonzero same-spectral-fibre coefficient of a reflection-real Ward kernel forces its row
onto the critical line. -/
theorem criticalLine_of_kernelWard_of_reflectionReal_of_spectralLocal_ne_zero
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hward : HBXiPeierlsUnitSourceFEKernelWard K)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (hlocal : HBXiPeierlsSpectralFibreLocalKernel K)
    (q r : XiZeroCopy) (hqr : K q r ≠ 0) :
    (q.1 : ℂ).re = 1 / 2 := by
  have hsupport : q.1 = r.1 := hlocal q r hqr
  have hcocycle := hbXiPeierlsUnitSourceFECocycle_eq_of_fst_eq hsupport
  have hW := hward q r
  rw [hreflect q r, ← hcocycle] at hW
  have hK : (starRingEnd ℂ) (K q r) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hqr
  have hsquare : hbXiPeierlsUnitSourceFECocycle q ^ (2 : ℕ) = 1 := by
    apply mul_left_cancel₀ hK
    simpa only [pow_two, mul_one, mul_assoc] using hW
  exact (hbXiPeierlsUnitSourceFECocycle_sq_eq_one_iff q).mp hsquare

/-- Every tilted row of a reflection-real, spectrally local Ward kernel vanishes identically. -/
theorem kernel_row_eq_zero_of_kernelWard_of_reflectionReal_of_spectralLocal_of_tilt
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hward : HBXiPeierlsUnitSourceFEKernelWard K)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (hlocal : HBXiPeierlsSpectralFibreLocalKernel K)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    ∀ r : XiZeroCopy, K q r = 0 := by
  intro r
  by_contra hqr
  exact htilt
    (criticalLine_of_kernelWard_of_reflectionReal_of_spectralLocal_ne_zero
      K hward hreflect hlocal q r hqr)

/-- A tilted basis packet lies in the left radical of every reflection-real, spectrally local
Ward form. -/
theorem hbXiPeierlsKernelForm_single_left_eq_zero_of_spectralLocal_of_tilt
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hward : HBXiPeierlsUnitSourceFEKernelWard K)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (hlocal : HBXiPeierlsSpectralFibreLocalKernel K)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2)
    (c : ℂ) (y : HBXiPeierlsPacket) :
    hbXiPeierlsKernelForm K (Finsupp.single q c) y = 0 := by
  classical
  have hrow :=
    kernel_row_eq_zero_of_kernelWard_of_reflectionReal_of_spectralLocal_of_tilt
      K hward hreflect hlocal q htilt
  simp [hbXiPeierlsKernelForm, hrow]

/-- Algebraic left nondegeneracy of a finite-packet kernel form. -/
def HBXiPeierlsKernelFormLeftNondegenerate
    (K : XiZeroCopy → XiZeroCopy → ℂ) : Prop :=
  ∀ x : HBXiPeierlsPacket,
    (∀ y : HBXiPeierlsPacket, hbXiPeierlsKernelForm K x y = 0) → x = 0

/-- HC54's canonical line-conjugate form is left nondegenerate. -/
theorem hbXiPeierlsLineConjPermutationKernelForm_leftNondegenerate :
    HBXiPeierlsKernelFormLeftNondegenerate
      hbXiPeierlsLineConjPermutationKernel := by
  intro x hx
  exact (hbXiPeierlsLineConjPermutationKernelForm_leftRadical_iff x).mp hx

/-- Trivial left radical forces every kernel row to contain a nonzero coefficient. -/
theorem exists_kernel_ne_zero_of_leftNondegenerate
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hnondeg : HBXiPeierlsKernelFormLeftNondegenerate K)
    (q : XiZeroCopy) :
    ∃ r : XiZeroCopy, K q r ≠ 0 := by
  by_contra hnone
  have hrow : ∀ r : XiZeroCopy, K q r = 0 := by
    intro r
    by_contra hqr
    exact hnone ⟨r, hqr⟩
  have hsingle : (Finsupp.single q 1 : HBXiPeierlsPacket) = 0 := by
    apply hnondeg
    intro y
    classical
    simp [hbXiPeierlsKernelForm, hrow]
  have hvalue := congrArg (fun x : HBXiPeierlsPacket => x q) hsingle
  simp at hvalue

/-- Under RH, reflection reality alone makes every arbitrary kernel satisfy the source-FE Ward
law. -/
theorem kernelWard_of_rh_of_reflectionReal
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (hRH : RiemannHypothesis) :
    HBXiPeierlsUnitSourceFEKernelWard K := by
  have hfixed :=
    (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH
  intro q r
  have hq : (q.1 : ℂ).re = 1 / 2 :=
    (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp (hfixed q)
  have hr : (r.1 : ℂ).re = 1 / 2 :=
    (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff r).mp (hfixed r)
  have hkq : hbXiPeierlsUnitSourceFECocycle q = 1 := by
    have hsource :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hq
    simp [hbXiPeierlsUnitSourceFECocycle, hsource]
  have hkr : hbXiPeierlsUnitSourceFECocycle r = 1 := by
    have hsource :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero r).mpr hr
    simp [hbXiPeierlsUnitSourceFECocycle, hsource]
  rw [hreflect q r, hkq, hkr, mul_one, mul_one]

/-- Spectral locality and algebraic left nondegeneracy close the arbitrary-kernel loophole:
full finite-packet covariance is exactly RH. -/
theorem forall_hbXiPeierlsKernelForm_packetTransport_iff_rh_of_reflectionReal_of_spectralLocal_of_leftNondegenerate
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (hlocal : HBXiPeierlsSpectralFibreLocalKernel K)
    (hnondeg : HBXiPeierlsKernelFormLeftNondegenerate K) :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsKernelForm K (hbXiPeierlsUnitSourceFEPacketTransport x)
          (hbXiPeierlsUnitSourceFEPacketTransport y) =
        (starRingEnd ℂ) (hbXiPeierlsKernelForm K x y)) ↔
      RiemannHypothesis := by
  rw [forall_hbXiPeierlsKernelForm_packetTransport_iff_kernelWard]
  constructor
  · intro hward
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    obtain ⟨r, hqr⟩ := exists_kernel_ne_zero_of_leftNondegenerate K hnondeg q
    exact criticalLine_of_kernelWard_of_reflectionReal_of_spectralLocal_ne_zero
      K hward hreflect hlocal q r hqr
  · exact kernelWard_of_rh_of_reflectionReal K hreflect

/-- HC54's canonical nondegenerate survivor is spectrally local exactly under RH. -/
theorem hbXiPeierlsLineConjPermutationKernel_spectralLocal_iff_rh :
    HBXiPeierlsSpectralFibreLocalKernel hbXiPeierlsLineConjPermutationKernel ↔
      RiemannHypothesis := by
  constructor
  · intro hlocal
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    have hsupport : q.1 = (xiZeroCopyLineConjEquiv q).1 :=
      hlocal q (xiZeroCopyLineConjEquiv q)
        (by simp [hbXiPeierlsLineConjPermutationKernel])
    have hcomplex : (q.1 : ℂ) = ((xiZeroCopyLineConjEquiv q).1 : ℂ) :=
      congrArg (fun rho : XiDivisorSupport => (rho : ℂ)) hsupport
    change (q.1 : ℂ) = 1 - (starRingEnd ℂ) (q.1 : ℂ) at hcomplex
    have hre := congrArg Complex.re hcomplex
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro hRH q r hqr
    have hr : r = xiZeroCopyLineConjEquiv q :=
      (hbXiPeierlsLineConjPermutationKernel_ne_zero_iff q r).mp hqr
    subst r
    have hfixed :=
      (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH
    have hline : (q.1 : ℂ).re = 1 / 2 :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp (hfixed q)
    apply Subtype.ext
    change (q.1 : ℂ) = 1 - (starRingEnd ℂ) (q.1 : ℂ)
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp

end

end RHTower
