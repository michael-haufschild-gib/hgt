import GaloisForLFunctions.RHTower.RouteRExternalTensorMonodromy
import GaloisForLFunctions.RHTower.DeningerBigWittPrimeSeamDirichletTransport
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixPairedDefectGaussHodgeCurvature

/-!
# Completion quantum and non-descending formation cost

At the first trace wall, every nonzero horizontal grade has one of two oriented prime-harmonic
completion classes. External squaring removes the orientation, so every nonzero grade has the same
external tensor curvature. Its representative coefficients are exactly the reciprocal-prime
Big-Witt physical atoms.

The literal Gamma-six paired boundary cost behaves differently: it is `2 * (cosh t - 1)` and
strictly distinguishes positive rapidities. Consequently this cost cannot factor through the
external completion curvature. Completion occupation and formation cost are two distinct levels of
the source history; the latter cannot be reconstructed from the phase-quotiented tensor class.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Universal external square of the prime-harmonic completion quantum. -/
def routeRPrimeHarmonicExternalTensor : RouteRExternalMonodromyTensor :=
  routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence ⊗ₜ[ℂ]
    routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence

/-- Phase quantization: after external squaring, every nonzero horizontal grade is the same
prime-harmonic completion quantum. -/
theorem routeRExternalTensorCurvature_eq_harmonic_of_ne_zero
    {t : ℝ} (ht : t ≠ 0) :
    routeRExternalTensorCurvature t = routeRPrimeHarmonicExternalTensor := by
  rcases lt_trichotomy t 0 with hneg | hzero | hpos
  · rw [routeRExternalTensorCurvature]
    change routeRPrimeGammaCriticalWallSummableHadamardClass t ⊗ₜ[ℂ]
      routeRPrimeGammaCriticalWallSummableHadamardClass t = _
    rw [routeRPrimeGammaCriticalWallSummableHadamardClass]
    simp [hneg, not_lt.mpr hneg.le, routeRPrimeHarmonicExternalTensor]
  · exact (ht hzero).elim
  · rw [routeRExternalTensorCurvature]
    change routeRPrimeGammaCriticalWallSummableHadamardClass t ⊗ₜ[ℂ]
      routeRPrimeGammaCriticalWallSummableHadamardClass t = _
    rw [routeRPrimeGammaCriticalWallSummableHadamardClass]
    simp only [if_pos hpos, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
      neg_neg]
    rfl

/-- External completion curvature remembers occupation but forgets every nonzero rapidity
magnitude. -/
theorem routeRExternalTensorCurvature_eq_of_ne_zero
    {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) :
    routeRExternalTensorCurvature s = routeRExternalTensorCurvature t := by
  rw [routeRExternalTensorCurvature_eq_harmonic_of_ne_zero hs,
    routeRExternalTensorCurvature_eq_harmonic_of_ne_zero ht]

/-- The coefficient kernel of the universal external completion quantum is exactly the physical
reciprocal-prime Big-Witt pair atom. -/
theorem routeRPrimeHarmonic_product_eq_bigWittPhysicalAtom (n m : ℕ) :
    routeRPrimeHarmonicTraceSequence n * routeRPrimeHarmonicTraceSequence m =
      (deningerBigWittPrimePairExtendedPhysicalAtom
        (nthPrimeEquiv n) (nthPrimeEquiv m) : ℂ) := by
  simp only [routeRPrimeHarmonicTraceSequence,
    deningerBigWittPrimePairExtendedPhysicalAtom_eq]
  push_cast
  ring

/-- Literal Gamma-six paired formation cost still separates two positive rapidities that external
completion identifies. -/
theorem sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_one_lt_two :
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature 1 <
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature 2 := by
  rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]
  have hcosh : Real.cosh 1 < Real.cosh 2 :=
    Real.cosh_strictMonoOn (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Formation cost does not descend through phase-quantized external completion curvature. -/
theorem sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_not_factor_externalTensor :
    ¬ ∃ F : RouteRExternalMonodromyTensor → ℝ,
      ∀ t : ℝ,
        F (routeRExternalTensorCurvature t) =
          sourceHorizontalGammaSixUnitOppositeBoundaryCurvature t := by
  rintro ⟨F, hF⟩
  have hcurv : routeRExternalTensorCurvature (1 : ℝ) =
      routeRExternalTensorCurvature (2 : ℝ) :=
    routeRExternalTensorCurvature_eq_of_ne_zero (by norm_num) (by norm_num)
  have hEq : sourceHorizontalGammaSixUnitOppositeBoundaryCurvature 1 =
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature 2 := by
    rw [← hF 1, ← hF 2, hcurv]
  exact (ne_of_lt sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_one_lt_two) hEq

/-- Two-level completion record: oriented occupation in the summable corona together with its
literal pre-completion Gamma formation cost. -/
def routeRMarkedCompletionProfile (t : ℝ) :
    RouteRSummableHadamardCorona × ℝ :=
  (routeRNilpotentMonodromyWallClass t,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature t)

/-- Joint reconstruction: orientation plus source cost recovers the entire horizontal rapidity,
although external occupation alone collapses every nonzero magnitude. -/
theorem routeRMarkedCompletionProfile_injective :
    Function.Injective routeRMarkedCompletionProfile := by
  intro s t hprofile
  have hclass := congrArg Prod.fst hprofile
  have hcost := congrArg Prod.snd hprofile
  change routeRPrimeGammaCriticalWallSummableHadamardClass s =
    routeRPrimeGammaCriticalWallSummableHadamardClass t at hclass
  change sourceHorizontalGammaSixUnitOppositeBoundaryCurvature s =
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature t at hcost
  have hnotneg : routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence ≠
      -routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence := by
    intro hsign
    apply routeRPrimeHarmonicSummableHadamardClass_ne_zero
    have htwo : (2 : ℂ) •
        routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence = 0 := by
      rw [two_smul]
      have hadd := congrArg (fun x => x +
        routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence) hsign
      simpa using hadd
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  rcases lt_trichotomy s 0 with hs | rfl | hs <;>
    rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hcosh : Real.cosh (-s) = Real.cosh (-t) := by
      rw [Real.cosh_neg, Real.cosh_neg]
      rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
        sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq] at hcost
      linarith
    have hneg : -s = -t := Real.cosh_strictMonoOn.injOn
      (by simp [hs.le]) (by simp [ht.le]) hcosh
    linarith
  · have hne := (routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff s).2 hs.ne
    simp [routeRPrimeGammaCriticalWallSummableHadamardClass] at hclass
    exact (hne hclass).elim
  · have hsign : routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence =
        -routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence := by
      simpa [routeRPrimeGammaCriticalWallSummableHadamardClass,
        hs, ht, not_lt.mpr hs.le] using hclass
    exact (hnotneg hsign).elim
  · have hne := (routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff t).2 ht.ne
    simp [routeRPrimeGammaCriticalWallSummableHadamardClass] at hclass
    exact (hne hclass.symm).elim
  · rfl
  · have hne := (routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff t).2 ht.ne'
    simp [routeRPrimeGammaCriticalWallSummableHadamardClass] at hclass
    exact (hne hclass.symm).elim
  · have hsign : -routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence =
        routeRSummableHadamardClass routeRPrimeHarmonicBoundedTraceSequence := by
      simpa [routeRPrimeGammaCriticalWallSummableHadamardClass,
        hs, ht, not_lt.mpr ht.le] using hclass
    exact (hnotneg hsign.symm).elim
  · have hne := (routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff s).2 hs.ne'
    simp [routeRPrimeGammaCriticalWallSummableHadamardClass] at hclass
    exact (hne hclass).elim
  · have hcosh : Real.cosh s = Real.cosh t := by
      rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
        sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq] at hcost
      linarith
    exact Real.cosh_strictMonoOn.injOn hs.le ht.le hcosh

end

end RHTower
