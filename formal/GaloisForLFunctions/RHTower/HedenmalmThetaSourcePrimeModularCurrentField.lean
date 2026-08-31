import GaloisForLFunctions.RHTower.HedenmalmThetaSourceGlobalConormalCurrentSewing
import GaloisForLFunctions.RHTower.FrankensteinThetaPrimeTranslationPluckerLanding
import GaloisForLFunctions.RHTower.SeamSpectrumDensity

/-!
# Theta-source prime-modular current field

The functional-equation root-block double carries a positive reciprocal prime dilation.  This
dilation is invertible, is conjugated to its inverse by source reflection, commutes with the
nonzero conormal current, and has squared norm equal to the literal two theta prime-translation
energies.

Group-completing the prime interventions exposes a sharp formation-spectrum dichotomy.  The dense
prime-log weld lattice gives every positive modular scale at any off-wall Xi sector, whereas an
on-wall sector has the singleton spectrum `{1}`.  Thus reciprocal/indefinite conservation is the
unconditional law; tracial collapse is exactly the additional critical-line condition.
-/

open Complex Module.End
open GaloisForLFunctions.HTGeometry

namespace RHTower.HedenmalmThetaSource

noncomputable section

def thetaPrimeModularAmplitudeLeft (p : Nat.Primes) (t : ℝ) : ℂ :=
  ((p : ℝ) ^ (-t / 2) : ℝ)

def thetaPrimeModularAmplitudeRight (p : Nat.Primes) (t : ℝ) : ℂ :=
  ((p : ℝ) ^ (t / 2) : ℝ)

def thetaPrimeModularDilationLM (mu : ThetaNonzeroSpectrum)
    (p : Nat.Primes) (t : ℝ) :
    ThetaReflectionPairFiber mu →ₗ[ℂ] ThetaReflectionPairFiber mu where
  toFun v := WithLp.toLp 2
    (thetaPrimeModularAmplitudeLeft p t • v.fst,
      thetaPrimeModularAmplitudeRight p t • v.snd)
  map_add' v w := by
    rw [WithLp.ext_iff]
    apply Prod.ext <;> simp
  map_smul' c v := by
    rw [WithLp.ext_iff]
    apply Prod.ext <;>
      simp [smul_smul, mul_comm]

def thetaPrimeModularDilation (mu : ThetaNonzeroSpectrum)
    (p : Nat.Primes) (t : ℝ) :
    ThetaReflectionPairFiber mu →L[ℂ] ThetaReflectionPairFiber mu :=
  LinearMap.toContinuousLinearMap (thetaPrimeModularDilationLM mu p t)

@[simp] theorem thetaPrimeModularDilation_apply
    (mu : ThetaNonzeroSpectrum) (p : Nat.Primes) (t : ℝ)
    (v : ThetaReflectionPairFiber mu) :
    thetaPrimeModularDilation mu p t v = WithLp.toLp 2
      (thetaPrimeModularAmplitudeLeft p t • v.fst,
        thetaPrimeModularAmplitudeRight p t • v.snd) := rfl

theorem norm_thetaPrimeModularAmplitudeLeft_sq
    (p : Nat.Primes) (t : ℝ) :
    ‖thetaPrimeModularAmplitudeLeft p t‖ ^ 2 =
      (p : ℝ) ^ (-t) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [thetaPrimeModularAmplitudeLeft, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hp _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  congr 1
  norm_num

theorem norm_thetaPrimeModularAmplitudeRight_sq
    (p : Nat.Primes) (t : ℝ) :
    ‖thetaPrimeModularAmplitudeRight p t‖ ^ 2 =
      (p : ℝ) ^ t := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [thetaPrimeModularAmplitudeRight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hp _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  congr 1
  norm_num

/-- Prime modular formation has the literal reciprocal source-energy norm. -/
theorem norm_thetaPrimeModularDilation_sq
    (mu : ThetaNonzeroSpectrum) (p : Nat.Primes) (t : ℝ)
    (v : ThetaReflectionPairFiber mu) :
    ‖thetaPrimeModularDilation mu p t v‖ ^ 2 =
      (p : ℝ) ^ (-t) * ‖v.fst‖ ^ 2 +
        (p : ℝ) ^ t * ‖v.snd‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [thetaPrimeModularDilation_apply, WithLp.toLp_fst,
    WithLp.toLp_snd, norm_smul, mul_pow]
  rw [norm_thetaPrimeModularAmplitudeLeft_sq,
    norm_thetaPrimeModularAmplitudeRight_sq]

theorem thetaPrimeModularDilation_reflection
    (mu : ThetaNonzeroSpectrum) (p : Nat.Primes) (t : ℝ)
    (v : ThetaReflectionPairFiber mu) :
    thetaReflectionPairLIE mu
        (thetaPrimeModularDilation mu p t (thetaReflectionPairLIE mu v)) =
      thetaPrimeModularDilation mu p (-t) v := by
  rw [WithLp.ext_iff]
  apply Prod.ext
  · change (thetaRootBlockReflectionLIE mu).symm
        (thetaPrimeModularAmplitudeRight p t •
          thetaRootBlockReflectionLIE mu v.fst) =
      thetaPrimeModularAmplitudeLeft p (-t) • v.fst
    rw [map_smul, (thetaRootBlockReflectionLIE mu).symm_apply_apply]
    simp [thetaPrimeModularAmplitudeLeft, thetaPrimeModularAmplitudeRight]
  · change thetaRootBlockReflectionLIE mu
        (thetaPrimeModularAmplitudeLeft p t •
          (thetaRootBlockReflectionLIE mu).symm v.snd) =
      thetaPrimeModularAmplitudeRight p (-t) • v.snd
    rw [map_smul, (thetaRootBlockReflectionLIE mu).apply_symm_apply]
    congr 1

theorem thetaPrimeModularDilation_comp_neg
    (mu : ThetaNonzeroSpectrum) (p : Nat.Primes) (t : ℝ)
    (v : ThetaReflectionPairFiber mu) :
    thetaPrimeModularDilation mu p t
        (thetaPrimeModularDilation mu p (-t) v) = v := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hleft : thetaPrimeModularAmplitudeLeft p t *
      thetaPrimeModularAmplitudeLeft p (-t) = 1 := by
    rw [thetaPrimeModularAmplitudeLeft, thetaPrimeModularAmplitudeLeft,
      ← Complex.ofReal_mul]
    congr 1
    rw [← Real.rpow_add hp]
    rw [show -t / 2 + -(-t) / 2 = 0 by ring, Real.rpow_zero]
  have hright : thetaPrimeModularAmplitudeRight p t *
      thetaPrimeModularAmplitudeRight p (-t) = 1 := by
    rw [thetaPrimeModularAmplitudeRight, thetaPrimeModularAmplitudeRight,
      ← Complex.ofReal_mul]
    congr 1
    rw [← Real.rpow_add hp]
    rw [show t / 2 + -t / 2 = 0 by ring, Real.rpow_zero]
  rw [WithLp.ext_iff]
  apply Prod.ext
  · change thetaPrimeModularAmplitudeLeft p t •
        (thetaPrimeModularAmplitudeLeft p (-t) • v.fst) = v.fst
    rw [smul_smul, hleft]
    simp
  · change thetaPrimeModularAmplitudeRight p t •
        (thetaPrimeModularAmplitudeRight p (-t) • v.snd) = v.snd
    rw [smul_smul, hright]
    simp

theorem thetaPrimeModularDilation_commutes_current
    (mu : ThetaNonzeroSpectrum) (p : Nat.Primes) (t : ℝ)
    (v : ThetaReflectionPairFiber mu) :
    normalizedThetaReflectionPairCurrent mu
        (thetaPrimeModularDilation mu p t v) =
      thetaPrimeModularDilation mu p t
        (normalizedThetaReflectionPairCurrent mu v) := by
  rw [WithLp.ext_iff]
  apply Prod.ext
  · change normalizedThetaSourceConormalCurrent mu
        (thetaPrimeModularAmplitudeLeft p t • v.fst) =
      thetaPrimeModularAmplitudeLeft p t •
        normalizedThetaSourceConormalCurrent mu v.fst
    exact map_smul _ _ _
  · change normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu)
        (thetaPrimeModularAmplitudeRight p t • v.snd) =
      thetaPrimeModularAmplitudeRight p t •
        normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu) v.snd
    exact map_smul _ _ _

/-! ## Actual Xi source modular field -/

def thetaXiPrimeModularDilation (q : RHTower.XiZeroCopy)
    (p : Nat.Primes) :
    ThetaReflectionPairFiber (thetaSpectrumOfXiSupport q.1) →L[ℂ]
      ThetaReflectionPairFiber (thetaSpectrumOfXiSupport q.1) :=
  thetaPrimeModularDilation (thetaSpectrumOfXiSupport q.1) p
    (RHTower.primeDepthBVWoldXiCenteredRate q.1)

/-- The modular norm is exactly the two literal source-translation energies. -/
theorem norm_thetaXiPrimeModularDilation_sq
    (q : RHTower.XiZeroCopy) (p : Nat.Primes)
    (v : ThetaReflectionPairFiber (thetaSpectrumOfXiSupport q.1)) :
    ‖thetaXiPrimeModularDilation q p v‖ ^ 2 =
      frankensteinThetaPrimeTranslationEnergy q p * ‖v.fst‖ ^ 2 +
        frankensteinThetaPrimeTranslationEnergy
          (RHTower.xiZeroCopyLineConjEquiv q) p * ‖v.snd‖ ^ 2 := by
  rw [thetaXiPrimeModularDilation, norm_thetaPrimeModularDilation_sq,
    frankensteinThetaPrimeTranslationEnergy_eq,
    frankensteinThetaPrimeTranslationEnergy_lineConj_eq]

theorem thetaXiPrimeModularDilation_commutes_current
    (q : RHTower.XiZeroCopy) (p : Nat.Primes)
    (v : ThetaReflectionPairFiber (thetaSpectrumOfXiSupport q.1)) :
    normalizedThetaReflectionPairCurrent (thetaSpectrumOfXiSupport q.1)
        (thetaXiPrimeModularDilation q p v) =
      thetaXiPrimeModularDilation q p
        (normalizedThetaReflectionPairCurrent
          (thetaSpectrumOfXiSupport q.1) v) :=
  thetaPrimeModularDilation_commutes_current
    (thetaSpectrumOfXiSupport q.1) p
      (RHTower.primeDepthBVWoldXiCenteredRate q.1) v

private abbrev PrimeFormationLogLattice :=
  GaloisForLFunctions.RHTower.primeLogLattice

def thetaXiPrimeModularLogOrbit (q : RHTower.XiZeroCopy)
    (x : PrimeFormationLogLattice) : ℝ :=
  RHTower.primeDepthBVWoldXiCenteredRate q.1 * (x : ℝ)

def thetaXiPositivePrimeModularOrbit (q : RHTower.XiZeroCopy)
    (x : PrimeFormationLogLattice) : Set.Ioi (0 : ℝ) :=
  Real.expOrderIso.toHomeomorph (thetaXiPrimeModularLogOrbit q x)

def thetaXiPositivePrimeModularSpectrum (q : RHTower.XiZeroCopy) :
    Set (Set.Ioi (0 : ℝ)) :=
  closure (Set.range (thetaXiPositivePrimeModularOrbit q))

theorem denseRange_thetaXiPrimeModularLogOrbit
    (q : RHTower.XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    DenseRange (thetaXiPrimeModularLogOrbit q) := by
  have ht : RHTower.primeDepthBVWoldXiCenteredRate q.1 ≠ 0 :=
    mt (RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).mp hoff
  have hinc : DenseRange (fun x : PrimeFormationLogLattice => (x : ℝ)) := by
    change Dense (Set.range fun x : PrimeFormationLogLattice => (x : ℝ))
    convert GaloisForLFunctions.RHTower.primeLogLattice_dense using 1
    ext y
    simp
  have hscale : DenseRange
      (fun x : ℝ => RHTower.primeDepthBVWoldXiCenteredRate q.1 * x) := by
    apply Function.Surjective.denseRange
    intro y
    refine ⟨y / RHTower.primeDepthBVWoldXiCenteredRate q.1, ?_⟩
    field_simp
  exact hscale.comp hinc (continuous_const.mul continuous_id)

/-- Off-wall prime formation has maximal positive modular spectrum. -/
theorem thetaXiPositivePrimeModularSpectrum_eq_univ_of_offline
    (q : RHTower.XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    thetaXiPositivePrimeModularSpectrum q = Set.univ := by
  have hexp : DenseRange
      (Real.expOrderIso.toHomeomorph : ℝ → Set.Ioi (0 : ℝ)) :=
    Real.expOrderIso.toHomeomorph.surjective.denseRange
  have horbit : DenseRange (thetaXiPositivePrimeModularOrbit q) :=
    hexp.comp (denseRange_thetaXiPrimeModularLogOrbit q hoff)
      Real.expOrderIso.toHomeomorph.continuous
  exact denseRange_iff_closure_range.mp horbit

/-- On-wall prime formation has the singleton tracial modular spectrum. -/
theorem thetaXiPositivePrimeModularSpectrum_eq_singleton_of_onwall
    (q : RHTower.XiZeroCopy)
    (hwall : (q.1 : ℂ).re = 1 / 2) :
    thetaXiPositivePrimeModularSpectrum q =
      ({⟨(1 : ℝ), by norm_num⟩} : Set (Set.Ioi (0 : ℝ))) := by
  have ht : RHTower.primeDepthBVWoldXiCenteredRate q.1 = 0 :=
    (RHTower.primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1).2 hwall
  let onePos : Set.Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  have horbit : thetaXiPositivePrimeModularOrbit q = fun _ => onePos := by
    funext x
    apply Subtype.ext
    simp [thetaXiPositivePrimeModularOrbit, thetaXiPrimeModularLogOrbit,
      ht, onePos]
  rw [thetaXiPositivePrimeModularSpectrum, horbit]
  simp [onePos]

/-- Tracial modular collapse is exactly critical-line placement on each source root block. -/
theorem thetaXiPositivePrimeModularSpectrum_eq_singleton_iff
    (q : RHTower.XiZeroCopy) :
    thetaXiPositivePrimeModularSpectrum q =
        ({⟨(1 : ℝ), by norm_num⟩} : Set (Set.Ioi (0 : ℝ))) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hsingle
    by_contra hoff
    have huniv := thetaXiPositivePrimeModularSpectrum_eq_univ_of_offline q hoff
    have heq : (Set.univ : Set (Set.Ioi (0 : ℝ))) =
        ({⟨(1 : ℝ), by norm_num⟩} : Set (Set.Ioi (0 : ℝ))) :=
      huniv.symm.trans hsingle
    let twoPos : Set.Ioi (0 : ℝ) := ⟨2, by norm_num⟩
    have hmem : twoPos ∈
        ({⟨(1 : ℝ), by norm_num⟩} : Set (Set.Ioi (0 : ℝ))) := by
      rw [← heq]
      exact Set.mem_univ twoPos
    have htwo : twoPos = ⟨(1 : ℝ), by norm_num⟩ := by simpa using hmem
    have := congrArg Subtype.val htwo
    norm_num [twoPos] at this
  · exact thetaXiPositivePrimeModularSpectrum_eq_singleton_of_onwall q

/-- No intermediate modular phase exists: every Xi source sector is tracial or maximally
noncompact under the group-completed prime formation action. -/
theorem thetaXiPositivePrimeModularSpectrum_dichotomy
    (q : RHTower.XiZeroCopy) :
    ((q.1 : ℂ).re = 1 / 2 ∧
      thetaXiPositivePrimeModularSpectrum q =
        ({⟨(1 : ℝ), by norm_num⟩} : Set (Set.Ioi (0 : ℝ)))) ∨
    ((q.1 : ℂ).re ≠ 1 / 2 ∧
      thetaXiPositivePrimeModularSpectrum q = Set.univ) := by
  rcases eq_or_ne (q.1 : ℂ).re (1 / 2) with hwall | hoff
  · exact Or.inl ⟨hwall,
      thetaXiPositivePrimeModularSpectrum_eq_singleton_of_onwall q hwall⟩
  · exact Or.inr ⟨hoff,
      thetaXiPositivePrimeModularSpectrum_eq_univ_of_offline q hoff⟩

/-- Global modular traciality is exactly the familiar global critical-line condition, now
reconstructed from the source-formation spectrum rather than a chosen scalar reporter. -/
theorem forall_thetaXiPositivePrimeModularSpectrum_eq_singleton_iff :
    (∀ q : RHTower.XiZeroCopy,
      thetaXiPositivePrimeModularSpectrum q =
        ({⟨(1 : ℝ), by norm_num⟩} : Set (Set.Ioi (0 : ℝ)))) ↔
      ∀ q : RHTower.XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
  simp only [thetaXiPositivePrimeModularSpectrum_eq_singleton_iff]

end
end RHTower.HedenmalmThetaSource
