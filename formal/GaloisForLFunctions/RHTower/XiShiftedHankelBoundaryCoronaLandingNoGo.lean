import GaloisForLFunctions.HTGeometry.TateClockObservableWitnesses
import GaloisForLFunctions.HTGeometry.CountablePrimeProfileRealization
import GaloisForLFunctions.HTGeometry.ConstitutiveGammaResponseLifetime
import GaloisForLFunctions.RHTower.RouteRCriticalWallOrientedHarmonicQuantization

/-!
# Fixed-corona landing boundary for the shifted-Xi Hankel normal

The fixed Gamma corona is the quotient of all prime trace sequences by the summable ideal.  Its
canonical lift therefore kills every finitely supported prime sequence.  Such sequences are dense
for the raw product topology, so a Hausdorff linear reporter whose canonical lift is continuous
must vanish.  In particular a nonzero fixed-corona landing into the adaptive shifted-Hankel normal
cannot be a product-continuous linear observation.

This topological no-go does not make the infinite source uninformative.  The exact Gamma response
lifetime records the modulus of the centered grade, while the nonzero oriented harmonic wall class
records its sign.  Their joint signature is injective.  Thus the remaining burden is a nonlinear
or admission-sensitive landing of this infinite signature, rather than another finite Hankel
carrier or fixed continuous linear reporter.
-/

open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Product-topology blindness of the fixed corona -/

/-- Reindex a countable product clock as a prime trace sequence. -/
def primeTraceSequenceFromClock : (ℕ → ℂ) →ₗ[ℂ] PrimeTraceSequence where
  toFun a p := a (chosenPrimeEnumerationEquiv.symm p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem primeTraceSequenceFromClock_apply (a : ℕ → ℂ) (p : Nat.Primes) :
    primeTraceSequenceFromClock a p = a (chosenPrimeEnumerationEquiv.symm p) :=
  rfl

/-- Prime reindexing is continuous for the raw product topologies. -/
theorem continuous_primeTraceSequenceFromClock :
    Continuous primeTraceSequenceFromClock := by
  apply continuous_pi
  intro p
  exact continuous_apply (chosenPrimeEnumerationEquiv.symm p)

/-- Every prime trace sequence is a reindexed countable clock. -/
theorem primeTraceSequenceFromClock_surjective :
    Function.Surjective primeTraceSequenceFromClock := by
  intro a
  refine ⟨fun n => a (chosenPrimeEnumerationEquiv n), ?_⟩
  funext p
  simp

/-- Reindexing a finitely supported clock gives a summable prime trace sequence. -/
theorem summable_primeTraceSequenceFromClock_of_finiteSupport
    (w : finiteSupportClockSubmodule ℂ) :
    Summable (primeTraceSequenceFromClock w.1) := by
  rw [← chosenPrimeEnumerationEquiv.summable_iff]
  simpa [Function.comp_def] using summable_of_hasFiniteSupport w.2

/-- **Prime product-observation no-go.**  A continuous Hausdorff linear reporter on the raw prime
product which vanishes on every summable trace sequence is identically zero. -/
theorem primeTraceReporter_eq_zero_of_continuous_of_vanishing_on_summable
    {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] [T2Space Q]
    (L : PrimeTraceSequence →ₗ[ℂ] Q) (hL : Continuous L)
    (hzero : ∀ a : PrimeTraceSequence, Summable a → L a = 0) :
    L = 0 := by
  have hcomp : L.comp primeTraceSequenceFromClock = 0 := by
    apply continuousLinearMap_eq_zero_of_vanishing_on_finiteSupport
    · exact hL.comp continuous_primeTraceSequenceFromClock
    · intro w
      exact hzero _ (summable_primeTraceSequenceFromClock_of_finiteSupport w)
  apply LinearMap.ext
  intro a
  obtain ⟨w, rfl⟩ := primeTraceSequenceFromClock_surjective a
  exact LinearMap.congr_fun hcomp w

/-- **Fixed-corona continuous-landing no-go.**  Every linear reporter on the constitutive Gamma
corona is zero if its canonical lift to the raw prime product is continuous and its target is
Hausdorff. -/
theorem constitutiveGammaCoronaReporter_eq_zero_of_continuous_lift
    {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] [T2Space Q]
    (reporter : ConstitutiveGammaCorona →ₗ[ℂ] Q)
    (hcontinuous : Continuous (reporter.comp primeFirstTraceSummableIdeal.mkQ)) :
    reporter = 0 := by
  have hlift : reporter.comp primeFirstTraceSummableIdeal.mkQ = 0 := by
    apply primeTraceReporter_eq_zero_of_continuous_of_vanishing_on_summable
    · exact hcontinuous
    · intro a ha
      rw [LinearMap.comp_apply]
      have hmk : primeFirstTraceSummableIdeal.mkQ a = 0 :=
        (Submodule.Quotient.mk_eq_zero primeFirstTraceSummableIdeal).mpr ha
      rw [hmk, map_zero]
  apply LinearMap.ext
  intro q
  obtain ⟨a, rfl⟩ := primeFirstTraceSummableIdeal.mkQ_surjective q
  exact LinearMap.congr_fun hlift a

/-- A nonzero fixed-corona linear reporter necessarily has a product-discontinuous canonical
lift. -/
theorem no_nonzero_constitutiveGammaCoronaReporter_with_continuous_lift
    {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] [T2Space Q]
    (reporter : ConstitutiveGammaCorona →ₗ[ℂ] Q) (hne : reporter ≠ 0) :
    ¬ Continuous (reporter.comp primeFirstTraceSummableIdeal.mkQ) := by
  intro hcontinuous
  exact hne (constitutiveGammaCoronaReporter_eq_zero_of_continuous_lift
    reporter hcontinuous)

/-! ## Positive survivor: oriented lifetime is complete -/

/-- Prime-harmonic representative of the universal oriented first-wall class. -/
def constitutiveGammaPrimeHarmonicSequence : PrimeTraceSequence :=
  fun p => ((((p : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)

/-- Universal prime-harmonic class in the fixed constitutive Gamma corona. -/
def constitutiveGammaPrimeHarmonicClass : ConstitutiveGammaCorona :=
  Submodule.Quotient.mk constitutiveGammaPrimeHarmonicSequence

/-- Prime-indexed critical-wall representative of a centered grade. -/
def constitutiveGammaCriticalWallSequence (t : ℝ) : PrimeTraceSequence :=
  fun p => (primeGammaCofinalBocksteinCriticalWallCoefficient t p : ℂ)

/-- Bockstein class observed exactly at its critical response time. -/
def constitutiveGammaCriticalWallClass (t : ℝ) : ConstitutiveGammaCorona :=
  constitutiveGammaCoronaResponse ⟨|t| / 2, by positivity⟩
    (primeGammaCofinalBockstein t)

/-- Critical response is represented by the oriented critical-wall prime sequence. -/
theorem constitutiveGammaCriticalWallClass_eq_mk (t : ℝ) :
    constitutiveGammaCriticalWallClass t =
      Submodule.Quotient.mk (constitutiveGammaCriticalWallSequence t) := by
  rw [constitutiveGammaCriticalWallClass,
    constitutiveGammaCoronaResponse_bockstein]
  congr 1
  funext p
  have hexp : -2 * (|t| / 2) = -|t| := by ring
  change (↑((p : ℝ) ^ (-2 * (|t| / 2))) : ℂ) *
      ((primeActivationOccupancyFisherComplexTwist (-t) p) -
        primeActivationOccupancyFisherComplexTwist t p) =
    ↑((p : ℝ) ^ (-|t|) *
      (primeActivationOccupancyFisherTwist (-t) p -
        primeActivationOccupancyFisherTwist t p))
  rw [hexp]
  simp only [primeActivationOccupancyFisherComplexTwist]
  push_cast
  ring

/-- Positive centered grades give the negative universal harmonic corona orientation. -/
theorem constitutiveGammaCriticalWallClass_eq_neg_harmonic_of_pos
    {t : ℝ} (ht : 0 < t) :
    constitutiveGammaCriticalWallClass t =
      -constitutiveGammaPrimeHarmonicClass := by
  rw [constitutiveGammaCriticalWallClass_eq_mk,
    constitutiveGammaPrimeHarmonicClass, ← Submodule.Quotient.mk_neg]
  apply (Submodule.Quotient.eq primeFirstTraceSummableIdeal).2
  have hreal := summable_criticalWallCoefficient_add_primeHarmonic_of_pos ht
  have hcomplex := (Complex.ofRealCLM.hasSum hreal.hasSum).summable
  exact hcomplex.congr fun p => by
    simp [constitutiveGammaCriticalWallSequence,
      constitutiveGammaPrimeHarmonicSequence]

/-- Negative centered grades give the positive universal harmonic corona orientation. -/
theorem constitutiveGammaCriticalWallClass_eq_harmonic_of_neg
    {t : ℝ} (ht : t < 0) :
    constitutiveGammaCriticalWallClass t =
      constitutiveGammaPrimeHarmonicClass := by
  rw [constitutiveGammaCriticalWallClass_eq_mk,
    constitutiveGammaPrimeHarmonicClass]
  apply (Submodule.Quotient.eq primeFirstTraceSummableIdeal).2
  have hreal := summable_criticalWallCoefficient_sub_primeHarmonic_of_neg ht
  have hcomplex := (Complex.ofRealCLM.hasSum hreal.hasSum).summable
  exact hcomplex.congr fun p => by
    simp [constitutiveGammaCriticalWallSequence,
      constitutiveGammaPrimeHarmonicSequence]

/-- The universal oriented harmonic class is nonzero in the fixed Gamma corona. -/
theorem constitutiveGammaPrimeHarmonicClass_ne_zero :
    constitutiveGammaPrimeHarmonicClass ≠ 0 := by
  intro hzero
  have hcritical : constitutiveGammaCriticalWallClass 1 ≠ 0 :=
    constitutiveGammaBockstein_critical_survival (t := 1) one_ne_zero
  apply hcritical
  rw [constitutiveGammaCriticalWallClass_eq_neg_harmonic_of_pos zero_lt_one,
    hzero, neg_zero]

/-- Infinite-source signature formed by response lifetime and its oriented fixed-corona class. -/
def gammaOrientedLifetimeSignature (t : ℝ) :=
  (constitutiveGammaBocksteinLifetime t, constitutiveGammaCriticalWallClass t)

/-- **Oriented-lifetime reconstruction.**  Response lifetime records `|t| / 2`; the nonzero
harmonic wall class distinguishes the two signs.  Their joint infinite-source signature therefore
reconstructs the centered grade exactly. -/
theorem gammaOrientedLifetimeSignature_injective :
    Function.Injective gammaOrientedLifetimeSignature := by
  intro t u hsignature
  have hlifetime := congrArg Prod.fst hsignature
  have hclass := congrArg Prod.snd hsignature
  have habs : |t| = |u| := by
    simp only [gammaOrientedLifetimeSignature,
      constitutiveGammaBocksteinLifetime_eq] at hlifetime
    linarith
  rcases abs_eq_abs.mp habs with htu | htu
  · exact htu
  · by_cases htzero : t = 0
    · have huabs : |u| = 0 := by simpa [htzero] using habs.symm
      exact htzero.trans (abs_eq_zero.mp huabs).symm
    · have hH : constitutiveGammaPrimeHarmonicClass ≠ 0 :=
        constitutiveGammaPrimeHarmonicClass_ne_zero
      have hnegH :
          -constitutiveGammaPrimeHarmonicClass ≠
            constitutiveGammaPrimeHarmonicClass := by
        intro hneg
        apply hH
        have hadd : constitutiveGammaPrimeHarmonicClass +
            constitutiveGammaPrimeHarmonicClass = 0 :=
          neg_eq_iff_add_eq_zero.mp hneg
        have hsmul : (2 : ℂ) • constitutiveGammaPrimeHarmonicClass = 0 := by
          simpa only [two_smul] using hadd
        exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
      have hut : u = -t := by linarith
      change constitutiveGammaCriticalWallClass t =
        constitutiveGammaCriticalWallClass u at hclass
      rcases lt_or_gt_of_ne htzero with htneg | htpos
      · have huneg : 0 < u := by rw [hut]; exact neg_pos.mpr htneg
        rw [constitutiveGammaCriticalWallClass_eq_harmonic_of_neg htneg,
          constitutiveGammaCriticalWallClass_eq_neg_harmonic_of_pos huneg] at hclass
        exact False.elim (hnegH hclass.symm)
      · have huneg : u < 0 := by rw [hut]; exact neg_lt_zero.mpr htpos
        rw [constitutiveGammaCriticalWallClass_eq_neg_harmonic_of_pos htpos,
          constitutiveGammaCriticalWallClass_eq_harmonic_of_neg huneg] at hclass
        exact False.elim (hnegH hclass)

/-- Critical-wall representatives are odd under centered-grade reflection. -/
theorem constitutiveGammaCriticalWallSequence_neg (t : ℝ) :
    constitutiveGammaCriticalWallSequence (-t) =
      -constitutiveGammaCriticalWallSequence t := by
  funext p
  simp [constitutiveGammaCriticalWallSequence,
    primeGammaCofinalBocksteinCriticalWallCoefficient]
  ring

/-- The oriented critical-wall corona class is odd under functional-equation reflection. -/
theorem constitutiveGammaCriticalWallClass_neg (t : ℝ) :
    constitutiveGammaCriticalWallClass (-t) =
      -constitutiveGammaCriticalWallClass t := by
  rw [constitutiveGammaCriticalWallClass_eq_mk,
    constitutiveGammaCriticalWallClass_eq_mk,
    constitutiveGammaCriticalWallSequence_neg, Submodule.Quotient.mk_neg]

/-- **Reflection-cancellation wall.**  Linear aggregation of one reflected centered-grade pair
annihilates its oriented critical-wall corona class.  Any surviving source landing must polarize
the odd class against another odd datum before reflection summation. -/
theorem constitutiveGammaCriticalWallClass_reflection_sum (t : ℝ) :
    constitutiveGammaCriticalWallClass t +
      constitutiveGammaCriticalWallClass (-t) = 0 := by
  rw [constitutiveGammaCriticalWallClass_neg, add_neg_cancel]

/-- Critical-wall corona class is nonzero exactly away from neutral centered grade. -/
theorem constitutiveGammaCriticalWallClass_ne_zero_iff (t : ℝ) :
    constitutiveGammaCriticalWallClass t ≠ 0 ↔ t ≠ 0 := by
  constructor
  · intro hclass ht
    subst t
    apply hclass
    rw [constitutiveGammaCriticalWallClass_eq_mk]
    rw [Submodule.Quotient.mk_eq_zero]
    change Summable (constitutiveGammaCriticalWallSequence 0)
    convert summable_zero using 1
    funext p
    simp [constitutiveGammaCriticalWallSequence,
      primeGammaCofinalBocksteinCriticalWallCoefficient]
  · intro ht
    simpa [constitutiveGammaCriticalWallClass] using
      (constitutiveGammaBockstein_critical_survival (t := t) ht)

/-- Reflection-even polarization of the odd critical-wall class by centered grade. -/
def constitutiveGammaPolarizedCriticalWallClass (t : ℝ) : ConstitutiveGammaCorona :=
  (t : ℂ) • constitutiveGammaCriticalWallClass t

/-- Odd grade times odd corona orientation survives as a reflection-even class. -/
theorem constitutiveGammaPolarizedCriticalWallClass_neg (t : ℝ) :
    constitutiveGammaPolarizedCriticalWallClass (-t) =
      constitutiveGammaPolarizedCriticalWallClass t := by
  simp [constitutiveGammaPolarizedCriticalWallClass,
    constitutiveGammaCriticalWallClass_neg]

/-- The polarized reflection-even class detects every nonneutral centered grade. -/
theorem constitutiveGammaPolarizedCriticalWallClass_ne_zero_iff (t : ℝ) :
    constitutiveGammaPolarizedCriticalWallClass t ≠ 0 ↔ t ≠ 0 := by
  constructor
  · intro hpolar ht
    subst t
    exact hpolar (by simp [constitutiveGammaPolarizedCriticalWallClass])
  · intro ht
    exact smul_ne_zero (Complex.ofReal_ne_zero.mpr ht)
      ((constitutiveGammaCriticalWallClass_ne_zero_iff t).mpr ht)

/-- Every polarized grade lies on one fixed oriented harmonic ray, with coefficient `|t|`. -/
theorem constitutiveGammaPolarizedCriticalWallClass_eq_neg_abs_smul_harmonic
    (t : ℝ) :
    constitutiveGammaPolarizedCriticalWallClass t =
      (-((|t| : ℝ) : ℂ)) • constitutiveGammaPrimeHarmonicClass := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [constitutiveGammaPolarizedCriticalWallClass,
      constitutiveGammaCriticalWallClass_eq_harmonic_of_neg ht,
      abs_of_neg ht]
    push_cast
    simp
  · subst t
    simp [constitutiveGammaPolarizedCriticalWallClass]
  · rw [constitutiveGammaPolarizedCriticalWallClass,
      constitutiveGammaCriticalWallClass_eq_neg_harmonic_of_pos ht,
      abs_of_pos ht]
    simp

/-- A reflected pair doubles, rather than cancels, after the canonical odd-by-odd polarization. -/
theorem constitutiveGammaPolarizedCriticalWallClass_reflection_sum (t : ℝ) :
    constitutiveGammaPolarizedCriticalWallClass t +
      constitutiveGammaPolarizedCriticalWallClass (-t) =
        (2 : ℂ) • constitutiveGammaPolarizedCriticalWallClass t := by
  rw [constitutiveGammaPolarizedCriticalWallClass_neg, two_smul]

/-- Every finite packet of polarized grades remains on the same harmonic ray. -/
theorem sum_constitutiveGammaPolarizedCriticalWallClass_eq
    {ι : Type*} (S : Finset ι) (t : ι → ℝ) :
    ∑ i ∈ S, constitutiveGammaPolarizedCriticalWallClass (t i) =
      (-((∑ i ∈ S, |t i| : ℝ) : ℂ)) •
        constitutiveGammaPrimeHarmonicClass := by
  simp_rw [constitutiveGammaPolarizedCriticalWallClass_eq_neg_abs_smul_harmonic]
  rw [← Finset.sum_smul]
  congr 1
  simp

/-- **Finite polarized-corona no-shorting.**  A finite packet cannot cancel if at least one
centered grade is nonneutral. -/
theorem sum_constitutiveGammaPolarizedCriticalWallClass_ne_zero
    {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (hnonzero : ∃ i ∈ S, t i ≠ 0) :
    ∑ i ∈ S, constitutiveGammaPolarizedCriticalWallClass (t i) ≠ 0 := by
  have hsum : 0 < ∑ i ∈ S, |t i| := by
    apply Finset.sum_pos'
    · intro i hi
      exact abs_nonneg (t i)
    · obtain ⟨i, hi, hti⟩ := hnonzero
      exact ⟨i, hi, abs_pos.mpr hti⟩
  rw [sum_constitutiveGammaPolarizedCriticalWallClass_eq]
  have hcoeff : (-((∑ i ∈ S, |t i| : ℝ) : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hsum.ne')
  exact smul_ne_zero
    hcoeff
    constitutiveGammaPrimeHarmonicClass_ne_zero

/-- **Polarization/topology separation.**  The canonical polarization prevents reflection
cancellation, but no product-continuous Hausdorff linear reporter on the fixed corona can detect
it.  A successful adaptive-normal landing must therefore spend topology or admission, not only
algebraic polarization. -/
theorem no_productContinuous_coronaReporter_detects_polarizedCriticalWall
    {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] [T2Space Q]
    (t : ℝ) :
    ¬ ∃ reporter : ConstitutiveGammaCorona →ₗ[ℂ] Q,
      Continuous (reporter.comp primeFirstTraceSummableIdeal.mkQ) ∧
        reporter (constitutiveGammaPolarizedCriticalWallClass t) ≠ 0 := by
  rintro ⟨reporter, hcontinuous, hdetect⟩
  have hzero := constitutiveGammaCoronaReporter_eq_zero_of_continuous_lift
    reporter hcontinuous
  rw [hzero] at hdetect
  exact hdetect rfl

end

end RHTower
