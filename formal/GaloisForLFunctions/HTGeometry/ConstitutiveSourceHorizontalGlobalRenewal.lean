import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry
import GaloisForLFunctions.RHTower.SourceHorizontalAbelianClassLawInformationEvacuation

/-!
# Source-horizontal global renewal

This module instantiates cofinal renewal geometry on the literal abelian class-law tower.  The
canonical elementary/cyclic apertures are proved pairwise disjoint from their exact order and
socle invariants.  Existing class-law atom formulas then give the sharp forward and reverse
exponential evacuation rates.  One finite-KL renewal consequently has a summable cofinal moment
and a summable mass-weighted adaptive Jeffreys current.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory Set Filter Topology
open scoped ENNReal Topology
open _root_.RHTower

noncomputable section

/-- Canonical source-horizontal two-class aperture at positive grade `n + 1`. -/
def sourceHorizontalClassAperture (p : Nat.Primes) (n : ℕ) : Set AbelianZetaGroupClass :=
  {sourceHorizontalAbelianElementaryClass p (n + 1),
    sourceHorizontalAbelianCyclicClass p (n + 1)}

private theorem sourceHorizontalClassAperture_classes_ne
    (p : Nat.Primes) (n : ℕ) :
    sourceHorizontalAbelianElementaryClass p (n + 1) ≠
      sourceHorizontalAbelianCyclicClass p (n + 1) := by
  intro h
  have hs := congrArg AbelianZetaGroupClass.socleOrder h
  rw [sourceHorizontalAbelianElementaryClass_socleOrder,
    sourceHorizontalAbelianCyclicClass_socleOrder] at hs
  have hpow : (p : ℕ) ^ 1 < (p : ℕ) ^ (n + 2) :=
    Nat.pow_lt_pow_right p.2.one_lt (Nat.succ_lt_succ (Nat.zero_lt_succ n))
  simp only [pow_one] at hpow
  exact (ne_of_gt hpow) hs

/-- The canonical apertures at distinct grades are disjoint. -/
theorem pairwise_disjoint_sourceHorizontalClassAperture (p : Nat.Primes) :
    Pairwise fun n m =>
      Disjoint (sourceHorizontalClassAperture p n) (sourceHorizontalClassAperture p m) := by
  intro n m hnm
  rw [Set.disjoint_left]
  intro x hxn hxm
  simp only [sourceHorizontalClassAperture, Set.mem_insert_iff, Set.mem_singleton_iff]
    at hxn hxm
  rcases hxn with hnE | hnC <;> rcases hxm with hmE | hmC
  · have horder := congrArg AbelianZetaGroupClass.order (hnE.symm.trans hmE)
    rw [sourceHorizontalAbelianElementaryClass_order,
      sourceHorizontalAbelianElementaryClass_order] at horder
    have hexp : n + 2 = m + 2 := (Nat.pow_right_injective p.2.two_le) horder
    exact hnm (Nat.add_right_cancel hexp)
  · have hs := congrArg AbelianZetaGroupClass.socleOrder (hnE.symm.trans hmC)
    rw [sourceHorizontalAbelianElementaryClass_socleOrder,
      sourceHorizontalAbelianCyclicClass_socleOrder] at hs
    have hpow : (p : ℕ) ^ 1 < (p : ℕ) ^ (n + 2) :=
      Nat.pow_lt_pow_right p.2.one_lt (Nat.succ_lt_succ (Nat.zero_lt_succ n))
    simp only [pow_one] at hpow
    exact (ne_of_gt hpow) hs
  · have hs := congrArg AbelianZetaGroupClass.socleOrder (hnC.symm.trans hmE)
    rw [sourceHorizontalAbelianCyclicClass_socleOrder,
      sourceHorizontalAbelianElementaryClass_socleOrder] at hs
    have hpow : (p : ℕ) ^ 1 < (p : ℕ) ^ (m + 2) :=
      Nat.pow_lt_pow_right p.2.one_lt (Nat.succ_lt_succ (Nat.zero_lt_succ m))
    simp only [pow_one] at hpow
    exact (ne_of_lt hpow) hs
  · have horder := congrArg AbelianZetaGroupClass.order (hnC.symm.trans hmC)
    rw [sourceHorizontalAbelianCyclicClass_order p (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)),
      sourceHorizontalAbelianCyclicClass_order p (m + 1)
        (Nat.succ_le_succ (Nat.zero_le m))] at horder
    have hexp : 2 * (n + 1) = 2 * (m + 1) :=
      (Nat.pow_right_injective p.2.two_le) horder
    have hsucc : n + 1 = m + 1 :=
      Nat.mul_left_cancel (Nat.zero_lt_succ 1) hexp
    exact hnm (Nat.add_right_cancel hsucc)

theorem measurableSet_sourceHorizontalClassAperture (p : Nat.Primes) (n : ℕ) :
    MeasurableSet (sourceHorizontalClassAperture p n) :=
  MeasurableSet.of_discrete

/-- Exact event mass: finite additivity turns the two singleton masses into the previously defined
source-horizontal admission. -/
theorem sourceHorizontalClassAperture_real
    (theta : AbelianZetaConvergentParameters) (p : Nat.Primes) (n : ℕ) :
    (classLaw theta.toAbelianZetaParameters).real (sourceHorizontalClassAperture p n) =
      sourceHorizontalAbelianTwoClassAdmission theta p (n + 1) := by
  have hne := sourceHorizontalClassAperture_classes_ne p n
  have hdisj : Disjoint
      ({sourceHorizontalAbelianElementaryClass p (n + 1)} : Set AbelianZetaGroupClass)
      {sourceHorizontalAbelianCyclicClass p (n + 1)} := by
    simp [hne]
  rw [measureReal_def]
  unfold sourceHorizontalClassAperture sourceHorizontalAbelianTwoClassAdmission
  rw [show ({sourceHorizontalAbelianElementaryClass p (n + 1),
      sourceHorizontalAbelianCyclicClass p (n + 1)} : Set AbelianZetaGroupClass) =
      {sourceHorizontalAbelianElementaryClass p (n + 1)} ∪
      {sourceHorizontalAbelianCyclicClass p (n + 1)} by
        ext x
        simp [or_comm]]
  rw [measure_union hdisj (MeasurableSet.singleton _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

/-- Sharp forward source-law exponential aperture estimate. -/
theorem sourceHorizontalForwardClassAperture_real_le
    (p : Nat.Primes) (n : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (classLaw
        (sourceHorizontalAbelianForwardParameters a ha0 ha1).toAbelianZetaParameters).real
        (sourceHorizontalClassAperture p n) ≤
      (2 * (sourceHorizontalAbelianForwardParameters a ha0 ha1).ennNormalizer.toReal) *
        Real.exp (-((2 - a) * Real.log (p : ℝ)) * ((n + 1 : ℕ) : ℝ)) := by
  rw [sourceHorizontalClassAperture_real,
    sourceHorizontalAbelianForwardAdmission_eq p (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) ha0 ha1]
  let c := (sourceHorizontalAbelianForwardParameters a ha0 ha1).ennNormalizer.toReal
  let target : ℝ := (p : ℝ) ^ (-((2 - a) * ((n + 1 : ℕ) : ℝ)))
  change c * ((p : ℝ) ^ ((a - 2) * (((n + 1 : ℕ) : ℝ) + 1)) +
      (p : ℝ) ^ (-2 * (((n + 1 : ℕ) : ℝ)) - 1 + a)) ≤
    (2 * c) * Real.exp (-((2 - a) * Real.log (p : ℝ)) * ((n + 1 : ℕ) : ℝ))
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hfirst :
      (p : ℝ) ^ ((a - 2) * (((n + 1 : ℕ) : ℝ) + 1)) ≤ target := by
    apply Real.rpow_le_rpow_of_exponent_le hp1
    have hn : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hsecond :
      (p : ℝ) ^ (-2 * (((n + 1 : ℕ) : ℝ)) - 1 + a) ≤ target := by
    apply Real.rpow_le_rpow_of_exponent_le hp1
    have hn : 1 ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  calc
    c * ((p : ℝ) ^ ((a - 2) * (((n + 1 : ℕ) : ℝ) + 1)) +
        (p : ℝ) ^ (-2 * (((n + 1 : ℕ) : ℝ)) - 1 + a)) ≤ c * (2 * target) := by
      gcongr
      linarith
    _ = (2 * c) * Real.exp (-((2 - a) * Real.log (p : ℝ)) *
        ((n + 1 : ℕ) : ℝ)) := by
      rw [show target = Real.exp (-((2 - a) * Real.log (p : ℝ)) *
          ((n + 1 : ℕ) : ℝ)) by
        rw [show target = (p : ℝ) ^ (-((2 - a) * ((n + 1 : ℕ) : ℝ))) by rfl,
          Real.rpow_def_of_pos hp0]
        congr 1
        ring]
      ring

/-- Sharp reverse source-law exponential aperture estimate. -/
theorem sourceHorizontalReverseClassAperture_real_le
    (p : Nat.Primes) (n : ℕ) {a : ℝ} (ha0 : 0 ≤ a) :
    (classLaw
        (sourceHorizontalAbelianReverseParameters a ha0).toAbelianZetaParameters).real
        (sourceHorizontalClassAperture p n) ≤
      (2 * (sourceHorizontalAbelianReverseParameters a ha0).ennNormalizer.toReal) *
        Real.exp (-(2 * Real.log (p : ℝ)) * ((n + 1 : ℕ) : ℝ)) := by
  rw [sourceHorizontalClassAperture_real,
    sourceHorizontalAbelianReverseAdmission_eq p (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) ha0]
  let c := (sourceHorizontalAbelianReverseParameters a ha0).ennNormalizer.toReal
  let target : ℝ := (p : ℝ) ^ (-(2 * ((n + 1 : ℕ) : ℝ)))
  change c * ((p : ℝ) ^ (-(a + 2) * (((n + 1 : ℕ) : ℝ) + 1)) +
      (p : ℝ) ^ (-2 * (((n + 1 : ℕ) : ℝ)) - 1 - a)) ≤
    (2 * c) * Real.exp (-(2 * Real.log (p : ℝ)) * ((n + 1 : ℕ) : ℝ))
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hfirst :
      (p : ℝ) ^ (-(a + 2) * (((n + 1 : ℕ) : ℝ) + 1)) ≤ target := by
    apply Real.rpow_le_rpow_of_exponent_le hp1
    have hn : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hsecond :
      (p : ℝ) ^ (-2 * (((n + 1 : ℕ) : ℝ)) - 1 - a) ≤ target := by
    apply Real.rpow_le_rpow_of_exponent_le hp1
    linarith
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  calc
    c * ((p : ℝ) ^ (-(a + 2) * (((n + 1 : ℕ) : ℝ) + 1)) +
        (p : ℝ) ^ (-2 * (((n + 1 : ℕ) : ℝ)) - 1 - a)) ≤ c * (2 * target) := by
      gcongr
      linarith
    _ = (2 * c) * Real.exp (-(2 * Real.log (p : ℝ)) * ((n + 1 : ℕ) : ℝ)) := by
      rw [show target = Real.exp (-(2 * Real.log (p : ℝ)) *
          ((n + 1 : ℕ) : ℝ)) by
        rw [show target = (p : ℝ) ^ (-(2 * ((n + 1 : ℕ) : ℝ))) by rfl,
          Real.rpow_def_of_pos hp0]
        congr 1
        ring]
      ring

private theorem forwardNormalizer_pos
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    0 < (sourceHorizontalAbelianForwardParameters a ha0 ha1).ennNormalizer.toReal :=
  ENNReal.toReal_pos
    (AbelianZetaConvergentParameters.ennNormalizer_ne_zero _)
    (ennNormalizer_ne_top _)

private theorem reverseNormalizer_pos {a : ℝ} (ha0 : 0 ≤ a) :
    0 < (sourceHorizontalAbelianReverseParameters a ha0).ennNormalizer.toReal :=
  ENNReal.toReal_pos
    (AbelianZetaConvergentParameters.ennNormalizer_ne_zero _)
    (ennNormalizer_ne_top _)

/-- The forward literal source-height partition function is finite throughout its sharp tilt
range, with the exact disjoint-aperture decomposition. -/
theorem sourceHorizontalForward_partition
    (p : Nat.Primes) {a lambda : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hlambda : 0 < lambda) (hlt : lambda < (2 - a) * Real.log (p : ℝ)) :
    let mu := classLaw
      (sourceHorizontalAbelianForwardParameters a ha0 ha1).toAbelianZetaParameters
    let H := apertureGauge (sourceHorizontalClassAperture p)
      (fun n => ((n + 1 : ℕ) : ℝ))
    Integrable (fun x => Real.exp (lambda * H x)) mu ∧
      (∫ x, Real.exp (lambda * H x) ∂mu) =
        mu.real ((⋃ n, sourceHorizontalClassAperture p n)ᶜ) +
          ∑' n, Real.exp (lambda * ((n + 1 : ℕ) : ℝ)) *
            mu.real (sourceHorizontalClassAperture p n) := by
  dsimp only
  let theta := sourceHorizontalAbelianForwardParameters a ha0 ha1
  let mu := classLaw theta.toAbelianZetaParameters
  let C : ℝ := 2 * theta.ennNormalizer.toReal
  let beta : ℝ := (2 - a) * Real.log (p : ℝ)
  have hC : 0 < C := mul_pos (by linarith) (forwardNormalizer_pos ha0 ha1)
  have hsum : Summable (fun n =>
      Real.exp (lambda * ((n + 1 : ℕ) : ℝ)) *
        mu.real (sourceHorizontalClassAperture p n)) := by
    have h := summable_exp_stretchedApertureMass mu (sourceHorizontalClassAperture p)
      C beta 1 lambda hC (by positivity) hlambda.le (by simpa [beta] using hlt)
      (fun n => by
        simpa [mu, theta, C, beta, Real.rpow_one] using
          sourceHorizontalForwardClassAperture_real_le p n ha0 ha1)
    simpa [Real.rpow_one] using h
  have hint := integrable_exp_apertureGauge_of_summable mu
    (sourceHorizontalClassAperture p) (measurableSet_sourceHorizontalClassAperture p)
    (pairwise_disjoint_sourceHorizontalClassAperture p)
    (fun n => ((n + 1 : ℕ) : ℝ)) (fun _ => by positivity) lambda hlambda.le hsum
  refine ⟨hint, ?_⟩
  exact integral_exp_apertureGauge mu (sourceHorizontalClassAperture p)
    (measurableSet_sourceHorizontalClassAperture p)
    (pairwise_disjoint_sourceHorizontalClassAperture p)
    (fun n => ((n + 1 : ℕ) : ℝ)) lambda hint

/-- Reverse analogue of `sourceHorizontalForward_partition`. -/
theorem sourceHorizontalReverse_partition
    (p : Nat.Primes) {a lambda : ℝ} (ha0 : 0 ≤ a)
    (hlambda : 0 < lambda) (hlt : lambda < 2 * Real.log (p : ℝ)) :
    let mu := classLaw
      (sourceHorizontalAbelianReverseParameters a ha0).toAbelianZetaParameters
    let H := apertureGauge (sourceHorizontalClassAperture p)
      (fun n => ((n + 1 : ℕ) : ℝ))
    Integrable (fun x => Real.exp (lambda * H x)) mu ∧
      (∫ x, Real.exp (lambda * H x) ∂mu) =
        mu.real ((⋃ n, sourceHorizontalClassAperture p n)ᶜ) +
          ∑' n, Real.exp (lambda * ((n + 1 : ℕ) : ℝ)) *
            mu.real (sourceHorizontalClassAperture p n) := by
  dsimp only
  let theta := sourceHorizontalAbelianReverseParameters a ha0
  let mu := classLaw theta.toAbelianZetaParameters
  let C : ℝ := 2 * theta.ennNormalizer.toReal
  let beta : ℝ := 2 * Real.log (p : ℝ)
  have hC : 0 < C := mul_pos (by linarith) (reverseNormalizer_pos ha0)
  have hsum : Summable (fun n =>
      Real.exp (lambda * ((n + 1 : ℕ) : ℝ)) *
        mu.real (sourceHorizontalClassAperture p n)) := by
    have h := summable_exp_stretchedApertureMass mu (sourceHorizontalClassAperture p)
      C beta 1 lambda hC (by positivity) hlambda.le (by simpa [beta] using hlt)
      (fun n => by
        simpa [mu, theta, C, beta, Real.rpow_one] using
          sourceHorizontalReverseClassAperture_real_le p n ha0)
    simpa [Real.rpow_one] using h
  have hint := integrable_exp_apertureGauge_of_summable mu
    (sourceHorizontalClassAperture p) (measurableSet_sourceHorizontalClassAperture p)
    (pairwise_disjoint_sourceHorizontalClassAperture p)
    (fun n => ((n + 1 : ℕ) : ℝ)) (fun _ => by positivity) lambda hlambda.le hsum
  refine ⟨hint, ?_⟩
  exact integral_exp_apertureGauge mu (sourceHorizontalClassAperture p)
    (measurableSet_sourceHorizontalClassAperture p)
    (pairwise_disjoint_sourceHorizontalClassAperture p)
    (fun n => ((n + 1 : ℕ) : ℝ)) lambda hint

/-- Every finite-KL renewal of the forward class law has a finite complete cofinal occupation
moment and obeys the global entropy budget. -/
theorem sourceHorizontalForward_entropyMoment
    (p : Nat.Primes) {a lambda : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hlambda : 0 < lambda) (hlt : lambda < (2 - a) * Real.log (p : ℝ))
    (nu : Measure AbelianZetaGroupClass) [IsProbabilityMeasure nu]
    (hfin : klDiv nu
      (classLaw
        (sourceHorizontalAbelianForwardParameters a ha0 ha1).toAbelianZetaParameters) ≠ ⊤) :
    Summable (fun n => ((n + 1 : ℕ) : ℝ) *
      nu.real (sourceHorizontalClassAperture p n)) ∧
      lambda * (∑' n, ((n + 1 : ℕ) : ℝ) *
        nu.real (sourceHorizontalClassAperture p n)) ≤
        (klDiv nu (classLaw
          (sourceHorizontalAbelianForwardParameters a ha0 ha1).toAbelianZetaParameters)).toReal +
          Real.log (∫ x, Real.exp (lambda * apertureGauge
            (sourceHorizontalClassAperture p) (fun n => ((n + 1 : ℕ) : ℝ)) x) ∂
              (classLaw
                (sourceHorizontalAbelianForwardParameters a ha0 ha1).toAbelianZetaParameters)) := by
  let theta := sourceHorizontalAbelianForwardParameters a ha0 ha1
  let mu := classLaw theta.toAbelianZetaParameters
  let C : ℝ := 2 * theta.ennNormalizer.toReal
  let beta : ℝ := (2 - a) * Real.log (p : ℝ)
  have hC : 0 < C := mul_pos (by linarith) (forwardNormalizer_pos ha0 ha1)
  have h := stretchedAperture_partition_entropyMoment mu nu
    (sourceHorizontalClassAperture p) (measurableSet_sourceHorizontalClassAperture p)
    (pairwise_disjoint_sourceHorizontalClassAperture p) C beta 1 lambda
    hC (by positivity) hlambda (by simpa [beta] using hlt)
    (fun n => by
      simpa [mu, theta, C, beta, Real.rpow_one] using
        sourceHorizontalForwardClassAperture_real_le p n ha0 ha1)
    (by simpa [mu, theta] using hfin)
  constructor
  · simpa using h.2.2.2.2.1
  · simpa [mu, theta] using h.2.2.2.2.2

/-- Reverse finite-KL source renewal has the same complete cofinal occupation conservation law. -/
theorem sourceHorizontalReverse_entropyMoment
    (p : Nat.Primes) {a lambda : ℝ} (ha0 : 0 ≤ a)
    (hlambda : 0 < lambda) (hlt : lambda < 2 * Real.log (p : ℝ))
    (nu : Measure AbelianZetaGroupClass) [IsProbabilityMeasure nu]
    (hfin : klDiv nu
      (classLaw
        (sourceHorizontalAbelianReverseParameters a ha0).toAbelianZetaParameters) ≠ ⊤) :
    Summable (fun n => ((n + 1 : ℕ) : ℝ) *
      nu.real (sourceHorizontalClassAperture p n)) ∧
      lambda * (∑' n, ((n + 1 : ℕ) : ℝ) *
        nu.real (sourceHorizontalClassAperture p n)) ≤
        (klDiv nu (classLaw
          (sourceHorizontalAbelianReverseParameters a ha0).toAbelianZetaParameters)).toReal +
          Real.log (∫ x, Real.exp (lambda * apertureGauge
            (sourceHorizontalClassAperture p) (fun n => ((n + 1 : ℕ) : ℝ)) x) ∂
              (classLaw
                (sourceHorizontalAbelianReverseParameters a ha0).toAbelianZetaParameters)) := by
  let theta := sourceHorizontalAbelianReverseParameters a ha0
  let mu := classLaw theta.toAbelianZetaParameters
  let C : ℝ := 2 * theta.ennNormalizer.toReal
  let beta : ℝ := 2 * Real.log (p : ℝ)
  have hC : 0 < C := mul_pos (by linarith) (reverseNormalizer_pos ha0)
  have h := stretchedAperture_partition_entropyMoment mu nu
    (sourceHorizontalClassAperture p) (measurableSet_sourceHorizontalClassAperture p)
    (pairwise_disjoint_sourceHorizontalClassAperture p) C beta 1 lambda
    hC (by positivity) hlambda (by simpa [beta] using hlt)
    (fun n => by
      simpa [mu, theta, C, beta, Real.rpow_one] using
        sourceHorizontalReverseClassAperture_real_le p n ha0)
    (by simpa [mu, theta] using hfin)
  constructor
  · simpa using h.2.2.2.2.1
  · simpa [mu, theta] using h.2.2.2.2.2

/-- Every finite-action forward renewal has summable mass-weighted adaptive Jeffreys current, and
that current evacuates grade by grade. -/
theorem sourceHorizontalForward_adaptiveCurrent_summable
    (p : Nat.Primes) {a lambda : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hlambda : 0 < lambda) (hlt : lambda < (2 - a) * Real.log (p : ℝ))
    (nu : Measure AbelianZetaGroupClass) [IsProbabilityMeasure nu]
    (hfin : klDiv nu
      (classLaw
        (sourceHorizontalAbelianForwardParameters a ha0 ha1).toAbelianZetaParameters) ≠ ⊤) :
    let J := fun n => nu.real (sourceHorizontalClassAperture p n) *
      sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a)
    Summable J ∧
      (∑' n, J n) ≤
        ((2 * a * Real.log (p : ℝ)) / lambda) *
          ((klDiv nu (classLaw
            (sourceHorizontalAbelianForwardParameters a ha0 ha1).toAbelianZetaParameters)).toReal +
            Real.log (∫ x, Real.exp (lambda * apertureGauge
              (sourceHorizontalClassAperture p) (fun n => ((n + 1 : ℕ) : ℝ)) x) ∂
                (classLaw
                  (sourceHorizontalAbelianForwardParameters a ha0 ha1).toAbelianZetaParameters))) ∧
      Tendsto J atTop (nhds 0) := by
  dsimp only
  let theta := sourceHorizontalAbelianForwardParameters a ha0 ha1
  let mu := classLaw theta.toAbelianZetaParameters
  let C : ℝ := 2 * theta.ennNormalizer.toReal
  let beta : ℝ := (2 - a) * Real.log (p : ℝ)
  let K : ℝ := 2 * a * Real.log (p : ℝ)
  have hC : 0 < C := mul_pos (by linarith) (forwardNormalizer_pos ha0 ha1)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hW : ∀ n, 0 ≤ sourceHorizontalPrimeAdaptiveJeffreysWork p
      (((n + 1 : ℕ) : ℝ) * a) := fun n =>
    sourceHorizontalPrimeAdaptiveJeffreysWork_nonneg p _
  have hwork : ∀ n, sourceHorizontalPrimeAdaptiveJeffreysWork p
      (((n + 1 : ℕ) : ℝ) * a) ≤ K * ((n + 1 : ℕ) : ℝ) := by
    intro n
    have h := sourceHorizontalPrimeAdaptiveJeffreysWork_le_linear p
      (u := ((n + 1 : ℕ) * a)) (mul_nonneg (by positivity) ha0)
    calc
      sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a) ≤
          2 * (((n + 1 : ℕ) : ℝ) * a) * Real.log (p : ℝ) := h
      _ = K * ((n + 1 : ℕ) : ℝ) := by ring
  have h := exponentialAperture_totalLinearCurrent_bound mu nu
    (sourceHorizontalClassAperture p) (measurableSet_sourceHorizontalClassAperture p)
    (pairwise_disjoint_sourceHorizontalClassAperture p)
    (fun n => sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a))
    C beta lambda K hC hlambda (by simpa [beta] using hlt) hK hW
    (fun n => by
      simpa [mu, theta, C, beta] using
        sourceHorizontalForwardClassAperture_real_le p n ha0 ha1)
    hwork (by simpa [mu, theta] using hfin)
  refine ⟨h.1, ?_, h.1.tendsto_atTop_zero⟩
  simpa [mu, theta, K] using h.2

/-- Reverse counterpart of `sourceHorizontalForward_adaptiveCurrent_summable`. -/
theorem sourceHorizontalReverse_adaptiveCurrent_summable
    (p : Nat.Primes) {a lambda : ℝ} (ha0 : 0 ≤ a)
    (hlambda : 0 < lambda) (hlt : lambda < 2 * Real.log (p : ℝ))
    (nu : Measure AbelianZetaGroupClass) [IsProbabilityMeasure nu]
    (hfin : klDiv nu
      (classLaw
        (sourceHorizontalAbelianReverseParameters a ha0).toAbelianZetaParameters) ≠ ⊤) :
    let J := fun n => nu.real (sourceHorizontalClassAperture p n) *
      sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a)
    Summable J ∧
      (∑' n, J n) ≤
        ((2 * a * Real.log (p : ℝ)) / lambda) *
          ((klDiv nu (classLaw
            (sourceHorizontalAbelianReverseParameters a ha0).toAbelianZetaParameters)).toReal +
            Real.log (∫ x, Real.exp (lambda * apertureGauge
              (sourceHorizontalClassAperture p) (fun n => ((n + 1 : ℕ) : ℝ)) x) ∂
                (classLaw
                  (sourceHorizontalAbelianReverseParameters a ha0).toAbelianZetaParameters))) ∧
      Tendsto J atTop (nhds 0) := by
  dsimp only
  let theta := sourceHorizontalAbelianReverseParameters a ha0
  let mu := classLaw theta.toAbelianZetaParameters
  let C : ℝ := 2 * theta.ennNormalizer.toReal
  let beta : ℝ := 2 * Real.log (p : ℝ)
  let K : ℝ := 2 * a * Real.log (p : ℝ)
  have hC : 0 < C := mul_pos (by linarith) (reverseNormalizer_pos ha0)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hW : ∀ n, 0 ≤ sourceHorizontalPrimeAdaptiveJeffreysWork p
      (((n + 1 : ℕ) : ℝ) * a) := fun n =>
    sourceHorizontalPrimeAdaptiveJeffreysWork_nonneg p _
  have hwork : ∀ n, sourceHorizontalPrimeAdaptiveJeffreysWork p
      (((n + 1 : ℕ) : ℝ) * a) ≤ K * ((n + 1 : ℕ) : ℝ) := by
    intro n
    have h := sourceHorizontalPrimeAdaptiveJeffreysWork_le_linear p
      (u := ((n + 1 : ℕ) * a)) (mul_nonneg (by positivity) ha0)
    calc
      sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a) ≤
          2 * (((n + 1 : ℕ) : ℝ) * a) * Real.log (p : ℝ) := h
      _ = K * ((n + 1 : ℕ) : ℝ) := by ring
  have h := exponentialAperture_totalLinearCurrent_bound mu nu
    (sourceHorizontalClassAperture p) (measurableSet_sourceHorizontalClassAperture p)
    (pairwise_disjoint_sourceHorizontalClassAperture p)
    (fun n => sourceHorizontalPrimeAdaptiveJeffreysWork p (((n + 1 : ℕ) : ℝ) * a))
    C beta lambda K hC hlambda (by simpa [beta] using hlt) hK hW
    (fun n => by
      simpa [mu, theta, C, beta] using
        sourceHorizontalReverseClassAperture_real_le p n ha0)
    hwork (by simpa [mu, theta] using hfin)
  refine ⟨h.1, ?_, h.1.tendsto_atTop_zero⟩
  simpa [mu, theta, K] using h.2

end

end GaloisForLFunctions.HTGeometry
