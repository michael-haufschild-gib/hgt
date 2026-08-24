import GaloisForLFunctions.HTGeometry.CirclePoissonProductEquivalence
import GaloisForLFunctions.HTGeometry.CirclePoissonOuterFactor
import GaloisForLFunctions.HTGeometry.FiniteModificationZeroOneEquiv
import GaloisForLFunctions.HTGeometry.PrimeSieveTransitionSize
import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter
import GaloisForLFunctions.HTGeometry.ShortcutSpectralPhase
import GaloisForLFunctions.HTGeometry.InfiniteTorusEquidistribution
import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier
import GaloisForLFunctions.HTGeometry.TemporalCharacterWallCrossingLaw
import GaloisForLFunctions.RHTower.PrimeSchattenReflectionDuality
import GaloisForLFunctions.RHTower.PrimeClockEnergyDivergence
import GaloisForLFunctions.RHTower.PrimeClockShaleDiagonal
import GaloisForLFunctions.RHTower.PrimeDensityLocalUnitary
import GaloisForLFunctions.RHTower.SoninSemilocalGradingNoGo
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.HTGeometry.SchattenOneBanach
import GaloisForLFunctions.HTGeometry.LpCoordinateProjection
import GaloisForLFunctions.HTGeometry.LatticeL2Shift
import GaloisForLFunctions.HTGeometry.ZetaTailClosedModulus
import GaloisForLFunctions.HTGeometry.ScheffeCounting
import Mathlib.Analysis.Normed.Group.Tannery

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

noncomputable section

local instance : MeasurableSpace Circle :=
  instMeasurableSpaceCircle_galoisForLFunctions

/-- Canonical relabelling from an enumerated multiplicative-circle product to the additive prime
torus. -/
def natCircleHomeomorphPrimeTorus :
    (ℕ → Circle) ≃ₜ (Nat.Primes → UnitAddCircle) :=
  Homeomorph.piCongr natEquivPrimes fun _ =>
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

/-- Pull a finite prime character back through the canonical prime enumeration. -/
def pullPrimeFourierIndex (q : Nat.Primes →₀ ℤ) : ℕ →₀ ℤ :=
  (Finsupp.domCongr natEquivPrimes).symm q

@[simp]
theorem pullPrimeFourierIndex_apply (q : Nat.Primes →₀ ℤ) (n : ℕ) :
    pullPrimeFourierIndex q n = q (natEquivPrimes n) := by
  simp [pullPrimeFourierIndex]

theorem infiniteTorusFourier_natCircleHomeomorphPrimeTorus
    (q : Nat.Primes →₀ ℤ) (x : ℕ → Circle) :
    infiniteTorusFourier q (natCircleHomeomorphPrimeTorus x) =
      infiniteCircleFourier (pullPrimeFourierIndex q) x := by
  classical
  simp only [infiniteTorusFourier, infiniteCircleFourier, ContinuousMap.coe_mk,
    Finsupp.prod]
  rw [show q.support = (pullPrimeFourierIndex q).support.image natEquivPrimes by
    ext p
    simp only [Finsupp.mem_support_iff, Finset.mem_image]
    constructor
    · intro hp
      refine ⟨natEquivPrimes.symm p, ?_, natEquivPrimes.apply_symm_apply p⟩
      simpa [pullPrimeFourierIndex_apply] using hp
    · rintro ⟨n, hn, rfl⟩
      simpa [pullPrimeFourierIndex_apply] using hn]
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro n _
    rw [show natCircleHomeomorphPrimeTorus x (natEquivPrimes n) =
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (x n) by
      simp [natCircleHomeomorphPrimeTorus]]
    rw [pullPrimeFourierIndex_apply, fourier_apply, AddCircle.toCircle_zsmul]
    have he : AddCircle.toCircle
        ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (x n)) = x n := by
      rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
      exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply (x n)
    rw [he]
    exact Circle.coe_zpow (x n) (q (natEquivPrimes n))
  · exact natEquivPrimes.injective.injOn

theorem pullPrimeFourierIndex_prod {M : Type*} [CommMonoid M]
    (q : Nat.Primes →₀ ℤ) (f : Nat.Primes → ℤ → M) :
    (pullPrimeFourierIndex q).prod (fun n k => f (natEquivPrimes n) k) = q.prod f := by
  classical
  unfold Finsupp.prod
  rw [show q.support = (pullPrimeFourierIndex q).support.image natEquivPrimes by
    ext p
    simp only [Finsupp.mem_support_iff, Finset.mem_image]
    constructor
    · intro hp
      refine ⟨natEquivPrimes.symm p, ?_, natEquivPrimes.apply_symm_apply p⟩
      simpa [pullPrimeFourierIndex_apply] using hp
    · rintro ⟨n, hn, rfl⟩
      simpa [pullPrimeFourierIndex_apply] using hn]
  rw [Finset.prod_image natEquivPrimes.injective.injOn]
  apply Finset.prod_congr rfl
  intro n _
  rw [pullPrimeFourierIndex_apply]

/-- Reindexing the natural circle product and transporting each circle to the additive model gives
the product Poisson law on the literal prime torus. -/
theorem map_natCirclePoissonProductMeasure_eq_torusPoissonMeasure
    (a : Nat.Primes → CirclePoissonParameter) :
    Measure.map natCircleHomeomorphPrimeTorus
        (natCirclePoissonProductMeasure fun n => a (natEquivPrimes n)) =
      torusPoissonMeasure a := by
  let μ : ProbabilityMeasure (Nat.Primes → UnitAddCircle) :=
    ProbabilityMeasure.map
      (⟨natCirclePoissonProductMeasure (fun n => a (natEquivPrimes n)), inferInstance⟩ :
        ProbabilityMeasure (ℕ → Circle))
      natCircleHomeomorphPrimeTorus.continuous.aemeasurable
  let ν : ProbabilityMeasure (Nat.Primes → UnitAddCircle) :=
    torusPoissonProbabilityMeasure a
  have heq : μ = ν := by
    apply probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq
    intro q
    dsimp only [μ, ν]
    rw [ProbabilityMeasure.toMeasure_map]
    rw [integral_map natCircleHomeomorphPrimeTorus.continuous.aemeasurable
      (infiniteTorusFourier q).continuous.aestronglyMeasurable]
    simp_rw [infiniteTorusFourier_natCircleHomeomorphPrimeTorus]
    change (∫ x, infiniteCircleFourier (pullPrimeFourierIndex q) x
        ∂natCirclePoissonProductMeasure (fun n => a (natEquivPrimes n))) =
      ∫ x, infiniteTorusFourier q x ∂torusPoissonMeasure a
    rw [integral_infiniteCircleFourier_natCirclePoissonProductMeasure,
      integral_infiniteTorusFourier_torusPoissonMeasure]
    exact pullPrimeFourierIndex_prod q
      (fun p k => circlePoissonFourierMoment (a p) k)
  exact congrArg (fun ρ : ProbabilityMeasure (Nat.Primes → UnitAddCircle) =>
    (ρ : Measure (Nat.Primes → UnitAddCircle))) heq

theorem absolutelyContinuous_map_measurableEquiv_iff
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) :
    Measure.map e μ ≪ Measure.map e ν ↔ μ ≪ ν := by
  constructor
  · intro h
    have hpull := h.map e.symm.measurable
    have hcomp : e.symm ∘ e = id := by
      funext x
      exact e.symm_apply_apply x
    rwa [Measure.map_map e.symm.measurable e.measurable, hcomp, Measure.map_id,
      Measure.map_map e.symm.measurable e.measurable, hcomp, Measure.map_id] at hpull
  · intro h
    exact h.map e.measurable

theorem mutuallySingular_map_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) {μ ν : Measure α} (h : μ.MutuallySingular ν) :
    (Measure.map e μ).MutuallySingular (Measure.map e ν) := by
  rcases h with ⟨s, hs, hμ, hν⟩
  let t : Set β := e.symm ⁻¹' s
  have ht : MeasurableSet t := hs.preimage e.symm.measurable
  refine ⟨t, ht, ?_, ?_⟩
  · rw [Measure.map_apply e.measurable ht]
    have hpre : e ⁻¹' (e.symm ⁻¹' s) = s := by
      ext x
      simp
    rw [show e ⁻¹' t = s by exact hpre]
    exact hμ
  · rw [Measure.map_apply e.measurable ht.compl]
    have hpre : e ⁻¹' (e.symm ⁻¹' s)ᶜ = sᶜ := by
      ext x
      simp
    rw [show e ⁻¹' tᶜ = sᶜ by exact hpre]
    exact hν

/-- Exact Kakutani classification on the literal prime-indexed additive torus. -/
theorem torusPoissonMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq
    (a b : Nat.Primes → CirclePoissonParameter)
    (ha : Tendsto (fun n => (a (natEquivPrimes n) : ℂ)) atTop (𝓝 0))
    (hb : Tendsto (fun n => (b (natEquivPrimes n) : ℂ)) atTop (𝓝 0)) :
    ((torusPoissonMeasure a ≪ torusPoissonMeasure b) ∧
        torusPoissonMeasure b ≪ torusPoissonMeasure a) ↔
      Summable (fun p => ‖(a p : ℂ) - (b p : ℂ)‖ ^ 2) := by
  let an : ℕ → CirclePoissonParameter := fun n => a (natEquivPrimes n)
  let bn : ℕ → CirclePoissonParameter := fun n => b (natEquivPrimes n)
  rw [← map_natCirclePoissonProductMeasure_eq_torusPoissonMeasure a,
    ← map_natCirclePoissonProductMeasure_eq_torusPoissonMeasure b]
  change ((Measure.map natCircleHomeomorphPrimeTorus.toMeasurableEquiv
      (natCirclePoissonProductMeasure an) ≪
      Measure.map natCircleHomeomorphPrimeTorus.toMeasurableEquiv
        (natCirclePoissonProductMeasure bn)) ∧
    Measure.map natCircleHomeomorphPrimeTorus.toMeasurableEquiv
      (natCirclePoissonProductMeasure bn) ≪
      Measure.map natCircleHomeomorphPrimeTorus.toMeasurableEquiv
        (natCirclePoissonProductMeasure an)) ↔ _
  rw [absolutelyContinuous_map_measurableEquiv_iff,
    absolutelyContinuous_map_measurableEquiv_iff]
  rw [natCirclePoissonProductMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq
    an bn (by simpa [an] using ha) (by simpa [bn] using hb)]
  change Summable ((fun p : Nat.Primes => ‖(a p : ℂ) - (b p : ℂ)‖ ^ 2) ∘
      natEquivPrimes) ↔ Summable (fun p => ‖(a p : ℂ) - (b p : ℂ)‖ ^ 2)
  exact natEquivPrimes.summable_iff

theorem torusPoissonMeasure_mutuallySingular_of_not_summable_normSq
    (a b : Nat.Primes → CirclePoissonParameter)
    (hdiv : ¬ Summable (fun p => ‖(a p : ℂ) - (b p : ℂ)‖ ^ 2)) :
    (torusPoissonMeasure a).MutuallySingular (torusPoissonMeasure b) := by
  let an : ℕ → CirclePoissonParameter := fun n => a (natEquivPrimes n)
  let bn : ℕ → CirclePoissonParameter := fun n => b (natEquivPrimes n)
  have hdivNat : ¬ Summable (fun n => ‖(an n : ℂ) - (bn n : ℂ)‖ ^ 2) := by
    intro h
    apply hdiv
    apply natEquivPrimes.summable_iff.mp
    change Summable (fun n => ‖(an n : ℂ) - (bn n : ℂ)‖ ^ 2)
    exact h
  have hsing := natCirclePoissonProductMeasure_mutuallySingular_of_not_summable_normSq
    an bn hdivNat
  have hmap := mutuallySingular_map_measurableEquiv
    natCircleHomeomorphPrimeTorus.toMeasurableEquiv hsing
  change (Measure.map natCircleHomeomorphPrimeTorus
      (natCirclePoissonProductMeasure an)).MutuallySingular
    (Measure.map natCircleHomeomorphPrimeTorus
      (natCirclePoissonProductMeasure bn)) at hmap
  dsimp only [an, bn] at hmap
  rwa [map_natCirclePoissonProductMeasure_eq_torusPoissonMeasure,
    map_natCirclePoissonProductMeasure_eq_torusPoissonMeasure] at hmap

/-- Along the canonical prime enumeration, every positive-horizontal-coordinate Poisson
parameter tends to the disk origin. -/
theorem tendsto_primePoissonParameter_natEquivPrimes_zero
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    Tendsto
      (fun n => ((primePoissonParameter sigma t hsigma (natEquivPrimes n) :
        CirclePoissonParameter) : ℂ)) atTop (nhds 0) := by
  have hpNat : Tendsto (fun n => ((natEquivPrimes n : Nat.Primes) : ℕ)) atTop atTop :=
    tendsto_primeIndex_atTop natEquivPrimes
  have hpReal : Tendsto (fun n => ((natEquivPrimes n : Nat.Primes) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpNat
  have hlog : Tendsto
      (fun n => Real.log ((natEquivPrimes n : Nat.Primes) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hpReal
  have hneg : Tendsto
      (fun n => -sigma * Real.log ((natEquivPrimes n : Nat.Primes) : ℝ)) atTop atBot :=
    hlog.const_mul_atTop_of_neg (neg_lt_zero.mpr hsigma)
  have hexp : Tendsto
      (fun n => Real.exp (-sigma * Real.log ((natEquivPrimes n : Nat.Primes) : ℝ)))
        atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa [norm_primePoissonParameterValue] using hexp

/-- The squared prime-Poisson parameter is summable exactly to the right of the critical wall. -/
theorem summable_normSq_primePoissonParameter_zero_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    Summable (fun p : Nat.Primes =>
      ‖((primePoissonParameter sigma t hsigma p : CirclePoissonParameter) : ℂ) - 0‖ ^ 2) ↔
      1 / 2 < sigma := by
  rw [show (fun p : Nat.Primes =>
      ‖((primePoissonParameter sigma t hsigma p : CirclePoissonParameter) : ℂ) - 0‖ ^ 2) =
      GaloisForLFunctions.primeSchattenMass sigma 2 by
    funext p
    rw [sub_zero, coe_primePoissonParameter, norm_primePoissonParameterValue]
    have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
    rw [GaloisForLFunctions.primeSchattenMass, Real.rpow_def_of_pos hp, pow_two,
      ← Real.exp_add]
    congr 1
    ring]
  rw [GaloisForLFunctions.summable_primeSchattenMass_iff]
  constructor <;> intro h <;> linarith

/-- Zero Poisson parameters give exactly Haar probability on a countable product torus. -/
theorem torusPoissonMeasure_zero_eq_torusHaar
    (I : Type*) [Countable I] [DecidableEq I] :
    torusPoissonMeasure (fun _ : I => (0 : CirclePoissonParameter)) = torusHaar I := by
  let mu : ProbabilityMeasure (I → UnitAddCircle) :=
    torusPoissonProbabilityMeasure (fun _ : I => (0 : CirclePoissonParameter))
  let nu : ProbabilityMeasure (I → UnitAddCircle) :=
    ⟨torusHaar I, inferInstance⟩
  have hmu : mu = nu := by
    apply probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq
    intro q
    dsimp only [mu, nu]
    change (∫ x, infiniteTorusFourier q x
        ∂torusPoissonMeasure (fun _ : I => (0 : CirclePoissonParameter))) =
      ∫ x, infiniteTorusFourier q x ∂torusHaar I
    rw [integral_infiniteTorusFourier_torusPoissonMeasure]
    have hcharacter : (fun x => infiniteTorusFourier q x) = fun x => torusCharacter q x := by
      funext x
      simp only [infiniteTorusFourier, torusCharacter, ContinuousMap.coe_mk]
      rfl
    rw [hcharacter, integral_torusCharacter]
    by_cases hq : q = 0
    · subst q
      simp [circlePoissonFourierMoment]
    · rw [if_neg hq]
      obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
        by_contra h
        push Not at h
        exact hq (Finsupp.ext fun i => h i)
      unfold Finsupp.prod
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      cases hqi : q i with
      | ofNat n =>
          have hn : n ≠ 0 := by
            intro hn
            subst n
            exact hi hqi
          simpa [circlePoissonFourierMoment, hqi] using (zero_pow hn : (0 : ℂ) ^ n = 0)
      | negSucc n => simp [circlePoissonFourierMoment]
  exact congrArg (fun rho : ProbabilityMeasure (I → UnitAddCircle) =>
    (rho : Measure (I → UnitAddCircle))) hmu

/-- Prime Poisson law lies in the Haar measure class exactly to the right of the critical wall. -/
theorem primePoissonMeasure_mutuallyAbsolutelyContinuous_torusHaar_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    ((primePoissonMeasure sigma t hsigma ≪ torusHaar Nat.Primes) ∧
        torusHaar Nat.Primes ≪ primePoissonMeasure sigma t hsigma) ↔
      1 / 2 < sigma := by
  rw [← torusPoissonMeasure_zero_eq_torusHaar Nat.Primes]
  rw [primePoissonMeasure,
    torusPoissonMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq
      (primePoissonParameter sigma t hsigma)
      (fun _ : Nat.Primes => (0 : CirclePoissonParameter))
      (tendsto_primePoissonParameter_natEquivPrimes_zero sigma t hsigma)
      tendsto_const_nhds]
  exact summable_normSq_primePoissonParameter_zero_iff sigma t hsigma

/-- On and left of the critical wall, prime Poisson law is singular to Haar probability. -/
theorem primePoissonMeasure_mutuallySingular_torusHaar_of_le_half
    (sigma t : ℝ) (hsigma : 0 < sigma) (hwall : sigma ≤ 1 / 2) :
    (primePoissonMeasure sigma t hsigma).MutuallySingular (torusHaar Nat.Primes) := by
  rw [← torusPoissonMeasure_zero_eq_torusHaar Nat.Primes]
  apply torusPoissonMeasure_mutuallySingular_of_not_summable_normSq
  intro hsum
  have hright :=
    (summable_normSq_primePoissonParameter_zero_iff sigma t hsigma).mp hsum
  exact (not_lt_of_ge hwall) hright

/-- Normality of the prime Poisson spectral measure relative to Haar has the exact threshold
`sigma > 1/2`. -/
theorem primePoissonMeasure_absolutelyContinuous_torusHaar_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    primePoissonMeasure sigma t hsigma ≪ torusHaar Nat.Primes ↔ 1 / 2 < sigma := by
  constructor
  · intro hac
    by_contra hright
    have hwall : sigma ≤ 1 / 2 := le_of_not_gt hright
    rcases primePoissonMeasure_mutuallySingular_torusHaar_of_le_half
        sigma t hsigma hwall with ⟨s, hs, hmus, hhaar⟩
    have hmucomp : primePoissonMeasure sigma t hsigma sᶜ = 0 := hac hhaar
    have huniv : primePoissonMeasure sigma t hsigma Set.univ = 0 := by
      calc
        primePoissonMeasure sigma t hsigma Set.univ =
            primePoissonMeasure sigma t hsigma (s ∪ sᶜ) := by rw [union_compl_self]
        _ = primePoissonMeasure sigma t hsigma s +
            primePoissonMeasure sigma t hsigma sᶜ :=
          measure_union disjoint_compl_right hs.compl
        _ = 0 := by rw [hmus, hmucomp]; simp
    have hone : primePoissonMeasure sigma t hsigma Set.univ = 1 := measure_univ
    rw [hone] at huniv
    exact one_ne_zero huniv
  · intro hright
    exact (primePoissonMeasure_mutuallyAbsolutelyContinuous_torusHaar_iff
      sigma t hsigma).mpr hright |>.1

/-- The harmonic prime-clock defect is never summable at a nonzero frequency. -/
theorem not_summable_primeClockDefect {tau : ℝ} (htau : tau ≠ 0) :
    ¬ Summable (fun p : Nat.Primes =>
      (1 - Real.cos (tau * Real.log (p : ℝ))) / (p : ℝ)) := by
  intro hsum
  let G : ℕ → ℝ := fun n =>
    if n.Prime then (1 - Real.cos (tau * Real.log (n : ℝ))) / (n : ℝ) else 0
  have hGnonneg : ∀ n, 0 ≤ G n := by
    intro n
    simp only [G]
    by_cases hn : n.Prime
    · rw [if_pos hn]
      exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Nat.cast_nonneg n)
    · rw [if_neg hn]
  have hGeq : ∀ p : Nat.Primes, G (p : ℕ) =
      (1 - Real.cos (tau * Real.log (p : ℝ))) / (p : ℝ) := by
    intro p
    simp only [G, if_pos p.prop]
  have hzero : ∀ n ∉ Set.range (fun p : Nat.Primes => (p : ℕ)), G n = 0 := by
    intro n hn
    have hnprime : ¬ n.Prime := fun hp => hn ⟨⟨n, hp⟩, rfl⟩
    simp only [G, if_neg hnprime]
  have hsupp : Function.support G ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
    intro n hn
    by_contra hnr
    exact hn (hzero n hnr)
  have hGsummable : Summable G :=
    (Function.Injective.summable_iff (fun a b h => Subtype.ext h) hzero).mp
      (hsum.congr fun p => (hGeq p).symm)
  have hbound (x : ℝ) : RHTower.primeClockEnergy tau x ≤ ∑' n, G n := by
    rw [RHTower.primeClockEnergy]
    have hfin :
        ∑ p ∈ Nat.primesLE ⌊x⌋₊,
            (1 - Real.cos (tau * Real.log p)) / p =
          ∑ n ∈ Nat.primesLE ⌊x⌋₊, G n := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [G, if_pos (Nat.prime_of_mem_primesLE hp)]
    rw [hfin]
    exact hGsummable.sum_le_tsum (Nat.primesLE ⌊x⌋₊) (fun n _ => hGnonneg n)
  have heventually : ∀ᶠ x in atTop,
      (∑' n, G n) + 1 ≤ RHTower.primeClockEnergy tau x :=
    (tendsto_atTop.1 (RHTower.tendsto_primeClockEnergy_atTop htau)) ((∑' n, G n) + 1)
  obtain ⟨x, hx⟩ := heventually.exists
  linarith [hbound x]

/-- Polar factorization of the literal prime Poisson disk parameter. -/
theorem primePoissonParameterValue_eq_radius_mul_phase
    (sigma t : ℝ) (p : Nat.Primes) :
    primePoissonParameterValue sigma t p =
      ((Real.exp (-sigma * Real.log (p : ℝ)) : ℝ) : ℂ) *
        Complex.exp (((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [primePoissonParameterValue]
  have hexponent :
      ((((-sigma : ℝ) : ℂ) + (t : ℂ) * Complex.I) * (Real.log (p : ℝ) : ℂ)) =
        ((-sigma * Real.log (p : ℝ) : ℝ) : ℂ) +
          ((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexponent, Complex.exp_add]
  simp

/-- Squared displacement of two critical-line prime parameters is the literal prime-clock defect. -/
theorem normSq_primePoissonParameter_half_sub_eq_primeClockDefect
    (t u : ℝ) (p : Nat.Primes) :
    ‖primePoissonParameterValue (1 / 2) t p -
        primePoissonParameterValue (1 / 2) u p‖ ^ 2 =
      2 * (1 - Real.cos ((t - u) * Real.log (p : ℝ))) / (p : ℝ) := by
  rw [primePoissonParameterValue_eq_radius_mul_phase,
    primePoissonParameterValue_eq_radius_mul_phase, ← mul_sub, norm_mul, mul_pow,
    normSq_expI_sub]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hradius : Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) ^ 2 = 1 / (p : ℝ) := by
    rw [pow_two, ← Real.exp_add]
    rw [show -(1 / 2 : ℝ) * Real.log (p : ℝ) +
        -(1 / 2 : ℝ) * Real.log (p : ℝ) =
        Real.log (p : ℝ) * (-1 : ℝ) by ring]
    rw [← Real.rpow_def_of_pos hp, Real.rpow_neg_one]
    simp [one_div]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), hradius]
  rw [show t * Real.log (p : ℝ) - u * Real.log (p : ℝ) =
      (t - u) * Real.log (p : ℝ) by ring]
  ring

/-- Distinct critical heights have divergent squared prime-parameter displacement. -/
theorem not_summable_normSq_primePoissonParameter_half_sub_of_ne
    {t u : ℝ} (htu : t ≠ u) :
    ¬ Summable (fun p : Nat.Primes =>
      ‖primePoissonParameterValue (1 / 2) t p -
        primePoissonParameterValue (1 / 2) u p‖ ^ 2) := by
  intro hsum
  apply not_summable_primeClockDefect (sub_ne_zero.mpr htu)
  apply (summable_mul_left_iff (by norm_num : (2 : ℝ) ≠ 0)).mp
  exact hsum.congr fun p => by
    rw [normSq_primePoissonParameter_half_sub_eq_primeClockDefect]
    ring

/-- Product Poisson spectral laws at distinct critical heights are mutually singular. -/
theorem primePoissonMeasure_half_mutuallySingular_of_ne
    {t u : ℝ} (htu : t ≠ u) :
    (primePoissonMeasure (1 / 2) t (by norm_num)).MutuallySingular
      (primePoissonMeasure (1 / 2) u (by norm_num)) := by
  unfold primePoissonMeasure
  apply torusPoissonMeasure_mutuallySingular_of_not_summable_normSq
  simpa only [coe_primePoissonParameter] using
    not_summable_normSq_primePoissonParameter_half_sub_of_ne htu

/-- Squared displacement of reflected prime parameters is the corpus's prime-clock reflection
energy, independently of height. -/
theorem normSq_primePoissonParameterValue_reflection_sub
    (sigma t : ℝ) (p : Nat.Primes) :
    ‖primePoissonParameterValue sigma t p -
        primePoissonParameterValue (1 - sigma) t p‖ ^ 2 =
      RHTower.primeClockReflectionEnergy sigma p := by
  rw [primePoissonParameterValue_eq_radius_mul_phase,
    primePoissonParameterValue_eq_radius_mul_phase]
  rw [← sub_mul, norm_mul, mul_pow]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hpow (a : ℝ) : Real.exp (-a * Real.log (p : ℝ)) = (p : ℝ) ^ (-a) := by
    rw [Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, Real.exp_zero, mul_one]
  rw [sq_abs, hpow sigma, hpow (1 - sigma)]
  simp [RHTower.primeClockReflectionEnergy]

/-- Reflected prime-parameter displacement is square-summable exactly on the fixed wall. -/
theorem summable_normSq_primePoissonParameterValue_reflection_sub_iff
    (sigma t : ℝ) :
    Summable (fun p : Nat.Primes =>
      ‖primePoissonParameterValue sigma t p -
        primePoissonParameterValue (1 - sigma) t p‖ ^ 2) ↔
      sigma = 1 / 2 := by
  rw [show (fun p : Nat.Primes =>
      ‖primePoissonParameterValue sigma t p -
        primePoissonParameterValue (1 - sigma) t p‖ ^ 2) =
      RHTower.primeClockReflectionEnergy sigma by
    funext p
    exact normSq_primePoissonParameterValue_reflection_sub sigma t p]
  exact RHTower.summable_primeClockReflectionEnergy_iff sigma

/-- In the open critical strip, functional-equation-reflected product laws share a measure class
exactly at the fixed wall. -/
theorem primePoissonMeasure_reflection_mutuallyAbsolutelyContinuous_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    ((primePoissonMeasure sigma t hsigma ≪
          primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)) ∧
        primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1) ≪
          primePoissonMeasure sigma t hsigma) ↔
      sigma = 1 / 2 := by
  unfold primePoissonMeasure
  rw [torusPoissonMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq
    (primePoissonParameter sigma t hsigma)
    (primePoissonParameter (1 - sigma) t (sub_pos.mpr hsigma1))
    (tendsto_primePoissonParameter_natEquivPrimes_zero sigma t hsigma)
    (tendsto_primePoissonParameter_natEquivPrimes_zero
      (1 - sigma) t (sub_pos.mpr hsigma1))]
  simpa only [coe_primePoissonParameter] using
    summable_normSq_primePoissonParameterValue_reflection_sub_iff sigma t

/-- Off the fixed wall, reflected product laws are mutually singular. -/
theorem primePoissonMeasure_reflection_mutuallySingular_of_ne_half
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hwall : sigma ≠ 1 / 2) :
    (primePoissonMeasure sigma t hsigma).MutuallySingular
      (primePoissonMeasure (1 - sigma) t (sub_pos.mpr hsigma1)) := by
  unfold primePoissonMeasure
  apply torusPoissonMeasure_mutuallySingular_of_not_summable_normSq
  intro hsum
  exact hwall ((summable_normSq_primePoissonParameterValue_reflection_sub_iff
    sigma t).mp (by simpa only [coe_primePoissonParameter] using hsum))

/-- Prime-logarithm point of the additive torus implementing height translation. -/
def primeHeightPoint (h : ℝ) : Nat.Primes → UnitAddCircle :=
  clockPhasePoint (fun p : Nat.Primes => Real.log (p : ℝ)) h

/-- A finite-support Fourier character is multiplicative under point addition. -/
theorem infiniteTorusFourier_add_point_local
    {J : Type*} (q : J →₀ ℤ) (x y : J → UnitAddCircle) :
    infiniteTorusFourier q (x + y) =
      infiniteTorusFourier q x * infiniteTorusFourier q y := by
  classical
  simp only [infiniteTorusFourier, ContinuousMap.coe_mk, Finsupp.prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact fourier_add_arg (q j) (x j) (y j)

/-- Fourier value of the prime height point is its ordinary logarithmic phase. -/
theorem fourier_primeHeightPoint (h : ℝ) (p : Nat.Primes) (q : ℤ) :
    fourier q (primeHeightPoint h p) =
      Complex.exp ((((q : ℝ) * h * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) := by
  rw [primeHeightPoint, clockPhasePoint, fourier_coe_apply]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- A prime disk parameter at shifted height is the original parameter rotated by the prime height
point. -/
theorem primePoissonParameter_shift_height
    (sigma t h : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    ((primePoissonParameter sigma (t + h) hsigma p : CirclePoissonParameter) : ℂ) =
      fourier 1 (primeHeightPoint h p) *
        ((primePoissonParameter sigma t hsigma p : CirclePoissonParameter) : ℂ) := by
  simp only [coe_primePoissonParameter, fourier_primeHeightPoint,
    primePoissonParameterValue]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Local Poisson moments transform covariantly under multiplication of the disk parameter by a
unit phase. -/
theorem circlePoissonFourierMoment_eq_zpow_mul_of_coe_eq
    (a b : CirclePoissonParameter) (z : Circle)
    (hba : (b : ℂ) = (z : ℂ) * (a : ℂ)) (q : ℤ) :
    circlePoissonFourierMoment b q =
      (z : ℂ) ^ q * circlePoissonFourierMoment a q := by
  cases q with
  | ofNat n =>
      simp only [circlePoissonFourierMoment]
      rw [hba, mul_pow]
      simp
  | negSucc n =>
      simp only [circlePoissonFourierMoment]
      rw [hba, map_mul, mul_pow]
      have hzinv : ((z : ℂ))⁻¹ = (starRingEnd ℂ) (z : ℂ) :=
        Complex.inv_eq_conj (Circle.norm_coe z)
      rw [zpow_negSucc, ← inv_pow, hzinv]

/-- Each local prime Poisson moment transforms by the corresponding height character. -/
theorem circlePoissonFourierMoment_shift_height
    (sigma t h : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) (q : ℤ) :
    circlePoissonFourierMoment (primePoissonParameter sigma (t + h) hsigma p) q =
      fourier q (primeHeightPoint h p) *
        circlePoissonFourierMoment (primePoissonParameter sigma t hsigma p) q := by
  let z : Circle := AddCircle.toCircle (primeHeightPoint h p)
  have hfourier : fourier q (primeHeightPoint h p) = (z : ℂ) ^ q := by
    rw [fourier_apply, AddCircle.toCircle_zsmul]
    exact Circle.coe_zpow z q
  have hz1 : (z : ℂ) = fourier 1 (primeHeightPoint h p) := by
    simp [fourier_apply, z]
  rw [hfourier]
  apply circlePoissonFourierMoment_eq_zpow_mul_of_coe_eq
  rw [hz1]
  exact primePoissonParameter_shift_height sigma t h hsigma p

/-- Arithmetic height translation pushes the prime Poisson law at `t` to the law at `t+h`. -/
theorem map_primeHeightTranslation_primePoissonMeasure
    (sigma t h : ℝ) (hsigma : 0 < sigma) :
    Measure.map (Homeomorph.addLeft (primeHeightPoint h))
        (primePoissonMeasure sigma t hsigma) =
      primePoissonMeasure sigma (t + h) hsigma := by
  let mu : ProbabilityMeasure (Nat.Primes → UnitAddCircle) :=
    ProbabilityMeasure.map (primePoissonProbabilityMeasure sigma t hsigma)
      (Homeomorph.addLeft (primeHeightPoint h)).continuous.aemeasurable
  let nu : ProbabilityMeasure (Nat.Primes → UnitAddCircle) :=
    primePoissonProbabilityMeasure sigma (t + h) hsigma
  have hmunu : mu = nu := by
    apply probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq
    intro q
    dsimp only [mu, nu]
    rw [ProbabilityMeasure.toMeasure_map]
    rw [integral_map (Homeomorph.addLeft (primeHeightPoint h)).continuous.aemeasurable
      (infiniteTorusFourier q).continuous.aestronglyMeasurable]
    change (∫ x, infiniteTorusFourier q (primeHeightPoint h + x)
        ∂primePoissonMeasure sigma t hsigma) =
      ∫ x, infiniteTorusFourier q x ∂primePoissonMeasure sigma (t + h) hsigma
    simp_rw [infiniteTorusFourier_add_point_local]
    rw [integral_const_mul, integral_infiniteTorusFourier_primePoissonMeasure,
      integral_infiniteTorusFourier_primePoissonMeasure]
    simp only [infiniteTorusFourier, ContinuousMap.coe_mk, Finsupp.prod]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    exact (circlePoissonFourierMoment_shift_height sigma t h hsigma p (q p)).symm
  exact congrArg (fun rho : ProbabilityMeasure (Nat.Primes → UnitAddCircle) =>
    (rho : Measure (Nat.Primes → UnitAddCircle))) hmunu

/-- Probability law obtained by uniformly averaging the height translates of one prime Poisson
state over a centered window of radius `A`. -/
def primePoissonHeightAverageProbabilityMeasure
    (sigma t : ℝ) (hsigma : 0 < sigma) (A : ℝ) :
    ProbabilityMeasure (Nat.Primes → UnitAddCircle) :=
  ProbabilityMeasure.map
    ((infiniteTorusPhaseProbabilityMeasure
        (fun p : Nat.Primes => Real.log (p : ℝ)) A).prod
      (primePoissonProbabilityMeasure sigma t hsigma))
    (f := fun y => y.1 + y.2)
    (by fun_prop)

/-- Every Fourier coefficient of the height-averaged state is the original coefficient multiplied
by the exact centered-window sinc factor. -/
theorem integral_infiniteTorusFourier_primePoissonHeightAverage
    (sigma t : ℝ) (hsigma : 0 < sigma) (A : ℝ)
    (q : Nat.Primes →₀ ℤ) :
    (∫ x, infiniteTorusFourier q x
        ∂(primePoissonHeightAverageProbabilityMeasure sigma t hsigma A :
          Measure (Nat.Primes → UnitAddCircle))) =
      Real.sinc (A * infiniteTorusCharacterDetuning q
        (fun p : Nat.Primes => Real.log (p : ℝ))) *
        (q.prod fun p k =>
          circlePoissonFourierMoment (primePoissonParameter sigma t hsigma p) k) := by
  rw [primePoissonHeightAverageProbabilityMeasure, ProbabilityMeasure.toMeasure_map]
  rw [integral_map (by fun_prop)
    (infiniteTorusFourier q).continuous.aestronglyMeasurable]
  change (∫ y : (Nat.Primes → UnitAddCircle) ×
      (Nat.Primes → UnitAddCircle), infiniteTorusFourier q (y.1 + y.2)
      ∂((infiniteTorusPhaseProbabilityMeasure
          (fun p : Nat.Primes => Real.log (p : ℝ)) A :
            Measure (Nat.Primes → UnitAddCircle)).prod
        (primePoissonMeasure sigma t hsigma))) = _
  have hint : Integrable
      (fun y : (Nat.Primes → UnitAddCircle) × (Nat.Primes → UnitAddCircle) =>
        infiniteTorusFourier q (y.1 + y.2))
      ((infiniteTorusPhaseProbabilityMeasure
          (fun p : Nat.Primes => Real.log (p : ℝ)) A :
            Measure (Nat.Primes → UnitAddCircle)).prod
        (primePoissonMeasure sigma t hsigma)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (infiniteTorusFourier q).continuous.comp (continuous_fst.add continuous_snd)
    · exact HasCompactSupport.of_compactSpace _
  rw [integral_prod _ hint]
  simp_rw [infiniteTorusFourier_add_point_local, integral_const_mul]
  rw [integral_mul_const,
    infiniteTorusPhaseProbabilityMeasure_fourier_integral,
    integral_infiniteTorusFourier_primePoissonMeasure]

/-- Prime logarithms have no nontrivial finite-support integer detuning. -/
theorem infiniteTorusCharacterDetuning_logPrime_eq_zero_iff
    (q : Nat.Primes →₀ ℤ) :
    infiniteTorusCharacterDetuning q
        (fun p : Nat.Primes => Real.log (p : ℝ)) = 0 ↔ q = 0 := by
  have hri : RationallyIndependentSequence
      (fun p : Nat.Primes => Real.log (p : ℝ)) :=
    rationallyIndependentSequence_of_linearIndependent_int
      GaloisForLFunctions.logPrime_linearIndependent_int
  change characterDetuning q (fun p : Nat.Primes => Real.log (p : ℝ)) = 0 ↔ q = 0
  exact characterDetuning_eq_zero_iff hri q

/-- A nonzero rescaling of the centered sinc window vanishes at positive infinite radius. -/
theorem tendsto_sinc_mul_atTop_zero_of_ne {d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun A : ℝ => Real.sinc (A * d)) atTop (nhds 0) := by
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · have harg : Tendsto (fun A : ℝ => (-d) * A) atTop atTop :=
      tendsto_id.const_mul_atTop (neg_pos.mpr hdneg)
    have hlim := tendsto_real_sinc_atTop_zero.comp harg
    have heq : (fun A : ℝ => Real.sinc (A * d)) =
        fun A => Real.sinc ((-d) * A) := by
      funext A
      rw [show A * d = -((-d) * A) by ring, Real.sinc_neg]
    rw [heq]
    change Tendsto (Real.sinc ∘ fun A : ℝ => (-d) * A) atTop (nhds 0)
    exact hlim
  · have harg : Tendsto (fun A : ℝ => d * A) atTop atTop :=
      tendsto_id.const_mul_atTop hdpos
    have hlim := tendsto_real_sinc_atTop_zero.comp harg
    have heq : (fun A : ℝ => Real.sinc (A * d)) =
        fun A => Real.sinc (d * A) := by
      funext A
      rw [mul_comm]
    rw [heq]
    change Tendsto (Real.sinc ∘ fun A : ℝ => d * A) atTop (nhds 0)
    exact hlim

/-- Exact state dephasing law: centered height averages of every positive-aperture prime Poisson
state converge weakly to Haar probability. -/
theorem tendsto_primePoissonHeightAverageProbabilityMeasure_haar
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    Tendsto (fun A : ℝ =>
        primePoissonHeightAverageProbabilityMeasure sigma t hsigma A)
      atTop (nhds (⟨torusHaar Nat.Primes, inferInstance⟩ :
        ProbabilityMeasure (Nat.Primes → UnitAddCircle))) := by
  apply probabilityMeasure_tendsto_of_infiniteTorusFourier_integral_tendsto
  intro q
  change Tendsto (fun A : ℝ =>
      ∫ x, infiniteTorusFourier q x
        ∂(primePoissonHeightAverageProbabilityMeasure sigma t hsigma A :
          Measure (Nat.Primes → UnitAddCircle))) atTop
    (nhds (∫ x, infiniteTorusFourier q x ∂torusHaar Nat.Primes))
  rw [show (∫ x, infiniteTorusFourier q x ∂torusHaar Nat.Primes) =
      if q = 0 then 1 else 0 by
    have hcharacter : (fun x => infiniteTorusFourier q x) = fun x => torusCharacter q x := by
      funext x
      simp only [infiniteTorusFourier, torusCharacter, ContinuousMap.coe_mk]
      rfl
    rw [hcharacter, integral_torusCharacter]]
  by_cases hq : q = 0
  · subst q
    simp
  · rw [if_neg hq]
    rw [show (fun A : ℝ =>
        ∫ x, infiniteTorusFourier q x
          ∂(primePoissonHeightAverageProbabilityMeasure sigma t hsigma A :
            Measure (Nat.Primes → UnitAddCircle))) =
      fun A => Real.sinc (A * infiniteTorusCharacterDetuning q
          (fun p : Nat.Primes => Real.log (p : ℝ))) *
        (q.prod fun p k => circlePoissonFourierMoment
          (primePoissonParameter sigma t hsigma p) k) by
      funext A
      exact integral_infiniteTorusFourier_primePoissonHeightAverage
        sigma t hsigma A q]
    have hsinc := tendsto_sinc_mul_atTop_zero_of_ne
      (fun hzero => hq ((infiniteTorusCharacterDetuning_logPrime_eq_zero_iff q).mp hzero))
    have hsincComplex : Tendsto (fun A : ℝ =>
        (Real.sinc (A * infiniteTorusCharacterDetuning q
          (fun p : Nat.Primes => Real.log (p : ℝ))) : ℂ)) atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hsinc
    simpa using hsincComplex.mul_const
      (q.prod fun p k => circlePoissonFourierMoment
        (primePoissonParameter sigma t hsigma p) k)

/-- Prime Poisson disk parameter after an arbitrary unimodular prime-phase twist. -/
def twistedPrimePoissonParameter
    (sigma t : ℝ) (hsigma : 0 < sigma) (chi : Nat.Primes → Circle)
    (p : Nat.Primes) : CirclePoissonParameter := by
  refine ⟨(chi p : ℂ) * primePoissonParameterValue sigma t p, ?_⟩
  rw [mem_ball_zero_iff, norm_mul, Circle.norm_coe, one_mul]
  have hmem := (primePoissonParameter sigma t hsigma p).property
  rw [mem_ball_zero_iff] at hmem
  exact hmem

/-- Product spectral law of the prime-phase-twisted Poisson state. -/
def twistedPrimePoissonMeasure
    (sigma t : ℝ) (hsigma : 0 < sigma) (chi : Nat.Primes → Circle) :
    Measure (Nat.Primes → UnitAddCircle) :=
  torusPoissonMeasure (twistedPrimePoissonParameter sigma t hsigma chi)

instance twistedPrimePoissonMeasure_isProbabilityMeasure
    (sigma t : ℝ) (hsigma : 0 < sigma) (chi : Nat.Primes → Circle) :
    IsProbabilityMeasure (twistedPrimePoissonMeasure sigma t hsigma chi) := by
  unfold twistedPrimePoissonMeasure
  infer_instance

@[simp]
theorem coe_twistedPrimePoissonParameter
    (sigma t : ℝ) (hsigma : 0 < sigma) (chi : Nat.Primes → Circle)
    (p : Nat.Primes) :
    ((twistedPrimePoissonParameter sigma t hsigma chi p : CirclePoissonParameter) : ℂ) =
      (chi p : ℂ) * primePoissonParameterValue sigma t p := rfl

/-- Every unimodularly twisted positive-aperture prime sequence still tends to the disk origin. -/
theorem tendsto_twistedPrimePoissonParameter_natEquivPrimes_zero
    (sigma t : ℝ) (hsigma : 0 < sigma) (chi : Nat.Primes → Circle) :
    Tendsto (fun n =>
      ((twistedPrimePoissonParameter sigma t hsigma chi (natEquivPrimes n) :
        CirclePoissonParameter) : ℂ)) atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have horiginal := tendsto_iff_norm_sub_tendsto_zero.mp
    (tendsto_primePoissonParameter_natEquivPrimes_zero sigma t hsigma)
  have hnorm : (fun n =>
      ‖((twistedPrimePoissonParameter sigma t hsigma chi (natEquivPrimes n) :
          CirclePoissonParameter) : ℂ) - 0‖) =
      fun n =>
        ‖((primePoissonParameter sigma t hsigma (natEquivPrimes n) :
          CirclePoissonParameter) : ℂ) - 0‖ := by
    funext n
    rw [sub_zero, sub_zero, coe_twistedPrimePoissonParameter,
      coe_primePoissonParameter, norm_mul, Circle.norm_coe, one_mul]
  rw [hnorm]
  exact horiginal

/-- Exact local weighted phase-distance formula for a twisted prime parameter. -/
theorem normSq_twistedPrimePoissonParameter_sub_eq
    (sigma t : ℝ) (hsigma : 0 < sigma) (chi : Nat.Primes → Circle)
    (p : Nat.Primes) :
    ‖((twistedPrimePoissonParameter sigma t hsigma chi p :
        CirclePoissonParameter) : ℂ) -
      ((primePoissonParameter sigma t hsigma p : CirclePoissonParameter) : ℂ)‖ ^ 2 =
      (p : ℝ) ^ (-2 * sigma) * ‖(chi p : ℂ) - 1‖ ^ 2 := by
  simp only [coe_twistedPrimePoissonParameter, coe_primePoissonParameter]
  rw [show (chi p : ℂ) * primePoissonParameterValue sigma t p -
      primePoissonParameterValue sigma t p =
      ((chi p : ℂ) - 1) * primePoissonParameterValue sigma t p by ring,
    norm_mul, mul_pow, norm_primePoissonParameterValue]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hradial : Real.exp (-sigma * Real.log (p : ℝ)) ^ 2 =
      (p : ℝ) ^ (-2 * sigma) := by
    rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [hradial]
  ring

/-- Exact phase-twist Kakutani criterion for prime Poisson states. -/
theorem twistedPrimePoissonMeasure_mutuallyAbsolutelyContinuous_iff
    (sigma t : ℝ) (hsigma : 0 < sigma) (chi : Nat.Primes → Circle) :
    ((twistedPrimePoissonMeasure sigma t hsigma chi ≪
          primePoissonMeasure sigma t hsigma) ∧
        primePoissonMeasure sigma t hsigma ≪
          twistedPrimePoissonMeasure sigma t hsigma chi) ↔
      Summable (fun p : Nat.Primes =>
        (p : ℝ) ^ (-2 * sigma) * ‖(chi p : ℂ) - 1‖ ^ 2) := by
  unfold twistedPrimePoissonMeasure primePoissonMeasure
  rw [torusPoissonMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq
    (twistedPrimePoissonParameter sigma t hsigma chi)
    (primePoissonParameter sigma t hsigma)
    (tendsto_twistedPrimePoissonParameter_natEquivPrimes_zero sigma t hsigma chi)
    (tendsto_primePoissonParameter_natEquivPrimes_zero sigma t hsigma)]
  apply summable_congr
  exact normSq_twistedPrimePoissonParameter_sub_eq sigma t hsigma chi

/-- To the right of the critical wall, every unimodular prime twist remains in the Haar/untwisted
measure class. -/
theorem twistedPrimePoissonMeasure_mutuallyAbsolutelyContinuous_of_half_lt
    (sigma t : ℝ) (hsigma : 0 < sigma) (hsigmaHalf : 1 / 2 < sigma)
    (chi : Nat.Primes → Circle) :
    (twistedPrimePoissonMeasure sigma t hsigma chi ≪
        primePoissonMeasure sigma t hsigma) ∧
      primePoissonMeasure sigma t hsigma ≪
        twistedPrimePoissonMeasure sigma t hsigma chi := by
  rw [twistedPrimePoissonMeasure_mutuallyAbsolutelyContinuous_iff]
  have hmass : Summable (GaloisForLFunctions.primeSchattenMass sigma 2) :=
    (GaloisForLFunctions.summable_primeSchattenMass_iff sigma 2).mpr (by linarith)
  have hfour : Summable (fun p : Nat.Primes =>
      4 * GaloisForLFunctions.primeSchattenMass sigma 2 p) :=
    (summable_mul_left_iff (by norm_num : (4 : ℝ) ≠ 0)).mpr hmass
  apply Summable.of_nonneg_of_le
  · intro p
    positivity
  · intro p
    have hchi : ‖(chi p : ℂ) - 1‖ ≤ 2 := by
      calc
        ‖(chi p : ℂ) - 1‖ ≤ ‖(chi p : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [Circle.norm_coe]; norm_num
    have hpow : 0 ≤ (p : ℝ) ^ (-2 * sigma) := Real.rpow_nonneg (by positivity) _
    have hsquare : ‖(chi p : ℂ) - 1‖ ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg (‖(chi p : ℂ) - 1‖), norm_nonneg ((chi p : ℂ) - 1)]
    simpa [GaloisForLFunctions.primeSchattenMass] using
      mul_le_mul_of_nonneg_left hsquare hpow
  · simpa [GaloisForLFunctions.primeSchattenMass, mul_comm] using hfour

/-- A divergent critical weighted phase defect enters a disjoint product sector. -/
theorem twistedPrimePoissonMeasure_half_mutuallySingular_of_not_summable
    (t : ℝ) (chi : Nat.Primes → Circle)
    (hdiv : ¬ Summable (fun p : Nat.Primes =>
      ‖(chi p : ℂ) - 1‖ ^ 2 / (p : ℝ))) :
    (twistedPrimePoissonMeasure (1 / 2) t (by norm_num) chi).MutuallySingular
      (primePoissonMeasure (1 / 2) t (by norm_num)) := by
  unfold twistedPrimePoissonMeasure primePoissonMeasure
  apply torusPoissonMeasure_mutuallySingular_of_not_summable_normSq
  intro hsum
  apply hdiv
  exact hsum.congr fun p => by
    rw [normSq_twistedPrimePoissonParameter_sub_eq]
    have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
    rw [show (-2 : ℝ) * (1 / 2) = -1 by ring, Real.rpow_neg_one]
    field_simp

/-! ## Full prime wave vector and rank-one trace-class density -/

/-- Unimodular natural-number phase `n ↦ n^{-it}`, completed by `1` at zero. -/
def primeWavePhase (t : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 1
  else Complex.exp (-(((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I))

theorem norm_primeWavePhase (t : ℝ) (n : ℕ) : ‖primeWavePhase t n‖ = 1 := by
  rw [primeWavePhase]
  split_ifs
  · exact norm_one
  · rw [Complex.norm_exp]
    have hre : (-(((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)).re = 0 := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, neg_zero]
    rw [hre, Real.exp_zero]

@[simp]
theorem primeWavePhase_one (t : ℝ) : primeWavePhase t 1 = 1 := by
  rw [primeWavePhase, if_neg one_ne_zero]
  simp

@[simp]
theorem primeWavePhase_zero_height (n : ℕ) : primeWavePhase 0 n = 1 := by
  rw [primeWavePhase]
  split_ifs
  · rfl
  · simp

/-- The natural-number phases form the additive height representation. -/
theorem primeWavePhase_add (t h : ℝ) (n : ℕ) :
    primeWavePhase (t + h) n = primeWavePhase h n * primeWavePhase t n := by
  rw [primeWavePhase, primeWavePhase, primeWavePhase]
  split_ifs with hn
  · simp
  · rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- Spatial height translation on the arithmetic Hilbert space. -/
def primeHeightUnitary (h : ℝ) :
    GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert ≃ₗᵢ[ℂ]
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  lpPhaseUnitary (primeWavePhase h) (norm_primeWavePhase h)

/-- Normalized full Dirichlet prime vector in `ℓ²(ℕ)` for `sigma > 1/2`. -/
def primeWaveState
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  GaloisForLFunctions.RHTower.PrimeDensity.arithState sigma hsigma
    (primeWavePhase t) (fun n _ => norm_primeWavePhase t n)

/-- Height translation is implemented by the diagonal phase unitary. -/
theorem primeHeightUnitary_primeWaveState
    (sigma t h : ℝ) (hsigma : 1 / 2 < sigma) :
    primeHeightUnitary h (primeWaveState sigma t hsigma) =
      primeWaveState sigma (t + h) hsigma := by
  rw [primeHeightUnitary, primeWaveState, primeWaveState,
    GaloisForLFunctions.RHTower.PrimeDensity.arithState,
    GaloisForLFunctions.RHTower.PrimeDensity.arithState, map_smul]
  congr 1
  refine lp.ext (funext fun n => ?_)
  simp only [lpPhaseUnitary_apply, GaloisForLFunctions.RHTower.PrimeDensity.amp]
  rw [primeWavePhase_add]
  ring

/-- Every wave coordinate is the zero-height coefficient times its unimodular phase. -/
theorem primeWaveState_apply_eq_phase_mul
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) (n : ℕ) :
    primeWaveState sigma t hsigma n =
      primeWavePhase t n * primeWaveState sigma 0 hsigma n := by
  have h := congrArg (fun x :
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert => x n)
    (primeHeightUnitary_primeWaveState sigma 0 t hsigma)
  simpa [primeHeightUnitary] using h.symm

/-- Each natural-number height phase varies continuously. -/
theorem continuous_primeWavePhase (n : ℕ) :
    Continuous (fun t : ℝ => primeWavePhase t n) := by
  unfold primeWavePhase
  split_ifs with hn
  · exact continuous_const
  · fun_prop

/-- Each coordinate of the normalized wave varies continuously with height. -/
theorem continuous_primeWaveState_apply
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) (n : ℕ) :
    Continuous (fun t : ℝ => primeWaveState sigma t hsigma n) := by
  convert (continuous_primeWavePhase n).mul continuous_const using 1
  funext t
  exact primeWaveState_apply_eq_phase_mul sigma t hsigma n

/-- The normalized prime wave is strongly continuous in the arithmetic Hilbert space. -/
theorem continuous_primeWaveState
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    Continuous (fun t : ℝ => primeWaveState sigma t hsigma) := by
  rw [continuous_iff_continuousAt]
  intro t0
  change Tendsto (fun t : ℝ => primeWaveState sigma t hsigma)
    (nhds t0) (nhds (primeWaveState sigma t0 hsigma))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Summable (fun n : ℕ =>
      4 * ‖primeWaveState sigma 0 hsigma n‖ ^ 2) := by
    have h := ((lp.memℓp (primeWaveState sigma 0 hsigma)).summable
      (by norm_num)).mul_left 4
    refine h.congr (fun n => ?_)
    rw [← Real.rpow_natCast]
    norm_num
  have hpoint : ∀ n : ℕ, Tendsto
      (fun t : ℝ => ‖primeWaveState sigma t hsigma n -
        primeWaveState sigma t0 hsigma n‖ ^ 2)
      (nhds t0) (nhds 0) := by
    intro n
    have hc : ContinuousAt
        (fun t : ℝ => ‖primeWaveState sigma t hsigma n -
          primeWaveState sigma t0 hsigma n‖ ^ 2) t0 :=
      (((continuous_primeWaveState_apply sigma hsigma n).continuousAt.sub
        (continuous_const.continuousAt : ContinuousAt
          (fun _ : ℝ => primeWaveState sigma t0 hsigma n) t0)).norm.pow 2)
    change Tendsto (fun t : ℝ => ‖primeWaveState sigma t hsigma n -
      primeWaveState sigma t0 hsigma n‖ ^ 2) (nhds t0)
      (nhds (‖primeWaveState sigma t0 hsigma n -
        primeWaveState sigma t0 hsigma n‖ ^ 2)) at hc
    simpa using hc
  have hbound : ∀ t n, ‖‖primeWaveState sigma t hsigma n -
      primeWaveState sigma t0 hsigma n‖ ^ 2‖ ≤
      4 * ‖primeWaveState sigma 0 hsigma n‖ ^ 2 := by
    intro t n
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have ht : ‖primeWaveState sigma t hsigma n‖ =
        ‖primeWaveState sigma 0 hsigma n‖ := by
      rw [primeWaveState_apply_eq_phase_mul, norm_mul, norm_primeWavePhase, one_mul]
    have ht0 : ‖primeWaveState sigma t0 hsigma n‖ =
        ‖primeWaveState sigma 0 hsigma n‖ := by
      rw [primeWaveState_apply_eq_phase_mul, norm_mul, norm_primeWavePhase, one_mul]
    calc
      ‖primeWaveState sigma t hsigma n - primeWaveState sigma t0 hsigma n‖ ^ 2
          ≤ (‖primeWaveState sigma t hsigma n‖ +
            ‖primeWaveState sigma t0 hsigma n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
      _ = 4 * ‖primeWaveState sigma 0 hsigma n‖ ^ 2 := by rw [ht, ht0]; ring
  have hsq : Tendsto
      (fun t : ℝ => ‖primeWaveState sigma t hsigma -
        primeWaveState sigma t0 hsigma‖ ^ 2)
      (nhds t0) (nhds 0) := by
    rw [show (fun t : ℝ => ‖primeWaveState sigma t hsigma -
        primeWaveState sigma t0 hsigma‖ ^ 2) =
        fun t => ∑' n : ℕ, ‖primeWaveState sigma t hsigma n -
          primeWaveState sigma t0 hsigma n‖ ^ 2 by
      funext t
      exact HilbertSchmidt.lp_norm_sq_eq _]
    simpa using tendsto_tsum_of_dominated_convergence hsum hpoint
      (by filter_upwards [] with t; exact hbound t)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  convert hsqrt using 1
  · funext t
    rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
  · simp

/-- The full prime wave vector is normalized. -/
theorem norm_primeWaveState
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeWaveState sigma t hsigma‖ = 1 := by
  exact GaloisForLFunctions.RHTower.PrimeDensity.norm_arithState sigma hsigma
    (primeWavePhase t) (fun n _ => norm_primeWavePhase t n) (primeWavePhase_one t)

/-- Full prime density operator: the rank-one projector of the normalized Dirichlet vector. -/
def primeWaveDensity
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert →L[ℂ]
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  InnerProductSpace.rankOne ℂ
    (primeWaveState sigma t hsigma) (primeWaveState sigma t hsigma)

/-- The density operator acts by the corpus's literal rank-one projector formula. -/
theorem primeWaveDensity_apply
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma)
    (x : GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert) :
    primeWaveDensity sigma t hsigma x =
      GaloisForLFunctions.RHTower.rankOneProj (primeWaveState sigma t hsigma) x := by
  rw [primeWaveDensity, InnerProductSpace.rankOne_apply]
  rfl

/-- Full density evolution is spatial: conjugation by the diagonal height unitary. -/
theorem primeWaveDensity_height_conjugation_apply
    (sigma t h : ℝ) (hsigma : 1 / 2 < sigma)
    (x : GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert) :
    primeWaveDensity sigma (t + h) hsigma x =
      primeHeightUnitary h
        (primeWaveDensity sigma t hsigma ((primeHeightUnitary h).symm x)) := by
  rw [primeWaveDensity_apply, primeWaveDensity_apply,
    ← primeHeightUnitary_primeWaveState sigma t h hsigma]
  exact GaloisForLFunctions.RHTower.PrimeDensity.rankOneProj_map
    (primeHeightUnitary h) (primeWaveState sigma t hsigma) x

/-- Every full prime density in the normal bulk is trace class. -/
theorem primeWaveDensity_isTraceClass
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    ContinuousLinearMap.IsTraceClass (primeWaveDensity sigma t hsigma) := by
  exact RHTower.isTraceClass_rankOne_lp
    (primeWaveState sigma t hsigma) (primeWaveState sigma t hsigma)

/-- The full prime density has operator rank at most one. -/
theorem primeWaveDensity_hasRankLE_one
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    RHTower.HasRankLE (primeWaveDensity sigma t hsigma) 1 := by
  simpa [primeWaveDensity] using
    (RHTower.hasRankLE_sum_range_rankOne
      (fun _ : ℕ => primeWaveState sigma t hsigma)
      (fun _ : ℕ => primeWaveState sigma t hsigma) 1)

/-- The normalized rank-one prime density has trace norm exactly one. -/
theorem traceNorm_primeWaveDensity
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    RHTower.traceNorm
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert
      (primeWaveDensity sigma t hsigma) = 1 := by
  rw [RHTower.traceNorm_eq_norm_of_hasRankLE_one
    (primeWaveDensity_hasRankLE_one sigma t hsigma)]
  rw [primeWaveDensity, InnerProductSpace.norm_rankOne,
    norm_primeWaveState, one_mul]

/-! ## Trace-norm particle dephasing -/

/-- The rank-one prime density bundled in the complete Schatten-one carrier. -/
noncomputable def primeWaveDensitySchattenOne
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    RHTower.SchattenOneOperator
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  RHTower.positiveRankOneSchattenOne (primeWaveState sigma t hsigma)

@[simp]
theorem primeWaveDensitySchattenOne_coe
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    (primeWaveDensitySchattenOne sigma t hsigma :
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert →L[ℂ]
        GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert) =
      primeWaveDensity sigma t hsigma := rfl

@[simp]
theorem norm_primeWaveDensitySchattenOne
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeWaveDensitySchattenOne sigma t hsigma‖ = 1 := by
  rw [primeWaveDensitySchattenOne,
    RHTower.norm_positiveRankOneSchattenOne, norm_primeWaveState, one_pow]

theorem continuous_primeWaveDensitySchattenOne
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    Continuous (fun t : ℝ => primeWaveDensitySchattenOne sigma t hsigma) :=
  RHTower.continuous_positiveRankOneSchattenOne.comp
    (continuous_primeWaveState sigma hsigma)

theorem integrable_primeWaveDensitySchattenOne
    (sigma A : ℝ) (hsigma : 1 / 2 < sigma) :
    Integrable (fun t : ℝ => primeWaveDensitySchattenOne sigma t hsigma)
      (centeredUniformClockProbabilityMeasure A) := by
  have hone : Integrable (fun _ : ℝ => (1 : ℝ))
      (centeredUniformClockProbabilityMeasure A : Measure ℝ) :=
    MeasureTheory.integrable_const 1
  apply hone.mono'
  · exact (continuous_primeWaveDensitySchattenOne sigma hsigma).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_primeWaveDensitySchattenOne]

/-- Symmetric height average of the literal full prime density, in trace norm. -/
noncomputable def primeWaveDensityAverage
    (sigma A : ℝ) (hsigma : 1 / 2 < sigma) :
    RHTower.SchattenOneOperator
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  ∫ t : ℝ, primeWaveDensitySchattenOne sigma t hsigma
    ∂centeredUniformClockProbabilityMeasure A

/-- Canonical natural-number coordinate vector in the arithmetic Hilbert space. -/
noncomputable def primeWaveBasis (n : ℕ) :
    GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  lp.single 2 n (1 : ℂ)

@[simp]
theorem norm_primeWaveBasis (n : ℕ) : ‖primeWaveBasis n‖ = 1 := by
  rw [primeWaveBasis, lp.norm_single (by norm_num)]
  simp

/-- Untwisted Dirichlet amplitude before normalization. -/
noncomputable def primeWaveUntwistedAmplitude
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  ⟨GaloisForLFunctions.RHTower.PrimeDensity.amp sigma (fun _ => 1),
    GaloisForLFunctions.RHTower.PrimeDensity.memℓp_amp hsigma
      (fun _ _ => norm_one)⟩

/-- Exact real zeta mass normalizing the full prime wave. -/
noncomputable def primeWaveZetaMass (sigma : ℝ) : ℝ :=
  ‖riemannZeta ((2 * sigma : ℝ) : ℂ)‖

theorem norm_sq_primeWaveUntwistedAmplitude_eq_zetaMass
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeWaveUntwistedAmplitude sigma hsigma‖ ^ 2 =
      primeWaveZetaMass sigma := by
  rw [HilbertSchmidt.lp_norm_sq_eq, primeWaveZetaMass,
    norm_riemannZeta_ofReal_eq_tsum (by linarith)]
  apply tsum_congr
  intro n
  rw [primeWaveUntwistedAmplitude,
    GaloisForLFunctions.RHTower.PrimeDensity.norm_amp (by linarith)
      (fun _ _ => norm_one)]
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -sigma ≠ 0)]
  · rw [if_neg hn]
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    congr 1
    ring

theorem primeWaveState_zero_eq
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    primeWaveState sigma 0 hsigma =
      (‖primeWaveUntwistedAmplitude sigma hsigma‖ : ℂ)⁻¹ •
        primeWaveUntwistedAmplitude sigma hsigma := by
  apply lp.ext
  funext n
  simp [primeWaveState, primeWaveUntwistedAmplitude,
    GaloisForLFunctions.RHTower.PrimeDensity.arithState,
    GaloisForLFunctions.RHTower.PrimeDensity.amp]

/-- Particle probability at natural number `n`; height phases have been discarded. -/
noncomputable def primeWaveParticleWeight
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) (n : ℕ) : ℝ :=
  ‖primeWaveState sigma 0 hsigma n‖ ^ 2

/-- Exact zeta-normalized particle probability, including the zero coordinate convention. -/
theorem primeWaveParticleWeight_eq_zeta
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) (n : ℕ) :
    primeWaveParticleWeight sigma hsigma n =
      (if n = 0 then 0 else (n : ℝ) ^ (-2 * sigma)) /
        primeWaveZetaMass sigma := by
  let v := primeWaveUntwistedAmplitude sigma hsigma
  have hvpos : 0 < ‖v‖ := by
    apply norm_pos_iff.mpr
    intro hv
    have hcoord := congrArg (fun x :
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert => x 1) hv
    simp [v, primeWaveUntwistedAmplitude,
      GaloisForLFunctions.RHTower.PrimeDensity.amp] at hcoord
  have hvn : ‖v n‖ ^ 2 =
      if n = 0 then 0 else (n : ℝ) ^ (-2 * sigma) := by
    change ‖GaloisForLFunctions.RHTower.PrimeDensity.amp sigma
      (fun _ => 1) n‖ ^ 2 = _
    rw [GaloisForLFunctions.RHTower.PrimeDensity.norm_amp (by linarith)
      (fun _ _ => norm_one)]
    by_cases hn : n = 0
    · subst n
      simp [Real.zero_rpow (by linarith : -sigma ≠ 0)]
    · rw [if_neg hn]
      have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      congr 1
      ring
  have hvz : ‖v‖ ^ 2 = primeWaveZetaMass sigma := by
    exact norm_sq_primeWaveUntwistedAmplitude_eq_zetaMass sigma hsigma
  rw [primeWaveParticleWeight, primeWaveState_zero_eq]
  change ‖(‖v‖ : ℂ)⁻¹ * v n‖ ^ 2 = _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg v), mul_pow, hvn, ← hvz]
  field_simp

theorem summable_primeWaveParticleWeight
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    Summable (primeWaveParticleWeight sigma hsigma) := by
  have h := (lp.memℓp (primeWaveState sigma 0 hsigma)).summable (by norm_num)
  refine h.congr (fun n => ?_)
  rw [primeWaveParticleWeight, ← Real.rpow_natCast]
  norm_num

theorem tsum_primeWaveParticleWeight
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    ∑' n : ℕ, primeWaveParticleWeight sigma hsigma n = 1 := by
  change (∑' n : ℕ, ‖primeWaveState sigma 0 hsigma n‖ ^ 2) = 1
  rw [← HilbertSchmidt.lp_norm_sq_eq (primeWaveState sigma 0 hsigma),
    norm_primeWaveState, one_pow]

/-- One diagonal particle atom in the Schatten-one carrier. -/
noncomputable def primeWaveParticleDensityTerm
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) (n : ℕ) :
    RHTower.SchattenOneOperator
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  (primeWaveParticleWeight sigma hsigma n : ℂ) •
    RHTower.positiveRankOneSchattenOne (primeWaveBasis n)

@[simp]
theorem norm_primeWaveParticleDensityTerm
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) (n : ℕ) :
    ‖primeWaveParticleDensityTerm sigma hsigma n‖ =
      primeWaveParticleWeight sigma hsigma n := by
  rw [primeWaveParticleDensityTerm, norm_smul,
    RHTower.norm_positiveRankOneSchattenOne, norm_primeWaveBasis, one_pow, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact sq_nonneg _

theorem summable_primeWaveParticleDensityTerm
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    Summable (primeWaveParticleDensityTerm sigma hsigma) := by
  apply Summable.of_norm
  simpa only [norm_primeWaveParticleDensityTerm] using
    summable_primeWaveParticleWeight sigma hsigma

/-- Exact particle shadow: the trace-norm sum of diagonal natural-number atoms. -/
noncomputable def primeWaveParticleDensity
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    RHTower.SchattenOneOperator
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  ∑' n : ℕ, primeWaveParticleDensityTerm sigma hsigma n

/-- The particle shadow is literally diagonal in natural-number coordinates. -/
theorem primeWaveParticleDensity_apply
    (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (x : GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert) (n : ℕ) :
    ((primeWaveParticleDensity sigma hsigma :
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert →L[ℂ]
        GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert) x) n =
      (primeWaveParticleWeight sigma hsigma n : ℂ) * x n := by
  let evalX :
      (GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert →L[ℂ]
        GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert) →L[ℂ]
          GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
    (ContinuousLinearMap.apply ℂ
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert) x
  let coord : GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert →L[ℂ] ℂ :=
    innerSL ℂ (primeWaveBasis n)
  let Phi : RHTower.SchattenOneOperator
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert →L[ℂ] ℂ :=
    coord.comp (evalX.comp RHTower.schattenOneCoeCLM)
  calc
    ((primeWaveParticleDensity sigma hsigma :
        GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert →L[ℂ]
          GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert) x) n =
        Phi (primeWaveParticleDensity sigma hsigma) := by
          simp [Phi, coord, evalX, primeWaveBasis, lp.inner_single_left]
    _ = (primeWaveParticleWeight sigma hsigma n : ℂ) * x n := by
      rw [primeWaveParticleDensity,
        Phi.map_tsum (summable_primeWaveParticleDensityTerm sigma hsigma)]
      rw [tsum_eq_single n]
      · simp [Phi, coord, evalX, primeWaveParticleDensityTerm,
          RHTower.positiveRankOneSchattenOne, RHTower.rankOneSchattenOne,
          primeWaveBasis, InnerProductSpace.rankOne_apply, lp.inner_single_left]
      · intro k hkn
        simp [Phi, coord, evalX, primeWaveParticleDensityTerm,
          RHTower.positiveRankOneSchattenOne, RHTower.rankOneSchattenOne,
          primeWaveBasis, InnerProductSpace.rankOne_apply, lp.inner_single_left,
          lp.single_apply, hkn]

/-- Coordinate probabilities are independent of height. -/
theorem norm_primeWaveState_apply_sq_eq_weight
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) (n : ℕ) :
    ‖primeWaveState sigma t hsigma n‖ ^ 2 =
      primeWaveParticleWeight sigma hsigma n := by
  rw [primeWaveState_apply_eq_phase_mul, norm_mul, norm_primeWavePhase,
    one_mul, primeWaveParticleWeight]

/-- Hard finite-coordinate truncation of the prime wave. -/
noncomputable def primeWaveStateHead
    (S : Finset ℕ) (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  lpCoordinateProjection (↑S : Set ℕ) (primeWaveState sigma t hsigma)

theorem continuous_primeWaveStateHead
    (S : Finset ℕ) (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    Continuous (fun t : ℝ => primeWaveStateHead S sigma t hsigma) :=
  (lpCoordinateProjection (↑S : Set ℕ)).continuous.comp
    (continuous_primeWaveState sigma hsigma)

theorem norm_primeWaveStateHead_le_one
    (S : Finset ℕ) (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeWaveStateHead S sigma t hsigma‖ ≤ 1 := by
  calc
    ‖primeWaveStateHead S sigma t hsigma‖ ≤
        ‖primeWaveState sigma t hsigma‖ := by
      apply lp.norm_mono (by norm_num)
      intro n
      rw [primeWaveStateHead, lpCoordinateProjection_apply]
      by_cases hn : n ∈ S
      · rw [Set.indicator_of_mem hn]
      · rw [Set.indicator_of_notMem hn]
        simp
    _ = 1 := norm_primeWaveState sigma t hsigma

/-- The Hilbert tail is exactly the particle mass outside the finite head. -/
theorem norm_primeWaveState_sub_head_sq
    (S : Finset ℕ) (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeWaveState sigma t hsigma - primeWaveStateHead S sigma t hsigma‖ ^ 2 =
      ∑' n : {n // n ∉ S}, primeWaveParticleWeight sigma hsigma n := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  change (∑' n : ℕ, ‖(primeWaveState sigma t hsigma -
    primeWaveStateHead S sigma t hsigma) n‖ ^ 2) =
      ∑' n : ↥((↑S : Set ℕ)ᶜ), primeWaveParticleWeight sigma hsigma n
  rw [tsum_subtype]
  apply tsum_congr
  intro n
  change ‖primeWaveState sigma t hsigma n -
    primeWaveStateHead S sigma t hsigma n‖ ^ 2 = _
  rw [primeWaveStateHead, lpCoordinateProjection_apply]
  by_cases hn : n ∈ S
  · rw [Set.indicator_of_mem hn, sub_self, norm_zero, zero_pow (by norm_num),
      Set.indicator_of_notMem]
    simpa using hn
  · rw [Set.indicator_of_notMem hn, sub_zero,
      Set.indicator_of_mem, norm_primeWaveState_apply_sq_eq_weight]
    simpa using hn

/-- Finite-head rank-one density in the complete trace-class carrier. -/
noncomputable def primeWaveDensityHeadSchattenOne
    (S : Finset ℕ) (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    RHTower.SchattenOneOperator
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  RHTower.positiveRankOneSchattenOne (primeWaveStateHead S sigma t hsigma)

theorem continuous_primeWaveDensityHeadSchattenOne
    (S : Finset ℕ) (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    Continuous (fun t : ℝ => primeWaveDensityHeadSchattenOne S sigma t hsigma) :=
  RHTower.continuous_positiveRankOneSchattenOne.comp
    (continuous_primeWaveStateHead S sigma hsigma)

theorem integrable_primeWaveDensityHeadSchattenOne
    (S : Finset ℕ) (sigma A : ℝ) (hsigma : 1 / 2 < sigma) :
    Integrable (fun t : ℝ => primeWaveDensityHeadSchattenOne S sigma t hsigma)
      (centeredUniformClockProbabilityMeasure A) := by
  have hone : Integrable (fun _ : ℝ => (1 : ℝ))
      (centeredUniformClockProbabilityMeasure A : Measure ℝ) :=
    MeasureTheory.integrable_const 1
  apply hone.mono'
  · exact (continuous_primeWaveDensityHeadSchattenOne S sigma hsigma).aestronglyMeasurable
  · filter_upwards [] with t
    rw [primeWaveDensityHeadSchattenOne,
      RHTower.norm_positiveRankOneSchattenOne]
    nlinarith [norm_nonneg (primeWaveStateHead S sigma t hsigma),
      norm_primeWaveStateHead_le_one S sigma t hsigma]

/-- Symmetric height average of a finite-coordinate wave head. -/
noncomputable def primeWaveDensityHeadAverage
    (S : Finset ℕ) (sigma A : ℝ) (hsigma : 1 / 2 < sigma) :
    RHTower.SchattenOneOperator
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  ∫ t : ℝ, primeWaveDensityHeadSchattenOne S sigma t hsigma
    ∂centeredUniformClockProbabilityMeasure A

/-- Finite diagonal head of the particle density. -/
noncomputable def primeWaveParticleDensityHead
    (S : Finset ℕ) (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    RHTower.SchattenOneOperator
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  ∑ n ∈ S, primeWaveParticleDensityTerm sigma hsigma n

theorem norm_primeWaveState_sub_head_eq_zero_height
    (S : Finset ℕ) (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeWaveState sigma t hsigma - primeWaveStateHead S sigma t hsigma‖ =
      ‖primeWaveState sigma 0 hsigma - primeWaveStateHead S sigma 0 hsigma‖ := by
  have ht := norm_primeWaveState_sub_head_sq S sigma t hsigma
  have h0 := norm_primeWaveState_sub_head_sq S sigma 0 hsigma
  nlinarith [norm_nonneg (primeWaveState sigma t hsigma -
      primeWaveStateHead S sigma t hsigma),
    norm_nonneg (primeWaveState sigma 0 hsigma -
      primeWaveStateHead S sigma 0 hsigma)]

/-- Uniform trace-norm cost of replacing the full averaged wave by a finite head. -/
theorem norm_primeWaveDensityAverage_sub_head_le
    (S : Finset ℕ) (sigma A : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeWaveDensityAverage sigma A hsigma -
        primeWaveDensityHeadAverage S sigma A hsigma‖ ≤
      2 * ‖primeWaveState sigma 0 hsigma -
        primeWaveStateHead S sigma 0 hsigma‖ := by
  rw [primeWaveDensityAverage, primeWaveDensityHeadAverage,
    ← MeasureTheory.integral_sub
      (integrable_primeWaveDensitySchattenOne sigma A hsigma)
      (integrable_primeWaveDensityHeadSchattenOne S sigma A hsigma)]
  calc
    ‖∫ t : ℝ, primeWaveDensitySchattenOne sigma t hsigma -
        primeWaveDensityHeadSchattenOne S sigma t hsigma
        ∂centeredUniformClockProbabilityMeasure A‖ ≤
        (2 * ‖primeWaveState sigma 0 hsigma -
          primeWaveStateHead S sigma 0 hsigma‖) *
          (centeredUniformClockProbabilityMeasure A : Measure ℝ).real Set.univ := by
      apply MeasureTheory.norm_integral_le_of_norm_le_const
      filter_upwards [] with t
      calc
        ‖primeWaveDensitySchattenOne sigma t hsigma -
            primeWaveDensityHeadSchattenOne S sigma t hsigma‖ ≤
            ‖primeWaveState sigma t hsigma -
              primeWaveStateHead S sigma t hsigma‖ *
              (‖primeWaveState sigma t hsigma‖ +
                ‖primeWaveStateHead S sigma t hsigma‖) :=
          RHTower.norm_positiveRankOneSchattenOne_sub_le _ _
        _ ≤ ‖primeWaveState sigma t hsigma -
              primeWaveStateHead S sigma t hsigma‖ * 2 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [norm_primeWaveState]
          linarith [norm_primeWaveStateHead_le_one S sigma t hsigma]
        _ = 2 * ‖primeWaveState sigma 0 hsigma -
              primeWaveStateHead S sigma 0 hsigma‖ := by
          rw [norm_primeWaveState_sub_head_eq_zero_height S sigma t hsigma]
          ring
    _ = 2 * ‖primeWaveState sigma 0 hsigma -
          primeWaveStateHead S sigma 0 hsigma‖ := by simp

/-- Trace-norm particle tail is bounded by its missing probability mass. -/
theorem norm_primeWaveParticleDensityHead_sub_le
    (S : Finset ℕ) (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeWaveParticleDensityHead S sigma hsigma -
        primeWaveParticleDensity sigma hsigma‖ ≤
      ∑' n : {n // n ∉ S}, primeWaveParticleWeight sigma hsigma n := by
  have hsum := summable_primeWaveParticleDensityTerm sigma hsigma
  have hsplit := hsum.sum_add_tsum_subtype_compl S
  have heq : primeWaveParticleDensityHead S sigma hsigma -
      primeWaveParticleDensity sigma hsigma =
        -(∑' n : {n // n ∉ S},
          primeWaveParticleDensityTerm sigma hsigma n) := by
    rw [primeWaveParticleDensityHead, primeWaveParticleDensity, ← hsplit]
    abel
  rw [heq, norm_neg]
  have hnorm : Summable (fun n : {n // n ∉ S} =>
      ‖primeWaveParticleDensityTerm sigma hsigma n‖) := by
    refine ((summable_primeWaveParticleWeight sigma hsigma).subtype
      {n : ℕ | n ∉ S}).congr (fun n => ?_)
    exact (norm_primeWaveParticleDensityTerm sigma hsigma n).symm
  calc
    ‖∑' n : {n // n ∉ S}, primeWaveParticleDensityTerm sigma hsigma n‖ ≤
        ∑' n : {n // n ∉ S},
          ‖primeWaveParticleDensityTerm sigma hsigma n‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ∑' n : {n // n ∉ S}, primeWaveParticleWeight sigma hsigma n := by
      apply tsum_congr
      intro n
      exact norm_primeWaveParticleDensityTerm sigma hsigma n

/-- Two natural-number wave phases have the exact logarithmic detuning character. -/
theorem primeWavePhase_mul_conj_eq_exp
    (t : ℝ) (m n : ℕ) :
    primeWavePhase t m * starRingEnd ℂ (primeWavePhase t n) =
      Complex.exp ((((Real.log (n : ℝ) - Real.log (m : ℝ)) * t : ℝ) : ℂ) *
        Complex.I) := by
  have hconj (x : ℝ) :
      starRingEnd ℂ (-((x : ℂ) * Complex.I)) = (x : ℂ) * Complex.I := by
    rw [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [primeWavePhase, primeWavePhase]
  split_ifs with hm hn
  · subst m
    subst n
    simp
  · subst m
    rw [one_mul, ← Complex.exp_conj, hconj]
    congr 1
    simp only [Nat.cast_zero, Real.log_zero, sub_zero]
    push_cast
    ring
  · subst n
    rw [map_one, mul_one]
    congr 1
    simp
    ring
  · rw [← Complex.exp_conj, hconj, ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- Cross-coordinate coherence is a fixed amplitude times its logarithmic character. -/
theorem primeWaveState_cross_eq_exp_mul
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) (m n : ℕ) :
    primeWaveState sigma t hsigma m *
        starRingEnd ℂ (primeWaveState sigma t hsigma n) =
      Complex.exp ((((Real.log (n : ℝ) - Real.log (m : ℝ)) * t : ℝ) : ℂ) *
          Complex.I) *
        (primeWaveState sigma 0 hsigma m *
          starRingEnd ℂ (primeWaveState sigma 0 hsigma n)) := by
  let cm := primeWaveState sigma 0 hsigma m
  let cn := primeWaveState sigma 0 hsigma n
  change primeWaveState sigma t hsigma m *
      starRingEnd ℂ (primeWaveState sigma t hsigma n) =
    Complex.exp ((((Real.log (n : ℝ) - Real.log (m : ℝ)) * t : ℝ) : ℂ) *
      Complex.I) * (cm * starRingEnd ℂ cn)
  rw [show primeWaveState sigma t hsigma m = primeWavePhase t m * cm by
      exact primeWaveState_apply_eq_phase_mul sigma t hsigma m,
    show primeWaveState sigma t hsigma n = primeWavePhase t n * cn by
      exact primeWaveState_apply_eq_phase_mul sigma t hsigma n,
    map_mul]
  calc
    primeWavePhase t m * cm *
        (starRingEnd ℂ (primeWavePhase t n) * starRingEnd ℂ cn) =
      (primeWavePhase t m * starRingEnd ℂ (primeWavePhase t n)) *
        (cm * starRingEnd ℂ cn) := by ring
    _ = _ := by rw [primeWavePhase_mul_conj_eq_exp]

/-- Exact sinc multiplier on every natural-number matrix coefficient. -/
theorem integral_primeWaveState_cross
    (sigma A : ℝ) (hsigma : 1 / 2 < sigma) (m n : ℕ) :
    ∫ t : ℝ, primeWaveState sigma t hsigma m *
        starRingEnd ℂ (primeWaveState sigma t hsigma n)
        ∂centeredUniformClockProbabilityMeasure A =
      Real.sinc (A * (Real.log (n : ℝ) - Real.log (m : ℝ))) *
        (primeWaveState sigma 0 hsigma m *
          starRingEnd ℂ (primeWaveState sigma 0 hsigma n)) := by
  rw [show (fun t : ℝ => primeWaveState sigma t hsigma m *
      starRingEnd ℂ (primeWaveState sigma t hsigma n)) =
      fun t => Complex.exp
        ((((Real.log (n : ℝ) - Real.log (m : ℝ)) * t : ℝ) : ℂ) * Complex.I) *
          (primeWaveState sigma 0 hsigma m *
            starRingEnd ℂ (primeWaveState sigma 0 hsigma n)) by
    funext t
    exact primeWaveState_cross_eq_exp_mul sigma t hsigma m n]
  rw [MeasureTheory.integral_mul_const]
  rw [show (∫ t : ℝ, Complex.exp
      ((((Real.log (n : ℝ) - Real.log (m : ℝ)) * t : ℝ) : ℂ) * Complex.I)
      ∂centeredUniformClockProbabilityMeasure A) =
      MeasureTheory.charFun
        (centeredUniformClockProbabilityMeasure A : Measure ℝ)
        (Real.log (n : ℝ) - Real.log (m : ℝ)) by
    rw [MeasureTheory.charFun_apply_real]
    congr 1
    funext t
    congr 1
    push_cast
    ring]
  rw [charFun_centeredUniformClockProbabilityMeasure]

/-- A finite coordinate projection is its exact canonical-basis expansion. -/
theorem primeWaveStateHead_eq_sum
    (S : Finset ℕ) (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    primeWaveStateHead S sigma t hsigma =
      ∑ n ∈ S, primeWaveState sigma t hsigma n • primeWaveBasis n := by
  apply lp.ext
  funext k
  rw [primeWaveStateHead, lpCoordinateProjection_apply]
  rw [lp.coeFn_sum, Finset.sum_apply]
  by_cases hk : k ∈ S
  · rw [Set.indicator_of_mem hk]
    simp [primeWaveBasis, lp.single_apply, Pi.single_apply, hk]
  · rw [Set.indicator_of_notMem hk]
    simp [primeWaveBasis, lp.single_apply, Pi.single_apply, hk]

/-- Canonical rectangular rank-one matrix unit in trace class. -/
noncomputable def primeWaveMatrixAtom (m n : ℕ) :
    RHTower.SchattenOneOperator
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
  RHTower.rankOneSchattenOne (primeWaveBasis m) (primeWaveBasis n)

@[simp]
theorem norm_primeWaveMatrixAtom (m n : ℕ) :
    ‖primeWaveMatrixAtom m n‖ = 1 := by
  rw [primeWaveMatrixAtom, RHTower.norm_rankOneSchattenOne,
    norm_primeWaveBasis, norm_primeWaveBasis, one_mul]

/-- Exact finite matrix expansion of a truncated pure density. -/
theorem primeWaveDensityHeadSchattenOne_eq_sum
    (S : Finset ℕ) (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    primeWaveDensityHeadSchattenOne S sigma t hsigma =
      ∑ m ∈ S, ∑ n ∈ S,
        (primeWaveState sigma t hsigma m *
          starRingEnd ℂ (primeWaveState sigma t hsigma n)) •
            primeWaveMatrixAtom m n := by
  apply RHTower.SchattenOneOperator.ext
  change InnerProductSpace.rankOne ℂ (primeWaveStateHead S sigma t hsigma)
      (primeWaveStateHead S sigma t hsigma) =
    RHTower.schattenOneCoeCLM
      (∑ m ∈ S, ∑ n ∈ S,
        (primeWaveState sigma t hsigma m *
          starRingEnd ℂ (primeWaveState sigma t hsigma n)) •
            primeWaveMatrixAtom m n)
  rw [map_sum]
  simp_rw [map_sum]
  simp only [map_smul, RHTower.schattenOneCoeCLM_apply,
    primeWaveMatrixAtom, RHTower.rankOneSchattenOne_coe]
  apply ContinuousLinearMap.ext
  intro x
  rw [InnerProductSpace.rankOne_apply, primeWaveStateHead_eq_sum,
    sum_inner]
  simp only [inner_smul_left]
  rw [sum_apply]
  simp_rw [sum_apply, smul_apply, InnerProductSpace.rankOne_apply]
  rw [Finset.smul_sum]
  simp_rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  module

theorem norm_primeWaveState_apply_le_one
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) (n : ℕ) :
    ‖primeWaveState sigma t hsigma n‖ ≤ 1 := by
  calc
    ‖primeWaveState sigma t hsigma n‖ =
        ‖inner ℂ (primeWaveBasis n) (primeWaveState sigma t hsigma)‖ := by
      rw [primeWaveBasis, lp.inner_single_left]
      simp
    _ ≤ ‖primeWaveBasis n‖ * ‖primeWaveState sigma t hsigma‖ :=
      norm_inner_le_norm _ _
    _ = 1 := by rw [norm_primeWaveBasis, norm_primeWaveState, one_mul]

theorem integrable_primeWaveState_cross
    (sigma A : ℝ) (hsigma : 1 / 2 < sigma) (m n : ℕ) :
    Integrable (fun t : ℝ => primeWaveState sigma t hsigma m *
      starRingEnd ℂ (primeWaveState sigma t hsigma n))
      (centeredUniformClockProbabilityMeasure A) := by
  have hcont : Continuous (fun t : ℝ => primeWaveState sigma t hsigma m *
      starRingEnd ℂ (primeWaveState sigma t hsigma n)) :=
    (continuous_primeWaveState_apply sigma hsigma m).mul
      (continuous_star.comp (continuous_primeWaveState_apply sigma hsigma n))
  have hone : Integrable (fun _ : ℝ => (1 : ℝ))
      (centeredUniformClockProbabilityMeasure A : Measure ℝ) :=
    MeasureTheory.integrable_const 1
  apply hone.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_one₀ (norm_primeWaveState_apply_le_one sigma t hsigma m)
    (norm_nonneg _) (norm_primeWaveState_apply_le_one sigma t hsigma n)

theorem integral_primeWaveMatrixTerm
    (sigma A : ℝ) (hsigma : 1 / 2 < sigma) (m n : ℕ) :
    ∫ t : ℝ, (primeWaveState sigma t hsigma m *
        starRingEnd ℂ (primeWaveState sigma t hsigma n)) •
          primeWaveMatrixAtom m n
        ∂centeredUniformClockProbabilityMeasure A =
      (Real.sinc (A * (Real.log (n : ℝ) - Real.log (m : ℝ))) *
        (primeWaveState sigma 0 hsigma m *
          starRingEnd ℂ (primeWaveState sigma 0 hsigma n))) •
            primeWaveMatrixAtom m n := by
  let L : ℂ →L[ℂ] RHTower.SchattenOneOperator
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
    (1 : ℂ →L[ℂ] ℂ).smulRight (primeWaveMatrixAtom m n)
  have hscalar := integrable_primeWaveState_cross sigma A hsigma m n
  calc
    (∫ t : ℝ, (primeWaveState sigma t hsigma m *
        starRingEnd ℂ (primeWaveState sigma t hsigma n)) •
          primeWaveMatrixAtom m n
        ∂centeredUniformClockProbabilityMeasure A) =
      L (∫ t : ℝ, primeWaveState sigma t hsigma m *
          starRingEnd ℂ (primeWaveState sigma t hsigma n)
          ∂centeredUniformClockProbabilityMeasure A) := by
        rw [← L.integral_comp_comm hscalar]
        rfl
    _ = _ := by
      rw [integral_primeWaveState_cross]
      rfl

/-- The finite averaged density has the exact sinc-damped matrix expansion. -/
theorem primeWaveDensityHeadAverage_eq_sum
    (S : Finset ℕ) (sigma A : ℝ) (hsigma : 1 / 2 < sigma) :
    primeWaveDensityHeadAverage S sigma A hsigma =
      ∑ m ∈ S, ∑ n ∈ S,
        (Real.sinc (A * (Real.log (n : ℝ) - Real.log (m : ℝ))) *
          (primeWaveState sigma 0 hsigma m *
            starRingEnd ℂ (primeWaveState sigma 0 hsigma n))) •
              primeWaveMatrixAtom m n := by
  rw [primeWaveDensityHeadAverage]
  simp_rw [primeWaveDensityHeadSchattenOne_eq_sum]
  rw [MeasureTheory.integral_finsetSum S]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [MeasureTheory.integral_finsetSum S]
    · apply Finset.sum_congr rfl
      intro n hn
      exact integral_primeWaveMatrixTerm sigma A hsigma m n
    · intro n hn
      exact (integrable_primeWaveState_cross sigma A hsigma m n).smul_const
        (primeWaveMatrixAtom m n)
  · intro m hm
    exact MeasureTheory.integrable_finsetSum S fun n hn =>
      (integrable_primeWaveState_cross sigma A hsigma m n).smul_const
        (primeWaveMatrixAtom m n)

theorem primeWaveParticleDensityTerm_eq_matrix
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) (n : ℕ) :
    primeWaveParticleDensityTerm sigma hsigma n =
      (primeWaveState sigma 0 hsigma n *
        starRingEnd ℂ (primeWaveState sigma 0 hsigma n)) •
          primeWaveMatrixAtom n n := by
  rw [primeWaveParticleDensityTerm, primeWaveParticleWeight,
    primeWaveMatrixAtom, RHTower.positiveRankOneSchattenOne]
  congr 1
  simpa only [Complex.ofReal_pow] using
    (Complex.mul_conj' (primeWaveState sigma 0 hsigma n)).symm

theorem log_natCast_sub_log_natCast_ne_zero
    {m n : ℕ} (hm0 : m ≠ 0) (hn0 : n ≠ 0) (hmn : m ≠ n) :
    Real.log (n : ℝ) - Real.log (m : ℝ) ≠ 0 := by
  intro hlog
  have heqlog : Real.log (n : ℝ) = Real.log (m : ℝ) := sub_eq_zero.mp hlog
  have hexp := congrArg Real.exp heqlog
  rw [Real.exp_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)),
    Real.exp_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0))] at hexp
  exact hmn (Nat.cast_injective hexp.symm)

@[simp]
theorem primeWaveParticleWeight_zero
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    primeWaveParticleWeight sigma hsigma 0 = 0 := by
  rw [primeWaveParticleWeight_eq_zeta]
  simp

@[simp]
theorem primeWaveState_zero_coordinate
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    primeWaveState sigma t hsigma 0 = 0 := by
  have h := norm_primeWaveState_apply_sq_eq_weight sigma t hsigma 0
  rw [primeWaveParticleWeight_zero] at h
  have hnorm : ‖primeWaveState sigma t hsigma 0‖ = 0 := by
    nlinarith [norm_nonneg (primeWaveState sigma t hsigma 0)]
  exact norm_eq_zero.mp hnorm

theorem tendsto_primeWaveAveragedMatrixTerm
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) (m n : ℕ) :
    Tendsto (fun A : ℝ =>
      (Real.sinc (A * (Real.log (n : ℝ) - Real.log (m : ℝ))) *
        (primeWaveState sigma 0 hsigma m *
          starRingEnd ℂ (primeWaveState sigma 0 hsigma n))) •
            primeWaveMatrixAtom m n) atTop
      (nhds (if m = n then primeWaveParticleDensityTerm sigma hsigma m else 0)) := by
  by_cases hmn : m = n
  · subst n
    simp [primeWaveParticleDensityTerm_eq_matrix]
  · rw [if_neg hmn]
    by_cases hm0 : m = 0
    · subst m
      simp
    by_cases hn0 : n = 0
    · subst n
      simp
    have hd := log_natCast_sub_log_natCast_ne_zero hm0 hn0 hmn
    have hsR := tendsto_sinc_mul_atTop_zero_of_ne hd
    have hsC : Tendsto (fun A : ℝ =>
        (Real.sinc (A * (Real.log (n : ℝ) - Real.log (m : ℝ))) : ℂ))
        atTop (nhds 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hsR
    have hcoeff := hsC.mul_const
      (primeWaveState sigma 0 hsigma m *
        starRingEnd ℂ (primeWaveState sigma 0 hsigma n))
    let L : ℂ →L[ℂ] RHTower.SchattenOneOperator
        GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert :=
      (1 : ℂ →L[ℂ] ℂ).smulRight (primeWaveMatrixAtom m n)
    have hterm := L.continuous.continuousAt.tendsto.comp hcoeff
    convert hterm using 1
    · funext A
      change _ = (1 : ℂ →L[ℂ] ℂ) _ • primeWaveMatrixAtom m n
      simp
    · simp [L]

/-- Every positive-coordinate finite wave head dephases to its exact diagonal in trace norm. -/
theorem tendsto_primeWaveDensityHeadAverage_particleHead
    (S : Finset ℕ) (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    Tendsto (fun A : ℝ => primeWaveDensityHeadAverage S sigma A hsigma)
      atTop (nhds (primeWaveParticleDensityHead S sigma hsigma)) := by
  have hinner : ∀ m ∈ S, Tendsto (fun A : ℝ =>
      ∑ n ∈ S,
        (Real.sinc (A * (Real.log (n : ℝ) - Real.log (m : ℝ))) *
          (primeWaveState sigma 0 hsigma m *
            starRingEnd ℂ (primeWaveState sigma 0 hsigma n))) •
              primeWaveMatrixAtom m n)
      atTop (nhds (primeWaveParticleDensityTerm sigma hsigma m)) := by
    intro m hm
    have hsum := tendsto_finsetSum S (fun n hn =>
      tendsto_primeWaveAveragedMatrixTerm sigma hsigma m n)
    simpa [hm] using hsum
  have houter := tendsto_finsetSum S hinner
  simpa [primeWaveDensityHeadAverage_eq_sum,
    primeWaveParticleDensityHead] using houter

/-- Full particle dephasing: symmetric height averages converge to the zeta-normalized diagonal
in the genuine Schatten-one norm. -/
theorem tendsto_primeWaveDensityAverage_particleDensity
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    Tendsto (fun A : ℝ => primeWaveDensityAverage sigma A hsigma)
      atTop (nhds (primeWaveParticleDensity sigma hsigma)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hhas : HasSum (primeWaveParticleWeight sigma hsigma) 1 := by
    have h := (summable_primeWaveParticleWeight sigma hsigma).hasSum
    rw [tsum_primeWaveParticleWeight] at h
    exact h
  let delta : ℝ := min (epsilon / 4) ((epsilon / 8) ^ 2)
  have hdelta : 0 < delta := by
    apply lt_min
    · positivity
    · positivity
  obtain ⟨S, hStail⟩ := exists_finset_tsum_compl_lt hhas hdelta
  let q : ℝ := ∑' n : {n // n ∉ S}, primeWaveParticleWeight sigma hsigma n
  have hq0 : 0 ≤ q := by
    apply tsum_nonneg
    intro n
    exact sq_nonneg _
  have hq_quarter : q < epsilon / 4 := by
    calc
      q < delta := hStail
      _ ≤ epsilon / 4 := min_le_left _ _
  have hq_square : q < (epsilon / 8) ^ 2 := by
    calc
      q < delta := hStail
      _ ≤ (epsilon / 8) ^ 2 := min_le_right _ _
  let r : ℝ := ‖primeWaveState sigma 0 hsigma -
    primeWaveStateHead S sigma 0 hsigma‖
  have hrsq : r ^ 2 = q := by
    exact norm_primeWaveState_sub_head_sq S sigma 0 hsigma
  have hr : r < epsilon / 8 := by
    have hr0 : 0 ≤ r := norm_nonneg _
    nlinarith [sq_nonneg (r + epsilon / 8)]
  have hfullHead : ∀ A : ℝ,
      ‖primeWaveDensityAverage sigma A hsigma -
          primeWaveDensityHeadAverage S sigma A hsigma‖ < epsilon / 4 := by
    intro A
    have hbound := norm_primeWaveDensityAverage_sub_head_le S sigma A hsigma
    change _ ≤ 2 * r at hbound
    linarith
  have hparticleTail :
      ‖primeWaveParticleDensityHead S sigma hsigma -
          primeWaveParticleDensity sigma hsigma‖ < epsilon / 4 := by
    have hbound := norm_primeWaveParticleDensityHead_sub_le S sigma hsigma
    change _ ≤ q at hbound
    linarith
  have hfinite := tendsto_primeWaveDensityHeadAverage_particleHead S sigma hsigma
  rw [Metric.tendsto_atTop] at hfinite
  obtain ⟨A0, hA0⟩ := hfinite (epsilon / 2) (half_pos hepsilon)
  refine ⟨A0, fun A hA => ?_⟩
  have hmiddle := hA0 A hA
  rw [dist_eq_norm] at hmiddle ⊢
  have hdecomp : primeWaveDensityAverage sigma A hsigma -
      primeWaveParticleDensity sigma hsigma =
      (primeWaveDensityAverage sigma A hsigma -
        primeWaveDensityHeadAverage S sigma A hsigma) +
      (primeWaveDensityHeadAverage S sigma A hsigma -
        primeWaveParticleDensityHead S sigma hsigma) +
      (primeWaveParticleDensityHead S sigma hsigma -
        primeWaveParticleDensity sigma hsigma) := by
    abel
  rw [hdecomp]
  calc
    ‖(primeWaveDensityAverage sigma A hsigma -
          primeWaveDensityHeadAverage S sigma A hsigma) +
        (primeWaveDensityHeadAverage S sigma A hsigma -
          primeWaveParticleDensityHead S sigma hsigma) +
        (primeWaveParticleDensityHead S sigma hsigma -
          primeWaveParticleDensity sigma hsigma)‖ ≤
      ‖primeWaveDensityAverage sigma A hsigma -
          primeWaveDensityHeadAverage S sigma A hsigma‖ +
        ‖primeWaveDensityHeadAverage S sigma A hsigma -
          primeWaveParticleDensityHead S sigma hsigma‖ +
        ‖primeWaveParticleDensityHead S sigma hsigma -
          primeWaveParticleDensity sigma hsigma‖ := by
      calc
        _ ≤ ‖(primeWaveDensityAverage sigma A hsigma -
              primeWaveDensityHeadAverage S sigma A hsigma) +
            (primeWaveDensityHeadAverage S sigma A hsigma -
              primeWaveParticleDensityHead S sigma hsigma)‖ +
            ‖primeWaveParticleDensityHead S sigma hsigma -
              primeWaveParticleDensity sigma hsigma‖ := norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ < epsilon := by
      linarith [hfullHead A, hmiddle, hparticleTail]

/-! ## Normalized Bohr outer wave and exact Poisson density -/

/-- Prime Poisson parameters in the canonical natural enumeration of rational primes. -/
def primePoissonNaturalParameters
    (sigma t : ℝ) (hsigma : 0 < sigma) : ℕ → CirclePoissonParameter :=
  fun n => primePoissonParameter sigma t hsigma (natEquivPrimes n)

theorem summable_norm_sq_primePoissonNaturalParameters
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    Summable (fun n => ‖(primePoissonNaturalParameters sigma t (by linarith) n : ℂ)‖ ^ 2) := by
  have hp := (summable_normSq_primePoissonParameter_zero_iff sigma t (by linarith)).mpr hsigma
  have hnat := natEquivPrimes.summable_iff.mpr hp
  refine hnat.congr ?_
  intro n
  simp only [Function.comp_apply, primePoissonNaturalParameters,
    coe_primePoissonParameter, sub_zero]

theorem summable_hellinger_primePoissonNaturalParameters
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    Summable (fun n => 1 - circlePoissonHellingerAffinity
      (primePoissonNaturalParameters sigma t (by linarith) n)
      zeroCirclePoissonParameter) := by
  apply summable_circlePoissonHellingerDefect_of_tendsto_zero_of_summable_normSq
  · change Tendsto (fun n =>
      ((primePoissonParameter sigma t (by linarith) (natEquivPrimes n) :
        CirclePoissonParameter) : ℂ)) atTop (nhds 0)
    exact tendsto_primePoissonParameter_natEquivPrimes_zero sigma t (by linarith)
  · exact tendsto_const_nhds
  · simpa [zeroCirclePoissonParameter, sub_zero] using
      summable_norm_sq_primePoissonNaturalParameters sigma t hsigma

/-- The normalized Bohr wave: strong Haar-`L²` limit of its finite analytic prime Euler products. -/
def primeBohrWave
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    Lp ℂ 2 (natCirclePoissonProductMeasure (fun _ => zeroCirclePoissonParameter)) :=
  circlePoissonOuterFactorLimitLp
    (primePoissonNaturalParameters sigma t (by linarith))
    (summable_norm_sq_primePoissonNaturalParameters sigma t hsigma)

/-- Finite normalized Euler product whose strong `L²` limit is `primeBohrWave`. -/
def primeBohrEulerPrefix
    (sigma t : ℝ) (hsigma : 0 < sigma) (N : ℕ) (x : ℕ → Circle) : ℂ :=
  circlePoissonPrefixOuterFactor (primePoissonNaturalParameters sigma t hsigma) N x

theorem tendsto_primeBohrEulerPrefixLp
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    Tendsto (circlePoissonPrefixOuterFactorLp
      (primePoissonNaturalParameters sigma t (by linarith))) atTop
      (nhds (primeBohrWave sigma t hsigma)) :=
  tendsto_circlePoissonPrefixOuterFactorLp
    (primePoissonNaturalParameters sigma t (by linarith))
    (summable_norm_sq_primePoissonNaturalParameters sigma t hsigma)

/-- Literal local Dirichlet coefficient `p^{-s}` for `s = sigma + i t`. -/
def primeDirichletEulerCoefficient (sigma t : ℝ) (p : Nat.Primes) : ℂ :=
  starRingEnd ℂ (primePoissonParameterValue sigma t p)

theorem primeDirichletEulerCoefficient_eq_exp
    (sigma t : ℝ) (p : Nat.Primes) :
    primeDirichletEulerCoefficient sigma t p =
      Complex.exp ((((-sigma : ℝ) : ℂ) - (t : ℂ) * Complex.I) *
        (Real.log (p : ℝ) : ℂ)) := by
  rw [primeDirichletEulerCoefficient, primePoissonParameterValue]
  rw [← Complex.exp_conj]
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  ring

theorem norm_sq_primePoissonParameterValue_eq_rpow
    (sigma t : ℝ) (p : Nat.Primes) :
    ‖primePoissonParameterValue sigma t p‖ ^ 2 = (p : ℝ) ^ (-2 * sigma) := by
  rw [norm_primePoissonParameterValue]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- Exact finite Euler-product formula, including every local normalizer and the literal
`p^{-s}` denominator. -/
theorem primeBohrEulerPrefix_eq_product
    (sigma t : ℝ) (hsigma : 0 < sigma) (N : ℕ) (x : ℕ → Circle) :
    primeBohrEulerPrefix sigma t hsigma N x =
      ∏ n : ↑(Finset.range N),
        (Real.sqrt (1 - ((natEquivPrimes n : Nat.Primes) : ℝ) ^ (-2 * sigma)) : ℂ) /
          (1 - primeDirichletEulerCoefficient sigma t (natEquivPrimes n) * (x n : ℂ)) := by
  unfold primeBohrEulerPrefix circlePoissonPrefixOuterFactor
  apply Finset.prod_congr rfl
  intro n _
  rw [circlePoissonOuterFactor, primePoissonNaturalParameters,
    coe_primePoissonParameter, primeDirichletEulerCoefficient,
    norm_sq_primePoissonParameterValue_eq_rpow]

/-- On the enumerated prime torus, the product-Poisson law is exactly Haar weighted by
`|primeBohrWave|²`. -/
theorem natPrimePoissonProductMeasure_eq_primeBohrDensity
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    natCirclePoissonProductMeasure
        (primePoissonNaturalParameters sigma t (by linarith)) =
      circlePoissonOuterDensityMeasure (primeBohrWave sigma t hsigma) := by
  exact natCirclePoissonProductMeasure_eq_outerDensityMeasure
    (primePoissonNaturalParameters sigma t (by linarith))
    (summable_norm_sq_primePoissonNaturalParameters sigma t hsigma)
    (summable_hellinger_primePoissonNaturalParameters sigma t hsigma)

/-- Prime-torus spectral measure generated by the squared modulus of the normalized Bohr wave,
transported through the canonical prime-coordinate homeomorphism. -/
def primeBohrSpectralMeasure
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    Measure (Nat.Primes → UnitAddCircle) :=
  Measure.map natCircleHomeomorphPrimeTorus
    (circlePoissonOuterDensityMeasure (primeBohrWave sigma t hsigma))

/-- Exact equation (5): the full prime Poisson law is the wave spectral measure `|F_s|² dm`. -/
theorem primePoissonMeasure_eq_primeBohrSpectralMeasure
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    primePoissonMeasure sigma t (by linarith) =
      primeBohrSpectralMeasure sigma t hsigma := by
  rw [primePoissonMeasure, primeBohrSpectralMeasure,
    ← map_natCirclePoissonProductMeasure_eq_torusPoissonMeasure]
  congr 1
  exact natPrimePoissonProductMeasure_eq_primeBohrDensity sigma t hsigma

/-! ## Exact normalized Bohr series -/

/-- Natural prime occupations, identified with positive integers by unique factorization. -/
def naturalOccupationEquivNatPos : (ℕ →₀ ℕ) ≃ {n : ℕ // n ≠ 0} :=
  (Finsupp.domCongr natEquivPrimes).toEquiv.trans occupationEquivNatPos

/-- The normalized arithmetic wave with its identically zero coordinate removed. -/
def primeWavePositiveState
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
  lp (fun _ : {n : ℕ // n ≠ 0} => ℂ) 2 :=
  ⟨fun n => primeWaveState sigma t hsigma n,
    by
      change Memℓp (fun n : {n : ℕ // n ≠ 0} =>
        primeWaveState sigma t hsigma n) 2
      rw [memℓp_gen_iff (by norm_num)]
      have h := (memℓp_gen_iff (by norm_num)).mp
        (lp.memℓp (primeWaveState sigma t hsigma))
      exact h.subtype (fun n : ℕ => n ≠ 0)⟩

/-- Normalized Dirichlet coefficients indexed by natural prime occupations. -/
def primeNaturalCoefficientState
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    lp (fun _ : ℕ →₀ ℕ => ℂ) 2 :=
  lpDomCongr (p := 2) (by norm_num) naturalOccupationEquivNatPos
    (primeWavePositiveState sigma t hsigma)

@[simp]
theorem primeNaturalCoefficientState_apply
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) (ν : ℕ →₀ ℕ) :
    primeNaturalCoefficientState sigma t hsigma ν =
      primeWaveState sigma t hsigma
        (primeProduct ((Finsupp.domCongr natEquivPrimes) ν)) := rfl

theorem norm_primeWavePositiveState
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeWavePositiveState sigma t hsigma‖ = 1 := by
  have hsq : ‖primeWavePositiveState sigma t hsigma‖ ^ 2 =
      ‖primeWaveState sigma t hsigma‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    let f : ℕ → ℝ := fun n => ‖primeWaveState sigma t hsigma n‖ ^ 2
    change (∑' n : ↑{n : ℕ | n ≠ 0}, f n) = ∑' n : ℕ, f n
    rw [tsum_subtype]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [f]
    · rw [Set.indicator_of_mem hn]
  rw [norm_primeWaveState] at hsq
  nlinarith [norm_nonneg (primeWavePositiveState sigma t hsigma)]

theorem norm_primeNaturalCoefficientState
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeNaturalCoefficientState sigma t hsigma‖ = 1 := by
  rw [primeNaturalCoefficientState,
    LinearIsometryEquiv.norm_map, norm_primeWavePositiveState]

/-- A natural occupation monomial is the literal Dirichlet coefficient of its prime product. -/
theorem primeDirichletNaturalOccupationProduct_eq
    (sigma t : ℝ) (ν : ℕ →₀ ℕ) :
    ν.prod (fun n k =>
        primeDirichletEulerCoefficient sigma t (natEquivPrimes n) ^ k) =
      primeWavePhase t (primeProduct ((Finsupp.domCongr natEquivPrimes) ν)) *
        ((((primeProduct ((Finsupp.domCongr natEquivPrimes) ν) : ℕ) : ℝ) ^
          (-sigma) : ℝ) : ℂ) := by
  classical
  let A : ℂ := ((-sigma : ℝ) : ℂ) - (t : ℂ) * Complex.I
  let κ : Nat.Primes →₀ ℕ := (Finsupp.domCongr natEquivPrimes) ν
  have hlog : Real.log (primeProduct κ : ℝ) =
      ν.sum fun n k => (k : ℝ) * Real.log (natEquivPrimes n : ℕ) := by
    rw [log_primeProduct]
    simp [κ, Finsupp.sum, Finsupp.domCongr_apply, Finsupp.equivMapDomain]
  have hprod :
      ν.prod (fun n k =>
          primeDirichletEulerCoefficient sigma t (natEquivPrimes n) ^ k) =
        Complex.exp (A * (Real.log (primeProduct κ : ℝ) : ℂ)) := by
    rw [Finsupp.prod]
    calc
      ∏ n ∈ ν.support,
          primeDirichletEulerCoefficient sigma t (natEquivPrimes n) ^ ν n =
          ∏ n ∈ ν.support,
            Complex.exp ((ν n : ℂ) *
              (A * (Real.log (natEquivPrimes n : ℕ) : ℂ))) := by
        apply Finset.prod_congr rfl
        intro n _
        rw [primeDirichletEulerCoefficient_eq_exp]
        change Complex.exp (A * (Real.log (natEquivPrimes n : ℕ) : ℂ)) ^ ν n = _
        exact (Complex.exp_nat_mul
          (A * (Real.log (natEquivPrimes n : ℕ) : ℂ)) (ν n)).symm
      _ = Complex.exp (∑ n ∈ ν.support,
            ((ν n : ℂ) *
              (A * (Real.log (natEquivPrimes n : ℕ) : ℂ)))) := by
        exact (Complex.exp_sum ν.support fun n =>
          ((ν n : ℂ) *
            (A * (Real.log (natEquivPrimes n : ℕ) : ℂ)))).symm
      _ = Complex.exp (A * (Real.log (primeProduct κ : ℝ) : ℂ)) := by
        congr 1
        rw [hlog]
        change (∑ n ∈ ν.support, (ν n : ℂ) *
            (A * (Real.log (natEquivPrimes n : ℕ) : ℂ))) =
          A * (((∑ n ∈ ν.support,
            (ν n : ℝ) * Real.log (natEquivPrimes n : ℕ)) : ℝ) : ℂ)
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
  rw [hprod]
  have hκpos : 0 < primeProduct κ := primeProduct_pos κ
  rw [primeWavePhase, if_neg hκpos.ne', Real.rpow_def_of_pos (by exact_mod_cast hκpos)]
  change Complex.exp (A * (Real.log (primeProduct κ : ℝ) : ℂ)) =
    Complex.exp (-(((t * Real.log (primeProduct κ : ℝ) : ℝ) : ℂ) * Complex.I)) *
      ((Real.exp (Real.log (primeProduct κ : ℝ) * -sigma) : ℝ) : ℂ)
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [A, κ]
  rw [Complex.ofReal_neg]
  ring

/-- Every normalized coefficient has global zeta normalizer times its local Euler monomial. -/
theorem primeNaturalCoefficientState_apply_eq_normalized_product
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) (ν : ℕ →₀ ℕ) :
    primeNaturalCoefficientState sigma t hsigma ν =
      (‖primeWaveUntwistedAmplitude sigma hsigma‖ : ℂ)⁻¹ *
        ν.prod (fun n k =>
          primeDirichletEulerCoefficient sigma t (natEquivPrimes n) ^ k) := by
  rw [primeNaturalCoefficientState_apply,
    primeDirichletNaturalOccupationProduct_eq]
  rw [primeWaveState, GaloisForLFunctions.RHTower.PrimeDensity.arithState]
  change (‖primeWaveUntwistedAmplitude sigma hsigma‖ : ℂ)⁻¹ *
      GaloisForLFunctions.RHTower.PrimeDensity.amp sigma (primeWavePhase t)
        (primeProduct ((Finsupp.domCongr natEquivPrimes) ν)) = _
  rw [GaloisForLFunctions.RHTower.PrimeDensity.amp]

theorem norm_primeWaveUntwistedAmplitude_pos
    (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    0 < ‖primeWaveUntwistedAmplitude sigma hsigma‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hcoord := congrArg (fun x :
      GaloisForLFunctions.RHTower.PrimeDensity.ArithHilbert => x 1) hzero
  simp [primeWaveUntwistedAmplitude,
    GaloisForLFunctions.RHTower.PrimeDensity.amp] at hcoord

theorem primeOuterNormalizer_nonneg
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    0 ≤ circlePoissonOuterNormalizerProduct
      (primePoissonNaturalParameters sigma t (by linarith)) := by
  apply IsClosed.mem_of_tendsto isClosed_Ici
    (tendsto_circlePoissonOuterNormalizer_prefix
      (primePoissonNaturalParameters sigma t (by linarith))
      (summable_norm_sq_primePoissonNaturalParameters sigma t hsigma))
  filter_upwards with N
  exact Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _

/-- Coefficients with the a priori outer-product normalizer. -/
def primeOuterCoefficientState
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    lp (fun _ : ℕ →₀ ℕ => ℂ) 2 :=
  (((circlePoissonOuterNormalizerProduct
      (primePoissonNaturalParameters sigma t (by linarith)) *
      ‖primeWaveUntwistedAmplitude sigma hsigma‖ : ℝ) : ℂ)) •
    primeNaturalCoefficientState sigma t hsigma

theorem primeOuterCoefficientState_apply
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) (ν : ℕ →₀ ℕ) :
    primeOuterCoefficientState sigma t hsigma ν =
      (circlePoissonOuterNormalizerProduct
        (primePoissonNaturalParameters sigma t (by linarith)) : ℂ) *
        ν.prod (fun n k =>
          primeDirichletEulerCoefficient sigma t (natEquivPrimes n) ^ k) := by
  rw [primeOuterCoefficientState, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    primeNaturalCoefficientState_apply_eq_normalized_product]
  have hnorm : (‖primeWaveUntwistedAmplitude sigma hsigma‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_primeWaveUntwistedAmplitude_pos sigma hsigma).ne'
  push_cast
  field_simp

theorem primeBohrWave_eq_outerCoefficientTransform
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    primeBohrWave sigma t hsigma =
      naturalBohrTransform (primeOuterCoefficientState sigma t hsigma) := by
  apply circlePoissonOuterFactorLimitLp_eq_naturalBohrTransform
  intro ν
  rw [primeOuterCoefficientState_apply]
  congr 1

theorem norm_primeBohrWave
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    ‖primeBohrWave sigma t hsigma‖ = 1 := by
  have hnorm := (tendsto_primeBohrEulerPrefixLp sigma t hsigma).norm
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  apply tendsto_nhds_unique hnorm
  convert hone using 1
  funext N
  exact norm_circlePoissonPrefixOuterFactorLp _ _

/-- The infinite product of local positive normalizers is the inverse global Dirichlet norm. -/
theorem primeOuterNormalizer_eq_inv_norm
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    circlePoissonOuterNormalizerProduct
        (primePoissonNaturalParameters sigma t (by linarith)) =
      ‖primeWaveUntwistedAmplitude sigma hsigma‖⁻¹ := by
  have hstate : ‖primeOuterCoefficientState sigma t hsigma‖ = 1 := by
    calc
      ‖primeOuterCoefficientState sigma t hsigma‖ =
          ‖naturalBohrTransform (primeOuterCoefficientState sigma t hsigma)‖ :=
        (LinearIsometry.norm_map _ _).symm
      _ = ‖primeBohrWave sigma t hsigma‖ := by
        rw [primeBohrWave_eq_outerCoefficientTransform]
      _ = 1 := norm_primeBohrWave sigma t hsigma
  rw [primeOuterCoefficientState, norm_smul,
    norm_primeNaturalCoefficientState, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (primeOuterNormalizer_nonneg sigma t hsigma)
      (norm_nonneg _))] at hstate
  exact eq_inv_of_mul_eq_one_left hstate

/-- Exact global zeta normalization `zeta(2 sigma)^(-1/2)`. -/
theorem primeOuterNormalizer_eq_zetaInvSqrt
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    circlePoissonOuterNormalizerProduct
        (primePoissonNaturalParameters sigma t (by linarith)) =
      (Real.sqrt (primeWaveZetaMass sigma))⁻¹ := by
  rw [primeOuterNormalizer_eq_inv_norm sigma t hsigma,
    ← norm_sq_primeWaveUntwistedAmplitude_eq_zetaMass sigma hsigma,
    Real.sqrt_sq (norm_nonneg _)]

/-- Exact normalized Bohr series with coefficients `zeta(2 sigma)^(-1/2) n^{-sigma-it}`. -/
theorem primeBohrWave_eq_naturalBohrTransform
    (sigma t : ℝ) (hsigma : 1 / 2 < sigma) :
    primeBohrWave sigma t hsigma =
      naturalBohrTransform (primeNaturalCoefficientState sigma t hsigma) := by
  apply circlePoissonOuterFactorLimitLp_eq_naturalBohrTransform
  intro ν
  rw [primeNaturalCoefficientState_apply_eq_normalized_product,
    primeOuterNormalizer_eq_inv_norm sigma t hsigma]
  push_cast
  congr 1

end
end GaloisForLFunctions.HTGeometry

