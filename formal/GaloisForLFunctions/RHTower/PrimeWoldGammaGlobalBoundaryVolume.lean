import GaloisForLFunctions.HTGeometry.PrimeOccupationPolarizedGammaPhaseSurvival
import GaloisForLFunctions.RHTower.PrimeStokesWoldCalderonSuspension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Prime Wold--Gamma global boundary volume

For a finite prime source, the first occupation moment is exactly the inverse product of the unit
Wold boundary masses `1 - p⁻¹`.  Consequently the finite genus-zero/genus-one polarized Gamma
scheme change is an exact irregular exponential gauge with canonical parameter that boundary
volume.

This file proves the finite-stage algebra, degeneration of the volume along the canonical all-prime
exhaustion, and the exact two-sided polynomial-moderateness selector for the resulting irregular
gauge.  It does not construct a bi-moderate enhanced completion or prove that Xi conormal fibres
survive in both reflected branches.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace GaloisForLFunctions

private theorem complex_tsum_pi_geometric_fin :
    ∀ (n : ℕ) (u : Fin n → ℂ), (∀ i, ‖u i‖ < 1) →
      Summable (fun f : Fin n → ℕ => ‖∏ i, u i ^ f i‖) ∧
      ∑' f : Fin n → ℕ, ∏ i, u i ^ f i =
        ∏ i, (1 - u i)⁻¹ := by
  intro n
  induction n with
  | zero =>
      intro u hu
      constructor
      · exact Summable.of_finite
      · simp
  | succ n ih =>
      intro u hu
      let v : Fin n → ℂ := fun i => u i.succ
      obtain ⟨hbNorm, hbValue⟩ := ih v (fun i => hu i.succ)
      let a : ℕ → ℂ := fun k => u 0 ^ k
      let b : (Fin n → ℕ) → ℂ := fun f => ∏ i, v i ^ f i
      have haNorm : Summable (fun k => ‖a k‖) := by
        simpa only [a, norm_pow] using
          summable_geometric_of_lt_one (norm_nonneg (u 0)) (hu 0)
      have hbNorm' : Summable (fun f => ‖b f‖) := by
        simpa only [b, v] using hbNorm
      have hbSum : HasSum b (∏ i, (1 - v i)⁻¹) := by
        have h := hbNorm'.of_norm.hasSum
        rw [show (∑' f, b f) = ∏ i, (1 - v i)⁻¹ by
          simpa only [b] using hbValue] at h
        exact h
      have habNorm :
          Summable (fun x : ℕ × (Fin n → ℕ) => a x.1 * b x.2) :=
        summable_mul_of_summable_norm haNorm hbNorm'
      have habNormReal :
          Summable (fun x : ℕ × (Fin n → ℕ) => ‖a x.1‖ * ‖b x.2‖) := by
        exact summable_mul_of_summable_norm
          (R := ℝ) (f := fun k => ‖a k‖) (g := fun f => ‖b f‖)
          haNorm.norm hbNorm'.norm
      have habSum :
          HasSum (fun x : ℕ × (Fin n → ℕ) => a x.1 * b x.2)
            ((1 - u 0)⁻¹ * ∏ i, (1 - v i)⁻¹) :=
        (hasSum_geometric_of_norm_lt_one (hu 0)).mul hbSum habNorm
      constructor
      · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).summable_iff]
        simpa only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ,
          norm_mul, a, b, v] using! habNormReal
      · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).tsum_eq]
        simpa only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ,
          a, b, v] using habSum.tsum_eq

private theorem complex_tsum_pi_geometric {ι : Type*} [Fintype ι]
    (u : ι → ℂ) (hu : ∀ i, ‖u i‖ < 1) :
    ∑' f : ι → ℕ, ∏ i, u i ^ f i =
      ∏ i, (1 - u i)⁻¹ := by
  let e := Fintype.equivFin ι
  let pe : (ι → ℕ) ≃ (Fin (Fintype.card ι) → ℕ) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℕ) e
  calc
    ∑' f : ι → ℕ, ∏ i, u i ^ f i =
        ∑' h : Fin (Fintype.card ι) → ℕ,
          ∏ j, u (e.symm j) ^ h j := by
            rw [← pe.tsum_eq]
            congr 1
            funext f
            exact Fintype.prod_equiv e (fun i => u i ^ f i)
              (fun j => u (e.symm j) ^ pe f j) (by simp [pe])
    _ = ∏ j, (1 - u (e.symm j))⁻¹ :=
      (complex_tsum_pi_geometric_fin _ _ (fun j => hu (e.symm j))).2
    _ = ∏ i, (1 - u i)⁻¹ := by
      exact Fintype.prod_equiv e.symm
        (fun j => (1 - u (e.symm j))⁻¹)
        (fun i => (1 - u i)⁻¹) (by simp)

/-- Exact finite-boson Euler product over any finite nome type. -/
theorem tsum_nomeMonomial_eq_fintype_eulerProduct
    {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ < 1) :
    ∑' ν : ι →₀ ℕ, HTGeometry.nomeMonomial u ν =
      ∏ i, (1 - u i)⁻¹ := by
  let e := (Finsupp.equivFunOnFinite : (ι →₀ ℕ) ≃ (ι → ℕ))
  calc
    (∑' ν : ι →₀ ℕ, HTGeometry.nomeMonomial u ν) =
        ∑' ν : ι →₀ ℕ, ∏ i, u i ^ (e ν) i := by
          apply tsum_congr
          intro ν
          rw [HTGeometry.nomeMonomial,
            Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
          rfl
    _ = ∑' f : ι → ℕ, ∏ i, u i ^ f i :=
      e.tsum_eq (fun f : ι → ℕ => ∏ i, u i ^ f i)
    _ = ∏ i, (1 - u i)⁻¹ := complex_tsum_pi_geometric u hu

/-- The finite prime-occupation first moment is its ordinary finite Euler product at `1`. -/
theorem finitePrimeOccupationFirstMoment_eq_eulerProduct
    (S : Finset Nat.Primes) :
    finitePrimeOccupationFirstMoment S =
      ∏ p : S, (1 - primeLinearNome p)⁻¹ := by
  rw [finitePrimeOccupationFirstMoment]
  exact tsum_nomeMonomial_eq_fintype_eulerProduct
    (fun p : S => primeLinearNome p)
    (fun p => norm_primeLinearNome_lt_one p)

/-- Real product of the local multiplication-Wold boundary masses. -/
def finitePrimeWoldBoundaryVolume (S : Finset Nat.Primes) : ℝ :=
  ∏ p : S, (1 - ((((p : Nat.Primes) : ℕ) : ℝ))⁻¹)

/-- Every finite-prime Wold boundary volume is strictly positive. -/
theorem finitePrimeWoldBoundaryVolume_pos (S : Finset Nat.Primes) :
    0 < finitePrimeWoldBoundaryVolume S := by
  rw [finitePrimeWoldBoundaryVolume]
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < ((p : Nat.Primes) : ℕ) := by
    exact_mod_cast (p : Nat.Primes).2.one_lt
  exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).2 hp1)

/-- Complexifying the real boundary volume gives the product of the prime-linear defects. -/
theorem finitePrimeWoldBoundaryVolume_cast (S : Finset Nat.Primes) :
    (finitePrimeWoldBoundaryVolume S : ℂ) =
      ∏ p : S, (1 - primeLinearNome p) := by
  rw [finitePrimeWoldBoundaryVolume]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  rw [primeLinearNome]

/-- Exact global source weld: finite prime-occupation first trace is the inverse Wold boundary
volume. -/
theorem finitePrimeOccupationFirstMoment_eq_inv_woldBoundaryVolume
    (S : Finset Nat.Primes) :
    finitePrimeOccupationFirstMoment S =
      (finitePrimeWoldBoundaryVolume S : ℂ)⁻¹ := by
  rw [finitePrimeOccupationFirstMoment_eq_eulerProduct,
    finitePrimeWoldBoundaryVolume_cast]
  exact Finset.prod_inv_distrib (fun p : S => 1 - primeLinearNome p)

/-- Each prime-linear Euler defect is the complexified unit-exponential Wold first-cell mass. -/
theorem one_sub_primeLinearNome_eq_woldBoundaryMass (p : Nat.Primes) :
    (1 : ℂ) - primeLinearNome p =
      (RHTower.unitExponentialWoldBoundaryMass
        (Real.log ((p : ℕ) : ℝ)) : ℂ) := by
  rw [primeLinearNome,
    RHTower.unitExponentialWoldBoundaryMass_log
      (show (0 : ℝ) < (p : ℕ) by exact_mod_cast p.2.pos)]
  norm_num [Complex.ofReal_inv]

/-- The complexified global volume is exactly the product of unit-exponential Wold cell masses. -/
theorem finitePrimeWoldBoundaryVolume_cast_eq_woldProduct
    (S : Finset Nat.Primes) :
    (finitePrimeWoldBoundaryVolume S : ℂ) =
      ∏ p : S,
        (RHTower.unitExponentialWoldBoundaryMass
          (Real.log (((p : Nat.Primes) : ℕ) : ℝ)) : ℂ) := by
  rw [finitePrimeWoldBoundaryVolume_cast]
  apply Finset.prod_congr rfl
  intro p hp
  exact one_sub_primeLinearNome_eq_woldBoundaryMass p

/-- Finite-prime raw, genus-zero reflected occupation phase. -/
def finitePrimeGenusZeroPolarizedPhase
    (S : Finset Nat.Primes) (t : ℂ) : ℂ :=
  HTGeometry.infiniteMultipleEllipticGamma
      0 (fun p : S => primeLinearNome p) t /
    HTGeometry.infiniteMultipleEllipticGamma
      0 (fun p : S => primeLinearNome p) (-t)

/-- Finite-prime tangent-normalized, genus-one reflected occupation phase. -/
def finitePrimeGenusOnePolarizedPhase
    (S : Finset Nat.Primes) (t : ℂ) : ℂ :=
  HTGeometry.infiniteMultipleEllipticGamma
      1 (fun p : S => primeLinearNome p) t /
    HTGeometry.infiniteMultipleEllipticGamma
      1 (fun p : S => primeLinearNome p) (-t)

/-- Exact irregular gauge: tangent normalization introduces `exp(2t / epsilon_S)`, where
`epsilon_S` is the finite-prime Wold boundary volume. -/
theorem finitePrimeGenusOnePolarizedPhase_eq_irregularGauge_mul
    (S : Finset Nat.Primes) (t : ℂ) :
    finitePrimeGenusOnePolarizedPhase S t =
      Complex.exp
          (2 * t * (finitePrimeWoldBoundaryVolume S : ℂ)⁻¹) *
        finitePrimeGenusZeroPolarizedPhase S t := by
  rw [finitePrimeGenusOnePolarizedPhase,
    finitePrimeGenusZeroPolarizedPhase,
    finitePrime_genusOne_polarized_eq_genusZero_polarized_mul_firstMomentGauge,
    finitePrimeOccupationFirstMoment_eq_inv_woldBoundaryVolume]

/-- Recovered raw phase: the opposite irregular branch multiplies the genus-one phase. -/
theorem finitePrimeGenusZeroPolarizedPhase_eq_oppositeIrregularGauge_mul
    (S : Finset Nat.Primes) (t : ℂ) :
    finitePrimeGenusZeroPolarizedPhase S t =
      Complex.exp
          (-(2 * t * (finitePrimeWoldBoundaryVolume S : ℂ)⁻¹)) *
        finitePrimeGenusOnePolarizedPhase S t := by
  rw [finitePrimeGenusOnePolarizedPhase_eq_irregularGauge_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  simp

/-- Reflection exchanges the two raw branches by multiplicative inversion. -/
theorem finitePrimeGenusZeroPolarizedPhase_reflection
    (S : Finset Nat.Primes) (t : ℂ) :
    finitePrimeGenusZeroPolarizedPhase S (-t) =
      (finitePrimeGenusZeroPolarizedPhase S t)⁻¹ := by
  simp [finitePrimeGenusZeroPolarizedPhase, inv_div]

/-- Reflection exchanges the two tangent-normalized branches by multiplicative inversion. -/
theorem finitePrimeGenusOnePolarizedPhase_reflection
    (S : Finset Nat.Primes) (t : ℂ) :
    finitePrimeGenusOnePolarizedPhase S (-t) =
      (finitePrimeGenusOnePolarizedPhase S t)⁻¹ := by
  simp [finitePrimeGenusOnePolarizedPhase, inv_div]

/-- Canonical finite set of prime subtypes below `N`. -/
def primesBelowSubtype (N : ℕ) : Finset Nat.Primes :=
  (Nat.primesBelow N).attach.map
    (⟨fun p => ⟨p.1, Nat.prime_of_mem_primesBelow p.2⟩,
      fun _ _ h =>
        Subtype.ext (congrArg (fun q : Nat.Primes => (q : ℕ)) h)⟩ :
      {p // p ∈ Nat.primesBelow N} ↪ Nat.Primes)

/-- Canonical all-prime exhaustion of the finite Wold boundary volume. -/
def primeWoldBoundaryVolumeBelow (N : ℕ) : ℝ :=
  finitePrimeWoldBoundaryVolume (primesBelowSubtype N)

/-- The subtype exhaustion is the ordinary finite product over primes below `N`. -/
theorem primeWoldBoundaryVolumeBelow_eq (N : ℕ) :
    primeWoldBoundaryVolumeBelow N =
      ∏ p ∈ Nat.primesBelow N, (1 - ((p : ℝ))⁻¹) := by
  rw [primeWoldBoundaryVolumeBelow, finitePrimeWoldBoundaryVolume]
  calc
    (∏ p : primesBelowSubtype N,
        (1 - ((((p : Nat.Primes) : ℕ) : ℝ))⁻¹)) =
        ∏ p ∈ primesBelowSubtype N,
          (1 - ((((p : Nat.Primes) : ℕ) : ℝ))⁻¹) :=
      (Finset.prod_subtype (primesBelowSubtype N)
        (fun _ => Iff.rfl)
        (fun p : Nat.Primes => (1 - ((((p : Nat.Primes) : ℕ) : ℝ))⁻¹))).symm
    _ = ∏ p ∈ Nat.primesBelow N, (1 - ((p : ℝ))⁻¹) := by
      rw [primesBelowSubtype, Finset.prod_map]
      change
        (∏ p ∈ (Nat.primesBelow N).attach,
          (1 - ((((p : {p // p ∈ Nat.primesBelow N}) : ℕ) : ℝ))⁻¹)) =
          ∏ p ∈ Nat.primesBelow N, (1 - ((p : ℝ))⁻¹)
      exact Finset.prod_attach (Nat.primesBelow N)
        (fun p : ℕ => (1 - ((p : ℝ))⁻¹))

/-- Prime reciprocal partial sum on the same exhaustion. -/
def primeReciprocalPartialSum (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow N, ((p : ℝ))⁻¹

/-- Euler's divergence theorem in the exact partial-sum form used by the global boundary volume. -/
theorem tendsto_primeReciprocalPartialSum_atTop :
    Filter.Tendsto primeReciprocalPartialSum Filter.atTop Filter.atTop := by
  let f : ℕ → ℝ :=
    Set.indicator {p : ℕ | p.Prime} (fun n => (1 : ℝ) / n)
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    exact Set.indicator_nonneg (fun _ _ => by positivity) n
  have hdiv : ¬ Summable f := by
    simpa only [f] using not_summable_one_div_on_primes
  have h :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp hdiv
  apply h.congr'
  filter_upwards [] with N
  rw [primeReciprocalPartialSum, Nat.primesBelow_eq_filter_range]
  simp only [f, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime
  · simp [hprime, div_eq_mul_inv]
  · simp [hprime]

/-- Every boundary volume in the canonical exhaustion is nonnegative. -/
theorem primeWoldBoundaryVolumeBelow_nonneg (N : ℕ) :
    0 ≤ primeWoldBoundaryVolumeBelow N := by
  rw [primeWoldBoundaryVolumeBelow_eq]
  apply Finset.prod_nonneg
  intro p hp
  have hprime := Nat.prime_of_mem_primesBelow hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
  exact sub_nonneg.mpr ((inv_le_one₀ (by positivity)).2 hp1)

/-- Elementary exponential majorant for the finite Wold boundary volume. -/
theorem primeWoldBoundaryVolumeBelow_le_exp (N : ℕ) :
    primeWoldBoundaryVolumeBelow N ≤
      Real.exp (-primeReciprocalPartialSum N) := by
  rw [primeWoldBoundaryVolumeBelow_eq, primeReciprocalPartialSum]
  calc
    (∏ p ∈ Nat.primesBelow N, (1 - ((p : ℝ))⁻¹)) ≤
        ∏ p ∈ Nat.primesBelow N, Real.exp (-((p : ℝ))⁻¹) := by
          apply Finset.prod_le_prod
          · intro p hp
            have hprime := Nat.prime_of_mem_primesBelow hp
            have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
            exact sub_nonneg.mpr ((inv_le_one₀ (by positivity)).2 hp1)
          · intro p hp
            exact Real.one_sub_le_exp_neg _
    _ = Real.exp (-∑ p ∈ Nat.primesBelow N, ((p : ℝ))⁻¹) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.sum_neg_distrib]

/-- **Global boundary degeneration.**  The canonical product of all local Wold boundary masses
tends to zero along the prime exhaustion. -/
theorem tendsto_primeWoldBoundaryVolumeBelow_zero :
    Filter.Tendsto primeWoldBoundaryVolumeBelow Filter.atTop (𝓝 0) := by
  have hneg :
      Filter.Tendsto (fun N => -primeReciprocalPartialSum N)
        Filter.atTop Filter.atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_primeReciprocalPartialSum_atTop
  have hexp :
      Filter.Tendsto (fun N => Real.exp (-primeReciprocalPartialSum N))
        Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  exact squeeze_zero'
    (Filter.Eventually.of_forall fun N => primeWoldBoundaryVolumeBelow_nonneg N)
    (Filter.Eventually.of_forall fun N => primeWoldBoundaryVolumeBelow_le_exp N) hexp

/-- Every finite stage has strictly positive boundary volume; degeneration occurs only at the
all-prime boundary. -/
theorem primeWoldBoundaryVolumeBelow_pos (N : ℕ) :
    0 < primeWoldBoundaryVolumeBelow N := by
  exact finitePrimeWoldBoundaryVolume_pos (primesBelowSubtype N)

/-- Reciprocal Wold volume is the canonical cofinal coordinate at the all-prime boundary. -/
def primeWoldBoundaryScale (N : ℕ) : ℝ :=
  (primeWoldBoundaryVolumeBelow N)⁻¹

/-- The reciprocal Wold-volume coordinate tends to infinity. -/
theorem tendsto_primeWoldBoundaryScale_atTop :
    Filter.Tendsto primeWoldBoundaryScale Filter.atTop Filter.atTop := by
  apply tendsto_inv_nhdsGT_zero.comp
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_primeWoldBoundaryVolumeBelow_zero, ?_⟩
  filter_upwards [] with N
  exact primeWoldBoundaryVolumeBelow_pos N

/-- Positive irregular Gamma gauge sampled on the canonical prime boundary coordinate. -/
def primeWoldIrregularGauge (t : ℂ) (N : ℕ) : ℂ :=
  Complex.exp (2 * t * (primeWoldBoundaryScale N : ℂ))

/-- Reflected, negative irregular Gamma gauge on the same source coordinate. -/
def primeWoldReflectedIrregularGauge (t : ℂ) (N : ℕ) : ℂ :=
  Complex.exp (-(2 * t * (primeWoldBoundaryScale N : ℂ)))

/-- The positive irregular gauge has exact real rate `2 Re(t)`. -/
theorem norm_primeWoldIrregularGauge (t : ℂ) (N : ℕ) :
    ‖primeWoldIrregularGauge t N‖ =
      Real.exp (2 * t.re * primeWoldBoundaryScale N) := by
  rw [primeWoldIrregularGauge, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  norm_num

/-- Reflection reverses the exact real exponential rate. -/
theorem norm_primeWoldReflectedIrregularGauge (t : ℂ) (N : ℕ) :
    ‖primeWoldReflectedIrregularGauge t N‖ =
      Real.exp (-2 * t.re * primeWoldBoundaryScale N) := by
  rw [primeWoldReflectedIrregularGauge, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  norm_num

/-- Polynomial moderateness of a rank-one irregular exponential branch.  The quotient formulation
is insensitive to changing the polynomial order by a bounded amount and makes the asymptotic
obstruction exact. -/
def exponentialBranchPolynomiallyModerateAtTop (a : ℝ) : Prop :=
  ∃ n : ℕ, ∃ C : ℝ,
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp (a * x) / x ^ (n : ℝ) ≤ C

/-- An exponential branch is polynomially moderate at infinity exactly when its real exponential
rate is nonpositive. -/
theorem exponentialBranchPolynomiallyModerateAtTop_iff (a : ℝ) :
    exponentialBranchPolynomiallyModerateAtTop a ↔ a ≤ 0 := by
  constructor
  · rintro ⟨n, C, hbound⟩
    by_contra ha
    have ha_pos : 0 < a := lt_of_not_ge ha
    have hdiv :
        Filter.Tendsto
          (fun x : ℝ => Real.exp (a * x) / x ^ (n : ℝ))
          Filter.atTop Filter.atTop :=
      tendsto_exp_mul_div_rpow_atTop (n : ℝ) a ha_pos
    have hgt :
        ∀ᶠ x : ℝ in Filter.atTop,
          C < Real.exp (a * x) / x ^ (n : ℝ) :=
      hdiv.eventually (eventually_gt_atTop C)
    obtain ⟨x, hx_le, hx_gt⟩ := (hbound.and hgt).exists
    exact (not_lt_of_ge hx_le) hx_gt
  · intro ha
    refine ⟨0, 1, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Nat.cast_zero, Real.rpow_zero, div_one]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ha hx)

/-- Reflection exposes the two opposite irregular exponential rates. -/
def reflectedIrregularPairPolynomiallyModerateAtTop (t : ℂ) : Prop :=
  exponentialBranchPolynomiallyModerateAtTop (2 * t.re) ∧
    exponentialBranchPolynomiallyModerateAtTop (-2 * t.re)

/-- **Universal bi-moderate selector.**  Both reflected irregular branches have polynomial growth
exactly on the imaginary axis of the centered parameter. -/
theorem reflectedIrregularPairPolynomiallyModerateAtTop_iff (t : ℂ) :
    reflectedIrregularPairPolynomiallyModerateAtTop t ↔ t.re = 0 := by
  rw [reflectedIrregularPairPolynomiallyModerateAtTop,
    exponentialBranchPolynomiallyModerateAtTop_iff,
    exponentialBranchPolynomiallyModerateAtTop_iff]
  constructor
  · rintro ⟨hpos, hneg⟩
    linarith
  · intro ht
    constructor <;> linarith

/-- In the zeta coordinate `t = s - 1/2`, two-sided polynomial moderateness is exactly the
critical-line equation. -/
theorem centeredReflectedIrregularPairPolynomiallyModerateAtTop_iff (s : ℂ) :
    reflectedIrregularPairPolynomiallyModerateAtTop (s - (1 / 2 : ℂ)) ↔
      s.re = 1 / 2 := by
  rw [reflectedIrregularPairPolynomiallyModerateAtTop_iff]
  rw [Complex.sub_re]
  norm_num
  constructor <;> intro h <;> linarith

/-- Polynomial moderateness sampled on the actual reciprocal prime Wold-volume exhaustion. -/
def exponentialBranchPolynomiallyModerateAlongPrimeBoundary (a : ℝ) : Prop :=
  ∃ n : ℕ, ∃ C : ℝ,
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.exp (a * primeWoldBoundaryScale N) /
        (primeWoldBoundaryScale N) ^ (n : ℝ) ≤ C

/-- Cofinality of the Wold-volume coordinate makes sampled and universal moderateness equivalent. -/
theorem exponentialBranchPolynomiallyModerateAlongPrimeBoundary_iff (a : ℝ) :
    exponentialBranchPolynomiallyModerateAlongPrimeBoundary a ↔ a ≤ 0 := by
  constructor
  · rintro ⟨n, C, hbound⟩
    by_contra ha
    have ha_pos : 0 < a := lt_of_not_ge ha
    have hdiv :
        Filter.Tendsto
          (fun N : ℕ =>
            Real.exp (a * primeWoldBoundaryScale N) /
              (primeWoldBoundaryScale N) ^ (n : ℝ))
          Filter.atTop Filter.atTop :=
      (tendsto_exp_mul_div_rpow_atTop (n : ℝ) a ha_pos).comp
        tendsto_primeWoldBoundaryScale_atTop
    have hgt :
        ∀ᶠ N : ℕ in Filter.atTop,
          C <
            Real.exp (a * primeWoldBoundaryScale N) /
              (primeWoldBoundaryScale N) ^ (n : ℝ) :=
      hdiv.eventually (eventually_gt_atTop C)
    obtain ⟨N, hN_le, hN_gt⟩ := (hbound.and hgt).exists
    exact (not_lt_of_ge hN_le) hN_gt
  · intro ha
    obtain ⟨n, C, hbound⟩ :=
      (exponentialBranchPolynomiallyModerateAtTop_iff a).mpr ha
    exact ⟨n, C, tendsto_primeWoldBoundaryScale_atTop.eventually hbound⟩

/-- The reflected pair sampled by the prime exhaustion. -/
def reflectedIrregularPairPolynomiallyModerateAlongPrimeBoundary (t : ℂ) : Prop :=
  exponentialBranchPolynomiallyModerateAlongPrimeBoundary (2 * t.re) ∧
    exponentialBranchPolynomiallyModerateAlongPrimeBoundary (-2 * t.re)

/-- **Prime-boundary bi-moderate selector.**  The exact global Wold-volume exhaustion retains both
reflected branches precisely for centered parameters on the imaginary axis. -/
theorem reflectedIrregularPairPolynomiallyModerateAlongPrimeBoundary_iff (t : ℂ) :
    reflectedIrregularPairPolynomiallyModerateAlongPrimeBoundary t ↔ t.re = 0 := by
  rw [reflectedIrregularPairPolynomiallyModerateAlongPrimeBoundary,
    exponentialBranchPolynomiallyModerateAlongPrimeBoundary_iff,
    exponentialBranchPolynomiallyModerateAlongPrimeBoundary_iff]
  constructor
  · rintro ⟨hpos, hneg⟩
    linarith
  · intro ht
    constructor <;> linarith

/-- In the original zeta coordinate, the sampled global selector is the critical line. -/
theorem centeredReflectedIrregularPairPolynomiallyModerateAlongPrimeBoundary_iff (s : ℂ) :
    reflectedIrregularPairPolynomiallyModerateAlongPrimeBoundary (s - (1 / 2 : ℂ)) ↔
      s.re = 1 / 2 := by
  rw [reflectedIrregularPairPolynomiallyModerateAlongPrimeBoundary_iff]
  rw [Complex.sub_re]
  norm_num
  constructor <;> intro h <;> linarith

end GaloisForLFunctions
