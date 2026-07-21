import GaloisForLFunctions.RHTower.RealCharacterDenseL2
import GaloisForLFunctions.HTGeometry.EntireIdentityTheorem
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Polynomial density from an entire exponential-moment window

This file proves the analytic density input needed by the Gaussian-window moment-cone law.  If a
finite Borel measure on `ℝ` has a bilateral moment-generating function on the whole real axis, then
real polynomials are dense in its real `L²` space.

The proof is deliberately intrinsic.  An `L²` vector orthogonal to every monomial defines its
positive and negative density measures.  Hölder transfers the exponential moments of the base
measure to both density measures.  Their complex moment-generating functions are therefore entire,
and equality of every polynomial moment makes their difference flat at the origin.  The entire
identity theorem and uniqueness of complex moment-generating functions identify the measures;
mutual singularity of positive and negative parts then forces the vector to vanish.

This is stronger than the Gaussian instance: the only hypothesis is the exact all-direction
exponential-moment law `integrableExpSet id μ = Set.univ`.
-/

noncomputable section

open Complex MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace RHTower

/-- A finite real measure has an entire bilateral moment-generating window when every real
exponential is integrable. -/
def HasEntireExponentialMoments (mu : Measure ℝ) : Prop :=
  integrableExpSet id mu = Set.univ

/-- Every real exponential belongs to `L²` when the measure has an entire exponential-moment
window. -/
theorem exp_mul_memLp_two_of_entireExponentialMoments
    {mu : Measure ℝ} (hmu : HasEntireExponentialMoments mu) (t : ℝ) :
    MemLp (fun x : ℝ => Real.exp (t * x)) 2 mu := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have hmem : (2 * t) ∈ integrableExpSet id mu := by
    rw [hmu]
    exact Set.mem_univ _
  have hint := integrable_of_mem_integrableExpSet hmem
  convert hint using 1
  funext x
  rw [pow_two, ← Real.exp_add]
  congr 1
  simp only [id_eq]
  ring

/-- Every monomial belongs to `L²` under an entire exponential-moment window. -/
theorem monomial_memLp_two_of_entireExponentialMoments
    {mu : Measure ℝ} (hmu : HasEntireExponentialMoments mu) (n : ℕ) :
    MemLp (fun x : ℝ => x ^ n) 2 mu := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have hzero : 0 ∈ interior (integrableExpSet id mu) := by
    rw [hmu]
    simp
  have hint := integrable_pow_of_mem_interior_integrableExpSet hzero (2 * n)
  convert hint using 1
  funext x
  simp only [id_eq]
  rw [pow_two, ← pow_add]
  congr 1
  omega

/-- The `n`th real monomial as an element of `L²(mu)`. -/
def realMonomialLp (mu : Measure ℝ) (hmu : HasEntireExponentialMoments mu) (n : ℕ) :
    Lp ℝ 2 mu :=
  (monomial_memLp_two_of_entireExponentialMoments hmu n).toLp (fun x : ℝ => x ^ n)

theorem realMonomialLp_ae (mu : Measure ℝ) (hmu : HasEntireExponentialMoments mu) (n : ℕ) :
    realMonomialLp mu hmu n =ᵐ[mu] fun x : ℝ => x ^ n :=
  (monomial_memLp_two_of_entireExponentialMoments hmu n).coeFn_toLp

/-- The positive density measure of a real function relative to a base measure. -/
def positiveDensityMeasure (mu : Measure ℝ) (g : ℝ → ℝ) : Measure ℝ :=
  mu.withDensity fun x => ENNReal.ofReal (g x)

/-- The negative density measure of a real function relative to a base measure. -/
def negativeDensityMeasure (mu : Measure ℝ) (g : ℝ → ℝ) : Measure ℝ :=
  mu.withDensity fun x => ENNReal.ofReal (-g x)

theorem positiveDensityMeasure_finite {mu : Measure ℝ} [IsFiniteMeasure mu]
    {g : ℝ → ℝ} (hg : Integrable g mu) :
    IsFiniteMeasure (positiveDensityMeasure mu g) := by
  unfold positiveDensityMeasure
  exact isFiniteMeasure_withDensity_ofReal hg.hasFiniteIntegral

theorem negativeDensityMeasure_finite {mu : Measure ℝ} [IsFiniteMeasure mu]
    {g : ℝ → ℝ} (hg : Integrable g mu) :
    IsFiniteMeasure (negativeDensityMeasure mu g) := by
  unfold negativeDensityMeasure
  exact isFiniteMeasure_withDensity_ofReal hg.neg.hasFiniteIntegral

/-- Hölder transfers the full exponential window to the positive density measure of an `L²`
function. -/
theorem positiveDensityMeasure_hasEntireExponentialMoments
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hmu : HasEntireExponentialMoments mu)
    {g : ℝ → ℝ} (hgmeas : Measurable g) (hg : MemLp g 2 mu) :
    HasEntireExponentialMoments (positiveDensityMeasure mu g) := by
  apply Set.eq_univ_of_forall
  intro t
  change Integrable (fun x : ℝ => Real.exp (t * x)) (positiveDensityMeasure mu g)
  unfold positiveDensityMeasure
  rw [integrable_withDensity_iff_integrable_smul₀'
    hgmeas.ennreal_ofReal.aemeasurable (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal']
  have hprod : MemLp (fun x : ℝ => Real.exp (t * x) * max (g x) 0) 1 mu :=
    hg.pos_part.mul' (exp_mul_memLp_two_of_entireExponentialMoments hmu t)
  have hint : Integrable (fun x : ℝ => Real.exp (t * x) * max (g x) 0) mu :=
    memLp_one_iff_integrable.mp hprod
  simpa [smul_eq_mul, mul_comm] using hint

/-- Hölder transfers the full exponential window to the negative density measure of an `L²`
function. -/
theorem negativeDensityMeasure_hasEntireExponentialMoments
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hmu : HasEntireExponentialMoments mu)
    {g : ℝ → ℝ} (hgmeas : Measurable g) (hg : MemLp g 2 mu) :
    HasEntireExponentialMoments (negativeDensityMeasure mu g) := by
  apply Set.eq_univ_of_forall
  intro t
  change Integrable (fun x : ℝ => Real.exp (t * x)) (negativeDensityMeasure mu g)
  unfold negativeDensityMeasure
  rw [integrable_withDensity_iff_integrable_smul₀'
    hgmeas.neg.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal']
  have hprod : MemLp (fun x : ℝ => Real.exp (t * x) * max (-g x) 0) 1 mu :=
    hg.neg_part.mul' (exp_mul_memLp_two_of_entireExponentialMoments hmu t)
  have hint : Integrable (fun x : ℝ => Real.exp (t * x) * max (-g x) 0) mu :=
    memLp_one_iff_integrable.mp hprod
  simpa [smul_eq_mul, mul_comm] using hint

/-- The positive and negative density measures integrate every monomial. -/
theorem integrable_pow_positiveDensityMeasure
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hmu : HasEntireExponentialMoments mu)
    {g : ℝ → ℝ} (hgmeas : Measurable g) (hg : MemLp g 2 mu) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (positiveDensityMeasure mu g) := by
  have hwindow := positiveDensityMeasure_hasEntireExponentialMoments hmu hgmeas hg
  have hzero : 0 ∈ interior (integrableExpSet id (positiveDensityMeasure mu g)) := by
    rw [hwindow]
    simp
  simpa only [id_eq] using integrable_pow_of_mem_interior_integrableExpSet hzero n

theorem integrable_pow_negativeDensityMeasure
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hmu : HasEntireExponentialMoments mu)
    {g : ℝ → ℝ} (hgmeas : Measurable g) (hg : MemLp g 2 mu) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (negativeDensityMeasure mu g) := by
  have hwindow := negativeDensityMeasure_hasEntireExponentialMoments hmu hgmeas hg
  have hzero : 0 ∈ interior (integrableExpSet id (negativeDensityMeasure mu g)) := by
    rw [hwindow]
    simp
  simpa only [id_eq] using integrable_pow_of_mem_interior_integrableExpSet hzero n

/-- Vanishing weighted moments identify the positive and negative density measures. -/
theorem positiveDensityMeasure_eq_negativeDensityMeasure_of_moments_zero
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hmu : HasEntireExponentialMoments mu)
    {g : ℝ → ℝ} (hgmeas : Measurable g) (hg : MemLp g 2 mu)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n * g x ∂mu = 0) :
    positiveDensityMeasure mu g = negativeDensityMeasure mu g := by
  have hg1 : Integrable g mu :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (by norm_num))
  letI : IsFiniteMeasure (positiveDensityMeasure mu g) := positiveDensityMeasure_finite hg1
  letI : IsFiniteMeasure (negativeDensityMeasure mu g) := negativeDensityMeasure_finite hg1
  have hposWindow := positiveDensityMeasure_hasEntireExponentialMoments hmu hgmeas hg
  have hnegWindow := negativeDensityMeasure_hasEntireExponentialMoments hmu hgmeas hg
  change integrableExpSet id (positiveDensityMeasure mu g) = Set.univ at hposWindow
  change integrableExpSet id (negativeDensityMeasure mu g) = Set.univ at hnegWindow
  have hposAnalytic : AnalyticOnNhd ℂ
      (complexMGF id (positiveDensityMeasure mu g)) Set.univ := by
    simpa [hposWindow] using
      (analyticOnNhd_complexMGF (X := id) (μ := positiveDensityMeasure mu g))
  have hnegAnalytic : AnalyticOnNhd ℂ
      (complexMGF id (negativeDensityMeasure mu g)) Set.univ := by
    simpa [hnegWindow] using
      (analyticOnNhd_complexMGF (X := id) (μ := negativeDensityMeasure mu g))
  have hmeasureMoment (n : ℕ) :
      ∫ x, x ^ n ∂positiveDensityMeasure mu g =
        ∫ x, x ^ n ∂negativeDensityMeasure mu g := by
    have hpow := monomial_memLp_two_of_entireExponentialMoments hmu n
    have hposLp : MemLp (fun x : ℝ => x ^ n * max (g x) 0) 1 mu :=
      hg.pos_part.mul' hpow
    have hnegLp : MemLp (fun x : ℝ => x ^ n * max (-g x) 0) 1 mu :=
      hg.neg_part.mul' hpow
    have hposInt : Integrable (fun x : ℝ => x ^ n * max (g x) 0) mu :=
      memLp_one_iff_integrable.mp hposLp
    have hnegInt : Integrable (fun x : ℝ => x ^ n * max (-g x) 0) mu :=
      memLp_one_iff_integrable.mp hnegLp
    have hsplit : (fun x : ℝ => x ^ n * g x) =
        fun x => x ^ n * max (g x) 0 - x ^ n * max (-g x) 0 := by
      funext x
      rw [← mul_sub]
      congr 1
      exact (max_zero_sub_max_neg_zero_eq_self (g x)).symm
    have heq : ∫ x, x ^ n * max (g x) 0 ∂mu =
        ∫ x, x ^ n * max (-g x) 0 ∂mu := by
      have hz := hmom n
      rw [hsplit, integral_sub hposInt hnegInt] at hz
      exact sub_eq_zero.mp hz
    unfold positiveDensityMeasure negativeDensityMeasure
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hgmeas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hgmeas.neg.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal']
    simpa [smul_eq_mul, mul_comm] using heq
  have hflat : ∀ n : ℕ, iteratedDeriv n
      (complexMGF id (positiveDensityMeasure mu g) -
        complexMGF id (negativeDensityMeasure mu g)) 0 = 0 := by
    intro n
    rw [iteratedDeriv_sub
      (hposAnalytic 0 (Set.mem_univ 0)).contDiffAt
      (hnegAnalytic 0 (Set.mem_univ 0)).contDiffAt]
    rw [iteratedDeriv_complexMGF (by rw [hposWindow]; simp) n]
    rw [iteratedDeriv_complexMGF (by rw [hnegWindow]; simp) n]
    simp only [id_eq, zero_mul, exp_zero, mul_one]
    have heq := hmeasureMoment n
    exact sub_eq_zero.mpr (by exact_mod_cast heq)
  have hdiff : Differentiable ℂ
      (complexMGF id (positiveDensityMeasure mu g) -
        complexMGF id (negativeDensityMeasure mu g)) := by
    intro z
    exact (hposAnalytic z (Set.mem_univ z)).differentiableAt.sub
      (hnegAnalytic z (Set.mem_univ z)).differentiableAt
  have hzero := GaloisForLFunctions.entire_eq_zero_of_forall_iteratedDeriv_zero hdiff hflat
  have hmgf : complexMGF id (positiveDensityMeasure mu g) =
      complexMGF id (negativeDensityMeasure mu g) := by
    funext z
    have hz := congrFun hzero z
    exact sub_eq_zero.mp (by simpa using hz)
  exact Measure.ext_of_complexMGF_id_eq hmgf

/-- **All-moment rigidity.** Under an entire exponential-moment window, an `L²` density whose
polynomial moments all vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_all_moments_of_entireExponentialMoments
    {mu : Measure ℝ} [IsFiniteMeasure mu] (hmu : HasEntireExponentialMoments mu)
    {g : ℝ → ℝ} (hgmeas : Measurable g) (hg : MemLp g 2 mu)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n * g x ∂mu = 0) :
    g =ᵐ[mu] 0 := by
  have hg1 : Integrable g mu :=
    memLp_one_iff_integrable.mp (hg.mono_exponent (by norm_num))
  let mup := positiveDensityMeasure mu g
  let mun := negativeDensityMeasure mu g
  letI : IsFiniteMeasure mup := positiveDensityMeasure_finite hg1
  letI : IsFiniteMeasure mun := negativeDensityMeasure_finite hg1
  have heq : mup = mun := by
    simpa only [mup, mun] using
      positiveDensityMeasure_eq_negativeDensityMeasure_of_moments_zero hmu hgmeas hg hmom
  have hsing : mup ⟂ₘ mun := by
    simpa only [mup, mun, positiveDensityMeasure, negativeDensityMeasure] using
      withDensity_ofReal_mutuallySingular hgmeas
  have hself : mup ⟂ₘ mup := by simpa [heq] using hsing
  have hmup : mup = 0 := by
    have hdisjoint := hself.disjoint
    simpa using hdisjoint
  have hmun : mun = 0 := by rw [← heq, hmup]
  have hpzero : (fun x => ENNReal.ofReal (g x)) =ᵐ[mu] (fun _ => 0) :=
    (withDensity_eq_zero_iff hgmeas.ennreal_ofReal.aemeasurable).mp (by
      simpa only [mup, positiveDensityMeasure] using hmup)
  have hnzero : (fun x => ENNReal.ofReal (-g x)) =ᵐ[mu] (fun _ => 0) :=
    (withDensity_eq_zero_iff hgmeas.neg.ennreal_ofReal.aemeasurable).mp (by
      simpa only [mun, negativeDensityMeasure] using hmun)
  filter_upwards [hpzero, hnzero] with x hpx hnx
  have hle : g x ≤ 0 := by simpa using hpx
  have hge : 0 ≤ g x := by simpa using hnx
  exact le_antisymm hle hge

/-- The real algebraic span of monomials in `L²(mu)`. -/
def realMonomialSpan (mu : Measure ℝ) (hmu : HasEntireExponentialMoments mu) :
    Submodule ℝ (Lp ℝ 2 mu) :=
  Submodule.span ℝ (Set.range (realMonomialLp mu hmu))

/-- **Polynomial density theorem.** A finite real measure with a bilateral moment-generating
function on the whole real axis has dense real polynomial span in `L²`. -/
theorem realMonomialSpan_closure_eq_top
    (mu : Measure ℝ) [IsFiniteMeasure mu] (hmu : HasEntireExponentialMoments mu) :
    (realMonomialSpan mu hmu).topologicalClosure = ⊤ := by
  have horth : (realMonomialSpan mu hmu)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hmom : ∀ n : ℕ, ∫ x, x ^ n * y x ∂mu = 0 := by
      intro n
      have hn := hy (realMonomialLp mu hmu n)
        (Submodule.subset_span (Set.mem_range_self n))
      rw [L2.inner_def] at hn
      have hpoint : (fun x : ℝ => inner ℝ (realMonomialLp mu hmu n x) (y x)) =ᵐ[mu]
          fun x => x ^ n * y x := by
        filter_upwards [realMonomialLp_ae mu hmu n] with x hx
        rw [hx]
        rw [RCLike.inner_apply]
        change y x * x ^ n = x ^ n * y x
        ring
      rw [integral_congr_ae hpoint] at hn
      exact hn
    have hyzero := ae_eq_zero_of_all_moments_of_entireExponentialMoments hmu
      (Lp.stronglyMeasurable y).measurable (Lp.memLp y) hmom
    apply Lp.ext
    filter_upwards [hyzero, Lp.coeFn_zero ℝ 2 mu] with x hx hzero
    exact hx.trans hzero.symm
  calc
    (realMonomialSpan mu hmu).topologicalClosure = (realMonomialSpan mu hmu)ᗮᗮ :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = (⊥ : Submodule ℝ (Lp ℝ 2 mu))ᗮ := by rw [horth]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

end RHTower
