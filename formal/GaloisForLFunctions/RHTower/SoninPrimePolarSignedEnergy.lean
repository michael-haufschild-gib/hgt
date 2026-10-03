import GaloisForLFunctions.RHTower.SoninCutoffMonomialDilation
import GaloisForLFunctions.RHTower.SoninDilationAverage

/-!
# Full signed prime–polar dilation energy

The original finite prime source and literal logarithmic pole continuum form a
bounded operator on full Sonin L2. Their complete symmetric action on every
actual time-band Taylor output has an exact positive mixed-energy decomposition.
The proof retains complex signs in the general source theorem and proves
integrability for the native source. No cofinal convergence is asserted.
-/

noncomputable section
open MeasureTheory Set
namespace RHTower

private theorem sqrt_exp_half (u : ℝ) : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
  rw [Real.sq_sqrt (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 1
  ring

private theorem log_overlap_of_le (a : ℝ) (n : ℕ) (u v : ℝ) (huv : u ≤ v) :
    inner ℂ (rayDilate (Real.exp u) (soninCutoffMonomial a n))
      (rayDilate (Real.exp v) (soninCutoffMonomial a n)) =
        ((‖soninCutoffMonomial a n‖ ^ 2 * Real.exp (-((n : ℝ) + 1/2) * (v-u)) : ℝ) : ℂ) := by
  rw [rayDilate_of_pos (Real.exp_pos u), rayDilate_of_pos (Real.exp_pos v),
    inner_dilation_soninCutoffMonomial_of_le a n _ _ _ _ (Real.exp_le_exp.mpr huv)]
  congr 1
  rw [sqrt_exp_half, sqrt_exp_half, ← Real.exp_sub, ← Real.exp_sub,
    ← Real.exp_nat_mul, ← Real.exp_add]
  have he : u / 2 - v / 2 + (n : ℝ) * (u-v) = -((n : ℝ) + 1/2) * (v-u) := by ring
  rw [he, mul_comm]

/-- Exact logarithmic covariance of the actual time-band output monomials. -/
theorem inner_logDilation_soninCutoffMonomial (a : ℝ) (n : ℕ) (u v : ℝ) :
    inner ℂ (rayDilate (Real.exp u) (soninCutoffMonomial a n))
      (rayDilate (Real.exp v) (soninCutoffMonomial a n)) =
        ((‖soninCutoffMonomial a n‖ ^ 2 * Real.exp (-((n : ℝ) + 1/2) * |u-v|) : ℝ) : ℂ) := by
  rcases le_total u v with huv | hvu
  · rw [log_overlap_of_le a n u v huv, abs_of_nonpos (sub_nonpos.mpr huv)]
    congr 3; ring
  · rw [← inner_conj_symm, log_overlap_of_le a n v u hvu, Complex.conj_ofReal,
      abs_of_nonneg (sub_nonneg.mpr hvu)]

private theorem inner_integral_left {μ : Measure ℝ} {f : ℝ → SoninL2}
    (hf : Integrable f μ) (y : SoninL2) :
    inner ℂ (∫ u, f u ∂μ) y = ∫ u, inner ℂ (f u) y ∂μ := by
  rw [← inner_conj_symm, ← integral_inner hf, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with u
  exact inner_conj_symm _ _

/-- One direction of a signed source acting on the actual Taylor output.
The sign parameter reverses the logarithmic dilation direction. -/
def soninSignedMonomialSource (a : ℝ) (n : ℕ) (μ : Measure ℝ)
    (w : ℝ → ℂ) (sign : ℝ) : SoninL2 :=
  ∫ u, w u • rayDilate (Real.exp (sign*u)) (soninCutoffMonomial a n) ∂μ

private theorem weighted_orbit_integrable (a : ℝ) (n : ℕ) {μ : Measure ℝ}
    {w : ℝ → ℂ} (hw : Integrable w μ) (sign : ℝ) :
    Integrable (fun u => w u • rayDilate (Real.exp (sign*u)) (soninCutoffMonomial a n)) μ := by
  have hc := (continuous_dilationOrbit (soninCutoffMonomial a n)).comp
    (continuous_const.mul continuous_id : Continuous fun u : ℝ => sign*u)
  apply Integrable.mono' (hw.norm.mul_const ‖soninCutoffMonomial a n‖)
    (hw.aestronglyMeasurable.smul hc.aestronglyMeasurable)
  filter_upwards [] with u
  change ‖w u • rayDilate (Real.exp (sign*u)) (soninCutoffMonomial a n)‖ ≤ _
  rw [norm_smul, norm_rayDilate (Real.exp_pos _)]

private theorem source_inner (a : ℝ) (n : ℕ) {μ : Measure ℝ}
    {w : ℝ → ℂ} (hw : Integrable w μ) (s t : ℝ) :
    inner ℂ (soninSignedMonomialSource a n μ w s) (soninSignedMonomialSource a n μ w t) =
      ∫ u, ∫ v, star (w u) * w v *
        ((‖soninCutoffMonomial a n‖ ^ 2 * Real.exp (-((n : ℝ) + 1/2) * |s*u-t*v|) : ℝ) : ℂ) ∂μ ∂μ := by
  rw [soninSignedMonomialSource, inner_integral_left (weighted_orbit_integrable a n hw s)]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [soninSignedMonomialSource, ← integral_inner (weighted_orbit_integrable a n hw t)]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [inner_smul_left, inner_smul_right, inner_logDilation_soninCutoffMonomial]
  simp only [starRingEnd_apply]
  ring

/-- The two directions of every integrable complex signed source have the
same full energy on an actual time-band Taylor output. -/
theorem norm_sq_soninSignedMonomialSource_neg (a : ℝ) (n : ℕ) {μ : Measure ℝ}
    {w : ℝ → ℂ} (hw : Integrable w μ) :
    ‖soninSignedMonomialSource a n μ w (-1)‖ ^ 2 =
      ‖soninSignedMonomialSource a n μ w 1‖ ^ 2 := by
  have h : inner ℂ (soninSignedMonomialSource a n μ w (-1))
      (soninSignedMonomialSource a n μ w (-1)) =
      inner ℂ (soninSignedMonomialSource a n μ w 1)
        (soninSignedMonomialSource a n μ w 1) := by
    rw [source_inner a n hw, source_inner a n hw]
    apply integral_congr_ae
    filter_upwards [] with u
    apply integral_congr_ae
    filter_upwards [] with v
    have he : (-1 : ℝ)*u-(-1)*v = -(u-v) := by ring
    rw [he, abs_neg, one_mul, one_mul]
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- The exact decaying source moment that survives opposite dilation directions. -/
def soninSignedMonomialMoment (n : ℕ) (μ : Measure ℝ) (w : ℝ → ℂ) : ℂ :=
  ∫ u, w u * (Real.exp (-((n : ℝ) + 1/2) * u) : ℂ) ∂μ

/-- Opposite directions have a nonnegative, exactly factored mixed energy,
even when the original source has complex signs. -/
theorem inner_soninSignedMonomialSource_opposite (a : ℝ) (n : ℕ) {μ : Measure ℝ}
    {w : ℝ → ℂ} (hw : Integrable w μ) (hpos : ∀ᵐ u ∂μ, 0 ≤ u) :
    inner ℂ (soninSignedMonomialSource a n μ w 1) (soninSignedMonomialSource a n μ w (-1)) =
      ((‖soninCutoffMonomial a n‖ ^ 2 * ‖soninSignedMonomialMoment n μ w‖ ^ 2 : ℝ) : ℂ) := by
  let c : ℝ := ‖soninCutoffMonomial a n‖ ^ 2
  let e : ℝ → ℂ := fun u => (Real.exp (-((n : ℝ) + 1/2) * u) : ℂ)
  have hkernel (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      star (w u) * w v * ((c * Real.exp (-((n : ℝ) + 1/2) * |1*u-(-1)*v|) : ℝ) : ℂ) =
        (c : ℂ) * star (w u * e u) * (w v * e v) := by
    have habs : |(1 : ℝ)*u-(-1)*v| = u+v := by
      rw [one_mul, neg_one_mul, sub_neg_eq_add, abs_of_nonneg (add_nonneg hu hv)]
    have he : Real.exp (-((n : ℝ) + 1/2) * (u+v)) =
        Real.exp (-((n : ℝ) + 1/2) * u) * Real.exp (-((n : ℝ) + 1/2) * v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [habs, he]
    simp only [e, Complex.ofReal_mul, map_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [source_inner a n hw]
  calc
    _ = ∫ u, ∫ v, (c : ℂ) * star (w u * e u) * (w v * e v) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hpos] with u hu
      apply integral_congr_ae
      filter_upwards [hpos] with v hv
      exact hkernel u v hu hv
    _ = (c : ℂ) * star (∫ u, w u * e u ∂μ) * (∫ u, w u * e u ∂μ) := by
      simp only [integral_const_mul, integral_mul_const, Complex.star_def, integral_conj]
    _ = _ := by
      rw [mul_assoc, mul_comm (star _) _, Complex.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
      rfl

/-- Full signed source energy retains a positive mixed term. It is not an
absolute majorant and does not discard the contracting or expanding leg. -/
theorem norm_sq_soninSignedMonomialSource_symmetric (a : ℝ) (n : ℕ) {μ : Measure ℝ}
    {w : ℝ → ℂ} (hw : Integrable w μ) (hpos : ∀ᵐ u ∂μ, 0 ≤ u) :
    ‖soninSignedMonomialSource a n μ w 1 + soninSignedMonomialSource a n μ w (-1)‖ ^ 2 =
      2 * ‖soninSignedMonomialSource a n μ w 1‖ ^ 2 +
        2 * ‖soninCutoffMonomial a n‖ ^ 2 * ‖soninSignedMonomialMoment n μ w‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), norm_sq_soninSignedMonomialSource_neg a n hw,
    inner_soninSignedMonomialSource_opposite a n hw hpos]
  change _ + 2 * (‖soninCutoffMonomial a n‖ ^ 2 * ‖soninSignedMonomialMoment n μ w‖ ^ 2) + _ = _
  ring

/-- The native logarithmic pole density, away from its lower endpoint. -/
def soninLogPolarDensity (u : ℝ) : ℂ := (2 * Real.cosh (u/2) / u : ℝ)

/-- Actual finite prime minus polar source on a Taylor output, with either
normalized dilation direction. No limiting admission is part of this definition. -/
def soninPrimePolarMonomialSource (a : ℝ) (n : ℕ) (P : Finset Nat.Primes)
    (b R sign : ℝ) : SoninL2 :=
  (∑ p ∈ P, ((Real.sqrt (p : ℝ))⁻¹ : ℂ) •
    rayDilate (Real.exp (sign * Real.log (p : ℝ))) (soninCutoffMonomial a n)) -
  ∫ u in Icc b R, soninLogPolarDensity u •
    rayDilate (Real.exp (sign*u)) (soninCutoffMonomial a n)

/-- The literal mixed moment; the same pole density and prime coefficients
are used as in the operator source. -/
def soninPrimePolarMonomialMoment (n : ℕ) (P : Finset Nat.Primes) (b R : ℝ) : ℂ :=
  (∑ p ∈ P, ((Real.sqrt (p : ℝ))⁻¹ : ℂ) *
    (Real.exp (-((n : ℝ) + 1/2) * Real.log (p : ℝ)) : ℂ)) -
  ∫ u in Icc b R, soninLogPolarDensity u * (Real.exp (-((n : ℝ) + 1/2) * u) : ℂ)

private def primeLogPoints (P : Finset Nat.Primes) : Finset ℝ := by
  classical
  exact P.image (fun p : Nat.Primes => Real.log (p : ℝ))

private def sourceMeasure (P : Finset Nat.Primes) (b R : ℝ) : Measure ℝ :=
  (∑ p ∈ P, Measure.dirac (Real.log (p : ℝ))) + volume.restrict (Icc b R)

private def sourceWeight (P : Finset Nat.Primes) (u : ℝ) : ℂ := by
  classical
  exact if u ∈ primeLogPoints P then ((Real.sqrt (Real.exp u))⁻¹ : ℂ)
    else -soninLogPolarDensity u

private theorem sourceWeight_at_prime (P : Finset Nat.Primes) {p : Nat.Primes}
    (hp : p ∈ P) : sourceWeight P (Real.log (p : ℝ)) = ((Real.sqrt (p : ℝ))⁻¹ : ℂ) := by
  classical
  have hmem : Real.log (p : ℝ) ∈ primeLogPoints P := by
    change Real.log (p : ℝ) ∈ P.image (fun q : Nat.Primes => Real.log (q : ℝ))
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  simp only [sourceWeight, if_pos hmem,
    Real.exp_log (by exact_mod_cast p.prop.pos : 0 < (p : ℝ))]

private theorem sourceWeight_ae_polar (P : Finset Nat.Primes) (b R : ℝ) :
    sourceWeight P =ᵐ[volume.restrict (Icc b R)] fun u => -soninLogPolarDensity u := by
  classical
  filter_upwards [(primeLogPoints P).finite_toSet.countable.ae_notMem
    (volume.restrict (Icc b R))] with u hu
  exact if_neg hu

private theorem polar_density_continuousOn (b R : ℝ) (hb : 0 < b) :
    ContinuousOn soninLogPolarDensity (Icc b R) := by
  apply Complex.continuous_ofReal.continuousOn.comp
    ((continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).continuousOn.div
      continuous_id.continuousOn (fun u hu => (hb.trans_le hu.1).ne'))
    (fun _ _ => Set.mem_univ _)

private theorem sourceWeight_integrable (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) :
    Integrable (sourceWeight P) (sourceMeasure P b R) := by
  rw [sourceMeasure, integrable_add_measure]
  constructor
  · apply integrable_finsetSum_measure.mpr
    intro p hp
    exact integrable_dirac (by simp)
  · exact ((polar_density_continuousOn b R hb).integrableOn_Icc.neg).congr
      (sourceWeight_ae_polar P b R).symm

private theorem sourceMeasure_nonneg (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) :
    ∀ᵐ u ∂(sourceMeasure P b R), 0 ≤ u := by
  rw [sourceMeasure, ae_add_measure_iff]
  constructor
  · rw [ae_finsetSum_measure_iff]
    intro p hp
    simp only [ae_dirac_eq, Filter.eventually_pure]
    apply Real.log_nonneg
    exact_mod_cast p.prop.one_lt.le
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hb.le.trans hu.1

private theorem native_source_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b)
    (F : ℝ → E) (hF : Continuous F) :
    (∫ u, sourceWeight P u • F u ∂(sourceMeasure P b R)) =
      (∑ p ∈ P, ((Real.sqrt (p : ℝ))⁻¹ : ℂ) • F (Real.log (p : ℝ))) -
        ∫ u in Icc b R, soninLogPolarDensity u • F u := by
  have hpol : Integrable (fun u => soninLogPolarDensity u • F u)
      (volume.restrict (Icc b R)) :=
    ((polar_density_continuousOn b R hb).smul hF.continuousOn).integrableOn_Icc
  have hae : (fun u => sourceWeight P u • F u) =ᵐ[volume.restrict (Icc b R)]
      fun u => -(soninLogPolarDensity u • F u) := by
    filter_upwards [sourceWeight_ae_polar P b R] with u hu
    rw [hu, neg_smul]
  have hat : ∀ p ∈ P, Integrable (fun u => sourceWeight P u • F u)
      (Measure.dirac (Real.log (p : ℝ))) := fun _ _ => integrable_dirac (by simp)
  rw [sourceMeasure, integral_add_measure (integrable_finsetSum_measure.mpr hat)
    (hpol.neg.congr hae.symm), integral_finsetSum_measure hat,
    integral_congr_ae hae, integral_neg, sub_eq_add_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_dirac, sourceWeight_at_prime P hp]

private theorem native_source_eq (a : ℝ) (n : ℕ) (P : Finset Nat.Primes)
    (b R sign : ℝ) (hb : 0 < b) :
    soninSignedMonomialSource a n (sourceMeasure P b R) (sourceWeight P) sign =
      soninPrimePolarMonomialSource a n P b R sign := by
  exact native_source_integral P b R hb _
    ((continuous_dilationOrbit (soninCutoffMonomial a n)).comp
      (continuous_const.mul continuous_id))

private theorem native_moment_eq (n : ℕ) (P : Finset Nat.Primes)
    (b R : ℝ) (hb : 0 < b) :
    soninSignedMonomialMoment n (sourceMeasure P b R) (sourceWeight P) =
      soninPrimePolarMonomialMoment n P b R := by
  exact native_source_integral P b R hb _ (by fun_prop)

/-- Exact full prime–polar energy, with the native continuum and both actual
dilation directions. Integrability is proved from the source, not assumed. -/
theorem norm_sq_soninPrimePolarMonomialSource_symmetric (a : ℝ) (n : ℕ)
    (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) :
    ‖soninPrimePolarMonomialSource a n P b R 1 +
        soninPrimePolarMonomialSource a n P b R (-1)‖ ^ 2 =
      2 * ‖soninPrimePolarMonomialSource a n P b R 1‖ ^ 2 +
        2 * ‖soninCutoffMonomial a n‖ ^ 2 * ‖soninPrimePolarMonomialMoment n P b R‖ ^ 2 := by
  simpa only [native_source_eq a n P b R 1 hb, native_source_eq a n P b R (-1) hb,
    native_moment_eq n P b R hb] using
    norm_sq_soninSignedMonomialSource_symmetric a n
      (sourceWeight_integrable P b R hb) (sourceMeasure_nonneg P b R hb)

private theorem polar_orbit_integrable (b R sign : ℝ) (hb : 0 < b) (f : SoninL2) :
    Integrable (fun u => soninLogPolarDensity u • rayDilate (Real.exp (sign*u)) f)
      (volume.restrict (Icc b R)) :=
  ((polar_density_continuousOn b R hb).smul
    ((continuous_dilationOrbit f).comp (continuous_const.mul continuous_id)).continuousOn).integrableOn_Icc

private def polarSourceOperator (b R sign : ℝ) (hb : 0 < b) : SoninL2 →L[ℂ] SoninL2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ u in Icc b R,
        soninLogPolarDensity u • rayDilate (Real.exp (sign*u)) f
      map_add' := by
        intro f g
        rw [← integral_add (polar_orbit_integrable b R sign hb f)
          (polar_orbit_integrable b R sign hb g)]
        apply integral_congr_ae
        filter_upwards [] with u
        rw [rayDilate_of_pos (Real.exp_pos _), rayDilate_of_pos (Real.exp_pos _),
          rayDilate_of_pos (Real.exp_pos _), map_add, smul_add]
      map_smul' := by
        intro c f
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [] with u
        simp only [rayDilate_of_pos (Real.exp_pos _), map_smul, smul_smul,
          RingHom.id_apply]
        rw [mul_comm] }
    (∫ u in Icc b R, ‖soninLogPolarDensity u‖) (fun f => by
      calc
        _ ≤ ∫ u in Icc b R, ‖soninLogPolarDensity u • rayDilate (Real.exp (sign*u)) f‖ :=
          norm_integral_le_integral_norm _
        _ = ∫ u in Icc b R, ‖soninLogPolarDensity u‖ * ‖f‖ := by
          apply integral_congr_ae
          filter_upwards [] with u
          rw [norm_smul, norm_rayDilate (Real.exp_pos _)]
        _ = _ := integral_mul_const _ _)

/-- Bounded original finite prime–polar source on full physical L2.
The continuum is the strong integral of normalized dilations with its literal density. -/
def soninPrimePolarSourceOperator (P : Finset Nat.Primes) (b R sign : ℝ)
    (hb : 0 < b) : SoninL2 →L[ℂ] SoninL2 :=
  (∑ p ∈ P, ((Real.sqrt (p : ℝ))⁻¹ : ℂ) •
    dilationCLM (Real.exp (sign * Real.log (p : ℝ))) (Real.exp_pos _)) -
  polarSourceOperator b R sign hb

/-- The original prime and continuum formula on every full physical vector. -/
theorem soninPrimePolarSourceOperator_apply (P : Finset Nat.Primes) (b R sign : ℝ)
    (hb : 0 < b) (f : SoninL2) :
    soninPrimePolarSourceOperator P b R sign hb f =
      (∑ p ∈ P, ((Real.sqrt (p : ℝ))⁻¹ : ℂ) •
        rayDilate (Real.exp (sign * Real.log (p : ℝ))) f) -
      ∫ u in Icc b R, soninLogPolarDensity u • rayDilate (Real.exp (sign*u)) f := by
  simp only [soninPrimePolarSourceOperator, sub_apply, sum_apply, smul_apply,
    dilationCLM_apply, polarSourceOperator, LinearMap.mkContinuous_apply,
    rayDilate_of_pos (Real.exp_pos _)]
  rfl

/-- Exact source provenance of every Taylor column used in the nuclear expansion. -/
theorem soninPrimePolarSourceOperator_apply_monomial (a : ℝ) (n : ℕ)
    (P : Finset Nat.Primes) (b R sign : ℝ) (hb : 0 < b) :
    soninPrimePolarSourceOperator P b R sign hb (soninCutoffMonomial a n) =
      soninPrimePolarMonomialSource a n P b R sign := by
  simp only [soninPrimePolarSourceOperator, sub_apply,
    sum_apply, smul_apply, dilationCLM_apply,
    soninPrimePolarMonomialSource, polarSourceOperator, LinearMap.mkContinuous_apply,
    rayDilate_of_pos (Real.exp_pos _)]
  rfl

/-- The native full operator has exactly the signed energy, including its
nonnegative mixed prime–polar term; no convergence premise is present. -/
theorem norm_sq_soninPrimePolarSourceOperator_symmetric (a : ℝ) (n : ℕ)
    (P : Finset Nat.Primes) (b R : ℝ) (hb : 0 < b) :
    ‖(soninPrimePolarSourceOperator P b R 1 hb + soninPrimePolarSourceOperator P b R (-1) hb)
        (soninCutoffMonomial a n)‖ ^ 2 =
      2 * ‖soninPrimePolarSourceOperator P b R 1 hb (soninCutoffMonomial a n)‖ ^ 2 +
        2 * ‖soninCutoffMonomial a n‖ ^ 2 * ‖soninPrimePolarMonomialMoment n P b R‖ ^ 2 := by
  rw [add_apply, soninPrimePolarSourceOperator_apply_monomial,
    soninPrimePolarSourceOperator_apply_monomial,
    norm_sq_soninPrimePolarMonomialSource_symmetric a n P b R hb]

end RHTower
