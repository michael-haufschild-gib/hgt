import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelFiniteModeObservability
import Mathlib.MeasureTheory.Function.L2Space

open Complex Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal

attribute [local instance] Measure.Subtype.measureSpace

namespace RHTower

noncomputable section

/-!
# Countable `L²` dominance for physical theta--Abel apertures

The scalar dominant-packet theorem is lifted to Hilbert-valued coefficients and then instantiated
with literal theta--Abel aperture profiles. This identifies the exact countable-tail escapes left
after finite-mode observability: failure of norm summability, failure of finite isolated rightmost
spectral support, or cancellation of the maximal phase-fiber vector.
-/

/-- Sum of vector coefficients in one mode fiber. -/
def finiteExponentialVectorFiberCoefficient
    {ι E : Type*} [AddCommMonoid E] (s : Finset ι)
    (c : ι → E) (z : ι → ℂ) (u : ℂ) : E :=
  ∑ i ∈ s with z i = u, c i

theorem finiteExponentialFiberCoefficient_innerSL
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (c : ι → E) (z : ι → ℂ) (u : ℂ) (v : E) :
    finiteExponentialFiberCoefficient s (fun i => (innerSL ℂ v) (c i)) z u =
      (innerSL ℂ v) (finiteExponentialVectorFiberCoefficient s c z u) := by
  classical
  simp only [finiteExponentialFiberCoefficient, finiteExponentialVectorFiberCoefficient,
    map_sum]

/-- A norm-summable Hilbert-valued pencil cannot hide a finite isolated dominant packet whose
aggregate vector in one phase fiber is nonzero. -/
theorem not_tendsto_tsum_normalizedExponentialPencil_vector_zero_of_dominantFinset
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (c : ι → E) (b : ι → ℂ) (hc : Summable (fun i => ‖c i‖))
    (D : Finset ι) {r : ℝ} (hr : 0 < r)
    (hdom : ∀ i ∈ D, ‖b i‖ = r)
    (hsub : ∀ i ∉ D, ‖b i‖ < r)
    (hfiber : ∃ u ∈ D.image (fun i => b i / (r : ℂ)),
      finiteExponentialVectorFiberCoefficient D c
        (fun i => b i / (r : ℂ)) u ≠ 0) :
    ¬ Tendsto
      (fun n : ℕ => ∑' i : ι, (b i / (r : ℂ)) ^ n • c i)
      atTop (nhds 0) := by
  classical
  obtain ⟨u, hu, hV⟩ := hfiber
  let V := finiteExponentialVectorFiberCoefficient D c
    (fun i => b i / (r : ℂ)) u
  let L : E →L[ℂ] ℂ := innerSL ℂ V
  have hcL : Summable (fun i => L (c i)) := by
    exact (hc.of_norm.map L L.continuous).congr (fun i => rfl)
  have hfiberL : ∃ w ∈ D.image (fun i => b i / (r : ℂ)),
      finiteExponentialFiberCoefficient D (fun i => L (c i))
        (fun i => b i / (r : ℂ)) w ≠ 0 := by
    refine ⟨u, hu, ?_⟩
    rw [finiteExponentialFiberCoefficient_innerSL]
    change inner ℂ V V ≠ 0
    rw [inner_self_eq_norm_sq_to_K]
    have hnorm : (‖V‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hV
    exact pow_ne_zero 2 hnorm
  have hscalar := not_tendsto_tsum_normalizedExponentialPencil_zero_of_dominantFinset
    (fun i => L (c i)) b hcL D hr hdom hsub hfiberL
  intro hvector
  apply hscalar
  have hmapped : Tendsto
      (fun n : ℕ => L (∑' i : ι, (b i / (r : ℂ)) ^ n • c i))
      atTop (nhds 0) := by
    have hraw := (L.continuous.tendsto 0).comp hvector
    change Tendsto (L ∘ fun n : ℕ =>
      ∑' i : ι, (b i / (r : ℂ)) ^ n • c i) atTop (nhds 0)
    simpa only [map_zero] using hraw
  apply hmapped.congr'
  exact Filter.Eventually.of_forall fun n => by
    have hzle (i : ι) : ‖b i / (r : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      apply (div_le_one hr).2
      by_cases hi : i ∈ D
      · exact (hdom i hi).le
      · exact (hsub i hi).le
    have hsum : Summable (fun i : ι => (b i / (r : ℂ)) ^ n • c i) := by
      apply Summable.of_norm_bounded hc
      intro i
      rw [norm_smul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg (c i))
        (pow_le_one₀ (norm_nonneg _) (hzle i))
    change L (∑' i : ι, (b i / (r : ℂ)) ^ n • c i) =
      ∑' i : ι, L (c i) * (b i / (r : ℂ)) ^ n
    rw [L.map_tsum hsum]
    apply tsum_congr
    intro i
    simp [mul_comm]

/-- Complex exponential aperture profile on the physical interval. -/
def xiPhysicalThetaAbelModeApertureContinuous (A : ℝ) (z : ℂ) :
    C(ClosedInterval 0 A, ℂ) where
  toFun u := Complex.exp (-z * (u.1 : ℂ))
  continuous_toFun := by fun_prop

/-- Aperture profile as a genuine complex `L²` vector. -/
def xiPhysicalThetaAbelModeApertureL2 (A : ℝ) (z : ℂ) :
    Lp ℂ 2 (volume : Measure (ClosedInterval 0 A)) :=
  ContinuousMap.toLp 2 volume ℂ (xiPhysicalThetaAbelModeApertureContinuous A z)

/-- Height-independent `L²` vector carried by one theta--Abel mode. -/
def xiPhysicalThetaAbelCountableModeVector
    {ι : Type*} (A c : ℝ) (z a : ι → ℂ) (i : ι) :
    Lp ℂ 2 (volume : Measure (ClosedInterval 0 A)) :=
  (a i * xiPhysicalLogWindowModeMultiplier c (z i) * ((z i + 1) / z i)) •
    xiPhysicalThetaAbelModeApertureL2 A (z i)

/-- Every exponential profile on a positive aperture is a nonzero `L²` vector. -/
theorem xiPhysicalThetaAbelModeApertureL2_ne_zero
    {A : ℝ} (hA : 0 < A) (z : ℂ) :
    xiPhysicalThetaAbelModeApertureL2 A z ≠ 0 := by
  intro hzero
  have hveczero :
      (xiPhysicalThetaAbelModeApertureL2 A z : ClosedInterval 0 A → ℂ) =ᵐ[volume]
        fun _ => 0 := by
    rw [hzero]
    exact Lp.coeFn_zero ℂ 2 (volume : Measure (ClosedInterval 0 A))
  have hcoe := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
    (μ := (volume : Measure (ClosedInterval 0 A)))
    (xiPhysicalThetaAbelModeApertureContinuous A z)
  have hfalse : ∀ᵐ x : ClosedInterval 0 A ∂volume, False := by
    filter_upwards [hcoe, hveczero] with x hx hxzero
    change (((ContinuousMap.toLp 2 volume ℂ
      (xiPhysicalThetaAbelModeApertureContinuous A z) :
        Lp ℂ 2 (volume : Measure (ClosedInterval 0 A))) :
          ClosedInterval 0 A → ℂ) x) = 0 at hxzero
    rw [hx] at hxzero
    exact Complex.exp_ne_zero _ hxzero
  have hmeasure : (volume : Measure (ClosedInterval 0 A)) Set.univ = 0 := by
    simpa using ae_iff.mp hfalse
  have hmass : (volume : Measure (ClosedInterval 0 A)) Set.univ =
      ENNReal.ofReal A := by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc]
    simp
  have hofReal : ENNReal.ofReal A = 0 := hmass.symm.trans hmeasure
  exact (ENNReal.ofReal_ne_zero_iff.mpr hA) hofReal

/-- Nonzero source coefficient and nondegenerate theta--Abel multiplier give a nonzero mode
vector on every positive aperture. -/
theorem xiPhysicalThetaAbelCountableModeVector_ne_zero
    {ι : Type*} {A c : ℝ} {z a : ι → ℂ} (i : ι)
    (hA : 0 < A) (hc : 0 < c) (hzre : (z i).re < 0)
    (ha : a i ≠ 0) (hznegOne : z i ≠ -1) :
    xiPhysicalThetaAbelCountableModeVector A c z a i ≠ 0 := by
  have hz : z i ≠ 0 := by
    intro h
    rw [h] at hzre
    simp at hzre
  have hnum : z i + 1 ≠ 0 := by
    intro h
    apply hznegOne
    calc
      z i = (z i + 1) - 1 := by ring
      _ = -1 := by rw [h]; ring
  apply smul_ne_zero
  · exact mul_ne_zero (mul_ne_zero ha
      (xiPhysicalLogWindowModeMultiplier_ne_zero hc hzre)) (div_ne_zero hnum hz)
  · exact xiPhysicalThetaAbelModeApertureL2_ne_zero hA (z i)

/-- Injectivity of phases on a finite packet turns any selected nonzero vector into a nonzero
phase-fiber aggregate. -/
theorem exists_nonzero_finiteExponentialVectorFiberCoefficient_of_injOn
    {ι E : Type*} [AddCommMonoid E]
    (D : Finset ι) (v : ι → E) (phase : ι → ℂ)
    (hphase : Set.InjOn phase D) {j : ι} (hj : j ∈ D) (hv : v j ≠ 0) :
    ∃ u ∈ D.image phase,
      finiteExponentialVectorFiberCoefficient D v phase u ≠ 0 := by
  classical
  refine ⟨phase j, Finset.mem_image_of_mem phase hj, ?_⟩
  rw [finiteExponentialVectorFiberCoefficient]
  have hfilter : D.filter (fun i => phase i = phase j) =
      D.filter (fun i => i = j) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hsame⟩
      exact ⟨hi, hphase hi hj hsame⟩
    · rintro ⟨hi, rfl⟩
      exact ⟨hi, rfl⟩
  rw [hfilter]
  rw [Finset.sum_filter]
  simpa [hj] using hv

/-- Countable theta--Abel packet after maximal-real-part normalization. -/
def xiPhysicalThetaAbelCountableNormalizedL2Response
    {ι : Type*} (A c beta : ℝ) (z a : ι → ℂ) (n : ℕ) :
    Lp ℂ 2 (volume : Measure (ClosedInterval 0 A)) :=
  ∑' i : ι, (Complex.exp (z i) / (Real.exp beta : ℂ)) ^ n •
    xiPhysicalThetaAbelCountableModeVector A c z a i

/-- A norm-summable countable theta--Abel `L²` packet cannot hide a finite isolated rightmost
spectral layer whose aggregate aperture vector is nonzero in one phase fiber. -/
theorem not_tendsto_xiPhysicalThetaAbelCountableNormalizedL2Response_zero_of_dominantFinset
    {ι : Type*} (A c beta : ℝ) (z a : ι → ℂ)
    (hsum : Summable (fun i => ‖xiPhysicalThetaAbelCountableModeVector A c z a i‖))
    (D : Finset ι)
    (hdom : ∀ i ∈ D, (z i).re = beta)
    (hsub : ∀ i ∉ D, (z i).re < beta)
    (hfiber : ∃ u ∈ D.image
        (fun i => Complex.exp (z i) / (Real.exp beta : ℂ)),
      finiteExponentialVectorFiberCoefficient D
        (xiPhysicalThetaAbelCountableModeVector A c z a)
        (fun i => Complex.exp (z i) / (Real.exp beta : ℂ)) u ≠ 0) :
    ¬ Tendsto
      (xiPhysicalThetaAbelCountableNormalizedL2Response A c beta z a)
      atTop (nhds 0) := by
  apply not_tendsto_tsum_normalizedExponentialPencil_vector_zero_of_dominantFinset
    (xiPhysicalThetaAbelCountableModeVector A c z a)
    (fun i => Complex.exp (z i)) hsum D (Real.exp_pos beta)
  · intro i hi
    rw [Complex.norm_exp, hdom i hi]
  · intro i hi
    rw [Complex.norm_exp]
    exact Real.exp_lt_exp.mpr (hsub i hi)
  · exact hfiber

/-- Above the critical wall, physical half-density renormalization cannot make the countable
theta--Abel `L²` packet decay. -/
theorem not_tendsto_xiPhysicalThetaAbelCountableL2PhysicalScale_zero_of_dominantFinset
    {ι : Type*} (A c beta : ℝ) (z a : ι → ℂ)
    (hsum : Summable (fun i => ‖xiPhysicalThetaAbelCountableModeVector A c z a i‖))
    (D : Finset ι)
    (hdom : ∀ i ∈ D, (z i).re = beta)
    (hsub : ∀ i ∉ D, (z i).re < beta)
    (hfiber : ∃ u ∈ D.image
        (fun i => Complex.exp (z i) / (Real.exp beta : ℂ)),
      finiteExponentialVectorFiberCoefficient D
        (xiPhysicalThetaAbelCountableModeVector A c z a)
        (fun i => Complex.exp (z i) / (Real.exp beta : ℂ)) u ≠ 0)
    (hwall : -(1 / 2 : ℝ) < beta) :
    ¬ Tendsto
      (fun n : ℕ =>
        Complex.exp ((beta + 1 / 2 : ℝ) : ℂ) ^ n •
          xiPhysicalThetaAbelCountableNormalizedL2Response A c beta z a n)
      atTop (nhds 0) := by
  have hnormalized :=
    not_tendsto_xiPhysicalThetaAbelCountableNormalizedL2Response_zero_of_dominantFinset
      A c beta z a hsum D hdom hsub hfiber
  intro hphysical
  apply hnormalized
  let q : ℂ := Complex.exp (-((beta + 1 / 2 : ℝ) : ℂ))
  have hgap : 0 < beta + 1 / 2 := by linarith
  have hqnorm : ‖q‖ < 1 := by
    rw [show q = Complex.exp (-((beta + 1 / 2 : ℝ) : ℂ)) from rfl,
      Complex.norm_exp]
    simp only [neg_re, ofReal_re]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hgap)
  have hq : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hqnorm
  have hzero := hq.smul hphysical
  have hzero' : Tendsto
      (fun n : ℕ => q ^ n •
        (Complex.exp ((beta + 1 / 2 : ℝ) : ℂ) ^ n •
          xiPhysicalThetaAbelCountableNormalizedL2Response A c beta z a n))
      atTop (nhds 0) := by simpa using hzero
  apply hzero'.congr'
  exact Filter.Eventually.of_forall fun n => by
    simp only [smul_smul]
    have hunit : q * Complex.exp ((beta + 1 / 2 : ℝ) : ℂ) = 1 := by
      rw [show q = Complex.exp (-((beta + 1 / 2 : ℝ) : ℂ)) from rfl,
        ← Complex.exp_add]
      simp
    rw [← mul_pow, hunit, one_pow, one_smul]

/-- Collision-free maximal phase data make the nonzero-fiber premise automatic. Thus a selected
nonzero supercritical theta--Abel mode survives every norm-summable strictly subdominant tail. -/
theorem not_tendsto_xiPhysicalThetaAbelCountableL2PhysicalScale_zero_of_phaseInjective
    {ι : Type*} (A c beta : ℝ) (z a : ι → ℂ)
    (hA : 0 < A) (hc : 0 < c)
    (hsum : Summable (fun i => ‖xiPhysicalThetaAbelCountableModeVector A c z a i‖))
    (D : Finset ι)
    (hdom : ∀ i ∈ D, (z i).re = beta)
    (hsub : ∀ i ∉ D, (z i).re < beta)
    (hphase : Set.InjOn
      (fun i => Complex.exp (z i) / (Real.exp beta : ℂ)) D)
    (j : ι) (hj : j ∈ D) (ha : a j ≠ 0) (hznegOne : z j ≠ -1)
    (hbeta0 : beta < 0) (hwall : -(1 / 2 : ℝ) < beta) :
    ¬ Tendsto
      (fun n : ℕ =>
        Complex.exp ((beta + 1 / 2 : ℝ) : ℂ) ^ n •
          xiPhysicalThetaAbelCountableNormalizedL2Response A c beta z a n)
      atTop (nhds 0) := by
  have hzjre : (z j).re < 0 := by rw [hdom j hj]; exact hbeta0
  have hvj : xiPhysicalThetaAbelCountableModeVector A c z a j ≠ 0 :=
    xiPhysicalThetaAbelCountableModeVector_ne_zero j hA hc hzjre ha hznegOne
  have hfiber := exists_nonzero_finiteExponentialVectorFiberCoefficient_of_injOn
    D (xiPhysicalThetaAbelCountableModeVector A c z a)
      (fun i => Complex.exp (z i) / (Real.exp beta : ℂ)) hphase hj hvj
  exact not_tendsto_xiPhysicalThetaAbelCountableL2PhysicalScale_zero_of_dominantFinset
    A c beta z a hsum D hdom hsub hfiber hwall

end

end RHTower
