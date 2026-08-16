import GaloisForLFunctions.HTGeometry.ApertureHyperbolicL2Expansion
import GaloisForLFunctions.HTGeometry.GroundOverlap
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The aperture Fourier character and its ground direction

The Fourier character `t ↦ e^{-ixt}` of a bounded aperture is the `L²` sum of its monomial series,
uniformly dominated by the exponential majorant.  A bounded observable that annihilates every
monomial below a given degree therefore sees the character only through its leading direction: the
rescaled image converges to the observable of that monomial.

Consequently the normalized overlap between the leading direction and the image of the character
tends to one at the origin.  Vanishing at the origin is forced by minimality of the degree and is
not a loss of coherence.
-/

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The complex monomial and the Fourier character -/

theorem memLp_apertureComplexPow (a : ℝ) (n : ℕ) :
    MemLp (fun x : ℝ => ((x : ℂ)) ^ n) 2 (apertureMeasure a) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) (a ^ n) ?_
  filter_upwards [apertureMeasure_ae_mem a] with x hx
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg x) (abs_le_of_mem_aperture hx) n

theorem memLp_apertureFourier (a x : ℝ) :
    MemLp (fun t : ℝ => Complex.exp (-(x : ℂ) * Complex.I * (t : ℂ))) 2 (apertureMeasure a) := by
  refine MemLp.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1 ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [Complex.norm_exp]
  have hre : (-(x : ℂ) * Complex.I * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- The complex monomial `t ↦ tⁿ` as an aperture `L²` class. -/
def apertureComplexMonomialL2 (a : ℝ) (n : ℕ) : Lp ℂ 2 (apertureMeasure a) :=
  (memLp_apertureComplexPow a n).toLp _

/-- The Fourier character `t ↦ e^{-ixt}` as an aperture `L²` class. -/
def apertureFourierL2 (a x : ℝ) : Lp ℂ 2 (apertureMeasure a) :=
  (memLp_apertureFourier a x).toLp _

theorem coeFn_apertureComplexMonomialL2 (a : ℝ) (n : ℕ) :
    (apertureComplexMonomialL2 a n : ℝ → ℂ) =ᵐ[apertureMeasure a] fun x => ((x : ℂ)) ^ n :=
  (memLp_apertureComplexPow a n).coeFn_toLp

theorem norm_apertureComplexMonomialL2_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ‖apertureComplexMonomialL2 a n‖ ≤ Real.sqrt (2 * a) * a ^ n := by
  have hbd : ∀ᵐ x ∂(apertureMeasure a),
      ‖(apertureComplexMonomialL2 a n : ℝ → ℂ) x‖ ≤ a ^ n := by
    filter_upwards [coeFn_apertureComplexMonomialL2 a n, apertureMeasure_ae_mem a] with x hx hmem
    rw [hx, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg x) (abs_le_of_mem_aperture hmem) n
  have h := Lp.norm_le_of_ae_bound (p := 2) (pow_nonneg ha n) hbd
  refine h.trans (le_of_eq ?_)
  rw [rpow_measureUnivNNReal_apertureMeasure ha]

set_option maxHeartbeats 1000000 in
/-- **The Fourier character is the `L²` sum of its monomial series.** -/
theorem hasSum_apertureFourierL2 {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    HasSum (fun n : ℕ => ((-(x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ))
        • apertureComplexMonomialL2 a n)
      (apertureFourierL2 a x) := by
  have hmem : ∀ n : ℕ, MemLp
      (fun t : ℝ => ((-(x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ)) * ((t : ℂ)) ^ n) 2
      (apertureMeasure a) := fun n => (memLp_apertureComplexPow a n).const_mul _
  have hnormcoef : ∀ n : ℕ,
      ‖((-(x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ))‖ = |x| ^ n / (Nat.factorial n : ℝ) := by
    intro n
    rw [norm_div, norm_pow, norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs]
    congr 1
    rw [Complex.norm_natCast]
  have hgsum : Summable fun n : ℕ => (|x| * a) ^ n / (Nat.factorial n : ℝ) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (|x| * a)
    exact h.summable
  have hbase := hasSum_apertureToLp (𝕜 := ℂ)
    (f := fun n t => ((-(x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ)) * ((t : ℂ)) ^ n)
    (F := fun t => Complex.exp (-(x : ℂ) * Complex.I * (t : ℂ)))
    (g := fun n => (|x| * a) ^ n / (Nat.factorial n : ℝ))
    hgsum (fun n => by positivity)
    (fun n t ht => by
      rw [norm_mul, hnormcoef n, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow,
        div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg t) (abs_le_of_mem_aperture ht) n) (by positivity))
    (fun t _ => by
      have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (-(x : ℂ) * Complex.I * (t : ℂ))
      rw [← Complex.exp_eq_exp_ℂ] at h
      refine h.congr_fun fun n => ?_
      rw [mul_pow]
      ring)
    hmem (memLp_apertureFourier a x)
  refine hbase.congr_fun fun n => ?_
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul ((-(x : ℂ) * Complex.I) ^ n / (Nat.factorial n : ℂ))
    (apertureComplexMonomialL2 a n), coeFn_apertureComplexMonomialL2 a n,
    (hmem n).coeFn_toLp] with t ht1 ht2 ht3
  rw [ht3, ht1, Pi.smul_apply, ht2, smul_eq_mul]

/-! ## The leading ground direction -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The observable's leading ground coefficient at degree `n`. -/
def fourierGroundVector (a : ℝ) (P : Lp ℂ 2 (apertureMeasure a) →L[ℂ] E) (n : ℕ) : E :=
  ((-Complex.I) ^ n / (Nat.factorial n : ℂ)) • P (apertureComplexMonomialL2 a n)

set_option maxHeartbeats 1000000 in
theorem summable_norm_fourierGroundVector {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℂ 2 (apertureMeasure a) →L[ℂ] E) {R : ℝ} (hR : 0 ≤ R) :
    Summable fun n : ℕ => ‖fourierGroundVector a P n‖ * R ^ n := by
  have hmaj : Summable fun n : ℕ =>
      (‖P‖ * Real.sqrt (2 * a)) * ((a * R) ^ n / (Nat.factorial n : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (a * R)).summable.mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  have hcoef : ‖((-Complex.I) ^ n / (Nat.factorial n : ℂ))‖ = (Nat.factorial n : ℝ)⁻¹ := by
    rw [norm_div, norm_pow, norm_neg, Complex.norm_I, one_pow, Complex.norm_natCast, one_div]
  have hnorm : ‖fourierGroundVector a P n‖
      = (Nat.factorial n : ℝ)⁻¹ * ‖P (apertureComplexMonomialL2 a n)‖ := by
    rw [fourierGroundVector, norm_smul, hcoef]
  have hchain : ‖P (apertureComplexMonomialL2 a n)‖ ≤ ‖P‖ * (Real.sqrt (2 * a) * a ^ n) :=
    (P.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (norm_apertureComplexMonomialL2_le ha n) (norm_nonneg _))
  rw [hnorm]
  have hstep : (Nat.factorial n : ℝ)⁻¹ * ‖P (apertureComplexMonomialL2 a n)‖ * R ^ n
      ≤ (Nat.factorial n : ℝ)⁻¹ * (‖P‖ * (Real.sqrt (2 * a) * a ^ n)) * R ^ n := by
    have h1 := mul_le_mul_of_nonneg_left hchain
      (le_of_lt (inv_pos.mpr (show (0:ℝ) < (Nat.factorial n : ℝ) by positivity)))
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [mul_pow]
  field_simp

set_option maxHeartbeats 1000000 in
/-- **`(69)`: the ground Fourier line has an exact leading direction.**  An observable annihilating
every monomial below degree `k` sees the character only through its degree-`k` coefficient. -/
theorem tendsto_smul_inv_pow_apertureFourier {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℂ 2 (apertureMeasure a) →L[ℂ] E) {k : ℕ}
    (hzero : ∀ n, n < k → P (apertureComplexMonomialL2 a n) = 0) :
    Tendsto (fun x : ℝ => (x ^ k)⁻¹ • P (apertureFourierL2 a x)) (𝓝[≠] (0 : ℝ))
      (𝓝 (fourierGroundVector a P k)) := by
  refine tendsto_smul_inv_pow_of_hasSum_punctured (E := E)
    (u := fourierGroundVector a P) (R := 1) (by norm_num)
    (summable_norm_fourierGroundVector ha P (by norm_num))
    (fun n hn => by rw [fourierGroundVector, hzero n hn, smul_zero]) ?_
  intro x _ _
  have hbase := (hasSum_apertureFourierL2 ha x).mapL P
  refine hbase.congr_fun fun n => ?_
  rw [ContinuousLinearMap.map_smul, fourierGroundVector, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  rw [mul_pow]
  ring

/-! ## The normalized ground overlap -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
/-- **`(70)`: the normalized ground overlap tends to one.**  Vanishing of the character's image at
the origin is forced by minimality of the visible degree and is not a loss of coherence. -/
theorem tendsto_groundOverlap_apertureFourier {a : ℝ} (ha : 0 ≤ a)
    (P : Lp ℂ 2 (apertureMeasure a) →L[ℂ] E) {k : ℕ}
    (hzero : ∀ n, n < k → P (apertureComplexMonomialL2 a n) = 0)
    (hk : P (apertureComplexMonomialL2 a k) ≠ 0) :
    Tendsto (fun x : ℝ =>
        groundOverlap (((Nat.factorial k : ℂ))⁻¹ • P (apertureComplexMonomialL2 a k))
          (P (apertureFourierL2 a x)))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  set u : E := ((Nat.factorial k : ℂ))⁻¹ • P (apertureComplexMonomialL2 a k) with hudef
  have hfacne : ((Nat.factorial k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hu : u ≠ 0 := by
    rw [hudef]
    exact smul_ne_zero (inv_ne_zero hfacne) hk
  have hcnorm : ‖((-Complex.I) ^ k)‖ = 1 := by
    rw [norm_pow, norm_neg, Complex.norm_I, one_pow]
  have hL : fourierGroundVector a P k = ((-Complex.I) ^ k) • u := by
    rw [fourierGroundVector, hudef, smul_smul, div_eq_mul_inv]
  have hcne : ((-Complex.I) ^ k) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcnorm
    norm_num at hcnorm
  have hLne : fourierGroundVector a P k ≠ 0 := by
    rw [hL]
    exact smul_ne_zero hcne hu
  have hW := tendsto_smul_inv_pow_apertureFourier ha P hzero
  have hnum : Tendsto (fun x : ℝ =>
        ‖(inner ℂ u ((x ^ k)⁻¹ • P (apertureFourierL2 a x)) : ℂ)‖ ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (‖(inner ℂ u (fourierGroundVector a P k) : ℂ)‖ ^ 2)) :=
    ((tendsto_const_nhds.inner hW).norm).pow 2
  have hden : Tendsto (fun x : ℝ => ‖u‖ ^ 2 * ‖(x ^ k)⁻¹ • P (apertureFourierL2 a x)‖ ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (‖u‖ ^ 2 * ‖fourierGroundVector a P k‖ ^ 2)) :=
    tendsto_const_nhds.mul (hW.norm.pow 2)
  have hdenne : ‖u‖ ^ 2 * ‖fourierGroundVector a P k‖ ^ 2 ≠ 0 := by
    have h1 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have h2 : ‖fourierGroundVector a P k‖ ≠ 0 := norm_ne_zero_iff.mpr hLne
    positivity
  have hlim := hnum.div hden hdenne
  have hvalue : ‖(inner ℂ u (fourierGroundVector a P k) : ℂ)‖ ^ 2 /
      (‖u‖ ^ 2 * ‖fourierGroundVector a P k‖ ^ 2) = 1 := by
    have h := groundOverlap_unimodular_smul (c := ((-Complex.I) ^ k)) hcnorm hu
    rw [← hL] at h
    exact h
  rw [hvalue] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxne : x ≠ 0 := hx
  have hpowne : (x ^ k)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero k hxne)
  simp only [Pi.div_apply]
  rw [← groundOverlap_real_smul hpowne u (P (apertureFourierL2 a x)), groundOverlap]

end Inner

end GaloisForLFunctions.HTGeometry
