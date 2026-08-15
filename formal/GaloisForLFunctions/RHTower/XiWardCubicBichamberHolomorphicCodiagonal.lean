import GaloisForLFunctions.RHTower.XiWardCubicReflectionLoewnerCodiagonalIncidence

/-!
# Cubic Ward bichamber holomorphic codiagonal (W-H191)

The apparently nonholomorphic zero feature from W-H190 is the restriction of a jointly entire
two-variable feature.  The left FE chamber supplies the conjugate horizontal coordinate that one
right-chamber scalar cannot retain.  On the reflection graph `s = 1 - star t`, the two entire
features become the cubic tensor feature and its conjugate, so their product is its norm square.

The reflection-Loewner kernel simultaneously becomes a coefficient-linear arithmetic divided
difference when `s` is in the left Euler chamber and `t` is in the right Euler chamber.  Thus the
same meromorphic current is holomorphically weighted on the source bichamber and has iterated
sesquiresidue equal to multiplicity times exact cubic Hellinger density.  The weight is holomorphic
in `(s,t)`, whereas the Loewner kernel is holomorphic/antiholomorphic in `(s,t)`; this construction
therefore exposes, but does not erase, the remaining complex-structure mismatch.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Split a complex exponential into horizontal damping and unitary phase. -/
theorem complexExp_neg_mul_eq_horizontal_mul_phase (z : ℂ) (r : ℝ) :
    Complex.exp (-(z * (r : ℂ))) =
      (Real.exp (-(z.re * r)) : ℂ) *
        Complex.exp (-I * ((z.im * r : ℝ) : ℂ)) := by
  have hexp : -(z * (r : ℂ)) =
      ((-(z.re * r) : ℝ) : ℂ) + -I * ((z.im * r : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp]

/-- Right-decaying jointly entire bichamber feature. -/
def xiWardCubicBichamberRightFeature (s t : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) *
    (Complex.exp (-((t - 1 / 2) * (r : ℂ))) -
      Complex.exp (-(((3 * (t - 1 / 2) - (s - 1 / 2)) / 2) * (r : ℂ))))

/-- Left-decaying jointly entire bichamber feature. -/
def xiWardCubicBichamberLeftFeature (s t : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) *
    (Complex.exp ((s - 1 / 2) * (r : ℂ)) -
      Complex.exp (((3 * (s - 1 / 2) - (t - 1 / 2)) / 2) * (r : ℂ)))

/-- On the FE reflection graph, the right entire feature is the W-H190 tensor feature. -/
theorem xiWardCubicBichamberRightFeature_reflectionGraph (t : ℂ) (r : ℝ) :
    xiWardCubicBichamberRightFeature (1 - star t) t r =
      xiWardCubicTensorConormalFeature t r := by
  have hx1 : (3 * (t - 1 / 2) - (1 - star t - 1 / 2)) / 2 =
      ((2 * (t - 1 / 2).re : ℝ) : ℂ) +
        I * (((t - 1 / 2).im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [xiWardCubicBichamberRightFeature, hx1,
    complexExp_neg_mul_eq_horizontal_mul_phase,
    complexExp_neg_mul_eq_horizontal_mul_phase]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [ofReal_mul]
  rw [xiWardCubicTensorConormalFeature,
    xiWardCubicTensorHorizontalDifference]
  push_cast
  ring

/-- On the FE reflection graph, the left entire feature is the conjugate tensor feature. -/
theorem xiWardCubicBichamberLeftFeature_reflectionGraph (t : ℂ) (r : ℝ) :
    xiWardCubicBichamberLeftFeature (1 - star t) t r =
      star (xiWardCubicTensorConormalFeature t r) := by
  have hx0 : -(1 - star t - 1 / 2) = star (t - 1 / 2) := by
    simp
    ring
  have hx1 : -(3 * (1 - star t - 1 / 2) - (t - 1 / 2)) / 2 =
      ((2 * (t - 1 / 2).re : ℝ) : ℂ) -
        I * (((t - 1 / 2).im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [xiWardCubicBichamberLeftFeature]
  have hx0' : 1 - star t - 1 / 2 = -star (t - 1 / 2) := by
    have h := congrArg Neg.neg hx0
    simpa only [neg_neg] using h
  have hfirstArg : (1 - star t - 1 / 2) * (r : ℂ) =
      -(star (t - 1 / 2) * (r : ℂ)) := by
    rw [hx0']
    ring
  have hsecondArg :
      ((3 * (1 - star t - 1 / 2) - (t - 1 / 2)) / 2) * (r : ℂ) =
        -((((2 * (t - 1 / 2).re : ℝ) : ℂ) -
          I * (((t - 1 / 2).im : ℝ) : ℂ)) * (r : ℂ)) := by
    rw [← hx1]
    ring
  rw [hfirstArg, hsecondArg,
    complexExp_neg_mul_eq_horizontal_mul_phase,
    complexExp_neg_mul_eq_horizontal_mul_phase]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [xiWardCubicTensorConormalFeature]
  change _ = (starRingEnd ℂ) (_ * _ * _)
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [xiWardCubicTensorHorizontalDifference]
  push_cast
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  norm_num
  ring

/-- The bichamber product restricts to the exact tensor norm square. -/
theorem xiWardCubicBichamberFeatureProduct_reflectionGraph (t : ℂ) (r : ℝ) :
    xiWardCubicBichamberLeftFeature (1 - star t) t r *
        xiWardCubicBichamberRightFeature (1 - star t) t r =
      (Complex.normSq (xiWardCubicTensorConormalFeature t r) : ℂ) := by
  rw [xiWardCubicBichamberLeftFeature_reflectionGraph,
    xiWardCubicBichamberRightFeature_reflectionGraph,
    Complex.normSq_eq_conj_mul_self]
  rfl

/-- Right bichamber feature is jointly entire. -/
theorem xiWardCubicBichamberRightFeature_differentiable (r : ℝ) :
    Differentiable ℂ
      (fun p : ℂ × ℂ => xiWardCubicBichamberRightFeature p.1 p.2 r) := by
  unfold xiWardCubicBichamberRightFeature
  fun_prop

/-- Left bichamber feature is jointly entire. -/
theorem xiWardCubicBichamberLeftFeature_differentiable (r : ℝ) :
    Differentiable ℂ
      (fun p : ℂ × ℂ => xiWardCubicBichamberLeftFeature p.1 p.2 r) := by
  unfold xiWardCubicBichamberLeftFeature
  fun_prop

/-- Jointly entire feature product used to weight the meromorphic Loewner current. -/
def xiWardCubicBichamberFeatureProduct (s t : ℂ) (r : ℝ) : ℂ :=
  xiWardCubicBichamberLeftFeature s t r *
    xiWardCubicBichamberRightFeature s t r

/-- In opposite Euler chambers the reflection kernel is a source-linear divided difference whose
two arithmetic arguments both lie in the absolute-convergence half-plane. -/
theorem xiWardCubicReflectionLoewnerKernel_eq_bichamberArithmetic
    {s t : ℂ} (hs : s.re < 0) (ht : 1 < t.re) :
    xiWardCubicReflectionLoewnerKernel s t =
      (xiWardCubicCompletedArithmeticCurrent (star t) -
        xiWardCubicCompletedArithmeticCurrent (1 - s)) /
          (star t - (1 - s)) := by
  have hu : 1 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hv : 1 < (star t).re := by simpa using ht
  have hsld : logDeriv xi s = -logDeriv xi (1 - s) := by
    rw [logDeriv_xi_reciprocity]
    ring
  rw [xiWardCubicReflectionLoewnerKernel, hsld,
    show star (logDeriv xi t) = logDeriv xi (star t) by
      exact (logDeriv_xi_conj_global t).symm,
    logDeriv_xi_eq_arithmetic hu, logDeriv_xi_eq_arithmetic hv]
  unfold xiWardCubicCompletedArithmeticCurrent
  congr 1 <;> ring

/-- Holomorphically weighted reflection-Loewner current. -/
def xiWardCubicBichamberHolomorphicallyWeightedCurrent (s t : ℂ) (r : ℝ) : ℂ :=
  xiWardCubicReflectionLoewnerKernel s t *
    xiWardCubicBichamberFeatureProduct s t r

/-- Source expression of the complete current on the opposite Euler chambers. -/
theorem xiWardCubicBichamberHolomorphicallyWeightedCurrent_eq_arithmetic
    {s t : ℂ} (hs : s.re < 0) (ht : 1 < t.re) (r : ℝ) :
    xiWardCubicBichamberHolomorphicallyWeightedCurrent s t r =
      ((xiWardCubicCompletedArithmeticCurrent (star t) -
        xiWardCubicCompletedArithmeticCurrent (1 - s)) /
          (star t - (1 - s))) * xiWardCubicBichamberFeatureProduct s t r := by
  rw [xiWardCubicBichamberHolomorphicallyWeightedCurrent,
    xiWardCubicReflectionLoewnerKernel_eq_bichamberArithmetic hs ht]

/-- Explicit first residue column of the holomorphic bichamber current. -/
def xiWardCubicBichamberHolomorphicallyWeightedCurrentLeftResidue
    (rho t : ℂ) (r : ℝ) : ℂ :=
  xiWardCubicReflectionLoewnerLeftResidue rho t *
    xiWardCubicBichamberFeatureProduct (1 - star rho) t r

/-- First residue of the holomorphic bichamber current. -/
theorem xiWardCubicBichamberHolomorphicallyWeightedCurrent_left_residue
    (rho : ℂ) {t : ℂ} (ht : t ≠ rho) (r : ℝ) :
    Tendsto
      (fun s : ℂ =>
        (s - (1 - star rho)) *
          xiWardCubicBichamberHolomorphicallyWeightedCurrent s t r)
      (nhdsWithin (1 - star rho) ({1 - star rho}ᶜ))
      (nhds (xiWardCubicBichamberHolomorphicallyWeightedCurrentLeftResidue rho t r)) := by
  have hL := xiWardCubicReflectionLoewnerKernel_left_residue rho ht
  have hf : Tendsto (fun s : ℂ => xiWardCubicBichamberFeatureProduct s t r)
      (nhdsWithin (1 - star rho) ({1 - star rho}ᶜ))
      (nhds (xiWardCubicBichamberFeatureProduct (1 - star rho) t r)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply ContinuousAt.tendsto
    unfold xiWardCubicBichamberFeatureProduct
      xiWardCubicBichamberLeftFeature xiWardCubicBichamberRightFeature
    fun_prop
  have h := hL.mul hf
  convert h using 1
  · funext s
    simp [xiWardCubicBichamberHolomorphicallyWeightedCurrent]
    ring
  · simp [xiWardCubicBichamberHolomorphicallyWeightedCurrentLeftResidue]

/-- Iterated sesquiresidue lands multiplicity times exact cubic tensor norm square. -/
theorem xiWardCubicBichamberHolomorphicallyWeightedCurrent_iterated_sesquiresidue
    (rho : ℂ) (r : ℝ) :
    Tendsto
      (fun t : ℂ => star (t - rho) *
        xiWardCubicBichamberHolomorphicallyWeightedCurrentLeftResidue rho t r)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds ((((analyticOrderAt xi (1 - star rho)).toNat : ℂ)) *
        ((Complex.normSq (xiWardCubicTensorConormalFeature rho r) : ℝ) : ℂ))) := by
  have hf : Tendsto
      (fun t : ℂ => xiWardCubicBichamberFeatureProduct (1 - star rho) t r)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (xiWardCubicBichamberFeatureProduct (1 - star rho) rho r)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply ContinuousAt.tendsto
    unfold xiWardCubicBichamberFeatureProduct
      xiWardCubicBichamberLeftFeature xiWardCubicBichamberRightFeature
    fun_prop
  let m : ℂ := ((analyticOrderAt xi (1 - star rho)).toNat : ℂ)
  have htarget := hf.const_mul m
  have heq :
      (fun t : ℂ => star (t - rho) *
        xiWardCubicBichamberHolomorphicallyWeightedCurrentLeftResidue rho t r) =ᶠ[
          nhdsWithin rho ({rho}ᶜ)]
      fun t => m * xiWardCubicBichamberFeatureProduct (1 - star rho) t r := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hne : star (t - rho) ≠ 0 := by
      intro h
      have h' := congrArg (starRingEnd ℂ) h
      have hz : t - rho = 0 := by simpa using h'
      exact ht (sub_eq_zero.mp hz)
    rw [xiWardCubicBichamberHolomorphicallyWeightedCurrentLeftResidue,
      xiWardCubicReflectionLoewnerLeftResidue]
    dsimp only [m]
    field_simp [hne]
  have hfinal := htarget.congr' heq.symm
  convert hfinal using 1
  unfold xiWardCubicBichamberFeatureProduct
  rw [xiWardCubicBichamberFeatureProduct_reflectionGraph]

end
end RHTower
