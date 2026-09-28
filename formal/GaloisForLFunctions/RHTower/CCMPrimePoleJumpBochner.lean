import GaloisForLFunctions.HTGeometry.JumpBochner
import GaloisForLFunctions.RHTower.CCMPrimePoleSchurDefect

/-!
# Bochner calculus for the literal prime Schur operator

Signed logarithmic jumps retain von Mangoldt weights, aperture indicators and the
pole-profile ratio. Their integrated rate potential is exactly the existing Schur
row potential. After dividing a state by the pole profile, their weighted energy
density is exactly the existing Schur edge density.

The iterated energy identity retains both rate-variation terms. No sign for those
terms, Gamma comparison, or Riemann-hypothesis conclusion is assumed or asserted.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators InnerProduct
noncomputable section
namespace RHTower

/-- Both orientations of every prime-power shift in the actual finite prime operator. -/
def ccmPrimePoleJumpIndices (a : SuzukiPositiveAperture) : Finset (ℕ × Bool) :=
  (Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊).product Finset.univ

/-- Translation by the signed logarithm attached to an index. -/
def ccmPrimePoleJumpShift (j : ℕ × Bool) (x : ℝ) : ℝ :=
  x + if j.2 then Real.log j.1 else -Real.log j.1

/-- Literal prime weight after the pole-profile transform, with both endpoint cutoffs. -/
def ccmPrimePoleJumpRate (a : SuzukiPositiveAperture) (j : ℕ × Bool) (x : ℝ) : ℝ :=
  (centralInterval a.1).indicator
    (fun y => (ArithmeticFunction.vonMangoldt j.1 / Real.sqrt j.1) *
      ((centralInterval a.1).indicator primePoleProfile (ccmPrimePoleJumpShift j y) /
        primePoleProfile y)) x

theorem ccmPrimePoleJumpRate_nonneg (a : SuzukiPositiveAperture) (j : ℕ × Bool) (x : ℝ) :
    0 ≤ ccmPrimePoleJumpRate a j x := by
  apply indicator_nonneg _ x
  intro y hy
  apply mul_nonneg
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact div_nonneg (indicator_nonneg (fun z _ => (primePoleProfile_pos z).le) _)
      (primePoleProfile_pos y).le

theorem ccmPrimePoleJumpShift_comm (i j : ℕ × Bool) (x : ℝ) :
    ccmPrimePoleJumpShift i (ccmPrimePoleJumpShift j x) =
      ccmPrimePoleJumpShift j (ccmPrimePoleJumpShift i x) := by
  unfold ccmPrimePoleJumpShift
  ring

theorem ccmPrimePoleJumpRate_true_mul_norm_sq
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SoninL2) {x : ℝ}
    (hx : x ∈ centralInterval a.1) :
    ccmPrimePoleJumpRate a (n, true) x * ‖f x‖ ^ 2 =
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ccmPrimePoleRowDensity a (Real.log n) f x := by
  rw [ccmPrimePoleJumpRate, indicator_of_mem hx]
  simp only [ccmPrimePoleJumpShift, ↓reduceIte, ccmPrimePoleRowDensity]
  ring

theorem ccmPrimePoleJumpRate_false_mul_norm_sq
    (a : SuzukiPositiveAperture) (n : ℕ) (f : SoninL2) {x : ℝ}
    (hx : x ∈ centralInterval a.1) :
    ccmPrimePoleJumpRate a (n, false) x * ‖f x‖ ^ 2 =
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ccmPrimePoleRowDensity a (-Real.log n) f x := by
  rw [ccmPrimePoleJumpRate, indicator_of_mem hx]
  simp only [ccmPrimePoleJumpShift, Bool.false_eq_true, ↓reduceIte, ccmPrimePoleRowDensity]
  ring

theorem ccmPrimePoleJumpRate_mul_norm_sq_ae
    (a : SuzukiPositiveAperture) (n : ℕ) (b : Bool) (f : suzukiApertureHilbert a) :
    (fun x => ccmPrimePoleJumpRate a (n, b) x * ‖f.1 x‖ ^ 2) =ᵐ[volume]
      (fun x => (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ccmPrimePoleRowDensity a (if b then Real.log n else -Real.log n) f.1 x) := by
  have hs := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hs
  filter_upwards [hs] with x hx
  by_cases hmem : x ∈ centralInterval a.1
  · cases b
    · exact ccmPrimePoleJumpRate_false_mul_norm_sq a n f.1 hmem
    · exact ccmPrimePoleJumpRate_true_mul_norm_sq a n f.1 hmem
  · have hz : f.1 x = 0 := by rw [hx, indicator_of_notMem hmem]
    simp [hz, ccmPrimePoleRowDensity]


theorem integrable_ccmPrimePoleJumpRate_mul_norm_sq
    (a : SuzukiPositiveAperture) (j : ℕ × Bool) (f : suzukiApertureHilbert a) :
    Integrable (fun x => ccmPrimePoleJumpRate a j x * ‖f.1 x‖ ^ 2) :=
  ((integrable_ccmPrimePoleRowDensity a _ f.1).const_mul _).congr
    (ccmPrimePoleJumpRate_mul_norm_sq_ae a j.1 j.2 f).symm

/-- The jump-rate potential integrates to the actual prime Schur row potential. -/
theorem ccmPrimePoleRowPotential_eq_jumpRate_integral
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmPrimePoleRowPotential a f.1 =
      ∫ x, ∑ j ∈ ccmPrimePoleJumpIndices a, ccmPrimePoleJumpRate a j x * ‖f.1 x‖ ^ 2 := by
  rw [integral_finsetSum _ (fun j _ => integrable_ccmPrimePoleJumpRate_mul_norm_sq a j f)]
  unfold ccmPrimePoleJumpIndices
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  unfold ccmPrimePoleRowPotential
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Fintype.sum_bool]
  rw [integral_congr_ae (ccmPrimePoleJumpRate_mul_norm_sq_ae a n true f),
    integral_congr_ae (ccmPrimePoleJumpRate_mul_norm_sq_ae a n false f)]
  simp only [Bool.false_eq_true, ↓reduceIte, integral_const_mul]
  ring

open HTGeometry.JumpBochner in
/-- Exact Bochner identity with every aperture and profile rate-variation term retained. -/
theorem ccmPrimePoleJump_gammaTwo_eq_squares_add_rateDefect
    (a : SuzukiPositiveAperture) (f : ℝ → ℝ) (x : ℝ) :
    gammaTwo (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a) ccmPrimePoleJumpShift f x =
      ∑ i ∈ ccmPrimePoleJumpIndices a, ∑ j ∈ ccmPrimePoleJumpIndices a,
        (ccmPrimePoleJumpRate a i x * ccmPrimePoleJumpRate a j x *
            (difference ccmPrimePoleJumpShift j (difference ccmPrimePoleJumpShift i f) x) ^ 2 / 4 +
          ccmPrimePoleJumpRate a j x * difference ccmPrimePoleJumpShift j (ccmPrimePoleJumpRate a i) x *
            (difference ccmPrimePoleJumpShift i f (ccmPrimePoleJumpShift j x)) ^ 2 / 4 -
          ccmPrimePoleJumpRate a i x * difference ccmPrimePoleJumpShift i (ccmPrimePoleJumpRate a j) x *
            difference ccmPrimePoleJumpShift i f x *
              difference ccmPrimePoleJumpShift j f (ccmPrimePoleJumpShift i x) / 2) :=
  gammaTwo_eq_squares_add_rateDefect _ _ _ _ _ (fun i _ j _ => ccmPrimePoleJumpShift_comm i j x)

/-- Algebraic transport of a normalized jump into the weighted edge square. -/
theorem primePoleProfile_normalized_difference (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (A B : ℂ) :
    u ^ 2 * (v / u) * ‖B / (v : ℂ) - A / (u : ℂ)‖ ^ 2 =
      ‖(u : ℂ) * B - (v : ℂ) * A‖ ^ 2 / (u * v) := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hdiff : B / (v : ℂ) - A / (u : ℂ) =
      ((u : ℂ) * B - (v : ℂ) * A) / ((u : ℂ) * (v : ℂ)) := by
    field_simp
  rw [hdiff, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu, abs_of_pos hv]
  field_simp


/-- Divide a state by the strictly positive pole profile. -/
def ccmPrimePoleNormalized (f : SoninL2) (x : ℝ) : ℂ := f x / (primePoleProfile x : ℂ)

/-- Pointwise identity with the existing Schur edge density, including outside the aperture. -/
theorem ccmPrimePoleJumpRate_mul_normalized_difference
    (a : SuzukiPositiveAperture) (n : ℕ) (b : Bool) (f : SoninL2) (x : ℝ) :
    primePoleProfile x ^ 2 * ccmPrimePoleJumpRate a (n, b) x *
        ‖ccmPrimePoleNormalized f (ccmPrimePoleJumpShift (n, b) x) -
          ccmPrimePoleNormalized f x‖ ^ 2 =
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        ccmPrimePoleEdgeDensity a (if b then Real.log n else -Real.log n) f x := by
  let h : ℝ := if b then Real.log n else -Real.log n
  change primePoleProfile x ^ 2 *
      (centralInterval a.1).indicator (fun y =>
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          ((centralInterval a.1).indicator primePoleProfile (y+h) / primePoleProfile y)) x *
        ‖f (x+h) / (primePoleProfile (x+h) : ℂ) - f x / (primePoleProfile x : ℂ)‖ ^ 2 =
    (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * ccmPrimePoleEdgeDensity a h f x
  by_cases hx : x ∈ centralInterval a.1
  · by_cases hy : x+h ∈ centralInterval a.1
    · have hxy : x ∈ centralInterval a.1 ∩ (fun y => y+h) ⁻¹' centralInterval a.1 := ⟨hx, hy⟩
      rw [indicator_of_mem hx, indicator_of_mem hy, ccmPrimePoleEdgeDensity, indicator_of_mem hxy]
      have he := primePoleProfile_normalized_difference (primePoleProfile x) (primePoleProfile (x+h))
        (primePoleProfile_pos x) (primePoleProfile_pos (x+h)) (f x) (f (x+h))
      calc
        _ = (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (primePoleProfile x ^ 2 * (primePoleProfile (x+h) / primePoleProfile x) *
            ‖f (x+h) / (primePoleProfile (x+h) : ℂ) - f x / (primePoleProfile x : ℂ)‖ ^ 2) := by ring
        _ = _ := congrArg (fun y => (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * y) he
    · simp [indicator_of_mem hx, hy, ccmPrimePoleEdgeDensity]
  · simp [hx, ccmPrimePoleEdgeDensity]

/-- Pole-weighted energy of both oriented jumps. -/
def ccmPrimePoleJumpEnergyDensity (a : SuzukiPositiveAperture) (f : SoninL2) (x : ℝ) : ℝ :=
  (∑ j ∈ ccmPrimePoleJumpIndices a,
    primePoleProfile x ^ 2 * ccmPrimePoleJumpRate a j x *
      ‖ccmPrimePoleNormalized f (ccmPrimePoleJumpShift j x) - ccmPrimePoleNormalized f x‖ ^ 2) / 2

theorem ccmPrimePoleJumpEnergyDensity_eq_edgeSum
    (a : SuzukiPositiveAperture) (f : SoninL2) (x : ℝ) :
    ccmPrimePoleJumpEnergyDensity a f x =
      (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2*a.1)⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          (ccmPrimePoleEdgeDensity a (Real.log n) f x +
            ccmPrimePoleEdgeDensity a (-Real.log n) f x)) / 2 := by
  unfold ccmPrimePoleJumpEnergyDensity ccmPrimePoleJumpIndices
  simp only [Finset.product_eq_sprod, Finset.sum_product, Fintype.sum_bool]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [ccmPrimePoleJumpRate_mul_normalized_difference,
    ccmPrimePoleJumpRate_mul_normalized_difference]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

open HTGeometry.JumpBochner in
theorem ccmPrimePoleJumpEnergyDensity_eq_real_imag
    (a : SuzukiPositiveAperture) (f : SoninL2) (x : ℝ) :
    ccmPrimePoleJumpEnergyDensity a f x = primePoleProfile x ^ 2 *
      (energyDensity (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a)
        ccmPrimePoleJumpShift (fun y => (ccmPrimePoleNormalized f y).re)
          (fun y => (ccmPrimePoleNormalized f y).re) x +
       energyDensity (ccmPrimePoleJumpIndices a) (ccmPrimePoleJumpRate a)
        ccmPrimePoleJumpShift (fun y => (ccmPrimePoleNormalized f y).im)
          (fun y => (ccmPrimePoleNormalized f y).im) x) := by
  unfold ccmPrimePoleJumpEnergyDensity energyDensity difference
  simp only [Finset.sum_div, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem ccmPrimePoleEdgeDensity_neg_translate
    (a : SuzukiPositiveAperture) (h : ℝ) (f : SoninL2) (x : ℝ) :
    ccmPrimePoleEdgeDensity a (-h) f (x+h) = ccmPrimePoleEdgeDensity a h f x := by
  by_cases hx : x ∈ centralInterval a.1 <;> by_cases hy : x+h ∈ centralInterval a.1
  · simp only [ccmPrimePoleEdgeDensity, mem_inter_iff, mem_preimage, add_neg_cancel_right,
      hx, hy, and_self, indicator_of_mem]
    rw [norm_sub_rev, mul_comm (primePoleProfile (x+h))]
  · simp [ccmPrimePoleEdgeDensity, hx, hy]
  · simp [ccmPrimePoleEdgeDensity, hx, hy]
  · simp [ccmPrimePoleEdgeDensity, hx, hy]

theorem ccmPrimePoleEdgeEnergy_neg_shift
    (a : SuzukiPositiveAperture) (h : ℝ) (f : SoninL2) :
    ccmPrimePoleEdgeEnergy a (-h) f = ccmPrimePoleEdgeEnergy a h f := by
  unfold ccmPrimePoleEdgeEnergy
  calc
    _ = ∫ x, ccmPrimePoleEdgeDensity a (-h) f (x+h) :=
      (integral_add_right_eq_self (fun x => ccmPrimePoleEdgeDensity a (-h) f x) h).symm
    _ = _ := integral_congr_ae (Eventually.of_forall (ccmPrimePoleEdgeDensity_neg_translate a h f))

theorem integrable_ccmPrimePoleJumpEnergyDensity
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    Integrable (ccmPrimePoleJumpEnergyDensity a f.1) := by
  change Integrable (fun x => ccmPrimePoleJumpEnergyDensity a f.1 x)
  simp_rw [ccmPrimePoleJumpEnergyDensity_eq_edgeSum]
  apply Integrable.div_const
  exact integrable_finsetSum _ (fun n _ =>
    ((integrable_ccmPrimePoleEdgeDensity a _ f).add
      (integrable_ccmPrimePoleEdgeDensity a _ f)).const_mul _)

/-- The literal jump energy integrates to the existing prime Schur energy. -/
theorem integral_ccmPrimePoleJumpEnergyDensity
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (∫ x, ccmPrimePoleJumpEnergyDensity a f.1 x) = ccmPrimePoleSchurEnergy a f.1 := by
  simp_rw [ccmPrimePoleJumpEnergyDensity_eq_edgeSum]
  rw [integral_div]
  have hint (n : ℕ) : Integrable (fun x =>
      (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
        (ccmPrimePoleEdgeDensity a (Real.log n) f.1 x +
          ccmPrimePoleEdgeDensity a (-Real.log n) f.1 x)) :=
    ((integrable_ccmPrimePoleEdgeDensity a (Real.log n) f).add
      (integrable_ccmPrimePoleEdgeDensity a (-Real.log n) f)).const_mul _
  rw [integral_finsetSum _ (fun n _ => hint n)]
  unfold ccmPrimePoleSchurEnergy
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_const_mul, integral_add (integrable_ccmPrimePoleEdgeDensity a _ f)
    (integrable_ccmPrimePoleEdgeDensity a _ f)]
  change (_ * (ccmPrimePoleEdgeEnergy a (Real.log n) f.1 +
    ccmPrimePoleEdgeEnergy a (-Real.log n) f.1)) / 2 = _
  rw [ccmPrimePoleEdgeEnergy_neg_shift]
  ring

end RHTower
