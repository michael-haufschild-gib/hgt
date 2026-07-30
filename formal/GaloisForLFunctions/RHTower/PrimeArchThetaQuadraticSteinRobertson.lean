import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenRadialHierarchy
import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenRobinSteinWard

/-!
# Quadratic Stein--Robertson certificate for the first radial theta atom
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- Arbitrary integral power moment of a radial Born--Witten state. -/
def thetaCuspBornWittenRadialPowerMoment (m k n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ m * thetaCuspBornWittenRadialAmplitude k n x ^ 2

/-- Every polynomially weighted radial density is integrable. -/
theorem integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    (m k : ℕ) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ =>
      x ^ m * thetaCuspBornWittenRadialAmplitude k n x ^ 2) (Ioi 0) := by
  have hsource : IntegrableOn (fun x : ℝ =>
      x ^ (m + 2 * k) * thetaCuspSourceTerm x n) (Ioi 0) := by
    have hpoly := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
      (m + 2 * k) thetaCuspSeedPolynomial hn
    apply hpoly.congr
    filter_upwards [] with x
    rw [← congrFun (thetaCuspSourceTerm_eq_polynomialAtom n) x]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hscaled := hsource.const_mul (Real.pi)⁻¹
  apply hscaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hsourceEq := thetaCusp_pow_mul_sourceTerm_eq_pi_mul_radialAmplitude_sq
    k hn hx.le
  calc
    Real.pi⁻¹ * (x ^ (m + 2 * k) * thetaCuspSourceTerm x n) =
        Real.pi⁻¹ * (x ^ m *
          (x ^ (2 * k) * thetaCuspSourceTerm x n)) := by
      rw [pow_add]
      ring
    _ = Real.pi⁻¹ * (x ^ m *
          (Real.pi * thetaCuspBornWittenRadialAmplitude k n x ^ 2)) := by
      rw [hsourceEq]
    _ = x ^ m * thetaCuspBornWittenRadialAmplitude k n x ^ 2 := by
      field_simp [hpi]

/-- A squared Morse-scale insertion remains inside the polynomial--Gaussian integrability
class already available for the theta source. -/
theorem integrableOn_pow_mul_thetaCuspMorseScale_sq_mul_source (m : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ m * thetaCuspMorseScale 1 x ^ 2 * thetaCuspSourceTerm x 1)
      (Ioi 0) := by
  have h := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    m (C (Real.pi ^ 2) * X ^ 4 * thetaCuspSeedPolynomial)
      (n := 1) (by norm_num)
  apply h.congr
  filter_upwards [] with x
  rw [congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1) x]
  simp only [thetaCuspPolynomialAtom, eval_mul, eval_C, eval_pow, eval_X,
    thetaCuspMorseScale, Nat.cast_one, one_mul]
  ring

/-- Even power moments recover the existing radial raw moments. -/
theorem thetaCuspBornWittenRadialPowerMoment_even
    (j k n : ℕ) :
    thetaCuspBornWittenRadialPowerMoment (2 * j) k n =
      thetaCuspBornWittenRadialRawMoment j k n := by
  rfl

/-- The quadratic vector field selected by the first-atom quantum bootstrap. -/
def thetaCuspQuadraticSteinField (x : ℝ) : ℝ :=
  x - x ^ 2 / 2

/-- Derivative of the quadratic Stein field. -/
def thetaCuspQuadraticSteinFieldDerivative (x : ℝ) : ℝ :=
  1 - x

/-- Symmetric first-order score of the quadratic field in the `k=1,n=1` radial state. -/
def thetaCuspFirstRadialQuadraticSteinScore (x : ℝ) : ℝ :=
  HTGeometry.halfLineSteinScore
    thetaCuspQuadraticSteinField
    thetaCuspQuadraticSteinFieldDerivative
    (thetaCuspBornWittenRadialSuperpotential 1 1) x

/-- Squared norm of the quadratic symmetric generator. -/
def thetaCuspFirstRadialQuadraticSteinEnergy : ℝ :=
  ∫ x : ℝ in Ioi 0,
    thetaCuspFirstRadialQuadraticSteinScore x ^ 2 *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- Curvature/field-gradient side of the quadratic local-virial identity. -/
def thetaCuspFirstRadialQuadraticVirialEnergy : ℝ :=
  ∫ x : ℝ in Ioi 0,
    ((1 / 2 : ℝ) * thetaCuspQuadraticSteinField x ^ 2 *
          thetaCuspBornWittenRadialCurvature 1 1 x +
        (1 / 4 : ℝ) * thetaCuspQuadraticSteinFieldDerivative x ^ 2) *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- Exact local-virial current whose endpoint flux distinguishes the half-line identity from its
boundaryless whole-line counterpart. -/
def thetaCuspFirstRadialQuadraticVirialCurrent (x : ℝ) : ℝ :=
  thetaCuspQuadraticSteinField x ^ 2 *
    thetaCuspBornWittenRadialSuperpotential 1 1 x *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- Position-score coupling selected by `P(x)=x-x^2/2`. -/
def thetaCuspFirstRadialQuadraticSteinCoupling : ℝ :=
  ∫ x : ℝ in Ioi 0,
    (x ^ 2 - x ^ 3 / 2) *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2

/-- The quadratic score has no radial `1/x` singularity on the open half-line. -/
theorem thetaCuspFirstRadialQuadraticSteinScore_eq
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstRadialQuadraticSteinScore x =
      thetaCuspQuadraticSteinField x *
          thetaCuspBornWittenSuperpotential 1 x + x - 3 / 2 := by
  simp only [thetaCuspFirstRadialQuadraticSteinScore,
    HTGeometry.halfLineSteinScore,
    thetaCuspQuadraticSteinField,
    thetaCuspQuadraticSteinFieldDerivative,
    thetaCuspBornWittenRadialSuperpotential]
  field_simp [hx.ne']
  ring

/-- The rational Born--Witten superpotential causes no new tail hypothesis: on the positive
half-line the squared quadratic score is bounded by four polynomial--Morse monomials. -/
theorem thetaCuspFirstRadialQuadraticSteinScore_sq_le {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstRadialQuadraticSteinScore x ^ 2 ≤
      4 * x ^ 2 * thetaCuspMorseScale 1 x ^ 2 +
      x ^ 4 * thetaCuspMorseScale 1 x ^ 2 +
      4 * x ^ 2 + 4 * thetaCuspMorseScale 1 x ^ 2 := by
  let t := thetaCuspMorseScale 1 x
  have ht : 3 < t := by
    dsimp [t, thetaCuspMorseScale]
    have hexp : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
    have hexpSq : 1 < Real.exp x ^ 2 := by
      nlinarith [sq_nonneg (Real.exp x - 1)]
    have hmul : Real.pi ≤ Real.pi * Real.exp x ^ 2 :=
      le_mul_of_one_le_right Real.pi_pos.le hexpSq.le
    simpa only [Nat.cast_one, one_mul] using Real.pi_gt_three.trans_le hmul
  have hq : 1 ≤ t - 3 / 2 := by linarith
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.le
  have hq0 : 0 ≤ t - 3 / 2 := le_trans (by norm_num) hq
  have hdiv0 : 0 ≤ t / (t - 3 / 2) := div_nonneg ht0 hq0
  have hdiv_le : t / (t - 3 / 2) ≤ t := div_le_self ht0 hq
  have hWform : thetaCuspBornWittenSuperpotential 1 x =
      t - 5 / 4 - t / (t - 3 / 2) := by
    simp only [thetaCuspBornWittenSuperpotential,
      thetaCuspMorseSuperpotential, thetaCuspBornWittenWeight_eq]
    rfl
  have hWabs : |thetaCuspBornWittenSuperpotential 1 x| ≤ t := by
    rw [hWform]
    apply (abs_le).2
    constructor <;> nlinarith
  have hPabs : |thetaCuspQuadraticSteinField x| ≤ x + x ^ 2 / 2 := by
    unfold thetaCuspQuadraticSteinField
    calc
      |x - x ^ 2 / 2| ≤ |x| + |x ^ 2 / 2| := abs_sub _ _
      _ = x + x ^ 2 / 2 := by
        rw [abs_of_pos hx, abs_of_nonneg (by positivity)]
  have hshiftabs : |x - 3 / 2| ≤ x + t := by
    calc
      |x - 3 / 2| ≤ |x| + |(3 / 2 : ℝ)| := abs_sub _ _
      _ ≤ x + t := by
        rw [abs_of_pos hx, abs_of_pos (by norm_num)]
        linarith
  let A := x * t + x ^ 2 * t / 2 + x + t
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hscoreAbs : |thetaCuspFirstRadialQuadraticSteinScore x| ≤ A := by
    rw [thetaCuspFirstRadialQuadraticSteinScore_eq hx]
    calc
      |thetaCuspQuadraticSteinField x *
          thetaCuspBornWittenSuperpotential 1 x + x - 3 / 2| ≤
          |thetaCuspQuadraticSteinField x *
            thetaCuspBornWittenSuperpotential 1 x| + |x - 3 / 2| := by
              rw [show
                thetaCuspQuadraticSteinField x *
                    thetaCuspBornWittenSuperpotential 1 x + x - 3 / 2 =
                  thetaCuspQuadraticSteinField x *
                    thetaCuspBornWittenSuperpotential 1 x + (x - 3 / 2) by
                ring]
              exact abs_add_le _ _
      _ = |thetaCuspQuadraticSteinField x| *
            |thetaCuspBornWittenSuperpotential 1 x| + |x - 3 / 2| := by
              rw [abs_mul]
      _ ≤ (x + x ^ 2 / 2) * t + (x + t) := by
              exact add_le_add
                (mul_le_mul hPabs hWabs (abs_nonneg _) (by positivity)) hshiftabs
      _ = A := by
        dsimp [A]
        ring
  have hscoreSqA : thetaCuspFirstRadialQuadraticSteinScore x ^ 2 ≤ A ^ 2 := by
    apply (sq_le_sq).2
    simpa only [abs_of_nonneg hA0] using hscoreAbs
  have hfour : A ^ 2 ≤
      4 * x ^ 2 * t ^ 2 + x ^ 4 * t ^ 2 + 4 * x ^ 2 + 4 * t ^ 2 := by
    dsimp [A]
    nlinarith [sq_nonneg (x * t - x ^ 2 * t / 2),
      sq_nonneg (x * t - x), sq_nonneg (x * t - t),
      sq_nonneg (x ^ 2 * t / 2 - x),
      sq_nonneg (x ^ 2 * t / 2 - t), sq_nonneg (x - t)]
  exact hscoreSqA.trans (by simpa only [t] using hfour)

/-- The radial density obeys the exact logarithmic derivative equation. -/
theorem hasDerivAt_thetaCuspFirstRadialDensity {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => thetaCuspBornWittenRadialAmplitude 1 1 y ^ 2)
      (-2 * thetaCuspBornWittenRadialSuperpotential 1 1 x *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) x := by
  have hraw := (hasDerivAt_thetaCuspBornWittenRadialAmplitude
    (k := 1) (n := 1) (by norm_num) hx).pow 2
  simpa only [Pi.pow_apply] using!
    hraw.congr_deriv
      (g' := -2 * thetaCuspBornWittenRadialSuperpotential 1 1 x *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (by ring)

/-- The quadratic field has the displayed derivative. -/
theorem hasDerivAt_thetaCuspQuadraticSteinField (x : ℝ) :
    HasDerivAt thetaCuspQuadraticSteinField
      (thetaCuspQuadraticSteinFieldDerivative x) x := by
  unfold thetaCuspQuadraticSteinField thetaCuspQuadraticSteinFieldDerivative
  have hraw := (hasDerivAt_id x).sub
    ((hasDerivAt_id x).pow 2 |>.div_const 2)
  simpa only [Pi.sub_apply, Pi.pow_apply, id_eq] using!
    hraw.congr_deriv (g' := 1 - x) (by norm_num)

/-- The quadratic score energy is pointwise the radial curvature energy minus the derivative of
one explicit virial current.  The identity removes the squared rational Born--Witten
superpotential before any estimate is made. -/
theorem thetaCuspFirstRadialQuadraticStein_localVirial
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstRadialQuadraticSteinScore x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 =
      ((1 / 2 : ℝ) * thetaCuspQuadraticSteinField x ^ 2 *
            thetaCuspBornWittenRadialCurvature 1 1 x +
          (1 / 4 : ℝ) * thetaCuspQuadraticSteinFieldDerivative x ^ 2) *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 -
          (1 / 2 : ℝ) * deriv thetaCuspFirstRadialQuadraticVirialCurrent x := by
  have hcurrent :
      thetaCuspFirstRadialQuadraticVirialCurrent =
        fun y : ℝ =>
          thetaCuspQuadraticSteinField y ^ 2 *
            thetaCuspBornWittenRadialSuperpotential 1 1 y *
              thetaCuspBornWittenRadialAmplitude 1 1 y ^ 2 := by
    funext y
    rfl
  rw [hcurrent]
  simpa only [thetaCuspFirstRadialQuadraticSteinScore] using!
    HTGeometry.halfLineSteinScore_sq_mul_eq_curvature_sub_deriv
      (hasDerivAt_thetaCuspQuadraticSteinField x)
      (hasDerivAt_thetaCuspBornWittenRadialSuperpotential
        (k := 1) (n := 1) (by norm_num) hx)
      (hasDerivAt_thetaCuspFirstRadialDensity hx)

/-- The virial current has no hidden rational denominator: multiplication by the exact radial
density turns it into two polynomial--Gaussian theta atoms. -/
theorem thetaCuspFirstRadialQuadraticVirialCurrent_eq
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstRadialQuadraticVirialCurrent x =
      -(2 * Real.pi)⁻¹ * thetaCuspQuadraticSteinField x ^ 2 * x ^ 2 *
          thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) 1 x -
        Real.pi⁻¹ * thetaCuspQuadraticSteinField x ^ 2 * x *
          thetaCuspSourceTerm x 1 := by
  have hB := thetaCuspBornWittenSuperpotential_mul_amplitude_sq_eq_polynomialAtom
    (n := 1) (by norm_num) hx
  have hsource := thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq
    (n := 1) (by norm_num) hx.le
  have hamp : thetaCuspBornWittenAmplitude 1 x ^ 2 =
      Real.pi⁻¹ * thetaCuspSourceTerm x 1 := by
    field_simp [Real.pi_ne_zero]
    nlinarith
  simp only [thetaCuspFirstRadialQuadraticVirialCurrent,
    thetaCuspBornWittenRadialSuperpotential,
    thetaCuspBornWittenRadialAmplitude_sq, Nat.reduceMul, Nat.cast_one]
  rw [show
      thetaCuspQuadraticSteinField x ^ 2 *
          (thetaCuspBornWittenSuperpotential 1 x - (1 : ℝ) / x) *
            (x ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) =
        thetaCuspQuadraticSteinField x ^ 2 *
          (x ^ 2 * (thetaCuspBornWittenSuperpotential 1 x *
            thetaCuspBornWittenAmplitude 1 x ^ 2) -
          x * thetaCuspBornWittenAmplitude 1 x ^ 2) by
      field_simp [hx.ne'],
    hB, hamp]
  ring

theorem hasDerivAt_thetaCuspFirstRadialQuadraticVirialCurrent
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspFirstRadialQuadraticVirialCurrent
      ((2 * thetaCuspQuadraticSteinField x *
              thetaCuspQuadraticSteinFieldDerivative x *
              thetaCuspBornWittenRadialSuperpotential 1 1 x +
            thetaCuspQuadraticSteinField x ^ 2 *
              thetaCuspBornWittenRadialCurvature 1 1 x -
            2 * thetaCuspQuadraticSteinField x ^ 2 *
              thetaCuspBornWittenRadialSuperpotential 1 1 x ^ 2) *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) x := by
  have hcurrent :
      thetaCuspFirstRadialQuadraticVirialCurrent =
        fun y : ℝ =>
          thetaCuspQuadraticSteinField y ^ 2 *
            thetaCuspBornWittenRadialSuperpotential 1 1 y *
              thetaCuspBornWittenRadialAmplitude 1 1 y ^ 2 := by
    funext y
    rfl
  rw [hcurrent]
  simpa only using!
    HTGeometry.hasDerivAt_halfLineSteinVirialCurrent
      (hasDerivAt_thetaCuspQuadraticSteinField x)
      (hasDerivAt_thetaCuspBornWittenRadialSuperpotential
        (k := 1) (n := 1) (by norm_num) hx)
      (hasDerivAt_thetaCuspFirstRadialDensity hx)

theorem thetaCuspFirstRadialQuadraticVirialCurrent_tendsto_zero :
    Tendsto thetaCuspFirstRadialQuadraticVirialCurrent (𝓝[>] 0) (𝓝 0) := by
  let g : ℝ → ℝ := fun x =>
    -(2 * Real.pi)⁻¹ * thetaCuspQuadraticSteinField x ^ 2 * x ^ 2 *
        thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) 1 x -
      Real.pi⁻¹ * thetaCuspQuadraticSteinField x ^ 2 * x * thetaCuspSourceTerm x 1
  have hatom : Continuous
      (thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) 1) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspPolynomialAtom
        (thetaCuspLogDerivativePolynomial 1) 1 x).continuousAt
  have hsource : Continuous (fun x : ℝ => thetaCuspSourceTerm x 1) := by
    rw [thetaCuspSourceTerm_eq_polynomialAtom]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspPolynomialAtom thetaCuspSeedPolynomial 1 x).continuousAt
  have hP : Continuous thetaCuspQuadraticSteinField := by
    unfold thetaCuspQuadraticSteinField
    fun_prop
  have hg : Continuous g := by
    dsimp only [g]
    fun_prop
  have hgt : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have h := (hg.tendsto 0).mono_left (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    have hg0 : g 0 = 0 := by
      dsimp [g, thetaCuspQuadraticSteinField]
      ring
    rw [hg0] at h
    exact h
  apply Tendsto.congr' _ hgt
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (thetaCuspFirstRadialQuadraticVirialCurrent_eq hx).symm

theorem thetaCuspFirstRadialQuadraticVirialCurrent_tendsto_atTop_zero :
    Tendsto thetaCuspFirstRadialQuadraticVirialCurrent atTop (𝓝 0) := by
  let A : ℝ → ℝ :=
    thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial 1) 1
  let S : ℝ → ℝ := fun x => thetaCuspSourceTerm x 1
  let g : ℝ → ℝ := fun x =>
    -(2 * Real.pi)⁻¹ * thetaCuspQuadraticSteinField x ^ 2 * x ^ 2 * A x -
      Real.pi⁻¹ * thetaCuspQuadraticSteinField x ^ 2 * x * S x
  have hA4 := pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    4 (thetaCuspLogDerivativePolynomial 1) (n := 1) (by norm_num)
  have hA5 := pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    5 (thetaCuspLogDerivativePolynomial 1) (n := 1) (by norm_num)
  have hA6 := pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
    6 (thetaCuspLogDerivativePolynomial 1) (n := 1) (by norm_num)
  have hfirst0 := (hA4.sub hA5).add (hA6.const_mul (1 / 4 : ℝ))
  have hfirst : Tendsto
      (fun x : ℝ => thetaCuspQuadraticSteinField x ^ 2 * x ^ 2 * A x)
      atTop (𝓝 0) := by
    convert hfirst0 using 1
    · funext x
      dsimp [A, thetaCuspQuadraticSteinField]
      ring
    · ring_nf
  have hS3 : Tendsto (fun x : ℝ => x ^ 3 * S x) atTop (𝓝 0) := by
    simpa only [S, ← congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1)] using
      pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
        3 thetaCuspSeedPolynomial (n := 1) (by norm_num)
  have hS4 : Tendsto (fun x : ℝ => x ^ 4 * S x) atTop (𝓝 0) := by
    simpa only [S, ← congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1)] using
      pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
        4 thetaCuspSeedPolynomial (n := 1) (by norm_num)
  have hS5 : Tendsto (fun x : ℝ => x ^ 5 * S x) atTop (𝓝 0) := by
    simpa only [S, ← congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1)] using
      pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
        5 thetaCuspSeedPolynomial (n := 1) (by norm_num)
  have hsecond0 := (hS3.sub hS4).add (hS5.const_mul (1 / 4 : ℝ))
  have hsecond : Tendsto
      (fun x : ℝ => thetaCuspQuadraticSteinField x ^ 2 * x * S x)
      atTop (𝓝 0) := by
    convert hsecond0 using 1
    · funext x
      dsimp [thetaCuspQuadraticSteinField]
      ring
    · ring_nf
  have hg0 := (hfirst.const_mul (-(2 * Real.pi)⁻¹)).sub
    (hsecond.const_mul Real.pi⁻¹)
  have hg : Tendsto g atTop (𝓝 0) := by
    convert hg0 using 1
    · funext x
      dsimp [g]
      ring
    · ring_nf
  apply Tendsto.congr' _ hg
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (thetaCuspFirstRadialQuadraticVirialCurrent_eq hx).symm

end

end RHTower

namespace RHTower

noncomputable section

/-- Unnormalized centered quadratic observable for the first radial atom. -/
def thetaCuspFirstRadialCenteredQuadratic (x : ℝ) : ℝ :=
  thetaCuspBornWittenRadialPowerMoment 0 1 1 * x ^ 2 -
    thetaCuspBornWittenRadialPowerMoment 2 1 1

/-- The centered quadratic observable has finite squared norm. -/
theorem integrableOn_thetaCuspFirstRadialCenteredQuadratic_sq :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialCenteredQuadratic x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (Ioi 0) := by
  let J0 := thetaCuspBornWittenRadialPowerMoment 0 1 1
  let J1 := thetaCuspBornWittenRadialPowerMoment 2 1 1
  have h0 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    0 1 (n := 1) (by norm_num)
  have h2 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    2 1 (n := 1) (by norm_num)
  have h4 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    4 1 (n := 1) (by norm_num)
  have hcomb := ((h4.const_mul (J0 ^ 2)).sub
    (h2.const_mul (2 * J0 * J1))).add (h0.const_mul (J1 ^ 2))
  apply hcomb.congr
  filter_upwards [] with x
  simp only [thetaCuspFirstRadialCenteredQuadratic, J0, J1,
    Pi.add_apply, Pi.sub_apply, pow_zero, one_mul]
  ring

@[fun_prop]
theorem continuous_thetaCuspMorseScale (n : ℕ) :
    Continuous (thetaCuspMorseScale n) := by
  unfold thetaCuspMorseScale
  fun_prop

@[fun_prop]
theorem continuous_thetaCuspMorseSuperpotential (A : ℝ) (n : ℕ) :
    Continuous (thetaCuspMorseSuperpotential A n) := by
  unfold thetaCuspMorseSuperpotential
  fun_prop

/-- The first radial amplitude is measurable. -/
theorem measurable_thetaCuspFirstRadialAmplitude :
    Measurable (thetaCuspBornWittenRadialAmplitude 1 1) := by
  unfold thetaCuspBornWittenRadialAmplitude thetaCuspBornWittenAmplitude
    thetaCuspBornWittenWeight thetaCuspMorseSuperpotential
    thetaCuspMorseScale thetaCuspMorseGroundState thetaCuspMorseZeroMode
  fun_prop

/-- The first radial quadratic score is measurable. -/
theorem measurable_thetaCuspFirstRadialQuadraticSteinScore :
    Measurable thetaCuspFirstRadialQuadraticSteinScore := by
  unfold thetaCuspFirstRadialQuadraticSteinScore HTGeometry.halfLineSteinScore
    thetaCuspQuadraticSteinField thetaCuspQuadraticSteinFieldDerivative
    thetaCuspBornWittenRadialSuperpotential thetaCuspBornWittenSuperpotential
    thetaCuspMorseSuperpotential thetaCuspMorseScale thetaCuspBornWittenWeight
  fun_prop

/-- A source-specific upper envelope for the first radial curvature.  Its rational term is
absorbed by the fact that the Born--Witten observable is already at least one on the positive
half-line. -/
theorem thetaCuspFirstRadialCurvature_le_scale {x : ℝ} (hx : 0 < x) :
    thetaCuspBornWittenRadialCurvature 1 1 x ≤
      5 * thetaCuspMorseScale 1 x + 1 / x ^ 2 := by
  let t := thetaCuspMorseScale 1 x
  let q := thetaCuspBornWittenWeight 1 x
  have ht : 3 < t := by
    dsimp [t, thetaCuspMorseScale]
    have hexp : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
    have hexpSq : 1 < Real.exp x ^ 2 := by
      nlinarith [sq_nonneg (Real.exp x - 1)]
    have hmul : Real.pi ≤ Real.pi * Real.exp x ^ 2 :=
      le_mul_of_one_le_right Real.pi_pos.le hexpSq.le
    simpa only [Nat.cast_one, one_mul] using Real.pi_gt_three.trans_le hmul
  have hq : 1 ≤ q := by
    dsimp [q]
    rw [thetaCuspBornWittenWeight_eq]
    dsimp [t] at ht ⊢
    linarith
  have hqSq : 1 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht.le
  have hdiv : t / q ^ 2 ≤ t := div_le_self ht0 hqSq
  have hdiv3 : 3 * t / q ^ 2 ≤ 3 * t := by
    calc
      3 * t / q ^ 2 = 3 * (t / q ^ 2) := by ring
      _ ≤ 3 * t := mul_le_mul_of_nonneg_left hdiv (by norm_num)
  dsimp [t, q] at hdiv hdiv3 ⊢
  simp only [thetaCuspBornWittenRadialCurvature,
    thetaCuspBornWittenCurvature, Nat.cast_one]
  linarith

theorem measurable_thetaCuspFirstRadialCurvature :
    Measurable (thetaCuspBornWittenRadialCurvature 1 1) := by
  unfold thetaCuspBornWittenRadialCurvature thetaCuspBornWittenCurvature
    thetaCuspBornWittenWeight thetaCuspMorseSuperpotential thetaCuspMorseScale
  fun_prop

/-- Polynomial--Gaussian envelope for the curvature form in the local-virial identity. -/
def thetaCuspFirstRadialQuadraticVirialEnergyMajorant (x : ℝ) : ℝ :=
  Real.pi⁻¹ *
    (3 * (x ^ 4 * thetaCuspMorseScale 1 x ^ 2 * thetaCuspSourceTerm x 1) +
      3 * (x ^ 6 * thetaCuspMorseScale 1 x ^ 2 * thetaCuspSourceTerm x 1) +
      x ^ 2 * thetaCuspSourceTerm x 1 + x ^ 4 * thetaCuspSourceTerm x 1)

theorem integrableOn_thetaCuspFirstRadialQuadraticVirialEnergyMajorant :
    IntegrableOn thetaCuspFirstRadialQuadraticVirialEnergyMajorant (Ioi 0) := by
  have h4t := integrableOn_pow_mul_thetaCuspMorseScale_sq_mul_source 4
  have h6t := integrableOn_pow_mul_thetaCuspMorseScale_sq_mul_source 6
  have h2 := integrableOn_pow_mul_thetaCuspSourceTerm 1 1
  have h4 := integrableOn_pow_mul_thetaCuspSourceTerm 2 1
  have hsum := (((h4t.const_mul 3).add (h6t.const_mul 3)).add h2).add h4
  have hscaled := hsum.const_mul Real.pi⁻¹
  apply hscaled.congr
  filter_upwards [] with x
  simp only [thetaCuspFirstRadialQuadraticVirialEnergyMajorant, Pi.add_apply]

theorem thetaCuspFirstRadialQuadraticVirialEnergy_integrand_nonneg
    {x : ℝ} (hx : 0 < x) :
    0 ≤
      ((1 / 2 : ℝ) * thetaCuspQuadraticSteinField x ^ 2 *
            thetaCuspBornWittenRadialCurvature 1 1 x +
          (1 / 4 : ℝ) * thetaCuspQuadraticSteinFieldDerivative x ^ 2) *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 := by
  have hcurv := thetaCuspBornWittenRadialCurvature_floor
    (k := 1) (n := 1) (by norm_num) hx
  have hcurv0 : 0 ≤ thetaCuspBornWittenRadialCurvature 1 1 x := by
    norm_num only [Nat.cast_one, one_pow, mul_one] at hcurv
    have hbase : 0 ≤ 2 * Real.pi + (1 : ℝ) / x ^ 2 := by positivity
    exact hbase.trans hcurv
  positivity

theorem thetaCuspFirstRadialQuadraticVirialEnergy_integrand_le_majorant
    {x : ℝ} (hx : 0 < x) :
    ((1 / 2 : ℝ) * thetaCuspQuadraticSteinField x ^ 2 *
          thetaCuspBornWittenRadialCurvature 1 1 x +
        (1 / 4 : ℝ) * thetaCuspQuadraticSteinFieldDerivative x ^ 2) *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 ≤
        thetaCuspFirstRadialQuadraticVirialEnergyMajorant x := by
  let t := thetaCuspMorseScale 1 x
  let P := thetaCuspQuadraticSteinField x
  let P' := thetaCuspQuadraticSteinFieldDerivative x
  let K := thetaCuspBornWittenRadialCurvature 1 1 x
  have ht : 1 ≤ t := by
    have ht3 : 3 < t := by
      dsimp [t, thetaCuspMorseScale]
      have hexp : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
      have hexpSq : 1 < Real.exp x ^ 2 := by
        nlinarith [sq_nonneg (Real.exp x - 1)]
      have hmul : Real.pi ≤ Real.pi * Real.exp x ^ 2 :=
        le_mul_of_one_le_right Real.pi_pos.le hexpSq.le
      simpa only [Nat.cast_one, one_mul] using Real.pi_gt_three.trans_le hmul
    linarith
  have hP : P ^ 2 ≤ x ^ 2 + x ^ 4 := by
    dsimp [P, thetaCuspQuadraticSteinField]
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
  have hP0 : 0 ≤ P ^ 2 := sq_nonneg P
  have hPsum0 : 0 ≤ x ^ 2 + x ^ 4 := by positivity
  have hP' : P' ^ 2 ≤ 2 + 2 * x ^ 2 := by
    dsimp [P', thetaCuspQuadraticSteinFieldDerivative]
    nlinarith [sq_nonneg (x + 1)]
  have hK := thetaCuspFirstRadialCurvature_le_scale hx
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have hfloor := thetaCuspBornWittenRadialCurvature_floor
      (k := 1) (n := 1) (by norm_num) hx
    norm_num only [Nat.cast_one, one_pow, mul_one] at hfloor
    have hbase : 0 ≤ 2 * Real.pi + (1 : ℝ) / x ^ 2 := by positivity
    exact hbase.trans hfloor
  have hPK : P ^ 2 * K ≤ (x ^ 2 + x ^ 4) * (5 * t + 1 / x ^ 2) :=
    mul_le_mul hP (by simpa only [K, t] using hK) hK0 hPsum0
  have htSq : t ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  have hAt : (x ^ 2 + x ^ 4) * t ≤ (x ^ 2 + x ^ 4) * t ^ 2 :=
    mul_le_mul_of_nonneg_left htSq hPsum0
  have hfactor :
      (1 / 2 : ℝ) * P ^ 2 * K + (1 / 4 : ℝ) * P' ^ 2 ≤
        3 * (x ^ 2 + x ^ 4) * t ^ 2 + (1 + x ^ 2) := by
    have hx0 := hx.ne'
    field_simp [hx0] at hPK ⊢
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hfactor
    (sq_nonneg (thetaCuspBornWittenRadialAmplitude 1 1 x))
  have hsource := thetaCusp_pow_mul_sourceTerm_eq_pi_mul_radialAmplitude_sq
    1 (n := 1) (by norm_num) hx.le
  have hamp : thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 =
      Real.pi⁻¹ * x ^ 2 * thetaCuspSourceTerm x 1 := by
    norm_num only [Nat.reduceMul] at hsource
    field_simp [Real.pi_ne_zero]
    nlinarith
  dsimp [P, P', K, t] at hmul
  rw [hamp] at hmul ⊢
  dsimp [thetaCuspFirstRadialQuadraticVirialEnergyMajorant]
  exact hmul.trans (le_of_eq (by ring))

/-- The curvature side of the local-virial law is integrable without an auxiliary hypothesis. -/
theorem integrableOn_thetaCuspFirstRadialQuadraticVirialEnergy :
    IntegrableOn (fun x : ℝ =>
      ((1 / 2 : ℝ) * thetaCuspQuadraticSteinField x ^ 2 *
            thetaCuspBornWittenRadialCurvature 1 1 x +
          (1 / 4 : ℝ) * thetaCuspQuadraticSteinFieldDerivative x ^ 2) *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (Ioi 0) := by
  apply Integrable.mono'
    integrableOn_thetaCuspFirstRadialQuadraticVirialEnergyMajorant
  · have hP : Measurable thetaCuspQuadraticSteinField := by
      unfold thetaCuspQuadraticSteinField
      fun_prop
    have hP' : Measurable thetaCuspQuadraticSteinFieldDerivative := by
      unfold thetaCuspQuadraticSteinFieldDerivative
      fun_prop
    have hmeas :=
      (((((hP.pow_const 2).mul measurable_thetaCuspFirstRadialCurvature).const_mul
          (1 / 2 : ℝ)).add ((hP'.pow_const 2).const_mul (1 / 4 : ℝ))).mul
        (measurable_thetaCuspFirstRadialAmplitude.pow_const 2)).aestronglyMeasurable
          (μ := volume.restrict (Ioi (0 : ℝ)))
    apply hmeas.congr
    filter_upwards [] with x
    simp only [Pi.mul_apply, Pi.add_apply]
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (thetaCuspFirstRadialQuadraticVirialEnergy_integrand_nonneg hx)]
    exact thetaCuspFirstRadialQuadraticVirialEnergy_integrand_le_majorant hx

/-- Explicit polynomial--Gaussian majorant for the squared quadratic-generator density. -/
def thetaCuspFirstRadialQuadraticSteinEnergyMajorant (x : ℝ) : ℝ :=
  Real.pi⁻¹ *
    (4 * (x ^ 4 * thetaCuspMorseScale 1 x ^ 2 * thetaCuspSourceTerm x 1) +
      (x ^ 6 * thetaCuspMorseScale 1 x ^ 2 * thetaCuspSourceTerm x 1) +
      4 * (x ^ 4 * thetaCuspSourceTerm x 1) +
      4 * (x ^ 2 * thetaCuspMorseScale 1 x ^ 2 * thetaCuspSourceTerm x 1))

theorem integrableOn_thetaCuspFirstRadialQuadraticSteinEnergyMajorant :
    IntegrableOn thetaCuspFirstRadialQuadraticSteinEnergyMajorant (Ioi 0) := by
  have h4t := integrableOn_pow_mul_thetaCuspMorseScale_sq_mul_source 4
  have h6t := integrableOn_pow_mul_thetaCuspMorseScale_sq_mul_source 6
  have h2t := integrableOn_pow_mul_thetaCuspMorseScale_sq_mul_source 2
  have h4 := integrableOn_pow_mul_thetaCuspSourceTerm 2 1
  have hsum := (((h4t.const_mul 4).add h6t).add (h4.const_mul 4)).add
    (h2t.const_mul 4)
  have hscaled := hsum.const_mul Real.pi⁻¹
  apply hscaled.congr
  filter_upwards [] with x
  simp only [thetaCuspFirstRadialQuadraticSteinEnergyMajorant, Pi.add_apply]

theorem thetaCuspFirstRadialQuadraticSteinEnergy_integrand_le_majorant
    {x : ℝ} (hx : 0 < x) :
    thetaCuspFirstRadialQuadraticSteinScore x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 ≤
      thetaCuspFirstRadialQuadraticSteinEnergyMajorant x := by
  have hscore := thetaCuspFirstRadialQuadraticSteinScore_sq_le hx
  have hmul := mul_le_mul_of_nonneg_right hscore
    (sq_nonneg (thetaCuspBornWittenRadialAmplitude 1 1 x))
  rw [thetaCuspBornWittenRadialAmplitude_sq] at hmul
  norm_num only [Nat.reduceMul] at hmul
  have hsource := thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq
    (n := 1) (by norm_num) hx.le
  have hamp : thetaCuspBornWittenAmplitude 1 x ^ 2 =
      Real.pi⁻¹ * thetaCuspSourceTerm x 1 := by
    field_simp [Real.pi_ne_zero]
    nlinarith
  rw [hamp] at hmul
  rw [thetaCuspBornWittenRadialAmplitude_sq]
  norm_num only [Nat.reduceMul]
  rw [hamp]
  dsimp [thetaCuspFirstRadialQuadraticSteinEnergyMajorant]
  exact hmul.trans (le_of_eq (by ring))

/-- The quadratic generator has finite energy without an auxiliary assumption.  Its rational
superpotential is absorbed into an explicit polynomial--Gaussian majorant. -/
theorem integrableOn_thetaCuspFirstRadialQuadraticSteinEnergy :
    IntegrableOn (fun x : ℝ =>
      thetaCuspFirstRadialQuadraticSteinScore x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (Ioi 0) := by
  apply Integrable.mono'
    integrableOn_thetaCuspFirstRadialQuadraticSteinEnergyMajorant
  · exact ((measurable_thetaCuspFirstRadialQuadraticSteinScore.pow_const 2).mul
      (measurable_thetaCuspFirstRadialAmplitude.pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact thetaCuspFirstRadialQuadraticSteinEnergy_integrand_le_majorant hx

theorem integrableOn_deriv_thetaCuspFirstRadialQuadraticVirialCurrent :
    IntegrableOn (fun x : ℝ =>
      deriv thetaCuspFirstRadialQuadraticVirialCurrent x) (Ioi 0) := by
  have hdiff := integrableOn_thetaCuspFirstRadialQuadraticVirialEnergy.sub
    integrableOn_thetaCuspFirstRadialQuadraticSteinEnergy
  have hscaled := hdiff.const_mul (2 : ℝ)
  apply hscaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hlocal := thetaCuspFirstRadialQuadraticStein_localVirial hx
  change 2 *
      (((1 / 2 : ℝ) * thetaCuspQuadraticSteinField x ^ 2 *
            thetaCuspBornWittenRadialCurvature 1 1 x +
          (1 / 4 : ℝ) * thetaCuspQuadraticSteinFieldDerivative x ^ 2) *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 -
      thetaCuspFirstRadialQuadraticSteinScore x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) =
        deriv thetaCuspFirstRadialQuadraticVirialCurrent x
  nlinarith

/-- Both endpoint fluxes vanish, so the exact local-virial current contributes zero after
integration over the positive half-line. -/
theorem integral_deriv_thetaCuspFirstRadialQuadraticVirialCurrent_eq_zero :
    (∫ x : ℝ in Ioi 0,
      deriv thetaCuspFirstRadialQuadraticVirialCurrent x) = 0 := by
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := fun _ : ℝ => 1) (u' := fun _ : ℝ => 0)
    (v := thetaCuspFirstRadialQuadraticVirialCurrent)
    (v' := fun x : ℝ => deriv thetaCuspFirstRadialQuadraticVirialCurrent x)
    (fun x _ => hasDerivAt_const x 1)
    (fun _ hx => by
      have h := hasDerivAt_thetaCuspFirstRadialQuadraticVirialCurrent hx
      change HasDerivAt thetaCuspFirstRadialQuadraticVirialCurrent
        (deriv thetaCuspFirstRadialQuadraticVirialCurrent _) _
      rw [h.deriv]
      exact h)
    (integrableOn_deriv_thetaCuspFirstRadialQuadraticVirialCurrent.congr_fun
      (fun x _ => by simp) measurableSet_Ioi)
    ((integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi 0)).congr_fun
      (g := (fun _ : ℝ => 0) * thetaCuspFirstRadialQuadraticVirialCurrent)
      (fun x _ => by simp) measurableSet_Ioi)
    (by
      exact Tendsto.congr'
        (Eventually.of_forall fun x => by simp)
        thetaCuspFirstRadialQuadraticVirialCurrent_tendsto_zero)
    (by
      exact Tendsto.congr'
        (Eventually.of_forall fun x => by simp)
        thetaCuspFirstRadialQuadraticVirialCurrent_tendsto_atTop_zero)
  simpa only [Pi.mul_apply, one_mul, zero_mul, integral_zero, sub_zero,
    zero_sub, neg_zero] using hibp

/-- **Integrated Stein--virial identity for the first radial theta atom.**  The open quadratic
generator energy is exactly its curvature/field-gradient form; no rational superpotential square
or boundary term remains. -/
theorem thetaCuspFirstRadialQuadraticSteinEnergy_eq_virialEnergy :
    thetaCuspFirstRadialQuadraticSteinEnergy =
      thetaCuspFirstRadialQuadraticVirialEnergy := by
  rw [thetaCuspFirstRadialQuadraticSteinEnergy,
    thetaCuspFirstRadialQuadraticVirialEnergy]
  calc
    (∫ x : ℝ in Ioi 0,
        thetaCuspFirstRadialQuadraticSteinScore x ^ 2 *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) =
        ∫ x : ℝ in Ioi 0,
          (((1 / 2 : ℝ) * thetaCuspQuadraticSteinField x ^ 2 *
                thetaCuspBornWittenRadialCurvature 1 1 x +
              (1 / 4 : ℝ) * thetaCuspQuadraticSteinFieldDerivative x ^ 2) *
            thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 -
              (1 / 2 : ℝ) *
                deriv thetaCuspFirstRadialQuadraticVirialCurrent x) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact thetaCuspFirstRadialQuadraticStein_localVirial hx
    _ = (∫ x : ℝ in Ioi 0,
          ((1 / 2 : ℝ) * thetaCuspQuadraticSteinField x ^ 2 *
                thetaCuspBornWittenRadialCurvature 1 1 x +
              (1 / 4 : ℝ) * thetaCuspQuadraticSteinFieldDerivative x ^ 2) *
            thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) := by
          rw [integral_sub integrableOn_thetaCuspFirstRadialQuadraticVirialEnergy
            (integrableOn_deriv_thetaCuspFirstRadialQuadraticVirialCurrent.const_mul
              (1 / 2 : ℝ)), integral_const_mul,
            integral_deriv_thetaCuspFirstRadialQuadraticVirialCurrent_eq_zero]
          ring

/-- The boundary current of the centered observable and quadratic field vanishes at the
Dirichlet endpoint. -/
theorem thetaCuspFirstRadialQuadraticSteinCurrent_tendsto_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspFirstRadialCenteredQuadratic x *
        thetaCuspQuadraticSteinField x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hcont : Continuous (fun x : ℝ =>
      thetaCuspFirstRadialCenteredQuadratic x *
        thetaCuspQuadraticSteinField x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) := by
    unfold thetaCuspFirstRadialCenteredQuadratic thetaCuspQuadraticSteinField
      thetaCuspBornWittenRadialAmplitude thetaCuspBornWittenAmplitude
      thetaCuspBornWittenWeight thetaCuspMorseSuperpotential
      thetaCuspMorseScale thetaCuspMorseGroundState thetaCuspMorseZeroMode
    fun_prop
  have h := (hcont.tendsto 0).mono_left
    (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  simpa [thetaCuspQuadraticSteinField] using! h

/-- The same boundary current vanishes at infinity. -/
theorem thetaCuspFirstRadialQuadraticSteinCurrent_tendsto_atTop_zero :
    Tendsto (fun x : ℝ =>
      thetaCuspFirstRadialCenteredQuadratic x *
        thetaCuspQuadraticSteinField x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)
      atTop (𝓝 0) := by
  let J0 := thetaCuspBornWittenRadialPowerMoment 0 1 1
  let J1 := thetaCuspBornWittenRadialPowerMoment 2 1 1
  have hpow (m : ℕ) : Tendsto
      (fun x : ℝ => x ^ m * thetaCuspSourceTerm x 1) atTop (𝓝 0) := by
    have h := pow_mul_thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
      m thetaCuspSeedPolynomial (n := 1) (by norm_num)
    simpa only [← congrFun (thetaCuspSourceTerm_eq_polynomialAtom 1)] using h
  have hcomb : Tendsto (fun x : ℝ =>
      Real.pi⁻¹ * (J0 * (x ^ 5 * thetaCuspSourceTerm x 1) -
        J0 / 2 * (x ^ 6 * thetaCuspSourceTerm x 1) -
        J1 * (x ^ 3 * thetaCuspSourceTerm x 1) +
        J1 / 2 * (x ^ 4 * thetaCuspSourceTerm x 1))) atTop (𝓝 0) := by
    have h := ((((((hpow 5).const_mul J0).sub
      ((hpow 6).const_mul (J0 / 2))).sub
        ((hpow 3).const_mul J1)).add
          ((hpow 4).const_mul (J1 / 2))).const_mul Real.pi⁻¹)
    simpa using h
  apply hcomb.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hsource := thetaCusp_pow_mul_sourceTerm_eq_pi_mul_radialAmplitude_sq
    1 (n := 1) (by norm_num) hx
  simp only [thetaCuspFirstRadialCenteredQuadratic,
    thetaCuspQuadraticSteinField, J0, J1]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hsource ⊢
  rw [← hsource]
  ring

/-- Exact source-specific Stein covariance of the quadratic quantum generator. -/
theorem integral_thetaCuspFirstRadialCentered_mul_quadraticSteinScore
    : (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialCenteredQuadratic x *
        thetaCuspFirstRadialQuadraticSteinScore x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) =
      thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialQuadraticSteinCoupling := by
  let hEnergyInt := integrableOn_thetaCuspFirstRadialQuadraticSteinEnergy
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let amp : ℝ → ℝ := thetaCuspBornWittenRadialAmplitude 1 1
  let f : ℝ → ℝ := thetaCuspFirstRadialCenteredQuadratic
  let score : ℝ → ℝ := thetaCuspFirstRadialQuadraticSteinScore
  have hfSq : Integrable (fun x => (f x * amp x) ^ 2) μ := by
    apply integrableOn_thetaCuspFirstRadialCenteredQuadratic_sq.congr
    filter_upwards [] with x
    simp only [f, amp]
    ring
  have hgSq : Integrable (fun x => (score x * amp x) ^ 2) μ := by
    apply hEnergyInt.congr
    filter_upwards [] with x
    simp only [score, amp]
    ring
  have hfMeas : AEStronglyMeasurable (fun x => f x * amp x) μ := by
    exact (((by
      unfold f thetaCuspFirstRadialCenteredQuadratic
      fun_prop : Continuous f)).measurable.mul
        measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hgMeas : AEStronglyMeasurable (fun x => score x * amp x) μ := by
    exact (measurable_thetaCuspFirstRadialQuadraticSteinScore.mul
      measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hfLp : MemLp (fun x => f x * amp x) 2 μ :=
    (memLp_two_iff_integrable_sq hfMeas).2 hfSq
  have hgLp : MemLp (fun x => score x * amp x) 2 μ :=
    (memLp_two_iff_integrable_sq hgMeas).2 hgSq
  have hprod := hfLp.integrable_mul hgLp
  have hleft : IntegrableOn (fun x : ℝ =>
      f x * score x * amp x ^ 2) (Ioi 0) := by
    apply hprod.congr
    filter_upwards [] with x
    simp only [Pi.mul_apply]
    ring
  have hright : IntegrableOn (fun x : ℝ =>
      (2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 * x) *
        thetaCuspQuadraticSteinField x * amp x ^ 2) (Ioi 0) := by
    have h2 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      2 1 (n := 1) (by norm_num)
    have h3 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      3 1 (n := 1) (by norm_num)
    have hcomb := (h2.const_mul
      (2 * thetaCuspBornWittenRadialPowerMoment 0 1 1)).sub
      (h3.const_mul (thetaCuspBornWittenRadialPowerMoment 0 1 1))
    apply hcomb.congr
    filter_upwards [] with x
    simp only [amp, thetaCuspQuadraticSteinField, Pi.sub_apply]
    ring
  have hstein := HTGeometry.integral_Ioi_mul_halfLineSteinScore
    (f := f)
    (f' := fun x => 2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 * x)
    (P := thetaCuspQuadraticSteinField)
    (P' := thetaCuspQuadraticSteinFieldDerivative)
    (ρ := fun x => amp x ^ 2)
    (W := thetaCuspBornWittenRadialSuperpotential 1 1)
    (fun x _ => by
      unfold f thetaCuspFirstRadialCenteredQuadratic
      have hraw := (((hasDerivAt_id x).pow 2 |>.const_mul
        (thetaCuspBornWittenRadialPowerMoment 0 1 1)).sub_const
          (thetaCuspBornWittenRadialPowerMoment 2 1 1))
      simpa only [Pi.pow_apply, id_eq] using!
        hraw.congr_deriv
          (g' := 2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 * x)
          (by norm_num; ring))
    (fun x _ => hasDerivAt_thetaCuspQuadraticSteinField x)
    (fun x hx => by
      simpa only [amp] using hasDerivAt_thetaCuspFirstRadialDensity hx)
    (by simpa only [f, score, amp, thetaCuspFirstRadialQuadraticSteinScore] using hleft)
    (by simpa only [amp] using hright)
    (by simpa only [f, amp] using
      thetaCuspFirstRadialQuadraticSteinCurrent_tendsto_zero)
    (by simpa only [f, amp] using
      thetaCuspFirstRadialQuadraticSteinCurrent_tendsto_atTop_zero)
  rw [show (fun x : ℝ =>
      (2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 * x) *
        thetaCuspQuadraticSteinField x * amp x ^ 2) =
      fun x => 2 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        ((x ^ 2 - x ^ 3 / 2) * amp x ^ 2) by
      funext x
      simp only [thetaCuspQuadraticSteinField]
      ring, integral_const_mul] at hstein
  rw [thetaCuspFirstRadialQuadraticSteinCoupling]
  dsimp [f, score, amp] at hstein
  simpa only [thetaCuspFirstRadialQuadraticSteinScore] using hstein.trans (by ring)

end

end RHTower

namespace RHTower

noncomputable section

/-- The first radial state has strictly positive mass. -/
theorem thetaCuspFirstRadialPowerMoment_zero_pos :
    0 < thetaCuspBornWittenRadialPowerMoment 0 1 1 := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let ρ : ℝ → ℝ := fun x => thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2
  have hρint : Integrable ρ μ := by
    have h := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
      0 1 (n := 1) (by norm_num)
    apply h.congr
    filter_upwards [] with x
    simp only [ρ, pow_zero, one_mul]
  have hρnonneg : 0 ≤ᵐ[μ] ρ := Eventually.of_forall fun x => sq_nonneg _
  have hsupp : Ioi (0 : ℝ) ⊆ Function.support ρ := by
    intro x hx
    exact Function.mem_support.mpr (pow_ne_zero 2
      (thetaCuspBornWittenRadialAmplitude_pos
        (k := 1) (n := 1) (by norm_num) hx).ne')
  have hμpos : 0 < μ (Ioi (0 : ℝ)) := by
    simp [μ]
  have hsupppos : 0 < μ (Function.support ρ) :=
    lt_of_lt_of_le hμpos (measure_mono hsupp)
  have hpos := (integral_pos_iff_support_of_nonneg_ae hρnonneg hρint).2 hsupppos
  simpa only [thetaCuspBornWittenRadialPowerMoment, pow_zero, one_mul, ρ, μ] using hpos

/-- Exact squared norm of the unnormalized centered quadratic observable. -/
theorem integral_thetaCuspFirstRadialCenteredQuadratic_sq :
    (∫ x : ℝ in Ioi 0,
      thetaCuspFirstRadialCenteredQuadratic x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) =
      thetaCuspBornWittenRadialPowerMoment 0 1 1 ^ 2 *
          thetaCuspBornWittenRadialPowerMoment 4 1 1 -
        thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 := by
  let J0 := thetaCuspBornWittenRadialPowerMoment 0 1 1
  let J1 := thetaCuspBornWittenRadialPowerMoment 2 1 1
  have h0 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    0 1 (n := 1) (by norm_num)
  have h2 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    2 1 (n := 1) (by norm_num)
  have h4 := integrableOn_pow_mul_thetaCuspBornWittenRadialAmplitude_sq
    4 1 (n := 1) (by norm_num)
  rw [show (fun x : ℝ =>
      thetaCuspFirstRadialCenteredQuadratic x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) =
      fun x => J0 ^ 2 *
          (x ^ 4 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) -
        (2 * J0 * J1) *
          (x ^ 2 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) +
        J1 ^ 2 *
          (x ^ 0 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) by
      funext x
      simp only [thetaCuspFirstRadialCenteredQuadratic, J0, J1,
        pow_zero, one_mul]
      ring]
  rw [show (fun x : ℝ => J0 ^ 2 *
          (x ^ 4 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) -
        (2 * J0 * J1) *
          (x ^ 2 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) +
        J1 ^ 2 *
          (x ^ 0 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) =
      (fun x => J0 ^ 2 *
          (x ^ 4 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) -
        (fun x => (2 * J0 * J1) *
          (x ^ 2 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) +
        (fun x => J1 ^ 2 *
          (x ^ 0 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]]
  change (∫ x : ℝ in Ioi 0,
      (J0 ^ 2 * (x ^ 4 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) -
        (2 * J0 * J1) *
          (x ^ 2 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) +
        J1 ^ 2 *
          (x ^ 0 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) = _
  calc
    (∫ x : ℝ in Ioi 0,
        (J0 ^ 2 * (x ^ 4 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) -
          (2 * J0 * J1) *
            (x ^ 2 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) +
          J1 ^ 2 *
            (x ^ 0 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) =
      (∫ x : ℝ in Ioi 0,
        J0 ^ 2 * (x ^ 4 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) -
          (2 * J0 * J1) *
            (x ^ 2 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) +
        ∫ x : ℝ in Ioi 0,
          J1 ^ 2 *
            (x ^ 0 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) := by
              exact integral_add
                ((h4.const_mul (J0 ^ 2)).sub
                  (h2.const_mul (2 * J0 * J1)))
                (h0.const_mul (J1 ^ 2))
    _ = ((∫ x : ℝ in Ioi 0,
          J0 ^ 2 * (x ^ 4 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) -
        ∫ x : ℝ in Ioi 0,
          (2 * J0 * J1) *
            (x ^ 2 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2)) +
        ∫ x : ℝ in Ioi 0,
          J1 ^ 2 *
            (x ^ 0 * thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) := by
              rw [integral_sub (h4.const_mul (J0 ^ 2))
                (h2.const_mul (2 * J0 * J1))]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul, integral_const_mul]
      simp only [thetaCuspBornWittenRadialPowerMoment, J0, J1]
      ring

/-- **Stein–Robertson bound for an arbitrary radial score.**  Cauchy–Schwarz against the
Born–Witten radial amplitude: for any measurable score `ψ` whose amplitude-weighted square is
integrable, the squared coupling of `ψ` with the centred quadratic is bounded by the centred
quadratic's own weighted variance times the energy of `ψ`.  Only the score varies between
applications; the left factor is the fixed moment combination `m₀²m₄ − m₀m₂²`. -/
theorem thetaCuspFirstRadialSteinRobertson_of_score
    {ψ : ℝ → ℝ} (hψMeas : Measurable ψ)
    (hψSq : Integrable (fun x => ψ x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2) (volume.restrict (Ioi 0)))
    {coupling energy : ℝ}
    (hcoupling : (∫ x, thetaCuspFirstRadialCenteredQuadratic x * ψ x *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 ∂(volume.restrict (Ioi 0))) =
      thetaCuspBornWittenRadialPowerMoment 0 1 1 * coupling)
    (henergy : (∫ x, ψ x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 ∂(volume.restrict (Ioi 0))) = energy) :
    (thetaCuspBornWittenRadialPowerMoment 0 1 1 * coupling) ^ 2 ≤
      (thetaCuspBornWittenRadialPowerMoment 0 1 1 ^ 2 *
          thetaCuspBornWittenRadialPowerMoment 4 1 1 -
        thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2) * energy := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x => thetaCuspFirstRadialCenteredQuadratic x *
    thetaCuspBornWittenRadialAmplitude 1 1 x
  let g : ℝ → ℝ := fun x => ψ x * thetaCuspBornWittenRadialAmplitude 1 1 x
  have hfMeas : AEStronglyMeasurable f μ := by
    exact (((by
      unfold thetaCuspFirstRadialCenteredQuadratic
      fun_prop : Continuous thetaCuspFirstRadialCenteredQuadratic)).measurable.mul
        measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hgMeas : AEStronglyMeasurable g μ :=
    (hψMeas.mul measurable_thetaCuspFirstRadialAmplitude).aestronglyMeasurable
  have hfSq : Integrable (fun x => f x ^ 2) μ := by
    apply integrableOn_thetaCuspFirstRadialCenteredQuadratic_sq.congr
    filter_upwards [] with x
    simp only [f]
    ring
  have hgSq : Integrable (fun x => g x ^ 2) μ := by
    apply hψSq.congr
    filter_upwards [] with x
    simp only [g]
    ring
  have hcs := HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
    hfMeas hgMeas hfSq hgSq
  have hfg : (∫ x, f x * g x ∂μ) =
      thetaCuspBornWittenRadialPowerMoment 0 1 1 * coupling := by
    rw [show (fun x => f x * g x) = fun x =>
        thetaCuspFirstRadialCenteredQuadratic x * ψ x *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 by
      funext x
      simp only [f, g]
      ring]
    exact hcoupling
  have hf2 : (∫ x, f x ^ 2 ∂μ) =
      thetaCuspBornWittenRadialPowerMoment 0 1 1 ^ 2 *
          thetaCuspBornWittenRadialPowerMoment 4 1 1 -
        thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 := by
    rw [show (fun x => f x ^ 2) = fun x =>
        thetaCuspFirstRadialCenteredQuadratic x ^ 2 *
          thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 by
      funext x
      simp only [f]
      ring]
    exact integral_thetaCuspFirstRadialCenteredQuadratic_sq
  have hg2 : (∫ x, g x ^ 2 ∂μ) = energy := by
    rw [show (fun x => g x ^ 2) = fun x => ψ x ^ 2 *
        thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2 by
      funext x
      simp only [g]
      ring]
    exact henergy
  rwa [hfg, hf2, hg2] at hcs


/-- Quadratic-field Robertson uncertainty for the exact first radial theta state. -/
theorem thetaCuspFirstRadialQuadraticSteinRobertson
    : (thetaCuspBornWittenRadialPowerMoment 0 1 1 *
        thetaCuspFirstRadialQuadraticSteinCoupling) ^ 2 ≤
      (thetaCuspBornWittenRadialPowerMoment 0 1 1 ^ 2 *
          thetaCuspBornWittenRadialPowerMoment 4 1 1 -
        thetaCuspBornWittenRadialPowerMoment 0 1 1 *
          thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2) *
        thetaCuspFirstRadialQuadraticSteinEnergy := by
  refine thetaCuspFirstRadialSteinRobertson_of_score
    measurable_thetaCuspFirstRadialQuadraticSteinScore ?_
    integral_thetaCuspFirstRadialCentered_mul_quadraticSteinScore ?_
  · exact integrableOn_thetaCuspFirstRadialQuadraticSteinEnergy
  · rw [thetaCuspFirstRadialQuadraticSteinEnergy]

end

end RHTower

namespace RHTower

noncomputable section

/-- Finite quadratic generator energy is automatically strictly positive. -/
theorem thetaCuspFirstRadialQuadraticSteinEnergy_pos
    : 0 < thetaCuspFirstRadialQuadraticSteinEnergy := by
  let hEnergyInt := integrableOn_thetaCuspFirstRadialQuadraticSteinEnergy
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let e : ℝ → ℝ := fun x =>
    thetaCuspFirstRadialQuadraticSteinScore x ^ 2 *
      thetaCuspBornWittenRadialAmplitude 1 1 x ^ 2
  have hscore2 : thetaCuspFirstRadialQuadraticSteinScore 2 = 1 / 2 := by
    norm_num [thetaCuspFirstRadialQuadraticSteinScore,
      HTGeometry.halfLineSteinScore, thetaCuspQuadraticSteinField,
      thetaCuspQuadraticSteinFieldDerivative]
  have hamp2 : 0 < thetaCuspBornWittenRadialAmplitude 1 1 2 :=
    thetaCuspBornWittenRadialAmplitude_pos (k := 1) (n := 1)
      (by norm_num) (by norm_num)
  have he2 : 0 < e 2 := by
    dsimp [e]
    rw [hscore2]
    positivity
  have hWcont : ContinuousAt
      (thetaCuspBornWittenRadialSuperpotential 1 1) 2 :=
    (hasDerivAt_thetaCuspBornWittenRadialSuperpotential
      (k := 1) (n := 1) (by norm_num) (by norm_num)).continuousAt
  have hampcont : ContinuousAt
      (thetaCuspBornWittenRadialAmplitude 1 1) 2 :=
    (hasDerivAt_thetaCuspBornWittenRadialAmplitude
      (k := 1) (n := 1) (by norm_num) (by norm_num)).continuousAt
  have hPcont : ContinuousAt thetaCuspQuadraticSteinField 2 :=
    (hasDerivAt_thetaCuspQuadraticSteinField 2).continuousAt
  have hP'cont : ContinuousAt thetaCuspQuadraticSteinFieldDerivative 2 := by
    unfold thetaCuspQuadraticSteinFieldDerivative
    fun_prop
  have hscorecont : ContinuousAt thetaCuspFirstRadialQuadraticSteinScore 2 := by
    unfold thetaCuspFirstRadialQuadraticSteinScore HTGeometry.halfLineSteinScore
    fun_prop
  have hecont : ContinuousAt e 2 := by
    dsimp [e]
    exact (hscorecont.pow 2).mul (hampcont.pow 2)
  have hne : ∀ᶠ x in 𝓝 (2 : ℝ), e x ≠ 0 :=
    hecont.eventually_ne he2.ne'
  have hposmem : Function.support e ∩ Ioi (0 : ℝ) ∈ 𝓝 (2 : ℝ) := by
    filter_upwards [hne, Ioi_mem_nhds (by norm_num : (0 : ℝ) < 2)] with x hx hxi
    exact ⟨Function.mem_support.mpr hx, hxi⟩
  have hvolpos : 0 < volume (Function.support e ∩ Ioi (0 : ℝ)) :=
    Measure.measure_pos_of_mem_nhds volume hposmem
  have heMeas : Measurable e := by
    exact ((measurable_thetaCuspFirstRadialQuadraticSteinScore.pow_const 2).mul
      (measurable_thetaCuspFirstRadialAmplitude.pow_const 2))
  have hsupppos : 0 < μ (Function.support e) := by
    change 0 < (volume.restrict (Ioi (0 : ℝ))) (Function.support e)
    rw [Measure.restrict_apply (measurableSet_support heMeas)]
    exact hvolpos
  have henonneg : 0 ≤ᵐ[μ] e := Eventually.of_forall fun x => by
    dsimp [e]
    positivity
  have hpos := (integral_pos_iff_support_of_nonneg_ae henonneg hEnergyInt).2 hsupppos
  dsimp [e] at hpos
  rw [thetaCuspFirstRadialQuadraticSteinEnergy]
  exact hpos

theorem thetaCuspFirstRadialQuadraticVirialEnergy_pos :
    0 < thetaCuspFirstRadialQuadraticVirialEnergy := by
  rw [← thetaCuspFirstRadialQuadraticSteinEnergy_eq_virialEnergy]
  exact thetaCuspFirstRadialQuadraticSteinEnergy_pos

end

end RHTower

namespace RHTower

noncomputable section

/-- The single source-specific energy certificate selected by the quadratic Stein field. -/
def ThetaCuspFirstRadialQuadraticSteinEnergyCertificate : Prop :=
  (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
        thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialQuadraticSteinEnergy ≤
    9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
      thetaCuspFirstRadialQuadraticSteinCoupling ^ 2

/-- Curvature-form replacement for the quadratic score certificate.  Unlike the original form,
the integrand is linear in the already-positive radial curvature and contains no square of the
rational Born--Witten superpotential. -/
def ThetaCuspFirstRadialQuadraticVirialEnergyCertificate : Prop :=
  (14 * (3005 / 2997 : ℝ) ^ 2 - 9) *
        thetaCuspBornWittenRadialPowerMoment 2 1 1 ^ 2 *
          thetaCuspFirstRadialQuadraticVirialEnergy ≤
    9 * thetaCuspBornWittenRadialPowerMoment 0 1 1 *
      thetaCuspFirstRadialQuadraticSteinCoupling ^ 2

theorem quadraticSteinEnergyCertificate_iff_virialEnergyCertificate :
    ThetaCuspFirstRadialQuadraticSteinEnergyCertificate ↔
      ThetaCuspFirstRadialQuadraticVirialEnergyCertificate := by
  rw [ThetaCuspFirstRadialQuadraticSteinEnergyCertificate,
    ThetaCuspFirstRadialQuadraticVirialEnergyCertificate,
    thetaCuspFirstRadialQuadraticSteinEnergy_eq_virialEnergy]

/-- The quadratic Stein energy certificate discharges the open upper first-atom ratio. -/
theorem thetaCusp_firstRadial_upper_of_quadraticSteinEnergyCertificate
    (hcert : ThetaCuspFirstRadialQuadraticSteinEnergyCertificate) :
    14 * ((3005 / 2997 : ℝ) *
        thetaCuspBornWittenRadialRawMoment 1 1 1) ^ 2 ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 := by
  let hEnergy := hcert
  let J0 := thetaCuspBornWittenRadialPowerMoment 0 1 1
  let J1 := thetaCuspBornWittenRadialPowerMoment 2 1 1
  let J2 := thetaCuspBornWittenRadialPowerMoment 4 1 1
  let C := thetaCuspFirstRadialQuadraticSteinCoupling
  let E := thetaCuspFirstRadialQuadraticSteinEnergy
  let c := 14 * (3005 / 2997 : ℝ) ^ 2 - 9
  have hJ0 : 0 < J0 := thetaCuspFirstRadialPowerMoment_zero_pos
  have hE : 0 < E := thetaCuspFirstRadialQuadraticSteinEnergy_pos
  have hunc := thetaCuspFirstRadialQuadraticSteinRobertson
  have huncFactor : J0 * (J0 * C ^ 2) ≤
      J0 * ((J0 * J2 - J1 ^ 2) * E) := by
    dsimp [J0, J1, J2, C, E] at hunc ⊢
    convert hunc using 1 <;> ring
  have hunc' : J0 * C ^ 2 ≤ (J0 * J2 - J1 ^ 2) * E :=
    (mul_le_mul_iff_of_pos_left hJ0).mp huncFactor
  have hEnergy' : c * J1 ^ 2 * E ≤ 9 * J0 * C ^ 2 := by
    simpa only [ThetaCuspFirstRadialQuadraticSteinEnergyCertificate,
      c, J0, J1, C, E] using hEnergy
  have hchain : c * J1 ^ 2 * E ≤ 9 * ((J0 * J2 - J1 ^ 2) * E) := by
    calc
      c * J1 ^ 2 * E ≤ 9 * (J0 * C ^ 2) := by simpa only [mul_assoc] using hEnergy'
      _ ≤ 9 * ((J0 * J2 - J1 ^ 2) * E) :=
        mul_le_mul_of_nonneg_left hunc' (by norm_num : (0 : ℝ) ≤ 9)
  have hcore : c * J1 ^ 2 ≤ 9 * (J0 * J2 - J1 ^ 2) := by
    have hfactor : E * (c * J1 ^ 2) ≤ E * (9 * (J0 * J2 - J1 ^ 2)) := by
      convert hchain using 1 <;> ring
    exact (mul_le_mul_iff_of_pos_left hE).mp hfactor
  rw [← thetaCuspBornWittenRadialPowerMoment_even 0 1 1,
    ← thetaCuspBornWittenRadialPowerMoment_even 1 1 1,
    ← thetaCuspBornWittenRadialPowerMoment_even 2 1 1]
  dsimp [J0, J1, J2, c] at hcore
  norm_num only [Nat.reduceMul] at hcore ⊢
  nlinarith

/-- The new local-virial certificate feeds the existing upper first-atom consumer directly. -/
theorem thetaCusp_firstRadial_upper_of_quadraticVirialEnergyCertificate
    (hcert : ThetaCuspFirstRadialQuadraticVirialEnergyCertificate) :
    14 * ((3005 / 2997 : ℝ) *
        thetaCuspBornWittenRadialRawMoment 1 1 1) ^ 2 ≤
      9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
        thetaCuspBornWittenRadialRawMoment 2 1 1 :=
  thetaCusp_firstRadial_upper_of_quadraticSteinEnergyCertificate
    (quadraticSteinEnergyCertificate_iff_virialEnergyCertificate.mpr hcert)

/-- Direct quadratic-generator interface to the existing linear prime--archimedean Hankel
consumer.  The former upper three-moment hypothesis is replaced by one source-native energy
certificate; the independent relaxed fourth-moment condition is unchanged. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_quadraticSteinEnergy
    (hcert : ThetaCuspFirstRadialQuadraticSteinEnergyCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  exact forall_primeArchSourceTraceHankel_linear_nonneg_of_radialBornWittenAmplitude
    (thetaCusp_firstRadial_upper_of_quadraticSteinEnergyCertificate hcert) hrelaxed

/-- Direct curvature-energy interface to the existing linear prime--archimedean Hankel gate. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_quadraticVirialEnergy
    (hcert : ThetaCuspFirstRadialQuadraticVirialEnergyCertificate)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  exact forall_primeArchSourceTraceHankel_linear_nonneg_of_radialBornWittenAmplitude
    (thetaCusp_firstRadial_upper_of_quadraticVirialEnergyCertificate hcert) hrelaxed

end

end RHTower
