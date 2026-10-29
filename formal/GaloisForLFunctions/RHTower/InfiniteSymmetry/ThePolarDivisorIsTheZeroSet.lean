import GaloisForLFunctions.RHTower.InfiniteSymmetry.CurveDatumWeylPoles
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticZeta

/-!
# The polar divisor of the affine Weyl sum is the zero set: a receiver

For a curve datum with zeros in the open critical strip, the continued affine `A₁` Weyl sum on the
level-four slice is, in the band `−1 < Re s < 0`, eventually holomorphic at `s` exactly when
`s + 1` is not a zero of the datum's zeta function (`eventually_analytic_iff`). Hence:

* **Receiver form of RH for the datum** (`unitary_iff_eventually_analytic_off_critical`): the
  datum is unitary (`|β_i| = 1`) iff the continuation is eventually holomorphic at every point of
  the band off the critical hyperplane `Re s = −1/2`.
* **The polar calculus does not see purity** (`polarCalculus_does_not_force_unitarity`): the
  golden datum (`q = 5`, `β = φ, φ⁻¹`) satisfies the strip condition, so its complete Weyl sum has
  the same exact pole calculus, and it has a pole at `Re s = −1/2 + log φ / log 5`
  (`golden_offLine_pole`). The actual genus-one curve over `𝔽₃` has all its poles on the critical
  hyperplane (`actual_poles_on_critical_hyperplane`).

Continuation, functional-equation coefficients, convergence of the infinite Weyl sum and exact
pole survival therefore place the poles wherever the zeros are; a constraint on the polar divisor
is the Riemann hypothesis for the datum, not a consequence of the calculus.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower.InfiniteSymmetry

open ArithmeticCastelnuovoSeveri HTGeometry.LoopEisenstein.AffineA1

noncomputable section

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : ArithmeticCastelnuovoSeveri.CurveDatum ι)

/-! ### Poles in the left band are exactly the shifted zeros -/

/-- In `Re s < 0` the factor `1 − qT(s)` never vanishes, so `Q(s) = 0` iff `Z(s + 1)` vanishes. -/
lemma ratioDenominator_eq_zero_iff (s : ℂ) (hs : s.re < 0) :
    ratioDenominator D s = 0 ↔ (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0 := by
  unfold ratioDenominator
  rw [← zetaCoord_add_one, mul_eq_zero, or_iff_right]
  intro h
  have hq := q_pos D
  have hnorm : D.q * ‖zetaCoord D s‖ = 1 := by
    have := congrArg norm (show (D.q : ℂ) * zetaCoord D s = 1 by linear_combination -h)
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, norm_one] at this
  have hT : 1 < ‖zetaCoord D s‖ := by
    rw [norm_zetaCoord]
    apply Real.one_lt_exp_iff.mpr
    nlinarith [log_q_pos D]
  nlinarith [D.one_lt_q]

lemma not_analyticAt_of_order_neg {f : ℂ → ℂ} {s : ℂ} (h : meromorphicOrderAt f s < 0) :
    ¬ AnalyticAt ℂ f s := fun hA => absurd hA.meromorphicOrderAt_nonneg (not_le.mpr h)

lemma rootMultiplicity_pos_of_root (s : ℂ)
    (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) :
    0 < (numeratorPoly D).rootMultiplicity (zetaCoord D (s + 1)) :=
  (Polynomial.rootMultiplicity_pos (numeratorPoly_ne_zero D)).mpr hs

lemma neg_multiplicity_lt_zero (s : ℂ) (hs : (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0) :
    -(((numeratorPoly D).rootMultiplicity (zetaCoord D (s + 1)) : ℤ) : WithTop ℤ) < 0 := by
  have hm := rootMultiplicity_pos_of_root D s hs
  have hm' : (0 : ℤ) < ((numeratorPoly D).rootMultiplicity (zetaCoord D (s + 1)) : ℤ) := by
    exact_mod_cast hm
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
  exact WithTop.coe_lt_coe.mpr (by omega)

/-- **The receiver.** In the band `−1 < Re s < 0`, the continuation is holomorphic at `s` for all
strong rotations iff `s + 1` is not a zero of the datum's zeta function. -/
theorem eventually_analytic_iff (hD : StripCondition D) (s : ℂ) (hs₁ : -1 < s.re)
    (hs₀ : s.re < 0) :
    (∀ᶠ R : ℝ in atTop, AnalyticAt ℂ (continuedWeylSum D R) s) ↔
      (numeratorPoly D).eval (zetaCoord D (s + 1)) ≠ 0 := by
  constructor
  · intro h hroot
    obtain ⟨R, hA, -, hord⟩ := (h.and (continuedWeylSum_eventual_order D hD s hroot)).exists
    exact not_analyticAt_of_order_neg (hord ▸ neg_multiplicity_lt_zero D s hroot) hA
  · intro hne
    have hQ : ratioDenominator D s ≠ 0 := fun h => hne ((ratioDenominator_eq_zero_iff D s hs₀).mp h)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact continuedWeylSum_analytic D hD R hR s ⟨hs₁, by linarith⟩ hQ

/-! ### Unitarity is the location of the polar divisor -/

lemma alpha_ne_zero (hD : StripCondition D) (i : ι) : D.alpha i ≠ 0 := fun h => by
  have := (hD i).1
  rw [h, norm_zero] at this
  exact absurd this (by norm_num)

/-- The pole parameter attached to the eigenvalue `α_i`. -/
def poleParameter (i : ι) : ℂ := Complex.log (D.alpha i) / (Real.log D.q : ℂ) - 1

lemma alpha_mul_zetaCoord_poleParameter (hD : StripCondition D) (i : ι) :
    D.alpha i * zetaCoord D (poleParameter D i + 1) = 1 := by
  have hl : (Real.log D.q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (log_q_pos D).ne'
  have he : zetaCoord D (poleParameter D i + 1) = (D.alpha i)⁻¹ := by
    rw [zetaCoord, poleParameter, sub_add_cancel, neg_mul, mul_div_cancel₀ _ hl, Complex.exp_neg,
      Complex.exp_log (alpha_ne_zero D hD i)]
  rw [he, mul_inv_cancel₀ (alpha_ne_zero D hD i)]

lemma poleParameter_root (hD : StripCondition D) (i : ι) :
    (numeratorPoly D).eval (zetaCoord D (poleParameter D i + 1)) = 0 :=
  (numeratorPoly_eval_eq_zero_iff D _).mpr ⟨i, alpha_mul_zetaCoord_poleParameter D hD i⟩

/-- RH for the datum is the statement that every pole lies on `Re s = −1/2`. -/
theorem unitary_iff_poles_on_critical_hyperplane (hD : StripCondition D) :
    (∀ i, ‖D.β i‖ = 1) ↔
      ∀ s : ℂ, (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0 → s.re = -(1 / 2 : ℝ) := by
  constructor
  · intro hu s hs
    obtain ⟨i, hi⟩ := exists_alpha_of_root D s hs
    exact (re_root_eq_neg_half_iff D s i hi).mpr (hu i)
  · intro hp i
    exact (re_root_eq_neg_half_iff D _ i (alpha_mul_zetaCoord_poleParameter D hD i)).mp
      (hp _ (poleParameter_root D hD i))

/-- **Receiver form of RH for the datum.** Unitarity is equivalent to holomorphy of the continued
constant term, for all strong rotations, at every point of the band off the critical hyperplane. -/
theorem unitary_iff_eventually_analytic_off_critical (hD : StripCondition D) :
    (∀ i, ‖D.β i‖ = 1) ↔
      ∀ s : ℂ, -1 < s.re → s.re < 0 → s.re ≠ -(1 / 2 : ℝ) →
        ∀ᶠ R : ℝ in atTop, AnalyticAt ℂ (continuedWeylSum D R) s := by
  rw [unitary_iff_poles_on_critical_hyperplane D hD]
  constructor
  · intro hp s hs₁ hs₀ hne
    exact (eventually_analytic_iff D hD s hs₁ hs₀).mpr fun hroot => hne (hp s hroot)
  · intro ha s hroot
    obtain ⟨hs₁, hs₀⟩ := re_root_mem D hD s hroot
    by_contra hne
    exact (eventually_analytic_iff D hD s hs₁ hs₀).mp (ha s hs₁ hs₀ hne) hroot

end CurveDatum

/-! ### Calibration: the golden datum and the actual curve -/

open CurveDatum

open Real in
/-- The golden datum satisfies the strip condition: `√5 φ⁻¹, √5 φ ∈ (1, 5)`. -/
theorem golden_stripCondition : StripCondition goldenDatum := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs2 : 2 < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs3 : Real.sqrt 5 < 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsq : goldenDatum.sqrtq = Real.sqrt 5 := rfl
  have hq : goldenDatum.q = 5 := rfl
  intro i
  rw [CurveDatum.norm_alpha, hsq, hq]
  fin_cases i
  · change 1 < √5 * ‖((goldenRatio : ℝ) : ℂ)‖ ∧ √5 * ‖((goldenRatio : ℝ) : ℂ)‖ < 5
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos goldenRatio_pos]
    have hφ : goldenRatio = (1 + √5) / 2 := rfl
    rw [hφ]
    constructor <;> nlinarith
  · change 1 < √5 * ‖((goldenRatio⁻¹ : ℝ) : ℂ)‖ ∧ √5 * ‖((goldenRatio⁻¹ : ℝ) : ℂ)‖ < 5
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr goldenRatio_pos),
      inv_goldenRatio]
    have hψ : goldenConj = (1 - √5) / 2 := rfl
    rw [hψ]
    constructor <;> nlinarith

open Real in
/-- The golden datum is not unitary. -/
theorem golden_not_unitary : ¬ ∀ i, ‖goldenDatum.β i‖ = 1 := by
  intro h
  have h0 := h 0
  change ‖((goldenRatio : ℝ) : ℂ)‖ = 1 at h0
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos goldenRatio_pos] at h0
  exact (ne_of_gt one_lt_goldenRatio) h0

open Real in
/-- **An off-line pole.** The complete affine Weyl sum of the golden datum has, for all strong
rotations, a pole at `Re s = −1/2 + log φ / log 5`, away from the critical hyperplane. -/
theorem golden_offLine_pole :
    ∃ s : ℂ, s.re = -(1 / 2 : ℝ) + Real.log goldenRatio / Real.log 5 ∧
      s.re ≠ -(1 / 2 : ℝ) ∧
      ∀ᶠ R : ℝ in atTop, 0 < R ∧
        meromorphicOrderAt (fun z => weylSum goldenDatum (levelFourParameter z) 0 0 (Real.log R))
          s < 0 := by
  have hD := golden_stripCondition
  set s := poleParameter goldenDatum 0
  have hroot := poleParameter_root goldenDatum hD 0
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlφ : 0 < Real.log goldenRatio := Real.log_pos one_lt_goldenRatio
  have hre : s.re = -(1 / 2 : ℝ) + Real.log goldenRatio / Real.log 5 := by
    rw [re_root_eq goldenDatum s 0 (alpha_mul_zetaCoord_poleParameter goldenDatum hD 0),
      CurveDatum.norm_alpha]
    have hsq : goldenDatum.sqrtq = Real.sqrt 5 := rfl
    have hq : goldenDatum.q = 5 := rfl
    have hβ : ‖goldenDatum.β 0‖ = goldenRatio := by
      change ‖((goldenRatio : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos goldenRatio_pos]
    rw [hsq, hq, hβ, Real.log_mul (Real.sqrt_pos.mpr (by norm_num)).ne' goldenRatio_ne_zero,
      Real.log_sqrt (by norm_num)]
    field_simp
    ring
  refine ⟨s, hre, ?_, ?_⟩
  · rw [hre]
    have : 0 < Real.log goldenRatio / Real.log 5 := div_pos hlφ hl5
    linarith
  · filter_upwards [weylSum_eventual_order goldenDatum hD s hroot] with R hR
    exact ⟨hR.1, hR.2 ▸ neg_multiplicity_lt_zero goldenDatum s hroot⟩

/-- **The polar calculus does not force unitarity.** A curve datum satisfies the strip condition,
has the exact pole survival of its complete affine Weyl sum at every zero, and is not unitary. -/
theorem polarCalculus_does_not_force_unitarity :
    ∃ D : ArithmeticCastelnuovoSeveri.CurveDatum (Fin 2), StripCondition D ∧
      (∀ s : ℂ, (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0 →
        ∀ᶠ R : ℝ in atTop, 0 < R ∧
          meromorphicOrderAt (fun z => weylSum D (levelFourParameter z) 0 0 (Real.log R)) s =
            -(((numeratorPoly D).rootMultiplicity (zetaCoord D (s + 1)) : ℤ) : WithTop ℤ)) ∧
      ¬ ∀ i, ‖D.β i‖ = 1 :=
  ⟨goldenDatum, golden_stripCondition,
    fun s hs => weylSum_eventual_order goldenDatum golden_stripCondition s hs,
    golden_not_unitary⟩

/-- The actual genus-one curve over `𝔽₃` satisfies the strip condition. -/
theorem actual_stripCondition :
    StripCondition ArithmeticEffectivityTheory.FiniteFieldEllipticBase.datum := by
  intro i
  rw [ArithmeticEffectivityTheory.FiniteFieldEllipticBase.norm_alpha,
    ArithmeticEffectivityTheory.FiniteFieldEllipticBase.datum_q]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  constructor <;> nlinarith

/-- For the actual curve every pole of the continued Weyl sum lies on the critical hyperplane. -/
theorem actual_poles_on_critical_hyperplane (s : ℂ)
    (hs : (numeratorPoly ArithmeticEffectivityTheory.FiniteFieldEllipticBase.datum).eval
      (zetaCoord ArithmeticEffectivityTheory.FiniteFieldEllipticBase.datum (s + 1)) = 0) :
    s.re = -(1 / 2 : ℝ) := by
  refine (unitary_iff_poles_on_critical_hyperplane _ actual_stripCondition).mp ?_ s hs
  intro i
  have h := ArithmeticEffectivityTheory.FiniteFieldEllipticBase.norm_alpha i
  rw [CurveDatum.norm_alpha] at h
  have hsq : ArithmeticEffectivityTheory.FiniteFieldEllipticBase.datum.sqrtq = Real.sqrt 3 := by
    rw [ArithmeticCastelnuovoSeveri.CurveDatum.sqrtq,
      ArithmeticEffectivityTheory.FiniteFieldEllipticBase.datum_q]
  rw [hsq] at h
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  field_simp at h
  linarith

end

end GaloisForLFunctions.RHTower.InfiniteSymmetry
