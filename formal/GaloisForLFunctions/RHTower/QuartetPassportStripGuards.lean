import GaloisForLFunctions.RHTower.QuartetPassportRealizer

noncomputable section

namespace RHTower

/-- The strip-coordinate quartet realizer is entire. -/
theorem quartetRealizerStrip_analyticAt (a : ℝ) (B : Polynomial ℂ) (s : ℂ) :
    AnalyticAt ℂ (quartetRealizerStrip a B) s := by
  exact (quartetRealizer_analyticAt a B _).comp_of_eq
    (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)) rfl

/-- Derivative transport from centered coordinates to the critical-strip coordinate. -/
theorem deriv_quartetRealizerStrip (a : ℝ) (B : Polynomial ℂ) (s : ℂ) :
    deriv (quartetRealizerStrip a B) s =
      -Complex.I * deriv (quartetRealizer a B)
        (-Complex.I * (s - ((1 / 2 : ℝ) : ℂ))) := by
  have hinner : HasDerivAt
      (fun w : ℂ => -Complex.I * (w - ((1 / 2 : ℝ) : ℂ))) (-Complex.I) s := by
    simpa using
      (((hasDerivAt_id s).sub_const ((1 / 2 : ℝ) : ℂ)).const_mul (-Complex.I))
  have houter :=
    (quartetRealizer_differentiable a B
      (-Complex.I * (s - ((1 / 2 : ℝ) : ℂ)))).hasDerivAt
  change deriv
      (fun x : ℂ => quartetRealizer a B
        (-Complex.I * (x - ((1 / 2 : ℝ) : ℂ)))) s = _
  simpa [Function.comp_def, mul_comm] using
    (houter.comp s hinner).deriv

/-- Aperiodicity is invariant under the invertible strip-coordinate change. -/
theorem quartetRealizerStrip_period_eq_zero_of_centered {a : ℝ} {B : Polynomial ℂ}
    (hperiod : ∀ h : ℂ, Function.Periodic (quartetRealizer a B) h → h = 0)
    {h : ℂ} (hh : Function.Periodic (quartetRealizerStrip a B) h) : h = 0 := by
  have hcenter : Function.Periodic (quartetRealizer a B) (-Complex.I * h) := by
    intro z
    have hz := hh (((1 / 2 : ℝ) : ℂ) + Complex.I * z)
    have hI : -Complex.I * Complex.I = 1 := by
      rw [neg_mul, Complex.I_mul_I]
      simp
    have hleft :
        -Complex.I *
            ((((1 / 2 : ℝ) : ℂ) + Complex.I * z + h) - ((1 / 2 : ℝ) : ℂ)) =
          z + -Complex.I * h := by
      calc
        _ = -Complex.I * (Complex.I * z + h) := by ring
        _ = z + -Complex.I * h := by rw [mul_add, ← mul_assoc, hI, one_mul]
    have hright :
        -Complex.I *
            ((((1 / 2 : ℝ) : ℂ) + Complex.I * z) - ((1 / 2 : ℝ) : ℂ)) = z := by
      calc
        _ = (-Complex.I * Complex.I) * z := by ring
        _ = z := by rw [hI, one_mul]
    change quartetRealizer a B
        (-Complex.I *
          ((((1 / 2 : ℝ) : ℂ) + Complex.I * z + h) - ((1 / 2 : ℝ) : ℂ))) =
      quartetRealizer a B
        (-Complex.I *
          ((((1 / 2 : ℝ) : ℂ) + Complex.I * z) - ((1 / 2 : ℝ) : ℂ))) at hz
    rw [hleft, hright] at hz
    exact hz
  have hz := hperiod (-Complex.I * h) hcenter
  exact (mul_eq_zero.mp hz).resolve_left (by simp)

/-- Exact order-one bounds survive the affine strip-coordinate change. The lower ray becomes the
vertical ray `1/2 + i x`; the upper exponential type is unchanged. -/
theorem quartetRealizerStrip_exact_order_one_bounds_of_centered
    {a : ℝ} {B : Polynomial ℂ}
    (horder : ∃ Kupper Klower R : ℝ,
      0 < Kupper ∧ 0 < Klower ∧
      (∀ z : ℂ, ‖quartetRealizer a B z‖ ≤
        Kupper * (1 + ‖z‖) ^ B.natDegree * Real.exp (2 * ‖z‖)) ∧
      ∀ x : ℝ, R ≤ x →
        Klower * Real.exp (2 * x) ≤ ‖quartetRealizer a B (x : ℂ)‖) :
    ∃ Kupper Klower R : ℝ,
      0 < Kupper ∧ 0 < Klower ∧
      (∀ s : ℂ, ‖quartetRealizerStrip a B s‖ ≤
        Kupper * (1 + ‖s‖) ^ B.natDegree * Real.exp (2 * ‖s‖)) ∧
      ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * x) ≤
        ‖quartetRealizerStrip a B (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ))‖ := by
  obtain ⟨Kupper, Klower, R, hKupper, hKlower, hupper, hlower⟩ := horder
  refine ⟨Kupper * 2 ^ B.natDegree * Real.exp 2, Klower, R, ?_, hKlower, ?_, ?_⟩
  · positivity
  · intro s
    let z := -Complex.I * (s - ((1 / 2 : ℝ) : ℂ))
    have hz : ‖z‖ ≤ ‖s‖ + 1 := by
      calc
        ‖z‖ = ‖s - ((1 / 2 : ℝ) : ℂ)‖ := by
          simp [z]
        _ ≤ ‖s‖ + ‖((1 / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖s‖ + 1 := by norm_num
    have hbase : 1 + ‖z‖ ≤ 2 * (1 + ‖s‖) := by
      nlinarith [norm_nonneg s]
    have hexp : Real.exp (2 * ‖z‖) ≤ Real.exp (2 * ‖s‖ + 2) := by
      apply Real.exp_le_exp.mpr
      linarith
    calc
      ‖quartetRealizerStrip a B s‖ = ‖quartetRealizer a B z‖ := by rfl
      _ ≤ Kupper * (1 + ‖z‖) ^ B.natDegree * Real.exp (2 * ‖z‖) := hupper z
      _ ≤ Kupper * (2 * (1 + ‖s‖)) ^ B.natDegree * Real.exp (2 * ‖s‖ + 2) := by
        gcongr
      _ = (Kupper * 2 ^ B.natDegree * Real.exp 2) *
          (1 + ‖s‖) ^ B.natDegree * Real.exp (2 * ‖s‖) := by
        rw [mul_pow, Real.exp_add]
        ring
  · intro x hx
    have hcoord :
        -Complex.I *
            ((((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)) - ((1 / 2 : ℝ) : ℂ)) =
          (x : ℂ) := by
      rw [add_sub_cancel_left]
      have hI : -Complex.I * Complex.I = 1 := by
        rw [neg_mul, Complex.I_mul_I]
        simp
      rw [← mul_assoc, hI, one_mul]
    rw [quartetRealizerStrip, hcoord]
    exact hlower x hx

end RHTower
