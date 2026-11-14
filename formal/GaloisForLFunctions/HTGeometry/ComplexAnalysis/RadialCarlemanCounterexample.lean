import GaloisForLFunctions.HTGeometry.ComplexAnalysis.RadialMonomialDerivative
import GaloisForLFunctions.HTGeometry.ComplexAnalysis.CarlemanLogCutoff
import GaloisForLFunctions.HTGeometry.Probability.BlockSphereMellin

/-!
# Radial Carleman concentration in higher complex dimension

A fixed smooth annular cutoff times powers of one complex coordinate separates into radial
and angular factors. At the critical conjugate exponents, the radial factors are independent
of degree. The unequal angular concentration rates obstruct a uniform radial estimate.
-/

open MeasureTheory Set Metric Filter Topology

noncomputable section
namespace GaloisForLFunctions.HTGeometry

local instance (n : ℕ) : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n)) :=
  InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin n))

/-- The complex Hilbert space with one distinguished coordinate and `n` transverse coordinates. -/
abbrev RadialCarlemanSpace (n : ℕ) := BlockSpace ℂ (EuclideanSpace ℂ (Fin n))

/-- A fixed annular profile multiplied by a holomorphic coordinate power. -/
def radialCarlemanTest (n m : ℕ) : RadialCarlemanSpace n → ℂ :=
  radialComplexMonomial (EuclideanSpace ℂ (Fin n)) m carlemanLogCutoff

/-- Every test function vanishes on the unit ball, including its centre. -/
theorem radialCarlemanTest_eq_zero_of_norm_le_one (n m : ℕ) {x : RadialCarlemanSpace n}
    (hx : ‖x‖ ≤ 1) : radialCarlemanTest n m x = 0 := by
  have hlog : Real.log ‖x‖ ≤ 1 :=
    (Real.log_nonpos (norm_nonneg x) hx).trans (by norm_num)
  unfold radialCarlemanTest radialComplexMonomial
  rw [carlemanLogCutoff_eq_zero (Or.inl hlog), Complex.ofReal_zero, mul_zero]

/-- The outer support radius is fixed independently of monomial degree. -/
theorem radialCarlemanTest_eq_zero_of_exp_le_norm (n m : ℕ) {x : RadialCarlemanSpace n}
    (hx : Real.exp 5 ≤ ‖x‖) : radialCarlemanTest n m x = 0 := by
  have hr : 0 < ‖x‖ := (Real.exp_pos 5).trans_le hx
  have hlog : 5 ≤ Real.log ‖x‖ := by
    apply le_of_not_gt
    intro h
    exact (not_lt_of_ge hx) ((Real.log_lt_iff_lt_exp hr).mp h)
  unfold radialCarlemanTest radialComplexMonomial
  rw [carlemanLogCutoff_eq_zero (Or.inr hlog), Complex.ofReal_zero, mul_zero]

/-- Each test is compactly supported in the same closed ball. -/
theorem hasCompactSupport_radialCarlemanTest (n m : ℕ) :
    HasCompactSupport (radialCarlemanTest n m) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : RadialCarlemanSpace n) (Real.exp 5))
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (radialCarlemanTest_eq_zero_of_exp_le_norm n m (le_of_not_ge h))

/-- The annular test family is smooth everywhere, including the origin where it is locally zero. -/
theorem contDiff_radialCarlemanTest (n m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (radialCarlemanTest n m) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : RadialCarlemanSpace n) zero_lt_one] with y hy
    have hy' : ‖y‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hy
    exact radialCarlemanTest_eq_zero_of_norm_le_one n m hy'.le
  · have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y : RadialCarlemanSpace n => y.fst ^ m) :=
      (((ContinuousLinearMap.fst ℂ ℂ (EuclideanSpace ℂ (Fin n))).comp
        (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (EuclideanSpace ℂ (Fin n))).toContinuousLinearMap)
          .restrictScalars ℝ).contDiff.pow m
    have hr : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : RadialCarlemanSpace n => carlemanLogCutoff (Real.log ‖y‖)) x :=
      contDiff_carlemanLogCutoff.contDiffAt.comp x
        ((contDiffAt_id.norm ℂ hx).log (norm_ne_zero_iff.mpr hx))
    change ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : RadialCarlemanSpace n => y.fst ^ m * (carlemanLogCutoff (Real.log ‖y‖) : ℂ)) x
    exact hf.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x hr)

/-- Weighted integral norm of a scalar field in radial Carleman coordinates. -/
def radialCarlemanNorm (n : ℕ) (p τ : ℝ) (f : RadialCarlemanSpace n → ℂ) : ℝ :=
  (∫ x : RadialCarlemanSpace n, (‖x‖ ^ (-τ) * ‖f x‖) ^ p) ^ (1 / p)

/-- Weighted integral norm of the antiholomorphic differential. -/
def radialCarlemanDbarNorm (n : ℕ) (p τ : ℝ) (f : RadialCarlemanSpace n → ℂ) : ℝ :=
  (∫ x : RadialCarlemanSpace n,
    (‖x‖ ^ (-τ) * ‖_root_.HTGeometry.dbarDifferential f x‖) ^ p) ^ (1 / p)

/-- The real dimension of the complex orthogonal sum. -/
theorem radialCarlemanSpace_finrank (n : ℕ) :
    Module.finrank ℝ (RadialCarlemanSpace n) = 2 + 2 * n := by
  have hv : Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin n)),
      Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_fin]
  rw [RadialCarlemanSpace, blockSpace_finrank, Complex.finrank_real_complex, hv]

theorem radialCarlemanSpace_real_finrank (n : ℕ) :
    (Module.finrank ℝ (RadialCarlemanSpace n) : ℝ) = 2 * ((n : ℝ) + 1) := by
  rw [radialCarlemanSpace_finrank]
  push_cast
  ring

/-- Complex and real-coordinate models give the same spherical Mellin moment. -/
theorem complexHilbertSphereMellin_eq (n : ℕ) {s : ℝ} (hs : -1 < s) :
    complexBlockSphereMellin (EuclideanSpace ℂ (Fin n)) s = complexSphereMellin n s := by
  rw [complexBlockSphereMellin_eq _ hs, complexSphereMellin_eq_gamma n hs,
    radialCarlemanSpace_real_finrank]
  have he : 2 * ((n : ℝ) + 1) / 2 = (n : ℝ) + 1 := by ring
  rw [he, Real.Gamma_nat_eq_factorial]
  congr 2
  ring

/-- Degree-independent radial factor in the weighted function norm. -/
def radialCarlemanAmplitude (n : ℕ) (p : ℝ) : ℝ :=
  (((volume : Measure (RadialCarlemanSpace n)).toSphere).real univ *
    ∫ t : ℝ, |carlemanLogCutoff t| ^ p) ^ (1 / p)

/-- Degree-independent radial factor in the weighted differential norm. -/
def radialCarlemanDefect (n : ℕ) (p : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (((volume : Measure (RadialCarlemanSpace n)).toSphere).real univ *
      ∫ t : ℝ, |deriv carlemanLogCutoff t| ^ p) ^ (1 / p)

theorem radialCarlemanAmplitude_pos (n : ℕ) {p : ℝ} (hp : 0 < p) :
    0 < radialCarlemanAmplitude n p := by
  apply Real.rpow_pos_of_pos
  exact mul_pos (complexBlock_sphere_mass_pos (EuclideanSpace ℂ (Fin n)))
    (integral_carlemanLogCutoff_rpow_pos hp)

theorem radialCarlemanDefect_pos (n : ℕ) {p : ℝ} (hp : 0 < p) :
    0 < radialCarlemanDefect n p := by
  apply mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
  apply Real.rpow_pos_of_pos
  exact mul_pos (complexBlock_sphere_mass_pos (EuclideanSpace ℂ (Fin n)))
    (integral_deriv_carlemanLogCutoff_rpow_pos hp)

/-- The balanced weighted function norm is a fixed radial constant times its angular norm. -/
theorem radialCarlemanNorm_balanced (n m : ℕ) {p : ℝ} (hp : 0 < p) :
    radialCarlemanNorm n p ((m : ℝ) + 2 * ((n : ℝ) + 1) / p) (radialCarlemanTest n m) =
      radialCarlemanAmplitude n p * complexSphereMonomialNorm n p m := by
  have hs : -1 < (m : ℝ) * p / 2 := by
    have hmp : 0 ≤ (m : ℝ) * p / 2 := by positivity
    linarith only [hmp]
  have hi : 0 ≤ ∫ t : ℝ, |carlemanLogCutoff t| ^ p :=
    integral_nonneg fun t => Real.rpow_nonneg (abs_nonneg _) _
  have hm := (complexBlock_sphere_mass_pos (EuclideanSpace ℂ (Fin n))).le
  have hM := (complexBlockSphereMellin_pos (EuclideanSpace ℂ (Fin n)) hs).le
  have h := integral_critical_weighted_radialComplexMonomial
    (EuclideanSpace ℂ (Fin n)) m carlemanLogCutoff hp.ne'
  rw [radialCarlemanSpace_real_finrank] at h
  unfold radialCarlemanNorm radialCarlemanTest
  rw [h]
  have he (a b c : ℝ) : a * b * c = (a * c) * b := by ring
  rw [he, Real.mul_rpow (mul_nonneg hm hi) hM, complexHilbertSphereMellin_eq n hs]
  rfl

/-- The balanced differential norm has the same angular factor and a fixed derivative constant. -/
theorem radialCarlemanDbarNorm_balanced (n m : ℕ) {p : ℝ} (hp : 0 < p) :
    radialCarlemanDbarNorm n p ((m : ℝ) + 2 * ((n : ℝ) + 1) / p - 1)
      (radialCarlemanTest n m) =
        radialCarlemanDefect n p * complexSphereMonomialNorm n p m := by
  have hs : -1 < (m : ℝ) * p / 2 := by
    have hmp : 0 ≤ (m : ℝ) * p / 2 := by positivity
    linarith only [hmp]
  have hi : 0 ≤ ∫ t : ℝ, |deriv carlemanLogCutoff t| ^ p :=
    integral_nonneg fun t => Real.rpow_nonneg (abs_nonneg _) _
  have hm := (complexBlock_sphere_mass_pos (EuclideanSpace ℂ (Fin n))).le
  have hM := (complexBlockSphereMellin_pos (EuclideanSpace ℂ (Fin n)) hs).le
  have h := integral_critical_weighted_dbarDifferential_radialComplexMonomial
    (EuclideanSpace ℂ (Fin n)) m
    (contDiff_carlemanLogCutoff.differentiable (by simp)) hp.ne'
  rw [radialCarlemanSpace_real_finrank] at h
  unfold radialCarlemanDbarNorm radialCarlemanTest
  rw [h, Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)
    (mul_nonneg (mul_nonneg hm hM) hi),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    show p * (1 / p) = 1 by field_simp, Real.rpow_one]
  have he (a b c : ℝ) : a * b * c = (a * c) * b := by ring
  rw [he, Real.mul_rpow (mul_nonneg hm hi) hM, complexHilbertSphereMellin_eq n hs]
  change (1 / 2 : ℝ) * (_ * _) = ((1 / 2 : ℝ) * _) * _
  ring

/-- The critical upper exponent leaves the weighted function norm's radial factor fixed. -/
theorem radialCarlemanNorm_critical (n m : ℕ) :
    radialCarlemanNorm n (complexSphereCarlemanQ n) ((m : ℝ) + n + 1 / 2)
      (radialCarlemanTest n m) =
        radialCarlemanAmplitude n (complexSphereCarlemanQ n) *
          complexSphereMonomialNorm n (complexSphereCarlemanQ n) m := by
  have hq := (complexSphereCarlemanP_pos n).trans (complexSphereCarlemanP_lt_Q n)
  have h := radialCarlemanNorm_balanced n m hq
  have he : (m : ℝ) + 2 * ((n : ℝ) + 1) / complexSphereCarlemanQ n =
      (m : ℝ) + n + 1 / 2 := by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    unfold complexSphereCarlemanQ
    field_simp
    ring
  rw [he] at h
  exact h

/-- The same critical weight balances the lower-exponent antiholomorphic norm. -/
theorem radialCarlemanDbarNorm_critical (n m : ℕ) :
    radialCarlemanDbarNorm n (complexSphereCarlemanP n) ((m : ℝ) + n + 1 / 2)
      (radialCarlemanTest n m) =
        radialCarlemanDefect n (complexSphereCarlemanP n) *
          complexSphereMonomialNorm n (complexSphereCarlemanP n) m := by
  have h := radialCarlemanDbarNorm_balanced n m (complexSphereCarlemanP_pos n)
  have he : (m : ℝ) + 2 * ((n : ℝ) + 1) / complexSphereCarlemanP n - 1 =
      (m : ℝ) + n + 1 / 2 := by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    unfold complexSphereCarlemanP
    field_simp
    ring
  rw [he] at h
  exact h

/-- Exact leading constant for the full radial Carleman ratio, including its cutoff factors. -/
theorem tendsto_radialCarleman_ratio_scaled (n : ℕ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ (-((n : ℝ) / (2 * ((n : ℝ) + 1)))) *
      (radialCarlemanNorm n (complexSphereCarlemanQ n) ((m : ℝ) + n + 1 / 2)
          (radialCarlemanTest n m) /
        radialCarlemanDbarNorm n (complexSphereCarlemanP n) ((m : ℝ) + n + 1 / 2)
          (radialCarlemanTest n m))) atTop
      (𝓝 ((radialCarlemanAmplitude n (complexSphereCarlemanQ n) /
        radialCarlemanDefect n (complexSphereCarlemanP n)) *
          (complexSphereMonomialConstant n (complexSphereCarlemanQ n) /
            complexSphereMonomialConstant n (complexSphereCarlemanP n)))) := by
  have h := ((tendsto_complexSphereCarleman_ratio n).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
      (radialCarlemanAmplitude n (complexSphereCarlemanQ n) /
        radialCarlemanDefect n (complexSphereCarlemanP n))
  apply h.congr'
  filter_upwards with m
  rw [radialCarlemanNorm_critical, radialCarlemanDbarNorm_critical]
  ring

/-- The one-complex-dimensional family has a degree-independent ratio: the concentration
obstruction begins precisely when a transverse complex direction is present. -/
theorem radialCarleman_dimension_one (m : ℕ) :
    radialCarlemanNorm 0 (complexSphereCarlemanQ 0) ((m : ℝ) + 1 / 2)
      (radialCarlemanTest 0 m) =
      (radialCarlemanAmplitude 0 (complexSphereCarlemanQ 0) /
        radialCarlemanDefect 0 (complexSphereCarlemanP 0)) *
      radialCarlemanDbarNorm 0 (complexSphereCarlemanP 0) ((m : ℝ) + 1 / 2)
        (radialCarlemanTest 0 m) := by
  have hp := complexSphereCarlemanP_pos 0
  have hq := hp.trans (complexSphereCarlemanP_lt_Q 0)
  have hN := radialCarlemanNorm_critical 0 m
  have hD := radialCarlemanDbarNorm_critical 0 m
  simp only [Nat.cast_zero, add_zero, complexSphereMonomialNorm_zero hp (Nat.cast_nonneg m),
    complexSphereMonomialNorm_zero hq (Nat.cast_nonneg m), mul_one] at hN hD
  rw [hN, hD, div_mul_cancel₀ _ (radialCarlemanDefect_pos 0 hp).ne']

/-- In every complex dimension at least two, radial coordinate monomials defeat any uniform
critical radial Carleman constant. -/
theorem not_uniform_radialCarleman (n : ℕ) :
    ¬ ∃ C : ℝ, ∀ m : ℕ,
      radialCarlemanNorm (n + 1) (complexSphereCarlemanQ (n + 1))
        ((m : ℝ) + (n + 1 : ℕ) + 1 / 2) (radialCarlemanTest (n + 1) m) ≤
      C * radialCarlemanDbarNorm (n + 1) (complexSphereCarlemanP (n + 1))
        ((m : ℝ) + (n + 1 : ℕ) + 1 / 2) (radialCarlemanTest (n + 1) m) := by
  rintro ⟨C, hC⟩
  have hp := complexSphereCarlemanP_pos (n + 1)
  have hpq := complexSphereCarlemanP_lt_Q (n + 1)
  have hA := radialCarlemanAmplitude_pos (n + 1) (hp.trans hpq)
  apply not_uniform_complexSphereMonomialNorm (Nat.succ_pos n) hp hpq
  refine ⟨C * radialCarlemanDefect (n + 1) (complexSphereCarlemanP (n + 1)) /
    radialCarlemanAmplitude (n + 1) (complexSphereCarlemanQ (n + 1)), ?_⟩
  intro m
  have h := hC m
  rw [radialCarlemanNorm_critical, radialCarlemanDbarNorm_critical] at h
  calc
    _ ≤ (C * (radialCarlemanDefect (n + 1) (complexSphereCarlemanP (n + 1)) *
        complexSphereMonomialNorm (n + 1) (complexSphereCarlemanP (n + 1)) m)) /
        radialCarlemanAmplitude (n + 1) (complexSphereCarlemanQ (n + 1)) := by
      apply (le_div_iff₀ hA).mpr
      simpa only [mul_comm (complexSphereMonomialNorm (n + 1)
        (complexSphereCarlemanQ (n + 1)) (m : ℝ))] using h
    _ = _ := by ring

/-- No critical radial Carleman estimate is uniform over the half-integer weight sequence,
even for smooth compactly supported scalar functions vanishing on the unit ball. -/
theorem not_uniform_radialCarleman_smooth (n : ℕ) :
    ¬ ∃ C : ℝ, ∀ (m : ℕ) (f : RadialCarlemanSpace (n + 1) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      (∀ x, ‖x‖ ≤ 1 → f x = 0) →
      radialCarlemanNorm (n + 1) (complexSphereCarlemanQ (n + 1))
        ((m : ℝ) + (n + 1 : ℕ) + 1 / 2) f ≤
      C * radialCarlemanDbarNorm (n + 1) (complexSphereCarlemanP (n + 1))
        ((m : ℝ) + (n + 1 : ℕ) + 1 / 2) f := by
  rintro ⟨C, hC⟩
  apply not_uniform_radialCarleman n
  refine ⟨C, fun m => ?_⟩
  exact hC m (radialCarlemanTest (n + 1) m)
    (contDiff_radialCarlemanTest (n + 1) m)
    (hasCompactSupport_radialCarlemanTest (n + 1) m)
    (fun _ hx => radialCarlemanTest_eq_zero_of_norm_le_one (n + 1) m hx)

end GaloisForLFunctions.HTGeometry
