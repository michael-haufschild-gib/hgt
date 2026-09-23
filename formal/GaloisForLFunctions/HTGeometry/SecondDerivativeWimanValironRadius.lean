import GaloisForLFunctions.HTGeometry.SecondDerivativeWimanValironWindow
import GaloisForLFunctions.HTGeometry.WimanValironRadius

/-!
# The order-two Wiman--Valiron estimate at a selected radius

The selection of `WimanValironRadius` is repeated once, keeping the window data long enough to feed
both the order-one and the order-two window estimates at the same point.
-/

open MeasureTheory Complex Set

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The explicit order-one Wiman--Valiron bound at the closed parameters. -/
noncomputable def wvClosedBound (a : ℕ → ℂ) (x : ℝ) (N : ℕ) (L h : ℝ) : ℝ :=
  (Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L))))))
      * (2 * L * h
        + 2 * Real.log ((centralIndex a (Real.exp x) : ℝ) + 2 * L * h + 1
            + 1 / (Real.exp h - 1)) / h)
    + Real.sqrt (2 * ((N : ℝ) ^ (2 : ℕ) * Real.sqrt (2 * (N : ℝ) + 1)
          + 2 * (2 * ((N : ℝ) + 1) ^ (2 : ℕ) * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
              / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ (3 : ℕ)))
        * (Real.sqrt (2 * (N : ℝ) + 1)
          + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
              / (1 - Real.exp (-((N : ℝ) / (4 * L)))))))

/-- The explicit constant bounding the normalised second moment. -/
noncomputable def wvSecondMomentBound (N : ℕ) (L : ℝ) : ℝ :=
  (N : ℝ) ^ (2 : ℕ) * Real.sqrt (2 * (N : ℝ) + 1)
    + 2 * (2 * ((N : ℝ) + 1) ^ (2 : ℕ) * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
        / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ (3 : ℕ))

set_option maxHeartbeats 800000 in
/-- **Both Wiman--Valiron estimates at one selected radius, retaining the full maximum-circle
property of the selected point.** -/
theorem exists_radius_point_secondDeriv_le_closed_isMaximumOnCircle
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H v₀ s L h : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hv₀ : 0 < v₀) (hs : 0 < s) (hL : 0 < L) (hsL : s ≤ L * v₀)
    (hh : 0 < h) (hv₀h : v₀ ≤ h) (hhH : 2 * h ≤ H)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c)
    {N : ℕ} (hN0 : 0 < N) (hNv : 2 * L * v₀ ≤ (N : ℝ)) (hNK : (N : ℝ) ≤ 2 * L * H) :
    ∃ x ∈ Icc (c + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ wvClosedBound a x N L h ∧
      ‖z ^ (2 : ℕ) * deriv (deriv (coeffFun a)) z / coeffFun a z
          - ((centralIndex a (Real.exp x) : ℂ) * ((centralIndex a (Real.exp x) : ℂ) - 1))‖
        ≤ wvSecondMomentBound N L
          + (2 * (centralIndex a (Real.exp x) : ℝ) + 1) * wvClosedBound a x N L h ∧
      ∀ w : ℂ, ‖w‖ = ‖z‖ → ‖coeffFun a w‖ ≤ ‖coeffFun a z‖ := by
  obtain ⟨x, hx, hlipA0, hlipB0⟩ :=
    exists_radius_lipschitz_centralIndex ha hn₀ hcd hH hv₀ hs hsmall
  have hupg : ∀ v : ℝ, v₀ ≤ v → s / v₀ * v ≤ L * v := by
    intro v hv
    refine mul_le_mul_of_nonneg_right ?_ (le_trans hv₀.le hv)
    rw [div_le_iff₀ hv₀]
    exact hsL
  have hA : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v := by
    intro v hv hvH
    have h1 := hlipA0 v hv hvH
    have h2 := hupg v hv
    linarith
  have hB : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ) := by
    intro v hv hvH
    have h1 := hlipB0 v hv hvH
    have h2 := hupg v hv
    linarith
  have hr : (0 : ℝ) < Real.exp x := Real.exp_pos x
  obtain ⟨z, hz, hmax⟩ := exists_max_on_circle ha hr
  have hfz := maxTerm_le_norm_of_max_on_circle ha hr hz hmax
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hfpos : 0 < ‖coeffFun a z‖ := lt_of_lt_of_le hμpos hfz
  have hfne : coeffFun a z ≠ 0 := norm_pos_iff.mp hfpos
  have hcrit := im_mul_deriv_div_eq_zero_of_max_on_circle ha hr hz hfne hmax
  have hfac : coeffFun a z
      = (a (centralIndex a (Real.exp x)) * z ^ centralIndex a (Real.exp x))
        * ∑' n : ℕ, normalisedCoeff a (Real.exp x) z n :=
    coeffFun_eq_central_term_mul_tsum ha hr hn₀ hz
  have hWne : (∑' n : ℕ, normalisedCoeff a (Real.exp x) z n) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfac
    exact hfne hfac
  obtain ⟨u, hu, hWdir⟩ := exists_unit_dir hWne
  have hest := norm_mul_logDeriv_sub_centralIndex_le_explicit_window ha hn₀ hH hL hN0 hNK hNv
    hA hB hz hfz hmax hcrit hu hWdir
  have hgap := abs_meanIndex_sub_centralIndex_le_lipschitz ha hn₀ hL hh hhH hv₀h hA hB
  have hq0 : (0 : ℝ) < Real.exp (-((N : ℝ) / (4 * L))) := Real.exp_pos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hq1 : Real.exp (-((N : ℝ) / (4 * L))) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : (0 : ℝ) < (N : ℝ) / (4 * L) := by positivity
    linarith
  have hAnn : (0 : ℝ) ≤ Real.sqrt (2 * (N : ℝ) + 1)
      + 2 * (Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
          / (1 - Real.exp (-((N : ℝ) / (4 * L))))) := by
    have hden : (0 : ℝ) < 1 - Real.exp (-((N : ℝ) / (4 * L))) := by linarith
    have h1 : (0 : ℝ) ≤ Real.sqrt (2 * (N : ℝ) + 1) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
        / (1 - Real.exp (-((N : ℝ) / (4 * L)))) := by positivity
    linarith
  have hstep := mul_le_mul_of_nonneg_left hgap hAnn
  have hone : ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
      ≤ wvClosedBound a x N L h := by
    rw [wvClosedBound]
    linarith
  have hmaxFull : ∀ w : ℂ, ‖w‖ = ‖z‖ → ‖coeffFun a w‖ ≤ ‖coeffFun a z‖ := by
    intro w hw
    let θ : ℝ := Complex.arg w
    have hw0 : w ≠ 0 := by
      intro hwzero
      rw [hwzero, norm_zero, hz] at hw
      exact (Real.exp_ne_zero x) hw.symm
    have hwr : ‖w‖ = Real.exp x := hw.trans hz
    have hcircle : circleMap 0 (Real.exp x) θ = w := by
      rw [circleMap, zero_add, ← hwr]
      simpa [θ, mul_comm] using Complex.norm_mul_exp_arg_mul_I w
    rw [← hcircle]
    exact hmax θ
  refine ⟨x, hx, z, hz, hfz, hone, ?_, hmaxFull⟩
  have hG₂ : ∑' j : ℕ, ((N : ℝ) + 1 + j) ^ (2 : ℕ)
      * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1 + j)
      ≤ 2 * ((N : ℝ) + 1) ^ (2 : ℕ) * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1)
        / (1 - Real.exp (-((N : ℝ) / (4 * L)))) ^ (3 : ℕ) :=
    tsum_shifted_sq_weight_le hq0 hq1 N
  have h2nd := norm_mul_sq_deriv2_div_sub_le ha hn₀ (v₀ := v₀) hH hL hN0 hNK hNv hA hB
    hz hfz hmax hG₂ hone
  rw [wvSecondMomentBound]
  exact h2nd

/-- **Both Wiman--Valiron estimates at one selected radius.** -/
theorem exists_radius_point_secondDeriv_le_closed
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {c d H v₀ s L h : ℝ}
    (hcd : c ≤ d) (hH : 0 < H) (hv₀ : 0 < v₀) (hs : 0 < s) (hL : 0 < L) (hsL : s ≤ L * v₀)
    (hh : 0 < h) (hv₀h : v₀ ≤ h) (hhH : 2 * h ≤ H)
    (hsmall : 2 * H * ((centralIndex a (Real.exp (d + 2 * H)) : ℝ)
        - (centralIndex a (Real.exp c) : ℝ)) / s < d - c)
    {N : ℕ} (hN0 : 0 < N) (hNv : 2 * L * v₀ ≤ (N : ℝ)) (hNK : (N : ℝ) ≤ 2 * L * H) :
    ∃ x ∈ Icc (c + H) (d + H), ∃ z : ℂ, ‖z‖ = Real.exp x ∧
      maxTerm a (Real.exp x) ≤ ‖coeffFun a z‖ ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp x) : ℂ)‖
        ≤ wvClosedBound a x N L h ∧
      ‖z ^ (2 : ℕ) * deriv (deriv (coeffFun a)) z / coeffFun a z
          - ((centralIndex a (Real.exp x) : ℂ) * ((centralIndex a (Real.exp x) : ℂ) - 1))‖
        ≤ wvSecondMomentBound N L
          + (2 * (centralIndex a (Real.exp x) : ℝ) + 1) * wvClosedBound a x N L h := by
  obtain ⟨x, hx, z, hz, hfloor, hone, htwo, _⟩ :=
    exists_radius_point_secondDeriv_le_closed_isMaximumOnCircle ha hn₀ hcd hH hv₀ hs hL hsL
      hh hv₀h hhH hsmall hN0 hNv hNK
  exact ⟨x, hx, z, hz, hfloor, hone, htwo⟩

end GaloisForLFunctions.HTGeometry
