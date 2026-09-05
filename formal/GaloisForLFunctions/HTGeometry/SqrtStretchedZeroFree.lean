import GaloisForLFunctions.HTGeometry.SqrtStretchedGrowth
import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard
import GaloisForLFunctions.RHTower.ArgumentVariation
import GaloisForLFunctions.HTGeometry.CauchyFirstOrderStep

/-!
# A zero-free entire function of order zero is constant

The magnitude bound of the square-root stretched-exponential family transfers to the function
itself.  If such a function were zero-free, Hadamard's zero-free factorization would write it as
`exp ∘ p`; Borel–Carathéodory turns the one-sided bound `Re p ≤ C + ε ‖z‖` into a two-sided bound,
and the Cauchy coefficient estimates then kill every coefficient of positive degree.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section


/-- The function is dominated by its magnitude series. -/
theorem norm_sqrtStretchedPhaseFunction_le (θ : ℕ → ℝ) (z : ℂ) :
    ‖GaloisForLFunctions.sqrtStretchedPhaseFunction θ z‖
      ≤ ∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * ‖z‖ ^ n := by
  rw [GaloisForLFunctions.sqrtStretchedPhaseFunction_eq_tsum]
  have hnorm : ∀ n : ℕ,
      ‖(Real.exp (-Real.exp (Real.sqrt n)) : ℂ) * Complex.exp (Complex.I * (θ n : ℂ)) * z ^ n‖
        = Real.exp (-Real.exp (Real.sqrt n)) * ‖z‖ ^ n := by
    intro n
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    simp
  have hsummable : Summable (fun n : ℕ =>
      ‖(Real.exp (-Real.exp (Real.sqrt n)) : ℂ) * Complex.exp (Complex.I * (θ n : ℂ)) * z ^ n‖) := by
    have := summable_sqrtStretched_term (r := ‖z‖) (norm_nonneg z)
    exact this.congr fun n => (hnorm n).symm
  refine le_trans (norm_tsum_le_tsum_norm hsummable) ?_
  exact le_of_eq (tsum_congr hnorm)

/-- **Order zero for the function.**  For every `ε > 0` the family is eventually below
`exp (ε ‖z‖)`. -/
theorem sqrtStretched_norm_le_exp (θ : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖GaloisForLFunctions.sqrtStretchedPhaseFunction θ z‖ ≤ Real.exp (C + ε * ‖z‖) := by
  obtain ⟨R, hR⟩ := (sqrtStretched_growth hε).exists_forall_of_atTop
  set C : ℝ := max 0 (Real.log (∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * (max R 1) ^ n)
    + ε * max R 1) with hC
  refine ⟨C, le_max_left _ _, fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ max R 1
  · -- small radius: the series is monotone in the radius
    have hmono : ∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * ‖z‖ ^ n
        ≤ ∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * (max R 1) ^ n := by
      refine Summable.tsum_le_tsum (fun n => ?_)
        (summable_sqrtStretched_term (norm_nonneg z))
        (summable_sqrtStretched_term (le_trans (norm_nonneg z) hz))
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
      exact pow_le_pow_left₀ (norm_nonneg z) hz n
    have hpos : (0 : ℝ) < ∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * (max R 1) ^ n := by
      refine lt_of_lt_of_le ?_ (Summable.le_tsum (summable_sqrtStretched_term
        (le_trans (norm_nonneg z) hz)) 0 (fun i _ => by positivity))
      positivity
    have hlog : ∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * (max R 1) ^ n
        = Real.exp (Real.log (∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * (max R 1) ^ n)) := by
      rw [Real.exp_log hpos]
    refine le_trans (norm_sqrtStretchedPhaseFunction_le θ z) ?_
    refine le_trans hmono ?_
    rw [hlog]
    refine Real.exp_le_exp.mpr ?_
    have hle : Real.log (∑' n : ℕ, Real.exp (-Real.exp (Real.sqrt n)) * (max R 1) ^ n)
        + ε * max R 1 ≤ C := le_max_right _ _
    nlinarith [hle, norm_nonneg z, hε.le]
  · push Not at hz
    have hzR : R ≤ ‖z‖ := le_trans (le_max_left R 1) (le_of_lt hz)
    refine le_trans (norm_sqrtStretchedPhaseFunction_le θ z) ?_
    refine le_trans (hR ‖z‖ hzR) ?_
    refine Real.exp_le_exp.mpr ?_
    have : (0 : ℝ) ≤ C := le_max_left _ _
    linarith

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Metric


/-- **A zero-free entire function of order zero is constant.**  Hadamard writes it as `exp ∘ p`;
Borel–Carathéodory bounds `p` on every circle by `K + 4 ε r`, and the Cauchy estimate for the first
derivative then forces `p′ = 0`. -/
theorem const_of_ne_zero_of_subexponential {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0)
    (hgrow : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C + ε * ‖z‖)) :
    ∀ z : ℂ, f z = f 0 := by
  classical
  -- Hadamard's zero-free factorization
  obtain ⟨C₁, hC₁, hgrow₁⟩ := hgrow 1 one_pos
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℂ, ∀ z, f z = Complex.exp (p.eval z) := by
    refine GaloisForLFunctions.HTGeometry.exists_polynomial_exp_of_ne_zero_of_growth hf hne
      (C := C₁ + 1) (d := 1) (by linarith) fun z => ?_
    refine le_trans (hgrow₁ z) ?_
    refine Real.exp_le_exp.mpr ?_
    have : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    nlinarith [hC₁]
  set P : ℂ → ℂ := fun z => p.eval z with hP
  have hPdiff : Differentiable ℂ P := Polynomial.differentiable p
  have hRe : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, (P z).re ≤ C + ε * ‖z‖ := by
    intro ε hε
    obtain ⟨C, hC0, hCz⟩ := hgrow ε hε
    refine ⟨C, fun z => ?_⟩
    have hfz : ‖f z‖ = Real.exp (P z).re := by
      rw [hp z, Complex.norm_exp]
    have := hCz z
    rw [hfz] at this
    exact Real.exp_le_exp.mp this
  -- the derivative of the polynomial vanishes everywhere
  have hderiv : ∀ z₀ : ℂ, deriv P z₀ = 0 := by
    intro z₀
    have hbound : ∀ ε : ℝ, 0 < ε → ‖deriv P z₀‖ ≤ 4 * ε := by
      intro ε hε
      obtain ⟨C, hCz⟩ := hRe ε hε
      set K : ℝ := ‖P z₀‖ + 2 * (C + ε * ‖z₀‖ - (P z₀).re) with hK
      have hstep : ∀ r : ℝ, 0 < r → ‖deriv P z₀‖ ≤ (K + 4 * ε * r) / r := by
        intro r hr
        have hA : (P z₀).re < C + ε * (‖z₀‖ + 2 * r) := by
          have := hCz z₀
          nlinarith [hε, hr]
        have hball : ∀ w ∈ ball z₀ (2 * r), (P w).re ≤ C + ε * (‖z₀‖ + 2 * r) := by
          intro w hw
          have hwn : ‖w‖ ≤ ‖z₀‖ + 2 * r := by
            have hdist : ‖w - z₀‖ < 2 * r := mem_ball_iff_norm.mp hw
            calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
              _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
              _ ≤ ‖z₀‖ + 2 * r := by linarith
          refine le_trans (hCz w) ?_
          have : ε * ‖w‖ ≤ ε * (‖z₀‖ + 2 * r) := mul_le_mul_of_nonneg_left hwn (le_of_lt hε)
          linarith
        have hsphere : ∀ w ∈ sphere z₀ r, ‖P w‖ ≤ K + 4 * ε * r := by
          intro w hw
          have hwmem : w ∈ ball z₀ (2 * r) := by
            rw [mem_ball_iff_norm]
            have : ‖w - z₀‖ = r := by
              rw [← dist_eq_norm]
              exact hw
            linarith
          have hbc := RHTower.borel_caratheodory (g := P) (c := z₀) (z := w) (R := 2 * r)
            (A := C + ε * (‖z₀‖ + 2 * r)) (hPdiff.differentiableOn) hball hA hwmem
          have hwd : ‖w - z₀‖ = r := by
            rw [← dist_eq_norm]
            exact hw
          rw [hwd] at hbc
          have hfrac : 2 * r / (2 * r - r) = 2 := by
            field_simp
            ring
          rw [hfrac] at hbc
          calc ‖P w‖ = ‖(P w - P z₀) + P z₀‖ := by ring_nf
            _ ≤ ‖P w - P z₀‖ + ‖P z₀‖ := norm_add_le _ _
            _ ≤ 2 * (C + ε * (‖z₀‖ + 2 * r) - (P z₀).re) + ‖P z₀‖ := by linarith
            _ = K + 4 * ε * r := by rw [hK]; ring
        have hcauchy := _root_.HTGeometry.norm_deriv_le_of_forall_mem_sphere_norm_le
          (f := P) (z := z₀) (R := r) hr (hPdiff.diffContOnCl) hsphere
        exact hcauchy
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      obtain ⟨r, hr1, hr2⟩ : ∃ r : ℝ, 0 < r ∧ K / r ≤ δ := by
        rcases le_or_gt K 0 with hKle | hKpos
        · exact ⟨1, one_pos, by
            have : K / 1 = K := by ring
            rw [this]
            linarith⟩
        · refine ⟨K / δ + 1, by positivity, ?_⟩
          rw [div_le_iff₀ (by positivity)]
          have : K / δ * δ = K := by field_simp
          nlinarith [hδ, hKpos]
      have := hstep r hr1
      have hdiv : (K + 4 * ε * r) / r = K / r + 4 * ε := by
        field_simp
      rw [hdiv] at this
      linarith
    have hzero : ‖deriv P z₀‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have := hbound (δ / 8) (by positivity)
      linarith
    exact norm_le_zero_iff.mp hzero
  -- a vanishing derivative makes the composite constant
  have hfderiv : ∀ z : ℂ, deriv f z = 0 := by
    intro z
    have hcomp : ∀ w : ℂ, f w = Complex.exp (P w) := fun w => hp w
    have hd : HasDerivAt f (Complex.exp (P z) * deriv P z) z := by
      have hPd : HasDerivAt P (deriv P z) z := (hPdiff z).hasDerivAt
      have := hPd.cexp
      refine HasDerivAt.congr_of_eventuallyEq this ?_
      filter_upwards with w
      exact hcomp w
    rw [hd.deriv, hderiv z, mul_zero]
  have hfd : ∀ z : ℂ, fderiv ℂ f z = 0 := by
    intro z
    rw [toSpanSingleton_deriv.symm, hfderiv z]
    simp
  intro z
  exact is_const_of_fderiv_eq_zero hf hfd z 0

end

end GaloisForLFunctions.HTGeometry
