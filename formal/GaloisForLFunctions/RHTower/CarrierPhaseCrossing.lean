/-
# Phase advance produces a simple zero of the finite completed carrier

The direct completed Dirichlet summand has an exact logarithmic derivative on the critical
line.  A positive Dirichlet floor bounds its finite-frequency counter-rotation, while the
archimedean factor supplies increasing positive winding.  If the resulting net phase advance
exceeds a half-turn, the real part of the direct summand vanishes.  This is precisely a zero of
the completed finite carrier; the same strict phase dominance makes that zero simple.
-/
import GaloisForLFunctions.RHTower.CarrierTransverseZero
import GaloisForLFunctions.RHTower.LateralWindingFloor
import GaloisForLFunctions.RHTower.EulerTailWinding
import GaloisForLFunctions.RHTower.EdgeEventSynthesis
import GaloisForLFunctions.RHTower.Peeling

namespace RHTower

open Complex Metric MeasureTheory

noncomputable section

/-- A polar path whose phase advances by a half-turn has a zero of its real part. -/
theorem exists_re_zero_of_phase_advance {F : ℝ → ℂ} {r θ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hpolar : ∀ τ ∈ Set.Icc a b, F τ = (r τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hθc : ContinuousOn θ (Set.Icc a b)) (hadv : θ a + Real.pi ≤ θ b) :
    ∃ τ ∈ Set.Icc a b, (F τ).re = 0 := by
  let F' : ℝ → ℂ := fun τ => I * F τ
  let θ' : ℝ → ℝ := fun τ => θ τ + Real.pi / 2
  have hpolar' : ∀ τ ∈ Set.Icc a b,
      F' τ = (r τ : ℂ) * Complex.exp ((θ' τ : ℝ) * I) := by
    intro τ hτ
    simp only [F', θ']
    rw [hpolar τ hτ]
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
    ring
  have hθc' : ContinuousOn θ' (Set.Icc a b) := hθc.add continuousOn_const
  have hadv' : θ' a + Real.pi ≤ θ' b := by
    dsimp [θ']
    linarith
  obtain ⟨τ, hτ, him⟩ := exists_im_zero_of_phase_advance hab hpolar' hθc' hadv'
  refine ⟨τ, hτ, ?_⟩
  simpa [F', Complex.mul_im] using him

/-- The explicit archimedean winding floor at height `a`. -/
def carrierWindingFloor (a : ℝ) : ℝ :=
  (Real.log (a / (2 * Real.pi)) - (4 / a ^ 2 + Real.pi / a)) / 2

/-- Archimedean winding remaining after paying the finite Dirichlet derivative budget. -/
def carrierNetPhaseRate (N : ℕ) (d a : ℝ) : ℝ :=
  carrierWindingFloor a - dirichletLineDerivativeBudget N / d

/-- At sufficiently large height the net phase rate exceeds any fixed target. -/
theorem exists_height_carrierNetPhaseRate_ge (N : ℕ) {d q : ℝ} :
    ∃ A : ℝ, 0 < A ∧ ∀ a, A ≤ a → q ≤ carrierNetPhaseRate N d a := by
  obtain ⟨A, hA0, hA⟩ := exists_height_net_rate_ge
    (P := ∅) (σ := 1) (B_D := dirichletLineDerivativeBudget N / d) (ρ₀ := q) (by norm_num)
  refine ⟨A, hA0, fun a ha => ?_⟩
  simpa [carrierNetPhaseRate, carrierWindingFloor, stripFloor, eulerHeadBound] using hA a ha

/-- The exact logarithmic derivative of the direct completed summand on the critical line. -/
noncomputable def completedDirectLineLogDeriv (N : ℕ) (τ : ℝ) : ℂ :=
  (archWinding τ +
    deriv (dirichletPoly N) (linePt τ) / dirichletPoly N (linePt τ)) * I

/-- A positive Dirichlet floor and a half-turn of net archimedean phase force a simple zero of
the finite completed carrier.  Zero existence and zero transversality are both conclusions. -/
theorem exists_simple_completedGN_zero_of_interval_floor (N : ℕ) {a b d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hd0 : 0 < d)
    (hDfloor : ∀ τ ∈ Set.Icc a b, d ≤ ‖dirichletPoly N (linePt τ)‖)
    (hnet0 : 0 < carrierNetPhaseRate N d a)
    (hadvance : Real.pi ≤ (b - a) * carrierNetPhaseRate N d a) :
    ∃ τ ∈ Set.Icc a b,
      completedGN N (linePt τ) = 0 ∧ deriv (completedGN N) (linePt τ) ≠ 0 := by
  have hlinec : Continuous (fun τ : ℝ => linePt τ) := by
    rw [continuous_iff_continuousAt]
    intro τ
    exact (hasDerivAt_linePt τ).continuousAt
  have hDc : Continuous (fun τ : ℝ => dirichletPoly N (linePt τ)) :=
    (dirichletPoly_differentiable N).continuous.comp hlinec
  have hderivc : Continuous (fun τ : ℝ => deriv (dirichletPoly N) (linePt τ)) := by
    rw [show (fun τ : ℝ => deriv (dirichletPoly N) (linePt τ)) = fun τ =>
        -dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n)
          (Finset.Icc 1 N) τ by
      funext τ
      exact deriv_dirichletPoly_line_eq_neg_dpoly_log N τ]
    exact (dpoly_continuous
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log n) (Finset.Icc 1 N)).neg
  let U : Set ℝ := {τ | d / 2 < ‖dirichletPoly N (linePt τ)‖}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_Ioi.preimage (continuous_norm.comp hDc)
  have hsub : Set.Icc a b ⊆ U := by
    intro τ hτ
    dsimp [U]
    have hfloor := hDfloor τ hτ
    linarith
  have hDneU : ∀ τ ∈ U, dirichletPoly N (linePt τ) ≠ 0 := by
    intro τ hτ
    apply norm_pos_iff.mp
    dsimp [U] at hτ
    linarith
  have hquotc : ContinuousOn (fun τ : ℝ =>
      deriv (dirichletPoly N) (linePt τ) / dirichletPoly N (linePt τ)) U :=
    hderivc.continuousOn.div hDc.continuousOn hDneU
  have hωc : ContinuousOn (completedDirectLineLogDeriv N) U := by
    unfold completedDirectLineLogDeriv
    exact (continuous_archWinding.continuousOn.add hquotc).mul continuousOn_const
  have hDneIcc : ∀ τ ∈ Set.Icc a b, dirichletPoly N (linePt τ) ≠ 0 := by
    intro τ hτ
    exact norm_pos_iff.mp (lt_of_lt_of_le hd0 (hDfloor τ hτ))
  have hG : ∀ τ ∈ Set.Icc a b,
      HasDerivAt (completedDirectLine N)
        (completedDirectLine N τ * completedDirectLineLogDeriv N τ) τ := by
    intro τ hτ
    have hslope := completedDirectLineSlope_eq_factor N τ (hDneIcc τ hτ)
    have h := hasDerivAt_completedDirectLine N τ
    rw [hslope] at h
    simpa [completedDirectLineLogDeriv] using h
  let r : ℝ → ℝ := fun τ =>
    ‖completedDirectLine N a‖ * Real.exp (∫ t in a..τ, (completedDirectLineLogDeriv N t).re)
  let θ : ℝ → ℝ := fun τ =>
    (completedDirectLine N a).arg +
      ∫ t in a..τ, (completedDirectLineLogDeriv N t).im
  have hpolar0 := polar_presentation_of_logDeriv hUopen hsub hG hωc
  have hpolar : ∀ τ ∈ Set.Icc a b,
      completedDirectLine N τ = (r τ : ℂ) * Complex.exp ((θ τ : ℝ) * I) := by
    intro τ hτ
    simpa [r, θ] using hpolar0 τ hτ
  have hωimc : ContinuousOn (fun τ => (completedDirectLineLogDeriv N τ).im) U :=
    Complex.continuous_im.comp_continuousOn hωc
  have hθc : ContinuousOn θ (Set.Icc a b) := by
    dsimp [θ]
    exact continuousOn_const.add (continuousOn_primitive_of_open hUopen hsub hωimc)
  have hpoint : ∀ τ ∈ Set.Icc a b,
      carrierNetPhaseRate N d a ≤ (completedDirectLineLogDeriv N τ).im := by
    intro τ hτ
    have hτ0 : 0 < τ := lt_of_lt_of_le ha hτ.1
    have hwind : carrierWindingFloor a ≤ windingRate τ :=
      le_trans (winding_floor_expr_mono ha hτ.1) (windingRate_ge hτ0)
    have hdir := re_dirichletPoly_logDeriv_line_ge N τ d hd0 (hDfloor τ hτ)
    have hωim : (completedDirectLineLogDeriv N τ).im = windingRate τ +
        (deriv (dirichletPoly N) (linePt τ) / dirichletPoly N (linePt τ)).re := by
      simp [completedDirectLineLogDeriv, windingRate, Complex.mul_im]
    rw [hωim]
    dsimp [carrierNetPhaseRate]
    linarith
  have hInt : (b - a) * carrierNetPhaseRate N d a ≤
      ∫ τ in a..b, (completedDirectLineLogDeriv N τ).im := by
    have hsubu : Set.uIcc a b ⊆ U := by
      rwa [Set.uIcc_of_le hab]
    calc
      (b - a) * carrierNetPhaseRate N d a =
          ∫ _ in a..b, carrierNetPhaseRate N d a := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ τ in a..b, (completedDirectLineLogDeriv N τ).im :=
        intervalIntegral.integral_mono_on hab intervalIntegrable_const
          ((hωimc.mono hsubu).intervalIntegrable) hpoint
  have hθadv : θ a + Real.pi ≤ θ b := by
    dsimp [θ]
    rw [intervalIntegral.integral_same, add_zero]
    linarith
  obtain ⟨τ, hτ, hre⟩ := exists_re_zero_of_phase_advance hab hpolar hθc hθadv
  have hzero : completedGN N (linePt τ) = 0 := by
    rw [completedGN_line_eq_direct_add_conj]
    apply Complex.ext <;> simp [hre]
  have hwind : carrierWindingFloor a ≤ windingRate τ :=
    le_trans (winding_floor_expr_mono ha hτ.1)
      (windingRate_ge (lt_of_lt_of_le ha hτ.1))
  have hdom : dirichletLineDerivativeBudget N < d * windingRate τ := by
    dsimp [carrierNetPhaseRate] at hnet0
    have hquot : dirichletLineDerivativeBudget N / d < windingRate τ := by
      linarith
    have := (div_lt_iff₀ hd0).mp hquot
    nlinarith
  exact ⟨τ, hτ, hzero,
    deriv_completedGN_line_zero_ne_zero N τ d hd0 (hDfloor τ hτ) hdom hzero⟩

/-- A simple critical-line carrier zero automatically supplies the exact one-zero analytic
factorization required by the pinned-window gates on some positive-radius ball. -/
theorem completedGN_simple_zero_peel_ball (N : ℕ) (τ : ℝ)
    (hzero : completedGN N (linePt τ) = 0)
    (hsimple : deriv (completedGN N) (linePt τ) ≠ 0) :
    ∃ R > 0, ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball (linePt τ) R) ∧
      (∀ z ∈ ball (linePt τ) R, h z ≠ 0) ∧
      ∀ z ∈ ball (linePt τ) R, completedGN N z = (z - linePt τ) * h z := by
  let U : Set ℂ := {z | 0 < z.re ∧ z.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hcenter : linePt τ ∈ U := by
    dsimp [U]
    exact ⟨linePt_re_pos τ, linePt_re_lt_one τ⟩
  have han : AnalyticAt ℂ (completedGN N) (linePt τ) :=
    completedGN_analyticAt (linePt_re_pos τ) (linePt_re_lt_one τ)
  have horder : analyticOrderAt (completedGN N) (linePt τ) = 1 :=
    han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hsimple
  obtain ⟨h, hhan, hh0, hfact, -⟩ := exists_peel hUopen
    (completedGN_analyticOnNhd_strip N) hcenter horder
  have hev0 : ∀ᶠ z in nhds (linePt τ), h z ≠ 0 :=
    (hhan (linePt τ) hcenter).continuousAt.eventually_ne hh0
  have hevU : ∀ᶠ z in nhds (linePt τ), h z ≠ 0 ∧ z ∈ U :=
    hev0.and (hUopen.mem_nhds hcenter)
  obtain ⟨R, hR0, hball⟩ := Metric.eventually_nhds_iff.mp hevU
  refine ⟨R, hR0, h, ?_, ?_, ?_⟩
  · intro z hz
    exact hhan z (hball (by rwa [mem_ball] at hz)).2
  · intro z hz
    exact (hball (by rwa [mem_ball] at hz)).1
  · intro z hz
    simpa using hfact z (hball (by rwa [mem_ball] at hz)).2

/-- Cofinal center floors spread to fixed-radius intervals and, at high enough height, force
cofinally many simple critical-line zeros of the finite completed carrier. -/
theorem simple_completedGN_zero_cofinal_of_line_floor (N : ℕ) {t₀ d R : ℝ}
    (hd0 : 0 < d) (hR0 : 0 < R)
    (hbudget :
      (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(1 / 2 - R))) * R ≤ t₀ - d)
    (hcofinal : ∀ M : ℝ, ∃ τ, M < τ ∧ t₀ < ‖dirichletPoly N (linePt τ)‖) :
    ∀ M : ℝ, ∃ τ, M < τ ∧ completedGN N (linePt τ) = 0 ∧
      deriv (completedGN N) (linePt τ) ≠ 0 := by
  obtain ⟨A, hA0, hA⟩ := exists_height_carrierNetPhaseRate_ge N
    (d := d) (q := Real.pi / (2 * R))
  intro M
  obtain ⟨τc, hτc, hcenter⟩ := hcofinal (max (M + R) (A + R))
  have hM : M < τc - R := by linarith [lt_of_le_of_lt (le_max_left _ _) hτc]
  have hAleft : A ≤ τc - R := by linarith [lt_of_le_of_lt (le_max_right _ _) hτc]
  have hleft0 : 0 < τc - R := lt_of_lt_of_le hA0 hAleft
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hcenter' : t₀ < ‖dpoly2 (fun _ => 1) (Finset.Icc 1 N) (linePt τc)‖ := by
    rwa [← dirichletPoly_eq_dpoly2]
  have hbudget' :
      (∑ n ∈ Finset.Icc 1 N,
        |(fun _ : ℕ => (1 : ℝ)) n| *
          (Real.log n * (n : ℝ) ^ (-((linePt τc).re - R)))) * R ≤ t₀ - d := by
    rw [linePt_re]
    simpa using hbudget
  have hball := dpoly2_ball_floor (fun _ => (1 : ℝ)) (Finset.Icc 1 N) hs hR0.le
    hcenter' hbudget'
  have hinterval : ∀ τ ∈ Set.Icc (τc - R) (τc + R),
      d ≤ ‖dirichletPoly N (linePt τ)‖ := by
    intro τ hτ
    have hmem : linePt τ ∈ closedBall (linePt τc) R := by
      rw [mem_closedBall, dist_eq_norm, norm_linePt_sub, abs_le]
      constructor <;> linarith [hτ.1, hτ.2]
    rw [dirichletPoly_eq_dpoly2]
    exact (hball (linePt τ) hmem).le
  have hrate : Real.pi / (2 * R) ≤ carrierNetPhaseRate N d (τc - R) :=
    hA (τc - R) hAleft
  have htarget0 : 0 < Real.pi / (2 * R) := div_pos Real.pi_pos (by positivity)
  have hnet0 : 0 < carrierNetPhaseRate N d (τc - R) :=
    lt_of_lt_of_le htarget0 hrate
  have hadvance : Real.pi ≤
      ((τc + R) - (τc - R)) * carrierNetPhaseRate N d (τc - R) := by
    have hm := mul_le_mul_of_nonneg_left hrate (show 0 ≤ 2 * R by positivity)
    have hid : (2 * R) * (Real.pi / (2 * R)) = Real.pi := by
      field_simp
    nlinarith
  obtain ⟨τ, hτ, hzero, hsimple⟩ :=
    exists_simple_completedGN_zero_of_interval_floor N hleft0 (by linarith) hd0
      hinterval hnet0 hadvance
  exact ⟨τ, lt_of_lt_of_le hM hτ.1, hzero, hsimple⟩

/-- The cofinal floor supply therefore yields cofinally many fully factorized simple carrier
centers, not merely points at which a zero is postulated. -/
theorem completedGN_factorized_simple_zero_cofinal_of_line_floor (N : ℕ) {t₀ d R : ℝ}
    (hd0 : 0 < d) (hR0 : 0 < R)
    (hbudget :
      (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(1 / 2 - R))) * R ≤ t₀ - d)
    (hcofinal : ∀ M : ℝ, ∃ τ, M < τ ∧ t₀ < ‖dirichletPoly N (linePt τ)‖) :
    ∀ M : ℝ, ∃ τ R' h,
      M < τ ∧ 0 < R' ∧ completedGN N (linePt τ) = 0 ∧
      deriv (completedGN N) (linePt τ) ≠ 0 ∧
      AnalyticOnNhd ℂ h (ball (linePt τ) R') ∧
      (∀ z ∈ ball (linePt τ) R', h z ≠ 0) ∧
      ∀ z ∈ ball (linePt τ) R', completedGN N z = (z - linePt τ) * h z := by
  intro M
  obtain ⟨τ, hτM, hzero, hsimple⟩ :=
    simple_completedGN_zero_cofinal_of_line_floor N hd0 hR0 hbudget hcofinal M
  obtain ⟨R', hR'0, h, hhan, hh0, hfact⟩ :=
    completedGN_simple_zero_peel_ball N τ hzero hsimple
  exact ⟨τ, R', h, hτM, hR'0, hzero, hsimple, hhan, hh0, hfact⟩

end

end RHTower
