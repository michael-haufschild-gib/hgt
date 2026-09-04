import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLaplaceCriterion
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfSqrtLogScheduleBoundaryNoGo
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfAnchoredCountertermNoGo
import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangleSubpower
import GaloisForLFunctions.HTGeometry.BoundedCoefficientLaplaceMellin
import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference
import GaloisForLFunctions.HTGeometry.FiniteAbscissaDirichletUpperEnd

/-!
# Diagonal Laplace smoothing cannot be locally bounded

At `boundaryExteriorPoint = 6/11`, local boundedness of the pole-cleared diagonal Laplace family
would force its underlying heat samples to decay geometrically.  Adjacent heat times are close
enough that the bounded coefficient estimate makes the full heat profile bounded near zero.
Its Mellin transform would then continue the canonical convolution-half Dirichlet series across
the zeta pole at one, which is impossible.
-/

open Complex Filter Metric Set Topology Asymptotics MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Boundary coefficient stream whose heat profile contains the diagonal Laplace samples. -/
def squarefreeHalfBoundaryLaplaceCoeff (n : ℕ) : ℂ :=
  LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint n

/-- Continuous heat-time profile attached to the boundary coefficient stream. -/
def squarefreeHalfBoundaryLaplaceProfile (x : ℝ) : ℂ :=
  coeffLaplaceProfile squarefreeHalfBoundaryLaplaceCoeff x

/-- Local boundedness of the normalized family forces geometric decay of every sufficiently late
boundary heat sample. -/
theorem exists_geometric_bound_squarefreeHalfLaplaceSum_boundary_of_locallyBounded
    (hloc : PoleClearedFirstTraceLaplaceLocallyBounded) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 24 ≤ N →
      (5 : ℝ) ^ (N - 24) *
        ‖squarefreeHalfLaplaceSum N boundaryExteriorPoint‖ ≤ K := by
  obtain ⟨R, hR, _, C, hC⟩ :=
    hloc boundaryExteriorPoint boundaryExteriorPoint_mem_rightHalf
  have hcenter : boundaryExteriorPoint ∈ ball boundaryExteriorPoint R := mem_ball_self hR
  have hbound : ∀ N : ℕ,
      ‖poleClearedFirstTraceLaplaceApprox N boundaryExteriorPoint‖ ≤ C :=
    fun N => hC N boundaryExteriorPoint hcenter
  have hCnonneg : 0 ≤ C :=
    (norm_nonneg (poleClearedFirstTraceLaplaceApprox 0 boundaryExteriorPoint)).trans (hbound 0)
  let K : ℝ := C * ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hKnonneg, ?_⟩
  intro N hN
  have hfactor := norm_poleFactorSqrtApprox_boundaryExteriorPoint_five_pow hN
  have hdetpos : 0 < ‖squarefreeCarlemanHalfDet boundaryExteriorPoint‖ :=
    norm_pos_iff.mpr (squarefreeCarlemanHalfDet_ne_zero boundaryExteriorPoint)
  have hsource := hbound N
  have hprod :
      ‖poleFactorSqrtApprox N boundaryExteriorPoint‖ *
          ‖squarefreeHalfLaplaceSum N boundaryExteriorPoint‖ ≤ K := by
    rw [poleClearedFirstTraceLaplaceApprox, norm_div, norm_mul] at hsource
    exact (div_le_iff₀ hdetpos).mp hsource
  exact (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans hprod

/-- The discrete smoothing is exactly the continuous boundary profile at time `1/(N+1)`. -/
theorem squarefreeHalfBoundaryLaplaceProfile_scale (N : ℕ) :
    squarefreeHalfBoundaryLaplaceProfile (squarefreeHalfLaplaceScale N) =
      squarefreeHalfLaplaceSum N boundaryExteriorPoint := by
  unfold squarefreeHalfBoundaryLaplaceProfile coeffLaplaceProfile squarefreeHalfLaplaceSum
    squarefreeHalfBoundaryLaplaceCoeff squarefreeHalfLaplaceTerm
  apply tsum_congr
  intro n
  ring

/-- The shifted boundary coefficients remain bounded by one. -/
theorem norm_squarefreeHalfBoundaryLaplaceCoeff_le_one (n : ℕ) :
    ‖squarefreeHalfBoundaryLaplaceCoeff n‖ ≤ 1 := by
  unfold squarefreeHalfBoundaryLaplaceCoeff
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_zero]
  rw [LSeries.norm_term_eq, if_neg hn]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  have hden : 1 ≤ (n : ℝ) ^ boundaryExteriorPoint.re := by
    apply Real.one_le_rpow hn1
    norm_num [boundaryExteriorPoint]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one hden)).2
    ((norm_squarefreeConvolutionHalf_le_one n).trans hden)

@[simp] theorem squarefreeHalfBoundaryLaplaceCoeff_zero :
    squarefreeHalfBoundaryLaplaceCoeff 0 = 0 := by
  simp [squarefreeHalfBoundaryLaplaceCoeff, LSeries.term_zero]

/-- Concrete boundedness interface needed at the zero end of the Mellin integral. -/
def SquarefreeHalfBoundaryLaplaceBoundedAtZero : Prop :=
  ∃ C delta : ℝ, 0 ≤ C ∧ 0 < delta ∧
    ∀ x : ℝ, 0 < x → x < delta →
      ‖squarefreeHalfBoundaryLaplaceProfile x‖ ≤ C

theorem SquarefreeHalfBoundaryLaplaceBoundedAtZero.isBigO
    (hbound : SquarefreeHalfBoundaryLaplaceBoundedAtZero) :
    squarefreeHalfBoundaryLaplaceProfile =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) := by
  rcases hbound with ⟨C, delta, hC, hdelta, hbound⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < delta :=
    (eventually_lt_nhds hdelta).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with x hx hxd
  simpa [hC] using hbound x hx hxd

theorem squarefreeHalfBoundaryLaplaceProfile_locallyIntegrableOn :
    LocallyIntegrableOn squarefreeHalfBoundaryLaplaceProfile (Ioi 0) := by
  change LocallyIntegrableOn
    (coeffLaplaceProfile squarefreeHalfBoundaryLaplaceCoeff) (Ioi 0)
  exact coeffLaplaceProfile_locallyIntegrableOn
    norm_squarefreeHalfBoundaryLaplaceCoeff_le_one

theorem squarefreeHalfBoundaryLaplaceProfile_isBigO_exp_neg :
    squarefreeHalfBoundaryLaplaceProfile =O[atTop]
      (fun x : ℝ => Real.exp (-1 * x)) := by
  change coeffLaplaceProfile squarefreeHalfBoundaryLaplaceCoeff =O[atTop]
    (fun x : ℝ => Real.exp (-1 * x))
  exact coeffLaplaceProfile_isBigO_exp_neg
    norm_squarefreeHalfBoundaryLaplaceCoeff_le_one
    squarefreeHalfBoundaryLaplaceCoeff_zero

/-- A mere uniform bound at zero already makes the boundary-profile Mellin transform holomorphic
on the positive half-plane. -/
theorem analyticOnNhd_mellin_squarefreeHalfBoundaryLaplaceProfile_of_boundedAtZero
    (hbound : SquarefreeHalfBoundaryLaplaceBoundedAtZero) :
    AnalyticOnNhd ℂ (mellin squarefreeHalfBoundaryLaplaceProfile) {z : ℂ | 0 < z.re} := by
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
    (isOpen_lt continuous_const Complex.continuous_re)
  exact (mellin_differentiableAt_of_isBigO_rpow_exp
    (a := 1) (b := 0) (by norm_num)
    squarefreeHalfBoundaryLaplaceProfile_locallyIntegrableOn
    squarefreeHalfBoundaryLaplaceProfile_isBigO_exp_neg
    (by simpa using hbound.isBigO) hz).differentiableWithinAt

/-- The boundary stream is the standard Dirichlet shift by `6/11`. -/
theorem squarefreeHalfBoundaryLaplaceCoeff_eq_dirichletShift (n : ℕ) :
    squarefreeHalfBoundaryLaplaceCoeff n =
      dirichletShift boundaryExteriorPoint squarefreeConvolutionHalf n := by
  unfold squarefreeHalfBoundaryLaplaceCoeff
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term_zero]
  have h := dirichletShift_LSeries_term
    boundaryExteriorPoint (0 : ℂ) squarefreeConvolutionHalf n
  calc
    LSeries.term squarefreeConvolutionHalf boundaryExteriorPoint n =
        LSeries.term (fun m => dirichletShift boundaryExteriorPoint
          squarefreeConvolutionHalf m) 0 n := by simpa using h.symm
    _ = dirichletShift boundaryExteriorPoint squarefreeConvolutionHalf n := by
      rw [LSeries.term_of_ne_zero hn]
      simp

/-- The L-series of the boundary stream translates back to the canonical arithmetic half. -/
theorem LSeries_squarefreeHalfBoundaryLaplaceCoeff (z : ℂ) :
    LSeries squarefreeHalfBoundaryLaplaceCoeff z =
      LSeries squarefreeConvolutionHalf (z + boundaryExteriorPoint) := by
  rw [show squarefreeHalfBoundaryLaplaceCoeff =
      fun n => dirichletShift boundaryExteriorPoint squarefreeConvolutionHalf n by
    funext n
    exact squarefreeHalfBoundaryLaplaceCoeff_eq_dirichletShift n]
  exact LSeries_dirichletShift boundaryExteriorPoint z squarefreeConvolutionHalf

/-- Translate the Mellin variable and remove its Gamma factor by the entire reciprocal Gamma. -/
def squarefreeHalfBoundaryMellinContinuation (s : ℂ) : ℂ :=
  mellin squarefreeHalfBoundaryLaplaceProfile (s - boundaryExteriorPoint) *
    (Complex.Gamma (s - boundaryExteriorPoint))⁻¹

theorem analyticOnNhd_squarefreeHalfBoundaryMellinContinuation
    (hbound : SquarefreeHalfBoundaryLaplaceBoundedAtZero) :
    AnalyticOnNhd ℂ squarefreeHalfBoundaryMellinContinuation
      {s : ℂ | boundaryExteriorPoint.re < s.re} := by
  let hM :=
    analyticOnNhd_mellin_squarefreeHalfBoundaryLaplaceProfile_of_boundedAtZero hbound
  intro s hs
  have hz : 0 < (s - boundaryExteriorPoint).re := by
    simpa only [Complex.sub_re] using sub_pos.mpr hs
  let inner : ℂ → ℂ := fun w => w - boundaryExteriorPoint
  have hinner : AnalyticAt ℂ inner s := by
    dsimp [inner]
    fun_prop
  have hMouter : AnalyticAt ℂ
      (mellin squarefreeHalfBoundaryLaplaceProfile) (inner s) := by
    simpa [inner] using hM (s - boundaryExteriorPoint) hz
  have hMshift : AnalyticAt ℂ
      (fun w : ℂ => mellin squarefreeHalfBoundaryLaplaceProfile
        (w - boundaryExteriorPoint)) s :=
    by simpa [inner, Function.comp_def] using hMouter.comp hinner
  have hGammaOuter : AnalyticAt ℂ
      (fun z : ℂ => (Complex.Gamma z)⁻¹) (inner s) :=
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd
      isOpen_univ) (inner s) (Set.mem_univ _)
  have hGamma : AnalyticAt ℂ
      (fun w : ℂ => (Complex.Gamma (w - boundaryExteriorPoint))⁻¹) s :=
    by simpa [inner, Function.comp_def] using hGammaOuter.comp hinner
  exact hMshift.mul hGamma

/-- On the absolute-convergence overlap, the translated Mellin continuation is the canonical
convolution-half L-series. -/
theorem squarefreeHalfBoundaryMellinContinuation_eq_LSeries
    {s : ℂ} (hs : 1 < (s - boundaryExteriorPoint).re) :
    squarefreeHalfBoundaryMellinContinuation s =
      LSeries squarefreeConvolutionHalf s := by
  have hmellin :
      mellin squarefreeHalfBoundaryLaplaceProfile (s - boundaryExteriorPoint) =
        Complex.Gamma (s - boundaryExteriorPoint) *
          LSeries squarefreeHalfBoundaryLaplaceCoeff
            (s - boundaryExteriorPoint) := by
    change mellin (coeffLaplaceProfile squarefreeHalfBoundaryLaplaceCoeff)
      (s - boundaryExteriorPoint) =
        Complex.Gamma (s - boundaryExteriorPoint) *
          LSeries squarefreeHalfBoundaryLaplaceCoeff
            (s - boundaryExteriorPoint)
    exact mellin_coeffLaplaceProfile_eq_gamma_mul_LSeries
      norm_squarefreeHalfBoundaryLaplaceCoeff_le_one
      squarefreeHalfBoundaryLaplaceCoeff_zero hs
  have hgamma : Complex.Gamma (s - boundaryExteriorPoint) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (lt_trans zero_lt_one hs)
  rw [squarefreeHalfBoundaryMellinContinuation, hmellin,
    LSeries_squarefreeHalfBoundaryLaplaceCoeff]
  have hadd : s - boundaryExteriorPoint + boundaryExteriorPoint = s := by ring
  rw [hadd]
  field_simp

/-- A bounded zero-end profile would analytically continue its square across the zeta pole at one,
contradicting the nonzero zeta residue unit. -/
theorem not_squarefreeHalfBoundaryLaplaceBoundedAtZero :
    ¬ SquarefreeHalfBoundaryLaplaceBoundedAtZero := by
  intro hbound
  let G : ℂ → ℂ := squarefreeHalfBoundaryMellinContinuation
  let U : Set ℂ := {s : ℂ | boundaryExteriorPoint.re < s.re}
  have hGana : AnalyticOnNhd ℂ G U := by
    simpa [G, U] using
      analyticOnNhd_squarefreeHalfBoundaryMellinContinuation hbound
  let H : ℂ → ℂ := fun s =>
    (s - 1) * G s ^ 2 * riemannZeta (2 * s) - zetaResidueUnit s
  have hHana : AnalyticOnNhd ℂ H U := by
    intro s hs
    have htwo : 2 * s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [U, boundaryExteriorPoint] at hs hre
      linarith
    exact (((show AnalyticAt ℂ (fun z : ℂ => z - 1) s by fun_prop).mul
      ((hGana s hs).pow 2)).mul
      ((analyticOn_riemannZeta (2 * s) htwo).comp (by fun_prop))).sub
      (analyticAt_zetaResidueUnit s)
  have hzeroNearTwo : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), H s = 0 := by
    have hgt : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), (17 / 11 : ℝ) < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with s hs
    have hshift : 1 < (s - boundaryExteriorPoint).re := by
      norm_num [boundaryExteriorPoint] at hs ⊢
      linarith
    have hs1 : 1 < s.re := by linarith
    have htwo : riemannZeta (2 * s) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by norm_num; linarith)
    have htwo' : riemannZeta (s * 2) ≠ 0 := by simpa [mul_comm] using htwo
    have hsne : s ≠ 1 := by
      intro h
      rw [h] at hs1
      norm_num at hs1
    dsimp [H]
    rw [show G s = LSeries squarefreeConvolutionHalf s by
      simpa [G] using squarefreeHalfBoundaryMellinContinuation_eq_LSeries hshift]
    rw [LSeries_squarefreeConvolutionHalf_sq hs1]
    rw [zetaResidueUnit, Function.update_of_ne hsne]
    field_simp [htwo']
    ring
  have hUpre : IsPreconnected U := by
    exact (convex_halfSpace_re_gt boundaryExteriorPoint.re).isPreconnected
  have honeU : (1 : ℂ) ∈ U := by
    norm_num [U, boundaryExteriorPoint]
  have htwoU : (2 : ℂ) ∈ U := by
    norm_num [U, boundaryExteriorPoint]
  have hfreq : ∃ᶠ s in 𝓝[≠] (2 : ℂ), H s = 0 :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds hzeroNearTwo).frequently
  have hzeroAll := hHana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hUpre htwoU hfreq
  have hzero := hzeroAll honeU
  dsimp [H] at hzero
  rw [zetaResidueUnit_one] at hzero
  norm_num at hzero

private theorem norm_exp_neg_nat_mul_sub_le
    (n : ℕ) {x y q : ℝ} (hqx : q ≤ x) (hqy : q ≤ y) :
    ‖Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
        Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ))‖ ≤
      Real.exp (-((n : ℝ) * q)) * (n : ℝ) * |x - y| := by
  have ha : -((n : ℝ) * x) ≤ -((n : ℝ) * q) := by
    exact neg_le_neg (mul_le_mul_of_nonneg_left hqx (Nat.cast_nonneg n))
  have hb : -((n : ℝ) * y) ≤ -((n : ℝ) * q) := by
    exact neg_le_neg (mul_le_mul_of_nonneg_left hqy (Nat.cast_nonneg n))
  have h := abs_exp_sub_exp_le ha hb
  have harg :
      |-((n : ℝ) * x) - -((n : ℝ) * y)| = (n : ℝ) * |x - y| := by
    rw [show -((n : ℝ) * x) - -((n : ℝ) * y) = -(n : ℝ) * (x - y) by ring,
      abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
  rw [show -(((n : ℝ) * x : ℝ) : ℂ) = ((-((n : ℝ) * x) : ℝ) : ℂ) by push_cast; ring,
    show -(((n : ℝ) * y : ℝ) : ℂ) = ((-((n : ℝ) * y) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    |Real.exp (-((n : ℝ) * x)) - Real.exp (-((n : ℝ) * y))| ≤
        Real.exp (-((n : ℝ) * q)) *
          |-((n : ℝ) * x) - -((n : ℝ) * y)| := h
    _ = Real.exp (-((n : ℝ) * q)) * (n : ℝ) * |x - y| := by rw [harg]; ring

/-- Quantitative interpolation bound for the boundary heat profile. -/
theorem norm_squarefreeHalfBoundaryLaplaceProfile_sub_le
    {x y q : ℝ} (hx : 0 < x) (hy : 0 < y) (hq : 0 < q)
    (hqx : q ≤ x) (hqy : q ≤ y) :
    ‖squarefreeHalfBoundaryLaplaceProfile x -
        squarefreeHalfBoundaryLaplaceProfile y‖ ≤
      |x - y| *
        (1 + Real.exp q * 2 ^ (1 : ℝ) * (1 / q) ^ (2 : ℝ) *
          Real.Gamma 2) := by
  let u : ℕ → ℝ := fun n =>
    ((n : ℝ) + 1) ^ (1 : ℝ) * Real.exp (-((n : ℝ) * q)) * |x - y|
  have hxsum := summable_coeffLaplaceTerm
    norm_squarefreeHalfBoundaryLaplaceCoeff_le_one hx
  have hysum := summable_coeffLaplaceTerm
    norm_squarefreeHalfBoundaryLaplaceCoeff_le_one hy
  have hmoment := summable_natSucc_rpow_exp_neg_and_tsum_le
    (r := (1 : ℝ)) (x := q) (by norm_num) hq
  have hu : Summable u := by
    have h := hmoment.1.mul_right |x - y|
    simpa only [u, mul_assoc] using h
  have hmomentBound :
      (∑' n : ℕ, ((n : ℝ) + 1) ^ (1 : ℝ) *
        Real.exp (-((n : ℝ) * q))) ≤
      1 + Real.exp q * 2 ^ (1 : ℝ) * (1 / q) ^ (2 : ℝ) *
        Real.Gamma 2 := by
    convert hmoment.2 using 1 <;> norm_num
  have hterm : ∀ n : ℕ,
      ‖squarefreeHalfBoundaryLaplaceCoeff n *
          Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
        squarefreeHalfBoundaryLaplaceCoeff n *
          Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ))‖ ≤ u n := by
    intro n
    rw [← mul_sub, norm_mul]
    have hexp := norm_exp_neg_nat_mul_sub_le n hqx hqy
    have hcoeff := norm_squarefreeHalfBoundaryLaplaceCoeff_le_one n
    have hnle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    dsimp [u]
    rw [Real.rpow_one]
    calc
      ‖squarefreeHalfBoundaryLaplaceCoeff n‖ *
          ‖Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
            Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ))‖ ≤
          1 * (Real.exp (-((n : ℝ) * q)) * (n : ℝ) * |x - y|) :=
        mul_le_mul hcoeff hexp (norm_nonneg _) (by positivity)
      _ ≤ ((n : ℝ) + 1) * Real.exp (-((n : ℝ) * q)) * |x - y| := by
        have hexpnonneg : 0 ≤ Real.exp (-((n : ℝ) * q)) := (Real.exp_pos _).le
        nlinarith [abs_nonneg (x - y)]
  have hdiff : Summable fun n : ℕ =>
      ‖squarefreeHalfBoundaryLaplaceCoeff n *
          Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
        squarefreeHalfBoundaryLaplaceCoeff n *
          Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ))‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hu
  unfold squarefreeHalfBoundaryLaplaceProfile coeffLaplaceProfile
  rw [← hxsum.tsum_sub hysum]
  calc
    ‖∑' n : ℕ,
        (squarefreeHalfBoundaryLaplaceCoeff n *
            Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
          squarefreeHalfBoundaryLaplaceCoeff n *
            Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ)))‖ ≤
        ∑' n : ℕ,
          ‖squarefreeHalfBoundaryLaplaceCoeff n *
              Complex.exp (-(((n : ℝ) * x : ℝ) : ℂ)) -
            squarefreeHalfBoundaryLaplaceCoeff n *
              Complex.exp (-(((n : ℝ) * y : ℝ) : ℂ))‖ :=
      norm_tsum_le_tsum_norm hdiff
    _ ≤ ∑' n : ℕ, u n := hdiff.tsum_le_tsum hterm hu
    _ = (∑' n : ℕ,
          ((n : ℝ) + 1) ^ (1 : ℝ) * Real.exp (-((n : ℝ) * q))) *
          |x - y| := by
      rw [tsum_mul_right]
    _ ≤ (1 + Real.exp q * 2 ^ (1 : ℝ) * (1 / q) ^ (2 : ℝ) *
          Real.Gamma 2) * |x - y| :=
      mul_le_mul_of_nonneg_right hmomentBound (abs_nonneg _)
    _ = |x - y| *
        (1 + Real.exp q * 2 ^ (1 : ℝ) * (1 / q) ^ (2 : ℝ) *
          Real.Gamma 2) := by ring

end

end RHTower
