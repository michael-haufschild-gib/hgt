import GaloisForLFunctions.SelbergClass.OrdinaryMellinContourShift
import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversionGeneralLine
import GaloisForLFunctions.SelbergClass.OrdinaryExponentialMellin
import GaloisForLFunctions.RHTower.SelbergStripPolynomialGrowth
import GaloisForLFunctions.RHTower.SelbergClass.BarnesHorizontalEdges

/-!
# The exponential series as a far-left Mellin integral

For any Gamma presentation and every far-left line `Re u = −K − ½`, on the whole right half-plane

`Σ a(n) e^{−nz} = P(z) + Σ_{k ≤ K} (−z)^k F(−k)/k! + (1/2π) ∫ z^{−u} Γ(u) F(u) dt`,

where `P` is the polar part at `u = 1` (`ordinaryExponentialSeries_eq_left`).  No degree restriction
enters: on real `z = x > 0` this is a contour shift, and both sides are holomorphic in `z`.
-/

noncomputable section

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace GaloisForLFunctions.SelbergClass.DegreeOne

/-- A sufficiently far left line lies past every Gamma factor of the presentation. -/
theorem exists_farLeft (G : SelbergGammaData) :
    ∃ K : ℕ, (-(K : ℝ) - 1 / 2) < -1 ∧
      ∀ j, G.lambda j * (-(K : ℝ) - 1 / 2) < 1 - (G.mu j).re := by
  have h1 : ∀ᶠ K : ℕ in atTop, (-(K : ℝ) - 1 / 2) < -1 := by
    filter_upwards [eventually_ge_atTop 1] with K hK
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have h2 : ∀ᶠ K : ℕ in atTop, ∀ j, G.lambda j * (-(K : ℝ) - 1 / 2) < 1 - (G.mu j).re := by
    refine Filter.eventually_all.2 fun j => ?_
    have hl := G.lambda_pos j
    obtain ⟨n, hn⟩ := exists_nat_gt (((G.mu j).re - 1) / G.lambda j)
    filter_upwards [eventually_ge_atTop n] with K hK
    have hK' : (n : ℝ) ≤ K := by exact_mod_cast hK
    have hlt : ((G.mu j).re - 1) / G.lambda j < K := hn.trans_le hK'
    rw [div_lt_iff₀ hl] at hlt
    have e : G.lambda j * (-(K : ℝ) - 1 / 2) = -((K : ℝ) * G.lambda j) - G.lambda j / 2 := by ring
    rw [e]
    linarith
  exact (h1.and h2).exists

theorem leftLine_ne_neg_nat (K : ℕ) (t : ℝ) (k : ℕ) : leftLine K t ≠ -(k : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp [leftLine] at hre
  have h2 : (2 : ℝ) * K + 1 = 2 * k := by linarith
  have h3 : 2 * K + 1 = 2 * k := by exact_mod_cast h2
  omega

theorem leftLine_ne_one (K : ℕ) (t : ℝ) : (0 : ℂ) + leftLine K t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp [leftLine] at hre
  have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  linarith

/-- The Mellin integrand is continuous on a far-left line. -/
theorem continuous_leftIntegrand (F : ExtendedSelbergClass) (K : ℕ) {z : ℂ} (hz : z ≠ 0) :
    Continuous fun t : ℝ => ordinaryMellinIntegrand F 0 z (leftLine K t) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have h := analyticAt_ordinaryMellinIntegrand F 0 hz (u := leftLine K t)
    (leftLine_ne_neg_nat K t) (leftLine_ne_one K t)
  exact ContinuousAt.comp (f := fun t : ℝ => leftLine K t) h.continuousAt
    (by unfold leftLine; fun_prop)

/-- The function `Γ(u) F(u)` on a far-left line. -/
def leftValue (F : ExtendedSelbergClass) (K : ℕ) (t : ℝ) : ℂ :=
  Complex.Gamma (leftLine K t) * F (0 + leftLine K t)

theorem continuous_leftValue (F : ExtendedSelbergClass) (K : ℕ) : Continuous (leftValue F K) := by
  have h := continuous_leftIntegrand F K (z := 1) one_ne_zero
  refine h.congr fun t => ?_
  simp [ordinaryMellinIntegrand, leftValue]

/-- `Γ` decays at rate `π/2` on every vertical line through a non-pole abscissa. -/
theorem exists_bound_Gamma_leftLine (K : ℕ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      ‖Complex.Gamma (leftLine K t)‖ ≤ C * (1 + |t|) ^ N * Real.exp (-(π * |t| / 2)) := by
  obtain ⟨C₁, N, hC₁, hb⟩ := exists_bound_norm_Gamma_vertical_strip_arbitrary
    (a := -(K : ℝ) - 1 / 2) (b := -(K : ℝ) - 1 / 2)
  have hcont : Continuous fun t : ℝ => ‖Complex.Gamma (leftLine K t)‖ := by
    have h := (continuous_iff_continuousAt.mpr fun t =>
      ContinuousAt.comp (f := fun t : ℝ => leftLine K t)
        (Complex.differentiableAt_Gamma _ (leftLine_ne_neg_nat K t)).continuousAt
        (by unfold leftLine; fun_prop))
    exact h.norm
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image hcont.continuousOn
  have hM' : ∀ t ∈ Icc (-1 : ℝ) 1, ‖Complex.Gamma (leftLine K t)‖ ≤ |M| := fun t ht =>
    (hM ⟨t, ht, rfl⟩).trans (le_abs_self M)
  refine ⟨C₁ + |M| * Real.exp (π / 2), N, by positivity, fun t => ?_⟩
  have hexp := Real.exp_pos (-(π * |t| / 2))
  have hone : (1 : ℝ) ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
  by_cases ht : 1 ≤ |t|
  · have h := hb _ t le_rfl le_rfl ht
    have hle : |t| ^ N ≤ (1 + |t|) ^ N := pow_le_pow_left₀ (abs_nonneg t) (by linarith) N
    calc ‖Complex.Gamma (leftLine K t)‖ ≤ C₁ * |t| ^ N * Real.exp (-(π * |t| / 2)) := by
          simpa [leftLine] using h
      _ ≤ C₁ * (1 + |t|) ^ N * Real.exp (-(π * |t| / 2)) := by gcongr
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hexp.le
          have : 0 ≤ |M| * Real.exp (π / 2) := by positivity
          linarith
  · have ht1 : |t| ≤ 1 := (not_le.mp ht).le
    have hmem : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp ht1
    have hE : 1 ≤ Real.exp (π / 2) * Real.exp (-(π * |t| / 2)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have := Real.pi_pos
      nlinarith
    calc ‖Complex.Gamma (leftLine K t)‖ ≤ |M| := hM' t hmem
      _ ≤ |M| * (Real.exp (π / 2) * Real.exp (-(π * |t| / 2))) :=
          le_mul_of_one_le_right (abs_nonneg M) hE
      _ ≤ (|M| * Real.exp (π / 2)) * (1 + |t|) ^ N * Real.exp (-(π * |t| / 2)) := by
          have h0 : 0 ≤ |M| * Real.exp (π / 2) * Real.exp (-(π * |t| / 2)) := by positivity
          nlinarith
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) hexp.le
          linarith

/-- Rapid decay of `Γ(u)F(u)` on a far-left line. -/
theorem exists_bound_leftValue (F : ExtendedSelbergClass) {K : ℕ} (ha : (-(K : ℝ) - 1 / 2) < -1)
    (haμ : ∀ j, F.gammaData.lambda j * (-(K : ℝ) - 1 / 2) < 1 - (F.gammaData.mu j).re) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      ‖leftValue F K t‖ ≤ C * (1 + |t|) ^ N * Real.exp (-(π * |t| / 2)) := by
  obtain ⟨C₁, N₁, hC₁, hb₁⟩ := exists_bound_Gamma_leftLine K
  obtain ⟨C₂, N₂, hC₂, hb₂⟩ := F.exists_bound_left_line ha haμ
  refine ⟨C₁ * C₂, N₁ + N₂, by positivity, fun t => ?_⟩
  have h₂ := hb₂ (0 + leftLine K t) (by simp [leftLine])
  have him : ((0 : ℂ) + leftLine K t).im = t := by simp [leftLine]
  rw [him] at h₂
  have hexp := (Real.exp_pos (-(π * |t| / 2))).le
  unfold leftValue
  rw [norm_mul, pow_add]
  calc _ ≤ (C₁ * (1 + |t|) ^ N₁ * Real.exp (-(π * |t| / 2))) * (C₂ * (1 + |t|) ^ N₂) :=
        mul_le_mul (hb₁ t) h₂ (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- `‖z‖^{-c}` is bounded on an annulus, whatever the sign of `c`. -/
theorem rpow_neg_le_add {q Q x c : ℝ} (hq : 0 < q) (hqx : q ≤ x) (hxQ : x ≤ Q) :
    x ^ (-c) ≤ q ^ (-c) + Q ^ (-c) := by
  have hx : 0 < x := hq.trans_le hqx
  have hQ : 0 < Q := hx.trans_le hxQ
  rcases le_total 0 (-c) with h | h
  · have := Real.rpow_le_rpow hx.le hxQ h
    linarith [Real.rpow_pos_of_pos hq (-c)]
  · have := Real.rpow_le_rpow_of_nonpos hq hqx h
    linarith [Real.rpow_pos_of_pos hQ (-c)]

/-- Inverse Mellin integrals of functions with Gamma-type decay are holomorphic on the right
half-plane. -/
theorem differentiableAt_mellinLine {σ : ℝ} {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hb : ∀ t : ℝ, ‖g t‖ ≤ C * (1 + |t|) ^ N * Real.exp (-(π * |t| / 2)))
    {z₀ : ℂ} (hz₀re : 0 < z₀.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∫ t : ℝ, z ^ (-((σ : ℂ) + (t : ℂ) * I)) * g t) z₀ := by
  let θ : ℝ := (|Complex.arg z₀| + π / 2) / 2
  have hz₀ne : z₀ ≠ 0 := by
    intro h
    rw [h] at hz₀re
    simp at hz₀re
  have harg₀ : |Complex.arg z₀| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz₀re)
  have hargθ : |Complex.arg z₀| < θ := by
    dsimp only [θ]
    linarith
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans hargθ.le
  have hθ : θ < π / 2 := by
    dsimp only [θ]
    linarith
  have hz₀pos : 0 < ‖z₀‖ := norm_pos_iff.mpr hz₀ne
  let q : ℝ := ‖z₀‖ / 2
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  let Q : ℝ := 2 * ‖z₀‖
  have hslit₀ : z₀ ∈ Complex.slitPlane := Or.inl hz₀re
  let S : Set ℂ := {z | |Complex.arg z| < θ ∧ q < ‖z‖ ∧ ‖z‖ < Q}
  have hS : S ∈ 𝓝 z₀ := by
    have hargEv : ∀ᶠ z in 𝓝 z₀, |Complex.arg z| < θ :=
      (Complex.continuousAt_arg hslit₀).abs.eventually_lt continuousAt_const hargθ
    have hqEv : ∀ᶠ z in 𝓝 z₀, q < ‖z‖ :=
      continuousAt_const.eventually_lt continuousAt_id.norm (by dsimp only [q, id]; linarith)
    have hQEv : ∀ᶠ z in 𝓝 z₀, ‖z‖ < Q :=
      continuousAt_id.norm.eventually_lt continuousAt_const (by dsimp only [Q, id]; linarith)
    filter_upwards [hargEv, hqEv, hQEv] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hSne : ∀ z ∈ S, z ≠ 0 := by
    intro z hz h0
    have h2 := hz.2.1
    rw [h0, norm_zero] at h2
    exact absurd h2 (not_lt.mpr hq.le)
  have hSre : ∀ z ∈ S, 0 < z.re := by
    intro z hz
    have h := Complex.abs_arg_lt_pi_div_two_iff.mp (hz.1.trans hθ)
    rcases h with h | h
    · exact h
    · exact absurd h (hSne z hz)
  let W : ℝ → ℂ := fun t => (σ : ℂ) + (t : ℂ) * I
  have hWc : Continuous W := by
    dsimp only [W]
    fun_prop
  let F : ℂ → ℝ → ℂ := fun z t => z ^ (-W t) * g t
  let F' : ℂ → ℝ → ℂ := fun z t => (-W t) * z ^ (-(W t) - 1) * g t
  let r : ℝ := π / 2 - θ
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hweight : ∀ (x : ℝ), 0 ≤ x → ∀ (z : ℂ), z ∈ S → ∀ t : ℝ,
      Real.exp (|Complex.arg z| * |t|) * Real.exp (-(π * |t| / 2)) ≤ Real.exp (-r * |t|) := by
    intro _ _ z hz t
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h := mul_le_mul_of_nonneg_right hz.1.le (abs_nonneg t)
    dsimp only [r]
    linarith
  have hnormF : ∀ z ∈ S, ∀ t : ℝ, ‖F z t‖ ≤
      (q ^ (-σ) + Q ^ (-σ)) * C * ((1 + |t|) ^ N * Real.exp (-r * |t|)) := by
    intro z hz t
    have hcp := norm_cpow_neg_line_add_mul_I_le σ z (hSne z hz) t
    have hp := rpow_neg_le_add (c := σ) hq hz.2.1.le hz.2.2.le
    have hw := hweight 0 le_rfl z hz t
    have hgt := hb t
    have hB : 0 ≤ q ^ (-σ) + Q ^ (-σ) := add_nonneg (Real.rpow_nonneg hq.le _)
      (Real.rpow_nonneg (by dsimp only [Q]; positivity) _)
    have hE0 := (Real.exp_pos (|Complex.arg z| * |t|)).le
    have hpow0 : 0 ≤ (1 + |t|) ^ N := by positivity
    dsimp only [F, W]
    rw [norm_mul]
    calc _ ≤ ((q ^ (-σ) + Q ^ (-σ)) * Real.exp (|Complex.arg z| * |t|)) *
          (C * (1 + |t|) ^ N * Real.exp (-(π * |t| / 2))) :=
          mul_le_mul (hcp.trans (mul_le_mul_of_nonneg_right hp hE0)) hgt (norm_nonneg _)
            (mul_nonneg hB hE0)
      _ = (q ^ (-σ) + Q ^ (-σ)) * C * (1 + |t|) ^ N *
          (Real.exp (|Complex.arg z| * |t|) * Real.exp (-(π * |t| / 2))) := by ring
      _ ≤ (q ^ (-σ) + Q ^ (-σ)) * C * (1 + |t|) ^ N * Real.exp (-r * |t|) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring
  have hzS : z₀ ∈ S := mem_of_mem_nhds hS
  have hFcont : ∀ z ∈ S, Continuous (F z) := by
    intro z hz
    have hpow : Continuous fun t : ℝ => z ^ (-W t) :=
      Continuous.const_cpow hWc.neg (Or.inl (hSne z hz))
    exact hpow.mul hg
  have hint₀ := integrable_one_add_abs_pow_mul_exp_neg_abs N hr
  have hFint : Integrable (F z₀) :=
    (hint₀.const_mul _).mono' (hFcont z₀ hzS).aestronglyMeasurable
      (Eventually.of_forall (hnormF z₀ hzS))
  have hFmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) volume := by
    filter_upwards [hS] with z hz
    exact (hFcont z hz).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' z₀) volume := by
    have hpow : Continuous fun t : ℝ => z₀ ^ (-(W t) - 1) :=
      Continuous.const_cpow (hWc.neg.sub continuous_const) (Or.inl hz₀ne)
    exact ((hWc.neg.mul hpow).mul hg).aestronglyMeasurable
  let bound : ℝ → ℝ := fun t =>
    (|σ| + 1) * (q ^ (-(σ + 1)) + Q ^ (-(σ + 1))) * C * ((1 + |t|) ^ (N + 1) * Real.exp (-r * |t|))
  have hbound : Integrable bound := by
    dsimp only [bound]
    exact (integrable_one_add_abs_pow_mul_exp_neg_abs (N + 1) hr).const_mul _
  have hderivBound : ∀ᵐ t : ℝ ∂volume, ∀ z ∈ S, ‖F' z t‖ ≤ bound t := by
    refine Eventually.of_forall fun t z hz => ?_
    have hexpForm : -(W t) - 1 = -(((σ + 1 : ℝ) : ℂ) + (t : ℂ) * I) := by
      dsimp only [W]
      push_cast
      ring
    have hcp := norm_cpow_neg_line_add_mul_I_le (σ + 1) z (hSne z hz) t
    have hp := rpow_neg_le_add (c := σ + 1) hq hz.2.1.le hz.2.2.le
    have hw := hweight 0 le_rfl z hz t
    have hgt := hb t
    have hB : 0 ≤ q ^ (-(σ + 1)) + Q ^ (-(σ + 1)) := add_nonneg (Real.rpow_nonneg hq.le _)
      (Real.rpow_nonneg (by dsimp only [Q]; positivity) _)
    have hE0 := (Real.exp_pos (|Complex.arg z| * |t|)).le
    have hWn : ‖W t‖ ≤ (|σ| + 1) * (1 + |t|) := by
      dsimp only [W]
      calc ‖(σ : ℂ) + (t : ℂ) * I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = |σ| + |t| := by simp
        _ ≤ _ := by nlinarith [abs_nonneg σ, abs_nonneg t]
    have hpow0 : 0 ≤ (1 + |t|) ^ N := by positivity
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, norm_neg, hexpForm]
    have h1 : ‖z ^ (-(((σ + 1 : ℝ) : ℂ) + (t : ℂ) * I))‖ ≤
        (q ^ (-(σ + 1)) + Q ^ (-(σ + 1))) * Real.exp (|Complex.arg z| * |t|) :=
      hcp.trans (mul_le_mul_of_nonneg_right hp hE0)
    calc _ ≤ ((|σ| + 1) * (1 + |t|)) *
          ((q ^ (-(σ + 1)) + Q ^ (-(σ + 1))) * Real.exp (|Complex.arg z| * |t|)) *
          (C * (1 + |t|) ^ N * Real.exp (-(π * |t| / 2))) :=
          mul_le_mul (mul_le_mul hWn h1 (norm_nonneg _) (by positivity)) hgt (norm_nonneg _)
            (by positivity)
      _ = (|σ| + 1) * (q ^ (-(σ + 1)) + Q ^ (-(σ + 1))) * C * (1 + |t|) ^ (N + 1) *
          (Real.exp (|Complex.arg z| * |t|) * Real.exp (-(π * |t| / 2))) := by ring
      _ ≤ (|σ| + 1) * (q ^ (-(σ + 1)) + Q ^ (-(σ + 1))) * C * (1 + |t|) ^ (N + 1) *
          Real.exp (-r * |t|) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = _ := by ring
  have hdiff : ∀ᵐ t : ℝ ∂volume, ∀ z ∈ S, HasDerivAt (fun w => F w t) (F' z t) z := by
    refine Eventually.of_forall fun t z hz => ?_
    have hzslit : z ∈ Complex.slitPlane := Or.inl (hSre z hz)
    have hcp := (hasDerivAt_id z).cpow_const (c := -W t) hzslit
    have hmul := hcp.mul_const (g t)
    dsimp only [F, F']
    simpa only [id_eq, mul_one] using hmul
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') hS hFmeas hFint hF'meas hderivBound hbound hdiff).2.differentiableAt

/-- Integrability on the far-left line, for every base in the right half-plane. -/
theorem integrable_leftIntegrand (F : ExtendedSelbergClass) {K : ℕ} (ha : (-(K : ℝ) - 1 / 2) < -1)
    (haμ : ∀ j, F.gammaData.lambda j * (-(K : ℝ) - 1 / 2) < 1 - (F.gammaData.mu j).re)
    {z : ℂ} (hz : 0 < z.re) :
    Integrable fun t : ℝ => ordinaryMellinIntegrand F 0 z (leftLine K t) := by
  obtain ⟨C, N, hC, hb⟩ := exists_bound_leftValue F ha haμ
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have harg : |Complex.arg z| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hr : 0 < π / 2 - |Complex.arg z| := by linarith
  refine ((integrable_one_add_abs_pow_mul_exp_neg_abs N hr).const_mul
    (‖z‖ ^ (-(-(K : ℝ) - 1 / 2)) * C)).mono'
    (continuous_leftIntegrand F K hz0).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hcp := norm_cpow_neg_line_add_mul_I_le (-(K : ℝ) - 1 / 2) z hz0 t
  have hg := hb t
  have hval : ordinaryMellinIntegrand F 0 z (leftLine K t) =
      z ^ (-((((-(K : ℝ) - 1 / 2 : ℝ)) : ℂ) + (t : ℂ) * I)) * leftValue F K t := rfl
  rw [hval, norm_mul]
  have hE : Real.exp (|Complex.arg z| * |t|) * Real.exp (-(π * |t| / 2)) =
      Real.exp (-(π / 2 - |Complex.arg z|) * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc _ ≤ (‖z‖ ^ (-(-(K : ℝ) - 1 / 2)) * Real.exp (|Complex.arg z| * |t|)) *
        (C * (1 + |t|) ^ N * Real.exp (-(π * |t| / 2))) :=
        mul_le_mul hcp hg (norm_nonneg _) (by positivity)
    _ = ‖z‖ ^ (-(-(K : ℝ) - 1 / 2)) * C * ((1 + |t|) ^ N *
        (Real.exp (|Complex.arg z| * |t|) * Real.exp (-(π * |t| / 2)))) := by ring
    _ = _ := by rw [hE]

/-- The contour shift at a positive real base, for an integrable left line. -/
theorem ordinaryMellin_contour_identity (F : ExtendedSelbergClass) {x : ℝ} (hx : 0 < x) (K : ℕ)
    (hK : Integrable fun t : ℝ => ordinaryMellinIntegrand F 0 (x : ℂ) (leftLine K t)) :
    (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I)) -
        (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (leftLine K t)) =
      2 * (π : ℂ) * (ordinaryPolarPart F (x : ℂ) +
        ∑ k ∈ Finset.range (K + 1), ordinaryTaylorCoeff F k * (x : ℂ) ^ k) := by
  classical
  have hx0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hright := integrable_ordinaryMellinIntegrand_right F hx
  set a : ℝ := -(K : ℝ) - 1 / 2 with ha
  have ha0 : a < 0 := by dsimp only [a]; have := Nat.cast_nonneg (α := ℝ) K; linarith
  have hac : a < 2 := by linarith
  set P : Finset ℂ := insert 1 ((Finset.range (K + 1)).image fun k : ℕ => -(k : ℂ)) with hP
  have hnotin : (1 : ℂ) ∉ (Finset.range (K + 1)).image fun k : ℕ => -(k : ℂ) := by
    intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_image.1 h
    have he := congrArg Complex.re hk
    simp at he
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hPre : ∀ p ∈ P, a < p.re ∧ p.re < 2 := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · simp only [Complex.one_re]
      constructor <;> linarith
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
      have hkK : (k : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hk0 := Nat.cast_nonneg (α := ℝ) k
      constructor <;> simp only [Complex.neg_re, Complex.natCast_re, a] <;> linarith
  have hmero : ∀ p ∈ P, MeromorphicAt (ordinaryMellinIntegrand F 0 (x : ℂ)) p :=
    fun p _ => meromorphicAt_ordinaryMellinIntegrand F 0 hx0 p
  have hoff : ∀ z : ℂ, a ≤ z.re → z.re ≤ 2 → z ∉ P →
      AnalyticAt ℂ (ordinaryMellinIntegrand F 0 (x : ℂ)) z := by
    intro z hza _ hzP
    refine analyticAt_ordinaryMellinIntegrand F 0 hx0 (fun k hk => ?_) (fun h => hzP ?_)
    · apply hzP
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨k, Finset.mem_range.2 ?_, hk.symm⟩)
      have hre := congrArg Complex.re hk
      simp at hre
      have : (k : ℝ) < K + 1 := by dsimp only [a] at hza; linarith
      exact_mod_cast this
    · simp only [zero_add] at h
      rw [h]
      exact Finset.mem_insert_self _ _
  have hT : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨htop, hbot⟩ := tendsto_hIntegral_ordinaryMellinIntegrand F hx hac.le
  have hshift := verticalIntegral_sub_eq_sum_laurentCoeff_of_horizontal_tendsto_seq hac hPre hmero
    hoff hK hright hT (htop.comp hT) (hbot.comp hT)
  change (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I)) -
      (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (leftLine K t)) = _ at hshift
  rw [hshift]
  congr 1
  rw [hP, Finset.sum_insert hnotin, Finset.sum_image (fun k _ k' _ h => by
    have := congrArg Complex.re h; simp at this; exact_mod_cast this)]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [laurentCoeff_ordinaryMellinIntegrand_neg_nat F hx0 k, ordinaryTaylorCoeff]
  ring

/-- The finite analytic part of the expansion. -/
def regularPart (F : ExtendedSelbergClass) (K : ℕ) (z : ℂ) : ℂ :=
  ordinaryPolarPart F z + ∑ k ∈ Finset.range (K + 1), ordinaryTaylorCoeff F k * z ^ k

theorem analyticOnNhd_regularPart (F : ExtendedSelbergClass) (K : ℕ) :
    AnalyticOnNhd ℂ (regularPart F K) Complex.slitPlane := by
  intro z hz
  refine (analyticOnNhd_ordinaryPolarPart F z hz).add ?_
  exact Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul (by fun_prop)

/-- **The left-line expansion of the exponential series on the right half-plane.** -/
theorem ordinaryExponentialSeries_eq_left (F : ExtendedSelbergClass) {K : ℕ}
    (ha : (-(K : ℝ) - 1 / 2) < -1)
    (haμ : ∀ j, F.gammaData.lambda j * (-(K : ℝ) - 1 / 2) < 1 - (F.gammaData.mu j).re)
    {z : ℂ} (hz : 0 < z.re) :
    ordinaryExponentialSeries F z = regularPart F K z +
      (1 / (2 * (π : ℂ))) * ∫ t : ℝ, ordinaryMellinIntegrand F 0 z (leftLine K t) := by
  obtain ⟨C, N, hC, hb⟩ := exists_bound_leftValue F ha haμ
  have hI : DifferentiableOn ℂ
      (fun w : ℂ => ∫ t : ℝ, ordinaryMellinIntegrand F 0 w (leftLine K t)) {w : ℂ | 0 < w.re} :=
    fun w hw => (differentiableAt_mellinLine (σ := -(K : ℝ) - 1 / 2) (continuous_leftValue F K) hC hb
      hw).differentiableWithinAt
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hIan := hI.analyticOnNhd hopen
  have hR : AnalyticOnNhd ℂ (fun w : ℂ => regularPart F K w + (1 / (2 * (π : ℂ))) *
      ∫ t : ℝ, ordinaryMellinIntegrand F 0 w (leftLine K t)) {w : ℂ | 0 < w.re} := by
    intro w hw
    exact (analyticOnNhd_regularPart F K w (Or.inl hw)).add (analyticAt_const.mul (hIan w hw))
  refine eqOn_rightHalfPlane_of_eq_on_pos_reals (analyticOnNhd_ordinaryExponentialSeries F) hR
    (fun x hx => ?_) hz
  have hcontour := ordinaryMellin_contour_identity F hx K
    (integrable_leftIntegrand F ha haμ (z := (x : ℂ)) (by simpa using hx))
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ordinaryExponentialSeries_eq_mellin F hx, Complex.real_smul, regularPart]
  have hR1 : ∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I) =
      (∫ t : ℝ, ordinaryMellinIntegrand F 0 (x : ℂ) (leftLine K t)) +
        2 * (π : ℂ) * (ordinaryPolarPart F (x : ℂ) +
          ∑ k ∈ Finset.range (K + 1), ordinaryTaylorCoeff F k * (x : ℂ) ^ k) := by
    rw [← hcontour]
    ring
  rw [hR1]
  push_cast
  field_simp
  ring

end GaloisForLFunctions.SelbergClass.DegreeOne
