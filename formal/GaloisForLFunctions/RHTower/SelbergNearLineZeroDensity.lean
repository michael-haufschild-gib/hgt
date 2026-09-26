import GaloisForLFunctions.RHTower.SelbergNearLineMollifiedErrorMeanSquare
import GaloisForLFunctions.RHTower.ZetaZeroDensityRightShiftedLine
import GaloisForLFunctions.RHTower.MollifierLineLogMeanFloor
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorAdmissibleContour

/-!
# Selberg-type zero density at the critical scale

There are absolute constants `A > 0` and `K ≥ 0` such that for every `a ≥ 1`, for all large `U`,
admissible heights `T₁ ∈ (U/4, U/4 + 1)` and `T₂ ∈ (U/2 − 1, U/2)` exist with

`2π (a/log U) · #{ρ : ζ(ρ) = 0, Re ρ ≥ 1/2 + 2a/log U, T₁ ≤ Im ρ ≤ T₂}
    ≤ (T₂ − T₁)/2 · r_A(a) + K log U`,

`r_A(a) = 3√η + 2η`, `η = A(1/a² + e^{−a/300})` (`exists_selberg_nearLine_zeroDensity`), zeros
counted with multiplicity. Since `r_A(a) → 0` as `a → ∞` (`tendsto_selbergNearLineRate`), the zeros
at distance `2a/log U` right of the line are a vanishing proportion of `(T₂ − T₁) log U / (2π)`
as `a` grows, uniformly in `U`: there is no power-of-log loss.

The mean square of the Barban–Vehov mollified zeta function on `Re s = 1/2 + a/log U` is
`(T₂ − T₁)(1 + O(√η))`: the von Mangoldt head contributes `O(1/a²)` by Chebyshev, and the tail
beyond it `O(e^{−a/300})` by L² three-lines from the Levinson-side gate. Littlewood's lemma for the
mollified detector (`exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide`) converts this
into the count.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-- The Selberg-type near-line rate `3√η + 2η`, `η = A(1/a² + e^{−a/300})`. -/
def selbergNearLineRate (A a : ℝ) : ℝ :=
  3 * Real.sqrt (A * (1 / a ^ 2 + Real.exp (-(a / 300)))) +
    2 * (A * (1 / a ^ 2 + Real.exp (-(a / 300))))

theorem selbergNearLineRate_nonneg {A : ℝ} (hA : 0 ≤ A) (a : ℝ) : 0 ≤ selbergNearLineRate A a := by
  unfold selbergNearLineRate
  positivity

/-- **The rate vanishes as the displacement grows.** -/
theorem tendsto_selbergNearLineRate (A : ℝ) :
    Tendsto (selbergNearLineRate A) atTop (nhds 0) := by
  have h1 : Tendsto (fun a : ℝ => 1 / a ^ 2) atTop (nhds 0) := by
    have := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α := ℝ) two_ne_zero)
    simpa [one_div, Function.comp_def] using this
  have h2 : Tendsto (fun a : ℝ => Real.exp (-(a / 300))) atTop (nhds 0) := by
    have : Tendsto (fun a : ℝ => -(a / 300)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num))
    exact Real.tendsto_exp_atBot.comp this
  have hη : Tendsto (fun a : ℝ => A * (1 / a ^ 2 + Real.exp (-(a / 300)))) atTop (nhds 0) := by
    have := (h1.add h2).const_mul A
    simpa using this
  have hs : Tendsto (fun a : ℝ => Real.sqrt (A * (1 / a ^ 2 + Real.exp (-(a / 300))))) atTop
      (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hη
    simpa [Function.comp_def] using this
  have := (hs.const_mul 3).add (hη.const_mul 2)
  unfold selbergNearLineRate
  simpa using this

theorem normSq_one_add_le {g : ℂ} {κ : ℝ} (hκ : 0 < κ) :
    ‖1 + g‖ ^ 2 ≤ (1 + κ) + (1 + 1 / κ) * ‖g‖ ^ 2 := by
  have h1 : ‖1 + g‖ ≤ 1 + ‖g‖ := by
    have := norm_add_le (1 : ℂ) g
    rwa [norm_one] at this
  have h2 : 2 * ‖g‖ ≤ κ + ‖g‖ ^ 2 / κ := by
    have hid : κ + ‖g‖ ^ 2 / κ - 2 * ‖g‖ = (κ - ‖g‖) ^ 2 / κ := by field_simp; ring
    have : 0 ≤ (κ - ‖g‖) ^ 2 / κ := by positivity
    linarith
  calc ‖1 + g‖ ^ 2 ≤ (1 + ‖g‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = 1 + 2 * ‖g‖ + ‖g‖ ^ 2 := by ring
    _ ≤ 1 + (κ + ‖g‖ ^ 2 / κ) + ‖g‖ ^ 2 := by linarith
    _ = (1 + κ) + (1 + 1 / κ) * ‖g‖ ^ 2 := by ring

/-- **Mean square from the head and the tail.** If `∫‖P‖² + ∫‖f‖² ≤ (T₂−T₁) η` with `η > 0`, then
`∫‖1 + P + f‖² ≤ (T₂ − T₁)(1 + 3√η + 2η)`. -/
theorem integral_normSq_one_add_add_le {P f : ℝ → ℂ} {T₁ T₂ η : ℝ} (hT : T₁ ≤ T₂) (hη : 0 < η)
    (hPc : ContinuousOn P (Icc T₁ T₂)) (hfc : ContinuousOn f (Icc T₁ T₂))
    (hsum : (∫ t in T₁..T₂, ‖P t‖ ^ 2) + (∫ t in T₁..T₂, ‖f t‖ ^ 2) ≤ (T₂ - T₁) * η) :
    ∫ t in T₁..T₂, ‖1 + (P t + f t)‖ ^ 2 ≤
      (T₂ - T₁) * (1 + 3 * Real.sqrt η + 2 * η) := by
  set κ : ℝ := Real.sqrt η with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.mpr hη
  have hκsq : κ * κ = η := Real.mul_self_sqrt hη.le
  have hintP : IntervalIntegrable (fun t => ‖P t‖ ^ 2) volume T₁ T₂ :=
    (hPc.norm.pow 2).intervalIntegrable_of_Icc hT
  have hintf : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume T₁ T₂ :=
    (hfc.norm.pow 2).intervalIntegrable_of_Icc hT
  have hint1 : IntervalIntegrable (fun t => ‖1 + (P t + f t)‖ ^ 2) volume T₁ T₂ :=
    ((continuousOn_const.add (hPc.add hfc)).norm.pow 2).intervalIntegrable_of_Icc hT
  have hint2 : IntervalIntegrable
      (fun t => (1 + κ) + (1 + 1 / κ) * (2 * ‖P t‖ ^ 2 + 2 * ‖f t‖ ^ 2)) volume T₁ T₂ :=
    intervalIntegrable_const.add (((hintP.const_mul 2).add (hintf.const_mul 2)).const_mul _)
  have hpt : ∀ t ∈ Icc T₁ T₂, ‖1 + (P t + f t)‖ ^ 2 ≤
      (1 + κ) + (1 + 1 / κ) * (2 * ‖P t‖ ^ 2 + 2 * ‖f t‖ ^ 2) := by
    intro t _
    refine (normSq_one_add_le hκ0).trans ?_
    have h1 : ‖P t + f t‖ ^ 2 ≤ 2 * ‖P t‖ ^ 2 + 2 * ‖f t‖ ^ 2 := by
      have := norm_add_le (P t) (f t)
      nlinarith [sq_nonneg (‖P t‖ - ‖f t‖), norm_nonneg (P t + f t)]
    have : 0 ≤ 1 + 1 / κ := by positivity
    nlinarith
  have hcalc : ∫ t in T₁..T₂, (1 + κ) + (1 + 1 / κ) * (2 * ‖P t‖ ^ 2 + 2 * ‖f t‖ ^ 2) =
      (T₂ - T₁) * (1 + κ) + 2 * (1 + 1 / κ) *
        ((∫ t in T₁..T₂, ‖P t‖ ^ 2) + (∫ t in T₁..T₂, ‖f t‖ ^ 2)) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (((hintP.const_mul 2).add (hintf.const_mul 2)).const_mul _),
      intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hintP.const_mul 2) (hintf.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  have hT0 : 0 ≤ T₂ - T₁ := by linarith
  calc ∫ t in T₁..T₂, ‖1 + (P t + f t)‖ ^ 2
      ≤ ∫ t in T₁..T₂, (1 + κ) + (1 + 1 / κ) * (2 * ‖P t‖ ^ 2 + 2 * ‖f t‖ ^ 2) :=
        intervalIntegral.integral_mono_on hT hint1 hint2 hpt
    _ = (T₂ - T₁) * (1 + κ) + 2 * (1 + 1 / κ) *
        ((∫ t in T₁..T₂, ‖P t‖ ^ 2) + (∫ t in T₁..T₂, ‖f t‖ ^ 2)) := hcalc
    _ ≤ (T₂ - T₁) * (1 + κ) + 2 * (1 + 1 / κ) * ((T₂ - T₁) * η) := by
        gcongr
    _ = (T₂ - T₁) * (1 + 3 * κ + 2 * η) := by
        rw [← hκsq]
        field_simp
        ring

/-- Admissible heights for the Barban–Vehov mollified zeta function: horizontal segments over
`[1/4, 15/2]` free of zeros of `ζ` and of `Ψ_N`. -/
theorem exists_admissible_heights_hbMollifier {N : ℕ} (hN : 2 ≤ N) {A₁ B₁ A₂ B₂ : ℝ}
    (h20 : 20 ≤ A₁) (h1 : A₁ < B₁) (h2 : B₁ < A₂) (h3 : A₂ < B₂) :
    ∃ T₁ ∈ Ioo A₁ B₁, ∃ T₂ ∈ Ioo A₂ B₂,
      (∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 ∧
        edPoly (hbCoeff N) (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 ∧
        edPoly (hbCoeff N) (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) := by
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  set F : ℂ → ℂ := fun z => zetaEntire z * edPoly (hbCoeff N) (Finset.Icc 1 N) z with hF
  have hFd : Differentiable ℂ F := differentiable_zetaEntire.mul (differentiable_edPoly _ hs)
  have hFan : AnalyticOnNhd ℂ F Set.univ := hFd.differentiableOn.analyticOnNhd isOpen_univ
  have hbn : ∀ n ∈ Finset.Icc 1 N, ‖hbCoeff N n‖ ≤ 1 := fun n hn => norm_hbCoeff_le hN hn
  have hFne : ∃ z : ℂ, F z ≠ 0 := by
    refine ⟨((15 / 2 : ℝ) : ℂ), mul_ne_zero ?_ ?_⟩
    · rw [zetaEntire_eq (by intro h; have := congrArg Complex.re h; simp at this; norm_num at this)]
      refine mul_ne_zero (by intro h; have := congrArg Complex.re h; simp at this; norm_num at this) ?_
      exact riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
    · intro h0
      have h := norm_edPoly_sub_one_le_half_of_six_le (hbCoeff N) hs
        (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) (hbCoeff_one hN) hbn
        (z := ((15 / 2 : ℝ) : ℂ)) (by simp; norm_num)
      rw [h0] at h
      norm_num at h
  obtain ⟨T₁, hT₁, T₂, hT₂, hF1, hF2⟩ :=
    exists_horizontal_slices_avoiding_entire_zeros hFan hFne (c := (1 / 4 : ℝ)) (d := 15 / 2)
      (by norm_num) h1 h2 h3
  have hedge : ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2), F ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      ∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
        edPoly (hbCoeff N) (Finset.Icc 1 N) ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
    intro T hT hFT x hx
    have hx' : x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2) := by
      rw [Set.uIcc_of_le (by norm_num)]; exact hx
    have hne1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hFx := hFT x hx'
    simp only [hF] at hFx
    rw [zetaEntire_eq hne1] at hFx
    refine ⟨fun h0 => hFx (by rw [h0]; ring), fun h0 => hFx (by rw [h0]; ring)⟩
  exact ⟨T₁, hT₁, T₂, hT₂, hedge T₁ (by linarith [hT₁.1]) hF1,
    hedge T₂ (by linarith [hT₂.1, hT₁.2]) hF2⟩

/-- **The mollified mean square on the right-shifted line** `Re s = 1/2 + a/L`, at the scale
`U = e^L`, from the tail estimate. -/
theorem integral_normSq_zetaHb_rightShift_le {N : ℕ} {L a Cf T₁ T₂ : ℝ} (ha : 1 ≤ a)
    (hCf : 0 < Cf) (hL500 : 500 ≤ L) (hLa : 2 * a + 2 ≤ L)
    (hNle : (N : ℝ) ≤ Real.exp (L / 100)) (hNgt : Real.exp (L / 100) - 1 < N)
    (hT₁ : 0 < T₁) (hT₁₂ : T₁ ≤ T₂) (hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁)
    (hf : ∫ t in T₁..T₂, ‖hbMollifiedTail N (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Cf * Real.exp (-((a + 1) / 300)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L))) :
    (∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly (hbCoeff N) (Finset.Icc 1 N) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        (T₂ - T₁) * (1 + selbergNearLineRate (max 400000 (3 * Cf)) a) := by
  have hL0 : 0 < L := by linarith
  obtain ⟨hN2, -, hMVT, -, -, -⟩ := nearLine_length_facts hL500 hNle hNgt
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : L / 200 ≤ Real.log N := by
    have h1 : Real.exp (L / 100) / 2 ≤ N := by
      have : (100 : ℝ) ≤ Real.exp (L / 100) := by
        have := hundred_le_exp_five
        have : Real.exp 5 ≤ Real.exp (L / 100) := Real.exp_le_exp.mpr (by linarith)
        linarith
      linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h2
    have h3 : Real.log 2 ≤ L / 200 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  set σ₀ : ℝ := 1 / 2 + a / L with hσ₀
  have haL : a / L ≤ 1 := by rw [div_le_one hL0]; linarith
  have haL0 : 0 < a / L := div_pos (by linarith) hL0
  have hP := integral_normSq_hbVonMangoldt_right_le hN2 haL0 haL hT₁₂
  have hpt : ∀ τ : ℝ, displacedLinePt (-(a / L)) τ = ((σ₀ : ℝ) : ℂ) + (τ : ℂ) * I := by
    intro τ
    unfold displacedLinePt
    rw [hσ₀]
    congr 2
    ring
  simp only [hpt] at hP
  set A : ℝ := max 400000 (3 * Cf) with hA
  set η : ℝ := A * (1 / a ^ 2 + Real.exp (-(a / 300))) with hη
  have hA0 : 0 < A := by positivity
  have hη0 : 0 < η := by positivity
  have hPb : ∫ τ in T₁..T₂,
      ‖edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) (((σ₀ : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤
        (T₂ - T₁) * (400000 / a ^ 2) := by
    refine hP.trans ?_
    have h1 : T₂ - T₁ + 8 * N * (1 + Real.log N) ≤ 2 * (T₂ - T₁) := by linarith
    have h2 : 5 / ((a / L) ^ 2 * Real.log N ^ 2) ≤ 200000 / a ^ 2 := by
      have ha0 : 0 < a := by linarith
      have hlogpos : 0 < Real.log N := by
        have : 0 < L / 200 := by positivity
        linarith
      rw [div_le_div_iff₀ (mul_pos (by positivity) (pow_pos hlogpos 2)) (by positivity)]
      have hsq : (L / 200) ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ (by positivity) hlogN 2
      have hid : (a / L) ^ 2 * (L / 200) ^ 2 = a ^ 2 / 40000 := by field_simp; ring
      have : a ^ 2 / 40000 ≤ (a / L) ^ 2 * Real.log N ^ 2 := by
        rw [← hid]; exact mul_le_mul_of_nonneg_left hsq (by positivity)
      nlinarith
    have h0 : 0 ≤ 5 / ((a / L) ^ 2 * Real.log N ^ 2) := by positivity
    calc (T₂ - T₁ + 8 * N * (1 + Real.log N)) * (5 / ((a / L) ^ 2 * Real.log N ^ 2))
        ≤ (2 * (T₂ - T₁)) * (200000 / a ^ 2) := mul_le_mul h1 h2 h0 (by linarith)
      _ = (T₂ - T₁) * (400000 / a ^ 2) := by ring
  have hfb : ∫ t in T₁..T₂, ‖hbMollifiedTail N (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁) * (3 * Cf * Real.exp (-(a / 300))) := by
    refine hf.trans ?_
    have he : Real.exp (-((a + 1) / 300)) ≤ Real.exp (-(a / 300)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : T₂ - T₁ + 2 * Real.exp (99 / 100 * L) ≤ 3 * (T₂ - T₁) := by linarith
    calc Cf * Real.exp (-((a + 1) / 300)) * (T₂ - T₁ + 2 * Real.exp (99 / 100 * L))
        ≤ Cf * Real.exp (-(a / 300)) * (3 * (T₂ - T₁)) := by gcongr
      _ = (T₂ - T₁) * (3 * Cf * Real.exp (-(a / 300))) := by ring
  have hsum : (∫ τ in T₁..T₂,
      ‖edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) (((σ₀ : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2) +
      (∫ t in T₁..T₂, ‖hbMollifiedTail N (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (T₂ - T₁) * η := by
    have h1 : 400000 / a ^ 2 ≤ A * (1 / a ^ 2) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    have h2 : 3 * Cf * Real.exp (-(a / 300)) ≤ A * Real.exp (-(a / 300)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    have hT0 : 0 ≤ T₂ - T₁ := by linarith
    calc _ ≤ (T₂ - T₁) * (400000 / a ^ 2) + (T₂ - T₁) * (3 * Cf * Real.exp (-(a / 300))) :=
          add_le_add hPb hfb
      _ ≤ (T₂ - T₁) * (A * (1 / a ^ 2)) + (T₂ - T₁) * (A * Real.exp (-(a / 300))) := by gcongr
      _ = (T₂ - T₁) * η := by rw [hη]; ring
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hPc : ContinuousOn (fun t : ℝ =>
      edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I)) (Icc T₁ T₂) :=
    ((differentiable_edPoly _ hs).continuous.comp (by fun_prop)).continuousOn
  have hfc : ContinuousOn (fun t : ℝ => hbMollifiedTail N (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I))
      (Icc T₁ T₂) := by
    intro t ht
    have hne : (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [ht.1]
    exact (ContinuousAt.comp (g := hbMollifiedTail N)
      (f := fun t : ℝ => (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I))
      (continuousAt_hbMollifiedTail hne) (by fun_prop)).continuousWithinAt
  have hMsq0 := integral_normSq_one_add_add_le hT₁₂ hη0 hPc hfc hsum
  have hid : ∀ t : ℝ, riemannZeta (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly (hbCoeff N) (Finset.Icc 1 N) (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I) =
      1 + (edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I) +
        hbMollifiedTail N (((σ₀ : ℝ) : ℂ) + (t : ℂ) * I)) := by
    intro t
    unfold hbMollifiedTail
    ring
  simp only [hid]
  refine hMsq0.trans (le_of_eq ?_)
  rw [selbergNearLineRate, ← hη]
  ring

/-- The Littlewood count at one scale, from the mean square and the consumer. -/
theorem selberg_count_le_of_meanSquare {N : ℕ} {L a A C K₀ T₁ T₂ : ℝ} (hA : 0 ≤ A) (hK₀ : 0 ≤ K₀)
    (hL : 1 ≤ L) (hN2 : 2 ≤ N) (hlogN : Real.log N ≤ L / 100) (hT12 : T₁ < T₂) (hT₂L : T₂ ≤ Real.exp L)
    (hT₁0 : 0 < T₁) {count : ℝ}
    (hmain : 2 * Real.pi * (a / L * count) ≤
      (T₂ - T₁) / 2 * Real.log ((T₂ - T₁) * (1 + selbergNearLineRate A a) / (T₂ - T₁)) + C +
        K₀ * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)))) (hC : 0 ≤ C) :
    2 * Real.pi * (a / L * count) ≤ (T₂ - T₁) / 2 * selbergNearLineRate A a + (C + 2 * K₀) * L := by
  refine hmain.trans ?_
  have hT0 : 0 < T₂ - T₁ := by linarith
  have hrate := selbergNearLineRate_nonneg hA a
  have hlog1 : Real.log ((T₂ - T₁) * (1 + selbergNearLineRate A a) / (T₂ - T₁)) ≤
      selbergNearLineRate A a := by
    rw [mul_div_cancel_left₀ _ hT0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + selbergNearLineRate A a by linarith)
    linarith
  have hlogT₂ : Real.log T₂ ≤ L := by
    have := Real.log_le_log (by linarith) hT₂L
    rwa [Real.log_exp] at this
  have hlogMb : Real.log ((N : ℝ) ^ (5 : ℕ)) ≤ L := by
    rw [Real.log_pow]
    push_cast
    have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    linarith
  have h1 : (T₂ - T₁) / 2 * Real.log ((T₂ - T₁) * (1 + selbergNearLineRate A a) / (T₂ - T₁)) ≤
      (T₂ - T₁) / 2 * selbergNearLineRate A a :=
    mul_le_mul_of_nonneg_left hlog1 (by linarith)
  have h2 : C + K₀ * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ))) ≤ (C + 2 * K₀) * L := by
    have := mul_le_mul_of_nonneg_left (add_le_add hlogT₂ hlogMb) hK₀
    nlinarith
  linarith

/-- **Selberg-type zero density at the critical scale.** -/
theorem exists_selberg_nearLine_zeroDensity :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ a : ℝ, 1 ≤ a → ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
          2 * Real.pi * ((a / Real.log U) *
            ∑ w ∈ Z.filter (fun w => 1 / 2 + 2 * a / Real.log U ≤ w.re),
              ((analyticOrderAt riemannZeta w).toNat : ℝ)) ≤
            (T₂ - T₁) / 2 * selbergNearLineRate A a + K * Real.log U := by
  obtain ⟨C, K₀, hC, hK₀, hcons⟩ := exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide
  obtain ⟨Cf, hCf, htail⟩ := exists_eventually_integral_hbMollifiedTail_rightShift_le
  refine ⟨max 400000 (3 * Cf), C + 2 * K₀, by positivity, by positivity, fun a ha => ?_⟩
  filter_upwards [htail a (by linarith), eventually_ge_atTop (Real.exp (max 500 (2 * a + 2)))]
    with U htailU hUL₀
  have hU0 : 0 < U := lt_of_lt_of_le (Real.exp_pos _) hUL₀
  have hL := Real.log_le_log (Real.exp_pos _) hUL₀
  rw [Real.log_exp] at hL
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log U := ⟨_, rfl⟩
  have hUexp : U = Real.exp L := by rw [hLdef, Real.exp_log hU0]
  rw [← hLdef] at hL
  subst hUexp
  simp only [Real.log_exp] at htailU ⊢
  have hL500 : 500 ≤ L := le_trans (le_max_left _ _) hL
  have hLa : 2 * a + 2 ≤ L := le_trans (le_max_right _ _) hL
  obtain ⟨-, hHU, -, -, hU160, -⟩ := nearLine_scale_facts hL500
  have hU100 : Real.exp L ^ ((1 : ℝ) / 100) = Real.exp (L / 100) := by
    rw [← Real.exp_mul]; ring_nf
  have hU99 : Real.exp L ^ ((99 : ℝ) / 100) = Real.exp (99 / 100 * L) := by
    rw [← Real.exp_mul]; ring_nf
  have hNle := ZetaGateProductAFE.mollN_le (Real.exp_pos L).le
  have hNgt := ZetaGateProductAFE.mollN_gt (Real.exp L)
  rw [hU100] at hNle hNgt
  obtain ⟨hN2, -, -, -, -, -⟩ := nearLine_length_facts hL500 hNle hNgt
  have hlogN_le : Real.log (ZetaGateProductAFE.mollN (Real.exp L) : ℝ) ≤ L / 100 := by
    have := Real.log_le_log (by exact_mod_cast (by omega : 0 < ZetaGateProductAFE.mollN
      (Real.exp L))) hNle
    rwa [Real.log_exp] at this
  obtain ⟨T₁, hT₁, T₂, hT₂, hE1, hE2⟩ := exists_admissible_heights_hbMollifier hN2
    (A₁ := Real.exp L / 4) (B₁ := Real.exp L / 4 + 1) (A₂ := Real.exp L / 2 - 1)
    (B₂ := Real.exp L / 2) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨T₁, hT₁, T₂, hT₂, fun Z hZ => ?_⟩
  have hT₁₂ : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hlen : Real.exp (99 / 100 * L) ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hf := htailU T₁ T₂ hT₁.1.le hT₁₂ hT₂.2.le
  rw [hU99] at hf
  have hMsq := integral_normSq_zetaHb_rightShift_le (by linarith) hCf hL500 hLa hNle hNgt
    (by linarith [hT₁.1]) hT₁₂ hlen hf
  have hL0 : 0 < L := by linarith
  have hσ₀a : 1 / 4 ≤ 1 / 2 + a / L := by
    have : 0 < a / L := div_pos (by linarith) hL0
    linarith
  have hσ₀b : 1 / 2 + a / L < 2 := by
    have : a / L ≤ 1 := by rw [div_le_one hL0]; linarith
    linarith
  have hmem : ∀ x ∈ Icc (1 / 2 + a / L) (15 / 2 : ℝ), x ∈ Icc (1 / 4 : ℝ) (15 / 2) :=
    fun x hx => ⟨le_trans hσ₀a hx.1, hx.2⟩
  have hNN : (1 : ℝ) ≤ ((ZetaGateProductAFE.mollN (Real.exp L) : ℕ) : ℝ) ^ (5 : ℕ) :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ ZetaGateProductAFE.mollN (Real.exp L)))
  have hmain := hcons (hbCoeff (ZetaGateProductAFE.mollN (Real.exp L)))
    (ZetaGateProductAFE.mollN (Real.exp L)) (by omega) (hbCoeff_one hN2)
    (fun n hn => norm_hbCoeff_le hN2 hn) (fun n _ => conj_hbCoeff _ n) _ hNN
    (sum_norm_hbCoeff_mul_rpow_le hN2) (1 / 2 + a / L) T₁ T₂ _
    hσ₀a hσ₀b (by linarith [hT₁.1]) hT12
    (fun x hx => (hE1 x (hmem x hx)).1) (fun x hx => (hE2 x (hmem x hx)).1)
    (fun x hx => (hE1 x (hmem x hx)).2) (fun x hx => (hE2 x (hmem x hx)).2)
    hMsq Z hZ (a / L) (div_pos (by linarith) hL0).le
  have hfilter : Z.filter (fun w => 1 / 2 + a / L + a / L ≤ w.re) =
      Z.filter (fun w => 1 / 2 + 2 * a / L ≤ w.re) := by
    refine Finset.filter_congr fun w _ => ?_
    rw [show 1 / 2 + a / L + a / L = 1 / 2 + 2 * a / L by ring]
  rw [hfilter] at hmain
  exact selberg_count_le_of_meanSquare (by positivity) hK₀.le (by linarith) hN2 hlogN_le hT12
    (by linarith [hT₂.2, Real.exp_pos L]) (by linarith [hT₁.1]) hmain hC.le

end RHTower
