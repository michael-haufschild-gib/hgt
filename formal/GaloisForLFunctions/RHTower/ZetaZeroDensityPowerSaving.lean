import GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines
import GaloisForLFunctions.RHTower.SelbergNearLineZeroDensity

/-!
# Zero density with a power saving for every `σ > 1/2`

For every `0 < δ ≤ 1`, for all large `U` there are heights `T₁ ∈ (U/4, U/4 + 1)`,
`T₂ ∈ (U/2 − 1, U/2)` such that the zeros of `ζ` with `Re ρ ≥ 1/2 + δ`, `T₁ ≤ Im ρ ≤ T₂`, counted
with multiplicity, number at most `U^{1 − δ/40}` (`exists_zetaZeroDensity_powerSaving`).

Mechanism: with the sharp Möbius mollifier `M_X`, `X = ⌊U^{1/4}⌋`, the error `E_X = ζ M_X − 1` has no
Dirichlet coefficients below `X`. L² three lines between the critical line (fourth moments of `ζ`
and `M_X`: mass `≪ U log⁵ U`) and `Re s = 3` (mass `≪ U^{1/2}`) give
`∫_{T₁}^{T₂} |E_X(1/2 + δ/2 + it)|² ≪ (log U)⁵ U^{1−δ/10}`. The mollified mean square on
`Re s = 1/2 + δ/2` is then `(T₂−T₁)(1 + O((log U)³ U^{−δ/20}))`, and Littlewood's lemma for the
mollified detector (`exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide`) converts it
into the count.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

theorem sum_norm_mobCoeff_mul_rpow_le (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ‖mobCoeff n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ (X : ℝ) ^ (5 : ℕ) := by
  have hterm : ∀ n ∈ Finset.Icc 1 X, ‖mobCoeff n‖ * ((n : ℝ) ^ (4 : ℝ)) ≤ (X : ℝ) ^ (4 : ℕ) := by
    intro n hn
    have hnX : (n : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc ‖mobCoeff n‖ * ((n : ℝ) ^ (4 : ℝ)) ≤ 1 * ((X : ℝ) ^ (4 : ℝ)) :=
          mul_le_mul (norm_mobCoeff_le n) (Real.rpow_le_rpow hn0 hnX (by norm_num))
            (by positivity) zero_le_one
      _ = (X : ℝ) ^ (4 : ℕ) := by rw [one_mul, Real.rpow_ofNat]
  calc (∑ n ∈ Finset.Icc 1 X, ‖mobCoeff n‖ * ((n : ℝ) ^ (4 : ℝ)))
      ≤ ∑ _n ∈ Finset.Icc 1 X, (X : ℝ) ^ (4 : ℕ) := Finset.sum_le_sum hterm
    _ = (X : ℝ) * (X : ℝ) ^ (4 : ℕ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ = (X : ℝ) ^ (5 : ℕ) := by ring

/-- Admissible heights for the Möbius mollifier: horizontal segments over `[1/4, 15/2]` free of
zeros of `ζ` and of `M_X`. -/
theorem exists_admissible_heights_mobMollifier {X : ℕ} (hX : 1 ≤ X) {A₁ B₁ A₂ B₂ : ℝ}
    (h20 : 20 ≤ A₁) (h1 : A₁ < B₁) (h2 : B₁ < A₂) (h3 : A₂ < B₂) :
    ∃ T₁ ∈ Ioo A₁ B₁, ∃ T₂ ∈ Ioo A₂ B₂,
      (∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 ∧
        edPoly mobCoeff (Finset.Icc 1 X) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 ∧
        edPoly mobCoeff (Finset.Icc 1 X) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) := by
  have hs : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  set F : ℂ → ℂ := fun z => zetaEntire z * edPoly mobCoeff (Finset.Icc 1 X) z with hF
  have hFd : Differentiable ℂ F := differentiable_zetaEntire.mul (differentiable_edPoly _ hs)
  have hFan : AnalyticOnNhd ℂ F Set.univ := hFd.differentiableOn.analyticOnNhd isOpen_univ
  have hFne : ∃ z : ℂ, F z ≠ 0 := by
    refine ⟨((15 / 2 : ℝ) : ℂ), mul_ne_zero ?_ ?_⟩
    · rw [zetaEntire_eq (by intro h; have := congrArg Complex.re h; simp at this; norm_num at this)]
      refine mul_ne_zero (by intro h; have := congrArg Complex.re h; simp at this; norm_num at this) ?_
      exact riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
    · intro h0
      have h := norm_edPoly_sub_one_le_half_of_six_le mobCoeff hs
        (Finset.mem_Icc.mpr ⟨le_rfl, hX⟩) mobCoeff_one (fun n _ => norm_mobCoeff_le n)
        (z := ((15 / 2 : ℝ) : ℂ)) (by simp; norm_num)
      rw [h0] at h
      norm_num at h
  obtain ⟨T₁, hT₁, T₂, hT₂, hF1, hF2⟩ :=
    exists_horizontal_slices_avoiding_entire_zeros hFan hFne (c := (1 / 4 : ℝ)) (d := 15 / 2)
      (by norm_num) h1 h2 h3
  have hedge : ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2), F ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      ∀ x ∈ Icc (1 / 4 : ℝ) (15 / 2), riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
        edPoly mobCoeff (Finset.Icc 1 X) ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
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

/-! ## The scale `U = e^L` -/

/-- Size facts for `X = ⌊e^{L/4}⌋`, `N = ⌊e^L (L+2)⌋`. -/
theorem powerSaving_length_facts {L : ℝ} (hL : 8 ≤ L) {X N : ℕ}
    (hXle : (X : ℝ) ≤ Real.exp (L / 4)) (hXgt : Real.exp (L / 4) - 1 < X)
    (hNle : (N : ℝ) ≤ Real.exp L * (L + 2)) (hNgt : Real.exp L * (L + 2) - 1 < N) :
    1 ≤ X ∧ 4 ≤ N ∧ Real.exp (L / 4) / 2 ≤ X ∧ (X : ℝ) ^ 2 ≤ Real.exp (L / 2) ∧
      Real.exp L * L ≤ N - 3 * Real.exp L / 8 ∧ 9 ≤ Real.exp L := by
  have hE4 : 3 ≤ Real.exp (L / 4) := by have := Real.add_one_le_exp (L / 4); linarith
  have hE : 9 ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) < X := by linarith
    exact_mod_cast this.le
  have hN4 : 4 ≤ N := by
    have : (4 : ℝ) < N := by nlinarith
    exact_mod_cast this.le
  refine ⟨hX1, hN4, by linarith, ?_, ?_, hE⟩
  · calc (X : ℝ) ^ 2 ≤ Real.exp (L / 4) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg X) hXle 2
      _ ≤ Real.exp (L / 2) := by
          rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by push_cast; linarith)
  · nlinarith

/-- **The left-edge mass at scale `e^L`.** -/
theorem powerSaving_SL_le {C D L : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hL : 8 ≤ L) {X N : ℕ}
    (hXle : (X : ℝ) ≤ Real.exp (L / 4)) (hXgt : Real.exp (L / 4) - 1 < X)
    (hNle : (N : ℝ) ≤ Real.exp L * (L + 2)) (hNgt : Real.exp L * (L + 2) - 1 < N) :
    Real.exp 1 ^ 2 * (2 * Real.sqrt
        ((2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
          (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 * (D * N * (1 + Real.log N) ^ 4)) + 4 * N) +
      Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 * (2 * (1 + |3 * Real.exp L / 8|) ^ 2 +
        2 * Real.exp L ^ 2) * Real.exp (-((Real.exp L * L) ^ 2 / (2 * Real.exp L ^ 2))) *
          Real.sqrt (Real.pi / (1 / (2 * Real.exp L ^ 2))) ≤
      (16 * Real.sqrt (160 * D + 1) + 32 + 96 * C ^ 2) * Real.exp L * (L + 2) ^ 5 := by
  obtain ⟨hX1, hN4, hXge, hX2, -, hE9⟩ := powerSaving_length_facts hL hXle hXgt hNle hNgt
  set E : ℝ := Real.exp L with hEdef
  have hE0 : 0 < E := Real.exp_pos L
  have hL2 : 0 < L + 2 := by linarith
  have he2 : Real.exp 1 ^ 2 ≤ 8 := by
    have := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos 1]
  have hXX : ((X * X : ℕ) : ℝ) = (X : ℝ) ^ 2 := by push_cast; ring
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hlogX : Real.log ((X * X : ℕ) : ℝ) ≤ L / 2 := by
    rw [hXX]
    have := Real.log_le_log (by positivity) hX2
    rwa [Real.log_exp] at this
  have hlogX0 : 0 ≤ Real.log ((X * X : ℕ) : ℝ) := Real.log_nonneg (by rw [hXX]; nlinarith)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN : 1 + Real.log (N : ℝ) ≤ 2 * (L + 2) := by
    have h1 := Real.log_le_log hNpos hNle
    rw [Real.log_mul hE0.ne' hL2.ne', Real.log_exp] at h1
    have h2 : Real.log (L + 2) ≤ L + 2 - 1 := Real.log_le_sub_one_of_pos hL2
    linarith
  have hlogN0 : 0 ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by linarith); linarith
  have hX2E : (X : ℝ) ^ 2 ≤ E := hX2.trans (Real.exp_le_exp.mpr (by linarith))
  -- the Cauchy–Schwarz term
  have hA : 2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ)) ≤ 10 * E * (L + 2) := by
    rw [hXX]
    have : (X : ℝ) ^ 2 * (1 + Real.log ((X * X : ℕ) : ℝ)) ≤ E * (L + 2) :=
      mul_le_mul hX2E (by linarith) (by linarith) hE0.le
    nlinarith
  have hB : (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 ≤ (L + 2) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hCc : D * N * (1 + Real.log N) ^ 4 ≤ 16 * D * E * (L + 2) ^ 5 := by
    have h4 : (1 + Real.log (N : ℝ)) ^ 4 ≤ (2 * (L + 2)) ^ 4 := pow_le_pow_left₀ hlogN0 hlogN 4
    have h5 : D * N * (1 + Real.log N) ^ 4 ≤ D * (E * (L + 2)) * (2 * (L + 2)) ^ 4 := by
      gcongr
    nlinarith [h5]
  have hprod : (2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
      (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 * (D * N * (1 + Real.log N) ^ 4) ≤
      (160 * D + 1) * (E * (L + 2) ^ 5) ^ 2 := by
    have hA0 : 0 ≤ 2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ)) := by positivity
    have hC0 : 0 ≤ D * N * (1 + Real.log N) ^ 4 := by positivity
    calc (2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
          (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 * (D * N * (1 + Real.log N) ^ 4)
        ≤ (10 * E * (L + 2)) * (L + 2) ^ 4 * (16 * D * E * (L + 2) ^ 5) := by
          gcongr
      _ = 160 * D * (E * (L + 2) ^ 5) ^ 2 := by ring
      _ ≤ (160 * D + 1) * (E * (L + 2) ^ 5) ^ 2 := by
          have : 0 ≤ (E * (L + 2) ^ 5) ^ 2 := sq_nonneg _
          nlinarith
  have hCS : Real.sqrt ((2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
      (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 * (D * N * (1 + Real.log N) ^ 4)) ≤
      Real.sqrt (160 * D + 1) * (E * (L + 2) ^ 5) := by
    calc _ ≤ Real.sqrt ((160 * D + 1) * (E * (L + 2) ^ 5) ^ 2) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt (160 * D + 1) * (E * (L + 2) ^ 5) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hL5 : L + 2 ≤ (L + 2) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
  have hfirst : Real.exp 1 ^ 2 * (2 * Real.sqrt
      ((2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
        (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 * (D * N * (1 + Real.log N) ^ 4)) + 4 * N) ≤
      (16 * Real.sqrt (160 * D + 1) + 32) * E * (L + 2) ^ 5 := by
    have hin : 2 * Real.sqrt ((2 * N + 8 * ((X * X : ℕ) : ℝ) *
        (1 + Real.log ((X * X : ℕ) : ℝ))) * (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 *
          (D * N * (1 + Real.log N) ^ 4)) + 4 * N ≤
        (2 * Real.sqrt (160 * D + 1) + 4) * E * (L + 2) ^ 5 := by
      have h4N : 4 * (N : ℝ) ≤ 4 * E * (L + 2) ^ 5 := by
        have : (N : ℝ) ≤ E * (L + 2) ^ 5 := hNle.trans (mul_le_mul_of_nonneg_left hL5 hE0.le)
        linarith
      nlinarith [hCS, Real.sqrt_nonneg (160 * D + 1)]
    have h0 : 0 ≤ 2 * Real.sqrt ((2 * N + 8 * ((X * X : ℕ) : ℝ) *
        (1 + Real.log ((X * X : ℕ) : ℝ))) * (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 *
          (D * N * (1 + Real.log N) ^ 4)) + 4 * N := by positivity
    calc _ ≤ 8 * ((2 * Real.sqrt (160 * D + 1) + 4) * E * (L + 2) ^ 5) :=
          mul_le_mul he2 hin h0 (by norm_num)
      _ = (16 * Real.sqrt (160 * D + 1) + 32) * E * (L + 2) ^ 5 := by ring
  -- the Gaussian tail
  have hτ : 2 * (1 + |3 * E / 8|) ^ 2 + 2 * E ^ 2 ≤ 4 * E ^ 2 := by
    rw [abs_of_pos (by positivity)]
    nlinarith
  have hexpL : Real.exp (-((E * L) ^ 2 / (2 * E ^ 2))) = Real.exp (-(L ^ 2 / 2)) := by
    congr 1; field_simp
  have hsq : Real.sqrt (Real.pi / (1 / (2 * E ^ 2))) ≤ 3 * E := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.pi_lt_d2
    have : Real.pi / (1 / (2 * E ^ 2)) = 2 * Real.pi * E ^ 2 := by field_simp
    rw [this]
    nlinarith [sq_nonneg E]
  have hdecay : Real.exp (L / 2) * E ^ 2 * Real.exp (-(L ^ 2 / 2)) * E ≤ E := by
    have : Real.exp (L / 2) * E ^ 2 * Real.exp (-(L ^ 2 / 2)) ≤ 1 := by
      rw [hEdef, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_one_iff.mpr
      push_cast
      nlinarith
    nlinarith
  have htail : Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 * (2 * (1 + |3 * E / 8|) ^ 2 + 2 * E ^ 2) *
      Real.exp (-((E * L) ^ 2 / (2 * E ^ 2))) * Real.sqrt (Real.pi / (1 / (2 * E ^ 2))) ≤
      96 * C ^ 2 * E * (L + 2) ^ 5 := by
    rw [hexpL]
    have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
    calc Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 * (2 * (1 + |3 * E / 8|) ^ 2 + 2 * E ^ 2) *
          Real.exp (-(L ^ 2 / 2)) * Real.sqrt (Real.pi / (1 / (2 * E ^ 2)))
        ≤ 8 * C ^ 2 * Real.exp (L / 2) * (4 * E ^ 2) * Real.exp (-(L ^ 2 / 2)) * (3 * E) := by
          gcongr
      _ = 96 * C ^ 2 * (Real.exp (L / 2) * E ^ 2 * Real.exp (-(L ^ 2 / 2)) * E) := by ring
      _ ≤ 96 * C ^ 2 * E := mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ ≤ 96 * C ^ 2 * E * (L + 2) ^ 5 := by
          have : (1 : ℝ) ≤ (L + 2) ^ 5 := one_le_pow₀ (by linarith)
          have h0 : 0 ≤ 96 * C ^ 2 * E := by positivity
          nlinarith
  calc _ ≤ (16 * Real.sqrt (160 * D + 1) + 32) * E * (L + 2) ^ 5 + 96 * C ^ 2 * E * (L + 2) ^ 5 :=
        add_le_add hfirst htail
    _ = (16 * Real.sqrt (160 * D + 1) + 32 + 96 * C ^ 2) * E * (L + 2) ^ 5 := by ring

/-- **The right-edge mass at scale `e^L`.** -/
theorem powerSaving_SR_le {L : ℝ} (hL : 8 ≤ L) {X N : ℕ}
    (hXle : (X : ℝ) ≤ Real.exp (L / 4)) (hXgt : Real.exp (L / 4) - 1 < X)
    (hNle : (N : ℝ) ≤ Real.exp L * (L + 2)) (hNgt : Real.exp L * (L + 2) - 1 < N) :
    Real.exp 1 ^ 2 * (2 / X) ^ 2 * Real.sqrt (Real.pi / (2 / Real.exp L ^ 2)) ≤
      256 * Real.exp (L / 2) := by
  obtain ⟨hX1, -, hXge, -, -, -⟩ := powerSaving_length_facts hL hXle hXgt hNle hNgt
  have he2 : Real.exp 1 ^ 2 ≤ 8 := by
    have := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos 1]
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hX2 : (2 / (X : ℝ)) ^ 2 ≤ 16 * Real.exp (-(L / 2)) := by
    have h1 : 2 / (X : ℝ) ≤ 4 / Real.exp (L / 4) := by
      rw [div_le_div_iff₀ hXpos (Real.exp_pos _)]; linarith
    have h2 : (2 / (X : ℝ)) ^ 2 ≤ (4 / Real.exp (L / 4)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    refine h2.trans (le_of_eq ?_)
    rw [div_pow, ← Real.exp_nat_mul, Real.exp_neg]
    push_cast
    field_simp
    ring_nf
  have hsq : Real.sqrt (Real.pi / (2 / Real.exp L ^ 2)) ≤ 2 * Real.exp L := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.pi_lt_d2
    have : Real.pi / (2 / Real.exp L ^ 2) = Real.pi / 2 * Real.exp L ^ 2 := by field_simp
    rw [this]
    nlinarith [sq_nonneg (Real.exp L)]
  calc Real.exp 1 ^ 2 * (2 / X) ^ 2 * Real.sqrt (Real.pi / (2 / Real.exp L ^ 2))
      ≤ 8 * (16 * Real.exp (-(L / 2))) * (2 * Real.exp L) := by gcongr
    _ = 256 * (Real.exp (-(L / 2)) * Real.exp L) := by ring
    _ = 256 * Real.exp (L / 2) := by rw [← Real.exp_add]; ring_nf

/-- Interpolating the two masses. -/
theorem powerSaving_interp_le {SL SR A L lam : ℝ} (hSL : 0 ≤ SL) (hSR : 0 ≤ SR) (hA : 0 ≤ A)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (hSLA : SL ≤ A * Real.exp L)
    (hSRA : SR ≤ A * Real.exp (L / 2)) :
    SL ^ (1 - lam) * SR ^ lam ≤ A * Real.exp (L * (1 - lam / 2)) := by
  have h1 : SL ^ (1 - lam) ≤ (A * Real.exp L) ^ (1 - lam) :=
    Real.rpow_le_rpow hSL hSLA (by linarith)
  have h2 : SR ^ lam ≤ (A * Real.exp (L / 2)) ^ lam := Real.rpow_le_rpow hSR hSRA hl0
  calc SL ^ (1 - lam) * SR ^ lam ≤ (A * Real.exp L) ^ (1 - lam) * (A * Real.exp (L / 2)) ^ lam :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = A * Real.exp (L * (1 - lam / 2)) := by
        rw [Real.mul_rpow hA (Real.exp_pos _).le, Real.mul_rpow hA (Real.exp_pos _).le,
          ← Real.exp_mul, ← Real.exp_mul]
        rcases hA.lt_or_eq with hA0 | hA0
        · have : A ^ (1 - lam) * A ^ lam = A := by
            rw [← Real.rpow_add hA0]; simp
          calc A ^ (1 - lam) * Real.exp (L * (1 - lam)) * (A ^ lam * Real.exp (L / 2 * lam))
              = (A ^ (1 - lam) * A ^ lam) * (Real.exp (L * (1 - lam)) *
                  Real.exp (L / 2 * lam)) := by ring
            _ = A * Real.exp (L * (1 - lam / 2)) := by
                rw [this, ← Real.exp_add]; ring_nf
        · subst hA0
          rcases hl0.lt_or_eq with hl | hl
          · rw [Real.zero_rpow hl.ne']; simp
          · subst hl; simp

/-- `(L+2)^n e^{−cL} → 0`. -/
theorem eventually_add_two_pow_mul_exp_neg_le (n : ℕ) {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ L in atTop, (L + 2) ^ n * Real.exp (-(c * L)) ≤ ε := by
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hc)
  have h2 := h1.eventually (Iic_mem_nhds (show (0 : ℝ) < ε / (2 / c) ^ n by positivity))
  filter_upwards [h2, eventually_ge_atTop (2 : ℝ)] with L hL hL2
  simp only [Function.comp, mem_Iic, id] at hL
  have hbase : (L + 2) ^ n ≤ (2 / c) ^ n * (c * L) ^ n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by linarith)
    rw [show 2 / c * (c * L) = 2 * L by field_simp]
    linarith
  have hpos : 0 < (2 / c) ^ n := by positivity
  calc (L + 2) ^ n * Real.exp (-(c * L)) ≤ (2 / c) ^ n * (c * L) ^ n * Real.exp (-(c * L)) :=
        mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le
    _ = (2 / c) ^ n * ((c * L) ^ n * Real.exp (-(c * L))) := by ring
    _ ≤ (2 / c) ^ n * (ε / (2 / c) ^ n) := mul_le_mul_of_nonneg_left hL hpos.le
    _ = ε := by field_simp

end RHTower

namespace RHTower

/-- **The error mean square at scale `e^L`** on `Re s = 1/2 + δ/2`. -/
theorem powerSaving_error_le {C D L δ : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hL : 100 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h3 : ∀ {X N : ℕ}, 1 ≤ X → 4 ≤ N →
      ∀ {H τ R₀ σ T₁ T₂ : ℝ}, 3 ≤ H → 0 ≤ R₀ → R₀ ≤ N - |τ| → 1 / 2 < σ → σ ≤ 1 →
        1 ≤ T₁ → T₁ ≤ T₂ → (∀ t ∈ Icc T₁ T₂, |t - τ| ≤ H / 8) →
        ∫ t in T₁..T₂, ‖mobMollifiedError X ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          4 * ((Real.exp 1 ^ 2 * (2 * Real.sqrt
              ((2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
                (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 * (D * N * (1 + Real.log N) ^ 4)) + 4 * N) +
              Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 * (2 * (1 + |τ|) ^ 2 + 2 * H ^ 2) *
                Real.exp (-(R₀ ^ 2 / (2 * H ^ 2))) *
                  Real.sqrt (Real.pi / (1 / (2 * H ^ 2)))) ^ (1 - (σ - 1 / 2) / (3 - 1 / 2)) *
            (Real.exp 1 ^ 2 * (2 / X) ^ 2 * Real.sqrt (Real.pi / (2 / H ^ 2))) ^
              ((σ - 1 / 2) / (3 - 1 / 2))))
    {X N : ℕ} (hXle : (X : ℝ) ≤ Real.exp (L / 4)) (hXgt : Real.exp (L / 4) - 1 < X)
    (hNle : (N : ℝ) ≤ Real.exp L * (L + 2)) (hNgt : Real.exp L * (L + 2) - 1 < N)
    {T₁ T₂ : ℝ} (hT₁ : Real.exp L / 4 < T₁) (hT : T₁ ≤ T₂) (hT₂ : T₂ < Real.exp L / 2) :
    ∫ t in T₁..T₂, ‖mobMollifiedError X (((1 / 2 + δ / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      4 * (max (16 * Real.sqrt (160 * D + 1) + 32 + 96 * C ^ 2) 256 * (L + 2) ^ 5) *
        Real.exp (L * (1 - δ / 10)) := by
  obtain ⟨hX1, hN4, -, -, hNR, hE9⟩ :=
    powerSaving_length_facts (by linarith) hXle hXgt hNle hNgt
  set E : ℝ := Real.exp L with hEdef
  have hE100 : 100 ≤ E := by have := Real.add_one_le_exp L; linarith
  set B : ℝ := max (16 * Real.sqrt (160 * D + 1) + 32 + 96 * C ^ 2) 256 with hB
  set A : ℝ := B * (L + 2) ^ 5 with hA
  have hL5 : (1 : ℝ) ≤ (L + 2) ^ 5 := one_le_pow₀ (by linarith)
  have hB256 : 256 ≤ B := le_max_right _ _
  have hA0 : 0 ≤ A := by positivity
  have hτ : |3 * E / 8| = 3 * E / 8 := abs_of_pos (by positivity)
  have hmain := h3 hX1 hN4 (H := E) (τ := 3 * E / 8) (R₀ := E * L) (σ := 1 / 2 + δ / 2)
    (T₁ := T₁) (T₂ := T₂) (by linarith) (by positivity) (by rw [hτ]; linarith)
    (by linarith) (by linarith) (by linarith) hT (fun t ht => by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
  have hlam : (1 / 2 + δ / 2 - 1 / 2) / (3 - 1 / 2 : ℝ) = δ / 5 := by ring
  rw [hlam] at hmain
  have hSL := powerSaving_SL_le hC hD (by linarith) hXle hXgt hNle hNgt
  have hSR := powerSaving_SR_le (by linarith) hXle hXgt hNle hNgt
  rw [← hEdef] at hSL hSR
  have hSLA : Real.exp 1 ^ 2 * (2 * Real.sqrt
      ((2 * N + 8 * ((X * X : ℕ) : ℝ) * (1 + Real.log ((X * X : ℕ) : ℝ))) *
        (1 + Real.log ((X * X : ℕ) : ℝ)) ^ 4 * (D * N * (1 + Real.log N) ^ 4)) + 4 * N) +
      Real.exp 1 ^ 2 * C ^ 2 * (X : ℝ) ^ 2 * (2 * (1 + |3 * E / 8|) ^ 2 + 2 * E ^ 2) *
        Real.exp (-((E * L) ^ 2 / (2 * E ^ 2))) * Real.sqrt (Real.pi / (1 / (2 * E ^ 2))) ≤
      A * E := by
    refine hSL.trans ?_
    have h1 : 16 * Real.sqrt (160 * D + 1) + 32 + 96 * C ^ 2 ≤ B := le_max_left _ _
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ E * (L + 2) ^ 5)
    simp only [hA]
    nlinarith
  have hSRA : Real.exp 1 ^ 2 * (2 / X) ^ 2 * Real.sqrt (Real.pi / (2 / E ^ 2)) ≤
      A * Real.exp (L / 2) := by
    refine hSR.trans ?_
    have : 256 ≤ A := by
      simp only [hA]; nlinarith
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hinterp := powerSaving_interp_le (by positivity) (by positivity) hA0
    (by positivity) (by linarith) hSLA hSRA
  refine hmain.trans ?_
  have hexp : Real.exp (L * (1 - δ / 5 / 2)) = Real.exp (L * (1 - δ / 10)) := by
    congr 1; ring
  rw [hexp] at hinterp
  push_cast at hinterp ⊢
  linarith

end RHTower

namespace RHTower

/-- **Zero density with a power saving for every `σ = 1/2 + δ`, `0 < δ ≤ 1`.** For all large `U`
there are heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` such that the zeros of `ζ` with
`Re ρ ≥ 1/2 + δ`, `T₁ ≤ Im ρ ≤ T₂`, counted with multiplicity, number at most `U^{1 − δ/40}`. -/
theorem exists_zetaZeroDensity_powerSaving {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ U in atTop, ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        ∑ w ∈ Z.filter (fun w => 1 / 2 + δ ≤ w.re), ((analyticOrderAt riemannZeta w).toNat : ℝ) ≤
          U ^ (1 - δ / 40) := by
  obtain ⟨C₀, K₀, hC₀, hK₀, hcons⟩ := exists_zetaZeroDensity_scale_le_of_mollified_meanSquare_wide
  obtain ⟨C, D, hC, hD, h3⟩ := exists_integral_normSq_mobMollifiedError_le_threeLines
  set B : ℝ := max (16 * Real.sqrt (160 * D + 1) + 32 + 96 * C ^ 2) 256 with hB
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  set κ : ℝ := 5 / 8 * Real.sqrt (32 * B) with hκ
  have hκ0 : 0 < κ := by positivity
  have hev1 := eventually_add_two_pow_mul_exp_neg_le 5 (c := δ / 10) (ε := 1 / (32 * B))
    (by positivity) (by positivity)
  have hev2 := eventually_add_two_pow_mul_exp_neg_le 3 (c := δ / 40)
    (ε := Real.pi * δ / (2 * κ)) (by positivity) (by positivity)
  have hev3 := eventually_add_two_pow_mul_exp_neg_le 1 (c := 1 / 2)
    (ε := Real.pi * δ / (2 * (C₀ + 3 * K₀ + 1))) (by norm_num) (by positivity)
  filter_upwards [Real.tendsto_log_atTop.eventually
    ((eventually_ge_atTop (100 : ℝ)).and (hev1.and (hev2.and hev3))), eventually_gt_atTop 0]
    with U hLev hU0
  obtain ⟨hL100, hη1, hsmall, hlin⟩ := hLev
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log U := ⟨_, rfl⟩
  have hUexp : U = Real.exp L := by rw [hLdef, Real.exp_log hU0]
  rw [← hLdef] at hL100 hη1 hsmall hlin
  subst hUexp
  set E : ℝ := Real.exp L with hEdef
  have hE100 : 100 ≤ E := by have := Real.add_one_le_exp L; linarith
  have hL0 : 0 < L := by linarith
  -- lengths
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ, X = ⌊Real.exp (L / 4)⌋₊ := ⟨_, rfl⟩
  have hXle : (X : ℝ) ≤ Real.exp (L / 4) := by rw [hXdef]; exact Nat.floor_le (by positivity)
  have hXgt : Real.exp (L / 4) - 1 < X := by
    rw [hXdef]; have := Nat.lt_floor_add_one (Real.exp (L / 4)); linarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌊E * (L + 2)⌋₊ := ⟨_, rfl⟩
  have hNle : (N : ℝ) ≤ E * (L + 2) := by rw [hNdef]; exact Nat.floor_le (by positivity)
  have hNgt : E * (L + 2) - 1 < N := by
    rw [hNdef]; have := Nat.lt_floor_add_one (E * (L + 2)); linarith
  obtain ⟨hX1, -, -, -, -, -⟩ := powerSaving_length_facts (by linarith) hXle hXgt hNle hNgt
  -- heights
  obtain ⟨T₁, hT₁, T₂, hT₂, hE1, hE2⟩ := exists_admissible_heights_mobMollifier hX1
    (A₁ := E / 4) (B₁ := E / 4 + 1) (A₂ := E / 2 - 1) (B₂ := E / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨T₁, hT₁, T₂, hT₂, fun Z hZ => ?_⟩
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hlen1 : E / 8 ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hlen2 : T₂ - T₁ ≤ E / 4 := by linarith [hT₁.1, hT₂.2]
  -- the error mean square
  have herr := powerSaving_error_le hC hD hL100 hδ hδ1 h3 hXle hXgt hNle hNgt hT₁.1 hT12.le hT₂.2
  rw [← hB] at herr
  set A : ℝ := B * (L + 2) ^ 5 with hA
  set η : ℝ := 32 * A * Real.exp (-(δ / 10 * L)) with hη
  have hη0 : 0 < η := by positivity
  have hηle : η ≤ 1 := by
    have := (le_div_iff₀ (by positivity)).mp hη1
    simp only [hη, hA]
    nlinarith
  have hsum : (∫ t in T₁..T₂, ‖(fun _ : ℝ => (0 : ℂ)) t‖ ^ 2) +
      (∫ t in T₁..T₂, ‖mobMollifiedError X (((1 / 2 + δ / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (T₂ - T₁) * η := by
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      intervalIntegral.integral_zero, zero_add]
    refine herr.trans ?_
    have hsplit : Real.exp (L * (1 - δ / 10)) = E * Real.exp (-(δ / 10 * L)) := by
      rw [hEdef, ← Real.exp_add]; congr 1; ring
    rw [hsplit]
    have h0 : 0 ≤ A * Real.exp (-(δ / 10 * L)) := by positivity
    simp only [hη]
    nlinarith
  have hs : ∀ n ∈ Finset.Icc 1 X, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hEc : ContinuousOn
      (fun t : ℝ => mobMollifiedError X (((1 / 2 + δ / 2 : ℝ) : ℂ) + (t : ℂ) * I)) (Icc T₁ T₂) := by
    intro t ht
    have hne : (((1 / 2 + δ / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith [ht.1, hT₁.1]
    have hc : ContinuousAt
        (fun t : ℝ => mobMollifiedError X (((1 / 2 + δ / 2 : ℝ) : ℂ) + (t : ℂ) * I)) t := by
      unfold mobMollifiedError
      exact ((ContinuousAt.comp (g := riemannZeta)
        (f := fun t : ℝ => ((1 / 2 + δ / 2 : ℝ) : ℂ) + (t : ℂ) * I)
        (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)).mul
        (((differentiable_edPoly mobCoeff hs).continuous.comp (by fun_prop)).continuousAt)).sub
        continuousAt_const
    exact hc.continuousWithinAt
  have hMsq0 := integral_normSq_one_add_add_le hT12.le hη0 continuousOn_const hEc hsum
  have hMsq : ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 + δ / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly mobCoeff (Finset.Icc 1 X) (((1 / 2 + δ / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (T₂ - T₁) * (1 + 3 * Real.sqrt η + 2 * η) := by
    refine le_trans (le_of_eq ?_) hMsq0
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [mobMollifiedError]
    ring_nf
  -- Littlewood
  have hσa : (1 / 4 : ℝ) ≤ 1 / 2 + δ / 2 := by linarith
  have hσb : 1 / 2 + δ / 2 < (2 : ℝ) := by linarith
  have hmem : ∀ x ∈ Icc (1 / 2 + δ / 2) (15 / 2 : ℝ), x ∈ Icc (1 / 4 : ℝ) (15 / 2) :=
    fun x hx => ⟨le_trans hσa hx.1, hx.2⟩
  have hX5 : (1 : ℝ) ≤ (X : ℝ) ^ (5 : ℕ) := one_le_pow₀ (by exact_mod_cast hX1)
  have hmain := hcons mobCoeff X hX1 mobCoeff_one (fun n _ => norm_mobCoeff_le n)
    (fun n _ => conj_mobCoeff n) _ hX5 (sum_norm_mobCoeff_mul_rpow_le X) (1 / 2 + δ / 2) T₁ T₂ _
    hσa hσb (by linarith [hT₁.1]) hT12
    (fun x hx => (hE1 x (hmem x hx)).1) (fun x hx => (hE2 x (hmem x hx)).1)
    (fun x hx => (hE1 x (hmem x hx)).2) (fun x hx => (hE2 x (hmem x hx)).2)
    hMsq Z hZ (δ / 2) (by linarith)
  have hfilter : Z.filter (fun w => 1 / 2 + δ / 2 + δ / 2 ≤ w.re) =
      Z.filter (fun w => 1 / 2 + δ ≤ w.re) := by
    refine Finset.filter_congr fun w _ => ?_
    rw [show 1 / 2 + δ / 2 + δ / 2 = 1 / 2 + δ by ring]
  rw [hfilter] at hmain
  set S : ℝ := ∑ w ∈ Z.filter (fun w => 1 / 2 + δ ≤ w.re),
    ((analyticOrderAt riemannZeta w).toNat : ℝ) with hS
  -- the right-hand side
  set r : ℝ := 3 * Real.sqrt η + 2 * η with hr
  have hr0 : 0 ≤ r := by positivity
  have hlog : Real.log ((T₂ - T₁) * (1 + r) / (T₂ - T₁)) ≤ r := by
    rw [mul_div_cancel_left₀ _ (by linarith : T₂ - T₁ ≠ 0)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + r by linarith)
    linarith
  have hsqrtη : Real.sqrt η ≤ Real.sqrt (32 * B) * (L + 2) ^ 3 * Real.exp (-(δ / 20 * L)) := by
    have h6 : η ≤ (Real.sqrt (32 * B) * (L + 2) ^ 3 * Real.exp (-(δ / 20 * L))) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, ← Real.exp_nat_mul]
      simp only [hη, hA]
      have hL6 : (L + 2) ^ 5 ≤ (L + 2) ^ (3 * 2) := pow_le_pow_right₀ (by linarith) (by norm_num)
      have hexp : Real.exp (-(δ / 10 * L)) = Real.exp (((2 : ℕ) : ℝ) * -(δ / 20 * L)) := by
        congr 1; push_cast; ring
      rw [hexp]
      have h0 : 0 ≤ 32 * B * Real.exp (((2 : ℕ) : ℝ) * -(δ / 20 * L)) := by positivity
      nlinarith
    calc Real.sqrt η ≤ Real.sqrt ((Real.sqrt (32 * B) * (L + 2) ^ 3 *
          Real.exp (-(δ / 20 * L))) ^ 2) := Real.sqrt_le_sqrt h6
      _ = _ := Real.sqrt_sq (by positivity)
  have hηsq : η ≤ Real.sqrt η := by
    have h1 : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hηle
    calc η = Real.sqrt η * Real.sqrt η := (Real.mul_self_sqrt hη0.le).symm
      _ ≤ Real.sqrt η * 1 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = Real.sqrt η := mul_one _
  have hr5 : r ≤ 5 * Real.sqrt η := by simp only [hr]; linarith
  have hlogT₂ : Real.log T₂ ≤ L := by
    have := Real.log_le_log (by linarith [hT₁.1]) (by linarith [hT₂.2] : T₂ ≤ E)
    rwa [hEdef, Real.log_exp] at this
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hlogX5 : Real.log ((X : ℝ) ^ (5 : ℕ)) ≤ 5 * (L / 4) := by
    rw [Real.log_pow]
    have := Real.log_le_log hXpos hXle
    rw [Real.log_exp] at this
    push_cast
    linarith
  have hRHS : (T₂ - T₁) / 2 * Real.log ((T₂ - T₁) * (1 + r) / (T₂ - T₁)) + C₀ +
      K₀ * (Real.log T₂ + Real.log ((X : ℝ) ^ (5 : ℕ))) ≤
      κ * (L + 2) ^ 3 * E * Real.exp (-(δ / 20 * L)) + (C₀ + 3 * K₀ * L) := by
    have h1 : (T₂ - T₁) / 2 * Real.log ((T₂ - T₁) * (1 + r) / (T₂ - T₁)) ≤ E / 8 * r := by
      calc (T₂ - T₁) / 2 * Real.log ((T₂ - T₁) * (1 + r) / (T₂ - T₁)) ≤ (T₂ - T₁) / 2 * r :=
            mul_le_mul_of_nonneg_left hlog (by linarith)
        _ ≤ E / 8 * r := mul_le_mul_of_nonneg_right (by linarith) hr0
    have h2 : E / 8 * r ≤ κ * (L + 2) ^ 3 * E * Real.exp (-(δ / 20 * L)) := by
      have := mul_le_mul_of_nonneg_left (hr5.trans (mul_le_mul_of_nonneg_left hsqrtη
        (by norm_num))) (by positivity : (0 : ℝ) ≤ E / 8)
      simp only [hκ]
      nlinarith
    have h3' : K₀ * (Real.log T₂ + Real.log ((X : ℝ) ^ (5 : ℕ))) ≤ 3 * K₀ * L := by
      have := mul_le_mul_of_nonneg_left (add_le_add hlogT₂ hlogX5) hK₀.le
      nlinarith
    linarith
  have hπδ : 0 < Real.pi * δ := by positivity
  have hcount : Real.pi * δ * S ≤
      κ * (L + 2) ^ 3 * E * Real.exp (-(δ / 20 * L)) + (C₀ + 3 * K₀ * L) := by
    have : 2 * Real.pi * (δ / 2 * S) = Real.pi * δ * S := by ring
    linarith
  -- the final comparison
  have hgoal : Real.exp L ^ (1 - δ / 40) = Real.exp (L * (1 - δ / 40)) := by
    rw [← Real.exp_mul]
  rw [hgoal]
  have hT1 : κ * (L + 2) ^ 3 * E * Real.exp (-(δ / 20 * L)) ≤
      Real.pi * δ / 2 * Real.exp (L * (1 - δ / 40)) := by
    have hsplit : E * Real.exp (-(δ / 20 * L)) =
        Real.exp (-(δ / 40 * L)) * Real.exp (L * (1 - δ / 40)) := by
      rw [hEdef, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h1 : κ * ((L + 2) ^ 3 * Real.exp (-(δ / 40 * L))) ≤ κ * (Real.pi * δ / (2 * κ)) :=
      mul_le_mul_of_nonneg_left hsmall hκ0.le
    have h2 : κ * (Real.pi * δ / (2 * κ)) = Real.pi * δ / 2 := by field_simp
    calc κ * (L + 2) ^ 3 * E * Real.exp (-(δ / 20 * L))
        = κ * ((L + 2) ^ 3 * Real.exp (-(δ / 40 * L))) * Real.exp (L * (1 - δ / 40)) := by
          rw [mul_assoc (κ * (L + 2) ^ 3), hsplit]; ring
      _ ≤ Real.pi * δ / 2 * Real.exp (L * (1 - δ / 40)) := by
          rw [← h2]
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hT2 : C₀ + 3 * K₀ * L ≤ Real.pi * δ / 2 * Real.exp (L * (1 - δ / 40)) := by
    have hlin' := hlin
    rw [pow_one] at hlin'
    have hc3 : 0 < C₀ + 3 * K₀ + 1 := by positivity
    have h1 : (C₀ + 3 * K₀ + 1) * ((L + 2) * Real.exp (-(1 / 2 * L))) ≤ Real.pi * δ / 2 := by
      have := mul_le_mul_of_nonneg_left hlin' hc3.le
      rwa [show (C₀ + 3 * K₀ + 1) * (Real.pi * δ / (2 * (C₀ + 3 * K₀ + 1))) = Real.pi * δ / 2 by
        field_simp] at this
    have h2 : C₀ + 3 * K₀ * L ≤ (C₀ + 3 * K₀ + 1) * (L + 2) := by nlinarith
    have h3e : Real.exp (L / 2) ≤ Real.exp (L * (1 - δ / 40)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h4 : (C₀ + 3 * K₀ + 1) * (L + 2) =
        (C₀ + 3 * K₀ + 1) * ((L + 2) * Real.exp (-(1 / 2 * L))) * Real.exp (L / 2) := by
      rw [mul_assoc (C₀ + 3 * K₀ + 1), mul_assoc (L + 2), ← Real.exp_add]
      rw [show -(1 / 2 * L) + L / 2 = 0 by ring, Real.exp_zero, mul_one]
    calc C₀ + 3 * K₀ * L ≤ (C₀ + 3 * K₀ + 1) * (L + 2) := h2
      _ = (C₀ + 3 * K₀ + 1) * ((L + 2) * Real.exp (-(1 / 2 * L))) * Real.exp (L / 2) := h4
      _ ≤ Real.pi * δ / 2 * Real.exp (L * (1 - δ / 40)) :=
          mul_le_mul h1 h3e (Real.exp_pos _).le (by positivity)
  have htot : Real.pi * δ * S ≤ Real.pi * δ * Real.exp (L * (1 - δ / 40)) := by linarith
  exact le_of_mul_le_mul_left htot hπδ

end RHTower
