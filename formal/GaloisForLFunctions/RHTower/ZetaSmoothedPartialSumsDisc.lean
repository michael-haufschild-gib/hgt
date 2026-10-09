import GaloisForLFunctions.RHTower.ZetaZeroSmoothedPartialSums

/-!
# Smoothed partial sums of `ζ`, uniformly on a disc

Let `ψ = Smooth1 ν ε` and let `B̄(ρ₀, r)` lie in the open strip `0 < Re ρ < 1`.  For every `A > 0`
there is `C` with (`exists_norm_tsum_smooth1_cpow_sub_le_disc`)

  `|Σ_n n^{−ρ}ψ(n/X) − ζ(ρ)ψ(1/X) − ν̃(ε(1 − ρ))X^{1−ρ}/(1 − ρ)| ≤ C X^{−A}`

for all `ρ ∈ B̄(ρ₀, r)` and `X > 0`.  No zero of `ζ` is assumed: the residue `ζ(ρ)ν̃(0) = ζ(ρ)` at
`s = 0` is the term `ζ(ρ)ψ(1/X)`.

**Proof.**  Split `ζ(s + ρ)/s = Z_ρ(s) + ζ(ρ)/s` with `Z_ρ(s) = (ζ(s + ρ) − ζ(ρ))/s`, holomorphic at
`s = 0`.  The smoothed Perron formula on `Re s = 3/2`, applied to the coefficients
`n^{−ρ} − ζ(ρ)δ_{n,1}`, gives `Σ n^{−ρ}ψ(n/X) − ζ(ρ)ψ(1/X)` as the vertical integral of
`Z_ρ(s)ν̃(εs)X^s`.  Shifting to `Re s = −A` picks up the residue at `s = 1 − ρ`.  On the new line
`|Z_ρ(s)ν̃(εs)| ≤ E(1 + |Im s|)^{−2}` with one `E` for the whole disc: polynomial growth of `ζ` on
strips beyond a fixed height, and compactness below it.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Interval

namespace RHTower

noncomputable section

theorem shiftedZetaQuot_eq_sub {ρ s : ℂ} (hs : s ≠ 0) :
    shiftedZetaQuot ρ s = (riemannZeta (s + ρ) - riemannZeta ρ) / s := by
  unfold shiftedZetaQuot
  rw [dslope_of_ne _ hs, slope_def_field]
  simp

/-- Polynomial growth of `Z_ρ` on vertical strips, uniformly in `ρ`. -/
theorem exists_norm_shiftedZetaQuot_le_unif (a b R M : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ ρ : ℂ, |ρ.re| ≤ R → |ρ.im| ≤ R → ‖riemannZeta ρ‖ ≤ M →
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → R + 1 ≤ |s.im| →
        ‖shiftedZetaQuot ρ s‖ ≤ C * |s.im| ^ N := by
  obtain ⟨C, N, hC0, hC⟩ := exists_bound_norm_riemannZeta_strip (|a| + |b| + |R| + 1)
  refine ⟨C * 2 ^ N + |M|, N, by positivity, fun ρ hρre hρim hM s ha hb him => ?_⟩
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hρre
  have hsim : 1 ≤ |s.im| := by linarith
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hsim; simp at hsim; linarith
  rw [shiftedZetaQuot_eq_sub hs0, norm_div]
  have hnorm : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hsρ : s + ρ = ((s.re + ρ.re : ℝ) : ℂ) + ((s.im + ρ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hre : |s.re + ρ.re| ≤ |a| + |b| + |R| + 1 := by
    have := abs_add_le (s.re) (ρ.re)
    have : |s.re| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
    have : R ≤ |R| := le_abs_self R
    linarith
  have himt : 1 ≤ |s.im + ρ.im| := by
    have := abs_sub_abs_le_abs_sub s.im (-ρ.im)
    rw [abs_neg, sub_neg_eq_add] at this
    linarith
  have hz := hC _ _ hre himt
  rw [← hsρ] at hz
  have himt2 : |s.im + ρ.im| ≤ 2 * |s.im| := by
    have := abs_add_le s.im ρ.im; linarith
  have hpow : |s.im + ρ.im| ^ N ≤ (2 * |s.im|) ^ N :=
    pow_le_pow_left₀ (abs_nonneg _) himt2 N
  have hpow1 : 1 ≤ |s.im| ^ N := one_le_pow₀ hsim
  rw [div_le_iff₀ (by linarith)]
  calc ‖riemannZeta (s + ρ) - riemannZeta ρ‖ ≤ ‖riemannZeta (s + ρ)‖ + ‖riemannZeta ρ‖ :=
        norm_sub_le _ _
    _ ≤ C * (2 * |s.im|) ^ N + |M| * |s.im| ^ N := by
        refine add_le_add (hz.trans (mul_le_mul_of_nonneg_left hpow hC0)) ?_
        calc ‖riemannZeta ρ‖ ≤ |M| := hM.trans (le_abs_self M)
          _ = |M| * 1 := (mul_one _).symm
          _ ≤ |M| * |s.im| ^ N := mul_le_mul_of_nonneg_left hpow1 (abs_nonneg _)
    _ = (C * 2 ^ N + |M|) * |s.im| ^ N * 1 := by rw [mul_pow]; ring
    _ ≤ (C * 2 ^ N + |M|) * |s.im| ^ N * ‖s‖ := by
        gcongr; linarith

/-- Decay of the kernel `Z_ρ(s)ν̃(εs)` on vertical strips, uniformly in `ρ`. -/
theorem exists_norm_zeroSmoothKernel_le_unif {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (a b R M : ℝ) :
    ∃ (D y₁ : ℝ), 0 ≤ D ∧ 1 ≤ y₁ ∧ ∀ ρ : ℂ, |ρ.re| ≤ R → |ρ.im| ≤ R →
      ‖riemannZeta ρ‖ ≤ M → ∀ s : ℂ, a ≤ s.re → s.re ≤ b → y₁ ≤ |s.im| →
        ‖zeroSmoothKernel ν ε ρ s‖ ≤ D * |s.im| ^ (-2 : ℝ) := by
  obtain ⟨CZ, N, hCZ0, hCZ⟩ := exists_norm_shiftedZetaQuot_le_unif a b R M
  obtain ⟨Cν, hCν0, hCν⟩ := exists_norm_mellin_le_rpow_of_bump (N + 2) hν
    (-(|a| + |b|)) (|a| + |b|)
  refine ⟨CZ * Cν / ε ^ (N + 2), max (|R| + 1) (1 / ε), by positivity,
    le_max_of_le_left (by linarith [abs_nonneg R]), fun ρ hρre hρim hM s ha hb hy => ?_⟩
  have hy1 : R + 1 ≤ |s.im| :=
    le_trans (by linarith [le_abs_self R]) (le_trans (le_max_left _ _) hy)
  have hy2 : 1 / ε ≤ |s.im| := le_trans (le_max_right _ _) hy
  have hyp : 0 < |s.im| := lt_of_lt_of_le (by positivity) hy2
  have hεs : (↑ε * s).re = ε * s.re := by simp
  have hεsi : (↑ε * s).im = ε * s.im := by simp
  have habs : |s.re| ≤ |a| + |b| := by
    rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
  have hstrip1 : -(|a| + |b|) ≤ (↑ε * s).re := by
    rw [hεs]
    have : |ε * s.re| ≤ |a| + |b| := by
      rw [abs_mul, abs_of_pos hε0]
      nlinarith [abs_nonneg s.re]
    linarith [neg_abs_le (ε * s.re)]
  have hstrip2 : (↑ε * s).re ≤ |a| + |b| := by
    rw [hεs]
    have := le_abs_self s.re
    nlinarith [abs_nonneg s.re]
  have him1 : 1 ≤ |(↑ε * s).im| := by
    rw [hεsi, abs_mul, abs_of_pos hε0]
    rw [div_le_iff₀ hε0] at hy2; linarith
  have hZ := hCZ ρ hρre hρim hM s ha hb hy1
  have hMl := hCν (↑ε * s) hstrip1 hstrip2 him1
  rw [hεsi, abs_mul, abs_of_pos hε0, mul_pow] at hMl
  unfold zeroSmoothKernel
  rw [norm_mul]
  have hrpow : |s.im| ^ (-2 : ℝ) = |s.im| ^ N / |s.im| ^ (N + 2) := by
    rw [pow_add, Real.rpow_neg hyp.le, Real.rpow_two]
    field_simp
  rw [hrpow]
  calc ‖shiftedZetaQuot ρ s‖ * ‖mellin (fun x : ℝ => (ν x : ℂ)) (↑ε * s)‖
      ≤ (CZ * |s.im| ^ N) * (Cν / (ε ^ (N + 2) * |s.im| ^ (N + 2))) :=
        mul_le_mul hZ hMl (norm_nonneg _) (by positivity)
    _ = CZ * Cν / ε ^ (N + 2) * (|s.im| ^ N / |s.im| ^ (N + 2)) := by
        field_simp

/-- **The left line, uniformly on the disc.**  On `Re s = −A` the kernel is bounded by
`E(1 + |Im s|)^{−2}` for every `ρ ∈ B̄(ρ₀, r)`. -/
theorem exists_norm_zeroSmoothKernel_leftLine_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {ρ₀ : ℂ} {r : ℝ}
    (hball : ∀ ρ ∈ Metric.closedBall ρ₀ r, 0 < ρ.re ∧ ρ.re < 1) {A : ℝ} (hA : 0 < A) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ ρ ∈ Metric.closedBall ρ₀ r, ∀ y : ℝ,
      ‖zeroSmoothKernel ν ε ρ ((-A : ℝ) + (y : ℂ) * I)‖ ≤ E * (1 + |y|) ^ (-2 : ℝ) := by
  set R : ℝ := ‖ρ₀‖ + |r| with hR
  have hζcont : ContinuousOn riemannZeta (Metric.closedBall ρ₀ r) := fun ρ hρ =>
    (differentiableAt_riemannZeta (fun h => by
      have := (hball ρ hρ).2; rw [h] at this; simp at this)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall ρ₀ r).exists_bound_of_continuousOn hζcont
  set M' : ℝ := max M 0 with hM'def
  have hM' : ∀ ρ ∈ Metric.closedBall ρ₀ r, ‖riemannZeta ρ‖ ≤ M' := fun ρ hρ =>
    (hM ρ hρ).trans (le_max_left _ _)
  have hRbd : ∀ ρ ∈ Metric.closedBall ρ₀ r, |ρ.re| ≤ R ∧ |ρ.im| ≤ R := by
    intro ρ hρ
    have h1 : ‖ρ‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hρ
      have : ‖ρ‖ ≤ ‖ρ₀‖ + ‖ρ - ρ₀‖ := by
        calc ‖ρ‖ = ‖ρ₀ + (ρ - ρ₀)‖ := by ring_nf
          _ ≤ ‖ρ₀‖ + ‖ρ - ρ₀‖ := norm_add_le _ _
      linarith [le_abs_self r]
    exact ⟨(Complex.abs_re_le_norm ρ).trans h1, (Complex.abs_im_le_norm ρ).trans h1⟩
  obtain ⟨D, y₁, hD0, hy₁, hdec⟩ :=
    exists_norm_zeroSmoothKernel_le_unif hν hε0 hε1 (-A) (-A) R M'
  set K : Set ℂ := Icc (-A) (1 - A) ×ℂ Icc (-(y₁ + R)) (y₁ + R) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKcont : ContinuousOn riemannZeta K := fun w hw =>
    (differentiableAt_riemannZeta (fun h => by
      have := (mem_reProdIm.mp hw).1.2; rw [h] at this; simp at this; linarith)).continuousAt.continuousWithinAt
  obtain ⟨Z₁, hZ₁⟩ := hKc.exists_bound_of_continuousOn hKcont
  set Z : ℝ := max Z₁ 0 with hZdef
  obtain ⟨Cν, hCν0, hCν⟩ := exists_norm_mellin_le_of_support hν.1.continuous hν.2
    (-(ε * A)) (-(ε * A))
  set E₁ : ℝ := (Z + M') * Cν / A * (1 + y₁) ^ 2 with hE₁
  refine ⟨max E₁ (4 * D), by positivity, fun ρ hρ y => ?_⟩
  obtain ⟨hRre, hRim⟩ := hRbd ρ hρ
  set s : ℂ := ((-A : ℝ) : ℂ) + (y : ℂ) * I with hsdef
  have hsre : s.re = -A := by simp [hsdef]
  have hsim : s.im = y := by simp [hsdef]
  have hpos : 0 < 1 + |y| := by positivity
  have hinv : (1 + |y|) ^ (-2 : ℝ) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hpos.le, Real.rpow_two]
  rcases le_or_gt y₁ |y| with hy | hy
  · have h := hdec ρ hRre hRim (hM' ρ hρ) s (by rw [hsre]) (by rw [hsre])
      (by rw [hsim]; exact hy)
    rw [hsim] at h
    have hy0 : 0 < |y| := by linarith
    rw [Real.rpow_neg hy0.le, Real.rpow_two] at h
    rw [hinv]
    calc ‖zeroSmoothKernel ν ε ρ s‖ ≤ D * (|y| ^ 2)⁻¹ := h
      _ ≤ D * (4 * ((1 + |y|) ^ 2)⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ hD0
          rw [show 4 * ((1 + |y|) ^ 2)⁻¹ = 4 / (1 + |y|) ^ 2 by ring, inv_eq_one_div,
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ = 4 * D * ((1 + |y|) ^ 2)⁻¹ := by ring
      _ ≤ max E₁ (4 * D) * ((1 + |y|) ^ 2)⁻¹ := by gcongr; exact le_max_right _ _
  · have hs0 : s ≠ 0 := fun h => by
      have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
    have hsA : A ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rwa [hsre, abs_neg, abs_of_pos hA] at this
    have hwK : s + ρ ∈ K := by
      rw [mem_reProdIm]
      have hρb := hball ρ hρ
      have hyab := abs_lt.mp hy
      have hρim := abs_le.mp hRim
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [Complex.add_re, Complex.add_im, hsre, hsim] <;>
        linarith [hρb.1, hρb.2]
    have hζ1 : ‖riemannZeta (s + ρ)‖ ≤ Z := (hZ₁ _ hwK).trans (le_max_left _ _)
    have hνb : ‖mellin (fun x : ℝ => (ν x : ℂ)) (↑ε * s)‖ ≤ Cν :=
      hCν _ (by simp [hsre]) (by simp [hsre])
    have hnum : ‖riemannZeta (s + ρ) - riemannZeta ρ‖ ≤ Z + M' :=
      (norm_sub_le _ _).trans (add_le_add hζ1 (hM' ρ hρ))
    have hy2 : (1 + |y|) ^ 2 ≤ (1 + y₁) ^ 2 := by
      have : 1 + |y| ≤ 1 + y₁ := by linarith
      exact pow_le_pow_left₀ hpos.le this 2
    unfold zeroSmoothKernel
    rw [shiftedZetaQuot_eq_sub hs0, norm_mul, norm_div, hinv]
    have hA0 : 0 < A := hA
    calc ‖riemannZeta (s + ρ) - riemannZeta ρ‖ / ‖s‖ * ‖mellin (fun x : ℝ => (ν x : ℂ)) (↑ε * s)‖
        ≤ (Z + M') / A * Cν := by
          refine mul_le_mul (div_le_div₀ (by positivity) hnum hA0 hsA) hνb (norm_nonneg _)
            (by positivity)
      _ = E₁ * ((1 + y₁) ^ 2)⁻¹ := by rw [hE₁]; field_simp
      _ ≤ E₁ * ((1 + |y|) ^ 2)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact inv_anti₀ (by positivity) hy2
      _ ≤ max E₁ (4 * D) * ((1 + |y|) ^ 2)⁻¹ := by gcongr; exact le_max_left _ _

/-! ## The contour identity for one `ρ` -/

theorem smooth1_eq_zero_of_three_le_disc {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {x : ℝ} (hx : 3 ≤ x) : Smooth1 ν ε x = 0 := by
  obtain ⟨c, _, hc, h⟩ := Smooth1Properties_above hν.2
  refine h ε x ⟨hε0, hε1⟩ ?_
  rw [hc]
  have := Real.log_two_lt_d9
  nlinarith

theorem lSeriesSummable_zeroCoeff {ρ s : ℂ} (hs : 1 < (s + ρ).re) :
    LSeriesSummable (zeroCoeff ρ) s := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1 - ρ.re) (by simp at hs; linarith)
    ⟨1, fun n hn => ?_⟩
  unfold zeroCoeff
  rw [if_neg hn, one_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
    Complex.neg_re]
  ring_nf
  exact le_rfl

theorem lSeriesSummable_delta (s : ℂ) (hs : 1 < s.re) : LSeriesSummable LSeries.delta s := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n hn => ?_⟩
  unfold LSeries.delta
  split_ifs <;> simp

/-- **The contour identity.**  For `0 < Re ρ < 1`, `A > 0`, `X > 0`:
`Σ n^{−ρ}ψ(n/X) − ζ(ρ)ψ(1/X) − ν̃(ε(1 − ρ))X^{1−ρ}/(1 − ρ)` is the vertical integral of
`Z_ρ(s)ν̃(εs)X^s` on `Re s = −A`. -/
theorem tsum_smooth1_cpow_sub_eq_verticalIntegral {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {A : ℝ} (hA : 0 < A)
    {X : ℝ} (hX : 0 < X) :
    (∑' n, zeroCoeff ρ n * (Smooth1 ν ε (n / X) : ℂ)) -
        riemannZeta ρ * (Smooth1 ν ε (1 / X) : ℂ) -
        (1 - ρ)⁻¹ * mellin (fun x : ℝ => (ν x : ℂ)) (ε * (1 - ρ)) * (X : ℂ) ^ (1 - ρ) =
      VerticalIntegral' (fun s => zeroSmoothKernel ν ε ρ s * (X : ℂ) ^ s) (-A) := by
  have hρne1 : ρ ≠ 1 := fun h => by rw [h] at hρ1; simp at hρ1
  set p : ℂ := 1 - ρ with hp
  have hpre : p.re = 1 - ρ.re := by simp [hp]
  have hp0 : p ≠ 0 := fun h => by rw [h] at hpre; simp at hpre; linarith
  set G : ℂ → ℂ := zeroSmoothKernel ν ε ρ with hG
  set f : ℂ → ℂ := fun s => G s * (X : ℂ) ^ s with hf
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hnormX : ∀ s : ℂ, ‖(X : ℂ) ^ s‖ = X ^ s.re := fun s =>
    Complex.norm_cpow_eq_rpow_re_of_pos hX s
  have hre_line : ∀ x y : ℝ, ((x : ℂ) + (y : ℂ) * I).re = x := fun x y => by simp
  have hfd : ∀ s : ℂ, s ≠ p → DifferentiableAt ℂ f s := fun s hs =>
    (differentiableAt_zeroSmoothKernel hν ε hρne1 hs).mul
      (differentiableAt_id.const_cpow (Or.inl hXc))
  set Rb : ℝ := |ρ.re| + |ρ.im| with hRb
  -- decay on the strip `[−A, 3/2]`
  obtain ⟨D, y₁, hD0, hy₁, hdec0⟩ :=
    exists_norm_zeroSmoothKernel_le_unif hν hε0 hε1 (-A) (3 / 2) Rb ‖riemannZeta ρ‖
  have hdec : ∀ s : ℂ, -A ≤ s.re → s.re ≤ 3 / 2 → y₁ ≤ |s.im| →
      ‖G s‖ ≤ D * |s.im| ^ (-2 : ℝ) := fun s h1 h2 h3 =>
    hdec0 ρ (by rw [hRb]; linarith [abs_nonneg ρ.im]) (by rw [hRb]; linarith [abs_nonneg ρ.re])
      le_rfl s h1 h2 h3
  have hbase : Integrable fun y : ℝ => (1 + |y|) ^ (-2 : ℝ) := by
    have h : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ)) :=
      integrable_one_add_norm (by norm_num)
    exact h.congr (Eventually.of_forall fun y => by simp only [Real.norm_eq_abs])
  have hlinecont : ∀ x : ℝ, x ≠ p.re → Continuous fun y : ℝ => G ((x : ℂ) + (y : ℂ) * I) := by
    intro x hx
    refine continuous_iff_continuousAt.mpr fun y => ?_
    have hne : (x : ℂ) + (y : ℂ) * I ≠ p := by
      intro h; apply hx; rw [← h]; simp
    exact ((differentiableAt_zeroSmoothKernel hν ε hρne1 hne).continuousAt).comp
      (f := fun y : ℝ => (x : ℂ) + (y : ℂ) * I) (by fun_prop)
  have hlineInt : ∀ x : ℝ, -A ≤ x → x ≤ 3 / 2 → x ≠ p.re →
      Integrable fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I) := by
    intro x hx1 hx2 hxp
    obtain ⟨E, hE0, hE⟩ := exists_bound_one_add_sq_of_decay (hlinecont x hxp) hy₁ hD0
      (fun y hy => by
        have := hdec ((x : ℂ) + (y : ℂ) * I) (by simp; linarith) (by simp; linarith)
          (by simpa using hy)
        simpa using this)
    refine (hbase.const_mul (E * X ^ x)).mono'
      ((hlinecont x hxp).mul (Continuous.const_cpow (by fun_prop) (Or.inl hXc))).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simp only [hf]
    rw [norm_mul, hnormX, hre_line]
    calc ‖G ((x : ℂ) + (y : ℂ) * I)‖ * X ^ x ≤ E * (1 + |y|) ^ (-2 : ℝ) * X ^ x :=
          mul_le_mul_of_nonneg_right (hE y) (by positivity)
      _ = E * X ^ x * (1 + |y|) ^ (-2 : ℝ) := by ring
  -- Perron on `Re s = 3/2` for `c = (1 + |ζ(ρ)|)⁻¹(n^{−ρ} − ζ(ρ)δ)`
  set k : ℝ := 1 + ‖riemannZeta ρ‖ with hk
  have hk0 : 0 < k := by positivity
  set c : ℕ → ℂ := ((k : ℂ)⁻¹) • (zeroCoeff ρ - riemannZeta ρ • LSeries.delta) with hc
  have hc0 : c 0 = 0 := by simp [hc, zeroCoeff, LSeries.delta]
  have hc1 : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    simp only [hc, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0]
    rw [inv_mul_le_one₀ hk0]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have h1 := norm_zeroCoeff_le hρ0.le n
    have h2 : ‖LSeries.delta n‖ ≤ 1 := by unfold LSeries.delta; split_ifs <;> simp
    have := mul_le_mul_of_nonneg_left h2 (norm_nonneg (riemannZeta ρ))
    rw [hk]; linarith
  have hP := GaloisForLFunctions.HTGeometry.SmoothedPerron.verticalIntegral'_eq_tsum_smooth1
    (hν.1.of_le (by exact_mod_cast le_top)) νpos hν.2 mass_one c hc0 hc1 hX hε0 hε1
    (σ := 3 / 2) (by norm_num) (by norm_num)
  have hsumm : ∀ g : ℕ → ℂ, Summable fun n : ℕ => g n * (Smooth1 ν ε (n / X) : ℂ) := by
    intro g
    refine summable_of_ne_finset_zero (s := Finset.range (⌈3 * X⌉₊ + 1)) fun n hn => ?_
    have hn' : 3 * X ≤ n := by
      have := Nat.le_ceil (3 * X)
      have : ⌈3 * X⌉₊ + 1 ≤ n := by simpa using hn
      have h2 : ((⌈3 * X⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈3 * X⌉₊ ≤ n)
      linarith
    rw [smooth1_eq_zero_of_three_le_disc hν hε0 hε1 (by rw [le_div_iff₀ hX]; linarith)]
    simp
  have htsum : ∑' n, c n * (Smooth1 ν ε (n / X) : ℂ) =
      (k : ℂ)⁻¹ * ((∑' n, zeroCoeff ρ n * (Smooth1 ν ε (n / X) : ℂ)) -
        riemannZeta ρ * (Smooth1 ν ε (1 / X) : ℂ)) := by
    have hδ : ∑' n, (riemannZeta ρ * LSeries.delta n) * (Smooth1 ν ε (n / X) : ℂ) =
        riemannZeta ρ * (Smooth1 ν ε (1 / X) : ℂ) := by
      rw [tsum_eq_single 1 (fun n hn => by simp [LSeries.delta, hn])]
      simp [LSeries.delta]
    rw [← hδ, ← (hsumm _).tsum_sub (hsumm _), ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [hc, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hright_eq : VerticalIntegral' f (3 / 2) = (k : ℂ) *
      VerticalIntegral' (fun s => LSeries c s *
        mellin (fun x ↦ ((Smooth1 ν ε x : ℝ) : ℂ)) s * (X : ℂ) ^ s) (3 / 2) := by
    have hpt : ∀ t : ℝ, f (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
        (k : ℂ) * (LSeries c (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          mellin (fun x ↦ ((Smooth1 ν ε x : ℝ) : ℂ)) (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          (X : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
      intro t
      set s : ℂ := ((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hs
      have hsre : s.re = 3 / 2 := by simp [hs]
      have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; norm_num at hsre
      have hsρ : 1 < (s + ρ).re := by simp [hsre]; linarith
      have hLc : LSeries c s = (k : ℂ)⁻¹ * (riemannZeta (s + ρ) - riemannZeta ρ) := by
        rw [hc, LSeries_smul, LSeries_sub (lSeriesSummable_zeroCoeff hsρ)
          ((lSeriesSummable_delta s (by rw [hsre]; norm_num)).smul _), LSeries_smul,
          LSeries_zeroCoeff hsρ, LSeries_delta]
        simp
      simp only [hf, hG, zeroSmoothKernel]
      rw [shiftedZetaQuot_eq_sub hs0, hLc, MellinOfSmooth1a
        (hν.1.of_le (by exact_mod_cast le_top)) hν.2 hε0 (by rw [hsre]; norm_num)]
      have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
      field_simp
    have hint : ∫ t : ℝ, f (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
        (k : ℂ) * ∫ t : ℝ, LSeries c (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          mellin (fun x ↦ ((Smooth1 ν ε x : ℝ) : ℂ)) (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          (X : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall hpt)
    simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
    rw [hint]
    ring
  -- holomorphy and the pole
  have hhol : HolomorphicOn f (Set.Icc (-A) (3 / 2) ×ℂ Set.univ \ {p}) := by
    intro s hs
    exact (hfd s hs.2).differentiableWithinAt
  set R₀ : ℂ := p⁻¹ * mellin (fun x : ℝ => (ν x : ℂ)) (ε * p) * (X : ℂ) ^ p with hR₀
  have hpole : (f - fun s => R₀ / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    set H : ℂ → ℂ := fun s => (zetaResidueUnit (s + ρ) - riemannZeta ρ * (s - p)) * s⁻¹ *
      mellin (fun x : ℝ => (ν x : ℂ)) (ε * s) * (X : ℂ) ^ s with hH
    have hHd : DifferentiableAt ℂ H p := by
      have h1 : DifferentiableAt ℂ (fun s => zetaResidueUnit (s + ρ)) p :=
        (analyticAt_zetaResidueUnit (p + ρ)).differentiableAt.comp p
          (differentiableAt_id.add_const ρ)
      exact (((h1.sub ((differentiableAt_id.sub_const p).const_mul _)).mul
        (differentiableAt_inv hp0)).mul
        ((differentiable_mellin_of_bump hν (ε * p)).comp p
          (differentiableAt_id.const_mul (ε : ℂ)))).mul
        (differentiableAt_id.const_cpow (Or.inl hXc))
    have hHp : H p = R₀ := by
      simp only [hH, hR₀, hp, sub_self, mul_zero, sub_zero]
      rw [show (1 : ℂ) - ρ + ρ = 1 by ring, zetaResidueUnit_one, one_mul]
    have h := GaloisForLFunctions.HTGeometry.SmoothedPerron.isBigO_div_sub_div hHd
    rw [hHp] at h
    refine h.congr' ?_ (Eventually.of_forall fun s => rfl)
    have hU : {s : ℂ | s ≠ 0} ∈ 𝓝 p := isOpen_ne.mem_nhds hp0
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hU] with s hsp hs0
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hsp
    simp only [Pi.sub_apply, hf, hG, hH, zeroSmoothKernel]
    have hs1 : s + ρ ≠ 1 := fun h => hsp (by rw [hp]; linear_combination h)
    have hZu : zetaResidueUnit (s + ρ) = (s + ρ - 1) * riemannZeta (s + ρ) :=
      (zetaResidueUnit_eventuallyEq hs1).eq_of_nhds
    have hsub : s - p = s + ρ - 1 := by rw [hp]; ring
    have hsub0 : s + ρ - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [shiftedZetaQuot_eq_sub hs0, hZu, hsub]
    field_simp
  -- horizontal decay
  set B : ℝ := D * (X ^ (-A) + X ^ (3 / 2 : ℝ)) with hB
  have hhor : ∀ y : ℝ, y₁ ≤ |y| → ∀ x ∈ Ι (-A) (3 / 2),
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * |y| ^ (-2 : ℝ) := by
    intro y hy x hx
    rw [uIoc_of_le (by linarith)] at hx
    have hdx := hdec ((x : ℂ) + (y : ℂ) * I) (by simp; linarith [hx.1]) (by simp; exact hx.2)
      (by simpa using hy)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero] at hdx
    have hXx : X ^ x ≤ X ^ (-A) + X ^ (3 / 2 : ℝ) := by
      rcases le_or_gt 1 X with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h hx.2
        linarith [Real.rpow_nonneg hX.le (-A)]
      · have := Real.rpow_le_rpow_of_exponent_ge hX h.le hx.1.le
        linarith [Real.rpow_nonneg hX.le (3 / 2 : ℝ)]
    simp only [hf]
    rw [norm_mul, hnormX, hre_line]
    calc ‖G ((x : ℂ) + (y : ℂ) * I)‖ * X ^ x ≤ D * |y| ^ (-2 : ℝ) *
          (X ^ (-A) + X ^ (3 / 2 : ℝ)) :=
          mul_le_mul hdx hXx (by positivity) (by positivity)
      _ = B * |y| ^ (-2 : ℝ) := by rw [hB]; ring
  have hlim : Tendsto (fun y : ℝ => B * |y| ^ (-2 : ℝ) * |3 / 2 - -A|) atTop (𝓝 0) ∧
      Tendsto (fun y : ℝ => B * |y| ^ (-2 : ℝ) * |3 / 2 - -A|) atBot (𝓝 0) := by
    have hp2 : Tendsto (fun y : ℝ => y ^ (-2 : ℝ)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    constructor
    · have := ((hp2.comp tendsto_abs_atTop_atTop).const_mul B).mul_const |3 / 2 - -A|
      simpa using this
    · have := ((hp2.comp tendsto_abs_atBot_atTop).const_mul B).mul_const |3 / 2 - -A|
      simpa using this
  have htop : Tendsto (fun y : ℝ => ∫ x in (-A)..(3 / 2 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim.1
    filter_upwards [eventually_ge_atTop y₁] with y hy
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hhor y (le_trans hy (le_abs_self y)) x hx
  have hbot : Tendsto (fun y : ℝ => ∫ x in (-A)..(3 / 2 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim.2
    filter_upwards [eventually_le_atBot (-y₁)] with y hy
    have hy' : y₁ ≤ |y| := by rw [abs_of_neg (by linarith)]; linarith
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => hhor y hy' x hx
  have hshift := GaloisForLFunctions.HTGeometry.verticalIntegral'_sub_of_simple_pole
    (σ := -A) (σ' := 3 / 2) (p := p) (A := R₀) (f := f) (by rw [hpre]; linarith)
    (by rw [hpre]; linarith) hhol hpole hbot htop
    (hlineInt (-A) le_rfl (by linarith) (by rw [hpre]; linarith))
    (hlineInt (3 / 2) (by linarith) le_rfl (by rw [hpre]; linarith))
  rw [hright_eq, hP, htsum] at hshift
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  rw [mul_inv_cancel_left₀ hkC] at hshift
  rw [hR₀] at hshift
  linear_combination hshift

/-! ## The uniform estimate -/

/-- **Smoothed partial sums of `ζ`, uniformly on a disc.** -/
theorem exists_norm_tsum_smooth1_cpow_sub_le_disc {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {ρ₀ : ℂ} {r : ℝ}
    (hball : ∀ ρ ∈ Metric.closedBall ρ₀ r, 0 < ρ.re ∧ ρ.re < 1) {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ ∈ Metric.closedBall ρ₀ r, ∀ X : ℝ, 0 < X →
      ‖(∑' n, zeroCoeff ρ n * (Smooth1 ν ε (n / X) : ℂ)) -
          riemannZeta ρ * (Smooth1 ν ε (1 / X) : ℂ) -
          (1 - ρ)⁻¹ * mellin (fun x : ℝ => (ν x : ℂ)) (ε * (1 - ρ)) * (X : ℂ) ^ (1 - ρ)‖ ≤
        C * X ^ (-A) := by
  obtain ⟨E, hE0, hE⟩ := exists_norm_zeroSmoothKernel_leftLine_le hν hε0 hε1 hball hA
  set I₀ : ℝ := ∫ y : ℝ, (1 + |y|) ^ (-2 : ℝ) with hI₀
  have hbase : Integrable fun y : ℝ => (1 + |y|) ^ (-2 : ℝ) := by
    have h : Integrable fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ)) :=
      integrable_one_add_norm (by norm_num)
    exact h.congr (Eventually.of_forall fun y => by simp only [Real.norm_eq_abs])
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun y => by positivity
  refine ⟨(2 * Real.pi)⁻¹ * (E * I₀), by positivity, fun ρ hρ X hX => ?_⟩
  obtain ⟨hρ0, hρ1⟩ := hball ρ hρ
  rw [tsum_smooth1_cpow_sub_eq_verticalIntegral hν νpos mass_one hε0 hε1 hρ0 hρ1 hA hX]
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hnorm : ‖1 / (2 * (Real.pi : ℂ) * I)‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, one_div]
  rw [hnorm]
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hpt : ∀ y : ℝ, ‖zeroSmoothKernel ν ε ρ (((-A : ℝ) : ℂ) + (y : ℂ) * I) *
      (X : ℂ) ^ (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ X ^ (-A) * (E * (1 + |y|) ^ (-2 : ℝ)) := by
    intro y
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
    have : (((-A : ℝ) : ℂ) + (y : ℂ) * I).re = -A := by simp
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_left (hE ρ hρ y) (by positivity)
  have hint := norm_integral_le_of_norm_le (hbase.const_mul E |>.const_mul (X ^ (-A)))
    (Eventually.of_forall hpt)
  rw [integral_const_mul, integral_const_mul] at hint
  have hπ : 0 < (2 * Real.pi)⁻¹ := by positivity
  calc (2 * Real.pi)⁻¹ * ‖∫ y : ℝ, zeroSmoothKernel ν ε ρ (((-A : ℝ) : ℂ) + (y : ℂ) * I) *
        (X : ℂ) ^ (((-A : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ (2 * Real.pi)⁻¹ * (X ^ (-A) * (E * I₀)) := mul_le_mul_of_nonneg_left hint hπ.le
    _ = (2 * Real.pi)⁻¹ * (E * I₀) * X ^ (-A) := by ring

end

end RHTower
