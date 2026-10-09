import GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment
import GaloisForLFunctions.HTGeometry.GammaHorizontalRatio
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.RHTower.XiStrongFirstOrderFilterNoGo

/-!
# The dyadic fourth moment of `Ξ`

`∫_X^{2X} e^{πy} Ξ(y)⁴ dy ≤ C X⁸ (log X)⁴` for `X ≥ 2` (`exists_integral_exp_mul_Xi_pow_four_le`).

**The Gamma factor on the line `Re z = ¼`.**  The Gauss product gives
`|Γ_n(a + ib)| ∏_{j ≤ n}(1 + b²/(a+j)²)^{1/2} = Γ_n(a)`.  With `A_j = 1 + b²/(j + ¾)²` and
`B_j = 1 + b²/(j + ¼)²`, convexity gives `A_j² ≤ B_j B_{j+1}` (`sq_one_add_sq_div_le`), so the
products telescope: `B₀(∏A_j)² ≤ B_n(∏B_j)²` (`prod_quarter_shift_le`).  In the limit
(`norm_Gamma_quarter_pow_four_le`)

  `|Γ(¼ + ib)|⁴ Γ(¾)⁴ (1 + 16b²) ≤ Γ(¼)⁴ |Γ(¾ + ib)|⁴`,

a gain of `|b|^{−1/2}` in the ratio `|Γ(¼ + ib)/Γ(¾ + ib)|`.  Legendre's duplication formula and
`|Γ(½ + iy)|² = π/cosh πy` give `(|Γ(¼ + ib)Γ(¾ + ib)|)² = 2π²/cosh 2πb`.  Together
(`exists_norm_Gamma_quarter_pow_four_mul_le`):

  `|Γ(¼ + ib)|⁴ √(1 + 16b²) cosh 2πb ≤ C`.

**Assembly.**  `Ξ(t) = ½ s(s − 1) π^{−s/2} Γ(s/2) ζ(s)` with `s = ½ + it`, so
`e^{πt}Ξ(t)⁴ ≤ C X⁷ |ζ(½ + it)|⁴` on `[X, 2X]`, and the fourth moment of `ζ` on the critical line
(`exists_integral_norm_riemannZeta_critical_pow_four_le`) finishes.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-! ## The Gamma factor on `Re z = ¼` -/

/-- `(1 + b²/m²)² ≤ (1 + b²/(m − ½)²)(1 + b²/(m + ½)²)` for `m > ½`. -/
theorem sq_one_add_sq_div_le (b : ℝ) {m : ℝ} (hm : 1 / 2 < m) :
    (1 + b ^ 2 / m ^ 2) ^ 2 ≤ (1 + b ^ 2 / (m - 1 / 2) ^ 2) * (1 + b ^ 2 / (m + 1 / 2) ^ 2) := by
  have hm0 : 0 < m := by linarith
  have hp : 0 < m - 1 / 2 := by linarith
  have hq : 0 < m + 1 / 2 := by linarith
  rw [show 1 + b ^ 2 / m ^ 2 = (m ^ 2 + b ^ 2) / m ^ 2 by
      rw [add_div, div_self (pow_ne_zero 2 hm0.ne')],
    show 1 + b ^ 2 / (m - 1 / 2) ^ 2 = ((m - 1 / 2) ^ 2 + b ^ 2) / (m - 1 / 2) ^ 2 by
      rw [add_div, div_self (pow_ne_zero 2 hp.ne')],
    show 1 + b ^ 2 / (m + 1 / 2) ^ 2 = ((m + 1 / 2) ^ 2 + b ^ 2) / (m + 1 / 2) ^ 2 by
      rw [add_div, div_self (pow_ne_zero 2 hq.ne')],
    div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have hB := sq_nonneg b
  have h1 : 0 ≤ 3 * m ^ 2 / 2 - 1 / 8 := by nlinarith
  have h2 : 0 ≤ 2 * m ^ 2 - 1 / 4 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hB (sq_nonneg m)) h1, mul_nonneg (mul_nonneg hB hB) h2]

/-- **Telescoping.**  `B₀(∏_{j<n} A_j)² ≤ B_n(∏_{j<n} B_j)²` with `A_j = 1 + b²/(¾ + j)²`,
`B_j = 1 + b²/(¼ + j)²`. -/
theorem prod_quarter_shift_le (b : ℝ) (n : ℕ) :
    (1 + b ^ 2 / (1 / 4 + ((0 : ℕ) : ℝ)) ^ 2) *
        (∏ j ∈ Finset.range n, (1 + b ^ 2 / (3 / 4 + (j : ℝ)) ^ 2)) ^ 2 ≤
      (1 + b ^ 2 / (1 / 4 + (n : ℝ)) ^ 2) *
        (∏ j ∈ Finset.range n, (1 + b ^ 2 / (1 / 4 + (j : ℝ)) ^ 2)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, mul_pow, mul_pow]
    have hA := sq_one_add_sq_div_le b (m := 3 / 4 + (n : ℝ))
      (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
    rw [show (3 / 4 + (n : ℝ)) - 1 / 2 = 1 / 4 + n by ring,
      show (3 / 4 + (n : ℝ)) + 1 / 2 = 1 / 4 + ((n + 1 : ℕ) : ℝ) by push_cast; ring] at hA
    set P := ∏ j ∈ Finset.range n, (1 + b ^ 2 / (3 / 4 + (j : ℝ)) ^ 2)
    set Q := ∏ j ∈ Finset.range n, (1 + b ^ 2 / (1 / 4 + (j : ℝ)) ^ 2)
    set A := 1 + b ^ 2 / (3 / 4 + (n : ℝ)) ^ 2
    set Bn := 1 + b ^ 2 / (1 / 4 + (n : ℝ)) ^ 2
    set Bn1 := 1 + b ^ 2 / (1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2
    have hBn : 0 ≤ Bn := by positivity
    calc (1 + b ^ 2 / (1 / 4 + ((0 : ℕ) : ℝ)) ^ 2) * (P ^ 2 * A ^ 2)
        = ((1 + b ^ 2 / (1 / 4 + ((0 : ℕ) : ℝ)) ^ 2) * P ^ 2) * A ^ 2 := by ring
      _ ≤ (Bn * Q ^ 2) * A ^ 2 := mul_le_mul_of_nonneg_right ih (sq_nonneg _)
      _ = Q ^ 2 * Bn * A ^ 2 := by ring
      _ ≤ Q ^ 2 * Bn * (Bn * Bn1) :=
          mul_le_mul_of_nonneg_left hA (mul_nonneg (sq_nonneg _) hBn)
      _ = Bn1 * (Q ^ 2 * Bn ^ 2) := by ring

theorem prod_sqrt_sq_sq (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (n : ℕ) :
    (∏ j ∈ Finset.range n, Real.sqrt (f j)) ^ 4 = (∏ j ∈ Finset.range n, f j) ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, ← Finset.prod_pow]
  congr 1
  exact Finset.prod_congr rfl fun j _ => Real.sq_sqrt (hf j)

/-- The finite Gauss products: `|Γ_n(¼ + ib)|⁴ Γ_n(¾)⁴ B₀ ≤ Γ_n(¼)⁴ |Γ_n(¾ + ib)|⁴ B_{n+1}`. -/
theorem norm_GammaSeq_quarter_pow_four_le (b : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖GammaSeq (((1 / 4 : ℝ) : ℂ) + b * I) n‖ ^ 4 * ‖GammaSeq ((3 / 4 : ℝ) : ℂ) n‖ ^ 4 *
        (1 + b ^ 2 / (1 / 4 + ((0 : ℕ) : ℝ)) ^ 2) ≤
      ‖GammaSeq ((1 / 4 : ℝ) : ℂ) n‖ ^ 4 * ‖GammaSeq (((3 / 4 : ℝ) : ℂ) + b * I) n‖ ^ 4 *
        (1 + b ^ 2 / (1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2) := by
  have h1 := HTGeometry.norm_GammaSeq_mul_prod (a := 1 / 4) (by norm_num) b hn
  have h3 := HTGeometry.norm_GammaSeq_mul_prod (a := 3 / 4) (by norm_num) b hn
  rw [← h1, ← h3]
  set x := ‖GammaSeq (((1 / 4 : ℝ) : ℂ) + b * I) n‖
  set y := ‖GammaSeq (((3 / 4 : ℝ) : ℂ) + b * I) n‖
  set Q₁ := ∏ j ∈ Finset.range (n + 1), Real.sqrt (1 + b ^ 2 / (1 / 4 + (j : ℝ)) ^ 2)
  set Q₃ := ∏ j ∈ Finset.range (n + 1), Real.sqrt (1 + b ^ 2 / (3 / 4 + (j : ℝ)) ^ 2)
  have hQ₁ : Q₁ ^ 4 = (∏ j ∈ Finset.range (n + 1), (1 + b ^ 2 / (1 / 4 + (j : ℝ)) ^ 2)) ^ 2 :=
    prod_sqrt_sq_sq _ (fun j => by positivity) _
  have hQ₃ : Q₃ ^ 4 = (∏ j ∈ Finset.range (n + 1), (1 + b ^ 2 / (3 / 4 + (j : ℝ)) ^ 2)) ^ 2 :=
    prod_sqrt_sq_sq _ (fun j => by positivity) _
  have key := prod_quarter_shift_le b (n + 1)
  rw [← hQ₁, ← hQ₃] at key
  have hxy : 0 ≤ x ^ 4 * y ^ 4 := by positivity
  calc x ^ 4 * (y * Q₃) ^ 4 * (1 + b ^ 2 / (1 / 4 + ((0 : ℕ) : ℝ)) ^ 2)
      = x ^ 4 * y ^ 4 * ((1 + b ^ 2 / (1 / 4 + ((0 : ℕ) : ℝ)) ^ 2) * Q₃ ^ 4) := by ring
    _ ≤ x ^ 4 * y ^ 4 * ((1 + b ^ 2 / (1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2) * Q₁ ^ 4) :=
        mul_le_mul_of_nonneg_left key hxy
    _ = (x * Q₁) ^ 4 * y ^ 4 * (1 + b ^ 2 / (1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2) := by ring

/-- **The quarter-shift ratio.**  `|Γ(¼ + ib)|⁴ Γ(¾)⁴ (1 + 16b²) ≤ Γ(¼)⁴ |Γ(¾ + ib)|⁴`. -/
theorem norm_Gamma_quarter_pow_four_le (b : ℝ) :
    ‖Gamma (((1 / 4 : ℝ) : ℂ) + b * I)‖ ^ 4 * ‖Gamma ((3 / 4 : ℝ) : ℂ)‖ ^ 4 *
        (1 + 16 * b ^ 2) ≤
      ‖Gamma ((1 / 4 : ℝ) : ℂ)‖ ^ 4 * ‖Gamma (((3 / 4 : ℝ) : ℂ) + b * I)‖ ^ 4 := by
  have hlin : Tendsto (fun n : ℕ => (1 / 4 : ℝ) + ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hB : Tendsto (fun n : ℕ => 1 + b ^ 2 / ((1 / 4 : ℝ) + ((n + 1 : ℕ) : ℝ)) ^ 2) atTop
      (𝓝 1) := by
    have := (tendsto_const_nhds (x := b ^ 2)).div_atTop
      ((tendsto_pow_atTop (two_ne_zero)).comp hlin)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add this
  have h1 := (((GammaSeq_tendsto_Gamma (((1 / 4 : ℝ) : ℂ) + b * I)).norm.pow 4).mul
    ((GammaSeq_tendsto_Gamma ((3 / 4 : ℝ) : ℂ)).norm.pow 4)).mul_const
    (1 + b ^ 2 / (1 / 4 + ((0 : ℕ) : ℝ)) ^ 2)
  have h2 := (((GammaSeq_tendsto_Gamma ((1 / 4 : ℝ) : ℂ)).norm.pow 4).mul
    ((GammaSeq_tendsto_Gamma (((3 / 4 : ℝ) : ℂ) + b * I)).norm.pow 4)).mul hB
  rw [mul_one] at h2
  have h := le_of_tendsto_of_tendsto h1 h2
    ((eventually_gt_atTop 0).mono fun n hn => norm_GammaSeq_quarter_pow_four_le b hn)
  have e : (1 + b ^ 2 / (1 / 4 + ((0 : ℕ) : ℝ)) ^ 2) = 1 + 16 * b ^ 2 := by
    rw [Nat.cast_zero, add_zero]; ring
  rwa [e] at h

/-- **Duplication.**  `(|Γ(¼ + ib)| |Γ(¾ + ib)|)² = 2π²/cosh 2πb`. -/
theorem norm_Gamma_quarter_mul_sq (b : ℝ) :
    (‖Gamma (((1 / 4 : ℝ) : ℂ) + b * I)‖ * ‖Gamma (((3 / 4 : ℝ) : ℂ) + b * I)‖) ^ 2 =
      2 * Real.pi ^ 2 / Real.cosh (2 * Real.pi * b) := by
  have h := Complex.Gamma_mul_Gamma_add_half (((1 / 4 : ℝ) : ℂ) + b * I)
  have e1 : ((1 / 4 : ℝ) : ℂ) + b * I + 1 / 2 = ((3 / 4 : ℝ) : ℂ) + b * I := by
    push_cast; ring
  have e2 : 2 * (((1 / 4 : ℝ) : ℂ) + b * I) = 1 / 2 + ((2 * b : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e1, e2] at h
  have hn := congrArg (fun w : ℂ => ‖w‖) h
  simp only [norm_mul] at hn
  have h2 : ‖(2 : ℂ) ^ (1 - (1 / 2 + ((2 * b : ℝ) : ℂ) * I))‖ = Real.sqrt 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
      Real.sqrt_eq_rpow]
    congr 1
    simp
    norm_num
  have hpi : ‖((Real.sqrt Real.pi : ℝ) : ℂ)‖ = Real.sqrt Real.pi := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [h2, hpi] at hn
  rw [hn, mul_pow, mul_pow, GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_sq,
    Real.sq_sqrt (by norm_num), Real.sq_sqrt Real.pi_pos.le]
  ring_nf

/-- **The Gamma factor on `Re z = ¼`.**  `|Γ(¼ + ib)|⁴ √(1 + 16b²) cosh 2πb ≤ C`. -/
theorem exists_norm_Gamma_quarter_pow_four_mul_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, ‖Gamma (((1 / 4 : ℝ) : ℂ) + b * I)‖ ^ 4 *
      (Real.sqrt (1 + 16 * b ^ 2) * Real.cosh (2 * Real.pi * b)) ≤ C := by
  set g₁ := ‖Gamma ((1 / 4 : ℝ) : ℂ)‖
  set g₃ := ‖Gamma ((3 / 4 : ℝ) : ℂ)‖
  have hg₃ : 0 < g₃ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  refine ⟨g₁ ^ 2 * (2 * Real.pi ^ 2) / g₃ ^ 2, by positivity, fun b => ?_⟩
  set x := ‖Gamma (((1 / 4 : ℝ) : ℂ) + b * I)‖
  set y := ‖Gamma (((3 / 4 : ℝ) : ℂ) + b * I)‖
  set ch := Real.cosh (2 * Real.pi * b)
  have hch : 0 < ch := Real.cosh_pos _
  have hB0 : 0 ≤ 1 + 16 * b ^ 2 := by positivity
  have H1 := norm_Gamma_quarter_pow_four_le b
  have H2 := norm_Gamma_quarter_mul_sq b
  set L := x ^ 4 * (Real.sqrt (1 + 16 * b ^ 2) * ch)
  have hL : 0 ≤ L := by positivity
  have hL2 : (L * g₃ ^ 2) ^ 2 ≤ (g₁ ^ 2 * (2 * Real.pi ^ 2)) ^ 2 := by
    have e1 : (L * g₃ ^ 2) ^ 2 = x ^ 4 * ch ^ 2 * (x ^ 4 * g₃ ^ 4 * (1 + 16 * b ^ 2)) := by
      simp only [L]
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hB0]
      ring
    have e2 : (g₁ ^ 2 * (2 * Real.pi ^ 2)) ^ 2 = x ^ 4 * ch ^ 2 * (g₁ ^ 4 * y ^ 4) := by
      have : x ^ 4 * ch ^ 2 * (g₁ ^ 4 * y ^ 4) = g₁ ^ 4 * ch ^ 2 * ((x * y) ^ 2) ^ 2 := by ring
      rw [this, H2]
      field_simp
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left H1 (by positivity)
  have hL' := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hL2
  rw [le_div_iff₀ (by positivity)]
  exact hL'

/-! ## Assembly -/

theorem continuous_riemannZeta_half_line :
    Continuous fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hne : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  exact (differentiableAt_riemannZeta hne).continuousAt.comp
    (f := fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by fun_prop)

/-- `|Ξ(t)| ≤ |s(s − 1)/2| |Γ(¼ + it/2)| |ζ(½ + it)|` with `s = ½ + it`. -/
theorem abs_Xi_le (t : ℝ) :
    |Xi t| ≤ ‖((1 / 2 : ℂ) + t * I) * ((1 / 2 : ℂ) + t * I - 1) / 2‖ *
      ‖Gamma (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ *
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  set s : ℂ := (1 / 2 : ℂ) + t * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hre; norm_num at hre
  have hs1 : s ≠ 1 := fun h => by rw [h] at hre; norm_num at hre
  have hxi : xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
    rw [xi, completedRiemannZeta_eq]
    have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    field_simp
    ring
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num)
  have hΛ : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0]; field_simp
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
    have : (-s / 2).re = -(1 / 4) := by
      rw [Complex.div_re, Complex.neg_re, hre]; norm_num
    rw [this]; norm_num
  have hs2 : s / 2 = ((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
  have hζ : riemannZeta s = riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    rw [hs]; push_cast; ring_nf
  have hX : Xi t = (xi s).re := rfl
  rw [hX]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [hxi, hΛ, Gammaℝ_def, hs2, hζ, norm_mul, norm_mul, norm_mul]
  set A := ‖s * (s - 1) / 2‖
  set P := ‖(Real.pi : ℂ) ^ (-s / 2)‖
  set G := ‖Gamma (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖
  set Z := ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖
  have h1 : P * G * Z ≤ G * Z := by
    have := mul_le_mul_of_nonneg_right hpi (mul_nonneg (norm_nonneg _) (norm_nonneg _) :
      (0 : ℝ) ≤ G * Z)
    linarith [show P * G * Z = P * (G * Z) by ring]
  calc A * (P * G * Z) ≤ A * (G * Z) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = A * G * Z := by ring

/-- **The dyadic fourth moment of `Ξ`.**  `∫_X^{2X} e^{πy} Ξ(y)⁴ dy ≤ C X⁸ (log X)⁴` for
`X ≥ 2`. -/
theorem exists_integral_exp_mul_Xi_pow_four_le :
    ∃ C₄ : ℝ, 0 ≤ C₄ ∧ ∀ X : ℝ, 2 ≤ X →
      ∫ y in X..2 * X, Real.exp (Real.pi * y) * Xi y ^ 4 ≤
        C₄ * X ^ (8 : ℝ) * Real.log X ^ 4 := by
  obtain ⟨CG, hCG, hG⟩ := exists_norm_Gamma_quarter_pow_four_mul_le
  obtain ⟨D, hD, hmom⟩ := exists_integral_norm_riemannZeta_critical_pow_four_le
  set K : ℝ := (9 / 2 : ℝ) ^ 4 * (2 * CG) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * D * 3 * 6 ^ 4, by positivity, fun X hX => ?_⟩
  have hX0 : 0 < X := by linarith
  set Z : ℝ → ℝ := fun y => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ^ 4 with hZ
  have hZc : Continuous Z := continuous_riemannZeta_half_line.norm.pow 4
  -- the pointwise bound on `[X, 2X]`
  have hpt : ∀ y ∈ Icc X (2 * X), Real.exp (Real.pi * y) * Xi y ^ 4 ≤ K * X ^ 7 * Z y := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have hXi := abs_Xi_le y
    set A := ‖((1 / 2 : ℂ) + y * I) * ((1 / 2 : ℂ) + y * I - 1) / 2‖
    set G := ‖Gamma (((1 / 4 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖
    set ζ := ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖
    have hA : A ≤ 9 * X ^ 2 / 2 := by
      have hn1 : ‖(1 / 2 : ℂ) + y * I‖ ≤ 1 / 2 + y := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hy0.le]
        norm_num
      have hn2 : ‖(1 / 2 : ℂ) + y * I - 1‖ ≤ 1 / 2 + y := by
        rw [show (1 / 2 : ℂ) + y * I - 1 = -(1 / 2 : ℂ) + y * I by ring]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hy0.le,
          norm_neg]
        norm_num
      have h3 : 1 / 2 + y ≤ 3 * X := by linarith [hy.2]
      simp only [A]
      rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
      have := mul_le_mul (hn1.trans h3) (hn2.trans h3) (norm_nonneg _) (by positivity)
      linarith
    have hGb := hG (y / 2)
    have hsq : X ≤ Real.sqrt (1 + 16 * (y / 2) ^ 2) := by
      rw [Real.le_sqrt hX0.le (by positivity)]
      nlinarith [hy.1]
    have hcosh : Real.exp (Real.pi * y) / 2 ≤ Real.cosh (2 * Real.pi * (y / 2)) := by
      rw [show 2 * Real.pi * (y / 2) = Real.pi * y by ring, Real.cosh_eq]
      linarith [Real.exp_pos (-(Real.pi * y))]
    have hGexp : Real.exp (Real.pi * y) * G ^ 4 ≤ 2 * CG / X := by
      rw [le_div_iff₀ hX0]
      have h1 : G ^ 4 * (X * (Real.exp (Real.pi * y) / 2)) ≤
          G ^ 4 * (Real.sqrt (1 + 16 * (y / 2) ^ 2) * Real.cosh (2 * Real.pi * (y / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hsq hcosh (by positivity) (Real.sqrt_nonneg _))
          (by positivity)
      have h2 := h1.trans hGb
      nlinarith
    have hXi4 : Xi y ^ 4 ≤ (A * G * ζ) ^ 4 := by
      rw [← Even.pow_abs (by decide : Even 4) (Xi y)]
      exact pow_le_pow_left₀ (abs_nonneg _) hXi 4
    have hA4 : A ^ 4 ≤ (9 * X ^ 2 / 2) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hA 4
    calc Real.exp (Real.pi * y) * Xi y ^ 4 ≤ Real.exp (Real.pi * y) * (A * G * ζ) ^ 4 :=
          mul_le_mul_of_nonneg_left hXi4 (Real.exp_pos _).le
      _ = A ^ 4 * (Real.exp (Real.pi * y) * G ^ 4) * ζ ^ 4 := by ring
      _ ≤ (9 * X ^ 2 / 2) ^ 4 * (2 * CG / X) * ζ ^ 4 := by
          gcongr
      _ = K * X ^ 7 * Z y := by
          simp only [hK, hZ]
          field_simp
          ring
  have hint1 : IntervalIntegrable (fun y => Real.exp (Real.pi * y) * Xi y ^ 4) volume X
      (2 * X) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Littlewood.continuous_Xi.pow 4)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun y => K * X ^ 7 * Z y) volume X (2 * X) :=
    (continuous_const.mul hZc).intervalIntegrable _ _
  have step1 := intervalIntegral.integral_mono_on (by linarith) hint1 hint2 hpt
  rw [intervalIntegral.integral_const_mul] at step1
  -- extend to `[−N, N]`
  set N := ⌈2 * X⌉₊ with hNdef
  have hN2X : 2 * X ≤ N := Nat.le_ceil _
  have hN4 : 4 ≤ N := by
    have : (4 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hNX : (N : ℝ) ≤ 3 * X := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * X by linarith)
    linarith
  have step2 : ∫ y in X..2 * X, Z y ≤ ∫ y in (-(N : ℝ))..(N : ℝ), Z y :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) hN2X
      (Filter.Eventually.of_forall fun y => by positivity) (hZc.intervalIntegrable _ _)
  have step3 := hmom hN4
  -- arithmetic
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : Real.log N ≤ Real.log 3 + Real.log X := by
    rw [← Real.log_mul (by norm_num) hX0.ne']
    exact Real.log_le_log (by linarith) hNX
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hlogX : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hlog2 := Real.log_two_gt_d9
  have hL : 1 + Real.log N ≤ 6 * Real.log X := by
    norm_num at hlog2; linarith
  have hL0 : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  have hL4 : (1 + Real.log N) ^ 4 ≤ (6 * Real.log X) ^ 4 := pow_le_pow_left₀ hL0 hL 4
  have hmomX : ∫ y in (-(N : ℝ))..(N : ℝ), Z y ≤ D * (3 * X) * (6 * Real.log X) ^ 4 := by
    refine step3.trans ?_
    have := mul_le_mul hNX hL4 (pow_nonneg hL0 4) (by linarith)
    have hD' := mul_le_mul_of_nonneg_left this hD
    linarith [show D * N * (1 + Real.log N) ^ 4 = D * (N * (1 + Real.log N) ^ 4) by ring,
      show D * (3 * X) * (6 * Real.log X) ^ 4 = D * (3 * X * (6 * Real.log X) ^ 4) by ring]
  have hX7 : 0 ≤ K * X ^ 7 := by positivity
  rw [show X ^ (8 : ℝ) = X ^ (8 : ℕ) by rw [← Real.rpow_natCast]; norm_num]
  calc ∫ y in X..2 * X, Real.exp (Real.pi * y) * Xi y ^ 4
      ≤ K * X ^ 7 * ∫ y in X..2 * X, Z y := step1
    _ ≤ K * X ^ 7 * (D * (3 * X) * (6 * Real.log X) ^ 4) :=
        mul_le_mul_of_nonneg_left (step2.trans hmomX) hX7
    _ = K * D * 3 * 6 ^ 4 * X ^ 8 * Real.log X ^ 4 := by ring

end

end RHTower
