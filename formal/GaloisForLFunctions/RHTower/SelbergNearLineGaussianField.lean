import GaloisForLFunctions.RHTower.BarbanVehovMollifiedZetaTail
import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding
import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound

/-!
# The Gaussian-windowed pole-cleared mollified tail

With `Ψ_N` the Barban–Vehov mollifier and `P_N` its von Mangoldt head, the tail
`f_N = ζΨ_N − 1 − P_N` has a simple pole at `s = 1`. The field

`W_N(z) = ((z−1)ζ(z) Ψ_N(z) − (z−1)(1 + P_N(z)))/z = ((z−1)/z) f_N(z)`

is holomorphic on `Re z > 0` (`differentiableOn_nearLineField`), and on the strip
`1/4 ≤ Re z ≤ 3` it grows at most linearly, `‖W_N(z)‖ ≤ C N (1 + |Im z|)`
(`exists_norm_nearLineField_le`). Multiplying by the Gaussian `exp((z − iτ)²/H²)`, whose modulus is
`exp((σ² − (t−τ)²)/H²)` (`norm_nearLineGauss`), localises it to heights `|t − τ| ≲ H`.

The pole-clearing factor costs only constants: `|(z−1)/z| ≤ 1` on `Re z ≥ 1/2`, `≤ 5/3` on
`Re z ≥ 3/8`, and `|z/(z−1)|² ≤ 2` on `1/2 ≤ Re z ≤ 1`, `|Im z| ≥ 1`.
-/

noncomputable section

open Complex Set Metric

namespace RHTower

/-- The pole-cleared mollified tail `((z−1)/z)(ζΨ_N − 1 − P_N)`. -/
def nearLineField (N : ℕ) (z : ℂ) : ℂ :=
  (zetaEntire z * edPoly (hbCoeff N) (Finset.Icc 1 N) z -
    (z - 1) * (1 + edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) z)) / z

theorem nearLineField_eq {N : ℕ} {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    nearLineField N z = (z - 1) / z * hbMollifiedTail N z := by
  unfold nearLineField hbMollifiedTail
  rw [zetaEntire_eq hz1]
  field_simp
  ring

theorem differentiableOn_nearLineField (N : ℕ) :
    DifferentiableOn ℂ (nearLineField N) {z | 0 < z.re} := by
  intro z hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div _ differentiableAt_id hz0
  exact ((differentiable_zetaEntire z).mul (differentiable_edPoly _ hs z)).sub
    ((differentiableAt_id.sub_const 1).mul
      ((differentiableAt_const 1).add (differentiable_edPoly _ hs z)))

/-- The Gaussian window `exp((z − iτ)²/H²)`. -/
def nearLineGauss (H τ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((z - (τ : ℂ) * I) ^ 2 / (((H ^ 2 : ℝ)) : ℂ))

theorem differentiable_nearLineGauss (H τ : ℝ) : Differentiable ℂ (nearLineGauss H τ) := by
  unfold nearLineGauss
  fun_prop

theorem norm_nearLineGauss (H τ σ t : ℝ) :
    ‖nearLineGauss H τ ((σ : ℂ) + (t : ℂ) * I)‖ = Real.exp ((σ ^ 2 - (t - τ) ^ 2) / H ^ 2) := by
  unfold nearLineGauss
  rw [Complex.norm_exp, Complex.div_ofReal_re]
  congr 2
  simp only [sq, Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im]
  ring

/-- The windowed field `exp((z − iτ)²/H²) W_N(z)`. -/
def nearLineWindowField (N : ℕ) (H τ : ℝ) (z : ℂ) : ℂ :=
  nearLineGauss H τ z * nearLineField N z

theorem differentiableOn_nearLineWindowField (N : ℕ) (H τ : ℝ) :
    DifferentiableOn ℂ (nearLineWindowField N H τ) {z | 0 < z.re} :=
  (differentiable_nearLineGauss H τ).differentiableOn.mul (differentiableOn_nearLineField N)

/-- `|(z−1)/z| ≤ 1` on `Re z ≥ 1/2`. -/
theorem norm_sub_one_div_le_one {z : ℂ} (hz : 1 / 2 ≤ z.re) : ‖(z - 1) / z‖ ≤ 1 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz; linarith
  rw [norm_div, div_le_one (norm_pos_iff.mpr hz0)]
  have h1 : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have : ‖z - 1‖ ^ 2 ≤ ‖z‖ ^ 2 := by rw [h1, h2]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).mp this

/-- `|(z−1)/z|² ≤ 3` on `3/8 ≤ Re z ≤ 1/2`. -/
theorem norm_sub_one_div_sq_le_three {z : ℂ} (hz : 3 / 8 ≤ z.re) (hz' : z.re ≤ 1 / 2) :
    ‖(z - 1) / z‖ ^ 2 ≤ 3 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz; linarith
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [norm_div, div_pow, div_le_iff₀ (by positivity)]
  have h1 : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [h1, h2]
  nlinarith [sq_nonneg z.im]

/-- `|z/(z−1)|² ≤ 2` on `1/2 ≤ Re z ≤ 1`, `|Im z| ≥ 1`: the tail is controlled by the field. -/
theorem norm_hbMollifiedTail_sq_le_two_mul {N : ℕ} {z : ℂ} (hz : 1 / 2 ≤ z.re) (hz' : z.re ≤ 1)
    (him : 1 ≤ |z.im|) :
    ‖hbMollifiedTail N z‖ ^ 2 ≤ 2 * ‖nearLineField N z‖ ^ 2 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz; linarith
  have hz1 : z ≠ 1 := fun h => by simp [h] at him; linarith
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [nearLineField_eq hz0 hz1, norm_mul, mul_pow, norm_div]
  have h1 : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hpos1 : 0 < ‖z - 1‖ := norm_pos_iff.mpr hsub
  have hpos0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have him2 : 1 ≤ z.im ^ 2 := by
    have := sq_abs z.im
    nlinarith [abs_nonneg z.im]
  have hratio : ‖z‖ ^ 2 ≤ 2 * ‖z - 1‖ ^ 2 := by
    rw [h1, h2]
    nlinarith
  rw [div_pow]
  have hT := sq_nonneg ‖hbMollifiedTail N z‖
  rw [show 2 * (‖z - 1‖ ^ 2 / ‖z‖ ^ 2 * ‖hbMollifiedTail N z‖ ^ 2) =
      (2 * ‖z - 1‖ ^ 2) / ‖z‖ ^ 2 * ‖hbMollifiedTail N z‖ ^ 2 by ring]
  have hge : 1 ≤ (2 * ‖z - 1‖ ^ 2) / ‖z‖ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  nlinarith

/-- **Linear growth of the pole-cleared tail on the strip `1/4 ≤ Re z ≤ 3`.** -/
theorem exists_norm_nearLineField_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ z : ℂ, 1 / 4 ≤ z.re → z.re ≤ 3 →
      ‖nearLineField N z‖ ≤ C * N * (1 + |z.im|) := by
  set K : Set ℂ := (Set.Icc (1 / 4 : ℝ) 3) ×ℂ (Set.Icc (-2 : ℝ) 2) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨CZ, hCZ⟩ := hKc.exists_bound_of_continuousOn
    (differentiable_zetaEntire.continuous.continuousOn (s := K))
  set CZ' : ℝ := max CZ 0 with hCZ'
  refine ⟨max 16 (4 * (CZ' + 8)), by positivity, fun N hN z hz hz' => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hΨ := norm_edPoly_hbCoeff_le hN (s := z) (by linarith)
  have hP := norm_edPoly_hbVonMangoldtCoeff_le hN (s := z) (by linarith)
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz; linarith
  have hzn : 1 / 4 ≤ ‖z‖ := le_trans hz (Complex.re_le_norm z)
  have habs : 0 ≤ |z.im| := abs_nonneg _
  rcases le_or_gt 2 |z.im| with him | him
  · have hz1 : z ≠ 1 := fun h => by simp [h] at him; linarith
    rw [nearLineField_eq hz0 hz1, norm_mul]
    have hfac : ‖(z - 1) / z‖ ≤ 2 := by
      rw [norm_div, div_le_iff₀ (by linarith)]
      have h1 : ‖z - 1‖ ≤ ‖z‖ + 1 := by
        have := norm_sub_le z 1
        simpa using this
      have h2 : 2 ≤ ‖z‖ := le_trans him (Complex.abs_im_le_norm z)
      linarith
    have hζ := norm_riemannZeta_le_quarter hz him
    have hf : ‖hbMollifiedTail N z‖ ≤ 8 * N * (1 + |z.im|) := by
      unfold hbMollifiedTail
      calc ‖riemannZeta z * edPoly (hbCoeff N) (Finset.Icc 1 N) z - 1 -
            edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) z‖
          ≤ ‖riemannZeta z‖ * ‖edPoly (hbCoeff N) (Finset.Icc 1 N) z‖ + 1 +
            ‖edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) z‖ := by
            have h1 := norm_sub_le (riemannZeta z * edPoly (hbCoeff N) (Finset.Icc 1 N) z - 1)
              (edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) z)
            have h2 := norm_sub_le (riemannZeta z * edPoly (hbCoeff N) (Finset.Icc 1 N) z) 1
            rw [norm_mul, norm_one] at h2
            linarith
        _ ≤ (2 + 8 * |z.im|) * N + 1 + N := by
            have := mul_le_mul hζ hΨ (norm_nonneg _) (by positivity)
            linarith
        _ ≤ 8 * N * (1 + |z.im|) := by nlinarith
    calc ‖(z - 1) / z‖ * ‖hbMollifiedTail N z‖ ≤ 2 * (8 * N * (1 + |z.im|)) :=
          mul_le_mul hfac hf (norm_nonneg _) (by norm_num)
      _ = 16 * N * (1 + |z.im|) := by ring
      _ ≤ max 16 (4 * (CZ' + 8)) * N * (1 + |z.im|) := by
          gcongr
          exact le_max_left _ _
  · have hmem : z ∈ K := by
      rw [hK]
      refine ⟨⟨hz, hz'⟩, ?_⟩
      have := abs_lt.mp him
      exact ⟨by linarith, by linarith⟩
    have hZ : ‖zetaEntire z‖ ≤ CZ' := (hCZ z hmem).trans (le_max_left _ _)
    have hz1n : ‖z - 1‖ ≤ 4 := by
      have h := norm_le_abs_re_add_abs_im (z - 1)
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
      have : |z.re - 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    unfold nearLineField
    rw [norm_div, div_le_iff₀ (by linarith)]
    calc ‖zetaEntire z * edPoly (hbCoeff N) (Finset.Icc 1 N) z -
          (z - 1) * (1 + edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) z)‖
        ≤ ‖zetaEntire z‖ * ‖edPoly (hbCoeff N) (Finset.Icc 1 N) z‖ +
          ‖z - 1‖ * (1 + ‖edPoly (hbVonMangoldtCoeff N) (Finset.Icc 1 N) z‖) := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, norm_mul]
          gcongr
          exact (norm_add_le _ _).trans (by rw [norm_one])
      _ ≤ CZ' * N + 4 * (1 + N) := by
          have hCZ0 : 0 ≤ CZ' := le_max_right _ _
          have h1 := mul_le_mul hZ hΨ (norm_nonneg _) hCZ0
          have h2 := mul_le_mul hz1n (add_le_add_left hP 1) (by positivity) (by norm_num)
          linarith
      _ ≤ (CZ' + 8) * N := by nlinarith
      _ ≤ max 16 (4 * (CZ' + 8)) * N * (1 + |z.im|) * ‖z‖ := by
          have hmax : 4 * (CZ' + 8) ≤ max 16 (4 * (CZ' + 8)) := le_max_right _ _
          have hCZ0 : 0 ≤ CZ' := le_max_right _ _
          have hN0 : (0 : ℝ) ≤ N := by linarith
          have e1 : (CZ' + 8) * N = (4 * (CZ' + 8)) * N * 1 * (1 / 4) := by ring
          rw [e1]
          gcongr
          linarith

/-- The pole-cleared tail on the edge `Re z = 3` is at most `2/N`. -/
theorem norm_nearLineField_three_le {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    ‖nearLineField N ((3 : ℂ) + (t : ℂ) * I)‖ ≤ 2 / N := by
  set z : ℂ := (3 : ℂ) + (t : ℂ) * I with hzdef
  have hre : z.re = 3 := by simp [hzdef]
  have hz0 : z ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hz1 : z ≠ 1 := fun h => by rw [h] at hre; simp at hre
  rw [nearLineField_eq hz0 hz1, norm_mul]
  have h1 := norm_sub_one_div_le_one (z := z) (by rw [hre]; norm_num)
  have h2 := norm_hbMollifiedTail_le hN (s := z) (by rw [hre])
  calc ‖(z - 1) / z‖ * ‖hbMollifiedTail N z‖ ≤ 1 * (2 / N) :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 2 / N := one_mul _

end RHTower
