import GaloisForLFunctions.HTGeometry.AbstractSpectralComovingExtinction

/-!
# Exponential extinction inside the widening mass cone

The co-moving trace is not merely `C₀`.  Joint mass-height geometry gives a uniform exponential
rate.  If `a ≥ 2`, `|u| ≤ a`, and `σ > 1/2`, set

`κ(σ) = 2σ/3 - 3/16 > 0`.

For an original point `R+iJ` and its mass image `M+iK`, the principal root satisfies

`2(a+R) ≤ 3M`.

Charge conservation and `|J|<1/2` then give

`a|K| ≤ 3(a+R)/16`.

Thus every massive term is bounded by `exp (-κa) exp (-κR)`, and summation yields exponential
co-moving extinction for every admissible spectral family.  This is substantially stronger than
the earlier Tannery limit and remains positive uniformly as `σ ↓ 1/2`.
-/

open Complex

namespace HTGeometry

noncomputable section

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

/-- Universal rational decay rate exposed by joint mass-height geometry. -/
def comovingExponentialRate (σ : ℝ) : ℝ := 2 * σ / 3 - 3 / 16

theorem comovingExponentialRate_pos {σ : ℝ} (hσ : 1 / 2 < σ) :
    0 < comovingExponentialRate σ := by
  unfold comovingExponentialRate
  linarith

/-- The universal rate stays uniformly separated from zero even as `σ ↓ 1/2`. -/
theorem seven_div_fortyEight_lt_comovingExponentialRate
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    7 / 48 < comovingExponentialRate σ := by
  unfold comovingExponentialRate
  linarith

/-- **Joint mass-height lower bound.**  At aperture at least `2`, the mass root controls the sum of
the aperture and original spectral height. -/
theorem two_mul_mass_add_re_le_three_mul_mass_re
    {a : ℝ} (ha : 2 ≤ a) (i : ι) :
    2 * (a + (F.pt i).re) ≤
      3 * ((F.mass (show 1 / 2 ≤ a by linarith)).pt i).re := by
  let haHalf : 1 / 2 ≤ a := by linarith
  have hJ := F.abs_im_lt i
  have hJ2 : (F.pt i).im ^ (2 : ℕ) < 1 / 4 := by
    nlinarith [sq_abs (F.pt i).im, abs_nonneg ((F.pt i).im)]
  have hM2raw := re_le_sq_csqrtRe (F.massArg_re_pos haHalf i)
  rw [F.massArg_re] at hM2raw
  have hM2 :
      (F.pt i).re ^ (2 : ℕ) - (F.pt i).im ^ (2 : ℕ) + a ^ (2 : ℕ) ≤
        ((F.mass haHalf).pt i).re ^ (2 : ℕ) := by
    simpa only [F.mass_pt, csqrt_re] using hM2raw
  have hM0 : 0 ≤ ((F.mass haHalf).pt i).re := by
    rw [F.mass_pt, csqrt_re]
    exact csqrtRe_nonneg (F.massArg a i)
  have hR := F.re_pos i
  have hquad :
      (2 * (a + (F.pt i).re)) ^ (2 : ℕ) <
        (3 * ((F.mass haHalf).pt i).re) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (5 * (F.pt i).re - 4 * a)]
  have hfinal :
      2 * (a + (F.pt i).re) ≤ 3 * ((F.mass haHalf).pt i).re := by
    nlinarith
  simpa only using hfinal

/-- **Sharp rational transverse bound used by exponential extinction.**  The vertical mass
displacement consumes at most `3/16` of the joint aperture-height scale. -/
theorem sixteen_mul_mass_mul_abs_im_le_three_mul_add_re
    {a : ℝ} (ha : 2 ≤ a) (i : ι) :
    16 * a * |((F.mass (show 1 / 2 ≤ a by linarith)).pt i).im| ≤
      3 * (a + (F.pt i).re) := by
  let haHalf : 1 / 2 ≤ a := by linarith
  let M : ℝ := ((F.mass haHalf).pt i).re
  let K : ℝ := ((F.mass haHalf).pt i).im
  let R : ℝ := (F.pt i).re
  let J : ℝ := (F.pt i).im
  have hR : 0 < R := F.re_pos i
  have hM : 0 < M := by
    have hMR : R < M := by
      dsimp only [R, M]
      simpa only [F.mass_pt, csqrt_re] using F.re_lt_csqrtRe_massArg haHalf i
    linarith
  have hsum : 0 < a + R := by linarith
  have hroot : 2 * (a + R) ≤ 3 * M := by
    dsimp only [R, M]
    simpa only using F.two_mul_mass_add_re_le_three_mul_mass_re ha i
  have hprod := F.re_mul_im_mass haHalf i
  have hprodAbs : M * |K| = R * |J| := by
    have habs := congrArg abs hprod
    simpa only [M, K, R, J, abs_mul, abs_of_pos hM, abs_of_pos hR] using habs
  have hJ : |J| ≤ 1 / 2 := (F.abs_im_lt i).le
  have hMK : M * |K| ≤ R / 2 := by
    rw [hprodAbs]
    nlinarith [mul_le_mul_of_nonneg_left hJ hR.le]
  have hK : 4 * (a + R) * |K| ≤ 3 * R := by
    have hscale := mul_le_mul_of_nonneg_right hroot (abs_nonneg K)
    nlinarith
  have hamgm : 4 * a * R ≤ (a + R) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (a - R)]
  have hscale :
      (4 * a) * (4 * (a + R) * |K|) ≤ (4 * a) * (3 * R) :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  have hmul : (a + R) * (16 * a * |K|) ≤ (a + R) * (3 * (a + R)) := by
    nlinarith
  have hfinal : 16 * a * |K| ≤ 3 * (a + R) :=
    le_of_mul_le_mul_left hmul hsum
  simpa only [K, R] using hfinal

/-- **Pointwise exponential cone estimate.**  Both aperture and spectral height receive the same
strictly positive decay rate. -/
theorem norm_mass_term_le_comoving_exponential
    {a σ u : ℝ} (ha : 2 ≤ a) (hu : |u| ≤ a) (hσ : 1 / 2 < σ) (i : ι) :
    ‖(F.mass (show 1 / 2 ≤ a by linarith)).term ((σ : ℂ) + u * I) i‖ ≤
      Real.exp (-(comovingExponentialRate σ) * a) *
        F.weight (comovingExponentialRate σ) i := by
  let haHalf : 1 / 2 ≤ a := by linarith
  let κ : ℝ := comovingExponentialRate σ
  let M : ℝ := ((F.mass haHalf).pt i).re
  let K : ℝ := ((F.mass haHalf).pt i).im
  let R : ℝ := (F.pt i).re
  have hκ : 0 < κ := comovingExponentialRate_pos hσ
  have hM : 2 * (a + R) ≤ 3 * M := by
    dsimp only [M, R]
    simpa only using F.two_mul_mass_add_re_le_three_mul_mass_re ha i
  have hK : 16 * a * |K| ≤ 3 * (a + R) := by
    dsimp only [K, R]
    simpa only using F.sixteen_mul_mass_mul_abs_im_le_three_mul_add_re ha i
  have huK : u * K ≤ 3 / 16 * (a + R) := by
    calc
      u * K ≤ |u * K| := le_abs_self _
      _ = |u| * |K| := abs_mul _ _
      _ ≤ a * |K| := mul_le_mul_of_nonneg_right hu (abs_nonneg _)
      _ ≤ 3 / 16 * (a + R) := by nlinarith
  have hσM : 2 * σ / 3 * (a + R) ≤ σ * M := by
    have hscale : σ * (2 * (a + R)) ≤ σ * (3 * M) :=
      mul_le_mul_of_nonneg_left hM (by linarith)
    nlinarith
  have hexponent : -σ * M + u * K ≤ -κ * a - κ * R := by
    dsimp only [κ, comovingExponentialRate]
    nlinarith
  rw [(F.mass haHalf).norm_term, weight]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (((σ : ℂ) + u * I)).re = σ := by simp [Complex.mul_re]
  have him : (((σ : ℂ) + u * I)).im = u := by simp [Complex.mul_im]
  rw [hre, him]
  dsimp only [M, K, R] at hexponent
  linarith

/-- **Universal exponential co-moving extinction.**  Unlike the earlier qualitative limit, this
is a pointwise all-height bound with an explicit positive rate. -/
theorem norm_mass_traceC_le_comoving_exponential
    {a σ u : ℝ} (ha : 2 ≤ a) (hu : |u| ≤ a) (hσ : 1 / 2 < σ) :
    ‖(F.mass (show 1 / 2 ≤ a by linarith)).traceC ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-(comovingExponentialRate σ) * a) *
        F.traceReal (comovingExponentialRate σ) := by
  let haHalf : 1 / 2 ≤ a := by linarith
  let κ : ℝ := comovingExponentialRate σ
  have hκ : 0 < κ := comovingExponentialRate_pos hσ
  have hτ : 0 < (((σ : ℂ) + u * I)).re := by
    simpa [Complex.mul_re] using (show 0 < σ by linarith)
  refine le_trans
    (norm_tsum_le_tsum_norm ((F.mass haHalf).summable_norm_term hτ)) ?_
  rw [traceReal, ← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun i => by
      simpa only [κ] using F.norm_mass_term_le_comoving_exponential ha hu hσ i)
    ((F.mass haHalf).summable_norm_term hτ)
    ((F.summable_weight hκ).mul_left _)

end AbstractSpectralFamily

end


end HTGeometry
