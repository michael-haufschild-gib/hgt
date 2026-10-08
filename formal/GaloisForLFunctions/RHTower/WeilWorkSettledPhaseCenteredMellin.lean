import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCenteredConvolution
import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianMellin
import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianShift
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay
import GaloisForLFunctions.HTGeometry.PolynomialExponentialDomination

/-!
# Gaussian Mellin cancellation for the actual pole-centered square

Subtracting the actual zeta residue removes the pole before squaring. Gamma
strip decay then permits every fixed Mellin line strictly right of one half.
The estimates concern signed arithmetic sums, not positive boundary energy.
-/

open Complex Set Filter MeasureTheory Topology
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSpectral GaussZeroSum
open GaloisForLFunctions.HTGeometry
variable {lam : ℕ → ℝ}

def centeredSquareCoeff (hW : WeilPositiveFull lam) : ℕ → ℂ :=
  LSeries.convolution (quantizationCenteredCoeff hW) (quantizationCenteredCoeff hW)

@[simp] theorem centeredSquareCoeff_zero (hW : WeilPositiveFull lam) :
    centeredSquareCoeff hW 0 = 0 := by simp [centeredSquareCoeff]

theorem centeredSquareCoeff_summable (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (centeredSquareCoeff hW) s :=
  (quantizationCenteredCoeff_summable hW hs).convolution
    (quantizationCenteredCoeff_summable hW hs)

theorem centeredSquareCoeff_LSeries (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (centeredSquareCoeff hW) s = quantizationCenteredProdF hW s ^ 2 := by
  rw [centeredSquareCoeff, LSeries_convolution'
    (quantizationCenteredCoeff_summable hW hs) (quantizationCenteredCoeff_summable hW hs),
    quantizationCenteredCoeff_LSeries hW hs, pow_two]

def centeredMellinProfile (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  quantizationGaussianMellinKernel s * quantizationCenteredProdF hW s ^ 2

theorem differentiableAt_centeredMellinProfile (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (centeredMellinProfile hW) s := by
  have hG : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hr := congrArg Complex.re hm
    simp at hr
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hH := (differentiableOn_quantizationCenteredProdF hW).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  exact ((hG.comp s (differentiableAt_id.div_const 2)).div_const 2).mul (hH.pow 2)

/-- Uniform tail control; the filled center creates no exception at `s=1`. -/
theorem exists_centeredMellinProfile_decay (hW : WeilPositiveFull lam) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 3 / 2 → 2 ≤ |s.im| →
      ‖centeredMellinProfile hW s‖ ≤ D * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨A, hA, hH⟩ := exists_quantizationCenteredProdF_tail hW
  obtain ⟨C, N, hC, hG⟩ := exists_sharp_bound_norm_Gamma_strip (1 / 4) (3 / 4)
  let D : ℝ := 4 * C * A ^ 2
  refine ⟨D * Real.exp (Real.pi / 4) *
    (((N + 2 + 2).factorial : ℝ) / (Real.pi / 4) ^ (N + 2 + 2)),
    by dsimp [D]; positivity, fun s hs hs' ht => ?_⟩
  have hhalf : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
  have hg := hG (s / 2) (by simp; linarith) (by simp; linarith)
    (by rw [hhalf]; linarith)
  rw [hhalf] at hg
  have he : -(Real.pi * (|s.im| / 2) / 2) = -(Real.pi / 4 * |s.im|) := by ring
  rw [he] at hg
  have hg' : ‖Complex.Gamma (s / 2)‖ ≤
      C * |s.im| ^ N * Real.exp (-(Real.pi / 4 * |s.im|)) := by
    apply hg.trans
    gcongr
    nlinarith [abs_nonneg s.im]
  have hh : ‖quantizationCenteredProdF hW s‖ ≤ A * (1 + |s.im|) := by
    simpa only [Complex.re_add_im] using hH s.re s.im hs hs' ht
  have hk : ‖quantizationGaussianMellinKernel s‖ ≤ ‖Complex.Gamma (s / 2)‖ := by
    rw [quantizationGaussianMellinKernel, norm_div, norm_ofNat]
    exact div_le_self (norm_nonneg _) (by norm_num)
  have hb : ‖centeredMellinProfile hW s‖ ≤
      D * |s.im| ^ (N + 2) * Real.exp (-(Real.pi / 4 * |s.im|)) := by
    rw [centeredMellinProfile, norm_mul, norm_pow]
    calc
      _ ≤ (C * |s.im| ^ N * Real.exp (-(Real.pi / 4 * |s.im|))) *
          (A * (2 * |s.im|)) ^ 2 := by
        gcongr
        · exact hk.trans hg'
        · exact hh.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
      _ = _ := by dsimp [D]; rw [pow_add]; ring
  exact hb.trans (polyExp_le_inv_one_add_sq (by dsimp [D]; positivity)
    (by positivity : 0 < Real.pi / 4) (N + 2) s.im)

theorem integrable_centeredMellinProfile (hW : WeilPositiveFull lam)
    {c : ℝ} (hc : 1 / 2 < c) (hc' : c ≤ 3 / 2) :
    Integrable fun t : ℝ => centeredMellinProfile hW ((c : ℂ) + t * I) := by
  obtain ⟨D, _, hb⟩ := exists_centeredMellinProfile_decay hW
  refine integrable_line_of_bound (T₀ := 2) (C := D)
    (fun t => (differentiableAt_centeredMellinProfile hW (by simpa using hc)).continuousAt)
    (fun t ht => ?_)
  simpa using hb ((c : ℂ) + t * I) (by simpa using hc) (by simpa using hc')
    (by simpa using ht)

private theorem norm_cpow_neg_strip {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs' : s.re ≤ 3 / 2) :
    ‖(x : ℂ) ^ (-s)‖ ≤ x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 / 2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, neg_re]
  rcases le_or_gt x 1 with hx1 | hx1
  · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith : -(3 / 2 : ℝ) ≤ -s.re)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith : -s.re ≤ -(1 / 2 : ℝ))).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))

/-- The centered inverse Mellin contour crosses one with zero residue. -/
theorem centeredMellin_shift (hW : WeilPositiveFull lam) {c x : ℝ}
    (hc : 1 / 2 < c) (hc' : c < 1) (hx : 0 < x) :
    mellinInv (3 / 2) (centeredMellinProfile hW) x =
      mellinInv c (centeredMellinProfile hW) x := by
  let F : ℂ → ℂ := fun s => (x : ℂ) ^ (-s) * centeredMellinProfile hW s
  have hd (s : ℂ) (hs : 1 / 2 < s.re) : DifferentiableAt ℂ F s :=
    ((differentiableAt_id.neg).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).mul
      (differentiableAt_centeredMellinProfile hW hs)
  have hres : Tendsto (fun s : ℂ => (s - 1) * F s) (𝓝[≠] 1) (𝓝 0) := by
    have hm : ContinuousAt (fun s : ℂ => (s - 1) * F s) 1 :=
      (continuousAt_id.sub continuousAt_const).mul (hd 1 (by norm_num)).continuousAt
    have hh := hm.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    simpa using hh
  obtain ⟨D, hD, hb⟩ := exists_centeredMellinProfile_decay hW
  have he := integral_line_sub_integral_line_eq (F := F) (a := c) (b := 3 / 2)
    (p := 1) (by simpa using hc') (by norm_num)
    (fun s hs _ _ => hd s (lt_of_lt_of_le hc hs)) hres
    (T₀ := 2) (C := (x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 / 2 : ℝ))) * D)
    (fun s hs hs' ht => by
      dsimp only [F]
      rw [norm_mul]
      calc
        _ ≤ (x ^ (-(1 / 2 : ℝ)) + x ^ (-(3 / 2 : ℝ))) *
            (D * (1 + s.im ^ 2)⁻¹) := by
          gcongr
          · exact norm_cpow_neg_strip hx (by linarith) hs'
          · exact hb s (by linarith) hs' ht
        _ = _ := by ring)
  rw [mul_zero, sub_eq_zero] at he
  unfold mellinInv
  exact congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z) he

/-- Exact Gaussian inversion of the actual centered convolution. -/
theorem centeredGaussianSum_eq_mellinInv (hW : WeilPositiveFull lam) {T : ℝ}
    (hT : 0 < T) :
    (∑' n : ℕ, centeredSquareCoeff hW n * (gaussW T n : ℂ)) =
      mellinInv (3 / 2) (centeredMellinProfile hW) (2 * Real.pi / T) := by
  have hx : 0 < 2 * Real.pi / T := by positivity
  have hs := (centeredSquareCoeff_summable hW (s := (3 / 2 : ℝ)) (by norm_num)).norm
  have hsum : Summable fun n : ℕ => ‖centeredSquareCoeff hW n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    refine hs.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.norm_term_eq, if_neg hn.ne', ofReal_re,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have he := quantizationGaussian_mellinInv_LSeries (a := centeredSquareCoeff hW)
    (c := 3 / 2) (by norm_num) hx (centeredSquareCoeff_zero hW) hsum
  have hw (n : ℕ) : Real.exp (-((n : ℝ) * (2 * Real.pi / T)) ^ 2) = gaussW T n := by
    unfold gaussW
    congr 1
    ring
  simp_rw [hw] at he
  rw [← he]
  unfold mellinInv
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun t => by
    dsimp only [centeredMellinProfile]
    rw [centeredSquareCoeff_LSeries hW (by norm_num)])

/-- Signed Gaussian sums have every fixed power strictly above one half. -/
theorem exists_centeredGaussianSum_le (hW : WeilPositiveFull lam) {c : ℝ}
    (hc : 1 / 2 < c) (hc' : c < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ‖∑' n : ℕ, centeredSquareCoeff hW n * (gaussW T n : ℂ)‖ ≤ C * T ^ c := by
  let J : ℝ := ∫ t : ℝ, ‖centeredMellinProfile hW ((c : ℂ) + t * I)‖
  have hJ : 0 ≤ J := integral_nonneg fun _ => norm_nonneg _
  refine ⟨(1 / (2 * Real.pi)) * (2 * Real.pi) ^ (-c) * J, by positivity, fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hx : 0 < 2 * Real.pi / T := by positivity
  rw [centeredGaussianSum_eq_mellinInv hW hT0, centeredMellin_shift hW hc hc' hx,
    mellinInv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  have hn (t : ℝ) : ‖((2 * Real.pi / T : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) *
      centeredMellinProfile hW ((c : ℂ) + t * I)‖ =
      (2 * Real.pi / T) ^ (-c) * ‖centeredMellinProfile hW ((c : ℂ) + t * I)‖ := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  calc
    _ ≤ (1 / (2 * Real.pi)) * ((2 * Real.pi / T) ^ (-c) * J) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_integral_le_integral_norm _).trans_eq
      change (∫ t : ℝ, ‖((2 * Real.pi / T : ℝ) : ℂ) ^ (-((c : ℂ) + t * I)) *
        centeredMellinProfile hW ((c : ℂ) + t * I)‖) = _
      simp_rw [hn]
      exact integral_const_mul _ _
    _ = _ := by
      rw [Real.div_rpow (by positivity : 0 ≤ 2 * Real.pi) hT0.le,
        Real.rpow_neg hT0.le, div_inv_eq_mul]
      ring

end RHTower.WeilWorkSettledPhase
