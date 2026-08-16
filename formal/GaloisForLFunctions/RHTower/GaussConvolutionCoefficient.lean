import GaloisForLFunctions.RHTower.GaussQuasiInnerBlocks
import GaloisForLFunctions.RHTower.GaussAmplitudeClass
import GaloisForLFunctions.HTGeometry.FourierMultiplierTruncation
import GaloisForLFunctions.HTGeometry.PiecewiseExponentialFourier
import GaloisForLFunctions.HTGeometry.IntegerPowerSeriesBounds

/-!
# Fourier coefficients of the reciprocal-square multiplier applied to a general amplitude

Multiplication by a bounded real symbol on the circle mixes frequencies by the convolution law:
the `j`-th coefficient of `c·w` is `∑_l conj(ĉ(l-j))·ŵ(l)`, an absolutely convergent series when
the symbol's coefficients decay harmonically.  This is Parseval for the vector `c·e_j` against
`w`, using that a real symbol is self-adjoint.

For the reciprocal square of the prime scale the symbol is a single-piece exponential, so its
coefficients are bounded by `2/(1+|x|)` and the convolution bound applies with constant `2`.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions

noncomputable section

/-! ## The kernel decay of the reciprocal square -/

theorem gaussPrimeScaleInvSqCircle_conj (p : ℝ) (z : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (gaussPrimeScaleInvSqCircle p z) = gaussPrimeScaleInvSqCircle p z := by
  have hval : gaussPrimeScaleInvSqCircle p z =
      ((gaussPrimeScaleInvSq p
        ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) : ℝ) : ℂ) := rfl
  rw [hval, Complex.conj_ofReal]

/-- The reciprocal square of the prime scale is a single-piece exponential. -/
theorem isExpPiecewise_gaussPrimeScaleInvSqCircle {p : ℝ} (hp : 1 < p) :
    IsExpPiecewise (Real.log p) 1 (fun i => if i = 0 then 0 else 1)
      (fun _ => ((p⁻¹ : ℝ) : ℂ)) (gaussPrimeScaleInvSqCircle p) where
  base := by norm_num
  top := by norm_num
  mono := by intro i hi; interval_cases i; norm_num
  nonneg := by intro i hi; interval_cases i; norm_num
  le_one := by intro i hi; interval_cases i; norm_num
  eq := by
    intro i hi x hx
    interval_cases i
    norm_num at hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have hval : gaussPrimeScaleInvSqCircle p ((x : ℝ) : AddCircle (1 : ℝ))
        = (gaussPrimeScaleInvSq p x : ℂ) :=
      AddCircle.liftIoc_coe_apply (by simpa using And.intro hx0 hx1.le)
    rw [hval, gaussPrimeScaleInvSq_eq_expPiece (by linarith : (0 : ℝ) < p) x]

/-- **Kernel decay.**  The Fourier coefficients of the reciprocal square are bounded by
`2/(1+|x|)`. -/
theorem norm_fourierCoeff_gaussPrimeScaleInvSqCircle_le {p : ℝ} (hp : 1 < p) (x : ℤ) :
    ‖fourierCoeff (gaussPrimeScaleInvSqCircle p) x‖ ≤ 2 / (1 + (x.natAbs : ℝ)) := by
  have hppos : (0 : ℝ) < p := by linarith
  have hM : ∀ i : ℕ, ‖((p⁻¹ : ℝ) : ℂ)‖ ≤ p⁻¹ := by
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hbound := norm_fourierCoeff_of_isExpPiecewise
    (isExpPiecewise_gaussPrimeScaleInvSqCircle hp) (by positivity) hM x
  refine hbound.trans (le_of_eq ?_)
  have habs : |Real.log p| = Real.log p := abs_of_pos (Real.log_pos hp)
  have hexp : Real.exp (Real.log p) = p := Real.exp_log hppos
  rw [habs, hexp]
  have hval : ((1 : ℕ) : ℝ) * (p⁻¹ * (2 * p)) = 2 := by
    push_cast
    field_simp
  rw [hval]

/-! ## The convolution law for a bounded real symbol -/

variable {c : AddCircle (1 : ℝ) → ℂ}

/-- **Parseval convolution law.**  For a bounded real symbol, the coefficient of the multiplied
vector is the absolutely convergent convolution of the symbol coefficients with the amplitude
coefficients. -/
theorem hasSum_fourierCoeff_lpBoundedMulCLM (hc : Measurable c) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖c x‖ ≤ C) (hreal : ∀ x, starRingEnd ℂ (c x) = c x)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    HasSum (fun l : ℤ => starRingEnd ℂ (fourierCoeff c (l - j)) *
        fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l)
      (fourierCoeff ((MeasureTheory.lpBoundedMulCLM (p := 2)
        (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC w : AddCircle (1 : ℝ) → ℂ)) j) := by
  have hinner : fourierCoeff ((MeasureTheory.lpBoundedMulCLM (p := 2)
      (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC w : AddCircle (1 : ℝ) → ℂ)) j
      = inner ℂ (MeasureTheory.lpBoundedMulCLM (p := 2)
          (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC
            (fourierLp 2 j)) w := by
    rw [← GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff,
      MeasureTheory.lpBoundedMulCLM_inner_real hc hC0 hC hreal]
  have hexpand := HilbertBasis.hasSum_inner_mul_inner (fourierBasis (T := (1 : ℝ)))
    (MeasureTheory.lpBoundedMulCLM (p := 2)
      (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC (fourierLp 2 j)) w
  rw [← hinner] at hexpand
  refine hexpand.congr_fun fun l => ?_
  congr 1
  · rw [← inner_conj_symm]
    congr 1
    have hbl : ((fourierBasis (T := (1 : ℝ))) l : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
        = fourierLp 2 l := by rw [coe_fourierBasis]
    rw [hbl, GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff,
      GaloisForLFunctions.fourierCoeff_lpBoundedMulCLM_fourierLp hc hC0 hC j l]
  · have hbl : ((fourierBasis (T := (1 : ℝ))) l : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
        = fourierLp 2 l := by rw [coe_fourierBasis]
    rw [hbl, GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff]

/-! ## Summability of the convolution majorant -/

/-- The amplitude coefficients are square-summable. -/
theorem summable_sq_fourierCoeff (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    Summable (fun l : ℤ => ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2) := by
  have hmem := lp.memℓp ((fourierBasis (T := (1 : ℝ))).repr w)
  have hs := hmem.summable (p := 2) (by norm_num)
  simp only [ENNReal.toReal_ofNat] at hs
  have hcast : ∀ l : ℤ, ‖((fourierBasis (T := (1 : ℝ))).repr w : ℤ → ℂ) l‖ ^ (2 : ℝ)
      = ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2 := by
    intro l
    rw [fourierBasis_repr, ← Real.rpow_natCast (‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) 2]
    norm_num
  exact hs.congr hcast

/-- The shifted harmonic kernel is square-summable. -/
theorem summable_sq_harmonicKernel (A : ℝ) (j : ℤ) :
    Summable (fun l : ℤ => (A / (1 + ((l - j).natAbs : ℝ))) ^ 2) := by
  have hbase : Summable (fun x : ℤ => (A / (1 + (x.natAbs : ℝ))) ^ 2) := by
    have hpow := summable_one_div_one_add_abs_rpow (s := 2) (by norm_num)
    have hsq : Summable (fun x : ℤ => A ^ 2 * (1 / (1 + |(x : ℝ)|) ^ (2 : ℝ))) :=
      hpow.mul_left _
    refine hsq.congr fun x => ?_
    have habs : |(x : ℝ)| = (x.natAbs : ℝ) := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have hrpow : (1 + |(x : ℝ)|) ^ (2 : ℝ) = (1 + |(x : ℝ)|) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast (1 + |(x : ℝ)|) 2]
      norm_num
    rw [hrpow, habs, div_pow]
    ring
  have hshift := (Equiv.subRight j).summable_iff
    (f := fun x : ℤ => (A / (1 + (x.natAbs : ℝ))) ^ 2)
  exact hshift.mpr hbase

/-- Summability of the convolution majorant: harmonic kernel times amplitude coefficients. -/
theorem summable_harmonicKernel_mul_fourierCoeff {κ : ℤ → ℝ} {A : ℝ}
    (hκ : ∀ x : ℤ, 0 ≤ κ x) (hκA : ∀ x : ℤ, κ x ≤ A / (1 + (x.natAbs : ℝ)))
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    Summable (fun l : ℤ => κ (l - j) * ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) := by
  have hAnn : ∀ x : ℤ, 0 ≤ A / (1 + (x.natAbs : ℝ)) :=
    fun x => le_trans (hκ x) (hκA x)
  have hdom : Summable (fun l : ℤ =>
      ((A / (1 + ((l - j).natAbs : ℝ))) ^ 2 +
        ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ ^ 2) / 2) :=
    ((summable_sq_harmonicKernel A j).add (summable_sq_fourierCoeff w)).div_const 2
  refine Summable.of_nonneg_of_le
    (fun l => mul_nonneg (hκ _) (norm_nonneg _)) (fun l => ?_) hdom
  have hb := hκA (l - j)
  have hn : (0 : ℝ) ≤ ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ := norm_nonneg _
  have hprod : κ (l - j) * ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖
      ≤ (A / (1 + ((l - j).natAbs : ℝ))) * ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ :=
    mul_le_mul_of_nonneg_right hb hn
  refine hprod.trans ?_
  nlinarith [sq_nonneg ((A / (1 + ((l - j).natAbs : ℝ))) -
    ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖)]

/-! ## The convolution bound for a general symbol -/

/-- **Convolution bound.**  For a bounded real symbol whose Fourier coefficients decay
harmonically with constant `A`, the coefficient of the multiplied vector is dominated by the
convolution of the kernel `A/(1+|x|)` with the amplitude coefficients. -/
theorem norm_fourierCoeff_lpBoundedMulCLM_le {c : AddCircle (1 : ℝ) → ℂ} (hc : Measurable c)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖c x‖ ≤ C) (hreal : ∀ x, starRingEnd ℂ (c x) = c x)
    {A : ℝ} (hA : ∀ x : ℤ, ‖fourierCoeff c x‖ ≤ A / (1 + (x.natAbs : ℝ)))
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    ‖fourierCoeff ((MeasureTheory.lpBoundedMulCLM (p := 2)
        (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC w : AddCircle (1 : ℝ) → ℂ)) j‖
      ≤ ∑' l : ℤ, A / (1 + ((l - j).natAbs : ℝ)) *
          ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ := by
  have hA0 : 0 ≤ A := by
    have h0 := hA 0
    simp only [Int.natAbs_zero, Nat.cast_zero, add_zero, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hsum := hasSum_fourierCoeff_lpBoundedMulCLM hc hC0 hC hreal w j
  have hmaj : Summable (fun l : ℤ =>
      ‖starRingEnd ℂ (fourierCoeff c (l - j)) *
        fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) := by
    have hbase := summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => ‖fourierCoeff c x‖) (A := A) (fun x => norm_nonneg _) hA w j
    refine hbase.congr fun l => ?_
    rw [norm_mul, RCLike.norm_conj]
  have heq : fourierCoeff ((MeasureTheory.lpBoundedMulCLM (p := 2)
      (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) hc hC0 hC w : AddCircle (1 : ℝ) → ℂ)) j
      = ∑' l : ℤ, starRingEnd ℂ (fourierCoeff c (l - j)) *
          fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l := hsum.tsum_eq.symm
  rw [heq]
  refine (norm_tsum_le_tsum_norm hmaj).trans ?_
  have hterm : Summable (fun l : ℤ => A / (1 + ((l - j).natAbs : ℝ)) *
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) :=
    summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => A / (1 + (x.natAbs : ℝ))) (A := A)
      (fun x => by positivity) (fun x => le_refl _) w j
  refine hmaj.tsum_le_tsum (fun l => ?_) hterm
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_right (hA (l - j)) (norm_nonneg _)

/-! ## The convolution bound for the reciprocal-square block -/

/-- **Convolution bound.**  The coefficient of `B⁻² w` is dominated by the convolution of the
kernel `2/(1+|x|)` with the amplitude coefficients. -/
theorem norm_fourierCoeff_gaussPrimeScaleInvSqBlock_le {p : ℝ} (hp : 1 < p)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    ‖fourierCoeff ((gaussPrimeScaleInvSqBlock hp w : AddCircle (1 : ℝ) → ℂ)) j‖
      ≤ ∑' l : ℤ, 2 / (1 + ((l - j).natAbs : ℝ)) *
          ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ := by
  have hsum := hasSum_fourierCoeff_lpBoundedMulCLM
    (measurable_gaussPrimeScaleInvSqCircle p) zero_le_one
    (norm_gaussPrimeScaleInvSqCircle_le hp) (gaussPrimeScaleInvSqCircle_conj p) w j
  have hmaj : Summable (fun l : ℤ =>
      ‖starRingEnd ℂ (fourierCoeff (gaussPrimeScaleInvSqCircle p) (l - j)) *
        fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) := by
    have hbase := summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => ‖fourierCoeff (gaussPrimeScaleInvSqCircle p) x‖) (A := 2)
      (fun x => norm_nonneg _)
      (fun x => norm_fourierCoeff_gaussPrimeScaleInvSqCircle_le hp x) w j
    refine hbase.congr fun l => ?_
    rw [norm_mul, RCLike.norm_conj]
  have heq : fourierCoeff ((gaussPrimeScaleInvSqBlock hp w : AddCircle (1 : ℝ) → ℂ)) j
      = ∑' l : ℤ, starRingEnd ℂ (fourierCoeff (gaussPrimeScaleInvSqCircle p) (l - j)) *
          fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l := hsum.tsum_eq.symm
  rw [heq]
  refine (norm_tsum_le_tsum_norm hmaj).trans ?_
  have hterm : Summable (fun l : ℤ => 2 / (1 + ((l - j).natAbs : ℝ)) *
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) :=
    summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => 2 / (1 + (x.natAbs : ℝ))) (A := 2)
      (fun x => by positivity) (fun x => le_refl _) w j
  refine hmaj.tsum_le_tsum (fun l => ?_) hterm
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_right
    (norm_fourierCoeff_gaussPrimeScaleInvSqCircle_le hp (l - j)) (norm_nonneg _)

end

end RHTower
