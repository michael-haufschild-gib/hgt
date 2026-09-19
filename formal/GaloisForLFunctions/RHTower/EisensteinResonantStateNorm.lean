import GaloisForLFunctions.RHTower.EisensteinLineRealness

/-!
# The truncated norm of a resonant state: the cutoff-exponent receiver

For `u ∈ Ω` with `Re u < 0` and `A(u) = Λ(1+2u) = 0` — in particular `u = ρ/2 − ½` for a zero `ρ`
of `Λ` in the strip with `Im ρ > 0`, where `E*(·, ρ/2)` is the resonant state of the scattering
pole — the Maass–Selberg relation gives the exact truncated `L²` norm

`∫_𝒟 ‖Λ^Y E_u‖² dμ = ‖B(u)‖² Y^{−2 Re u} / (−2 Re u)`, i.e. `‖Λ(ρ−1)‖² Y^{1−Re ρ} / (1 − Re ρ)`.

The sesquilinear norm is the bilinear pairing with `−conj u ∈ Ω` (conjugation and reflection
symmetry of the model).  The growth exponent `1 − Re ρ` of the truncated norm reads off the real
part of the zero: this is the exact cutoff-exponent receiver of the HB route, now certified.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Symmetries of the truncated model -/

theorem truncatedLineModel_conj (u : ℂ) (Y : ℝ) (z : ℍ) :
    (starRingEnd ℂ) (truncatedLineModel u Y z) = truncatedLineModel ((starRingEnd ℂ) u) Y z := by
  unfold truncatedLineModel eisensteinLineModel
  rw [map_sub, cuspLeg_conj u z.re z.im_pos]
  congr 1
  split_ifs
  · exact cuspConstantPart_conj u z.im_pos
  · simp

theorem truncatedLineModel_neg {u : ℂ} (hu : u.im ≠ 0) (Y : ℝ) (z : ℍ) :
    truncatedLineModel (-u) Y z = truncatedLineModel u Y z := by
  unfold truncatedLineModel eisensteinLineModel
  rw [d4BMCompletedEisensteinScalarCuspLeg_neg u hu]
  congr 1
  split_ifs
  · exact cuspConstantPart_neg hu z.im
  · rfl

/-- The functional equation of `Λ` off the real axis. -/
theorem reflectedCompletedLambda_one_sub_of_im {s : ℂ} (hs : s.im ≠ 0) :
    reflectedCompletedLambda (1 - s) = reflectedCompletedLambda s := by
  have hs' : (1 - s).im ≠ 0 := by simp [hs]
  have h0 : s ≠ 0 := by intro h; apply hs; rw [h]; simp
  have h0' : 1 - s ≠ 0 := by intro h; apply hs'; rw [h]; simp
  rw [reflectedCompletedLambda_eq_completed h0' (Gammaℝ_ne_zero_of_im_ne_zero hs'),
    reflectedCompletedLambda_eq_completed h0 (Gammaℝ_ne_zero_of_im_ne_zero hs),
    completedRiemannZeta_one_sub]

theorem neg_conj_mem_eisensteinLineDomain {u : ℂ} (hu : u ∈ eisensteinLineDomain) (hre : u.re < 1 / 2) :
    -(starRingEnd ℂ) u ∈ eisensteinLineDomain := by
  refine ⟨?_, ?_⟩
  · simp; linarith
  · simp; exact hu.2

/-- **The sesquilinear norm is the bilinear pairing with `−conj u`.** -/
theorem integral_norm_sq_eq_truncatedPairing {u : ℂ} (hu : u ∈ eisensteinLineDomain) (Y : ℝ) :
    ((∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ) =
      truncatedPairing Y u (-(starRingEnd ℂ) u) := by
  unfold truncatedPairing
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
  have him : ((starRingEnd ℂ) u).im ≠ 0 := by simp; exact hu.2.ne'
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, truncatedLineModel_conj,
    truncatedLineModel_neg him]

/-! ## Evaluation when `A(u) = 0` -/

theorem msA_neg_conj {u : ℂ} (hu : u.im ≠ 0) :
    msA (-(starRingEnd ℂ) u) = (starRingEnd ℂ) (msB u) := by
  unfold msA msB
  have hw : (2 * (starRingEnd ℂ) u).im ≠ 0 := by simp [hu]
  rw [← reflectedCompletedLambda_conj,
    show 1 + 2 * -(starRingEnd ℂ) u = 1 - 2 * (starRingEnd ℂ) u by ring,
    reflectedCompletedLambda_one_sub_of_im hw]
  congr 1
  rw [map_mul, map_ofNat]

theorem msB_neg_conj {u : ℂ} (hu : u.im ≠ 0) :
    msB (-(starRingEnd ℂ) u) = (starRingEnd ℂ) (msA u) := by
  unfold msA msB
  have hw : (1 + 2 * (starRingEnd ℂ) u).im ≠ 0 := by simp [hu]
  rw [← reflectedCompletedLambda_conj,
    show 2 * -(starRingEnd ℂ) u = 1 - (1 + 2 * (starRingEnd ℂ) u) by ring,
    reflectedCompletedLambda_one_sub_of_im hw]
  congr 1
  rw [map_add, map_one, map_mul, map_ofNat]

/-- **The truncated norm when the first Weyl coefficient vanishes.** -/
theorem integral_norm_sq_of_msA_eq_zero {u : ℂ} (hu : u ∈ eisensteinLineDomain) (hre : u.re < 0)
    (hA : msA u = 0) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 =
      ‖msB u‖ ^ 2 * Y ^ (-2 * u.re) / (-2 * u.re) := by
  have hYpos : 0 < Y := by linarith
  have hw : -(starRingEnd ℂ) u ∈ eisensteinLineDomain :=
    neg_conj_mem_eisensteinLineDomain hu (by linarith)
  have hms := maassSelberg_lineModel hu hw hY
  have him : u.im ≠ 0 := hu.2.ne'
  rw [← integral_norm_sq_eq_truncatedPairing hu Y] at hms
  -- the two combinations
  have hsub : u - -(starRingEnd ℂ) u = ((2 * u.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp; ring
  have hadd : u + -(starRingEnd ℂ) u = ((2 * u.im : ℝ) : ℂ) * Complex.I := by
    refine Complex.ext ?_ ?_
    · simp
    · simp; ring
  have hpow : (Y : ℂ) ^ (-(starRingEnd ℂ) u - u) = ((Y ^ (-2 * u.re) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hYpos.le]
    congr 1
    apply Complex.ext <;> simp; ring
  have hBB : msB u * (starRingEnd ℂ) (msB u) = ((‖msB u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold msRight at hms
  rw [hA, msA_neg_conj him, msB_neg_conj him, hA, map_zero, hsub, hadd, hpow] at hms
  simp only [zero_mul, mul_zero, zero_add, sub_zero, zero_sub] at hms
  -- hms : ↑(2 Re u) * (↑(2 Im u) I) * ↑(∫…) = ↑(2 Im u) I * -(msB u * conj (msB u) * ↑(Y^…))
  rw [hBB] at hms
  have hre' : ((2 * u.re : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  have him' : ((2 * u.im : ℝ) : ℂ) * Complex.I ≠ 0 := by
    apply mul_ne_zero
    · rw [Complex.ofReal_ne_zero]; linarith [hu.2]
    · exact Complex.I_ne_zero
  have h1 : ((2 * u.re : ℝ) : ℂ) * ((∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ) =
      -(((‖msB u‖ ^ 2 : ℝ) : ℂ) * ((Y ^ (-2 * u.re) : ℝ) : ℂ)) := by
    have h' : (((2 * u.im : ℝ) : ℂ) * Complex.I) *
        (((2 * u.re : ℝ) : ℂ) * ((∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 : ℝ) : ℂ)) =
        (((2 * u.im : ℝ) : ℂ) * Complex.I) *
          (-(((‖msB u‖ ^ 2 : ℝ) : ℂ) * ((Y ^ (-2 * u.re) : ℝ) : ℂ))) := by
      rw [← hms]; ring
    exact mul_left_cancel₀ him' h'
  have h1' : 2 * u.re * (∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2) =
      -(‖msB u‖ ^ 2 * Y ^ (-2 * u.re)) := by exact_mod_cast h1
  have hne : -2 * u.re ≠ 0 := by linarith
  rw [eq_div_iff hne]
  linear_combination -h1'

/-! ## Resonant states -/

/-- The parameter of the resonant state `E*(·, ρ/2)`. -/
def resonantParameter (ρ : ℂ) : ℂ := ρ / 2 - 1 / 2

theorem resonantParameter_mem {ρ : ℂ} (h0 : 0 < ρ.re) (him : 0 < ρ.im) :
    resonantParameter ρ ∈ eisensteinLineDomain := by
  refine ⟨?_, ?_⟩ <;> simp [resonantParameter] <;> linarith

theorem resonantParameter_re_neg {ρ : ℂ} (h1 : ρ.re < 1) : (resonantParameter ρ).re < 0 := by
  simp [resonantParameter]; linarith

theorem msA_resonantParameter (ρ : ℂ) : msA (resonantParameter ρ) = reflectedCompletedLambda ρ := by
  unfold msA resonantParameter; congr 1; ring

theorem msB_resonantParameter (ρ : ℂ) :
    msB (resonantParameter ρ) = reflectedCompletedLambda (ρ - 1) := by
  unfold msB resonantParameter; congr 1; ring

/-- `Λ(ρ − 1) ≠ 0` for `ρ` in the strip with `Im ρ ≠ 0`, by the functional equation. -/
theorem reflectedCompletedLambda_sub_one_ne_zero {ρ : ℂ} (h1 : ρ.re < 1) (him : ρ.im ≠ 0) :
    reflectedCompletedLambda (ρ - 1) ≠ 0 := by
  have h : reflectedCompletedLambda (ρ - 1) = reflectedCompletedLambda (2 - ρ) := by
    have := reflectedCompletedLambda_one_sub_of_im (s := 2 - ρ) (by simp [him])
    rw [← this]; congr 1; ring
  rw [h]
  unfold reflectedCompletedLambda
  apply mul_ne_zero
  · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  · exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)

/-- **The truncated `L²` norm of the resonant state of a zero: the cutoff-exponent receiver.**
For a zero `ρ` of `Λ` with `0 < Re ρ < 1`, `Im ρ > 0`, and every `Y ≥ 1`,
`∫_𝒟 ‖Λ^Y E*(·, ρ/2)‖² dμ = ‖Λ(ρ−1)‖² Y^{1−Re ρ} / (1 − Re ρ)`. -/
theorem integral_norm_sq_resonantState {ρ : ℂ} (hρ : reflectedCompletedLambda ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : 0 < ρ.im) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2 =
      ‖reflectedCompletedLambda (ρ - 1)‖ ^ 2 * Y ^ (1 - ρ.re) / (1 - ρ.re) := by
  have h := integral_norm_sq_of_msA_eq_zero (resonantParameter_mem h0 him)
    (resonantParameter_re_neg h1) (by rw [msA_resonantParameter]; exact hρ) hY
  rw [h, msB_resonantParameter]
  have e : -2 * (resonantParameter ρ).re = 1 - ρ.re := by simp [resonantParameter]; ring
  rw [e]

/-- The norm constant of a resonant state is positive. -/
theorem resonant_norm_const_pos {ρ : ℂ} (h1 : ρ.re < 1) (him : 0 < ρ.im) :
    0 < ‖reflectedCompletedLambda (ρ - 1)‖ ^ 2 / (1 - ρ.re) := by
  have := reflectedCompletedLambda_sub_one_ne_zero h1 him.ne'
  have hn : 0 < ‖reflectedCompletedLambda (ρ - 1)‖ := norm_pos_iff.mpr this
  have : 0 < 1 - ρ.re := by linarith
  positivity

end

end RHTower
