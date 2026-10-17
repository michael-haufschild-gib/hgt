import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation
import GaloisForLFunctions.RHTower.PrimeArchBernsteinPencil
import GaloisForLFunctions.RHTower.XiOrdinateBandCopies
import GaloisForLFunctions.RHTower.XiMassHeightTransfer
import GaloisForLFunctions.RHTower.RiemannVonMangoldt

/-!
# Fixed-order large-shift positivity of the calibrated Hausdorff tower

The endpoint-calibrated prime–archimedean Hausdorff array is

`D(k, r) = Σ_q x_q^(k+1) (R − x_q)^r`,

summed over the multiplicity copies `q` of the Xi divisor, where `x_q = a_q^(-2)` is the
reciprocal-square atom of the centered zero `a_q` and `R` is the endpoint radius.  Positivity of
the whole array is RH.  This file proves that every row is eventually nonnegative in the shift:

`∀ k, ∃ r₀, ∀ r ≥ r₀, 0 ≤ D(k, r)`,

unconditionally.

Mechanism.  Put `Λ = K R / r` with `K = 10(k+1) + 20` and `T = √(r / (K R))`.  Atoms with
`Re x_q ≤ Λ` come from zeros of ordinate at least `0.97 T`; their reciprocal squares have relative
imaginary part `O(1/T)`, both phases `(k+1)·arg x_q` and `r·arg(R − x_q)` are small, and each
such term has real part at least half its modulus.  Atoms with `Re x_q > Λ` have ordinate below
`T`, are counted by the Riemann–von Mangoldt law, and their terms carry the factor `e^(-0.99 K)`.
The band of zeros with ordinate in `(1.2 T, 1.4 T]`, counted by the same law, contributes with the
factor `e^(-0.75 K)`; for the chosen `K` the band dominates.

Large shifts therefore probe only the Weyl regime of the divisor, where positivity is a density
statement rather than an angle budget.  The RH content of the Hausdorff tower is carried by
bounded shifts in each order.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Geometry of one reciprocal-square atom -/

theorem xiSpectralPoint_re_eq_ordinate' (q : XiZeroCopy) :
    (xiSpectralPoint q).re = (q.1 : ℂ).im := by
  simp [xiSpectralPoint]

/-- Every centered zero has squared ordinate at least `41/2`. -/
theorem xiSpectralPoint_re_sq_ge (q : XiZeroCopy) :
    41 / 2 ≤ (xiSpectralPoint q).re ^ 2 := by
  rw [xiSpectralPoint_re_eq_ordinate']
  have h := xiZeroCopy_im_sq_ge_endpoint_source_inverse_gap q
  have hC := xiEndpointCompletedCurvature_lt_two_over_fortyThree
  have hCpos := xiEndpointCompletedCurvature_pos
  have h43 : (43 : ℝ) / 2 < 1 / xiEndpointCompletedCurvature := by
    rw [lt_div_iff₀ hCpos]
    nlinarith
  linarith

theorem xiSpectralPoint_im_sq_lt (q : XiZeroCopy) :
    (xiSpectralPoint q).im ^ 2 < 1 / 4 := by
  obtain ⟨h1, h2⟩ := xiSpectralPoint_im_mem_openHalf q
  nlinarith

theorem normSq_xiSpectralPoint_eq (q : XiZeroCopy) :
    Complex.normSq (xiSpectralPoint q) =
      (xiSpectralPoint q).re ^ 2 + (xiSpectralPoint q).im ^ 2 := by
  rw [Complex.normSq_apply]
  ring

theorem normSq_xiSpectralPoint_ge (q : XiZeroCopy) :
    41 / 2 ≤ Complex.normSq (xiSpectralPoint q) := by
  rw [normSq_xiSpectralPoint_eq]
  nlinarith [xiSpectralPoint_re_sq_ge q, sq_nonneg (xiSpectralPoint q).im]

theorem normSq_xiSpectralPoint_pos (q : XiZeroCopy) :
    0 < Complex.normSq (xiSpectralPoint q) := by
  linarith [normSq_xiSpectralPoint_ge q]

/-- Real part of the reciprocal-square atom. -/
theorem xiZeroCopyReciprocalSquare_re (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).re =
      ((xiSpectralPoint q).re ^ 2 - (xiSpectralPoint q).im ^ 2) /
        Complex.normSq (xiSpectralPoint q) ^ 2 := by
  have hN := (normSq_xiSpectralPoint_pos q).ne'
  rw [xiZeroCopyReciprocalSquare, pow_two, Complex.mul_re, Complex.inv_re, Complex.inv_im]
  field_simp

/-- Imaginary part of the reciprocal-square atom. -/
theorem xiZeroCopyReciprocalSquare_im (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im =
      -(2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im) /
        Complex.normSq (xiSpectralPoint q) ^ 2 := by
  have hN := (normSq_xiSpectralPoint_pos q).ne'
  rw [xiZeroCopyReciprocalSquare, pow_two, Complex.mul_im, Complex.inv_re, Complex.inv_im]
  field_simp
  ring

/-- Modulus of the reciprocal-square atom. -/
theorem norm_xiZeroCopyReciprocalSquare (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ = 1 / Complex.normSq (xiSpectralPoint q) := by
  have hN := (normSq_xiSpectralPoint_pos q).ne'
  rw [xiZeroCopyReciprocalSquare, norm_pow, norm_inv, Complex.normSq_eq_norm_sq]
  field_simp

theorem xiThermalNode_eq_re (q : XiZeroCopy) :
    xiThermalNode q = (xiZeroCopyReciprocalSquare q).re := rfl

/-- The thermal node is at most the reciprocal squared modulus of the zero. -/
theorem xiThermalNode_le_inv_normSq (q : XiZeroCopy) :
    xiThermalNode q ≤ 1 / Complex.normSq (xiSpectralPoint q) := by
  rw [xiThermalNode_eq_re, xiZeroCopyReciprocalSquare_re]
  have hN := normSq_xiSpectralPoint_pos q
  rw [div_le_div_iff₀ (by positivity) hN, normSq_xiSpectralPoint_eq]
  nlinarith [sq_nonneg (xiSpectralPoint q).im, sq_nonneg (xiSpectralPoint q).re]

/-- Lower bound for the thermal node in terms of the squared modulus `N`: `(N − 1/2)/N² ≤ λ`. -/
theorem sub_half_div_sq_le_xiThermalNode (q : XiZeroCopy) :
    (Complex.normSq (xiSpectralPoint q) - 1 / 2) / Complex.normSq (xiSpectralPoint q) ^ 2 ≤
      xiThermalNode q := by
  rw [xiThermalNode_eq_re, xiZeroCopyReciprocalSquare_re]
  have hN := normSq_xiSpectralPoint_pos q
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [normSq_xiSpectralPoint_eq]
  nlinarith [xiSpectralPoint_im_sq_lt q]

/-- The imaginary part of the atom is at most `|γ| / N²`. -/
theorem abs_im_xiZeroCopyReciprocalSquare_le (q : XiZeroCopy) :
    |(xiZeroCopyReciprocalSquare q).im| ≤
      |(xiSpectralPoint q).re| / Complex.normSq (xiSpectralPoint q) ^ 2 := by
  rw [xiZeroCopyReciprocalSquare_im, abs_div,
    abs_of_pos (pow_pos (normSq_xiSpectralPoint_pos q) 2)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [abs_neg, abs_mul, abs_mul, abs_two]
  have hβ : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
    obtain ⟨h1, h2⟩ := xiSpectralPoint_im_mem_openHalf q
    rw [abs_le]
    constructor <;> linarith
  nlinarith [abs_nonneg (xiSpectralPoint q).re]

/-- The relative tilt of the atom is at most `2/|γ|`: `|Im x| ≤ (2/|γ|) λ`. -/
theorem abs_im_xiZeroCopyReciprocalSquare_le_tilt (q : XiZeroCopy) :
    |(xiZeroCopyReciprocalSquare q).im| ≤
      2 / |(xiSpectralPoint q).re| * xiThermalNode q := by
  have hγsq : 41 / 2 ≤ (xiSpectralPoint q).re ^ 2 := xiSpectralPoint_re_sq_ge q
  have hγabs : 4 ≤ |(xiSpectralPoint q).re| := by
    have h := sq_abs (xiSpectralPoint q).re
    nlinarith [abs_nonneg (xiSpectralPoint q).re]
  have hγpos : 0 < |(xiSpectralPoint q).re| := by linarith
  have hN : 41 / 2 ≤ Complex.normSq (xiSpectralPoint q) := normSq_xiSpectralPoint_ge q
  have hNγ : (xiSpectralPoint q).re ^ 2 ≤ Complex.normSq (xiSpectralPoint q) := by
    rw [normSq_xiSpectralPoint_eq]
    nlinarith [sq_nonneg (xiSpectralPoint q).im]
  have h1 := abs_im_xiZeroCopyReciprocalSquare_le q
  have h2 := sub_half_div_sq_le_xiThermalNode q
  have hkey : |(xiSpectralPoint q).re| / Complex.normSq (xiSpectralPoint q) ^ 2 ≤
      2 / |(xiSpectralPoint q).re| *
        ((Complex.normSq (xiSpectralPoint q) - 1 / 2) /
          Complex.normSq (xiSpectralPoint q) ^ 2) := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : |(xiSpectralPoint q).re| * |(xiSpectralPoint q).re| =
        (xiSpectralPoint q).re ^ 2 := by rw [← sq, sq_abs]
    nlinarith [pow_pos (normSq_xiSpectralPoint_pos q) 2]
  calc |(xiZeroCopyReciprocalSquare q).im|
      ≤ |(xiSpectralPoint q).re| / Complex.normSq (xiSpectralPoint q) ^ 2 := h1
    _ ≤ 2 / |(xiSpectralPoint q).re| *
        ((Complex.normSq (xiSpectralPoint q) - 1 / 2) /
          Complex.normSq (xiSpectralPoint q) ^ 2) := hkey
    _ ≤ 2 / |(xiSpectralPoint q).re| * xiThermalNode q :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Universal tilt bound `|Im x| ≤ λ / 2`. -/
theorem abs_im_xiZeroCopyReciprocalSquare_le_half (q : XiZeroCopy) :
    |(xiZeroCopyReciprocalSquare q).im| ≤ 1 / 2 * xiThermalNode q := by
  have h := abs_im_xiZeroCopyReciprocalSquare_le_tilt q
  have hγsq : 41 / 2 ≤ (xiSpectralPoint q).re ^ 2 := xiSpectralPoint_re_sq_ge q
  have hγabs : 4 ≤ |(xiSpectralPoint q).re| := by
    have := sq_abs (xiSpectralPoint q).re
    nlinarith [abs_nonneg (xiSpectralPoint q).re]
  have hlam := (xiThermalNode_pos q).le
  have hfrac : 2 / |(xiSpectralPoint q).re| ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  calc |(xiZeroCopyReciprocalSquare q).im| ≤ 2 / |(xiSpectralPoint q).re| * xiThermalNode q := h
    _ ≤ 1 / 2 * xiThermalNode q := mul_le_mul_of_nonneg_right hfrac hlam

/-- The modulus of the atom is at most `(1 + 1/(2N − 1))` times its thermal node. -/
theorem norm_xiZeroCopyReciprocalSquare_le_node_mul (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ ≤
      (1 + 1 / (2 * Complex.normSq (xiSpectralPoint q) - 1)) * xiThermalNode q := by
  have hN : 41 / 2 ≤ Complex.normSq (xiSpectralPoint q) := normSq_xiSpectralPoint_ge q
  have hN0 : Complex.normSq (xiSpectralPoint q) ≠ 0 := by positivity
  have hN1 : 2 * Complex.normSq (xiSpectralPoint q) - 1 ≠ 0 := by
    intro h
    linarith
  have h2 := sub_half_div_sq_le_xiThermalNode q
  rw [norm_xiZeroCopyReciprocalSquare]
  have hkey : 1 / Complex.normSq (xiSpectralPoint q) =
      (1 + 1 / (2 * Complex.normSq (xiSpectralPoint q) - 1)) *
        ((Complex.normSq (xiSpectralPoint q) - 1 / 2) /
          Complex.normSq (xiSpectralPoint q) ^ 2) := by
    have e1 : 1 + 1 / (2 * Complex.normSq (xiSpectralPoint q) - 1) =
        2 * Complex.normSq (xiSpectralPoint q) / (2 * Complex.normSq (xiSpectralPoint q) - 1) := by
      rw [eq_div_iff hN1]
      rw [add_mul, one_div, inv_mul_cancel₀ hN1]
      ring
    have e2 : Complex.normSq (xiSpectralPoint q) - 1 / 2 =
        (2 * Complex.normSq (xiSpectralPoint q) - 1) / 2 := by ring
    rw [e1, e2, div_mul_div_comm, div_eq_div_iff hN0 (by positivity)]
    ring
  rw [hkey]
  have hpos : 0 ≤ 1 + 1 / (2 * Complex.normSq (xiSpectralPoint q) - 1) := by
    have : 0 < 2 * Complex.normSq (xiSpectralPoint q) - 1 := by linarith
    positivity
  exact mul_le_mul_of_nonneg_left h2 hpos

/-- The reciprocal-square atom has modulus at most `41/40` of its thermal node. -/
theorem norm_xiZeroCopyReciprocalSquare_le_universal (q : XiZeroCopy) :
    ‖xiZeroCopyReciprocalSquare q‖ ≤ 41 / 40 * xiThermalNode q := by
  have h := norm_xiZeroCopyReciprocalSquare_le_node_mul q
  have hN : 41 / 2 ≤ Complex.normSq (xiSpectralPoint q) := normSq_xiSpectralPoint_ge q
  have hlam := (xiThermalNode_pos q).le
  have hfrac : 1 + 1 / (2 * Complex.normSq (xiSpectralPoint q) - 1) ≤ 41 / 40 := by
    have : 1 / (2 * Complex.normSq (xiSpectralPoint q) - 1) ≤ 1 / 40 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  calc ‖xiZeroCopyReciprocalSquare q‖ ≤
      (1 + 1 / (2 * Complex.normSq (xiSpectralPoint q) - 1)) * xiThermalNode q := h
    _ ≤ 41 / 40 * xiThermalNode q := mul_le_mul_of_nonneg_right hfrac hlam

/-! ## Distance from the atom to the radius -/

/-- If `|Im x| ≤ δ λ` with `λ = Re x ≤ R`, then `‖R − x‖ ≤ R − (1 − δ) λ`.  The difference of
squares is exactly `2 δ λ (R − λ) + δ² λ² − (Im x)²`. -/
theorem norm_real_sub_le_of_abs_im_le {R lam δ : ℝ} {x : ℂ} (hre : x.re = lam)
    (hlam : 0 ≤ lam) (hlamR : lam ≤ R) (hδ : 0 ≤ δ) (him : |x.im| ≤ δ * lam) :
    ‖(R : ℂ) - x‖ ≤ R - (1 - δ) * lam := by
  have hR0 : 0 ≤ R - (1 - δ) * lam := by nlinarith
  rw [Complex.norm_def, Real.sqrt_le_left hR0, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, hre, zero_sub,
    mul_neg]
  have h1 : x.im * x.im ≤ (δ * lam) ^ 2 := by
    have h0 : 0 ≤ δ * lam := mul_nonneg hδ hlam
    have := abs_le.mp him
    nlinarith [abs_nonneg x.im, sq_abs x.im]
  nlinarith [h1, mul_nonneg (mul_nonneg hδ hlam) (sub_nonneg.mpr hlamR)]

/-! ## Elementary exponential estimates -/

theorem one_sub_pow_le_exp_neg {t : ℝ} (ht1 : t ≤ 1) (r : ℕ) :
    (1 - t) ^ r ≤ Real.exp (-(r * t)) := by
  have h := Real.one_sub_le_exp_neg t
  have h0 : 0 ≤ 1 - t := by linarith
  calc (1 - t) ^ r ≤ (Real.exp (-t)) ^ r := pow_le_pow_left₀ h0 h r
    _ = Real.exp (-(r * t)) := by
        rw [← Real.exp_nat_mul]
        ring_nf

theorem exp_neg_div_le_one_sub_pow {t : ℝ} (ht1 : t < 1) (r : ℕ) :
    Real.exp (-(r * t) / (1 - t)) ≤ (1 - t) ^ r := by
  have hpos : 0 < 1 - t := by linarith
  have hlog : -t / (1 - t) ≤ Real.log (1 - t) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos
    have heq : 1 - (1 - t)⁻¹ = -t / (1 - t) := by
      field_simp
      ring
    linarith
  calc Real.exp (-(r * t) / (1 - t)) = (Real.exp (-t / (1 - t))) ^ r := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ (Real.exp (Real.log (1 - t))) ^ r :=
        pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr hlog) r
    _ = (1 - t) ^ r := by rw [Real.exp_log hpos]

/-- `λ ↦ λ^n e^{-cλ}` is decreasing beyond `n/c`. -/
theorem pow_mul_exp_neg_antitone_beyond {c lam0 lam : ℝ} (n : ℕ) (h0 : 0 < lam0) (hle : lam0 ≤ lam)
    (hc : (n : ℝ) ≤ c * lam0) :
    lam ^ n * Real.exp (-(c * lam)) ≤ lam0 ^ n * Real.exp (-(c * lam0)) := by
  have hlam : 0 < lam := lt_of_lt_of_le h0 hle
  have hratio : (lam / lam0) ^ n ≤ Real.exp (c * (lam - lam0)) := by
    have h1 : lam / lam0 ≤ Real.exp ((lam - lam0) / lam0) := by
      have h := Real.add_one_le_exp ((lam - lam0) / lam0)
      have heq : lam / lam0 = (lam - lam0) / lam0 + 1 := by
        field_simp
        ring
      linarith
    calc (lam / lam0) ^ n ≤ (Real.exp ((lam - lam0) / lam0)) ^ n :=
          pow_le_pow_left₀ (div_nonneg hlam.le h0.le) h1 n
      _ = Real.exp (n * ((lam - lam0) / lam0)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (c * (lam - lam0)) := by
          apply Real.exp_le_exp.mpr
          have hd : 0 ≤ lam - lam0 := by linarith
          have hn : (n : ℝ) / lam0 ≤ c := by
            rw [div_le_iff₀ h0]
            exact hc
          calc (n : ℝ) * ((lam - lam0) / lam0) = (n / lam0) * (lam - lam0) := by ring
            _ ≤ c * (lam - lam0) := by gcongr
  calc lam ^ n * Real.exp (-(c * lam))
      = lam0 ^ n * (lam / lam0) ^ n * Real.exp (-(c * lam)) := by
        rw [div_pow]
        field_simp
    _ ≤ lam0 ^ n * Real.exp (c * (lam - lam0)) * Real.exp (-(c * lam)) := by
        gcongr
    _ = lam0 ^ n * Real.exp (-(c * lam0)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-! ## The small-phase lemma -/

/-- If the total phase budget `n|τ| + r|σ|` is at most `1/20`, the product
`(1 + iτ)^n (1 − iσ)^r` has real part at least half its modulus. -/
theorem half_norm_le_re_of_small_phase {τ σ : ℝ} (n r : ℕ) (hτ : |τ| ≤ 1 / 2)
    (hσ : |σ| ≤ 1 / 2) (h : (n : ℝ) * |τ| + (r : ℝ) * |σ| ≤ 1 / 20) :
    1 / 2 * ‖(1 + (τ : ℂ) * I) ^ n * (1 - (σ : ℂ) * I) ^ r‖ ≤
      ((1 + (τ : ℂ) * I) ^ n * (1 - (σ : ℂ) * I) ^ r).re := by
  set u : ℂ := 1 + (τ : ℂ) * I with hu_def
  set v : ℂ := 1 - (σ : ℂ) * I with hv_def
  have hu : u ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hu_def] at this
  have hv : v ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hv_def] at this
  have hnormτ : ‖(τ : ℂ) * I‖ = |τ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hnormσ : ‖-((σ : ℂ) * I)‖ = |σ| := by
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hlogu : ‖Complex.log u‖ ≤ 3 / 2 * |τ| := by
    have := Complex.norm_log_one_add_half_le_self (z := (τ : ℂ) * I) (by rw [hnormτ]; exact hτ)
    rw [hnormτ] at this
    simpa [hu_def] using this
  have hlogv : ‖Complex.log v‖ ≤ 3 / 2 * |σ| := by
    have := Complex.norm_log_one_add_half_le_self (z := -((σ : ℂ) * I))
      (by rw [hnormσ]; exact hσ)
    rw [hnormσ] at this
    have hv' : v = 1 + -((σ : ℂ) * I) := by rw [hv_def]; ring
    rw [hv']
    exact this
  set Z : ℂ := (n : ℂ) * Complex.log u + (r : ℂ) * Complex.log v with hZ_def
  have hexp : Complex.exp Z = u ^ n * v ^ r := by
    rw [hZ_def, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul, Complex.exp_log hu,
      Complex.exp_log hv]
  have hZ : ‖Z‖ ≤ 3 / 40 := by
    calc ‖Z‖ ≤ ‖(n : ℂ) * Complex.log u‖ + ‖(r : ℂ) * Complex.log v‖ := norm_add_le _ _
      _ = n * ‖Complex.log u‖ + r * ‖Complex.log v‖ := by
          rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
      _ ≤ n * (3 / 2 * |τ|) + r * (3 / 2 * |σ|) := by gcongr
      _ = 3 / 2 * (n * |τ| + r * |σ|) := by ring
      _ ≤ 3 / 2 * (1 / 20) := by gcongr
      _ = 3 / 40 := by norm_num
  have hdiff : ‖Complex.exp Z - 1‖ ≤ 3 / 20 := by
    have := Complex.norm_exp_sub_one_le (x := Z) (by linarith)
    linarith
  rw [← hexp]
  have hre : 17 / 20 ≤ (Complex.exp Z).re := by
    have h1 : |(Complex.exp Z - 1).re| ≤ ‖Complex.exp Z - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h1
    have := (abs_le.mp h1).1
    linarith
  have hnorm : ‖Complex.exp Z‖ ≤ 23 / 20 := by
    calc ‖Complex.exp Z‖ = ‖(Complex.exp Z - 1) + 1‖ := by ring_nf
      _ ≤ ‖Complex.exp Z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 / 20 + 1 := by
          gcongr
          simp
      _ = 23 / 20 := by norm_num
  linarith

/-! ## Counting copies through the symmetric divisor mass -/

theorem xiSymmetricMass_zero : xiSymmetricMass 0 = 0 := by
  rw [xiSymmetricMass_eq_support_sum le_rfl]
  apply Finset.sum_eq_zero
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ
  exfalso
  have him : (ρ : ℂ).im = 0 := abs_nonpos_iff.mp hρ
  exact xiSupport_im_ne_zero ρ him

/-- A finite set of copies with ordinate modulus at most `T` has at most `xiSymmetricMass T`
elements. -/
theorem card_le_xiSymmetricMass_of_forall_abs_im_le {T : ℝ} (hT : 0 ≤ T)
    {S : Finset XiZeroCopy} (hS : ∀ q ∈ S, |(q.1 : ℂ).im| ≤ T) :
    (S.card : ℝ) ≤ xiSymmetricMass T := by
  have hsub : S ⊆ xiCopiesBand 0 T := by
    intro q hq
    rw [mem_xiCopiesBand]
    exact ⟨abs_pos.mpr (xiSupport_im_ne_zero q.1), hS q hq⟩
  have h := xiSymmetricMass_diff_eq_card (le_refl (0 : ℝ)) hT
  rw [xiSymmetricMass_zero, sub_zero] at h
  have hcard : (S.card : ℤ) ≤ ((xiCopiesBand 0 T).card : ℤ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hreal : (S.card : ℝ) ≤ ((xiCopiesBand 0 T).card : ℝ) := by exact_mod_cast hcard
  calc (S.card : ℝ) ≤ ((xiCopiesBand 0 T).card : ℝ) := hreal
    _ = ((xiSymmetricMass T : ℤ) : ℝ) := by exact_mod_cast h.symm

/-- The band count as a real difference of symmetric masses. -/
theorem card_xiCopiesBand_eq_real {T₁ T₂ : ℝ} (h₁ : 0 ≤ T₁) (h : T₁ ≤ T₂) :
    ((xiCopiesBand T₁ T₂).card : ℝ) = (xiSymmetricMass T₂ : ℝ) - (xiSymmetricMass T₁ : ℝ) := by
  have hdiff := xiSymmetricMass_diff_eq_card h₁ h
  have := congrArg (fun z : ℤ => (z : ℝ)) hdiff
  push_cast at this
  linarith

/-! ## The atom term and its polar factorization -/

/-- The `(k, r)` atom of the calibrated Hausdorff array. -/
def hausdorffAtomTerm (R : ℝ) (k r : ℕ) (q : XiZeroCopy) : ℂ :=
  xiZeroCopyReciprocalSquare q ^ (k + 1) * ((R : ℂ) - xiZeroCopyReciprocalSquare q) ^ r

theorem norm_hausdorffAtomTerm (R : ℝ) (k r : ℕ) (q : XiZeroCopy) :
    ‖hausdorffAtomTerm R k r q‖ =
      ‖xiZeroCopyReciprocalSquare q‖ ^ (k + 1) * ‖(R : ℂ) - xiZeroCopyReciprocalSquare q‖ ^ r := by
  rw [hausdorffAtomTerm, norm_mul, norm_pow, norm_pow]

/-- Below the radius, the atom factors as a positive real scale times a product of two near-unit
phase factors. -/
theorem hausdorffAtomTerm_eq_scale_mul_phase (R : ℝ) (k r : ℕ) (q : XiZeroCopy)
    (hlamR : xiThermalNode q < R) :
    hausdorffAtomTerm R k r q =
      ((xiThermalNode q ^ (k + 1) * (R - xiThermalNode q) ^ r : ℝ) : ℂ) *
        ((1 + (((xiZeroCopyReciprocalSquare q).im / xiThermalNode q : ℝ) : ℂ) * I) ^ (k + 1) *
          (1 - (((xiZeroCopyReciprocalSquare q).im / (R - xiThermalNode q) : ℝ) : ℂ) * I) ^ r) := by
  have hlam : 0 < xiThermalNode q := xiThermalNode_pos q
  have hRl : R - xiThermalNode q ≠ 0 := by linarith
  set τ : ℝ := (xiZeroCopyReciprocalSquare q).im / xiThermalNode q with hτ
  set σ : ℝ := (xiZeroCopyReciprocalSquare q).im / (R - xiThermalNode q) with hσ
  set u : ℂ := 1 + (τ : ℂ) * I with hu
  set v : ℂ := 1 - (σ : ℂ) * I with hv
  have hx : (xiThermalNode q : ℂ) * u = xiZeroCopyReciprocalSquare q := by
    apply Complex.ext
    · simp [hu, xiThermalNode_eq_re]
    · simp only [hu, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.one_im, Complex.I_im, Complex.I_re, Complex.add_re, Complex.one_re, mul_one,
        mul_zero, zero_add, add_zero, zero_mul]
      rw [hτ]
      field_simp
  have hRx : ((R - xiThermalNode q : ℝ) : ℂ) * v = (R : ℂ) - xiZeroCopyReciprocalSquare q := by
    apply Complex.ext
    · simp [hv, xiThermalNode_eq_re]
    · simp only [hv, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
        Complex.one_im, Complex.I_im, Complex.I_re, Complex.sub_re, Complex.one_re, mul_one,
        mul_zero, zero_sub, zero_mul, add_zero]
      rw [hσ]
      field_simp
  have hcalc : ((xiThermalNode q ^ (k + 1) * (R - xiThermalNode q) ^ r : ℝ) : ℂ) *
      (u ^ (k + 1) * v ^ r) =
      ((xiThermalNode q : ℂ) * u) ^ (k + 1) * (((R - xiThermalNode q : ℝ) : ℂ) * v) ^ r := by
    rw [mul_pow, mul_pow]
    push_cast
    ring
  rw [hausdorffAtomTerm, hcalc, hx, hRx]

/-- An atom below the radius whose two phases are small has real part at least half its modulus. -/
theorem half_norm_le_re_hausdorffAtomTerm {R : ℝ} (k r : ℕ) {q : XiZeroCopy}
    (hlamR : xiThermalNode q < R)
    (hτ : |(xiZeroCopyReciprocalSquare q).im / xiThermalNode q| ≤ 1 / 2)
    (hσ : |(xiZeroCopyReciprocalSquare q).im / (R - xiThermalNode q)| ≤ 1 / 2)
    (h : ((k + 1 : ℕ) : ℝ) * |(xiZeroCopyReciprocalSquare q).im / xiThermalNode q| +
      (r : ℝ) * |(xiZeroCopyReciprocalSquare q).im / (R - xiThermalNode q)| ≤ 1 / 20) :
    1 / 2 * ‖hausdorffAtomTerm R k r q‖ ≤ (hausdorffAtomTerm R k r q).re := by
  have hlam : 0 < xiThermalNode q := xiThermalNode_pos q
  rw [hausdorffAtomTerm_eq_scale_mul_phase R k r q hlamR]
  set c : ℝ := xiThermalNode q ^ (k + 1) * (R - xiThermalNode q) ^ r with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (pow_nonneg hlam.le _) (pow_nonneg (by linarith) _)
  set W : ℂ := (1 + (((xiZeroCopyReciprocalSquare q).im / xiThermalNode q : ℝ) : ℂ) * I) ^ (k + 1) *
    (1 - (((xiZeroCopyReciprocalSquare q).im / (R - xiThermalNode q) : ℝ) : ℂ) * I) ^ r with hW
  have hphase : 1 / 2 * ‖W‖ ≤ W.re :=
    half_norm_le_re_of_small_phase (k + 1) r hτ hσ h
  rw [Complex.re_ofReal_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
  calc 1 / 2 * (c * ‖W‖) = c * (1 / 2 * ‖W‖) := by ring
    _ ≤ c * W.re := mul_le_mul_of_nonneg_left hphase hc0

/-- Real part of a complex number is at least minus its modulus. -/
theorem neg_norm_le_re' (z : ℂ) : -‖z‖ ≤ z.re := by
  have := Complex.abs_re_le_norm z
  exact (abs_le.mp this).1

/-! ## Ordinate windows read off the thermal node -/

/-- If `λ_q > 1/T²` then the zero has ordinate modulus below `T`. -/
theorem abs_ordinate_lt_of_inv_sq_lt_xiThermalNode {T : ℝ} (hT : 0 < T) {q : XiZeroCopy}
    (h : 1 / T ^ 2 < xiThermalNode q) : |(q.1 : ℂ).im| < T := by
  have h1 := xiThermalNode_le_inv_normSq q
  have hN := normSq_xiSpectralPoint_pos q
  have hNT : Complex.normSq (xiSpectralPoint q) < T ^ 2 := by
    have : 1 / T ^ 2 < 1 / Complex.normSq (xiSpectralPoint q) := lt_of_lt_of_le h h1
    exact lt_of_one_div_lt_one_div (by positivity) this
  have hγ : (xiSpectralPoint q).re ^ 2 < T ^ 2 := by
    have := normSq_xiSpectralPoint_eq q
    nlinarith [sq_nonneg (xiSpectralPoint q).im]
  rw [← xiSpectralPoint_re_eq_ordinate']
  have habs : |(xiSpectralPoint q).re| ^ 2 < T ^ 2 := by rwa [sq_abs]
  exact (pow_lt_pow_iff_left₀ (abs_nonneg _) hT.le two_ne_zero).mp habs

/-- If `λ_q ≤ c / T²` with `c ≤ 4` and `T ≥ 10`, then `N ≥ (10/(41 c)) · 4 T²`; we record the
two instances used: `c = 1` gives `|γ| ≥ 0.97 T`, `c = 4` gives `|γ| ≥ 0.46 T`. -/
theorem normSq_ge_of_xiThermalNode_le {T c : ℝ} (hT : 10 ≤ T) {q : XiZeroCopy}
    (h : xiThermalNode q ≤ c / T ^ 2) :
    40 / 41 * T ^ 2 ≤ c * Complex.normSq (xiSpectralPoint q) := by
  have h2 := sub_half_div_sq_le_xiThermalNode q
  have hN : 41 / 2 ≤ Complex.normSq (xiSpectralPoint q) := normSq_xiSpectralPoint_ge q
  have hNpos : 0 < Complex.normSq (xiSpectralPoint q) := by linarith
  have hT2 : 0 < T ^ 2 := by positivity
  have hcross : (Complex.normSq (xiSpectralPoint q) - 1 / 2) * T ^ 2 ≤
      c * Complex.normSq (xiSpectralPoint q) ^ 2 := by
    have := le_trans h2 h
    rw [div_le_div_iff₀ (by positivity) hT2] at this
    linarith
  -- N − 1/2 ≥ (40/41) N
  have hN' : 40 / 41 * Complex.normSq (xiSpectralPoint q) ≤
      Complex.normSq (xiSpectralPoint q) - 1 / 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hN' hT2.le]

theorem ordinate_ge_of_xiThermalNode_le_inv_sq {T : ℝ} (hT : 10 ≤ T) {q : XiZeroCopy}
    (h : xiThermalNode q ≤ 1 / T ^ 2) : 97 / 100 * T ≤ |(xiSpectralPoint q).re| := by
  have hN := normSq_ge_of_xiThermalNode_le (c := 1) hT h
  rw [one_mul] at hN
  have hβ := xiSpectralPoint_im_sq_lt q
  have hNeq := normSq_xiSpectralPoint_eq q
  have hT2 : 100 ≤ T ^ 2 := by nlinarith
  have hγ : (97 / 100 * T) ^ 2 ≤ (xiSpectralPoint q).re ^ 2 := by nlinarith
  have habs : (97 / 100 * T) ^ 2 ≤ |(xiSpectralPoint q).re| ^ 2 := by rwa [sq_abs]
  exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).mp habs

theorem ordinate_ge_of_xiThermalNode_le_four_inv_sq {T : ℝ} (hT : 10 ≤ T) {q : XiZeroCopy}
    (h : xiThermalNode q ≤ 4 / T ^ 2) : 46 / 100 * T ≤ |(xiSpectralPoint q).re| := by
  have hN := normSq_ge_of_xiThermalNode_le (c := 4) hT h
  have hβ := xiSpectralPoint_im_sq_lt q
  have hNeq := normSq_xiSpectralPoint_eq q
  have hT2 : 100 ≤ T ^ 2 := by nlinarith
  have hγ : (46 / 100 * T) ^ 2 ≤ (xiSpectralPoint q).re ^ 2 := by nlinarith
  have habs : (46 / 100 * T) ^ 2 ≤ |(xiSpectralPoint q).re| ^ 2 := by rwa [sq_abs]
  exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).mp habs

/-- Zeros in the ordinate band `(6T/5, 7T/5]` have thermal node in `[0.49/T², 0.7/T²]`. -/
theorem xiThermalNode_mem_of_ordinate_band {T : ℝ} (hT : 10 ≤ T) {q : XiZeroCopy}
    (h1 : 6 / 5 * T < |(q.1 : ℂ).im|) (h2 : |(q.1 : ℂ).im| ≤ 7 / 5 * T) :
    49 / 100 / T ^ 2 ≤ xiThermalNode q ∧ xiThermalNode q ≤ 7 / 10 / T ^ 2 := by
  rw [← xiSpectralPoint_re_eq_ordinate'] at h1 h2
  have hT2 : 100 ≤ T ^ 2 := by nlinarith
  have hTpos : 0 < T := by linarith
  have hγlo : (6 / 5 * T) ^ 2 < (xiSpectralPoint q).re ^ 2 := by
    rw [← sq_abs (xiSpectralPoint q).re]
    exact (pow_lt_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).mpr h1
  have hγhi : (xiSpectralPoint q).re ^ 2 ≤ (7 / 5 * T) ^ 2 := by
    rw [← sq_abs (xiSpectralPoint q).re]
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mpr h2
  have hβ := xiSpectralPoint_im_sq_lt q
  have hβ0 : 0 ≤ (xiSpectralPoint q).im ^ 2 := sq_nonneg _
  have hNeq := normSq_xiSpectralPoint_eq q
  have hNpos := normSq_xiSpectralPoint_pos q
  have hNlo : 36 / 25 * T ^ 2 < Complex.normSq (xiSpectralPoint q) := by nlinarith
  have hNhi : Complex.normSq (xiSpectralPoint q) ≤ 2 * T ^ 2 := by nlinarith
  constructor
  · have h2' := sub_half_div_sq_le_xiThermalNode q
    refine le_trans ?_ h2'
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hNlo.le) (sub_nonneg.mpr hNhi)]
  · have h1' := xiThermalNode_le_inv_normSq q
    refine le_trans h1' ?_
    rw [div_le_div_iff₀ hNpos (by positivity)]
    nlinarith

/-- Tilt bound from an ordinate lower bound: `|Im x| ≤ (2/G) λ` once `G ≤ |γ|`. -/
theorem abs_im_le_of_ordinate_ge {G : ℝ} (hG : 0 < G) {q : XiZeroCopy}
    (h : G ≤ |(xiSpectralPoint q).re|) :
    |(xiZeroCopyReciprocalSquare q).im| ≤ 2 / G * xiThermalNode q := by
  have h1 := abs_im_xiZeroCopyReciprocalSquare_le_tilt q
  have hlam := (xiThermalNode_pos q).le
  have hfrac : 2 / |(xiSpectralPoint q).re| ≤ 2 / G :=
    div_le_div_of_nonneg_left (by norm_num) hG h
  exact h1.trans (mul_le_mul_of_nonneg_right hfrac hlam)

/-! ## Per-atom bounds at the threshold scale `Λ = K R / r = 1 / T²` -/

/-- Atoms at or below the threshold are phase-controlled. -/
theorem half_norm_le_re_of_node_le_threshold {R K T : ℝ} (k r : ℕ) (hR : 0 < R)
    (hK : 1 ≤ K) (hr : 20 * K ≤ (r : ℝ)) (hT : 10 ≤ T)
    (hTK : 42 * ((k + 1 : ℕ) : ℝ) + 44 * K ≤ T)
    (hΛ : K * R / r = 1 / T ^ 2) {q : XiZeroCopy} (hq : xiThermalNode q ≤ 1 / T ^ 2) :
    1 / 2 * ‖hausdorffAtomTerm R k r q‖ ≤ (hausdorffAtomTerm R k r q).re := by
  have hlam := xiThermalNode_pos q
  have hrpos : 0 < (r : ℝ) := by linarith
  have hTpos : 0 < T := by linarith
  have hΛR : 1 / T ^ 2 ≤ R / 20 := by
    rw [← hΛ, div_le_div_iff₀ hrpos (by norm_num)]
    nlinarith
  have hlamR : xiThermalNode q < R := by linarith
  set G : ℝ := 97 / 100 * T with hG
  have hGpos : 0 < G := by positivity
  have hγ : G ≤ |(xiSpectralPoint q).re| := ordinate_ge_of_xiThermalNode_le_inv_sq hT hq
  have him : |(xiZeroCopyReciprocalSquare q).im| ≤ 2 / G * xiThermalNode q :=
    abs_im_le_of_ordinate_ge hGpos hγ
  have hτ : |(xiZeroCopyReciprocalSquare q).im / xiThermalNode q| ≤ 2 / G := by
    rw [abs_div, abs_of_pos hlam, div_le_iff₀ hlam]
    exact him
  -- `λ / (R − λ) ≤ Λ / (R − Λ) = K / (r − K) ≤ (20/19) K / r`
  have hRl : 0 < R - xiThermalNode q := by linarith
  have hrK : 0 < (r : ℝ) - K := by linarith
  have hΛK : (1 / T ^ 2) / (R - 1 / T ^ 2) = K / (r - K) := by
    rw [← hΛ]
    field_simp
  have hmono : xiThermalNode q / (R - xiThermalNode q) ≤ (1 / T ^ 2) / (R - 1 / T ^ 2) := by
    rw [div_le_div_iff₀ hRl (by linarith)]
    nlinarith
  have hσ : |(xiZeroCopyReciprocalSquare q).im / (R - xiThermalNode q)| ≤
      2 / G * (K / (r - K)) := by
    rw [abs_div, abs_of_pos hRl, div_le_iff₀ hRl]
    calc |(xiZeroCopyReciprocalSquare q).im| ≤ 2 / G * xiThermalNode q := him
      _ = 2 / G * (xiThermalNode q / (R - xiThermalNode q)) * (R - xiThermalNode q) := by
          field_simp
      _ ≤ 2 / G * ((1 / T ^ 2) / (R - 1 / T ^ 2)) * (R - xiThermalNode q) := by
          gcongr
      _ = 2 / G * (K / (r - K)) * (R - xiThermalNode q) := by rw [hΛK]
  have hrσ : (r : ℝ) * (2 / G * (K / (r - K))) ≤ 2 / G * (20 / 19 * K) := by
    have : (r : ℝ) * (K / (r - K)) ≤ 20 / 19 * K := by
      rw [mul_div_assoc', div_le_iff₀ hrK]
      nlinarith
    calc (r : ℝ) * (2 / G * (K / (r - K))) = 2 / G * (r * (K / (r - K))) := by ring
      _ ≤ 2 / G * (20 / 19 * K) := by gcongr
  have hbudget : ((k + 1 : ℕ) : ℝ) * (2 / G) + 2 / G * (20 / 19 * K) ≤ 1 / 20 := by
    have hG' : 40 * (((k + 1 : ℕ) : ℝ) + 20 / 19 * K) ≤ G := by
      rw [hG]
      nlinarith
    rw [show ((k + 1 : ℕ) : ℝ) * (2 / G) + 2 / G * (20 / 19 * K) =
        2 * (((k + 1 : ℕ) : ℝ) + 20 / 19 * K) / G by ring]
    rw [div_le_iff₀ hGpos]
    linarith
  have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have hGbig : 4 ≤ G := by
    rw [hG]
    linarith
  have hτhalf : |(xiZeroCopyReciprocalSquare q).im / xiThermalNode q| ≤ 1 / 2 := by
    refine hτ.trans ?_
    rw [div_le_div_iff₀ hGpos (by norm_num)]
    linarith
  have hσhalf : |(xiZeroCopyReciprocalSquare q).im / (R - xiThermalNode q)| ≤ 1 / 2 := by
    refine hσ.trans ?_
    have h1 : K / (r - K) ≤ 1 / 19 := by
      rw [div_le_div_iff₀ hrK (by norm_num)]
      linarith
    calc 2 / G * (K / (r - K)) ≤ 2 / 4 * (1 / 19) := by gcongr
      _ ≤ 1 / 2 := by norm_num
  apply half_norm_le_re_hausdorffAtomTerm k r hlamR hτhalf hσhalf
  calc ((k + 1 : ℕ) : ℝ) * |(xiZeroCopyReciprocalSquare q).im / xiThermalNode q| +
        (r : ℝ) * |(xiZeroCopyReciprocalSquare q).im / (R - xiThermalNode q)|
      ≤ ((k + 1 : ℕ) : ℝ) * (2 / G) + (r : ℝ) * (2 / G * (K / (r - K))) := by gcongr
    _ ≤ ((k + 1 : ℕ) : ℝ) * (2 / G) + 2 / G * (20 / 19 * K) := by linarith
    _ ≤ 1 / 20 := hbudget

/-- Lower bound for atoms in the ordinate band `(6T/5, 7T/5]`. -/
theorem band_re_hausdorffAtomTerm_ge {R K T : ℝ} (k r : ℕ) (hR : 0 < R) (hK : 1 ≤ K)
    (hr : 20 * K ≤ (r : ℝ)) (hT : 10 ≤ T) (hTK : 42 * ((k + 1 : ℕ) : ℝ) + 44 * K ≤ T)
    (hΛ : K * R / r = 1 / T ^ 2) {q : XiZeroCopy}
    (h1 : 6 / 5 * T < |(q.1 : ℂ).im|) (h2 : |(q.1 : ℂ).im| ≤ 7 / 5 * T) :
    1 / 2 * (49 / 100 * (1 / T ^ 2)) ^ (k + 1) * R ^ r * Real.exp (-(3 / 4 * K)) ≤
      (hausdorffAtomTerm R k r q).re := by
  obtain ⟨hlo₀, hhi₀⟩ := xiThermalNode_mem_of_ordinate_band hT h1 h2
  have hlo : 49 / 100 * (1 / T ^ 2) ≤ xiThermalNode q := by
    rwa [div_eq_mul_one_div] at hlo₀
  have hhi : xiThermalNode q ≤ 7 / 10 * (1 / T ^ 2) := by
    rwa [div_eq_mul_one_div] at hhi₀
  have hrpos : 0 < (r : ℝ) := by linarith
  have hTpos : 0 < T := by linarith
  have hΛpos : 0 < 1 / T ^ 2 := by positivity
  have hq : xiThermalNode q ≤ 1 / T ^ 2 := by linarith
  have hhalf := half_norm_le_re_of_node_le_threshold k r hR hK hr hT hTK hΛ hq
  have hlam := xiThermalNode_pos q
  have hΛR : 1 / T ^ 2 ≤ R / 20 := by
    rw [← hΛ, div_le_div_iff₀ hrpos (by norm_num)]
    nlinarith
  -- modulus bounds for the atom
  have hxlo : xiThermalNode q ≤ ‖xiZeroCopyReciprocalSquare q‖ := by
    rw [xiThermalNode_eq_re]
    exact Complex.re_le_norm _
  have hxhi : ‖xiZeroCopyReciprocalSquare q‖ ≤ 287 / 400 * (1 / T ^ 2) := by
    have := norm_xiZeroCopyReciprocalSquare_le_universal q
    linarith
  have hRx : R - 287 / 400 * (1 / T ^ 2) ≤ ‖(R : ℂ) - xiZeroCopyReciprocalSquare q‖ := by
    have := norm_sub_norm_le (R : ℂ) (xiZeroCopyReciprocalSquare q)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at this
    linarith
  have hRx0 : 0 ≤ R - 287 / 400 * (1 / T ^ 2) := by linarith
  -- the shift factor
  set t : ℝ := 287 / 400 * K / r with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 287 / 8000 := by
    rw [ht, div_le_iff₀ hrpos]
    nlinarith
  have htΛ : 287 / 400 * (1 / T ^ 2) = R * t := by
    rw [← hΛ, ht]
    field_simp
  have hrt : (r : ℝ) * t = 287 / 400 * K := by
    rw [ht]
    field_simp
  have hexp : Real.exp (-(3 / 4 * K)) ≤ (1 - t) ^ r := by
    refine le_trans ?_ (exp_neg_div_le_one_sub_pow (by linarith) r)
    apply Real.exp_le_exp.mpr
    rw [hrt, le_div_iff₀ (by linarith)]
    nlinarith
  have hpow : (49 / 100 * (1 / T ^ 2)) ^ (k + 1) * (R ^ r * Real.exp (-(3 / 4 * K))) ≤
      ‖hausdorffAtomTerm R k r q‖ := by
    rw [norm_hausdorffAtomTerm]
    apply mul_le_mul
    · exact pow_le_pow_left₀ (by positivity) (hlo.trans hxlo) _
    · calc R ^ r * Real.exp (-(3 / 4 * K)) ≤ R ^ r * (1 - t) ^ r := by gcongr
        _ = (R * (1 - t)) ^ r := (mul_pow _ _ _).symm
        _ ≤ ‖(R : ℂ) - xiZeroCopyReciprocalSquare q‖ ^ r := by
            apply pow_le_pow_left₀ (by nlinarith)
            rw [mul_sub, mul_one, ← htΛ]
            exact hRx
    · positivity
    · positivity
  calc 1 / 2 * (49 / 100 * (1 / T ^ 2)) ^ (k + 1) * R ^ r * Real.exp (-(3 / 4 * K))
      = 1 / 2 * ((49 / 100 * (1 / T ^ 2)) ^ (k + 1) * (R ^ r * Real.exp (-(3 / 4 * K)))) := by
        ring
    _ ≤ 1 / 2 * ‖hausdorffAtomTerm R k r q‖ := by gcongr
    _ ≤ (hausdorffAtomTerm R k r q).re := hhalf

/-- Upper bound for atoms strictly above the threshold. -/
theorem norm_hausdorffAtomTerm_le_of_threshold_lt {R K T : ℝ} (k r : ℕ) (hR : 0 < R)
    (hK10 : 10 * ((k + 1 : ℕ) : ℝ) ≤ K) (hK : 1 ≤ K) (hr : 20 * K ≤ (r : ℝ)) (hT : 500 ≤ T)
    (hΛ : K * R / r = 1 / T ^ 2) {q : XiZeroCopy} (hlamR : xiThermalNode q ≤ R)
    (hq : 1 / T ^ 2 < xiThermalNode q) :
    ‖hausdorffAtomTerm R k r q‖ ≤
      (41 / 10 * (1 / T ^ 2)) ^ (k + 1) * R ^ r * Real.exp (-(99 / 100 * K)) := by
  have hlam := xiThermalNode_pos q
  have hrpos : 0 < (r : ℝ) := by linarith
  have hTpos : 0 < T := by linarith
  have hT10 : 10 ≤ T := by linarith
  have hΛpos : 0 < 1 / T ^ 2 := by positivity
  have hxnorm := norm_xiZeroCopyReciprocalSquare_le_universal q
  rw [norm_hausdorffAtomTerm]
  by_cases hcase : xiThermalNode q ≤ 4 / T ^ 2
  · -- near-threshold atoms: tilt at most `1/100`
    have hγ := ordinate_ge_of_xiThermalNode_le_four_inv_sq hT10 hcase
    have hG : 0 < 46 / 100 * T := by positivity
    have him := abs_im_le_of_ordinate_ge hG hγ
    have him' : |(xiZeroCopyReciprocalSquare q).im| ≤ 1 / 100 * xiThermalNode q := by
      refine him.trans ?_
      apply mul_le_mul_of_nonneg_right _ hlam.le
      rw [div_le_iff₀ hG]
      nlinarith
    have hRx := norm_real_sub_le_of_abs_im_le (xiThermalNode_eq_re q).symm hlam.le hlamR
      (by norm_num) him'
    set t : ℝ := 99 / 100 * K / r with ht
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_iff₀ hrpos]
      nlinarith
    have hrt : (r : ℝ) * t = 99 / 100 * K := by
      rw [ht]
      field_simp
    have hRt : R - (1 - 1 / 100) * (1 / T ^ 2) = R * (1 - t) := by
      rw [← hΛ, ht]
      field_simp
      ring
    have hRx' : ‖(R : ℂ) - xiZeroCopyReciprocalSquare q‖ ≤ R * (1 - t) := by
      rw [← hRt]
      refine hRx.trans ?_
      nlinarith
    have hRt0 : 0 ≤ R * (1 - t) := le_trans (norm_nonneg _) hRx'
    have hx4 : ‖xiZeroCopyReciprocalSquare q‖ ≤ 41 / 10 * (1 / T ^ 2) := by
      have hcase' : xiThermalNode q ≤ 4 * (1 / T ^ 2) := by
        rwa [div_eq_mul_one_div] at hcase
      linarith
    calc ‖xiZeroCopyReciprocalSquare q‖ ^ (k + 1) * ‖(R : ℂ) - xiZeroCopyReciprocalSquare q‖ ^ r
        ≤ (41 / 10 * (1 / T ^ 2)) ^ (k + 1) * (R * (1 - t)) ^ r := by
          gcongr
      _ = (41 / 10 * (1 / T ^ 2)) ^ (k + 1) * (R ^ r * (1 - t) ^ r) := by
          rw [mul_pow R (1 - t) r]
      _ ≤ (41 / 10 * (1 / T ^ 2)) ^ (k + 1) * (R ^ r * Real.exp (-(r * t))) := by
          gcongr
          exact one_sub_pow_le_exp_neg ht1 r
      _ = (41 / 10 * (1 / T ^ 2)) ^ (k + 1) * R ^ r * Real.exp (-(99 / 100 * K)) := by
          rw [hrt]
          ring
  · -- far atoms: universal tilt `1/2` and the decreasing profile `λ^(k+1) e^{-rλ/(2R)}`
    rw [not_le] at hcase
    have hcase' : 4 * (1 / T ^ 2) < xiThermalNode q := by
      rwa [div_eq_mul_one_div] at hcase
    have him := abs_im_xiZeroCopyReciprocalSquare_le_half q
    have hRx := norm_real_sub_le_of_abs_im_le (xiThermalNode_eq_re q).symm hlam.le hlamR
      (by norm_num) him
    have hRx' : ‖(R : ℂ) - xiZeroCopyReciprocalSquare q‖ ≤
        R * (1 - xiThermalNode q / (2 * R)) := by
      refine hRx.trans (le_of_eq ?_)
      field_simp
      ring
    have ht1 : xiThermalNode q / (2 * R) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hprofile : xiThermalNode q ^ (k + 1) * Real.exp (-((r / (2 * R)) * xiThermalNode q)) ≤
        (4 * (1 / T ^ 2)) ^ (k + 1) * Real.exp (-((r / (2 * R)) * (4 * (1 / T ^ 2)))) := by
      apply pow_mul_exp_neg_antitone_beyond (k + 1) (by positivity) hcase'.le
      rw [← hΛ]
      field_simp
      nlinarith
    have hexpK : Real.exp (-((r / (2 * R)) * (4 * (1 / T ^ 2)))) ≤ Real.exp (-(99 / 100 * K)) := by
      apply Real.exp_le_exp.mpr
      rw [← hΛ]
      field_simp
      nlinarith
    calc ‖xiZeroCopyReciprocalSquare q‖ ^ (k + 1) * ‖(R : ℂ) - xiZeroCopyReciprocalSquare q‖ ^ r
        ≤ (41 / 40 * xiThermalNode q) ^ (k + 1) * (R * (1 - xiThermalNode q / (2 * R))) ^ r := by
          gcongr
      _ = (41 / 40) ^ (k + 1) * R ^ r *
          (xiThermalNode q ^ (k + 1) * (1 - xiThermalNode q / (2 * R)) ^ r) := by
          rw [mul_pow, mul_pow]
          ring
      _ ≤ (41 / 40) ^ (k + 1) * R ^ r *
          (xiThermalNode q ^ (k + 1) * Real.exp (-(r * (xiThermalNode q / (2 * R))))) := by
          gcongr
          exact one_sub_pow_le_exp_neg ht1 r
      _ = (41 / 40) ^ (k + 1) * R ^ r *
          (xiThermalNode q ^ (k + 1) * Real.exp (-((r / (2 * R)) * xiThermalNode q))) := by
          congr 3
          ring
      _ ≤ (41 / 40) ^ (k + 1) * R ^ r *
          ((4 * (1 / T ^ 2)) ^ (k + 1) * Real.exp (-((r / (2 * R)) * (4 * (1 / T ^ 2))))) := by
          gcongr
      _ ≤ (41 / 40) ^ (k + 1) * R ^ r *
          ((4 * (1 / T ^ 2)) ^ (k + 1) * Real.exp (-(99 / 100 * K))) := by
          gcongr
      _ = (41 / 10 * (1 / T ^ 2)) ^ (k + 1) * R ^ r * Real.exp (-(99 / 100 * K)) := by
          have hsplit : (41 / 10 * (1 / T ^ 2) : ℝ) ^ (k + 1) =
              (41 / 40) ^ (k + 1) * (4 * (1 / T ^ 2)) ^ (k + 1) := by
            rw [← mul_pow]
            congr 1
            ring
          rw [hsplit]
          ring

/-! ## Numerical constants -/

theorem exp_six_lt_fiveHundred : Real.exp 6 < 500 := by
  have h := Real.exp_one_lt_d9
  have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h6]
  calc Real.exp 1 ^ 6 < (2.7182818286 : ℝ) ^ 6 :=
        pow_lt_pow_left₀ h (Real.exp_pos 1).le (by norm_num)
    _ < 500 := by norm_num

theorem six_le_log_of_fiveHundred_le {T : ℝ} (hT : 500 ≤ T) : 6 ≤ Real.log T := by
  have := (Real.lt_log_iff_exp_lt (by linarith)).mpr (lt_of_lt_of_le exp_six_lt_fiveHundred hT)
  exact this.le

/-- `e^{2.4} ≥ 9` via `e^{0.6} ≥ 1.78`. -/
theorem nine_le_exp_twelve_fifths : (9 : ℝ) ≤ Real.exp (12 / 5) := by
  have h1 : (1 + 3 / 5 + (3 / 5) ^ 2 / 2 : ℝ) ≤ Real.exp (3 / 5) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have h4 : Real.exp (12 / 5) = Real.exp (3 / 5) ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h4]
  calc (9 : ℝ) ≤ (1 + 3 / 5 + (3 / 5) ^ 2 / 2) ^ 4 := by norm_num
    _ ≤ Real.exp (3 / 5) ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4

/-- `e^{4.8} ≥ 18` via `e^{1.2} ≥ 2.92`. -/
theorem eighteen_le_exp_twentyFour_fifths : (18 : ℝ) ≤ Real.exp (24 / 5) := by
  have h1 : (1 + 6 / 5 + (6 / 5) ^ 2 / 2 : ℝ) ≤ Real.exp (6 / 5) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have h4 : Real.exp (24 / 5) = Real.exp (6 / 5) ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h4]
  calc (18 : ℝ) ≤ (1 + 6 / 5 + (6 / 5) ^ 2 / 2) ^ 4 := by norm_num
    _ ≤ Real.exp (6 / 5) ^ 4 := pow_le_pow_left₀ (by norm_num) h1 4

/-- The band constant beats the threshold constant: with `K = 10(k+1) + 20`,
`(41/10)^(k+1) e^{-0.99K} ≤ (1/9) · (1/2)(49/100)^(k+1) e^{-0.75K}`. -/
theorem threshold_constant_le_band_constant (k : ℕ) :
    (41 / 10 : ℝ) ^ (k + 1) * Real.exp (-(99 / 100 * (10 * ((k + 1 : ℕ) : ℝ) + 20))) ≤
      1 / 9 * (1 / 2 * (49 / 100) ^ (k + 1) * Real.exp (-(3 / 4 * (10 * ((k + 1 : ℕ) : ℝ) + 20)))) := by
  set n : ℕ := k + 1 with hn
  have hexp : Real.exp (-(99 / 100 * (10 * (n : ℝ) + 20))) =
      Real.exp (-(3 / 4 * (10 * (n : ℝ) + 20))) / (Real.exp (12 / 5) ^ n * Real.exp (24 / 5)) := by
    rw [eq_div_iff (by positivity), ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have h9 := nine_le_exp_twelve_fifths
  have h18 := eighteen_le_exp_twentyFour_fifths
  have hpow : (9 : ℝ) ^ n ≤ Real.exp (12 / 5) ^ n := pow_le_pow_left₀ (by norm_num) h9 n
  have hE0 : 0 < Real.exp (-(3 / 4 * (10 * (n : ℝ) + 20))) := Real.exp_pos _
  have hden : (9 : ℝ) ^ n * 18 ≤ Real.exp (12 / 5) ^ n * Real.exp (24 / 5) := by
    gcongr
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  have hratio : (41 / 10 : ℝ) ^ n ≤ (49 / 100) ^ n * 9 ^ n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by norm_num)
    norm_num
  calc (41 / 10 : ℝ) ^ n * Real.exp (-(3 / 4 * (10 * (n : ℝ) + 20)))
      ≤ (49 / 100) ^ n * 9 ^ n * Real.exp (-(3 / 4 * (10 * (n : ℝ) + 20))) := by gcongr
    _ = 1 / 9 * (1 / 2 * (49 / 100) ^ n * Real.exp (-(3 / 4 * (10 * (n : ℝ) + 20)))) *
          (9 ^ n * 18) := by ring
    _ ≤ 1 / 9 * (1 / 2 * (49 / 100) ^ n * Real.exp (-(3 / 4 * (10 * (n : ℝ) + 20)))) *
          (Real.exp (12 / 5) ^ n * Real.exp (24 / 5)) := by gcongr

/-! ## Counting through the Riemann–von Mangoldt asymptotic -/

/-- Copies of ordinate modulus at most `T` number at most `0.33 · T log T` once `T` is in the
asymptotic range. -/
theorem card_le_of_mass_close {T₀ T : ℝ}
    (hclose : ∀ S : ℝ, T₀ ≤ S →
      |(xiSymmetricMass S : ℝ) - 1 / Real.pi * (S * Real.log S)| ≤ 1 / 500 * (S * Real.log S))
    (hT500 : 500 ≤ T) (hTT0 : T₀ ≤ T) {S : Finset XiZeroCopy}
    (hS : ∀ q ∈ S, |(q.1 : ℂ).im| ≤ T) :
    (S.card : ℝ) ≤ 33 / 100 * (T * Real.log T) := by
  have hTpos : 0 < T := by linarith
  have hlogT : 6 ≤ Real.log T := six_le_log_of_fiveHundred_le hT500
  have hTlog : 0 ≤ T * Real.log T := mul_nonneg hTpos.le (by linarith)
  have hpi_hi : 1 / Real.pi < 1 / 3.14 := one_div_lt_one_div_of_lt (by norm_num) Real.pi_gt_d2
  have h1 := card_le_xiSymmetricMass_of_forall_abs_im_le hTpos.le hS
  have h2 := (abs_le.mp (hclose T hTT0)).2
  have h3 : 1 / Real.pi * (T * Real.log T) ≤ 1 / 3.14 * (T * Real.log T) :=
    mul_le_mul_of_nonneg_right hpi_hi.le hTlog
  have h4 : (1 / 3.14 + 1 / 500 : ℝ) * (T * Real.log T) ≤ 33 / 100 * (T * Real.log T) :=
    mul_le_mul_of_nonneg_right (by norm_num) hTlog
  linarith

/-- The band `(6T/5, 7T/5]` carries at least `0.04 · T log T` copies. -/
theorem band_card_ge_of_mass_close {T₀ T : ℝ}
    (hclose : ∀ S : ℝ, T₀ ≤ S →
      |(xiSymmetricMass S : ℝ) - 1 / Real.pi * (S * Real.log S)| ≤ 1 / 500 * (S * Real.log S))
    (hT500 : 500 ≤ T) (hTT0 : T₀ ≤ T) :
    4 / 100 * (T * Real.log T) ≤ ((xiCopiesBand (6 / 5 * T) (7 / 5 * T)).card : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hlogT : 6 ≤ Real.log T := six_le_log_of_fiveHundred_le hT500
  have hTlog : 0 ≤ T * Real.log T := mul_nonneg hTpos.le (by linarith)
  have hpi_lo : 1 / 3.15 < 1 / Real.pi := one_div_lt_one_div_of_lt Real.pi_pos Real.pi_lt_d2
  have hcard := card_xiCopiesBand_eq_real (by positivity : (0 : ℝ) ≤ 6 / 5 * T)
    (by linarith : 6 / 5 * T ≤ 7 / 5 * T)
  rw [hcard]
  have h7 := (abs_le.mp (hclose (7 / 5 * T) (by linarith))).1
  have h6 := (abs_le.mp (hclose (6 / 5 * T) (by linarith))).2
  have hlog7 : Real.log T ≤ Real.log (7 / 5 * T) := Real.log_le_log hTpos (by linarith)
  have hlog6 : Real.log (6 / 5 * T) ≤ 31 / 30 * Real.log T := by
    rw [Real.log_mul (by norm_num) hTpos.ne']
    have : Real.log (6 / 5 : ℝ) ≤ 6 / 5 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hS7 : 7 / 5 * (T * Real.log T) ≤ 7 / 5 * T * Real.log (7 / 5 * T) := by
    have := mul_le_mul_of_nonneg_left hlog7 (by positivity : (0 : ℝ) ≤ 7 / 5 * T)
    linarith
  have hS6 : 6 / 5 * T * Real.log (6 / 5 * T) ≤ 6 / 5 * (31 / 30) * (T * Real.log T) := by
    have := mul_le_mul_of_nonneg_left hlog6 (by positivity : (0 : ℝ) ≤ 6 / 5 * T)
    linarith
  have hε7 : 0 ≤ 1 / Real.pi - 1 / 500 := by
    have : (1 / 500 : ℝ) ≤ 1 / 3.15 := by norm_num
    linarith
  have hε6 : 0 ≤ 1 / Real.pi + 1 / 500 := by positivity
  have hM7 : (1 / Real.pi - 1 / 500) * (7 / 5 * (T * Real.log T)) ≤
      (xiSymmetricMass (7 / 5 * T) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hS7 hε7
    linarith
  have hM6 : (xiSymmetricMass (6 / 5 * T) : ℝ) ≤
      (1 / Real.pi + 1 / 500) * (6 / 5 * (31 / 30) * (T * Real.log T)) := by
    have := mul_le_mul_of_nonneg_left hS6 hε6
    linarith
  have hpiT : 1 / 3.15 * (T * Real.log T) ≤ 1 / Real.pi * (T * Real.log T) :=
    mul_le_mul_of_nonneg_right hpi_lo.le hTlog
  have hnum : (4 / 100 : ℝ) * (T * Real.log T) ≤
      (7 / 5 - 6 / 5 * (31 / 30)) * (1 / 3.15 * (T * Real.log T)) -
        (7 / 5 + 6 / 5 * (31 / 30)) * (1 / 500 * (T * Real.log T)) := by
    have : (4 / 100 : ℝ) ≤ (7 / 5 - 6 / 5 * (31 / 30)) * (1 / 3.15) -
        (7 / 5 + 6 / 5 * (31 / 30)) * (1 / 500) := by norm_num
    nlinarith
  nlinarith

/-! ## Generic assembly -/

/-- A summable real family whose negative part lives on a finite set `B`, with a finite band `A`
whose positive contribution dominates `B` by the stated count and constant margins, has
nonnegative total sum. -/
theorem tsum_nonneg_of_band_dominates {f : XiZeroCopy → ℝ} (hf : Summable f)
    {B A : Finset XiZeroCopy} (hdisj : Disjoint B A) {α β X : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hX : 0 ≤ X) (hA : ∀ q ∈ A, α ≤ f q) (hB : ∀ q ∈ B, -β ≤ f q)
    (htail : ∀ q, q ∉ B ∪ A → 0 ≤ f q) (hBcard : (B.card : ℝ) ≤ 33 / 100 * X)
    (hAcard : 4 / 100 * X ≤ (A.card : ℝ)) (hβα : β ≤ α / 9) :
    0 ≤ ∑' q, f q := by
  classical
  have hsplit := hf.sum_add_tsum_subtype_compl (B ∪ A)
  rw [← hsplit, Finset.sum_union hdisj]
  have htail' : 0 ≤ ∑' (q : {q // q ∉ B ∪ A}), f q.1 := tsum_nonneg fun q => htail q.1 q.2
  have hBsum : -((B.card : ℝ) * β) ≤ ∑ q ∈ B, f q := by
    have h := Finset.card_nsmul_le_sum B f (-β) hB
    rw [nsmul_eq_mul] at h
    linarith
  have hAsum : (A.card : ℝ) * α ≤ ∑ q ∈ A, f q := by
    have h := Finset.card_nsmul_le_sum A f α hA
    rw [nsmul_eq_mul] at h
    exact h
  have h1 : (B.card : ℝ) * β ≤ 33 / 100 * X * β := mul_le_mul_of_nonneg_right hBcard hβ
  have h2 : 33 / 100 * X * β ≤ 33 / 100 * X * (α / 9) :=
    mul_le_mul_of_nonneg_left hβα (by positivity)
  have h3 : 4 / 100 * X * α ≤ (A.card : ℝ) * α := mul_le_mul_of_nonneg_right hAcard hα
  have h4 : 0 ≤ X * α := mul_nonneg hX hα
  linarith

/-! ## The main theorem -/

/-- **Fixed-order large-shift positivity of the calibrated Hausdorff tower.**  For every order
`k`, all sufficiently large shifts `r` give a nonnegative endpoint-calibrated Hausdorff difference
of the normalized prime–archimedean moments, unconditionally. -/
theorem exists_forall_scaledHausdorffMomentDifference_nonneg (k : ℕ) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment k r := by
  classical
  have hR : 0 < primeArchEndpointHausdorffRadius := primeArchEndpointHausdorffRadius_pos
  set K : ℝ := 10 * ((k + 1 : ℕ) : ℝ) + 20 with hK_def
  have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have hK1 : 1 ≤ K := by rw [hK_def]; linarith
  have hK10 : 10 * ((k + 1 : ℕ) : ℝ) ≤ K := by rw [hK_def]; linarith
  obtain ⟨T₀, hT₀4, hclose⟩ := exists_xiSymmetricMass_close (1 / 500) (by norm_num)
  set Tstar : ℝ := max T₀ (max 500 (42 * ((k + 1 : ℕ) : ℝ) + 44 * K)) with hTstar_def
  have hTstar0 : 0 ≤ Tstar := le_trans (by linarith) (le_max_left _ _)
  refine ⟨⌈20 * K⌉₊ + ⌈K * primeArchEndpointHausdorffRadius * Tstar ^ 2⌉₊ + 1, fun r hr => ?_⟩
  have hr' : ((⌈20 * K⌉₊ + ⌈K * primeArchEndpointHausdorffRadius * Tstar ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ r := by
    exact_mod_cast hr
  push_cast at hr'
  have hc1 := Nat.le_ceil (20 * K)
  have hc2 := Nat.le_ceil (K * primeArchEndpointHausdorffRadius * Tstar ^ 2)
  have hc1' : (0 : ℝ) ≤ (⌈20 * K⌉₊ : ℝ) := by positivity
  have hc2' : (0 : ℝ) ≤ (⌈K * primeArchEndpointHausdorffRadius * Tstar ^ 2⌉₊ : ℝ) := by
    positivity
  have hr20 : 20 * K ≤ (r : ℝ) := by linarith
  have hrT : K * primeArchEndpointHausdorffRadius * Tstar ^ 2 < (r : ℝ) := by linarith
  have hrpos : 0 < (r : ℝ) := by linarith
  have hKR : 0 < K * primeArchEndpointHausdorffRadius := by positivity
  set T : ℝ := Real.sqrt ((r : ℝ) / (K * primeArchEndpointHausdorffRadius)) with hT_def
  have hT2 : T ^ 2 = r / (K * primeArchEndpointHausdorffRadius) := Real.sq_sqrt (by positivity)
  have hTpos : 0 < T := Real.sqrt_pos.mpr (by positivity)
  have hΛ : K * primeArchEndpointHausdorffRadius / r = 1 / T ^ 2 := by
    rw [hT2]
    field_simp
  have hTstar : Tstar ≤ T := by
    rw [hT_def, ← Real.sqrt_sq hTstar0]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hKR]
    linarith
  have hT500 : 500 ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTstar
  have hT10 : 10 ≤ T := by linarith
  have hTK : 42 * ((k + 1 : ℕ) : ℝ) + 44 * K ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTstar
  have hTT0 : T₀ ≤ T := le_trans (le_max_left _ _) hTstar
  -- the array value as a real series over the atoms
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum]
  have hsum : Summable (fun q => hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q) :=
    summable_xiCentralScaledHausdorffTerm primeArchEndpointHausdorffRadius k r
  have hfsum : Summable (fun q => (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re) :=
    ⟨_, Complex.hasSum_re hsum.hasSum⟩
  change 0 ≤ (∑' q, hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re
  rw [Complex.re_tsum hsum]
  -- the two finite families
  set B : Finset XiZeroCopy :=
    (xiCopiesBand 0 T).filter (fun q => 1 / T ^ 2 < xiThermalNode q) with hB_def
  set A : Finset XiZeroCopy := xiCopiesBand (6 / 5 * T) (7 / 5 * T) with hA_def
  have hmemB : ∀ q, 1 / T ^ 2 < xiThermalNode q → q ∈ B := by
    intro q hq
    rw [hB_def, Finset.mem_filter, mem_xiCopiesBand]
    exact ⟨⟨abs_pos.mpr (xiSupport_im_ne_zero q.1),
      (abs_ordinate_lt_of_inv_sq_lt_xiThermalNode hTpos hq).le⟩, hq⟩
  have hB_node : ∀ q ∈ B, 1 / T ^ 2 < xiThermalNode q := fun q hq =>
    (Finset.mem_filter.mp hq).2
  have hB_ord : ∀ q ∈ B, |(q.1 : ℂ).im| ≤ T := fun q hq =>
    (mem_xiCopiesBand.mp (Finset.mem_filter.mp hq).1).2
  have hA_node : ∀ q ∈ A, xiThermalNode q ≤ 1 / T ^ 2 := by
    intro q hq
    rw [hA_def, mem_xiCopiesBand] at hq
    have h := (xiThermalNode_mem_of_ordinate_band hT10 hq.1 hq.2).2
    exact h.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  have hdisj : Disjoint B A := by
    rw [Finset.disjoint_left]
    intro q hqB hqA
    exact absurd (hA_node q hqA) (not_le.mpr (hB_node q hqB))
  -- per-atom bounds
  set α : ℝ := 1 / 2 * (49 / 100 * (1 / T ^ 2)) ^ (k + 1) *
    primeArchEndpointHausdorffRadius ^ r * Real.exp (-(3 / 4 * K)) with hα
  set β : ℝ := (41 / 10 * (1 / T ^ 2)) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r *
    Real.exp (-(99 / 100 * K)) with hβ
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  have hA_term : ∀ q ∈ A, α ≤ (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re := by
    intro q hq
    rw [hA_def, mem_xiCopiesBand] at hq
    exact band_re_hausdorffAtomTerm_ge k r hR hK1 hr20 hT10 hTK hΛ hq.1 hq.2
  have hB_term : ∀ q ∈ B, -β ≤ (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re := by
    intro q hq
    have h := norm_hausdorffAtomTerm_le_of_threshold_lt k r hR hK10 hK1 hr20 hT500 hΛ
      (xiThermalNode_le_primeArchEndpointHausdorffRadius q) (hB_node q hq)
    have h2 := neg_norm_le_re' (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q)
    linarith
  have htail : ∀ q, q ∉ B ∪ A →
      0 ≤ (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q).re := by
    intro q hq
    have hqB : q ∉ B := fun h => hq (Finset.mem_union_left _ h)
    have hle : xiThermalNode q ≤ 1 / T ^ 2 := by
      by_contra hlt
      exact hqB (hmemB q (not_le.mp hlt))
    have h := half_norm_le_re_of_node_le_threshold k r hR hK1 hr20 hT10 hTK hΛ hle
    have h2 := norm_nonneg (hausdorffAtomTerm primeArchEndpointHausdorffRadius k r q)
    linarith
  -- counts and the constant margin
  have hBcard := card_le_of_mass_close hclose hT500 hTT0 hB_ord
  have hAcard := band_card_ge_of_mass_close hclose hT500 hTT0
  have hβα : β ≤ α / 9 := by
    have h := threshold_constant_le_band_constant k
    rw [← hK_def] at h
    rw [hβ, hα]
    have hpos : 0 ≤ (1 / T ^ 2) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r := by
      positivity
    calc (41 / 10 * (1 / T ^ 2)) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r *
          Real.exp (-(99 / 100 * K))
        = ((41 / 10) ^ (k + 1) * Real.exp (-(99 / 100 * K))) *
            ((1 / T ^ 2) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r) := by
          rw [mul_pow]
          ring
      _ ≤ (1 / 9 * (1 / 2 * (49 / 100) ^ (k + 1) * Real.exp (-(3 / 4 * K)))) *
            ((1 / T ^ 2) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r) := by
          gcongr
      _ = 1 / 2 * (49 / 100 * (1 / T ^ 2)) ^ (k + 1) * primeArchEndpointHausdorffRadius ^ r *
            Real.exp (-(3 / 4 * K)) / 9 := by
          rw [mul_pow]
          ring
  have hTlog : 0 ≤ T * Real.log T :=
    mul_nonneg hTpos.le (Real.log_nonneg (by linarith))
  exact tsum_nonneg_of_band_dominates hfsum hdisj hα0 hβ0 hTlog hA_term hB_term htail hBcard
    hAcard hβα

/-- Filter form: every row of the calibrated Hausdorff tower is eventually nonnegative. -/
theorem eventually_scaledHausdorffMomentDifference_nonneg (k : ℕ) :
    ∀ᶠ r : ℕ in atTop,
      0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment k r := by
  obtain ⟨r₀, h⟩ := exists_forall_scaledHausdorffMomentDifference_nonneg k
  exact eventually_atTop.mpr ⟨r₀, h⟩

/-! ## Consequences: bounded shifts carry RH; low-index Bernstein masses are eventually positive -/

/-- The shift threshold of order `k`: at and beyond it, row `k` of the calibrated Hausdorff tower is
nonnegative. -/
def primeArchHausdorffShiftThreshold (k : ℕ) : ℕ :=
  Classical.choose (exists_forall_scaledHausdorffMomentDifference_nonneg k)

theorem scaledHausdorffMomentDifference_nonneg_of_shiftThreshold_le (k r : ℕ)
    (hr : primeArchHausdorffShiftThreshold k ≤ r) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r :=
  Classical.choose_spec (exists_forall_scaledHausdorffMomentDifference_nonneg k) r hr

/-- **RH is carried by bounded shifts.**  The complete calibrated Hausdorff criterion reduces to the
differences below the shift threshold of each order; the unbounded-shift direction is unconditional. -/
theorem riemannHypothesis_iff_forall_lt_shiftThreshold_nonneg :
    RiemannHypothesis ↔
      ∀ k r : ℕ, r < primeArchHausdorffShiftThreshold k →
        0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment k r := by
  constructor
  · intro hRH k r _
    exact scaledPrimeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis hRH k r
  · intro h
    apply riemannHypothesis_of_scaledPrimeArchHausdorffMomentDifferencesNonnegative
      primeArchEndpointHausdorffRadius_pos
    intro k r
    by_cases hr : primeArchHausdorffShiftThreshold k ≤ r
    · exact scaledHausdorffMomentDifference_nonneg_of_shiftThreshold_le k r hr
    · exact h k r (not_le.mp hr)

/-- **Eventual positivity of each Bernstein mass.**  For every index `i`, the `i`-th Bernstein
coefficient of the endpoint-normalized prime–archimedean source is nonnegative at every sufficiently
large degree. -/
theorem eventually_bernsteinCoefficient_endpoint_nonneg (i : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      0 ≤ bernsteinCoefficient
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n i := by
  obtain ⟨r₀, h⟩ := exists_forall_scaledHausdorffMomentDifference_nonneg i
  rw [eventually_atTop]
  refine ⟨i + r₀, fun n hn => ?_⟩
  have hR := primeArchEndpointHausdorffRadius_pos
  rw [bernsteinCoefficient, bernsteinPolynomial]
  rw [show ((n.choose i : ℕ) : Polynomial ℝ) * Polynomial.X ^ i * (1 - Polynomial.X) ^ (n - i) =
      (n.choose i : ℝ) • (Polynomial.X ^ i * (1 - Polynomial.X) ^ (n - i)) by
    simp [Polynomial.smul_eq_C_mul]
    ring]
  rw [HTGeometry.momentFunctional_smul, ← hausdorffMomentDifference_eq_momentFunctional,
    hausdorffMomentDifference_radiusNormalizedMoment hR]
  apply mul_nonneg (Nat.cast_nonneg _)
  apply div_nonneg _ (pow_nonneg hR.le _)
  exact h (n - i) (by omega)

end

end RHTower
