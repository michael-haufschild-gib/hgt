import GaloisForLFunctions.RHTower.JointAncestryExplicitSectorBlindBand

/-!
# JAS explicit-formula sectors are measures exactly on the critical line

The local explicit-formula density on a prime circle is
`ℓ_{a,b}(θ) = (1 - a e(θ))⁻¹ + (1 - b ē(θ))⁻¹ - 1`, with Fourier coefficients `a^k` at `k ≥ 0` and
`b^{|k|}` at `k ≤ 0`.  In particular `∫ ℓ = 1`, `ℓ̂(1) = a` and `ℓ̂(-1) = b`.

**Total-variation excess.**  The function `ℓ - ℓ̄ = 2i Im ℓ` has first Fourier coefficient
`a - b̄`, so `‖a - b̄‖ ≤ 2 ∫ |Im ℓ|`.  Pointwise `(Im ℓ)² ≤ 2M(|ℓ| - Re ℓ)` when `|ℓ| ≤ M`, and on the
probability circle `(∫|Im ℓ|)² ≤ ∫ (Im ℓ)²`.  Hence

`∫ |ℓ| ≥ 1 + ‖a - b̄‖² / (8M)`.

For the prime parameters `a = p^{-s}`, `b = p^{-(1-s)}` one has `‖a - b̄‖ = |p^{-σ} - p^{σ-1}|`, and
off the critical line `|p^{-σ} - p^{σ-1}|² ≥ c/p`.  The total variation of the depth-`P` density is
the product of the local total variations, so it is at least `1 + κ Σ_{p ∈ P} 1/p`, which is
unbounded.  On the critical line the density is a probability density at every depth.

Thus the explicit-formula sector of a strip point has bounded marginal total variation, i.e. is a
genuine measure on the prime torus, exactly on the critical line.  The divergence used is the
quadratic Kakutani divergence `Σ_p (p^{-σ} - p^{σ-1})² = ∞` that also drives prime-Poisson
superselection; off the line the explicit-formula sector is a distribution of infinite total
variation.
-/

open Complex MeasureTheory Filter
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-- The normalized Haar probability measure on the unit additive circle. -/
abbrev jasCircleHaar : Measure UnitAddCircle := AddCircle.haarAddCircle

/-- Local explicit-formula density as a function on the unit additive circle. -/
def jasHoloCircle (a b : ℂ) (θ : UnitAddCircle) : ℂ := jasHoloLocal a b (fourier 1 θ)

theorem norm_fourier_unit (n : ℤ) (θ : UnitAddCircle) : ‖fourier n θ‖ = 1 := by simp

theorem fourier_natCast_eq_pow (j : ℕ) (θ : UnitAddCircle) :
    fourier (j : ℤ) θ = fourier 1 θ ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.cast_succ, fourier_add, ih, pow_succ]

theorem norm_inv_one_sub_le {z : ℂ} (hz : ‖z‖ < 1) : ‖(1 - z)⁻¹‖ ≤ 1 / (1 - ‖z‖) := by
  rw [norm_inv, one_div]
  apply inv_anti₀ (by linarith)
  have := norm_sub_norm_le (1 : ℂ) z
  rw [norm_one] at this
  linarith

theorem one_sub_mul_fourier_ne_zero {a : ℂ} (ha : ‖a‖ < 1) (θ : UnitAddCircle) :
    1 - a * fourier 1 θ ≠ 0 := by
  intro h
  have h1 : a * fourier 1 θ = 1 := by linear_combination -h
  have := congrArg norm h1
  rw [norm_mul, norm_fourier_unit, mul_one, norm_one] at this
  linarith

theorem continuous_inv_one_sub_mul_fourier {a : ℂ} (ha : ‖a‖ < 1) :
    Continuous fun θ : UnitAddCircle => (1 - a * fourier 1 θ)⁻¹ :=
  (continuous_const.sub (continuous_const.mul (fourier 1).continuous)).inv₀
    (one_sub_mul_fourier_ne_zero ha)

theorem hasSum_inv_one_sub_mul_fourier {a : ℂ} (ha : ‖a‖ < 1) (θ : UnitAddCircle) :
    HasSum (fun j : ℕ => a ^ j * fourier (j : ℤ) θ) (1 - a * fourier 1 θ)⁻¹ := by
  have h := hasSum_geometric_of_norm_lt_one
    (ξ := a * fourier 1 θ) (by rw [norm_mul, norm_fourier_unit, mul_one]; exact ha)
  refine h.congr_fun fun j => ?_
  rw [fourier_natCast_eq_pow, mul_pow]

/-- Fourier coefficients of the holomorphic Cauchy factor: `∫ e(-kθ) (1 - a e(θ))⁻¹ = a^k`
for `k ≥ 0` and `0` for `k < 0`. -/
theorem integral_fourier_mul_inv_one_sub {a : ℂ} (ha : ‖a‖ < 1) (k : ℤ) :
    ∫ θ, fourier (-k) θ * (1 - a * fourier 1 θ)⁻¹ ∂jasCircleHaar =
      ∑' j : ℕ, a ^ j * (Pi.single (j : ℤ) (1 : ℂ) : ℤ → ℂ) k := by
  have hsum : ∀ θ, HasSum (fun j : ℕ => fourier (-k) θ * (a ^ j * fourier (j : ℤ) θ))
      (fourier (-k) θ * (1 - a * fourier 1 θ)⁻¹) :=
    fun θ => (hasSum_inv_one_sub_mul_fourier ha θ).mul_left _
  have hint : ∀ j : ℕ, ∫ θ, fourier (-k) θ * (a ^ j * fourier (j : ℤ) θ) ∂jasCircleHaar =
      a ^ j * (Pi.single (j : ℤ) (1 : ℂ) : ℤ → ℂ) k := by
    intro j
    have hc := congrFun (fourierCoeff_fourier (T := 1) (j : ℤ)) k
    rw [fourierCoeff] at hc
    simp only [smul_eq_mul] at hc
    rw [← hc, ← integral_const_mul]
    congr 1; funext θ; ring
  calc ∫ θ, fourier (-k) θ * (1 - a * fourier 1 θ)⁻¹ ∂jasCircleHaar
      = ∫ θ, ∑' j : ℕ, fourier (-k) θ * (a ^ j * fourier (j : ℤ) θ) ∂jasCircleHaar := by
        congr 1; funext θ; exact (hsum θ).tsum_eq.symm
    _ = ∑' j : ℕ, ∫ θ, fourier (-k) θ * (a ^ j * fourier (j : ℤ) θ) ∂jasCircleHaar := by
        apply integral_tsum
        · intro j
          exact ((fourier (-k)).continuous.mul (continuous_const.mul
            (fourier (j : ℤ)).continuous)).aestronglyMeasurable
        · have hterm : ∀ j : ℕ, ∫⁻ θ, ‖fourier (-k) θ * (a ^ j * fourier (j : ℤ) θ)‖ₑ
              ∂jasCircleHaar = ‖a‖ₑ ^ j := by
            intro j
            have : ∀ θ : UnitAddCircle,
                ‖fourier (-k) θ * (a ^ j * fourier (j : ℤ) θ)‖ₑ = ‖a‖ₑ ^ j := by
              intro θ
              rw [enorm_mul, enorm_mul, enorm_pow]
              have h1 : ‖fourier (-k) θ‖ₑ = 1 := by
                rw [← ofReal_norm, norm_fourier_unit]; simp
              have h2 : ‖fourier (j : ℤ) θ‖ₑ = 1 := by
                rw [← ofReal_norm, norm_fourier_unit]; simp
              rw [h1, h2, one_mul, mul_one]
            simp_rw [this]
            rw [lintegral_const, measure_univ, mul_one]
          simp_rw [hterm]
          rw [ENNReal.tsum_geometric]
          apply ENNReal.inv_ne_top.mpr
          rw [ne_eq, tsub_eq_zero_iff_le, not_le]
          rw [← ofReal_norm]
          exact ENNReal.ofReal_lt_one.mpr ha
    _ = ∑' j : ℕ, a ^ j * (Pi.single (j : ℤ) (1 : ℂ) : ℤ → ℂ) k := by
        simp_rw [hint]

theorem integral_inv_one_sub_mul_fourier {a : ℂ} (ha : ‖a‖ < 1) :
    ∫ θ, (1 - a * fourier 1 θ)⁻¹ ∂jasCircleHaar = 1 := by
  have h := integral_fourier_mul_inv_one_sub ha 0
  simp only [neg_zero, fourier_zero, one_mul] at h
  rw [h, tsum_eq_single 0]
  · simp
  · intro j hj
    rw [Pi.single_apply, if_neg (fun h => hj (by exact_mod_cast h.symm))]
    ring

theorem integral_fourier_neg_one_mul_inv_one_sub {a : ℂ} (ha : ‖a‖ < 1) :
    ∫ θ, fourier (-1) θ * (1 - a * fourier 1 θ)⁻¹ ∂jasCircleHaar = a := by
  rw [integral_fourier_mul_inv_one_sub ha 1, tsum_eq_single 1]
  · simp
  · intro j hj
    rw [Pi.single_apply, if_neg (fun h => hj (by exact_mod_cast h.symm))]
    ring

theorem integral_fourier_one_mul_inv_one_sub {a : ℂ} (ha : ‖a‖ < 1) :
    ∫ θ, fourier 1 θ * (1 - a * fourier 1 θ)⁻¹ ∂jasCircleHaar = 0 := by
  have h := integral_fourier_mul_inv_one_sub ha (-1)
  rw [neg_neg] at h
  rw [h]
  have hz : ∀ j : ℕ, a ^ j * (Pi.single (j : ℤ) (1 : ℂ) : ℤ → ℂ) (-1) = 0 := by
    intro j
    rw [Pi.single_apply, if_neg (by omega)]
    ring
  simp_rw [hz, tsum_zero]

/-- The antiholomorphic factor is the conjugate of a holomorphic one. -/
theorem inv_one_sub_mul_conj_fourier (b : ℂ) (θ : UnitAddCircle) :
    (1 - b * conj (fourier 1 θ))⁻¹ = conj ((1 - conj b * fourier 1 θ)⁻¹) := by
  rw [map_inv₀, map_sub, map_one, map_mul, Complex.conj_conj]

theorem integral_inv_one_sub_mul_conj_fourier {b : ℂ} (hb : ‖b‖ < 1) :
    ∫ θ, (1 - b * conj (fourier 1 θ))⁻¹ ∂jasCircleHaar = 1 := by
  simp_rw [inv_one_sub_mul_conj_fourier]
  rw [integral_conj, integral_inv_one_sub_mul_fourier (by rwa [Complex.norm_conj]), map_one]

theorem integral_fourier_neg_one_mul_inv_one_sub_conj {b : ℂ} (hb : ‖b‖ < 1) :
    ∫ θ, fourier (-1) θ * (1 - b * conj (fourier 1 θ))⁻¹ ∂jasCircleHaar = 0 := by
  have : ∀ θ : UnitAddCircle, fourier (-1) θ * (1 - b * conj (fourier 1 θ))⁻¹ =
      conj (fourier 1 θ * (1 - conj b * fourier 1 θ)⁻¹) := by
    intro θ
    rw [inv_one_sub_mul_conj_fourier, map_mul, fourier_neg]
  simp_rw [this]
  rw [integral_conj, integral_fourier_one_mul_inv_one_sub (by rwa [Complex.norm_conj]), map_zero]

theorem integral_fourier_one_mul_inv_one_sub_conj {b : ℂ} (hb : ‖b‖ < 1) :
    ∫ θ, fourier 1 θ * (1 - b * conj (fourier 1 θ))⁻¹ ∂jasCircleHaar = b := by
  have : ∀ θ : UnitAddCircle, fourier 1 θ * (1 - b * conj (fourier 1 θ))⁻¹ =
      conj (fourier (-1) θ * (1 - conj b * fourier 1 θ)⁻¹) := by
    intro θ
    rw [inv_one_sub_mul_conj_fourier, map_mul, fourier_neg, Complex.conj_conj]
  simp_rw [this]
  rw [integral_conj, integral_fourier_neg_one_mul_inv_one_sub (by rwa [Complex.norm_conj]),
    Complex.conj_conj]

theorem continuous_jasHoloCircle {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Continuous (jasHoloCircle a b) := by
  have h2 : Continuous fun θ : UnitAddCircle => (1 - b * conj (fourier 1 θ))⁻¹ := by
    simp_rw [inv_one_sub_mul_conj_fourier]
    exact Complex.continuous_conj.comp
      (continuous_inv_one_sub_mul_fourier (by rwa [Complex.norm_conj]))
  unfold jasHoloCircle jasHoloLocal
  exact ((continuous_inv_one_sub_mul_fourier ha).add h2).sub continuous_const

theorem integrable_of_continuous_circle {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    Integrable f jasCircleHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The local explicit-formula density has total mass one. -/
theorem integral_jasHoloCircle {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ∫ θ, jasHoloCircle a b θ ∂jasCircleHaar = 1 := by
  have h2c : Continuous fun θ : UnitAddCircle => (1 - b * conj (fourier 1 θ))⁻¹ := by
    simp_rw [inv_one_sub_mul_conj_fourier]
    exact Complex.continuous_conj.comp
      (continuous_inv_one_sub_mul_fourier (by rwa [Complex.norm_conj]))
  unfold jasHoloCircle jasHoloLocal
  rw [integral_sub, integral_add, integral_inv_one_sub_mul_fourier ha,
    integral_inv_one_sub_mul_conj_fourier hb, integral_const]
  · simp
  · exact integrable_of_continuous_circle (continuous_inv_one_sub_mul_fourier ha)
  · exact integrable_of_continuous_circle h2c
  · exact integrable_of_continuous_circle ((continuous_inv_one_sub_mul_fourier ha).add h2c)
  · exact integrable_const _

/-- The first Fourier coefficient of `ℓ - ℓ̄` is `a - b̄`. -/
theorem integral_fourier_neg_one_mul_sub_conj_jasHoloCircle {a b : ℂ} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    ∫ θ, fourier (-1) θ * (jasHoloCircle a b θ - conj (jasHoloCircle a b θ)) ∂jasCircleHaar =
      a - conj b := by
  have hc := continuous_jasHoloCircle ha hb
  have h2c : Continuous fun θ : UnitAddCircle => (1 - b * conj (fourier 1 θ))⁻¹ := by
    simp_rw [inv_one_sub_mul_conj_fourier]
    exact Complex.continuous_conj.comp
      (continuous_inv_one_sub_mul_fourier (by rwa [Complex.norm_conj]))
  have hf := (fourier (-1 : ℤ)).continuous (X := UnitAddCircle)
  have h1 : ∫ θ, fourier (-1) θ * jasHoloCircle a b θ ∂jasCircleHaar = a := by
    unfold jasHoloCircle jasHoloLocal
    simp_rw [mul_sub, mul_add, mul_one]
    rw [integral_sub, integral_add, integral_fourier_neg_one_mul_inv_one_sub ha,
      integral_fourier_neg_one_mul_inv_one_sub_conj hb]
    · have h0 := congrFun (fourierCoeff_fourier (T := 1) (0 : ℤ)) 1
      rw [fourierCoeff] at h0
      simp only [smul_eq_mul, fourier_zero, mul_one] at h0
      rw [h0]; simp
    · exact integrable_of_continuous_circle (hf.mul (continuous_inv_one_sub_mul_fourier ha))
    · exact integrable_of_continuous_circle (hf.mul h2c)
    · exact integrable_of_continuous_circle
        ((hf.mul (continuous_inv_one_sub_mul_fourier ha)).add (hf.mul h2c))
    · exact integrable_of_continuous_circle hf
  have h2 : ∫ θ, fourier (-1) θ * conj (jasHoloCircle a b θ) ∂jasCircleHaar = conj b := by
    have : ∀ θ, fourier (-1) θ * conj (jasHoloCircle a b θ) =
        conj (fourier 1 θ * jasHoloCircle a b θ) := by
      intro θ; rw [map_mul, fourier_neg]
    simp_rw [this]
    rw [integral_conj]
    congr 1
    unfold jasHoloCircle jasHoloLocal
    have hf1 := (fourier (1 : ℤ)).continuous (X := UnitAddCircle)
    simp_rw [mul_sub, mul_add, mul_one]
    rw [integral_sub, integral_add, integral_fourier_one_mul_inv_one_sub ha,
      integral_fourier_one_mul_inv_one_sub_conj hb]
    · have h0 := congrFun (fourierCoeff_fourier (T := 1) (0 : ℤ)) (-1)
      rw [fourierCoeff] at h0
      simp only [smul_eq_mul, fourier_zero, mul_one, neg_neg] at h0
      rw [h0]; simp
    · exact integrable_of_continuous_circle (hf1.mul (continuous_inv_one_sub_mul_fourier ha))
    · exact integrable_of_continuous_circle (hf1.mul h2c)
    · exact integrable_of_continuous_circle
        ((hf1.mul (continuous_inv_one_sub_mul_fourier ha)).add (hf1.mul h2c))
    · exact integrable_of_continuous_circle hf1
  simp_rw [mul_sub]
  rw [integral_sub, h1, h2]
  · exact integrable_of_continuous_circle (hf.mul hc)
  · exact integrable_of_continuous_circle (hf.mul (Complex.continuous_conj.comp hc))

/-- Pointwise: `(Im z)² ≤ 2M(|z| - Re z)` whenever `|z| ≤ M`. -/
theorem im_sq_le_two_mul_norm_sub_re {z : ℂ} {M : ℝ} (hz : ‖z‖ ≤ M) :
    z.im ^ 2 ≤ 2 * M * (‖z‖ - z.re) := by
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hre' : -‖z‖ ≤ z.re := by have := Complex.abs_re_le_norm z; linarith [neg_abs_le z.re]
  have h1 : z.im ^ 2 = (‖z‖ - z.re) * (‖z‖ + z.re) := by nlinarith
  rw [h1]
  have : ‖z‖ + z.re ≤ 2 * M := by linarith
  nlinarith

/-- **Total-variation excess of a local explicit-formula density.** -/
theorem one_add_le_integral_norm_jasHoloCircle {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    {M : ℝ} (hM : ∀ θ, ‖jasHoloCircle a b θ‖ ≤ M) (hM0 : 0 < M) :
    1 + ‖a - conj b‖ ^ 2 / (8 * M) ≤ ∫ θ, ‖jasHoloCircle a b θ‖ ∂jasCircleHaar := by
  have hc := continuous_jasHoloCircle ha hb
  set f := jasHoloCircle a b with hfdef
  have hInorm : Integrable (fun θ => ‖f θ‖) jasCircleHaar :=
    (integrable_of_continuous_circle hc).norm
  have hIre : Integrable (fun θ => (f θ).re) jasCircleHaar :=
    (integrable_of_continuous_circle hc).re
  have hIim : Integrable (fun θ => |(f θ).im|) jasCircleHaar :=
    (integrable_of_continuous_circle hc).im.abs
  have hIim2 : Integrable (fun θ => (f θ).im ^ 2) jasCircleHaar := by
    have : Continuous fun θ => (f θ).im ^ 2 := (Complex.continuous_im.comp hc).pow 2
    exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- mass one
  have hmass : ∫ θ, (f θ).re ∂jasCircleHaar = 1 := by
    have h := integral_re (integrable_of_continuous_circle hc)
    simp only [RCLike.re_to_complex] at h
    rw [h, hfdef, integral_jasHoloCircle ha hb]
    simp
  -- first coefficient bound
  have hcoef : ‖a - conj b‖ ≤ 2 * ∫ θ, |(f θ).im| ∂jasCircleHaar := by
    rw [← integral_fourier_neg_one_mul_sub_conj_jasHoloCircle ha hb]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun θ => norm_nonneg _
    · exact hIim.const_mul 2
    · refine Eventually.of_forall fun θ => ?_
      simp only
      rw [norm_mul, norm_fourier_unit, one_mul, Complex.sub_conj, norm_mul, Complex.norm_real,
        Complex.norm_I, mul_one, Real.norm_eq_abs, abs_mul, abs_two]
  -- Jensen on the probability circle
  have hjensen : (∫ θ, |(f θ).im| ∂jasCircleHaar) ^ 2 ≤
      ∫ θ, (f θ).im ^ 2 ∂jasCircleHaar := by
    set c := ∫ θ, |(f θ).im| ∂jasCircleHaar
    have hnonneg : 0 ≤ ∫ θ, (|(f θ).im| - c) ^ 2 ∂jasCircleHaar :=
      integral_nonneg fun θ => sq_nonneg _
    have hexp : ∫ θ, (|(f θ).im| - c) ^ 2 ∂jasCircleHaar =
        ∫ θ, (f θ).im ^ 2 ∂jasCircleHaar - c ^ 2 := by
      have hpt : ∀ θ, (|(f θ).im| - c) ^ 2 = (f θ).im ^ 2 - 2 * c * |(f θ).im| + c ^ 2 := by
        intro θ; rw [sub_sq, sq_abs]; ring
      simp_rw [hpt]
      rw [integral_add, integral_sub, integral_const_mul, integral_const]
      · simp; ring
      · exact hIim2
      · exact hIim.const_mul _
      · exact hIim2.sub (hIim.const_mul _)
      · exact integrable_const _
    linarith
  -- pointwise excess
  have hpt : ∫ θ, (f θ).im ^ 2 ∂jasCircleHaar ≤
      2 * M * (∫ θ, ‖f θ‖ ∂jasCircleHaar - 1) := by
    have hdiff : ∫ θ, (‖f θ‖ - (f θ).re) ∂jasCircleHaar = ∫ θ, ‖f θ‖ ∂jasCircleHaar - 1 := by
      rw [integral_sub hInorm hIre, hmass]
    rw [← hdiff, ← integral_const_mul]
    exact integral_mono hIim2 ((hInorm.sub hIre).const_mul _)
      fun θ => im_sq_le_two_mul_norm_sub_re (hM θ)
  have hsq : ‖a - conj b‖ ^ 2 ≤ 4 * ∫ θ, (f θ).im ^ 2 ∂jasCircleHaar := by
    have h0 : 0 ≤ ‖a - conj b‖ := norm_nonneg _
    nlinarith
  have : ‖a - conj b‖ ^ 2 / (8 * M) ≤ ∫ θ, ‖f θ‖ ∂jasCircleHaar - 1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem norm_jasHoloCircle_le {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (θ : UnitAddCircle) :
    ‖jasHoloCircle a b θ‖ ≤ 1 / (1 - ‖a‖) + 1 / (1 - ‖b‖) + 1 := by
  unfold jasHoloCircle jasHoloLocal
  have h1 := norm_inv_one_sub_le (z := a * fourier 1 θ)
    (by rw [norm_mul, norm_fourier_unit, mul_one]; exact ha)
  have h2 := norm_inv_one_sub_le (z := b * conj (fourier 1 θ))
    (by rw [norm_mul, Complex.norm_conj, norm_fourier_unit, mul_one]; exact hb)
  rw [norm_mul, norm_fourier_unit, mul_one] at h1
  rw [norm_mul, Complex.norm_conj, norm_fourier_unit, mul_one] at h2
  calc ‖(1 - a * fourier 1 θ)⁻¹ + (1 - b * conj (fourier 1 θ))⁻¹ - 1‖
      ≤ ‖(1 - a * fourier 1 θ)⁻¹‖ + ‖(1 - b * conj (fourier 1 θ))⁻¹‖ + ‖(1 : ℂ)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ _ := by rw [norm_one]; gcongr

/-! ## Prime parameters -/

theorem jasHoloA_sub_conj_jasHoloB_norm (s : ℂ) (p : Nat.Primes) :
    ‖jasHoloA s p - conj (jasHoloB s p)‖ = |jasR1 s p - jasR2 s p| := by
  have hA := jasHoloA_mul_eq s p 1
  have hB := jasHoloB_mul_conj_eq s p 1
  simp only [mul_one, map_one] at hA hB
  rw [hA, hB, map_mul, Complex.conj_ofReal, Complex.conj_conj, ← sub_mul, ← Complex.ofReal_sub,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Off the critical line the radius gap is at least `c/√p` in square: `|r₁ - r₂|² ≥ c/p`. -/
theorem exists_pos_inv_le_sq_jasR1_sub_jasR2 {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hoff : s.re ≠ 1 / 2) :
    ∃ c > 0, ∀ p : Nat.Primes, c * (p : ℝ)⁻¹ ≤ (jasR1 s p - jasR2 s p) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinvp : ∀ p : Nat.Primes, ((p : ℕ) : ℝ)⁻¹ = Real.exp (-Real.log p) := fun p => by
    rw [Real.exp_neg, Real.exp_log (by exact_mod_cast p.2.pos)]
  rcases lt_or_gt_of_ne hoff with hlt | hgt
  · set κ := 1 - Real.exp ((2 * s.re - 1) * Real.log 2) with hκ
    have hκ0 : 0 < κ := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    refine ⟨κ ^ 2, by positivity, fun p => ?_⟩
    have hp := log_prime_pos p
    have hp2 : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
    have hratio : jasR2 s p = jasR1 s p * Real.exp ((2 * s.re - 1) * Real.log p) := by
      rw [jasR1, jasR2, ← Real.exp_add]; congr 1; ring
    have hmono : Real.exp ((2 * s.re - 1) * Real.log p) ≤
        Real.exp ((2 * s.re - 1) * Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
    have hR1sq : ((p : ℕ) : ℝ)⁻¹ ≤ jasR1 s p ^ 2 := by
      rw [hinvp, jasR1, ← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by push_cast; nlinarith)
    have hgap : κ * jasR1 s p ≤ jasR1 s p - jasR2 s p := by
      rw [hratio, hκ]; nlinarith [jasR1_pos s p]
    have hκr : 0 ≤ κ * jasR1 s p := by have := jasR1_pos s p; positivity
    calc κ ^ 2 * ((p : ℕ) : ℝ)⁻¹ ≤ κ ^ 2 * jasR1 s p ^ 2 := by gcongr
      _ = (κ * jasR1 s p) ^ 2 := by ring
      _ ≤ (jasR1 s p - jasR2 s p) ^ 2 := by gcongr
  · set κ := 1 - Real.exp ((1 - 2 * s.re) * Real.log 2) with hκ
    have hκ0 : 0 < κ := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
    refine ⟨κ ^ 2, by positivity, fun p => ?_⟩
    have hp := log_prime_pos p
    have hp2 : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
    have hratio : jasR1 s p = jasR2 s p * Real.exp ((1 - 2 * s.re) * Real.log p) := by
      rw [jasR1, jasR2, ← Real.exp_add]; congr 1; ring
    have hmono : Real.exp ((1 - 2 * s.re) * Real.log p) ≤
        Real.exp ((1 - 2 * s.re) * Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
    have hR2sq : ((p : ℕ) : ℝ)⁻¹ ≤ jasR2 s p ^ 2 := by
      rw [hinvp, jasR2, ← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by push_cast; nlinarith)
    have hgap : κ * jasR2 s p ≤ jasR2 s p - jasR1 s p := by
      rw [hratio, hκ]; nlinarith [jasR2_pos s p]
    have hκr : 0 ≤ κ * jasR2 s p := by have := jasR2_pos s p; positivity
    calc κ ^ 2 * ((p : ℕ) : ℝ)⁻¹ ≤ κ ^ 2 * jasR2 s p ^ 2 := by gcongr
      _ = (κ * jasR2 s p) ^ 2 := by ring
      _ ≤ (jasR2 s p - jasR1 s p) ^ 2 := by gcongr
      _ = (jasR1 s p - jasR2 s p) ^ 2 := by ring

/-- Uniform bound for the local densities of one strip point over all primes. -/
def jasStripBound (s : ℂ) : ℝ :=
  1 / (1 - Real.exp (-s.re * Real.log 2)) + 1 / (1 - Real.exp (-(1 - s.re) * Real.log 2)) + 1

theorem jasStripBound_pos {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) : 0 < jasStripBound s := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.exp (-s.re * Real.log 2) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h2 : Real.exp (-(1 - s.re) * Real.log 2) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  unfold jasStripBound
  have : 0 < 1 - Real.exp (-s.re * Real.log 2) := by linarith
  have : 0 < 1 - Real.exp (-(1 - s.re) * Real.log 2) := by linarith
  positivity

theorem norm_jasHoloCircle_prime_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (p : Nat.Primes)
    (θ : UnitAddCircle) :
    ‖jasHoloCircle (jasHoloA s p) (jasHoloB s p) θ‖ ≤ jasStripBound s := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp2 : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
  refine (norm_jasHoloCircle_le (norm_jasHoloA_lt_one hs0 p) (norm_jasHoloB_lt_one hs1 p) θ).trans ?_
  unfold jasStripBound
  have hA : ‖jasHoloA s p‖ ≤ Real.exp (-s.re * Real.log 2) := by
    rw [norm_jasHoloA]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hB : ‖jasHoloB s p‖ ≤ Real.exp (-(1 - s.re) * Real.log 2) := by
    rw [norm_jasHoloB]; exact Real.exp_le_exp.mpr (by nlinarith)
  have h1 : Real.exp (-s.re * Real.log 2) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h2 : Real.exp (-(1 - s.re) * Real.log 2) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hAl := norm_jasHoloA_lt_one hs0 p
  have hBl := norm_jasHoloB_lt_one hs1 p
  gcongr

/-- Total variation of the depth-`P` explicit-formula density on the finite prime torus. -/
def jasHoloTotalVariation (s : ℂ) (P : Finset Nat.Primes) : ℝ :=
  ∫ x : (↥P → UnitAddCircle),
    ‖∏ i : ↥P, jasHoloCircle (jasHoloA s i) (jasHoloB s i) (x i)‖
      ∂Measure.pi fun _ => jasCircleHaar

theorem jasHoloTotalVariation_eq_prod (s : ℂ) (P : Finset Nat.Primes) :
    jasHoloTotalVariation s P =
      ∏ i : ↥P, ∫ θ, ‖jasHoloCircle (jasHoloA s i) (jasHoloB s i) θ‖ ∂jasCircleHaar := by
  unfold jasHoloTotalVariation
  simp_rw [norm_prod]
  exact integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (fun i : ↥P => fun θ => ‖jasHoloCircle (jasHoloA s i) (jasHoloB s i) θ‖)

theorem jas_one_add_sum_le_prod_one_add {ι : Type*} (t : Finset ι) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) : 1 + ∑ i ∈ t, x i ≤ ∏ i ∈ t, (1 + x i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hprod : 1 ≤ ∏ i ∈ t, (1 + x i) :=
      Finset.one_le_prod fun i _ => by linarith [hx i]
    nlinarith [hx j]

/-- **Off-line total-variation divergence.**  The explicit-formula sector of an off-line strip
point has unbounded total variation over finite prime tori. -/
theorem exists_lt_jasHoloTotalVariation {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hoff : s.re ≠ 1 / 2) (B : ℝ) : ∃ P : Finset Nat.Primes, B < jasHoloTotalVariation s P := by
  classical
  obtain ⟨c, hc, hgap⟩ := exists_pos_inv_le_sq_jasR1_sub_jasR2 hs0 hs1 hoff
  have hM := jasStripBound_pos hs0 hs1
  set κ := c / (8 * jasStripBound s) with hκ
  have hκ0 : 0 < κ := by positivity
  have hlocal : ∀ p : Nat.Primes, 1 + κ * ((p : ℕ) : ℝ)⁻¹ ≤
      ∫ θ, ‖jasHoloCircle (jasHoloA s p) (jasHoloB s p) θ‖ ∂jasCircleHaar := by
    intro p
    refine le_trans ?_ (one_add_le_integral_norm_jasHoloCircle (norm_jasHoloA_lt_one hs0 p)
      (norm_jasHoloB_lt_one hs1 p) (norm_jasHoloCircle_prime_le hs0 hs1 p) hM)
    rw [jasHoloA_sub_conj_jasHoloB_norm, sq_abs]
    have hp8 : 0 < 8 * jasStripBound s := by positivity
    have hκp : κ * ((p : ℕ) : ℝ)⁻¹ = (c * ((p : ℕ) : ℝ)⁻¹) / (8 * jasStripBound s) := by
      rw [hκ]; ring
    rw [hκp]
    gcongr
    exact hgap p
  -- unbounded reciprocal prime sums
  obtain ⟨P, hP⟩ : ∃ P : Finset Nat.Primes, (B - 1) / κ < ∑ p ∈ P, ((p : ℕ) : ℝ)⁻¹ := by
    by_contra h
    push Not at h
    apply Nat.Primes.not_summable_one_div
    simp_rw [one_div]
    exact summable_of_sum_le (fun p => by positivity) h
  refine ⟨P, ?_⟩
  rw [jasHoloTotalVariation_eq_prod]
  have hprod : ∏ i : ↥P, (1 + κ * ((i : Nat.Primes) : ℝ)⁻¹) ≤
      ∏ i : ↥P, ∫ θ, ‖jasHoloCircle (jasHoloA s i) (jasHoloB s i) θ‖ ∂jasCircleHaar :=
    Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hlocal i)
  have hsum : 1 + ∑ i : ↥P, κ * ((i : Nat.Primes) : ℝ)⁻¹ ≤
      ∏ i : ↥P, (1 + κ * ((i : Nat.Primes) : ℝ)⁻¹) :=
    jas_one_add_sum_le_prod_one_add Finset.univ
      (fun i : ↥P => κ * ((i : Nat.Primes) : ℝ)⁻¹)
      fun i => by positivity
  have hsumP : ∑ i : ↥P, κ * ((i : Nat.Primes) : ℝ)⁻¹ = κ * ∑ p ∈ P, ((p : ℕ) : ℝ)⁻¹ := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_coe_sort P (fun p : Nat.Primes => ((p : ℕ) : ℝ)⁻¹)
  rw [hsumP] at hsum
  have : B - 1 < κ * ∑ p ∈ P, ((p : ℕ) : ℝ)⁻¹ := by
    rw [div_lt_iff₀ hκ0] at hP; linarith
  linarith

/-- On the critical line the depth-`P` explicit-formula density is a probability density. -/
theorem jasHoloTotalVariation_eq_one_of_critical {s : ℂ} (hs : s.re = 1 / 2)
    (P : Finset Nat.Primes) : jasHoloTotalVariation s P = 1 := by
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s.re < 1 := by rw [hs]; norm_num
  rw [jasHoloTotalVariation_eq_prod]
  apply Finset.prod_eq_one
  intro i _
  have hreal : ∀ θ, ‖jasHoloCircle (jasHoloA s i) (jasHoloB s i) θ‖ =
      (jasHoloCircle (jasHoloA s i) (jasHoloB s i) θ).re := by
    intro θ
    have him : (jasHoloCircle (jasHoloA s i) (jasHoloB s i) θ).im = 0 := by
      unfold jasHoloCircle
      rw [jasHoloB_eq_conj_jasHoloA hs]
      exact im_jasHoloLocal_conj _ _
    have hre : 0 < (jasHoloCircle (jasHoloA s i) (jasHoloB s i) θ).re :=
      re_jasHoloLocal_pos (norm_jasHoloA_lt_one hs0 i) (norm_jasHoloB_lt_one hs1 i)
        (norm_fourier_unit 1 θ)
    rw [← Complex.re_add_im (jasHoloCircle (jasHoloA s i) (jasHoloB s i) θ), him,
      Complex.ofReal_zero, zero_mul, add_zero, Complex.norm_real, Real.norm_of_nonneg hre.le]
    simp
  simp_rw [hreal]
  have h := integral_re (integrable_of_continuous_circle (continuous_jasHoloCircle
    (norm_jasHoloA_lt_one hs0 i) (norm_jasHoloB_lt_one hs1 i)))
  simp only [RCLike.re_to_complex] at h
  rw [h, integral_jasHoloCircle (norm_jasHoloA_lt_one hs0 i) (norm_jasHoloB_lt_one hs1 i)]
  simp

/-- **Measure dichotomy.**  A strip point's explicit-formula sector has bounded total variation
over all finite prime tori exactly on the critical line. -/
theorem bddAbove_jasHoloTotalVariation_iff {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    BddAbove (Set.range (jasHoloTotalVariation s)) ↔ s.re = 1 / 2 := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hoff
    obtain ⟨P, hP⟩ := exists_lt_jasHoloTotalVariation hs0 hs1 hoff B
    exact absurd (hB ⟨P, rfl⟩) (not_le.mpr hP)
  · intro hs
    exact ⟨1, by rintro _ ⟨P, rfl⟩; rw [jasHoloTotalVariation_eq_one_of_critical hs]⟩

/-- RH is equivalent to every Xi zero's explicit-formula sector having bounded total variation on
all finite prime tori. -/
theorem forall_xi_bddAbove_jasHoloTotalVariation_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport, BddAbove (Set.range (jasHoloTotalVariation (rho : ℂ)))) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    have hstrip := xi_divisor_support_re_mem_open_unit rho
    exact (bddAbove_jasHoloTotalVariation_iff hstrip.1 hstrip.2).1 (h rho)
  · intro hRH rho
    have hstrip := xi_divisor_support_re_mem_open_unit rho
    exact (bddAbove_jasHoloTotalVariation_iff hstrip.1 hstrip.2).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower
