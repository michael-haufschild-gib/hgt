import GaloisForLFunctions.SignedSuccessorArithmetic.TheSizeTruncatedHypercubeFormIsTheReceiver

/-!
# The forward-dilated hypercube form and multiplicative sieve functional equation

In `TheNaturalCutoffDilationFormIsTheReceiver` and `TheSizeTruncatedHypercubeFormIsTheReceiver`,
`sizeHypercubeForm hr ε D` was expanded on the physical side through the **backward-dilated**
step vectors `D_{1/d} v_r`, yielding the discrete pronic energy of
`Ψ_D(n) = ∑_{d ≤ D} μ(d) d^{−ε} C_r(⌊n / d⌋)` whose weights `μ(d) d^{−ε}` are non-summable on the
critical band `0 < ε ≤ 1/2`.

Because the Ramanujan dilation profile `Φ_r(d₁ / d₂) = Re⟨v_r, D_{d₁/d₂} v_r⟩` is symmetric under
`d₁ ↔ d₂`, unitary conjugation by `D_{d₂}` reflects the Gram matrix from backward dilations
`D_{1/d} v_r` to **forward dilations** `D_d v_r`:

    R_{ε,r}(D) = ‖∑_{d ≤ D} μ(d) d^{−1/2−ε} D_d v_r‖_{L²(ℝ)}²
               = ∫_0^∞ (∑_{d ≤ D} μ(d) d^{−1−ε} C_r(⌊d x⌋))² dx / x².

This reflection transforms the analytic structure of the receiver:
1. **Unconditional summability of weights:** For every `ε > 0`, the forward-dilated weights
   `μ(d) d^{−1−ε}` are **absolutely summable**, and the exterior ray `[1, ∞)` is unconditionally
   bounded uniformly in `D` (`integral_Ioi_one_forwardDilatedPrimitive_le`).
2. **Compact `L²(1, D)` support after inversion `u = 1/x`:** Since `⌊d x⌋ = 0` whenever `d x < 1`,
   the interior integral on `(0, 1)` vanishes below `x = 1/D` and transforms under `u = 1/x` into
   the unweighted Lebesgue `L²` integral on `(1, D)` (`integral_Ioo_zero_one_forwardDilatedPrimitive_eq`):
       ∫_0^1 G_{ε,D}(x)² dx / x² = ∫_1^D G_{ε,D}(1/u)² du.
   Consequently, `RiemannHypothesis` follows from cofinal cutoff-uniform bounds on
   `∫_1^D G_{ε,D}(1/u)² du` (`riemannHypothesis_of_cofinal_bounded_forwardDilated_Ioo`), and at
   `r = 2` from cofinal bounds on `∫_1^D (∑_{u ≤ d ≤ D, Odd ⌊d/u⌋} μ(d) d^{−1−ε})² du`
   (`riemannHypothesis_of_cofinal_bounded_alternating_moebius_Ioo`).
3. **Terminal dyadic window = literal Möbius harmonic tail:** At `r = 2`, on `u ∈ (D/2, D)`, every
   `d ∈ [u, D]` has `⌊d / u⌋ = 1`, so `-G_{ε,D}(1/u)` collapses identically to the literal Möbius
   harmonic window `∑_{u ≤ d ≤ D} μ(d) d^{−1−ε}` (`forwardDilatedPrimitive_two_inv_eq_moebius_window`).
4. **Uniform `D → ∞` limit, periodicity, and exact sieve functional equation:** For `ε > 0`,
   `G_{ε,D}(x)` converges uniformly on `ℝ` to `G_ε(x) = ∑_{d ≥ 1} μ(d) d^{−1−ε} C_r(⌊d x⌋)`,
   which is `r`-periodic on `[0, ∞)` and satisfies the exact rounding-free Möbius sieve identity
       ∑_{m ≥ 1} m^{−1−ε} G_ε(m x) = C_r(⌊x⌋)   (∀ x ∈ ℝ),
   so in particular `G_ε(x) = −∑_{m ≥ 2} m^{−1−ε} G_ε(m x)` identically for all `x < 1`
   (`forwardDilatedLimit_eq_neg_tsum_of_lt_one`).
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open MeasureTheory Set Finset Filter Topology
open _root_.RHTower GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

/-! ## §1. Forward-dilation reflection of `pmRamanujanDilationProfile` and `sizeHypercubeForm` -/

private theorem rayDilate_mul_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (f : SoninL2) :
    rayDilate u (rayDilate v f) = rayDilate (u * v) f := by
  rw [rayDilate_of_pos hu, rayDilate_of_pos hv, rayDilate_of_pos (mul_pos hu hv),
    dilation_dilation hu hv f]

private theorem rayDilate_one_eq (f : SoninL2) : rayDilate 1 f = f := by
  rw [rayDilate_of_pos one_pos]
  apply Lp.ext
  filter_upwards [dilation_ae 1 one_pos f] with x hx
  simpa using hx

/-- **Forward-dilation inner-product representation of `pmRamanujanDilationProfile`.**
For any modulus `r > 1` and positive scales `a, b > 0`, `Φ_r(a / b) = Re⟨D_a v_r, D_b v_r⟩`. -/
theorem re_inner_rayDilate_self {r : ℕ} (hr : 1 < r) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (inner ℂ (rayDilate a (pmRamanujanStepVector r hr))
      (rayDilate b (pmRamanujanStepVector r hr))).re =
      pmRamanujanDilationProfile r hr (a / b) := by
  let f := pmRamanujanStepVector r hr
  have hiso : inner ℂ (rayDilate b⁻¹ (rayDilate a f)) (rayDilate b⁻¹ (rayDilate b f)) =
      inner ℂ (rayDilate a f) (rayDilate b f) := by
    rw [rayDilate_of_pos (inv_pos.mpr hb), rayDilate_of_pos (inv_pos.mpr hb)]
    exact (dilation b⁻¹ (inv_pos.mpr hb)).inner_map_map _ _
  rw [rayDilate_mul_pos (inv_pos.mpr hb) ha, rayDilate_mul_pos (inv_pos.mpr hb) hb,
    inv_mul_cancel₀ hb.ne', rayDilate_one_eq,
    show b⁻¹ * a = a / b by ring] at hiso
  rw [pmRamanujanDilationProfile, ← hiso, ← inner_conj_symm (rayDilate (a / b) f) f,
    Complex.conj_re]

/-- Finite-cutoff forward-dilated Möbius–Ramanujan sum
`G_{ε,D}(x) = ∑_{1 ≤ d ≤ D} μ(d) d^{−1−ε} C_r(⌊d x⌋)`. -/
noncomputable def forwardDilatedPrimitive (r : ℕ) (ε : ℝ) (D : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ Icc 1 D, moebiusReal d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re

/-- Forward-dilated `SoninL2` vector `∑_{1 ≤ d ≤ D} μ(d) d^{−1/2−ε} D_d v_r`. -/
noncomputable def forwardDilatedVector {r : ℕ} (hr : 1 < r) (ε : ℝ) (D : ℕ) : SoninL2 :=
  ∑ d ∈ Icc 1 D, ((moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ) •
    rayDilate (d : ℝ) (pmRamanujanStepVector r hr)

/-- **Hilbert-norm realization of `sizeHypercubeForm` via forward dilations.** -/
theorem norm_sq_forwardDilatedVector_eq_sizeHypercubeForm {r : ℕ} (hr : 1 < r)
    (ε : ℝ) (D : ℕ) :
    ‖forwardDilatedVector hr ε D‖ ^ 2 = sizeHypercubeForm hr ε D := by
  have hre : ‖forwardDilatedVector hr ε D‖ ^ 2 =
      (inner ℂ (forwardDilatedVector hr ε D) (forwardDilatedVector hr ε D)).re := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hre, forwardDilatedVector, sum_inner, Complex.re_sum, sizeHypercubeForm]
  refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
  rw [inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
  have hd₁0 : (0 : ℝ) < d₁ := by exact_mod_cast (mem_Icc.mp hd₁).1
  have hd₂0 : (0 : ℝ) < d₂ := by exact_mod_cast (mem_Icc.mp hd₂).1
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc]
  have hmul : (((moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ) *
      ((moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ) *
      inner ℂ (rayDilate (d₁ : ℝ) (pmRamanujanStepVector r hr))
        (rayDilate (d₂ : ℝ) (pmRamanujanStepVector r hr))).re =
      (moebiusReal d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
        (moebiusReal d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
        (inner ℂ (rayDilate (d₁ : ℝ) (pmRamanujanStepVector r hr))
          (rayDilate (d₂ : ℝ) (pmRamanujanStepVector r hr))).re := by
    rw [← Complex.ofReal_mul, Complex.re_ofReal_mul]
  rw [hmul, re_inner_rayDilate_self hr hd₁0 hd₂0]

private theorem forwardDilated_term_ae {r d : ℕ} (hr : 1 < r) (hd : 1 ≤ d) (ε : ℝ) :
    (((((moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ) •
      rayDilate (d : ℝ) (pmRamanujanStepVector r hr) : SoninL2) : ℝ → ℂ)) =ᵐ[volume]
      fun x : ℝ => if 0 < x then
        (((moebiusReal d * (d : ℝ) ^ (-1 - ε) *
          (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re) / x : ℝ) : ℂ)
      else 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcomp := (memLp_pmRamanujanStepSource hr).coeFn_toLp.comp_tendsto
    (realMul_quasiMeasurePreserving (d : ℝ) hdR.ne').tendsto_ae
  filter_upwards [Lp.coeFn_smul ((moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ)
      (rayDilate (d : ℝ) (pmRamanujanStepVector r hr)),
    rayDilate_ae hdR (pmRamanujanStepVector r hr), hcomp] with x hsmul hdil hc
  change (pmRamanujanStepVector r hr : ℝ → ℂ) ((d : ℝ) * x) =
    pmRamanujanStepSource r ((d : ℝ) * x) at hc
  rw [hsmul, Pi.smul_apply, smul_eq_mul, hdil, hc]
  by_cases hx : 0 < x
  · rw [if_pos hx, pmRamanujanStepSource, stepFun]
    have hexp : (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) * Real.sqrt d * (d : ℝ)⁻¹ = (d : ℝ) ^ (-1 - ε) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one (d : ℝ), ← Real.rpow_add hdR, ← Real.rpow_add hdR]
      congr 1
      ring
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    rw [mul_inv_rev, div_eq_mul_inv]
    calc moebiusReal d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) *
          (Real.sqrt d * ((pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re * (x⁻¹ * (d : ℝ)⁻¹)))
        = moebiusReal d * ((d : ℝ) ^ (-(1 / 2 : ℝ) - ε) * Real.sqrt d * (d : ℝ)⁻¹) *
            (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re * x⁻¹ := by ring
      _ = moebiusReal d * (d : ℝ) ^ (-1 - ε) *
            (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re * x⁻¹ := by rw [hexp]
  · rw [if_neg hx]
    have hxle : x ≤ 0 := not_lt.mp hx
    have hdx : (d : ℝ) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hdR.le hxle
    simp [pmRamanujanStepSource, stepFun, Nat.floor_of_nonpos hdx, pmRamanujanPrimitive]

private theorem forwardDilatedVector_ae {r : ℕ} (hr : 1 < r) (ε : ℝ) :
    ∀ D : ℕ, (forwardDilatedVector hr ε D : ℝ → ℂ) =ᵐ[volume]
      (Set.Ioi (0 : ℝ)).indicator (fun x : ℝ => ((forwardDilatedPrimitive r ε D x / x : ℝ) : ℂ)) := by
  intro D
  induction D with
  | zero =>
    have h0 : forwardDilatedVector hr ε 0 = 0 := by simp [forwardDilatedVector]
    rw [h0]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    rw [hx, Pi.zero_apply]
    by_cases hpos : 0 < x
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hpos)]
      simp [forwardDilatedPrimitive]
    · rw [Set.indicator_of_notMem (show x ∉ Set.Ioi (0 : ℝ) from hpos)]
  | succ D ih =>
    have hsplit : forwardDilatedVector hr ε (D + 1) =
        forwardDilatedVector hr ε D +
          ((moebiusReal (D + 1) * ((D + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ) - ε) : ℝ) : ℂ) •
            rayDilate ((D + 1 : ℕ) : ℝ) (pmRamanujanStepVector r hr) := by
      unfold forwardDilatedVector
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hsplit]
    filter_upwards [Lp.coeFn_add (forwardDilatedVector hr ε D) _,
      ih, forwardDilated_term_ae hr (by omega : 1 ≤ D + 1) ε] with x hadd hD hlast
    rw [hadd, Pi.add_apply, hD, hlast]
    by_cases hpos : 0 < x
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hpos),
        Set.indicator_of_mem (Set.mem_Ioi.mpr hpos), if_pos hpos]
      unfold forwardDilatedPrimitive
      rw [Finset.sum_Icc_succ_top (by omega), add_div]
      push_cast
      rfl
    · rw [Set.indicator_of_notMem (show x ∉ Set.Ioi (0 : ℝ) from hpos),
        Set.indicator_of_notMem (show x ∉ Set.Ioi (0 : ℝ) from hpos), if_neg hpos, add_zero]

/-- **Forward-dilated `L²(0, ∞)` integral identity for `sizeHypercubeForm`.**
`R_{ε,r}(D) = ∫_0^∞ (∑_{1 ≤ d ≤ D} μ(d) d^{−1−ε} C_r(⌊d x⌋))² dx / x²`. -/
theorem sizeHypercubeForm_eq_integral_Ioi_forwardDilatedPrimitive {r : ℕ} (hr : 1 < r)
    (ε : ℝ) (D : ℕ) :
    sizeHypercubeForm hr ε D =
      ∫ x in Set.Ioi (0 : ℝ), forwardDilatedPrimitive r ε D x ^ 2 / x ^ 2 := by
  rw [← norm_sq_forwardDilatedVector_eq_sizeHypercubeForm hr ε D, norm_sq_lp_eq_integral_norm_sq]
  have hae : (fun x : ℝ => ‖(forwardDilatedVector hr ε D : ℝ → ℂ) x‖ ^ 2) =ᵐ[volume]
      (Set.Ioi (0 : ℝ)).indicator (fun x : ℝ => forwardDilatedPrimitive r ε D x ^ 2 / x ^ 2) := by
    filter_upwards [forwardDilatedVector_ae hr ε D] with x hx
    rw [hx]
    by_cases hpos : 0 < x
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hpos),
        Set.indicator_of_mem (Set.mem_Ioi.mpr hpos),
        Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
    · rw [Set.indicator_of_notMem (show x ∉ Set.Ioi (0 : ℝ) from hpos),
        Set.indicator_of_notMem (show x ∉ Set.Ioi (0 : ℝ) from hpos),
        norm_zero, zero_pow two_ne_zero]
  rw [integral_congr_ae hae, integral_indicator measurableSet_Ioi]

/-! ## §2. Exterior unconditional bound on `[1, ∞)` and interior compact `L²(1, D)` inversion -/

theorem measurable_forwardDilatedPrimitive (r : ℕ) (ε : ℝ) (D : ℕ) :
    Measurable (forwardDilatedPrimitive r ε D) := by
  unfold forwardDilatedPrimitive
  refine Finset.measurable_sum _ fun d _ => Measurable.const_mul ?_ _
  exact (measurable_of_countable fun n => (pmRamanujanPrimitive r n).re).comp
    (Nat.measurable_floor.comp (measurable_const.mul measurable_id))

/-- `forwardDilatedPrimitive r ε D x` vanishes identically whenever `D x < 1` (and for all `x ≤ 0`). -/
theorem forwardDilatedPrimitive_eq_zero_of_mul_lt_one (r : ℕ) (ε : ℝ) (D : ℕ) {x : ℝ}
    (hx : (D : ℝ) * x < 1) :
    forwardDilatedPrimitive r ε D x = 0 := by
  unfold forwardDilatedPrimitive
  refine Finset.sum_eq_zero fun d hd => ?_
  have hdD : (d : ℝ) ≤ D := by exact_mod_cast (mem_Icc.mp hd).2
  have hdx : (d : ℝ) * x < 1 := by
    rcases le_or_gt x 0 with hx0 | hx0
    · have : (d : ℝ) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg d) hx0
      linarith
    · exact (mul_le_mul_of_nonneg_right hdD hx0.le).trans_lt hx
  rw [Nat.floor_eq_zero.mpr hdx]
  simp [pmRamanujanPrimitive]

private theorem abs_moebiusReal_le_one_local (d : ℕ) : |moebiusReal d| ≤ 1 := by
  unfold moebiusReal
  have := ArithmeticFunction.abs_moebius_le_one (n := d)
  exact_mod_cast this

/-- **Uniform pointwise bound on `forwardDilatedPrimitive` for every `ε > 0`.** -/
theorem abs_forwardDilatedPrimitive_le {r : ℕ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε)
    (D : ℕ) (x : ℝ) :
    |forwardDilatedPrimitive r ε D x| ≤
      pmRamanujanPrimitiveBound r * ∑' d : ℕ, ((d : ℝ) ^ (1 + ε))⁻¹ := by
  have hsum : Summable (fun d : ℕ => ((d : ℝ) ^ (1 + ε))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  have hB0 : 0 ≤ pmRamanujanPrimitiveBound r :=
    (abs_nonneg _).trans ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr 0))
  unfold forwardDilatedPrimitive
  calc |∑ d ∈ Icc 1 D, moebiusReal d * (d : ℝ) ^ (-1 - ε) *
          (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re|
      ≤ ∑ d ∈ Icc 1 D, |moebiusReal d * (d : ℝ) ^ (-1 - ε) *
          (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 D, pmRamanujanPrimitiveBound r * ((d : ℝ) ^ (1 + ε))⁻¹ := by
        refine Finset.sum_le_sum fun d _ => ?_
        have hd_nn : 0 ≤ (d : ℝ) ^ (-1 - ε) := Real.rpow_nonneg (Nat.cast_nonneg d) _
        have hC : |(pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re| ≤ pmRamanujanPrimitiveBound r :=
          (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
        rw [abs_mul, abs_mul, abs_of_nonneg hd_nn, show (-1 - ε : ℝ) = -(1 + ε) by ring,
          Real.rpow_neg (Nat.cast_nonneg d)]
        calc |moebiusReal d| * ((d : ℝ) ^ (1 + ε))⁻¹ * |(pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re|
            ≤ 1 * ((d : ℝ) ^ (1 + ε))⁻¹ * pmRamanujanPrimitiveBound r :=
              mul_le_mul (mul_le_mul_of_nonneg_right (abs_moebiusReal_le_one_local d)
                (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg d) _))) hC (abs_nonneg _)
                (by positivity)
          _ = _ := by ring
    _ = pmRamanujanPrimitiveBound r * ∑ d ∈ Finset.Icc 1 D, ((d : ℝ) ^ (1 + ε))⁻¹ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ pmRamanujanPrimitiveBound r * ∑' d : ℕ, ((d : ℝ) ^ (1 + ε))⁻¹ :=
        mul_le_mul_of_nonneg_left
          (hsum.sum_le_tsum _ fun d _ => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg d) _))
          hB0

theorem integrableOn_Ioi_forwardDilatedPrimitive_sq {r : ℕ} (hr : 1 < r) (ε : ℝ) (D : ℕ) :
    IntegrableOn (fun x : ℝ => forwardDilatedPrimitive r ε D x ^ 2 / x ^ 2) (Set.Ioi 0) := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · refine (integrableOn_zero (s := Set.Ioi (0 : ℝ))).congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp [forwardDilatedPrimitive]
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  set M : ℝ := ∑ d ∈ Finset.Icc 1 D, |moebiusReal d| * (d : ℝ) ^ (-1 - ε) * pmRamanujanPrimitiveBound r
  have hM_bdd : ∀ x : ℝ, |forwardDilatedPrimitive r ε D x| ≤ M := fun x => by
    unfold forwardDilatedPrimitive
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)) (by positivity)
  have hdom : IntegrableOn (fun x : ℝ => M ^ 2 * x ^ (-2 : ℝ)) (Set.Ioi ((D : ℝ)⁻¹)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (inv_pos.mpr hDpos)).const_mul (M ^ 2)
  have htail : IntegrableOn (fun x : ℝ => forwardDilatedPrimitive r ε D x ^ 2 / x ^ 2)
      (Set.Ioi ((D : ℝ)⁻¹)) := by
    refine hdom.mono' (((measurable_forwardDilatedPrimitive r ε D).pow_const 2).div
      (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans (inv_pos.mpr hDpos) (Set.mem_Ioi.mp hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_natCast,
      div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM_bdd x) 2
  have hunion : Set.Ioc (0 : ℝ) ((D : ℝ)⁻¹) ∪ Set.Ioi ((D : ℝ)⁻¹) = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi (inv_nonneg.mpr hDpos.le)
  rw [← hunion]
  refine IntegrableOn.union ?_ htail
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  refine (integrableOn_zero (s := Set.Ioo (0 : ℝ) ((D : ℝ)⁻¹))).congr_fun (fun x hx => ?_)
    measurableSet_Ioo
  have hlt : (D : ℝ) * x < 1 :=
    calc (D : ℝ) * x < (D : ℝ) * (D : ℝ)⁻¹ := mul_lt_mul_of_pos_left hx.2 hDpos
      _ = 1 := mul_inv_cancel₀ hDpos.ne'
  simp [forwardDilatedPrimitive_eq_zero_of_mul_lt_one r ε D hlt]

/-- **Unconditional cutoff-uniform bound on the exterior ray `[1, ∞)` for every `ε > 0`.**
On `(1, ∞)`, `∫_1^∞ G_{ε,D}(x)² dx / x² ≤ (B_r · ζ(1 + ε))²` uniformly for all `D : ℕ`. -/
theorem integral_Ioi_one_forwardDilatedPrimitive_le {r : ℕ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε)
    (D : ℕ) :
    (∫ x in Set.Ioi (1 : ℝ), forwardDilatedPrimitive r ε D x ^ 2 / x ^ 2) ≤
      (pmRamanujanPrimitiveBound r * ∑' d : ℕ, ((d : ℝ) ^ (1 + ε))⁻¹) ^ 2 := by
  set C := pmRamanujanPrimitiveBound r * ∑' d : ℕ, ((d : ℝ) ^ (1 + ε))⁻¹
  have hint1 : IntegrableOn (fun x : ℝ => forwardDilatedPrimitive r ε D x ^ 2 / x ^ 2) (Set.Ioi 1) :=
    (integrableOn_Ioi_forwardDilatedPrimitive_sq hr ε D).mono_set
      (Set.Ioi_subset_Ioi zero_le_one)
  have hint2 : IntegrableOn (fun x : ℝ => C ^ 2 * x ^ (-2 : ℝ)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul (C ^ 2)
  have hle : (∫ x in Set.Ioi (1 : ℝ), forwardDilatedPrimitive r ε D x ^ 2 / x ^ 2) ≤
      ∫ x in Set.Ioi (1 : ℝ), C ^ 2 * x ^ (-2 : ℝ) := by
    refine setIntegral_mono_on hint1 hint2 measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := lt_trans zero_lt_one (Set.mem_Ioi.mp hx)
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx0.le, Real.rpow_natCast,
      div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_forwardDilatedPrimitive_le hr hε D x) 2
  refine hle.trans_eq ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

/-- **Exact interior-plus-exterior split of `sizeHypercubeForm`.** -/
theorem sizeHypercubeForm_eq_Ioo_zero_one_add_Ioi_one {r : ℕ} (hr : 1 < r) (ε : ℝ) (D : ℕ) :
    sizeHypercubeForm hr ε D =
      (∫ x in Set.Ioo (0 : ℝ) 1, forwardDilatedPrimitive r ε D x ^ 2 / x ^ 2) +
        (∫ x in Set.Ioi (1 : ℝ), forwardDilatedPrimitive r ε D x ^ 2 / x ^ 2) := by
  rw [sizeHypercubeForm_eq_integral_Ioi_forwardDilatedPrimitive hr ε D]
  have hint := integrableOn_Ioi_forwardDilatedPrimitive_sq hr ε D
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := Set.Ioc_disjoint_Ioi le_rfl
  rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
    (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi zero_le_one)),
    integral_Ioc_eq_integral_Ioo]

/-- General inversion identity `∫_{x ∈ (0, 1)} h(x) / x² dx = ∫_{u ∈ (1, ∞)} h(1/u) du`. -/
theorem integral_Ioo_zero_one_div_sq_eq_integral_Ioi_one_inv (h : ℝ → ℝ) :
    (∫ x in Set.Ioo (0 : ℝ) 1, h x / x ^ 2) = ∫ u in Set.Ioi (1 : ℝ), h u⁻¹ := by
  have hrpow := integral_comp_rpow_Ioi
    ((Set.Ioi (1 : ℝ)).indicator fun u : ℝ => h u⁻¹) (p := (-1 : ℝ)) (by norm_num)
  rw [setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
    max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] at hrpow
  have hlhs : (∫ x in Set.Ioo (0 : ℝ) 1, h x / x ^ 2) =
      ∫ x in Set.Ioi (0 : ℝ), (Set.Ioo (0 : ℝ) 1).indicator (fun x => h x / x ^ 2) x := by
    rw [setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_self_of_subset_right Set.Ioo_subset_Ioi_self]
  rw [hlhs, ← hrpow]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := Set.mem_Ioi.mp hx
  dsimp only [smul_eq_mul]
  rw [abs_neg, abs_one, one_mul, show (-1 - 1 : ℝ) = -2 by norm_num,
    Real.rpow_neg_one x]
  by_cases hx1 : x < 1
  · have hinv1 : 1 < x⁻¹ := (one_lt_inv₀ hx0).mpr hx1
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hinv1), inv_inv,
      Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hx0, hx1⟩),
      Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_eq_mul_inv, mul_comm]
  · have hinv_le : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (not_lt.mp hx1)
    rw [Set.indicator_of_notMem (show x⁻¹ ∉ Set.Ioi (1 : ℝ) from not_lt.mpr hinv_le),
      Set.indicator_of_notMem (fun hm : x ∈ Set.Ioo (0 : ℝ) 1 => hx1 hm.2), mul_zero]

/-- **Exact compact-interval `L²(1, D)` formula for the interior `(0, 1)` forward-dilated energy.**
Under `u = 1/x`, `∫_0^1 G_{ε,D}(x)² dx / x² = ∫_1^D G_{ε,D}(1/u)² du`. -/
theorem integral_Ioo_zero_one_forwardDilatedPrimitive_eq (r : ℕ) (ε : ℝ) (D : ℕ) :
    (∫ x in Set.Ioo (0 : ℝ) 1, forwardDilatedPrimitive r ε D x ^ 2 / x ^ 2) =
      ∫ u in Set.Ioo (1 : ℝ) D, forwardDilatedPrimitive r ε D u⁻¹ ^ 2 := by
  rw [integral_Ioo_zero_one_div_sq_eq_integral_Ioi_one_inv
    (fun x => forwardDilatedPrimitive r ε D x ^ 2),
    ← integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioc]
  congr 1
  ext u
  by_cases hu1 : 1 < u
  · by_cases huD : u ≤ D
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hu1),
        Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hu1, huD⟩)]
    · have hDu : (D : ℝ) < u := not_le.mp huD
      have hu0 : 0 < u := lt_trans zero_lt_one hu1
      have hlt : (D : ℝ) * u⁻¹ < 1 := (mul_inv_lt_iff₀ hu0).mpr (by linarith)
      rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hu1),
        Set.indicator_of_notMem (fun hm : u ∈ Set.Ioc (1 : ℝ) D => huD hm.2),
        forwardDilatedPrimitive_eq_zero_of_mul_lt_one r ε D hlt, zero_pow two_ne_zero]
  · rw [Set.indicator_of_notMem (show u ∉ Set.Ioi (1 : ℝ) from hu1),
      Set.indicator_of_notMem (fun hm : u ∈ Set.Ioc (1 : ℝ) D => hu1 hm.1)]

/-- **Upper bound on `sizeHypercubeForm` by the compact `L²(1, D)` integral plus `O_ε(1)`.** -/
theorem sizeHypercubeForm_le_forwardDilated_Ioo_add_const {r : ℕ} (hr : 1 < r)
    {ε : ℝ} (hε : 0 < ε) (D : ℕ) :
    sizeHypercubeForm hr ε D ≤
      (∫ u in Set.Ioo (1 : ℝ) D, forwardDilatedPrimitive r ε D u⁻¹ ^ 2) +
        (pmRamanujanPrimitiveBound r * ∑' d : ℕ, ((d : ℝ) ^ (1 + ε))⁻¹) ^ 2 := by
  rw [sizeHypercubeForm_eq_Ioo_zero_one_add_Ioi_one hr ε D,
    integral_Ioo_zero_one_forwardDilatedPrimitive_eq r ε D]
  exact add_le_add le_rfl (integral_Ioi_one_forwardDilatedPrimitive_le hr hε D)

/-- **Forward-dilated `L²(1, D)` criterion for `RiemannHypothesis`.**
If for some prime `p` and dampings `ε → 0⁺` the unweighted Lebesgue integral
`∫_1^D (∑_{d ≤ D} μ(d) d^{−1−ε} C_p(⌊d / u⌋))² du` is bounded uniformly in `D`, then
`RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_cofinal_bounded_forwardDilated_Ioo {p : ℕ} (hp : p.Prime)
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ D : ℕ, (∫ u in Set.Ioo (1 : ℝ) D, forwardDilatedPrimitive p ε D u⁻¹ ^ 2) ≤ B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_cofinal_bounded_sizeHypercubeForm hp fun δ hδ => ?_
  obtain ⟨ε, hε0, hεδ, B, hB⟩ := h δ hδ
  refine ⟨ε, hε0, hεδ,
    B + (pmRamanujanPrimitiveBound p * ∑' d : ℕ, ((d : ℝ) ^ (1 + ε))⁻¹) ^ 2, fun D => ?_⟩
  exact (sizeHypercubeForm_le_forwardDilated_Ioo_add_const hp.one_lt hε0 D).trans
    (add_le_add (hB D) le_rfl)

/-! ## §3. Prime-two parity specialization and terminal dyadic Möbius window -/

/-- Exact evaluation of the real Ramanujan primitive at prime `r = 2`: `C_2(m) = −(m mod 2)`. -/
theorem pmRamanujanPrimitive_two_re (m : ℕ) :
    (pmRamanujanPrimitive 2 m).re = -((m % 2 : ℕ) : ℝ) := by
  rw [pmRamanujanPrimitive_re_eq_floor 2 m,
    Nat.sum_divisorsAntidiagonal (fun a b => (a : ℝ) * moebiusReal b * ((m / a : ℕ) : ℝ)),
    Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  simp only [Nat.div_self two_pos, Nat.div_one, moebiusReal_one',
    moebiusReal_of_prime Nat.prime_two]
  have hmod : (2 : ℝ) * ((m / 2 : ℕ) : ℝ) + ((m % 2 : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Nat.div_add_mod m 2
  push_cast
  linarith

/-- At `r = 2`, `forwardDilatedPrimitive` is minus the alternating odd-floor Möbius sum. -/
theorem forwardDilatedPrimitive_two_eq (ε : ℝ) (D : ℕ) (x : ℝ) :
    forwardDilatedPrimitive 2 ε D x =
      -∑ d ∈ Finset.Icc 1 D,
        moebiusReal d * (d : ℝ) ^ (-1 - ε) * ((⌊(d : ℝ) * x⌋₊ % 2 : ℕ) : ℝ) := by
  unfold forwardDilatedPrimitive
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pmRamanujanPrimitive_two_re]
  ring

/-- **Alternating odd-floor Möbius `L²(1, D)` criterion for `RiemannHypothesis`.** -/
theorem riemannHypothesis_of_cofinal_bounded_alternating_moebius_Ioo
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ∃ B : ℝ, ∀ D : ℕ,
      (∫ u in Set.Ioo (1 : ℝ) D,
        (∑ d ∈ Finset.Icc 1 D,
          moebiusReal d * (d : ℝ) ^ (-1 - ε) * ((⌊(d : ℝ) / u⌋₊ % 2 : ℕ) : ℝ)) ^ 2) ≤ B) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_cofinal_bounded_forwardDilated_Ioo Nat.prime_two fun δ hδ => ?_
  obtain ⟨ε, hε0, hεδ, B, hB⟩ := h δ hδ
  refine ⟨ε, hε0, hεδ, B, fun D => ?_⟩
  refine (hB D).trans_eq' (setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_)
  rw [forwardDilatedPrimitive_two_eq, neg_sq]
  simp only [div_eq_mul_inv]

/-- **Terminal dyadic window identity (`u ∈ (D/2, D)`).**
On the top dyadic octave `(D/2, D)`, every `d ∈ [u, D]` satisfies `1 ≤ d / u < 2`, hence
`⌊d / u⌋ = 1` (odd), while every `d < u` has `⌊d / u⌋ = 0` (even). Thus `forwardDilatedPrimitive 2`
at `1 / u` equals minus the literal unweighted Möbius harmonic window `∑_{u ≤ d ≤ D} μ(d) d^{−1−ε}`. -/
theorem forwardDilatedPrimitive_two_inv_eq_moebius_window (ε : ℝ) (D : ℕ) {u : ℝ}
    (hu : u ∈ Set.Ioo ((D : ℝ) / 2) D) :
    forwardDilatedPrimitive 2 ε D u⁻¹ =
      -∑ d ∈ (Finset.Icc 1 D).filter (fun d : ℕ => u ≤ (d : ℝ)),
        moebiusReal d * (d : ℝ) ^ (-1 - ε) := by
  have hDpos : (0 : ℝ) < D := by linarith [hu.1, hu.2]
  have hu0 : 0 < u := by linarith [hu.1, hDpos]
  rw [forwardDilatedPrimitive_two_eq, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdD : (d : ℝ) ≤ D := by exact_mod_cast (Finset.mem_Icc.mp hd).2
  by_cases hud : u ≤ (d : ℝ)
  · rw [if_pos hud]
    have hge1 : (1 : ℝ) ≤ (d : ℝ) * u⁻¹ :=
      calc (1 : ℝ) = u * u⁻¹ := (mul_inv_cancel₀ hu0.ne').symm
        _ ≤ (d : ℝ) * u⁻¹ := mul_le_mul_of_nonneg_right hud (inv_nonneg.mpr hu0.le)
    have hlt2 : (d : ℝ) * u⁻¹ < 2 := (mul_inv_lt_iff₀ hu0).mpr (by linarith [hu.1, hdD])
    have hfl : ⌊(d : ℝ) * u⁻¹⌋₊ = 1 :=
      (Nat.floor_eq_iff (by positivity)).mpr ⟨by norm_cast, by norm_cast⟩
    rw [hfl]
    norm_num
  · rw [if_neg hud]
    have hlt1 : (d : ℝ) * u⁻¹ < 1 := (mul_inv_lt_iff₀ hu0).mpr (by linarith [not_le.mp hud])
    rw [Nat.floor_eq_zero.mpr hlt1]
    norm_num

/-! ## §4. Infinite `D → ∞` forward-dilated limit, periodicity, and Möbius sieve identity -/

/-- The absolutely convergent infinite-cutoff forward-dilated Möbius–Ramanujan function
`G_ε(x) = ∑_{d ≥ 1} μ(d) d^{−1−ε} C_r(⌊d x⌋)`. -/
noncomputable def forwardDilatedLimit (r : ℕ) (ε : ℝ) (x : ℝ) : ℝ :=
  ∑' d : ℕ, moebiusReal d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re

theorem summable_forwardDilatedLimit_term {r : ℕ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    Summable (fun d : ℕ =>
      moebiusReal d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re) := by
  have hsum : Summable (fun d : ℕ => pmRamanujanPrimitiveBound r * ((d : ℝ) ^ (1 + ε))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _
  refine hsum.of_norm_bounded fun d => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
    show (-1 - ε : ℝ) = -(1 + ε) by ring, Real.rpow_neg (Nat.cast_nonneg d)]
  have hC : |(pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re| ≤ pmRamanujanPrimitiveBound r :=
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
  calc |moebiusReal d| * ((d : ℝ) ^ (1 + ε))⁻¹ * |(pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re|
      ≤ 1 * ((d : ℝ) ^ (1 + ε))⁻¹ * pmRamanujanPrimitiveBound r :=
        mul_le_mul (mul_le_mul_of_nonneg_right (abs_moebiusReal_le_one_local d)
          (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg d) _))) hC (abs_nonneg _)
          (by positivity)
    _ = _ := by ring

/-- **Uniform `O(D^{−ε})` approximation of `forwardDilatedLimit` by `forwardDilatedPrimitive`.** -/
theorem abs_forwardDilatedLimit_sub_primitive_le {r : ℕ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε)
    (D : ℕ) (x : ℝ) :
    |forwardDilatedLimit r ε x - forwardDilatedPrimitive r ε D x| ≤
      pmRamanujanPrimitiveBound r * ∑' m : ℕ, (((m + (D + 1) : ℕ) : ℝ) ^ (1 + ε))⁻¹ := by
  have hs := summable_forwardDilatedLimit_term hr hε x
  have hdom : Summable (fun m : ℕ =>
      pmRamanujanPrimitiveBound r * (((m + (D + 1) : ℕ) : ℝ) ^ (1 + ε))⁻¹) :=
    ((Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + ε)).comp_injective
      (add_left_injective (D + 1))).mul_left _
  have hhead : (∑ d ∈ Finset.range (D + 1),
      moebiusReal d * (d : ℝ) ^ (-1 - ε) * (pmRamanujanPrimitive r ⌊(d : ℝ) * x⌋₊).re) =
      forwardDilatedPrimitive r ε D x := by
    rw [Finset.range_eq_Ico, show Finset.Ico 0 (D + 1) = insert 0 (Finset.Icc 1 D) by
      ext d; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp)]
    simp [forwardDilatedPrimitive, pmRamanujanPrimitive]
  have htail : forwardDilatedLimit r ε x - forwardDilatedPrimitive r ε D x =
      ∑' m : ℕ, moebiusReal (m + (D + 1)) * ((m + (D + 1) : ℕ) : ℝ) ^ (-1 - ε) *
        (pmRamanujanPrimitive r ⌊((m + (D + 1) : ℕ) : ℝ) * x⌋₊).re := by
    have hsplit := hs.sum_add_tsum_nat_add (D + 1)
    rw [hhead] at hsplit
    unfold forwardDilatedLimit
    linarith
  rw [htail, ← Real.norm_eq_abs, ← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm (hs.comp_injective (add_left_injective (D + 1))).norm).trans
    (Summable.tsum_le_tsum (fun m => ?_) (hs.comp_injective (add_left_injective (D + 1))).norm hdom)
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    show (-1 - ε : ℝ) = -(1 + ε) by ring, Real.rpow_neg (Nat.cast_nonneg _)]
  have hC : |(pmRamanujanPrimitive r ⌊((m + (D + 1) : ℕ) : ℝ) * x⌋₊).re| ≤
      pmRamanujanPrimitiveBound r :=
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
  calc |moebiusReal (m + (D + 1))| * (((m + (D + 1) : ℕ) : ℝ) ^ (1 + ε))⁻¹ *
        |(pmRamanujanPrimitive r ⌊((m + (D + 1) : ℕ) : ℝ) * x⌋₊).re|
      ≤ 1 * (((m + (D + 1) : ℕ) : ℝ) ^ (1 + ε))⁻¹ * pmRamanujanPrimitiveBound r :=
        mul_le_mul (mul_le_mul_of_nonneg_right (abs_moebiusReal_le_one_local _)
          (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _))) hC (abs_nonneg _)
          (by positivity)
    _ = _ := by ring

private theorem sum_divisors_moebiusReal_local (j : ℕ) :
    ∑ m ∈ j.divisors, moebiusReal m = if j = 1 then 1 else 0 := by
  have hμ := congrArg (fun F : ArithmeticFunction ℝ => F j)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply] at hμ
  rw [show ∑ i ∈ j.divisors, moebiusReal i = (1 : ArithmeticFunction ℝ) j from hμ]
  rcases eq_or_ne j 1 with rfl | hj
  · simp
  · simp [hj]

/-- `C_r(m + k r) = C_r(m)` for every `r > 1` and `m, k : ℕ`. -/
theorem pmRamanujanPrimitive_re_add_mul_self {r : ℕ} (hr : 1 < r) (m k : ℕ) :
    (pmRamanujanPrimitive r (m + k * r)).re = (pmRamanujanPrimitive r m).re := by
  rw [pmRamanujanPrimitive_re_eq_floor, pmRamanujanPrimitive_re_eq_floor]
  have hterm : ∀ x ∈ r.divisorsAntidiagonal,
      (x.1 : ℝ) * moebiusReal x.2 * (((m + k * r) / x.1 : ℕ) : ℝ) =
        (x.1 : ℝ) * moebiusReal x.2 * ((m / x.1 : ℕ) : ℝ) +
          ((k * r : ℕ) : ℝ) * moebiusReal x.2 := by
    intro x hx
    have hmul : x.1 * x.2 = r := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hx1 : 0 < x.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
    have hdiv : (m + k * r) / x.1 = m / x.1 + k * x.2 := by
      rw [show m + k * r = m + (k * x.2) * x.1 by rw [← hmul]; ring,
        Nat.add_mul_div_right m (k * x.2) hx1]
    have hmulR : (x.1 : ℝ) * (x.2 : ℝ) = (r : ℝ) := by exact_mod_cast hmul
    rw [hdiv]
    push_cast
    linear_combination moebiusReal x.2 * (k : ℝ) * hmulR
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    Nat.sum_divisorsAntidiagonal' (fun _ b => moebiusReal b),
    sum_divisors_moebiusReal_local r, if_neg hr.ne', mul_zero, add_zero]

/-- **Exact `r`-periodicity of `forwardDilatedLimit` on `[0, ∞)`.** -/
theorem forwardDilatedLimit_add_natCast {r : ℕ} (hr : 1 < r) (ε : ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    forwardDilatedLimit r ε (x + r) = forwardDilatedLimit r ε x := by
  unfold forwardDilatedLimit
  refine tsum_congr fun d => ?_
  have hfl : ⌊(d : ℝ) * (x + r)⌋₊ = ⌊(d : ℝ) * x⌋₊ + d * r := by
    rw [show (d : ℝ) * (x + r) = (d : ℝ) * x + ((d * r : ℕ) : ℝ) by push_cast; ring,
      Nat.floor_add_natCast (mul_nonneg (Nat.cast_nonneg d) hx) (d * r)]
  rw [hfl, pmRamanujanPrimitive_re_add_mul_self hr]

/-- **Exact rounding-free Möbius sieve functional equation for `forwardDilatedLimit`.**
For every `r > 1`, `ε > 0`, and `x ∈ ℝ`,
`∑_{m ≥ 1} m^{−1−ε} G_ε(m x) = C_r(⌊x⌋)`. -/
theorem hasSum_forwardDilatedLimit_mul {r : ℕ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasSum (fun m : ℕ =>
        if m = 0 then 0 else (m : ℝ) ^ (-1 - ε) * forwardDilatedLimit r ε ((m : ℝ) * x))
      (pmRamanujanPrimitive r ⌊x⌋₊).re := by
  set H : ℕ × ℕ → ℝ := fun p =>
    if p.1 = 0 then 0
    else (p.1 : ℝ) ^ (-1 - ε) *
      (moebiusReal p.2 * (p.2 : ℝ) ^ (-1 - ε) *
        (pmRamanujanPrimitive r ⌊((p.1 * p.2 : ℕ) : ℝ) * x⌋₊).re)
  have hz : Summable (fun m : ℕ => ‖(m : ℝ) ^ (-1 - ε)‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
      (Real.summable_nat_rpow.mpr (by linarith : -1 - ε < -1))
  have hprod : Summable (fun p : ℕ × ℕ => (p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε)) :=
    summable_mul_of_summable_norm (f := fun m : ℕ => (m : ℝ) ^ (-1 - ε))
      (g := fun m : ℕ => (m : ℝ) ^ (-1 - ε)) hz hz
  have hB0 : 0 ≤ pmRamanujanPrimitiveBound r :=
    (abs_nonneg _).trans ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr 0))
  have hHb : ∀ p : ℕ × ℕ, ‖H p‖ ≤
      pmRamanujanPrimitiveBound r * ((p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε)) := fun p => by
    rw [Real.norm_eq_abs]
    dsimp only [H]
    split_ifs with hp1
    · rw [abs_zero]
      exact mul_nonneg hB0 (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    · rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      have hC : |(pmRamanujanPrimitive r ⌊((p.1 * p.2 : ℕ) : ℝ) * x⌋₊).re| ≤
          pmRamanujanPrimitiveBound r :=
        (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
      calc (p.1 : ℝ) ^ (-1 - ε) *
            (|moebiusReal p.2| * (p.2 : ℝ) ^ (-1 - ε) *
              |(pmRamanujanPrimitive r ⌊((p.1 * p.2 : ℕ) : ℝ) * x⌋₊).re|)
          ≤ (p.1 : ℝ) ^ (-1 - ε) *
            (1 * (p.2 : ℝ) ^ (-1 - ε) * pmRamanujanPrimitiveBound r) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (mul_le_mul_of_nonneg_right (abs_moebiusReal_le_one_local p.2)
                (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hC (abs_nonneg _)
                (by positivity))
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = _ := by ring
  have hH : Summable H := (hprod.mul_left _).of_norm_bounded hHb
  have hrow : ∀ m : ℕ, HasSum (fun d => H (m, d))
      (if m = 0 then 0 else (m : ℝ) ^ (-1 - ε) * forwardDilatedLimit r ε ((m : ℝ) * x)) := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp [H]
    · simp only [if_neg hm, H]
      refine ((summable_forwardDilatedLimit_term hr hε ((m : ℝ) * x)).hasSum.mul_left
        ((m : ℝ) ^ (-1 - ε))).congr_fun fun d => ?_
      rw [show ((m * d : ℕ) : ℝ) * x = (d : ℝ) * ((m : ℝ) * x) by push_cast; ring]
  have hval : ∀ j : ℕ, ∑' p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {j}), H p =
      if j = 1 then (pmRamanujanPrimitive r ⌊x⌋₊).re else 0 := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · have h0 : ∀ p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {0}), H p = 0 := fun p => by
        rcases Nat.mul_eq_zero.mp p.2 with hp1 | hp2
        · simp [H, hp1]
        · simp [H, hp2, pmRamanujanPrimitive]
      rw [tsum_congr h0, tsum_zero, if_neg (by norm_num)]
    · rw [show (fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {j} = j.divisorsAntidiagonal by ext; simp [hj],
        Finset.tsum_subtype' j.divisorsAntidiagonal H]
      have hfac : ∀ p ∈ j.divisorsAntidiagonal, H p =
          ((j : ℝ) ^ (-1 - ε) * (pmRamanujanPrimitive r ⌊(j : ℝ) * x⌋₊).re) *
            moebiusReal p.2 := fun p hp => by
        have hmul : p.1 * p.2 = j := (Nat.mem_divisorsAntidiagonal.mp hp).1
        have hp1 : p.1 ≠ 0 := fun h0 => hj (by rw [← hmul, h0, zero_mul])
        dsimp only [H]
        rw [if_neg hp1, hmul]
        have hrp : (p.1 : ℝ) ^ (-1 - ε) * (p.2 : ℝ) ^ (-1 - ε) = (j : ℝ) ^ (-1 - ε) := by
          rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), ← Nat.cast_mul, hmul]
        linear_combination moebiusReal p.2 * (pmRamanujanPrimitive r ⌊(j : ℝ) * x⌋₊).re * hrp
      rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum,
        Nat.sum_divisorsAntidiagonal' (fun _ b => moebiusReal b),
        sum_divisors_moebiusReal_local j]
      split_ifs with h1
      · subst h1; simp
      · simp
  have hfib := hH.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1 * p.2)
  rw [show (fun j => ∑' p : ((fun p : ℕ × ℕ => p.1 * p.2) ⁻¹' {j}), H p) =
    fun j => if j = 1 then (pmRamanujanPrimitive r ⌊x⌋₊).re else 0 from funext hval] at hfib
  have htot : ∑' p, H p = (pmRamanujanPrimitive r ⌊x⌋₊).re := hfib.unique (hasSum_ite_eq 1 _)
  rw [← htot]
  exact hH.hasSum.prod_fiberwise hrow

/-- **Homogeneous dilation fixed-point equation on `(-∞, 1)`.**
For every `r > 1`, `ε > 0`, and `x < 1` (in particular every `x ∈ (0, 1)`),
`G_ε(x) = −∑_{m ≥ 2} m^{−1−ε} G_ε(m x)` with zero rounding error. -/
theorem forwardDilatedLimit_eq_neg_tsum_of_lt_one {r : ℕ} (hr : 1 < r) {ε : ℝ} (hε : 0 < ε)
    {x : ℝ} (hx : x < 1) :
    forwardDilatedLimit r ε x =
      -∑' k : ℕ, ((k + 2 : ℕ) : ℝ) ^ (-1 - ε) *
        forwardDilatedLimit r ε (((k + 2 : ℕ) : ℝ) * x) := by
  have hsum := hasSum_forwardDilatedLimit_mul hr hε x
  have hsplit := hsum.summable.sum_add_tsum_nat_add 2
  have h0 : (pmRamanujanPrimitive r 0).re = 0 := by simp [pmRamanujanPrimitive]
  rw [hsum.tsum_eq, Nat.floor_eq_zero.mpr hx, h0] at hsplit
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ↓reduceIte,
    Nat.one_ne_zero, Nat.cast_one, Real.one_rpow, one_mul] at hsplit
  have htail_congr : (∑' k : ℕ,
      if k + 2 = 0 then (0 : ℝ)
      else ((k + 2 : ℕ) : ℝ) ^ (-1 - ε) *
        forwardDilatedLimit r ε (((k + 2 : ℕ) : ℝ) * x)) =
      ∑' k : ℕ, ((k + 2 : ℕ) : ℝ) ^ (-1 - ε) *
        forwardDilatedLimit r ε (((k + 2 : ℕ) : ℝ) * x) :=
    tsum_congr fun k => by simp
  rw [htail_congr] at hsplit
  linarith

end GaloisForLFunctions.SignedSuccessorArithmetic
