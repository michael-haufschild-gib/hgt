import GaloisForLFunctions.RHTower.LiouvilleHyperbolaCutoffWide

/-!
# The cutoff transport law up to the three-quarter cut

`LiouvilleHyperbolaCutoffWide` proves that the Möbius head `A_θ` of the Liouville hyperbola
decomposition, cut at `x^θ`, oscillates beyond `x^{1-θ/2-ε}` in every combination `dP + cA_θ`,
`c ≠ 0`, for `θ < 2/3`. The limit came from the remainder `E_θ = O(x^θ)`, whose transform is only
known to be holomorphic on `Re z > θ`.

Here the limit is moved to `θ < 3/4`.

* The square-lattice remainder `W(y) - Zy + 2√y` equals `½ + O(y^{-1/2})`
  (`abs_squareTriangle_remainder_sub_half_le`), from the two-sided telescoping bounds
  `1/(q+½) - (1/9)/(q+½)³ ≤ Σ_{k>q} 1/k² ≤ 1/(q+½)` (`squareTail_bounds_sharp`).
* So `E_θ(x) = ½M(x^θ) + O(x^{(3θ-1)/2})` with `M` the Mertens function
  (`abs_refinedRemainder_le`). The Mertens head has transform `1/(2sζ(s/θ))`
  (`integral_mertensHead`), and the refined remainder is holomorphic on `Re z > (3θ-1)/2`
  (`analyticOnNhd_refinedRemainderTransform`); `(3θ-1)/2 < 1 - θ/2` exactly when `θ < 3/4`.
* At `w = 1 + θ(ρ - 1)` the Mertens-head argument is `w/θ = ρ + (1/θ - 1)`, on the horizontal line
  of `ρ`; for a horizontal-singleton zero `ρ` it is not a zero
  (`zetaResidueUnit_div_ne_zero_of_singleton`), so the new pole term does not cancel the transported
  pole.

**Theorem** (`frequently_gt_and_frequently_lt_tq`). For every `0 < θ < 3/4`, real `d`, `c ≠ 0`,
`β < 1 - θ/2` and `C ≥ 0`, `dP + cA_θ` exceeds `C x^β` and falls below `-C x^β` for arbitrarily
large `x`.
-/

open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.RHTower
open RHTower.LiouvilleTriangularHeadOscillation
open RHTower.LiouvilleHyperbolaCutoffOscillation
open RHTower.LiouvilleHyperbolaCutoffWide

namespace RHTower.LiouvilleHyperbolaCutoffThreeQuarter

noncomputable section

/-! ## The square lattice remainder is `½ + O(y^{-1/2})` -/

/-- `Σ_n ((n+a)^{-p} - (n+a+1)^{-p}) = a^{-p}` for `a > 0`. -/
theorem hasSum_inv_pow_sub (a : ℝ) (ha : 0 < a) {p : ℕ} (hp : 0 < p) :
    HasSum (fun n : ℕ => (((n : ℝ) + a) ^ p)⁻¹ - (((n : ℝ) + a + 1) ^ p)⁻¹) (a ^ p)⁻¹ := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => sub_nonneg.mpr
    (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) p))) _).mpr
  have heq (N : ℕ) : ∑ n ∈ Finset.range N, ((((n : ℝ) + a) ^ p)⁻¹ - (((n : ℝ) + a + 1) ^ p)⁻¹)
      = (a ^ p)⁻¹ - (((N : ℝ) + a) ^ p)⁻¹ := by
    have := Finset.sum_range_sub' (fun n : ℕ => (((n : ℝ) + a) ^ p)⁻¹) N
    simpa [Nat.cast_add, Nat.cast_one, add_right_comm, add_comm, add_assoc] using this
  simp only [heq]
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) + a) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have ht : Tendsto (fun N : ℕ => (((N : ℝ) + a) ^ p)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop hp.ne').comp h1)
  simpa using tendsto_const_nhds.sub ht

/-- The tail `Σ_{k > q} 1/k²` as a `tsum`. -/
theorem squareMass_sub_eq_tsum (q : ℕ) :
    LiouvilleTriangularShortHead.squareMass - ∑ n ∈ Finset.range q, 1 / ((n : ℝ) + 1) ^ 2
      = ∑' n : ℕ, 1 / ((n : ℝ) + q + 1) ^ 2 := by
  have hs : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)))
  have h := hs.sum_add_tsum_nat_add q
  simp only [Nat.cast_add] at h
  unfold LiouvilleTriangularShortHead.squareMass
  have : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + (q : ℝ) + 1) ^ 2 = 1 / ((n : ℝ) + q + 1) ^ 2 := fun _ => rfl
  linarith

/-- Termwise upper comparison: `1/(A+½)² ≤ 1/A - 1/(A+1)` for `A > 0`. -/
theorem inv_sq_le_telescope {A : ℝ} (hA : 0 < A) :
    1 / (A + 1 / 2) ^ 2 ≤ (A ^ 1)⁻¹ - ((A + 1) ^ 1)⁻¹ := by
  rw [pow_one, pow_one, inv_sub_inv hA.ne' (by linarith), div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith

/-- Termwise lower comparison:
`1/A - 1/(A+1) - (1/9)(1/A³ - 1/(A+1)³) ≤ 1/(A+½)²` for `A ≥ ½`. -/
theorem telescope_le_inv_sq {A : ℝ} (hA : 1 / 2 ≤ A) :
    (A ^ 1)⁻¹ - ((A + 1) ^ 1)⁻¹ - 1 / 9 * ((A ^ 3)⁻¹ - ((A + 1) ^ 3)⁻¹)
      ≤ 1 / (A + 1 / 2) ^ 2 := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < A + 1 := by linarith
  have e : (A ^ 1)⁻¹ - ((A + 1) ^ 1)⁻¹ - 1 / 9 * ((A ^ 3)⁻¹ - ((A + 1) ^ 3)⁻¹)
      = (9 * A ^ 2 * (A + 1) ^ 2 - ((A + 1) ^ 3 - A ^ 3)) / (9 * (A * (A + 1)) ^ 3) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hA0 hB0, pow_pos hA0 3, pow_pos hA0 4, pow_pos hA0 5, pow_pos hA0 6,
    sq_nonneg (A - 1 / 2)]

/-- Two-sided telescoping bound for the square tail:
`1/(q+½) - (1/9)/(q+½)³ ≤ Σ_{k>q} 1/k² ≤ 1/(q+½)`. -/
theorem squareTail_bounds_sharp (q : ℕ) :
    1 / ((q : ℝ) + 1 / 2) - 1 / 9 * (1 / ((q : ℝ) + 1 / 2) ^ 3)
      ≤ ∑' n : ℕ, 1 / ((n : ℝ) + q + 1) ^ 2 ∧
    ∑' n : ℕ, 1 / ((n : ℝ) + q + 1) ^ 2 ≤ 1 / ((q : ℝ) + 1 / 2) := by
  have ha : (0 : ℝ) < q + 1 / 2 := by positivity
  have h1 := hasSum_inv_pow_sub ((q : ℝ) + 1 / 2) ha (by norm_num : 0 < 1)
  have h3 := hasSum_inv_pow_sub ((q : ℝ) + 1 / 2) ha (by norm_num : 0 < 3)
  have hs : Summable fun n : ℕ => 1 / ((n : ℝ) + q + 1) ^ 2 := by
    have : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)))
    simpa only [Nat.cast_add, add_assoc, add_comm (1 : ℝ)] using (summable_nat_add_iff q).mpr this
  have hk : ∀ n : ℕ, (n : ℝ) + q + 1 = (n : ℝ) + ((q : ℝ) + 1 / 2) + 1 / 2 := fun n => by ring
  constructor
  · have hcomb := h1.sub (h3.mul_left (1 / 9))
    have hval : (((q : ℝ) + 1 / 2) ^ 1)⁻¹ - 1 / 9 * (((q : ℝ) + 1 / 2) ^ 3)⁻¹
        = 1 / ((q : ℝ) + 1 / 2) - 1 / 9 * (1 / ((q : ℝ) + 1 / 2) ^ 3) := by
      simp [one_div]
    rw [← hval, ← hcomb.tsum_eq]
    refine Summable.tsum_le_tsum (fun n => ?_) hcomb.summable hs
    rw [hk n]
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h0' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    exact telescope_le_inv_sq (by linarith)
  · have hval : 1 / ((q : ℝ) + 1 / 2) = (((q : ℝ) + 1 / 2) ^ 1)⁻¹ := by simp
    rw [hval, ← h1.tsum_eq]
    refine Summable.tsum_le_tsum (fun n => ?_) hs h1.summable
    rw [hk n]
    exact inv_sq_le_telescope (by positivity)

theorem squareTriangle_eq' (y : ℝ) :
    LiouvilleTriangularShortHead.squareTriangle y
      = y * (∑ n ∈ Finset.range ⌊Real.sqrt y⌋₊, 1 / ((n : ℝ) + 1) ^ 2) - (⌊Real.sqrt y⌋₊ : ℝ) := by
  simp only [LiouvilleTriangularShortHead.squareTriangle, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Finset.mul_sum, mul_one_div]

/-- **The square-lattice remainder is `½ + O(y^{-1/2})`:**
`|W(y) - Zy + 2√y - ½| ≤ 1/√y` for `y ≥ 1`. -/
theorem abs_squareTriangle_remainder_sub_half_le {y : ℝ} (hy : 1 ≤ y) :
    |LiouvilleTriangularShortHead.squareTriangle y - LiouvilleTriangularShortHead.squareMass * y
      + 2 * Real.sqrt y - 1 / 2| ≤ 1 / Real.sqrt y := by
  set s := Real.sqrt y with hsdef
  set q := ⌊s⌋₊ with hqdef
  have hs1 : 1 ≤ s := by rw [hsdef]; exact Real.one_le_sqrt.mpr hy
  have hys : y = s ^ 2 := by rw [hsdef, Real.sq_sqrt (by linarith)]
  have hq1 : (1 : ℝ) ≤ q := by
    have : 1 ≤ q := Nat.le_floor (by exact_mod_cast hs1)
    exact_mod_cast this
  have hqs : (q : ℝ) ≤ s := Nat.floor_le (by linarith)
  have hsq : s < (q : ℝ) + 1 := Nat.lt_floor_add_one s
  obtain ⟨hTlo, hTup⟩ := squareTail_bounds_sharp q
  rw [← squareMass_sub_eq_tsum] at hTlo hTup
  set T := LiouvilleTriangularShortHead.squareMass -
    ∑ n ∈ Finset.range q, 1 / ((n : ℝ) + 1) ^ 2 with hTdef
  set P : ℝ := (q : ℝ) + 1 / 2 with hPdef
  have hP : 0 < P := by rw [hPdef]; linarith
  have hsP : s ≤ 2 * P := by rw [hPdef]; linarith
  have hE : LiouvilleTriangularShortHead.squareTriangle y
      - LiouvilleTriangularShortHead.squareMass * y + 2 * s - 1 / 2
      = -(s ^ 2 * T) - (P - 1 / 2) + 2 * s - 1 / 2 := by
    rw [squareTriangle_eq', ← hsdef, ← hqdef, hTdef, hPdef, hys]; ring
  rw [hE, abs_le]
  have hs0 : 0 < s := by linarith
  constructor
  · -- lower: -(s - P)²/P ≥ -1/(4P) ≥ -1/s
    have h1 : -(s ^ 2 * T) ≥ -(s ^ 2 * (1 / P)) := by
      have := mul_le_mul_of_nonneg_left hTup (sq_nonneg s); linarith
    have h2 : -(s ^ 2 * (1 / P)) - (P - 1 / 2) + 2 * s - 1 / 2 = -((s - P) ^ 2 / P) := by
      field_simp; ring
    have hd : (s - P) ^ 2 ≤ 1 / 4 := by
      have h5 : -(1 / 2) ≤ s - P := by rw [hPdef]; linarith
      have h6 : s - P ≤ 1 / 2 := by rw [hPdef]; linarith
      nlinarith
    have h3 : (s - P) ^ 2 / P ≤ 1 / s := by
      rw [div_le_div_iff₀ hP hs0]
      nlinarith [sq_nonneg (s - P), mul_le_mul_of_nonneg_right hd hs0.le]
    linarith
  · -- upper: -(s-P)²/P + s²/(9P³) ≤ s²/(9P³) ≤ 1/s
    have h1 : -(s ^ 2 * T) ≤ -(s ^ 2 * (1 / P - 1 / 9 * (1 / P ^ 3))) := by
      have := mul_le_mul_of_nonneg_left hTlo (sq_nonneg s); linarith
    have h2 : -(s ^ 2 * (1 / P - 1 / 9 * (1 / P ^ 3))) - (P - 1 / 2) + 2 * s - 1 / 2
        = -((s - P) ^ 2 / P) + s ^ 2 / (9 * P ^ 3) := by
      field_simp; ring
    have h3 : 0 ≤ (s - P) ^ 2 / P := by positivity
    have h4 : s ^ 2 / (9 * P ^ 3) ≤ 1 / s := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      have : s ^ 3 ≤ (2 * P) ^ 3 := pow_le_pow_left₀ hs0.le hsP 3
      nlinarith [pow_pos hP 3]
    linarith

/-! ## The Mertens head and the refined remainder -/

/-- `E'_θ(x) = E_θ(x) - ½M(x^θ)`, the remainder after the Mertens head. -/
def refinedRemainder (θ x : ℝ) : ℝ := cutoffRemainder θ x - 1 / 2 * mertensFunctionReal (x ^ θ)

theorem measurable_refinedRemainder (θ : ℝ) : Measurable (refinedRemainder θ) :=
  (measurable_cutoffRemainder θ).sub (measurable_const.mul
    (measurable_mertensFunctionReal.comp (measurable_id.pow_const θ)))

theorem refinedRemainder_eq (θ x : ℝ) :
    refinedRemainder θ x = ∑ m ∈ Finset.Icc 1 ⌊x ^ θ⌋₊,
      ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        (LiouvilleTriangularShortHead.squareTriangle (x / m)
          - LiouvilleTriangularShortHead.squareMass * (x / m) + 2 * Real.sqrt (x / m) - 1 / 2) := by
  unfold refinedRemainder mertensFunctionReal
  rw [cutoffRemainder_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- `|E'_θ(x)| ≤ x^θ · x^{θ/2} / √x` for `x ≥ 1`, `θ ≤ 1`. -/
theorem abs_refinedRemainder_le {θ x : ℝ} (hθ1 : θ ≤ 1) (hx : 1 ≤ x) :
    |refinedRemainder θ x| ≤ x ^ θ * Real.sqrt (x ^ θ) / Real.sqrt x := by
  rw [refinedRemainder_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hxθ : x ^ θ ≤ x := Real.rpow_le_self_of_one_le hx hθ1
  have hxθ0 : 0 ≤ x ^ θ := Real.rpow_nonneg (by linarith) θ
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  calc ∑ m ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, |((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        (LiouvilleTriangularShortHead.squareTriangle (x / m)
          - LiouvilleTriangularShortHead.squareMass * (x / m) + 2 * Real.sqrt (x / m) - 1 / 2)|
      ≤ ∑ _m ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, Real.sqrt (x ^ θ) / Real.sqrt x := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
        have hmθ : (m : ℝ) ≤ x ^ θ := by
          have h1 : (m : ℝ) ≤ ⌊x ^ θ⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hm).2
          exact h1.trans (Nat.floor_le hxθ0)
        have hxm : 1 ≤ x / m := (le_div_iff₀ (by linarith)).mpr (by linarith)
        rw [abs_mul]
        have hr := abs_squareTriangle_remainder_sub_half_le hxm
        have hsq : 1 / Real.sqrt (x / m) = Real.sqrt m / Real.sqrt x := by
          rw [Real.sqrt_div' x (by linarith : (0 : ℝ) ≤ m)]
          field_simp
        calc |((ArithmeticFunction.moebius m : ℤ) : ℝ)| *
              |LiouvilleTriangularShortHead.squareTriangle (x / m)
              - LiouvilleTriangularShortHead.squareMass * (x / m)
              + 2 * Real.sqrt (x / m) - 1 / 2|
            ≤ 1 * (1 / Real.sqrt (x / m)) :=
              mul_le_mul (abs_moebius_cast_le_one m) hr (abs_nonneg _) zero_le_one
          _ = Real.sqrt m / Real.sqrt x := by rw [one_mul, hsq]
          _ ≤ Real.sqrt (x ^ θ) / Real.sqrt x :=
              div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hmθ) hsx.le
    _ ≤ x ^ θ * Real.sqrt (x ^ θ) / Real.sqrt x := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (Nat.floor_le hxθ0) (by positivity)

theorem abs_refinedRemainder_exp_le {θ u : ℝ} (hθ1 : θ ≤ 1) (hu : 0 ≤ u) :
    |refinedRemainder θ (Real.exp u)| ≤ Real.exp ((3 * θ - 1) / 2 * u) := by
  refine (abs_refinedRemainder_le hθ1 (Real.one_le_exp hu)).trans (le_of_eq ?_)
  rw [exp_rpow_eq_exp_mul, sqrt_exp_eq_exp_half_mul, sqrt_exp_eq_exp_half_mul,
    div_eq_iff (Real.exp_pos _).ne', ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The transform of the refined remainder. -/
def refinedRemainderTransform (θ : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (refinedRemainder θ (Real.exp u) : ℂ) * Complex.exp (-z * u)

theorem analyticOnNhd_refinedRemainderTransform {θ : ℝ} (hθ0 : 1 / 3 ≤ θ) (hθ1 : θ ≤ 1) :
    AnalyticOnNhd ℂ (refinedRemainderTransform θ) {z : ℂ | (3 * θ - 1) / 2 < z.re} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (differentiableAt_integral_mul_cexp_exp
      ((measurable_refinedRemainder θ).comp Real.measurable_exp) (by linarith)
      (fun _ hu => abs_refinedRemainder_exp_le hθ1 hu.le) hz).differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

/-- `∫_0^∞ ½M(e^{θu}) e^{-su} du = 1/(2sζ(s/θ))` on `Re s > θ`. -/
theorem integral_mertensHead {θ : ℝ} (hθ0 : 0 < θ) {s : ℂ} (hs : θ < s.re) :
    ∫ u in Ioi (0 : ℝ), ((1 / 2 * mertensFunctionReal (Real.exp u ^ θ) : ℝ) : ℂ)
        * Complex.exp (-s * u)
      = 1 / (2 * s * riemannZeta (s / θ)) := by
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  set g : ℝ → ℂ := fun v => ((1 / 2 * mertensFunctionReal (Real.exp v) : ℝ) : ℂ)
    * Complex.exp (-(s / θ) * v) with hg
  have hpt : ∀ u : ℝ, ((1 / 2 * mertensFunctionReal (Real.exp u ^ θ) : ℝ) : ℂ)
      * Complex.exp (-s * u) = g (θ * u) := by
    intro u
    simp only [hg]
    rw [exp_rpow_eq_exp_mul]
    congr 2
    push_cast
    field_simp
  have hre : 1 < (s / θ).re := by
    rw [show s / (θ : ℂ) = s * ((θ⁻¹ : ℝ) : ℂ) by push_cast; ring,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      ← div_eq_mul_inv, lt_div_iff₀ hθ0]
    linarith
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs; linarith
  have hM := integral_mertensFunctionReal_exp_mul_cexp hre
  have hg' : ∫ v in Ioi (0 : ℝ), g v = (1 / 2 : ℂ) * ∫ v in Ioi (0 : ℝ),
      (mertensFunctionReal (Real.exp v) : ℂ) * Complex.exp (-(s / θ) * v) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [hg]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u), integral_comp_mul g hθ0, hg',
    hM]
  field_simp

/-! ## Transforms with the Mertens head -/

theorem cutoffRemainderTransform_eq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {s : ℂ}
    (hs : 2 < s.re) :
    cutoffRemainderTransform θ s
      = 1 / (2 * s * riemannZeta (s / θ)) + refinedRemainderTransform θ s := by
  have i1 : IntegrableOn (fun u : ℝ => ((1 / 2 * mertensFunctionReal (Real.exp u ^ θ) : ℝ) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le
      (g := fun u => 1 / 2 * mertensFunctionReal (Real.exp u ^ θ)) (C := 1) (a := θ)
      (measurable_const.mul (measurable_mertensFunctionReal.comp
        (Real.measurable_exp.pow_const θ)))
      (fun u _ => by
        rw [exp_rpow_eq_exp_mul, abs_mul, one_mul]
        have h := abs_mertensFunctionReal_exp_le (θ * u)
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        nlinarith [Real.exp_pos (θ * u)]) (by linarith)
  have i2 : IntegrableOn (fun u : ℝ => (refinedRemainder θ (Real.exp u) : ℂ)
      * Complex.exp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (C := 1) (a := (3 * θ - 1) / 2)
      ((measurable_refinedRemainder θ).comp Real.measurable_exp)
      (fun u hu => by simpa using abs_refinedRemainder_exp_le hθ1.le hu.le) (by linarith)
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (cutoffRemainder θ (Real.exp u) : ℂ) * Complex.exp (-s * u)
      = ((1 / 2 * mertensFunctionReal (Real.exp u ^ θ) : ℝ) : ℂ) * Complex.exp (-s * u)
        + (refinedRemainder θ (Real.exp u) : ℂ) * Complex.exp (-s * u) := by
    intro u _
    unfold refinedRemainder
    push_cast
    ring
  unfold cutoffRemainderTransform refinedRemainderTransform
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i1 i2,
    integral_mertensHead hθ0 (by linarith)]

/-- The four-term transform of `dP + cA_θ`. -/
def tqPoleModel (θ d c : ℝ) (z : ℂ) : ℂ :=
  cutPoleModel θ d c z + c * ((z / θ - 1) / (2 * z * RHTower.zetaResidueUnit (z / θ)))

/-- `D₄(z) = D(z) U(z/θ)`. -/
def tqPoleDenominator (θ : ℝ) (z : ℂ) : ℂ :=
  cutPoleDenominator θ z * RHTower.zetaResidueUnit (z / θ)

/-- The four-term model times `D₄`, without denominators. -/
def tqPoleNumerator (θ d c : ℝ) (z : ℂ) : ℂ :=
  cutPoleNumerator θ d c z * RHTower.zetaResidueUnit (z / θ)
    + c * ((z / θ - 1) / 2) * (RHTower.zetaResidueUnit z * (z - 1 / 2)
      * RHTower.zetaResidueUnit (rootArg θ z) * RHTower.zetaResidueUnit (headArg θ z))

theorem tqPoleModel_mul_denominator (θ d c : ℝ) (hθ : (θ : ℂ) ≠ 0) {z : ℂ} (h0 : z ≠ 0)
    (hU : RHTower.zetaResidueUnit z ≠ 0) (hh : z - 1 / 2 ≠ 0)
    (hUv : RHTower.zetaResidueUnit (rootArg θ z) ≠ 0)
    (hUh : RHTower.zetaResidueUnit (headArg θ z) ≠ 0)
    (hUq : RHTower.zetaResidueUnit (z / θ) ≠ 0) :
    tqPoleModel θ d c z * tqPoleDenominator θ z = tqPoleNumerator θ d c z := by
  have hbase := cutPoleModel_mul_denominator θ d c hθ h0 hU hh hUv hUh
  unfold tqPoleModel tqPoleDenominator tqPoleNumerator
  rw [← hbase]
  unfold cutPoleDenominator
  field_simp

theorem differentiableAt_tqPoleDenominator (θ : ℝ) (z : ℂ) :
    DifferentiableAt ℂ (tqPoleDenominator θ) z := by
  unfold tqPoleDenominator
  exact (differentiableAt_cutPoleDenominator θ z).mul
    ((RHTower.analyticAt_zetaResidueUnit _).differentiableAt.comp z (by fun_prop))

theorem differentiableAt_tqPoleNumerator (θ d c : ℝ) {z : ℂ} (hz : 2 * z ≠ 1) :
    DifferentiableAt ℂ (tqPoleNumerator θ d c) z := by
  have hu := fun w => (RHTower.analyticAt_zetaResidueUnit w).differentiableAt
  have hq : DifferentiableAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (z / θ)) z :=
    (hu _).comp z (by fun_prop)
  have hv : DifferentiableAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (rootArg θ z)) z :=
    (hu _).comp z (by unfold rootArg; fun_prop)
  have hh : DifferentiableAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (headArg θ z)) z :=
    (hu _).comp z (by unfold headArg; fun_prop)
  unfold tqPoleNumerator
  exact ((differentiableAt_cutPoleNumerator θ d c hz).mul hq).add
    (((differentiableAt_const _).mul (by fun_prop)).mul
      ((((hu z).mul (differentiableAt_id.sub_const _)).mul hv).mul hh))

theorem analyticAt_tqPoleModel_ofReal {θ : ℝ} (hθ0 : 0 < θ) (d c : ℝ) {t : ℝ}
    (ht : 1 / 2 < t) (htθ : 1 - θ < t) :
    AnalyticAt ℂ (tqPoleModel θ d c) t := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < t).ne'
  have hq : RHTower.zetaResidueUnit ((t : ℂ) / θ) ≠ 0 := by
    have := zetaResidueUnit_ofReal_ne_zero (div_pos (by linarith : (0 : ℝ) < t) hθ0)
    push_cast at this; exact this
  have hA : AnalyticAt ℂ (fun z : ℂ => RHTower.zetaResidueUnit (z / θ)) t :=
    (RHTower.analyticAt_zetaResidueUnit _).comp (by fun_prop)
  unfold tqPoleModel
  exact (analyticAt_cutPoleModel_ofReal hθ0 d c ht htθ).add
    (analyticAt_const.mul ((by fun_prop : AnalyticAt ℂ (fun z : ℂ => z / θ - 1) t).div
      ((analyticAt_const.mul analyticAt_id).mul hA) (mul_ne_zero (mul_ne_zero two_ne_zero ht0)
        hq)))

/-- On `Re s > 2` the transform of `dP + cA_θ` is the four-term model plus `cR'_θ(s)`. -/
theorem integral_cutCombination_exp_mul_cexp_tq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (d c : ℝ) {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), ((d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)
        : ℝ) : ℂ) * Complex.exp (-s * u)
      = tqPoleModel θ d c s + c * refinedRemainderTransform θ s := by
  rw [integral_cutCombination_exp_mul_cexp_wide hθ0 hθ1 d c hs,
    cutoffRemainderTransform_eq hθ0 hθ1 hs]
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs; linarith
  have hre : 1 < (s / θ).re := by
    rw [show s / (θ : ℂ) = s * ((θ⁻¹ : ℝ) : ℂ) by push_cast; ring,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      ← div_eq_mul_inv, lt_div_iff₀ hθ0]
    linarith
  have hq1 : s / θ ≠ 1 := by intro h; rw [h, Complex.one_re] at hre; linarith
  have hz : riemannZeta (s / θ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hre
  unfold tqPoleModel
  rw [zetaResidueUnit_eq hq1]
  have hd : s / θ - 1 ≠ 0 := sub_ne_zero.mpr hq1
  have key : (s / θ - 1) / (2 * s * ((s / θ - 1) * riemannZeta (s / θ)))
      = 1 / (2 * s * riemannZeta (s / θ)) := by
    rw [show 2 * s * ((s / θ - 1) * riemannZeta (s / θ))
        = (s / θ - 1) * (2 * s * riemannZeta (s / θ)) by ring,
      div_mul_eq_div_div, div_self hd]
  rw [key]
  ring

/-! ## The contradiction with the Mertens head -/

theorem false_of_oneSided_tq {θ d c η C β K : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C) (hβθ : 1 - θ < β) (hθ3 : 1 / 3 ≤ θ)
    (hβr : (3 * θ - 1) / 2 < β) (hβh : 1 / 2 < β)
    (hK : 0 ≤ K) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hρlo : 1 / 2 ≤ ρ.re) (hρhi : ρ.re < 1) (hρim : ρ.im ≠ 0)
    (hwz : riemannZeta (1 + θ * (ρ - 1)) ≠ 0)
    (hUv : RHTower.zetaResidueUnit (rootArg θ (1 + θ * (ρ - 1))) ≠ 0)
    (hUq : RHTower.zetaResidueUnit ((1 + θ * (ρ - 1)) / θ) ≠ 0)
    (hβw : β < 1 - θ * (1 - ρ.re))
    (hg : ∀ u, 0 < u → η * (d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u))
      ≤ C * Real.exp (β * u) + K) :
    False := by
  set Z := LiouvilleTriangularShortHead.squareMass with hZdef
  have hZ := squareMass_pos
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  set f : ℝ → ℝ := fun u => d * liouvilleTriangle (Real.exp u) + c * cutoffHead θ (Real.exp u)
    with hfdef
  have hf : Measurable f := (measurable_const.mul
    (measurable_liouvilleTriangle.comp Real.measurable_exp)).add
    (measurable_const.mul ((measurable_cutoffHead θ).comp Real.measurable_exp))
  set B : ℝ := 2 * |d| + |c| * (Z + 3) with hBdef
  have hB : 0 ≤ B := by positivity
  have hb : ∀ u, 0 < u → |f u| ≤ B * Real.exp (2 * u) := fun u hu =>
    abs_cutCombination_exp_le_wide hθ1.le d c hu.le
  have hβ0 : 0 ≤ β := by linarith
  have hβ2 : β ≤ 2 := by nlinarith
  have hCC : C < C + 1 := lt_add_one C
  obtain ⟨hc0, hlo, hhi⟩ := isAbscissa_oneSidedMeasure hf hη hC hCC hK hB hβ2
    (by norm_num) hb hg
  set ν := expOneSidedMeasure f η (C + 1) β K with hνdef
  set Ψ : ℂ → ℂ := fun z => ((C + 1 : ℝ) : ℂ) / (z - β) + (K : ℂ) / z
      - η * (tqPoleModel θ d c z + c * refinedRemainderTransform θ z) with hΨdef
  have hagree : ∀ z : ℂ, 2 < z.re → complexLaplace ν z = Ψ z := by
    intro z hz
    rw [complexLaplace_oneSidedMeasure_eq hf hβ0 hβ2 hCC.le hb hg hz]
    simp only [hΨdef, hfdef]
    rw [integral_cutCombination_exp_mul_cexp_tq hθ0 hθ1 d c hz]
  have hΨa : ∀ t : ℝ, β < t → AnalyticAt ℂ Ψ t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < t).ne'
    have htβ : (t : ℂ) - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hP := analyticAt_tqPoleModel_ofReal hθ0 d c (by linarith : (1 : ℝ) / 2 < t)
      (by linarith : 1 - θ < t)
    have hR : AnalyticAt ℂ (refinedRemainderTransform θ) t :=
      analyticOnNhd_refinedRemainderTransform hθ3 hθ1.le t (by simp; linarith)
    simp only [hΨdef]
    exact ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) htβ).add
      (analyticAt_const.div analyticAt_id ht0)).sub
      (analyticAt_const.mul (hP.add (analyticAt_const.mul hR)))
  have hcβ : IsAbscissa ν β := isAbscissa_eq_of_analyticAt_real hc0 hlo hhi hΨa hagree
  set V : Set ℂ := {z : ℂ | β < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  set Lf : ℂ → ℂ := fun z => (((C + 1 : ℝ) : ℂ) / (z - β) + (K : ℂ) / z
      - complexLaplace ν z) * tqPoleDenominator θ z with hLf
  set Rf : ℂ → ℂ := fun z => (η : ℂ) * (tqPoleNumerator θ d c z
      + c * refinedRemainderTransform θ z * tqPoleDenominator θ z) with hRf
  have hLa : AnalyticOnNhd ℂ Lf V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hVo
    have hz' : β < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz'; linarith
    have hzβ : z - β ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have d1 : DifferentiableAt ℂ (fun z : ℂ => ((C + 1 : ℝ) : ℂ) / (z - β)) z :=
      (differentiableAt_const _).div (differentiableAt_id.sub_const _) hzβ
    have d2 : DifferentiableAt ℂ (fun z : ℂ => (K : ℂ) / z) z :=
      (differentiableAt_const _).div differentiableAt_id hz0
    exact (((d1.add d2).sub (hasDerivAt_complexLaplace hcβ hz').differentiableAt).mul
      (differentiableAt_tqPoleDenominator θ z)).differentiableWithinAt
  have hRa : AnalyticOnNhd ℂ Rf V := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hVo
    have hz' : β < z.re := hz
    have h2z : 2 * z ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hR : DifferentiableAt ℂ (refinedRemainderTransform θ) z :=
      (analyticOnNhd_refinedRemainderTransform hθ3 hθ1.le z
        (by simp; linarith)).differentiableAt
    exact ((differentiableAt_const _).mul ((differentiableAt_tqPoleNumerator θ d c h2z).add
      (((differentiableAt_const _).mul hR).mul
        (differentiableAt_tqPoleDenominator θ z)))).differentiableWithinAt
  have hθre : ∀ w : ℂ, (w / θ).re = w.re / θ := fun w => by
    rw [show w / (θ : ℂ) = w * ((θ⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, div_eq_mul_inv]
  have hev : Lf =ᶠ[𝓝 (3 : ℂ)] Rf := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with z hz
    have hz' : 2 < z.re := hz
    have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz'; linarith
    have hz1 : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hz'; linarith
    have hzh : z - 1 / 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hhre : 1 < (headArg θ z).re := by
      unfold headArg
      rw [Complex.add_re, hθre, Complex.one_re, Complex.sub_re, Complex.one_re]
      have : 0 < (z.re - 1) / θ := div_pos (by linarith) hθ0
      linarith
    have hvre : 1 < (rootArg θ z).re := by
      unfold rootArg
      rw [Complex.add_re, hθre, Complex.sub_re]
      have : 1 ≤ (z.re - (1 / 2 : ℂ).re) / θ := by
        rw [le_div_iff₀ hθ0]; norm_num; linarith
      norm_num at this ⊢
      linarith
    have hh1 : headArg θ z ≠ 1 := by intro h; rw [h, Complex.one_re] at hhre; linarith
    have hv1 : rootArg θ z ≠ 1 := by intro h; rw [h, Complex.one_re] at hvre; linarith
    have hU : RHTower.zetaResidueUnit z ≠ 0 := by
      rw [zetaResidueUnit_eq hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_lt_re (by linarith))
    have hUh : RHTower.zetaResidueUnit (headArg θ z) ≠ 0 := by
      rw [zetaResidueUnit_eq hh1]
      exact mul_ne_zero (sub_ne_zero.mpr hh1) (riemannZeta_ne_zero_of_one_lt_re hhre)
    have hUv : RHTower.zetaResidueUnit (rootArg θ z) ≠ 0 := by
      rw [zetaResidueUnit_eq hv1]
      exact mul_ne_zero (sub_ne_zero.mpr hv1) (riemannZeta_ne_zero_of_one_lt_re hvre)
    have hqre : 1 < (z / θ).re := by
      rw [hθre]; rw [lt_div_iff₀ hθ0]; linarith
    have hq1 : z / θ ≠ 1 := by intro h; rw [h, Complex.one_re] at hqre; linarith
    have hUq : RHTower.zetaResidueUnit (z / θ) ≠ 0 := by
      rw [zetaResidueUnit_eq hq1]
      exact mul_ne_zero (sub_ne_zero.mpr hq1) (riemannZeta_ne_zero_of_one_lt_re hqre)
    simp only [hLf, hRf]
    rw [hagree z hz', ← tqPoleModel_mul_denominator θ d c hθC hz0 hU hzh hUv hUh hUq]
    simp only [hΨdef]
    ring
  have h3V : (3 : ℂ) ∈ V := by show β < (3 : ℂ).re; norm_num; linarith
  have heq := hLa.eqOn_of_preconnected_of_eventuallyEq hRa
    (convex_halfSpace_re_gt β).isPreconnected h3V hev
  set w : ℂ := 1 + θ * (ρ - 1) with hwdef
  have hwre : w.re = 1 - θ * (1 - ρ.re) := by simp [hwdef]; ring
  have hwim : w.im = θ * ρ.im := by simp [hwdef]
  have hwlo : 1 - θ / 2 ≤ w.re := by rw [hwre]; nlinarith
  have hwV : w ∈ V := by show β < w.re; rw [hwre]; exact hβw
  have hhw : headArg θ w = ρ := by
    unfold headArg; rw [hwdef]; field_simp; ring
  have hUh : RHTower.zetaResidueUnit (headArg θ w) = 0 := by
    rw [hhw]; exact zetaResidueUnit_eq_zero_of_riemannZeta_eq_zero hρ
  have hDw : tqPoleDenominator θ w = 0 := by
    unfold tqPoleDenominator cutPoleDenominator; rw [hUh, mul_zero, zero_mul]
  have h := heq hwV
  simp only [hLf, hRf, hDw, mul_zero, add_zero] at h
  have hNw : tqPoleNumerator θ d c w = c * Z / θ * (w * RHTower.zetaResidueUnit w * (w - 1 / 2)
      * RHTower.zetaResidueUnit (rootArg θ w)) * RHTower.zetaResidueUnit (w / θ) := by
    unfold tqPoleNumerator cutPoleNumerator; rw [hUh]; ring
  rw [hNw] at h
  have hη0 : (η : ℂ) ≠ 0 := by
    have : η ≠ 0 := by intro h0; rw [h0, abs_zero] at hη; norm_num at hη
    exact_mod_cast this
  have ha : (c : ℂ) * Z / θ ≠ 0 :=
    div_ne_zero (mul_ne_zero (by exact_mod_cast hc) (by exact_mod_cast hZ.ne')) hθC
  have hw0 : w ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; rw [Complex.zero_re] at this; linarith
  have hw1 : w ≠ 1 := by
    intro h0; have := congrArg Complex.im h0; rw [hwim, Complex.one_im] at this
    exact mul_ne_zero hθ0.ne' hρim this
  have hwh : w - 1 / 2 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hUw : RHTower.zetaResidueUnit w ≠ 0 := by
    rw [zetaResidueUnit_eq hw1]; exact mul_ne_zero (sub_ne_zero.mpr hw1) hwz
  exact (mul_ne_zero hη0 (mul_ne_zero (mul_ne_zero ha (mul_ne_zero (mul_ne_zero
    (mul_ne_zero hw0 hUw) hwh) hUv)) hUq)) h.symm



/-! ## The cutoff law for `0 < θ < 3/4` -/

/-- For a singleton zero `ρ` the Mertens-head argument `(1 + θ(ρ - 1))/θ = ρ + (1/θ - 1)` is not a
zero, so its residue unit does not vanish. -/
theorem zetaResidueUnit_div_ne_zero_of_singleton {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ρ : ℂ} (hρ : XiHorizontalSingletonZero ρ) (him : 0 < ρ.im) :
    RHTower.zetaResidueUnit ((1 + θ * (ρ - 1)) / θ) ≠ 0 := by
  have hθC : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0.ne'
  have hre : ρ.re = 1 / 2 := xiHorizontalSingletonZero_re_eq_half hρ
  set v := (1 + θ * (ρ - 1)) / θ with hvdef
  have ev : v = ρ + (((1 / θ - 1 : ℝ)) : ℂ) := by
    rw [hvdef]; push_cast; field_simp; ring
  have hc : 0 < 1 / θ - 1 := by
    have : 1 < 1 / θ := by rw [lt_div_iff₀ hθ0]; linarith
    linarith
  have hvre : v.re = 1 / 2 + (1 / θ - 1) := by
    rw [ev, Complex.add_re, Complex.ofReal_re, hre]
  have hvim : v.im = ρ.im := by rw [ev, Complex.add_im, Complex.ofReal_im, add_zero]
  have hv1 : v ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hvim, Complex.one_im] at this; linarith
  have hζ : riemannZeta v ≠ 0 := by
    intro hz
    rcases le_or_gt 1 v.re with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz
    · have hxi := xi_eq_zero_of_riemannZeta_eq_zero hz (by rw [hvre]; linarith)
      have hvmem : v ∈ stripHeightFinset ρ.im :=
        mem_stripHeightFinset.mpr ⟨by rw [hvre]; linarith, h1, hvim, hxi⟩
      have hne : ρ ≠ v := by
        intro h; have := congrArg Complex.re h; rw [hre, hvre] at this; linarith
      have := two_le_xiHorizontalMultiplicity_of_ne hρ.1 hvmem hne
      rw [hρ.2] at this
      omega
  rw [zetaResidueUnit_eq hv1]
  exact mul_ne_zero (sub_ne_zero.mpr hv1) hζ

/-- A one-sided bound `η(dP + cA_θ)(x) ≤ C x^β` for large `x`, `β < 1 - θ/2`, `1/3 ≤ θ < 3/4`,
`c ≠ 0`, is impossible. -/
theorem false_of_eventually_le_tq {θ d c η C β : ℝ} (hθ3 : 1 / 3 ≤ θ) (hθ : θ < 3 / 4)
    (hc : c ≠ 0) (hη : |η| = 1) (hC : 0 ≤ C) (hβ : β < 1 - θ / 2)
    (h : ∀ᶠ x in atTop, η * (d * liouvilleTriangle x + c * cutoffHead θ x) ≤ C * x ^ β) :
    False := by
  have hθ0 : 0 < θ := by linarith
  have hθ1 : θ < 1 := by linarith
  set m : ℝ := (max (max ((3 * θ - 1) / 2) (1 - θ)) (1 / 2) + (1 - θ / 2)) / 2 with hmdef
  have hm1 : max (max ((3 * θ - 1) / 2) (1 - θ)) (1 / 2) < 1 - θ / 2 := by
    refine max_lt (max_lt (by linarith) (by linarith)) (by linarith)
  have hl1 := le_max_left ((3 * θ - 1) / 2) (1 - θ)
  have hl2 := le_max_right ((3 * θ - 1) / 2) (1 - θ)
  have hl3 := le_max_left (max ((3 * θ - 1) / 2) (1 - θ)) (1 / 2)
  have hl4 := le_max_right (max ((3 * θ - 1) / 2) (1 - θ)) (1 / 2)
  set β₁ := max β m with hβ₁def
  have hmβ₁ : m ≤ β₁ := le_max_right _ _
  have hβ₁ : β₁ < 1 - θ / 2 := max_lt hβ (by rw [hmdef]; linarith)
  obtain ⟨K, hK, hg⟩ := exists_oneSided_of_eventually_le_wide hθ1.le hη hC (le_max_left _ _) h
  obtain ⟨ρ, hsing, him, hwz⟩ := exists_singleton_zero_contracted_nonzero hθ0 hθ1
  have hre : ρ.re = 1 / 2 := xiHorizontalSingletonZero_re_eq_half hsing
  have hρ : riemannZeta ρ = 0 := by
    have hxi : xi ρ = 0 := (mem_stripHeightFinset.mp hsing.1).2.2.2
    exact RHTower.riemannZeta_eq_zero_iff_xi_or_trivial.mpr (Or.inl hxi)
  refine false_of_oneSided_tq (d := d) hθ0 hθ1 hc hη hC (by rw [hmdef] at hmβ₁; linarith) hθ3
    (by rw [hmdef] at hmβ₁; linarith) (by rw [hmdef] at hmβ₁; linarith) hK hρ
    (by rw [hre]) (by rw [hre]; norm_num) him.ne'
    hwz (zetaResidueUnit_rootArg_ne_zero_of_singleton hθ0 hθ1 hsing him)
    (zetaResidueUnit_div_ne_zero_of_singleton hθ0 hθ1 hsing him)
    (by rw [hre]; linarith) hg

/-- **Cutoff transport law up to `θ < 3/4`.** For every `0 < θ < 3/4`, every real `d`, every
`c ≠ 0`, every `β < 1 - θ/2` and every `C ≥ 0`, the combination `dP + cA_θ` exceeds `C x^β`
and falls below `-C x^β` for arbitrarily large `x`. -/
theorem frequently_gt_and_frequently_lt_tq {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 3 / 4) (d c : ℝ)
    (hc : c ≠ 0) {β C : ℝ} (hβ : β < 1 - θ / 2) (hC : 0 ≤ C) :
    (∃ᶠ x in atTop, C * x ^ β < d * liouvilleTriangle x + c * cutoffHead θ x) ∧
      (∃ᶠ x in atTop, d * liouvilleTriangle x + c * cutoffHead θ x < -(C * x ^ β)) := by
  rcases lt_or_ge θ (2 / 3) with h23 | h23
  · exact frequently_gt_and_frequently_lt_wide hθ0 h23 d c hc hβ hC
  have hθ3 : 1 / 3 ≤ θ := by linarith
  constructor
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le_tq hθ3 hθ hc (η := 1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [one_mul]; exact not_lt.mp hx)
  · by_contra h
    rw [Filter.not_frequently] at h
    exact false_of_eventually_le_tq hθ3 hθ hc (η := -1) (by norm_num) hC hβ
      (h.mono fun x hx => by rw [neg_one_mul, neg_le]; exact not_lt.mp hx)

end

end RHTower.LiouvilleHyperbolaCutoffThreeQuarter
