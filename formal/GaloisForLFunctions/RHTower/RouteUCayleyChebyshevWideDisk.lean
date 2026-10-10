import GaloisForLFunctions.RHTower.XiCayleyChebyshevPositiveRootCriterion
import GaloisForLFunctions.RHTower.LiCayleyWindowLaw

/-!
# Route U's Cayley–Chebyshev generating identity on the disk of radius `200/201`

The Route U moments `a_k = Σ_q u_q T_k(x_q)` (`xiCayleyChebyshevMoment`) satisfy a two-resolvent
generating identity. The corpus proves it unconditionally on `‖r‖ < 1/3`
(`xiCayleyChebyshevMoment_generating_eq_resolvent`), from the strip bound
`‖y_q‖, ‖y_q⁻¹‖ ≤ 3` on the hard-edge Cayley phases `y_q = (1 + i a_q)/(1 - i a_q)`.

**Window law.** With `a_q = γ - iδ`,

`‖y_q‖² = ((1 + δ)² + γ²)/((1 - δ)² + γ²)`.

This is `1` on the critical line, and off it `‖y_q‖^{±2} ≤ 1 + 4|δ|/((1 - |δ|)² + γ²)`. Off-line zeros
have `γ² ≥ 431/2`, so `‖y_q‖^{±1} ≤ 201/200` for every zero
(`norm_xiCayleyChebyshevPhase_le_wide`). The generating identity therefore holds unconditionally on
`‖r‖ < 200/201` (`xiCayleyChebyshevMoment_generating_eq_resolvent_wide`). The paper's unit disk
would need `‖y_q‖ = 1` for every zero, i.e. RH.
-/

open Complex Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **The hard-edge Cayley phase is within `201/200` of the unit circle.** -/
theorem norm_xiCayleyChebyshevPhase_le_wide (q : XiZeroCopy) :
    ‖xiCayleyChebyshevPhase q‖ ≤ 201 / 200 := by
  let α := xiSpectralPoint q
  have hden := sub_I_mul_spectral_ne_zero (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re) q
  set ρ : ℂ := (q.1 : ℂ) with hρ
  have hz : xi ρ = 0 := xi_eq_zero_of_mem_divisor_support q.1
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hαre : α.re = ρ.im := by simp [α, xiSpectralPoint, hρ]
  have hαim : α.im = -(ρ.re - 1 / 2) := by simp [α, xiSpectralPoint, hρ]
  have hsq :
      ‖(1 : ℂ) + Complex.I * α‖ ^ 2 ≤
        (201 / 200) ^ 2 * ‖(1 : ℂ) - Complex.I * α‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul]
    rw [hαre, hαim]
    by_cases hoff : ρ.re = 1 / 2
    · rw [hoff]; nlinarith [sq_nonneg ρ.im]
    · have hγ := im_sq_ge_of_xi_eq_zero_of_re_ne_half hz hoff
      nlinarith [sq_nonneg ρ.im, sq_nonneg (ρ.re - 1 / 2), hstrip.1, hstrip.2]
  have hnorm :
      ‖(1 : ℂ) + Complex.I * α‖ ≤ 201 / 200 * ‖(1 : ℂ) - Complex.I * α‖ := by
    nlinarith [norm_nonneg ((1 : ℂ) + Complex.I * α),
      norm_nonneg ((1 : ℂ) - Complex.I * α)]
  rw [xiCayleyChebyshevPhase, xiHardEdgeCayleyPhase, norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hden)).2 (by simpa only [α] using hnorm)

theorem norm_xiCayleyChebyshevPhase_inv_le_wide (q : XiZeroCopy) :
    ‖(xiCayleyChebyshevPhase q)⁻¹‖ ≤ 201 / 200 := by
  rw [← xiCayleyChebyshevPhase_reflect]
  exact norm_xiCayleyChebyshevPhase_le_wide _

private theorem wide_phaseGenerating_algebra
    {u r y x : ℂ} (hy : y ≠ 0)
    (hx : (y + y⁻¹) / 2 = x)
    (hry : 1 - r * y ≠ 0) (hryi : 1 - r * y⁻¹ ≠ 0)
    (hD : 1 - 2 * r * x + r ^ 2 ≠ 0) :
    u / 2 * ((1 - r * y)⁻¹ + (1 - r * y⁻¹)⁻¹) =
      u * (1 - r * x) / (1 - 2 * r * x + r ^ 2) := by
  let A : ℂ := 1 - r * y
  let B : ℂ := 1 - r * y⁻¹
  let D : ℂ := 1 - 2 * r * x + r ^ 2
  have hAB : A * B = D := by
    dsimp only [A, B, D]
    have hx' : y ^ 2 + 1 = 2 * x * y := by
      field_simp [hy] at hx
      linear_combination hx
    field_simp [hy]
    linear_combination hx' * (-r)
  have hAaddB : A + B = 2 * (1 - r * x) := by
    dsimp only [A, B]
    have hphase : y + y⁻¹ = 2 * x := by
      calc
        y + y⁻¹ = 2 * ((y + y⁻¹) / 2) := by ring
        _ = 2 * x := by rw [hx]
    calc
      1 - r * y + (1 - r * y⁻¹) = 2 - r * (y + y⁻¹) := by ring
      _ = 2 - r * (2 * x) := by rw [hphase]
      _ = 2 * (1 - r * x) := by ring
  have hsum : A⁻¹ + B⁻¹ = (A + B) / (A * B) := by
    have hA : A ≠ 0 := by simpa only [A] using hry
    have hB : B ≠ 0 := by simpa only [B] using hryi
    field_simp [hA, hB]
    ring
  rw [show 1 - r * y = A by rfl, show 1 - r * y⁻¹ = B by rfl,
    hsum, hAB, hAaddB]
  dsimp only [D]
  field_simp [hD]

private theorem wide_resolvent_algebra
    {w r : ℂ} (hw : 1 + w ≠ 0) (hr1 : 1 + r ≠ 0)
    (hres : w + ((1 - r) / (1 + r)) ^ 2 ≠ 0) :
    (w + 1)⁻¹ * (1 - r * ((1 - w) / (1 + w))) /
          (1 - 2 * r * ((1 - w) / (1 + w)) + r ^ 2) =
      (1 / 2) * ((w + 1)⁻¹ +
        ((1 - r) / (1 + r)) *
          (w + ((1 - r) / (1 + r)) ^ 2)⁻¹) := by
  have hw' : w + 1 ≠ 0 := by simpa [add_comm] using hw
  have hresnum : w * (1 + r) ^ 2 + (1 - r) ^ 2 ≠ 0 := by
    intro hzero
    apply hres
    field_simp [hr1]
    linear_combination hzero
  let H : ℂ := w * (1 + r) ^ 2 + (1 - r) ^ 2
  have hH : H ≠ 0 := by simpa only [H] using hresnum
  have hDform :
      1 - 2 * r * ((1 - w) / (1 + w)) + r ^ 2 = H / (1 + w) := by
    dsimp only [H]
    field_simp [hw]
    ring
  have hNform :
      1 - r * ((1 - w) / (1 + w)) =
        ((1 - r) + w * (1 + r)) / (1 + w) := by
    field_simp [hw]
    ring
  have hresform :
      w + ((1 - r) / (1 + r)) ^ 2 = H / (1 + r) ^ 2 := by
    dsimp only [H]
    field_simp [hr1]
  rw [hNform, hDform, hresform]
  dsimp only [H]
  field_simp [hw, hw', hr1, hH]
  ring

private theorem wide_resolvent_denominator_ne_zero
    {w r : ℂ} (hw : 1 + w ≠ 0) (hr1 : 1 + r ≠ 0)
    (hD : 1 - 2 * r * ((1 - w) / (1 + w)) + r ^ 2 ≠ 0) :
    w + ((1 - r) / (1 + r)) ^ 2 ≠ 0 := by
  intro hzero
  apply hD
  field_simp [hw, hr1] at hzero ⊢
  linear_combination hzero

/-- Exact pointwise generating row on its unconditional uniform disk. -/
theorem hasSum_xiCayleyChebyshevAtom_generating_wide
    (q : XiZeroCopy) {r : ℂ} (hr : ‖r‖ < 200 / 201) :
    HasSum (fun k : ℕ =>
      xiResolventPoint 1 q *
        evalRealPolynomial (xiCayleyChebyshevPolynomial k)
          (xiResolventPoint 1 q) * r ^ k)
      ((1 / 2) *
        (xiResolventPoint 1 q + xiCayleyAbelParameter r *
          (xiSpectralPoint q ^ 2 + xiCayleyAbelParameter r ^ 2)⁻¹)) := by
  let y := xiCayleyChebyshevPhase q
  let u := xiResolventPoint 1 q
  let w := xiSpectralPoint q ^ 2
  let x := 2 * u - 1
  have hy : y ≠ 0 := xiCayleyChebyshevPhase_ne_zero q
  have hynorm : ‖y‖ ≤ 201 / 200 := norm_xiCayleyChebyshevPhase_le_wide q
  have hyinvnorm : ‖y⁻¹‖ ≤ 201 / 200 := norm_xiCayleyChebyshevPhase_inv_le_wide q
  have hrynorm : ‖r * y‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg r]
  have hryinorm : ‖r * y⁻¹‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg r]
  have hry : 1 - r * y ≠ 0 := by
    intro hzero
    have : r * y = 1 := (sub_eq_zero.mp hzero).symm
    rw [this] at hrynorm
    norm_num at hrynorm
  have hryi : 1 - r * y⁻¹ ≠ 0 := by
    intro hzero
    have : r * y⁻¹ = 1 := (sub_eq_zero.mp hzero).symm
    rw [this] at hryinorm
    norm_num at hryinorm
  have hxphase : (y + y⁻¹) / 2 = x := by
    have h := eval_xiCayleyChebyshevPolynomial_xiResolventPoint 1 q
    have hp :
        evalRealPolynomial (xiCayleyChebyshevPolynomial 1) u = x := by
      simp [u, x, xiCayleyChebyshevPolynomial,
        xiHardEdgeReciprocalPolynomial, evalRealPolynomial]
    change evalRealPolynomial (xiCayleyChebyshevPolynomial 1) u =
      y ^ 1 / 2 + (y ^ 1)⁻¹ / 2 at h
    rw [hp] at h
    norm_num at h
    rw [show (y + y⁻¹) / 2 = y / 2 + y⁻¹ / 2 by ring]
    exact h.symm
  have hAB :
      (1 - r * y) * (1 - r * y⁻¹) =
        1 - 2 * r * x + r ^ 2 := by
    have hx' : y ^ 2 + 1 = 2 * x * y := by
      field_simp [hy] at hxphase
      linear_combination hxphase
    field_simp [hy]
    linear_combination hx' * (-r)
  have hD : 1 - 2 * r * x + r ^ 2 ≠ 0 := by
    rw [← hAB]
    exact mul_ne_zero hry hryi
  have hgeomY := hasSum_geometric_of_norm_lt_one hrynorm
  have hgeomYi := hasSum_geometric_of_norm_lt_one hryinorm
  have hphaseSum : HasSum (fun k : ℕ =>
      u / 2 * (r * y) ^ k + u / 2 * (r * y⁻¹) ^ k)
      (u / 2 * (1 - r * y)⁻¹ + u / 2 * (1 - r * y⁻¹)⁻¹) :=
    (hgeomY.mul_left (u / 2)).add (hgeomYi.mul_left (u / 2))
  have hterm (k : ℕ) :
      xiResolventPoint 1 q *
          evalRealPolynomial (xiCayleyChebyshevPolynomial k)
            (xiResolventPoint 1 q) * r ^ k =
        u / 2 * (r * y) ^ k + u / 2 * (r * y⁻¹) ^ k := by
    rw [eval_xiCayleyChebyshevPolynomial_xiResolventPoint]
    change u * (y ^ k / 2 + (y ^ k)⁻¹ / 2) * r ^ k = _
    rw [mul_pow, mul_pow, inv_pow]
    ring
  have hsum : HasSum (fun k : ℕ =>
      xiResolventPoint 1 q *
        evalRealPolynomial (xiCayleyChebyshevPolynomial k)
          (xiResolventPoint 1 q) * r ^ k)
      (u / 2 * ((1 - r * y)⁻¹ + (1 - r * y⁻¹)⁻¹)) := by
    have hs := HasSum.congr_fun hphaseSum fun k => hterm k
    convert hs using 1
    ring
  have hphaseAlg := wide_phaseGenerating_algebra
    (u := u) hy hxphase hry hryi hD
  have hw : 1 + w ≠ 0 := by
    simpa [w, add_comm] using
      xiSpectralSq_add_ofReal_ne_zero (X := (1 : ℝ)) (by norm_num) q
  have hu : u = (w + 1)⁻¹ := by
    simp [u, w, xiResolventPoint, add_comm]
  have hxw : x = (1 - w) / (1 + w) := by
    dsimp only [x]
    rw [hu]
    rw [show w + 1 = 1 + w by ring]
    field_simp [hw]
    ring
  have hr1 : 1 + r ≠ 0 := by
    intro hzero
    have : r = -1 := by linear_combination hzero
    rw [this] at hr
    norm_num at hr
  have hDw : 1 - 2 * r * ((1 - w) / (1 + w)) + r ^ 2 ≠ 0 := by
    simpa only [hxw] using hD
  have hres := wide_resolvent_denominator_ne_zero hw hr1 hDw
  have hresAlg := wide_resolvent_algebra hw hr1 hres
  rw [hphaseAlg, hxw, hu, hresAlg] at hsum
  simpa [u, w, xiCayleyAbelParameter, xiResolventPoint, add_comm] using hsum

theorem norm_eval_xiCayleyChebyshevPolynomial_le_wide_pow
    (k : ℕ) (q : XiZeroCopy) :
    ‖evalRealPolynomial (xiCayleyChebyshevPolynomial k)
        (xiResolventPoint 1 q)‖ ≤ (201 / 200) ^ k := by
  rw [eval_xiCayleyChebyshevPolynomial_xiResolventPoint]
  let y := xiCayleyChebyshevPhase q
  have hpow : ‖y ^ k‖ ≤ (201 / 200) ^ k := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg y)
      (norm_xiCayleyChebyshevPhase_le_wide q) k
  have hinvpow : ‖(y ^ k)⁻¹‖ ≤ (201 / 200) ^ k := by
    have h : ‖(y⁻¹) ^ k‖ ≤ (201 / 200) ^ k := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg y⁻¹)
        (norm_xiCayleyChebyshevPhase_inv_le_wide q) k
    simpa only [inv_pow] using h
  calc
    ‖y ^ k / 2 + (y ^ k)⁻¹ / 2‖ ≤
        ‖y ^ k / 2‖ + ‖(y ^ k)⁻¹ / 2‖ := norm_add_le _ _
    _ = ‖y ^ k‖ / 2 + ‖(y ^ k)⁻¹‖ / 2 := by
      simp only [norm_div]
      norm_num
    _ ≤ (201 / 200) ^ k / 2 + (201 / 200) ^ k / 2 := by gcongr
    _ = (201 / 200) ^ k := by ring

theorem summable_xiCayleyChebyshevGeneratingAtom_prod_wide
    {r : ℂ} (hr : ‖r‖ < 200 / 201) :
    Summable (fun p : XiZeroCopy × ℕ =>
      xiResolventPoint 1 p.1 *
        evalRealPolynomial (xiCayleyChebyshevPolynomial p.2)
          (xiResolventPoint 1 p.1) * r ^ p.2) := by
  have hratio0 : 0 ≤ 201 / 200 * ‖r‖ := mul_nonneg (by norm_num) (norm_nonneg r)
  have hratio1 : 201 / 200 * ‖r‖ < 1 := by nlinarith
  have hgeom : Summable (fun k : ℕ => (201 / 200 * ‖r‖) ^ k) :=
    summable_geometric_of_lt_one hratio0 hratio1
  have hbase : Summable (fun q : XiZeroCopy => ‖xiResolventPoint 1 q‖) :=
    summable_norm_xiResolventPoint (by norm_num)
  refine Summable.of_norm_bounded
      (g := fun p : XiZeroCopy × ℕ =>
        ‖xiResolventPoint 1 p.1‖ * (201 / 200 * ‖r‖) ^ p.2) ?_ ?_
  · exact hbase.mul_of_nonneg hgeom (fun q => norm_nonneg _)
      (fun k => pow_nonneg hratio0 k)
  · intro p
    rw [norm_mul, norm_mul, norm_pow]
    calc
      ‖xiResolventPoint 1 p.1‖ *
          ‖evalRealPolynomial (xiCayleyChebyshevPolynomial p.2)
            (xiResolventPoint 1 p.1)‖ * ‖r‖ ^ p.2 ≤
        ‖xiResolventPoint 1 p.1‖ * (201 / 200) ^ p.2 * ‖r‖ ^ p.2 := by
          gcongr
          exact norm_eval_xiCayleyChebyshevPolynomial_le_wide_pow p.2 p.1
      _ = ‖xiResolventPoint 1 p.1‖ * (201 / 200 * ‖r‖) ^ p.2 := by
        rw [mul_pow]
        ring

/-- Correct unconditional form of Route U's global generating identity.  The paper's asserted
unit disk is replaced by the uniform disk forced by the proved Cayley strip bound. -/
theorem xiCayleyChebyshevMoment_generating_eq_resolvent_wide
    {r : ℂ} (hr : ‖r‖ < 200 / 201) :
    (∑' k : ℕ, xiCayleyChebyshevMoment k * r ^ k) =
      (1 / 2) *
        (xiCayleySpectralResolvent 1 +
          xiCayleyAbelParameter r *
            xiCayleySpectralResolvent (xiCayleyAbelParameter r ^ 2)) := by
  let F : XiZeroCopy → ℕ → ℂ := fun q k =>
    xiResolventPoint 1 q *
      evalRealPolynomial (xiCayleyChebyshevPolynomial k)
        (xiResolventPoint 1 q) * r ^ k
  let A : XiZeroCopy → ℂ := fun q => xiResolventPoint 1 q
  let B : XiZeroCopy → ℂ := fun q =>
    xiCayleyAbelParameter r *
      (xiSpectralPoint q ^ 2 + xiCayleyAbelParameter r ^ 2)⁻¹
  have hprod : Summable (fun p : XiZeroCopy × ℕ => F p.1 p.2) := by
    simpa only [F] using summable_xiCayleyChebyshevGeneratingAtom_prod_wide hr
  have hinner (q : XiZeroCopy) :
      (∑' k : ℕ, F q k) = (1 / 2) * (A q + B q) := by
    exact (hasSum_xiCayleyChebyshevAtom_generating_wide q hr).tsum_eq
  have hinnerSummable : Summable (fun q : XiZeroCopy => ∑' k : ℕ, F q k) :=
    hprod.prod
  have hRhs : Summable (fun q : XiZeroCopy => (1 / 2) * (A q + B q)) :=
    hinnerSummable.congr hinner
  have hAB : Summable (fun q : XiZeroCopy => A q + B q) :=
    (summable_mul_left_iff (by norm_num : (1 / 2 : ℂ) ≠ 0)).mp hRhs
  have hA : Summable A := by
    simpa only [A] using
      summable_xiResolventPoint (X := (1 : ℝ)) (by norm_num)
  have hBraw : Summable (fun q : XiZeroCopy => (A q + B q) - A q) := hAB.sub hA
  have hB : Summable B := hBraw.congr fun q => by ring
  calc
    (∑' k : ℕ, xiCayleyChebyshevMoment k * r ^ k) =
        ∑' k : ℕ, ∑' q : XiZeroCopy, F q k := by
      apply tsum_congr
      intro k
      rw [xiCayleyChebyshevMoment, tsum_mul_right]
    _ = ∑' q : XiZeroCopy, ∑' k : ℕ, F q k := hprod.tsum_comm
    _ = ∑' q : XiZeroCopy, (1 / 2) * (A q + B q) :=
      tsum_congr hinner
    _ = (1 / 2) * ((∑' q : XiZeroCopy, A q) + ∑' q : XiZeroCopy, B q) := by
      rw [show (fun q : XiZeroCopy => (1 / 2 : ℂ) * (A q + B q)) =
          fun q => (1 / 2 : ℂ) * A q + (1 / 2 : ℂ) * B q by
        funext q
        ring]
      rw [(hA.mul_left (1 / 2)).tsum_add (hB.mul_left (1 / 2)),
        tsum_mul_left, tsum_mul_left]
      ring
    _ = (1 / 2) *
        (xiCayleySpectralResolvent 1 +
          xiCayleyAbelParameter r *
            xiCayleySpectralResolvent (xiCayleyAbelParameter r ^ 2)) := by
      rw [xiCayleySpectralResolvent, xiCayleySpectralResolvent]
      rw [show (∑' q : XiZeroCopy, A q) =
          ∑' q : XiZeroCopy, (xiSpectralPoint q ^ 2 + (1 : ℂ))⁻¹ by
        apply tsum_congr
        intro q
        simp [A, xiResolventPoint, add_comm]]
      rw [show (∑' q : XiZeroCopy, B q) =
          xiCayleyAbelParameter r *
            ∑' q : XiZeroCopy,
              (xiSpectralPoint q ^ 2 + xiCayleyAbelParameter r ^ 2)⁻¹ by
        change (∑' q : XiZeroCopy,
            xiCayleyAbelParameter r *
              (xiSpectralPoint q ^ 2 + xiCayleyAbelParameter r ^ 2)⁻¹) = _
        rw [tsum_mul_left]]


end

end RHTower
