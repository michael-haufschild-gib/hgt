import GaloisForLFunctions.RHTower.XiResolventNodalSupply
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# The unconditional resolvent mass budget

The certified height floor `γ² > 32` and the open critical strip place every shifted spectral
square `z = α² + X` in an explicit sector: `|z| ≤ (129/127)·Re z`, with equality exactly at the
floor.  Two consequences, both unconditional:

* **norm mass is dominated by the trace** — `Σ'‖u_q(X)‖ ≤ (129/127)·Re(M₀(X))`, and at
  `X = x²` the right side is prime–Gamma data, `(129/127)·Re(logDeriv ξ(1/2 + x)/x)`;
* **a numeric cap, uniform in the shift** — each resolvent norm is at most `132/127` times the
  critical budget mass `massAt(1/2)` (again tight at the floor: `127·33 = 132·(127/4)`), so the
  corpus budget `Σ massAt(1/2) ≤ 3/50` gives `Σ'‖u_q(X)‖ ≤ 198/3175` for every `X ≥ 0`.

The universal supply theorem then holds with its total-mass input discharged by the numeric
budget: line placement above one scale, a sub-`δ` tail bound, and one witness inequality are
all that remain — the arithmetic core of the first rational-nodal data is exactly partial line
placement plus one zero-density statement.
-/

open Complex

namespace RHTower

noncomputable section

/-- The open critical strip for the centered spectral point: `Im(α)² < 1/4`. -/
theorem xiSpectralPoint_im_sq_lt_quarter (q : XiZeroCopy) :
    (xiSpectralPoint q).im ^ (2 : ℕ) < 1 / 4 := by
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
    simp [xiSpectralPoint]
  rw [him, neg_sq]
  exact xi_divisor_support_centered_re_sq_lt_quarter q.1

/-- The real part of the shifted spectral square in coordinates. -/
theorem xiSpectralSq_add_ofReal_re_eq (X : ℝ) (q : XiZeroCopy) :
    (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).re =
      (xiSpectralPoint q).re ^ (2 : ℕ) - (xiSpectralPoint q).im ^ (2 : ℕ) + X := by
  rw [Complex.add_re, Complex.ofReal_re, pow_two, Complex.mul_re]
  ring

/-- The imaginary part of the shifted spectral square in coordinates. -/
theorem xiSpectralSq_add_ofReal_im_eq (X : ℝ) (q : XiZeroCopy) :
    (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)).im =
      2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
  rw [Complex.add_im, Complex.ofReal_im, add_zero, pow_two, Complex.mul_im]
  ring

/-- **The sector bound, tight at the certified floor**: at every shift the resolvent norm is at
most `129/127` times its real part. -/
theorem norm_xiResolventPoint_le_re_mul {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    ‖xiResolventPoint X q‖ ≤ (129 / 127) * (xiResolventPoint X q).re := by
  set z : ℂ := xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ) with hz
  have hzre : 0 < z.re := xiSpectralSq_add_ofReal_re_pos hX q
  have hzne : z ≠ 0 := xiSpectralSq_add_ofReal_ne_zero hX q
  have hg := xiSpectral_re_sq_gt_thirtytwo q
  have hs := xiSpectralPoint_im_sq_lt_quarter q
  have hzre_eq : z.re = (xiSpectralPoint q).re ^ (2 : ℕ) - (xiSpectralPoint q).im ^ (2 : ℕ) + X :=
    xiSpectralSq_add_ofReal_re_eq X q
  have hzim_eq : z.im = 2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im :=
    xiSpectralSq_add_ofReal_im_eq X q
  have hsector : ‖z‖ ^ (2 : ℕ) ≤ (129 / 127) ^ (2 : ℕ) * z.re ^ (2 : ℕ) := by
    have hnorm : ‖z‖ ^ (2 : ℕ) = z.re ^ (2 : ℕ) + z.im ^ (2 : ℕ) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hnorm, hzre_eq, hzim_eq]
    have h1 : 4 * ((xiSpectralPoint q).im ^ (2 : ℕ)) ≤ 1 := by linarith
    have h2 : (0 : ℝ) < (xiSpectralPoint q).re ^ (2 : ℕ) := by linarith
    have h3 : (xiSpectralPoint q).re ^ (2 : ℕ) - 1 / 4 ≤
        (xiSpectralPoint q).re ^ (2 : ℕ) - (xiSpectralPoint q).im ^ (2 : ℕ) + X := by linarith
    have h4 : (0 : ℝ) < (xiSpectralPoint q).re ^ (2 : ℕ) - 1 / 4 := by linarith
    have h5 : ((xiSpectralPoint q).re ^ (2 : ℕ) - 1 / 4) ^ (2 : ℕ) ≤
        ((xiSpectralPoint q).re ^ (2 : ℕ) - (xiSpectralPoint q).im ^ (2 : ℕ) + X) ^ (2 : ℕ) := by nlinarith
    have h6 : 16129 * ((xiSpectralPoint q).re ^ (2 : ℕ)) ≤
        512 * ((xiSpectralPoint q).re ^ (2 : ℕ) - 1 / 4) ^ (2 : ℕ) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (xiSpectralPoint q).re ^ (2 : ℕ) - 32)
        (by linarith : (0 : ℝ) ≤ 512 * (xiSpectralPoint q).re ^ (2 : ℕ) - 1)]
    have h7 : 4 * ((xiSpectralPoint q).re ^ (2 : ℕ) * (xiSpectralPoint q).im ^ (2 : ℕ)) ≤
        (xiSpectralPoint q).re ^ (2 : ℕ) := by nlinarith [h1, h2]
    nlinarith [h5, h6, h7]
  have hzabs : ‖z‖ ≤ (129 / 127) * z.re := by
    nlinarith [hsector, norm_nonneg z, hzre]
  have hu : xiResolventPoint X q = z⁻¹ := by
    rw [xiResolventPoint]
  rw [hu, norm_inv, Complex.inv_re]
  have hnormSq : Complex.normSq z = ‖z‖ ^ (2 : ℕ) := (Complex.sq_norm z).symm
  rw [hnormSq]
  have hznorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  have hgoal : (1 : ℝ) / ‖z‖ ≤ (129 / 127 * z.re) / ‖z‖ ^ (2 : ℕ) := by
    rw [div_le_div_iff₀ hznorm_pos (by positivity)]
    nlinarith [hzabs, hznorm_pos.le]
  calc ‖z‖⁻¹ = 1 / ‖z‖ := (one_div _).symm
    _ ≤ (129 / 127 * z.re) / ‖z‖ ^ (2 : ℕ) := hgoal
    _ = 129 / 127 * (z.re / ‖z‖ ^ (2 : ℕ)) := by ring

/-- **Norm mass is dominated by the trace**: the total resolvent norm mass at any shift is at
most `129/127` times the real part of the zeroth moment. -/
theorem tsum_norm_xiResolventPoint_le_re_moment {X : ℝ} (hX : 0 ≤ X) :
    (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖) ≤
      (129 / 127) * (xiResolventMoment 0 X).re := by
  have hsum : Summable (fun q : XiZeroCopy => xiResolventPoint X q) :=
    (summable_norm_xiResolventPoint hX).of_norm
  have hre_sum : Summable (fun q : XiZeroCopy => (xiResolventPoint X q).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  have hM : xiResolventMoment 0 X = ∑' q : XiZeroCopy, xiResolventPoint X q := by
    rw [xiResolventMoment]
    exact tsum_congr fun q => pow_one _
  rw [hM, Complex.re_tsum hsum]
  calc (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖)
      ≤ ∑' q : XiZeroCopy, (129 / 127) * (xiResolventPoint X q).re :=
        Summable.tsum_le_tsum (fun q => norm_xiResolventPoint_le_re_mul hX q)
          (summable_norm_xiResolventPoint hX) (hre_sum.mul_left _)
    _ = (129 / 127) * ∑' q : XiZeroCopy, (xiResolventPoint X q).re := tsum_mul_left

/-- The trace domination on prime–Gamma data: at `X = x²` the norm mass is bounded by the
Euler-ray response of `ξ`. -/
theorem tsum_norm_xiResolventPoint_le_logDeriv {x : ℝ} (hx : 0 < x) :
    (∑' q : XiZeroCopy, ‖xiResolventPoint (x ^ (2 : ℕ)) q‖) ≤
      (129 / 127) * (logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) / (x : ℂ)).re := by
  have h := tsum_norm_xiResolventPoint_le_re_moment (X := x ^ (2 : ℕ)) (by positivity)
  rwa [xiResolventMoment_zero_eq_logDeriv hx] at h

/-- **Pointwise budget domination, tight at the certified floor**: each resolvent norm is at
most `132/127` times the critical budget mass, uniformly in the shift. -/
theorem norm_xiResolventPoint_le_budgetMass {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    ‖xiResolventPoint X q‖ ≤ (132 / 127) * xiBudgetMassAt (1 / 2) q := by
  have hg := xiSpectral_re_sq_gt_thirtytwo q
  have hs := xiSpectralPoint_im_sq_lt_quarter q
  have hb1 : (xiSpectralPoint q).im < 1 / 2 := by nlinarith
  have hb2 : -(1 / 2) < (xiSpectralPoint q).im := by nlinarith
  have hApos : (0 : ℝ) < (xiSpectralPoint q).re ^ (2 : ℕ) - 1 / 4 := by linarith
  have hBpos : (0 : ℝ) < (xiSpectralPoint q).re ^ (2 : ℕ) + 1 := by linarith
  -- the resolvent norm against the floor-shifted real part
  have hnorm_u : ‖xiResolventPoint X q‖ ≤ 1 / ((xiSpectralPoint q).re ^ (2 : ℕ) - 1 / 4) := by
    have h1 : ‖xiResolventPoint X q‖ = ‖xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)‖⁻¹ := by
      rw [xiResolventPoint, norm_inv]
    have hre_le : (xiSpectralPoint q).re ^ (2 : ℕ) - 1 / 4 ≤
        ‖xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ)‖ := by
      have hle := Complex.re_le_norm (xiSpectralPoint q ^ (2 : ℕ) + (X : ℂ))
      have heq := xiSpectralSq_add_ofReal_re_eq X q
      linarith [hs, hX]
    rw [h1, inv_eq_one_div]
    exact one_div_le_one_div_of_le hApos hre_le
  -- the budget mass against the strip-shifted real part
  have hmass_lb : 1 / ((xiSpectralPoint q).re ^ (2 : ℕ) + 1) ≤ xiBudgetMassAt (1 / 2) q := by
    rw [xiBudgetMassAt]
    have hnum1 : (0 : ℝ) ≤ 1 / 2 - (xiSpectralPoint q).im := by linarith
    have hnum2 : (0 : ℝ) ≤ 1 / 2 + (xiSpectralPoint q).im := by linarith
    have hden1pos : (0 : ℝ) < (xiSpectralPoint q).re ^ (2 : ℕ) +
        (1 / 2 - (xiSpectralPoint q).im) ^ (2 : ℕ) := by nlinarith
    have hden2pos : (0 : ℝ) < (xiSpectralPoint q).re ^ (2 : ℕ) +
        (1 / 2 + (xiSpectralPoint q).im) ^ (2 : ℕ) := by nlinarith
    have hden1 : (xiSpectralPoint q).re ^ (2 : ℕ) + (1 / 2 - (xiSpectralPoint q).im) ^ (2 : ℕ) ≤
        (xiSpectralPoint q).re ^ (2 : ℕ) + 1 := by nlinarith
    have hden2 : (xiSpectralPoint q).re ^ (2 : ℕ) + (1 / 2 + (xiSpectralPoint q).im) ^ (2 : ℕ) ≤
        (xiSpectralPoint q).re ^ (2 : ℕ) + 1 := by nlinarith
    have ht1 : (1 / 2 - (xiSpectralPoint q).im) / ((xiSpectralPoint q).re ^ (2 : ℕ) + 1) ≤
        (1 / 2 - (xiSpectralPoint q).im) /
          ((xiSpectralPoint q).re ^ (2 : ℕ) + (1 / 2 - (xiSpectralPoint q).im) ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_left hnum1 hden1pos hden1
    have ht2 : (1 / 2 + (xiSpectralPoint q).im) / ((xiSpectralPoint q).re ^ (2 : ℕ) + 1) ≤
        (1 / 2 + (xiSpectralPoint q).im) /
          ((xiSpectralPoint q).re ^ (2 : ℕ) + (1 / 2 + (xiSpectralPoint q).im) ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_left hnum2 hden2pos hden2
    have hsum : (1 / 2 - (xiSpectralPoint q).im) / ((xiSpectralPoint q).re ^ (2 : ℕ) + 1) +
        (1 / 2 + (xiSpectralPoint q).im) / ((xiSpectralPoint q).re ^ (2 : ℕ) + 1) =
        1 / ((xiSpectralPoint q).re ^ (2 : ℕ) + 1) := by
      rw [← add_div, show (1 / 2 - (xiSpectralPoint q).im) +
        (1 / 2 + (xiSpectralPoint q).im) = 1 by ring]
    linarith [ht1, ht2]
  -- the floor closes the gap between the two real parts
  have hfinal : 1 / ((xiSpectralPoint q).re ^ (2 : ℕ) - 1 / 4) ≤
      (132 / 127) * (1 / ((xiSpectralPoint q).re ^ (2 : ℕ) + 1)) := by
    rw [show (132 / 127 : ℝ) * (1 / ((xiSpectralPoint q).re ^ (2 : ℕ) + 1)) =
      132 / (127 * ((xiSpectralPoint q).re ^ (2 : ℕ) + 1)) by
        rw [mul_one_div, div_div],
      div_le_div_iff₀ hApos (by positivity)]
    nlinarith [hg]
  calc ‖xiResolventPoint X q‖ ≤ 1 / ((xiSpectralPoint q).re ^ (2 : ℕ) - 1 / 4) := hnorm_u
    _ ≤ (132 / 127) * (1 / ((xiSpectralPoint q).re ^ (2 : ℕ) + 1)) := hfinal
    _ ≤ (132 / 127) * xiBudgetMassAt (1 / 2) q :=
        mul_le_mul_of_nonneg_left hmass_lb (by norm_num)

/-- **The unconditional mass budget**: at every shift the total resolvent norm mass of the ξ
divisor is at most `198/3175`. -/
theorem tsum_norm_xiResolventPoint_le_budget {X : ℝ} (hX : 0 ≤ X) :
    (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖) ≤ 198 / 3175 := by
  have hmsum : Summable (xiBudgetMassAt (1 / 2)) :=
    summable_xiBudgetMassAt xi_probe_half_ne_zero
  calc (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖)
      ≤ ∑' q : XiZeroCopy, (132 / 127) * xiBudgetMassAt (1 / 2) q :=
        Summable.tsum_le_tsum (fun q => norm_xiResolventPoint_le_budgetMass hX q)
          (summable_norm_xiResolventPoint hX) (hmsum.mul_left _)
    _ = (132 / 127) * ∑' q : XiZeroCopy, xiBudgetMassAt (1 / 2) q := tsum_mul_left
    _ ≤ (132 / 127) * (3 / 50) :=
        mul_le_mul_of_nonneg_left tsum_massAt_half_le (by norm_num)
    _ = 198 / 3175 := by norm_num

/-- **Supply with the mass budget discharged**: line placement above one scale, a sub-`δ` tail
bound, and one witness inequality supply the `(0,2,1)` datum of `X^m·p` — the total-mass factor
is the unconditional `198/3175`. -/
theorem polyTuranMinor_supply_of_partial_line_budget {X δ : ℝ} (hX : 0 ≤ X) (hδ : 0 < δ)
    (hline : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0)
    (p : Polynomial ℝ) (m : ℕ) {B : ℝ}
    (hB : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖evalRealPolynomial p z‖ ≤ B)
    {q₁ q₂ : XiZeroCopy}
    (h1 : δ ≤ ‖xiResolventPoint X q₁‖) (h2 : δ ≤ ‖xiResolventPoint X q₂‖)
    (hne : ‖xiResolventPoint X q₁‖ ≠ ‖xiResolventPoint X q₂‖)
    {E : ℝ} (hE : (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
      ‖xiResolventPoint X (q : XiZeroCopy)‖) ≤ E)
    (hmassE : 8 * B ^ (4 : ℕ) * E * (198 / 3175) ≤
      2 * ((‖xiResolventPoint X q₁‖ * ‖xiResolventPoint X q₂‖) ^ (2 * m + 1) *
        (Polynomial.eval ‖xiResolventPoint X q₁‖ p ^ (2 : ℕ) *
          Polynomial.eval ‖xiResolventPoint X q₂‖ p ^ (2 : ℕ)) *
        (‖xiResolventPoint X q₁‖ - ‖xiResolventPoint X q₂‖) ^ (2 : ℕ))) :
    0 ≤ (xiPolyMoment (Polynomial.X ^ m * p) 0 X *
      xiPolyMoment (Polynomial.X ^ m * p) 2 X -
      xiPolyMoment (Polynomial.X ^ m * p) 1 X ^ (2 : ℕ)).re := by
  refine polyTuranMinor_supply_of_partial_line hX hδ hline p m hB h1 h2 hne ?_
  have hS := tsum_norm_xiResolventPoint_le_budget (X := X) hX
  have hεnn : (0 : ℝ) ≤ ∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
      ‖xiResolventPoint X (q : XiZeroCopy)‖ := tsum_nonneg fun q => norm_nonneg _
  have hSnn : (0 : ℝ) ≤ ∑' q : XiZeroCopy, ‖xiResolventPoint X q‖ :=
    tsum_nonneg fun q => norm_nonneg _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simp))
  have hprod : (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
      ‖xiResolventPoint X (q : XiZeroCopy)‖) *
      (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖) ≤ E * (198 / 3175) :=
    mul_le_mul hE hS hSnn (le_trans hεnn hE)
  have h8 : 8 * B ^ (4 : ℕ) * ((∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
      ‖xiResolventPoint X (q : XiZeroCopy)‖) *
      (∑' q : XiZeroCopy, ‖xiResolventPoint X q‖)) ≤
      8 * B ^ (4 : ℕ) * (E * (198 / 3175)) :=
    mul_le_mul_of_nonneg_left hprod (by positivity)
  nlinarith [h8, hmassE]

/-- **The first rational-nodal data on line placement and a tail bound alone**: every entry of
the countable criterion follows from partial line placement, one sub-`δ` tail-mass bound, and
one explicit witness inequality whose total-mass factor is the unconditional `198/3175`. -/
theorem rational_nodal_datum_of_partial_line_budget {X δ : ℝ} (hX : 0 ≤ X) (hδ : 0 < δ)
    (hline : ∀ q : XiZeroCopy, δ ≤ ‖xiResolventPoint X q‖ → (xiSpectralPoint q).im = 0)
    {j : ℕ} (c : Fin j → ℝ) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1) (m : ℕ)
    {q₁ q₂ : XiZeroCopy}
    (h1 : δ ≤ ‖xiResolventPoint X q₁‖) (h2 : δ ≤ ‖xiResolventPoint X q₂‖)
    (hne : ‖xiResolventPoint X q₁‖ ≠ ‖xiResolventPoint X q₂‖)
    {E : ℝ} (hE : (∑' q : {q : XiZeroCopy | ‖xiResolventPoint X q‖ < δ},
      ‖xiResolventPoint X (q : XiZeroCopy)‖) ≤ E)
    (hmassE : 8 * 2 ^ (4 * j) * E * (198 / 3175) ≤
      2 * ((‖xiResolventPoint X q₁‖ * ‖xiResolventPoint X q₂‖) ^ (2 * m + 1) *
        ((∏ i, (‖xiResolventPoint X q₁‖ - c i)) ^ (2 : ℕ) *
          (∏ i, (‖xiResolventPoint X q₂‖ - c i)) ^ (2 : ℕ)) *
        (‖xiResolventPoint X q₁‖ - ‖xiResolventPoint X q₂‖) ^ (2 : ℕ))) :
    0 ≤ (xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 0 X *
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 2 X -
      xiPolyMoment (Polynomial.X ^ m * finNodalPolynomial c) 1 X ^ (2 : ℕ)).re := by
  have hB : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖evalRealPolynomial (finNodalPolynomial c) z‖ ≤ 2 ^ j := by
    intro z hz
    rw [evalRealPolynomial_finNodalPolynomial, norm_prod]
    calc ∏ i, ‖z - ((c i : ℝ) : ℂ)‖ ≤ ∏ _i : Fin j, (2 : ℝ) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _)
            (fun i _ => norm_sub_node_le hz (hc i).1 (hc i).2)
      _ = 2 ^ j := by rw [Finset.prod_const, Finset.card_fin]
  have hBpow : ((2 : ℝ) ^ j) ^ (4 : ℕ) = 2 ^ (4 * j) := by
    rw [← pow_mul, mul_comm]
  refine polyTuranMinor_supply_of_partial_line_budget hX hδ hline (finNodalPolynomial c) m
    hB h1 h2 hne hE ?_
  rw [hBpow, eval_finNodalPolynomial, eval_finNodalPolynomial]
  exact hmassE

/-- **The numeric top-level detection window**: with the unconditional mass budget, finitely
many plain even Turán minors of the raw ξ resolvent moments detect an off-line zero at the
maximal resolvent modulus, within the fully numeric window
`(2·(198/3175)²/g + (198/3175)²/(ℓ² − ρ₂²)) / Im(u)²`. -/
theorem exists_neg_even_plain_minor_of_offline_top_budget {X : ℝ} (hX : 0 ≤ X)
    {ℓ : ℝ} (hℓpos : 0 < ℓ) (htop : ∀ q : XiZeroCopy, ‖xiResolventPoint X q‖ ≤ ℓ)
    {ρ₂ : ℝ} (hρ₂0 : 0 ≤ ρ₂) (hρ₂lt : ρ₂ < ℓ)
    (hρ₂bound : ∀ q, ‖xiResolventPoint X q‖ < ℓ → ‖xiResolventPoint X q‖ ≤ ρ₂)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ q q' : XiZeroCopy, ‖xiResolventPoint X q‖ = ℓ → ‖xiResolventPoint X q'‖ = ℓ →
      xiResolventPoint X q * xiResolventPoint X q' ≠ (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ) →
      g ≤ ‖(xiResolventPoint X q * xiResolventPoint X q' / (((ℓ : ℝ)) : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) - 1‖)
    {qh : XiZeroCopy} (hqhℓ : ‖xiResolventPoint X qh‖ = ℓ)
    (hoff : (xiSpectralPoint qh).im ≠ 0)
    {N : ℕ} (hN : (2 * (198 / 3175) ^ (2 : ℕ) / g + (198 / 3175) ^ (2 : ℕ) / (ℓ ^ (2 : ℕ) - ρ₂ ^ (2 : ℕ))) /
      (xiResolventPoint X qh).im ^ (2 : ℕ) < (N : ℝ)) :
    ∃ n : ℕ, n < N ∧ (xiResolventMoment (2 * n) X * xiResolventMoment (2 * n + 2) X -
      xiResolventMoment (2 * n + 1) X ^ (2 : ℕ)).re < 0 :=
  exists_neg_even_plain_minor_of_offline_top hX hℓpos htop hρ₂0 hρ₂lt hρ₂bound
    (tsum_norm_xiResolventPoint_le_budget hX) hg hgap hqhℓ hoff hN

end

end RHTower
