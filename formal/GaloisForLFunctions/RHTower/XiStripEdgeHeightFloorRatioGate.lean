import GaloisForLFunctions.RHTower.XiStripEdgeSquaredWeightSum
import GaloisForLFunctions.RHTower.CompletedZetaStripEdgeJetBounds
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.XiResolventMassBudget

/-!
# The strip-edge height floor and the signed moment ratio gate

Write a zero copy in the spectral coordinate `a = u + iv = (ρ − 1/2)(−i)`, so `u = Im ρ` and
`v² < 1/4`.  Its strip-edge weight `w = (1/4 + a²)⁻¹ = 1/(ρ(1−ρ))` has `1/4 + a² = A + iC` with
`A = 1/4 + u² − v² ≥ u²` and `C² = 4u²v² < u²`, hence

`Re w > 0`   and   `Re w² = (A² − C²)/(A² + C²)² ≥ (A − 1)/(A(A + 1)²) ≥ 0`.

The two strip-edge sum rules give `Σ Re w = 2Λ₀(1)` and `Σ Re w² = 2(Λ₀(1)² − 2 Re Λ₀'(1))`.
The first forces `Λ₀(1) ≥ 0`; with the certified jet bounds `Λ₀(1) ≤ 93/4000` and
`Re Λ₀'(1) ≥ 111/500000` the second is at most `2/8000`.  A copy and its functional-equation
reflection `a ↦ −a` carry the same weight, so every copy has `Re w² ≤ 1/8000`, and the cubic
`8000(A − 1) > A(A + 1)²` on `[32, 83]` turns this into the **height floor** `u² > 331/4`:
no zero of `ξ` has ordinate of absolute value at most `9.09`.

Above that floor every copy satisfies `81(u² + v²) < Re a⁴ = u⁴ − 6u²v² + v⁴`, which is the
termwise inequality `Re a⁻⁶ < Re a⁻⁴ / 81`.  Summing over the divisor gives the signed gate
`normalizedPrimeArchMoment 2 < normalizedPrimeArchMoment 1 / 81` unconditionally.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Real coordinates of a zero copy -/

theorem stripEdgeDenominator_re (q : XiZeroCopy) :
    ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re =
      1 / 4 + (xiSpectralPoint q).re ^ 2 - (xiSpectralPoint q).im ^ 2 := by
  simp only [add_re, pow_two, mul_re]
  norm_num
  ring

theorem stripEdgeDenominator_im (q : XiZeroCopy) :
    ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).im =
      2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
  simp only [add_im, pow_two, mul_im]
  norm_num
  ring

/-- The real part `A = 1/4 + u² − v²` of the strip-edge denominator dominates `u²`. -/
theorem sq_re_le_stripEdgeDenominator_re (q : XiZeroCopy) :
    (xiSpectralPoint q).re ^ 2 ≤ ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re := by
  rw [stripEdgeDenominator_re]
  linarith [xiSpectralPoint_im_sq_lt_quarter q]

/-- The imaginary part `C = 2uv` of the strip-edge denominator has `C² < u²`. -/
theorem stripEdgeDenominator_im_sq_le (q : XiZeroCopy) :
    ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).im ^ 2 ≤ (xiSpectralPoint q).re ^ 2 := by
  rw [stripEdgeDenominator_im]
  have hv := xiSpectralPoint_im_sq_lt_quarter q
  nlinarith [sq_nonneg (xiSpectralPoint q).re]

theorem xiStripEdgeWeight_re_pos (q : XiZeroCopy) : 0 < (xiStripEdgeWeight q).re := by
  rw [xiStripEdgeWeight_eq_spectral, Complex.inv_re]
  have hA : 32 < ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re :=
    lt_of_lt_of_le (xiSpectral_re_sq_gt_thirtytwo q) (sq_re_le_stripEdgeDenominator_re q)
  have hz : (1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ) ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hA
    norm_num at hA
  exact div_pos (by linarith) (Complex.normSq_pos.mpr hz)

/-- `Re w² = (A² − C²)/(A² + C²)²`. -/
theorem xiStripEdgeWeight_sq_re_eq (q : XiZeroCopy) :
    (xiStripEdgeWeight q ^ (2 : ℕ)).re =
      (((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re ^ 2 -
          ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).im ^ 2) /
        (((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re ^ 2 +
          ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).im ^ 2) ^ 2 := by
  rw [xiStripEdgeWeight_eq_spectral, inv_pow, Complex.inv_re, map_pow, Complex.normSq_apply]
  set z := (1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)
  have hre : (z ^ (2 : ℕ)).re = z.re ^ 2 - z.im ^ 2 := by
    simp only [pow_two, mul_re]
  rw [hre]
  ring

/-- The weight square has nonnegative real part, bounded below by `(A − 1)/(A(A+1)²)`. -/
theorem xiStripEdgeWeight_sq_re_ge (q : XiZeroCopy) :
    (((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re ^ 2 -
        ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re) /
      (((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re ^ 2 +
        ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re) ^ 2 ≤
      (xiStripEdgeWeight q ^ (2 : ℕ)).re := by
  rw [xiStripEdgeWeight_sq_re_eq]
  set A := ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re
  set C := ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).im
  have hA : 32 < A :=
    lt_of_lt_of_le (xiSpectral_re_sq_gt_thirtytwo q) (sq_re_le_stripEdgeDenominator_re q)
  have hC : C ^ 2 ≤ A :=
    (stripEdgeDenominator_im_sq_le q).trans (sq_re_le_stripEdgeDenominator_re q)
  have hC0 : 0 ≤ C ^ 2 := sq_nonneg C
  have hnum : A ^ 2 - A ≤ A ^ 2 - C ^ 2 := by linarith
  have hnum0 : 0 ≤ A ^ 2 - A := by nlinarith
  have hden : (A ^ 2 + C ^ 2) ^ 2 ≤ (A ^ 2 + A) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hden0 : 0 < (A ^ 2 + C ^ 2) ^ 2 := by positivity
  calc (A ^ 2 - A) / (A ^ 2 + A) ^ 2 ≤ (A ^ 2 - A) / (A ^ 2 + C ^ 2) ^ 2 :=
        div_le_div_of_nonneg_left hnum0 hden0 hden
    _ ≤ (A ^ 2 - C ^ 2) / (A ^ 2 + C ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right hnum hden0.le

theorem xiStripEdgeWeight_sq_re_nonneg (q : XiZeroCopy) :
    0 ≤ (xiStripEdgeWeight q ^ (2 : ℕ)).re := by
  refine le_trans ?_ (xiStripEdgeWeight_sq_re_ge q)
  set A := ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re
  have hA : 32 < A :=
    lt_of_lt_of_le (xiSpectral_re_sq_gt_thirtytwo q) (sq_re_le_stripEdgeDenominator_re q)
  apply div_nonneg (by nlinarith) (by positivity)

/-! ## The strip-edge budget -/

/-- The first sum rule forces `Λ₀(1) ≥ 0`. -/
theorem completedRiemannZeta₀_one_re_nonneg : 0 ≤ (completedRiemannZeta₀ 1).re := by
  have h := (Complex.hasSum_re hasSum_xiStripEdgeWeight).nonneg
    (fun q => (xiStripEdgeWeight_re_pos q).le)
  simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at h
  linarith

/-- **The certified strip-edge budget**: `Σ_ρ Re (ρ(1−ρ))⁻² ≤ 2/8000`. -/
theorem hasSum_xiStripEdgeWeight_sq_re :
    HasSum (fun q => (xiStripEdgeWeight q ^ (2 : ℕ)).re)
      (2 * ((completedRiemannZeta₀ 1).re ^ 2 - 2 * (deriv completedRiemannZeta₀ 1).re)) := by
  have h := Complex.hasSum_re hasSum_xiStripEdgeWeight_sq
  have him := completedRiemannZeta₀_one_im
  convert h using 1
  simp only [mul_re, sub_re, pow_two, re_ofNat, im_ofNat, mul_im, sub_im, him]
  ring

theorem stripEdgeBudget_le :
    2 * ((completedRiemannZeta₀ 1).re ^ 2 - 2 * (deriv completedRiemannZeta₀ 1).re) ≤
      2 / 8000 := by
  have h0 := completedRiemannZeta₀_one_re_nonneg
  have h1 := completedRiemannZeta₀_one_re_le
  have h2 := completedRiemannZeta₀_deriv_one_re_ge_num
  have hsq : (completedRiemannZeta₀ 1).re ^ 2 ≤ (93 / 4000) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  nlinarith

/-! ## The height floor -/

theorem xiZeroCopyReflect_ne (q : XiZeroCopy) : xiZeroCopyReflectEquiv q ≠ q := by
  intro h
  have ha := xiSpectralPoint_reflect q
  rw [h] at ha
  have : xiSpectralPoint q = 0 := by linear_combination ha / 2
  exact xiSpectralPoint_ne_zero q this

theorem xiStripEdgeWeight_reflect (q : XiZeroCopy) :
    xiStripEdgeWeight (xiZeroCopyReflectEquiv q) = xiStripEdgeWeight q := by
  rw [xiStripEdgeWeight_eq_spectral, xiStripEdgeWeight_eq_spectral, xiSpectralPoint_reflect,
    neg_sq]

/-- Every copy carries at most half the budget: `Re w² ≤ 1/8000`. -/
theorem xiStripEdgeWeight_sq_re_le (q : XiZeroCopy) :
    (xiStripEdgeWeight q ^ (2 : ℕ)).re ≤ 1 / 8000 := by
  have hS := hasSum_xiStripEdgeWeight_sq_re
  have hpair := sum_le_hasSum ({q, xiZeroCopyReflectEquiv q} : Finset XiZeroCopy)
    (fun i _ => xiStripEdgeWeight_sq_re_nonneg i) hS
  rw [Finset.sum_pair (xiZeroCopyReflect_ne q).symm, xiStripEdgeWeight_reflect] at hpair
  linarith [stripEdgeBudget_le]

/-- The cubic separating the floor: `A(A+1)² < 8000(A − 1)` on `[32, 83]`. -/
theorem stripEdge_cubic_lt {A : ℝ} (h1 : 32 ≤ A) (h2 : A ≤ 83) :
    A * (A + 1) ^ 2 < 8000 * (A - 1) := by
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2))
    (by linarith : (0 : ℝ) ≤ A + 117)]

/-- **The unconditional height floor**: every zero copy has squared ordinate above `331/4`. -/
theorem xiSpectralPoint_re_sq_gt_floor (q : XiZeroCopy) :
    (331 / 4 : ℝ) < (xiSpectralPoint q).re ^ 2 := by
  by_contra hle
  push Not at hle
  have hw := xiStripEdgeWeight_sq_re_le q
  have hge := xiStripEdgeWeight_sq_re_ge q
  set A := ((1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ)).re with hAdef
  have hA32 : 32 < A :=
    lt_of_lt_of_le (xiSpectral_re_sq_gt_thirtytwo q) (sq_re_le_stripEdgeDenominator_re q)
  have hA83 : A ≤ 83 := by
    rw [hAdef, stripEdgeDenominator_re]
    nlinarith [sq_nonneg (xiSpectralPoint q).im]
  have hcub := stripEdge_cubic_lt hA32.le hA83
  have hden : 0 < (A ^ 2 + A) ^ 2 := by positivity
  have hlt : 1 / 8000 < (A ^ 2 - A) / (A ^ 2 + A) ^ 2 := by
    rw [div_lt_div_iff₀ (by norm_num) hden]
    have hfac : (A ^ 2 + A) ^ 2 = A * (A * (A + 1) ^ 2) := by ring
    have hfac' : (A ^ 2 - A) * 8000 = A * (8000 * (A - 1)) := by ring
    rw [hfac, hfac', one_mul]
    exact mul_lt_mul_of_pos_left hcub (by linarith)
  linarith

/-- No zero of `ξ` has ordinate of absolute value at most `9.09`. -/
theorem xi_zero_im_sq_gt_floor {ρ : ℂ} (hρ : xi ρ = 0) : (331 / 4 : ℝ) < ρ.im ^ 2 := by
  have hmem := mem_xi_divisor_support_of_eq_zero hρ
  let r : XiDivisorSupport := ⟨ρ, hmem⟩
  have hpos := xi_divisor_pos_on_support r
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (r : ℂ)) := by omega
  have h := xiSpectralPoint_re_sq_gt_floor ⟨r, ⟨0, hn⟩⟩
  rwa [xiSpectralPoint_re_eq] at h

/-- The floor as a centred distance: every divisor point lies at distance more than `9` from
the centre `1/2`. -/
theorem nine_lt_norm_sub_half_of_xi_zero {ρ : ℂ} (hρ : xi ρ = 0) : 9 < ‖ρ - 1 / 2‖ := by
  have h := xi_zero_im_sq_gt_floor hρ
  have hsq : ρ.im ^ 2 ≤ ‖ρ - 1 / 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have him : (ρ - 1 / 2).im = ρ.im := by simp
    rw [him]
    nlinarith [mul_self_nonneg (ρ - 1 / 2).re]
  nlinarith [norm_nonneg (ρ - 1 / 2)]

/-! ## The signed moment ratio gate -/

/-- The signed moments are sums of real parts over the zero copies. -/
theorem normalizedPrimeArchMoment_eq_tsum_re (n : ℕ) :
    normalizedPrimeArchMoment n =
      ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q ^ (n + 1)).re := by
  have h : ((normalizedPrimeArchMoment n : ℝ) : ℂ) = xiCentralReciprocalMoment n :=
    primeArchSourceMoment_eq_xiCentralReciprocalMoment n
  rw [← tsum_xiZeroCopyReciprocalSquare_pow] at h
  have hre := congrArg Complex.re h
  rwa [Complex.ofReal_re, Complex.re_tsum (summable_xiZeroCopyReciprocalSquare_pow n)] at hre

/-- **Termwise gate**: above the height floor, `Re a⁻⁶ < Re a⁻⁴ / 81`. -/
theorem xiZeroCopy_gate_term_lt (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q ^ (2 + 1)).re <
      (xiZeroCopyReciprocalSquare q ^ (1 + 1)).re / 81 := by
  set a := xiSpectralPoint q with ha
  have hu := xiSpectralPoint_re_sq_gt_floor q
  have hv := xiSpectralPoint_im_sq_lt_quarter q
  rw [← ha] at hu hv
  have ha0 : a ≠ 0 := xiSpectralPoint_ne_zero q
  set N := Complex.normSq a with hN
  have hNpos : 0 < N := Complex.normSq_pos.mpr ha0
  have hNeq : N = a.re ^ 2 + a.im ^ 2 := by rw [hN, Complex.normSq_apply]; ring
  have h6 : xiZeroCopyReciprocalSquare q ^ (2 + 1) = (a ^ (6 : ℕ))⁻¹ := by
    rw [xiZeroCopyReciprocalSquare, ← ha, ← pow_mul, inv_pow]
  have h4 : xiZeroCopyReciprocalSquare q ^ (1 + 1) = (a ^ (4 : ℕ))⁻¹ := by
    rw [xiZeroCopyReciprocalSquare, ← ha, ← pow_mul, inv_pow]
  rw [h6, h4]
  have hup : ((a ^ (6 : ℕ))⁻¹).re ≤ (N ^ 3)⁻¹ := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_inv, norm_pow, show ‖a‖ ^ (6 : ℕ) = (‖a‖ ^ 2) ^ 3 by ring, Complex.sq_norm]
  have hre4 : (a ^ (4 : ℕ)).re = a.re ^ 4 - 6 * a.re ^ 2 * a.im ^ 2 + a.im ^ 4 := by
    simp only [pow_succ, pow_zero, one_mul, mul_re, mul_im]
    ring
  have hlow : ((a ^ (4 : ℕ))⁻¹).re = (a.re ^ 4 - 6 * a.re ^ 2 * a.im ^ 2 + a.im ^ 4) / N ^ 4 := by
    rw [Complex.inv_re, hre4, map_pow]
  rw [hlow]
  have hkey : 81 * N < a.re ^ 4 - 6 * a.re ^ 2 * a.im ^ 2 + a.im ^ 4 := by
    rw [hNeq]
    nlinarith [sq_nonneg a.im, sq_nonneg (a.im ^ 2), mul_pos (by linarith : (0 : ℝ) < a.re ^ 2)
      (by linarith : (0 : ℝ) < 1 / 4 - a.im ^ 2)]
  refine lt_of_le_of_lt hup ?_
  calc (N ^ 3)⁻¹ = 81 * N / (81 * N ^ 4) := by field_simp
    _ < (a.re ^ 4 - 6 * a.re ^ 2 * a.im ^ 2 + a.im ^ 4) / (81 * N ^ 4) :=
        div_lt_div_of_pos_right hkey (by positivity)
    _ = (a.re ^ 4 - 6 * a.re ^ 2 * a.im ^ 2 + a.im ^ 4) / N ^ 4 / 81 := by ring

/-- The divisor of `ξ` is nonempty: otherwise both strip-edge sums vanish and `Λ₀'(1) = 0`,
against the certified derivative floor. -/
theorem xiZeroCopy_nonempty : Nonempty XiZeroCopy := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have h1 := hasSum_xiStripEdgeWeight.unique (hasSum_empty)
  have h2 := hasSum_xiStripEdgeWeight_sq.unique (hasSum_empty)
  have hz : completedRiemannZeta₀ 1 = 0 := by linear_combination h1 / 2
  rw [hz] at h2
  have hd : deriv completedRiemannZeta₀ 1 = 0 := by linear_combination -h2 / 4
  have := completedRiemannZeta₀_deriv_one_re_ge_num
  rw [hd, Complex.zero_re] at this
  norm_num at this

/-- **The route-Q ratio gate, unconditionally**:
`normalizedPrimeArchMoment 2 < normalizedPrimeArchMoment 1 / 81`. -/
theorem normalizedPrimeArchMoment_two_lt_one_div_eightyOne :
    normalizedPrimeArchMoment 2 < normalizedPrimeArchMoment 1 / 81 := by
  obtain ⟨q⟩ := xiZeroCopy_nonempty
  rw [normalizedPrimeArchMoment_eq_tsum_re, normalizedPrimeArchMoment_eq_tsum_re, ← tsum_div_const]
  have hs2 := (Complex.hasSum_re (summable_xiZeroCopyReciprocalSquare_pow 2).hasSum).summable
  have hs1 :=
    ((Complex.hasSum_re (summable_xiZeroCopyReciprocalSquare_pow 1).hasSum).summable).div_const 81
  exact Summable.tsum_lt_tsum (fun i => (xiZeroCopy_gate_term_lt i).le) (xiZeroCopy_gate_term_lt q)
    hs2 hs1

end

end RHTower
