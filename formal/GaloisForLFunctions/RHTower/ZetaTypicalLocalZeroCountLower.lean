import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCountMultiScale

/-!
# Lower local zero counts at the critical scale, at typical heights

`ZetaTypicalLocalZeroCount` bounds local zero counts from above. This module bounds them from
below, so that at typical heights the local counting is regular in both directions.

At `s = ½ + R + it` twice `Re ξ'/ξ(s)` is the full sum of the line-conjugate pair real parts
`P(R, a, u) = (R − a)/((R − a)² + u²) + (R + a)/((R + a)² + u²)`, with `a = Re ρ − ½` and
`u = t − Im ρ` (`two_mul_re_logDeriv_xi_eq_tsum_pair`). Under log-derivative scale data this sum is
`log(t/2π)` up to `2B + 3` (`abs_re_logDeriv_xi_sub_half_log_le_of_zetaLogDerivScaleData`).

**Pair bounds.** Under the scale-data alternative (`|a| ≤ R/2`, or `|a| + 12R < |u|`):
* every pair has `P(R, a, u) ≤ 4/R` (`xiLinePairRe_le_four_div`);
* a pair with `|u| ≥ R'` for some `R' ≥ R` satisfying the alternative at `R'` has
  `P(R, a, u) ≤ 25 (R/R') P(R', a, u)` (`xiLinePairRe_le_mul_of_far`). This holds because
  `P = 2R(R² − a² + u²)/(((R − a)² + u²)((R + a)² + u²))`, the denominator at `R` is at least `u⁴`,
  and the one at `R'` is at most `25u⁴`.

**Theorem** (`le_card_of_zetaLogDerivScaleData_two_scales`). With scale data at `R` and at `KR`
(`K ≥ 1`, `KR ≤ 1/16`, `t ≥ 8`), the zero copies with `|Im ρ − t| ≤ KR` number at least
`(R/4)(log(t/2π) − 2B − 3 − (25/K)(log(t/2π) + 2B' + 3))`. The pairs outside the band are
dominated by `(25/K)` times the pair sum at scale `KR`. The pairs inside it are at most `4/R` each.

**Corollary** (`exists_volume_localZeroCount_lt_le`). There are `C` and `κ₁` such that for all
large `T` and every `R` with `100R ≤ 1/16` and `κ = R log T ≥ κ₁`, the heights `t ∈ [T, 2T]` at
which fewer than `R log T/8` zero copies have ordinates within `100R` of `t` have measure at most
`C T e^{−κ/120000} + C T^{1/2}`. Together with the upper bound, at typical heights every window of
length `200R` around `t` carries between `R log T/8` and `2000 R log T` zeros.
-/

open Complex MeasureTheory Filter Set GaloisForLFunctions

namespace RHTower

noncomputable section

/-- The pair real part as a single fraction. -/
theorem xiLinePairRe_eq_div (R a u : ℝ) (h1 : 0 < (R - a) ^ 2 + u ^ 2)
    (h2 : 0 < (R + a) ^ 2 + u ^ 2) :
    xiLinePairRe R a u =
      2 * R * (R ^ 2 - a ^ 2 + u ^ 2) / (((R - a) ^ 2 + u ^ 2) * ((R + a) ^ 2 + u ^ 2)) := by
  unfold xiLinePairRe
  rw [div_add_div _ _ h1.ne' h2.ne']
  congr 1
  ring

/-- `b/(b² + u²) ≤ 1/(2|u|)` for `u ≠ 0`. -/
theorem div_sq_add_sq_le_inv_two_abs {b u : ℝ} (hu : u ≠ 0) :
    b / (b ^ 2 + u ^ 2) ≤ 1 / (2 * |u|) := by
  have hu' : 0 < |u| := abs_pos.mpr hu
  rcases le_or_gt b 0 with hb | hb
  · exact (div_nonpos_of_nonpos_of_nonneg hb (by positivity)).trans (by positivity)
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (b - |u|), sq_abs u]

/-- **A pair contributes at most `4/R`** under the scale-data alternative. -/
theorem xiLinePairRe_le_four_div {R a u : ℝ} (hR : 0 < R)
    (h : |a| ≤ R / 2 ∨ |a| + 12 * R < |u|) : xiLinePairRe R a u ≤ 4 / R := by
  rcases h with ha | hu
  · have ha' := abs_le.mp ha
    have h1 : 0 < R - a := by linarith
    have h2 : 0 < R + a := by linarith
    have t1 : (R - a) / ((R - a) ^ 2 + u ^ 2) ≤ 2 / R := by
      rw [div_le_div_iff₀ (by positivity) hR]
      nlinarith [sq_nonneg u, mul_nonneg h1.le (show 0 ≤ 2 * (R - a) - R by linarith)]
    have t2 : (R + a) / ((R + a) ^ 2 + u ^ 2) ≤ 2 / R := by
      rw [div_le_div_iff₀ (by positivity) hR]
      nlinarith [sq_nonneg u, mul_nonneg h2.le (show 0 ≤ 2 * (R + a) - R by linarith)]
    unfold xiLinePairRe
    have e : 4 / R = 2 / R + 2 / R := by ring
    linarith
  · have hu0 : u ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hu; linarith [abs_nonneg a]
    have hu12 : 12 * R < |u| := by linarith [abs_nonneg a]
    have t1 := div_sq_add_sq_le_inv_two_abs (b := R - a) hu0
    have t2 := div_sq_add_sq_le_inv_two_abs (b := R + a) hu0
    have h3 : 1 / (2 * |u|) ≤ 2 / R := by
      rw [div_le_div_iff₀ (by positivity) hR]; nlinarith
    unfold xiLinePairRe
    have e : 4 / R = 2 / R + 2 / R := by ring
    linarith

/-- **Far pairs are dominated by the pair at a larger scale.**  If `R ≤ R' ≤ |u|` and the pair
satisfies the scale-data alternative at `R'`, then `P(R, a, u) ≤ 25 (R/R') P(R', a, u)`. -/
theorem xiLinePairRe_le_mul_of_far {R R' a u : ℝ} (hR : 0 < R) (hRR : R ≤ R') (hu : R' ≤ |u|)
    (h : |a| ≤ R' / 2 ∨ |a| + 12 * R' < |u|) :
    xiLinePairRe R a u ≤ 25 * (R / R') * xiLinePairRe R' a u := by
  have hR' : 0 < R' := lt_of_lt_of_le hR hRR
  have hu0 : 0 < |u| := lt_of_lt_of_le hR' hu
  have hu2 : 0 < u ^ 2 := by rw [← sq_abs]; positivity
  have hau : |a| < |u| := by rcases h with h | h <;> linarith
  have ha2 : a ^ 2 < u ^ 2 := by
    rw [← sq_abs a, ← sq_abs u]; exact pow_lt_pow_left₀ hau (abs_nonneg _) two_ne_zero
  have hRa : R' + |a| ≤ 2 * |u| := by rcases h with h | h <;> linarith
  have hsq : (R' + |a|) ^ 2 ≤ 4 * u ^ 2 := by
    have h0 : 0 ≤ R' + |a| := by positivity
    have := mul_le_mul hRa hRa h0 (by positivity)
    nlinarith [sq_abs u]
  have e1 : (R' - a) ^ 2 ≤ (R' + |a|) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ |a| + a by linarith [neg_abs_le a])
      (show 0 ≤ 2 * R' + |a| - a by linarith [le_abs_self a])]
  have e2 : (R' + a) ^ 2 ≤ (R' + |a|) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ |a| - a by linarith [le_abs_self a])
      (show 0 ≤ 2 * R' + |a| + a by linarith [neg_abs_le a])]
  have hd1 : 0 < (R - a) ^ 2 + u ^ 2 := by positivity
  have hd2 : 0 < (R + a) ^ 2 + u ^ 2 := by positivity
  have hd1' : 0 < (R' - a) ^ 2 + u ^ 2 := by positivity
  have hd2' : 0 < (R' + a) ^ 2 + u ^ 2 := by positivity
  rw [xiLinePairRe_eq_div R a u hd1 hd2, xiLinePairRe_eq_div R' a u hd1' hd2']
  set D := ((R - a) ^ 2 + u ^ 2) * ((R + a) ^ 2 + u ^ 2) with hD
  set D' := ((R' - a) ^ 2 + u ^ 2) * ((R' + a) ^ 2 + u ^ 2) with hD'
  have hDge : u ^ 2 * u ^ 2 ≤ D :=
    mul_le_mul (by nlinarith [sq_nonneg (R - a)]) (by nlinarith [sq_nonneg (R + a)])
      hu2.le (by positivity)
  have hD'le : D' ≤ (5 * u ^ 2) * (5 * u ^ 2) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hD'pos : 0 < D' := by positivity
  have hN : 0 < R' ^ 2 - a ^ 2 + u ^ 2 := by nlinarith
  have hNR : 0 < R ^ 2 - a ^ 2 + u ^ 2 := by nlinarith
  have hNle : R ^ 2 - a ^ 2 + u ^ 2 ≤ R' ^ 2 - a ^ 2 + u ^ 2 := by nlinarith
  calc 2 * R * (R ^ 2 - a ^ 2 + u ^ 2) / D
      ≤ 2 * R * (R' ^ 2 - a ^ 2 + u ^ 2) / (u ^ 2 * u ^ 2) :=
        div_le_div₀ (by positivity) (by gcongr) (by positivity) hDge
    _ = 50 * R * (R' ^ 2 - a ^ 2 + u ^ 2) / ((5 * u ^ 2) * (5 * u ^ 2)) := by
        field_simp; ring
    _ ≤ 50 * R * (R' ^ 2 - a ^ 2 + u ^ 2) / D' :=
        div_le_div_of_nonneg_left (by positivity) hD'pos hD'le
    _ = 25 * (R / R') * (2 * R' * (R' ^ 2 - a ^ 2 + u ^ 2) / D') := by
        field_simp; ring

/-- The scale-data alternative for every zero copy. -/
theorem scaleData_alternative {t R B : ℝ} (hR : 0 < R) (hdata : ZetaLogDerivScaleData t R B)
    (q : XiZeroCopy) :
    |((q.1 : ℂ)).re - 1 / 2| ≤ R / 2 ∨
      |((q.1 : ℂ)).re - 1 / 2| + 12 * R < |t - ((q.1 : ℂ)).im| := by
  by_cases hnear : |((q.1 : ℂ)).re - 1 / 2| ≤ R / 2
  · exact Or.inl hnear
  · push Not at hnear
    have hfar := lt_abs_im_sub_of_zetaLogDerivScaleData hR hdata q hnear
    rw [abs_sub_comm ((q.1 : ℂ)).im t] at hfar
    exact Or.inr hfar

/-- Under scale data, the pair at every zero copy is nonnegative. -/
theorem xiLinePairRe_nonneg_of_scaleData {t R B : ℝ} (hR : 0 < R)
    (hdata : ZetaLogDerivScaleData t R B) (q : XiZeroCopy) :
    0 ≤ xiLinePairRe R (((q.1 : ℂ)).re - 1 / 2) (t - ((q.1 : ℂ)).im) := by
  rcases scaleData_alternative hR hdata q with h | h
  · exact xiLinePairRe_nonneg_of_near hR h
  · refine xiLinePairRe_nonneg_of_sq_lt hR ?_
    have h1 : |((q.1 : ℂ)).re - 1 / 2| < |t - ((q.1 : ℂ)).im| := by
      linarith [abs_nonneg (((q.1 : ℂ)).re - 1 / 2)]
    exact sq_lt_sq.mpr h1

/-- The pair real parts at `s` are summable and sum to `2 Re ξ'/ξ(s)`. -/
theorem summable_xiLinePairRe_and_tsum_eq {s : ℂ} (hxi : xi s ≠ 0) :
    Summable (fun q : XiZeroCopy =>
      xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im)) ∧
    ∑' q : XiZeroCopy, xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2)
      (s.im - ((q.1 : ℂ)).im) = 2 * (logDeriv xi s).re := by
  have hsum : Summable (pfTerm s) := summable_partialFractionTerm hxi
  have hsumJ : Summable (fun q => pfTerm s (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpairs : Summable (fun q => pfTerm s q + pfTerm s (xiZeroCopyLineConjEquiv q)) :=
    hsum.add hsumJ
  have heq : ∀ q, (pfTerm s q + pfTerm s (xiZeroCopyLineConjEquiv q)).re =
      xiLinePairRe (s.re - 1 / 2) (((q.1 : ℂ)).re - 1 / 2) (s.im - ((q.1 : ℂ)).im) :=
    fun q => re_partialFraction_pair_eq s q
  exact ⟨(Complex.reCLM.summable hpairs).congr heq, (two_mul_re_logDeriv_xi_eq_tsum_pair hxi).symm⟩

/-- The point `½ + R + it` is not a zero of `ξ` under scale data at `(t, R, B)`. -/
theorem xi_ne_zero_of_zetaLogDerivScaleData {t R B : ℝ} (ht : 8 ≤ t) (hR : 0 < R)
    (hdata : ZetaLogDerivScaleData t R B) :
    xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
  set s : ℂ := ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = 1 / 2 + R := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim, Complex.one_im] at this; linarith
  have hζ : riemannZeta s ≠ 0 := by
    intro h0
    have := hdata.zeroFree s h0 (by rw [hsre]; linarith)
    rw [hsim, sub_self, abs_zero, hsre] at this
    linarith
  exact fun h => hζ ((xi_eq_zero_iff (by rw [hsre]; linarith) hs1).mp h)

/-- **Lower local zero count from scale data at two scales.** -/
theorem le_card_of_zetaLogDerivScaleData_two_scales {t R K B B' : ℝ} (ht : 8 ≤ t) (hR : 0 < R)
    (hK : 1 ≤ K) (hKR : K * R ≤ 1 / 16) (h1 : ZetaLogDerivScaleData t R B)
    (h2 : ZetaLogDerivScaleData t (K * R) B') :
    R / 4 * (Real.log (t / (2 * Real.pi)) - 2 * B - 3 -
        25 / K * (Real.log (t / (2 * Real.pi)) + 2 * B' + 3)) ≤
      ((finite_xiZeroCopy_band t (r := K * R) (by positivity)).toFinset.card : ℝ) := by
  classical
  have hKR0 : 0 < K * R := by positivity
  have hRle : R ≤ K * R := le_mul_of_one_le_left hR.le hK
  have hR16 : R ≤ 1 / 16 := hRle.trans hKR
  set s : ℂ := ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I with hs
  set s' : ℂ := ((1 / 2 + K * R : ℝ) : ℂ) + (t : ℂ) * I with hs'
  have hsre : s.re - 1 / 2 = R := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hsre' : s'.re - 1 / 2 = K * R := by simp [hs']
  have hsim' : s'.im = t := by simp [hs']
  obtain ⟨hf, hfsum⟩ :=
    summable_xiLinePairRe_and_tsum_eq (xi_ne_zero_of_zetaLogDerivScaleData ht hR h1)
  obtain ⟨hg, hgsum⟩ :=
    summable_xiLinePairRe_and_tsum_eq (xi_ne_zero_of_zetaLogDerivScaleData ht hKR0 h2)
  rw [← hs, hsre, hsim] at hf hfsum
  rw [← hs', hsre', hsim'] at hg hgsum
  set f : XiZeroCopy → ℝ := fun q => xiLinePairRe R (((q.1 : ℂ)).re - 1 / 2) (t - ((q.1 : ℂ)).im)
    with hfdef
  set g : XiZeroCopy → ℝ :=
    fun q => xiLinePairRe (K * R) (((q.1 : ℂ)).re - 1 / 2) (t - ((q.1 : ℂ)).im) with hgdef
  -- the two-sided smoothed densities
  have hlow := abs_re_logDeriv_xi_sub_half_log_le_of_zetaLogDerivScaleData ht hR hR16 h1
  have hhigh := abs_re_logDeriv_xi_sub_half_log_le_of_zetaLogDerivScaleData ht hKR0 hKR h2
  rw [← hs] at hlow
  rw [← hs'] at hhigh
  have hflow : Real.log (t / (2 * Real.pi)) - 2 * B - 3 ≤ ∑' q, f q := by
    rw [hfsum]; linarith [(abs_le.mp hlow).1]
  have hghigh : ∑' q, g q ≤ Real.log (t / (2 * Real.pi)) + 2 * B' + 3 := by
    rw [hgsum]; linarith [(abs_le.mp hhigh).2]
  have hg0 : ∀ q, 0 ≤ g q := fun q => xiLinePairRe_nonneg_of_scaleData hKR0 h2 q
  -- split into the band and its complement
  set F := (finite_xiZeroCopy_band t (r := K * R) hKR0.le).toFinset with hFdef
  have hmemF : ∀ q, q ∈ F ↔ |((q.1 : ℂ)).im - t| ≤ K * R := fun q => by
    rw [hFdef, Set.Finite.mem_toFinset]; rfl
  have hsplit := hf.sum_add_tsum_compl (s := F)
  have hnear : ∑ q ∈ F, f q ≤ (F.card : ℝ) * (4 / R) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun q _ => xiLinePairRe_le_four_div hR (scaleData_alternative hR h1 q)
  have hfar_pt : ∀ q : ↑(↑F : Set XiZeroCopy)ᶜ, f q ≤ 25 / K * g q := by
    intro q
    set x : XiZeroCopy := q.1 with hx
    have hq : ¬ |((x.1 : ℂ)).im - t| ≤ K * R := fun h => q.2 (Finset.mem_coe.mpr ((hmemF x).mpr h))
    push Not at hq
    have hu : K * R ≤ |t - ((x.1 : ℂ)).im| := by rw [abs_sub_comm]; exact hq.le
    have := xiLinePairRe_le_mul_of_far hR hRle hu (scaleData_alternative hKR0 h2 x)
    have e : 25 * (R / (K * R)) = 25 / K := by field_simp
    rw [e] at this
    exact this
  have hfar : ∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, f q ≤ 25 / K * ∑' q, g q := by
    have hgs : Summable fun q : ↑(↑F : Set XiZeroCopy)ᶜ => g q := hg.subtype _
    calc ∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, f q ≤ ∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, 25 / K * g q :=
          Summable.tsum_le_tsum hfar_pt (hf.subtype _) (hgs.mul_left _)
      _ = 25 / K * ∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, g q := tsum_mul_left
      _ ≤ 25 / K * ∑' q, g q :=
          mul_le_mul_of_nonneg_left (Summable.tsum_subtype_le g _ hg0 hg) (by positivity)
  have hK0 : 0 < 25 / K := by positivity
  have hcard : Real.log (t / (2 * Real.pi)) - 2 * B - 3 -
      25 / K * (Real.log (t / (2 * Real.pi)) + 2 * B' + 3) ≤ (F.card : ℝ) * (4 / R) := by
    have := mul_le_mul_of_nonneg_left hghigh hK0.le
    linarith
  have hR4 : 0 < R / 4 := by positivity
  have e : (F.card : ℝ) * (4 / R) * (R / 4) = F.card := by field_simp
  calc R / 4 * (Real.log (t / (2 * Real.pi)) - 2 * B - 3 -
        25 / K * (Real.log (t / (2 * Real.pi)) + 2 * B' + 3))
      ≤ R / 4 * ((F.card : ℝ) * (4 / R)) := mul_le_mul_of_nonneg_left hcard hR4.le
    _ = F.card := by rw [mul_comm]; exact e

/-- `log(2π) < 2`. -/
private theorem log_two_pi_lt_two : Real.log (2 * Real.pi) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  have hpi := Real.pi_lt_d2
  have he : (2.7 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [he2]; nlinarith

/-- The exceptional-set profile at level `log T/16`, at any `y ≥ 120000`, is at most
`18 e^{−y/120000}`. -/
theorem scaleData_profile_le {y : ℝ} (hy : 120000 ≤ y) :
    Real.exp (-(y / 120000)) / (1 / 16) + (y ^ 2 * Real.exp (-(y / 16)) +
      Real.exp (-(y * (1 / 16) / 15))) ≤ 18 * Real.exp (-(y / 120000)) := by
  have h1 := sq_mul_exp_neg_div_sixteen_le (x := y) (by linarith)
  have h2 : Real.exp (-(y * (1 / 16) / 15)) ≤ Real.exp (-(y / 120000)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have e : Real.exp (-(y / 120000)) / (1 / 16) = 16 * Real.exp (-(y / 120000)) := by ring
  rw [e]; linarith

/-- **Sparse critical-scale windows are exponentially rare.**  There are `C` and `κ₁` such that for
all large `T` and every `R` with `100R ≤ 1/16` and `κ = R log T ≥ κ₁`, the heights `t ∈ [T, 2T]` at
which fewer than `κ/8` zero copies have ordinates within `100R` of `t` have measure at most
`C T e^{−κ/120000} + C T^{1/2}`. -/
theorem exists_volume_localZeroCount_lt_le :
    ∃ C κ₁ : ℝ, 0 < C ∧ 1 ≤ κ₁ ∧ ∀ᶠ T in atTop, ∀ R : ℝ, 0 < R → 100 * R ≤ 1 / 16 →
      κ₁ ≤ R * Real.log T →
      volume {t | t ∈ Icc T (2 * T) ∧
          ({q : XiZeroCopy | |((q.1 : ℂ)).im - t| ≤ 100 * R}.ncard : ℝ) <
            R * Real.log T / 8} ≤
        ENNReal.ofReal (C * T * Real.exp (-(R * Real.log T / 120000)) +
          C * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, κ₁, hC, hκ₁, hev⟩ := exists_volume_not_zetaLogDerivScaleData_le_exp (ε := 1 / 16)
    (by norm_num) (by norm_num)
  refine ⟨36 * C, max κ₁ 120000, by positivity, le_trans hκ₁ (le_max_left _ _), ?_⟩
  filter_upwards [hev, Real.tendsto_log_atTop.eventually_ge_atTop 56,
    eventually_ge_atTop (8 : ℝ)] with T hT hTlog hT8 R hR hR100 hκ
  have hR16 : R ≤ 1 / 16 := by linarith
  have hκR : κ₁ ≤ R * Real.log T := (le_max_left _ _).trans hκ
  have hκR' : κ₁ ≤ 100 * R * Real.log T := by
    have : 0 ≤ R * Real.log T := by linarith [(le_max_right κ₁ 120000).trans hκ]
    nlinarith
  have hx : 120000 ≤ R * Real.log T := (le_max_right _ _).trans hκ
  have hx' : 120000 ≤ 100 * R * Real.log T := by nlinarith
  set A := {t | t ∈ Icc T (2 * T) ∧ ¬ ZetaLogDerivScaleData t R (1 / 16 * Real.log T)} with hA
  set A' := {t | t ∈ Icc T (2 * T) ∧
    ¬ ZetaLogDerivScaleData t (100 * R) (1 / 16 * Real.log T)} with hA'
  have hsub : {t | t ∈ Icc T (2 * T) ∧
      ({q : XiZeroCopy | |((q.1 : ℂ)).im - t| ≤ 100 * R}.ncard : ℝ) < R * Real.log T / 8} ⊆
      A ∪ A' := by
    intro t ht
    by_contra hnot
    simp only [hA, hA', Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_not] at hnot
    have h1 := hnot.1 ht.1
    have h2 := hnot.2 ht.1
    have ht8 : 8 ≤ t := le_trans hT8 ht.1.1
    have hbound := le_card_of_zetaLogDerivScaleData_two_scales ht8 hR (K := 100) (by norm_num)
      hR100 h1 h2
    have hnc : (({q : XiZeroCopy | |((q.1 : ℂ)).im - t| ≤ 100 * R}.ncard : ℕ) : ℝ) =
        ((finite_xiZeroCopy_band t (r := 100 * R) (by positivity)).toFinset.card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ (finite_xiZeroCopy_band t (r := 100 * R) (by positivity))]
    rw [← hnc] at hbound
    have hT0 : 0 < T := by linarith
    have hlo : Real.log T - 2 ≤ Real.log (t / (2 * Real.pi)) := by
      have : Real.log (T / (2 * Real.pi)) ≤ Real.log (t / (2 * Real.pi)) :=
        Real.log_le_log (by positivity) (by gcongr; exact ht.1.1)
      rw [Real.log_div hT0.ne' (by positivity)] at this
      linarith [log_two_pi_lt_two]
    have hkey : R * Real.log T / 8 ≤ R / 4 * (Real.log (t / (2 * Real.pi)) -
        2 * (1 / 16 * Real.log T) - 3 - 25 / 100 * (Real.log (t / (2 * Real.pi)) +
          2 * (1 / 16 * Real.log T) + 3)) := by
      have hin : Real.log T / 2 ≤ Real.log (t / (2 * Real.pi)) -
          2 * (1 / 16 * Real.log T) - 3 - 25 / 100 * (Real.log (t / (2 * Real.pi)) +
            2 * (1 / 16 * Real.log T) + 3) := by nlinarith
      have := mul_le_mul_of_nonneg_left hin (show 0 ≤ R / 4 by positivity)
      linarith
    linarith [ht.2]
  have hm1 := hT R hR hR16 hκR
  have hm2 := hT (100 * R) (by positivity) hR100 hκR'
  have hp1 := scaleData_profile_le hx
  have hp2 := scaleData_profile_le hx'
  have hexp : Real.exp (-(100 * R * Real.log T / 120000)) ≤ Real.exp (-(R * Real.log T / 120000)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc volume {t | t ∈ Icc T (2 * T) ∧
        ({q : XiZeroCopy | |((q.1 : ℂ)).im - t| ≤ 100 * R}.ncard : ℝ) < R * Real.log T / 8}
      ≤ volume (A ∪ A') := measure_mono hsub
    _ ≤ volume A + volume A' := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C * T * (Real.exp (-(R * Real.log T / 120000)) / (1 / 16) +
          ((R * Real.log T) ^ 2 * Real.exp (-(R * Real.log T / 16)) +
            Real.exp (-(R * Real.log T * (1 / 16) / 15)))) + C * T ^ ((1 : ℝ) / 2)) +
        ENNReal.ofReal (C * T * (Real.exp (-(100 * R * Real.log T / 120000)) / (1 / 16) +
          ((100 * R * Real.log T) ^ 2 * Real.exp (-(100 * R * Real.log T / 16)) +
            Real.exp (-(100 * R * Real.log T * (1 / 16) / 15)))) + C * T ^ ((1 : ℝ) / 2)) := by
        exact add_le_add hm1 (by simpa only [mul_assoc] using hm2)
    _ ≤ ENNReal.ofReal (36 * C * T * Real.exp (-(R * Real.log T / 120000)) +
          36 * C * T ^ ((1 : ℝ) / 2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hT0 : 0 ≤ T := by linarith
        have hCT : 0 ≤ C * T := by positivity
        have hs : 0 ≤ C * T ^ ((1 : ℝ) / 2) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hp1 hCT, mul_le_mul_of_nonneg_left hp2 hCT,
          mul_le_mul_of_nonneg_left hexp hCT, Real.exp_pos (-(R * Real.log T / 120000))]

end

end RHTower
