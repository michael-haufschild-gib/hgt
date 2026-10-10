import GaloisForLFunctions.HTGeometry.ToeplitzBorderedDeflation
import GaloisForLFunctions.HTGeometry.LogConcaveRatioRadius
import GaloisForLFunctions.HTGeometry.ReciprocalPositivityMinimumModulus
import GaloisForLFunctions.HTGeometry.VivantiPringsheim

/-!
# One deflation step for reciprocally totally positive entire functions

For an entire `F` with `F 0 ≠ 0` let `b_n` be the Taylor coefficients of `1/F(−z)` at `0`
(`recipCoeff`).  Call `F` *reciprocally totally positive* (`ReciprocalTP`) when the derivatives of
`1/F(−z)` at `0` are nonnegative reals and `b` is consecutive-row totally positive.

Suppose `F` has no zeros in `‖y‖ < D` and a zero on `‖y‖ = D`.

* `ReciprocalTP.apply_neg_eq_zero`: then `F(−D) = 0`.  This is the minimum-modulus form of
  Pringsheim: on each circle, `‖F(−z)‖` is smallest on the positive axis.
* `ReciprocalTP.deflate`: `G(y) = F(y)/(1 + y/D) = D · dslope F (−D) y` is again reciprocally
  totally positive.  Indeed `1/G(−z) = (1 − z/D)/F(−z)`, so the reciprocal coefficients of `G` are
  `b_n − b_{n−1}/D`.  The coefficients `b` are positive and log-concave, and `Σ b_n yⁿ` has radius
  exactly `D`, so `b_{n+1}/b_n → 1/D` (`tendsto_ratio_of_logConcave`).  The bordered limit
  (`ConsecutiveRowTP.deflate`) then keeps every consecutive-row minor nonnegative.
-/

open Complex Filter Topology Metric
open scoped ComplexOrder Nat

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The reciprocal of `F` at `−z`. -/
def recipNeg (F : ℂ → ℂ) (z : ℂ) : ℂ := (F (-z))⁻¹

/-- The Taylor coefficients of `1/F(−z)` at `0`, as real numbers. -/
def recipCoeff (F : ℂ → ℂ) (n : ℕ) : ℝ := (((n ! : ℂ))⁻¹ * iteratedDeriv n (recipNeg F) 0).re

/-- Reciprocal total positivity of an entire function. -/
structure ReciprocalTP (F : ℂ → ℂ) : Prop where
  differentiable : Differentiable ℂ F
  ne_zero : F 0 ≠ 0
  nonneg : ∀ n, 0 ≤ iteratedDeriv n (recipNeg F) 0
  tp : ConsecutiveRowTP (recipCoeff F)

/-- Reciprocal total positivity up to order `k`: the reciprocal coefficients are nonnegative and
their consecutive-row minors of order `≤ k` are nonnegative. -/
structure ReciprocalTPUpTo (k : ℕ) (F : ℂ → ℂ) : Prop where
  differentiable : Differentiable ℂ F
  ne_zero : F 0 ≠ 0
  nonneg : ∀ n, 0 ≤ iteratedDeriv n (recipNeg F) 0
  tp : ConsecutiveRowTPUpTo k (recipCoeff F)

theorem ReciprocalTP.upTo {F : ℂ → ℂ} (hF : ReciprocalTP F) (k : ℕ) : ReciprocalTPUpTo k F :=
  ⟨hF.differentiable, hF.ne_zero, hF.nonneg, hF.tp.upTo k⟩

/-- A nonnegative real derivative recovers the coefficient: `g^{(n)}(0) = n! · b_n`. -/
theorem iteratedDeriv_recipNeg_eq {k : ℕ} {F : ℂ → ℂ} (hF : ReciprocalTPUpTo k F) (n : ℕ) :
    iteratedDeriv n (recipNeg F) 0 = (((n ! : ℝ) * recipCoeff F n : ℝ) : ℂ) := by
  have hD := hF.nonneg n
  have hcoef : recipCoeff F n = ((n ! : ℝ))⁻¹ * (iteratedDeriv n (recipNeg F) 0).re := by
    unfold recipCoeff
    rw [show ((n ! : ℂ))⁻¹ = ((((n ! : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  rw [hcoef]
  have hfac : (n ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [← mul_assoc, mul_inv_cancel₀ hfac, one_mul]
  apply Complex.ext
  · simp
  · simp [(Complex.nonneg_iff.mp hD).2.symm]

theorem recipCoeff_nonneg {k : ℕ} {F : ℂ → ℂ} (hF : ReciprocalTPUpTo k F) (n : ℕ) :
    0 ≤ recipCoeff F n := by
  have h := hF.nonneg n
  unfold recipCoeff
  rw [show ((n ! : ℂ))⁻¹ = ((((n ! : ℝ))⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity) (Complex.nonneg_iff.mp h).1

/-- **Pringsheim: the nearest zero is on the negative axis.** -/
theorem ReciprocalTPUpTo.apply_neg_eq_zero {k : ℕ} {F : ℂ → ℂ} (hF : ReciprocalTPUpTo k F) {D : ℝ}
    (hD : 0 < D)
    (hfree : ∀ z : ℂ, ‖z‖ < D → F z ≠ 0) {w : ℂ} (hw : ‖w‖ = D) (hw0 : F w = 0) :
    F (-(D : ℂ)) = 0 := by
  have hh : Differentiable ℂ (fun z => F (-z)) := hF.differentiable.comp differentiable_neg
  have h := apply_eq_zero_of_inv_taylor_nonneg hh hD
    (fun z hz => hfree (-z) (by rwa [norm_neg])) hF.nonneg (w := -w) (by rwa [norm_neg])
    (by simpa using hw0)
  simpa using h

/-- The Taylor series of `1/F(−z)` converges to it on the zero-free disk, with real terms. -/
theorem hasSum_recipCoeff {k : ℕ} {F : ℂ → ℂ} (hF : ReciprocalTPUpTo k F) {D : ℝ}
    (hfree : ∀ z : ℂ, ‖z‖ < D → F z ≠ 0) {z : ℂ} (hz : ‖z‖ < D) :
    HasSum (fun n => ((recipCoeff F n : ℝ) : ℂ) * z ^ n) (recipNeg F z) := by
  have hg : DifferentiableOn ℂ (recipNeg F) (ball 0 D) := by
    intro x hx
    have hx' : ‖x‖ < D := by simpa using hx
    have : F (-x) ≠ 0 := hfree (-x) (by rwa [norm_neg])
    exact ((hF.differentiable.comp differentiable_neg).differentiableAt.inv this).differentiableWithinAt
  have h := Complex.hasSum_taylorSeries_on_ball hg (by simpa using hz)
  refine h.congr_fun fun n => ?_
  simp only [sub_zero, smul_eq_mul]
  rw [iteratedDeriv_recipNeg_eq hF n]
  have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  push_cast
  field_simp

/-- The iterated derivatives at `0` of `(1 + c z) g(z)`. -/
theorem factorial_inv_mul_iteratedDeriv_linear_mul {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (c : ℂ)
    (n : ℕ) :
    ((n ! : ℂ))⁻¹ * iteratedDeriv n (fun z => (1 + c * z ^ 1) * g z) 0 =
      ((n ! : ℂ))⁻¹ * iteratedDeriv n g 0 +
        (if n = 0 then 0 else c * ((((n - 1) ! : ℂ))⁻¹ * iteratedDeriv (n - 1) g 0)) := by
  have hl : AnalyticAt ℂ (fun z : ℂ => 1 + c * z ^ 1) 0 := by fun_prop
  have hlder : ∀ k : ℕ, iteratedDeriv k (fun z : ℂ => 1 + c * z ^ 1) 0 =
      (if k = 0 then 1 else 0) + c * (if k = 1 then 1 else 0) := by
    intro k
    have hc0 : ContDiffAt ℂ k (fun _ : ℂ => (1 : ℂ)) 0 := contDiffAt_const
    have hc1 : ContDiffAt ℂ k (fun z : ℂ => c * z ^ 1) 0 := by fun_prop
    rw [iteratedDeriv_fun_add hc0 hc1, iteratedDeriv_const,
      iteratedDeriv_const_mul_field c (fun z : ℂ => z ^ 1), iteratedDeriv_fun_pow_zero]
    simp
  have hmul : (fun z => (1 + c * z ^ 1) * g z) = (fun z : ℂ => 1 + c * z ^ 1) * g := rfl
  rw [hmul, iteratedDeriv_mul hl.contDiffAt hg.contDiffAt]
  rcases n with _ | m
  · simp
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hrest : ∑ i ∈ Finset.range m, ((m + 1).choose (i + 1 + 1) : ℂ) *
        iteratedDeriv (i + 1 + 1) (fun z : ℂ => 1 + c * z ^ 1) 0 *
          iteratedDeriv (m + 1 - (i + 1 + 1)) g 0 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hlder]
      simp
    rw [hrest, zero_add, hlder, hlder]
    simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_mul,
      Nat.sub_zero, add_tsub_cancel_right, one_ne_zero, if_false, if_true, zero_add,
      Nat.add_one_ne_zero]
    have h1 : ((m + 1) ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h2 : (m ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem differentiable_dslope_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a : ℂ) :
    Differentiable ℂ (dslope F a) := by
  have h := (Complex.differentiableOn_dslope (s := Set.univ) (c := a) Filter.univ_mem).mpr
    hF.differentiableOn
  exact differentiableOn_univ.mp h

/-- **One deflation step.**  If `F` is reciprocally totally positive, zero-free on `‖y‖ < D`, and
vanishes somewhere on `‖y‖ = D`, then `G(y) = D · dslope F (−D) y = F(y)/(1 + y/D)` is reciprocally
totally positive. -/
theorem ReciprocalTPUpTo.deflate {k : ℕ} {F : ℂ → ℂ} (hF : ReciprocalTPUpTo (k + 2) F) {D : ℝ}
    (hD : 0 < D) (hfree : ∀ z : ℂ, ‖z‖ < D → F z ≠ 0) {w : ℂ} (hw : ‖w‖ = D) (hw0 : F w = 0) :
    ReciprocalTPUpTo (k + 1) (fun y => (D : ℂ) * dslope F (-(D : ℂ)) y) := by
  set b := recipCoeff F with hbdef
  have hFD : F (-(D : ℂ)) = 0 := hF.apply_neg_eq_zero hD hfree hw hw0
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  -- the factorization `F y = (y + D) · dslope F (−D) y`
  have hfac : ∀ y : ℂ, F y = (y + D) * dslope F (-(D : ℂ)) y := by
    intro y
    have := sub_smul_dslope F (-(D : ℂ)) y
    rw [hFD, sub_zero, smul_eq_mul, sub_neg_eq_add] at this
    exact this.symm
  set G : ℂ → ℂ := fun y => (D : ℂ) * dslope F (-(D : ℂ)) y with hGdef
  have hGdiff : Differentiable ℂ G :=
    (differentiable_const _).mul (differentiable_dslope_entire hF.differentiable _)
  have hG0 : G 0 = F 0 := by
    have := hfac 0
    rw [zero_add] at this
    rw [hGdef]
    simp only
    rw [this]
  -- the reciprocal of `G(−z)` is `(1 − z/D)/F(−z)` near `0`
  have hgF : AnalyticAt ℂ (recipNeg F) 0 := by
    have hne : F (-0) ≠ 0 := by simpa using hF.ne_zero
    exact ((hF.differentiable.comp differentiable_neg).analyticAt 0).inv hne
  have hev : recipNeg G =ᶠ[𝓝 0] fun z => (1 + (-(1 / (D : ℂ))) * z ^ 1) * recipNeg F z := by
    have hcont : ContinuousAt (fun z : ℂ => F (-z)) 0 :=
      (hF.differentiable.comp differentiable_neg).continuous.continuousAt
    filter_upwards [hcont.eventually_ne (by simpa using hF.ne_zero),
      (continuous_id.continuousAt (x := (0 : ℂ))).eventually_ne
        (show (0 : ℂ) ≠ (D : ℂ) from fun h => hD.ne' (by exact_mod_cast h.symm))] with z hz hzD
    simp only [recipNeg, hGdef]
    have hfz := hfac (-z)
    have hlin : -z + (D : ℂ) ≠ 0 := by
      intro h
      apply hzD
      simp only [id]
      linear_combination -h
    have hdsl : dslope F (-(D : ℂ)) (-z) = F (-z) / (-z + D) := by
      field_simp
      rw [mul_comm]
      exact hfz.symm
    rw [hdsl]
    field_simp
    ring
  -- the reciprocal coefficients of `G` are the deflated sequence
  have hcoeff : ∀ n, ((n ! : ℂ))⁻¹ * iteratedDeriv n (recipNeg G) 0 =
      ((deflateSeq b (1 / D) n : ℝ) : ℂ) := by
    intro n
    rw [(hev.iteratedDeriv_eq n), factorial_inv_mul_iteratedDeriv_linear_mul hgF]
    have hb : ∀ k, ((k ! : ℂ))⁻¹ * iteratedDeriv k (recipNeg F) 0 = ((b k : ℝ) : ℂ) := by
      intro k
      rw [iteratedDeriv_recipNeg_eq hF k, hbdef]
      have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      push_cast
      field_simp
    rw [hb]
    unfold deflateSeq
    rcases n with _ | m
    · simp [zext_of_neg]
    · rw [if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel, hb,
        show (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) by push_cast; ring, zext_natCast]
      push_cast
      ring
  -- positivity, log-concavity, and the radius of `Σ b_n yⁿ`
  have hb0 : 0 < b 0 := by
    have hnn := recipCoeff_nonneg hF 0
    rcases hnn.eq_or_lt with h | h
    · exfalso
      have hz := iteratedDeriv_recipNeg_eq hF 0
      rw [← h] at hz
      simp only [iteratedDeriv_zero, recipNeg, neg_zero, Nat.factorial_zero, Nat.cast_one,
        one_mul, Complex.ofReal_zero, inv_eq_zero] at hz
      exact hF.ne_zero hz
    · exact h
  have hconv : ∀ y : ℝ, 0 ≤ y → y < D → Summable (fun n => b n * y ^ n) := by
    intro y hy0 hyD
    have h := hasSum_recipCoeff hF hfree (z := (y : ℂ)) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]; exact hyD)
    have : Summable (fun n => ((b n * y ^ n : ℝ) : ℂ)) := by
      refine h.summable.congr fun n => ?_
      push_cast
      rfl
    exact Complex.summable_ofReal.mp this
  have hdiv : ∀ y : ℝ, D < y → ¬ Summable (fun n => b n * y ^ n) := by
    intro y hDy hsum
    have hy0 : 0 < y := lt_trans hD hDy
    have hbnn : ∀ n, 0 ≤ b n := recipCoeff_nonneg hF
    have hconvy : ∀ s : ℝ, 0 ≤ s → s < y → Summable (fun n => |b n| * s ^ n) := by
      intro s hs0 hsy
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
      rw [abs_of_nonneg (hbnn n)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hsy.le n) (hbnn n)
    have hS := analyticOnNhd_realSeriesSum hy0 hconvy
    -- on the zero-free disk the series is `1/F(−z)`
    have hagree : ∀ z : ℂ, ‖z‖ < D → realSeriesSum b z = recipNeg F z := by
      intro z hz
      rw [realSeriesSum, (hasSum_recipCoeff hF hfree hz).tsum_eq]
    -- continuity at the boundary zero gives `F(w) · S(−w) = 1`
    have hcontS : ContinuousAt (realSeriesSum b) (-w) :=
      (hS (-w) (by rw [mem_ball, dist_zero_right, norm_neg, hw]; exact hDy)).continuousAt
    have hcontF : ContinuousAt (fun z => F (-z)) (-w) :=
      (hF.differentiable.comp differentiable_neg).continuous.continuousAt
    set seq : ℕ → ℂ := fun k => ((1 - 1 / ((k : ℝ) + 2) : ℝ) : ℂ) * (-w) with hseq
    have hseqlim : Tendsto seq atTop (𝓝 (-w)) := by
      have h1 : Tendsto (fun k : ℕ => (1 - 1 / ((k : ℝ) + 2) : ℝ)) atTop (𝓝 1) := by
        have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
          have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
            (tendsto_add_atTop_nat 1)
          refine h0.congr fun k => ?_
          simp only [Function.comp_apply]
          push_cast
          ring
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
      have h2 := ((Complex.continuous_ofReal.tendsto 1).comp h1).mul_const (-w)
      rw [Complex.ofReal_one, one_mul] at h2
      exact h2
    have hseqin : ∀ k, ‖seq k‖ < D := by
      intro k
      rw [hseq, norm_mul, norm_neg, hw, Complex.norm_real, Real.norm_eq_abs]
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
      have hk1 : 1 / ((k : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      rw [abs_of_pos (by linarith)]
      nlinarith
    have hone : ∀ k, F (-(seq k)) * realSeriesSum b (seq k) = 1 := by
      intro k
      rw [hagree _ (hseqin k), recipNeg]
      exact mul_inv_cancel₀ (hfree _ (by rw [norm_neg]; exact hseqin k))
    have hlim : Tendsto (fun k => F (-(seq k)) * realSeriesSum b (seq k)) atTop
        (𝓝 (F (-(-w)) * realSeriesSum b (-w))) :=
      (hcontF.tendsto.comp hseqlim).mul (hcontS.tendsto.comp hseqlim)
    simp only [hone, neg_neg, hw0, zero_mul] at hlim
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)
  have hlc : ∀ n, b n * b (n + 2) ≤ b (n + 1) ^ 2 := by
    intro n
    have h := hF.tp 2 (by omega) 0 ![n + 1, n + 2] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    rw [toeplitzMinor, Matrix.det_fin_two] at h
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add,
      Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, sub_zero] at h
    rw [show ((n + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) from rfl, zext_natCast,
      show ((n + 2 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) from rfl, zext_natCast,
      show ((n + 1 : ℕ) : ℤ) - 1 = ((n : ℕ) : ℤ) by push_cast; ring, zext_natCast,
      show ((n + 2 : ℕ) : ℤ) - 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zext_natCast] at h
    nlinarith [h]
  have hbpos : ∀ n, 0 < b n := by
    by_contra hneg
    push Not at hneg
    obtain ⟨n₀, hn₀⟩ := hneg
    have hzero : ∃ n, b n = 0 := ⟨n₀, le_antisymm hn₀ (recipCoeff_nonneg hF n₀)⟩
    classical
    set n := Nat.find hzero with hndef
    have hbn : b n = 0 := Nat.find_spec hzero
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at hbn; linarith
      · exact h
    have hprev : 0 < b (n - 1) := by
      rcases (recipCoeff_nonneg hF (n - 1)).eq_or_lt with h | h
      · exact absurd h.symm (Nat.find_min hzero (by omega))
      · exact h
    -- all later coefficients vanish
    have hlater : ∀ m, n < m → b m = 0 := by
      intro m hm
      have h := hF.tp 2 (by omega) 0 ![n, m] (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all)
      rw [toeplitzMinor, Matrix.det_fin_two] at h
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add,
        Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, sub_zero] at h
      rw [← hbdef] at h
      rw [zext_natCast, zext_natCast,
        show ((n : ℕ) : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) by push_cast [hn1]; ring, zext_natCast,
        show ((m : ℕ) : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) by push_cast [show 1 ≤ m by omega]; ring,
        zext_natCast, hbn, zero_mul, zero_sub] at h
      have hbm := recipCoeff_nonneg hF m
      nlinarith [mul_nonneg hbm hprev.le]
    -- then the series converges everywhere, contradicting the boundary zero
    apply hdiv (D + 1) (by linarith)
    refine summable_of_ne_finset_zero (s := Finset.range (n + 1)) fun m hm => ?_
    rw [Finset.mem_range, not_lt] at hm
    rw [hlater m (by omega), zero_mul]
  have hratio := tendsto_ratio_of_logConcave hbpos hlc hD hconv hdiv
  have htp := ConsecutiveRowTPUpTo.deflate hF.tp hbpos hratio
  refine ⟨hGdiff, by rw [hG0]; exact hF.ne_zero, fun n => ?_, ?_⟩
  · have h := hcoeff n
    have hk : (0 : ℂ) ≤ ((n ! : ℂ)) := by exact_mod_cast (Nat.cast_nonneg _ : (0 : ℝ) ≤ n !)
    have hD' : iteratedDeriv n (recipNeg G) 0 = ((n ! : ℂ)) * ((deflateSeq b (1 / D) n : ℝ) : ℂ) := by
      rw [← h]
      have : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      field_simp
    rw [hD']
    have hnn : 0 ≤ deflateSeq b (1 / D) n := by
      have := htp 1 (by omega) 0 ![n] (fun i j hij => by fin_cases i; fin_cases j; simp at hij)
      rw [toeplitzMinor, Matrix.det_unique] at this
      simpa [zext_natCast] using this
    exact mul_nonneg hk (Complex.zero_le_real.mpr hnn)
  · have heq : recipCoeff G = deflateSeq b (1 / D) := by
      funext n
      unfold recipCoeff
      rw [hcoeff n, Complex.ofReal_re]
    rw [heq]
    exact htp

theorem ReciprocalTP.apply_neg_eq_zero {F : ℂ → ℂ} (hF : ReciprocalTP F) {D : ℝ} (hD : 0 < D)
    (hfree : ∀ z : ℂ, ‖z‖ < D → F z ≠ 0) {w : ℂ} (hw : ‖w‖ = D) (hw0 : F w = 0) :
    F (-(D : ℂ)) = 0 :=
  (hF.upTo 0).apply_neg_eq_zero hD hfree hw hw0

/-- **One deflation step** (all orders). -/
theorem ReciprocalTP.deflate {F : ℂ → ℂ} (hF : ReciprocalTP F) {D : ℝ} (hD : 0 < D)
    (hfree : ∀ z : ℂ, ‖z‖ < D → F z ≠ 0) {w : ℂ} (hw : ‖w‖ = D) (hw0 : F w = 0) :
    ReciprocalTP (fun y => (D : ℂ) * dslope F (-(D : ℂ)) y) := by
  have h := fun k => ReciprocalTPUpTo.deflate (hF.upTo (k + 2)) hD hfree hw hw0
  exact ⟨(h 0).differentiable, (h 0).ne_zero, (h 0).nonneg,
    consecutiveRowTP_of_forall_upTo fun k m hm => (h k).tp m (by omega)⟩

end

end GaloisForLFunctions.HTGeometry
