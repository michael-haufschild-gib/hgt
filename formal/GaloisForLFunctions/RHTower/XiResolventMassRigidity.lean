import GaloisForLFunctions.RHTower.XiSquaredCompleteMonotonicityFarRay

/-!
# Quartic shift rigidity of the deviation mass, and RH as an escape law at infinity

The deviation mass `M X = sum_q (Im u_q)^(2 : ℕ)`, `u_q = (alpha_q^(2 : ℕ) + X)^(-1)`, vanishes at one shift
iff RH.  This file proves that `M` obeys a **self-improving differential law**: termwise
differentiation in the shift gives

`M' X = -4 * sum_q Re (u_q) * (Im u_q)^(2 : ℕ)`,

and the critical strip and height gap force `Re u_q ≤ 1/(X+1)`, so `-4 M X / (X+1) ≤ M' X ≤ 0`.
Integrated, the renormalized mass `(X+1)^(4 : ℕ) * M X` is **monotone nondecreasing** on the positive
shift ray.  Consequences:

* **quartic floor**: `M X ≥ (X₀+1)^(4 : ℕ) M X₀ / (X+1)^(4 : ℕ)` for every `X ≥ X₀ > 0` — an RH defect at one
  shift persists at all larger shifts with at most quartic loss, and the exponent is exactly
  critical: one off-critical zero quartet contributes `~ c/X^(4 : ℕ)`;
* **dichotomy**: either `M` vanishes identically (RH) or `M` is everywhere strictly positive with
  the explicit quartic floor, pinched against the quadratic ceiling
  `M X ≤ 2H/(X+1)^(2 : ℕ)` into the corridor `c/(X+1)^(4 : ℕ) ≤ M X ≤ 2H/(X+1)^(2 : ℕ)`;
* **escape law**: `RH ↔ (X+1)^(4 : ℕ) M X → 0 as X → ∞`, and one escape sequence suffices:
  RH follows from `(X_n+1)^(4 : ℕ) M X_n → 0` along any sequence `X_n → ∞`.

So the criterion moves from a value (`M X₀ = 0`) to a tail: RH holds exactly when the deviation
mass decays faster than its own rigidity rate, and the entire content of RH is compressed into
the exponent gap between the unconditional ceiling `X^(-2)` and the rigidity floor `X^(-4)`.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-! ## §1 The damped mass and the strip bound on the resolvent real part -/

/-- The damped deviation mass, the dissipation density of the deviation mass. -/
def xiResolventDampedMass (X : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, (xiResolventPoint X q).re * (xiResolventPoint X q).im ^ 2

theorem summable_damped_xiResolventPoint {X : ℝ} (hX : 0 ≤ X) :
    Summable (fun q : XiZeroCopy =>
      (xiResolventPoint X q).re * (xiResolventPoint X q).im ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun q => mul_nonneg (xiResolventPoint_re_pos hX q).le (sq_nonneg _))
    (fun q => ?_) (summable_im_sq_xiResolventPoint hX)
  have h1 : (xiResolventPoint X q).re ≤ 1 :=
    le_trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
      (norm_xiResolventPoint_le_one hX q)
  nlinarith [sq_nonneg (xiResolventPoint X q).im, (xiResolventPoint_re_pos hX q).le]

theorem xiResolventDampedMass_nonneg {X : ℝ} (hX : 0 ≤ X) :
    0 ≤ xiResolventDampedMass X :=
  tsum_nonneg fun q => mul_nonneg (xiResolventPoint_re_pos hX q).le (sq_nonneg _)

/-- The critical strip and the height gap force `Re u ≤ 1/(X+1)`. -/
theorem xiResolventPoint_re_le {X : ℝ} (hX : 0 ≤ X) (q : XiZeroCopy) :
    (xiResolventPoint X q).re ≤ 1 / (X + 1) := by
  have hγ : 2 < (xiSpectralPoint q).re ^ 2 := by
    have h := xiZeroCopy_two_lt_im_sq q
    rwa [← xiSpectralPoint_re_eq] at h
  have hb : |(xiSpectralPoint q).im| < 1 / 2 := abs_xiSpectralPoint_im_lt_half q
  have hb2 : (xiSpectralPoint q).im ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_abs (xiSpectralPoint q).im, abs_nonneg (xiSpectralPoint q).im]
  have hre : (xiSpectralPoint q ^ 2 + (X : ℂ)).re =
      (xiSpectralPoint q).re ^ 2 - (xiSpectralPoint q).im ^ 2 + X := by
    rw [Complex.add_re, Complex.ofReal_re, sq, Complex.mul_re]
    ring
  have h1 : X + 1 ≤ (xiSpectralPoint q ^ 2 + (X : ℂ)).re := by
    rw [hre]; linarith
  have hwpos : 0 < (xiSpectralPoint q ^ 2 + (X : ℂ)).re := by linarith
  have h2 : ((xiSpectralPoint q ^ 2 + (X : ℂ)).re) ^ 2 ≤
      Complex.normSq (xiSpectralPoint q ^ 2 + (X : ℂ)) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (xiSpectralPoint q ^ 2 + (X : ℂ)).im]
  rw [xiResolventPoint, Complex.inv_re]
  calc (xiSpectralPoint q ^ 2 + (X : ℂ)).re / Complex.normSq (xiSpectralPoint q ^ 2 + (X : ℂ))
      ≤ (xiSpectralPoint q ^ 2 + (X : ℂ)).re / ((xiSpectralPoint q ^ 2 + (X : ℂ)).re) ^ 2 :=
        div_le_div_of_nonneg_left hwpos.le (pow_pos hwpos 2) h2
    _ = 1 / (xiSpectralPoint q ^ 2 + (X : ℂ)).re := by
        rw [pow_two ((xiSpectralPoint q ^ 2 + (X : ℂ)).re), div_mul_eq_div_div,
          div_self hwpos.ne']
    _ ≤ 1 / (X + 1) := one_div_le_one_div_of_le (by linarith) h1

/-- **The dissipation is dominated by the mass over the shift**: `(X+1) D X ≤ M X`. -/
theorem xiResolventDampedMass_mul_le {X : ℝ} (hX : 0 ≤ X) :
    (X + 1) * xiResolventDampedMass X ≤ xiResolventImSqMass X := by
  rw [xiResolventDampedMass, ← tsum_mul_left, xiResolventImSqMass]
  refine Summable.tsum_le_tsum (fun q => ?_)
    ((summable_damped_xiResolventPoint hX).mul_left _)
    (summable_im_sq_xiResolventPoint hX)
  have hX1 : (0 : ℝ) < X + 1 := by linarith
  have h1 := xiResolventPoint_re_le hX q
  have h2 : (X + 1) * (xiResolventPoint X q).re ≤ 1 := by
    have h3 := mul_le_mul_of_nonneg_left h1 hX1.le
    rwa [mul_one_div, div_self hX1.ne'] at h3
  nlinarith [sq_nonneg (xiResolventPoint X q).im, (xiResolventPoint_re_pos hX q).le]

/-! ## §2 The differential law of the deviation mass -/

/-- Shift derivative of one deviation density: `d/dX (Im u)^(2 : ℕ) = -4 Re u (Im u)^(2 : ℕ)`. -/
theorem hasDerivAt_im_sq_xiResolventPoint {X : ℝ} (hX : 0 < X) (q : XiZeroCopy) :
    HasDerivAt (fun v : ℝ => (xiResolventPoint v q).im ^ 2)
      (-(4 * (xiResolventPoint X q).re * (xiResolventPoint X q).im ^ 2)) X := by
  have hne : xiSpectralPoint q ^ 2 + (X : ℂ) ≠ 0 := xiSpectralSq_add_ofReal_ne_zero hX.le q
  have hbase : HasDerivAt (fun v : ℝ => xiSpectralPoint q ^ 2 + (v : ℂ)) 1 X := by
    have h0 : HasDerivAt (fun v : ℝ => ((v : ℝ) : ℂ)) 1 X := (hasDerivAt_id X).ofReal_comp
    simpa using h0.const_add (xiSpectralPoint q ^ 2)
  have hinv := hbase.inv hne
  have huval : (-1 : ℂ) / (xiSpectralPoint q ^ 2 + (X : ℂ)) ^ 2 =
      -(xiResolventPoint X q ^ 2) := by
    rw [xiResolventPoint, inv_pow, neg_div, one_div]
  have hu : HasDerivAt (fun v : ℝ => xiResolventPoint v q) (-(xiResolventPoint X q ^ 2)) X := by
    rw [← huval]
    exact hinv
  have him : HasDerivAt (fun v : ℝ => (xiResolventPoint v q).im)
      ((-(xiResolventPoint X q ^ 2)).im) X := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt X hu
    have hval2 : Complex.imCLM (-(xiResolventPoint X q ^ 2)) =
        (-(xiResolventPoint X q ^ 2)).im := rfl
    rw [hval2] at h
    exact h
  have hsq := him.pow 2
  have hval : ((2 : ℕ) : ℝ) * (xiResolventPoint X q).im ^ (2 - 1) *
      ((-(xiResolventPoint X q ^ 2)).im) =
        -(4 * (xiResolventPoint X q).re * (xiResolventPoint X q).im ^ 2) := by
    simp only [Complex.neg_im, sq, Complex.mul_im, Nat.cast_ofNat]
    ring
  rw [hval] at hsq
  exact hsq

/-- **The differential law of the deviation mass**: `M' X = -4 D X`. -/
theorem hasDerivAt_xiResolventImSqMass {X : ℝ} (hX : 0 < X) :
    HasDerivAt xiResolventImSqMass (-(4 * xiResolventDampedMass X)) X := by
  have hu : Summable (fun q : XiZeroCopy => 8 * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left 8
  have hderiv : ∀ q : XiZeroCopy, ∀ v ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => (xiResolventPoint t q).im ^ 2)
        (-(4 * (xiResolventPoint v q).re * (xiResolventPoint v q).im ^ 2)) v :=
    fun q v hv => hasDerivAt_im_sq_xiResolventPoint hv q
  have hbound : ∀ q : XiZeroCopy, ∀ v ∈ Set.Ioi (0 : ℝ),
      ‖-(4 * (xiResolventPoint v q).re * (xiResolventPoint v q).im ^ 2)‖ ≤
        8 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    intro q v hv
    have hv0 : (0 : ℝ) ≤ v := (Set.mem_Ioi.mp hv).le
    have hn := norm_xiResolventPoint_le hv0 q
    have hgap : (2 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, xiSpectralPoint_re_eq]
      have h := xiZeroCopy_two_lt_im_sq q
      nlinarith [sq_nonneg (xiSpectralPoint q).im, sq_nonneg ((q.1 : ℂ).im)]
    have hApos : (0 : ℝ) < ‖xiSpectralPoint q‖ ^ 2 := by linarith
    have hre : |(xiResolventPoint v q).re| ≤ ‖xiResolventPoint v q‖ :=
      Complex.abs_re_le_norm _
    have him : |(xiResolventPoint v q).im| ≤ ‖xiResolventPoint v q‖ :=
      Complex.abs_im_le_norm _
    have hN : (0 : ℝ) ≤ ‖xiResolventPoint v q‖ := norm_nonneg _
    have step1 : ‖-(4 * (xiResolventPoint v q).re * (xiResolventPoint v q).im ^ 2)‖ =
        4 * |(xiResolventPoint v q).re| * (xiResolventPoint v q).im ^ 2 := by
      rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul]
      rw [abs_of_nonneg (sq_nonneg (xiResolventPoint v q).im)]
      norm_num
    have step2 : 4 * |(xiResolventPoint v q).re| * (xiResolventPoint v q).im ^ 2 ≤
        4 * ‖xiResolventPoint v q‖ ^ 3 := by
      have h2 : (xiResolventPoint v q).im ^ 2 ≤ ‖xiResolventPoint v q‖ ^ 2 := by
        rw [← sq_abs (xiResolventPoint v q).im]
        exact pow_le_pow_left₀ (abs_nonneg _) him 2
      nlinarith [abs_nonneg (xiResolventPoint v q).re, sq_nonneg (xiResolventPoint v q).im]
    have step3 : 4 * ‖xiResolventPoint v q‖ ^ 3 ≤ 4 * (2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) ^ 3 := by
      have := pow_le_pow_left₀ hN hn 3
      linarith
    have step4 : 4 * (2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) ^ 3 ≤
        8 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      have hc1 : 4 * (2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) ^ 3 =
          32 / (‖xiSpectralPoint q‖ ^ 2) ^ 3 := by
        field_simp
        ring
      have hc2 : 8 * (1 / ‖xiSpectralPoint q‖ ^ 2) = 8 / ‖xiSpectralPoint q‖ ^ 2 :=
        mul_one_div 8 _
      rw [hc1, hc2, div_le_div_iff₀ (by positivity) hApos]
      have hA2 : (4 : ℝ) < (‖xiSpectralPoint q‖ ^ 2) ^ 2 := by nlinarith
      nlinarith [mul_pos hApos (by linarith : (0 : ℝ) < (‖xiSpectralPoint q‖ ^ 2) ^ 2 - 4)]
    calc ‖-(4 * (xiResolventPoint v q).re * (xiResolventPoint v q).im ^ 2)‖
        = 4 * |(xiResolventPoint v q).re| * (xiResolventPoint v q).im ^ 2 := step1
      _ ≤ 4 * ‖xiResolventPoint v q‖ ^ 3 := step2
      _ ≤ 4 * (2 * (1 / ‖xiSpectralPoint q‖ ^ 2)) ^ 3 := step3
      _ ≤ 8 * (1 / ‖xiSpectralPoint q‖ ^ 2) := step4
  have hsum0 : Summable (fun q : XiZeroCopy => (xiResolventPoint X q).im ^ 2) :=
    summable_im_sq_xiResolventPoint hX.le
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hderiv hbound
    (Set.mem_Ioi.mpr hX) hsum0 (Set.mem_Ioi.mpr hX)
  have hval : (∑' q : XiZeroCopy,
      -(4 * (xiResolventPoint X q).re * (xiResolventPoint X q).im ^ 2))
        = -(4 * xiResolventDampedMass X) := by
    rw [tsum_neg]
    congr 1
    rw [xiResolventDampedMass, ← tsum_mul_left]
    exact tsum_congr fun q => by ring
  rw [hval] at hmain
  exact hmain

/-! ## §3 Quartic shift rigidity -/

/-- **Quartic shift rigidity**: the renormalized deviation mass `(X+1)^(4 : ℕ) M X` is monotone
nondecreasing on the positive shift ray. -/
theorem monotoneOn_quartic_mul_xiResolventImSqMass :
    MonotoneOn (fun X : ℝ => (X + 1) ^ 4 * xiResolventImSqMass X) (Set.Ioi 0) := by
  have hG : ∀ X ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun X : ℝ => (X + 1) ^ 4 * xiResolventImSqMass X)
        (4 * (X + 1) ^ 3 * xiResolventImSqMass X +
          (X + 1) ^ 4 * -(4 * xiResolventDampedMass X)) X := by
    intro X hX
    have hp : HasDerivAt (fun X : ℝ => (X + 1) ^ 4) (4 * (X + 1) ^ 3) X := by
      have h := ((hasDerivAt_id X).add_const 1).pow 4
      simp only [id_eq] at h
      have hv : ((4 : ℕ) : ℝ) * (X + 1) ^ (4 - 1) * 1 = 4 * (X + 1) ^ 3 := by
        norm_num
      rw [hv] at h
      exact h
    exact hp.mul (hasDerivAt_xiResolventImSqMass (Set.mem_Ioi.mp hX))
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · exact fun X hX => (hG X hX).differentiableAt.continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun X hX => (hG X hX).differentiableAt.differentiableWithinAt
  · intro X hX
    rw [interior_Ioi] at hX
    rw [(hG X hX).deriv]
    have hX0 : (0 : ℝ) < X := Set.mem_Ioi.mp hX
    have h1 := xiResolventDampedMass_mul_le hX0.le
    have hpow : (X + 1) ^ 4 = (X + 1) ^ 3 * (X + 1) := by ring
    nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ X + 1) 3)
      (sub_nonneg.mpr h1)]

/-- The deviation mass itself is nonincreasing in the shift. -/
theorem antitoneOn_xiResolventImSqMass :
    AntitoneOn xiResolventImSqMass (Set.Ioi 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
  · exact fun X hX => (hasDerivAt_xiResolventImSqMass
      (Set.mem_Ioi.mp hX)).differentiableAt.continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    exact fun X hX => (hasDerivAt_xiResolventImSqMass
      (Set.mem_Ioi.mp hX)).differentiableAt.differentiableWithinAt
  · intro X hX
    rw [interior_Ioi] at hX
    have hX0 : (0 : ℝ) < X := Set.mem_Ioi.mp hX
    rw [(hasDerivAt_xiResolventImSqMass hX0).deriv]
    have := xiResolventDampedMass_nonneg hX0.le
    linarith

/-- **The quartic floor**: an RH defect at one shift persists at every larger shift with at most
quartic loss. -/
theorem xiResolventImSqMass_quartic_floor {X₀ X : ℝ} (h0 : 0 < X₀) (hX : X₀ ≤ X) :
    ((X₀ + 1) ^ 4 * xiResolventImSqMass X₀) / (X + 1) ^ 4 ≤ xiResolventImSqMass X := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le h0 hX
  have hpos : (0 : ℝ) < (X + 1) ^ 4 := by positivity
  rw [div_le_iff₀ hpos]
  calc (X₀ + 1) ^ 4 * xiResolventImSqMass X₀
      ≤ (X + 1) ^ 4 * xiResolventImSqMass X :=
        monotoneOn_quartic_mul_xiResolventImSqMass (Set.mem_Ioi.mpr h0)
          (Set.mem_Ioi.mpr hXpos) hX
    _ = xiResolventImSqMass X * (X + 1) ^ 4 := mul_comm _ _

/-- **The dichotomy**: a strictly positive deviation mass anywhere stays strictly positive at
every larger shift. -/
theorem xiResolventImSqMass_pos_of_pos {X₀ X : ℝ} (h0 : 0 < X₀)
    (hm : 0 < xiResolventImSqMass X₀) (hX : X₀ ≤ X) :
    0 < xiResolventImSqMass X := by
  refine lt_of_lt_of_le ?_ (xiResolventImSqMass_quartic_floor h0 hX)
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le h0 hX
  exact div_pos (mul_pos (by positivity) hm) (by positivity)

/-- **The corridor**: any RH failure is pinched between the quartic rigidity floor and the
quadratic Hadamard ceiling. -/
theorem xiResolventImSqMass_corridor {X₀ X : ℝ} (h0 : 0 < X₀) (hX : X₀ ≤ X) :
    ((X₀ + 1) ^ 4 * xiResolventImSqMass X₀) / (X + 1) ^ 4 ≤ xiResolventImSqMass X ∧
      xiResolventImSqMass X ≤
        2 / (X + 1) ^ 2 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 :=
  ⟨xiResolventImSqMass_quartic_floor h0 hX,
    xiResolventImSqMass_le (le_of_lt (lt_of_lt_of_le h0 hX))⟩

/-! ## §4 RH as an escape law at infinity -/

/-- **RH is an escape law**: the Riemann Hypothesis holds iff the quartically renormalized
deviation mass tends to zero at infinite shift. -/
theorem riemannHypothesis_iff_tendsto_quartic_mass_zero :
    RiemannHypothesis ↔
      Tendsto (fun X : ℝ => (X + 1) ^ 4 * xiResolventImSqMass X) atTop (nhds 0) := by
  constructor
  · intro hRH
    have hev : ∀ᶠ X : ℝ in atTop, (X + 1) ^ 4 * xiResolventImSqMass X = 0 := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
      rw [(riemannHypothesis_iff_xiResolventImSqMass_eq_zero hX).mp hRH, mul_zero]
    exact Tendsto.congr' (by filter_upwards [hev] with X h using h.symm) tendsto_const_nhds
  · intro htend
    have hfloor : ∀ᶠ X : ℝ in atTop, ((1 : ℝ) + 1) ^ 4 * xiResolventImSqMass 1 ≤
        (X + 1) ^ 4 * xiResolventImSqMass X := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
      exact monotoneOn_quartic_mul_xiResolventImSqMass (Set.mem_Ioi.mpr one_pos)
        (Set.mem_Ioi.mpr (by linarith)) hX
    have h1 : ((1 : ℝ) + 1) ^ 4 * xiResolventImSqMass 1 ≤ 0 := ge_of_tendsto htend hfloor
    have h2 : 0 ≤ xiResolventImSqMass 1 := tsum_nonneg fun q => sq_nonneg _
    have h3 : xiResolventImSqMass 1 = 0 := by nlinarith
    exact (riemannHypothesis_iff_xiResolventImSqMass_eq_zero (by norm_num)).mpr h3

/-- **One escape sequence suffices**: RH follows from quartically renormalized mass decay along
any single sequence of shifts tending to infinity. -/
theorem riemannHypothesis_of_escape_sequence (Xn : ℕ → ℝ)
    (hXn : Tendsto Xn atTop atTop)
    (hmass : Tendsto (fun n => (Xn n + 1) ^ 4 * xiResolventImSqMass (Xn n)) atTop (nhds 0)) :
    RiemannHypothesis := by
  have hfloor : ∀ᶠ n : ℕ in atTop, ((1 : ℝ) + 1) ^ 4 * xiResolventImSqMass 1 ≤
      (Xn n + 1) ^ 4 * xiResolventImSqMass (Xn n) := by
    filter_upwards [hXn.eventually_ge_atTop 1] with n hn
    exact monotoneOn_quartic_mul_xiResolventImSqMass (Set.mem_Ioi.mpr one_pos)
      (Set.mem_Ioi.mpr (by linarith)) hn
  have h1 : ((1 : ℝ) + 1) ^ 4 * xiResolventImSqMass 1 ≤ 0 := ge_of_tendsto hmass hfloor
  have h2 : 0 ≤ xiResolventImSqMass 1 := tsum_nonneg fun q => sq_nonneg _
  have h3 : xiResolventImSqMass 1 = 0 := by nlinarith
  exact (riemannHypothesis_iff_xiResolventImSqMass_eq_zero (by norm_num)).mpr h3

/-- RH is equivalent to the existence of one escaping shift sequence along which the quartically
renormalized deviation mass dies. -/
theorem riemannHypothesis_iff_exists_escape_sequence :
    RiemannHypothesis ↔ ∃ Xn : ℕ → ℝ, Tendsto Xn atTop atTop ∧
      Tendsto (fun n => (Xn n + 1) ^ 4 * xiResolventImSqMass (Xn n)) atTop (nhds 0) := by
  constructor
  · intro hRH
    refine ⟨fun n => (n : ℝ), tendsto_natCast_atTop_atTop, ?_⟩
    have hev : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ 4 * xiResolventImSqMass (n : ℝ) = 0 := by
      filter_upwards with n
      rw [(riemannHypothesis_iff_xiResolventImSqMass_eq_zero (Nat.cast_nonneg n)).mp hRH,
        mul_zero]
    exact Tendsto.congr' (by filter_upwards [hev] with n h using h.symm) tendsto_const_nhds
  · rintro ⟨Xn, h1, h2⟩
    exact riemannHypothesis_of_escape_sequence Xn h1 h2

end

end RHTower
