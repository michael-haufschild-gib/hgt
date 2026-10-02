import GaloisForLFunctions.RHTower.LogPhasePhysicalWindow
import GaloisForLFunctions.RHTower.ChiDualSignedIntegrationByParts

/-!
# The complete nonstationary physical-window complement

The logarithmic phase denominator is removable on the common zero neighborhood
of the saddle. Smooth division and its vertical derivative preserve that region
and the full exterior support. Two exact integrations by parts retain all endpoints.
The final theorem constructs every input from the actual height and saddle cutoffs.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff
namespace GaloisForLFunctions.RHTower

private def windowPartial (A : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  fderiv ℝ A q (0, 1)

private theorem contDiff_windowPartial {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (windowPartial A) :=
  (contDiff_infty_iff_fderiv.mp hA).2.clm_apply contDiff_const

private theorem hasDerivAt_windowSlice {A : ℝ × ℝ → ℂ}
    (hA : ContDiff ℝ ∞ A) (p x : ℝ) :
    HasDerivAt (fun y => A (p, y)) (windowPartial A (p, x)) x := by
  exact ((hA.differentiable (by simp) (p, x)).hasFDerivAt).comp_hasDerivAt x
    ((hasDerivAt_const x p).prodMk (hasDerivAt_id x))

private def windowZeroSet (a b eps : ℝ) : Set ℝ :=
  {x | x < a ∨ b < x ∨ |x| < eps}

private theorem isOpen_windowZeroSet (a b eps : ℝ) : IsOpen (windowZeroSet a b eps) :=
  (isOpen_lt continuous_id continuous_const).union
    ((isOpen_lt continuous_const continuous_id).union (isOpen_lt continuous_abs continuous_const))

private theorem windowPartial_zero {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ ∞ A)
    {a b eps : ℝ} (hz : ∀ p x, x ∈ windowZeroSet a b eps → A (p, x) = 0) :
    ∀ p x, x ∈ windowZeroSet a b eps → windowPartial A (p, x) = 0 := by
  intro p x hx
  have he : (fun y : ℝ => A (p, y)) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isOpen_windowZeroSet a b eps).mem_nhds hx] with y hy
    exact hz p y hy
  exact (hasDerivAt_windowSlice hA p x).deriv.symm.trans
    (he.deriv_eq.trans (deriv_const x (0 : ℂ)))

private def logSlopeDivision (A : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  A q / ((-Real.log (1 + q.2) : ℝ) : ℂ)

private theorem logSlopeDivision_zero {A : ℝ × ℝ → ℂ} {a b eps : ℝ}
    (hz : ∀ p x, x ∈ windowZeroSet a b eps → A (p, x) = 0) :
    ∀ p x, x ∈ windowZeroSet a b eps → logSlopeDivision A (p, x) = 0 := by
  intro p x hx
  simp only [logSlopeDivision, hz p x hx, zero_div]

private theorem contDiff_logSlopeDivision {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ ∞ A)
    {a b eps : ℝ} (ha : -1 < a) (heps : 0 < eps)
    (hz : ∀ p x, x ∈ windowZeroSet a b eps → A (p, x) = 0) :
    ContDiff ℝ ∞ (logSlopeDivision A) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q.2 ∈ windowZeroSet a b eps
  · have hev : ∀ᶠ z : ℝ × ℝ in 𝓝 q, z.2 ∈ windowZeroSet a b eps :=
      (continuous_snd.tendsto q).eventually ((isOpen_windowZeroSet a b eps).mem_nhds hq)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hev] with z hz'
    exact logSlopeDivision_zero hz z.1 z.2 hz'
  · have hdom : -1 < q.2 := by
      by_contra hh
      exact hq (Or.inl (lt_of_le_of_lt (le_of_not_gt hh) ha))
    have hq0 : q.2 ≠ 0 := by
      intro hh
      apply hq
      exact Or.inr (Or.inr (by simpa [hh] using heps))
    have hden : ((-Real.log (1 + q.2) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr
        (Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by intro hh; apply hq0; linarith)))
    have hd : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => -Real.log (1 + z.2)) q :=
      ((contDiffAt_const.add contDiffAt_snd).log (by linarith : 1 + q.2 ≠ 0)).neg
    have hi : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (((-Real.log (1 + z.2))⁻¹ : ℝ) : ℂ)) q :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp q
        (hd.inv (Complex.ofReal_ne_zero.mp hden))
    simpa only [logSlopeDivision, div_eq_mul_inv, Complex.ofReal_inv] using! hA.contDiffAt.mul hi

private theorem logSlopeDivision_identity {A : ℝ × ℝ → ℂ} {a b eps : ℝ}
    (heps : 0 < eps) (hz : ∀ p x, x ∈ windowZeroSet a b eps → A (p, x) = 0)
    (p x : ℝ) (hx : -1 < x) :
    logSlopeDivision A (p, x) * ((-Real.log (1 + x) : ℝ) : ℂ) = A (p, x) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hh := hz p 0 (Or.inr (Or.inr (by simpa using heps)))
    simp [logSlopeDivision, hh]
  · exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr
      (Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by intro hh; apply hx0; linarith))))

/-- The entire complementary logarithmic integral gains two inverse frequencies.
Joint smoothness and a common zero neighborhood supply both divided amplitudes,
including all endpoint terms, uniformly over compact parameter sets. -/
theorem exists_uniform_logPhase_nonstationary_remainder
    {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ ∞ A) {K : Set ℝ} (hK : IsCompact K)
    {a b eps : ℝ} (ha : -1 < a) (hab : a ≤ b) (heps : 0 < eps)
    (hz : ∀ p x, x < a ∨ b < x ∨ |x| < eps → A (p, x) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ lam : ℝ, 0 < lam →
      ‖∫ x : ℝ, A (p, x) * Complex.exp (I * ((lam * logPhaseProfile x : ℝ) : ℂ))‖ ≤
        C / lam ^ 2 := by
  let Q := logSlopeDivision A
  let Q' := windowPartial Q
  let D := logSlopeDivision Q'
  let D' := windowPartial D
  have hQ : ContDiff ℝ ∞ Q := contDiff_logSlopeDivision hA ha heps hz
  have hQ' : ContDiff ℝ ∞ Q' := contDiff_windowPartial hQ
  have hQz : ∀ p x, x ∈ windowZeroSet a b eps → Q (p, x) = 0 := logSlopeDivision_zero hz
  have hQ'z : ∀ p x, x ∈ windowZeroSet a b eps → Q' (p, x) = 0 := windowPartial_zero hQ hQz
  have hD : ContDiff ℝ ∞ D := contDiff_logSlopeDivision hQ' ha heps hQ'z
  have hD' : ContDiff ℝ ∞ D' := contDiff_windowPartial hD
  have hDz : ∀ p x, x ∈ windowZeroSet a b eps → D (p, x) = 0 := logSlopeDivision_zero hQ'z
  let L := (a - 1) / 2
  let U := b + 1
  have hLa : L < a := by dsimp [L]; linarith
  have hLb : -1 < L := by dsimp [L]; linarith
  have hbU : b < U := by dsimp [U]; linarith
  have hLU : L < U := by linarith
  have hwidth : 0 < U - L := sub_pos.mpr hLU
  obtain ⟨M, hM⟩ := (hK.prod (isCompact_Icc (a := L) (b := U))).exists_bound_of_continuousOn
    hD'.continuous.continuousOn
  let M₁ := |M| + 1
  have hM₁ : 0 < M₁ := by dsimp [M₁]; positivity
  refine ⟨1 + M₁ * (U - L), by positivity, ?_⟩
  intro p hp lam hlam
  let z : ℂ := I * (lam : ℂ)
  have hz0 : z ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hlam.ne')
  have hreal (x : ℝ) : I * ((lam * (-Real.log (1 + x)) : ℝ) : ℂ) =
      z * ((-Real.log (1 + x) : ℝ) : ℂ) := by dsimp [z]; push_cast; ring
  have hpoint (x : ℝ) (hx : x ∈ uIcc L U) : -1 < x := by
    rw [uIcc_of_le hLU.le] at hx
    exact hLb.trans_le hx.1
  have hfirst (x : ℝ) (hx : x ∈ uIcc L U) :
      (Q (p, x) / z) * (I * ((lam * (-Real.log (1 + x)) : ℝ) : ℂ)) = A (p, x) := by
    rw [hreal]
    calc
      _ = Q (p, x) * ((-Real.log (1 + x) : ℝ) : ℂ) := by field_simp [hz0]
      _ = _ := logSlopeDivision_identity heps hz p x (hpoint x hx)
  have hsecond (x : ℝ) (hx : x ∈ uIcc L U) :
      (D (p, x) / z ^ 2) * (I * ((lam * (-Real.log (1 + x)) : ℝ) : ℂ)) = Q' (p, x) / z := by
    rw [hreal]
    calc
      _ = (D (p, x) * ((-Real.log (1 + x) : ℝ) : ℂ)) / z := by field_simp [hz0]
      _ = _ := by rw [logSlopeDivision_identity heps hQ'z p x (hpoint x hx)]
  have hsource := _root_.RHTower.integral_cexp_eq_of_two_antiderivatives
    (a := L) (b := U) (φ := fun x => lam * logPhaseProfile x)
    (φ' := fun x => lam * (-Real.log (1 + x)))
    (A := fun x => A (p, x)) (B := fun x => Q (p, x) / z)
    (B' := fun x => Q' (p, x) / z) (C := fun x => D (p, x) / z ^ 2)
    (C' := fun x => D' (p, x) / z ^ 2)
    (fun x hx => (hasDerivAt_logPhaseProfile (hpoint x hx)).const_mul lam)
    (fun x _ => (hasDerivAt_windowSlice hQ p x).div_const z)
    (fun x _ => (hasDerivAt_windowSlice hD p x).div_const (z ^ 2))
    (hA.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    ((hQ'.continuous.comp (continuous_const.prodMk continuous_id)).div_const z).continuousOn
    ((hD'.continuous.comp (continuous_const.prodMk continuous_id)).div_const (z ^ 2)).continuousOn
    hfirst hsecond
  have hLz : L ∈ windowZeroSet a b eps := Or.inl hLa
  have hUz : U ∈ windowZeroSet a b eps := Or.inr (Or.inl hbU)
  change _ = (Q (p, U) / z - D (p, U) / z ^ 2) * _ -
    (Q (p, L) / z - D (p, L) / z ^ 2) * _ + _ at hsource
  simp only [hQz p U hUz, hQz p L hLz, hDz p U hUz, hDz p L hLz,
    zero_div, sub_self, zero_mul, sub_self, zero_add] at hsource
  have hfull : (∫ x in L..U, A (p, x) *
      Complex.exp (I * ((lam * logPhaseProfile x : ℝ) : ℂ))) =
      ∫ x : ℝ, A (p, x) * Complex.exp (I * ((lam * logPhaseProfile x : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_of_le hLU.le]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxz : x < a ∨ b < x ∨ |x| < eps := by
      by_cases hxa : x < a
      · exact Or.inl hxa
      by_cases hxb : b < x
      · exact Or.inr (Or.inl hxb)
      exfalso
      exact hx ⟨by linarith, by linarith⟩
    rw [hz p x hxz, zero_mul]
  rw [hfull] at hsource
  rw [hsource]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := L) (b := U) (C := M₁ / lam ^ 2)
    (f := fun x => D' (p, x) / z ^ 2 *
      Complex.exp (I * ((lam * logPhaseProfile x : ℝ) : ℂ))) (fun x hx => by
      have hxi : x ∈ Icc L U := by
        rw [uIoc_of_le hLU.le] at hx
        exact ⟨hx.1.le, hx.2⟩
      have hn : ‖Complex.exp (I * ((lam * logPhaseProfile x : ℝ) : ℂ))‖ = 1 := by
        simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero]
      rw [norm_mul, hn, mul_one, norm_div, norm_pow]
      have hzNorm : ‖z‖ = lam := by
        simp only [z, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hlam]
      rw [hzNorm]
      apply div_le_div_of_nonneg_right _ (sq_nonneg lam)
      exact (hM (p, x) ⟨hp, hxi⟩).trans (by dsimp [M₁]; linarith [le_abs_self M]))
  apply hbound.trans
  rw [abs_of_pos (sub_pos.mpr hLU)]
  calc
    M₁ / lam ^ 2 * (U - L) = (M₁ * (U - L)) / lam ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (sq_nonneg lam)

/-- Every source height window has the same spatial support on the full saddle-ratio interval. -/
theorem bagPhysicalHeightWindow_scaled_eq_zero {p v : ℝ}
    (hp : p ∈ Icc (1 / 2 : ℝ) 4) (hv : v ∉ Icc (-(3 / 4 : ℝ)) 3) :
    bagPhysicalHeightWindow (p * (1 + v)) = 0 := by
  apply bagPhysicalHeightWindow.zero_of_le_dist
  change (1 / 2 : ℝ) ≤ dist (p * (1 + v)) (3 / 2 : ℝ)
  rw [Real.dist_eq]
  by_cases hvl : v < -(3 / 4 : ℝ)
  · have hprod : p * (1 + v) ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left (show 1 + v ≤ 1 / 4 by linarith)
        (show 0 ≤ p by linarith [hp.1])
      nlinarith [hp.2]
    linarith [neg_le_abs (p * (1 + v) - 3 / 2)]
  · have hvr : 3 < v := by
      by_contra hh
      exact hv ⟨le_of_not_gt hvl, le_of_not_gt hh⟩
    have hprod : 2 ≤ p * (1 + v) := by
      have hh := mul_le_mul_of_nonneg_right hp.1 (show 0 ≤ 1 + v by linarith)
      nlinarith
    linarith [le_abs_self (p * (1 + v) - 3 / 2)]

/-- The full complement of the source physical window is uniformly nonstationary.
The common zero neighborhood and all smooth quotient inputs are constructed from the cutoffs. -/
theorem exists_logPhaseMorse_source_window_complement (eta : ContDiffBump (0 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (1 / 2 : ℝ) 4, ∀ lam : ℝ, 0 < lam →
      ‖∫ v : ℝ, (1 - (eta (logPhaseMorse v) : ℂ)) *
          (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) *
          Complex.exp (I * ((lam * logPhaseProfile v : ℝ) : ℂ))‖ ≤ C / lam ^ 2 := by
  let theta : ContDiffBump (9 / 8 : ℝ) :=
    ⟨15 / 8, 2, by norm_num, by norm_num⟩
  let A : ℝ × ℝ → ℂ := fun q =>
    (theta q.2 : ℂ) * (1 - (eta (logPhaseMorse q.2) : ℂ)) *
      (bagPhysicalHeightWindow (q.1 * (1 + q.2)) : ℂ)
  have hA : ContDiff ℝ ∞ A := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : -1 < q.2
    · have hw : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => logPhaseMorse z.2) q :=
        (contDiffAt_logPhaseMorse hq).of_le (by simp) |>.comp q contDiffAt_snd
      have he : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (eta (logPhaseMorse z.2) : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q (eta.contDiffAt.comp q hw)
      have ht : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (theta z.2 : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q (theta.contDiffAt.comp q contDiffAt_snd)
      have hW : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ =>
          (bagPhysicalHeightWindow (z.1 * (1 + z.2)) : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q
          (bagPhysicalHeightWindow.contDiffAt.comp q
            (contDiffAt_fst.mul (contDiffAt_const.add contDiffAt_snd)))
      exact (ht.mul (contDiffAt_const.sub he)).mul hW
    · have hn : q.2 ∉ tsupport theta := by
        rw [theta.tsupport_eq]
        intro hm
        have hb : |q.2 - 9 / 8| ≤ 2 := by
          simpa only [Metric.mem_closedBall, Real.dist_eq, theta] using hm
        have hl := (abs_le.mp hb).1
        linarith [le_of_not_gt hq]
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
        (continuous_snd.tendsto q)
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hz] with z hz
      simp only [Function.comp_apply, Pi.zero_apply] at hz
      simp [A, hz]
  have hone : ∀ᶠ v : ℝ in 𝓝 0, eta (logPhaseMorse v) = 1 := by
    have hm : Tendsto logPhaseMorse (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, logPhaseMorse_zero] using
        (contDiffAt_logPhaseMorse (v := 0) (by norm_num)).continuousAt
    exact hm.eventually eta.eventuallyEq_one
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hone
  have hzero (p v : ℝ) (hv : v < -(7 / 8 : ℝ) ∨ 25 / 8 < v ∨ |v| < eps) :
      A (p, v) = 0 := by
    rcases hv with hv | hv | hv
    · have hz : theta v = 0 := theta.zero_of_le_dist (by
        change 2 ≤ dist v (9 / 8 : ℝ)
        rw [Real.dist_eq]
        linarith [neg_le_abs (v - 9 / 8)])
      simp [A, hz]
    · have hz : theta v = 0 := theta.zero_of_le_dist (by
        change 2 ≤ dist v (9 / 8 : ℝ)
        rw [Real.dist_eq]
        linarith [le_abs_self (v - 9 / 8)])
      simp [A, hz]
    · have he : eta (logPhaseMorse v) = 1 :=
        hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hv)
      simp [A, he]
  obtain ⟨C, hC, hbound⟩ := exists_uniform_logPhase_nonstationary_remainder hA
    (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 4))
    (show -1 < -(7 / 8 : ℝ) by norm_num) (show -(7 / 8 : ℝ) ≤ 25 / 8 by norm_num)
    heps hzero
  refine ⟨C, hC, ?_⟩
  intro p hp lam hlam
  have hthetaW (v : ℝ) : (theta v : ℂ) *
      (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) =
      (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) := by
    by_cases hv : v ∈ Icc (-(3 / 4 : ℝ)) 3
    · have he : theta v = 1 := theta.one_of_mem_closedBall (by
        change dist v (9 / 8 : ℝ) ≤ 15 / 8
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith [hv.1, hv.2])
      simp only [he, Complex.ofReal_one, one_mul]
    · have hw := bagPhysicalHeightWindow_scaled_eq_zero hp hv
      simp only [hw, Complex.ofReal_zero, mul_zero]
  have hfun (v : ℝ) : A (p, v) =
      (1 - (eta (logPhaseMorse v) : ℂ)) * (bagPhysicalHeightWindow (p * (1 + v)) : ℂ) := by
    dsimp [A]
    calc
      _ = (1 - (eta (logPhaseMorse v) : ℂ)) *
        ((theta v : ℂ) * (bagPhysicalHeightWindow (p * (1 + v)) : ℂ)) := by ring
      _ = _ := by rw [hthetaW]
  have hb := hbound p hp lam hlam
  simp_rw [hfun] at hb
  exact hb

end GaloisForLFunctions.RHTower
