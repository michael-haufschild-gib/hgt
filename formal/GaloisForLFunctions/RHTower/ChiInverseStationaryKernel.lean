import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import GaloisForLFunctions.RHTower.LogRemainderMorse
import GaloisForLFunctions.RHTower.ChiPhysicalStationaryKernel

/-!
# Complete inverse stationary chi kernel

The original compact frequency kernel reconstructs the actual physical chi
carrier with uniform error C/T. The correct inverse logarithmic phase has its
own analytic Morse coordinate. Its full weighted amplitude, both transitions,
and nonstationary complement remain in the proof.

Exact logarithmic substitution and integrable Fubini give the full bilinear
frequency main with finite-height smearing. The complete error is bounded by
(C/T) times the two physical L2 norms, independently of support or degree.
This supplies no arithmetic cancellation or target-event positivity.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology ContDiff
open RHTower
namespace GaloisForLFunctions.RHTower

/-- The actual compact inverse-stationary amplitude. -/
def chiInverseHeightWindow (x : ℝ) : ℝ := bagPhysicalHeightWindow x / Real.sqrt x

private theorem chiInverseHeightWindow_zero {x : ℝ} (hx : x ≤ 1 ∨ 2 ≤ x) :
    chiInverseHeightWindow x = 0 := by
  have hz : bagPhysicalHeightWindow x = 0 := by
    apply bagPhysicalHeightWindow.zero_of_le_dist
    change (1 / 2 : ℝ) ≤ dist x (3 / 2)
    rw [Real.dist_eq]
    rcases hx with hx | hx
    · linarith [neg_le_abs (x - 3 / 2)]
    · linarith [le_abs_self (x - 3 / 2)]
  simp only [chiInverseHeightWindow, hz, zero_div]

private theorem contDiff_chiInverseHeightWindow : ContDiff ℝ ∞ chiInverseHeightWindow := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · exact bagPhysicalHeightWindow.contDiffAt.div (Real.contDiffAt_sqrt hx.ne')
      (Real.sqrt_pos.mpr hx).ne'
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show x < (1 : ℝ) by linarith)] with y hy
    exact chiInverseHeightWindow_zero (Or.inl hy.le)

private theorem chiInverseHeightWindow_scaled_eq_zero {p v : ℝ}
    (hp : p ∈ Icc (1 / 2 : ℝ) 4) (hv : v ∉ Icc (-(3 / 4 : ℝ)) 3) :
    chiInverseHeightWindow (p * (1 + v)) = 0 := by
  simp only [chiInverseHeightWindow, bagPhysicalHeightWindow_scaled_eq_zero hp hv, zero_div]

private theorem exists_logRemainderMorse_physical_window_family :
    ∃ (r : ℝ) (j : ℝ → ℝ) (eta : ContDiffBump (0 : ℝ)),
      0 < r ∧ eta.rOut < r ∧ j 0 = 0 ∧ deriv j 0 = 1 ∧
      (∀ w ∈ Icc (-r) r, AnalyticAt ℝ j w ∧ 0 < deriv j w ∧ -1 < j w ∧
        logRemainderMorse (j w) = w ∧ logRemainder (j w) = -(w ^ 2) / 2) ∧
      ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → ∀ (K : Set ℝ), IsCompact K →
        ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ lam : ℝ, 0 < lam →
          ‖(∫ v in j (-r)..j r, (eta (logRemainderMorse v) : ℂ) * W (p * (1 + v)) *
              Complex.exp (Complex.I * ((lam * logRemainder v : ℝ) : ℂ))) -
            W p * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
              Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)‖ ≤
                C / (lam * Real.sqrt lam) := by
  obtain ⟨r, j, hr, hj0, hjd, hj⟩ := exists_logRemainderMorse_inverse
  let eta : ContDiffBump (0 : ℝ) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have heta : eta.rOut < r := by dsimp [eta]; linarith
  refine ⟨r, j, eta, hr, heta, hj0, hjd, hj, ?_⟩
  intro W hW K hK
  let B : ℝ × ℝ → ℂ := fun q =>
    (eta q.2 : ℂ) * ((deriv j q.2 : ℝ) : ℂ) * W (q.1 * (1 + j q.2))
  have hB : ContDiff ℝ ∞ B := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q.2 ∈ Icc (-r) r
    · have hjq : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => j z.2) q :=
        (hj q.2 hq).1.contDiffAt.comp q contDiffAt_snd
      have hdq : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => ((deriv j z.2 : ℝ) : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q
          ((hj q.2 hq).1.deriv.contDiffAt.comp q contDiffAt_snd)
      have heq : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (eta z.2 : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q
          (eta.contDiffAt.comp q contDiffAt_snd)
      exact (heq.mul hdq).mul
        (hW.contDiffAt.comp q (contDiffAt_fst.mul (contDiffAt_const.add hjq)))
    · have hn : q.2 ∉ tsupport eta := by
        rw [eta.tsupport_eq]
        intro hm
        have hb : |q.2| ≤ r / 2 := by
          simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, eta] using hm
        have ha := abs_le.mp hb
        exact hq ⟨by linarith, by linarith⟩
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
        (continuous_snd.tendsto q)
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hz] with z hz
      simp only [Function.comp_apply, Pi.zero_apply] at hz
      simp [B, hz]
  have hBs (p : ℝ) (_ : p ∈ K) (x : ℝ) (hx : r ≤ |x|) : B (p, x) = 0 := by
    have hz := eta.zero_of_le_dist
      (show eta.rOut ≤ dist x 0 by simpa only [Real.dist_eq, sub_zero] using heta.le.trans hx)
    simp [B, hz]
  obtain ⟨C, hC, hbound⟩ := exists_uniform_quadratic_fresnel_negative_remainder hB hK hr hBs
  refine ⟨C, hC, ?_⟩
  intro p hp lam hlam
  have hB0 : B (p, 0) = W p := by
    simp only [B, hj0, hjd, eta.one_of_mem_closedBall (Metric.mem_closedBall_self eta.rIn_pos.le),
      Complex.ofReal_one, one_mul, add_zero, mul_one]
  have hu : uIcc (-r) r = Icc (-r) r := uIcc_of_le (by linarith)
  have hcont : ContinuousOn j (uIcc (-r) r) := by
    rw [hu]
    exact fun w hw => (hj w hw).1.continuousAt.continuousWithinAt
  have hder : ∀ w ∈ Ioo (min (-r) r) (max (-r) r), HasDerivAt j (deriv j w) w := by
    intro w hw
    have hm : w ∈ uIcc (-r) r := ⟨hw.1.le, hw.2.le⟩
    exact (hj w (hu ▸ hm)).1.differentiableAt.hasDerivAt
  have hpos : ∀ w ∈ Ioo (min (-r) r) (max (-r) r), 0 ≤ deriv j w := by
    intro w hw
    have hm : w ∈ uIcc (-r) r := ⟨hw.1.le, hw.2.le⟩
    exact (hj w (hu ▸ hm)).2.1.le
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun v => (eta (logRemainderMorse v) : ℂ) * W (p * (1 + v)) *
      Complex.exp (Complex.I * ((lam * logRemainder v : ℝ) : ℂ))) hcont hder hpos
  have he : (∫ v in j (-r)..j r, (eta (logRemainderMorse v) : ℂ) * W (p * (1 + v)) *
      Complex.exp (Complex.I * ((lam * logRemainder v : ℝ) : ℂ))) =
        ∫ w : ℝ, B (p, w) * quadPhase (-lam) w := by
    rw [← hsub]
    have hpoint : (∫ w in (-r)..r, (deriv j w) •
        ((eta (logRemainderMorse (j w)) : ℂ) * W (p * (1 + j w)) *
          Complex.exp (Complex.I * ((lam * logRemainder (j w) : ℝ) : ℂ)))) =
        ∫ w in (-r)..r, B (p, w) * quadPhase (-lam) w := by
      apply intervalIntegral.integral_congr
      intro w hw
      have hm := hj w (hu ▸ hw)
      simp only [hm.2.2.2.1, hm.2.2.2.2, B, quadPhase, Complex.real_smul]
      have hex : Complex.I * ((lam * (-(w ^ 2) / 2) : ℝ) : ℂ) =
          (((-lam * w ^ 2 / 2 : ℝ) : ℂ) * I) := by push_cast; ring
      rw [hex]
      ring
    simp only [Function.comp_apply]
    rw [hpoint, intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    have hb : r ≤ |w| := by
      by_contra hh
      have ha := abs_lt.mp (lt_of_not_ge hh)
      exact hw ⟨ha.1, ha.2.le⟩
    rw [hBs p hp w hb, zero_mul]
  rw [he, ← hB0]
  exact hbound p hp lam hlam


private theorem inverseSlope_ne_zero {x : ℝ} (hx : -1 < x) (hx0 : x ≠ 0) :
    (1 + x)⁻¹ - 1 ≠ 0 := by
  intro he
  have hh := congrArg (fun y : ℝ => y * (1 + x)) (sub_eq_zero.mp he)
  rw [inv_mul_cancel₀ (by linarith : 1 + x ≠ 0), one_mul] at hh
  exact hx0 (by linarith)

private def inverseWindowPartial (A : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  fderiv ℝ A q (0, 1)

private theorem contDiff_inverseWindowPartial {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (inverseWindowPartial A) :=
  (contDiff_infty_iff_fderiv.mp hA).2.clm_apply contDiff_const

private theorem hasDerivAt_windowSlice {A : ℝ × ℝ → ℂ}
    (hA : ContDiff ℝ ∞ A) (p x : ℝ) :
    HasDerivAt (fun y => A (p, y)) (inverseWindowPartial A (p, x)) x := by
  exact ((hA.differentiable (by simp) (p, x)).hasFDerivAt).comp_hasDerivAt x
    ((hasDerivAt_const x p).prodMk (hasDerivAt_id x))

private def inverseWindowZeroSet (a b eps : ℝ) : Set ℝ :=
  {x | x < a ∨ b < x ∨ |x| < eps}

private theorem isOpen_inverseWindowZeroSet (a b eps : ℝ) : IsOpen (inverseWindowZeroSet a b eps) :=
  (isOpen_lt continuous_id continuous_const).union
    ((isOpen_lt continuous_const continuous_id).union (isOpen_lt continuous_abs continuous_const))

private theorem inverseWindowPartial_zero {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ ∞ A)
    {a b eps : ℝ} (hz : ∀ p x, x ∈ inverseWindowZeroSet a b eps → A (p, x) = 0) :
    ∀ p x, x ∈ inverseWindowZeroSet a b eps → inverseWindowPartial A (p, x) = 0 := by
  intro p x hx
  have he : (fun y : ℝ => A (p, y)) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [(isOpen_inverseWindowZeroSet a b eps).mem_nhds hx] with y hy
    exact hz p y hy
  exact (hasDerivAt_windowSlice hA p x).deriv.symm.trans
    (he.deriv_eq.trans (deriv_const x (0 : ℂ)))

private def inverseSlopeDivision (A : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  A q / ((((1 + q.2)⁻¹ - 1) : ℝ) : ℂ)

private theorem inverseSlopeDivision_zero {A : ℝ × ℝ → ℂ} {a b eps : ℝ}
    (hz : ∀ p x, x ∈ inverseWindowZeroSet a b eps → A (p, x) = 0) :
    ∀ p x, x ∈ inverseWindowZeroSet a b eps → inverseSlopeDivision A (p, x) = 0 := by
  intro p x hx
  simp only [inverseSlopeDivision, hz p x hx, zero_div]

private theorem contDiff_inverseSlopeDivision {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ ∞ A)
    {a b eps : ℝ} (ha : -1 < a) (heps : 0 < eps)
    (hz : ∀ p x, x ∈ inverseWindowZeroSet a b eps → A (p, x) = 0) :
    ContDiff ℝ ∞ (inverseSlopeDivision A) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q.2 ∈ inverseWindowZeroSet a b eps
  · have hev : ∀ᶠ z : ℝ × ℝ in 𝓝 q, z.2 ∈ inverseWindowZeroSet a b eps :=
      (continuous_snd.tendsto q).eventually ((isOpen_inverseWindowZeroSet a b eps).mem_nhds hq)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hev] with z hz'
    exact inverseSlopeDivision_zero hz z.1 z.2 hz'
  · have hdom : -1 < q.2 := by
      by_contra hh
      exact hq (Or.inl (lt_of_le_of_lt (le_of_not_gt hh) ha))
    have hq0 : q.2 ≠ 0 := by
      intro hh
      apply hq
      exact Or.inr (Or.inr (by simpa [hh] using heps))
    have hden : ((((1 + q.2)⁻¹ - 1) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (inverseSlope_ne_zero hdom hq0)
    have hd : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (1 + z.2)⁻¹ - 1) q :=
      ((contDiffAt_const.add contDiffAt_snd).inv (by linarith : 1 + q.2 ≠ 0)).sub contDiffAt_const
    have hi : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (((((1 + z.2)⁻¹ - 1))⁻¹ : ℝ) : ℂ)) q :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp q
        (hd.inv (Complex.ofReal_ne_zero.mp hden))
    simpa only [inverseSlopeDivision, div_eq_mul_inv, Complex.ofReal_inv] using! hA.contDiffAt.mul hi

private theorem inverseSlopeDivision_identity {A : ℝ × ℝ → ℂ} {a b eps : ℝ}
    (heps : 0 < eps) (hz : ∀ p x, x ∈ inverseWindowZeroSet a b eps → A (p, x) = 0)
    (p x : ℝ) (hx : -1 < x) :
    inverseSlopeDivision A (p, x) * ((((1 + x)⁻¹ - 1) : ℝ) : ℂ) = A (p, x) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · have hh := hz p 0 (Or.inr (Or.inr (by simpa using heps)))
    simp [inverseSlopeDivision, hh]
  · exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (inverseSlope_ne_zero hx hx0))

/-- The entire complementary logarithmic integral gains two inverse frequencies.
Joint smoothness and a common zero neighborhood supply both divided amplitudes,
including all endpoint terms, uniformly over compact parameter sets. -/
private theorem exists_uniform_logRemainder_nonstationary_remainder
    {A : ℝ × ℝ → ℂ} (hA : ContDiff ℝ ∞ A) {K : Set ℝ} (hK : IsCompact K)
    {a b eps : ℝ} (ha : -1 < a) (hab : a ≤ b) (heps : 0 < eps)
    (hz : ∀ p x, x < a ∨ b < x ∨ |x| < eps → A (p, x) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ lam : ℝ, 0 < lam →
      ‖∫ x : ℝ, A (p, x) * Complex.exp (I * ((lam * logRemainder x : ℝ) : ℂ))‖ ≤
        C / lam ^ 2 := by
  let Q := inverseSlopeDivision A
  let Q' := inverseWindowPartial Q
  let D := inverseSlopeDivision Q'
  let D' := inverseWindowPartial D
  have hQ : ContDiff ℝ ∞ Q := contDiff_inverseSlopeDivision hA ha heps hz
  have hQ' : ContDiff ℝ ∞ Q' := contDiff_inverseWindowPartial hQ
  have hQz : ∀ p x, x ∈ inverseWindowZeroSet a b eps → Q (p, x) = 0 := inverseSlopeDivision_zero hz
  have hQ'z : ∀ p x, x ∈ inverseWindowZeroSet a b eps → Q' (p, x) = 0 := inverseWindowPartial_zero hQ hQz
  have hD : ContDiff ℝ ∞ D := contDiff_inverseSlopeDivision hQ' ha heps hQ'z
  have hD' : ContDiff ℝ ∞ D' := contDiff_inverseWindowPartial hD
  have hDz : ∀ p x, x ∈ inverseWindowZeroSet a b eps → D (p, x) = 0 := inverseSlopeDivision_zero hQ'z
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
  have hreal (x : ℝ) : I * ((lam * (((1 + x)⁻¹ - 1)) : ℝ) : ℂ) =
      z * ((((1 + x)⁻¹ - 1) : ℝ) : ℂ) := by dsimp [z]; push_cast; ring
  have hpoint (x : ℝ) (hx : x ∈ uIcc L U) : -1 < x := by
    rw [uIcc_of_le hLU.le] at hx
    exact hLb.trans_le hx.1
  have hfirst (x : ℝ) (hx : x ∈ uIcc L U) :
      (Q (p, x) / z) * (I * ((lam * (((1 + x)⁻¹ - 1)) : ℝ) : ℂ)) = A (p, x) := by
    rw [hreal]
    calc
      _ = Q (p, x) * ((((1 + x)⁻¹ - 1) : ℝ) : ℂ) := by field_simp [hz0]
      _ = _ := inverseSlopeDivision_identity heps hz p x (hpoint x hx)
  have hsecond (x : ℝ) (hx : x ∈ uIcc L U) :
      (D (p, x) / z ^ 2) * (I * ((lam * (((1 + x)⁻¹ - 1)) : ℝ) : ℂ)) = Q' (p, x) / z := by
    rw [hreal]
    calc
      _ = (D (p, x) * ((((1 + x)⁻¹ - 1) : ℝ) : ℂ)) / z := by field_simp [hz0]
      _ = _ := by rw [inverseSlopeDivision_identity heps hQ'z p x (hpoint x hx)]
  have hsource := _root_.RHTower.integral_cexp_eq_of_two_antiderivatives
    (a := L) (b := U) (φ := fun x => lam * logRemainder x)
    (φ' := fun x => lam * (((1 + x)⁻¹ - 1)))
    (A := fun x => A (p, x)) (B := fun x => Q (p, x) / z)
    (B' := fun x => Q' (p, x) / z) (C := fun x => D (p, x) / z ^ 2)
    (C' := fun x => D' (p, x) / z ^ 2)
    (fun x hx => (hasDerivAt_logRemainder (hpoint x hx)).const_mul lam)
    (fun x _ => (hasDerivAt_windowSlice hQ p x).div_const z)
    (fun x _ => (hasDerivAt_windowSlice hD p x).div_const (z ^ 2))
    (hA.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    ((hQ'.continuous.comp (continuous_const.prodMk continuous_id)).div_const z).continuousOn
    ((hD'.continuous.comp (continuous_const.prodMk continuous_id)).div_const (z ^ 2)).continuousOn
    hfirst hsecond
  have hLz : L ∈ inverseWindowZeroSet a b eps := Or.inl hLa
  have hUz : U ∈ inverseWindowZeroSet a b eps := Or.inr (Or.inl hbU)
  change _ = (Q (p, U) / z - D (p, U) / z ^ 2) * _ -
    (Q (p, L) / z - D (p, L) / z ^ 2) * _ + _ at hsource
  simp only [hQz p U hUz, hQz p L hLz, hDz p U hUz, hDz p L hLz,
    zero_div, sub_self, zero_mul, sub_self, zero_add] at hsource
  have hfull : (∫ x in L..U, A (p, x) *
      Complex.exp (I * ((lam * logRemainder x : ℝ) : ℂ))) =
      ∫ x : ℝ, A (p, x) * Complex.exp (I * ((lam * logRemainder x : ℝ) : ℂ)) := by
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
      Complex.exp (I * ((lam * logRemainder x : ℝ) : ℂ))) (fun x hx => by
      have hxi : x ∈ Icc L U := by
        rw [uIoc_of_le hLU.le] at hx
        exact ⟨hx.1.le, hx.2⟩
      have hn : ‖Complex.exp (I * ((lam * logRemainder x : ℝ) : ℂ))‖ = 1 := by
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


private theorem exists_logRemainderMorse_inverse_window_complement (eta : ContDiffBump (0 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (1 / 2 : ℝ) 4, ∀ lam : ℝ, 0 < lam →
      ‖∫ v : ℝ, (1 - (eta (logRemainderMorse v) : ℂ)) *
          (chiInverseHeightWindow (p * (1 + v)) : ℂ) *
          Complex.exp (I * ((lam * logRemainder v : ℝ) : ℂ))‖ ≤ C / lam ^ 2 := by
  let theta : ContDiffBump (9 / 8 : ℝ) :=
    ⟨15 / 8, 2, by norm_num, by norm_num⟩
  let A : ℝ × ℝ → ℂ := fun q =>
    (theta q.2 : ℂ) * (1 - (eta (logRemainderMorse q.2) : ℂ)) *
      (chiInverseHeightWindow (q.1 * (1 + q.2)) : ℂ)
  have hA : ContDiff ℝ ∞ A := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : -1 < q.2
    · have hw : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => logRemainderMorse z.2) q :=
        (contDiffAt_logRemainderMorse hq).of_le (by simp) |>.comp q contDiffAt_snd
      have he : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (eta (logRemainderMorse z.2) : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q (eta.contDiffAt.comp q hw)
      have ht : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (theta z.2 : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q (theta.contDiffAt.comp q contDiffAt_snd)
      have hW : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ =>
          (chiInverseHeightWindow (z.1 * (1 + z.2)) : ℂ)) q :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp q
          (contDiff_chiInverseHeightWindow.contDiffAt.comp q
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
  have hone : ∀ᶠ v : ℝ in 𝓝 0, eta (logRemainderMorse v) = 1 := by
    have hm : Tendsto logRemainderMorse (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, logRemainderMorse_zero] using
        (contDiffAt_logRemainderMorse (v := 0) (by norm_num)).continuousAt
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
    · have he : eta (logRemainderMorse v) = 1 :=
        hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hv)
      simp [A, he]
  obtain ⟨C, hC, hbound⟩ := exists_uniform_logRemainder_nonstationary_remainder hA
    (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 4))
    (show -1 < -(7 / 8 : ℝ) by norm_num) (show -(7 / 8 : ℝ) ≤ 25 / 8 by norm_num)
    heps hzero
  refine ⟨C, hC, ?_⟩
  intro p hp lam hlam
  have hthetaW (v : ℝ) : (theta v : ℂ) *
      (chiInverseHeightWindow (p * (1 + v)) : ℂ) =
      (chiInverseHeightWindow (p * (1 + v)) : ℂ) := by
    by_cases hv : v ∈ Icc (-(3 / 4 : ℝ)) 3
    · have he : theta v = 1 := theta.one_of_mem_closedBall (by
        change dist v (9 / 8 : ℝ) ≤ 15 / 8
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith [hv.1, hv.2])
      simp only [he, Complex.ofReal_one, one_mul]
    · have hw := chiInverseHeightWindow_scaled_eq_zero hp hv
      simp only [hw, Complex.ofReal_zero, mul_zero]
  have hfun (v : ℝ) : A (p, v) =
      (1 - (eta (logRemainderMorse v) : ℂ)) * (chiInverseHeightWindow (p * (1 + v)) : ℂ) := by
    dsimp [A]
    calc
      _ = (1 - (eta (logRemainderMorse v) : ℂ)) *
        ((theta v : ℂ) * (chiInverseHeightWindow (p * (1 + v)) : ℂ)) := by ring
      _ = _ := by rw [hthetaW]
  have hb := hbound p hp lam hlam
  simp_rw [hfun] at hb
  exact hb

private theorem inverse_full_interval_eq {f : ℝ → ℂ}
    (hf : ∀ v : ℝ, v ∉ Icc (-(3 / 4 : ℝ)) 3 → f v = 0) :
    (∫ v in (-(7 / 8 : ℝ))..(25 / 8 : ℝ), f v) = ∫ v : ℝ, f v := by
  rw [intervalIntegral.integral_of_le (by norm_num : -(7 / 8 : ℝ) ≤ 25 / 8)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  apply hf v
  intro hm
  apply hv
  constructor <;> linarith [hm.1, hm.2]

private theorem inverse_window_integral_split (eta : ContDiffBump (0 : ℝ))
    {p : ℝ} (hp : p ∈ Icc (1 / 2 : ℝ) 4) (lam : ℝ) :
    (∫ v : ℝ, (chiInverseHeightWindow (p * (1 + v)) : ℂ) *
      Complex.exp (I * ((lam * logRemainder v : ℝ) : ℂ))) =
      (∫ v : ℝ, (eta (logRemainderMorse v) : ℂ) *
        (chiInverseHeightWindow (p * (1 + v)) : ℂ) *
        Complex.exp (I * ((lam * logRemainder v : ℝ) : ℂ))) +
      ∫ v : ℝ, (1 - (eta (logRemainderMorse v) : ℂ)) *
        (chiInverseHeightWindow (p * (1 + v)) : ℂ) *
        Complex.exp (I * ((lam * logRemainder v : ℝ) : ℂ)) := by
  let W : ℝ → ℂ := fun v => (chiInverseHeightWindow (p * (1 + v)) : ℂ)
  let E : ℝ → ℂ := fun v => Complex.exp (I * ((lam * logRemainder v : ℝ) : ℂ))
  let H : ℝ → ℂ := fun v => (eta (logRemainderMorse v) : ℂ)
  have hW : Continuous W := Complex.continuous_ofReal.comp
    (contDiff_chiInverseHeightWindow.continuous.comp
      (continuous_const.mul (continuous_const.add continuous_id)))
  have hpsi : ContinuousOn logRemainder (Icc (-(7 / 8 : ℝ)) (25 / 8)) :=
    fun v hv => (hasDerivAt_logRemainder (by linarith [hv.1])).continuousAt.continuousWithinAt
  have hE : ContinuousOn E (Icc (-(7 / 8 : ℝ)) (25 / 8)) :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hpsi)))
  have hH : ContinuousOn H (Icc (-(7 / 8 : ℝ)) (25 / 8)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (eta.continuous.comp_continuousOn (fun v hv =>
        (contDiffAt_logRemainderMorse (by linarith [hv.1])).continuousAt.continuousWithinAt))
  have hloc : IntervalIntegrable (fun v => H v * W v * E v) volume (-(7 / 8 : ℝ)) (25 / 8) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : -(7 / 8 : ℝ) ≤ 25 / 8)]
    exact (hH.mul hW.continuousOn).mul hE
  have hrem : IntervalIntegrable (fun v => (1 - H v) * W v * E v) volume
      (-(7 / 8 : ℝ)) (25 / 8) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : -(7 / 8 : ℝ) ≤ 25 / 8)]
    exact ((continuousOn_const.sub hH).mul hW.continuousOn).mul hE
  have hzero (v : ℝ) (hv : v ∉ Icc (-(3 / 4 : ℝ)) 3) : W v = 0 := by
    simp only [W, chiInverseHeightWindow_scaled_eq_zero hp hv, Complex.ofReal_zero]
  have hf := inverse_full_interval_eq (f := fun v => W v * E v) (fun v hv => by rw [hzero v hv, zero_mul])
  have hl := inverse_full_interval_eq (f := fun v => H v * W v * E v)
    (fun v hv => by rw [hzero v hv, mul_zero, zero_mul])
  have hr := inverse_full_interval_eq (f := fun v => (1 - H v) * W v * E v)
    (fun v hv => by rw [hzero v hv, mul_zero, zero_mul])
  have hi := intervalIntegral.integral_add hloc hrem
  have heq : (fun v => H v * W v * E v + (1 - H v) * W v * E v) =
      fun v => W v * E v := by funext v; ring
  rw [heq, hf, hl, hr] at hi
  exact hi

private theorem inverse_window_local_integral {r : ℝ} (hr : 0 < r)
    {j : ℝ → ℝ} {eta : ContDiffBump (0 : ℝ)} (heta : eta.rOut < r)
    (hdomL : -1 < j (-r)) (hdomR : -1 < j r)
    (hwL : logRemainderMorse (j (-r)) = -r) (hwR : logRemainderMorse (j r) = r)
    {p : ℝ} (hp : p ∈ Icc (1 / 2 : ℝ) 4) (lam : ℝ) :
    (∫ v in j (-r)..j r, (eta (logRemainderMorse v) : ℂ) *
        (chiInverseHeightWindow (p * (1 + v)) : ℂ) *
        Complex.exp (I * ((lam * logRemainder v : ℝ) : ℂ))) =
      ∫ v : ℝ, (eta (logRemainderMorse v) : ℂ) *
        (chiInverseHeightWindow (p * (1 + v)) : ℂ) *
        Complex.exp (I * ((lam * logRemainder v : ℝ) : ℂ)) := by
  have horder : j (-r) ≤ j r := by
    by_contra hh
    have hm := strictMonoOn_logRemainderMorse hdomR hdomL (lt_of_not_ge hh)
    rw [hwR, hwL] at hm
    linarith
  rw [intervalIntegral.integral_of_le horder]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  by_cases hvdom : -1 < v
  · have he : eta (logRemainderMorse v) = 0 := by
      apply eta.zero_of_le_dist
      rw [Real.dist_eq, sub_zero]
      by_cases hvL : v ≤ j (-r)
      · have hh := strictMonoOn_logRemainderMorse.monotoneOn hvdom hdomL hvL
        rw [hwL] at hh
        linarith [neg_le_abs (logRemainderMorse v)]
      · have hvR : j r < v := by
          by_contra hh
          exact hv ⟨lt_of_not_ge hvL, le_of_not_gt hh⟩
        have hh := strictMonoOn_logRemainderMorse.monotoneOn hdomR hvdom hvR.le
        rw [hwR] at hh
        linarith [le_abs_self (logRemainderMorse v)]
    simp only [he, Complex.ofReal_zero, zero_mul]
  · have hz := chiInverseHeightWindow_scaled_eq_zero hp (show v ∉ Icc (-(3 / 4 : ℝ)) 3 by
      intro hh
      linarith [le_of_not_gt hvdom, hh.1])
    simp only [hz, Complex.ofReal_zero, mul_zero, zero_mul]

/-- The complete source physical window has a uniform oriented Fresnel main.
The local saddle, both physical cutoff transitions, and the entire complement remain present. -/
private theorem exists_full_inverse_logRemainder_stationary :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (1 / 2 : ℝ) 4, ∀ lam : ℝ, 1 ≤ lam →
      ‖(∫ v : ℝ, (chiInverseHeightWindow (p * (1 + v)) : ℂ) *
          Complex.exp (I * ((lam * logRemainder v : ℝ) : ℂ))) -
        (chiInverseHeightWindow p : ℂ) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
          Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)‖ ≤
            C / (lam * Real.sqrt lam) := by
  obtain ⟨r, j, eta, hr, heta, hj0, hjd, hj, hfamily⟩ :=
    exists_logRemainderMorse_physical_window_family
  obtain ⟨Cj, hCj, hlocal⟩ := hfamily (fun x => (chiInverseHeightWindow x : ℂ))
    (Complex.ofRealCLM.contDiff.comp contDiff_chiInverseHeightWindow)
    (Icc (1 / 2 : ℝ) 4) isCompact_Icc
  obtain ⟨Cc, hCc, hcomp⟩ := exists_logRemainderMorse_inverse_window_complement eta
  refine ⟨Cj + Cc, by positivity, ?_⟩
  intro p hp lam hlam
  have hlam0 : 0 < lam := by linarith
  have hleft := hj (-r) ⟨le_rfl, by linarith⟩
  have hright := hj r ⟨by linarith, le_rfl⟩
  have hl := inverse_window_local_integral hr heta hleft.2.2.1 hright.2.2.1
    hleft.2.2.2.1 hright.2.2.2.1 hp lam
  have hb := hlocal p hp lam hlam0
  rw [hl] at hb
  rw [inverse_window_integral_split eta hp lam]
  have htriangle : ∀ z w main : ℂ, ‖z + w - main‖ ≤ ‖z - main‖ + ‖w‖ := by
    intro z w main
    calc
      _ = ‖(z - main) + w‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  apply (htriangle _ _ _).trans
  apply (add_le_add hb (hcomp p hp lam hlam0)).trans
  have hsqrt : Real.sqrt lam ≤ lam := Real.sqrt_le_self_iff.mpr (Or.inr hlam)
  have hden : lam * Real.sqrt lam ≤ lam ^ 2 := by nlinarith
  calc
    Cj / (lam * Real.sqrt lam) + Cc / lam ^ 2 ≤
        Cj / (lam * Real.sqrt lam) + Cc / (lam * Real.sqrt lam) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left hCc.le (by positivity) hden)
    _ = _ := by ring


private theorem exists_full_inverse_logRemainder_stationary_positive :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (1 / 2 : ℝ) 4, ∀ lam : ℝ, 1 ≤ lam →
      ‖(∫ v : ℝ, (chiInverseHeightWindow (p * (1 + v)) : ℂ) *
          Complex.exp (-(I * ((lam * logRemainder v : ℝ) : ℂ)))) -
        (chiInverseHeightWindow p : ℂ) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
          Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)‖ ≤
            C / (lam * Real.sqrt lam) := by
  obtain ⟨C, hC, hb⟩ := exists_full_inverse_logRemainder_stationary
  refine ⟨C, hC, ?_⟩
  intro p hp lam hlam
  have he (v : ℝ) : (chiInverseHeightWindow (p * (1 + v)) : ℂ) *
      Complex.exp (-(I * ((lam * logRemainder v : ℝ) : ℂ))) =
      (starRingEnd ℂ) ((chiInverseHeightWindow (p * (1 + v)) : ℂ) *
        Complex.exp (I * ((lam * logRemainder v : ℝ) : ℂ))) := by
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I, neg_mul]
  have hm : (chiInverseHeightWindow p : ℂ) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
      Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) =
      (starRingEnd ℂ) ((chiInverseHeightWindow p : ℂ) * (Real.sqrt (2 * Real.pi / lam) : ℂ) *
        Complex.exp (((-(Real.pi / 4) : ℝ) : ℂ) * I)) := by
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
    congr 2
    push_cast
    ring
  simp_rw [he]
  rw [integral_conj, hm, ← map_sub, RCLike.norm_conj]
  exact hb p hp lam hlam

private theorem inverse_full_integral_affine (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, f t) = (a : ℂ) * ∫ v : ℝ, f (a * (1 + v)) := by
  have hshift := integral_add_left_eq_self (μ := volume) (fun x : ℝ => f (a * x)) (1 : ℝ)
  have hscale := MeasureTheory.Measure.integral_comp_mul_left f a
  rw [hscale] at hshift
  rw [abs_of_pos (inv_pos.mpr ha), Complex.real_smul] at hshift
  rw [hshift, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne']

/-- The full inverse integral in its positive-height coordinate. -/
def chiInverseHeightIntegral (T t : ℝ) : ℂ :=
  (Real.sqrt (T / (2 * Real.pi)) : ℂ) * ∫ x : ℝ,
    (chiInverseHeightWindow x : ℂ) *
      Complex.exp (I * ((T * x - t * Real.log (T * x / (2 * Real.pi)) : ℝ) : ℂ))

private theorem chiInverseHeightIntegral_scaled {T t : ℝ} (hT : 0 < T) (ht : 0 < t) :
    chiInverseHeightIntegral T t =
      (Real.sqrt (T / (2 * Real.pi)) : ℂ) * ((t / T : ℝ) : ℂ) *
        Complex.exp (I * ((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ)) *
        ∫ v : ℝ, (chiInverseHeightWindow ((t / T) * (1 + v)) : ℂ) *
          Complex.exp (-(I * ((t * logRemainder v : ℝ) : ℂ))) := by
  unfold chiInverseHeightIntegral
  rw [inverse_full_integral_affine _ (div_pos ht hT)]
  have he (v : ℝ) : (chiInverseHeightWindow ((t / T) * (1 + v)) : ℂ) *
      Complex.exp (I * ((T * ((t / T) * (1 + v)) -
        t * Real.log (T * ((t / T) * (1 + v)) / (2 * Real.pi)) : ℝ) : ℂ)) =
      Complex.exp (I * ((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ)) *
        ((chiInverseHeightWindow ((t / T) * (1 + v)) : ℂ) *
          Complex.exp (-(I * ((t * logRemainder v : ℝ) : ℂ)))) := by
    by_cases hv : -1 < v
    · have hscale : T * ((t / T) * (1 + v)) = t * (1 + v) := by field_simp
      rw [hscale, chiInverseFrequency_phase_scaled ht hv]
      rw [Complex.ofReal_sub, mul_sub, Complex.exp_sub]
      rw [Complex.exp_neg]
      ring
    · have hz : chiInverseHeightWindow ((t / T) * (1 + v)) = 0 :=
        chiInverseHeightWindow_zero (Or.inl (by
          have := mul_nonpos_of_nonneg_of_nonpos (div_pos ht hT).le
            (show 1 + v ≤ 0 by linarith [le_of_not_gt hv])
          linarith))
      simp only [hz, Complex.ofReal_zero, zero_mul, mul_zero]
  simp_rw [he]
  rw [integral_const_mul]
  ring

private theorem inverse_main_amplitude {T t : ℝ} (hT : 0 < T) (ht : 0 < t) :
    Real.sqrt (T / (2 * Real.pi)) * (t / T) *
      chiInverseHeightWindow (t / T) * Real.sqrt (2 * Real.pi / t) =
        bagPhysicalHeightWindow (t / T) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hsT := Real.sq_sqrt hT.le
  have hst := Real.sq_sqrt ht.le
  unfold chiInverseHeightWindow
  rw [Real.sqrt_div hT.le, Real.sqrt_div hpi.le, Real.sqrt_div ht.le]
  field_simp [(Real.sqrt_pos.mpr hT).ne', (Real.sqrt_pos.mpr ht).ne',
    (Real.sqrt_pos.mpr hpi).ne', hT.ne']
  rw [hsT, hst]
  ring

/-- Uniform complete inverse-height reconstruction of the conductor model. -/
theorem exists_chiInverseHeightIntegral_model_remainder :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4 ≤ T → ∀ t ∈ Icc T (2 * T),
      ‖chiInverseHeightIntegral T t - (bagPhysicalHeightWindow (t / T) : ℂ) *
        Complex.exp (I * ((t - t * Real.log (t / (2 * Real.pi)) + Real.pi / 4 : ℝ) : ℂ))‖ ≤
          C / T := by
  obtain ⟨C, hC, hb⟩ := exists_full_inverse_logRemainder_stationary_positive
  refine ⟨2 * C, by positivity, ?_⟩
  intro T hT t ht
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le hT0 ht.1
  have hp : t / T ∈ Icc (1 / 2 : ℝ) 4 := by
    constructor
    · rw [le_div_iff₀ hT0]; linarith [ht.1]
    · rw [div_le_iff₀ hT0]; linarith [ht.2]
  have hb' := hb (t / T) hp t (by linarith [ht.1])
  let z := Complex.exp (I * ((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ))
  let m := (chiInverseHeightWindow (t / T) : ℂ) * (Real.sqrt (2 * Real.pi / t) : ℂ) *
    Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I)
  have hmain : (Real.sqrt (T / (2 * Real.pi)) : ℂ) * ((t / T : ℝ) : ℂ) * z * m =
      (bagPhysicalHeightWindow (t / T) : ℂ) *
        Complex.exp (I * ((t - t * Real.log (t / (2 * Real.pi)) + Real.pi / 4 : ℝ) : ℂ)) := by
    have he : I * ((t - t * Real.log (t / (2 * Real.pi)) + Real.pi / 4 : ℝ) : ℂ) =
        I * ((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) +
          ((Real.pi / 4 : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.exp_add, ← inverse_main_amplitude hT0 ht0]
    dsimp [z, m]
    push_cast
    ring
  have hz : ‖z‖ = 1 := by
    simp [z, Complex.norm_exp, Complex.mul_re]
  rw [chiInverseHeightIntegral_scaled hT0 ht0, ← hmain, ← mul_sub]
  rw [norm_mul, norm_mul, norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos ht0 hT0)]
  apply (mul_le_mul_of_nonneg_left hb' (by positivity)).trans
  have hsq : Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T := by
    apply Real.sqrt_le_sqrt
    apply div_le_self hT0.le
    nlinarith [Real.pi_gt_three]
  have hratio : t / T ≤ 2 := (div_le_iff₀ hT0).mpr ht.2
  have hroot : Real.sqrt T ≤ Real.sqrt t := Real.sqrt_le_sqrt ht.1
  have hden : 0 < t * Real.sqrt t := by positivity
  calc
    Real.sqrt (T / (2 * Real.pi)) * (t / T) * (C / (t * Real.sqrt t)) ≤
        Real.sqrt T * 2 * (C / (t * Real.sqrt t)) := by gcongr
    _ ≤ Real.sqrt t * 2 * (C / (t * Real.sqrt t)) := by gcongr
    _ = (2 * C) / t := by field_simp [(Real.sqrt_pos.mpr ht0).ne']
    _ ≤ (2 * C) / T := div_le_div_of_nonneg_left (by positivity) hT0 ht.1


/-- The entire stationary frequency kernel, retaining the actual physical window. -/
def chiStationaryFrequencyKernel (T lam : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi * (2 * Real.pi * Real.exp lam)) : ℂ) *
    (bagPhysicalHeightWindow ((2 * Real.pi * Real.exp lam) / T) : ℂ) *
      Complex.exp (I * ((2 * Real.pi * Real.exp lam : ℝ) : ℂ))

/-- Literal inverse-frequency reconstruction, with the angular-frequency normalization. -/
def chiInverseStationaryKernel (T t : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ lam : ℝ,
    chiStationaryFrequencyKernel T lam * Complex.exp (-(I * ((t * lam : ℝ) : ℂ)))

private theorem chiStationaryFrequencyKernel_zero {T lam : ℝ} (hT : 0 < T)
    (hlam : lam ≤ Real.log (T / (2 * Real.pi)) ∨
      Real.log (2 * T / (2 * Real.pi)) ≤ lam) :
    chiStationaryFrequencyKernel T lam = 0 := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hz : bagPhysicalHeightWindow ((2 * Real.pi * Real.exp lam) / T) = 0 := by
    apply bagPhysicalHeightWindow.zero_of_le_dist
    change (1 / 2 : ℝ) ≤ dist ((2 * Real.pi * Real.exp lam) / T) (3 / 2)
    rw [Real.dist_eq]
    rcases hlam with h | h
    · have he : Real.exp lam ≤ T / (2 * Real.pi) :=
        (Real.le_log_iff_exp_le (div_pos hT hpi)).mp h
      have ha : (2 * Real.pi * Real.exp lam) / T ≤ 1 := by
        rw [div_le_iff₀ hT]
        have := (le_div_iff₀ hpi).mp he
        nlinarith
      linarith [neg_le_abs ((2 * Real.pi * Real.exp lam) / T - 3 / 2)]
    · have he : 2 * T / (2 * Real.pi) ≤ Real.exp lam :=
        (Real.log_le_iff_le_exp (by positivity)).mp h
      have ha : 2 ≤ (2 * Real.pi * Real.exp lam) / T := by
        rw [le_div_iff₀ hT]
        have := (div_le_iff₀ hpi).mp he
        nlinarith
      linarith [le_abs_self ((2 * Real.pi * Real.exp lam) / T - 3 / 2)]
  simp only [chiStationaryFrequencyKernel, hz, Complex.ofReal_zero, mul_zero, zero_mul]

private theorem inverse_log_jacobian {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    (1 / (2 * Real.pi)) * x⁻¹ * Real.sqrt (2 * Real.pi * (T * x)) *
      bagPhysicalHeightWindow x =
        Real.sqrt (T / (2 * Real.pi)) * chiInverseHeightWindow x := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hsx := Real.sq_sqrt hx.le
  have hsp := Real.sq_sqrt hp.le
  unfold chiInverseHeightWindow
  rw [Real.sqrt_mul hp.le, Real.sqrt_mul hT.le, Real.sqrt_div hT.le]
  field_simp [(Real.sqrt_pos.mpr hp).ne', (Real.sqrt_pos.mpr hx).ne', hx.ne', hp.ne']
  rw [hsp, hsx]

/-- Exact logarithmic change of variables; no kernel term is discarded. -/
theorem chiInverseStationaryKernel_eq_heightIntegral {T : ℝ} (hT : 0 < T) (t : ℝ) :
    chiInverseStationaryKernel T t = chiInverseHeightIntegral T t := by
  let L := Real.log (T / (2 * Real.pi))
  let U := Real.log (2 * T / (2 * Real.pi))
  let f : ℝ → ℝ := fun x => Real.log (T * x / (2 * Real.pi))
  let g : ℝ → ℂ := fun lam => chiStationaryFrequencyKernel T lam *
    Complex.exp (-(I * ((t * lam : ℝ) : ℂ)))
  have hpi : 0 < 2 * Real.pi := by positivity
  have hLU : L ≤ U := Real.log_le_log (div_pos hT hpi) (by gcongr; linarith)
  have hf1 : f 1 = L := by simp [f, L]
  have hf2 : f 2 = U := by dsimp [f, U]; congr 1; ring
  have hff (x : ℝ) (hx : 0 < x) : HasDerivAt f x⁻¹ x := by
    have hd := ((hasDerivAt_id x).const_mul T).div_const (2 * Real.pi)
    have hl := (Real.hasDerivAt_log (ne_of_gt (div_pos (mul_pos hT hx) hpi))).comp x hd
    convert hl using 1 <;> first | rfl | field_simp
  have hf : ContinuousOn f (uIcc (1 : ℝ) 2) := by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    exact fun x hx => (hff x (by linarith [hx.1])).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ Ioo (min (1 : ℝ) 2) (max (1 : ℝ) 2), HasDerivAt f x⁻¹ x := by
    intro x hx
    exact hff x (by norm_num at hx; linarith [hx.1])
  have hn : ∀ x ∈ Ioo (min (1 : ℝ) 2) (max (1 : ℝ) 2), 0 ≤ x⁻¹ := by
    intro x hx
    have : 0 < x := by norm_num at hx; linarith [hx.1]
    positivity
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (g := g) hf hd hn
  rw [hf1, hf2] at hsub
  have hfull : (∫ lam in L..U, g lam) = ∫ lam : ℝ, g lam := by
    rw [intervalIntegral.integral_of_le hLU]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro lam hlam
    have hz : chiStationaryFrequencyKernel T lam = 0 := by
      apply chiStationaryFrequencyKernel_zero hT
      by_cases h : lam ≤ L
      · exact Or.inl h
      · exact Or.inr (le_of_lt (lt_of_not_ge (fun hU => hlam ⟨lt_of_not_ge h, hU⟩)))
    simp only [g, hz, zero_mul]
  have hxfull : (∫ x in (1 : ℝ)..2, (chiInverseHeightWindow x : ℂ) *
      Complex.exp (I * ((T * x - t * Real.log (T * x / (2 * Real.pi)) : ℝ) : ℂ))) =
      ∫ x : ℝ, (chiInverseHeightWindow x : ℂ) *
        Complex.exp (I * ((T * x - t * Real.log (T * x / (2 * Real.pi)) : ℝ) : ℂ)) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : chiInverseHeightWindow x = 0 := by
      apply chiInverseHeightWindow_zero
      by_cases h : x ≤ 1
      · exact Or.inl h
      · exact Or.inr (le_of_lt (lt_of_not_ge (fun h2 => hx ⟨lt_of_not_ge h, h2⟩)))
    simp only [hz, Complex.ofReal_zero, zero_mul]
  unfold chiInverseStationaryKernel chiInverseHeightIntegral
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ lam : ℝ, g lam) = _
  rw [← hfull, ← hsub, ← hxfull, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
  have hx0 : 0 < x := by linarith [hx.1]
  have ha : 2 * Real.pi * Real.exp (f x) = T * x := by
    rw [show f x = Real.log (T * x / (2 * Real.pi)) from rfl,
      Real.exp_log (div_pos (mul_pos hT hx0) hpi)]
    field_simp
  have harg : T * x / T = x := mul_div_cancel_left₀ x hT.ne'
  simp only [Function.comp_apply, Complex.real_smul, g, chiStationaryFrequencyKernel, ha, harg]
  have hphase : Complex.exp (I * ((T * x : ℝ) : ℂ)) *
      Complex.exp (-(I * ((t * f x : ℝ) : ℂ))) =
      Complex.exp (I * ((T * x - t * Real.log (T * x / (2 * Real.pi)) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [f]
    push_cast
    ring
  calc
    _ = ((((1 / (2 * Real.pi)) * x⁻¹ * Real.sqrt (2 * Real.pi * (T * x)) *
        bagPhysicalHeightWindow x : ℝ) : ℂ)) *
        (Complex.exp (I * ((T * x : ℝ) : ℂ)) * Complex.exp (-(I * ((t * f x : ℝ) : ℂ)))) := by
      push_cast
      ring
    _ = _ := by rw [inverse_log_jacobian hT hx0, hphase]; push_cast; ring


/-- One source constant reconstructs actual chi uniformly on the full physical window. -/
theorem exists_chiInverseStationaryKernel_remainder :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4 ≤ T → ∀ t ∈ Icc T (2 * T),
      ‖chiInverseStationaryKernel T t -
        (bagPhysicalHeightWindow (t / T) : ℂ) * zetaChi (linePt t)‖ ≤ C / T := by
  obtain ⟨C, hC, hb⟩ := exists_chiInverseHeightIntegral_model_remainder
  refine ⟨C + 26, by positivity, ?_⟩
  intro T hT t ht
  have hT0 : 0 < T := by linarith
  have ht4 : 4 ≤ t := hT.trans ht.1
  have ht0 : 0 < t := by linarith
  let m := Complex.exp (I * ((t - t * Real.log (t / (2 * Real.pi)) + Real.pi / 4 : ℝ) : ℂ))
  have hm : m = bourgainOscillation (Real.pi / 4) *
      Complex.exp (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I) := by
    unfold m bourgainOscillation
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hc : ‖zetaChi (linePt t) - m‖ ≤ 26 / t := by
    have h := norm_zetaChi_integerGrade_sub_explicit_model_le (1 : ℤ) ht4
    simpa only [hm, zpow_one, Int.cast_one, one_mul, abs_one, mul_one] using h
  have hw : ‖(bagPhysicalHeightWindow (t / T) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bagPhysicalHeightWindow.nonneg]
    exact bagPhysicalHeightWindow.le_one
  have hwm : ‖(bagPhysicalHeightWindow (t / T) : ℂ) * m -
      (bagPhysicalHeightWindow (t / T) : ℂ) * zetaChi (linePt t)‖ ≤ 26 / T := by
    rw [← mul_sub, norm_mul, norm_sub_rev]
    calc
      _ ≤ 1 * (26 / t) := mul_le_mul hw hc (norm_nonneg _) (by norm_num)
      _ ≤ 26 / T := by rw [one_mul]; exact div_le_div_of_nonneg_left (by norm_num) hT0 ht.1
  rw [chiInverseStationaryKernel_eq_heightIntegral hT0]
  calc
    _ ≤ ‖chiInverseHeightIntegral T t - (bagPhysicalHeightWindow (t / T) : ℂ) * m‖ +
        ‖(bagPhysicalHeightWindow (t / T) : ℂ) * m -
          (bagPhysicalHeightWindow (t / T) : ℂ) * zetaChi (linePt t)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C / T + 26 / T := add_le_add (hb T hT t ht) hwm
    _ = _ := by ring

/-- The complete error is bounded before any prime-product expansion. The same constant
works for every pair of physical L2 inputs and every moment degree. -/
theorem exists_chiInverseStationaryKernel_L2_remainder :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4 ≤ T →
      ∀ f g : Lp ℂ 2 (volume.restrict (Icc T (2 * T))),
        ‖∫ t in Icc T (2 * T),
          (chiInverseStationaryKernel T t -
            (bagPhysicalHeightWindow (t / T) : ℂ) * zetaChi (linePt t)) *
              f t * (starRingEnd ℂ) (g t)‖ ≤ (C / T) * ‖f‖ * ‖g‖ := by
  obtain ⟨C, hC, hb⟩ := exists_chiInverseStationaryKernel_remainder
  refine ⟨C, hC, ?_⟩
  intro T hT f g
  have hT0 : 0 < T := by linarith
  have hfg : Integrable (fun t => ‖f t‖ * ‖g t‖) (volume.restrict (Icc T (2 * T))) :=
    (Lp.memLp f).norm.integrable_mul (Lp.memLp g).norm
  have hholder : (∫ t in Icc T (2 * T), ‖f t‖ * ‖g t‖) ≤ ‖f‖ * ‖g‖ := by
    have hh := integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict (Icc T (2 * T)))
      (show Real.HolderConjugate 2 2 from Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (show MemLp (fun t => f t) (ENNReal.ofReal 2) (volume.restrict (Icc T (2 * T))) by
        simpa using Lp.memLp f)
      (show MemLp (fun t => g t) (ENNReal.ofReal 2) (volume.restrict (Icc T (2 * T))) by
        simpa using Lp.memLp g)
    have hf := lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal))
      (by norm_num) (by norm_num) (Lp.aestronglyMeasurable f)
    have hg := lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal))
      (by norm_num) (by norm_num) (Lp.aestronglyMeasurable g)
    rw [← toReal_eLpNorm (Lp.aestronglyMeasurable f), ← Lp.norm_def] at hf
    rw [← toReal_eLpNorm (Lp.aestronglyMeasurable g), ← Lp.norm_def] at hg
    norm_num only [ENNReal.toReal_ofNat, one_div] at hf hg hh
    rwa [← hf, ← hg] at hh
  calc
    _ ≤ ∫ t in Icc T (2 * T), (C / T) * (‖f t‖ * ‖g t‖) := by
      apply norm_integral_le_of_norm_le (hfg.const_mul (C / T))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [norm_mul, norm_mul, RCLike.norm_conj]
      calc
        _ ≤ (C / T) * ‖f t‖ * ‖g t‖ := by gcongr; exact hb T hT t ht
        _ = _ := by ring
    _ = (C / T) * (∫ t in Icc T (2 * T), ‖f t‖ * ‖g t‖) := integral_const_mul _ _
    _ ≤ (C / T) * (‖f‖ * ‖g‖) := mul_le_mul_of_nonneg_left hholder (by positivity)
    _ = _ := by ring


private theorem continuous_chiStationaryFrequencyKernel (T : ℝ) :
    Continuous (chiStationaryFrequencyKernel T) := by
  have hA : Continuous (fun lam : ℝ =>
      (Real.sqrt (2 * Real.pi * (2 * Real.pi * Real.exp lam)) : ℂ)) := by fun_prop
  have hW : Continuous (fun lam : ℝ =>
      (bagPhysicalHeightWindow ((2 * Real.pi * Real.exp lam) / T) : ℂ)) :=
    Complex.continuous_ofReal.comp (bagPhysicalHeightWindow.continuous.comp (by fun_prop))
  exact (hA.mul hW).mul (by fun_prop)

private theorem integrable_chiStationaryFrequencyKernel {T : ℝ} (hT : 0 < T) :
    Integrable (chiStationaryFrequencyKernel T) := by
  apply (continuous_chiStationaryFrequencyKernel T).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := Real.log (T / (2 * Real.pi)))
      (b := Real.log (2 * T / (2 * Real.pi))))
  intro lam hlam
  have hn : chiStationaryFrequencyKernel T lam ≠ 0 := hlam
  constructor
  · by_contra h
    exact hn (chiStationaryFrequencyKernel_zero hT (Or.inl (lt_of_not_ge h).le))
  · by_contra h
    exact hn (chiStationaryFrequencyKernel_zero hT (Or.inr (lt_of_not_ge h).le))

private theorem inverse_fubini_integrable {T : ℝ} (hT : 0 < T)
    {mu : Measure ℝ} [SFinite mu] {h : ℝ → ℂ} (hh : Integrable h mu) :
    Integrable (fun q : ℝ × ℝ => chiStationaryFrequencyKernel T q.1 *
      Complex.exp (-(I * ((q.2 * q.1 : ℝ) : ℂ))) * h q.2) (volume.prod mu) := by
  have hK := integrable_chiStationaryFrequencyKernel hT
  have hphase : Continuous (fun q : ℝ × ℝ =>
      Complex.exp (-(I * ((q.2 * q.1 : ℝ) : ℂ)))) := by fun_prop
  apply (hK.norm.mul_prod hh.norm).mono'
    ((hK.aestronglyMeasurable.comp_fst.mul hphase.aestronglyMeasurable).mul
      hh.aestronglyMeasurable.comp_snd)
  filter_upwards with q
  simp [Complex.norm_exp, Complex.mul_re]

private theorem integral_chiInverseStationaryKernel_mul_eq {T : ℝ} (hT : 0 < T)
    {mu : Measure ℝ} [SFinite mu] {h : ℝ → ℂ} (hh : Integrable h mu) :
    (∫ t, chiInverseStationaryKernel T t * h t ∂mu) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ lam : ℝ,
        chiStationaryFrequencyKernel T lam *
          (∫ t, Complex.exp (-(I * ((t * lam : ℝ) : ℂ))) * h t ∂mu) := by
  have hf := inverse_fubini_integrable hT hh
  have hs := integral_integral_swap (f := fun lam t => chiStationaryFrequencyKernel T lam *
    Complex.exp (-(I * ((t * lam : ℝ) : ℂ))) * h t) hf
  have he (t : ℝ) : chiInverseStationaryKernel T t * h t =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) * ∫ lam : ℝ,
        chiStationaryFrequencyKernel T lam * Complex.exp (-(I * ((t * lam : ℝ) : ℂ))) * h t := by
    rw [integral_mul_const]
    simp only [chiInverseStationaryKernel]
    ring
  simp_rw [he]
  rw [integral_const_mul, ← hs]
  simp_rw [mul_assoc, integral_const_mul]

private theorem integrable_chiInverseStationaryKernel_mul {T : ℝ} (hT : 0 < T)
    {mu : Measure ℝ} [SFinite mu] {h : ℝ → ℂ} (hh : Integrable h mu) :
    Integrable (fun t => chiInverseStationaryKernel T t * h t) mu := by
  have hi := (inverse_fubini_integrable hT hh).integral_prod_right.const_mul
    (((1 / (2 * Real.pi) : ℝ) : ℂ))
  simp only [integral_mul_const] at hi
  simpa only [chiInverseStationaryKernel, mul_assoc] using hi

/-- Exact main pairing, including the full finite-window frequency smearing. -/
theorem chiInverseStationaryKernel_physical_pairing {T : ℝ} (hT : 0 < T)
    (f g : Lp ℂ 2 (volume.restrict (Icc T (2 * T)))) :
    (∫ t in Icc T (2 * T), chiInverseStationaryKernel T t * f t * (starRingEnd ℂ) (g t)) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ lam : ℝ,
        chiStationaryFrequencyKernel T lam *
          (∫ t in Icc T (2 * T),
            Complex.exp (-(I * ((t * lam : ℝ) : ℂ))) * f t * (starRingEnd ℂ) (g t)) := by
  have hh : Integrable (fun t => f t * (starRingEnd ℂ) (g t))
      (volume.restrict (Icc T (2 * T))) :=
    (Lp.memLp f).integrable_mul (Lp.memLp g).star
  simpa only [mul_assoc] using integral_chiInverseStationaryKernel_mul_eq hT hh

/-- Complete actual-chi bilinear asymptotic. The frequency main keeps its literal
finite-height convolution, while the remainder has no prime-support or degree factor. -/
theorem exists_chiStationaryFrequencyKernel_bilinear_remainder :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4 ≤ T →
      ∀ f g : Lp ℂ 2 (volume.restrict (Icc T (2 * T))),
        ‖(∫ t in Icc T (2 * T), (bagPhysicalHeightWindow (t / T) : ℂ) *
            zetaChi (linePt t) * f t * (starRingEnd ℂ) (g t)) -
          ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ lam : ℝ,
            chiStationaryFrequencyKernel T lam *
              (∫ t in Icc T (2 * T), Complex.exp (-(I * ((t * lam : ℝ) : ℂ))) *
                f t * (starRingEnd ℂ) (g t))‖ ≤ (C / T) * ‖f‖ * ‖g‖ := by
  obtain ⟨C, hC, hb⟩ := exists_chiInverseStationaryKernel_L2_remainder
  refine ⟨C, hC, ?_⟩
  intro T hT f g
  have hT0 : 0 < T := by linarith
  have hh : Integrable (fun t => f t * (starRingEnd ℂ) (g t))
      (volume.restrict (Icc T (2 * T))) :=
    (Lp.memLp f).integrable_mul (Lp.memLp g).star
  have hR : Integrable (fun t => chiInverseStationaryKernel T t * f t * (starRingEnd ℂ) (g t))
      (volume.restrict (Icc T (2 * T))) := by
    simpa only [mul_assoc] using integrable_chiInverseStationaryKernel_mul hT0 hh
  have hchi : Continuous (fun t : ℝ => zetaChi (linePt t)) := by
    simpa only [zpow_one, zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
      using continuous_zetaChiCriticalGradeIntegrand (1 : ℤ) 0
  have hW : Continuous (fun t : ℝ => (bagPhysicalHeightWindow (t / T) : ℂ)) :=
    Complex.continuous_ofReal.comp (bagPhysicalHeightWindow.continuous.comp (by fun_prop))
  have hactual : Integrable (fun t => (bagPhysicalHeightWindow (t / T) : ℂ) *
      zetaChi (linePt t) * f t * (starRingEnd ℂ) (g t))
      (volume.restrict (Icc T (2 * T))) := by
    apply hh.norm.mono' (((hW.mul hchi).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)).mul (Lp.aestronglyMeasurable g).star)
    filter_upwards with t
    change ‖(bagPhysicalHeightWindow (t / T) : ℂ) * zetaChi (linePt t) *
      f t * (starRingEnd ℂ) (g t)‖ ≤ ‖f t * (starRingEnd ℂ) (g t)‖
    simp only [norm_mul, norm_zetaChi_line, mul_one, RCLike.norm_conj]
    have hw : ‖(bagPhysicalHeightWindow (t / T) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bagPhysicalHeightWindow.nonneg]
      exact bagPhysicalHeightWindow.le_one
    calc
      _ ≤ 1 * ‖f t‖ * ‖g t‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  rw [← chiInverseStationaryKernel_physical_pairing hT0 f g,
    norm_sub_rev, ← integral_sub hR hactual]
  have he : (fun t => chiInverseStationaryKernel T t * f t * (starRingEnd ℂ) (g t) -
      (bagPhysicalHeightWindow (t / T) : ℂ) * zetaChi (linePt t) * f t * (starRingEnd ℂ) (g t)) =
      fun t => (chiInverseStationaryKernel T t -
        (bagPhysicalHeightWindow (t / T) : ℂ) * zetaChi (linePt t)) * f t * (starRingEnd ℂ) (g t) := by
    funext t
    ring
  rw [he]
  exact hb T hT f g

end GaloisForLFunctions.RHTower
