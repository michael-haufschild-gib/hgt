import GaloisForLFunctions.HTGeometry.ReflectionContactParity

/-!
# The scalar arclength wall and the statistical fold

For an even positive analytic response `I` of order `2k`:

* **Corollary 4.1.**  The signed arclength `A(t) = sign(t) ∫₀^{|t|} √I` `(RP.8)` equals the
  primitive of `|t|ᵏ h(t)`.  For even `k` it is analytic and is the rank-one oriented realization;
  for odd `k` it is `Cᵏ` but not `C^{k+1}` at `0`, because `t^{k-1}|t|` is `C^{k-1}` but not `Cᵏ`
  (its `(k-1)`-st derivative is a multiple of `|t|`).
* **§5, `(RP.10)`–`(RP.13)`.**  For a scalar primitive `Θ` of an analytic square root of `I`,
  `|Θ| < π/2`, the Bernoulli family `p = (1 + sin Θ)/2` has Fisher information `p'²/(p(1-p)) = I`.
  For odd `k` every analytic square root of `I` is odd, so `Θ` is even and `p(t) = p(-t)`: any
  parameter-independent recovery of the law folds the two reflection sides.  Conversely the Fisher
  information is the second derivative of the divergence germ `s ↦ KL(p(t) ‖ p(s))` at `s = t`, so
  a recovery preserving the divergence germ preserves `I`, its half-order and the oriented rank.
-/

open Filter Topology Set
open scoped InnerProductSpace RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {I : ℝ → ℝ} {k : ℕ}

/-! ### The `|t|`-power wall -/

/-- `t |t|` has derivative `2 |t|` everywhere. -/
theorem hasDerivAt_mul_abs (t : ℝ) : HasDerivAt (fun s : ℝ => s * |s|) (2 * |t|) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have heq : (fun s : ℝ => s * |s|) =ᶠ[𝓝 t] fun s => -(s ^ 2) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      rw [abs_of_neg hs]
      ring
    have hd : HasDerivAt (fun s : ℝ => -(s ^ 2)) (2 * |t|) t := by
      refine (hasDerivAt_pow 2 t).neg.congr_deriv ?_
      rw [abs_of_neg ht, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact hd.congr_of_eventuallyEq heq
  · rw [abs_zero, mul_zero, hasDerivAt_iff_tendsto_slope]
    have hcont : Tendsto (fun s : ℝ => |s|) (𝓝[≠] 0) (𝓝 0) := by
      have := (continuous_abs (G := ℝ)).tendsto 0
      rw [abs_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine hcont.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [slope_def_field, zero_mul, sub_zero, sub_zero]
    field_simp [show s ≠ 0 from hs]
  · have heq : (fun s : ℝ => s * |s|) =ᶠ[𝓝 t] fun s => s ^ 2 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      rw [abs_of_pos hs]
      ring
    have hd : HasDerivAt (fun s : ℝ => s ^ 2) (2 * |t|) t := by
      refine (hasDerivAt_pow 2 t).congr_deriv ?_
      rw [abs_of_pos ht, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact hd.congr_of_eventuallyEq heq

/-- `t^{m+1} |t|` has derivative `(m + 2) tᵐ |t|`. -/
theorem hasDerivAt_pow_succ_mul_abs (m : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ (m + 1) * |s|) ((m + 2) * (t ^ m * |t|)) t := by
  have h1 : (fun s : ℝ => s ^ (m + 1) * |s|) = fun s => s ^ m * (s * |s|) := by
    funext s
    ring
  rw [h1]
  refine ((hasDerivAt_pow m t).mul (hasDerivAt_mul_abs t)).congr_deriv ?_
  cases m with
  | zero => simp
  | succ m =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

/-- `tᵐ |t|` is `Cᵐ`. -/
theorem contDiff_pow_mul_abs (m : ℕ) : ContDiff ℝ m (fun t : ℝ => t ^ m * |t|) := by
  induction m with
  | zero =>
      simp only [pow_zero, one_mul, Nat.cast_zero]
      exact contDiff_zero.mpr continuous_abs
  | succ m ih =>
      have hcast : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by norm_cast
      rw [hcast, contDiff_succ_iff_deriv]
      have hderiv : deriv (fun s : ℝ => s ^ (m + 1) * |s|) =
          fun t => ((m : ℝ) + 2) * (t ^ m * |t|) :=
        funext fun t => (hasDerivAt_pow_succ_mul_abs m t).deriv
      refine ⟨fun t => (hasDerivAt_pow_succ_mul_abs m t).differentiableAt, ?_, ?_⟩
      · intro h
        exact absurd h (by simp)
      · rw [hderiv]
        exact (contDiff_const (c := (m : ℝ) + 2)).mul ih

/-- **`tᵐ |t|` is not `C^{m+1}` at `0`.** -/
theorem not_contDiffAt_pow_mul_abs (m : ℕ) :
    ¬ ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun t : ℝ => t ^ m * |t|) 0 := by
  induction m with
  | zero =>
      intro h
      have hd := h.differentiableAt (by norm_num)
      simp only [pow_zero, one_mul] at hd
      exact not_differentiableAt_abs_zero hd
  | succ m ih =>
      intro h
      have hle : ((m + 1 : ℕ) : WithTop ℕ∞) + 1 ≤ ((m + 1 + 1 : ℕ) : WithTop ℕ∞) := by
        norm_cast
      have h1 : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞)
          (deriv fun s : ℝ => s ^ (m + 1) * |s|) 0 :=
        (h.fderiv_right hle).clm_apply contDiffAt_const
      have hderiv : deriv (fun s : ℝ => s ^ (m + 1) * |s|) =
          fun t => ((m : ℝ) + 2) * (t ^ m * |t|) :=
        funext fun t => (hasDerivAt_pow_succ_mul_abs m t).deriv
      rw [hderiv] at h1
      apply ih
      have h2 := (contDiffAt_const (c := ((m : ℝ) + 2)⁻¹)).mul h1
      refine h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
      have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
      field_simp

/-! ### The signed arclength -/

/-- The signed arclength `A(t) = sign(t) ∫₀^{|t|} √I` `(RP.8)`. -/
def signedArclength (I : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.sign t * ∫ s in (0 : ℝ)..|t|, Real.sqrt (I s)

/-- The fundamental theorem of calculus for a germ continuous near `0`. -/
theorem eventually_hasDerivAt_primitiveAtZero_of_continuousAt {f : ℝ → ℝ}
    (hf : ∀ᶠ t in 𝓝 0, ContinuousAt f t) :
    ∀ᶠ x in 𝓝 0, HasDerivAt (primitiveAtZero f) (f x) x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hf
  have hcont : ContinuousOn f (Metric.ball 0 δ) := fun t ht =>
    (hball (by simpa [Metric.mem_ball] using ht)).continuousWithinAt
  filter_upwards [Metric.ball_mem_nhds 0 hδ] with x hx
  have hsub : uIcc 0 x ⊆ Metric.ball 0 δ := fun t ht => by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
    exact (abs_le_abs_of_mem_uIcc_zero ht).trans_lt hx
  exact intervalIntegral.integral_hasDerivAt_right (hcont.mono hsub).intervalIntegrable
    (hcont.stronglyMeasurableAtFilter Metric.isOpen_ball x hx)
    (hcont.continuousAt (Metric.isOpen_ball.mem_nhds hx))

/-- `A = ∫₀ᵗ g` near `0` for an even germ `g` with `√I = g` near `0`. -/
theorem signedArclength_eventuallyEq {g : ℝ → ℝ} (hsqrt : ∀ᶠ s in 𝓝 0, Real.sqrt (I s) = g s)
    (heven : ∀ᶠ s in 𝓝 0, g (-s) = g s) : signedArclength I =ᶠ[𝓝 0] primitiveAtZero g := by
  have habs : Tendsto (fun t : ℝ => |t|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs (G := ℝ)).tendsto 0
  filter_upwards [habs.eventually (eventually_forall_uIcc hsqrt), primitiveAtZero_neg_of_even heven]
    with t ht hodd
  have hint : ∫ s in (0 : ℝ)..|t|, Real.sqrt (I s) = primitiveAtZero g |t| :=
    intervalIntegral.integral_congr fun s hs => ht s hs
  rw [signedArclength, hint]
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · rw [Real.sign_of_neg hneg, abs_of_neg hneg, hodd]
    ring
  · simp [primitiveAtZero_zero]
  · rw [Real.sign_of_pos hpos, abs_of_pos hpos, one_mul]

namespace EvenPositiveResponse

/-- **Corollary 4.1, even half-order.**  The signed arclength is analytic and is a rank-one
oriented realization `(RP.5)`. -/
theorem signedArclength_of_even (hI : EvenPositiveResponse I k) (hk : Even k) :
    AnalyticAt ℝ (signedArclength I) 0 ∧
      ∃ ρ : OrientedRealization I ℝ, ρ.curve = signedArclength I := by
  obtain ⟨h, hh, -, hhpos, hheven, hsq⟩ := hI.exists_sqrt
  set q : ℝ → ℝ := fun t => t ^ k * h t
  have hq : AnalyticAt ℝ q 0 := (analyticAt_id.pow k).mul hh
  have hqeven : ∀ᶠ t in 𝓝 0, q (-t) = q t := by
    filter_upwards [hheven] with t ht
    simp only [q, ht, hk.neg_pow]
  have hsqrt : ∀ᶠ s in 𝓝 0, Real.sqrt (I s) = q s := by
    filter_upwards [hsq, hhpos] with s hs hpos
    rw [hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (hk.pow_nonneg s) hpos.le)]
  have hqpos : ∀ᶠ t in 𝓝[>] 0, 0 < q t := by
    filter_upwards [nhdsWithin_le_nhds hhpos, self_mem_nhdsWithin] with t ht ht0
    exact mul_pos (pow_pos ht0 k) ht
  have hA := signedArclength_eventuallyEq hsqrt hqeven
  obtain ⟨ρ, hρ⟩ := exists_lineRealization_of_sqrt (I := I) hq hsq hqeven hqpos
  refine ⟨(analyticAt_primitiveAtZero hq).congr hA.symm,
    ρ.congrCurve (signedArclength I) (hρ ▸ hA), rfl⟩

/-- **Corollary 4.1, odd half-order: the scalar arclength regularity wall.**  The signed
arclength is `Cᵏ` but not `C^{k+1}` at `0`. -/
theorem signedArclength_of_odd (hI : EvenPositiveResponse I k) (hk : Odd k) :
    ContDiffAt ℝ k (signedArclength I) 0 ∧
      ¬ ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (signedArclength I) 0 := by
  obtain ⟨h, hh, hh0, hhpos, hheven, hsq⟩ := hI.exists_sqrt
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk.pos
  have hkev : Even (k - 1) := by
    obtain ⟨j, hj⟩ := hk
    exact ⟨j, by omega⟩
  set w : ℝ → ℝ := fun t => t ^ (k - 1) * |t|
  set g : ℝ → ℝ := fun t => w t * h t
  have hw_abs : ∀ t : ℝ, w t = |t| ^ k := by
    intro t
    simp only [w]
    rw [← hkev.pow_abs, ← pow_succ, hk1]
  have hsqrt : ∀ᶠ s in 𝓝 0, Real.sqrt (I s) = g s := by
    filter_upwards [hsq, hhpos] with s hs hpos
    rw [hs, Real.sqrt_sq_eq_abs, abs_mul, abs_pow, abs_of_pos hpos]
    simp only [g, hw_abs]
  have hgeven : ∀ᶠ s in 𝓝 0, g (-s) = g s := by
    filter_upwards [hheven] with s hs
    simp only [g, hw_abs, abs_neg, hs]
  have hA := signedArclength_eventuallyEq hsqrt hgeven
  have hwC : ContDiff ℝ ((k - 1 : ℕ) : WithTop ℕ∞) w := contDiff_pow_mul_abs (k - 1)
  have hgC : ContDiffAt ℝ ((k - 1 : ℕ) : WithTop ℕ∞) g 0 := hwC.contDiffAt.mul hh.contDiffAt
  have hgcont : ∀ᶠ t in 𝓝 0, ContinuousAt g t :=
    hh.eventually_analyticAt.mono fun t ht =>
      (hwC.continuous.continuousAt).mul ht.continuousAt
  have hderiv := eventually_hasDerivAt_primitiveAtZero_of_continuousAt hgcont
  constructor
  · have hG : ContDiffAt ℝ (((k - 1 : ℕ) : WithTop ℕ∞) + 1) (primitiveAtZero g) 0 := by
      refine contDiffAt_succ_iff_hasFDerivAt.mpr
        ⟨fun x => ContinuousLinearMap.toSpanSingleton ℝ (g x),
          ⟨_, hderiv, fun x hx => hasDerivAt_iff_hasFDerivAt.mp hx⟩, ?_⟩
      refine (ContDiffAt.smulRight (contDiffAt_const (c := (1 : StrongDual ℝ ℝ))) hgC
        ).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
      ext
      simp
    have hcast : ((k - 1 : ℕ) : WithTop ℕ∞) + 1 = (k : WithTop ℕ∞) := by
      rw [← hk1]
      norm_cast
    rw [hcast] at hG
    exact hG.congr_of_eventuallyEq hA
  · intro hC
    have hG : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (primitiveAtZero g) 0 :=
      hC.congr_of_eventuallyEq hA.symm
    have hle : ((k : ℕ) : WithTop ℕ∞) + 1 ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by norm_cast
    have hD : ContDiffAt ℝ (k : WithTop ℕ∞) (deriv (primitiveAtZero g)) 0 :=
      (hG.fderiv_right hle).clm_apply contDiffAt_const
    have hDg : deriv (primitiveAtZero g) =ᶠ[𝓝 0] g := by
      filter_upwards [hderiv] with t ht
      exact ht.deriv
    have hgk : ContDiffAt ℝ (k : WithTop ℕ∞) g 0 := hD.congr_of_eventuallyEq hDg.symm
    have hwk : ContDiffAt ℝ (k : WithTop ℕ∞) w 0 := by
      have hquot := hgk.div hh.contDiffAt hh0.ne'
      refine hquot.congr_of_eventuallyEq ?_
      filter_upwards [hhpos] with t ht
      simp only [g, Pi.div_apply]
      field_simp
    rw [← hk1] at hwk
    exact not_contDiffAt_pow_mul_abs (k - 1) hwk

end EvenPositiveResponse

/-! ### The statistical fold -/

/-- `Θ(t) = Θ(0) + ∫₀ᵗ Θ'` near `0` for an analytic germ. -/
theorem eventually_eq_add_primitive_deriv {Θ : ℝ → ℝ} (hΘ : AnalyticAt ℝ Θ 0) :
    ∀ᶠ t in 𝓝 0, Θ t = Θ 0 + primitiveAtZero (deriv Θ) t := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hΘ.eventually_analyticAt
  filter_upwards [Metric.ball_mem_nhds 0 hδ] with t ht
  have hsub : ∀ x ∈ uIcc 0 t, AnalyticAt ℝ Θ x := fun x hx => hball (by
    rw [Real.dist_eq, sub_zero]
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact (abs_le_abs_of_mem_uIcc_zero hx).trans_lt ht)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => (hsub x hx).differentiableAt.hasDerivAt)
    (ContinuousOn.intervalIntegrable fun x hx => (hsub x hx).deriv.continuousAt.continuousWithinAt)
  change primitiveAtZero (deriv Θ) t = Θ t - Θ 0 at h
  linarith

/-- The local Bernoulli family `p(t) = (1 + sin Θ(t))/2` `(RP.10)`. -/
def bernoulliFamily (Θ : ℝ → ℝ) (t : ℝ) : ℝ := (1 + Real.sin (Θ t)) / 2

theorem hasDerivAt_bernoulliFamily {Θ : ℝ → ℝ} {θ' t : ℝ} (hΘ : HasDerivAt Θ θ' t) :
    HasDerivAt (bernoulliFamily Θ) (Real.cos (Θ t) * θ' / 2) t :=
  (hΘ.sin.const_add 1).div_const 2

/-- **`(RP.11)`: the Fisher information of the Bernoulli family is `Θ'²`** (for `|Θ| < π/2`). -/
theorem bernoulliFamily_fisher {Θ : ℝ → ℝ} {θ' t : ℝ} (hΘ : HasDerivAt Θ θ' t)
    (hb : |Θ t| < Real.pi / 2) :
    deriv (bernoulliFamily Θ) t ^ 2 /
        (bernoulliFamily Θ t * (1 - bernoulliFamily Θ t)) = θ' ^ 2 := by
  rw [(hasDerivAt_bernoulliFamily hΘ).deriv, bernoulliFamily]
  have hc : 0 < Real.cos (Θ t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le (Θ t)], by linarith [le_abs_self (Θ t)]⟩
  have hden : (1 + Real.sin (Θ t)) / 2 * (1 - (1 + Real.sin (Θ t)) / 2) =
      Real.cos (Θ t) ^ 2 / 4 := by
    linear_combination (-1 / 4 : ℝ) * Real.sin_sq_add_cos_sq (Θ t)
  rw [hden]
  field_simp
  ring

namespace EvenPositiveResponse

/-- **`(RP.11)`.**  For an analytic `Θ` with `Θ'² = I` and `|Θ| < π/2`, the Bernoulli Fisher
information is the response. -/
theorem bernoulli_fisher_eq (_hI : EvenPositiveResponse I k) {Θ : ℝ → ℝ} (hΘ : AnalyticAt ℝ Θ 0)
    (hsq : ∀ᶠ t in 𝓝 0, deriv Θ t ^ 2 = I t) (hb : ∀ᶠ t in 𝓝 0, |Θ t| < Real.pi / 2) :
    ∀ᶠ t in 𝓝 0, deriv (bernoulliFamily Θ) t ^ 2 /
      (bernoulliFamily Θ t * (1 - bernoulliFamily Θ t)) = I t := by
  filter_upwards [hΘ.eventually_analyticAt, hsq, hb] with t ht hst hbt
  rw [bernoulliFamily_fisher ht.differentiableAt.hasDerivAt hbt, hst]

/-- **§8, attack 1: a scalar analytic square root folds at odd half-order.**  For odd `k`, every
analytic `Θ` with `Θ'² = I` is even near `0`: `Θ'` is `±q` and `q` is odd. -/
theorem even_of_sq_deriv (hI : EvenPositiveResponse I k) (hk : Odd k) {Θ : ℝ → ℝ}
    (hΘ : AnalyticAt ℝ Θ 0) (hsq : ∀ᶠ t in 𝓝 0, deriv Θ t ^ 2 = I t) :
    ∀ᶠ t in 𝓝 0, Θ (-t) = Θ t := by
  obtain ⟨q, hq, hqsq, hqpar, -⟩ := hI.exists_sqrt'
  have hqodd : ∀ᶠ t in 𝓝 0, q (-t) = -q t := by
    filter_upwards [hqpar] with t ht
    rw [ht, hk.neg_one_pow, neg_one_mul]
  have hroot : ∀ᶠ t in 𝓝 0, deriv Θ t ^ 2 = q t ^ 2 := by
    filter_upwards [hsq, hqsq] with t h1 h2
    rw [h1, h2]
  have hdodd : ∀ᶠ t in 𝓝 0, deriv Θ (-t) = -deriv Θ t := by
    rcases eventuallyEq_or_eventuallyEq_neg_of_sq_eq hΘ.deriv hq hroot with h | h
    · filter_upwards [h, eventually_neg_of_eventually h, hqodd] with t h1 h2 h3
      rw [h2, h3, h1]
    · filter_upwards [h, eventually_neg_of_eventually h, hqodd] with t h1 h2 h3
      rw [h2, h3, h1]
  have hftc := eventually_eq_add_primitive_deriv hΘ
  filter_upwards [hftc, eventually_neg_of_eventually hftc, primitiveAtZero_neg_of_odd hdodd]
    with t h1 h2 h3
  rw [h2, h1, h3]

/-- **`(RP.12)`–`(RP.13)`: the statistical fold and the common-recovery no-go.**  For odd `k` the
Bernoulli family of a scalar analytic square root is folded, `p(t) = p(-t)`, so every
parameter-independent recovery `Φ` of the law returns the same output on both reflection sides. -/
theorem bernoulli_fold (hI : EvenPositiveResponse I k) (hk : Odd k) {Θ : ℝ → ℝ}
    (hΘ : AnalyticAt ℝ Θ 0) (hsq : ∀ᶠ t in 𝓝 0, deriv Θ t ^ 2 = I t) {β : Type*} (Φ : ℝ → β) :
    ∀ᶠ t in 𝓝 0, Φ (bernoulliFamily Θ t) = Φ (bernoulliFamily Θ (-t)) := by
  filter_upwards [hI.even_of_sq_deriv hk hΘ hsq] with t ht
  rw [bernoulliFamily, bernoulliFamily, ht]

end EvenPositiveResponse

/-! ### Divergence germs determine the response -/

/-- The binary Kullback–Leibler divergence `KL(Ber(a) ‖ Ber(b))`. -/
def binaryKL (a b : ℝ) : ℝ := a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

/-- **The Fisher information is the Hessian of the divergence germ**:
`∂²ₛ KL(p(t) ‖ p(s))|_{s=t} = p'(t)² / (p(t)(1 - p(t)))`. -/
theorem hasDerivAt_deriv_binaryKL {p : ℝ → ℝ} {t : ℝ}
    (hp : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ p s) (hp2 : DifferentiableAt ℝ (deriv p) t)
    (h0 : 0 < p t) (h1 : p t < 1) :
    HasDerivAt (deriv fun s => binaryKL (p t) (p s)) (deriv p t ^ 2 / (p t * (1 - p t))) t := by
  set a := p t with ha
  have hpc : ContinuousAt p t := hp.self_of_nhds.continuousAt
  have hpos : ∀ᶠ s in 𝓝 t, 0 < p s := hpc.eventually (lt_mem_nhds h0)
  have hlt1 : ∀ᶠ s in 𝓝 t, p s < 1 := hpc.eventually (gt_mem_nhds h1)
  have ha0 : a ≠ 0 := h0.ne'
  have ha1 : 1 - a ≠ 0 := by linarith
  set ψ : ℝ → ℝ := fun s => (1 - a) / (1 - p s) - a / p s
  have hKL : (deriv fun s => binaryKL a (p s)) =ᶠ[𝓝 t] fun s => deriv p s * ψ s := by
    filter_upwards [hp, hpos, hlt1] with s hds h0s h1s
    have hd := hds.hasDerivAt
    have hp0 : p s ≠ 0 := h0s.ne'
    have hp1 : 1 - p s ≠ 0 := by linarith
    have hq1 : HasDerivAt (fun s => a / p s) ((0 * p s - a * deriv p s) / p s ^ 2) s :=
      (hasDerivAt_const s a).div hd hp0
    have hq2 : HasDerivAt (fun s => (1 - a) / (1 - p s))
        ((0 * (1 - p s) - (1 - a) * (0 - deriv p s)) / (1 - p s) ^ 2) s :=
      (hasDerivAt_const s (1 - a)).div ((hasDerivAt_const s 1).sub hd) hp1
    have hl1 := (hq1.log (div_ne_zero ha0 hp0)).const_mul a
    have hl2 := (hq2.log (div_ne_zero ha1 hp1)).const_mul (1 - a)
    have hsum := hl1.add hl2
    refine hsum.deriv.trans ?_
    simp only [ψ]
    field_simp
    ring
  have hψ : HasDerivAt ψ ((1 - a) * deriv p t / (1 - a) ^ 2 + a * deriv p t / a ^ 2) t := by
    have hd := (hp.self_of_nhds).hasDerivAt
    have hq1 : HasDerivAt (fun s => a / p s) ((0 * p t - a * deriv p t) / p t ^ 2) t :=
      (hasDerivAt_const t a).div hd h0.ne'
    have hq2 : HasDerivAt (fun s => (1 - a) / (1 - p s))
        ((0 * (1 - p t) - (1 - a) * (0 - deriv p t)) / (1 - p t) ^ 2) t :=
      (hasDerivAt_const t (1 - a)).div ((hasDerivAt_const t 1).sub hd) (by linarith)
    refine (hq2.sub hq1).congr_deriv ?_
    rw [← ha]
    ring
  have hψt : ψ t = 0 := by
    simp only [ψ, ← ha]
    rw [div_self ha1, div_self ha0, sub_self]
  have hmain := hp2.hasDerivAt.mul hψ
  rw [hψt, mul_zero, zero_add] at hmain
  refine (hmain.congr_of_eventuallyEq hKL).congr_deriv ?_
  field_simp
  ring

/-- **Exact recovery preserves the Fisher response**: Bernoulli families with the same divergence
germ at `t` have the same Fisher information at `t`. -/
theorem fisher_eq_of_binaryKL_eventuallyEq {p p' : ℝ → ℝ} {t : ℝ}
    (hp : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ p s) (hp2 : DifferentiableAt ℝ (deriv p) t)
    (h0 : 0 < p t) (h1 : p t < 1)
    (hp' : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ p' s) (hp2' : DifferentiableAt ℝ (deriv p') t)
    (h0' : 0 < p' t) (h1' : p' t < 1)
    (hdiv : (fun s => binaryKL (p t) (p s)) =ᶠ[𝓝 t] fun s => binaryKL (p' t) (p' s)) :
    deriv p t ^ 2 / (p t * (1 - p t)) = deriv p' t ^ 2 / (p' t * (1 - p' t)) :=
  (hasDerivAt_deriv_binaryKL hp hp2 h0 h1).unique
    ((hasDerivAt_deriv_binaryKL hp' hp2' h0' h1').congr_of_eventuallyEq hdiv.deriv)

/-- **Common recovery is information-neutral.**  If two analytic Bernoulli families with Fisher
informations `I` and `J` have the same divergence germ at every parameter near `0`, then `I = J`
near `0`; hence they have the same half-order and the same oriented rank. -/
theorem recovery_preserves_response {p p' J : ℝ → ℝ} (hp : AnalyticAt ℝ p 0)
    (hp' : AnalyticAt ℝ p' 0) (hrange : ∀ᶠ t in 𝓝 0, 0 < p t ∧ p t < 1 ∧ 0 < p' t ∧ p' t < 1)
    (hI : ∀ᶠ t in 𝓝 0, deriv p t ^ 2 / (p t * (1 - p t)) = I t)
    (hJ : ∀ᶠ t in 𝓝 0, deriv p' t ^ 2 / (p' t * (1 - p' t)) = J t)
    (hdiv : ∀ᶠ t in 𝓝 0,
      (fun s => binaryKL (p t) (p s)) =ᶠ[𝓝 t] fun s => binaryKL (p' t) (p' s)) :
    I =ᶠ[𝓝 0] J ∧ analyticOrderAt I 0 = analyticOrderAt J 0 ∧
      orientedRank I = orientedRank J := by
  have hIJ : I =ᶠ[𝓝 0] J := by
    filter_upwards [hp.eventually_analyticAt, hp'.eventually_analyticAt, hrange, hI, hJ, hdiv]
      with t ha ha' hr hIt hJt hdt
    rw [← hIt, ← hJt]
    exact fisher_eq_of_binaryKL_eventuallyEq
      (ha.eventually_analyticAt.mono fun s hs => hs.differentiableAt) ha.deriv.differentiableAt
      hr.1 hr.2.1 (ha'.eventually_analyticAt.mono fun s hs => hs.differentiableAt)
      ha'.deriv.differentiableAt hr.2.2.1 hr.2.2.2 hdt
  exact ⟨hIJ, analyticOrderAt_congr hIJ, orientedRank_congr hIJ⟩

end GaloisForLFunctions.HTGeometry
