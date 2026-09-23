import GaloisForLFunctions.RHTower.XiCTaylorSignedFourAtomTransverseOrbitRigidity
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# Non-atomic Route-J profiles require three source sign changes

The analytic core treats reciprocal radial rows: after positive reweighting they reduce to
orthogonality against `1`, `t`, and `tanh(c t / 2)`.  Strict concavity of the last function gives
a sharp chord obstruction to two sign changes.

The source theorem below restores the physical Fourier phase omitted by that radial core.
Imaginary-value and real-derivative cancellation at two reflected fibres reduces the actual
continuum density to the same system after reweighting by `cosh(c t) sin(u t)`.  Thus the relevant
invariant is sign complexity of the phase-weighted density `sin(u t) h(t)`, not of `h` alone.
Support may be unbounded and the atomless reference measure is arbitrary.
-/

open Real Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

def routeJReflectionRatio (c t : ℝ) : ℝ :=
  (Real.exp (c * t) - 1) / (Real.exp (c * t) + 1)

theorem hasDerivAt_routeJReflectionRatio (c t : ℝ) :
    HasDerivAt (routeJReflectionRatio c)
      (2 * c * Real.exp (c * t) / (Real.exp (c * t) + 1) ^ (2 : ℕ)) t := by
  have hlin : HasDerivAt (fun x : ℝ => c * x) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have he : HasDerivAt (fun x : ℝ => Real.exp (c * x))
      (Real.exp (c * t) * c) t :=
    (Real.hasDerivAt_exp (c * t)).comp t hlin
  have hden : Real.exp (c * t) + 1 ≠ 0 := by positivity
  have hraw := (he.sub_const 1).div (he.add_const 1) hden
  simpa only [routeJReflectionRatio] using!
    hraw.congr_deriv (by
      field_simp [hden]
      ring)

theorem deriv_routeJReflectionRatio (c t : ℝ) :
    deriv (routeJReflectionRatio c) t =
      2 * c * Real.exp (c * t) / (Real.exp (c * t) + 1) ^ (2 : ℕ) :=
  (hasDerivAt_routeJReflectionRatio c t).deriv

theorem hasDerivAt_routeJReflectionRatio_derivFormula (c t : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        2 * c * Real.exp (c * x) / (Real.exp (c * x) + 1) ^ (2 : ℕ))
      (2 * c ^ (2 : ℕ) * Real.exp (c * t) * (1 - Real.exp (c * t)) /
        (Real.exp (c * t) + 1) ^ (3 : ℕ)) t := by
  have hlin : HasDerivAt (fun x : ℝ => c * x) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have he : HasDerivAt (fun x : ℝ => Real.exp (c * x))
      (Real.exp (c * t) * c) t :=
    (Real.hasDerivAt_exp (c * t)).comp t hlin
  have hnum := he.const_mul (2 * c)
  have hden0 : Real.exp (c * t) + 1 ≠ 0 := by positivity
  have hden := (he.add_const 1).pow 2
  have hraw := hnum.div hden (pow_ne_zero 2 hden0)
  simpa only [Pi.pow_apply] using!
    hraw.congr_deriv (by
      norm_num [Pi.pow_apply]
      change
        (2 * c * (Real.exp (c * t) * c) *
              (Real.exp (c * t) + 1) ^ (2 : ℕ) -
            2 * c * Real.exp (c * t) *
              (2 * (Real.exp (c * t) + 1) *
                (Real.exp (c * t) * c))) /
            ((Real.exp (c * t) + 1) ^ (2 : ℕ)) ^ (2 : ℕ) =
          2 * c ^ (2 : ℕ) * Real.exp (c * t) *
              (1 - Real.exp (c * t)) /
            (Real.exp (c * t) + 1) ^ (3 : ℕ)
      field_simp [hden0]
      ring)

theorem routeJReflectionRatio_secondDeriv (c t : ℝ) :
    (deriv^[2]) (routeJReflectionRatio c) t =
      2 * c ^ (2 : ℕ) * Real.exp (c * t) * (1 - Real.exp (c * t)) /
        (Real.exp (c * t) + 1) ^ (3 : ℕ) := by
  change deriv (deriv (routeJReflectionRatio c)) t = _
  rw [show deriv (routeJReflectionRatio c) =
      (fun x : ℝ =>
        2 * c * Real.exp (c * x) / (Real.exp (c * x) + 1) ^ (2 : ℕ)) by
    funext x
    exact deriv_routeJReflectionRatio c x]
  exact (hasDerivAt_routeJReflectionRatio_derivFormula c t).deriv

theorem strictConcaveOn_routeJReflectionRatio {c : ℝ} (hc : 0 < c) :
    StrictConcaveOn ℝ (Ioi 0) (routeJReflectionRatio c) := by
  have hcont : Continuous (routeJReflectionRatio c) := by
    unfold routeJReflectionRatio
    apply Continuous.div
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).sub continuous_const)
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).add continuous_const)
    intro x
    exact ne_of_gt (add_pos_of_pos_of_nonneg (Real.exp_pos _) zero_le_one)
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 0)
    hcont.continuousOn
  intro t ht
  rw [routeJReflectionRatio_secondDeriv]
  have hct : 0 < c * t := mul_pos hc ht
  have hexp : 1 < Real.exp (c * t) := by simpa using Real.exp_lt_exp.mpr hct
  have hlead : 0 < 2 * c ^ (2 : ℕ) * Real.exp (c * t) := by
    exact mul_pos (mul_pos (by positivity) (sq_pos_of_pos hc)) (Real.exp_pos _)
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hlead (by linarith))
    (by positivity)

def routeJReflectionChordResidual (c a b t : ℝ) : ℝ :=
  routeJReflectionRatio c t - routeJReflectionRatio c a -
    ((routeJReflectionRatio c b - routeJReflectionRatio c a) / (b - a)) *
      (t - a)

@[simp] theorem routeJReflectionChordResidual_left (c a b : ℝ) :
    routeJReflectionChordResidual c a b a = 0 := by
  simp [routeJReflectionChordResidual]

@[simp] theorem routeJReflectionChordResidual_right
    {c a b : ℝ} (hab : a ≠ b) :
    routeJReflectionChordResidual c a b b = 0 := by
  unfold routeJReflectionChordResidual
  field_simp [hab]
  ring

theorem routeJReflectionChordResidual_pos_between
    {c a b t : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hat : a < t) (htb : t < b) :
    0 < routeJReflectionChordResidual c a b t := by
  have hf := strictConcaveOn_routeJReflectionRatio hc
  have hsec := hf.secant_strict_mono
    (a := a) (x := t) (y := b)
    (mem_Ioi.mpr ha) (mem_Ioi.mpr (ha.trans hat))
    (mem_Ioi.mpr (ha.trans (hat.trans htb)))
    (ne_of_gt hat) (ne_of_gt (hat.trans htb)) htb
  have hpos : 0 < t - a := sub_pos.mpr hat
  have hmul := mul_lt_mul_of_pos_right hsec hpos
  have hcancel :
      (routeJReflectionRatio c t - routeJReflectionRatio c a) /
          (t - a) * (t - a) =
        routeJReflectionRatio c t - routeJReflectionRatio c a :=
    div_mul_cancel₀ _ hpos.ne'
  rw [hcancel] at hmul
  unfold routeJReflectionChordResidual
  linarith

theorem routeJReflectionChordResidual_neg_left
    {c a b t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hta : t < a) (hab : a < b) :
    routeJReflectionChordResidual c a b t < 0 := by
  have hf := strictConcaveOn_routeJReflectionRatio hc
  have hsec := hf.secant_strict_mono
    (a := a) (x := t) (y := b)
    (mem_Ioi.mpr (ht.trans hta)) (mem_Ioi.mpr ht)
    (mem_Ioi.mpr (ht.trans (hta.trans hab)))
    (ne_of_lt hta) (ne_of_gt hab) (hta.trans hab)
  have hneg : t - a < 0 := sub_neg.mpr hta
  have hmul := mul_lt_mul_of_neg_right hsec hneg
  have hcancel :
      (routeJReflectionRatio c t - routeJReflectionRatio c a) /
          (t - a) * (t - a) =
        routeJReflectionRatio c t - routeJReflectionRatio c a :=
    div_mul_cancel₀ _ hneg.ne
  rw [hcancel] at hmul
  unfold routeJReflectionChordResidual
  linarith

theorem routeJReflectionChordResidual_neg_right
    {c a b t : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hab : a < b) (hbt : b < t) :
    routeJReflectionChordResidual c a b t < 0 := by
  have hf := strictConcaveOn_routeJReflectionRatio hc
  have hsec := hf.secant_strict_mono
    (a := a) (x := b) (y := t)
    (mem_Ioi.mpr ha) (mem_Ioi.mpr (ha.trans hab))
    (mem_Ioi.mpr (ha.trans (hab.trans hbt)))
    (ne_of_gt hab) (ne_of_gt (hab.trans hbt)) hbt
  have hpos : 0 < t - a := sub_pos.mpr (hab.trans hbt)
  have hmul := mul_lt_mul_of_pos_right hsec hpos
  have hcancel :
      (routeJReflectionRatio c t - routeJReflectionRatio c a) /
          (t - a) * (t - a) =
        routeJReflectionRatio c t - routeJReflectionRatio c a :=
    div_mul_cancel₀ _ hpos.ne'
  rw [hcancel] at hmul
  unfold routeJReflectionChordResidual
  linarith

/-- A non-atomic signed density satisfying the three reciprocal radial moment rows cannot have at
most two sign changes.  This is the analytic core of the physical phase-weighted theorem below,
not by itself a model of arbitrary continuum physical time.  The compact hypothesis
`0 ≤ (t-a)(t-b)v(t)` is one of the two alternating orientations; applying the theorem to `-v`
handles the other. -/
theorem routeJ_twoSignChange_reflectionMoments_ae_zero
    {μ : Measure ℝ} [NullSingletonClass μ]
    {v : ℝ → ℝ} {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hsupport : ∀ᵐ t ∂μ, v t ≠ 0 → 0 < t)
    (hpattern : ∀ᵐ t ∂μ, 0 ≤ (t - a) * (t - b) * v t)
    (hv : Integrable v μ)
    (htv : Integrable (fun t => t * v t) μ)
    (hgv : Integrable (fun t => routeJReflectionRatio c t * v t) μ)
    (hv0 : ∫ t, v t ∂μ = 0)
    (htv0 : ∫ t, t * v t ∂μ = 0)
    (hgv0 : ∫ t, routeJReflectionRatio c t * v t ∂μ = 0) :
    v =ᵐ[μ] 0 := by
  let m : ℝ :=
    (routeJReflectionRatio c b - routeJReflectionRatio c a) / (b - a)
  let L : ℝ → ℝ := routeJReflectionChordResidual c a b
  have htvSub : Integrable (fun t => (t - a) * v t) μ := by
    have hraw := htv.sub (hv.const_mul a)
    exact hraw.congr (Eventually.of_forall fun t => by
      simp only [Pi.sub_apply]
      ring)
  have hLInt : Integrable (fun t => L t * v t) μ := by
    have hraw :=
      (hgv.sub (hv.const_mul (routeJReflectionRatio c a))).sub
        (htvSub.const_mul m)
    convert hraw using 1
    funext t
    dsimp [L, m]
    unfold routeJReflectionChordResidual
    ring
  have hLZero : ∫ t, L t * v t ∂μ = 0 := by
    calc
      ∫ t, L t * v t ∂μ =
          ∫ t, (routeJReflectionRatio c t * v t -
              routeJReflectionRatio c a * v t) -
            m * ((t - a) * v t) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              dsimp [L, m]
              unfold routeJReflectionChordResidual
              ring
      _ =
          (∫ t, routeJReflectionRatio c t * v t -
              routeJReflectionRatio c a * v t ∂μ) -
            (∫ t, m * ((t - a) * v t) ∂μ) := by
              simpa only [Pi.sub_apply] using
                integral_sub
                  (hgv.sub (hv.const_mul (routeJReflectionRatio c a)))
                  (htvSub.const_mul m)
      _ =
          ((∫ t, routeJReflectionRatio c t * v t ∂μ) -
              (∫ t, routeJReflectionRatio c a * v t ∂μ)) -
            (∫ t, m * ((t - a) * v t) ∂μ) := by
              rw [integral_sub hgv
                (hv.const_mul (routeJReflectionRatio c a))]
      _ =
          (∫ t, routeJReflectionRatio c t * v t ∂μ) -
              routeJReflectionRatio c a * (∫ t, v t ∂μ) -
            m * (∫ t, (t - a) * v t ∂μ) := by
              rw [integral_const_mul, integral_const_mul]
      _ =
          (∫ t, routeJReflectionRatio c t * v t ∂μ) -
              routeJReflectionRatio c a * (∫ t, v t ∂μ) -
            m * ((∫ t, t * v t ∂μ) - a * (∫ t, v t ∂μ)) := by
              rw [show (∫ t, (t - a) * v t ∂μ) =
                  (∫ t, t * v t ∂μ) - a * (∫ t, v t ∂μ) by
                calc
                  ∫ t, (t - a) * v t ∂μ =
                      ∫ t, t * v t - a * v t ∂μ := by
                        apply integral_congr_ae
                        filter_upwards [] with t
                        ring
                  _ = _ := by
                    rw [integral_sub htv (hv.const_mul a),
                      integral_const_mul]]
      _ = 0 := by rw [hv0, htv0, hgv0]; ring
  have hLNonpos : ∀ᵐ t ∂μ, L t * v t ≤ 0 := by
    filter_upwards [hsupport, hpattern] with t htSupport htPattern
    by_cases hvt : v t = 0
    · simp [hvt]
    have ht : 0 < t := htSupport hvt
    rcases lt_trichotomy t a with hta | hta | hat
    · have htb : t < b := hta.trans hab
      have hpoly : 0 < (t - a) * (t - b) :=
        mul_pos_of_neg_of_neg (sub_neg.mpr hta) (sub_neg.mpr htb)
      have hvNonneg : 0 ≤ v t :=
        nonneg_of_mul_nonneg_right htPattern hpoly
      exact mul_nonpos_of_nonpos_of_nonneg
        (routeJReflectionChordResidual_neg_left hc ht hta hab).le hvNonneg
    · subst t
      simp [L]
    · rcases lt_trichotomy t b with htb | htb | hbt
      · have hpoly : (t - a) * (t - b) < 0 :=
          mul_neg_of_pos_of_neg (sub_pos.mpr hat) (sub_neg.mpr htb)
        have hvNonpos : v t ≤ 0 :=
          nonpos_of_mul_nonneg_right htPattern hpoly
        exact mul_nonpos_of_nonneg_of_nonpos
          (routeJReflectionChordResidual_pos_between hc ha hat htb).le hvNonpos
      · subst t
        simp [L, hab.ne]
      · have hpoly : 0 < (t - a) * (t - b) :=
          mul_pos (sub_pos.mpr (hab.trans hbt)) (sub_pos.mpr hbt)
        have hvNonneg : 0 ≤ v t :=
          nonneg_of_mul_nonneg_right htPattern hpoly
        exact mul_nonpos_of_nonpos_of_nonneg
          (routeJReflectionChordResidual_neg_right hc ha hab hbt).le hvNonneg
  have hnegInt : Integrable (fun t => -(L t * v t)) μ := hLInt.neg
  have hnegZero : ∫ t, -(L t * v t) ∂μ = 0 := by
    rw [integral_neg, hLZero, neg_zero]
  have hprodZero : (fun t => L t * v t) =ᵐ[μ] 0 := by
    have h :=
      (integral_eq_zero_iff_of_nonneg_ae
        (hLNonpos.mono fun t ht => neg_nonneg.mpr ht) hnegInt).1 hnegZero
    filter_upwards [h] with t ht
    simpa only [Pi.zero_apply, neg_eq_zero] using ht
  filter_upwards [hprodZero, hsupport, μ.ae_ne a, μ.ae_ne b] with
      t hprod htSupport hta htb
  by_contra hvt
  have ht : 0 < t := htSupport hvt
  have hL : L t = 0 := (mul_eq_zero.mp hprod).resolve_right hvt
  rcases lt_trichotomy t a with hleft | heq | hright
  · exact (routeJReflectionChordResidual_neg_left hc ht hleft hab).ne hL
  · exact hta heq
  · rcases lt_trichotomy t b with hmid | heq | hfar
    · exact (routeJReflectionChordResidual_pos_between hc ha hright hmid).ne' hL
    · exact htb heq
    · exact (routeJReflectionChordResidual_neg_right hc ha hab hfar).ne hL

/-- Literal continuum value row at logarithmic damping parameter `q`. -/
def routeJContinuumLiteralValueIntegrand
    (q : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  h t * (1 - Real.exp (q * t))

/-- Literal continuum weighted-derivative row at logarithmic damping parameter `q`. -/
def routeJContinuumLiteralDerivativeIntegrand
    (q : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * h t * Real.exp (q * t)

theorem routeJContinuumLiteralValue_neg_sub_pos
    (c : ℝ) (h : ℝ → ℝ) (t : ℝ) :
    (routeJContinuumLiteralValueIntegrand (-c) h t -
        routeJContinuumLiteralValueIntegrand c h t) / 2 =
      Real.sinh (c * t) * h t := by
  rw [Real.sinh_eq]
  unfold routeJContinuumLiteralValueIntegrand
  ring

theorem routeJContinuumLiteralValue_pos_add_neg
    (c : ℝ) (h : ℝ → ℝ) (t : ℝ) :
    -(routeJContinuumLiteralValueIntegrand c h t +
        routeJContinuumLiteralValueIntegrand (-c) h t) / 2 =
      (Real.cosh (c * t) - 1) * h t := by
  rw [Real.cosh_eq]
  unfold routeJContinuumLiteralValueIntegrand
  ring

theorem routeJContinuumLiteralDerivative_pos_sub_neg
    (c : ℝ) (h : ℝ → ℝ) (t : ℝ) :
    (routeJContinuumLiteralDerivativeIntegrand c h t -
        routeJContinuumLiteralDerivativeIntegrand (-c) h t) / 2 =
      t * (Real.sinh (c * t) * h t) := by
  rw [Real.sinh_eq]
  unfold routeJContinuumLiteralDerivativeIntegrand
  ring

theorem routeJReflectionRatio_mul_sinh
    (c t : ℝ) :
    routeJReflectionRatio c t * Real.sinh (c * t) =
      Real.cosh (c * t) - 1 := by
  rw [Real.sinh_eq, Real.cosh_eq]
  unfold routeJReflectionRatio
  have he : Real.exp (c * t) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.exp_neg]
  field_simp [he]
  ring

/-- **Radial continuum sign-complexity obstruction.** A non-atomic, possibly unbounded, signed
radial profile satisfying both reciprocal value rows and equal reflected derivative charge is
zero whenever its density has at most two sign changes.  Physical continuum time also carries a
Fourier sine phase; see `routeJ_nonAtomicContinuum_sineRows_atMostTwoChanges_ae_zero`. -/
theorem routeJ_nonAtomicContinuum_twoSignChange_equalCharge_ae_zero
    {μ : Measure ℝ} [NullSingletonClass μ]
    {h : ℝ → ℝ} {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hsupport : ∀ᵐ t ∂μ, h t ≠ 0 → 0 < t)
    (hpattern : ∀ᵐ t ∂μ, 0 ≤ (t - a) * (t - b) * h t)
    (hVpos : Integrable (routeJContinuumLiteralValueIntegrand c h) μ)
    (hVneg : Integrable (routeJContinuumLiteralValueIntegrand (-c) h) μ)
    (hDpos : Integrable (routeJContinuumLiteralDerivativeIntegrand c h) μ)
    (hDneg : Integrable (routeJContinuumLiteralDerivativeIntegrand (-c) h) μ)
    (hVposZero : ∫ t, routeJContinuumLiteralValueIntegrand c h t ∂μ = 0)
    (hVnegZero : ∫ t, routeJContinuumLiteralValueIntegrand (-c) h t ∂μ = 0)
    (hDequal :
      (∫ t, routeJContinuumLiteralDerivativeIntegrand c h t ∂μ) =
        ∫ t, routeJContinuumLiteralDerivativeIntegrand (-c) h t ∂μ) :
    h =ᵐ[μ] 0 := by
  let v : ℝ → ℝ := fun t => Real.sinh (c * t) * h t
  have hv : Integrable v μ := by
    have hraw := (hVneg.sub hVpos).div_const 2
    exact hraw.congr (Eventually.of_forall fun t => by
      dsimp [v]
      simpa only [Pi.sub_apply] using
        routeJContinuumLiteralValue_neg_sub_pos c h t)
  have htv : Integrable (fun t => t * v t) μ := by
    have hraw := (hDpos.sub hDneg).div_const 2
    exact hraw.congr (Eventually.of_forall fun t => by
      dsimp [v]
      simpa only [Pi.sub_apply] using
        routeJContinuumLiteralDerivative_pos_sub_neg c h t)
  have heven : Integrable (fun t => (Real.cosh (c * t) - 1) * h t) μ := by
    have hraw := (hVpos.add hVneg).neg.div_const 2
    exact hraw.congr (Eventually.of_forall fun t => by
      simpa only [Pi.add_apply, Pi.neg_apply] using
        routeJContinuumLiteralValue_pos_add_neg c h t)
  have hgv : Integrable (fun t => routeJReflectionRatio c t * v t) μ := by
    exact heven.congr (Eventually.of_forall fun t => by
      dsimp [v]
      calc
        (Real.cosh (c * t) - 1) * h t =
            (routeJReflectionRatio c t * Real.sinh (c * t)) * h t := by
              rw [routeJReflectionRatio_mul_sinh]
        _ = routeJReflectionRatio c t * (Real.sinh (c * t) * h t) := by
              ring)
  have hv0 : ∫ t, v t ∂μ = 0 := by
    calc
      ∫ t, v t ∂μ =
          ∫ t, (routeJContinuumLiteralValueIntegrand (-c) h t -
            routeJContinuumLiteralValueIntegrand c h t) / 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              exact (routeJContinuumLiteralValue_neg_sub_pos c h t).symm
      _ = ((∫ t, routeJContinuumLiteralValueIntegrand (-c) h t ∂μ) -
            (∫ t, routeJContinuumLiteralValueIntegrand c h t ∂μ)) / 2 := by
              rw [integral_div, integral_sub hVneg hVpos]
      _ = 0 := by rw [hVnegZero, hVposZero]; ring
  have htv0 : ∫ t, t * v t ∂μ = 0 := by
    calc
      ∫ t, t * v t ∂μ =
          ∫ t, (routeJContinuumLiteralDerivativeIntegrand c h t -
            routeJContinuumLiteralDerivativeIntegrand (-c) h t) / 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              exact
                (routeJContinuumLiteralDerivative_pos_sub_neg c h t).symm
      _ = ((∫ t, routeJContinuumLiteralDerivativeIntegrand c h t ∂μ) -
            (∫ t, routeJContinuumLiteralDerivativeIntegrand (-c) h t ∂μ)) / 2 := by
              rw [integral_div, integral_sub hDpos hDneg]
      _ = 0 := by rw [hDequal]; ring
  have hgv0 : ∫ t, routeJReflectionRatio c t * v t ∂μ = 0 := by
    calc
      ∫ t, routeJReflectionRatio c t * v t ∂μ =
          ∫ t, (Real.cosh (c * t) - 1) * h t ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              dsimp [v]
              calc
                routeJReflectionRatio c t * (Real.sinh (c * t) * h t) =
                    (routeJReflectionRatio c t * Real.sinh (c * t)) * h t := by
                      ring
                _ = (Real.cosh (c * t) - 1) * h t := by
                      rw [routeJReflectionRatio_mul_sinh]
      _ =
          ∫ t, -(routeJContinuumLiteralValueIntegrand c h t +
            routeJContinuumLiteralValueIntegrand (-c) h t) / 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              exact
                (routeJContinuumLiteralValue_pos_add_neg c h t).symm
      _ = -((∫ t, routeJContinuumLiteralValueIntegrand c h t ∂μ) +
            (∫ t, routeJContinuumLiteralValueIntegrand (-c) h t ∂μ)) / 2 := by
              rw [integral_div, integral_neg,
                integral_add hVpos hVneg]
      _ = 0 := by rw [hVposZero, hVnegZero]; ring
  have hvSupport : ∀ᵐ t ∂μ, v t ≠ 0 → 0 < t := by
    filter_upwards [hsupport] with t ht hvt
    apply ht
    intro hht
    dsimp [v] at hvt
    rw [hht, mul_zero] at hvt
    exact hvt rfl
  have hvPattern : ∀ᵐ t ∂μ, 0 ≤ (t - a) * (t - b) * v t := by
    filter_upwards [hsupport, hpattern] with t ht hp
    by_cases hht : h t = 0
    · simp [v, hht]
    have htpos := ht hht
    have hsinh : 0 < Real.sinh (c * t) := Real.sinh_pos_iff.mpr (mul_pos hc htpos)
    dsimp [v]
    nlinarith [mul_nonneg hsinh.le hp]
  have hvZero :=
    routeJ_twoSignChange_reflectionMoments_ae_zero
      hc ha hab hvSupport hvPattern hv htv hgv hv0 htv0 hgv0
  filter_upwards [hvZero, hsupport] with t hvt ht
  by_contra hht
  have htpos := ht hht
  have hsinh : Real.sinh (c * t) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hc htpos)).ne'
  dsimp [v] at hvt
  exact hht ((mul_eq_zero.mp hvt).resolve_left hsinh)

/-- Orientation-free version: either alternating orientation with at most two sign changes forces
the non-atomic continuum profile to vanish. -/
theorem routeJ_nonAtomicContinuum_atMostTwoSignChanges_equalCharge_ae_zero
    {μ : Measure ℝ} [NullSingletonClass μ]
    {h : ℝ → ℝ} {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hsupport : ∀ᵐ t ∂μ, h t ≠ 0 → 0 < t)
    (hpattern :
      (∀ᵐ t ∂μ, 0 ≤ (t - a) * (t - b) * h t) ∨
        (∀ᵐ t ∂μ, (t - a) * (t - b) * h t ≤ 0))
    (hVpos : Integrable (routeJContinuumLiteralValueIntegrand c h) μ)
    (hVneg : Integrable (routeJContinuumLiteralValueIntegrand (-c) h) μ)
    (hDpos : Integrable (routeJContinuumLiteralDerivativeIntegrand c h) μ)
    (hDneg : Integrable (routeJContinuumLiteralDerivativeIntegrand (-c) h) μ)
    (hVposZero : ∫ t, routeJContinuumLiteralValueIntegrand c h t ∂μ = 0)
    (hVnegZero : ∫ t, routeJContinuumLiteralValueIntegrand (-c) h t ∂μ = 0)
    (hDequal :
      (∫ t, routeJContinuumLiteralDerivativeIntegrand c h t ∂μ) =
        ∫ t, routeJContinuumLiteralDerivativeIntegrand (-c) h t ∂μ) :
    h =ᵐ[μ] 0 := by
  rcases hpattern with hpattern | hpattern
  · exact routeJ_nonAtomicContinuum_twoSignChange_equalCharge_ae_zero
      hc ha hab hsupport hpattern hVpos hVneg hDpos hDneg
        hVposZero hVnegZero hDequal
  · let g : ℝ → ℝ := fun t => -h t
    have gsupport : ∀ᵐ t ∂μ, g t ≠ 0 → 0 < t := by
      filter_upwards [hsupport] with t ht hgt
      apply ht
      intro hht
      dsimp [g] at hgt
      rw [hht, neg_zero] at hgt
      exact hgt rfl
    have gpattern : ∀ᵐ t ∂μ, 0 ≤ (t - a) * (t - b) * g t := by
      filter_upwards [hpattern] with t ht
      dsimp [g]
      nlinarith
    have gVpos : Integrable (routeJContinuumLiteralValueIntegrand c g) μ := by
      exact hVpos.neg.congr (Eventually.of_forall fun t => by
        simp [g, routeJContinuumLiteralValueIntegrand])
    have gVneg : Integrable (routeJContinuumLiteralValueIntegrand (-c) g) μ := by
      exact hVneg.neg.congr (Eventually.of_forall fun t => by
        simp [g, routeJContinuumLiteralValueIntegrand])
    have gDpos : Integrable (routeJContinuumLiteralDerivativeIntegrand c g) μ := by
      exact hDpos.neg.congr (Eventually.of_forall fun t => by
        simp [g, routeJContinuumLiteralDerivativeIntegrand])
    have gDneg : Integrable (routeJContinuumLiteralDerivativeIntegrand (-c) g) μ := by
      exact hDneg.neg.congr (Eventually.of_forall fun t => by
        simp [g, routeJContinuumLiteralDerivativeIntegrand])
    have gVposZero :
        ∫ t, routeJContinuumLiteralValueIntegrand c g t ∂μ = 0 := by
      calc
        ∫ t, routeJContinuumLiteralValueIntegrand c g t ∂μ =
            ∫ t, -routeJContinuumLiteralValueIntegrand c h t ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              simp [g, routeJContinuumLiteralValueIntegrand]
        _ = 0 := by rw [integral_neg, hVposZero, neg_zero]
    have gVnegZero :
        ∫ t, routeJContinuumLiteralValueIntegrand (-c) g t ∂μ = 0 := by
      calc
        ∫ t, routeJContinuumLiteralValueIntegrand (-c) g t ∂μ =
            ∫ t, -routeJContinuumLiteralValueIntegrand (-c) h t ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              simp [g, routeJContinuumLiteralValueIntegrand]
        _ = 0 := by rw [integral_neg, hVnegZero, neg_zero]
    have gDequal :
        (∫ t, routeJContinuumLiteralDerivativeIntegrand c g t ∂μ) =
          ∫ t, routeJContinuumLiteralDerivativeIntegrand (-c) g t ∂μ := by
      calc
        ∫ t, routeJContinuumLiteralDerivativeIntegrand c g t ∂μ =
            -(∫ t, routeJContinuumLiteralDerivativeIntegrand c h t ∂μ) := by
              rw [← integral_neg]
              apply integral_congr_ae
              filter_upwards [] with t
              simp [g, routeJContinuumLiteralDerivativeIntegrand]
        _ = -(∫ t, routeJContinuumLiteralDerivativeIntegrand (-c) h t ∂μ) := by
              rw [hDequal]
        _ = ∫ t, routeJContinuumLiteralDerivativeIntegrand (-c) g t ∂μ := by
              rw [← integral_neg]
              apply integral_congr_ae
              filter_upwards [] with t
              simp [g, routeJContinuumLiteralDerivativeIntegrand]
    have hg :=
      routeJ_nonAtomicContinuum_twoSignChange_equalCharge_ae_zero
        hc ha hab gsupport gpattern gVpos gVneg gDpos gDneg
          gVposZero gVnegZero gDequal
    filter_upwards [hg] with t hgt
    dsimp [g] at hgt
    exact neg_eq_zero.mp hgt

/-! ## Actual complex-phase continuum source -/

/-- Imaginary-value row of an actual continuum Fourier--Laplace source at real frequency `u`
and radial exponent `q`. -/
def routeJContinuumSineValueIntegrand
    (q u : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  h t * Real.exp (q * t) * Real.sin (u * t)

/-- Real-derivative row of an actual continuum Fourier--Laplace source. -/
def routeJContinuumSineDerivativeIntegrand
    (q u : ℝ) (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * h t * Real.exp (q * t) * Real.sin (u * t)

theorem routeJContinuumSineValue_pos_add_neg
    (c u : ℝ) (h : ℝ → ℝ) (t : ℝ) :
    (routeJContinuumSineValueIntegrand c u h t +
        routeJContinuumSineValueIntegrand (-c) u h t) / 2 =
      Real.cosh (c * t) * Real.sin (u * t) * h t := by
  rw [Real.cosh_eq]
  unfold routeJContinuumSineValueIntegrand
  ring

theorem routeJContinuumSineValue_pos_sub_neg
    (c u : ℝ) (h : ℝ → ℝ) (t : ℝ) :
    (routeJContinuumSineValueIntegrand c u h t -
        routeJContinuumSineValueIntegrand (-c) u h t) / 2 =
      Real.sinh (c * t) * Real.sin (u * t) * h t := by
  rw [Real.sinh_eq]
  unfold routeJContinuumSineValueIntegrand
  ring

theorem routeJContinuumSineDerivative_pos_add_neg
    (c u : ℝ) (h : ℝ → ℝ) (t : ℝ) :
    (routeJContinuumSineDerivativeIntegrand c u h t +
        routeJContinuumSineDerivativeIntegrand (-c) u h t) / 2 =
      t * (Real.cosh (c * t) * Real.sin (u * t) * h t) := by
  rw [Real.cosh_eq]
  unfold routeJContinuumSineDerivativeIntegrand
  ring

theorem routeJReflectionRatio_two_mul_cosh
    (c t : ℝ) :
    routeJReflectionRatio (2 * c) t * Real.cosh (c * t) =
      Real.sinh (c * t) := by
  rw [Real.sinh_eq, Real.cosh_eq]
  unfold routeJReflectionRatio
  have he : Real.exp (c * t) ≠ 0 := (Real.exp_pos _).ne'
  rw [show (2 * c) * t = c * t + c * t by ring, Real.exp_add,
    Real.exp_neg]
  field_simp [he]

theorem routeJReflectionRatio_two_mul_cosh_sine
    (c u : ℝ) (h : ℝ → ℝ) (t : ℝ) :
    routeJReflectionRatio (2 * c) t *
        (Real.cosh (c * t) * Real.sin (u * t) * h t) =
      (routeJContinuumSineValueIntegrand c u h t -
        routeJContinuumSineValueIntegrand (-c) u h t) / 2 := by
  rw [show
    routeJReflectionRatio (2 * c) t *
        (Real.cosh (c * t) * Real.sin (u * t) * h t) =
      (routeJReflectionRatio (2 * c) t * Real.cosh (c * t)) *
        Real.sin (u * t) * h t by ring,
    routeJReflectionRatio_two_mul_cosh]
  exact (routeJContinuumSineValue_pos_sub_neg c u h t).symm

/-- **Actual complex-phase continuum obstruction.** The imaginary-value rows and
real-derivative rows at two reflected Fourier--Laplace fibres already force an atomless density
to vanish when its phase-weighted density `sin(u t) h(t)` has at most two sign changes.

The support may be unbounded.  The assumption excluding sine nodes is automatic for a
Lebesgue-absolutely-continuous density and is stated explicitly for an arbitrary atomless
reference measure. -/
theorem routeJ_nonAtomicContinuum_sineRows_atMostTwoChanges_ae_zero
    {μ : Measure ℝ} [NullSingletonClass μ]
    {h : ℝ → ℝ} {c u a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hab : a < b)
    (hsupport :
      ∀ᵐ t ∂μ, h t ≠ 0 → 0 < t ∧ Real.sin (u * t) ≠ 0)
    (hpattern :
      (∀ᵐ t ∂μ,
          0 ≤ (t - a) * (t - b) * (Real.sin (u * t) * h t)) ∨
        (∀ᵐ t ∂μ,
          (t - a) * (t - b) * (Real.sin (u * t) * h t) ≤ 0))
    (hVpos : Integrable (routeJContinuumSineValueIntegrand c u h) μ)
    (hVneg : Integrable (routeJContinuumSineValueIntegrand (-c) u h) μ)
    (hDpos : Integrable (routeJContinuumSineDerivativeIntegrand c u h) μ)
    (hDneg : Integrable (routeJContinuumSineDerivativeIntegrand (-c) u h) μ)
    (hVposZero :
      ∫ t, routeJContinuumSineValueIntegrand c u h t ∂μ = 0)
    (hVnegZero :
      ∫ t, routeJContinuumSineValueIntegrand (-c) u h t ∂μ = 0)
    (hDposZero :
      ∫ t, routeJContinuumSineDerivativeIntegrand c u h t ∂μ = 0)
    (hDnegZero :
      ∫ t, routeJContinuumSineDerivativeIntegrand (-c) u h t ∂μ = 0) :
    h =ᵐ[μ] 0 := by
  let v : ℝ → ℝ := fun t =>
    Real.cosh (c * t) * Real.sin (u * t) * h t
  have hv :
      Integrable v μ := by
    exact (hVpos.add hVneg).div_const 2 |>.congr
      (Eventually.of_forall fun t => by
        dsimp [v]
        exact routeJContinuumSineValue_pos_add_neg c u h t)
  have htv :
      Integrable (fun t => t * v t) μ := by
    exact (hDpos.add hDneg).div_const 2 |>.congr
      (Eventually.of_forall fun t => by
        dsimp [v]
        exact routeJContinuumSineDerivative_pos_add_neg c u h t)
  have hgv :
      Integrable (fun t => routeJReflectionRatio (2 * c) t * v t) μ := by
    exact (hVpos.sub hVneg).div_const 2 |>.congr
      (Eventually.of_forall fun t => by
        dsimp [v]
        exact (routeJReflectionRatio_two_mul_cosh_sine c u h t).symm)
  have hv0 : ∫ t, v t ∂μ = 0 := by
    calc
      ∫ t, v t ∂μ =
          ∫ t, (routeJContinuumSineValueIntegrand c u h t +
            routeJContinuumSineValueIntegrand (-c) u h t) / 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              exact (routeJContinuumSineValue_pos_add_neg c u h t).symm
      _ = ((∫ t, routeJContinuumSineValueIntegrand c u h t ∂μ) +
            ∫ t, routeJContinuumSineValueIntegrand (-c) u h t ∂μ) / 2 := by
              rw [integral_div, integral_add hVpos hVneg]
      _ = 0 := by rw [hVposZero, hVnegZero]; norm_num
  have htv0 : ∫ t, t * v t ∂μ = 0 := by
    calc
      ∫ t, t * v t ∂μ =
          ∫ t, (routeJContinuumSineDerivativeIntegrand c u h t +
            routeJContinuumSineDerivativeIntegrand (-c) u h t) / 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              exact (routeJContinuumSineDerivative_pos_add_neg c u h t).symm
      _ = ((∫ t, routeJContinuumSineDerivativeIntegrand c u h t ∂μ) +
            ∫ t, routeJContinuumSineDerivativeIntegrand (-c) u h t ∂μ) / 2 := by
              rw [integral_div, integral_add hDpos hDneg]
      _ = 0 := by rw [hDposZero, hDnegZero]; norm_num
  have hgv0 :
      ∫ t, routeJReflectionRatio (2 * c) t * v t ∂μ = 0 := by
    calc
      ∫ t, routeJReflectionRatio (2 * c) t * v t ∂μ =
          ∫ t, (routeJContinuumSineValueIntegrand c u h t -
            routeJContinuumSineValueIntegrand (-c) u h t) / 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              dsimp [v]
              exact routeJReflectionRatio_two_mul_cosh_sine c u h t
      _ = ((∫ t, routeJContinuumSineValueIntegrand c u h t ∂μ) -
            ∫ t, routeJContinuumSineValueIntegrand (-c) u h t ∂μ) / 2 := by
              rw [integral_div, integral_sub hVpos hVneg]
      _ = 0 := by rw [hVposZero, hVnegZero]; norm_num
  have hvsupport : ∀ᵐ t ∂μ, v t ≠ 0 → 0 < t := by
    filter_upwards [hsupport] with t ht hvt
    exact (ht (by
      intro hht
      dsimp [v] at hvt
      rw [hht, mul_zero] at hvt
      exact hvt rfl)).1
  have finish (hvzero : v =ᵐ[μ] 0) : h =ᵐ[μ] 0 := by
    filter_upwards [hvzero, hsupport] with t hvt ht
    by_contra hht
    have hphase := (ht hht).2
    dsimp [v] at hvt
    rcases mul_eq_zero.mp hvt with hleft | hhzero
    · rcases mul_eq_zero.mp hleft with hcosh | hsin
      · exact (Real.cosh_pos (c * t)).ne' hcosh
      · exact hphase hsin
    · exact hht hhzero
  rcases hpattern with hpattern | hpattern
  · have hvpattern :
        ∀ᵐ t ∂μ, 0 ≤ (t - a) * (t - b) * v t := by
      filter_upwards [hpattern] with t ht
      dsimp [v]
      rw [show
        (t - a) * (t - b) *
            (Real.cosh (c * t) * Real.sin (u * t) * h t) =
          Real.cosh (c * t) *
            ((t - a) * (t - b) * (Real.sin (u * t) * h t)) by ring]
      exact mul_nonneg (Real.cosh_pos _).le ht
    exact finish
      (routeJ_twoSignChange_reflectionMoments_ae_zero
        (show 0 < 2 * c by positivity) ha hab hvsupport hvpattern
          hv htv hgv hv0 htv0 hgv0)
  · let w : ℝ → ℝ := fun t => -v t
    have hwsupport : ∀ᵐ t ∂μ, w t ≠ 0 → 0 < t := by
      filter_upwards [hvsupport] with t ht hwt
      exact ht (by
        intro hvt
        dsimp [w] at hwt
        rw [hvt, neg_zero] at hwt
        exact hwt rfl)
    have hwpattern :
        ∀ᵐ t ∂μ, 0 ≤ (t - a) * (t - b) * w t := by
      filter_upwards [hpattern] with t ht
      dsimp [w, v]
      rw [show
        (t - a) * (t - b) *
            (-(Real.cosh (c * t) * Real.sin (u * t) * h t)) =
          Real.cosh (c * t) *
            (-((t - a) * (t - b) * (Real.sin (u * t) * h t))) by ring]
      exact mul_nonneg (Real.cosh_pos _).le (neg_nonneg.mpr ht)
    have hw : Integrable w μ := hv.neg
    have htw' : Integrable (fun t => t * w t) μ := by
      exact htv.neg.congr (Eventually.of_forall fun t => by
        dsimp [w]
        ring)
    have hgw :
        Integrable (fun t => routeJReflectionRatio (2 * c) t * w t) μ := by
      exact hgv.neg.congr (Eventually.of_forall fun t => by
        dsimp [w]
        ring)
    have hw0 : ∫ t, w t ∂μ = 0 := by
      rw [show w = fun t => -v t by rfl, integral_neg, hv0, neg_zero]
    have htw0' : ∫ t, t * w t ∂μ = 0 := by
      calc
        ∫ t, t * w t ∂μ = ∫ t, -(t * v t) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with t
          dsimp [w]
          ring
        _ = 0 := by rw [integral_neg, htv0, neg_zero]
    have hgw0 :
        ∫ t, routeJReflectionRatio (2 * c) t * w t ∂μ = 0 := by
      calc
        ∫ t, routeJReflectionRatio (2 * c) t * w t ∂μ =
            ∫ t, -(routeJReflectionRatio (2 * c) t * v t) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with t
              dsimp [w]
              ring
        _ = 0 := by rw [integral_neg, hgv0, neg_zero]
    have hwzero :=
      routeJ_twoSignChange_reflectionMoments_ae_zero
        (show 0 < 2 * c by positivity) ha hab hwsupport hwpattern
          hw htw' hgw hw0 htw0' hgw0
    apply finish
    filter_upwards [hwzero] with t hwt
    dsimp [w] at hwt
    exact neg_eq_zero.mp hwt

end

end RHTower
