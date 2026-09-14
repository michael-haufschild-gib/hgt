import GaloisForLFunctions.RHTower.FZZCigarParityTwoMarkedSourceContact

/-!
# Full mixed Hessian of the compact two-marked FZZ annulus

The relative annular response sees only the direct contact term.  This file computes the missing
absolute response.  Its second contribution is the connected fluctuation of logarithmic radius.
-/

open GaloisForLFunctions.HTGeometry.FZZCigar

namespace GaloisForLFunctions.RHTower

noncomputable section

private def fzzTwoMarkedAnnularRate (u δ ε : ℝ) : ℝ :=
  1 + fzzTwoMarkedOPEExponent (fzzTwoMarkedPhysicalLevel u) (-1) δ ε

/-- Mean logarithmic radius in the unit annulus tilted by rate `a`. -/
def fzzTwoMarkedAnnularTiltMean (a : ℝ) : ℝ :=
  Real.exp a / (Real.exp a - 1) - 1 / a

/-- Connected logarithmic-radius fluctuation in the unit annulus tilted by rate `a`. -/
def fzzTwoMarkedAnnularTiltVariance (a : ℝ) : ℝ :=
  1 / a ^ 2 - Real.exp a / (Real.exp a - 1) ^ 2

/-- Actual mixed logarithmic response of the compact opposite-winding pair. -/
def fzzTwoMarkedAnnularFullMixedResponse (u L : ℝ) : ℝ :=
  deriv (fun e => deriv (fun d =>
    Real.log (fzzTwoMarkedAnnularIntegral u L d e)) 0) 0

private def fzzTwoMarkedAnnularLogMoment (a : ℝ) : ℝ :=
  Real.log ((Real.exp a - 1) / a)

private theorem intervalIntegral_rexp_mul_of_ne_zero
    {a : ℝ} (ha : a ≠ 0) (s t : ℝ) :
    (∫ x : ℝ in s..t, Real.exp (a * x)) =
      (Real.exp (a * t) - Real.exp (a * s)) / a := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (a * y) / a) (Real.exp (a * x)) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => a * y) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have h := hlin.exp.div_const a
    have hcancel : Real.exp (a * x) * a / a = Real.exp (a * x) := by
      field_simp
    rw [hcancel] at h
    exact h
  have hcont : ContinuousOn (fun x : ℝ => Real.exp (a * x)) (Set.uIcc s t) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    hcont.intervalIntegrable, sub_div]

private theorem fzzTwoMarkedAnnularIntegral_closedForm_of_rate_ne
    {u L δ ε : ℝ} (h : fzzTwoMarkedAnnularRate u δ ε ≠ 0) :
    fzzTwoMarkedAnnularIntegral u L δ ε =
      Real.exp (fzzTwoMarkedAnnularRate u δ ε * L) *
        ((Real.exp (fzzTwoMarkedAnnularRate u δ ε) - 1) /
          fzzTwoMarkedAnnularRate u δ ε) := by
  rw [fzzTwoMarkedAnnularIntegral_scale]
  congr 1
  unfold fzzTwoMarkedAnnularIntegral
  simp only [zero_add]
  change (∫ x : ℝ in 0..1, Real.exp (fzzTwoMarkedAnnularRate u δ ε * x)) = _
  rw [intervalIntegral_rexp_mul_of_ne_zero h]
  simp

private theorem fzzTwoMarkedAnnularIntegral_log_closedForm_of_rate_neg
    {u L δ ε : ℝ} (h : fzzTwoMarkedAnnularRate u δ ε < 0) :
    Real.log (fzzTwoMarkedAnnularIntegral u L δ ε) =
      fzzTwoMarkedAnnularRate u δ ε * L +
        fzzTwoMarkedAnnularLogMoment (fzzTwoMarkedAnnularRate u δ ε) := by
  have ha : fzzTwoMarkedAnnularRate u δ ε ≠ 0 := ne_of_lt h
  have hexp : Real.exp (fzzTwoMarkedAnnularRate u δ ε) - 1 ≠ 0 := by
    have hlt : Real.exp (fzzTwoMarkedAnnularRate u δ ε) < 1 := by
      simpa using (Real.exp_lt_exp.mpr h :
        Real.exp (fzzTwoMarkedAnnularRate u δ ε) < Real.exp 0)
    linarith
  rw [fzzTwoMarkedAnnularIntegral_closedForm_of_rate_ne ha,
    Real.log_mul (Real.exp_pos _).ne' (div_ne_zero hexp ha), Real.log_exp]
  rfl

private theorem hasDerivAt_fzzTwoMarkedAnnularRate_left (u δ ε : ℝ) :
    HasDerivAt (fun d => fzzTwoMarkedAnnularRate u d ε)
      (fzzTwoMarkedPhysicalLevel u +
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * ε) δ := by
  have h := (hasDerivAt_fzzTwoMarkedOPEExponent_left u (-1) δ ε).const_add 1
  have heq : (fun d => fzzTwoMarkedAnnularRate u d ε) =ᶠ[nhds δ]
      fun d => 1 + fzzTwoMarkedOPEExponent (fzzTwoMarkedPhysicalLevel u) (-1) d ε := by
    filter_upwards with d
    unfold fzzTwoMarkedAnnularRate
    rfl
  have h' := h.congr_of_eventuallyEq heq
  apply h'.congr_deriv
  ring

private theorem hasDerivAt_fzzTwoMarkedAnnularRate_right (u δ ε : ℝ) :
    HasDerivAt (fun e => fzzTwoMarkedAnnularRate u δ e)
      (fzzTwoMarkedPhysicalLevel u +
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * δ) ε := by
  unfold fzzTwoMarkedAnnularRate
  simp_rw [fzzTwoMarkedOPEExponent_normalForm]
  have h := (((hasDerivAt_id ε).const_mul
    (fzzTwoMarkedPhysicalLevel u / 2 * (1 - (-1)) +
      fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * δ)).const_add
        (1 + (-(fzzTwoMarkedPhysicalLevel u - 2) / 2 +
          fzzTwoMarkedPhysicalLevel u * (-1) / 2 +
          fzzTwoMarkedPhysicalLevel u / 2 * (1 - (-1)) * δ)))
  have heq : (fun e : ℝ =>
      1 + (-(fzzTwoMarkedPhysicalLevel u - 2) / 2 +
        fzzTwoMarkedPhysicalLevel u * (-1) / 2 +
        fzzTwoMarkedPhysicalLevel u / 2 * (1 - (-1)) * (δ + e) +
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * δ * e)) =ᶠ[nhds ε]
      fun e =>
        (1 + (-(fzzTwoMarkedPhysicalLevel u - 2) / 2 +
          fzzTwoMarkedPhysicalLevel u * (-1) / 2 +
          fzzTwoMarkedPhysicalLevel u / 2 * (1 - (-1)) * δ)) +
        (fzzTwoMarkedPhysicalLevel u / 2 * (1 - (-1)) +
          fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * δ) * e := by
    filter_upwards with e
    ring
  have h' := h.congr_of_eventuallyEq heq
  apply h'.congr_deriv
  ring

private theorem fzzTwoMarkedAnnularRate_zero_zero (u : ℝ) :
    fzzTwoMarkedAnnularRate u 0 0 = -Real.exp u := by
  unfold fzzTwoMarkedAnnularRate
  rw [fzzTwoMarkedOPEExponent_opposite]
  unfold fzzTwoMarkedPhysicalLevel
  ring

private theorem exp_sub_one_ne_zero_of_neg {a : ℝ} (ha : a < 0) :
    Real.exp a - 1 ≠ 0 := by
  have hlt : Real.exp a < 1 := by
    simpa using (Real.exp_lt_exp.mpr ha : Real.exp a < Real.exp 0)
  linarith

private theorem hasDerivAt_fzzTwoMarkedAnnularLogMoment
    {a : ℝ} (ha : a < 0) :
    HasDerivAt fzzTwoMarkedAnnularLogMoment (fzzTwoMarkedAnnularTiltMean a) a := by
  have ha0 : a ≠ 0 := ne_of_lt ha
  have he0 : Real.exp a - 1 ≠ 0 := exp_sub_one_ne_zero_of_neg ha
  have hquot := (Real.hasDerivAt_exp a).sub_const 1 |>.div (hasDerivAt_id a) ha0
  have hlog := hquot.log (div_ne_zero he0 ha0)
  unfold fzzTwoMarkedAnnularLogMoment fzzTwoMarkedAnnularTiltMean
  simp only [Pi.div_apply, id_eq] at hlog
  apply hlog.congr_deriv
  field_simp [ha0, he0]

private theorem hasDerivAt_fzzTwoMarkedAnnularTiltMean
    {a : ℝ} (ha : a < 0) :
    HasDerivAt fzzTwoMarkedAnnularTiltMean (fzzTwoMarkedAnnularTiltVariance a) a := by
  have ha0 : a ≠ 0 := ne_of_lt ha
  have he0 : Real.exp a - 1 ≠ 0 := exp_sub_one_ne_zero_of_neg ha
  have h₁ := (Real.hasDerivAt_exp a).div ((Real.hasDerivAt_exp a).sub_const 1) he0
  have h₂ := (hasDerivAt_const a 1).div (hasDerivAt_id a) ha0
  unfold fzzTwoMarkedAnnularTiltMean fzzTwoMarkedAnnularTiltVariance
  have h := h₁.sub h₂
  simp only [id_eq] at h
  apply h.congr_deriv
  field_simp [ha0, he0]
  ring

private theorem hasDerivAt_log_fzzTwoMarkedAnnularIntegral_left
    {u L δ ε : ℝ} (hneg : fzzTwoMarkedAnnularRate u δ ε < 0) :
    HasDerivAt (fun d => Real.log (fzzTwoMarkedAnnularIntegral u L d ε))
      ((fzzTwoMarkedPhysicalLevel u +
          fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * ε) *
        (L + fzzTwoMarkedAnnularTiltMean (fzzTwoMarkedAnnularRate u δ ε))) δ := by
  let A : ℝ → ℝ := fun d => fzzTwoMarkedAnnularRate u d ε
  have hA : HasDerivAt A
      (fzzTwoMarkedPhysicalLevel u +
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * ε) δ :=
    hasDerivAt_fzzTwoMarkedAnnularRate_left u δ ε
  have hnear : ∀ᶠ d in nhds δ, A d < 0 :=
    hA.continuousAt (Iio_mem_nhds hneg)
  have heq : (fun d => Real.log (fzzTwoMarkedAnnularIntegral u L d ε)) =ᶠ[nhds δ]
      (fun d => A d * L) + fzzTwoMarkedAnnularLogMoment ∘ A := by
    filter_upwards [hnear] with d hd
    simpa only [Pi.add_apply, Function.comp_apply] using
      fzzTwoMarkedAnnularIntegral_log_closedForm_of_rate_neg hd
  have hclosed := hA.mul_const L |>.add
    ((hasDerivAt_fzzTwoMarkedAnnularLogMoment hneg).comp δ hA)
  apply hclosed.congr_of_eventuallyEq heq |>.congr_deriv
  ring

private theorem deriv_log_fzzTwoMarkedAnnularIntegral_left
    {u L δ ε : ℝ} (hneg : fzzTwoMarkedAnnularRate u δ ε < 0) :
    deriv (fun d => Real.log (fzzTwoMarkedAnnularIntegral u L d ε)) δ =
      (fzzTwoMarkedPhysicalLevel u +
          fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * ε) *
        (L + fzzTwoMarkedAnnularTiltMean (fzzTwoMarkedAnnularRate u δ ε)) :=
  (hasDerivAt_log_fzzTwoMarkedAnnularIntegral_left hneg).deriv

/-- Exact full mixed logarithmic response of the compact opposite-winding annulus.  The first
term is the direct two-source contact; the second is the connected fluctuation generated by
integrating the common logarithmic radius. -/
theorem fzzTwoMarkedAnnularIntegral_fullMixedLogDeriv (u L : ℝ) :
    deriv (fun e => deriv (fun d =>
      Real.log (fzzTwoMarkedAnnularIntegral u L d e)) 0) 0 =
      fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) *
          (L + fzzTwoMarkedAnnularTiltMean (-Real.exp u)) +
        fzzTwoMarkedPhysicalLevel u ^ 2 *
          fzzTwoMarkedAnnularTiltVariance (-Real.exp u) := by
  let A : ℝ → ℝ := fun e => fzzTwoMarkedAnnularRate u 0 e
  have hA0 : A 0 = -Real.exp u := fzzTwoMarkedAnnularRate_zero_zero u
  have hneg0 : A 0 < 0 := by rw [hA0]; exact neg_neg_of_pos (Real.exp_pos u)
  have hA : HasDerivAt A (fzzTwoMarkedPhysicalLevel u) 0 := by
    simpa [A] using hasDerivAt_fzzTwoMarkedAnnularRate_right u 0 0
  have hnear : ∀ᶠ e in nhds 0, A e < 0 :=
    hA.continuousAt (Iio_mem_nhds hneg0)
  let C : ℝ := fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1)
  let k : ℝ := fzzTwoMarkedPhysicalLevel u
  have heq : (fun e => deriv (fun d =>
      Real.log (fzzTwoMarkedAnnularIntegral u L d e)) 0) =ᶠ[nhds 0]
      (fun e => k + C * e) *
        ((fun _ => L) + fun e => fzzTwoMarkedAnnularTiltMean (A e)) := by
    filter_upwards [hnear] with e he
    simpa only [Pi.mul_apply, Pi.add_apply] using
      (show deriv (fun d => Real.log (fzzTwoMarkedAnnularIntegral u L d e)) 0 =
        (k + C * e) * (L + fzzTwoMarkedAnnularTiltMean (A e)) by
          simpa [A, C, k] using deriv_log_fzzTwoMarkedAnnularIntegral_left he)
  have hfactor : HasDerivAt (fun e : ℝ => k + C * e) C 0 := by
    have h := ((hasDerivAt_id 0).const_mul C).const_add k
    have heq : (fun e : ℝ => k + C * e) =ᶠ[nhds 0]
        fun e => k + C * id e := by
      filter_upwards with e
      rfl
    have h' := h.congr_of_eventuallyEq heq
    apply h'.congr_deriv
    ring
  have hmean : HasDerivAt (fun e => fzzTwoMarkedAnnularTiltMean (A e))
      (fzzTwoMarkedAnnularTiltVariance (A 0) * k) 0 :=
    (hasDerivAt_fzzTwoMarkedAnnularTiltMean hneg0).comp 0 hA
  have hclosed := hfactor.mul ((hasDerivAt_const 0 L).add hmean)
  have hactual := hclosed.congr_of_eventuallyEq heq
  rw [hactual.deriv]
  simp only [Pi.add_apply]
  rw [hA0]
  dsimp [C, k]
  ring

theorem fzzTwoMarkedAnnularFullMixedResponse_eq (u L : ℝ) :
    fzzTwoMarkedAnnularFullMixedResponse u L =
      fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) *
          (L + fzzTwoMarkedAnnularTiltMean (-Real.exp u)) +
        fzzTwoMarkedPhysicalLevel u ^ 2 *
          fzzTwoMarkedAnnularTiltVariance (-Real.exp u) := by
  exact fzzTwoMarkedAnnularIntegral_fullMixedLogDeriv u L

/-- The complete compact response differs between annulus geometries by exactly the direct
contact term; the connected fluctuation is source-fixed and geometry-independent. -/
theorem fzzTwoMarkedAnnularIntegral_fullMixedLogDeriv_sub (u L₁ L₂ : ℝ) :
    deriv (fun e => deriv (fun d =>
      Real.log (fzzTwoMarkedAnnularIntegral u L₁ d e)) 0) 0 -
      deriv (fun e => deriv (fun d =>
        Real.log (fzzTwoMarkedAnnularIntegral u L₂ d e)) 0) 0 =
        fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * (L₁ - L₂) := by
  rw [fzzTwoMarkedAnnularIntegral_fullMixedLogDeriv,
    fzzTwoMarkedAnnularIntegral_fullMixedLogDeriv]
  ring

theorem fzzTwoMarkedAnnularContact_neg (u : ℝ) :
    fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) < 0 := by
  have hk := fzzTwoMarkedPhysicalLevel_gt_two u
  have hd : fzzTwoMarkedPhysicalLevel u - 2 ≠ 0 := by linarith
  have hform : fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) =
      -(fzzTwoMarkedPhysicalLevel u * (fzzTwoMarkedPhysicalLevel u - 1) /
        (fzzTwoMarkedPhysicalLevel u - 2)) := by
    unfold fzzTwoMarkedContact
    field_simp [hd]
    ring
  rw [hform]
  have hk0 : 0 < fzzTwoMarkedPhysicalLevel u := by linarith
  have hk1 : 0 < fzzTwoMarkedPhysicalLevel u - 1 := by linarith
  have hk2 : 0 < fzzTwoMarkedPhysicalLevel u - 2 := by linarith
  have hpos : 0 < fzzTwoMarkedPhysicalLevel u *
      (fzzTwoMarkedPhysicalLevel u - 1) /
        (fzzTwoMarkedPhysicalLevel u - 2) :=
    div_pos (mul_pos hk0 hk1) hk2
  linarith

/-- The full compact response, including its connected fluctuation, ranges over every real value
as annulus geometry varies at one fixed physical level. -/
theorem fzzTwoMarkedAnnularFullMixedResponse_surjective (u target : ℝ) :
    ∃ L : ℝ, fzzTwoMarkedAnnularFullMixedResponse u L = target := by
  let C := fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1)
  let M := fzzTwoMarkedAnnularTiltMean (-Real.exp u)
  let V := fzzTwoMarkedPhysicalLevel u ^ 2 *
    fzzTwoMarkedAnnularTiltVariance (-Real.exp u)
  have hC : C ≠ 0 := ne_of_lt (fzzTwoMarkedAnnularContact_neg u)
  refine ⟨(target - C * M - V) / C, ?_⟩
  rw [fzzTwoMarkedAnnularFullMixedResponse_eq]
  change C * ((target - C * M - V) / C + M) + V = target
  have hdiv : (target - C * M - V) / C * C = target - C * M - V :=
    div_mul_cancel₀ _ hC
  calc
    C * ((target - C * M - V) / C + M) + V =
        (target - C * M - V) / C * C + C * M + V := by ring
    _ = target := by rw [hdiv]; ring

/-- Every physical level has exactly one annular geometry at which direct contact and connected
fluctuation cancel. -/
theorem existsUnique_fzzTwoMarkedAnnularFullMixedResponse_eq_zero (u : ℝ) :
    ∃! L : ℝ, fzzTwoMarkedAnnularFullMixedResponse u L = 0 := by
  obtain ⟨L, hL⟩ := fzzTwoMarkedAnnularFullMixedResponse_surjective u 0
  refine ⟨L, hL, ?_⟩
  intro y hy
  have hsub := fzzTwoMarkedAnnularIntegral_fullMixedLogDeriv_sub u y L
  change fzzTwoMarkedAnnularFullMixedResponse u y -
    fzzTwoMarkedAnnularFullMixedResponse u L =
      fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * (y - L) at hsub
  rw [hy, hL] at hsub
  have hz : fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) * (y - L) = 0 := by
    linarith
  have hC : fzzTwoMarkedContact (fzzTwoMarkedPhysicalLevel u) (-1) ≠ 0 :=
    ne_of_lt (fzzTwoMarkedAnnularContact_neg u)
  have : y - L = 0 := (mul_eq_zero.mp hz).resolve_left hC
  linarith

/-- The complete one-pair annular Hessian has no universal orientation: at every physical level
source geometry realizes both signs.  Thus this factor alone cannot supply the source-fixed Ward
orientation required before balanced-Gamma saturation and passivity. -/
theorem fzzTwoMarkedAnnularUniversalSignRouteKilled (u : ℝ) :
    (¬ ∀ L : ℝ, 0 ≤ fzzTwoMarkedAnnularFullMixedResponse u L) ∧
      (¬ ∀ L : ℝ, fzzTwoMarkedAnnularFullMixedResponse u L ≤ 0) := by
  obtain ⟨Lneg, hneg⟩ := fzzTwoMarkedAnnularFullMixedResponse_surjective u (-1)
  obtain ⟨Lpos, hpos⟩ := fzzTwoMarkedAnnularFullMixedResponse_surjective u 1
  constructor
  · intro h
    have := h Lneg
    rw [hneg] at this
    norm_num at this
  · intro h
    have := h Lpos
    rw [hpos] at this
    norm_num at this

end

end GaloisForLFunctions.RHTower
