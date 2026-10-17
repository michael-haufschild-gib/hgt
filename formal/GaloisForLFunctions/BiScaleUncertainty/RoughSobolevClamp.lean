import GaloisForLFunctions.BiScaleUncertainty.RoughSobolevModulus

/-!
# Actual Sobolev clamping and exact additive energy localization

Two modulus velocities construct the unit clamp inside the physical L2 domain.
The retained velocity lives on the open state band; its residual is orthogonal
pointwise a.e. Exact local energy splitting survives logarithmic transport.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def unitClamp (a : ℝ) : ℝ := min (max a 0) 1

theorem unitClamp_nonneg (a : ℝ) : 0 ≤ unitClamp a :=
  le_min (le_max_right _ _) (by norm_num)

theorem unitClamp_le_one (a : ℝ) : unitClamp a ≤ 1 := min_le_right _ _

theorem unitClamp_of_nonpos (a : ℝ) (ha : a ≤ 0) : unitClamp a = 0 := by
  simp [unitClamp, max_eq_right ha]

theorem unitClamp_of_one_le (a : ℝ) (ha : 1 ≤ a) : unitClamp a = 1 := by
  simp [unitClamp, max_eq_left (show 0 ≤ a by linarith), min_eq_right ha]

theorem unitClamp_eq_self (a : ℝ) (ha : 0 ≤ a) (hb : a ≤ 1) : unitClamp a = a := by
  simp [unitClamp, max_eq_left ha, min_eq_left hb]

theorem unitClamp_eq_abs (a : ℝ) : unitClamp a = (|a|-|a-1|+1)/2 := by
  by_cases ha : a ≤ 0
  · rw [unitClamp_of_nonpos a ha, abs_of_nonpos ha, abs_of_nonpos (show a-1 ≤ 0 by linarith)]
    ring
  · have h₀ : 0 ≤ a := (lt_of_not_ge ha).le
    by_cases h₁ : a ≤ 1
    · rw [unitClamp_eq_self a h₀ h₁, abs_of_nonneg h₀,
        abs_of_nonpos (show a-1 ≤ 0 by linarith)]
      ring
    · have h₁' : 1 ≤ a := (lt_of_not_ge h₁).le
      rw [unitClamp_of_one_le a h₁', abs_of_nonneg h₀, abs_of_nonneg (sub_nonneg.mpr h₁')]
      ring

theorem monotone_unitClamp : Monotone unitClamp := by
  intro a b hab
  exact min_le_min (max_le_max hab le_rfl) le_rfl

theorem unitClamp_abs_sub_le (a b : ℝ) : |unitClamp a-unitClamp b| ≤ |a-b| := by
  have h := abs_min_sub_min_le_max (max a 0) 1 (max b 0) 1
  simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (max a 0-max b 0))] at h
  exact h.trans (abs_max_sub_max_le_abs a b 0)

/-- The retained and removed increments have nonnegative interaction. -/
theorem unitClamp_firm_sq (a b : ℝ) :
    (unitClamp b-unitClamp a)^2 + ((b-unitClamp b)-(a-unitClamp a))^2 ≤ (b-a)^2 := by
  have h := unitClamp_abs_sub_le b a
  rcases le_total a b with hab | hba
  · have hm := monotone_unitClamp hab
    rw [abs_of_nonneg (sub_nonneg.mpr hm), abs_of_nonneg (sub_nonneg.mpr hab)] at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr h)]
  · have hm := monotone_unitClamp hba
    rw [abs_of_nonpos (sub_nonpos.mpr hm), abs_of_nonpos (sub_nonpos.mpr hba)] at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr h)]

theorem unitClamp_residual_injective_outside (a b : ℝ) (ha : a < 0 ∨ 1 < a)
    (he : a-unitClamp a = b-unitClamp b) : a = b := by
  rcases ha with ha | ha
  · rw [unitClamp_of_nonpos a ha.le, sub_zero] at he
    have hb : b < 0 := by
      by_contra hb
      have h₀ : 0 ≤ b := le_of_not_gt hb
      have ht : unitClamp b ≤ b := by
        simpa only [unitClamp, max_eq_left h₀] using (min_le_left b (1 : ℝ))
      linarith
    simpa only [unitClamp_of_nonpos b hb.le, sub_zero] using he
  · rw [unitClamp_of_one_le a ha.le] at he
    have hb : 1 < b := by
      by_contra hb
      have h₁ : b ≤ 1 := le_of_not_gt hb
      have ht : b ≤ unitClamp b := le_min (le_max_left _ _) h₁
      linarith
    rw [unitClamp_of_one_le b hb.le] at he
    linarith

theorem primitive_velocity_sub (q r : Velocity) (t : ℝ) :
    primitive (q-r) t = primitive q t-primitive r t := by
  calc
    _ = ∫ x in 0..t, q x-r x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Lp.coeFn_sub q r] with x hx
      exact fun _ => hx
    _ = _ := intervalIntegral.integral_sub
      (intervalIntegrable_velocity q 0 t) (intervalIntegrable_velocity r 0 t)

theorem primitive_velocity_smul (a : ℝ) (q : Velocity) (t : ℝ) :
    primitive (a • q) t = a * primitive q t := by
  calc
    _ = ∫ x in 0..t, a*q x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Lp.coeFn_smul a q] with x hx
      exact fun _ => hx
    _ = _ := intervalIntegral.integral_const_mul a _

def clampVelocity (q : Velocity) (c : ℝ) : Velocity :=
  (1/2 : ℝ) • (modulusVelocity q c-modulusVelocity q (c-1))

def clampResidualVelocity (q : Velocity) (c : ℝ) : Velocity := q-clampVelocity q c

theorem primitive_clampVelocity (q : Velocity) (c t : ℝ) :
    unitClamp c + primitive (clampVelocity q c) t = unitClamp (physicalState q c t) := by
  have h₀ := primitive_modulusVelocity q c t
  have h₁ := primitive_modulusVelocity q (c-1) t
  have hs : physicalState q (c-1) t = physicalState q c t-1 := by unfold physicalState; ring
  rw [hs] at h₁
  rw [clampVelocity, primitive_velocity_smul, primitive_velocity_sub,
    unitClamp_eq_abs c, unitClamp_eq_abs (physicalState q c t)]
  linarith

theorem primitive_clampResidualVelocity (q : Velocity) (c t : ℝ) :
    (c-unitClamp c) + primitive (clampResidualVelocity q c) t =
      physicalState q c t-unitClamp (physicalState q c t) := by
  rw [clampResidualVelocity, primitive_velocity_sub]
  have h := primitive_clampVelocity q c t
  dsimp [physicalState] at h ⊢
  linarith

theorem logPrimitive_clampVelocity (q : Velocity) (c x : ℝ) :
    unitClamp c + logPrimitive (clampVelocity q c) x = unitClamp (c+logPrimitive q x) :=
  primitive_clampVelocity q c (Real.exp x)

theorem logPrimitive_clampResidualVelocity (q : Velocity) (c x : ℝ) :
    (c-unitClamp c) + logPrimitive (clampResidualVelocity q c) x =
      c+logPrimitive q x-unitClamp (c+logPrimitive q x) :=
  primitive_clampResidualVelocity q c (Real.exp x)

/-- Threshold values introduce no unproved derivative assumption. -/
theorem ae_clampVelocity (q : Velocity) (c : ℝ) :
    clampVelocity q c =ᵐ[volume]
      fun t => if 0 < physicalState q c t ∧ physicalState q c t < 1 then q t else 0 := by
  filter_upwards [Lp.coeFn_smul (1/2 : ℝ) (modulusVelocity q c-modulusVelocity q (c-1)),
    Lp.coeFn_sub (modulusVelocity q c) (modulusVelocity q (c-1)),
    ae_modulusVelocity q c, ae_modulusVelocity q (c-1),
    ae_velocity_zero_on_state_zero q c] with t hsm hsub h₀ h₁ hz
  change (clampVelocity q c) t = (1/2 : ℝ) *
    ((modulusVelocity q c-modulusVelocity q (c-1)) t) at hsm
  change (modulusVelocity q c-modulusVelocity q (c-1)) t =
    modulusVelocity q c t-modulusVelocity q (c-1) t at hsub
  rw [hsm, hsub, h₀, h₁]
  have hs : physicalState q (c-1) t = physicalState q c t-1 := by unfold physicalState; ring
  rw [hs]
  rcases lt_trichotomy (physicalState q c t) 0 with hn | he | hp
  · simp [not_le.mpr hn, show ¬0 ≤ physicalState q c t-1 by linarith, not_lt.mpr hn.le]
  · simp [he, hz he]
  · by_cases h₁ : physicalState q c t < 1
    · simp [hp, hp.le, h₁, show ¬0 ≤ physicalState q c t-1 by linarith]
      ring
    · simp [hp, hp.le, h₁, show 0 ≤ physicalState q c t-1 by linarith]

theorem ae_clampResidualVelocity (q : Velocity) (c : ℝ) :
    clampResidualVelocity q c =ᵐ[volume]
      fun t => if 0 < physicalState q c t ∧ physicalState q c t < 1 then 0 else q t := by
  filter_upwards [Lp.coeFn_sub q (clampVelocity q c), ae_clampVelocity q c] with t hr hc
  change clampResidualVelocity q c t = q t-clampVelocity q c t at hr
  rw [hr, hc]
  split_ifs <;> simp

theorem absolutelyContinuous_clampState (q : Velocity) (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => unitClamp (physicalState q c t)) a b := by
  have he : (fun t => unitClamp (physicalState q c t)) =
      physicalState (clampVelocity q c) (unitClamp c) := by
    funext t
    exact (primitive_clampVelocity q c t).symm
  rw [he]
  exact absolutelyContinuous_physicalState (clampVelocity q c) (unitClamp c) a b

theorem ae_hasDerivAt_clampState (q : Velocity) (c : ℝ) :
    ∀ᵐ t, HasDerivAt (fun u => unitClamp (physicalState q c u))
      (if 0 < physicalState q c t ∧ physicalState q c t < 1 then q t else 0) t := by
  have he : (fun t => unitClamp (physicalState q c t)) =
      (fun t => unitClamp c + primitive (clampVelocity q c) t) := by
    funext t
    exact (primitive_clampVelocity q c t).symm
  filter_upwards [ae_hasDerivAt_primitive (clampVelocity q c), ae_clampVelocity q c] with t ht hc
  rw [he, ← hc]
  exact ht.const_add (unitClamp c)

theorem ae_clamp_energy_split (q : Velocity) (c : ℝ) :
    (fun t => (q t)^2) =ᵐ[volume]
      fun t => (clampVelocity q c t)^2+(clampResidualVelocity q c t)^2 := by
  filter_upwards [ae_clampVelocity q c, ae_clampResidualVelocity q c] with t hc hr
  rw [hc, hr]
  split_ifs <;> simp

theorem energy_clampVelocity_localized (q : Velocity) (c a b : ℝ) :
    energy (clampVelocity q c) a b = ∫ t in a..b,
      if 0 < physicalState q c t ∧ physicalState q c t < 1 then (q t)^2 else 0 := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_clampVelocity q c] with t ht
  intro _
  rw [ht]
  split_ifs <;> simp

theorem energy_clamp_split (q : Velocity) (c a b : ℝ) :
    energy q a b = energy (clampVelocity q c) a b + energy (clampResidualVelocity q c) a b := by
  rw [energy, energy, energy, ← intervalIntegral.integral_add
    (integrable_velocity_sq (clampVelocity q c)).intervalIntegrable
    (integrable_velocity_sq (clampResidualVelocity q c)).intervalIntegrable]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_clamp_energy_split q c] with t ht
  exact fun _ => ht

theorem energy_clampVelocity_le (q : Velocity) (c a b : ℝ) (hab : a ≤ b) :
    energy (clampVelocity q c) a b ≤ energy q a b := by
  rw [energy_clamp_split q c]
  exact le_add_of_nonneg_right (intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _))

theorem log_energy_clamp_split (q : Velocity) (c a b : ℝ) :
    (∫ x in a..b, Real.exp (-x)*(deriv (logPrimitive q) x)^2) =
      (∫ x in a..b, Real.exp (-x)*(deriv (logPrimitive (clampVelocity q c)) x)^2) +
      ∫ x in a..b, Real.exp (-x)*(deriv (logPrimitive (clampResidualVelocity q c)) x)^2 := by
  rw [log_energy_eq, log_energy_eq, log_energy_eq, energy_clamp_split]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
