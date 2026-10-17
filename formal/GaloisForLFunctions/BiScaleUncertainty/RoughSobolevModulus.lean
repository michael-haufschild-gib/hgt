import GaloisForLFunctions.BiScaleUncertainty.SobolevLogarithmicTransport
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Modulus inside the actual Sobolev primitive domain

Absolute continuity of the modulus and Fermat's theorem prove the zero-level
derivative law. The modulus derivative then defines an actual L2 velocity with
the exact modulus primitive and unchanged local additive Dirichlet energy.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators NNReal Topology

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def physicalState (q : Velocity) (c t : ℝ) : ℝ := c + primitive q t

theorem continuous_physicalState (q : Velocity) (c : ℝ) : Continuous (physicalState q c) :=
  continuous_const.add (intervalIntegral.continuous_primitive (intervalIntegrable_velocity q) 0)

theorem absolutelyContinuous_physicalState (q : Velocity) (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (physicalState q c) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
    (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ => c) (uIcc a b)).absolutelyContinuousOnInterval
  exact hc.add (absolutelyContinuous_primitive q a b)

theorem absolutelyContinuous_absState (q : Velocity) (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => |physicalState q c t|) a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := (absolutelyContinuousOnInterval_iff _ _ _).mp
    (absolutelyContinuous_physicalState q c a b) ε hε
  refine ⟨δ, hδ, fun E hE hlen => lt_of_le_of_lt ?_ (h E hE hlen)⟩
  apply Finset.sum_le_sum
  intro i _
  simp only [Real.dist_eq]
  exact abs_abs_sub_abs_le_abs_sub _ _

theorem ae_differentiable_absState (q : Velocity) (c : ℝ) :
    ∀ᵐ t, DifferentiableAt ℝ (fun x => |physicalState q c x|) t := by
  have h : ∀ᵐ t, ∀ n : ℕ, t ∈ uIcc (-(n : ℝ)) n →
      DifferentiableAt ℝ (fun x => |physicalState q c x|) t :=
    ae_all_iff.mpr fun n => (absolutelyContinuous_absState q c (-n) n).ae_differentiableAt
  filter_upwards [h] with t ht
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  apply ht n
  have hn0 : -(n : ℝ) ≤ n := by linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  rw [uIcc_of_le hn0]
  constructor <;> linarith [le_abs_self t, neg_abs_le t]

private theorem velocity_zero_at_state_zero (q : Velocity) (c t : ℝ)
    (hq : HasDerivAt (primitive q) (q t) t)
    (hm : DifferentiableAt ℝ (fun x => |physicalState q c x|) t)
    (hz : physicalState q c t = 0) : q t = 0 := by
  have hmin : IsLocalMin (fun x => |physicalState q c x|) t := by
    apply Filter.Eventually.of_forall
    intro x
    simp only [hz, abs_zero]
    exact abs_nonneg (physicalState q c x)
  have hsum : IsLocalMin (fun x => |physicalState q c x| + physicalState q c x) t := by
    apply Filter.Eventually.of_forall
    intro x
    simp only [hz, abs_zero, zero_add]
    linarith [neg_abs_le (physicalState q c x)]
  have hzero := hmin.deriv_eq_zero
  have hboth := hsum.hasDerivAt_eq_zero (hm.hasDerivAt.add (hq.const_add c))
  linarith

/-- A physical velocity vanishes almost everywhere on each level set of its primitive. -/
theorem ae_velocity_zero_on_state_zero (q : Velocity) (c : ℝ) :
    ∀ᵐ t, physicalState q c t = 0 → q t = 0 := by
  filter_upwards [ae_hasDerivAt_primitive q, ae_differentiable_absState q c] with t ht hm
  exact velocity_zero_at_state_zero q c t ht hm

theorem ae_deriv_absState (q : Velocity) (c : ℝ) :
    deriv (fun t => |physicalState q c t|) =ᵐ[volume]
      fun t => if 0 ≤ physicalState q c t then q t else -q t := by
  filter_upwards [ae_hasDerivAt_primitive q, ae_differentiable_absState q c] with t ht hm
  rcases lt_trichotomy (physicalState q c t) 0 with hn | hz | hp
  · have hd := (hasDerivAt_abs_neg hn).comp t (ht.const_add c)
    simpa only [Function.comp_def, neg_one_mul, if_neg (not_le.mpr hn)] using hd.deriv
  · have hmin : IsLocalMin (fun x => |physicalState q c x|) t := by
      apply Filter.Eventually.of_forall
      intro x
      simp only [hz, abs_zero]
      exact abs_nonneg (physicalState q c x)
    simp only [hz, le_refl, if_true, hmin.deriv_eq_zero,
      velocity_zero_at_state_zero q c t ht hm hz]
  · have hd := (hasDerivAt_abs_pos hp).comp t (ht.const_add c)
    simpa only [Function.comp_def, one_mul, if_pos hp.le] using hd.deriv

theorem memLp_deriv_absState (q : Velocity) (c : ℝ) :
    MemLp (deriv (fun t => |physicalState q c t|)) 2 volume := by
  apply (Lp.memLp q).of_le (stronglyMeasurable_deriv _).aestronglyMeasurable
  filter_upwards [ae_deriv_absState q c] with t ht
  rw [ht]
  split_ifs <;> simp

/-- The actual L2 velocity whose anchored primitive is the modulus state. -/
def modulusVelocity (q : Velocity) (c : ℝ) : Velocity :=
  (memLp_deriv_absState q c).toLp (deriv (fun t => |physicalState q c t|))

theorem ae_modulusVelocity (q : Velocity) (c : ℝ) :
    modulusVelocity q c =ᵐ[volume]
      fun t => if 0 ≤ physicalState q c t then q t else -q t :=
  (MemLp.coeFn_toLp (memLp_deriv_absState q c)).trans (ae_deriv_absState q c)

theorem ae_modulusVelocity_sign (q : Velocity) (c : ℝ) :
    modulusVelocity q c =ᵐ[volume]
      fun t => (SignType.sign (physicalState q c t) : ℝ) * q t := by
  filter_upwards [ae_modulusVelocity q c, ae_velocity_zero_on_state_zero q c] with t ht hz
  rw [ht]
  rcases lt_trichotomy (physicalState q c t) 0 with hn | he | hp
  · simp [hn, not_le.mpr hn]
  · simp [he, hz he]
  · simp [hp, hp.le]

theorem ae_modulusVelocity_sq (q : Velocity) (c : ℝ) :
    (fun t => (modulusVelocity q c t)^2) =ᵐ[volume] fun t => (q t)^2 := by
  filter_upwards [ae_modulusVelocity q c] with t ht
  rw [ht]
  split_ifs <;> simp

theorem primitive_modulusVelocity (q : Velocity) (c t : ℝ) :
    |c| + primitive (modulusVelocity q c) t = |physicalState q c t| := by
  have hi : primitive (modulusVelocity q c) t =
      ∫ x in 0..t, deriv (fun u => |physicalState q c u|) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (memLp_deriv_absState q c)] with x hx
    exact fun _ => hx
  rw [hi, (absolutelyContinuous_absState q c 0 t).integral_deriv_eq_sub]
  simp [physicalState, primitive]

theorem energy_modulusVelocity (q : Velocity) (c a b : ℝ) :
    energy (modulusVelocity q c) a b = energy q a b := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_modulusVelocity_sq q c] with t ht
  exact fun _ => ht

theorem logPrimitive_modulusVelocity (q : Velocity) (c x : ℝ) :
    |c| + logPrimitive (modulusVelocity q c) x = |c + logPrimitive q x| :=
  primitive_modulusVelocity q c (Real.exp x)

theorem log_energy_modulusVelocity (q : Velocity) (c a b : ℝ) :
    (∫ x in a..b, Real.exp (-x)*(deriv (logPrimitive (modulusVelocity q c)) x)^2) =
      ∫ x in a..b, Real.exp (-x)*(deriv (logPrimitive q) x)^2 := by
  rw [log_energy_eq, log_energy_eq, energy_modulusVelocity]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
