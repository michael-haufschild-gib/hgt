import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

/-!
# Reciprocal scaling, canonical action, and its Noether charge

The first-order complex Lagrangian `p vq - a q p` has reciprocal scaling
symmetry. Its real and imaginary parts give two real actions and two real
charges. The off-shell variation identity identifies their common complex
charge as `q p`. Explicit exponential trajectories satisfy both canonical
equations and conserve this charge for every initial value.

Variation of the rate while holding the field and velocity fixed detects
the charge. In contrast, the Lagrangian vanishes on every canonical
trajectory, including trajectories with nonzero charge.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Reciprocal dilation of a complex canonical coordinate and momentum. -/
def reciprocalScale (s : ℝ) (z : ℂ × ℂ) : ℂ × ℂ :=
  ((Real.exp s : ℂ) * z.1, (Real.exp (-s) : ℂ) * z.2)

/-- The canonical first-order Lagrangian, before taking real or imaginary parts. -/
def reciprocalScaleLagrangian (a : ℂ) (z v : ℂ × ℂ) : ℂ :=
  z.2 * v.1 - a * (z.1 * z.2)

/-- Charge of simultaneous coordinate dilation and reciprocal momentum dilation. -/
def reciprocalScaleCharge (z : ℂ × ℂ) : ℂ := z.1 * z.2

/-- The canonical velocity field of the bilinear Hamiltonian. -/
def reciprocalScaleVelocity (a : ℂ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (a * z.1, -a * z.2)

private theorem reciprocalExp_cancel (s : ℝ) :
    (Real.exp s : ℂ) * (Real.exp (-s) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  simp

theorem reciprocalScaleCharge_scale (s : ℝ) (z : ℂ × ℂ) :
    reciprocalScaleCharge (reciprocalScale s z) = reciprocalScaleCharge z := by
  change ((Real.exp s : ℂ) * z.1) * ((Real.exp (-s) : ℂ) * z.2) = _
  calc
    _ = ((Real.exp s : ℂ) * (Real.exp (-s) : ℂ)) * (z.1 * z.2) := by ring
    _ = _ := by rw [reciprocalExp_cancel, one_mul]; rfl

/-- The continuous symmetry preserves the Lagrangian at every field and velocity. -/
theorem reciprocalScaleLagrangian_symmetry (a : ℂ) (s : ℝ) (z v : ℂ × ℂ) :
    reciprocalScaleLagrangian a (reciprocalScale s z) (reciprocalScale s v) =
      reciprocalScaleLagrangian a z v := by
  unfold reciprocalScaleLagrangian reciprocalScale
  dsimp only
  calc
    _ = ((Real.exp s : ℂ) * (Real.exp (-s) : ℂ)) *
        (z.2 * v.1 - a * (z.1 * z.2)) := by ring
    _ = _ := by rw [reciprocalExp_cancel, one_mul]

theorem reciprocalScale_continuous (z : ℂ × ℂ) :
    Continuous (fun s => reciprocalScale s z) := by
  unfold reciprocalScale
  fun_prop

/-- Both real components of the action inherit the same pointwise symmetry. -/
def reciprocalScaleAction (a : ℂ) (z : ℝ → ℂ × ℂ) (l r : ℝ) : ℂ :=
  ∫ t in l..r, reciprocalScaleLagrangian a (z t)
    (deriv (fun u => (z u).1) t, deriv (fun u => (z u).2) t)

theorem reciprocalScaleAction_symmetry
    (a : ℂ) (s : ℝ) (z : ℝ → ℂ × ℂ) (l r : ℝ) :
    reciprocalScaleAction a (fun t => reciprocalScale s (z t)) l r =
      reciprocalScaleAction a z l r := by
  unfold reciprocalScaleAction
  apply intervalIntegral.integral_congr
  intro t _
  simpa only [reciprocalScale, deriv_const_mul_field] using
    reciprocalScaleLagrangian_symmetry a s (z t)
      (deriv (fun u => (z u).1) t, deriv (fun u => (z u).2) t)

/-- The polynomial first variation is the actual complex derivative in the variation parameter. -/
theorem hasDerivAt_reciprocalScale_firstVariation
    (a : ℂ) (z v eta w : ℂ × ℂ) :
    HasDerivAt (fun e : ℂ => reciprocalScaleLagrangian a
      (z.1 + e * eta.1, z.2 + e * eta.2) (v.1 + e * w.1, v.2 + e * w.2))
      (eta.2 * v.1 + z.2 * w.1 - a * (eta.1 * z.2 + z.1 * eta.2)) 0 := by
  have hq := (hasDerivAt_const (0 : ℂ) z.1).add ((hasDerivAt_id 0).mul_const eta.1)
  have hp := (hasDerivAt_const (0 : ℂ) z.2).add ((hasDerivAt_id 0).mul_const eta.2)
  have hv := (hasDerivAt_const (0 : ℂ) v.1).add ((hasDerivAt_id 0).mul_const w.1)
  convert! (hp.mul hv).sub ((hq.mul hp).const_mul a) using 1
  simp

/-- First variation decomposes into the two canonical equations and a boundary term.
Here `w` is the derivative of the field variation `eta`. -/
theorem reciprocalScale_firstVariation_identity
    (a : ℂ) (z v eta w : ℂ × ℂ) :
    eta.2 * v.1 + z.2 * w.1 - a * (eta.1 * z.2 + z.1 * eta.2) =
      (v.1 - a * z.1) * eta.2 + (-v.2 - a * z.2) * eta.1 +
        (v.2 * eta.1 + z.2 * w.1) := by
  ring

/-- Off-shell Noether identity: the derivative of `q p` is precisely the
canonical equation residual paired with the scaling generator. -/
theorem reciprocalScale_noether_identity (a : ℂ) (z v : ℂ × ℂ) :
    v.1 * z.2 + z.1 * v.2 =
      (v.1 - a * z.1) * z.2 - (-v.2 - a * z.2) * z.1 := by
  ring

/-- The two Euler--Lagrange residuals vanish on the explicit canonical velocity. -/
theorem reciprocalScale_eulerLagrange (a : ℂ) (z : ℂ × ℂ) :
    (reciprocalScaleVelocity a z).1 - a * z.1 = 0 ∧
      -(reciprocalScaleVelocity a z).2 - a * z.2 = 0 := by
  simp [reciprocalScaleVelocity]

theorem hasDerivAt_reciprocalScale_fst (a t : ℝ) (z : ℂ × ℂ) :
    HasDerivAt (fun u => (reciprocalScale (a * u) z).1)
      ((a : ℂ) * (reciprocalScale (a * t) z).1) t := by
  have h := (((hasDerivAt_id t).const_mul a).exp.ofReal_comp).mul_const z.1
  convert! h using 1
  simp [reciprocalScale]
  ring

theorem hasDerivAt_reciprocalScale_snd (a t : ℝ) (z : ℂ × ℂ) :
    HasDerivAt (fun u => (reciprocalScale (a * u) z).2)
      (-(a : ℂ) * (reciprocalScale (a * t) z).2) t := by
  have h := ((((hasDerivAt_id t).const_mul a).neg).exp.ofReal_comp).mul_const z.2
  convert! h using 1
  simp [reciprocalScale]
  ring

/-- Noether conservation on all explicit canonical solutions, with no condition on the charge. -/
theorem hasDerivAt_reciprocalScaleCharge (a t : ℝ) (z : ℂ × ℂ) :
    HasDerivAt (fun u => reciprocalScaleCharge (reciprocalScale (a * u) z)) 0 t := by
  simpa only [reciprocalScaleCharge_scale] using
    hasDerivAt_const t (reciprocalScaleCharge z)

/-- Every complex conserved value is realized by the same action and symmetry. -/
theorem reciprocalScaleCharge_realizes (c : ℂ) (t : ℝ) :
    reciprocalScaleCharge (reciprocalScale t (1, c)) = c := by
  rw [reciprocalScaleCharge_scale]
  simp [reciprocalScaleCharge]

/-- Moving along the solution family makes the action density zero at every charge. -/
theorem reciprocalScaleLagrangian_onShell (a : ℂ) (z : ℂ × ℂ) :
    reciprocalScaleLagrangian a z (reciprocalScaleVelocity a z) = 0 := by
  simp only [reciprocalScaleLagrangian, reciprocalScaleVelocity]
  ring

/-- The action evaluated on any explicit canonical trajectory is zero, at every charge. -/
theorem reciprocalScaleAction_onShell (a : ℝ) (z : ℂ × ℂ) (l r : ℝ) :
    reciprocalScaleAction a (fun t => reciprocalScale (a * t) z) l r = 0 := by
  have hv (t : ℝ) :
      (deriv (fun u => (reciprocalScale (a * u) z).1) t,
       deriv (fun u => (reciprocalScale (a * u) z).2) t) =
        reciprocalScaleVelocity a (reciprocalScale (a * t) z) := by
    exact Prod.ext (hasDerivAt_reciprocalScale_fst a t z).deriv
      (hasDerivAt_reciprocalScale_snd a t z).deriv
  simp only [reciprocalScaleAction, hv, reciprocalScaleLagrangian_onShell,
    intervalIntegral.integral_zero]

/-- Holding the trajectory jet fixed and varying the rate exposes the Noether charge. -/
theorem reciprocalScaleLagrangian_rateShift (a b : ℂ) (z v : ℂ × ℂ) :
    reciprocalScaleLagrangian (a + b) z v - reciprocalScaleLagrangian a z v =
      -b * reciprocalScaleCharge z := by
  unfold reciprocalScaleLagrangian reciprocalScaleCharge
  ring

theorem hasDerivAt_reciprocalScaleLagrangian_rate (a : ℂ) (z v : ℂ × ℂ) :
    HasDerivAt (fun b => reciprocalScaleLagrangian b z v)
      (-reciprocalScaleCharge z) a := by
  simpa [reciprocalScaleLagrangian, reciprocalScaleCharge] using!
    (hasDerivAt_const a (z.2 * v.1)).sub
      ((hasDerivAt_id a).mul_const (z.1 * z.2))

/-- Rate independence at fixed field and velocity is exactly zero Noether charge. -/
theorem reciprocalScaleLagrangian_rate_independent_iff (a : ℂ) (z v : ℂ × ℂ) :
    (∀ b, reciprocalScaleLagrangian (a + b) z v = reciprocalScaleLagrangian a z v) ↔
      reciprocalScaleCharge z = 0 := by
  constructor
  · intro h
    have he := reciprocalScaleLagrangian_rateShift a 1 z v
    rw [h 1, sub_self] at he
    simpa using he.symm
  · intro h b
    apply sub_eq_zero.mp
    rw [reciprocalScaleLagrangian_rateShift, h, mul_zero]

/-- The conjugate charge gives an exact descent direction for the real action density. -/
theorem reciprocalScaleLagrangian_chargeDescent (a : ℂ) (z v : ℂ × ℂ) (t : ℝ) :
    (reciprocalScaleLagrangian
      (a + (t : ℂ) * (starRingEnd ℂ) (reciprocalScaleCharge z)) z v).re =
      (reciprocalScaleLagrangian a z v).re - t * Complex.normSq (reciprocalScaleCharge z) := by
  have h := reciprocalScaleLagrangian_rateShift a
    ((t : ℂ) * (starRingEnd ℂ) (reciprocalScaleCharge z)) z v
  rw [neg_mul, mul_assoc, ← Complex.normSq_eq_conj_mul_self] at h
  have hr := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hr
  exact sub_eq_iff_eq_add.mp hr |>.trans (by ring)

/-- A free complex rate has a real action minimum exactly on the zero-charge locus. -/
theorem reciprocalScaleLagrangian_rate_minimum_iff (z v : ℂ × ℂ) :
    (∃ a : ℂ, ∀ b : ℂ, (reciprocalScaleLagrangian a z v).re ≤
      (reciprocalScaleLagrangian b z v).re) ↔ reciprocalScaleCharge z = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    have h := ha (a + (1 : ℂ) * (starRingEnd ℂ) (reciprocalScaleCharge z))
    have hd := reciprocalScaleLagrangian_chargeDescent a z v 1
    simp only [Complex.ofReal_one] at hd
    rw [hd] at h
    have hn : Complex.normSq (reciprocalScaleCharge z) = 0 := by
      have := Complex.normSq_nonneg (reciprocalScaleCharge z)
      linarith
    exact Complex.normSq_eq_zero.mp hn
  · intro h
    refine ⟨0, fun b => le_of_eq ?_⟩
    have he := (reciprocalScaleLagrangian_rate_independent_iff 0 z v).mpr h b
    simpa only [zero_add] using (congrArg Complex.re he).symm

end GaloisForLFunctions.HTGeometry
