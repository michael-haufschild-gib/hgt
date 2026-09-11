import GaloisForLFunctions.HTGeometry.FZZCigarBackreactionCriticality
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Neutral FZZ radial zero mode and its coupling Ward boundary

For a fixed nonzero-mode configuration, an exponential winding potential contributes a radial
constant-mode factor `exp(-A * exp(b*x))`. At zero background radial charge there is no additional
linear exponential in the radial measure. Here `b = exp(v)` parametrizes positive slopes.

The real cutoff integral on `(-R, infinity)` exists exactly when `A > 0`. In that chamber write
`A = exp(u)`. The original radial integral equals `E1(exp(u-b*R))/b`. Subtracting the physical radial
length `R` leaves the finite part `-(u+gamma)/b`. The logarithmic coupling derivative, both before
and after removal of the cutoff, retains the boundary contribution tending to `-1/b`.

All source and insertion integrability statements, the change of variables, and differentiation
under the integral are proved. No vanishing boundary condition is assumed. Subtraction of `R` is
the particular geometric volume subtraction audited here; a full source counterterm is not fixed
by this calculation.

This is a radial factor in the positive effective-coupling chamber. The complete winding field
integral can leave that chamber; the exact convergence classification does not construct its
contour or meromorphic continuation. Nonzero modes, external momentum, the full torus Ward identity,
and an RH conclusion remain outside the result.

Source: Halder--Jafferis, arXiv:2402.00932v3, (3.14), (3.26), (3.28)--(3.33). The exponential-integral
constant is reused from the corpus's Dai--Yoshikawa analytic-torsion calculation.
-/

open MeasureTheory Set Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower
noncomputable section

def fzzNeutralRadialCoordinate (u v x : ℝ) : ℝ := Real.exp (u + Real.exp v * x)

def fzzNeutralRadialKernel (u v x : ℝ) : ℝ :=
  Real.exp (-fzzNeutralRadialCoordinate u v x)

def fzzNeutralRadialCutoffIntegral (u v R : ℝ) : ℝ :=
  ∫ x in Ioi (-R), fzzNeutralRadialKernel u v x

private theorem coordinate_deriv (u v x : ℝ) :
    HasDerivAt (fzzNeutralRadialCoordinate u v)
      (fzzNeutralRadialCoordinate u v x * Real.exp v) x := by
  change HasDerivAt (fun x => Real.exp (u + Real.exp v * x))
    (Real.exp (u + Real.exp v * x) * Real.exp v) x
  simpa only [mul_one, id_eq] using
    (((hasDerivAt_id x).const_mul (Real.exp v)).const_add u).exp

private theorem coordinate_inj (u v : ℝ) :
    Function.Injective (fzzNeutralRadialCoordinate u v) := by
  intro x y h
  have h' := Real.exp_injective h
  nlinarith [Real.exp_pos v]

private theorem coordinate_image (u v R : ℝ) :
    fzzNeutralRadialCoordinate u v '' Ioi (-R) = Ioi (Real.exp (u - Real.exp v * R)) := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    change -R < x at hx
    apply Real.exp_lt_exp.mpr
    nlinarith [Real.exp_pos v]
  · intro ht
    change Real.exp (u - Real.exp v * R) < t at ht
    have ht0 : 0 < t := lt_trans (Real.exp_pos _) ht
    have hl : u - Real.exp v * R < Real.log t := by
      apply Real.exp_lt_exp.mp
      simpa only [Real.exp_log ht0] using ht
    refine ⟨(Real.log t - u) / Real.exp v, ?_, ?_⟩
    · apply (lt_div_iff₀ (Real.exp_pos v)).mpr
      linarith
    · unfold fzzNeutralRadialCoordinate
      rw [mul_div_cancel₀ _ (Real.exp_pos v).ne']
      convert Real.exp_log ht0 using 1
      congr 1
      ring

private theorem radial_substitution (u v R : ℝ) (g : ℝ → ℝ) :
    (∫ t in Ioi (Real.exp (u - Real.exp v * R)), g t) =
      ∫ x in Ioi (-R),
        (fzzNeutralRadialCoordinate u v x * Real.exp v) *
          g (fzzNeutralRadialCoordinate u v x) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (-R)) measurableSet_Ioi
    (fun x _ => (coordinate_deriv u v x).hasDerivWithinAt)
    (coordinate_inj u v).injOn g
  rw [coordinate_image] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  change |fzzNeutralRadialCoordinate u v x * Real.exp v| *
      g (fzzNeutralRadialCoordinate u v x) = _
  have hp : 0 < fzzNeutralRadialCoordinate u v x * Real.exp v :=
    mul_pos (Real.exp_pos _) (Real.exp_pos v)
  rw [abs_of_pos hp]

theorem integrableOn_fzzNeutralRadialKernel (u v R : ℝ) :
    IntegrableOn (fzzNeutralRadialKernel u v) (Ioi (-R)) := by
  have hbase : IntegrableOn
      (fun x : ℝ => Real.exp (-u) * Real.exp (-(Real.exp v) * x)) (Ioi (-R)) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos (Real.exp_pos v)) (-R)).const_mul _
  refine hbase.mono' (by
    exact (show Continuous (fzzNeutralRadialKernel u v) by
      unfold fzzNeutralRadialKernel fzzNeutralRadialCoordinate
      fun_prop).aestronglyMeasurable) ?_
  filter_upwards with x
  rw [fzzNeutralRadialKernel, fzzNeutralRadialCoordinate, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [Real.add_one_le_exp (u + Real.exp v * x)]

/-- The original target-radial cutoff integral, including its Jacobian. -/
theorem fzzNeutralRadialCutoffIntegral_eq (u v R : ℝ) :
    fzzNeutralRadialCutoffIntegral u v R =
      DaiYoshikawa.expIntegralE1 (Real.exp (u - Real.exp v * R)) / Real.exp v := by
  have h := radial_substitution u v R (fun t => Real.exp (-t) / t)
  change DaiYoshikawa.expIntegralE1 _ = _ at h
  have heq : (fun x => (fzzNeutralRadialCoordinate u v x * Real.exp v) *
      (Real.exp (-fzzNeutralRadialCoordinate u v x) / fzzNeutralRadialCoordinate u v x)) =
      fun x => Real.exp v * fzzNeutralRadialKernel u v x := by
    funext x
    unfold fzzNeutralRadialKernel
    have hp : fzzNeutralRadialCoordinate u v x ≠ 0 := (Real.exp_pos _).ne'
    field_simp [hp]
  rw [heq, integral_const_mul] at h
  apply (eq_div_iff (Real.exp_pos v).ne').mpr
  simpa only [fzzNeutralRadialCutoffIntegral, mul_comm] using h.symm

/-- The coupling insertion is a boundary contribution, with the complete cutoff retained. -/
theorem fzzNeutralRadialCouplingInsertion_integral (u v R : ℝ) :
    (∫ x in Ioi (-R),
      fzzNeutralRadialCoordinate u v x * fzzNeutralRadialKernel u v x) =
        Real.exp (-Real.exp (u - Real.exp v * R)) / Real.exp v := by
  have h := radial_substitution u v R (fun t => Real.exp (-t))
  rw [integral_exp_neg_Ioi] at h
  have heq : (fun x => (fzzNeutralRadialCoordinate u v x * Real.exp v) *
      Real.exp (-fzzNeutralRadialCoordinate u v x)) =
      fun x => Real.exp v *
        (fzzNeutralRadialCoordinate u v x * fzzNeutralRadialKernel u v x) := by
    funext x
    unfold fzzNeutralRadialKernel
    ring
  rw [heq, integral_const_mul] at h
  apply (eq_div_iff (Real.exp_pos v).ne').mpr
  simpa only [mul_comm] using h.symm

theorem integrableOn_fzzNeutralRadialCouplingInsertion (u v R : ℝ) :
    IntegrableOn (fun x => fzzNeutralRadialCoordinate u v x *
      fzzNeutralRadialKernel u v x) (Ioi (-R)) := by
  by_contra h
  have hz := integral_undef h
  rw [fzzNeutralRadialCouplingInsertion_integral] at hz
  exact (div_pos (Real.exp_pos _) (Real.exp_pos v)).ne' hz

/-- Exact real effective-coupling convergence chamber of the neutral radial source. -/
theorem fzzNeutralRadialSignedKernel_integrable_iff (A v R : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(A * Real.exp (Real.exp v * x))))
      (Ioi (-R)) ↔ 0 < A := by
  constructor
  · intro hi
    by_contra hA
    have hA0 : A ≤ 0 := le_of_not_gt hA
    have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioi (-R))) := by
      refine hi.mono' aestronglyMeasurable_const ?_
      filter_upwards with x
      rw [norm_one]
      exact Real.one_le_exp_iff.mpr
        (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hA0 (Real.exp_pos _).le))
    simp [integrable_const_iff, isFiniteMeasure_iff] at hconst
  · intro hA
    have h := integrableOn_fzzNeutralRadialKernel (Real.log A) v R
    have heq : fzzNeutralRadialKernel (Real.log A) v =
        fun x : ℝ => Real.exp (-(A * Real.exp (Real.exp v * x))) := by
      funext x
      rw [fzzNeutralRadialKernel, fzzNeutralRadialCoordinate, Real.exp_add, Real.exp_log hA]
    rwa [heq] at h

/-- The source itself has the coupling insertion as its negative derivative. -/
theorem hasDerivAt_fzzNeutralRadialKernel_logCoupling (u v x : ℝ) :
    HasDerivAt (fun a => fzzNeutralRadialKernel a v x)
      (-(fzzNeutralRadialCoordinate u v x * fzzNeutralRadialKernel u v x)) u := by
  have hi : HasDerivAt (fun a => fzzNeutralRadialCoordinate a v x)
      (fzzNeutralRadialCoordinate u v x) u := by
    simpa only [fzzNeutralRadialCoordinate, id_eq, mul_one] using
      ((hasDerivAt_id u).add_const (Real.exp v * x)).exp
  have h := hi.neg.exp
  simp only [Pi.neg_apply] at h
  have hc : Real.exp (-fzzNeutralRadialCoordinate u v x) *
      -fzzNeutralRadialCoordinate u v x =
      -(fzzNeutralRadialCoordinate u v x * fzzNeutralRadialKernel u v x) := by
    unfold fzzNeutralRadialKernel
    ring
  rw [hc] at h
  simpa only [fzzNeutralRadialKernel, Pi.neg_apply] using h

def fzzNeutralRadialFinitePart (u v : ℝ) : ℝ :=
  -(u + Real.eulerMascheroniConstant) / Real.exp v

private theorem radial_cutoff_tendsto (u v : ℝ) :
    Tendsto (fun R : ℝ => Real.exp (u - Real.exp v * R)) atTop (𝓝[>] 0) := by
  apply Real.tendsto_exp_atBot_nhdsGT.comp
  apply tendsto_atBot.mpr
  intro m
  filter_upwards [eventually_ge_atTop ((u - m) / Real.exp v)] with R hR
  have h := (div_le_iff₀ (Real.exp_pos v)).mp hR
  linarith

/-- Subtract the physical radial length, retaining the coupling-dependent finite value. -/
theorem fzzNeutralRadialCutoffIntegral_finitePart (u v : ℝ) :
    Tendsto (fun R : ℝ => fzzNeutralRadialCutoffIntegral u v R - R) atTop
      (𝓝 (fzzNeutralRadialFinitePart u v)) := by
  have h := (((DaiYoshikawa.tendsto_expIntegralE1_add_log.comp
    (radial_cutoff_tendsto u v)).sub_const u).div_const (Real.exp v))
  have hv : Real.exp v ≠ 0 := (Real.exp_pos v).ne'
  have heq : (fun R : ℝ => fzzNeutralRadialCutoffIntegral u v R - R) =
      fun R => (DaiYoshikawa.expIntegralE1 (Real.exp (u - Real.exp v * R)) +
        Real.log (Real.exp (u - Real.exp v * R)) - u) / Real.exp v := by
    funext R
    rw [fzzNeutralRadialCutoffIntegral_eq, Real.log_exp]
    field_simp [hv]
    ring
  rw [heq]
  have hvalue : (-Real.eulerMascheroniConstant - u) / Real.exp v =
      fzzNeutralRadialFinitePart u v := by
    unfold fzzNeutralRadialFinitePart
    ring
  rw [hvalue] at h
  simpa only [Function.comp_apply] using h

/-- Exact finite-cutoff logarithmic coupling derivative. -/
theorem hasDerivAt_fzzNeutralRadialCutoffIntegral (u v R : ℝ) :
    HasDerivAt (fun a => fzzNeutralRadialCutoffIntegral a v R)
      (-Real.exp (-Real.exp (u - Real.exp v * R)) / Real.exp v) u := by
  simp_rw [fzzNeutralRadialCutoffIntegral_eq]
  have hi : HasDerivAt (fun a => Real.exp (a - Real.exp v * R))
      (Real.exp (u - Real.exp v * R)) u := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id u).sub_const (Real.exp v * R)).exp)
  have h := ((FZZCigar.hasDerivAt_expIntegralE1
    (Real.exp_pos (u - Real.exp v * R))).comp u hi).div_const (Real.exp v)
  have hc : -Real.exp (-Real.exp (u - Real.exp v * R)) /
      Real.exp (u - Real.exp v * R) * Real.exp (u - Real.exp v * R) =
        -Real.exp (-Real.exp (u - Real.exp v * R)) :=
    div_mul_cancel₀ _ (Real.exp_pos _).ne'
  rw [hc] at h
  simpa only [Function.comp_apply] using h

/-- The differentiated integral equals the negative integrated coupling insertion. -/
theorem fzzNeutralRadialCutoffIntegral_couplingWard (u v R : ℝ) :
    deriv (fun a => fzzNeutralRadialCutoffIntegral a v R) u =
      -(∫ x in Ioi (-R),
        fzzNeutralRadialCoordinate u v x * fzzNeutralRadialKernel u v x) := by
  rw [(hasDerivAt_fzzNeutralRadialCutoffIntegral u v R).deriv,
    fzzNeutralRadialCouplingInsertion_integral]
  ring

/-- Differentiation and the original radial integration agree, with the boundary term retained. -/
theorem fzzNeutralRadialCutoffIntegral_deriv_eq_integral_deriv (u v R : ℝ) :
    deriv (fun a => fzzNeutralRadialCutoffIntegral a v R) u =
      ∫ x in Ioi (-R), deriv (fun a => fzzNeutralRadialKernel a v x) u := by
  simp_rw [(hasDerivAt_fzzNeutralRadialKernel_logCoupling u v _).deriv]
  rw [integral_neg]
  exact fzzNeutralRadialCutoffIntegral_couplingWard u v R

/-- Removing the cutoff retains a nonzero coupling Ward term at radial neutrality. -/
theorem fzzNeutralRadialCutoffIntegral_couplingWard_limit (u v : ℝ) :
    Tendsto (fun R : ℝ => deriv (fun a => fzzNeutralRadialCutoffIntegral a v R) u)
      atTop (𝓝 (-(Real.exp v)⁻¹)) := by
  simp_rw [(hasDerivAt_fzzNeutralRadialCutoffIntegral u v _).deriv]
  have h0 := (radial_cutoff_tendsto u v).mono_right nhdsWithin_le_nhds
  have he := Real.continuous_exp.continuousAt.tendsto.comp h0.neg
  simpa only [Function.comp_apply, neg_zero, Real.exp_zero, neg_div, one_div] using
    he.neg.div_const (Real.exp v)

/-- Differentiating the finite part gives the same boundary contribution. -/
theorem hasDerivAt_fzzNeutralRadialFinitePart (u v : ℝ) :
    HasDerivAt (fun a => fzzNeutralRadialFinitePart a v) (-(Real.exp v)⁻¹) u := by
  simpa only [fzzNeutralRadialFinitePart, id_eq, Pi.neg_apply, neg_div, one_div] using
    (((hasDerivAt_id u).add_const Real.eulerMascheroniConstant).neg).div_const (Real.exp v)

theorem fzzNeutralRadialFinitePart_couplingWard_ne_zero (u v : ℝ) :
    deriv (fun a => fzzNeutralRadialFinitePart a v) u ≠ 0 := by
  rw [(hasDerivAt_fzzNeutralRadialFinitePart u v).deriv]
  exact neg_ne_zero.mpr (inv_ne_zero (Real.exp_pos v).ne')

end
end GaloisForLFunctions.RHTower
