import GaloisForLFunctions.RHTower.SelbergBesselBoundarySlope
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Exact critical Bessel boundary energy for compact cusp profiles

For a compact C¹ profile in logarithmic height, completing the square with the
actual critical Bessel logarithmic derivative gives the weighted mode energy
minus one quarter of its mass as a nonnegative square integral plus the complete
lower seam term. Every integrand is proved integrable.

The seam coefficient is the outgoing derivative proved in
`SelbergBesselBoundarySlope`. Its unique transition gives a sufficient cutoff
strictly below the elementary dimensionless cutoff one half. The theorem does
not assert necessity of that cutoff for all test energies: a negative seam
coefficient alone does not prove existence of a negative-energy compact test.
General Maass Fourier assembly and compact-core gluing are not assumed.
-/

open MeasureTheory Set Filter Topology
open scoped Distributions
namespace GaloisForLFunctions.RHTower.SelbergBesselEnergy
open SelbergBesselSlope
noncomputable section

/-- Compact real C¹ profiles on the whole logarithmic-height line. -/
abbrev Profile := TestFunction (⊤ : TopologicalSpace.Opens ℝ) ℝ 1

/-- The actual critical mode logarithmic derivative. -/
def coefficient (a t : ℝ) : ℝ := 1 / 2 - logSlope (a + t)

/-- C¹ regularity of the exact square-completion coefficient. -/
theorem coefficient_contDiff (a : ℝ) : ContDiff ℝ 1 (coefficient a) :=
  contDiff_const.sub (logSlope_contDiff.comp (contDiff_const.add contDiff_id))

private theorem coefficient_hasDerivAt (a t : ℝ) :
    HasDerivAt (coefficient a) (-(logSlope (a + t) ^ 2 - Real.exp (a + t) ^ 2)) t := by
  convert ((logSlope_hasDerivAt (a + t)).comp t
    ((hasDerivAt_id t).const_add a)).const_sub (1 / 2) using 1 <;> try rfl
  simp only [mul_one]

private theorem compact_mul_left (u v : ℝ → ℝ) (hv : HasCompactSupport v) :
    HasCompactSupport (fun t => u t * v t) := by
  convert hv.mul_left (f := u) using 1 <;> rfl

private theorem compact_sq (u : ℝ → ℝ) (hu : HasCompactSupport u) :
    HasCompactSupport (fun t => u t ^ 2) := by
  simpa only [pow_two] using compact_mul_left u u hu

/-- The complete weighted lower-boundary flux. -/
def flux (f : Profile) (a t : ℝ) : ℝ := Real.exp (-t) * coefficient a t * f t ^ 2

/-- The flux is C¹ on the full real line. -/
theorem flux_contDiff (f : Profile) (a : ℝ) : ContDiff ℝ 1 (flux f a) :=
  (contDiff_id.neg.exp.mul (coefficient_contDiff a)).mul (f.contDiff.pow 2)

/-- Its upper endpoint vanishes because its profile factor has compact support. -/
theorem flux_compact (f : Profile) (a : ℝ) : HasCompactSupport (flux f a) :=
  compact_mul_left _ _ (compact_sq f f.hasCompactSupport)

private theorem flux_hasDerivAt (f : Profile) (a t : ℝ) :
    HasDerivAt (flux f a)
      (Real.exp (-t) * ((-coefficient a t - logSlope (a + t) ^ 2 + Real.exp (a + t) ^ 2) *
        f t ^ 2 + 2 * coefficient a t * f t * deriv f t)) t := by
  have he := (hasDerivAt_id t).neg.exp
  have hf := (f.contDiff.differentiable one_ne_zero t).hasDerivAt
  convert (he.mul (coefficient_hasDerivAt a t)).mul (hf.pow 2) using 1 <;> try rfl
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, id_eq]
  ring

/-- The nonnegative remainder after the exact Bessel square completion. -/
def squareField (f : Profile) (a t : ℝ) : ℝ :=
  Real.exp (-t) * (deriv f t - coefficient a t * f t) ^ 2

/-- The nonzero-mode energy minus one quarter of mass, in logarithmic height. -/
def excessField (f : Profile) (a t : ℝ) : ℝ :=
  Real.exp (-t) * (deriv f t ^ 2 + (Real.exp (a + t) ^ 2 - 1 / 4) * f t ^ 2)

private theorem field_decomposition (f : Profile) (a t : ℝ) :
    excessField f a t = squareField f a t + deriv (flux f a) t := by
  rw [(flux_hasDerivAt f a t).deriv]
  unfold excessField squareField coefficient
  ring

/-- The actual square remainder is integrable. -/
theorem squareField_integrable (f : Profile) (a : ℝ) : Integrable (squareField f a) := by
  have hc : Continuous (fun t => deriv f t - coefficient a t * f t) :=
    (f.contDiff.continuous_deriv le_rfl).sub ((coefficient_contDiff a).continuous.mul f.continuous)
  have hs : HasCompactSupport (fun t => deriv f t - coefficient a t * f t) :=
    f.hasCompactSupport.deriv.sub (compact_mul_left _ _ f.hasCompactSupport)
  exact (Real.continuous_exp.comp continuous_id.neg |>.mul (hc.pow 2)).integrable_of_hasCompactSupport
    (compact_mul_left _ _ (compact_sq _ hs))

private theorem flux_deriv_integrable (f : Profile) (a : ℝ) : Integrable (deriv (flux f a)) :=
  ((flux_contDiff f a).continuous_deriv le_rfl).integrable_of_hasCompactSupport (flux_compact f a).deriv

/-- The actual quarter-energy excess is integrable. -/
theorem excessField_integrable (f : Profile) (a : ℝ) : Integrable (excessField f a) := by
  have he : excessField f a = fun t => squareField f a t + deriv (flux f a) t :=
    funext (field_decomposition f a)
  rw [he]
  exact (squareField_integrable f a).add (flux_deriv_integrable f a)

/-- Exact Bessel ground-state identity, with unrestricted lower trace retained. -/
theorem critical_boundary_identity (f : Profile) (a T : ℝ) :
    (∫ t in Ioi T, excessField f a t) = (∫ t in Ioi T, squareField f a t) +
      outgoing a T * f T ^ 2 := by
  have he : (∫ t in Ioi T, excessField f a t) =
      ∫ t in Ioi T, squareField f a t + deriv (flux f a) t := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (field_decomposition f a)
  have hadd := integral_add ((squareField_integrable f a).integrableOn (s := Ioi T))
    ((flux_deriv_integrable f a).integrableOn (s := Ioi T))
  rw [he, hadd, HasCompactSupport.integral_Ioi_deriv_eq (flux_contDiff f a) (flux_compact f a)]
  rw [outgoing_eq]
  unfold flux coefficient
  rw [Real.exp_neg]
  ring

/-- The boundary coefficient gives a lower bound at every cutoff. -/
theorem exact_boundary_lower_bound (f : Profile) (a T : ℝ) :
    outgoing a T * f T ^ 2 ≤ ∫ t in Ioi T, excessField f a t := by
  rw [critical_boundary_identity]
  have hs : 0 ≤ ∫ t in Ioi T, squareField f a t :=
    integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  linarith

/-- The isolated tail excess is nonnegative at every cutoff above the transition. -/
theorem cusp_quarter_at_transition (f : Profile) (a u : ℝ) :
    0 ≤ ∫ t in Ioi (transition - a + u ^ 2), excessField f a t := by
  apply le_trans _ (exact_boundary_lower_bound f a _)
  apply mul_nonneg _ (sq_nonneg _)
  have hh : 1 / 2 ≤ logSlope (a + (transition - a + u ^ 2)) := by
    rw [← transition_eq]
    apply logSlope_strictMono.monotone
    nlinarith [sq_nonneg u]
  rw [outgoing_eq]
  exact div_nonneg (sub_nonneg.mpr hh) (Real.exp_pos _).le

/-- The cutoff parameterization covers exactly the whole sufficient range. -/
theorem range_tail_cutoff (a : ℝ) :
    Set.range (fun u : ℝ => transition - a + u ^ 2) = Ici (transition - a) := by
  ext T
  constructor
  · rintro ⟨u, rfl⟩
    exact le_add_of_nonneg_right (sq_nonneg u)
  · intro hT
    refine ⟨Real.sqrt (T - (transition - a)), ?_⟩
    change transition - a + Real.sqrt (T - (transition - a)) ^ 2 = T
    rw [Real.sq_sqrt (sub_nonneg.mpr hT)]
    ring

private theorem weighted_sq_integrable (v w : ℝ → ℝ) (hv : Continuous v)
    (hw : Continuous w) (hs : HasCompactSupport v) : Integrable (fun t => w t * v t ^ 2) :=
  (hw.mul (hv.pow 2)).integrable_of_hasCompactSupport (compact_mul_left _ _ (compact_sq v hs))

/-- One quarter of the actual weighted mass is bounded by the kinetic and horizontal energies. -/
theorem cusp_tail_quarter (f : Profile) (a u : ℝ) :
    (1 / 4) * (∫ t in Ioi (transition - a + u ^ 2), Real.exp (-t) * f t ^ 2) ≤
      (∫ t in Ioi (transition - a + u ^ 2), Real.exp (-t) * deriv f t ^ 2) +
      (∫ t in Ioi (transition - a + u ^ 2), Real.exp (-t) * Real.exp (a + t) ^ 2 * f t ^ 2) := by
  let T := transition - a + u ^ 2
  have hm : IntegrableOn (fun t => Real.exp (-t) * f t ^ 2) (Ioi T) :=
    (weighted_sq_integrable f (fun t => Real.exp (-t)) f.continuous
      (by fun_prop) f.hasCompactSupport).integrableOn
  have hk : IntegrableOn (fun t => Real.exp (-t) * deriv f t ^ 2) (Ioi T) :=
    (weighted_sq_integrable (deriv f) (fun t => Real.exp (-t))
      (f.contDiff.continuous_deriv le_rfl) (by fun_prop) f.hasCompactSupport.deriv).integrableOn
  have hp : IntegrableOn (fun t => Real.exp (-t) * Real.exp (a + t) ^ 2 * f t ^ 2) (Ioi T) :=
    (weighted_sq_integrable f (fun t => Real.exp (-t) * Real.exp (a + t) ^ 2)
      f.continuous (by fun_prop) f.hasCompactSupport).integrableOn
  have he : (∫ t in Ioi T, excessField f a t) =
      (∫ t in Ioi T, Real.exp (-t) * deriv f t ^ 2) +
      (∫ t in Ioi T, Real.exp (-t) * Real.exp (a + t) ^ 2 * f t ^ 2) -
      (∫ t in Ioi T, Real.exp (-t) * f t ^ 2) / 4 := by
    have hfun : excessField f a = fun t => Real.exp (-t) * deriv f t ^ 2 +
        Real.exp (-t) * Real.exp (a + t) ^ 2 * f t ^ 2 - Real.exp (-t) * f t ^ 2 / 4 := by
      funext t; unfold excessField; ring
    have hsub := integral_sub (hk.add hp) (hm.div_const 4)
    simp only [Pi.add_apply] at hsub
    rw [hfun, hsub, integral_add hk hp, integral_div]
  have hpos := cusp_quarter_at_transition f a u
  change 0 ≤ ∫ t in Ioi T, excessField f a t at hpos
  rw [he] at hpos
  change _ ≤ (∫ t in Ioi T, Real.exp (-t) * deriv f t ^ 2) +
    (∫ t in Ioi T, Real.exp (-t) * Real.exp (a + t) ^ 2 * f t ^ 2)
  linarith

end
end GaloisForLFunctions.RHTower.SelbergBesselEnergy
