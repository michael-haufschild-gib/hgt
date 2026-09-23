import GaloisForLFunctions.RHTower.SelbergBesselBoundaryEnergy
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Sharp trace-constrained critical cusp energy

The actual outgoing Bessel coefficient is the infimum of the quarter-energy
excess over compact real C¹ log-height profiles with unit lower trace.
An explicit rescaled compact cutoff of the actual critical mode approaches it,
with a frequency-independent remainder bound proportional to the inverse scale.

Consequently the critical transition is necessary and sufficient for
nonnegativity of every isolated compact tail profile. Below it, the construction
supplies actual compact negative-energy tests. These are isolated cusp tests;
no Maass automorphic extension or positivity of the coupled core is asserted.
-/

open MeasureTheory Set Filter Topology
open scoped Distributions
namespace GaloisForLFunctions.RHTower.SelbergBesselTrace
open SelbergBesselSlope SelbergBesselEnergy
noncomputable section

/-- C¹ regularity of the actual critical mode on the full log-height line. -/
theorem logMode_contDiff (a : ℝ) : ContDiff ℝ 1 (logMode a) := by
  apply contDiff_one_iff_deriv.mpr
  have hc : Continuous (logMode a) :=
    continuous_iff_continuousAt.mpr (fun t => (logMode_hasDerivAt a t).continuousAt)
  have he : deriv (logMode a) = fun t => (1 / 2 - logSlope (a + t)) * logMode a t :=
    funext (fun t => (logMode_hasDerivAt a t).deriv)
  refine ⟨fun t => (logMode_hasDerivAt a t).differentiableAt, ?_⟩
  rw [he]
  exact ((continuous_const.sub (logSlope_contDiff.continuous.comp
    (continuous_const.add continuous_id))).mul hc)

/-- The actual order-zero Bessel factor decreases with logarithmic height. -/
theorem logK_zero_antitone (a : ℝ) : Antitone (fun t => K 0 (Real.exp (a + t))) := by
  have hd (t : ℝ) : HasDerivAt (fun t => K 0 (Real.exp (a + t)))
      (-K 1 (Real.exp (a + t)) * Real.exp (a + t)) t := by
    convert (K_zero_hasDerivAt (Real.exp_pos (a + t))).comp t
      (((hasDerivAt_id t).const_add a).exp) using 1 <;> try rfl
    simp only [mul_one, id_eq]
  apply antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (K_pos (Real.exp_pos _) 1).le)
    (Real.exp_pos _).le

/-- The height weight cancels the actual mode half-density exactly. -/
theorem weighted_mode_square (a t : ℝ) :
    Real.exp (-t) * logMode a t ^ (2 : ℕ) = K 0 (Real.exp (a + t)) ^ (2 : ℕ) := by
  have he : Real.exp (t / 2) ^ (2 : ℕ) = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [logMode, mul_pow, he, Real.exp_neg]
  field_simp

private theorem normalized_weight_le (a T t : ℝ) (ht : T ≤ t) :
    Real.exp (-t) * (logMode a t / logMode a T) ^ (2 : ℕ) ≤ Real.exp (-T) := by
  have hk := logK_zero_antitone a ht
  have hk2 : K 0 (Real.exp (a + t)) ^ (2 : ℕ) ≤ K 0 (Real.exp (a + T)) ^ (2 : ℕ) := by
    nlinarith [K_pos (Real.exp_pos (a + t)) 0, K_pos (Real.exp_pos (a + T)) 0]
  rw [div_pow, ← mul_div_assoc, weighted_mode_square]
  calc
    _ ≤ K 0 (Real.exp (a + T)) ^ (2 : ℕ) / logMode a T ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right hk2 (sq_nonneg _)
    _ = Real.exp (-T) := by
      apply (div_eq_iff (pow_ne_zero _ (logMode_pos a T).ne')).mpr
      exact (weighted_mode_square a T).symm

private theorem exists_seed : ∃ f : Profile, f 0 = 1 := by
  obtain ⟨f, _, hs, hc, _, hf⟩ := exists_contDiff_tsupport_subset
    (s := (univ : Set ℝ)) (x := 0) (n := 1) Filter.univ_mem
  exact ⟨⟨f, hc, hs, by intro t _; trivial⟩, hf⟩

/-- One fixed compact C¹ cutoff, selected independently of frequency, height, and scale. -/
def seed : Profile := Classical.choose exists_seed

/-- The selected cutoff has unit central value. -/
theorem seed_zero : seed 0 = 1 := Classical.choose_spec exists_seed

/-- Affine log-height rescaling by an arbitrary positive exponential scale. -/
def rescale (T ell : ℝ) : ℝ ≃ₜ ℝ where
  toFun t := (t - T) / Real.exp ell
  invFun x := x * Real.exp ell + T
  left_inv t := by field_simp; ring
  right_inv x := by field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The rescaling is C¹ everywhere. -/
theorem rescale_contDiff (T ell : ℝ) : ContDiff ℝ 1 (rescale T ell) := by
  change ContDiff ℝ 1 (fun t : ℝ => (t - T) / Real.exp ell)
  fun_prop

private theorem compact_mul (u v : ℝ → ℝ) (hu : HasCompactSupport u) :
    HasCompactSupport (fun t => u t * v t) := by
  convert hu.mul_right (f' := v) using 1 <;> rfl

/-- Compact approximation of the normalized actual critical Bessel profile. -/
def approximation (a T ell : ℝ) : Profile where
  toFun t := seed (rescale T ell t) * (logMode a t / logMode a T)
  contDiff' := (seed.contDiff.comp (rescale_contDiff T ell)).mul
    ((logMode_contDiff a).div_const _)
  hasCompactSupport' := compact_mul _ _ (seed.hasCompactSupport.comp_homeomorph (rescale T ell))
  tsupport_subset' := by intro t _; trivial

/-- Every approximant has exactly unit lower trace. -/
theorem approximation_trace (a T ell : ℝ) : approximation a T ell T = 1 := by
  change seed ((T - T) / Real.exp ell) * (logMode a T / logMode a T) = 1
  rw [sub_self, zero_div, seed_zero, div_self (logMode_pos a T).ne', one_mul]

/-- Actual derivative of the rescaled cutoff, including its inverse scale. -/
def cutoffSlope (T ell t : ℝ) : ℝ := deriv seed (rescale T ell t) / Real.exp ell

/-- The cutoff derivative is continuous. -/
theorem cutoffSlope_continuous (T ell : ℝ) : Continuous (cutoffSlope T ell) :=
  ((seed.contDiff.continuous_deriv le_rfl).comp (rescale T ell).continuous).div_const _

/-- The cutoff derivative retains compact support under rescaling. -/
theorem cutoffSlope_compact (T ell : ℝ) : HasCompactSupport (cutoffSlope T ell) := by
  have hs := seed.hasCompactSupport.deriv.comp_homeomorph (rescale T ell)
  convert compact_mul _ (fun _ => (Real.exp ell)⁻¹) hs using 1
  rfl

/-- The actual squared cutoff derivative is integrable. -/
theorem cutoffSlope_sq_integrable (T ell : ℝ) : Integrable (fun t => cutoffSlope T ell t ^ (2 : ℕ)) := by
  apply ((cutoffSlope_continuous T ell).pow 2).integrable_of_hasCompactSupport
  convert compact_mul (cutoffSlope T ell) (cutoffSlope T ell) (cutoffSlope_compact T ell) using 1 <;>
    first | rfl | (funext t; simp only [Pi.pow_apply, pow_two])

/-- The exact derivative retains the cutoff error and critical-mode terms. -/
theorem approximation_hasDerivAt (a T ell t : ℝ) :
    HasDerivAt (approximation a T ell)
      (cutoffSlope T ell t * (logMode a t / logMode a T) +
        coefficient a t * approximation a T ell t) t := by
  have hr : HasDerivAt (rescale T ell) (1 / Real.exp ell) t := by
    convert ((hasDerivAt_id t).sub_const T).div_const (Real.exp ell) using 1 <;> rfl
  have hs := (seed.contDiff.differentiable one_ne_zero (rescale T ell t)).hasDerivAt.comp t hr
  have hg := (logMode_hasDerivAt a t).div_const (logMode a T)
  convert hs.mul hg using 1 <;> try rfl
  symm
  change (deriv seed (rescale T ell t) * (1 / Real.exp ell)) * (logMode a t / logMode a T) +
    seed (rescale T ell t) * ((1 / 2 - logSlope (a + t)) * logMode a t / logMode a T) = _
  unfold cutoffSlope coefficient
  change _ = _ + (1 / 2 - logSlope (a + t)) *
    (seed (rescale T ell t) * (logMode a t / logMode a T))
  ring

/-- The critical square remainder contains only the differentiated cutoff. -/
theorem approximation_square (a T ell t : ℝ) :
    squareField (approximation a T ell) a t =
      (Real.exp (-t) * (logMode a t / logMode a T) ^ (2 : ℕ)) * cutoffSlope T ell t ^ (2 : ℕ) := by
  rw [squareField, (approximation_hasDerivAt a T ell t).deriv]
  ring

/-- The squared-derivative integral of the single fixed cutoff. -/
def seedEnergy : ℝ := ∫ t, deriv seed t ^ (2 : ℕ)

/-- The cutoff energy is nonnegative. -/
theorem seedEnergy_nonneg : 0 ≤ seedEnergy := integral_nonneg (fun _ => sq_nonneg _)

/-- Exact inverse-scale law for the squared cutoff derivative integral. -/
theorem integral_cutoffSlope_sq (T ell : ℝ) :
    (∫ t, cutoffSlope T ell t ^ (2 : ℕ)) = seedEnergy / Real.exp ell := by
  have hfun : (fun t => cutoffSlope T ell t ^ (2 : ℕ)) =
      fun t => (deriv seed ((t - T) / Real.exp ell)) ^ (2 : ℕ) / Real.exp ell ^ (2 : ℕ) := by
    funext t
    exact div_pow _ _ _
  rw [hfun, integral_div]
  have htrans := integral_sub_right_eq_self (μ := volume)
    (fun t : ℝ => deriv seed (t / Real.exp ell) ^ (2 : ℕ)) T
  rw [htrans, Measure.integral_comp_div (fun t => deriv seed t ^ (2 : ℕ)),
    abs_of_pos (Real.exp_pos ell), smul_eq_mul]
  unfold seedEnergy
  field_simp

/-- Frequency-independent upper bound on the compact approximation remainder. -/
theorem approximation_remainder_bound (a T ell : ℝ) :
    (∫ t in Ioi T, squareField (approximation a T ell) a t) ≤
      Real.exp (-T) * seedEnergy / Real.exp ell := by
  have hmaj := (cutoffSlope_sq_integrable T ell).const_mul (Real.exp (-T))
  calc
    _ ≤ ∫ t in Ioi T, Real.exp (-T) * cutoffSlope T ell t ^ (2 : ℕ) := by
      apply integral_mono_ae (squareField_integrable (approximation a T ell) a).integrableOn
        hmaj.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [approximation_square]
      exact mul_le_mul_of_nonneg_right (normalized_weight_le a T t ht.le) (sq_nonneg _)
    _ ≤ ∫ t, Real.exp (-T) * cutoffSlope T ell t ^ (2 : ℕ) :=
      setIntegral_le_integral hmaj (Eventually.of_forall (fun t =>
        mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
    _ = _ := by rw [integral_const_mul, integral_cutoffSlope_sq]; ring

/-- The actual isolated-tail quarter-energy excess of a compact C¹ profile. -/
def energy (f : Profile) (a T : ℝ) : ℝ := ∫ t in Ioi T, excessField f a t

/-- Actual approximant energies approach the boundary coefficient from above. -/
theorem approximation_energy_bounds (a T ell : ℝ) :
    outgoing a T ≤ energy (approximation a T ell) a T ∧
      energy (approximation a T ell) a T ≤
        outgoing a T + Real.exp (-T) * seedEnergy / Real.exp ell := by
  have hi := critical_boundary_identity (approximation a T ell) a T
  rw [approximation_trace, one_pow, mul_one] at hi
  change energy (approximation a T ell) a T = _ at hi
  have hsq : 0 ≤ ∫ t in Ioi T, squareField (approximation a T ell) a t :=
    integral_nonneg (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
  constructor <;> linarith [approximation_remainder_bound a T ell]

/-- An explicit logarithmic scale for each positive exponential error tolerance. -/
def accuracyScale (T e : ℝ) : ℝ := Real.log (1 + Real.exp (-T) * seedEnergy / Real.exp e)

/-- The selected scale makes the remainder strictly smaller than the tolerance. -/
theorem accuracyScale_error_lt (T e : ℝ) :
    Real.exp (-T) * seedEnergy / Real.exp (accuracyScale T e) < Real.exp e := by
  have hC : 0 ≤ Real.exp (-T) * seedEnergy := mul_nonneg (Real.exp_pos _).le seedEnergy_nonneg
  have hL : 0 < 1 + Real.exp (-T) * seedEnergy / Real.exp e := by positivity
  rw [accuracyScale, Real.exp_log hL, div_lt_iff₀ hL]
  have he : Real.exp e * (Real.exp (-T) * seedEnergy / Real.exp e) = Real.exp (-T) * seedEnergy := by
    field_simp
  nlinarith [Real.exp_pos e]

/-- Unit-trace compact witnesses approach the actual outgoing coefficient arbitrarily closely. -/
theorem unit_trace_approximation (a T e : ℝ) :
    approximation a T (accuracyScale T e) T = 1 ∧
      energy (approximation a T (accuracyScale T e)) a T < outgoing a T + Real.exp e := by
  refine ⟨approximation_trace _ _ _, ?_⟩
  linarith [(approximation_energy_bounds a T (accuracyScale T e)).2, accuracyScale_error_lt T e]

/-- The actual energy values of all compact C¹ profiles with unit lower trace. -/
def traceEnergies (a T : ℝ) : Set ℝ := {E | ∃ f : Profile, f T = 1 ∧ energy f a T = E}

/-- The actual outgoing Bessel coefficient is the greatest lower bound of unit-trace energies. -/
theorem outgoing_isGLB (a T : ℝ) : IsGLB (traceEnergies a T) (outgoing a T) := by
  constructor
  · rintro E ⟨f, hf, rfl⟩
    have h := exact_boundary_lower_bound f a T
    simpa only [hf, one_pow, mul_one, energy] using h
  · intro B hB
    by_contra hn
    have hgap : 0 < B - outgoing a T := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨hf, he⟩ := unit_trace_approximation a T (Real.log (B - outgoing a T))
    rw [Real.exp_log hgap] at he
    have hlow := hB ⟨approximation a T (accuracyScale T (Real.log (B - outgoing a T))), hf, rfl⟩
    linarith

/-- Exact infimum, with nonemptiness supplied by actual compact approximants. -/
theorem trace_energy_inf (a T : ℝ) : sInf (traceEnergies a T) = outgoing a T :=
  (outgoing_isGLB a T).csInf_eq
    ⟨energy (approximation a T 0) a T, approximation a T 0, approximation_trace a T 0, rfl⟩

/-- Compact negative-energy tail profiles exist exactly below the Bessel transition. -/
theorem negative_energy_iff (a T : ℝ) :
    (∃ f : Profile, energy f a T < 0) ↔ a + T < transition := by
  constructor
  · rintro ⟨f, hf⟩
    apply (outgoing_neg_iff a T).mp
    by_contra hn
    have ho : 0 ≤ outgoing a T := le_of_not_gt hn
    have h := exact_boundary_lower_bound f a T
    have hb := mul_nonneg ho (sq_nonneg (f T))
    change outgoing a T * f T ^ (2 : ℕ) ≤ energy f a T at h
    linarith
  · intro hT
    have ho := (outgoing_neg_iff a T).mpr hT
    obtain ⟨_, he⟩ := unit_trace_approximation a T (Real.log (-outgoing a T))
    rw [Real.exp_log (neg_pos.mpr ho), add_neg_cancel] at he
    exact ⟨_, he⟩

/-- Necessary and sufficient cutoff for nonnegative energy of every isolated compact tail profile. -/
theorem all_compact_energies_nonneg_iff (a T : ℝ) :
    (∀ f : Profile, 0 ≤ energy f a T) ↔ transition ≤ a + T := by
  constructor
  · intro hall
    by_contra hn
    obtain ⟨f, hf⟩ := (negative_energy_iff a T).mpr (lt_of_not_ge hn)
    exact (not_lt_of_ge (hall f)) hf
  · intro hT f
    by_contra hf
    have hh := (negative_energy_iff a T).mp ⟨f, lt_of_not_ge hf⟩
    exact (not_lt_of_ge hT) hh

end
end GaloisForLFunctions.RHTower.SelbergBesselTrace
