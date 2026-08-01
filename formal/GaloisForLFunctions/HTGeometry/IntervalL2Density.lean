import GaloisForLFunctions.HTGeometry.CompactIntervalL2Pairing
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Density in `L²` of a compact interval

Towards a countable Hilbert basis of `L²[-a,a]`, which mathlib does not provide: it has no
separability instance for `Lp` at all, and no isometry identifying `L²` of an interval with `L²` of
the circle where the Fourier basis lives.

The first step is density of the bounded continuous functions.  The measure is the restriction of
Lebesgue measure to a compact interval, so it is finite and weakly regular, which is exactly what
mathlib's density theorem needs — no compactness of the ambient space is required.

The `L²` norm of a bounded continuous function is controlled by its supremum norm times the square
root of the total mass, so uniform approximation on the interval suffices to approximate in `L²`.
This is what will let Stone–Weierstrass supply a countable total family.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

/-- The measure of a compact symmetric interval is finite. -/
theorem intervalL2_measure_ne_top (a : ℝ) :
    (volume.restrict (Set.Icc (-a) a)) Set.univ ≠ ⊤ := by
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- **The bounded continuous functions are dense in `L²` of a compact interval.**  The restricted
Lebesgue measure is finite and weakly regular, which is all mathlib's density theorem requires. -/
theorem denseRange_boundedContinuousToIntervalL2 (a : ℝ) :
    DenseRange (BoundedContinuousFunction.toLp (E := ℂ) 2
      (volume.restrict (Set.Icc (-a) a)) ℂ) :=
  BoundedContinuousFunction.toLp_denseRange _ _ ℂ (by norm_num)

/-- Every element of `L²` of the interval is a limit of bounded continuous functions. -/
theorem exists_boundedContinuous_close (a : ℝ) (f : IntervalL2 a) {eps : ℝ} (heps : 0 < eps) :
    ∃ g : BoundedContinuousFunction ℝ ℂ,
      ‖BoundedContinuousFunction.toLp (E := ℂ) 2 (volume.restrict (Set.Icc (-a) a)) ℂ g - f‖
        < eps := by
  obtain ⟨y, hy, hclose⟩ :=
    Metric.mem_closure_iff.mp
      ((denseRange_boundedContinuousToIntervalL2 a).closure_eq ▸ Set.mem_univ f) eps heps
  obtain ⟨g, hg⟩ := hy
  refine ⟨g, ?_⟩
  rw [hg, ← dist_eq_norm, dist_comm]
  exact hclose

/-! ## Sup-norm control of the `L²` norm

On a finite measure the `L²` norm is dominated by the supremum norm times the square root of the
total mass.  So uniform approximation on the interval gives approximation in `L²`, which is how
Stone–Weierstrass will supply a countable total family. -/

/-- **Uniform closeness on the interval implies `L²` closeness.** -/
theorem norm_toIntervalL2_sub_le (a : ℝ) {w v : ℝ → ℂ} (hw : Continuous w) (hv : Continuous v)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ x ∈ Set.Icc (-a) a, ‖w x - v x‖ ≤ C) :
    ‖toIntervalL2 a hw - toIntervalL2 a hv‖
      ≤ (measureUnivNNReal (volume.restrict (Set.Icc (-a) a)) : ℝ)
          ^ ((2 : ENNReal).toReal)⁻¹ * C := by
  refine Lp.norm_le_of_ae_bound hC ?_
  have hcoe : ((toIntervalL2 a hw - toIntervalL2 a hv : IntervalL2 a) : ℝ → ℂ)
      =ᵐ[volume.restrict (Set.Icc (-a) a)] fun x => w x - v x := by
    filter_upwards [Lp.coeFn_sub (toIntervalL2 a hw) (toIntervalL2 a hv),
      (memLp_two_of_continuous a hw).coeFn_toLp,
      (memLp_two_of_continuous a hv).coeFn_toLp] with x h1 h2 h3
    have hsub : ((toIntervalL2 a hw - toIntervalL2 a hv : IntervalL2 a) : ℝ → ℂ) x
        = (toIntervalL2 a hw : ℝ → ℂ) x - (toIntervalL2 a hv : ℝ → ℂ) x := by
      rw [h1]; rfl
    rw [hsub, show (toIntervalL2 a hw : ℝ → ℂ) x = w x from h2,
      show (toIntervalL2 a hv : ℝ → ℂ) x = v x from h3]
  filter_upwards [hcoe, ae_restrict_mem measurableSet_Icc] with x hx hmem
  rw [hx]
  exact h x hmem

/-! ## Polynomial approximation of complex functions on the interval

Weierstrass approximation is available for real-valued functions.  A complex-valued continuous
function is approximated by splitting into real and imaginary parts and approximating each, so no
complex Stone–Weierstrass is needed: the real monomials already span enough. -/

/-- **Uniform polynomial approximation of a complex continuous function on the interval.**  The
approximant is `p + i q` with `p`, `q` real polynomials. -/
theorem exists_complexPolynomial_near (a : ℝ) {w : ℝ → ℂ} (hw : Continuous w)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ p q : Polynomial ℝ, ∀ x ∈ Set.Icc (-a) a,
      ‖w x - (((Polynomial.eval x p : ℝ) : ℂ)
        + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ))‖ < eps := by
  have hre : ContinuousOn (fun x => (w x).re) (Set.Icc (-a) a) :=
    (Complex.continuous_re.comp hw).continuousOn
  have him : ContinuousOn (fun x => (w x).im) (Set.Icc (-a) a) :=
    (Complex.continuous_im.comp hw).continuousOn
  obtain ⟨p, hp⟩ :=
    exists_polynomial_near_of_continuousOn (-a) a _ hre (eps / 2) (by linarith)
  obtain ⟨q, hq⟩ :=
    exists_polynomial_near_of_continuousOn (-a) a _ him (eps / 2) (by linarith)
  refine ⟨p, q, fun x hx => ?_⟩
  have hbound := Complex.norm_le_abs_re_add_abs_im
    (w x - (((Polynomial.eval x p : ℝ) : ℂ) + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ)))
  have hre' : (w x - (((Polynomial.eval x p : ℝ) : ℂ)
      + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ))).re
      = (w x).re - Polynomial.eval x p := by simp
  have him' : (w x - (((Polynomial.eval x p : ℝ) : ℂ)
      + Complex.I * ((Polynomial.eval x q : ℝ) : ℂ))).im
      = (w x).im - Polynomial.eval x q := by simp
  rw [hre', him'] at hbound
  have h1 : |(w x).re - Polynomial.eval x p| < eps / 2 := by
    rw [abs_sub_comm]
    exact hp x hx
  have h2 : |(w x).im - Polynomial.eval x q| < eps / 2 := by
    rw [abs_sub_comm]
    exact hq x hx
  linarith

end GaloisForLFunctions.HTGeometry
