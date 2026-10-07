import GaloisForLFunctions.RHTower.XiPolynomialDensity
import GaloisForLFunctions.RHTower.RealCharacterDenseL2

/-!
# Restricted real shifts of the actual xi Fourier profile

The functions `XiC(r) exp(-i t r)`, with `t` in any nonempty real interval, have dense
complex span in `L²(ℝ)`. The proof uses the corpus's exponential-weight integrability,
strip identity theorem and actual xi nonvanishing almost everywhere.

This is the analytic component of WP06's fixed-cutoff feasibility proof. It supplies
no bound on approximation coefficients, no real-coefficient moment cone, and no
growing-cutoff deficit estimate. Its analytic-density mechanism is classical.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace RHTower.WeilSpectral

private theorem ae_zero_of_interval_xi_integrals {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (c : ℝ) (r : {r : ℝ // 0 < r})
    (hz : ∀ t ∈ Ioo (c - r.1) (c + r.1),
      expFourier (fun x => f x * XiC (x : ℂ)) (t : ℂ) = 0) :
    f =ᵐ[volume] 0 := by
  let g : ℝ → ℂ := fun x => f x * XiC (x : ℂ)
  let δ : ℝ := Real.pi / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgw : ExpWeightIntegrable g δ :=
    expWeightIntegrable_memLp_mul_XiC hδ.le
      (by dsimp [δ]; linarith [Real.pi_pos]) hf
  have hgm : AEStronglyMeasurable g volume :=
    hf.aestronglyMeasurable.mul continuous_XiC_ofReal.aestronglyMeasurable
  have hc : (c : ℂ) ∈ {w : ℂ | |w.im| < δ} := by simpa using hδ
  have hcl : (c : ℂ) ∈ closure ({z : ℂ | expFourier g z = 0} \ {(c : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let d := min r.1 ε / 2
    have hd : 0 < d := half_pos (lt_min r.2 hε)
    have hdr : d < r.1 := by dsimp [d]; linarith [min_le_left r.1 ε, r.2]
    have hdε : d < ε := by dsimp [d]; linarith [min_le_right r.1 ε]
    refine ⟨((c + d : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
    · exact hz (c + d) ⟨by linarith [r.2], by linarith⟩
    · simp only [mem_singleton_iff, Complex.ofReal_inj]
      linarith
    · rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simpa [abs_of_pos hd] using hdε
  have hstrip := (analyticOnNhd_expFourier' hgm hgw).eqOn_zero_of_preconnected_of_mem_closure
    (convex_imStrip δ).isPreconnected hc hcl
  have hgi : Integrable g := by
    have hb := hgw 0 (by simpa using hδ)
    refine Integrable.mono' hb hgm (Eventually.of_forall fun x => ?_)
    simp
  have hgz : g =ᵐ[volume] 0 := by
    apply integrable_ae_eq_zero_of_fourier_eq_zero hgi
    intro w
    have hm : (((2 * Real.pi * w : ℝ)) : ℂ) ∈ {z : ℂ | |z.im| < δ} := by
      simpa using hδ
    have hv : expFourier g (((2 * Real.pi * w : ℝ)) : ℂ) = 0 := hstrip hm
    rw [Real.fourier_real_eq_integral_exp_smul]
    rw [expFourier] at hv
    rw [← hv]
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 1
    congr 1
    push_cast
    ring
  filter_upwards [hgz, XiC_ofReal_ne_zero_ae] with x hx hne
  exact (mul_eq_zero.mp hx).resolve_right hne

/-- Vanishing against the actual xi profile on any open shift interval detects the zero
`L²` vector. The interval and vector are intrinsic inputs; no density premise is assumed. -/
theorem xi_interval_integrals_eq_zero_iff (c : ℝ) (r : {r : ℝ // 0 < r})
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (∀ t ∈ Ioo (c - r.1) (c + r.1),
      expFourier (fun x => f x * XiC (x : ℂ)) (t : ℂ) = 0) ↔ f = 0 := by
  constructor
  · intro hz
    apply Lp.ext
    exact (ae_zero_of_interval_xi_integrals (Lp.memLp f) c r hz).trans
      (Lp.coeFn_zero ℂ 2 volume).symm
  · rintro rfl t _
    unfold expFourier
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    simp

/-- Fourier profile of a real translate of the untruncated Riemann kernel. -/
def deficitXiShift (t x : ℝ) : ℂ :=
  XiC (x : ℂ) * Complex.exp (-(I * (t : ℂ) * (x : ℂ)))

private theorem memLp_deficitXiShift (t : ℝ) : MemLp (deficitXiShift t) 2 volume := by
  have hXi : MemLp (fun x : ℝ => XiC (x : ℂ)) 2 volume := by
    simpa using memLp_pow_mul_XiC_ofReal 0
  refine hXi.of_le (hXi.aestronglyMeasurable.mul (by fun_prop))
    (Eventually.of_forall fun x => ?_)
  simp [deficitXiShift, Complex.norm_exp]

/-- The actual shifted xi Fourier profile as an `L²` vector. -/
def deficitXiShiftLp (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_deficitXiShift t).toLp (deficitXiShift t)

private theorem deficitXiShiftLp_ae (t : ℝ) :
    deficitXiShiftLp t =ᵐ[volume] deficitXiShift t :=
  (memLp_deficitXiShift t).coeFn_toLp

/-- **Every open real shift interval gives a dense complex span of actual xi profiles.**
This is qualitative completeness only; it asserts no coefficient-cost estimate. -/
theorem dense_span_deficitXiShiftLp (c : ℝ) (r : {r : ℝ // 0 < r}) :
    Dense (Submodule.span ℂ (Set.range
      (fun t : Ioo (c - r.1) (c + r.1) => deficitXiShiftLp t.1)) :
        Set (Lp ℂ 2 (volume : Measure ℝ))) := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  let g : Lp ℂ 2 (volume : Measure ℝ) :=
    (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ))).symm L
  have hg : MemLp (fun x : ℝ => conj (g x)) 2 volume :=
    (Lp.memLp g).of_le (by fun_prop) (Eventually.of_forall fun x => by simp)
  have hzero : ∀ t ∈ Ioo (c - r.1) (c + r.1),
      expFourier (fun x => conj (g x) * XiC (x : ℂ)) (t : ℂ) = 0 := by
    intro t ht
    have hi : inner ℂ g (deficitXiShiftLp t) = 0 := by
      simpa [g, InnerProductSpace.toDual_symm_apply] using hL ⟨t, ht⟩
    rw [L2.inner_def] at hi
    rw [expFourier, ← hi]
    apply integral_congr_ae
    filter_upwards [deficitXiShiftLp_ae t] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, deficitXiShift]
    ring
  have hgz := ae_zero_of_interval_xi_integrals hg c r hzero
  have hg0 : g = 0 := by
    apply Lp.ext
    filter_upwards [hgz, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx h0
    rw [h0]
    have hz := congrArg (starRingEnd ℂ) hx
    simpa using hz
  calc
    L = (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ))) g := by
      symm
      exact (InnerProductSpace.toDual ℂ (Lp ℂ 2 (volume : Measure ℝ))).apply_symm_apply L
    _ = 0 := by rw [hg0]; simp

end RHTower.WeilSpectral
