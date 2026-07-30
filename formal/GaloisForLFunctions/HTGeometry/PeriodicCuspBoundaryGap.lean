import Mathlib.Analysis.Complex.Periodic

/-!
# Normed periodic cusp boundary gap

A bounded holomorphic periodic map into any complete complex normed space has a norm-holomorphic
q-expansion at its cusp. This extends the scalar periodic-cusp construction to arbitrary normed
targets and supplies the exact bridge from logarithmic-cover geometry to analytic boundary order.
-/

open Complex Filter Asymptotics Function Set
open scoped Real Topology

noncomputable section

namespace HTGeometry

local notation "I∞" => comap Complex.im atTop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Vector-valued cusp function of a periodic holomorphic map. -/
def normedPeriodicCuspFunction (h : ℝ) (f : ℂ → E) : ℂ → E :=
  update (f ∘ Function.Periodic.invQParam h) 0
    (limUnder (𝓝[≠] 0) (f ∘ Function.Periodic.invQParam h))

omit [NormedSpace ℂ E] [CompleteSpace E] in
 theorem normedPeriodicCuspFunction_eq_of_nonzero
    (h : ℝ) (f : ℂ → E) {q : ℂ} (hq : q ≠ 0) :
    normedPeriodicCuspFunction h f q = f (Function.Periodic.invQParam h q) :=
  update_of_ne hq ..

omit [NormedSpace ℂ E] [CompleteSpace E] in
 theorem normedPeriodicCuspFunction_zero_eq_limUnder_nhds_ne
    (h : ℝ) (f : ℂ → E) :
    normedPeriodicCuspFunction h f 0 =
      limUnder (𝓝[≠] 0) (normedPeriodicCuspFunction h f) := by
  conv_lhs => simp only [normedPeriodicCuspFunction, update_self]
  refine congr_arg lim (Filter.map_congr <|
    eventuallyEq_nhdsWithin_of_eqOn fun r hr => ?_)
  rw [normedPeriodicCuspFunction, update_of_ne hr]

omit [NormedSpace ℂ E] [CompleteSpace E] in
 theorem normedPeriodicCuspFunction_qParam_eq
    {h : ℝ} (hh : h ≠ 0) {f : ℂ → E} (hf : Periodic f h) (z : ℂ) :
    normedPeriodicCuspFunction h f (Function.Periodic.qParam h z) = f z := by
  have heq : normedPeriodicCuspFunction h f (Function.Periodic.qParam h z) =
      f (Function.Periodic.invQParam h (Function.Periodic.qParam h z)) := by
    rw [normedPeriodicCuspFunction, update_of_ne, comp_apply]
    exact exp_ne_zero _
  obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period hh z
  simpa only [heq, hm] using hf.int_mul m z

omit [CompleteSpace E] in
theorem differentiableAt_normedPeriodicCuspFunction
    {h : ℝ} (hh : h ≠ 0) {f : ℂ → E} (hf : Periodic f h)
    {z : ℂ} (hol_z : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (normedPeriodicCuspFunction h f)
      (Function.Periodic.qParam h z) := by
  let q := Function.Periodic.qParam h z
  have qdiff : HasStrictDerivAt (Function.Periodic.qParam h)
      (q * (2 * Real.pi * I / h)) z := by
    simpa only [id_eq, mul_one] using!
      (((hasStrictDerivAt_id z).const_mul _).div_const _).cexp
  have diff_ne : q * (2 * Real.pi * I / h) ≠ 0 :=
    mul_ne_zero (exp_ne_zero _)
      (div_ne_zero two_pi_I_ne_zero (mod_cast hh))
  let L := (qdiff.localInverse (Function.Periodic.qParam h) _ z) diff_ne
  have diff_L : DifferentiableAt ℂ L q :=
    (qdiff.to_localInverse diff_ne).hasStrictFDerivAt.differentiableAt
  have hL : Function.Periodic.qParam h ∘ L =ᶠ[𝓝 q] (id : ℂ → ℂ) :=
    (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_right_inverse
  have hF := hL.fun_comp (normedPeriodicCuspFunction h f)
  have hcomp : normedPeriodicCuspFunction h f ∘
      Function.Periodic.qParam h ∘ L = f ∘ L :=
    funext fun w => normedPeriodicCuspFunction_qParam_eq hh hf (L w)
  rw [hcomp] at hF
  rw [← EventuallyEq.eq_of_nhds
    (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_left_inverse] at hol_z
  exact (hol_z.comp q diff_L).congr_of_eventuallyEq hF.symm

omit [CompleteSpace E] in
theorem eventually_differentiableAt_normedPeriodicCuspFunction_nhds_ne_zero
    {h : ℝ} (hh : 0 < h) {f : ℂ → E} (hf : Periodic f h)
    (hhol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) :
    ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ (normedPeriodicCuspFunction h f) q := by
  refine ((Function.Periodic.invQParam_tendsto hh).eventually hhol).mp ?_
  refine eventually_nhdsWithin_of_forall (fun q hq hdiff => ?_)
  rw [← Function.Periodic.qParam_right_inv hh.ne' hq]
  exact differentiableAt_normedPeriodicCuspFunction hh.ne' hf hdiff

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem boundedAtFilter_normedPeriodicCuspFunction
    {h : ℝ} (hh : 0 < h) {f : ℂ → E} (hbd : BoundedAtFilter I∞ f) :
    BoundedAtFilter (𝓝[≠] 0) (normedPeriodicCuspFunction h f) := by
  refine (hbd.comp_tendsto <| Function.Periodic.invQParam_tendsto hh).congr' ?_ (by simp)
  refine eventually_nhdsWithin_of_forall fun q hq => ?_
  rw [normedPeriodicCuspFunction_eq_of_nonzero _ _ hq, comp_def]

omit [NormedSpace ℂ E] [CompleteSpace E] in
 theorem normedPeriodicCuspFunction_zero_of_zero_at_inf
    {h : ℝ} (hh : 0 < h) {f : ℂ → E} (hzero : ZeroAtFilter I∞ f) :
    normedPeriodicCuspFunction h f 0 = 0 := by
  simpa only [normedPeriodicCuspFunction, update_self] using
    (hzero.comp (Function.Periodic.invQParam_tendsto hh)).limUnder_eq

theorem differentiableAt_normedPeriodicCuspFunction_zero
    {h : ℝ} (hh : 0 < h) {f : ℂ → E} (hf : Periodic f h)
    (hhol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z)
    (hbd : BoundedAtFilter I∞ f) :
    DifferentiableAt ℂ (normedPeriodicCuspFunction h f) 0 := by
  obtain ⟨c, t⟩ := (boundedAtFilter_normedPeriodicCuspFunction hh hbd).bound
  replace t :=
    (eventually_differentiableAt_normedPeriodicCuspFunction_nhds_ne_zero
      hh hf hhol).and t
  simp only [norm_one, Pi.one_apply, mul_one] at t
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp t)
  have hdiff : DifferentiableOn ℂ (normedPeriodicCuspFunction h f) (S \ {0}) :=
    fun x hx => (hS1 x hx.1 hx.2).1.differentiableWithinAt
  have hFbd : BddAbove
      (norm ∘ normedPeriodicCuspFunction h f '' (S \ {0})) := by
    use c
    simp only [mem_upperBounds, Set.mem_image, Set.mem_sdiff,
      forall_exists_index, and_imp]
    intro y q hq hq2 hy
    simpa only [← hy, norm_one, mul_one] using! (hS1 q hq hq2).2
  have hrem := Complex.differentiableOn_update_limUnder_of_bddAbove
    (IsOpen.mem_nhds hS2 hS3) hdiff hFbd
  rw [← normedPeriodicCuspFunction_zero_eq_limUnder_nhds_ne,
    update_eq_self] at hrem
  exact hrem.differentiableAt (IsOpen.mem_nhds hS2 hS3)

theorem analyticAt_normedPeriodicCuspFunction_zero
    {h : ℝ} (hh : 0 < h) {f : ℂ → E} (hf : Periodic f h)
    (hhol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z)
    (hbd : BoundedAtFilter I∞ f) :
    AnalyticAt ℂ (normedPeriodicCuspFunction h f) 0 := by
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    (eventually_differentiableAt_normedPeriodicCuspFunction_nhds_ne_zero hh hf hhol)
    (differentiableAt_normedPeriodicCuspFunction_zero hh hf hhol hbd).continuousAt

/-- Vector-valued periodic cusp gap: a bounded holomorphic periodic function
vanishing at the cusp decays at least at the first integral Fourier rate. -/
theorem normedPeriodic_exp_decay_of_zero_at_inf
    {h : ℝ} (hh : 0 < h) {f : ℂ → E} (hf : Periodic f h)
    (hhol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z)
    (hzero : ZeroAtFilter I∞ f) :
    f =O[I∞] fun z => Real.exp (-2 * Real.pi * Complex.im z / h) := by
  have hdiff := differentiableAt_normedPeriodicCuspFunction_zero
    hh hf hhol hzero.boundedAtFilter
  simpa [normedPeriodicCuspFunction_zero_of_zero_at_inf hh hzero, sub_zero,
    Function.comp_def, normedPeriodicCuspFunction_qParam_eq hh.ne' hf,
    Function.Periodic.norm_qParam] using
    hdiff.isBigO_sub.mono nhdsWithin_le_nhds
      |>.comp_tendsto (Function.Periodic.qParam_tendsto hh)
      |>.norm_right

/-- Thermal density of a logarithmic cusp branch along its central vertical ray. -/
def logarithmicCuspBoundaryDensity (f : ℂ → E) (t : ℝ) : ℝ :=
  ‖f ((t : ℂ) * I)‖ ^ 2 /
    (1 - Real.exp (-Real.exp (-t)))

theorem qParam_vertical_eq_real_exp
    {h : ℝ} (hh : h ≠ 0) (t : ℝ) :
    Function.Periodic.qParam h ((t : ℂ) * I) =
      (Real.exp (-(2 * Real.pi / h) * t) : ℂ) := by
  rw [Function.Periodic.qParam]
  have harg : 2 * (Real.pi : ℂ) * I * ((t : ℂ) * I) / (h : ℂ) =
      ((-(2 * Real.pi / h) * t : ℝ) : ℂ) := by
    have hI : I * ((t : ℂ) * I) = -(t : ℂ) := by
      calc
        I * ((t : ℂ) * I) = (I * I) * (t : ℂ) := by ring
        _ = -(t : ℂ) := by rw [I_mul_I]; ring
    rw [mul_assoc (2 * (Real.pi : ℂ)) I ((t : ℂ) * I), hI]
    push_cast
    field_simp [hh]
  rw [harg, ← Complex.ofReal_exp]

end HTGeometry
