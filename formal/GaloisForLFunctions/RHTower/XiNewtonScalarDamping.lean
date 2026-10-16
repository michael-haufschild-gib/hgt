import GaloisForLFunctions.RHTower.XiNewtonDiscSourceMargin
import GaloisForLFunctions.RHTower.XiCriticalValueAccumulation

/-!
# Scalar damping of the Xi Newton map

An entire function of the value of Xi cancels a nonroot critical pole exactly
when it vanishes at that critical value. Nonzero critical values of Xi
accumulate at zero at arbitrarily large heights, so the only entire scalar
damping with a globally holomorphic Newton map is the zero function.

On every fixed closed disc, an explicit polynomial damping cancels all critical
poles, commutes with critical-line reflection, and preserves the first Newton
jet at every Xi zero, including multiple zeros. These local repairs assert no
disc self-mapping property and no arithmetic positivity.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace RHTower.XiNewtonCriticalLine

/-- Newton's displacement multiplied by a function of the value of Xi. -/
def scalarDampedXiNewton (A : ℂ → ℂ) (z : ℂ) : ℂ :=
  z - A (xi z) * xi z / deriv xi z

private theorem scalarDampedXiNewton_eq (A : ℂ → ℂ) (z : ℂ) :
    scalarDampedXiNewton A z = z - A (xi z) * (z - newtonMap xi z) := by
  simp only [scalarDampedXiNewton, newtonMap, sub_sub_cancel, mul_div_assoc]

private theorem damping_value_zero_of_continuous
    {A : ℂ → ℂ} (hA : Continuous A) {p : ℂ}
    (hD : ContinuousAt (scalarDampedXiNewton A) p) (hp : deriv xi p = 0) :
    A (xi p) * xi p = 0 := by
  have hleft : Tendsto (fun z => A (xi z) * xi z) (𝓝[≠] p)
      (𝓝 (A (xi p) * xi p)) :=
    (((hA.comp xi_differentiable.continuous).continuousAt).mul
      (xi_differentiable p).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun z => (z - scalarDampedXiNewton A z) * deriv xi z)
      (𝓝[≠] p) (𝓝 (0 : ℂ)) := by
    have h := ((continuousAt_id.sub hD).mul
      (xi_differentiable.analyticAt p).deriv.continuousAt).tendsto
    change Tendsto (fun z => (z - scalarDampedXiNewton A z) * deriv xi z)
      (𝓝 p) (𝓝 ((p - scalarDampedXiNewton A p) * deriv xi p)) at h
    rw [hp, mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  apply tendsto_nhds_unique_of_eventuallyEq hleft hright
  filter_upwards [xi_deriv_eventually_ne_zero p] with z hz
  simp only [scalarDampedXiNewton, sub_sub_cancel, div_mul_cancel₀ _ hz]

private theorem analyticAt_shifted_xi_newton (p : ℂ) :
    AnalyticAt ℂ (newtonMap (fun z => xi z - xi p)) p := by
  have hnonzero : ¬ ∀ᶠ z in 𝓝 p, xi z - xi p = 0 := by
    intro h
    have heq : xi =ᶠ[𝓝 p] fun _ => xi p := h.mono fun z hz => sub_eq_zero.mp hz
    have hd : ∀ᶠ z in 𝓝[≠] p, deriv xi z = 0 := by
      filter_upwards [nhdsWithin_le_nhds heq.deriv] with z hz
      simpa only [deriv_const] using hz
    obtain ⟨z, hz, hnz⟩ := (hd.and (xi_deriv_eventually_ne_zero p)).exists
    exact hnz hz
  obtain ⟨r, hr, hd, -⟩ := exists_ball_newton_invariant_of_zero
    (xi_differentiable.sub_const (xi p)) (sub_self _) hnonzero
  exact hd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))

private theorem analyticAt_scalarDampedXiNewton_of_value_zero
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) {p : ℂ} (hv : A (xi p) = 0) :
    AnalyticAt ℂ (scalarDampedXiNewton A) p := by
  let B : ℂ → ℂ := dslope A (xi p)
  have hB : Differentiable ℂ B := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hA.differentiableOn
  have hformula : scalarDampedXiNewton A = fun z =>
      z - (B (xi z) * xi z) * (z - newtonMap (fun w => xi w - xi p) z) := by
    funext z
    have hd : deriv (fun w => xi w - xi p) z = deriv xi z :=
      ((xi_differentiable z).hasDerivAt.sub_const (xi p)).deriv
    have hfactor : (xi z - xi p) * B (xi z) = A (xi z) := by
      simpa only [B, smul_eq_mul, hv, sub_zero] using sub_smul_dslope A (xi p) (xi z)
    simp only [scalarDampedXiNewton, newtonMap, hd, sub_sub_cancel]
    rw [← hfactor]
    ring
  rw [hformula]
  exact analyticAt_id.sub (((hB.analyticAt (xi p)).comp
    (xi_differentiable.analyticAt p)).mul (xi_differentiable.analyticAt p) |>.mul
      (analyticAt_id.sub (analyticAt_shifted_xi_newton p)))

/-- Exact cancellation of critical poles, with no simplicity assumption. -/
theorem analyticAt_scalarDampedXiNewton_iff
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) (p : ℂ) :
    AnalyticAt ℂ (scalarDampedXiNewton A) p ↔
      xi p = 0 ∨ deriv xi p ≠ 0 ∨ A (xi p) = 0 := by
  constructor
  · intro h
    by_cases hd : deriv xi p = 0
    · rcases mul_eq_zero.mp (damping_value_zero_of_continuous hA.continuous
        h.continuousAt hd) with hA0 | hxi
      · exact Or.inr (Or.inr hA0)
      · exact Or.inl hxi
    · exact Or.inr (Or.inl hd)
  · rintro (hxi | hd | hv)
    · have hN := (analyticAt_xi_newton_iff p).mpr (Or.inl hxi)
      have h := analyticAt_id.sub (((hA.analyticAt (xi p)).comp
        (xi_differentiable.analyticAt p)).mul (analyticAt_id.sub hN))
      exact h.congr (Filter.Eventually.of_forall fun z => (scalarDampedXiNewton_eq A z).symm)
    · exact analyticAt_id.sub ((((hA.analyticAt (xi p)).comp
        (xi_differentiable.analyticAt p)).mul (xi_differentiable.analyticAt p)).div
        (xi_differentiable.analyticAt p).deriv hd)
    · exact analyticAt_scalarDampedXiNewton_of_value_zero hA hv

/-- Normalization at zero preserves the Newton first jet at every Xi zero. -/
theorem scalarDampedXiNewton_root_jet
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) (hA0 : A 0 = 1)
    {p : ℂ} (hp : xi p = 0) :
    scalarDampedXiNewton A p = p ∧
      deriv (scalarDampedXiNewton A) p = deriv (newtonMap xi) p := by
  have hN := (analyticAt_xi_newton_iff p).mpr (Or.inl hp)
  have hNp := newtonMap_eq_self_of_eq_zero hp
  constructor
  · simp [scalarDampedXiNewton, hp]
  · have hcomp := (hA (xi p)).hasDerivAt.comp p (xi_differentiable p).hasDerivAt
    have hder := (hasDerivAt_id p).sub
      (hcomp.mul ((hasDerivAt_id p).sub hN.differentiableAt.hasDerivAt))
    have hfun : (id - (A ∘ xi) * (id - newtonMap xi)) = scalarDampedXiNewton A :=
      funext fun z => (scalarDampedXiNewton_eq A z).symm
    rw [hfun] at hder
    simpa only [Pi.sub_apply, Function.comp_apply, id_eq, hp, hA0, hNp, sub_self,
      mul_zero, one_mul, zero_add, sub_sub_cancel] using hder.deriv

/-- Every normalized entire scalar damping retains critical poles at unbounded heights. -/
theorem scalarDampedXiNewton_high_pole
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) (hA0 : A 0 = 1) (T : ℝ) :
    ∃ p : ℂ, p.re = 1 / 2 ∧ T < p.im ∧ deriv xi p = 0 ∧ xi p ≠ 0 ∧
      ¬ ContinuousAt (scalarDampedXiNewton A) p := by
  have hne : A 0 ≠ 0 := by rw [hA0]; exact one_ne_zero
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hA 0).continuousAt.eventually_ne hne)
  obtain ⟨p, hp, hT, hd, hpos, hsmall⟩ := exists_high_nonzero_small_xi_critical_value T hε
  have hAp : A (xi p) ≠ 0 := hball _ (by simpa [mem_ball, dist_eq_norm] using hsmall)
  have hxip : xi p ≠ 0 := norm_pos_iff.mp hpos
  exact ⟨p, hp, hT, hd, hxip, fun hc =>
    (mul_ne_zero hAp hxip) (damping_value_zero_of_continuous hA.continuous hc hd)⟩

/-- No entire scalar damping normalized at zero produces an entire Newton map. -/
theorem no_entire_normalized_scalarDampedXiNewton :
    ¬ ∃ A : ℂ → ℂ, Differentiable ℂ A ∧ A 0 = 1 ∧
      Differentiable ℂ (scalarDampedXiNewton A) := by
  rintro ⟨A, hA, hA0, hD⟩
  obtain ⟨p, -, -, -, -, hp⟩ := scalarDampedXiNewton_high_pole hA hA0 0
  exact hp (hD p).continuousAt

/-- Every nonzero entire scalar damping retains critical poles at unbounded heights. -/
theorem scalarDampedXiNewton_high_pole_of_ne_zero
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) (hne : A ≠ 0) (T : ℝ) :
    ∃ p : ℂ, p.re = 1 / 2 ∧ T < p.im ∧ deriv xi p = 0 ∧ xi p ≠ 0 ∧
      ¬ ContinuousAt (scalarDampedXiNewton A) p := by
  have hnot : ¬ ∀ᶠ w in 𝓝 (0 : ℂ), A w = 0 := by
    intro hzero
    apply hne
    funext w
    have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
    exact hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ (0 : ℂ)) hzero (mem_univ w)
  have hpunct := (hA.analyticAt 0).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp hpunct)
  obtain ⟨p, hp, hT, hd, hpos, hsmall⟩ := exists_high_nonzero_small_xi_critical_value T hε
  have hxip : xi p ≠ 0 := norm_pos_iff.mp hpos
  have hAp : A (xi p) ≠ 0 := hball _
    (by simpa [mem_ball, dist_eq_norm] using hsmall) hxip
  exact ⟨p, hp, hT, hd, hxip, fun hc =>
    (mul_ne_zero hAp hxip) (damping_value_zero_of_continuous hA.continuous hc hd)⟩

/-- The globally holomorphic scalar-damped Xi Newton maps are exactly the identity map
obtained from zero damping. -/
theorem differentiable_scalarDampedXiNewton_iff
    {A : ℂ → ℂ} (hA : Differentiable ℂ A) :
    Differentiable ℂ (scalarDampedXiNewton A) ↔ A = 0 := by
  constructor
  · intro hD
    by_contra hne
    obtain ⟨p, -, -, -, -, hp⟩ := scalarDampedXiNewton_high_pole_of_ne_zero hA hne 0
    exact hp (hD p).continuousAt
  · rintro rfl
    have heq : scalarDampedXiNewton (0 : ℂ → ℂ) = id := by
      funext z
      simp [scalarDampedXiNewton]
    rw [heq]
    exact differentiable_id

/-- Schwarz-real scalar damping preserves reflection in the critical line. -/
theorem scalarDampedXiNewton_lineReflect {A : ℂ → ℂ}
    (hA : ∀ z, A ((starRingEnd ℂ) z) = (starRingEnd ℂ) (A z)) (z : ℂ) :
    scalarDampedXiNewton A (1 - (starRingEnd ℂ) z) =
      1 - (starRingEnd ℂ) (scalarDampedXiNewton A z) := by
  simp only [scalarDampedXiNewton, xi_lineSymmetric z,
    deriv_lineReflect xi_lineSymmetric z, hA, map_sub, map_mul, map_div₀, div_neg]
  ring

private theorem xi_deriv_zeros_on_compact_finite {K : Set ℂ} (hK : IsCompact K) :
    {p ∈ K | deriv xi p = 0}.Finite := by
  obtain ⟨x, hx⟩ := (xi_deriv_eventually_ne_zero 0).exists
  have hcod : ((deriv xi) ⁻¹' {0}ᶜ) ∈ codiscreteWithin (univ : Set ℂ) :=
    xi_analyticOnNhd_univ.deriv.preimage_zero_mem_codiscreteWithin
      (x := x) hx (mem_univ x) isConnected_univ
  have hcodK : ((deriv xi) ⁻¹' {0}ᶜ) ∈ codiscreteWithin K :=
    Filter.codiscreteWithin_mono (subset_univ _) hcod
  refine (hK.finite_sdiff_of_mem_codiscreteWithin hcodK).subset ?_
  intro p hp
  exact ⟨hp.1, by simp [hp.2]⟩

/-- Every finite disc admits polynomial pole cancellation preserving critical-line
reflection and the first Newton jet at every Xi zero. -/
theorem exists_polynomial_scalarDampedXiNewton_on_closedBall (R : ℝ) :
    ∃ P : Polynomial ℂ, P.eval 0 = 1 ∧
      AnalyticOnNhd ℂ (scalarDampedXiNewton P.eval) (closedBall 0 R) ∧
      (∀ z : ℂ, scalarDampedXiNewton P.eval (1 - (starRingEnd ℂ) z) =
        1 - (starRingEnd ℂ) (scalarDampedXiNewton P.eval z)) ∧
      ∀ p : ℂ, xi p = 0 →
        scalarDampedXiNewton P.eval p = p ∧
          deriv (scalarDampedXiNewton P.eval) p = deriv (newtonMap xi) p := by
  classical
  let S : Finset ℂ := (xi_deriv_zeros_on_compact_finite
    (isCompact_closedBall (0 : ℂ) R)).toFinset.filter (fun p => xi p ≠ 0)
  let P : Polynomial ℂ := ∏ p ∈ S,
    ((1 - Polynomial.C ((xi p)⁻¹) * Polynomial.X) *
      (1 - Polynomial.C (((starRingEnd ℂ) (xi p))⁻¹) * Polynomial.X))
  have hP0 : P.eval 0 = 1 := by simp [P, Polynomial.eval_prod]
  have hPreal : ∀ z, P.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.eval z) := by
    intro z
    simp only [P, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X, map_prod]
    apply Finset.prod_congr rfl
    intro p _
    simp only [map_mul, map_sub, map_one, map_inv₀, Complex.conj_conj]
    ring
  refine ⟨P, hP0, ?_, scalarDampedXiNewton_lineReflect hPreal,
    fun p hp => scalarDampedXiNewton_root_jet P.differentiable hP0 hp⟩
  intro p hp
  apply (analyticAt_scalarDampedXiNewton_iff P.differentiable p).mpr
  by_cases hx : xi p = 0
  · exact Or.inl hx
  by_cases hd : deriv xi p = 0
  · right; right
    have hmem : p ∈ S := by
      simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset, mem_setOf_eq]
      exact ⟨⟨hp, hd⟩, hx⟩
    dsimp only [P]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hmem (by simp [hx])
  · exact Or.inr (Or.inl hd)

end RHTower.XiNewtonCriticalLine
