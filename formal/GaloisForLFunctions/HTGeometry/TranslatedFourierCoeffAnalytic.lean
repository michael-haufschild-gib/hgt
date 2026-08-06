import GaloisForLFunctions.HTGeometry.ActivePhaseLattice
import GaloisForLFunctions.HTGeometry.PolyannulusSliceUniqueness
import GaloisForLFunctions.HTGeometry.TorusDerivationJets
import GaloisForLFunctions.HTGeometry.ObserverTemporalPhaseSupportLaw

/-!
# The translated Fourier coefficient is holomorphic in the translation

The `m`-th active coefficient of a phase observable translated by a scaling
`h` is an integral over the product torus whose integrand is holomorphic in
`h`.  Differentiating under the integral sign in one coordinate at a time shows
that the coefficient is holomorphic in each coordinate of `h` separately.

The domination is uniform: the scaled torus points attached to a closed ball of
translations form a compact subset of the polyannulus, on which the differential
of the observable is bounded.
-/

open Complex Set Filter Topology MeasureTheory

attribute [local instance] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### The scaled torus point -/

/-- The torus point `x` scaled by `h`. -/
def scaledTorusPoint (h : d → ℂ) (x : UnitAddTorus d) : d → ℂ :=
  torusScale h (circleCoords x)

omit [Fintype d] [DecidableEq d] in
theorem scaledTorusPoint_mem_polyannulus {ρ : d → ℝ} {h : d → ℂ}
    (hh : h ∈ polyannulus ρ) (x : UnitAddTorus d) :
    scaledTorusPoint h x ∈ polyannulus ρ := by
  intro j
  have hnorm : ‖scaledTorusPoint h x j‖ = ‖h j‖ := by
    rw [scaledTorusPoint, torusScale, norm_mul, circleCoords_mem_unitTorus x j,
      mul_one]
  rw [mem_logAnnulus_iff, hnorm]
  exact hh j

omit [Fintype d] [DecidableEq d] in
theorem continuous_scaledTorusPoint_snd (h : d → ℂ) :
    Continuous fun x : UnitAddTorus d => scaledTorusPoint h x := by
  refine continuous_pi fun j => ?_
  exact continuous_const.mul ((continuous_apply j).comp continuous_circleCoords)

omit [Fintype d] in
theorem continuous_update (h : d → ℂ) (i : d) :
    Continuous fun u : ℂ => Function.update h i u := by
  refine continuous_pi fun j => ?_
  by_cases hj : j = i
  · subst hj
    have hfun : (fun u : ℂ => Function.update h j u j) = fun u : ℂ => u := by
      funext u
      rw [Function.update_self]
    rw [hfun]
    exact continuous_id
  · have hfun : (fun u : ℂ => Function.update h i u j) = fun _ : ℂ => h j := by
      funext u
      rw [Function.update_of_ne hj]
    rw [hfun]
    exact continuous_const

omit [Fintype d] in
theorem continuous_scaledTorusPoint_pair (h : d → ℂ) (i : d) :
    Continuous fun p : ℂ × UnitAddTorus d =>
      scaledTorusPoint (Function.update h i p.1) p.2 := by
  refine continuous_pi fun j => ?_
  exact (((continuous_apply j).comp (continuous_update h i)).comp continuous_fst).mul
    (((continuous_apply j).comp continuous_circleCoords).comp continuous_snd)

theorem norm_pi_single_le (i : d) (c : ℂ) :
    ‖(Pi.single i c : d → ℂ)‖ ≤ ‖c‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2 fun j => ?_
  by_cases hj : j = i
  · subst hj
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj, norm_zero]
    exact norm_nonneg c

/-! ### The integrand and its derivative -/

/-- The integrand of the translated Fourier coefficient. -/
def translatedIntegrand (F : (d → ℂ) → ℂ) (m : d → ℤ) (h : d → ℂ)
    (x : UnitAddTorus d) : ℂ :=
  UnitAddTorus.mFourier (-m) x • F (scaledTorusPoint h x)

/-- The derivative of the integrand in one translation coordinate. -/
def translatedDerivIntegrand (F : (d → ℂ) → ℂ) (m : d → ℤ) (i : d)
    (h : d → ℂ) (x : UnitAddTorus d) : ℂ :=
  UnitAddTorus.mFourier (-m) x •
    (circleCoords x i • coordDeriv F i (scaledTorusPoint h x))

omit [DecidableEq d] in
theorem activeCoeff_eq_integral (F : (d → ℂ) → ℂ) (m : d → ℤ) (h : d → ℂ) :
    activeCoeff (fun z => F (torusScale h z)) m
      = ∫ x, translatedIntegrand F m h x := rfl

omit [DecidableEq d] in
theorem norm_translatedIntegrand_sub (F : (d → ℂ) → ℂ) (m : d → ℤ)
    (h h' : d → ℂ) (x : UnitAddTorus d) :
    ‖translatedIntegrand F m h x - translatedIntegrand F m h' x‖
      = ‖F (scaledTorusPoint h x) - F (scaledTorusPoint h' x)‖ := by
  rw [translatedIntegrand, translatedIntegrand, smul_eq_mul, smul_eq_mul,
    ← mul_sub, norm_mul, norm_mFourier_apply, one_mul]

omit [DecidableEq d] in
theorem continuous_translatedIntegrand {ρ : d → ℝ} {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (m : d → ℤ) {h : d → ℂ}
    (hh : h ∈ polyannulus ρ) :
    Continuous fun x : UnitAddTorus d => translatedIntegrand F m h x := by
  refine (UnitAddTorus.mFourier (-m)).continuous.smul ?_
  refine continuous_iff_continuousAt.2 fun x => ?_
  exact ((hF _ (scaledTorusPoint_mem_polyannulus hh x)).continuousAt).comp
    (continuous_scaledTorusPoint_snd h).continuousAt

theorem continuous_translatedDerivIntegrand {ρ : d → ℝ} {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (m : d → ℤ) (i : d) {h : d → ℂ}
    (hh : h ∈ polyannulus ρ) :
    Continuous fun x : UnitAddTorus d => translatedDerivIntegrand F m i h x := by
  refine (UnitAddTorus.mFourier (-m)).continuous.smul ?_
  refine ((continuous_apply i).comp continuous_circleCoords).smul ?_
  refine continuous_iff_continuousAt.2 fun x => ?_
  exact (((analyticOnNhd_coordDeriv hF i) _
    (scaledTorusPoint_mem_polyannulus hh x)).continuousAt).comp
    (continuous_scaledTorusPoint_snd h).continuousAt

omit [Fintype d] in
theorem hasDerivAt_scaledTorusPoint_slice (h : d → ℂ) (i : d)
    (x : UnitAddTorus d) (w : ℂ) :
    HasDerivAt (fun u : ℂ => scaledTorusPoint (Function.update h i u) x)
      (Pi.single i (circleCoords x i)) w := by
  refine hasDerivAt_pi.2 fun j => ?_
  by_cases hj : j = i
  · subst hj
    have hfun : (fun u : ℂ => scaledTorusPoint (Function.update h j u) x j)
        = fun u : ℂ => u * circleCoords x j := by
      funext u
      rw [scaledTorusPoint, torusScale, Function.update_self]
    rw [hfun, Pi.single_eq_same]
    simpa using (hasDerivAt_id w).mul_const (circleCoords x j)
  · have hfun : (fun u : ℂ => scaledTorusPoint (Function.update h i u) x j)
        = fun _ : ℂ => h j * circleCoords x j := by
      funext u
      rw [scaledTorusPoint, torusScale, Function.update_of_ne hj]
    rw [hfun, Pi.single_eq_of_ne hj]
    exact hasDerivAt_const w _

theorem hasDerivAt_translatedIntegrand {ρ : d → ℝ} {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (m : d → ℤ) (i : d) (h : d → ℂ)
    {w : ℂ} (hw : Function.update h i w ∈ polyannulus ρ) (x : UnitAddTorus d) :
    HasDerivAt (fun u : ℂ => translatedIntegrand F m (Function.update h i u) x)
      (translatedDerivIntegrand F m i (Function.update h i w) x) w := by
  set A := scaledTorusPoint (Function.update h i w) x with hA
  have hAmem : A ∈ polyannulus ρ := scaledTorusPoint_mem_polyannulus hw x
  have hFd : HasFDerivAt F (fderiv ℂ F A) A :=
    (hF _ hAmem).differentiableAt.hasFDerivAt
  have hcomp : HasDerivAt (fun u : ℂ => F (scaledTorusPoint (Function.update h i u) x))
      ((fderiv ℂ F A) (Pi.single i (circleCoords x i))) w :=
    hFd.comp_hasDerivAt w (hasDerivAt_scaledTorusPoint_slice h i x w)
  have hval : (fderiv ℂ F A) (Pi.single i (circleCoords x i))
      = circleCoords x i • coordDeriv F i A := by
    have hsingle : (Pi.single i (circleCoords x i) : d → ℂ)
        = circleCoords x i • (Pi.single i (1 : ℂ)) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [Pi.single_eq_of_ne hj]
    rw [hsingle, map_smul, coordDeriv]
  rw [translatedDerivIntegrand, ← hval]
  exact hcomp.const_smul (UnitAddTorus.mFourier (-m) x)

/-! ### Holomorphy in one coordinate -/

/-- **Differentiating the translated Fourier coefficient under the integral
sign.** -/
theorem hasDerivAt_slice_activeCoeff {ρ : d → ℝ}
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (m : d → ℤ)
    {h : d → ℂ} (hh : h ∈ polyannulus ρ) (i : d) {w₀ : ℂ}
    (hw₀ : w₀ ∈ logAnnulus (ρ i)) :
    HasDerivAt
      (fun w : ℂ =>
        activeCoeff (fun z => F (torusScale (Function.update h i w) z)) m)
      (∫ x, translatedDerivIntegrand F m i (Function.update h i w₀) x) w₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_logAnnulus (ρ i)) w₀ hw₀
  set ε' : ℝ := ε / 2 with hε'
  have hε'pos : 0 < ε' := by positivity
  have hclosed : Metric.closedBall w₀ ε' ⊆ logAnnulus (ρ i) := by
    refine subset_trans (Metric.closedBall_subset_ball ?_) hball
    rw [hε']
    linarith
  have hupd : ∀ w ∈ Metric.closedBall w₀ ε',
      Function.update h i w ∈ polyannulus ρ := by
    intro w hw j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact hclosed hw
    · rw [Function.update_of_ne hj]
      exact hh j
  set K : Set (d → ℂ) :=
    (fun p : ℂ × UnitAddTorus d =>
        scaledTorusPoint (Function.update h i p.1) p.2) ''
      (Metric.closedBall w₀ ε' ×ˢ (Set.univ : Set (UnitAddTorus d))) with hK
  have hKcompact : IsCompact K :=
    IsCompact.image ((isCompact_closedBall w₀ ε').prod isCompact_univ)
      (continuous_scaledTorusPoint_pair h i)
  have hKsub : K ⊆ polyannulus ρ := by
    rintro - ⟨⟨u, x⟩, ⟨hu, -⟩, rfl⟩
    exact scaledTorusPoint_mem_polyannulus (hupd u hu) x
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn
    (f := fun z => fderiv ℂ F z)
    (fun z hz => ((hF.fderiv) z (hKsub hz)).continuousAt.continuousWithinAt)
  have hCball : ∀ w ∈ Metric.closedBall w₀ ε', ∀ x : UnitAddTorus d,
      ‖fderiv ℂ F (scaledTorusPoint (Function.update h i w) x)‖ ≤ C :=
    fun w hw x => hC _ ⟨(w, x), ⟨hw, Set.mem_univ x⟩, rfl⟩
  have hC0 : 0 ≤ C := by
    have hx : Nonempty (UnitAddTorus d) := ⟨fun _ => 0⟩
    obtain ⟨x⟩ := hx
    exact le_trans (norm_nonneg _)
      (hCball w₀ (Metric.mem_closedBall_self hε'pos.le) x)
  have hw₀mem : Function.update h i w₀ ∈ polyannulus ρ :=
    hupd w₀ (Metric.mem_closedBall_self hε'pos.le)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := (volume : Measure (UnitAddTorus d)))
    (F := fun w x => translatedIntegrand F m (Function.update h i w) x)
    (x₀ := w₀) (bound := fun _ => C) (s := Metric.ball w₀ ε')
    (F' := fun x => translatedDerivIntegrand F m i (Function.update h i w₀) x)
    (Metric.ball_mem_nhds w₀ hε'pos)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds w₀ hε'pos) fun w hw =>
      (continuous_translatedIntegrand hF m
        (hupd w (Metric.ball_subset_closedBall hw))).aestronglyMeasurable)
    ((continuous_translatedIntegrand hF m hw₀mem).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (continuous_translatedDerivIntegrand hF m i hw₀mem).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
    (integrable_const C)
    (Filter.Eventually.of_forall fun x =>
      hasDerivAt_translatedIntegrand hF m i h hw₀mem x)
  · exact hmain.2
  · refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    rw [Real.coe_nnabs, abs_of_nonneg hC0, dist_eq_norm, dist_eq_norm,
      norm_translatedIntegrand_sub]
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u : ℂ => F (scaledTorusPoint (Function.update h i u) x))
      (f' := fun u : ℂ =>
        (fderiv ℂ F (scaledTorusPoint (Function.update h i u) x))
          (Pi.single i (circleCoords x i)))
      (fun u hu => ?_) (fun u hu => ?_) (convex_ball w₀ ε') hv hu
    · have hmem : Function.update h i u ∈ polyannulus ρ :=
        hupd u (Metric.ball_subset_closedBall hu)
      have hAmem : scaledTorusPoint (Function.update h i u) x ∈ polyannulus ρ :=
        scaledTorusPoint_mem_polyannulus hmem x
      exact (((hF _ hAmem).differentiableAt.hasFDerivAt).comp_hasDerivAt u
        (hasDerivAt_scaledTorusPoint_slice h i x u)).hasDerivWithinAt
    · refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      have h1 : ‖(Pi.single i (circleCoords x i) : d → ℂ)‖ ≤ 1 := by
        refine le_trans (norm_pi_single_le i _) ?_
        rw [circleCoords_mem_unitTorus x i]
      have h2 : ‖fderiv ℂ F (scaledTorusPoint (Function.update h i u) x)‖ ≤ C :=
        hCball u (Metric.ball_subset_closedBall hu) x
      calc ‖fderiv ℂ F (scaledTorusPoint (Function.update h i u) x)‖ *
            ‖(Pi.single i (circleCoords x i) : d → ℂ)‖
          ≤ C * 1 := by
            refine mul_le_mul h2 h1 (norm_nonneg _) hC0
        _ = C := mul_one C

/-- **The translated Fourier coefficient is holomorphic in each coordinate of
the translation.** -/
theorem analyticOnNhd_slice_activeCoeff_comp_torusScale {ρ : d → ℝ}
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (m : d → ℤ)
    {h : d → ℂ} (hh : h ∈ polyannulus ρ) (i : d) :
    AnalyticOnNhd ℂ
      (fun w : ℂ =>
        activeCoeff (fun z => F (torusScale (Function.update h i w) z)) m)
      (logAnnulus (ρ i)) :=
  DifferentiableOn.analyticOnNhd
    (fun _ hw₀ =>
      (hasDerivAt_slice_activeCoeff hF m hh i hw₀).differentiableAt.differentiableWithinAt)
    (isOpen_logAnnulus (ρ i))

end

end GaloisForLFunctions.HTGeometry
