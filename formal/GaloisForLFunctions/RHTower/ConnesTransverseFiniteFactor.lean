import GaloisForLFunctions.RHTower.ConnesProductFibreDecay

/-!
# The non-archimedean transverse factor costs only a finite constant

Appendix I of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

`ConnesProductFibreDecay` transfers rapid decay across a product whose transverse factor is a
finite-dimensional *real* normed space, using the Japanese-bracket integrability
`integrable_one_add_norm`.  The finite part `∏_{v ∈ S_f} K_v` of an adelic test space is **not**
such a space, and it does not have to be: a Bruhat-Schwartz function on a non-archimedean factor
is *locally constant with compact support*, so its transverse profile is bounded and vanishes off
a set of finite measure.  No decay rate in the transverse variable is needed - the transverse
factor contributes exactly the finite constant `μ(K)`.

The results here are stated for an arbitrary measure space `(X, μ)` and an arbitrary measurable
`K` of finite measure, so they apply verbatim to `∏_{v ∈ S_f} K_v` with `K` the (compact, hence
finite-measure) support of the finite factor.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A fibre on which the test function vanishes identically is flat to all orders: the transverse
directions where a Bruhat-Schwartz function is zero contribute nothing to any seminorm. -/
theorem connes_fibre_iteratedFDeriv_eq_zero {X : Type*} {η : ℝ × X → ℂ} {x : X}
    (hx : ∀ s : ℝ, η (s, x) = 0) (n : ℕ) (t : ℝ) :
    iteratedFDeriv ℝ n (fun s : ℝ => η (s, x)) t = 0 := by
  have hfun : (fun s : ℝ => η (s, x)) = fun _ : ℝ => (0 : ℂ) := funext hx
  rw [hfun, iteratedFDeriv_fun_zero]
  rfl

variable {X : Type*} [MeasurableSpace X]

/-- **Bounded plus compactly supported is integrable.**  This replaces the decay hypothesis in the
archimedean transfer: on a non-archimedean factor a Bruhat-Schwartz function is bounded and
supported in a compact (hence finite-measure) set, which already gives integrability. -/
theorem connes_integrable_of_bounded_support {μ : Measure X} {b : X → ℝ} {K : Set X}
    (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤) (hbm : AEStronglyMeasurable b μ)
    {C : ℝ} (hbC : ∀ x, ‖b x‖ ≤ C) (hbsupp : ∀ x, x ∉ K → b x = 0) :
    Integrable b μ := by
  have hind : b = Set.indicator K b := by
    funext x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hbsupp x hx]
  rw [hind, MeasureTheory.integrable_indicator_iff hK]
  refine Measure.integrableOn_of_bounded (M := C) hKfin hbm ?_
  filter_upwards with x
  exact hbC x

/-- The constant majorant supported on `K` is integrable when `K` has finite measure. -/
theorem connes_indicator_const_integrable {μ : Measure X} {K : Set X}
    (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤) (c : ℝ) :
    Integrable (Set.indicator K fun _ : X => c) μ := by
  refine connes_integrable_of_bounded_support hK hKfin ?_ (C := ‖c‖) ?_ ?_
  · exact (aestronglyMeasurable_const).indicator hK
  · intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      simp
  · intro x hx
    exact Set.indicator_of_notMem hx _

/-- The integral of the constant majorant supported on `K`. -/
theorem connes_indicator_const_integral {μ : Measure X} {K : Set X}
    (hK : MeasurableSet K) (c : ℝ) :
    (∫ x, Set.indicator K (fun _ : X => c) x ∂μ) = μ.real K * c := by
  rw [MeasureTheory.integral_indicator hK, setIntegral_const, smul_eq_mul]

/-- **The transverse factor costs only `μ(K)`.**  If a nonnegative integrand on `ℝ × X` vanishes
off a transverse set `K` of finite measure and its archimedean fibre mass is at most `A`, then its
total mass is at most `μ(K) · A`: no transverse decay is used. -/
theorem connes_transverse_prodMass_le {μ : Measure X} [SFinite μ] {K : Set X}
    (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤) {F : ℝ × X → ℝ}
    (hFint : Integrable F (volume.prod μ)) (hFnn : ∀ p, 0 ≤ F p)
    (hFsupp : ∀ s : ℝ, ∀ x : X, x ∉ K → F (s, x) = 0) {A : ℝ}
    (hfib : ∀ x : X, (∫ s : ℝ, F (s, x)) ≤ A) :
    (∫ p, F p ∂(volume.prod μ)) ≤ μ.real K * A := by
  set g : X → ℝ := fun x => ∫ s : ℝ, F (s, x) with hg
  have hgnn : ∀ x, 0 ≤ g x := fun x => integral_nonneg fun s => hFnn (s, x)
  have hgsupp : ∀ x, x ∉ K → g x = 0 := by
    intro x hx
    have : (fun s : ℝ => F (s, x)) = fun _ : ℝ => (0 : ℝ) := funext fun s => hFsupp s x hx
    simp [hg, this]
  have hfubini : (∫ p, F p ∂(volume.prod μ)) = ∫ x, g x ∂μ :=
    MeasureTheory.integral_prod_symm F hFint
  have hmaj : Integrable (Set.indicator K fun _ : X => A) μ :=
    connes_indicator_const_integrable hK hKfin A
  have hnn : (0 : X → ℝ) ≤ᵐ[μ] g := by
    filter_upwards with x
    exact hgnn x
  have hle : g ≤ᵐ[μ] Set.indicator K fun _ : X => A := by
    filter_upwards with x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      exact hfib x
    · rw [Set.indicator_of_notMem hx, hgsupp x hx]
  rw [hfubini]
  refine le_trans (integral_mono_of_nonneg hnn hmaj hle) (le_of_eq ?_)
  exact connes_indicator_const_integral hK A

/-- **Rapid decay survives a non-archimedean transverse factor.**  If the archimedean fibre mass
of a family decays faster than every power of the parameter, so does the total mass on
`ℝ × X`, provided only that the family is supported in a transverse set of finite measure. -/
theorem connes_transverse_mass_rapidDecay {μ : Measure X} [SFinite μ] {K : Set X}
    (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤) {F : ℝ → ℝ × X → ℝ} {A : ℝ → ℝ} (N : ℕ)
    (hFint : ∀ L : ℝ, Integrable (F L) (volume.prod μ)) (hFnn : ∀ L : ℝ, ∀ p, 0 ≤ F L p)
    (hFsupp : ∀ L : ℝ, ∀ s : ℝ, ∀ x : X, x ∉ K → F L (s, x) = 0)
    (hfib : ∀ L : ℝ, ∀ x : X, (∫ s : ℝ, F L (s, x)) ≤ A L)
    (hA : Tendsto (fun L : ℝ => L ^ N * A L) atTop (𝓝 0)) :
    Tendsto (fun L : ℝ => L ^ N * ∫ p, F L p ∂(volume.prod μ)) atTop (𝓝 0) := by
  have hKr : (0 : ℝ) ≤ μ.real K := ENNReal.toReal_nonneg
  have hlim : Tendsto (fun L : ℝ => μ.real K * (L ^ N * A L)) atTop (𝓝 0) := by
    simpa using hA.const_mul (μ.real K)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact mul_nonneg (pow_nonneg hL N) (integral_nonneg fun p => hFnn L p)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    have hb := connes_transverse_prodMass_le hK hKfin (hFint L) (hFnn L) (hFsupp L) (hfib L)
    calc L ^ N * ∫ p, F L p ∂(volume.prod μ)
        ≤ L ^ N * (μ.real K * A L) :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg hL N)
      _ = μ.real K * (L ^ N * A L) := by ring

end

end GaloisForLFunctions.RHTower
