import GaloisForLFunctions.HTGeometry.FiniteObservableKoopmanBoundary
import GaloisForLFunctions.HTGeometry.RankTwoRealDependentPeriods

/-!
# Small translations make a finite observable model differential

A finite-dimensional space `V` of entire functions that is stable under a family of translations
whose integer span is **not discrete** is automatically stable under differentiation.  Along a
sequence of nonzero steps `p n → 0` the difference quotients `(g(· + p n) − g) / p n` all lie in
`V`, they converge pointwise to `g'`, and a finite-dimensional subspace is closed in the topology
of pointwise convergence (`Submodule.closed_of_finiteDimensional`).  Hence `g' ∈ V`.

The corpus's finite observable-model boundary then applies verbatim: in a finite-dimensional
derivation-invariant space every member has a nonzero **constant-coefficient** annihilator
(`differentiallyAlgebraic_of_mem_derivInvariantObservableSpace`), so every member is differentially
algebraic.

This is the finite-state form of the period-rank law.  Three things it does *not* need: a Wronskian
construction, transitivity of differential algebraicity over a differentially algebraic coefficient
field, and invertibility of the internal transition matrices — the translation is invertible on `V`
for free, because an injective endomorphism of a finite-dimensional space is surjective
(`translationStable_neg`).

* `derivInvariantObservableSpace_of_small_translations` — the analytic step;
* `translationStable_neg`, `translationStable_of_mem_span_range` — the step group acts;
* **`differentiallyAlgebraic_of_translationStable_of_not_discrete`** — the general law, and its two
  specializations `..._three` (three `ℚ`-independent steps) and `..._two_realDependent` (two
  `ℚ`-independent `ℝ`-dependent steps);
* **`differentiallyAlgebraic_component_of_matrix_monodromy`** — the vector form: a `ℂ^m`-valued
  entire function reproduced by each translation up to a constant matrix has every component
  differentially algebraic.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Translation of a function: `translate w g` is `z ↦ g (z + w)`. -/
def translate (w : ℂ) (g : ℂ → ℂ) : ℂ → ℂ := fun z => g (z + w)

/-- A space of functions stable under the translation by `w`. -/
def TranslationStable (V : Submodule ℂ (ℂ → ℂ)) (w : ℂ) : Prop :=
  ∀ g ∈ V, translate w g ∈ V

/-! ### Arbitrarily small translations force derivation invariance -/

/-- **Small translations differentiate.**  A finite-dimensional space of differentiable functions
stable under translation by each of a sequence of nonzero steps tending to zero is closed under
differentiation: the difference quotients lie in the space and converge pointwise to the
derivative, and a finite-dimensional subspace is closed. -/
theorem derivInvariantObservableSpace_of_small_translations
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (hdiff : ∀ g ∈ V, Differentiable ℂ g)
    (p : ℕ → ℂ) (hp0 : Tendsto p atTop (𝓝 0)) (hpne : ∀ n, p n ≠ 0)
    (hstable : ∀ n, TranslationStable V (p n)) :
    _root_.HTGeometry.DerivInvariantObservableSpace V := by
  intro g hg
  have hqV : ∀ n, (p n)⁻¹ • (translate (p n) g - g) ∈ V := fun n =>
    V.smul_mem _ (V.sub_mem (hstable n g hg) hg)
  have htend : Tendsto (fun n => (p n)⁻¹ • (translate (p n) g - g)) atTop (𝓝 (deriv g)) := by
    rw [tendsto_pi_nhds]
    intro z
    have hslope : Tendsto (slope g z) (𝓝[≠] z) (𝓝 (deriv g z)) :=
      hasDerivAt_iff_tendsto_slope.mp ((hdiff g hg z).hasDerivAt)
    have hseq : Tendsto (fun n => z + p n) atTop (𝓝[≠] z) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨by simpa using (tendsto_const_nhds.add hp0 :
        Tendsto (fun n => z + p n) atTop (𝓝 (z + 0))), ?_⟩
      exact Eventually.of_forall fun n => by simp [hpne n]
    refine (hslope.comp hseq).congr (fun n => ?_)
    simp only [Function.comp_apply, slope_def_field, translate, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, add_sub_cancel_left]
    rw [div_eq_inv_mul]
  exact V.closed_of_finiteDimensional.mem_of_tendsto htend (Eventually.of_forall hqV)

/-! ### The step group acts -/

/-- **The translation is automatically invertible.**  A finite-dimensional space stable under the
translation by `w` is stable under the opposite translation: the translation is an injective
endomorphism of `V`, hence surjective. -/
theorem translationStable_neg (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V] {w : ℂ}
    (hV : TranslationStable V w) : TranslationStable V (-w) := by
  let T : V →ₗ[ℂ] V :=
    { toFun := fun g => ⟨translate w (g : ℂ → ℂ), hV _ g.2⟩
      map_add' := fun a b => Subtype.ext (funext fun z => rfl)
      map_smul' := fun c a => Subtype.ext (funext fun z => rfl) }
  have hinj : Function.Injective T := by
    intro a b hab
    have hval : ∀ z, (a : ℂ → ℂ) (z + w) = (b : ℂ → ℂ) (z + w) :=
      fun z => congrFun (congrArg Subtype.val hab) z
    refine Subtype.ext (funext fun z => ?_)
    have hz : z - w + w = z := by ring
    have h := hval (z - w)
    rwa [hz] at h
  have hsurj := LinearMap.surjective_of_injective hinj
  intro g hg
  obtain ⟨h, hh⟩ := hsurj ⟨g, hg⟩
  have hval : ∀ z, (h : ℂ → ℂ) (z + w) = g z :=
    fun z => congrFun (congrArg Subtype.val hh) z
  have hfun : translate (-w) g = (h : ℂ → ℂ) := by
    funext z
    have hz : z + -w + w = z := by ring
    have hv := hval (z + -w)
    rw [hz] at hv
    exact hv.symm
  rw [hfun]
  exact h.2

/-- Translation stability propagates from a family of steps to their whole integer span. -/
theorem translationStable_of_mem_span_range {ι : Type*} (V : Submodule ℂ (ℂ → ℂ))
    [FiniteDimensional ℂ V] (w : ι → ℂ) (hV : ∀ i, TranslationStable V (w i)) :
    ∀ p ∈ Submodule.span ℤ (Set.range w), TranslationStable V p := by
  have hzero : TranslationStable V 0 := by
    intro g hg
    have : translate 0 g = g := by funext z; show g (z + 0) = g z; rw [add_zero]
    rw [this]; exact hg
  have hadd : ∀ q r : ℂ, TranslationStable V q → TranslationStable V r →
      TranslationStable V (q + r) := by
    intro q r hq hr g hg
    have hcomp : translate (q + r) g = translate q (translate r g) := by
      funext z
      show g (z + (q + r)) = g (z + q + r)
      rw [add_assoc]
    rw [hcomp]
    exact hq _ (hr g hg)
  have hzsmul : ∀ (a : ℤ) (q : ℂ), TranslationStable V q → TranslationStable V (a • q) := by
    intro a q hq
    induction a using Int.induction_on with
    | zero => simpa using hzero
    | succ n ih =>
        have hs : ((n : ℤ) + 1) • q = (n : ℤ) • q + q := by rw [add_smul, one_smul]
        rw [hs]
        exact hadd _ _ ih hq
    | pred n ih =>
        have hs : (-(n : ℤ) - 1) • q = (-(n : ℤ)) • q + -q := by rw [sub_smul, one_smul]; ring
        rw [hs]
        exact hadd _ _ ih (translationStable_neg V hq)
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hV i
  | zero => exact hzero
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul a x _ hx => exact hzsmul a x hx

/-! ### The finite-state period-rank law -/

/-- **The finite-state period-rank law.**  If a finite-dimensional space of entire functions is
stable under a family of translations whose integer span is not discrete, then every member of the
space is differentially algebraic — with a *constant-coefficient* annihilator. -/
theorem differentiallyAlgebraic_of_translationStable_of_not_discrete
    {ι : Type*} (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (hdiff : ∀ g ∈ V, Differentiable ℂ g) (w : ι → ℂ)
    (hnd : ¬ DiscreteTopology (Submodule.span ℤ (Set.range w)))
    (hV : ∀ i, TranslationStable V (w i))
    {f : ℂ → ℂ} (hf : f ∈ V) : DifferentiallyAlgebraic f := by
  obtain ⟨p, hp_mem, hp_ne, hp_zero⟩ := exists_small_nonzero_of_not_discrete_intSubmodule _ hnd
  exact _root_.HTGeometry.differentiallyAlgebraic_of_mem_derivInvariantObservableSpace V hf
    (derivInvariantObservableSpace_of_small_translations V hdiff p hp_zero hp_ne
      (fun n => translationStable_of_mem_span_range V w hV (p n) (hp_mem n)))

/-- Three `ℚ`-independent steps already have a non-discrete integer span. -/
theorem differentiallyAlgebraic_of_translationStable_three
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (hdiff : ∀ g ∈ V, Differentiable ℂ g) (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v)
    (hV : ∀ i, TranslationStable V (v i))
    {f : ℂ → ℂ} (hf : f ∈ V) : DifferentiallyAlgebraic f :=
  differentiallyAlgebraic_of_translationStable_of_not_discrete V hdiff v
    (not_discrete_intSpan_fin_three v hv) hV hf

/-- Two `ℚ`-independent, `ℝ`-dependent steps have a non-discrete integer span. -/
theorem differentiallyAlgebraic_of_translationStable_two_realDependent
    (V : Submodule ℂ (ℂ → ℂ)) [FiniteDimensional ℂ V]
    (hdiff : ∀ g ∈ V, Differentiable ℂ g) (v : Fin 2 → ℂ) (hv : LinearIndependent ℚ v)
    (hdep : ¬ LinearIndependent ℝ v) (hV : ∀ i, TranslationStable V (v i))
    {f : ℂ → ℂ} (hf : f ∈ V) : DifferentiallyAlgebraic f :=
  differentiallyAlgebraic_of_translationStable_of_not_discrete V hdiff v
    (not_discrete_intSpan_fin_two_of_not_linearIndependent_real v hv hdep) hV hf

/-! ### Spans of a finite family of functions -/

/-- Translation stability of a span is checked on generators. -/
theorem translationStable_span_of_generators {ι : Type*} (g : ι → (ℂ → ℂ)) {w : ℂ}
    (h : ∀ i, translate w (g i) ∈ Submodule.span ℂ (Set.range g)) :
    TranslationStable (Submodule.span ℂ (Set.range g)) w := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero =>
      have hz : translate w (0 : ℂ → ℂ) = 0 := rfl
      rw [hz]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      have hxy : translate w (x + y) = translate w x + translate w y := rfl
      rw [hxy]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      have hcx : translate w (c • x) = c • translate w x := rfl
      rw [hcx]; exact Submodule.smul_mem _ c hx

/-- Every member of the span of a family of entire functions is entire. -/
theorem differentiable_of_mem_span {ι : Type*} (g : ι → (ℂ → ℂ))
    (h : ∀ i, Differentiable ℂ (g i)) :
    ∀ u ∈ Submodule.span ℂ (Set.range g), Differentiable ℂ u := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => exact differentiable_const 0
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.const_smul c

/-- **Scalar constant multipliers.**  A single entire function reproduced up to a constant by each
translation of a family with non-discrete integer span is differentially algebraic.  The multipliers
are not required to be nonzero. -/
theorem differentiallyAlgebraic_of_quasiperiods_of_not_discrete {ι : Type*} {f : ℂ → ℂ}
    (hd : Differentiable ℂ f) (w : ι → ℂ) (c : ι → ℂ)
    (hqp : ∀ (i : ι) (z : ℂ), f (z + w i) = c i * f z)
    (hnd : ¬ DiscreteTopology (Submodule.span ℤ (Set.range w))) :
    DifferentiallyAlgebraic f := by
  set g : Unit → (ℂ → ℂ) := fun _ => f with hgdef
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  have hgen : f ∈ Submodule.span ℂ (Set.range g) := Submodule.subset_span ⟨(), rfl⟩
  have hstab : ∀ i, TranslationStable (Submodule.span ℂ (Set.range g)) (w i) := by
    intro i
    refine translationStable_span_of_generators g (fun _ => ?_)
    have hfun : translate (w i) f = c i • f := by
      funext z
      show f (z + w i) = c i * f z
      exact hqp i z
    show translate (w i) f ∈ _
    rw [hfun]
    exact Submodule.smul_mem _ _ hgen
  exact differentiallyAlgebraic_of_translationStable_of_not_discrete
    (Submodule.span ℂ (Set.range g)) (differentiable_of_mem_span g (fun _ => hd)) w hnd hstab hgen

/-! ### Constant internal monodromy -/

/-- **Constant internal monodromy does not escape the law.**  A `ℂ^m`-valued entire function which
each translation of a family reproduces up to a *constant* matrix, the integer span of the steps
being non-discrete, has every component differentially algebraic.  No invertibility of the matrices
is required. -/
theorem differentiallyAlgebraic_component_of_matrix_monodromy
    {m : ℕ} {ι : Type*} (G : ℂ → (Fin m → ℂ))
    (hdiff : ∀ i, Differentiable ℂ (fun z => G z i))
    (w : ι → ℂ) (M : ι → Matrix (Fin m) (Fin m) ℂ)
    (hmono : ∀ k z, G (z + w k) = (M k).mulVec (G z))
    (hnd : ¬ DiscreteTopology (Submodule.span ℤ (Set.range w))) (i : Fin m) :
    DifferentiallyAlgebraic (fun z => G z i) := by
  set g : Fin m → (ℂ → ℂ) := fun j z => G z j with hg
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  refine differentiallyAlgebraic_of_translationStable_of_not_discrete
    (Submodule.span ℂ (Set.range g)) (differentiable_of_mem_span g hdiff) w hnd
    (fun k => translationStable_span_of_generators g (fun j => ?_))
    (Submodule.subset_span ⟨i, rfl⟩)
  have hsum : translate (w k) (g j) = ∑ l : Fin m, (M k) j l • g l := by
    funext z
    show G (z + w k) j = (∑ l : Fin m, (M k) j l • g l) z
    rw [hmono k z]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, hg]
  rw [hsum]
  exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))

end GaloisForLFunctions.HTGeometry
