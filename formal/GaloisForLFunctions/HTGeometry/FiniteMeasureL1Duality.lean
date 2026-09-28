import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# `L¹–L^∞` duality for finite measures, Hahn–Banach annihilators and codimension

For a finite measure `μ`:

* `l2ToL1` is the continuous inclusion `L²(μ) → L¹(μ)`, and `linftyPairing g` is the functional
  `f ↦ ∫ g f dμ` on `L¹(μ)` of an essentially bounded `g`.
* **Duality.**  Every continuous linear functional `ℓ` on `L¹(μ)` is `f ↦ ∫ g f dμ` for a strongly
  measurable `g` with `|g| ≤ ‖ℓ‖` a.e.  The Riesz representation of `ℓ` restricted to `L²(μ)` is
  bounded by testing on indicators, and density of simple functions extends the identity.
* **Annihilators.**  A point outside the closure of a subspace `S ⊆ L¹(μ)` is detected by an
  essentially bounded function annihilating `S`; equivalently `f ∈ closure S` iff every bounded
  annihilator of `S` annihilates `f`.
* **Codimension.**  For functionals `ℓ₁, …, ℓₙ` on a normed space annihilating `S` and independent on a
  subspace `W`, the closure of `S` has codimension at least `n` in `W`, exactly `n` when the `ℓᵢ` cut
  out the closure, and infinite codimension follows from arbitrarily large such families.
-/
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-! ## Integration against essentially bounded functions -/

/-- Integration against an essentially bounded strongly measurable `g`, as a continuous functional
on `L¹(μ)`. -/
def linftyPairing (g : α → ℝ) (hg : StronglyMeasurable g) (C : ℝ) (hgC : ∀ᵐ x ∂μ, |g x| ≤ C) :
    StrongDual ℝ (Lp ℝ 1 μ) :=
  ContinuousLinearMap.lpPairing μ ∞ 1 (ContinuousLinearMap.mul ℝ ℝ)
    ((memLp_top_of_bound hg.aestronglyMeasurable C (by simpa using hgC)).toLp g)

theorem linftyPairing_apply (g : α → ℝ) (hg : StronglyMeasurable g) (C : ℝ)
    (hgC : ∀ᵐ x ∂μ, |g x| ≤ C) (f : Lp ℝ 1 μ) :
    linftyPairing g hg C hgC f = ∫ x, g x * f x ∂μ := by
  rw [linftyPairing, ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_top_of_bound hg.aestronglyMeasurable C
    (by simpa using hgC))] with x hx
  rw [hx]
  rfl

variable [IsFiniteMeasure μ]


/-! ## The inclusion `L² → L¹` of a finite measure space -/

theorem memLp_one_of_memLp_two {f : α → ℝ} (hf : MemLp f 2 μ) : MemLp f 1 μ :=
  hf.mono_exponent (by norm_num)

/-- The inclusion `L²(μ) → L¹(μ)` for a finite measure. -/
def l2ToL1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_one_of_memLp_two (Lp.memLp f)).toLp f
      map_add' := fun f g => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_one_of_memLp_two (Lp.memLp (f + g))),
          MemLp.coeFn_toLp (memLp_one_of_memLp_two (Lp.memLp f)),
          MemLp.coeFn_toLp (memLp_one_of_memLp_two (Lp.memLp g)), Lp.coeFn_add f g,
          Lp.coeFn_add ((memLp_one_of_memLp_two (Lp.memLp f)).toLp f)
            ((memLp_one_of_memLp_two (Lp.memLp g)).toLp g)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_one_of_memLp_two (Lp.memLp (c • f))),
          MemLp.coeFn_toLp (memLp_one_of_memLp_two (Lp.memLp f)), Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((memLp_one_of_memLp_two (Lp.memLp f)).toLp f)] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h4, Pi.smul_apply, h2, h3, Pi.smul_apply] }
    ((μ univ).toReal ^ (1 / 2 : ℝ)) fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp, Lp.norm_def]
      have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (f := (f : α → ℝ))
        (p := 1) (q := 2) (by norm_num) (Lp.aestronglyMeasurable f)
      have hfin : eLpNorm (f : α → ℝ) 2 μ ≠ ∞ := (Lp.memLp f).2.ne
      have hμ : μ univ ≠ ∞ := measure_ne_top μ univ
      norm_num at h
      rw [mul_comm]
      calc (eLpNorm (f : α → ℝ) 1 μ).toReal ≤ (eLpNorm (f : α → ℝ) 2 μ * μ univ ^ (1 / 2 : ℝ)).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top hfin (ENNReal.rpow_ne_top_of_nonneg
              (by norm_num) hμ)) h
        _ = (eLpNorm (f : α → ℝ) 2 μ).toReal * (μ univ).toReal ^ (1 / 2 : ℝ) := by
            rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]

theorem coeFn_l2ToL1 (f : Lp ℝ 2 μ) : (l2ToL1 f : α → ℝ) =ᵐ[μ] f :=
  MemLp.coeFn_toLp (memLp_one_of_memLp_two (Lp.memLp f))

/-! ## Every continuous functional on `L¹` is integration against an `L^∞` function -/

theorem l2ToL1_indicatorConstLp {s : Set α} (hs : MeasurableSet s) (c : ℝ) :
    l2ToL1 (indicatorConstLp 2 hs (measure_ne_top μ s) c) =
      indicatorConstLp 1 hs (measure_ne_top μ s) c := by
  refine Lp.ext ?_
  filter_upwards [coeFn_l2ToL1 (indicatorConstLp 2 hs (measure_ne_top μ s) c),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := c),
    indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := measure_ne_top μ s) (c := c)] with x h1 h2 h3
  rw [h1, h2, h3]

/-- **`L¹–L^∞` duality for a finite measure.**  Every continuous linear functional `ℓ` on `L¹(μ)` is
`f ↦ ∫ g f dμ` for a strongly measurable `g` with `|g| ≤ ‖ℓ‖` almost everywhere.  The proof
restricts `ℓ` to `L²(μ)`, applies the Riesz representation there, bounds the representative by
testing on indicators, and extends by density of simple functions. -/
theorem exists_linfty_representation (ℓ : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∃ g : α → ℝ, StronglyMeasurable g ∧ (∀ᵐ x ∂μ, |g x| ≤ ‖ℓ‖) ∧
      ∀ f : Lp ℝ 1 μ, ℓ f = ∫ x, g x * f x ∂μ := by
  set g₂ : Lp ℝ 2 μ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm (ℓ.comp l2ToL1)
  have hrep : ∀ f : Lp ℝ 2 μ, ℓ (l2ToL1 f) = ∫ x, g₂ x * f x ∂μ := by
    intro f
    have h := InnerProductSpace.toDual_symm_apply (x := f) (y := ℓ.comp l2ToL1)
    rw [MeasureTheory.L2.inner_def] at h
    rw [← ContinuousLinearMap.comp_apply, ← h]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  set g : α → ℝ := (g₂ : α → ℝ) with hgdef
  have hgm : StronglyMeasurable g := Lp.stronglyMeasurable g₂
  have hside : ∀ c : ℝ, |c| = 1 → μ {x | ‖ℓ‖ < c * g x} = 0 := by
    intro c hc
    set A := {x | ‖ℓ‖ < c * g x}
    have hA : MeasurableSet A := measurableSet_lt measurable_const (hgm.measurable.const_mul c)
    by_contra hpos
    have hval : ℓ (l2ToL1 (indicatorConstLp 2 hA (measure_ne_top μ A) c)) =
        ∫ x in A, c * g x ∂μ := by
      rw [hrep, ← integral_indicator hA]
      refine integral_congr_ae ?_
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top μ A)
        (c := c)] with x hx
      rw [hx]
      by_cases hxA : x ∈ A
      · rw [indicator_of_mem hxA, indicator_of_mem hxA]; ring
      · rw [indicator_of_notMem hxA, indicator_of_notMem hxA, mul_zero]
    have hle : ∫ x in A, c * g x ∂μ ≤ ‖ℓ‖ * μ.real A := by
      rw [← hval]
      refine (le_abs_self _).trans ((ℓ.le_opNorm _).trans ?_)
      rw [l2ToL1_indicatorConstLp, norm_indicatorConstLp (by norm_num) (by norm_num),
        Real.norm_eq_abs, hc]
      simp
    have hint : IntegrableOn (fun x => c * g x) A μ := by
      have h := (Lp.memLp g₂).integrable (by norm_num)
      exact (h.const_mul c).integrableOn
    have hgt : 0 < ∫ x in A, (c * g x - ‖ℓ‖) ∂μ := by
      refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ (hint.sub (integrableOn_const
        (measure_ne_top μ A)))).2 ?_
      · exact (ae_restrict_iff' hA).2 (ae_of_all _ fun x hx => by
          simp only [Pi.zero_apply]; exact (sub_pos.2 hx).le)
      · have hsub : A ⊆ Function.support (fun x => c * g x - ‖ℓ‖) ∩ A := fun x hx =>
          ⟨(sub_pos.2 hx).ne', hx⟩
        exact lt_of_lt_of_le (pos_iff_ne_zero.2 hpos) (measure_mono hsub)
    rw [integral_sub hint (integrableOn_const (measure_ne_top μ A)), setIntegral_const,
      smul_eq_mul] at hgt
    linarith
  have hbound : ∀ᵐ x ∂μ, |g x| ≤ ‖ℓ‖ := by
    have h1 := hside 1 (by norm_num)
    have h2 := hside (-1) (by norm_num)
    have h1' : ∀ᵐ x ∂μ, ¬ (‖ℓ‖ < 1 * g x) := ae_iff.2 (by simp only [not_not]; exact h1)
    have h2' : ∀ᵐ x ∂μ, ¬ (‖ℓ‖ < -1 * g x) := ae_iff.2 (by simp only [not_not]; exact h2)
    filter_upwards [h1', h2'] with x hx1 hx2
    simp only [one_mul, neg_one_mul, not_lt] at hx1 hx2
    exact abs_le.2 ⟨by linarith, hx1⟩
  refine ⟨g, hgm, hbound, fun f => ?_⟩
  rw [← linftyPairing_apply g hgm ‖ℓ‖ hbound f]
  refine Lp.induction (p := 1) (by norm_num)
    (motive := fun f => ℓ f = linftyPairing g hgm ‖ℓ‖ hbound f) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, ← l2ToL1_indicatorConstLp hs c, hrep,
      linftyPairing_apply, l2ToL1_indicatorConstLp]
    refine integral_congr_ae ?_
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := measure_ne_top μ s) (c := c),
      indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := measure_ne_top μ s) (c := c)] with x h1 h2
    rw [h1, h2]
  · intro f₁ f₂ _ _ _ h1 h2
    rw [map_add, map_add, h1, h2]
  · exact isClosed_eq ℓ.continuous (linftyPairing g hgm ‖ℓ‖ hbound).continuous

/-! ## Hahn–Banach in `L¹` -/

/-- **Bounded annihilators.**  If `f` is not in the closure of a subspace `S` of `L¹(μ)`, an
essentially bounded `g` annihilates `S` but not `f`. -/
theorem exists_linfty_annihilator {S : Submodule ℝ (Lp ℝ 1 μ)} {f : Lp ℝ 1 μ}
    (hf : f ∉ S.topologicalClosure) :
    ∃ g : α → ℝ, StronglyMeasurable g ∧ (∃ C, ∀ᵐ x ∂μ, |g x| ≤ C) ∧
      (∀ s ∈ S, ∫ x, g x * s x ∂μ = 0) ∧ ∫ x, g x * f x ∂μ ≠ 0 := by
  obtain ⟨ℓ, u, hℓf, hℓt⟩ := geometric_hahn_banach_point_closed
    S.topologicalClosure.convex S.isClosed_topologicalClosure hf
  have hzero : ∀ b ∈ S.topologicalClosure, ℓ b = 0 := by
    intro b hb
    by_contra hne
    have h := hℓt (((u - 1) / ℓ b) • b) (Submodule.smul_mem _ _ hb)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at h
    linarith
  have hu : u < 0 := by simpa using hℓt 0 (Submodule.zero_mem _)
  obtain ⟨g, hgm, hgb, hgrep⟩ := exists_linfty_representation ℓ
  refine ⟨g, hgm, ⟨‖ℓ‖, hgb⟩, fun s hs => ?_, ?_⟩
  · rw [← hgrep]; exact hzero s (S.le_topologicalClosure hs)
  · rw [← hgrep]; linarith

/-- **Bipolar description of closures in `L¹`.** -/
theorem mem_topologicalClosure_iff_linfty {S : Submodule ℝ (Lp ℝ 1 μ)} {f : Lp ℝ 1 μ} :
    f ∈ S.topologicalClosure ↔ ∀ g : α → ℝ, StronglyMeasurable g → (∃ C, ∀ᵐ x ∂μ, |g x| ≤ C) →
      (∀ s ∈ S, ∫ x, g x * s x ∂μ = 0) → ∫ x, g x * f x ∂μ = 0 := by
  constructor
  · intro hf g hgm ⟨C, hgC⟩ hS
    have hker : S ≤ LinearMap.ker (linftyPairing g hgm C hgC : Lp ℝ 1 μ →ₗ[ℝ] ℝ) := fun s hs => by
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, linftyPairing_apply]
      exact hS s hs
    have hclosed : IsClosed ((LinearMap.ker (linftyPairing g hgm C hgC :
        Lp ℝ 1 μ →ₗ[ℝ] ℝ)) : Set (Lp ℝ 1 μ)) :=
      (linftyPairing g hgm C hgC).isClosed_ker
    have := Submodule.topologicalClosure_minimal S hker hclosed hf
    simpa [linftyPairing_apply] using this
  · intro h
    by_contra hf
    obtain ⟨g, hgm, hgb, hS, hne⟩ := exists_linfty_annihilator hf
    exact hne (h g hgm hgb hS)

/-! ## Codimension from finitely many functionals -/

section Codimension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The evaluation map `w ↦ (ℓ_i w)_i` of finitely many functionals on a subspace `W`. -/
def functionalEval (W : Submodule ℝ E) {n : ℕ} (ℓ : Fin n → StrongDual ℝ E) :
    W →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i => (ℓ i : E →ₗ[ℝ] ℝ).comp W.subtype

theorem functionalEval_apply (W : Submodule ℝ E) {n : ℕ} (ℓ : Fin n → StrongDual ℝ E) (w : W)
    (i : Fin n) : functionalEval W ℓ w i = ℓ i w := rfl

/-- Functionals that are linearly independent on `W` evaluate `W` onto `ℝⁿ`. -/
theorem functionalEval_surjective (W : Submodule ℝ E) {n : ℕ} (ℓ : Fin n → StrongDual ℝ E)
    (hind : ∀ c : Fin n → ℝ, (∀ w ∈ W, ∑ i, c i * ℓ i w = 0) → c = 0) :
    Function.Surjective (functionalEval W ℓ) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  set c : Fin n → ℝ := fun i => f (fun j => if i = j then 1 else 0)
  have hc : c = 0 := hind c fun w hw => by
    have h := hle (LinearMap.mem_range_self (functionalEval W ℓ) ⟨w, hw⟩)
    rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]; rfl
  apply hf0
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun i _ => by
    rw [smul_eq_mul, show f (fun j => if i = j then 1 else 0) = c i from rfl, hc, Pi.zero_apply,
      mul_zero]

theorem topologicalClosure_le_ker_functionalEval {W S : Submodule ℝ E} {n : ℕ}
    (ℓ : Fin n → StrongDual ℝ E) (hann : ∀ i, ∀ s ∈ S, ℓ i s = 0) :
    S.topologicalClosure.comap W.subtype ≤ LinearMap.ker (functionalEval W ℓ) := by
  intro w hw
  rw [LinearMap.mem_ker]
  funext i
  have hker : S ≤ LinearMap.ker (ℓ i : E →ₗ[ℝ] ℝ) := fun s hs => hann i s hs
  exact Submodule.topologicalClosure_minimal S hker (ℓ i).isClosed_ker hw

/-- `n` functionals annihilating `S` and independent on `W` bound the codimension of the closure of
`S` in `W` from below. -/
theorem le_finrank_quotient_of_functionals {W S : Submodule ℝ E} {n : ℕ}
    (ℓ : Fin n → StrongDual ℝ E) (hann : ∀ i, ∀ s ∈ S, ℓ i s = 0)
    (hind : ∀ c : Fin n → ℝ, (∀ w ∈ W, ∑ i, c i * ℓ i w = 0) → c = 0)
    [FiniteDimensional ℝ (W ⧸ S.topologicalClosure.comap W.subtype)] :
    n ≤ Module.finrank ℝ (W ⧸ S.topologicalClosure.comap W.subtype) := by
  set Φ := (S.topologicalClosure.comap W.subtype).liftQ (functionalEval W ℓ)
    (topologicalClosure_le_ker_functionalEval ℓ hann)
  have hsurj : Function.Surjective Φ := by
    intro v
    obtain ⟨w, hw⟩ := functionalEval_surjective W ℓ hind v
    exact ⟨Submodule.Quotient.mk w, by simp [Φ, hw]⟩
  have := LinearMap.finrank_le_finrank_of_surjective hsurj
  rwa [Module.finrank_fin_fun] at this

/-- Arbitrarily many independent annihilating functionals give infinite codimension. -/
theorem not_finiteDimensional_quotient_of_functionals {W S : Submodule ℝ E}
    (h : ∀ n : ℕ, ∃ ℓ : Fin n → StrongDual ℝ E, (∀ i, ∀ s ∈ S, ℓ i s = 0) ∧
      ∀ c : Fin n → ℝ, (∀ w ∈ W, ∑ i, c i * ℓ i w = 0) → c = 0) :
    ¬ FiniteDimensional ℝ (W ⧸ S.topologicalClosure.comap W.subtype) := by
  intro hfin
  obtain ⟨ℓ, hann, hind⟩ :=
    h (Module.finrank ℝ (W ⧸ S.topologicalClosure.comap W.subtype) + 1)
  have := le_finrank_quotient_of_functionals ℓ hann hind
  omega

/-- **Exact codimension.**  If `n` functionals annihilate `S`, are independent on `W`, and cut out
the closure of `S` inside `W`, the closure has codimension exactly `n` in `W`. -/
theorem finrank_quotient_eq_of_functionals {W S : Submodule ℝ E} {n : ℕ}
    (ℓ : Fin n → StrongDual ℝ E) (hann : ∀ i, ∀ s ∈ S, ℓ i s = 0)
    (hind : ∀ c : Fin n → ℝ, (∀ w ∈ W, ∑ i, c i * ℓ i w = 0) → c = 0)
    (hcut : ∀ w ∈ W, (∀ i, ℓ i w = 0) → w ∈ S.topologicalClosure) :
    Module.finrank ℝ (W ⧸ S.topologicalClosure.comap W.subtype) = n := by
  have hker : LinearMap.ker (functionalEval W ℓ) = S.topologicalClosure.comap W.subtype := by
    refine le_antisymm (fun w hw => ?_) (topologicalClosure_le_ker_functionalEval ℓ hann)
    rw [LinearMap.mem_ker] at hw
    exact hcut w w.2 fun i => congrFun hw i
  have e := LinearMap.quotKerEquivOfSurjective _ (functionalEval_surjective W ℓ hind)
  rw [hker] at e
  rw [e.finrank_eq, Module.finrank_fin_fun]

end Codimension

end

end GaloisForLFunctions.HTGeometry
