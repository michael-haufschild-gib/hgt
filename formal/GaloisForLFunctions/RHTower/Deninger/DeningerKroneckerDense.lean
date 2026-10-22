import GaloisForLFunctions.RHTower.Deninger.DeningerWeylCriterion
import Mathlib.Topology.UrysohnsLemma

/-!
# Kronecker's theorem in `d` dimensions

A linear flow on the `d`-dimensional torus has dense orbit exactly when its velocity vector pairs
nontrivially with every nonzero integer vector, that is, exactly when the annihilator of the
one-parameter subgroup is trivial.

Density follows from equidistribution: a function vanishing on the orbit closure has vanishing
time averages, hence vanishing mean, and a nonnegative continuous function with vanishing mean is
identically zero because the Haar measure is positive on nonempty open sets.  Urysohn's lemma
supplies such a function whenever the orbit closure misses a point.  The converse is immediate: a
character in the annihilator is constant along the flow, so it would have to be constant on the
whole torus, contradicting that its mean vanishes.

* `deningerTorusIntegral_pos` : a nonnegative continuous function positive somewhere has positive
  mean.
* `deningerKroneckerFlow_dense` : trivial annihilator implies dense orbit.
* `deningerAnnihilator_eq_zero_of_dense` : dense orbit implies trivial annihilator.
* `deningerKroneckerFlow_dense_iff` : Kronecker's theorem.
-/

namespace RHTower

open UnitAddTorus MeasureTheory Filter Topology

/-- The circle is normalised to total mass one, as in the multivariate Fourier theory. -/
noncomputable local instance deningerKroneckerDenseMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance deningerKroneckerDenseIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance deningerKroneckerDenseIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Kronecker

variable {d : Type*} [Fintype d]

/-- A real continuous function on the torus is integrable. -/
theorem deningerTorusIntegrableReal (f : C(UnitAddTorus d, ℝ)) :
    Integrable (fun x => f x) (volume : Measure (UnitAddTorus d)) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **A nonnegative continuous function that is positive somewhere has positive mean.**  The set
where it is positive is open and nonempty, and Haar measure is positive on such sets. -/
theorem deningerTorusIntegral_pos {f : C(UnitAddTorus d, ℝ)} (hf : ∀ x, 0 ≤ f x)
    {x₀ : UnitAddTorus d} (hx₀ : 0 < f x₀) : 0 < ∫ x : UnitAddTorus d, f x := by
  rw [integral_pos_iff_support_of_nonneg (fun x => hf x) (deningerTorusIntegrableReal f)]
  have hopen : IsOpen {x : UnitAddTorus d | 0 < f x} :=
    isOpen_lt continuous_const f.continuous
  have hsub : {x : UnitAddTorus d | 0 < f x} ⊆ Function.support fun x => f x := by
    intro x hx
    exact ne_of_gt hx
  exact lt_of_lt_of_le (hopen.measure_pos volume ⟨x₀, hx₀⟩) (measure_mono hsub)

/-- **Kronecker's theorem: trivial annihilator implies dense orbit.**  A function vanishing on the
orbit closure has zero time averages, hence zero mean by Weyl's criterion, hence is identically
zero — so no point can be separated from the orbit closure. -/
theorem deningerKroneckerFlow_dense (lam : d → ℝ)
    (hlam : ∀ n : d → ℤ, n ≠ 0 → deningerFrequency n lam ≠ 0) :
    Dense (Set.range (deningerTorusFlow lam)) := by
  intro x₀
  by_contra hx₀
  obtain ⟨f, hf0, hf1, hfIcc⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_closure (s := Set.range (deningerTorusFlow lam))) (isClosed_singleton (x := x₀))
    (Set.disjoint_singleton_right.mpr hx₀)
  have hfnonneg : ∀ x, 0 ≤ f x := fun x => (hfIcc x).1
  have hfx₀ : f x₀ = 1 := hf1 rfl
  set F : C(UnitAddTorus d, ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ with hF
  have hflow : ∀ t : ℝ, F (deningerTorusFlow lam t) = 0 := by
    intro t
    have hmem : deningerTorusFlow lam t ∈ closure (Set.range (deningerTorusFlow lam)) :=
      subset_closure ⟨t, rfl⟩
    have := hf0 hmem
    show ((f (deningerTorusFlow lam t) : ℝ) : ℂ) = 0
    rw [this]
    simp
  have hzero : ∀ T : ℝ, deningerFlowAverage lam F T = 0 := by
    intro T
    rw [deningerFlowAverage, intervalIntegral.integral_congr fun t _ => hflow t]
    simp
  have hmean : (∫ x : UnitAddTorus d, F x) = 0 := by
    refine tendsto_nhds_unique (deningerWeyl lam hlam F) ?_
    have : deningerFlowAverage lam F = fun _ : ℝ => (0 : ℂ) := funext hzero
    rw [this]
    exact tendsto_const_nhds
  have hreal : (∫ x : UnitAddTorus d, f x) = 0 := by
    have h : (∫ x : UnitAddTorus d, ((f x : ℝ) : ℂ)) = ((∫ x : UnitAddTorus d, f x : ℝ) : ℂ) :=
      integral_complex_ofReal
    have hmean' : (∫ x : UnitAddTorus d, ((f x : ℝ) : ℂ)) = 0 := hmean
    rw [h] at hmean'
    exact_mod_cast hmean'
  have hpos : 0 < ∫ x : UnitAddTorus d, f x :=
    deningerTorusIntegral_pos hfnonneg (x₀ := x₀) (by rw [hfx₀]; norm_num)
  exact absurd hreal (ne_of_gt hpos)

/-- **Dense orbit implies trivial annihilator.**  A character in the annihilator is constant along
the flow, hence constant on the closure of the orbit; if that is everything its mean would be one,
but the mean of a nontrivial character vanishes. -/
theorem deningerAnnihilator_eq_zero_of_dense {lam : d → ℝ}
    (hdense : Dense (Set.range (deningerTorusFlow lam))) {n : d → ℤ}
    (hn : deningerFrequency n lam = 0) : n = 0 := by
  by_contra hne
  have hconst : ∀ t : ℝ, mFourier n (deningerTorusFlow lam t) = 1 := by
    intro t
    rw [deningerMFourier_flow, hn]
    simp
  have hdr : DenseRange (deningerTorusFlow lam) := hdense
  have heq : (mFourier n : UnitAddTorus d → ℂ) = fun _ => (1 : ℂ) :=
    hdr.equalizer (mFourier n).continuous continuous_const (funext hconst)
  have hint : (∫ x : UnitAddTorus d, mFourier n x) = 1 := by
    rw [show (fun x : UnitAddTorus d => mFourier n x) = fun _ => (1 : ℂ) from heq]
    simp
  rw [deningerMFourier_integral_eq_zero hne] at hint
  exact zero_ne_one hint

/-- **Kronecker's theorem.**  The orbit of the linear flow is dense exactly when the annihilator
of its velocity vector is trivial. -/
theorem deningerKroneckerFlow_dense_iff (lam : d → ℝ) :
    Dense (Set.range (deningerTorusFlow lam))
      ↔ ∀ n : d → ℤ, deningerFrequency n lam = 0 → n = 0 := by
  constructor
  · intro hdense n hn
    exact deningerAnnihilator_eq_zero_of_dense hdense hn
  · intro h
    refine deningerKroneckerFlow_dense lam fun n hn hfreq => hn (h n hfreq)

end Kronecker

end RHTower
