import GaloisForLFunctions.HTGeometry.IntegerTorusHomomorphism
import GaloisForLFunctions.HTGeometry.FrequencyLatticeBasis

/-!
# The closure of a phase orbit is a subtorus

The completed time of a finite frequency packet is the closure of its phase orbit in the phase
torus.  For a rationally independent packet the orbit is dense, by weak convergence of the
uniform-time phase laws to Haar measure: a continuous function vanishing on the orbit closure has
vanishing Haar mean, hence vanishes, so the closure misses no point.

In general the frequencies are integer combinations of a rationally independent basis of the group
they generate, so the orbit is the image of a dense orbit under the integer homomorphism of tori
attached to that presentation.  Its closure is therefore the range of that homomorphism, which is
injective; the completed time is a torus of dimension the rank of the frequency group.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d k : Type*} [Fintype d] [Fintype k]

/-- The sampled phase point is the phase flow at the sampled time. -/
theorem finiteTorusPhasePoint_eq_finiteClockPhasePoint (omega : d → ℝ) (A u : ℝ) :
    finiteTorusPhasePoint omega A u = finiteClockPhasePoint omega (A * (2 * u - 1)) := rfl

/-- A nonnegative continuous function on the phase torus which is positive somewhere has positive
Haar mean. -/
theorem integral_pos_of_haar {f : C(UnitAddTorus k, ℝ)} (hf : ∀ x, 0 ≤ f x)
    {x₀ : UnitAddTorus k} (hx₀ : 0 < f x₀) :
    0 < ∫ x, f x ∂(finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) := by
  haveI : (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)).IsOpenPosMeasure := by
    show (Measure.pi (fun _ => AddCircle.haarAddCircle)).IsOpenPosMeasure
    infer_instance
  have hint : Integrable (fun x => f x)
      (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_pos_iff_support_of_nonneg (fun x => hf x) hint]
  have hopen : IsOpen {x : UnitAddTorus k | 0 < f x} := isOpen_lt continuous_const f.continuous
  have hsub : {x : UnitAddTorus k | 0 < f x} ⊆ Function.support fun x => f x :=
    fun x hx => ne_of_gt hx
  exact lt_of_lt_of_le (hopen.measure_pos _ ⟨x₀, hx₀⟩) (measure_mono hsub)

/-- **Kronecker density.**  A rationally independent frequency packet has dense phase orbit. -/
theorem dense_range_finiteClockPhasePoint (gamma : k → ℝ)
    (hgamma : RationallyIndependentFrequency gamma) :
    Dense (Set.range (finiteClockPhasePoint gamma)) := by
  by_contra hnd
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : UnitAddTorus k,
      x₀ ∉ closure (Set.range (finiteClockPhasePoint gamma)) := by
    by_contra hcon
    exact hnd fun x => not_not.mp fun hx => hcon ⟨x, hx⟩
  obtain ⟨f, hf0, hf1, hfIcc⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_closure (s := Set.range (finiteClockPhasePoint gamma)))
    (isClosed_singleton (x := x₀)) (Set.disjoint_singleton_right.mpr hx₀)
  have hvanish : ∀ (A u : ℝ), f (finiteTorusPhasePoint gamma A u) = 0 := by
    intro A u
    refine hf0 (subset_closure ⟨A * (2 * u - 1), ?_⟩)
    exact (finiteTorusPhasePoint_eq_finiteClockPhasePoint gamma A u).symm
  have hzero : ∀ A : ℝ,
      (∫ x, f x ∂(finiteTorusPhaseProbabilityMeasure gamma A : Measure (UnitAddTorus k))) = 0 := by
    intro A
    rw [finiteTorusPhaseProbabilityMeasure, ProbabilityMeasure.toMeasure_map,
      integral_map (finiteTorusPhasePoint_continuous gamma A).aemeasurable
        f.continuous.aestronglyMeasurable]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => hvanish A u)]
    simp
  have hconv := (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (finiteTorusPhaseProbabilityMeasure_tendsto_haar gamma hgamma))
    (BoundedContinuousFunction.mkOfCompact f)
  have hconv' : Tendsto
      (fun A => (∫ x, f x ∂(finiteTorusPhaseProbabilityMeasure gamma A : Measure (UnitAddTorus k))))
      atTop (𝓝 (∫ x, f x ∂(finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)))) :=
    hconv
  have hlim : (∫ x, f x ∂(finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))) = 0 :=
    tendsto_nhds_unique hconv' (Tendsto.congr (fun A => (hzero A).symm) tendsto_const_nhds)
  have hpos := integral_pos_of_haar (f := f) (fun x => (hfIcc x).1) (x₀ := x₀)
    (by rw [hf1 rfl]; norm_num)
  exact absurd hlim (ne_of_gt hpos)

/-- The integer homomorphism of tori, bundled. -/
def torusIntegerAddHom (M : d → k → ℤ) : UnitAddTorus k →+ UnitAddTorus d where
  toFun := torusIntegerHom M
  map_zero' := torusIntegerHom_zero M
  map_add' := torusIntegerHom_add M

omit [Fintype d] in
@[simp] theorem torusIntegerAddHom_apply (M : d → k → ℤ) (x : UnitAddTorus k) :
    torusIntegerAddHom M x = torusIntegerHom M x := rfl

/-- **The orbit closure through a rationally independent presentation.**  If the frequencies are
integer combinations of a rationally independent family, the closure of their phase orbit is the
range of the corresponding integer homomorphism of tori. -/
theorem closure_range_finiteClockPhasePoint_eq (omega : d → ℝ) (gamma : k → ℝ) (M : d → k → ℤ)
    (hgamma : RationallyIndependentFrequency gamma)
    (hM : ∀ i, omega i = ∑ j, (M i j : ℝ) * gamma j) :
    closure (Set.range (finiteClockPhasePoint omega)) = Set.range (torusIntegerHom M) := by
  have hfactor : Set.range (finiteClockPhasePoint omega)
      = torusIntegerHom M '' Set.range (finiteClockPhasePoint gamma) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨finiteClockPhasePoint gamma t, ⟨t, rfl⟩,
        (finiteClockPhasePoint_eq_torusIntegerHom omega gamma M hM t).symm⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, finiteClockPhasePoint_eq_torusIntegerHom omega gamma M hM t⟩
  have hdense := dense_range_finiteClockPhasePoint gamma hgamma
  have himage : IsCompact (torusIntegerHom M '' (Set.univ : Set (UnitAddTorus k))) :=
    isCompact_univ.image (continuous_torusIntegerHom M)
  have hclosed : IsClosed (Set.range (torusIntegerHom M)) := by
    rw [← Set.image_univ]
    exact himage.isClosed
  refine le_antisymm ?_ ?_
  · rw [hfactor]
    refine closure_minimal ?_ hclosed
    rintro _ ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  · rintro _ ⟨y, rfl⟩
    have hy : y ∈ closure (Set.range (finiteClockPhasePoint gamma)) := hdense y
    have := image_closure_subset_closure_image (f := torusIntegerHom M)
      (continuous_torusIntegerHom M) (s := Set.range (finiteClockPhasePoint gamma))
      ⟨y, hy, rfl⟩
    rw [← hfactor] at this
    exact this

/-- **Completed observer time is a torus.**  The closure of the phase orbit of a finite frequency
packet is the range of an injective integer homomorphism from a torus whose dimension is the
rational rank of the packet. -/
theorem exists_orbitClosure_eq_range_torusIntegerHom (omega : d → ℝ) :
    ∃ (k : ℕ) (M : d → Fin k → ℤ),
      closure (Set.range (finiteClockPhasePoint omega)) = Set.range (torusIntegerHom M) ∧
        Function.Injective (torusIntegerHom M) ∧
        k = Module.finrank ℚ (Submodule.span ℚ (Set.range omega)) := by
  obtain ⟨k, gamma, M, A, hindep, -, -, hM, hA, hrank⟩ := exists_frequency_integer_basis omega
  exact ⟨k, M, closure_range_finiteClockPhasePoint_eq omega gamma M hindep hM,
    torusIntegerHom_injective M A hA, hrank⟩

end

end GaloisForLFunctions.HTGeometry
