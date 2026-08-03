import GaloisForLFunctions.HTGeometry.BarnesSourceRepresentative
import GaloisForLFunctions.HTGeometry.BarnesLadderOrderOne
import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.ScaledDigammaTranslateIndependence

/-!
# The order-one Barnes ladder in the meromorphic field

The pointwise order-one ladder identity of the cone product holds off the poles, and both sides are
represented on the punctured neighbourhood of every point: the left by the translated logarithmic
derivative, the right by the logarithmic derivative plus an explicit rational function.  Since a
punctured representative determines the field element, the identity holds in the field:

```text
σ_{ω_j} Ψ - Ψ = (1/ω_j + K) - 1/(z + ω_j),
```

with `K` the constant the ladder produces.  The correction is rational, so the defect of the source
is a simple pole plus a constant — the shape the atomic theorem consumes once the constant is
absorbed by a shift coboundary.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

attribute [local instance] puncturedRepDomain puncturedRepComplexAlgebraAnalytic
  puncturedRepComplexAlgebraMero puncturedRepDifferential

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-! ## Representatives of the constant and of a simple pole -/

theorem hasPuncturedMeromorphicRep_one :
    HasPuncturedMeromorphicRep (1 : meroField (Set.univ : Set ℂ)) (fun _ => 1) := by
  have h := hasPuncturedMeromorphicRep_fraction (a := 1) (b := 1) one_ne_zero
    (f := fun _ : ℂ => (1 : ℂ)) (g := fun _ : ℂ => (1 : ℂ))
    analyticOnNhd_const analyticOnNhd_const rfl rfl
  simpa using h

theorem hasPuncturedMeromorphicRep_const (c : ℂ) :
    HasPuncturedMeromorphicRep (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) (fun _ => c) := by
  have h := hasPuncturedMeromorphicRep_one.const_mul c
  rw [mul_one] at h
  exact h.congr_fun fun _ => Filter.Eventually.of_forall fun _ => by rw [mul_one]

theorem hasPuncturedMeromorphicRep_one_div_X_add_C (b : ℂ) :
    HasPuncturedMeromorphicRep
      (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
        Set.infinite_univ (1 / (RatFunc.X + RatFunc.C b)))
      (fun z => 1 / (z + b)) := by
  have hpoly : (RatFunc.X + RatFunc.C b : RatFunc ℂ)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X + Polynomial.C b) := by
    rw [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hone : (1 : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) 1 := by rw [map_one]
  have hden : polyToAnalytic (Set.univ : Set ℂ) (Polynomial.X + Polynomial.C b) ≠ 0 := by
    intro hcon
    exact Polynomial.X_add_C_ne_zero b
      (polyToAnalytic_injective Set.univ Set.infinite_univ (hcon.trans (map_zero _).symm))
  have hval : ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
        Set.infinite_univ (1 / (RatFunc.X + RatFunc.C b))
      = algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ 1) /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (polyToAnalytic Set.univ (Polynomial.X + Polynomial.C b)) := by
    rw [hone, hpoly, map_div₀, ratfuncToMero_algebraMap_polynomial,
      ratfuncToMero_algebraMap_polynomial]
    rfl
  rw [hval]
  refine (hasPuncturedMeromorphicRep_fraction hden (analyticOnNhd_polyEval _ 1)
    (analyticOnNhd_polyEval _ (Polynomial.X + Polynomial.C b)) rfl rfl).congr_fun ?_
  intro z
  refine Filter.Eventually.of_forall fun w => ?_
  simp only [Polynomial.eval_one, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-! ## The cone period of a single step -/

omit [Nonempty ι] in
theorem conePeriod_piSingle [DecidableEq ι] (ω : ι → ℂ) (j : ι) :
    conePeriod ω (Pi.single j 1) = ω j := by
  classical
  rw [conePeriod, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, Nat.cast_one, one_mul]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, Nat.cast_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

omit [Fintype ι] [Nonempty ι] in
theorem piSingle_ne_zero [DecidableEq ι] (j : ι) : (Pi.single j 1 : ι → ℕ) ≠ 0 := by
  intro hcon
  have := congrFun hcon j
  rw [Pi.single_eq_same] at this
  exact one_ne_zero this

/-! ## The ladder constant and the field identity -/

/-- The constant produced by the order-one ladder. -/
def barnesLadderConstOne [DecidableEq ι] (ω : ι → ℂ) (j : ι) : ℂ :=
  ∑' n : ι → ℕ, (if n = 0 then 0 else
    (conePeriod ω (n + Pi.single j 1))⁻¹ - (conePeriod ω n)⁻¹)

/-- **The order-one Barnes ladder, in the meromorphic field.**  The translation defect of the
order-one source is a simple pole plus a constant. -/
theorem addTranslationMeroEquiv_barnesSourceLogDerivMero_card_one [DecidableEq ι]
    (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (hcard : Fintype.card ι = 1) (j : ι) :
    addTranslationMeroEquiv (ω j) (barnesSourceLogDerivMero ω hω)
      = barnesSourceLogDerivMero ω hω +
        (algebraMap ℂ (meroField (Set.univ : Set ℂ)) ((ω j)⁻¹ + barnesLadderConstOne ω j) +
          algebraMap ℂ (meroField (Set.univ : Set ℂ)) (-1) *
            ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
              Set.infinite_univ (1 / (RatFunc.X + RatFunc.C (ω j)))) := by
  classical
  have hωj : ω j ≠ 0 := by
    intro hcon
    have := hω j
    rw [hcon] at this
    simp at this
  refine eq_of_hasPuncturedMeromorphicRep
    (hasPuncturedMeromorphicRep_addTranslation_barnesSourceLogDerivMero ω hω (ω j))
    (((hasPuncturedMeromorphicRep_barnesSourceLogDerivMero ω hω).add
      ((hasPuncturedMeromorphicRep_const ((ω j)⁻¹ + barnesLadderConstOne ω j)).add
        ((hasPuncturedMeromorphicRep_one_div_X_add_C (ω j)).const_mul (-1)))).congr_fun ?_)
  intro z₀
  have hshift := (tendsto_nhdsNE_add (ω j) z₀).eventually
    (eventually_nhdsNE_conePeriod_add_ne_zero ω hω (z₀ + ω j))
  filter_upwards [eventually_nhdsNE_conePeriod_add_ne_zero ω hω z₀, hshift] with w hw hw'
  have hladder := barnesSource_shift_sub_card_one ω hω hcard j hw hw'
  have hne : ω j + w ≠ 0 := by
    have := hw (Pi.single j 1) (piSingle_ne_zero j)
    rwa [conePeriod_piSingle] at this
  have hatom : barnesAtom ω (Pi.single j 1) w = -(w / ω j) / (ω j + w) := by
    rw [barnesAtom, if_neg (piSingle_ne_zero j), conePeriod_piSingle, hcard, pow_one]
  simp only [Pi.add_apply]
  rw [barnesLadderConstOne]
  rw [hatom] at hladder
  have hwj : w + ω j ≠ 0 := by
    intro hcon
    exact hne (by linear_combination hcon)
  have halg : (ω j)⁻¹ - 1 / (w + ω j) = -(-(w / ω j) / (ω j + w)) := by
    field_simp
    ring
  linear_combination (-1 : ℂ) * hladder + halg

/-! ## Normalizing the defect -/

theorem ratfuncToMero_ratFuncC (c : ℂ) :
    ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty Set.infinite_univ
      (RatFunc.C c) = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c := by
  have hpc : polyToAnalytic (Set.univ : Set ℂ) (Polynomial.C c) = constToAnalytic Set.univ c := by
    apply Subtype.ext
    have hfun : (fun z : ℂ => (Polynomial.C c).eval z) = fun _ : ℂ => c :=
      funext fun _ => Polynomial.eval_C
    show Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (fun z : ℂ => (Polynomial.C c).eval z)
        = Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) (fun _ : ℂ => c)
    rw [hfun]
  rw [← RatFunc.algebraMap_C, ratfuncToMero_algebraMap_polynomial, polyToMero,
    RingHom.comp_apply, hpc]
  rfl

/-- The order-one source, negated and corrected by a linear term, solves the ladder equation with
defect exactly a simple pole. -/
def barnesLadderSolutionOne [DecidableEq ι] (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (j : ι) :
    meroField (Set.univ : Set ℂ) :=
  -barnesSourceLogDerivMero ω hω +
    ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty Set.infinite_univ
      (RatFunc.C (((ω j)⁻¹ + barnesLadderConstOne ω j) / ω j) * RatFunc.X)

/-- **The order-one ladder in normalized form.**  The defect of the corrected order-one source is
exactly the simple pole `1/(z + ω_j)`. -/
theorem addTranslationMeroEquiv_barnesLadderSolutionOne [DecidableEq ι]
    (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (hcard : Fintype.card ι = 1) (j : ι) :
    addTranslationMeroEquiv (ω j) (barnesLadderSolutionOne ω hω j)
      = barnesLadderSolutionOne ω hω j +
        ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
          Set.infinite_univ (1 / (RatFunc.X + RatFunc.C (ω j))) := by
  classical
  have hωj : ω j ≠ 0 := by
    intro hcon
    have hj := hω j
    rw [hcon] at hj
    simp at hj
  have hshiftpoly : HTGeometry.ratShiftBy (ω j)
        (RatFunc.C (((ω j)⁻¹ + barnesLadderConstOne ω j) / ω j) * RatFunc.X)
      = RatFunc.C (((ω j)⁻¹ + barnesLadderConstOne ω j) / ω j) * RatFunc.X
        + RatFunc.C ((ω j)⁻¹ + barnesLadderConstOne ω j) := by
    rw [map_mul, HTGeometry.ratShiftBy_ratFuncC, HTGeometry.ratShiftBy_ratFuncX, mul_add,
      ← map_mul]
    congr 2
    field_simp
  have hneg : algebraMap ℂ (meroField (Set.univ : Set ℂ)) (-1) = -1 := by
    rw [map_neg, map_one]
  simp only [barnesLadderSolutionOne]
  rw [(addTranslationMeroEquiv (ω j)).map_add, (addTranslationMeroEquiv (ω j)).map_neg,
    addTranslationMeroEquiv_barnesSourceLogDerivMero_card_one ω hω hcard j,
    HTGeometry.addTranslationMeroEquiv_ratfuncToMero_by, hshiftpoly,
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ).map_add, ratfuncToMero_ratFuncC, hneg]
  ring

end

end GaloisForLFunctions
