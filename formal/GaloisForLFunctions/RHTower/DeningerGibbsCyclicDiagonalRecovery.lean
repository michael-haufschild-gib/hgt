import GaloisForLFunctions.RHTower.DeningerOrdinaryIntegerGibbsOperatorDomain
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Data.PNat.Prime
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Recovery of the cyclic Gibbs diagonal

Divisibility-set sums determine every summable complex family on positive integers.
Applied to the actual ordinary-integer Gibbs domain and its fixed physical exchange
law, this classifies all-integer Wold pair cyclicity by unit-supported diagonal.
No summable diagonal correction of the reciprocal Green operator can satisfy it.

These are source-domain and reconstruction results. They do not construct the
missing cyclic-to-physical source comparison or prove the Riemann hypothesis.
-/

open Set MeasureTheory MeasurableSpace
namespace RHTower
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Divisibility sets separate every positive integer. -/
theorem pnatDivisibility_generateFrom_eq_top :
    MeasurableSpace.generateFrom (Set.range (fun n : PNat => {k : PNat | n ∣ k})) = ⊤ := by
  apply top_unique
  intro s _hs
  letI : MeasurableSpace PNat :=
    MeasurableSpace.generateFrom (Set.range (fun n : PNat => {k : PNat | n ∣ k}))
  have hD (n : PNat) : MeasurableSet {k : PNat | n ∣ k} :=
    measurableSet_generateFrom ⟨n, rfl⟩
  have hsingle (k : PNat) : MeasurableSet ({k} : Set PNat) := by
    have hi : MeasurableSet (⋂ n : PNat,
        if n ∣ k then {j : PNat | n ∣ j} else {j : PNat | n ∣ j}ᶜ) := by
      apply MeasurableSet.iInter
      intro n
      split_ifs
      · exact hD n
      · exact (hD n).compl
    convert hi using 1
    ext j
    simp only [Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    · intro heq n
      rw [heq]
      by_cases h : n ∣ k <;> simp [h]
    · intro hj
      have hkj : k ∣ j := by simpa using hj k
      have hjk : j ∣ k := by
        by_contra h
        simpa [h] using hj j
      exact PNat.dvd_antisymm hjk hkj
  letI : MeasurableSingletonClass PNat := ⟨hsingle⟩
  exact (Set.to_countable s).measurableSet

theorem pnatDivisibility_isPiSystem :
    IsPiSystem (Set.range (fun n : PNat => {k : PNat | n ∣ k})) := by
  rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ _
  refine ⟨PNat.lcm n m, ?_⟩
  ext k
  exact ⟨fun h => ⟨dvd_trans (PNat.dvd_lcm_left n m) h,
      dvd_trans (PNat.dvd_lcm_right n m) h⟩,
    fun h => PNat.lcm_dvd h.1 h.2⟩

local instance : MeasurableSpace PNat := ⊤

/-- Countable additivity makes all divisibility evaluations jointly faithful. -/
theorem pnatDivisibility_vectorMeasure_eq_zero
    (v : VectorMeasure PNat ℂ) (h : ∀ n : PNat, v {k : PNat | n ∣ k} = 0) : v = 0 := by
  have hv : v Set.univ = 0 := by simpa using h 1
  apply VectorMeasure.ext
  intro t ht
  change v t = 0
  refine MeasurableSpace.induction_on_inter
    (C := fun t _ => v t = 0)
    pnatDivisibility_generateFrom_eq_top.symm pnatDivisibility_isPiSystem
    (VectorMeasure.empty v) ?_ ?_ ?_ t ht
  · rintro _ ⟨n, rfl⟩
    exact h n
  · intro t ht htz
    rw [VectorMeasure.of_compl ht, hv, htz, sub_self]
  · intro f hd hf hz
    rw [VectorMeasure.of_disjoint_iUnion hf hd]
    simp only [hz, tsum_zero]

/-- A summable diagonal family is zero if all of its multiples sums are zero. -/
theorem pnatDivisibility_summable_eq_zero
    (f : PNat → ℂ) (hf : Summable f)
    (h : ∀ n : PNat, (∑' k : PNat, if n ∣ k then f k else 0) = 0) :
    f = 0 := by
  have hi : Integrable f Measure.count := integrable_count_iff.mpr hf.norm
  let v : VectorMeasure PNat ℂ := Measure.count.withDensityᵥ f
  have heval (s : Set PNat) : v s = ∑' k : PNat, s.indicator f k := by
    rw [show v s = (Measure.count.withDensityᵥ f) s from rfl,
      withDensityᵥ_apply hi (by trivial), ← integral_indicator (by trivial),
      integral_countable (hi.indicator (by trivial))]
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  have hv : v = 0 := pnatDivisibility_vectorMeasure_eq_zero v (fun n => by
    rw [heval]
    simpa only [Set.indicator_apply, Set.mem_setOf_eq] using h n)
  funext k
  have hk := congrArg (fun w : VectorMeasure PNat ℂ => w {k}) hv
  rw [show v {k} = (Measure.count.withDensityᵥ f) {k} from rfl,
    withDensityᵥ_apply hi (by trivial), integral_singleton] at hk
  simpa [measureReal_def] using hk

/-- Every coefficient of a summable complex family is determined by its divisibility sums. -/
theorem pnatDivisibility_summable_injective
    (f g : PNat → ℂ) (hf : Summable f) (hg : Summable g)
    (h : ∀ n : PNat, (∑' k : PNat, if n ∣ k then f k else 0) =
      ∑' k : PNat, if n ∣ k then g k else 0) : f = g := by
  have hz : f - g = 0 := pnatDivisibility_summable_eq_zero (f - g) (hf.sub hg) (fun n => by
    have hs := (hf.indicator {k : PNat | n ∣ k}).tsum_sub
      (hg.indicator {k : PNat | n ∣ k})
    have heq : (fun k : PNat => if n ∣ k then (f - g) k else 0) =
        (fun k : PNat => ({k : PNat | n ∣ k}.indicator f) k -
          ({k : PNat | n ∣ k}.indicator g) k) := by
      funext k
      by_cases hn : n ∣ k <;> simp [hn]
    rw [heq, hs]
    exact sub_eq_zero.mpr (by simpa only [Set.indicator_apply, Set.mem_setOf_eq] using h n))
  exact sub_eq_zero.mp hz

/-- Vanishing of the nontrivial divisibility sums leaves exactly the unit coefficient. -/
theorem pnatDivisibility_summable_supported_unit
    (f : PNat → ℂ) (hf : Summable f)
    (h : ∀ n : PNat, n ≠ 1 → (∑' k : PNat, if n ∣ k then f k else 0) = 0) :
    ∀ k : PNat, k ≠ 1 → f k = 0 := by
  let c := ∑' k : PNat, f k
  let g : PNat → ℂ := fun k => if k = 1 then c else 0
  have hg : Summable g := (hasSum_ite_eq (1 : PNat) c).summable
  have heq : f = g := pnatDivisibility_summable_injective f g hf hg (fun n => by
    by_cases hn : n = 1
    · subst n
      simpa only [one_dvd, if_true] using (hasSum_ite_eq (1 : PNat) c).tsum_eq.symm
    · rw [h n hn]
      symm
      refine (tsum_congr (g := fun _ : PNat => (0 : ℂ)) ?_).trans tsum_zero
      intro k
      by_cases hk : k = 1
      · subst k
        have hd : ¬ n ∣ 1 := fun hdiv => hn (PNat.dvd_antisymm hdiv (one_dvd n))
        simp [hd]
      · simp [g, hk])
  intro k hk
  rw [heq]
  simp [g, hk]

/-- The actual all-integer Wold pair-cyclicity test for the fixed Gibbs reader. -/
def DeningerOrdinaryIntegerGibbsPairCyclic
    (sigma : ℝ) (h : 1 / 2 < sigma) (T : deningerOrdinaryIntegerGibbsDomain sigma) : Prop :=
  ∀ n : PNat, n ≠ 1 →
    deningerOrdinaryIntegerGibbsReader sigma h
      ⟨deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n),
        deningerOrdinaryIntegerGibbsDomain_compression T n⟩ =
      deningerOrdinaryIntegerGibbsReader sigma h
        ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
          deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩

theorem deningerOrdinaryIntegerGibbsTrace_projection_eq_multiples
    {sigma : ℝ} (T : deningerOrdinaryIntegerGibbsDomain sigma) (n : PNat) :
    deningerOrdinaryIntegerGibbsTrace sigma
      ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ =
      ∑' k : PNat, if n ∣ k then deningerOrdinaryIntegerGibbsDiagonal sigma k T.val else 0 := by
  change (∑' k : PNat, deningerOrdinaryIntegerGibbsDiagonal sigma k
    (T.val * deningerOrdinaryIntegerDivisibilityProjection n)) = _
  simp only [deningerOrdinaryIntegerGibbsDiagonal_rightProjection]

theorem deningerOrdinaryIntegerGibbsReader_projection_zero_iff
    {sigma : ℝ} (h : 1 / 2 < sigma) (T : deningerOrdinaryIntegerGibbsDomain sigma) (n : PNat) :
    deningerOrdinaryIntegerGibbsReader sigma h
      ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ = 0 ↔
      (∑' k : PNat, if n ∣ k then deningerOrdinaryIntegerGibbsDiagonal sigma k T.val else 0) = 0 := by
  have hZ : (deningerOrdinaryIntegerGibbsPartition sigma : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (deningerOrdinaryIntegerGibbsPartition_pos h).ne'
  rw [deningerOrdinaryIntegerGibbsReader, LinearMap.smul_apply, smul_eq_mul,
    deningerOrdinaryIntegerGibbsTrace_projection_eq_multiples T n,
    mul_eq_zero]
  simp [hZ]

theorem deningerOrdinaryIntegerGibbsGain_ne_one
    {sigma : ℝ} (h : 1 / 2 < sigma) (n : PNat) (hn : n ≠ 1) :
    (deningerHalfDensityMateGain n (sigma : ℂ) : ℂ) ≠ 1 := by
  intro hgain
  have hg : deningerHalfDensityMateGain n (sigma : ℂ) = 1 :=
    Complex.ofReal_injective (by simpa using hgain)
  have hn2 : 2 ≤ (n : ℕ) := by
    have hp := n.pos
    have hn1 : (n : ℕ) ≠ 1 := fun hc => hn (Subtype.ext hc)
    omega
  have hz : deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation n (sigma : ℂ) = 0 := by
    simp [deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation, hg]
  have hw := (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation_eq_zero_iff hn2
    (sigma : ℂ)).1 hz
  simp only [Complex.ofReal_re] at hw
  linarith

/-- Exact survivor of all-integer cyclicity: only the unit diagonal remains readable. -/
theorem deningerOrdinaryIntegerGibbsPairCyclic_iff_unit_diagonal
    {sigma : ℝ} (h : 1 / 2 < sigma) (T : deningerOrdinaryIntegerGibbsDomain sigma) :
    DeningerOrdinaryIntegerGibbsPairCyclic sigma h T ↔
      ∀ k : PNat, k ≠ 1 → deningerOrdinaryIntegerDiagonalCoefficient k T.val = 0 := by
  constructor
  · intro hc
    have hsum (n : PNat) (hn : n ≠ 1) :
        (∑' k : PNat, if n ∣ k then deningerOrdinaryIntegerGibbsDiagonal sigma k T.val else 0) = 0 := by
      apply (deningerOrdinaryIntegerGibbsReader_projection_zero_iff h T n).1
      have hx := (deningerOrdinaryIntegerGibbsReader_physicalExchange (sigma : ℂ) h T n).symm.trans
        (hc n hn)
      have hz : ((deningerHalfDensityMateGain n (sigma : ℂ) : ℂ) - 1) *
          deningerOrdinaryIntegerGibbsReader sigma h
            ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
              deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ = 0 := by
        linear_combination hx
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (deningerOrdinaryIntegerGibbsGain_ne_one h n hn))
    have hu := pnatDivisibility_summable_supported_unit
      (fun k => deningerOrdinaryIntegerGibbsDiagonal sigma k T.val) T.property hsum
    intro k hk
    have hz := hu k hk
    have hm : (deningerOrdinaryIntegerGibbsMass sigma k : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (deningerOrdinaryIntegerGibbsMass_pos sigma k).ne'
    have hkc : ((k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
    change ((deningerOrdinaryIntegerGibbsMass sigma k : ℂ) * ((k : ℕ) : ℂ)) *
      deningerOrdinaryIntegerDiagonalCoefficient k T.val = 0 at hz
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hm hkc)
  · intro hu n hn
    have hr : deningerOrdinaryIntegerGibbsReader sigma h
        ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
          deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ = 0 := by
      apply (deningerOrdinaryIntegerGibbsReader_projection_zero_iff h T n).2
      refine (tsum_congr (g := fun _ : PNat => (0 : ℂ)) ?_).trans tsum_zero
      intro k
      by_cases hnk : n ∣ k
      · have hk : k ≠ 1 := by
          intro heq
          exact hn (PNat.dvd_antisymm (heq ▸ hnk) (one_dvd n))
        simp [hnk, deningerOrdinaryIntegerGibbsDiagonal, hu k hk]
      · simp [hnk]
    have he : deningerOrdinaryIntegerGibbsReader sigma h
        ⟨deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n),
          deningerOrdinaryIntegerGibbsDomain_compression T n⟩ =
        (deningerHalfDensityMateGain n (sigma : ℂ) : ℂ) *
          deningerOrdinaryIntegerGibbsReader sigma h
            ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
              deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ :=
      deningerOrdinaryIntegerGibbsReader_physicalExchange (sigma : ℂ) h T n
    rw [he, hr, mul_zero]

/-- Cyclic admitted operators have summable diagonals: their diagonal is supported at one. -/
theorem deningerOrdinaryIntegerGibbsPairCyclic_summable_diagonal
    {sigma : ℝ} (h : 1 / 2 < sigma) (T : deningerOrdinaryIntegerGibbsDomain sigma)
    (hc : DeningerOrdinaryIntegerGibbsPairCyclic sigma h T) :
    Summable (fun k => deningerOrdinaryIntegerDiagonalCoefficient k T.val) := by
  have hu := (deningerOrdinaryIntegerGibbsPairCyclic_iff_unit_diagonal h T).1 hc
  have heq : (fun k => deningerOrdinaryIntegerDiagonalCoefficient k T.val) =
      (fun k : PNat => if k = 1 then deningerOrdinaryIntegerDiagonalCoefficient 1 T.val else 0) := by
    funext k
    by_cases hk : k = 1
    · simp [hk]
    · simp [hk, hu k hk]
  rw [heq]
  exact (hasSum_ite_eq (1 : PNat) _).summable

/-- No summable diagonal correction to the actual reciprocal Green source can make all
integer Wold boundaries cyclic for the fixed reader in its convergence chamber. -/
theorem deningerOrdinaryIntegerGibbs_no_summable_cyclic_green_repair
    (sigma : ℝ) (h : 1 / 2 < sigma) :
    ¬ ∃ T : deningerOrdinaryIntegerGibbsDomain sigma,
      Summable (fun k => deningerOrdinaryIntegerDiagonalCoefficient k
        (T.val - deningerOrdinaryIntegerReciprocalGreen)) ∧
      DeningerOrdinaryIntegerGibbsPairCyclic sigma h T := by
  rintro ⟨T, hR, hc⟩
  have hT := deningerOrdinaryIntegerGibbsPairCyclic_summable_diagonal h T hc
  have hQ : Summable (fun k : PNat => (((k : ℕ) : ℂ))⁻¹) := by
    refine (hT.sub hR).congr fun k => ?_
    rw [(deningerOrdinaryIntegerDiagonalCoefficient k).map_sub
      T.val deningerOrdinaryIntegerReciprocalGreen,
      deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen]
    ring
  have hmass : Summable (fun k : PNat => (deningerOrdinaryIntegerGibbsMass (1 / 2) k : ℂ)) := by
    refine hQ.congr fun k => ?_
    norm_num [deningerOrdinaryIntegerGibbsMass, Real.rpow_neg_one]
  have hbad := (summable_deningerOrdinaryIntegerGibbsMass_iff (1 / 2)).1
    (Complex.summable_ofReal.mp hmass)
  exact (lt_irrefl (1 / 2 : ℝ)) hbad

end
end RHTower
