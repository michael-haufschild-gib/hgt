import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.PhysicalOrbit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.FrozenClearance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Fine-error gate cost at coarse physical contact dates -/

open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits
open AccuracyScales.MaximumIntervals PrecisionReturns
noncomputable section

/-- Largest integer budget satisfying the strict sixteen-parameters bound. -/
def fineBudget (k : ℕ) := (2^(k+3)-2)/16

private theorem fineBudget_lt (k : ℕ) : 16*fineBudget k < 2^(k+3)-1 := by
  have h := Nat.div_mul_le_self (2^(k+3)-2) 16
  rw [Nat.mul_comm] at h
  have hp : 2 ≤ 2^(k+3) := (show 2^1 ≤ 2^(k+3) from
    Nat.pow_le_pow_right (by decide) (by omega))
  dsimp only [fineBudget]; omega

/-- Errors attained by a budget at an exact short-circuit date. -/
def contactValues (ω : PathPauliDisorder) : Set ℝ :=
  ⋃ (k : ℕ) (s : ℕ) (n : ℕ), orbitCircuitDistance (chainGenerator ω k) s ''
    {t ∈ Icc (-(n:ℝ)) (n:ℝ) | HasProjectiveCircuitApproximation (k+3) 0 (fineBudget k)
      (unitaryEvolution (chainGenerator ω k).val t)}

/-- Away from a countable set of coarse errors, every near-contact on
a compact time interval has a positive, uniform fine-error gate floor.
The fine accuracy may depend on the interval, the prefix and the
coarse budget. -/
theorem gaussian_coarse_contact_precision :
    ∀ᵐ ω ∂pathPauliDisorderLaw, (contactValues ω).Countable ∧
      ∀ e ∉ contactValues ω, ∀ (k s : ℕ) (a b : ℝ), ∃ δ > (0:ℝ), ∀ t ∈ Icc a b,
        let H := chainGenerator ω k
        |orbitCircuitDistance H s t-e| ≤ δ → δ < orbitCircuitDistance H (fineBudget k) t := by
  filter_upwards [gaussian_finite_exact_circuit_dates] with ω hω
  refine ⟨countable_iUnion fun k : ℕ => countable_iUnion fun s : ℕ => countable_iUnion fun n : ℕ =>
    ((hω k (fineBudget k) (fineBudget_lt k) (-(n:ℝ)) (n:ℝ)).image _).countable,?_⟩
  intro e he k s a b
  let H := chainGenerator ω k
  let d := orbitCircuitDistance H
  let f (t : ℝ) := |d s t-e|+d (fineBudget k) t
  have hpos (t : ℝ) : 0 < f t := by
    have hd : 0 ≤ d (fineBudget k) t := Metric.infDist_nonneg
    by_contra! h
    change |d s t-e|+d (fineBudget k) t ≤ 0 at h
    have h₁ : d s t=e := sub_eq_zero.mp (abs_eq_zero.mp (by
      linarith only [h,hd,abs_nonneg (d s t-e)]))
    have h₂ : d (fineBudget k) t ≤ 0 := by linarith only [h,abs_nonneg (d s t-e)]
    obtain ⟨n,hn⟩ := exists_nat_gt |t|
    apply he
    exact mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨n,t,
      ⟨abs_le.mp hn.le,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr h₂⟩,h₁⟩⟩⟩
  by_cases hab : a ≤ b
  · have hf : Continuous f := ((orbitCircuitDistance_lipschitz H s).continuous.sub continuous_const).abs.add
      (orbitCircuitDistance_lipschitz H (fineBudget k)).continuous
    obtain ⟨w,hw,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hf.continuousOn
    refine ⟨f w/3,div_pos (hpos w) (by norm_num),?_⟩
    intro t ht H' hfit
    have hh := isMinOn_iff.mp hmin t ht
    change f w ≤ |d s t-e|+d (fineBudget k) t at hh
    change |d s t-e| ≤ f w/3 at hfit
    change f w/3 < d (fineBudget k) t
    linarith only [hh,hfit,hpos w]
  · exact ⟨1,zero_lt_one,fun t ht => (hab (ht.1.trans ht.2)).elim⟩

/-- A genuine first visit from outside attains the selected error exactly. -/
theorem firstVisit_distance {N : ℕ} (H : selfAdjoint (DiagonalSynthesis.Register N))
    (a : ℝ) (s : ℕ) {e : ℝ} (he : 0 < e) (hout : e < orbitCircuitDistance H s a) :
    orbitCircuitDistance H s (firstVisit H a s e)=e := by
  let v := firstVisit H a s e
  obtain ⟨⟨hv,hfit⟩,hfirst⟩ := firstVisit_isLeast H a s he
  have hend : orbitCircuitDistance H s v ≤ e := (hasProjectiveCircuitApproximation_iff_infDist ..).mp hfit
  obtain ⟨u,hu,hu'⟩ := intermediate_value_Icc' hv
    (orbitCircuitDistance_lipschitz H s).continuous.continuousOn (show e ∈ Icc _ _ from ⟨hend,hout.le⟩)
  have hwu : v ≤ u := hfirst ⟨hu.1,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr hu'.le⟩
  exact (congrArg (orbitCircuitDistance H s) (le_antisymm hwu hu.2)).trans hu'

/-- At each genuine first return away from the exceptional coarse errors,
some finer positive accuracy requires more than (2ᴺ−2)/16 gates. The
observation origin can itself depend on the error, budget and draw. -/
theorem gaussian_first_visit_fine_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∃ E : Set ℝ, E.Countable ∧ ∀ e > (0:ℝ), e ∉ E →
      ∀ (k s : ℕ) (a : ℝ), let H := chainGenerator ω k
        e < orbitCircuitDistance H s a → let v := firstVisit H a s e
          ∃ δ > (0:ℝ), ∀ F : TwoQubitCircuit (k+3), ∀ z : ℂ, ‖z‖=1 →
            ‖unitaryEvolution H.val v-z • (F.eval : DiagonalSynthesis.Register (k+3))‖ ≤ δ →
              fineBudget k < F.gateCount := by
  filter_upwards [gaussian_coarse_contact_precision] with ω h
  refine ⟨contactValues ω,h.1,?_⟩
  intro e he hr k s a H hout v
  obtain ⟨δ,hδ,hbound⟩ := h.2 e hr k s v v
  have hz : |orbitCircuitDistance H s v-e| ≤ δ := by
    rw [firstVisit_distance H a s he hout,sub_self,abs_zero]; exact hδ.le
  have hw := hbound v ⟨le_rfl,le_rfl⟩ hz
  refine ⟨δ,hδ,?_⟩
  intro F z hz he
  by_contra! hf
  exact hw.not_ge ((hasProjectiveCircuitApproximation_iff_infDist ..).mp ⟨z,hz,F,hf,he⟩)

#print axioms gaussian_coarse_contact_precision
#print axioms gaussian_first_visit_fine_floor
end
end GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits
