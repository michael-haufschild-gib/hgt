import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HaarWindows.Averaging
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.HalfArc
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.ArcPowers
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateFullOccupation

/-! # Explicit scalar occupation in every initial interval of a static evolution -/

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
open SharpOccupation
open PrecisionReturns (firstVisit firstVisit_isLeast)
noncomputable section

/-- Subtract lifts in two enclosing arcs. The minimum lift of the difference
is a valid left endpoint for an arc with the sum of their widths. -/
theorem enclosing_sub {I : Type*} [Fintype I] {x y : I → UnitAddCircle} {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hx : x ∈ enclosingUnitArc r) (hy : y ∈ enclosingUnitArc s) :
    x-y ∈ enclosingUnitArc (r+s) := by
  classical
  obtain ⟨a,ha⟩ := HarmonicRuns.exists_anchor_lifts hr hx
  obtain ⟨b,hb⟩ := HarmonicRuns.exists_anchor_lifts hs hy
  choose u hu he using ha
  choose v hv hf using hb
  obtain ⟨i,_,hmin⟩ := Finset.univ.exists_min_image (fun i => u i-v i) ⟨a,Finset.mem_univ _⟩
  refine mem_iUnion.mpr ⟨i,fun j _ => ⟨(u j-v j)-(u i-v i),⟨sub_nonneg.mpr (hmin j (Finset.mem_univ _)),?_⟩,?_⟩⟩
  · linarith only [(hu j).2,(hv j).1,(hu i).1,(hv i).2]
  · simp only [AddCircle.coe_sub,he,hf,Pi.sub_apply]
    abel

theorem relative_enclosing_sub {I : Type*} [Fintype I] (i : I) {x y : {j : I // j ≠ i} → UnitAddCircle}
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hx : x ∈ relativeEnclosingUnitArc i r) (hy : y ∈ relativeEnclosingUnitArc i s) :
    x-y ∈ relativeEnclosingUnitArc i (r+s) := by
  classical
  have hh : relativeUnitPhasePacket i (x-y) = relativeUnitPhasePacket i x - relativeUnitPhasePacket i y := by
    funext j
    by_cases hj : j=i <;> simp [relativeUnitPhasePacket,hj]
  change relativeUnitPhasePacket i (x-y) ∈ enclosingUnitArc (r+s)
  rw [hh]
  exact enclosing_sub hr hs hx hy

/-- Subtracting two dates in a translated half-width scalar target
gives a physical empty-circuit fit at the full tolerance. -/
theorem shifted_scalar_difference {N : ℕ} (H : selfAdjoint (Register N)) (i : Fin N → Bool)
    {e : ℝ} (he : e ∈ Ioo (0:ℝ) 2) :
    let f := projectiveFrequency (fun j => -H.2.isHermitian.eigenvalues j) i
    let φ := finiteClockPhasePoint f
    let r := physicalArc e/2
    ∀ y t u, φ t+y ∈ relativeEnclosingUnitArc i r → φ u+y ∈ relativeEnclosingUnitArc i r →
      t-u ∈ visitSet H 0 e := by
  intro f φ r
  let x := physicalArc e
  obtain ⟨hx,htol⟩ := FiniteRecords.physicalArc_full he
  let w : Icc (0:ℝ) 1 := ⟨x,hx.1.le,hx.2.le⟩
  have hB : visitSet H 0 e = zeroGateReturnSet H w := by
    ext t
    change HasProjectiveCircuitApproximation N e 0 _ ↔ orbitCircuitDistance H 0 t ≤ zeroGateArcTolerance x
    rw [htol]
    exact hasProjectiveCircuitApproximation_iff_infDist ..
  intro y t u ht hu
  rw [hB,zeroGateReturnSet_eq_preimage_full H i w]
  have hv := relative_enclosing_sub i (half_pos hx.1).le (half_pos hx.1).le ht hu
  rw [add_sub_add_right_eq_sub] at hv
  have hsub : φ (t-u) = φ t-φ u := by
    apply eq_sub_iff_add_eq.mpr
    change finiteClockPhasePoint f (t-u)+finiteClockPhasePoint f u=finiteClockPhasePoint f t
    rw [←finiteClockPhasePoint_add,sub_add_cancel]
  change φ (t-u) ∈ relativeEnclosingUnitArc i x
  rwa [hsub,show x=r+r by dsimp only [r,x]; ring]

/-- Even a resonant or degenerate spectrum spends at least
`D (x/2)^(D−1) T` scalar-affordable time before every nonnegative date `T`.
Here `x` is the physical error expressed in turns of an enclosing arc. -/
theorem scalar_floor {N : ℕ} (H : selfAdjoint (Register N)) {e : ℝ} (he : e ∈ Ioo (0:ℝ) 2)
    (T : ℝ) (hT : 0 ≤ T) :
    zeroGateArcDensity (2^N) (physicalArc e/2)*T ≤ volume.real (visitSet H 0 e ∩ Icc 0 T) := by
  classical
  let i : Fin N → Bool := fun _ => false
  let f := projectiveFrequency (fun j => -H.2.isHermitian.eigenvalues j) i
  let φ := finiteClockPhasePoint f
  let x := physicalArc e
  have hx := (FiniteRecords.physicalArc_full he).1
  let r : Icc (0:ℝ) (1/2) := ⟨x/2,(half_pos hx.1).le,by linarith only [hx.2]⟩
  have hl := translated_window_floor φ (finiteClockPhasePoint_continuous f) _
    (isClosed_relativeEnclosingUnitArc i r) _ (closed_visits H 0 e).measurableSet (shifted_scalar_difference H i he) T hT
  have hmass := relativeUnitArcMass_eq_power i r
  rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hmass
  change relativeUnitArcMass i r * T ≤ _ at hl
  rwa [hmass] at hl

/-- The first return for any budget is bounded by the scalar time already
observed before its origin, uniformly over all finite Hamiltonians. -/
theorem static_scalar_deadline {N : ℕ} (H : selfAdjoint (Register N)) {e : ℝ} (he : e ∈ Ioo (0:ℝ) 2)
    (s : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    zeroGateArcDensity (2^N) (physicalArc e/2)*firstVisit H a s e ≤ volume.real (visitSet H 0 e ∩ Icc 0 a) := by
  have h0 := firstVisit_isLeast H a 0 he.1
  obtain ⟨c,hc,C,hC,hfit⟩ := h0.1.2
  have hle := (firstVisit_isLeast H a s he.1).2 ⟨h0.1.1,c,hc,C,hC.trans (Nat.zero_le s),hfit⟩
  have h := scalar_floor H he _ (ha.trans h0.1.1)
  rw [first_visit_mass H 0 he.1] at h
  have hx := (FiniteRecords.physicalArc_full he).1.1
  exact (mul_le_mul_of_nonneg_left hle
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (half_pos hx).le _))).trans h

#print axioms scalar_floor
#print axioms static_scalar_deadline
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines.HaarWindows
