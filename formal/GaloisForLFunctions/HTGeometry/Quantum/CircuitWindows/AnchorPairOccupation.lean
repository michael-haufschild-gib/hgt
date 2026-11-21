import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AnchorPairGeometry
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyArcPacking
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupationScaling

/-!
# Pair overlaps of covering anchors

Fixing the first anchor as zero, the second phase has a separation window
of length `2r - 1`. Conditional on that phase, all remaining coordinates
independently satisfy an arc constraint of the same length.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance pairOccupationCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

local instance pairOccupationCircleNoAtoms : NullSingletonClass (volume : Measure UnitAddCircle) :=
  ⟨fun x => by rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]; simp⟩

private theorem measurePreserving_splitPhaseCoordinate {J : Type*} [Fintype J] [DecidableEq J] (j : J) :
    MeasurePreserving (fun x : J → UnitAddCircle => (x j, fun k : {k : J // k ≠ j} => x k)) volume
      ((volume : Measure UnitAddCircle).prod (volume : Measure ({k : J // k ≠ j} → UnitAddCircle))) := by
  let K := {k : J // k ≠ j}
  let L := {k : J // ¬ k ≠ j}
  letI : Unique L := ⟨⟨⟨j, fun h => h rfl⟩⟩, fun k => Subtype.ext (not_not.mp k.2)⟩
  have hsplit := volume_preserving_piEquivPiSubtypeProd (fun _ : J => UnitAddCircle) (fun k => k ≠ j)
  have hsingle := volume_preserving_piUnique (fun _ : L => UnitAddCircle)
  have hprod := (MeasurePreserving.id (volume : Measure (K → UnitAddCircle))).prod hsingle
  exact Measure.measurePreserving_swap.comp (hprod.comp hsplit)

/-- Conditioning on one coordinate of a Haar packet factors the remaining
arc constraints whenever the slices have constant volume. -/
theorem volume_phaseCoordinateCondition {J : Type*} [Fintype J] [DecidableEq J] (j : J)
    (W : Set UnitAddCircle) (C : Set (UnitAddCircle × UnitAddCircle))
    (hW : MeasurableSet W) (hC : MeasurableSet C) (b : ℝ≥0∞)
    (hvol : ∀ t ∈ W, volume (Prod.mk t ⁻¹' C) = b) :
    volume {x : J → UnitAddCircle | x j ∈ W ∧ ∀ k, k ≠ j → (x j, x k) ∈ C} =
      volume W * b ^ (Fintype.card J - 1) := by
  let K := {k : J // k ≠ j}
  let S : Set (UnitAddCircle × (K → UnitAddCircle)) :=
    Prod.fst ⁻¹' W ∩ ⋂ k : K, (fun p : UnitAddCircle × (K → UnitAddCircle) => (p.1, p.2 k)) ⁻¹' C
  have hS : MeasurableSet S := (measurable_fst hW).inter (MeasurableSet.iInter fun k =>
    (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd)) hC)
  have hpre : (fun x : J → UnitAddCircle => (x j, fun k : K => x k)) ⁻¹' S =
      {x : J → UnitAddCircle | x j ∈ W ∧ ∀ k, k ≠ j → (x j, x k) ∈ C} := by
    ext x
    simp only [S, mem_preimage, mem_inter_iff, mem_iInter, mem_setOf_eq, K, Subtype.forall]
  have hcard : Fintype.card K = Fintype.card J - 1 := by
    dsimp only [K]
    rw [Fintype.card_subtype_compl (fun k => k = j), Fintype.card_subtype_eq]
  have hs (t : UnitAddCircle) : volume (Prod.mk t ⁻¹' S) =
      W.indicator (fun _ => b ^ (Fintype.card J - 1)) t := by
    by_cases ht : t ∈ W
    · have hf : Prod.mk t ⁻¹' S = (univ : Set K).pi (fun _ => Prod.mk t ⁻¹' C) := by
        ext y
        simp only [S, mem_preimage, mem_inter_iff, mem_iInter, ht, true_and, Set.mem_pi, mem_univ, true_implies]
      rw [hf, volume_pi_pi, indicator_of_mem ht]
      simp only [hvol t ht, Finset.prod_const, Finset.card_univ, hcard]
    · have hf : Prod.mk t ⁻¹' S = ∅ := by
        ext y
        simp only [S, mem_preimage, mem_inter_iff, ht, false_and, mem_empty_iff_false]
      rw [hf, measure_empty, indicator_of_notMem ht]
  rw [← hpre, (measurePreserving_splitPhaseCoordinate j).measure_preimage hS.nullMeasurableSet,
    Measure.prod_apply hS]
  simp only [hs]
  rw [lintegral_indicator hW, lintegral_const, Measure.restrict_apply_univ, mul_comm]

section Relative

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The event that `i` anchors an arc for a packet recorded relative to `ref`. -/
abbrev relativeAnchoredUnitArc (ref i : ι) (r : ℝ) : Set ({j : ι // j ≠ ref} → UnitAddCircle) :=
  relativeUnitPhasePacket ref ⁻¹' anchoredUnitArc i r

omit [Fintype ι] [DecidableEq ι] in
theorem isClosed_relativeAnchoredUnitArc (ref i : ι) (r : ℝ) : IsClosed (relativeAnchoredUnitArc ref i r) := by
  apply (isClosed_anchoredUnitArc i r).preimage
  refine continuous_pi fun j => ?_
  by_cases h : j ≠ ref
  · simpa only [relativeUnitPhasePacket, dif_pos h] using
      (continuous_apply (⟨j, h⟩ : {k : ι // k ≠ ref}))
  · simp only [relativeUnitPhasePacket, dif_neg h]
    exact continuous_const

omit [Fintype ι] [DecidableEq ι] in
private theorem preimage_rebase_relativeAnchoredUnitArc (ref base i : ι) (r : ℝ) :
    relativeUnitPhaseRebase ref base ⁻¹' relativeAnchoredUnitArc base i r = relativeAnchoredUnitArc ref i r := by
  ext x
  simp only [relativeAnchoredUnitArc, mem_preimage, anchoredUnitArc, mem_setOf_eq,
    relativeUnitPhasePacket_rebase, sub_sub_sub_cancel_right]

private theorem volume_sameBase_anchorPair {i j : ι} (hji : j ≠ i) (r : Ico (1 / 2 : ℝ) 1) :
    volume (relativeAnchoredUnitArc i i r ∩ relativeAnchoredUnitArc i j r) =
      ENNReal.ofReal (2 * (r : ℝ) - 1) ^ (Fintype.card ι - 1) := by
  let J := {k : ι // k ≠ i}
  let d : J := ⟨j, hji⟩
  let W := unitArcAnchorSeparation r
  let C : Set (UnitAddCircle × UnitAddCircle) := {p | p.2 ∈ commonForwardUnitArc r p.1}
  let A := relativeAnchoredUnitArc i i r ∩ relativeAnchoredUnitArc i j r
  have hW : MeasurableSet W := (isClosed_unitArcAnchorSeparation r).measurableSet
  have hC : MeasurableSet C := by
    change MeasurableSet (Prod.snd ⁻¹' forwardUnitArc r ∩ (fun p : UnitAddCircle × UnitAddCircle =>
      p.2 - p.1) ⁻¹' forwardUnitArc r)
    exact (measurable_snd (isClosed_forwardUnitArc r).measurableSet).inter
      ((measurable_snd.sub measurable_fst) (isClosed_forwardUnitArc r).measurableSet)
  have hsplit : {x : J → UnitAddCircle | x d ∈ W ∧ ∀ k, k ≠ d → (x d, x k) ∈ C} =
      A ∩ {x : J → UnitAddCircle | x d ≠ 0} := by
    ext x
    let y := relativeUnitPhasePacket i x
    have hy0 : y i = 0 := by simp [y, relativeUnitPhasePacket]
    have hy (k : J) : y k = x k := by simp [y, relativeUnitPhasePacket, k.2]
    have hyd : y j = x d := hy d
    change (x d ∈ W ∧ ∀ k, k ≠ d → (x d, x k) ∈ C) ↔
      (y ∈ anchoredUnitArc i r ∧ y ∈ anchoredUnitArc j r) ∧ x d ≠ 0
    constructor
    · rintro ⟨⟨ht, hneg, hne⟩, h⟩
      refine ⟨⟨?_, ?_⟩, hne⟩
      · intro k hki
        by_cases hkj : k = j
        · subst k
          simpa only [hyd, hy0, sub_zero] using ht
        · let l : J := ⟨k, hki⟩
          have hl : l ≠ d := fun he => hkj (congrArg Subtype.val he)
          have hf : x l ∈ forwardUnitArc r := (h l hl).1
          simpa only [hy0, sub_zero, ← hy l] using hf
      · intro k hkj
        by_cases hki : k = i
        · subst k
          simpa only [hyd, hy0, zero_sub] using hneg
        · let l : J := ⟨k, hki⟩
          have hl : l ≠ d := fun he => hkj (congrArg Subtype.val he)
          have hf : x l - x d ∈ forwardUnitArc r := (h l hl).2
          simpa only [← hy l, ← hyd] using hf
    · rintro ⟨⟨hi, hj⟩, hne⟩
      refine ⟨⟨?_, ?_, hne⟩, fun k hk => ?_⟩
      · simpa only [hyd, hy0, sub_zero] using hi j hji
      · simpa only [hyd, hy0, zero_sub] using hj i hji.symm
      · have hk' : (k : ι) ≠ j := fun h => hk (Subtype.ext h)
        exact ⟨by simpa only [hy, hy0, sub_zero] using hi k k.2,
          by simpa only [hy, hyd, mem_preimage] using hj k hk'⟩
  have hne : ∀ᵐ x ∂(volume : Measure (J → UnitAddCircle)), x d ≠ 0 := by
    rw [ae_iff]
    have he : {x : J → UnitAddCircle | ¬ x d ≠ 0} = Function.eval d ⁻¹' ({0} : Set UnitAddCircle) := by
      ext x
      simp only [mem_setOf_eq, not_not, mem_preimage, Function.eval, mem_singleton_iff]
    rw [he]
    change (Measure.pi (fun _ : J => (volume : Measure UnitAddCircle)))
      (Function.eval d ⁻¹' ({0} : Set UnitAddCircle)) = 0
    rw [(measurePreserving_eval (fun _ : J => (volume : Measure UnitAddCircle)) d).measure_preimage
      (measurableSet_singleton (0 : UnitAddCircle)).nullMeasurableSet, measure_singleton]
  have hae : (A ∩ {x : J → UnitAddCircle | x d ≠ 0} : Set (J → UnitAddCircle)) =ᵐ[volume] A := by
    filter_upwards [hne] with x hx
    change (x ∈ A ∩ {z : J → UnitAddCircle | z d ≠ 0}) = (x ∈ A)
    exact propext ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
  have hcard : Fintype.card J = Fintype.card ι - 1 := by
    dsimp only [J]
    rw [Fintype.card_subtype_compl (fun k => k = i), Fintype.card_subtype_eq]
  haveI : Nonempty J := ⟨d⟩
  have hjpos : 1 ≤ Fintype.card J := Fintype.card_pos
  change volume A = _
  rw [← measure_congr hae, ← hsplit,
    volume_phaseCoordinateCondition d W C hW hC _ (fun _ ht => volume_commonForwardUnitArc r ht),
    volume_unitArcAnchorSeparation r, ← pow_succ', Nat.sub_add_cancel hjpos, hcard]

/-- The joint probability of two distinct anchors is `(2r - 1)^(D-1)`. -/
theorem volume_relativeAnchoredUnitArc_inter (ref : ι) {i j : ι} (hji : j ≠ i)
    (r : Ico (1 / 2 : ℝ) 1) : volume (relativeAnchoredUnitArc ref i r ∩ relativeAnchoredUnitArc ref j r) =
      ENNReal.ofReal (2 * (r : ℝ) - 1) ^ (Fintype.card ι - 1) := by
  have he : relativeUnitPhaseRebase ref i ⁻¹'
      (relativeAnchoredUnitArc i i r ∩ relativeAnchoredUnitArc i j r) =
      relativeAnchoredUnitArc ref i r ∩ relativeAnchoredUnitArc ref j r := by
    rw [preimage_inter, preimage_rebase_relativeAnchoredUnitArc, preimage_rebase_relativeAnchoredUnitArc]
  have hm := ((isClosed_relativeAnchoredUnitArc i i r).inter
    (isClosed_relativeAnchoredUnitArc i j r)).measurableSet
  rw [← he, (measurePreserving_relativeUnitPhaseRebase ref i).measure_preimage hm.nullMeasurableSet,
    volume_sameBase_anchorPair hji r]

/-- The anchor count bounds the full return probability from below even at
the critical gap scale, where fixed disjoint trial arcs are too sparse. -/
theorem relativeUnitArcMass_ge_anchorMean (ref : ι) (r : Ico (1 / 2 : ℝ) 1) :
    let q := (Fintype.card ι : ℝ) * (r : ℝ) ^ (Fintype.card ι - 1)
    q / (1 + q) ≤ relativeUnitArcMass ref r := by
  let R : Icc (0 : ℝ) 1 := ⟨r, (by positivity : (0 : ℝ) ≤ 1 / 2).trans r.2.1, r.2.2.le⟩
  let A (i : ι) := relativeAnchoredUnitArc ref i (r : ℝ)
  let p := (r : ℝ) ^ (Fintype.card ι - 1)
  have hav (i : ι) : volume.real (A i) = p := by
    rw [Measure.real, volume_relativeAnchoredUnitArc_full ref i R, ENNReal.toReal_pow, ENNReal.toReal_ofReal R.2.1]
  have hp (i j : ι) (hij : i ≠ j) : volume.real (A i ∩ A j) ≤ p ^ 2 := by
    have hnon : 0 ≤ 2 * (r : ℝ) - 1 := by linarith only [r.2.1]
    rw [Measure.real, volume_relativeAnchoredUnitArc_inter ref hij.symm r, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hnon]
    have hle : 2 * (r : ℝ) - 1 ≤ (r : ℝ) ^ 2 := by nlinarith only [sq_nonneg ((r : ℝ) - 1)]
    have h := pow_le_pow_left₀ hnon hle (Fintype.card ι - 1)
    simpa only [p, ← pow_mul, Nat.mul_comm] using h
  letI : Nonempty ι := ⟨ref⟩
  have hmean : 0 < (Fintype.card ι : ℝ) * p :=
    mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (pow_pos ((by positivity : (0 : ℝ) < 1 / 2).trans_le r.2.1) _)
  have h := measureReal_iUnion_ge_mean_div_one_add_mean A
    (fun i => (isClosed_relativeAnchoredUnitArc ref i r).measurableSet) p hav hp hmean
  simpa only [relativeUnitArcMass, relativeEnclosingUnitArc, enclosingUnitArc, preimage_iUnion, A] using h

end Relative

/-- At least the following fraction of long-time zero-gate returns is supplied
by overlapping anchored windows. -/
theorem zeroGateFullArcMass_ge_anchorMean (n : ℕ) (r : Ico (1 / 2 : ℝ) 1) :
    let q := (2 : ℝ) ^ n * (r : ℝ) ^ (2 ^ n - 1)
    q / (1 + q) ≤ zeroGateFullArcMass n r := by
  simpa only [zeroGateFullArcMass, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] using relativeUnitArcMass_ge_anchorMean (fun _ : Fin n => false) r

#print axioms volume_phaseCoordinateCondition
#print axioms volume_relativeAnchoredUnitArc_inter
#print axioms relativeUnitArcMass_ge_anchorMean
#print axioms zeroGateFullArcMass_ge_anchorMean

end

end GaloisForLFunctions.HTGeometry
