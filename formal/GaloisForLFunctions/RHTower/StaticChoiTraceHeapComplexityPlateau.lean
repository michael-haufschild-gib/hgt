import GaloisForLFunctions.RHTower.GateWordFirstHit
import GaloisForLFunctions.RHTower.LocalCircuitTraceCapacity
import GaloisForLFunctions.RHTower.StaticChoiComplexityPlateau
import GaloisForLFunctions.RHTower.StaticChoiSyndeticComplexityLaw

/-!
# Static Choi plateaux after exact local-commutation quotienting

Disjoint local gates commute.  Hence a circuit dictionary is not the free word tree: exchanging
adjacent independent letters leaves its endpoint unchanged.  This file first proves that gate-word
evaluation descends to the corresponding trace monoid.  It then replaces the free-word multiplier
in the static Choi phase bound by the exact bounded-dependence trace capacity

`choose (|alpha| + ell - 1) ell * 2^(Delta * ell)`.

For a bounded-degree local alphabet and `ell` proportional to the spectral dimension, the binomial
profile is subexponential in that dimension.  Thus the certified completed-time plateau can have
depth proportional to spectral dimension, without the former `log |alpha|` loss.
-/

open Filter MeasureTheory Set Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

section TraceSemantics

variable {α X : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem wordEval_append (act : α → X → X) (u v : List α) (x : X) :
    wordEval act (u ++ v) x = wordEval act u (wordEval act v x) := by
  induction u with
  | nil => rfl
  | cons g u ih => simp [wordEval, ih]

omit [DecidableEq α] in
/-- Repeating an identity letter does not change a word endpoint. -/
@[simp] theorem wordEval_replicate_identity
    (act : α → X → X) (e : α) (he : ∀ x, act e x = x) (m : ℕ) (x : X) :
    wordEval act (List.replicate m e) x = x := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, ih, he]

omit [DecidableEq α] in
/-- **Exact-shell padding.**  Every word within a depth budget has the same endpoint as one word
on the exact budget shell whenever the alphabet contains an identity action. -/
theorem exists_vector_pad_wordEval
    (act : α → X → X) (e : α) (he : ∀ x, act e x = x)
    {w : List α} {budget : ℕ} (hw : w.length ≤ budget) (x : X) :
    ∃ v : List.Vector α budget, wordEval act v.1 x = wordEval act w x := by
  refine ⟨⟨List.replicate (budget - w.length) e ++ w, ?_⟩, ?_⟩
  · simp [Nat.sub_add_cancel hw]
  · rw [wordEval_append, wordEval_replicate_identity act e he]

omit [DecidableEq α] in
/-- Exchanging adjacent independent letters is semantically invisible whenever independent
letters act by commuting maps. -/
theorem wordEval_eq_of_independentSwap
    (act : α → X → X) (independent : α → α → Prop)
    (hcomm : ∀ a b, independent a b → ∀ x, act a (act b x) = act b (act a x))
    {u v : List α} (h : IndependentSwap independent u v) (x : X) :
    wordEval act u x = wordEval act v x := by
  cases h with
  | swap l r a b hab =>
      simp only [wordEval_append, wordEval_cons]
      rw [hcomm a b hab]

omit [DecidableEq α] in
/-- Gate-word evaluation is constant on every partially commutative trace class. -/
theorem wordEval_eq_of_traceEq
    (act : α → X → X) (independent : α → α → Prop)
    (hcomm : ∀ a b, independent a b → ∀ x, act a (act b x) = act b (act a x))
    {u v : List α} (h : TraceEq independent u v) (x : X) :
    wordEval act u x = wordEval act v x := by
  induction h with
  | rel u v huv => exact wordEval_eq_of_independentSwap act independent hcomm huv x
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ huv hvw => exact huv.trans hvw

/-- Semantic endpoint of a fixed-length trace class. -/
noncomputable def fixedTraceWordEval
    (act : α → X → X) (independent : α → α → Prop)
  (hcomm : ∀ a b, independent a b → ∀ x, act a (act b x) = act b (act a x))
    (ell : ℕ) (chi : X) : FixedTraceClass independent ell → X :=
  Quotient.lift (fun w : List.Vector α ell => wordEval act w.1 chi)
    (fun _ _ huv => wordEval_eq_of_traceEq act independent hcomm huv chi)

omit [DecidableEq α] in
@[simp]
theorem fixedTraceWordEval_mk
    (act : α → X → X) (independent : α → α → Prop)
    (hcomm : ∀ a b, independent a b → ∀ x, act a (act b x) = act b (act a x))
    (ell : ℕ) (chi : X) (w : List.Vector α ell) :
    fixedTraceWordEval act independent hcomm ell chi
        (Quotient.mk (fixedTraceSetoid independent ell) w) = wordEval act w.1 chi := rfl

end TraceSemantics

end GaloisForLFunctions.RHTower

namespace RHTower

section TraceHeapPlateau

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Intrinsic number bound for length-`ell` heaps over an alphabet whose dependence degree is at
most `Delta`. -/
def traceHeapCapacity (α : Type*) [Fintype α] (ell Delta : ℕ) : ℕ :=
  (Fintype.card α + ell - 1).choose ell * 2 ^ (Delta * ell)

/-- **Trace-heap static Choi entropy law.**  When target semantics is invariant under exchanges of
independent letters, the complete length-`ell` word union pays intrinsic trace capacity rather
than free-word cardinality. -/
theorem measureReal_iUnion_uniformPhaseDensity_traceWords_le
    {d : ℕ} (hd : 0 < d)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (ell Delta : ℕ)
    (hdegree : ∀ a, GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (target : List.Vector α ell → EuclideanSpace ℂ (Fin d × Fin d))
    (htrace : ∀ u v, GaloisForLFunctions.RHTower.TraceEq independent u.1 v.1 →
      target u = target v)
    {δ : ℝ} (hδ : 0 < δ) :
    volume.real
        (⋃ w, torusMetricBallTarget (uniformPhaseDensity d) (target w) δ) ≤
      (traceHeapCapacity α ell Delta : ℝ) *
        ((d : ℝ) * Real.exp ((d : ℝ) / 2) *
          Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ (d - 1)) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let Q := GaloisForLFunctions.RHTower.FixedTraceClass independent ell
  letI : Fintype Q := Fintype.ofFinite Q
  let targetQ : Q → EuclideanSpace ℂ (Fin d × Fin d) :=
    Quotient.lift target (fun u v huv => htrace u v huv)
  have hsub :
      (⋃ w, torusMetricBallTarget (uniformPhaseDensity d) (target w) δ) ⊆
        ⋃ q : Q, torusMetricBallTarget (uniformPhaseDensity d) (targetQ q) δ := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨w, hw⟩ := hx
    refine ⟨Quotient.mk (GaloisForLFunctions.RHTower.fixedTraceSetoid independent ell) w, ?_⟩
    exact hw
  have hraw := measureReal_iUnion_torusTargetControlled_le
    (fun q : Q => torusMetricBallTarget (uniformPhaseDensity d) (targetQ q) δ)
    (by positivity : 0 < 2 * δ ^ 2)
    (fun q => uniformPhaseDensity_metricBallTarget_controlled hd hδ.le (targetQ q))
  have hcardNat : Nat.card Q ≤ traceHeapCapacity α ell Delta := by
    simpa only [traceHeapCapacity] using
      (GaloisForLFunctions.RHTower.natCard_fixedTraceClass_le_maxDegree
        independent hsymm ell Delta hdegree)
  have hcard : (Fintype.card Q : ℝ) ≤ (traceHeapCapacity α ell Delta : ℝ) := by
    exact_mod_cast (by simpa [Nat.card_eq_fintype_card] using hcardNat)
  have hbase : 0 ≤
      (d : ℝ) * Real.exp ((d : ℝ) / 2) *
        Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ (d - 1) := by positivity
  calc
    volume.real (⋃ w, torusMetricBallTarget (uniformPhaseDensity d) (target w) δ)
        ≤ volume.real
            (⋃ q : Q, torusMetricBallTarget (uniformPhaseDensity d) (targetQ q) δ) :=
          measureReal_mono hsub
    _ ≤ (Fintype.card Q : ℝ) *
          ((d : ℝ) * Real.exp ((d : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ (d - 1)) := by
          simpa only [Fintype.card_fin] using hraw
    _ ≤ (traceHeapCapacity α ell Delta : ℝ) *
          ((d : ℝ) * Real.exp ((d : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ (d - 1)) :=
          mul_le_mul_of_nonneg_right hcard hbase

/-- **Completed-time trace-heap plateau law.**  One rationally independent static spectrum spends
at most the displayed intrinsic trace-capacity fraction of completed time within the entire local
circuit dictionary.  No eigenbasis randomness or redraw is used. -/
theorem completedTime_iUnion_uniformPhaseDensity_traceWords
    {d : ℕ} (hd : 0 < d)
    (frequency : Fin d → ℝ)
    (hindependent :
      GaloisForLFunctions.HTGeometry.RationallyIndependentFrequency frequency)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (ell Delta : ℕ)
    (hdegree : ∀ a, GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (target : List.Vector α ell → EuclideanSpace ℂ (Fin d × Fin d))
    (htrace : ∀ u v, GaloisForLFunctions.RHTower.TraceEq independent u.1 v.1 →
      target u = target v)
    {δ : ℝ} (hδ : 0 < δ) :
    let A : Set (UnitAddTorus (Fin d)) :=
      ⋃ w, torusMetricBallTarget (uniformPhaseDensity d) (target w) δ
    atTop.limsup (fun T =>
        (GaloisForLFunctions.HTGeometry.finiteTorusPhaseProbabilityMeasure
          frequency T : Measure (UnitAddTorus (Fin d))) A) ≤ volume A ∧
      volume.real A ≤
        (traceHeapCapacity α ell Delta : ℝ) *
          ((d : ℝ) * Real.exp ((d : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ (d - 1)) := by
  dsimp only
  constructor
  · apply GaloisForLFunctions.HTGeometry.rationallyIndependent_closedTarget_limsup_le_volume
      frequency hindependent
    apply isClosed_iUnion_of_finite
    intro w
    exact isClosed_torusMetricBallTarget (continuous_uniformPhaseDensity d) (target w) δ
  · exact measureReal_iUnion_uniformPhaseDensity_traceWords_le hd independent hsymm ell Delta
      hdegree target htrace hδ

/-! ## Physical projective phase and syndetic hard epochs -/

/-- Complete exact-length word target on the physical zero-anchored phase torus. -/
def zeroAnchoredTraceWordTarget
    (d ell : ℕ)
    (target : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (δ : ℝ) : Set (Fin d → UnitAddCircle) :=
  ⋃ w, zeroAnchoredMetricBallTarget d (target w) δ

omit [LinearOrder α] in
theorem isClosed_zeroAnchoredTraceWordTarget
    (d ell : ℕ)
    (target : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (δ : ℝ) :
    IsClosed (zeroAnchoredTraceWordTarget d ell target δ) := by
  rw [zeroAnchoredTraceWordTarget]
  exact isClosed_iUnion_of_finite fun w =>
    isClosed_zeroAnchoredMetricBallTarget d (target w) δ

omit [LinearOrder α] in
/-- Projectivization preserves the mass of the entire trace-word union, including all overlaps. -/
theorem volume_zeroAnchoredTraceWordTarget_eq_full
    (d ell : ℕ)
    (target : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (δ : ℝ) :
    volume (zeroAnchoredTraceWordTarget d ell target δ) =
      volume (⋃ w, torusMetricBallTarget
        (uniformPhaseDensity (d + 1)) (target w) δ) := by
  let B := zeroAnchoredTraceWordTarget d ell target δ
  let A := ⋃ w, torusMetricBallTarget
    (uniformPhaseDensity (d + 1)) (target w) δ
  have hB : MeasurableSet B :=
    (isClosed_zeroAnchoredTraceWordTarget d ell target δ).measurableSet
  have hpre : (zeroRelativePhaseEquiv d :
      (Fin (d + 1) → UnitAddCircle) →
        UnitAddCircle × (Fin d → UnitAddCircle)) ⁻¹' (Set.univ ×ˢ B) = A := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    have hdensity :
        uniformPhaseDensity (d + 1) x =
          uniformPhaseDensity (d + 1)
            (zeroAnchoredPhase d (zeroRelativePhaseEquiv d x).2) := by
      calc
        _ = uniformPhaseDensity (d + 1)
            ((zeroRelativePhaseEquiv d).symm (zeroRelativePhaseEquiv d x)) := by
              rw [(zeroRelativePhaseEquiv d).symm_apply_apply]
        _ = uniformPhaseDensity (d + 1)
            (fun i => zeroAnchoredPhase d (zeroRelativePhaseEquiv d x).2 i +
              (zeroRelativePhaseEquiv d x).1) := by
              rw [zeroRelativePhaseEquiv_symm_eq_anchored_add]
        _ = _ := uniformPhaseDensity_add_common _ _ _
    constructor
    · intro hx
      change (zeroRelativePhaseEquiv d x).2 ∈
        zeroAnchoredTraceWordTarget d ell target δ at hx
      rw [zeroAnchoredTraceWordTarget, Set.mem_iUnion] at hx
      obtain ⟨w, hw⟩ := hx
      rw [Set.mem_iUnion]
      refine ⟨w, ?_⟩
      change dist (uniformPhaseDensity (d + 1) x) (target w) ≤ δ
      rw [hdensity]
      exact hw
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨w, hw⟩ := hx
      change (zeroRelativePhaseEquiv d x).2 ∈
        zeroAnchoredTraceWordTarget d ell target δ
      rw [zeroAnchoredTraceWordTarget, Set.mem_iUnion]
      refine ⟨w, ?_⟩
      change dist
        (uniformPhaseDensity (d + 1)
          (zeroAnchoredPhase d (zeroRelativePhaseEquiv d x).2))
        (target w) ≤ δ
      rw [← hdensity]
      exact hw
  have hmeasure := (measurePreserving_zeroRelativePhaseEquiv d).measure_preimage
    (MeasurableSet.univ.prod hB).nullMeasurableSet
  rw [hpre] at hmeasure
  change volume A =
    ((volume : Measure UnitAddCircle).prod
      (volume : Measure (Fin d → UnitAddCircle))) (Set.univ ×ˢ B) at hmeasure
  rw [Measure.prod_prod, UnitAddCircle.measure_univ, one_mul] at hmeasure
  exact hmeasure.symm

/-- Intrinsic trace-capacity bound on the physical projective Choi torus. -/
theorem measureReal_zeroAnchoredTraceWordTarget_le
    (d : ℕ)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (ell Delta : ℕ)
    (hdegree : ∀ a, GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (target : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htrace : ∀ u v, GaloisForLFunctions.RHTower.TraceEq independent u.1 v.1 →
      target u = target v)
    {δ : ℝ} (hδ : 0 < δ) :
    volume.real (zeroAnchoredTraceWordTarget d ell target δ) ≤
      (traceHeapCapacity α ell Delta : ℝ) *
        (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
          Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ ((d + 1 : ℕ) - 1)) := by
  rw [measureReal_def, volume_zeroAnchoredTraceWordTarget_eq_full, ← measureReal_def]
  exact measureReal_iUnion_uniformPhaseDensity_traceWords_le (Nat.succ_pos d)
    independent hsymm ell Delta hdegree target htrace hδ

/-- Projective completed-time law with the exact local trace-heap multiplier. -/
theorem completedTime_zeroAnchoredTraceWordTargets
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (ell Delta : ℕ)
    (hdegree : ∀ a, GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (target : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htrace : ∀ u v, GaloisForLFunctions.RHTower.TraceEq independent u.1 v.1 →
      target u = target v)
    {δ : ℝ} (hδ : 0 < δ) :
    let A := zeroAnchoredTraceWordTarget d ell target δ
    atTop.limsup (fun T =>
        (GaloisForLFunctions.HTGeometry.finiteTorusPhaseProbabilityMeasure
          (zeroProjectiveFrequency energy) T : Measure (UnitAddTorus (Fin d))) A) ≤ volume A ∧
      volume.real A ≤
        (traceHeapCapacity α ell Delta : ℝ) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ ((d + 1 : ℕ) - 1)) := by
  dsimp only
  constructor
  · apply GaloisForLFunctions.HTGeometry.rationallyIndependent_closedTarget_limsup_le_volume
      (zeroProjectiveFrequency energy)
      (maximallyProjectiveEnergy_zeroProjectiveFrequency_independent energy hmax)
    exact isClosed_zeroAnchoredTraceWordTarget d ell target δ
  · exact measureReal_zeroAnchoredTraceWordTarget_le d independent hsymm ell Delta hdegree
      target htrace hδ

omit [Fintype α] [LinearOrder α] in
/-- A projective trace-word target of Haar mass below one has a hard phase. -/
theorem compl_zeroAnchoredTraceWordTarget_nonempty_of_volumeReal_lt_one
    (d ell : ℕ)
    (target : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (δ : ℝ)
    (hsmall : volume.real (zeroAnchoredTraceWordTarget d ell target δ) < 1) :
    (zeroAnchoredTraceWordTarget d ell target δ)ᶜ.Nonempty := by
  by_contra hnot
  have htarget : zeroAnchoredTraceWordTarget d ell target δ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact hnot ⟨x, hx⟩
  rw [htarget, measureReal_def] at hsmall
  change ((volume : Measure (Fin d → UnitAddCircle)) Set.univ).toReal < 1 at hsmall
  have huniv : (volume : Measure (Fin d → UnitAddCircle)) Set.univ = 1 := by
    change Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle)) Set.univ = 1
    rw [Measure.pi_univ]
    simp
  rw [huniv] at hsmall
  norm_num at hsmall

/-- **Syndetic dimension-linear trace-heap plateau.**  Under the explicit intrinsic-capacity
inequality, every interval of one finite length contains a physical time farther than `δ` from
every exact-length local word. -/
theorem maximallyProjective_traceWordsHardTimes_syndetic
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (ell Delta : ℕ)
    (hdegree : ∀ a, GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (target : List.Vector α ell →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (htrace : ∀ u v, GaloisForLFunctions.RHTower.TraceEq independent u.1 v.1 →
      target u = target v)
    {δ : ℝ} (hδ : 0 < δ)
    (hentropy :
      (traceHeapCapacity α ell Delta : ℝ) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ ((d + 1 : ℕ) - 1)) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, ∃ t ∈ Set.Icc a (a + L),
      ∀ w : List.Vector α ell,
        δ < dist
          (uniformPhaseDensity (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (target w) := by
  have hvolume : volume.real (zeroAnchoredTraceWordTarget d ell target δ) < 1 :=
    (measureReal_zeroAnchoredTraceWordTarget_le d independent hsymm ell Delta hdegree
      target htrace hδ).trans_lt hentropy
  have hopen : IsOpen (zeroAnchoredTraceWordTarget d ell target δ)ᶜ :=
    (isClosed_zeroAnchoredTraceWordTarget d ell target δ).isOpen_compl
  have hne := compl_zeroAnchoredTraceWordTarget_nonempty_of_volumeReal_lt_one
    d ell target δ hvolume
  obtain ⟨L, hL, hhits⟩ :=
    GaloisForLFunctions.HTGeometry.denseAddOrbit_open_hits_syndetically
      (projectivePhysicalPhaseFlowHom energy)
      (denseRange_projectivePhysicalPhaseFlowHom energy hmax)
      hopen hne
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨t, ht, hhard⟩ := hhits a
  refine ⟨t, ht, fun w => ?_⟩
  have hw : projectivePhysicalPhaseFlow energy t ∉
      zeroAnchoredMetricBallTarget d (target w) δ := by
    intro hmem
    apply hhard
    exact Set.mem_iUnion.mpr ⟨w, hmem⟩
  change ¬dist
    (uniformPhaseDensity (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
    (target w) ≤ δ at hw
  exact lt_of_not_ge hw

/-- Semantic specialization: commuting independent gate actions automatically satisfy the trace
invariance premise of the syndetic plateau law. -/
theorem maximallyProjective_commutingGateWordsHardTimes_syndetic
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (ell Delta : ℕ)
    (hdegree : ∀ a, GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (act : α →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (hcomm : ∀ a b, independent a b → ∀ x, act a (act b x) = act b (act a x))
    (chi : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {δ : ℝ} (hδ : 0 < δ)
    (hentropy :
      (traceHeapCapacity α ell Delta : ℝ) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ ((d + 1 : ℕ) - 1)) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, ∃ t ∈ Set.Icc a (a + L),
      ∀ w : List.Vector α ell,
        δ < dist
          (uniformPhaseDensity (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (GaloisForLFunctions.RHTower.wordEval act w.1 chi) := by
  exact maximallyProjective_traceWordsHardTimes_syndetic energy hmax independent hsymm ell Delta
    hdegree (fun w => GaloisForLFunctions.RHTower.wordEval act w.1 chi)
    (fun u v huv =>
      GaloisForLFunctions.RHTower.wordEval_eq_of_traceEq act independent hcomm huv chi)
    hδ hentropy

/-- **Complete bounded-depth trace-heap plateau.**  If the gate alphabet contains an identity
action, the exact-shell theorem simultaneously excludes every circuit word of length at most the
budget.  No union over shorter shells and no additional entropy multiplier is needed. -/
theorem maximallyProjective_commutingGateWordsAtMostHardTimes_syndetic
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy)
    (independent : α → α → Prop)
    (hsymm : ∀ a b, independent a b → independent b a)
    (budget Delta : ℕ)
    (hdegree : ∀ a, GaloisForLFunctions.RHTower.incidentEdgeCount independent a ≤ Delta)
    (act : α →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)) →
      EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (hcomm : ∀ a b, independent a b → ∀ x, act a (act b x) = act b (act a x))
    (e : α) (he : ∀ x, act e x = x)
    (chi : EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    {δ : ℝ} (hδ : 0 < δ)
    (hentropy :
      (traceHeapCapacity α budget Delta : ℝ) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ 2) / 2) ^ ((d + 1 : ℕ) - 1)) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, ∃ t ∈ Set.Icc a (a + L),
      ∀ w : List α, w.length ≤ budget →
        δ < dist
          (uniformPhaseDensity (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (GaloisForLFunctions.RHTower.wordEval act w chi) := by
  obtain ⟨L, hL, hhits⟩ :=
    maximallyProjective_commutingGateWordsHardTimes_syndetic energy hmax independent hsymm
      budget Delta hdegree act hcomm chi hδ hentropy
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨t, ht, hhard⟩ := hhits a
  refine ⟨t, ht, fun w hw => ?_⟩
  obtain ⟨v, hv⟩ := GaloisForLFunctions.RHTower.exists_vector_pad_wordEval act e he hw chi
  rw [← hv]
  exact hhard v

end TraceHeapPlateau

end RHTower
