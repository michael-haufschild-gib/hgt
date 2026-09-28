import GaloisForLFunctions.HTGeometry.OrbitInductionInformation

/-!
# Independent packet information: summability is the information boundary

For probability pairs `(Pᵢ, Qᵢ)` on possibly different measurable spaces and a finite set `F` of
indices, the independent packets `P_F = ⊗_{i∈F} Pᵢ`, `Q_F = ⊗_{i∈F} Qᵢ` satisfy

* `klDiv_independentPacket` — relative entropy is additive over heterogeneous finite products;
* `formationJeffreys_independentPacket_recovery` `(WOI.12)` — after a common recovery kernel on
  each pair, the symmetric information work is exactly `∑_{i∈F} J(Pᵢ, Qᵢ)`;
* `iSup_formationJeffreys_exhaustion`, `formationJeffreys_exhaustion_bounded_iff` `(WOI.13)` —
  along any increasing exhaustion `F_n ↑ I` the supremum of the work is the full sum
  `∑ᵢ J(Pᵢ, Qᵢ)`, so it is finite exactly when the local divergences are summable;
* `tsum_const_formationJeffreys_ne_top_iff` — for homogeneous packets over an infinite index set,
  bounded work forces `J = 0`;
* `exists_finite_information_unequal_packets` — finite total information does not force equal
  local packets.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal Topology

noncomputable section

section Packets

variable {I : Type*} {Z : I → Type*} [∀ i, MeasurableSpace (Z i)]

/-- `(WOI.11)`  The independent packet of a family of laws over a finite set of indices. -/
def independentPacket (F : Finset I) (P : ∀ i, Measure (Z i)) : Measure (∀ i : F, Z i) :=
  Measure.pi fun i : F => P i

instance isProbabilityMeasure_independentPacket (F : Finset I) (P : ∀ i, Measure (Z i))
    [∀ i, IsProbabilityMeasure (P i)] : IsProbabilityMeasure (independentPacket F P) := by
  rw [independentPacket]
  infer_instance

theorem independentPacket_empty_eq (P Q : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] :
    independentPacket (∅ : Finset I) P = independentPacket ∅ Q := by
  refine Measure.ext fun s _ => ?_
  rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
  · simp
  · have hs : s = Set.univ := by
      ext y
      have : y = x := funext fun i => absurd i.2 (Finset.notMem_empty _)
      simp [this, hx]
    rw [hs, measure_univ, measure_univ]

/-- **Relative entropy is additive over heterogeneous finite independent packets.** -/
theorem klDiv_independentPacket [DecidableEq I] (F : Finset I) (P Q : ∀ i, Measure (Z i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)] :
    klDiv (independentPacket F P) (independentPacket F Q) = ∑ i ∈ F, klDiv (P i) (Q i) := by
  induction F using Finset.induction_on with
  | empty =>
      rw [independentPacket_empty_eq P Q, klDiv_self, Finset.sum_empty]
  | insert j F hjF ih =>
      rw [Finset.insert_eq, Finset.sum_union (Finset.disjoint_singleton_left.mpr hjF),
        Finset.sum_singleton]
      have hdisj : Disjoint ({j} : Finset I) F := Finset.disjoint_singleton_left.mpr hjF
      have hP := measurePreserving_piFinsetUnion (α := Z) hdisj P
      have hQ := measurePreserving_piFinsetUnion (α := Z) hdisj Q
      have hemb := (MeasurableEquiv.piFinsetUnion Z hdisj).measurableEmbedding
      have hPj := measurePreserving_piUnique (X := fun i : ({j} : Finset I) => Z i)
        (fun i : ({j} : Finset I) => P i)
      have hQj := measurePreserving_piUnique (X := fun i : ({j} : Finset I) => Z i)
        (fun i : ({j} : Finset I) => Q i)
      have hembj := (MeasurableEquiv.piUnique fun i : ({j} : Finset I) => Z i).measurableEmbedding
      have hsingle : klDiv (Measure.pi fun i : ({j} : Finset I) => P i)
          (Measure.pi fun i : ({j} : Finset I) => Q i) = klDiv (P j) (Q j) := by
        rw [← klDiv_map_measurableEmbedding hembj, hPj.map_eq, hQj.map_eq]
        rfl
      unfold independentPacket
      rw [← hP.map_eq, ← hQ.map_eq, klDiv_map_measurableEmbedding hemb, klDiv_prod, hsingle]
      unfold independentPacket at ih
      rw [ih]

variable {W : I → Type*} [∀ i, MeasurableSpace (W i)]

/-- **Theorem 6.1, `(WOI.12)`.**  Under a common recovery kernel on each pair, the symmetric
information work of the finite independent packet is exactly the sum of the local works. -/
theorem formationJeffreys_independentPacket_recovery [DecidableEq I] (F : Finset I)
    (P Q : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] (κ : ∀ i, Kernel (Z i) (W i)) [∀ i, IsMarkovKernel (κ i)] :
    formationJeffreys (independentPacket F fun i => splitPacketLaw (P i) (κ i))
        (independentPacket F fun i => splitPacketLaw (Q i) (κ i))
      = ∑ i ∈ F, formationJeffreys (P i) (Q i) := by
  rw [formationJeffreys, klDiv_independentPacket, klDiv_independentPacket,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [klDiv_splitPacketLaw, klDiv_splitPacketLaw, formationJeffreys]

/-- **Theorem 6.1.**  Common recovery preserves the exact work of the finite packet. -/
theorem formationJeffreys_independentPacket_recovery_eq [DecidableEq I] (F : Finset I)
    (P Q : ∀ i, Measure (Z i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] (κ : ∀ i, Kernel (Z i) (W i)) [∀ i, IsMarkovKernel (κ i)] :
    formationJeffreys (independentPacket F fun i => splitPacketLaw (P i) (κ i))
        (independentPacket F fun i => splitPacketLaw (Q i) (κ i))
      = formationJeffreys (independentPacket F P) (independentPacket F Q) := by
  rw [formationJeffreys_independentPacket_recovery, formationJeffreys, klDiv_independentPacket,
    klDiv_independentPacket, ← Finset.sum_add_distrib]
  rfl

theorem exists_subset_of_exhaustion {Fn : ℕ → Finset I} (hmono : Monotone Fn)
    (hexh : ∀ i, ∃ n, i ∈ Fn n) (s : Finset I) : ∃ n, s ⊆ Fn n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | insert a s _ ih =>
      obtain ⟨n₁, hn₁⟩ := ih
      obtain ⟨n₂, hn₂⟩ := hexh a
      refine ⟨max n₁ n₂, Finset.insert_subset ?_ ?_⟩
      · exact hmono (le_max_right n₁ n₂) hn₂
      · exact hn₁.trans (hmono (le_max_left n₁ n₂))

/-- Along an increasing exhaustion, finite partial sums of a nonnegative family increase to the
full sum. -/
theorem iSup_sum_exhaustion {Fn : ℕ → Finset I} (hmono : Monotone Fn)
    (hexh : ∀ i, ∃ n, i ∈ Fn n) (j : I → ℝ≥0∞) :
    ⨆ n, ∑ i ∈ Fn n, j i = ∑' i, j i := by
  refine le_antisymm (iSup_le fun n => ENNReal.sum_le_tsum _) ?_
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  obtain ⟨n, hn⟩ := exists_subset_of_exhaustion hmono hexh s
  exact (Finset.sum_le_sum_of_subset hn).trans (le_iSup (fun n => ∑ i ∈ Fn n, j i) n)

/-- **Theorem 6.1, `(WOI.13)`.**  Along any increasing exhaustion `F_n ↑ I`, the supremum of the
recovered packet work is the full sum of the local works. -/
theorem iSup_formationJeffreys_exhaustion [DecidableEq I] {Fn : ℕ → Finset I}
    (hmono : Monotone Fn) (hexh : ∀ i, ∃ n, i ∈ Fn n) (P Q : ∀ i, Measure (Z i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]
    (κ : ∀ i, Kernel (Z i) (W i)) [∀ i, IsMarkovKernel (κ i)] :
    ⨆ n, formationJeffreys (independentPacket (Fn n) fun i => splitPacketLaw (P i) (κ i))
        (independentPacket (Fn n) fun i => splitPacketLaw (Q i) (κ i))
      = ∑' i, formationJeffreys (P i) (Q i) := by
  simp_rw [formationJeffreys_independentPacket_recovery]
  exact iSup_sum_exhaustion hmono hexh _

/-- **Theorem 6.1, `(WOI.13)`.**  The recovered packet work stays bounded along an exhaustion
exactly when the local divergences are summable. -/
theorem formationJeffreys_exhaustion_bounded_iff [DecidableEq I] {Fn : ℕ → Finset I}
    (hmono : Monotone Fn) (hexh : ∀ i, ∃ n, i ∈ Fn n) (P Q : ∀ i, Measure (Z i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]
    (κ : ∀ i, Kernel (Z i) (W i)) [∀ i, IsMarkovKernel (κ i)] :
    (⨆ n, formationJeffreys (independentPacket (Fn n) fun i => splitPacketLaw (P i) (κ i))
        (independentPacket (Fn n) fun i => splitPacketLaw (Q i) (κ i))) < ⊤
      ↔ ∑' i, formationJeffreys (P i) (Q i) < ⊤ := by
  rw [iSup_formationJeffreys_exhaustion hmono hexh P Q κ]

/-- `(WOI.13)`, bounded-sequence form. -/
theorem exists_bound_formationJeffreys_exhaustion_iff [DecidableEq I] {Fn : ℕ → Finset I}
    (hmono : Monotone Fn) (hexh : ∀ i, ∃ n, i ∈ Fn n) (P Q : ∀ i, Measure (Z i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)]
    (κ : ∀ i, Kernel (Z i) (W i)) [∀ i, IsMarkovKernel (κ i)] :
    (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n,
        formationJeffreys (independentPacket (Fn n) fun i => splitPacketLaw (P i) (κ i))
          (independentPacket (Fn n) fun i => splitPacketLaw (Q i) (κ i)) ≤ M)
      ↔ ∑' i, formationJeffreys (P i) (Q i) ≠ ⊤ := by
  rw [← iSup_formationJeffreys_exhaustion hmono hexh P Q κ]
  constructor
  · rintro ⟨M, hM, h⟩
    exact ne_top_of_le_ne_top hM (iSup_le h)
  · intro h
    exact ⟨_, h, fun n => le_iSup (fun n =>
      formationJeffreys (independentPacket (Fn n) fun i => splitPacketLaw (P i) (κ i))
        (independentPacket (Fn n) fun i => splitPacketLaw (Q i) (κ i))) n⟩

end Packets

/-! ## Homogeneous and inhomogeneous information -/

section Homogeneous

/-- **Homogeneous information induction.**  Over an infinite index set, a constant local work has
finite total exactly when it vanishes. -/
theorem tsum_const_ne_top_iff {I : Type*} [Infinite I] (j : ℝ≥0∞) :
    ∑' _ : I, j ≠ ⊤ ↔ j = 0 := by
  constructor
  · intro h
    by_contra hj
    exact h (ENNReal.tsum_const_eq_top_of_ne_zero hj)
  · rintro rfl
    simp

/-- **Homogeneous information induction.**  Copies of one probability pair over an infinite index
set have finite total information exactly when the pair is equal. -/
theorem tsum_const_formationJeffreys_ne_top_iff {I Z : Type*} [Infinite I] [MeasurableSpace Z]
    (P Q : Measure Z) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ∑' _ : I, formationJeffreys P Q ≠ ⊤ ↔ P = Q := by
  rw [tsum_const_ne_top_iff, formationJeffreys, add_eq_zero]
  constructor
  · rintro ⟨h, -⟩
    exact klDiv_eq_zero_iff.mp h
  · rintro rfl
    exact ⟨klDiv_self P, klDiv_self P⟩

/-- A two-point law with mass `p` at `true`. -/
def boolLaw (p : ℝ≥0∞) : Measure Bool := p • Measure.dirac true + (1 - p) • Measure.dirac false

theorem boolLaw_apply_true (p : ℝ≥0∞) : boolLaw p {true} = p := by
  simp [boolLaw]

theorem boolLaw_apply_false (p : ℝ≥0∞) : boolLaw p {false} = 1 - p := by
  simp [boolLaw]

theorem isProbabilityMeasure_boolLaw {p : ℝ≥0∞} (hp : p ≤ 1) :
    IsProbabilityMeasure (boolLaw p) := by
  constructor
  simp [boolLaw, add_tsub_cancel_of_le hp]

theorem boolLaw_absolutelyContinuous {p q : ℝ≥0∞} (hq0 : q ≠ 0) (hq1 : q < 1) :
    boolLaw p ≪ boolLaw q := by
  intro s hs
  have hs' : s = ∅ := by
    ext b
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hb
    have hle : boolLaw q {b} ≤ boolLaw q s := measure_mono (Set.singleton_subset_iff.mpr hb)
    rw [hs] at hle
    cases b
    · rw [boolLaw_apply_false] at hle
      exact absurd (le_antisymm hle zero_le) (tsub_pos_of_lt hq1).ne'
    · rw [boolLaw_apply_true] at hle
      exact hq0 (le_antisymm hle zero_le)
  rw [hs']
  exact measure_empty

theorem klDiv_boolLaw_ne_top {p q : ℝ≥0∞} (hp : p ≤ 1) (hq0 : q ≠ 0) (hq1 : q < 1) :
    klDiv (boolLaw p) (boolLaw q) ≠ ⊤ := by
  haveI := isProbabilityMeasure_boolLaw hp
  rw [klDiv_ne_top_iff]
  exact ⟨boolLaw_absolutelyContinuous hq0 hq1, Integrable.of_finite⟩

/-- **No-go 9.5.**  Finite total information does not force equal local packets: a family with
one unequal pair of full-support laws and equal pairs elsewhere has finite total work. -/
theorem exists_finite_information_unequal_packets :
    ∃ P Q : ℕ → Measure Bool, (∀ i, IsProbabilityMeasure (P i)) ∧
      (∀ i, IsProbabilityMeasure (Q i)) ∧
      ∑' i, formationJeffreys (P i) (Q i) ≠ ⊤ ∧ ∃ i, P i ≠ Q i := by
  set p : ℝ≥0∞ := 2⁻¹ with hp
  set q : ℝ≥0∞ := 4⁻¹ with hq
  have hp1 : p ≤ 1 := by rw [hp]; exact ENNReal.inv_le_one.mpr (by norm_num)
  have hq1' : q ≤ 1 := by rw [hq]; exact ENNReal.inv_le_one.mpr (by norm_num)
  have hp0 : p ≠ 0 := by rw [hp]; exact ENNReal.inv_ne_zero.mpr (by norm_num)
  have hq0 : q ≠ 0 := by rw [hq]; exact ENNReal.inv_ne_zero.mpr (by norm_num)
  have hplt : p < 1 := by rw [hp]; exact ENNReal.inv_lt_one.mpr (by norm_num)
  have hqlt : q < 1 := by rw [hq]; exact ENNReal.inv_lt_one.mpr (by norm_num)
  have hpq : p ≠ q := by
    rw [hp, hq]
    intro h
    have := congrArg (·⁻¹) h
    simp only [inv_inv] at this
    norm_num at this
  refine ⟨fun _ => boolLaw p, fun i => if i = 0 then boolLaw q else boolLaw p,
    fun _ => isProbabilityMeasure_boolLaw hp1, fun i => ?_, ?_, ⟨0, ?_⟩⟩
  · by_cases hi : i = 0
    · simp only [hi, if_true]; exact isProbabilityMeasure_boolLaw hq1'
    · simp only [hi, if_false]; exact isProbabilityMeasure_boolLaw hp1
  · haveI := isProbabilityMeasure_boolLaw hp1
    rw [tsum_eq_single 0 fun i hi => by
      simp only [hi, if_false, formationJeffreys, klDiv_self, add_zero]]
    simp only [if_true, formationJeffreys]
    exact ENNReal.add_ne_top.mpr ⟨klDiv_boolLaw_ne_top hp1 hq0 hqlt,
      klDiv_boolLaw_ne_top hq1' hp0 hplt⟩
  · simp only [if_true]
    intro h
    have := congrArg (fun μ : Measure Bool => μ {true}) h
    simp only [boolLaw_apply_true] at this
    exact hpq this

end Homogeneous

end

end GaloisForLFunctions.HTGeometry
