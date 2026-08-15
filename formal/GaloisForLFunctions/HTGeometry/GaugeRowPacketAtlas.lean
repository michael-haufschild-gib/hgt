import GaloisForLFunctions.HTGeometry.CompactNoncriticalProjectiveRowPacketAtlas
import GaloisForLFunctions.HTGeometry.EntireZeroSetNull

/-!
# Row-packet atlases for a source with a prescribed divisor

An evaluation row packet is admissible for a shift configuration when the whole row-by-shift node
family is collision-free, avoids the origin, and avoids the divisor of the source.  All three are
open conditions, and translating a collision-free row packet by a point outside a countable set
achieves them, because the zero set of a nonzero entire function is countable.

Compactness of a shift patch then produces a finite atlas of admissible row packets.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology

noncomputable section

/-! ### Translating a finite node family off a countable zero set -/

/-- A translate of a finite node family avoids both the origin and the divisor of a nonzero entire
source. -/
theorem exists_translate_off_divisor {W : ℂ → ℂ} (hW : AnalyticOnNhd ℂ W Set.univ)
    (h0 : ∃ w, W w ≠ 0) {α : Type*} [Fintype α] (a : α → ℂ) :
    ∃ z : ℂ, (∀ x, W (z + a x) ≠ 0) ∧ ∀ x, z + a x ≠ 0 := by
  classical
  have hzero : {w : ℂ | W w = 0}.Countable := _root_.HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd hW h0
  set bad : Set ℂ :=
    (⋃ x : α, (fun z : ℂ => z + a x) ⁻¹' {w : ℂ | W w = 0}) ∪ (⋃ x : α, {-(a x)}) with hbad
  have hcount : bad.Countable := by
    refine Set.Countable.union (Set.countable_iUnion fun x => ?_)
      (Set.countable_iUnion fun x => Set.countable_singleton _)
    exact hzero.preimage (add_left_injective (a x))
  have hexists : ∃ z : ℂ, z ∉ bad := by
    by_contra hcon
    have huniv : bad = Set.univ :=
      Set.eq_univ_of_forall fun z => not_not.mp fun hz => hcon ⟨z, hz⟩
    exact not_countable_complex (huniv ▸ hcount)
  obtain ⟨z, hz⟩ := hexists
  refine ⟨z, fun x hx => ?_, fun x hx => ?_⟩
  · exact hz (Or.inl (Set.mem_iUnion.mpr ⟨x, hx⟩))
  · refine hz (Or.inr (Set.mem_iUnion.mpr ⟨x, ?_⟩))
    have : z = -(a x) := by linear_combination hx
    exact this

/-! ### Admissible row packets -/

variable {row ι : Type*} [Fintype row] [Fintype ι]

/-- Ambient shifts for which one row packet gives distinct nonzero nodes off the divisor. -/
def gaugeGoodCombinedRowPacketAmbientSet (W : ℂ → ℂ)
    (packet : InjectiveProjectiveRowPacket row) : Set (ι → ℂ) :=
  (⋂ p : (row × ι) × (row × ι), ⋂ _ : p.1 ≠ p.2,
      {shift : ι → ℂ | packet.1 p.1.1 + shift p.1.2 ≠ packet.1 p.2.1 + shift p.2.2}) ∩
    ((⋂ x : row × ι, {shift : ι → ℂ | packet.1 x.1 + shift x.2 ≠ 0}) ∩
      (⋂ x : row × ι, {shift : ι → ℂ | W (packet.1 x.1 + shift x.2) ≠ 0}))

/-- Corresponding chart in the collision-free shift configuration space. -/
def gaugeGoodCombinedRowPacketSet (W : ℂ → ℂ)
    (packet : InjectiveProjectiveRowPacket row) : Set (InjectiveShiftConfiguration ι) :=
  Subtype.val ⁻¹' gaugeGoodCombinedRowPacketAmbientSet (ι := ι) W packet

theorem gaugeGoodCombinedRowPacketAmbientSet_isOpen {W : ℂ → ℂ} (hW : Continuous W)
    (packet : InjectiveProjectiveRowPacket row) :
    IsOpen (gaugeGoodCombinedRowPacketAmbientSet (ι := ι) W packet) := by
  classical
  refine IsOpen.inter (isOpen_iInter_of_finite fun p => isOpen_iInter_of_finite fun _ => ?_)
    (IsOpen.inter (isOpen_iInter_of_finite fun x => ?_) (isOpen_iInter_of_finite fun x => ?_))
  · exact isOpen_ne_fun (continuous_const.add (continuous_apply p.1.2))
      (continuous_const.add (continuous_apply p.2.2))
  · exact isOpen_ne_fun (continuous_const.add (continuous_apply x.2)) continuous_const
  · exact isOpen_ne_fun (hW.comp (continuous_const.add (continuous_apply x.2))) continuous_const

theorem gaugeGoodCombinedRowPacketSet_isOpen {W : ℂ → ℂ} (hW : Continuous W)
    (packet : InjectiveProjectiveRowPacket row) :
    IsOpen (gaugeGoodCombinedRowPacketSet (ι := ι) W packet) :=
  (gaugeGoodCombinedRowPacketAmbientSet_isOpen (ι := ι) hW packet).preimage continuous_subtype_val

omit [Fintype row] [Fintype ι] in
theorem injective_of_mem_gaugeGoodCombinedRowPacketAmbientSet {W : ℂ → ℂ}
    {packet : InjectiveProjectiveRowPacket row} {shift : ι → ℂ}
    (h : shift ∈ gaugeGoodCombinedRowPacketAmbientSet W packet) :
    Function.Injective (fun x : row × ι => packet.1 x.1 + shift x.2) := by
  intro x y hxy
  by_contra hne
  have hmem := Set.mem_iInter.mp (Set.mem_iInter.mp h.1 (x, y)) hne
  exact hmem hxy

omit [Fintype row] [Fintype ι] in
theorem ne_zero_of_mem_gaugeGoodCombinedRowPacketAmbientSet {W : ℂ → ℂ}
    {packet : InjectiveProjectiveRowPacket row} {shift : ι → ℂ}
    (h : shift ∈ gaugeGoodCombinedRowPacketAmbientSet W packet) (x : row × ι) :
    packet.1 x.1 + shift x.2 ≠ 0 :=
  Set.mem_iInter.mp h.2.1 x

omit [Fintype row] [Fintype ι] in
theorem source_ne_zero_of_mem_gaugeGoodCombinedRowPacketAmbientSet {W : ℂ → ℂ}
    {packet : InjectiveProjectiveRowPacket row} {shift : ι → ℂ}
    (h : shift ∈ gaugeGoodCombinedRowPacketAmbientSet W packet) (x : row × ι) :
    W (packet.1 x.1 + shift x.2) ≠ 0 :=
  Set.mem_iInter.mp h.2.2 x

/-- Every collision-free shift tuple has an admissible row packet. -/
theorem injectiveShiftConfigurations_covered_by_gaugeGoodCombinedRowPackets
    {W : ℂ → ℂ} (hW : AnalyticOnNhd ℂ W Set.univ) (h0 : ∃ w, W w ≠ 0) :
    Set.univ ⊆ ⋃ packet : InjectiveProjectiveRowPacket row,
      gaugeGoodCombinedRowPacketSet (ι := ι) W packet := by
  classical
  intro shift _
  obtain ⟨offset, hoffset, hcombined⟩ :=
    exists_rowOffsets_combined_injective (row := row) (ι := ι) shift.1 shift.2
  obtain ⟨z, hzW, hz0⟩ := exists_translate_off_divisor hW h0
    (fun x : row × ι => offset x.1 + shift.1 x.2)
  have hrowBase : Function.Injective (fun r : row => z + offset r) := by
    intro r s hrs
    exact hoffset (add_left_cancel hrs)
  refine Set.mem_iUnion.mpr ⟨⟨fun r => z + offset r, hrowBase⟩, ?_, ?_, ?_⟩
  · refine Set.mem_iInter.mpr fun p => Set.mem_iInter.mpr fun hp hxy => hp ?_
    refine hcombined ?_
    have := hxy
    simp only at this
    exact add_left_cancel (a := z) (by
      simpa only [add_assoc] using this)
  · refine Set.mem_iInter.mpr fun x => ?_
    show z + offset x.1 + shift.1 x.2 ≠ 0
    rw [add_assoc]
    exact hz0 x
  · refine Set.mem_iInter.mpr fun x => ?_
    show W (z + offset x.1 + shift.1 x.2) ≠ 0
    rw [add_assoc]
    exact hzW x

/-- Every compact collision-free shift patch has a finite compact refinement subordinate to
admissible row charts. -/
theorem compact_injectiveShiftPatch_finite_gaugeGoodCombinedRowPacket_refinement
    {W : ℂ → ℂ} (hWa : AnalyticOnNhd ℂ W Set.univ) (hWc : Continuous W) (h0 : ∃ w, W w ≠ 0)
    {K : Set (InjectiveShiftConfiguration ι)} (hK : IsCompact K) :
    ∃ n : ℕ, ∃ packets : Fin n → InjectiveProjectiveRowPacket row,
      ∃ pieces : Fin n → Set (InjectiveShiftConfiguration ι),
        K ⊆ ⋃ j, pieces j ∧ (∀ j, IsCompact (pieces j)) ∧
          ∀ j, pieces j ⊆ gaugeGoodCombinedRowPacketSet (ι := ι) W (packets j) := by
  classical
  obtain ⟨packetFinset, hpacketFinset⟩ := hK.elim_finite_subcover
    (fun packet : InjectiveProjectiveRowPacket row =>
      gaugeGoodCombinedRowPacketSet (ι := ι) W packet)
    (fun packet => gaugeGoodCombinedRowPacketSet_isOpen (ι := ι) hWc packet)
    (Set.Subset.trans (Set.subset_univ K)
      (injectiveShiftConfigurations_covered_by_gaugeGoodCombinedRowPackets
        (row := row) (ι := ι) hWa h0))
  let n := packetFinset.card
  let e : Fin n ≃ {packet // packet ∈ packetFinset} := by
    simpa [n] using (Fintype.equivFin {packet // packet ∈ packetFinset}).symm
  let packets : Fin n → InjectiveProjectiveRowPacket row := fun j => (e j).1
  let cover : Fin n → Set (InjectiveShiftConfiguration ι) := fun j =>
    gaugeGoodCombinedRowPacketSet (ι := ι) W (packets j)
  have hcover : K ⊆ ⋃ j, cover j := by
    intro shift hshift
    have hs := hpacketFinset hshift
    simp only [Set.mem_iUnion] at hs
    obtain ⟨packet, hpacketMem, hgood⟩ := hs
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨packet, hpacketMem⟩, ?_⟩
    change shift ∈ gaugeGoodCombinedRowPacketSet (ι := ι) W (packets (e.symm ⟨packet, hpacketMem⟩))
    simpa [packets] using hgood
  obtain ⟨v, hKv, hvclosed, hvsub⟩ :=
    exists_subset_iUnion_closed_subset hK.isClosed
      (fun j => gaugeGoodCombinedRowPacketSet_isOpen (ι := ι) hWc (packets j))
      (fun _ _ => Set.toFinite _) hcover
  refine ⟨n, packets, fun j => K ∩ v j, ?_, ?_, ?_⟩
  · intro shift hshift
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hKv hshift)
    exact Set.mem_iUnion.mpr ⟨j, hshift, hj⟩
  · intro j
    exact hK.inter_right (hvclosed j)
  · intro j
    exact inter_subset_right.trans (hvsub j)

end

end GaloisForLFunctions.HTGeometry
