import GaloisForLFunctions.HTGeometry.CompactNoncriticalProjectiveRowPacketAtlas
import GaloisForLFunctions.HTGeometry.InjectiveShiftConfigurationTopology

/-!
# Compact row-packet atlases for ordinary Cauchy translations

For the measure-universal Herglotz theorem no projective regularity certificate is present.  A row
chart therefore records exactly two open conditions: every row-plus-shift node is upper and the
whole row-by-shift packet is collision-free.  Widely separated row offsets give such a chart at
every collision-free shift tuple; compactness and closed shrinking give a finite compact
subordinate refinement.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Topology

noncomputable section

/-- Ambient shift packets for which one row packet gives distinct strict-upper combined nodes. -/
def cauchyUpperGoodCombinedRowPacketAmbientSet
    {row ι : Type*} [Fintype row] [Fintype ι]
    (packet : InjectiveProjectiveRowPacket row) : Set (ι → ℂ) :=
  {shift | Function.Injective (fun x : row × ι => packet.1 x.1 + shift x.2)} ∩
    {shift | ∀ x : row × ι, 0 < (packet.1 x.1 + shift x.2).im}

/-- The corresponding chart inside the collision-free shift configuration space. -/
def cauchyUpperGoodCombinedRowPacketSet
    {row ι : Type*} [Fintype row] [Fintype ι]
    (packet : InjectiveProjectiveRowPacket row) :
    Set (InjectiveShiftConfiguration ι) :=
  Subtype.val ⁻¹' cauchyUpperGoodCombinedRowPacketAmbientSet packet

/-- Ordinary Cauchy combined-row charts are open in the ambient finite shift space. -/
theorem cauchyUpperGoodCombinedRowPacketAmbientSet_isOpen
    {row ι : Type*} [Fintype row] [Fintype ι]
    (packet : InjectiveProjectiveRowPacket row) :
    IsOpen (cauchyUpperGoodCombinedRowPacketAmbientSet (ι := ι) packet) := by
  classical
  apply IsOpen.inter
  · have hpacket : Continuous
        (fun shift : ι → ℂ => fun x : row × ι => packet.1 x.1 + shift x.2) := by
      apply continuous_pi
      intro x
      exact continuous_const.add (continuous_apply x.2)
    change IsOpen ((fun shift : ι → ℂ =>
      fun x : row × ι => packet.1 x.1 + shift x.2) ⁻¹'
        injectiveShiftConfigurationSet (row × ι))
    exact (injectiveShiftConfigurationSet_isOpen (row × ι)).preimage hpacket
  · rw [show {shift : ι → ℂ |
        ∀ x : row × ι, 0 < (packet.1 x.1 + shift x.2).im} =
        ⋂ x : row × ι, {shift : ι → ℂ | 0 < (packet.1 x.1 + shift x.2).im} by
      ext shift
      simp]
    apply isOpen_iInter_of_finite
    intro x
    have hcont : Continuous
        (fun shift : ι → ℂ => (packet.1 x.1 + shift x.2).im) :=
      Complex.continuous_im.comp (continuous_const.add (continuous_apply x.2))
    exact isOpen_lt continuous_const hcont

/-- Ordinary Cauchy combined-row charts are open in the collision-free configuration type. -/
theorem cauchyUpperGoodCombinedRowPacketSet_isOpen
    {row ι : Type*} [Fintype row] [Fintype ι]
    (packet : InjectiveProjectiveRowPacket row) :
    IsOpen (cauchyUpperGoodCombinedRowPacketSet (ι := ι) packet) :=
  (cauchyUpperGoodCombinedRowPacketAmbientSet_isOpen (ι := ι) packet).preimage
    continuous_subtype_val

/-- Every collision-free finite shift packet admits an injective row packet whose full combined
node packet is collision-free and lies strictly in the upper half-plane. -/
theorem injectiveShiftConfigurations_covered_by_cauchyUpperGoodCombinedRowPackets
    {row ι : Type*} [Fintype row] [Fintype ι] :
    Set.univ ⊆ ⋃ packet : InjectiveProjectiveRowPacket row,
      cauchyUpperGoodCombinedRowPacketSet (ι := ι) packet := by
  classical
  intro shift _
  obtain ⟨offset, hoffset, hcombined⟩ :=
    exists_rowOffsets_combined_injective (row := row) (ι := ι) shift.1 shift.2
  obtain ⟨H, hH⟩ := finite_complex_family_has_imaginary_lower_bound
    (fun x : row × ι => offset x.1 + shift.1 x.2)
  let z : ℂ := ⟨0, H + 1⟩
  let rowBase : row → ℂ := fun r => z + offset r
  have hrowBase : Function.Injective rowBase := by
    intro r s hrs
    apply hoffset
    apply add_left_cancel (a := z)
    simpa [rowBase] using hrs
  let packet : InjectiveProjectiveRowPacket row := ⟨rowBase, hrowBase⟩
  apply Set.mem_iUnion.mpr
  refine ⟨packet, ?_, ?_⟩
  · intro x y hxy
    apply hcombined
    apply add_left_cancel (a := z)
    simpa [combinedProjectiveRowShiftPacket, packet, rowBase, add_assoc] using hxy
  · intro x
    have hx := hH x
    change 0 < (z + offset x.1 + shift.1 x.2).im
    simp only [Complex.add_im]
    change 0 < (H + 1) + (offset x.1).im + (shift.1 x.2).im
    have hx' : -((offset x.1).im + (shift.1 x.2).im) ≤ H := by
      simpa only [Complex.add_im] using hx
    linarith

/-- **Compact ordinary-Cauchy row atlas.**  Every compact collision-free shift patch has a finite
compact refinement subordinate to complete strict-upper collision-free row-packet charts. -/
theorem compact_injectiveShiftPatch_finite_cauchyUpperGoodCombinedRowPacket_refinement
    {row ι : Type*} [Fintype row] [Fintype ι]
    {K : Set (InjectiveShiftConfiguration ι)} (hK : IsCompact K) :
    ∃ n : ℕ, ∃ packets : Fin n → InjectiveProjectiveRowPacket row,
      ∃ pieces : Fin n → Set (InjectiveShiftConfiguration ι),
        K ⊆ ⋃ j, pieces j ∧
        (∀ j, IsCompact (pieces j)) ∧
        ∀ j, pieces j ⊆ cauchyUpperGoodCombinedRowPacketSet (ι := ι) (packets j) := by
  classical
  obtain ⟨packetFinset, hpacketFinset⟩ := hK.elim_finite_subcover
    (fun packet : InjectiveProjectiveRowPacket row =>
      cauchyUpperGoodCombinedRowPacketSet (ι := ι) packet)
    (fun packet => cauchyUpperGoodCombinedRowPacketSet_isOpen (ι := ι) packet)
    (Set.Subset.trans (Set.subset_univ K)
      (injectiveShiftConfigurations_covered_by_cauchyUpperGoodCombinedRowPackets
        (row := row) (ι := ι)))
  let n := packetFinset.card
  let e : Fin n ≃ {packet // packet ∈ packetFinset} :=
    by simpa [n] using (Fintype.equivFin {packet // packet ∈ packetFinset}).symm
  let packets : Fin n → InjectiveProjectiveRowPacket row := fun j => (e j).1
  let cover : Fin n → Set (InjectiveShiftConfiguration ι) := fun j =>
    cauchyUpperGoodCombinedRowPacketSet (ι := ι) (packets j)
  have hcover : K ⊆ ⋃ j, cover j := by
    intro shift hshift
    have hs := hpacketFinset hshift
    simp only [Set.mem_iUnion] at hs
    obtain ⟨packet, hpacketMem, hgood⟩ := hs
    let j : Fin n := e.symm ⟨packet, hpacketMem⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change shift ∈ cauchyUpperGoodCombinedRowPacketSet (ι := ι) (packets j)
    simpa [packets, j] using hgood
  obtain ⟨v, hKv, hvclosed, hvsub⟩ :=
    exists_subset_iUnion_closed_subset hK.isClosed
      (fun j => cauchyUpperGoodCombinedRowPacketSet_isOpen (ι := ι) (packets j))
      (fun _ _ => Set.toFinite _) hcover
  let pieces : Fin n → Set (InjectiveShiftConfiguration ι) := fun j => K ∩ v j
  refine ⟨n, packets, pieces, ?_, ?_, ?_⟩
  · intro shift hshift
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hKv hshift)
    exact Set.mem_iUnion.mpr ⟨j, hshift, hj⟩
  · intro j
    exact hK.inter_right (hvclosed j)
  · intro j
    exact inter_subset_right.trans (hvsub j)

end

end GaloisForLFunctions.HTGeometry
