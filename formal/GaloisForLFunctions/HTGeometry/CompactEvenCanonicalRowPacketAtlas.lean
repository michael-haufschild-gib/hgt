import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalFiniteJetSubmersion

/-!
# Compact row-packet atlases for even canonical translations

The even carrier's finite-jet submersion uses the doubled packet `x, -conj x`.  To keep this
packet collision-free, a row chart requires every ordinary combined node to have positive real
part in addition to lying in the upper half-plane.  Translating a collision-free row packet far
enough in both real and imaginary directions always achieves these conditions.  Compactness and
closed shrinking then give a finite subordinate atlas.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Topology

noncomputable section

/-- Ambient shifts for which one row packet has distinct upper nodes of positive real part. -/
def evenCanonicalUpperGoodCombinedRowPacketAmbientSet
    {row ι : Type*} [Fintype row] [Fintype ι]
    (packet : InjectiveProjectiveRowPacket row) : Set (ι → ℂ) :=
  cauchyUpperGoodCombinedRowPacketAmbientSet packet ∩
    {shift | ∀ x : row × ι, 0 < (packet.1 x.1 + shift x.2).re}

/-- Corresponding chart in the collision-free shift configuration space. -/
def evenCanonicalUpperGoodCombinedRowPacketSet
    {row ι : Type*} [Fintype row] [Fintype ι]
    (packet : InjectiveProjectiveRowPacket row) :
    Set (InjectiveShiftConfiguration ι) :=
  Subtype.val ⁻¹' evenCanonicalUpperGoodCombinedRowPacketAmbientSet packet

/-- Positive-real upper combined-row charts are open in the ambient shift space. -/
theorem evenCanonicalUpperGoodCombinedRowPacketAmbientSet_isOpen
    {row ι : Type*} [Fintype row] [Fintype ι]
    (packet : InjectiveProjectiveRowPacket row) :
    IsOpen (evenCanonicalUpperGoodCombinedRowPacketAmbientSet (ι := ι) packet) := by
  classical
  apply IsOpen.inter
  · exact cauchyUpperGoodCombinedRowPacketAmbientSet_isOpen packet
  · rw [show {shift : ι → ℂ |
        ∀ x : row × ι, 0 < (packet.1 x.1 + shift x.2).re} =
        ⋂ x : row × ι,
          {shift : ι → ℂ | 0 < (packet.1 x.1 + shift x.2).re} by
      ext shift
      simp]
    apply isOpen_iInter_of_finite
    intro x
    have hcont : Continuous
        (fun shift : ι → ℂ => (packet.1 x.1 + shift x.2).re) :=
      Complex.continuous_re.comp
        (continuous_const.add (continuous_apply x.2))
    exact isOpen_lt continuous_const hcont

/-- Positive-real upper combined-row charts are open in collision-free configuration space. -/
theorem evenCanonicalUpperGoodCombinedRowPacketSet_isOpen
    {row ι : Type*} [Fintype row] [Fintype ι]
    (packet : InjectiveProjectiveRowPacket row) :
    IsOpen (evenCanonicalUpperGoodCombinedRowPacketSet (ι := ι) packet) :=
  (evenCanonicalUpperGoodCombinedRowPacketAmbientSet_isOpen
    (ι := ι) packet).preimage continuous_subtype_val

/-- An injective packet in the positive-real half-plane is separated from its `-conj` image. -/
theorem positiveRealUpperNodes_evenSeparated
    {α : Type*} (x : α → ℂ)
    (hinj : Function.Injective x)
    (hreal : ∀ i, 0 < (x i).re) :
    EvenNodeSeparated x := by
  intro q q' hqq'
  cases q with
  | inl i =>
      cases q' with
      | inl j =>
          exact congrArg Sum.inl (hinj hqq')
      | inr j =>
          have hre := congrArg Complex.re hqq'
          simp [evenUpperNodePair] at hre
          have hi := hreal i
          have hj := hreal j
          linarith
  | inr i =>
      cases q' with
      | inl j =>
          have hre := congrArg Complex.re hqq'
          simp [evenUpperNodePair] at hre
          have hi := hreal i
          have hj := hreal j
          linarith
      | inr j =>
          apply congrArg Sum.inr
          apply hinj
          have h := congrArg
            (fun z : ℂ => -(starRingEnd ℂ) z) hqq'
          simpa [evenUpperNodePair] using h

/-- Every collision-free shift tuple belongs to a positive-real upper combined-row chart. -/
theorem injectiveShiftConfigurations_covered_by_evenCanonicalUpperGoodCombinedRowPackets
    {row ι : Type*} [Fintype row] [Fintype ι] :
    Set.univ ⊆ ⋃ packet : InjectiveProjectiveRowPacket row,
      evenCanonicalUpperGoodCombinedRowPacketSet (ι := ι) packet := by
  classical
  intro shift _
  obtain ⟨offset, hoffset, hcombined⟩ :=
    exists_rowOffsets_combined_injective
      (row := row) (ι := ι) shift.1 shift.2
  obtain ⟨H, hH⟩ := finite_complex_family_has_imaginary_lower_bound
    (fun x : row × ι => offset x.1 + shift.1 x.2)
  obtain ⟨R, hR⟩ := finite_complex_family_has_imaginary_lower_bound
    (fun x : row × ι => Complex.I *
      (offset x.1 + shift.1 x.2))
  let z : ℂ := ⟨R + 1, H + 1⟩
  let rowBase : row → ℂ := fun r => z + offset r
  have hrowBase : Function.Injective rowBase := by
    intro r s hrs
    apply hoffset
    apply add_left_cancel (a := z)
    simpa [rowBase] using hrs
  let packet : InjectiveProjectiveRowPacket row := ⟨rowBase, hrowBase⟩
  apply Set.mem_iUnion.mpr
  refine ⟨packet, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hcombined
      apply add_left_cancel (a := z)
      simpa [combinedProjectiveRowShiftPacket, packet, rowBase, add_assoc]
        using hxy
    · intro x
      have hx := hH x
      change 0 < (z + offset x.1 + shift.1 x.2).im
      simp only [Complex.add_im]
      change 0 < (H + 1) + (offset x.1).im + (shift.1 x.2).im
      have hx' : -((offset x.1).im + (shift.1 x.2).im) ≤ H := by
        simpa only [Complex.add_im] using hx
      linarith
  · intro x
    have hx := hR x
    change 0 < (z + offset x.1 + shift.1 x.2).re
    simp only [Complex.add_re]
    change 0 < (R + 1) + (offset x.1).re + (shift.1 x.2).re
    have hx' : -((offset x.1).re + (shift.1 x.2).re) ≤ R := by
      simpa only [Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_add, Complex.add_re] using hx
    linarith

/-- Every compact collision-free shift patch has a finite compact refinement subordinate to
positive-real upper combined-row charts. -/
theorem compact_injectiveShiftPatch_finite_evenCanonicalUpperGoodCombinedRowPacket_refinement
    {row ι : Type*} [Fintype row] [Fintype ι]
    {K : Set (InjectiveShiftConfiguration ι)} (hK : IsCompact K) :
    ∃ n : ℕ, ∃ packets : Fin n → InjectiveProjectiveRowPacket row,
      ∃ pieces : Fin n → Set (InjectiveShiftConfiguration ι),
        K ⊆ ⋃ j, pieces j ∧
        (∀ j, IsCompact (pieces j)) ∧
        ∀ j, pieces j ⊆
          evenCanonicalUpperGoodCombinedRowPacketSet
            (ι := ι) (packets j) := by
  classical
  obtain ⟨packetFinset, hpacketFinset⟩ := hK.elim_finite_subcover
    (fun packet : InjectiveProjectiveRowPacket row =>
      evenCanonicalUpperGoodCombinedRowPacketSet (ι := ι) packet)
    (fun packet =>
      evenCanonicalUpperGoodCombinedRowPacketSet_isOpen
        (ι := ι) packet)
    (Set.Subset.trans (Set.subset_univ K)
      (injectiveShiftConfigurations_covered_by_evenCanonicalUpperGoodCombinedRowPackets
        (row := row) (ι := ι)))
  let n := packetFinset.card
  let e : Fin n ≃ {packet // packet ∈ packetFinset} :=
    by simpa [n] using
      (Fintype.equivFin {packet // packet ∈ packetFinset}).symm
  let packets : Fin n → InjectiveProjectiveRowPacket row :=
    fun j => (e j).1
  let cover : Fin n → Set (InjectiveShiftConfiguration ι) := fun j =>
    evenCanonicalUpperGoodCombinedRowPacketSet
      (ι := ι) (packets j)
  have hcover : K ⊆ ⋃ j, cover j := by
    intro shift hshift
    have hs := hpacketFinset hshift
    simp only [Set.mem_iUnion] at hs
    obtain ⟨packet, hpacketMem, hgood⟩ := hs
    let j : Fin n := e.symm ⟨packet, hpacketMem⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change shift ∈ evenCanonicalUpperGoodCombinedRowPacketSet
      (ι := ι) (packets j)
    simpa [packets, j] using hgood
  obtain ⟨v, hKv, hvclosed, hvsub⟩ :=
    exists_subset_iUnion_closed_subset hK.isClosed
      (fun j =>
        evenCanonicalUpperGoodCombinedRowPacketSet_isOpen
          (ι := ι) (packets j))
      (fun _ _ => Set.toFinite _) hcover
  let pieces : Fin n → Set (InjectiveShiftConfiguration ι) :=
    fun j => K ∩ v j
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
