import GaloisForLFunctions.HTGeometry.CompactNoncriticalProjectiveSeparationAtlas
import GaloisForLFunctions.HTGeometry.PolynomialRelationDetector
import Mathlib.Topology.ShrinkingLemma

/-!
# Simultaneous multi-row regular atlases on compact shift patches

Transversality needs more than one good evaluation row.  For every finite row type, this module
selects an injective packet of rows which are simultaneously regular, target-separated,
frozen-safe, noncritical, and whose translated source nodes lie in the upper half-plane.  The
packet charts cover the full collision-free shift space.  On a compact patch, the finite open
cover is shrunk to a finite compact cover subordinate to those charts.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set Topology
open scoped BigOperators

noncomputable section

/-- An ordered finite packet of distinct complex evaluation rows. -/
abbrev InjectiveProjectiveRowPacket (row : Type*) [Fintype row] :=
  {z : row → ℂ // Function.Injective z}

/-- A row is upper-good when its complete projective certificate is nonzero and every translated
source node lies in the upper half-plane. -/
def noncriticalProjectiveUpperGoodRowSet
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (C D : ℂ → ℂ) (forbidden : κ → ℂ) (z : ℂ) :
    Set (InjectiveShiftConfiguration ι) :=
  noncriticalProjectiveGoodRowSet (ι := ι) (κ := κ) C D forbidden z ∩
    {shift | ∀ i, 0 < (z + shift.1 i).im}

/-- The upper-good configurations for a fixed row form an open set. -/
theorem noncriticalProjectiveUpperGoodRowSet_isOpen
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (forbidden : κ → ℂ) (z : ℂ) :
    IsOpen (noncriticalProjectiveUpperGoodRowSet
      (ι := ι) (κ := κ) C D forbidden z) := by
  apply (noncriticalProjectiveGoodRowSet_isOpen
    (ι := ι) (κ := κ) hC hD forbidden z).inter
  rw [show {shift : InjectiveShiftConfiguration ι | ∀ i, 0 < (z + shift.1 i).im} =
      ⋂ i, {shift : InjectiveShiftConfiguration ι | 0 < (z + shift.1 i).im} by
    ext shift
    simp]
  apply isOpen_iInter_of_finite
  intro i
  have hcont : Continuous
      (fun shift : InjectiveShiftConfiguration ι => (z + shift.1 i).im) := by
    exact Complex.continuous_im.comp
      (continuous_const.add ((continuous_apply i).comp continuous_subtype_val))
  exact isOpen_lt continuous_const hcont

/-- For one collision-free shift configuration, upper-good rows are unbounded in imaginary
height and therefore infinite. -/
theorem noncriticalProjectiveUpperGoodRows_infinite
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (forbidden : κ → ℂ) (shift : InjectiveShiftConfiguration ι) :
    {z : ℂ | shift ∈ noncriticalProjectiveUpperGoodRowSet
      (ι := ι) (κ := κ) C D forbidden z}.Infinite := by
  obtain ⟨Hshift, hHshift⟩ :=
    finite_complex_family_has_imaginary_lower_bound shift.1
  intro hfinite
  have himageFinite :
      ((fun z : ℂ => z.im) ''
        {z : ℂ | shift ∈ noncriticalProjectiveUpperGoodRowSet
          (ι := ι) (κ := κ) C D forbidden z}).Finite :=
    hfinite.image _
  obtain ⟨B, hB⟩ := himageFinite.bddAbove
  let H := max Hshift B
  have hcover := injectiveShiftConfigurations_covered_by_upper_noncriticalProjectiveGoodRows
    (ι := ι) (κ := κ) hCmin hD hnoCommon hCp hCc forbidden H
    (Set.mem_univ shift)
  obtain ⟨z, hzgood⟩ := Set.mem_iUnion.mp hcover
  have hzH : H < z.1.im := z.2
  have hzupper : ∀ i, 0 < (z.1 + shift.1 i).im := by
    intro i
    rw [Complex.add_im]
    have hshift := hHshift i
    have hrow : Hshift < z.1.im := (le_max_left _ _).trans_lt hzH
    linarith
  have hzmem : z.1 ∈ {w : ℂ | shift ∈ noncriticalProjectiveUpperGoodRowSet
      (ι := ι) (κ := κ) C D forbidden w} :=
    ⟨hzgood, hzupper⟩
  have hzle : z.1.im ≤ B := hB ⟨z.1, hzmem, rfl⟩
  have hBlt : B < z.1.im := (le_max_right _ _).trans_lt hzH
  exact (not_lt_of_ge hzle) hBlt

/-- Every finite row type can be filled by distinct rows which are all upper-good for one fixed
configuration. -/
theorem exists_noncriticalProjectiveUpperGoodRowPacket
    {row ι κ : Type*} [Fintype row]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (forbidden : κ → ℂ) (shift : InjectiveShiftConfiguration ι) :
    ∃ packet : InjectiveProjectiveRowPacket row,
      ∀ r, shift ∈ noncriticalProjectiveUpperGoodRowSet
        (ι := ι) (κ := κ) C D forbidden (packet.1 r) := by
  let good : Set ℂ :=
    {z | shift ∈ noncriticalProjectiveUpperGoodRowSet
      (ι := ι) (κ := κ) C D forbidden z}
  have hgood : good.Infinite :=
    noncriticalProjectiveUpperGoodRows_infinite
      hCmin hD hnoCommon hCp hCc forbidden shift
  letI : Infinite good := hgood.to_subtype
  let e : ℕ ↪ good := Infinite.natEmbedding good
  let rows : row → ℂ := fun r =>
    (e (Fintype.equivFin row r).val).1
  have hrows : Function.Injective rows := by
    intro r s hrs
    apply (Fintype.equivFin row).injective
    apply Fin.ext
    apply e.injective
    apply Subtype.ext
    exact hrs
  refine ⟨⟨rows, hrows⟩, ?_⟩
  intro r
  exact (e (Fintype.equivFin row r).val).2

/-- Configurations on which every row of a fixed packet is upper-good. -/
def noncriticalProjectiveUpperGoodRowPacketSet
    {row ι κ : Type*} [Fintype row]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (C D : ℂ → ℂ) (forbidden : κ → ℂ)
    (packet : InjectiveProjectiveRowPacket row) :
    Set (InjectiveShiftConfiguration ι) :=
  ⋂ r, noncriticalProjectiveUpperGoodRowSet
    (ι := ι) (κ := κ) C D forbidden (packet.1 r)

/-- Each simultaneous row-packet chart is open. -/
theorem noncriticalProjectiveUpperGoodRowPacketSet_isOpen
    {row ι κ : Type*} [Fintype row]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (forbidden : κ → ℂ) (packet : InjectiveProjectiveRowPacket row) :
    IsOpen (noncriticalProjectiveUpperGoodRowPacketSet
      (ι := ι) (κ := κ) C D forbidden packet) := by
  apply isOpen_iInter_of_finite
  intro r
  exact noncriticalProjectiveUpperGoodRowSet_isOpen hC hD forbidden (packet.1 r)

/-- Simultaneous upper-good row-packet charts cover the full collision-free shift space. -/
theorem injectiveShiftConfigurations_covered_by_noncriticalProjectiveUpperGoodRowPackets
    {row ι κ : Type*} [Fintype row]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (forbidden : κ → ℂ) :
    Set.univ ⊆ ⋃ packet : InjectiveProjectiveRowPacket row,
      noncriticalProjectiveUpperGoodRowPacketSet
        (ι := ι) (κ := κ) C D forbidden packet := by
  intro shift hshift
  obtain ⟨packet, hpacket⟩ := exists_noncriticalProjectiveUpperGoodRowPacket
    (row := row) hCmin hD hnoCommon hCp hCc forbidden shift
  apply Set.mem_iUnion.mpr
  refine ⟨packet, ?_⟩
  exact Set.mem_iInter.mpr fun r => hpacket r

set_option maxHeartbeats 0 in
/-- **Compact simultaneous row atlas with compact subordinate pieces.**  A compact shift patch is
covered by finitely many compact pieces, each contained in one open simultaneous row-packet chart.
The closed shrinking is what permits finitely many patchwise density statements to be intersected
without losing points on chart boundaries. -/
theorem compact_injectiveShiftPatch_finite_noncriticalProjectiveUpperGoodRowPacket_refinement
    {row ι κ : Type*} [Fintype row]
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (forbidden : κ → ℂ)
    {K : Set (InjectiveShiftConfiguration ι)} (hK : IsCompact K) :
    ∃ packets : Finset (InjectiveProjectiveRowPacket row),
      ∃ pieces : packets → Set (InjectiveShiftConfiguration ι),
        K ⊆ ⋃ j, pieces j ∧
        (∀ j, IsCompact (pieces j)) ∧
        ∀ j, pieces j ⊆ noncriticalProjectiveUpperGoodRowPacketSet
          (ι := ι) (κ := κ) C D forbidden j.1 := by
  obtain ⟨packets, hpackets⟩ := hK.elim_finite_subcover
    (fun packet : InjectiveProjectiveRowPacket row =>
      noncriticalProjectiveUpperGoodRowPacketSet
        (ι := ι) (κ := κ) C D forbidden packet)
    (fun packet => noncriticalProjectiveUpperGoodRowPacketSet_isOpen
      hCmin.1 hD forbidden packet)
    (Set.Subset.trans (Set.subset_univ K)
      (injectiveShiftConfigurations_covered_by_noncriticalProjectiveUpperGoodRowPackets
        (row := row) hCmin hD hnoCommon hCp hCc forbidden))
  let cover : packets → Set (InjectiveShiftConfiguration ι) := fun j =>
    noncriticalProjectiveUpperGoodRowPacketSet
      (ι := ι) (κ := κ) C D forbidden j.1
  have hcover : K ⊆ ⋃ j, cover j := by
    intro shift hshift
    have hs := hpackets hshift
    simp only [Set.mem_iUnion] at hs ⊢
    obtain ⟨packet, hpacketMem, hgood⟩ := hs
    exact ⟨⟨packet, hpacketMem⟩, hgood⟩
  obtain ⟨v, hKv, hvclosed, hvsub⟩ :=
    exists_subset_iUnion_closed_subset hK.isClosed
      (fun j => noncriticalProjectiveUpperGoodRowPacketSet_isOpen
        hCmin.1 hD forbidden j.1)
      (fun _ _ => Set.toFinite _)
      hcover
  let pieces : packets → Set (InjectiveShiftConfiguration ι) := fun j => K ∩ v j
  refine ⟨packets, pieces, ?_, ?_, ?_⟩
  · intro shift hshift
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hKv hshift)
    exact Set.mem_iUnion.mpr ⟨j, hshift, hj⟩
  · intro j
    exact hK.inter_right (hvclosed j)
  · intro j
    exact inter_subset_right.trans (hvsub j)

end

end GaloisForLFunctions.HTGeometry
