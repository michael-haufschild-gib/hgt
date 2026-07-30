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

/-- An ordered packet of distinct complex evaluation rows. -/
abbrev InjectiveProjectiveRowPacket (row : Type*) :=
  {z : row → ℂ // Function.Injective z}

/-- Every finite collision-free shift packet admits row offsets for which the complete
row-by-shift source-node packet is collision-free.  The construction spaces rows farther apart
than twice the total norm of the original shift packet. -/
theorem exists_rowOffsets_combined_injective
    {row ι : Type*} [Fintype row] [Fintype ι]
    (shift : ι → ℂ) (hshift : Function.Injective shift) :
    ∃ offset : row → ℂ, Function.Injective offset ∧
      Function.Injective (fun x : row × ι => offset x.1 + shift x.2) := by
  classical
  let e := Fintype.equivFin row
  let S : ℝ := ∑ i, ‖shift i‖
  let M : ℝ := 2 * S + 1
  let offset : row → ℂ := fun r => (M * ((e r).1 : ℝ) : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hM : 0 < M := by dsimp [M]; linarith
  have hcoord : Function.Injective (fun r : row => (e r).1) := by
    intro r s hrs
    exact e.injective (Fin.ext hrs)
  have hoffset : Function.Injective offset := by
    intro r s hrs
    have hrsC : ((M * ((e r).1 : ℝ) : ℝ) : ℂ) =
        ((M * ((e s).1 : ℝ) : ℝ) : ℂ) := by
      simpa [offset] using hrs
    have hrsR : M * ((e r).1 : ℝ) = M * ((e s).1 : ℝ) := by
      exact_mod_cast hrsC
    have : ((e r).1 : ℝ) = ((e s).1 : ℝ) := by nlinarith
    exact hcoord (by exact_mod_cast this)
  refine ⟨offset, hoffset, ?_⟩
  intro x y hxy
  by_cases hr : x.1 = y.1
  · have hi : x.2 = y.2 := by
      apply hshift
      apply add_left_cancel (a := offset x.1)
      simpa [hr] using hxy
    exact Prod.ext hr hi
  · have hidx : (e x.1).1 ≠ (e y.1).1 := fun h => hr (hcoord h)
    have hInt : (((e x.1).1 : ℤ) - ((e y.1).1 : ℤ)) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hidx)
    have hone : 1 ≤ |(((e x.1).1 : ℤ) - ((e y.1).1 : ℤ))| := Int.one_le_abs hInt
    have hoffnorm : M ≤ ‖offset x.1 - offset y.1‖ := by
      rw [show offset x.1 - offset y.1 =
          ((M * (((e x.1).1 : ℤ) - ((e y.1).1 : ℤ)) : ℝ) : ℂ) by
        simp [offset]
        ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hM]
      have honeR : (1 : ℝ) ≤
          |(((((e x.1).1 : ℤ) - ((e y.1).1 : ℤ) : ℤ) : ℝ))| := by
        rw [← Int.cast_abs]
        exact_mod_cast hone
      convert! mul_le_mul_of_nonneg_left honeR hM.le using 1 <;> norm_num
    have hxS : ‖shift x.2‖ ≤ S := by
      apply Finset.single_le_sum (fun _ _ => norm_nonneg _)
      exact Finset.mem_univ _
    have hyS : ‖shift y.2‖ ≤ S := by
      apply Finset.single_le_sum (fun _ _ => norm_nonneg _)
      exact Finset.mem_univ _
    have hshiftNorm : ‖shift y.2 - shift x.2‖ ≤ 2 * S :=
      (norm_sub_le _ _).trans (by linarith)
    have heq : offset x.1 - offset y.1 = shift y.2 - shift x.2 := by
      linear_combination hxy
    rw [heq] at hoffnorm
    have : M ≤ 2 * S := hoffnorm.trans hshiftNorm
    dsimp [M] at this
    linarith

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
    {row ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
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
    ∃ n : ℕ, ∃ packets : Fin n → InjectiveProjectiveRowPacket row,
      ∃ pieces : Fin n → Set (InjectiveShiftConfiguration ι),
        K ⊆ ⋃ j, pieces j ∧
        (∀ j, IsCompact (pieces j)) ∧
        ∀ j, pieces j ⊆ noncriticalProjectiveUpperGoodRowPacketSet
          (ι := ι) (κ := κ) C D forbidden (packets j) := by
  classical
  obtain ⟨packetFinset, hpacketFinset⟩ := hK.elim_finite_subcover
    (fun packet : InjectiveProjectiveRowPacket row =>
      noncriticalProjectiveUpperGoodRowPacketSet
        (ι := ι) (κ := κ) C D forbidden packet)
    (fun packet => noncriticalProjectiveUpperGoodRowPacketSet_isOpen
      hCmin.1 hD forbidden packet)
    (Set.Subset.trans (Set.subset_univ K)
      (injectiveShiftConfigurations_covered_by_noncriticalProjectiveUpperGoodRowPackets
        (row := row) hCmin hD hnoCommon hCp hCc forbidden))
  let n := packetFinset.card
  let e : Fin n ≃ {packet // packet ∈ packetFinset} :=
    by simpa [n] using (Fintype.equivFin {packet // packet ∈ packetFinset}).symm
  let packets : Fin n → InjectiveProjectiveRowPacket row := fun j => (e j).1
  let cover : Fin n → Set (InjectiveShiftConfiguration ι) := fun j =>
    noncriticalProjectiveUpperGoodRowPacketSet
      (ι := ι) (κ := κ) C D forbidden (packets j)
  have hcover : K ⊆ ⋃ j, cover j := by
    intro shift hshift
    have hs := hpacketFinset hshift
    simp only [Set.mem_iUnion] at hs
    obtain ⟨packet, hpacketMem, hgood⟩ := hs
    let j : Fin n := e.symm ⟨packet, hpacketMem⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change shift ∈ noncriticalProjectiveUpperGoodRowPacketSet
      (ι := ι) (κ := κ) C D forbidden (packets j)
    simpa [packets, j] using hgood
  obtain ⟨v, hKv, hvclosed, hvsub⟩ :=
    exists_subset_iUnion_closed_subset hK.isClosed
      (fun j => noncriticalProjectiveUpperGoodRowPacketSet_isOpen
        hCmin.1 hD forbidden (packets j))
      (fun _ _ => Set.toFinite _)
      hcover
  let pieces : Fin n → Set (InjectiveShiftConfiguration ι) := fun j => K ∩ v j
  refine ⟨n, packets, pieces, ?_, ?_, ?_⟩
  · intro shift hshift
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hKv hshift)
    exact Set.mem_iUnion.mpr ⟨j, hshift, hj⟩
  · intro j
    exact hK.inter_right (hvclosed j)
  · intro j
    exact inter_subset_right.trans (hvsub j)

/-- The literal row-by-shift source packet generated by a row packet and a shift configuration. -/
def combinedProjectiveRowShiftPacket
    {row ι : Type*}
    (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι) : row × ι → ℂ :=
  fun x => packet.1 x.1 + shift.1 x.2

/-- A simultaneous packet chart whose single complete certificate is imposed on the entire
`row × shift` node family.  Unlike coordinatewise row charts, this includes separation between
different rows and is therefore the exact chart required by constrained Cauchy controllability. -/
def noncriticalProjectiveUpperGoodCombinedRowPacketSet
    {row ι κ : Type*} [Fintype row]
    [Fintype ι] [DecidableEq (row × ι)] [Fintype κ]
    (C D : ℂ → ℂ) (forbidden : κ → ℂ)
    (packet : InjectiveProjectiveRowPacket row) :
    Set (InjectiveShiftConfiguration ι) :=
  {shift |
    noncriticalProjectiveSeparationProduct C D
      (combinedProjectiveRowShiftPacket packet shift) forbidden 0 ≠ 0} ∩
    {shift | ∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im}

/-- Complete combined row-packet charts are open in the collision-free shift space. -/
theorem noncriticalProjectiveUpperGoodCombinedRowPacketSet_isOpen
    {row ι κ : Type*} [Fintype row]
    [Fintype ι] [DecidableEq (row × ι)] [Fintype κ]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (forbidden : κ → ℂ) (packet : InjectiveProjectiveRowPacket row) :
    IsOpen (noncriticalProjectiveUpperGoodCombinedRowPacketSet
      (ι := ι) (κ := κ) C D forbidden packet) := by
  apply IsOpen.inter
  · have hpacket : Continuous
        (fun shift : InjectiveShiftConfiguration ι =>
          combinedProjectiveRowShiftPacket packet shift) := by
      apply continuous_pi
      intro x
      exact continuous_const.add ((continuous_apply x.2).comp continuous_subtype_val)
    have hcertificate : Continuous
        (fun shift : InjectiveShiftConfiguration ι =>
          noncriticalProjectiveSeparationProduct C D
            (combinedProjectiveRowShiftPacket packet shift) forbidden 0) :=
      (continuous_noncriticalProjectiveSeparationProduct_configuration
        hC hD forbidden 0).comp hpacket
    exact hcertificate.isOpen_preimage {w : ℂ | w ≠ 0} isOpen_ne
  · rw [show {shift : InjectiveShiftConfiguration ι |
        ∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im} =
        ⋂ x, {shift : InjectiveShiftConfiguration ι |
          0 < (combinedProjectiveRowShiftPacket packet shift x).im} by
      ext shift
      simp]
    apply isOpen_iInter_of_finite
    intro x
    have hcont : Continuous (fun shift : InjectiveShiftConfiguration ι =>
        (combinedProjectiveRowShiftPacket packet shift x).im) :=
      Complex.continuous_im.comp
        (continuous_const.add ((continuous_apply x.2).comp continuous_subtype_val))
    exact isOpen_lt continuous_const hcont

/-- Every collision-free shift configuration lies in a complete combined row-packet chart.  The
proof first creates widely separated row offsets, regards `row × shift` as one injective finite
packet, and then applies the nonzero entire certificate once to that combined packet. -/
theorem injectiveShiftConfigurations_covered_by_noncriticalProjectiveUpperGoodCombinedRowPackets
    {row ι κ : Type*} [Fintype row]
    [Fintype ι] [DecidableEq (row × ι)] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (forbidden : κ → ℂ) :
    Set.univ ⊆ ⋃ packet : InjectiveProjectiveRowPacket row,
      noncriticalProjectiveUpperGoodCombinedRowPacketSet
        (ι := ι) (κ := κ) C D forbidden packet := by
  intro shift hshift
  obtain ⟨offset, hoffset, hcombined⟩ :=
    exists_rowOffsets_combined_injective (row := row) (ι := ι) shift.1 shift.2
  let combined : InjectiveShiftConfiguration (row × ι) :=
    ⟨fun x => offset x.1 + shift.1 x.2, hcombined⟩
  have hinfinite := noncriticalProjectiveUpperGoodRows_infinite
    (ι := row × ι) hCmin hD hnoCommon hCp hCc forbidden combined
  obtain ⟨z, hzgood, hzupper⟩ := hinfinite.nonempty
  let rowBase : row → ℂ := fun r => z + offset r
  have hrowBase : Function.Injective rowBase := by
    intro r s hrs
    apply hoffset
    apply add_left_cancel (a := z)
    exact hrs
  let packet : InjectiveProjectiveRowPacket row := ⟨rowBase, hrowBase⟩
  apply Set.mem_iUnion.mpr
  refine ⟨packet, ?_⟩
  constructor
  · simpa [noncriticalProjectiveGoodRowSet, noncriticalProjectiveSeparationProduct,
      projectiveForbiddenSeparationProduct, projectiveSeparationProduct,
      projectiveShiftCollision, combinedProjectiveRowShiftPacket,
      packet, rowBase, combined, add_assoc] using hzgood
  · intro x
    simpa [combinedProjectiveRowShiftPacket, packet, rowBase, combined, add_assoc] using
      hzupper x

/-- **Complete compact simultaneous row atlas.**  Every compact collision-free shift patch has a
finite compact refinement subordinate to charts on which the whole row-by-shift packet is regular,
upper, target-separated across all rows, frozen-safe, and noncritical. -/
theorem compact_injectiveShiftPatch_finite_noncriticalProjectiveUpperGoodCombinedRowPacket_refinement
    {row ι κ : Type*} [Fintype row]
    [Fintype ι] [DecidableEq (row × ι)] [Fintype κ]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (forbidden : κ → ℂ)
    {K : Set (InjectiveShiftConfiguration ι)} (hK : IsCompact K) :
    ∃ n : ℕ, ∃ packets : Fin n → InjectiveProjectiveRowPacket row,
      ∃ pieces : Fin n → Set (InjectiveShiftConfiguration ι),
        K ⊆ ⋃ j, pieces j ∧
        (∀ j, IsCompact (pieces j)) ∧
        ∀ j, pieces j ⊆ noncriticalProjectiveUpperGoodCombinedRowPacketSet
          (ι := ι) (κ := κ) C D forbidden (packets j) := by
  classical
  obtain ⟨packetFinset, hpacketFinset⟩ := hK.elim_finite_subcover
    (fun packet : InjectiveProjectiveRowPacket row =>
      noncriticalProjectiveUpperGoodCombinedRowPacketSet
        (ι := ι) (κ := κ) C D forbidden packet)
    (fun packet => noncriticalProjectiveUpperGoodCombinedRowPacketSet_isOpen
      hCmin.1 hD forbidden packet)
    (Set.Subset.trans (Set.subset_univ K)
      (injectiveShiftConfigurations_covered_by_noncriticalProjectiveUpperGoodCombinedRowPackets
        (row := row) hCmin hD hnoCommon hCp hCc forbidden))
  let n := packetFinset.card
  let e : Fin n ≃ {packet // packet ∈ packetFinset} :=
    by simpa [n] using (Fintype.equivFin {packet // packet ∈ packetFinset}).symm
  let packets : Fin n → InjectiveProjectiveRowPacket row := fun j => (e j).1
  let cover : Fin n → Set (InjectiveShiftConfiguration ι) := fun j =>
    noncriticalProjectiveUpperGoodCombinedRowPacketSet
      (ι := ι) (κ := κ) C D forbidden (packets j)
  have hcover : K ⊆ ⋃ j, cover j := by
    intro shift hshift
    have hs := hpacketFinset hshift
    simp only [Set.mem_iUnion] at hs
    obtain ⟨packet, hpacketMem, hgood⟩ := hs
    let j : Fin n := e.symm ⟨packet, hpacketMem⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change shift ∈ noncriticalProjectiveUpperGoodCombinedRowPacketSet
      (ι := ι) (κ := κ) C D forbidden (packets j)
    simpa [packets, j] using hgood
  obtain ⟨v, hKv, hvclosed, hvsub⟩ :=
    exists_subset_iUnion_closed_subset hK.isClosed
      (fun j => noncriticalProjectiveUpperGoodCombinedRowPacketSet_isOpen
        hCmin.1 hD forbidden (packets j))
      (fun _ _ => Set.toFinite _)
      hcover
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
