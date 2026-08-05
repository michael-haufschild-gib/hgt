import GaloisForLFunctions.HTGeometry.SpacedRayNodePacket
import GaloisForLFunctions.HTGeometry.MovingCanonicalFullTranslationRankGenericity

/-!
# The expanded full-rank witness, for every phase

The translation-rank interface asks for one row packet whose row-by-shift family is collision-free,
lies in the open upper half-plane, and has full expanded rank.  The blow-up machinery now supplies
all three at once, and it supplies them for *every* parameter sequence rather than for a residual
set of them.

The reindexing is bookkeeping: the packet value of the interface is, coordinate by coordinate, the
jet of order `(e.symm c).2` at the node shifted by `shift (e.symm c).1`, where `e` enumerates the
combined jet index `Σ i, Fin (orders i)`.  That identity holds definitionally.

The conditions that remain are conditions on the configuration, not on the carrier: the distinguished
shift must have strictly least imaginary part, the exponent box must rise on the ground fibre and
fall off it, and the row type must be large enough to hold the sampled minor.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ## Reindexing the combined jets -/

/-- The shift slot of a combined jet coordinate. -/
noncomputable def combinedJetIndex {ι : Type*} [Fintype ι] (orders : ι → ℕ)
    (c : Fin (Fintype.card (Σ i, Fin (orders i)))) : ι :=
  (((Fintype.equivFin (Σ i, Fin (orders i))).symm c)).1

/-- The differentiation order of a combined jet coordinate. -/
noncomputable def combinedJetOrder {ι : Type*} [Fintype ι] (orders : ι → ℕ)
    (c : Fin (Fintype.card (Σ i, Fin (orders i)))) : ℕ :=
  (((Fintype.equivFin (Σ i, Fin (orders i))).symm c).2 : ℕ)

/-- The interface's packet value is the translated jet of the recorded order. -/
theorem movingCanonicalExpandedPacketValue_apply {row ι : Type} [Fintype row] [DecidableEq row]
    [Fintype ι] [DecidableEq ι] (orders : ι → ℕ) (packet : InjectiveProjectiveRowPacket row)
    (θ : BoundedRealSequence) (shift : InjectiveShiftConfiguration ι)
    (p : row × Fin (Fintype.card (Σ i, Fin (orders i)))) :
    movingCanonicalExpandedPacketValue orders packet θ shift p
      = iteratedDeriv (combinedJetOrder orders p.2) (movingCanonicalLogDerivative θ)
          (packet.1 p.1 + shift.1 (combinedJetIndex orders p.2)) := rfl

/-! ## Thresholds of a finite shift family -/

/-- The least distance between two distinct shifts. -/
noncomputable def shiftSeparation {ι : Type*} [Fintype ι] [DecidableEq ι] (shift : ι → ℂ) : ℝ :=
  if h : (Finset.univ.filter fun p : ι × ι => p.1 ≠ p.2).Nonempty then
    (Finset.univ.filter fun p : ι × ι => p.1 ≠ p.2).inf' h (fun p => ‖shift p.1 - shift p.2‖)
  else 1

theorem shiftSeparation_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {shift : ι → ℂ}
    (hinj : Function.Injective shift) : 0 < shiftSeparation shift := by
  classical
  rw [shiftSeparation]
  split
  · rename_i h
    rw [Finset.lt_inf'_iff]
    intro p hp
    have hne : p.1 ≠ p.2 := by simpa using hp
    exact norm_pos_iff.mpr (sub_ne_zero.mpr fun hc => hne (hinj hc))
  · norm_num

theorem shiftSeparation_le {ι : Type*} [Fintype ι] [DecidableEq ι] (shift : ι → ℂ)
    {i i' : ι} (hii : i ≠ i') : shiftSeparation shift ≤ ‖shift i - shift i'‖ := by
  classical
  have hmem : (i, i') ∈ (Finset.univ.filter fun p : ι × ι => p.1 ≠ p.2) := by
    simp [hii]
  rw [shiftSeparation, dif_pos ⟨(i, i'), hmem⟩]
  exact Finset.inf'_le _ hmem

/-- An integer spacing beyond the diameter of the shift family. -/
noncomputable def shiftSpread {ι : Type*} [Fintype ι] (shift : ι → ℂ) : ℕ :=
  ⌈(∑ i : ι, ∑ i' : ι, ‖shift i - shift i'‖) + 1⌉₊

theorem sum_norm_shift_nonneg {ι : Type*} [Fintype ι] (shift : ι → ℂ) :
    0 ≤ ∑ i : ι, ∑ i' : ι, ‖shift i - shift i'‖ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem shiftSpread_pos {ι : Type*} [Fintype ι] (shift : ι → ℂ) : 0 < shiftSpread shift := by
  have hB := sum_norm_shift_nonneg shift
  have hle := Nat.le_ceil ((∑ i : ι, ∑ i' : ι, ‖shift i - shift i'‖) + 1)
  have : (0 : ℝ) < (shiftSpread shift : ℝ) := by
    rw [shiftSpread]
    linarith
  exact_mod_cast this

theorem norm_sub_le_shiftSpread {ι : Type*} [Fintype ι] (shift : ι → ℂ) (i i' : ι) :
    ‖shift i - shift i'‖ ≤ (shiftSpread shift : ℝ) - 1 / 2 := by
  have hinner : ‖shift i - shift i'‖ ≤ ∑ j : ι, ‖shift i - shift j‖ :=
    Finset.single_le_sum (f := fun j => ‖shift i - shift j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ i')
  have houter : (∑ j : ι, ‖shift i - shift j‖)
      ≤ ∑ k : ι, ∑ j : ι, ‖shift k - shift j‖ :=
    Finset.single_le_sum (f := fun k => ∑ j : ι, ‖shift k - shift j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hle := Nat.le_ceil ((∑ k : ι, ∑ j : ι, ‖shift k - shift j‖) + 1)
  rw [shiftSpread]
  linarith

/-! ## Packets that meet every interface condition -/

set_option maxHeartbeats 1000000 in
/-- **A node packet meeting every condition of the translation-rank interface.**  The jets are
grouped by their shift slots; the distinguished slot has strictly least imaginary part; the box
rises on that slot's fibre and falls off it. -/
theorem exists_row_packet_spacedRays_combined
    {κ row ι : Type*} [Fintype κ] [DecidableEq κ] [LinearOrder κ] [Fintype row]
    [Fintype ι] [DecidableEq ι] {n q : ℕ}
    (θ : BoundedRealSequence) (m : Fin n → ℕ) (idx : Fin n → ι) (shift : ι → ℂ) (k₀ : Fin n)
    (exponent : κ → (Fin n →₀ ℕ))
    (hshiftinj : Function.Injective shift)
    (hmin : ∀ i : ι, i ≠ idx k₀ → (shift (idx k₀)).im < (shift i).im)
    (hmono : ∀ k, idx k = idx k₀ → Monotone fun a => exponent a k)
    (hanti : ∀ k, idx k ≠ idx k₀ → Antitone fun a => exponent a k)
    (hstrict : StrictMono fun a => exponent a k₀)
    (f : κ × Fin (q + 1) → row) (hf : Function.Injective f) :
    ∃ z : row → ℂ, Function.Injective z ∧
      Function.Injective (fun x : row × ι => z x.1 + shift x.2) ∧
      (∀ x : row × ι, 0 < (z x.1 + shift x.2).im) ∧
      Function.Injective (expandedDifferentialEvaluationMatrix q n z exponent
        (fun p => iteratedDeriv (m p.2) (movingCanonicalLogDerivative θ)
          (z p.1 + shift (idx p.2)))).mulVec := by
  classical
  set ε : ℝ := shiftSeparation shift with hεdef
  set K : ℕ := shiftSpread shift with hKdef
  have hε : 0 < ε := shiftSeparation_pos hshiftinj
  have hK : 0 < K := shiftSpread_pos shift
  have hidx : ∀ k, shift (idx k) = shift (idx k₀) → idx k = idx k₀ :=
    fun k h => hshiftinj h
  have hshiftσ : ∀ k, shift (idx k) ≠ shift (idx k₀) →
      (shift (idx k₀)).im < (shift (idx k)).im := by
    intro k hk
    exact hmin (idx k) fun hc => hk (by rw [hc])
  have hmonoσ : ∀ k, shift (idx k) = shift (idx k₀) → Monotone fun a => exponent a k :=
    fun k hk => hmono k (hidx k hk)
  have hantiσ : ∀ k, shift (idx k) ≠ shift (idx k₀) → Antitone fun a => exponent a k :=
    fun k hk => hanti k fun hc => hk (by rw [hc])
  have hzero : ∀ ζ ∈ spacedRayBase θ (shift (idx k₀)) K, ∃ p : ℕ,
      ζ = (movingCanonicalZero θ p : ℂ) - shift (idx k₀) := by
    rintro ζ ⟨j, rfl⟩
    exact ⟨j * K, rfl⟩
  obtain ⟨z, hzmem, hzinj, hrank⟩ := exists_row_packet_in_set_minimalShiftGroup_signedBox
    (κ := κ) (row := row) (q := q)
    (S := spacedRayNodes θ (shift (idx k₀)) K ε) (Z := spacedRayBase θ (shift (idx k₀)) K) (ε := ε)
    θ m (fun k => shift (idx k)) k₀ exponent hε
    (infinite_spacedRayNodes θ (shift (idx k₀)) hK hε)
    (infinite_spacedRayBase θ (shift (idx k₀)) hK)
    (fun ζ hζ => spacedRayNodes_mem_of_base θ (shift (idx k₀)) K hζ) hzero
    hshiftσ hmonoσ hantiσ hstrict f hf
  refine ⟨z, hzinj, ?_, ?_, hrank⟩
  · exact injective_combined_of_spacedRayNodes θ (shift (idx k₀)) hK z hzmem hzinj shift
      hshiftinj (fun i i' hii => shiftSeparation_le shift hii)
      (fun i i' => norm_sub_le_shiftSpread shift i i')
  · rintro ⟨b, i⟩
    have hb := spacedRayNodes_im_lt (hzmem b)
    show 0 < (z b + shift i).im
    rw [Complex.add_im]
    rcases eq_or_ne i (idx k₀) with rfl | hi
    · linarith
    · have := hmin i hi
      linarith

/-! ## The interface, discharged for every phase -/

set_option maxHeartbeats 1000000 in
/-- **The expanded full-rank witness holds for every parameter sequence.**  No genericity in `θ` is
needed: the blow-up at the carrier's own zeros produces the packet directly.  The hypotheses are
conditions on the interface's configuration — a strictly lowest shift slot, a box rising on that
slot's fibre and falling off it, and a row type large enough for the sampled minor. -/
theorem movingCanonicalExpandedFullRankWitness_of_strictMinimalShift
    {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ] [LinearOrder κ]
    [Fintype ι] [DecidableEq ι]
    (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (θ : BoundedRealSequence) (shift : InjectiveShiftConfiguration ι)
    (k₀ : Fin (Fintype.card (Σ i, Fin (orders i))))
    (hmin : ∀ i : ι, i ≠ combinedJetIndex orders k₀ →
      (shift.1 (combinedJetIndex orders k₀)).im < (shift.1 i).im)
    (hmono : ∀ k, combinedJetIndex orders k = combinedJetIndex orders k₀ →
      Monotone fun a => exponent a k)
    (hanti : ∀ k, combinedJetIndex orders k ≠ combinedJetIndex orders k₀ →
      Antitone fun a => exponent a k)
    (hstrict : StrictMono fun a => exponent a k₀)
    (f : κ × Fin (degree + 1) → row) (hf : Function.Injective f) :
    movingCanonicalExpandedFullRankWitness (row := row) (κ := κ)
      degree orders exponent θ shift := by
  classical
  obtain ⟨z, hzinj, hcomb, hupper, hrank⟩ := exists_row_packet_spacedRays_combined
    (κ := κ) (row := row) (ι := ι) (q := degree)
    θ (combinedJetOrder orders) (combinedJetIndex orders) shift.1 k₀ exponent
    shift.2 hmin hmono hanti hstrict f hf
  exact ⟨⟨z, hzinj⟩, hcomb, hupper, hrank⟩


/-! ## A closed instance -/

/-- The coordinate of a chosen jet in a chosen shift slot. -/
noncomputable def groundJetCoordinate {ι : Type*} [Fintype ι] (orders : ι → ℕ) (i₀ : ι)
    (j : Fin (orders i₀)) : Fin (Fintype.card (Σ i, Fin (orders i))) :=
  Fintype.equivFin (Σ i, Fin (orders i)) ⟨i₀, j⟩

@[simp] theorem combinedJetIndex_groundJetCoordinate {ι : Type*} [Fintype ι] (orders : ι → ℕ)
    (i₀ : ι) (j : Fin (orders i₀)) :
    combinedJetIndex orders (groundJetCoordinate orders i₀ j) = i₀ := by
  simp [combinedJetIndex, groundJetCoordinate]

/-- Shifts at the integer heights, as an injective configuration. -/
noncomputable def integerShiftConfiguration (n : ℕ) : InjectiveShiftConfiguration (Fin (n + 1)) :=
  ⟨integerHeightShift n, integerHeightShift_injective n⟩

/-- The box climbing on the ground fibre and descending on every other. -/
noncomputable def groundFibreBox {ι : Type*} [Fintype ι] [DecidableEq ι] (orders : ι → ℕ)
    (i₀ : ι) (N : ℕ) (a : Fin (N + 1)) : (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm
    (fun k => if combinedJetIndex orders k = i₀ then (a : ℕ) else N - (a : ℕ))

@[simp] theorem groundFibreBox_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (orders : ι → ℕ)
    (i₀ : ι) (N : ℕ) (a : Fin (N + 1)) (k : Fin (Fintype.card (Σ i, Fin (orders i)))) :
    groundFibreBox orders i₀ N a k
      = if combinedJetIndex orders k = i₀ then (a : ℕ) else N - (a : ℕ) := by
  simp [groundFibreBox]

set_option maxHeartbeats 1000000 in
/-- **Unconditional.**  For every parameter sequence, height count, jet multiplicities, degree budget
and box size, the expanded full-rank witness of the translation-rank interface holds at the integer
shift configuration and the ground-fibre box.

Every shift slot carries at least one jet, arbitrarily many jets sit on the ground slot, and the
statement has no hypotheses. -/
theorem movingCanonicalExpandedFullRankWitness_integerShifts
    (θ : BoundedRealSequence) (n degree N : ℕ) (orders : Fin (n + 1) → ℕ) :
    movingCanonicalExpandedFullRankWitness
      (row := Fin (N + 1) × Fin (degree + 1)) (κ := Fin (N + 1))
      degree (fun i => orders i + 1)
      (groundFibreBox (fun i => orders i + 1) 0 N) θ (integerShiftConfiguration n) := by
  classical
  set ord : Fin (n + 1) → ℕ := fun i => orders i + 1 with hord
  have hj : (0 : ℕ) < ord 0 := by simp [hord]
  set k₀ : Fin (Fintype.card (Σ i, Fin (ord i))) :=
    groundJetCoordinate ord 0 ⟨0, hj⟩ with hk₀
  have hidx0 : combinedJetIndex ord k₀ = 0 := by
    rw [hk₀]
    exact combinedJetIndex_groundJetCoordinate ord 0 ⟨0, hj⟩
  refine movingCanonicalExpandedFullRankWitness_of_strictMinimalShift
    (row := Fin (N + 1) × Fin (degree + 1)) (κ := Fin (N + 1)) (ι := Fin (n + 1))
    degree ord (groundFibreBox ord 0 N) θ (integerShiftConfiguration n) k₀ ?_ ?_ ?_ ?_
    id Function.injective_id
  · intro i hi
    rw [hidx0] at hi ⊢
    show (integerHeightShift n 0).im < (integerHeightShift n i).im
    rw [integerHeightShift_im, integerHeightShift_im]
    have hpos : 0 < ((i : Fin (n + 1)) : ℕ) := by
      refine Nat.pos_of_ne_zero fun h => hi ?_
      exact Fin.ext h
    have : (0 : ℝ) < (((i : Fin (n + 1)) : ℕ) : ℝ) := by exact_mod_cast hpos
    simpa using this
  · intro k hk a b hab
    rw [hidx0] at hk
    show groundFibreBox ord 0 N a k ≤ groundFibreBox ord 0 N b k
    rw [groundFibreBox_apply, groundFibreBox_apply, if_pos hk, if_pos hk]
    exact hab
  · intro k hk a b hab
    rw [hidx0] at hk
    show groundFibreBox ord 0 N b k ≤ groundFibreBox ord 0 N a k
    rw [groundFibreBox_apply, groundFibreBox_apply, if_neg hk, if_neg hk]
    exact Nat.sub_le_sub_left hab N
  · intro a b hab
    show groundFibreBox ord 0 N a k₀ < groundFibreBox ord 0 N b k₀
    rw [groundFibreBox_apply, groundFibreBox_apply, if_pos hidx0, if_pos hidx0]
    exact hab


/-- **Unconditional relation-freeness of the ground-fibre box.**  At the integer shift configuration
every expanded pattern relation among the moving canonical jets has vanishing coefficients — for
every parameter sequence, with no genericity and no analytic input. -/
theorem movingCanonicalExpandedPatternRelation_coefficients_eq_zero_integerShifts
    (θ : BoundedRealSequence) (n degree N : ℕ) (orders : Fin (n + 1) → ℕ)
    (coeff : Fin (N + 1) × Fin (degree + 1) → ℂ)
    (hrelation : movingCanonicalExpandedPatternRelationHolds
      (row := Fin (N + 1) × Fin (degree + 1)) degree (fun i => orders i + 1)
      (groundFibreBox (fun i => orders i + 1) 0 N) θ (integerShiftConfiguration n) coeff) :
    ∀ col, coeff col = 0 :=
  movingCanonicalExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
    degree (fun i => orders i + 1) (groundFibreBox (fun i => orders i + 1) 0 N) θ
    (integerShiftConfiguration n)
    (movingCanonicalExpandedFullRankWitness_integerShifts θ n degree N orders) coeff hrelation

end GaloisForLFunctions.HTGeometry
