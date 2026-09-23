import GaloisForLFunctions.HTGeometry.InfiniteLBitRecurrenceLocalitySeparationLaw

/-!
# L-bit boundary temporal-dimension budget

For the explicit quasi-local infinite l-bit field, this file isolates the
coefficient packet born when the environment of the flip at site `0` crosses
the boundary site `r + 1`.  The same `2 ^ r` coefficients that supply the new
temporal directions must pay the diameter-weighted locality mass.

The resulting estimate is deterministic and exact.  It concerns coefficient
resolution, not finite-time statistical distinguishability.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The sites strictly between the distinguished flip at `0` and the boundary
site `r + 1`. -/
def lbitBoundaryInterior (r : ℕ) : Finset ℕ :=
  Finset.Ico 1 (r + 1)

@[simp]
theorem card_lbitBoundaryInterior (r : ℕ) :
    (lbitBoundaryInterior r).card = r := by
  simp [lbitBoundaryInterior, Nat.card_Ico]

theorem zero_not_mem_lbitBoundaryInterior (r : ℕ) :
    0 ∉ lbitBoundaryInterior r := by
  simp [lbitBoundaryInterior]

theorem right_not_mem_lbitBoundaryInterior (r : ℕ) :
    r + 1 ∉ lbitBoundaryInterior r := by
  simp [lbitBoundaryInterior]

/-- Embed an interior site back into the countable chain. -/
def lbitBoundaryInteriorEmbedding (r : ℕ) :
    ↥(lbitBoundaryInterior r) ↪ ℕ :=
  Function.Embedding.subtype fun i : ℕ => i ∈ lbitBoundaryInterior r

/-- Support containing both endpoints and an arbitrary subset of the
interior. -/
def lbitBoundarySupport
    (r : ℕ) (S : Finset ↥(lbitBoundaryInterior r)) :
    {A : Finset ℕ // A.Nonempty} :=
  ⟨insert 0
      (insert (r + 1) (S.map (lbitBoundaryInteriorEmbedding r))),
    ⟨0, Finset.mem_insert_self _ _⟩⟩

@[simp]
theorem zero_mem_lbitBoundarySupport
    (r : ℕ) (S : Finset ↥(lbitBoundaryInterior r)) :
    0 ∈ (lbitBoundarySupport r S).1 := by
  simp [lbitBoundarySupport]

@[simp]
theorem right_mem_lbitBoundarySupport
    (r : ℕ) (S : Finset ↥(lbitBoundaryInterior r)) :
    r + 1 ∈ (lbitBoundarySupport r S).1 := by
  simp [lbitBoundarySupport]

theorem zero_not_mem_lbitBoundaryInterior_map
    (r : ℕ) (S : Finset ↥(lbitBoundaryInterior r)) :
    0 ∉ S.map (lbitBoundaryInteriorEmbedding r) := by
  intro h0
  obtain ⟨i, _hiS, hi0⟩ := Finset.mem_map.mp h0
  have hi0' : (i : ℕ) = 0 := hi0
  have hiInterior := i.2
  rw [hi0'] at hiInterior
  exact zero_not_mem_lbitBoundaryInterior r hiInterior

theorem right_not_mem_lbitBoundaryInterior_map
    (r : ℕ) (S : Finset ↥(lbitBoundaryInterior r)) :
    r + 1 ∉ S.map (lbitBoundaryInteriorEmbedding r) := by
  intro hy
  obtain ⟨i, _hiS, hiy⟩ := Finset.mem_map.mp hy
  have hiy' : (i : ℕ) = r + 1 := hiy
  have hiInterior := i.2
  rw [hiy'] at hiInterior
  exact right_not_mem_lbitBoundaryInterior r hiInterior

/-- The two fixed endpoints can be erased, so the boundary-support map
remembers the interior subset exactly. -/
theorem lbitBoundarySupport_injective (r : ℕ) :
    Function.Injective (lbitBoundarySupport r) := by
  intro S T hST
  apply Finset.map_injective (lbitBoundaryInteriorEmbedding r)
  have hval :
      (lbitBoundarySupport r S).1 =
        (lbitBoundarySupport r T).1 :=
    congrArg Subtype.val hST
  have hzeroS :
      0 ∉ insert (r + 1)
        (S.map (lbitBoundaryInteriorEmbedding r)) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨by omega, zero_not_mem_lbitBoundaryInterior_map r S⟩
  have hzeroT :
      0 ∉ insert (r + 1)
        (T.map (lbitBoundaryInteriorEmbedding r)) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨by omega, zero_not_mem_lbitBoundaryInterior_map r T⟩
  have hfirst :
      insert (r + 1)
          (S.map (lbitBoundaryInteriorEmbedding r)) =
        insert (r + 1)
          (T.map (lbitBoundaryInteriorEmbedding r)) := by
    have herase := congrArg (fun A : Finset ℕ => A.erase 0) hval
    simpa only [lbitBoundarySupport,
      Finset.erase_insert hzeroS,
      Finset.erase_insert hzeroT] using herase
  have hsecond :=
    congrArg (fun A : Finset ℕ => A.erase (r + 1)) hfirst
  simpa only [
    Finset.erase_insert
      (right_not_mem_lbitBoundaryInterior_map r S),
    Finset.erase_insert
      (right_not_mem_lbitBoundaryInterior_map r T)] using hsecond

/-- Every packet support spans the two boundary sites. -/
theorem lbitBoundarySupport_diameter_ge
    (r : ℕ) (S : Finset ↥(lbitBoundaryInterior r)) :
    r + 1 ≤
      finiteLBitSupportDiameter (lbitBoundarySupport r S).1 := by
  simpa only [Nat.dist_zero_left] using
    pairwiseDistance_le_finiteLBitSupportDiameter
      (zero_mem_lbitBoundarySupport r S)
      (right_mem_lbitBoundarySupport r S)

/-- Coefficient born across the boundary at `r + 1`, indexed by its interior
support. -/
noncomputable def lbitBoundaryCoefficient
    (r : ℕ) (S : Finset ↥(lbitBoundaryInterior r)) : ℝ :=
  quasiLocalInfiniteLBitCoefficient (lbitBoundarySupport r S).1

/-- Boundary-born coefficients inherit rational linear independence from the
global field. -/
theorem lbitBoundaryCoefficient_linearIndependent (r : ℕ) :
    LinearIndependent ℚ (lbitBoundaryCoefficient r) := by
  have hcomp :=
    quasiLocalInfiniteLBitCoefficient_linearIndependent.comp
      (lbitBoundarySupport r)
      (lbitBoundarySupport_injective r)
  change LinearIndependent ℚ
    (fun S => quasiLocalInfiniteLBitCoefficient
      (lbitBoundarySupport r S).1)
  simpa only [Function.comp_def] using hcomp

/-- Environment after adjoining the right boundary site. -/
def lbitBoundaryExtendedInterior (r : ℕ) : Finset ℕ :=
  insert (r + 1) (lbitBoundaryInterior r)

@[simp]
theorem card_lbitBoundaryExtendedInterior (r : ℕ) :
    (lbitBoundaryExtendedInterior r).card = r + 1 := by
  simp [lbitBoundaryExtendedInterior,
    right_not_mem_lbitBoundaryInterior,
    card_lbitBoundaryInterior]

theorem zero_not_mem_lbitBoundaryExtendedInterior (r : ℕ) :
    0 ∉ lbitBoundaryExtendedInterior r := by
  simp [lbitBoundaryExtendedInterior,
    zero_not_mem_lbitBoundaryInterior]

/-- Inclusion of the old environment in the environment with its new boundary
site. -/
def lbitBoundaryInteriorToExtendedEmbedding (r : ℕ) :
    ↥(lbitBoundaryInterior r) ↪
      ↥(lbitBoundaryExtendedInterior r) where
  toFun i :=
    ⟨i.1, by
      exact Finset.mem_insert_of_mem i.2⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact congrArg
      (fun z : ↥(lbitBoundaryExtendedInterior r) => z.1) hij

/-- The new boundary site as an element of the extended environment. -/
def lbitBoundaryRightSite (r : ℕ) :
    ↥(lbitBoundaryExtendedInterior r) :=
  ⟨r + 1, Finset.mem_insert_self _ _⟩

/-- Subsets of the extended environment that contain the new boundary site,
parameterized by their old-interior part. -/
def lbitBoundaryNewEnvironmentSubset
    (r : ℕ) (S : Finset ↥(lbitBoundaryInterior r)) :
    Finset ↥(lbitBoundaryExtendedInterior r) :=
  insert (lbitBoundaryRightSite r)
    (S.map (lbitBoundaryInteriorToExtendedEmbedding r))

/-- The new half of the extended incident packet is literally the boundary
packet defined above. -/
theorem
    quasiLocalInfiniteLBitIncidentRestriction_newEnvironmentSubset_eq_boundary
    (r : ℕ) (S : Finset ↥(lbitBoundaryInterior r)) :
    quasiLocalInfiniteLBitIncidentRestriction
        0 (lbitBoundaryExtendedInterior r)
        (lbitBoundaryNewEnvironmentSubset r S) =
      lbitBoundaryCoefficient r S := by
  unfold quasiLocalInfiniteLBitIncidentRestriction
    lbitBoundaryCoefficient
  congr 1
  ext z
  simp [quasiLocalInfiniteLBitIncidentSupport,
    lbitBoundaryNewEnvironmentSubset,
    lbitBoundaryRightSite,
    lbitBoundaryInteriorToExtendedEmbedding,
    lbitBoundarySupport,
    lbitBoundaryInteriorEmbedding]
  constructor
  · rintro (h0 | hy | ⟨hS, _hzExtended⟩)
    · exact Or.inl h0
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hS)
  · rintro (h0 | hy | hS)
    · exact Or.inl h0
    · exact Or.inr (Or.inl hy)
    · rcases hS with ⟨hzInterior, hzS⟩
      exact Or.inr
        (Or.inr
          ⟨⟨hzInterior, hzS⟩,
            Finset.mem_insert_of_mem hzInterior⟩)

/-- Before the boundary is resolved, the local flip has `2 ^ r` independent
conditional frequencies. -/
theorem lbitBoundary_oldEnvironment_localFlipTemporalRank (r : ℕ) :
    lbitLocalFlipTemporalRank
        (quasiLocalInfiniteLBitIncidentRestriction
          0 (lbitBoundaryInterior r)) =
      2 ^ r := by
  simpa using
    quasiLocalInfiniteLBitIncidentRestriction_localFlip_fullRank
      0 (lbitBoundaryInterior r)
      (zero_not_mem_lbitBoundaryInterior r)

/-- Resolving the boundary site enlarges the local flip packet to
`2 ^ (r + 1)` independent frequencies. -/
theorem lbitBoundary_extendedEnvironment_localFlipTemporalRank (r : ℕ) :
    lbitLocalFlipTemporalRank
        (quasiLocalInfiniteLBitIncidentRestriction
          0 (lbitBoundaryExtendedInterior r)) =
      2 ^ (r + 1) := by
  simpa using
    quasiLocalInfiniteLBitIncidentRestriction_localFlip_fullRank
      0 (lbitBoundaryExtendedInterior r)
      (zero_not_mem_lbitBoundaryExtendedInterior r)

/-- Adding the right boundary site exactly doubles local-flip temporal rank. -/
theorem lbitBoundary_localFlipTemporalRank_doubles (r : ℕ) :
    lbitLocalFlipTemporalRank
        (quasiLocalInfiniteLBitIncidentRestriction
          0 (lbitBoundaryExtendedInterior r)) =
      2 *
        lbitLocalFlipTemporalRank
          (quasiLocalInfiniteLBitIncidentRestriction
            0 (lbitBoundaryInterior r)) := by
  rw [lbitBoundary_extendedEnvironment_localFlipTemporalRank,
    lbitBoundary_oldEnvironment_localFlipTemporalRank, pow_succ]
  omega

/-- Absolute mass of the full boundary-born coefficient packet. -/
noncomputable def lbitBoundaryPacketAbsMass (r : ℕ) : ℝ :=
  ∑ S : Finset ↥(lbitBoundaryInterior r),
    |lbitBoundaryCoefficient r S|

/-- Embedding of the boundary packet into all finite supports. -/
def lbitBoundarySupportValueEmbedding (r : ℕ) :
    Finset ↥(lbitBoundaryInterior r) ↪ Finset ℕ where
  toFun S := (lbitBoundarySupport r S).1
  inj' := by
    intro S T hST
    apply lbitBoundarySupport_injective r
    exact Subtype.ext hST

/-- **Same-packet boundary budget.**  The packet born at distance `r + 1`
pays at least `2 ^ (r + 1)` per unit of absolute coefficient mass in the
global diameter-weighted locality budget. -/
theorem two_pow_mul_lbitBoundaryPacketAbsMass_le_weightedMass (r : ℕ) :
    (2 : ℝ) ^ (r + 1) * lbitBoundaryPacketAbsMass r ≤
      quasiLocalInfiniteLBitWeightedMass := by
  let weighted : Finset ℕ → ℝ := fun A =>
    (2 : ℝ) ^ finiteLBitSupportDiameter A *
      |quasiLocalInfiniteLBitCoefficient A|
  have hterm :
      ∀ S : Finset ↥(lbitBoundaryInterior r),
        (2 : ℝ) ^ (r + 1) *
            |lbitBoundaryCoefficient r S| ≤
          weighted (lbitBoundarySupport r S).1 := by
    intro S
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num)
        (lbitBoundarySupport_diameter_ge r S))
      (abs_nonneg _)
  have hpacket :
      (2 : ℝ) ^ (r + 1) * lbitBoundaryPacketAbsMass r ≤
        ∑ S : Finset ↥(lbitBoundaryInterior r),
          weighted (lbitBoundarySupport r S).1 := by
    rw [lbitBoundaryPacketAbsMass, Finset.mul_sum]
    exact Finset.sum_le_sum fun S _ => hterm S
  have hglobal :
      (∑ S : Finset ↥(lbitBoundaryInterior r),
          weighted (lbitBoundarySupport r S).1) ≤
        quasiLocalInfiniteLBitWeightedMass := by
    change
      (∑ S : Finset ↥(lbitBoundaryInterior r),
          weighted ((lbitBoundarySupportValueEmbedding r) S)) ≤
        ∑' A : Finset ℕ, weighted A
    have hsum :
        Summable weighted := by
      simpa only [weighted] using
        summable_quasiLocalInfiniteLBitWeightedCoefficient
    have hle :=
      hsum.sum_le_tsum
        (Finset.univ.map (lbitBoundarySupportValueEmbedding r))
        (fun A _ => by
          exact mul_nonneg (by positivity) (abs_nonneg _))
    rw [Finset.sum_map] at hle
    simpa using hle
  exact hpacket.trans hglobal

/-- Number of boundary-born coefficients visible above threshold `δ`. -/
noncomputable def lbitBoundaryThresholdCount (r : ℕ) (δ : ℝ) : ℕ :=
  (Finset.univ.filter fun S : Finset ↥(lbitBoundaryInterior r) =>
    δ ≤ |lbitBoundaryCoefficient r S|).card

/-- The above-threshold packet mass is at least threshold times count. -/
theorem threshold_mul_lbitBoundaryThresholdCount_le_packetAbsMass
    (r : ℕ) (δ : ℝ) :
    δ * (lbitBoundaryThresholdCount r δ : ℝ) ≤
      lbitBoundaryPacketAbsMass r := by
  let active :=
    Finset.univ.filter fun S : Finset ↥(lbitBoundaryInterior r) =>
      δ ≤ |lbitBoundaryCoefficient r S|
  have hactive :
      ∀ S ∈ active, δ ≤ |lbitBoundaryCoefficient r S| := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2
  calc
    δ * (lbitBoundaryThresholdCount r δ : ℝ) =
        ∑ _S ∈ active, δ := by
          simp [lbitBoundaryThresholdCount, active]
          ring
    _ ≤ ∑ S ∈ active, |lbitBoundaryCoefficient r S| := by
          exact Finset.sum_le_sum fun S hS => hactive S hS
    _ ≤ ∑ S : Finset ↥(lbitBoundaryInterior r),
          |lbitBoundaryCoefficient r S| := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
            (fun S _ _ => abs_nonneg _)
    _ = lbitBoundaryPacketAbsMass r := by
          rfl

/-- Division-free threshold-count budget. -/
theorem two_pow_mul_thresholdCount_le_weightedMass
    (r : ℕ) {δ : ℝ} (_hδ : 0 < δ) :
    (2 : ℝ) ^ (r + 1) *
        (δ * (lbitBoundaryThresholdCount r δ : ℝ)) ≤
      quasiLocalInfiniteLBitWeightedMass := by
  exact
    (mul_le_mul_of_nonneg_left
      (threshold_mul_lbitBoundaryThresholdCount_le_packetAbsMass r δ)
      (by positivity)).trans
        (two_pow_mul_lbitBoundaryPacketAbsMass_le_weightedMass r)

/-- Quotient form of the threshold-count budget. -/
theorem lbitBoundaryThresholdCount_le_weightedMass_div
    (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (lbitBoundaryThresholdCount r δ : ℝ) ≤
      quasiLocalInfiniteLBitWeightedMass /
        ((2 : ℝ) ^ (r + 1) * δ) := by
  rw [le_div_iff₀ (mul_pos (by positivity) hδ)]
  have h :=
    two_pow_mul_thresholdCount_le_weightedMass r hδ
  nlinarith

/-- A fully resolved boundary packet has all `2 ^ r` coefficients above the
threshold. -/
theorem lbitBoundaryThresholdCount_eq_full
    (r : ℕ) {δ : ℝ}
    (hfull :
      ∀ S : Finset ↥(lbitBoundaryInterior r),
        δ ≤ |lbitBoundaryCoefficient r S|) :
    lbitBoundaryThresholdCount r δ = 2 ^ r := by
  rw [lbitBoundaryThresholdCount,
    Finset.filter_eq_self.2 (fun S _ => hfull S)]
  simp [Fintype.card_finset, Fintype.card_coe,
    card_lbitBoundaryInterior]

/-- **Full-resolution quadratic boundary law.**  Resolving every one of the
`2 ^ r` new temporal directions at coefficient threshold `δ` costs at least
`2 * δ * (2 ^ r)^(2 : ℕ)` of diameter-weighted mass. -/
theorem two_mul_threshold_mul_sq_two_pow_le_weightedMass
    (r : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hfull :
      ∀ S : Finset ↥(lbitBoundaryInterior r),
        δ ≤ |lbitBoundaryCoefficient r S|) :
    2 * δ * ((2 : ℝ) ^ r) ^ (2 : ℕ) ≤
      quasiLocalInfiniteLBitWeightedMass := by
  have h :=
    two_pow_mul_thresholdCount_le_weightedMass r hδ
  rw [lbitBoundaryThresholdCount_eq_full r hfull] at h
  calc
    2 * δ * ((2 : ℝ) ^ r) ^ (2 : ℕ) =
        (2 : ℝ) ^ (r + 1) *
          (δ * ((2 ^ r : ℕ) : ℝ)) := by
            norm_num [pow_succ]
            ring
    _ ≤ quasiLocalInfiniteLBitWeightedMass := h

end

end GaloisForLFunctions.HTGeometry
