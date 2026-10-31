import GaloisForLFunctions.AdelicKreinGeometry.Haar.PuncturedLimits
import GaloisForLFunctions.HeckeKreinToeplitz.Index.SubgroupJumpKernels

/-!
# Sharp classification of finite-index Haar dilation limits

The possible punctured limits are exactly the nonpositive real numbers. Adding
a positive multiple of the identity-indicator jump to the Haar state realizes
each negative limit with one negative square. Zero is realized at index zero.
-/

open Complex Filter Topology
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A real multiple of the identity-indicator jump on rational slopes. -/
def haarJumpSlope (a : ℝ) (u : ℚˣ) : ℂ :=
  (a : ℂ) * subgroupJumpKernel (⊥ : Subgroup ℚˣ) u

theorem haarJumpSlope_hermitian (a : ℝ) : IsHermKernel (haarJumpSlope a) := by
  intro u
  change (a : ℂ) * subgroupJumpKernel (⊥ : Subgroup ℚˣ) u⁻¹ =
    (starRingEnd ℂ) ((a : ℂ) * subgroupJumpKernel (⊥ : Subgroup ℚˣ) u)
  rw [subgroupJumpKernel_hermitian, map_mul, Complex.conj_ofReal]

theorem haarJumpSlope_one (a : ℝ) : haarJumpSlope a 1 = 0 := by
  rw [haarJumpSlope, subgroupJumpKernel_one, mul_zero]

/-- A Haar carrier whose nonidentity dilation reading has constant downward shift. -/
def haarJumpCarrier (a : ℝ) (g : AffineGroupQ) : ℂ :=
  haarState g + haarJumpSlope a (slopeUnit g)

private theorem positive_haar_state : IsPosDefKernel haarState :=
  isPosDefKernel_iff_isPosDefOnGroup.mpr isPosDefOnGroup_haarState

theorem haarJumpCarrier_hermitian (a : ℝ) : IsHermKernel (haarJumpCarrier a) := by
  intro g
  change haarState g⁻¹ + haarJumpSlope a (slopeUnit g⁻¹) =
    (starRingEnd ℂ) (haarState g + haarJumpSlope a (slopeUnit g))
  rw [positive_haar_state.1, map_inv, haarJumpSlope_hermitian, map_add]

theorem haarJumpCarrier_hasIntegerSuccessor (a : ℝ) :
    HasIntegerSuccessor (haarJumpCarrier a) := by
  intro b
  have ht : slopeUnit (translation b) = 1 := Units.ext (affSlope_translation b)
  change haarState (translation b) + haarJumpSlope a (slopeUnit (translation b)) = _
  rw [ht, haarJumpSlope_one, add_zero]
  exact haarState_hasIntegerSuccessor b

theorem haarJumpCarrier_zero : haarJumpCarrier 0 = haarState := by
  funext g
  simp only [haarJumpCarrier, haarJumpSlope, Complex.ofReal_zero, zero_mul, add_zero]

/-- Every nonidentity slope has the same downward shift. -/
theorem haarJumpCarrier_dilation_of_ne (a : ℝ) (u : ℚˣ) (hu : u ≠ 1) :
    haarJumpCarrier a (dilation u) = haarState (dilation u) - (a : ℂ) := by
  have hd : slopeUnit (dilation u) = u := Units.ext (affSlope_dilation u)
  simp only [haarJumpCarrier, haarJumpSlope, hd, subgroupJumpKernel_apply,
    Subgroup.mem_bot, if_neg hu, mul_neg, mul_one, sub_eq_add_neg]

/-- The jump carrier has the prescribed punctured limit, at every real shift. -/
theorem haarJumpCarrier_punctured_limit (a : ℝ) :
    HasPuncturedDilationLimit (haarJumpCarrier a) (-(a : ℂ)) := by
  have hzero := hasPuncturedDilationLimit_zero_of_positive positive_haar_state
    haarState_hasIntegerSuccessor
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hzero ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u hu hne hclose
  rw [haarJumpCarrier_dilation_of_ne a u hne, sub_neg_eq_add, sub_add_cancel]
  simpa only [sub_zero] using hbound u hu hne hclose

/-- Every strictly negative punctured limit is realized with exactly one negative square. -/
theorem negIndex_haarJumpCarrier_of_pos {a : ℝ} (ha : 0 < a) :
    negIndex (haarJumpCarrier a) = 1 := by
  have hindex := negIndex_add_slope_of_integer_successor positive_haar_state
    haarState_hasIntegerSuccessor (haarJumpSlope a) (haarJumpSlope_hermitian a)
  change negIndex (haarJumpCarrier a) = negIndex (haarJumpSlope a) at hindex
  rw [hindex]
  have hproper : (⊥ : Subgroup ℚˣ) ≠ ⊤ := by
    intro he
    have hmem : Units.mk0 (2 : ℚ) (by norm_num) ∈ (⊥ : Subgroup ℚˣ) := by
      rw [he]
      exact Subgroup.mem_top _
    have htwo := congrArg (fun u : ℚˣ => (u : ℚ)) (Subgroup.mem_bot.mp hmem)
    norm_num at htwo
  exact negIndex_scaled_subgroupJumpKernel (⊥ : Subgroup ℚˣ) hproper ha

/-- Reversing the sign of the jump produces a positive punctured limit and infinite index. -/
theorem negIndex_haarJumpCarrier_of_neg {a : ℝ} (ha : a < 0) :
    negIndex (haarJumpCarrier a) = ⊤ := by
  apply negIndex_eq_top_of_haar_positive_punctured_limit
    (haarJumpCarrier_hermitian a) (haarJumpCarrier_hasIntegerSuccessor a) (neg_pos.mpr ha)
  simpa only [Complex.ofReal_neg] using haarJumpCarrier_punctured_limit a

/-- The jump family has index zero, one, or infinity according to the sign of its parameter. -/
theorem negIndex_haarJumpCarrier (a : ℝ) : negIndex (haarJumpCarrier a) =
    if a < 0 then ⊤ else if a = 0 then 0 else 1 := by
  by_cases hneg : a < 0
  · rw [if_pos hneg, negIndex_haarJumpCarrier_of_neg hneg]
  · rw [if_neg hneg]
    by_cases hz : a = 0
    · rw [if_pos hz, hz, haarJumpCarrier_zero, positive_haar_state.negIndex_eq_zero]
    · rw [if_neg hz, negIndex_haarJumpCarrier_of_pos (lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hz))]

/-- Nonnegative jump sizes give finite-index Haar carriers. -/
theorem negIndex_haarJumpCarrier_le_one {a : ℝ} (ha : 0 ≤ a) :
    negIndex (haarJumpCarrier a) ≤ 1 := by
  by_cases hz : a = 0
  · rw [hz, haarJumpCarrier_zero, positive_haar_state.negIndex_eq_zero]
    exact bot_le
  · rw [negIndex_haarJumpCarrier_of_pos (lt_of_le_of_ne ha (Ne.symm hz))]

/-- A negative limit cannot occur at index zero. -/
theorem one_le_negIndex_of_negative_punctured_limit {k : AffineGroupQ → ℂ} {L : ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k) (hL : HasPuncturedDilationLimit k L)
    (hneg : L.re < 0) : 1 ≤ negIndex k := by
  apply Order.one_le_iff_ne_zero.mpr
  intro hz
  have hp := (isPosDefKernel_iff hk).mpr hz
  have he := hL.unique (hasPuncturedDilationLimit_zero_of_positive hp hs)
  rw [he, Complex.zero_re] at hneg
  exact (lt_irrefl 0) hneg

/-- The possible finite-index Haar dilation limits are precisely the nonpositive reals. -/
theorem exists_finite_index_haar_punctured_limit_iff (L : ℂ) :
    (∃ k : AffineGroupQ → ℂ, IsHermKernel k ∧ HasIntegerSuccessor k ∧
      negIndex k < ⊤ ∧ HasPuncturedDilationLimit k L) ↔
        (L.re : ℂ) = L ∧ L.re ≤ 0 := by
  constructor
  · rintro ⟨k, hk, hs, hi, hL⟩
    exact haar_punctured_limit_real_nonpositive hk hs hi hL
  · rintro ⟨hreal, hnonpos⟩
    refine ⟨haarJumpCarrier (-L.re), haarJumpCarrier_hermitian _,
      haarJumpCarrier_hasIntegerSuccessor _, ?_, ?_⟩
    · exact lt_of_le_of_lt (negIndex_haarJumpCarrier_le_one (neg_nonneg.mpr hnonpos))
        (ENat.coe_lt_top 1)
    · simpa only [Complex.ofReal_neg, neg_neg, hreal] using haarJumpCarrier_punctured_limit (-L.re)

/-- The smallest index at punctured limit zero is zero. -/
theorem exists_haar_punctured_zero_index_zero :
    ∃ k : AffineGroupQ → ℂ, IsHermKernel k ∧ HasIntegerSuccessor k ∧
      negIndex k = 0 ∧ HasPuncturedDilationLimit k 0 :=
  ⟨haarState, positive_haar_state.1, haarState_hasIntegerSuccessor,
    positive_haar_state.negIndex_eq_zero,
    hasPuncturedDilationLimit_zero_of_positive positive_haar_state haarState_hasIntegerSuccessor⟩

/-- The smallest index at each strictly negative real limit is one. -/
theorem exists_haar_negative_limit_index_one {a : ℝ} (ha : a < 0) :
    ∃ k : AffineGroupQ → ℂ, IsHermKernel k ∧ HasIntegerSuccessor k ∧
      negIndex k = 1 ∧ HasPuncturedDilationLimit k (a : ℂ) := by
  refine ⟨haarJumpCarrier (-a), haarJumpCarrier_hermitian _,
    haarJumpCarrier_hasIntegerSuccessor _, negIndex_haarJumpCarrier_of_pos (neg_pos.mpr ha), ?_⟩
  simpa only [Complex.ofReal_neg, neg_neg] using haarJumpCarrier_punctured_limit (-a)

/-- Every existing punctured limit has distance at least one from the normalized identity value. -/
theorem one_le_norm_haar_identity_sub_punctured_limit {k : AffineGroupQ → ℂ} {L : ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k) (hi : negIndex k < ⊤)
    (hL : HasPuncturedDilationLimit k L) : 1 ≤ ‖k 1 - L‖ := by
  obtain ⟨hreal, hnonpos⟩ := haar_punctured_limit_real_nonpositive hk hs hi hL
  rw [hasIntegerSuccessor_one hs, ← hreal]
  have he : (1 : ℂ) - (L.re : ℂ) = ((1 - L.re : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith only [hnonpos] : 0 ≤ 1 - L.re)]
  linarith only [hnonpos]

#print axioms negIndex_haarJumpCarrier_of_pos
#print axioms negIndex_haarJumpCarrier
#print axioms one_le_negIndex_of_negative_punctured_limit
#print axioms exists_finite_index_haar_punctured_limit_iff
#print axioms exists_haar_negative_limit_index_one
#print axioms one_le_norm_haar_identity_sub_punctured_limit
end GaloisForLFunctions.AdelicKreinGeometry
