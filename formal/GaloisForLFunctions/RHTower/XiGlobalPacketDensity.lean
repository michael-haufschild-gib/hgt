import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# Global logarithmic density of the actual Xi divisor

Unit-height packets include every multiplicity copy. Reflection handles
negative heights and a finite compact packet handles the remaining heights.
-/

open Complex Set Filter Topology
noncomputable section
namespace RHTower

/-- All actual divisor copies within unit distance of a real height. -/
def xiUnitHeightPacket (T : ℝ) : Finset XiZeroCopy :=
  (finite_xiZeroCopy_band T (show (0 : ℝ) ≤ 1 by positivity)).toFinset

theorem mem_xiUnitHeightPacket (T : ℝ) (q : XiZeroCopy) :
    q ∈ xiUnitHeightPacket T ↔ |(q.1 : ℂ).im - T| ≤ 1 := by
  simp [xiUnitHeightPacket]

/-- Reflection preserves the complete packet cardinality, including multiplicities. -/
theorem xiUnitHeightPacket_card_neg (T : ℝ) :
    (xiUnitHeightPacket (-T)).card = (xiUnitHeightPacket T).card := by
  classical
  have he : (xiUnitHeightPacket T).map xiZeroCopyReflectEquiv.toEmbedding =
      xiUnitHeightPacket (-T) := by
    ext q
    rw [Finset.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rw [mem_xiUnitHeightPacket]
      change |(((xiZeroCopyReflectEquiv p).1 : ℂ).im) - -T| ≤ 1
      rw [xiZeroCopyReflect_coe]
      have hp' := (mem_xiUnitHeightPacket T p).mp hp
      simp only [Complex.sub_im, Complex.one_im, zero_sub]
      rw [show -(p.1 : ℂ).im - -T = -((p.1 : ℂ).im - T) by ring, abs_neg]
      exact hp'
    · intro hq
      refine ⟨xiZeroCopyReflectEquiv.symm q, ?_, xiZeroCopyReflectEquiv.apply_symm_apply q⟩
      rw [mem_xiUnitHeightPacket]
      have hp := xiZeroCopyReflect_coe (xiZeroCopyReflectEquiv.symm q)
      rw [xiZeroCopyReflectEquiv.apply_symm_apply] at hp
      have him := congrArg Complex.im hp
      simp only [Complex.sub_im, Complex.one_im, zero_sub] at him
      have hq' := (mem_xiUnitHeightPacket (-T) q).mp hq
      have hid : (((xiZeroCopyReflectEquiv.symm q).1 : ℂ).im - T) =
          -((q.1 : ℂ).im - -T) := by linarith only [him]
      rw [hid, abs_neg]
      exact hq'
  rw [← he, Finset.card_map]

/-- One unconditional logarithmic ceiling applies to every real height. -/
theorem exists_xiUnitHeightPacket_global_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ,
      ((xiUnitHeightPacket T).card : ℝ) ≤ C * (1 + Real.log (2 + |T|)) := by
  classical
  obtain ⟨C, hC, htail⟩ := exists_card_near_xi_zeros_le
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1
    (htail.and (eventually_ge_atTop (2 : ℝ)))
  have hTpos : 0 < T₀ := by linarith only [(hT₀ T₀ le_rfl).2]
  let F := (finite_xiZeroCopy_band 0 (show 0 ≤ T₀ + 1 by positivity)).toFinset
  let B : ℝ := F.card
  let C' : ℝ := C + B + 1
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hlog (T : ℝ) : 0 ≤ Real.log (2 + |T|) :=
    Real.log_nonneg (by linarith only [abs_nonneg T])
  have hupper (T : ℝ) (hT : T₀ ≤ T) :
      ((xiUnitHeightPacket T).card : ℝ) ≤ C' * (1 + Real.log (2 + |T|)) := by
    have hpos : 0 < T := hTpos.trans_le hT
    have ht := (hT₀ T hT).1 (xiUnitHeightPacket T)
      (fun q hq => (mem_xiUnitHeightPacket T q).mp hq)
    have hlogle : Real.log T ≤ 1 + Real.log (2 + |T|) := by
      have h := Real.log_le_log hpos (by linarith only [le_abs_self T] : T ≤ 2 + |T|)
      linarith only [h]
    exact ht.trans ((mul_le_mul_of_nonneg_left hlogle hC.le).trans
      (mul_le_mul_of_nonneg_right (by dsimp [C']; linarith only [hB] : C ≤ C')
        (by linarith only [hlog T])))
  refine ⟨C', hC', fun T => ?_⟩
  by_cases hlarge : T₀ ≤ |T|
  · rcases le_total 0 T with hT | hT
    · rw [abs_of_nonneg hT] at hlarge
      exact hupper T hlarge
    · rw [abs_of_nonpos hT] at hlarge
      have ht := hupper (-T) hlarge
      simpa only [xiUnitHeightPacket_card_neg, abs_neg] using ht
  · have hsmall : |T| < T₀ := lt_of_not_ge hlarge
    have hsub : xiUnitHeightPacket T ⊆ F := by
      intro q hq
      dsimp only [F]
      rw [Set.Finite.mem_toFinset]
      change |(q.1 : ℂ).im - 0| ≤ T₀ + 1
      rw [sub_zero]
      have hq' := (mem_xiUnitHeightPacket T q).mp hq
      have htri := abs_add_le ((q.1 : ℂ).im - T) T
      rw [sub_add_cancel] at htri
      linarith only [htri, hq', hsmall]
    have hcard : ((xiUnitHeightPacket T).card : ℝ) ≤ B := by
      change ((xiUnitHeightPacket T).card : ℝ) ≤ (F.card : ℝ)
      exact_mod_cast Finset.card_le_card hsub
    have hBC : B ≤ C' := by dsimp [C']; linarith only [hC]
    exact hcard.trans (hBC.trans
      (le_mul_of_one_le_right hC'.le (by linarith only [hlog T])))

end RHTower
