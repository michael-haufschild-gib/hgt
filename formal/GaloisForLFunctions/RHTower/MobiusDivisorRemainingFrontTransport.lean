import GaloisForLFunctions.RHTower.MobiusDivisorUniformSuccessorTransport

/-! # Successor transport charged to the remaining front -/
noncomputable section
open Finset
namespace RHTower

/-- A prescribed prime's new envelope cost can be charged to the quotients of the
other remaining primes, even when its own quotient is unbounded. -/
theorem mobiusDivisorSuccessorEnvelope_insert_le_remaining_quotient
    (M K : ℕ) (P : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpM : p< M) (hpP : p∉P)
    (hfront : ∀ q∈mobiusDivisorSelectionPrimes M\insert p P,M/q≤ K) :
    mobiusDivisorSuccessorEnvelope M (insert p P)≤ mobiusDivisorSuccessorEnvelope M P+
      (6/5:ℝ)*(K:ℝ)*Real.sqrt ((M:ℝ)*mobiusDivisorSuccessorEnvelope M P) := by
  let E := mobiusDivisorSuccessorEnvelope M P
  have hbase := (mobiusDivisorSuccessorEnvelope_le_iff M P E).mp le_rfl
  have hpbase := hbase.2 p (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hpM,hp⟩,hpP⟩)
  rw [mobiusDivisorSuccessorEnvelope_le_iff]
  refine ⟨hpbase.trans (le_add_of_nonneg_right (by positivity)),?_⟩
  intro q hq
  obtain ⟨hqactive,hqP⟩ := mem_sdiff.mp hq
  obtain ⟨hqrange,hqprime⟩ := mem_filter.mp hqactive
  have hg := (abs_le.mp (abs_mobiusDivisorSelectionEnergy_insert_le_quotient
    M (insert p P) hqprime (mem_range.mp hqrange) hqP)).2
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hpbase (Nat.cast_nonneg M))
  have hquot : ((M/q:ℕ):ℝ)≤ K := by exact_mod_cast hfront q hq
  have hcost : (6/5:ℝ)*(M/q:ℕ)*Real.sqrt ((M:ℝ)*mobiusDivisorSelectionEnergy M (insert p P))≤
      (6/5:ℝ)*(K:ℝ)*Real.sqrt ((M:ℝ)*E) := by gcongr
  linarith only [hpbase,hg,hcost]
end RHTower
