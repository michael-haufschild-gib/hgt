import GaloisForLFunctions.RHTower.ZetaRigidOrdinateGaps
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion

/-!
# Strictly increasing ordered ordinates force the critical line

If the ordered positive ordinates `γ_n` increase strictly from the index `N₀` on, then every zero
of `ξ` above height `γ_{N₀}` lies on the critical line (`RigidOrdinates.re_eq_half`). The ordered
positive zero copies above `N₀` are therefore `½ + iγ_n`
(`RigidOrdinates.orderedPositiveZeroCopy_eq`).

**Proof.** An off-line zero `ρ` and its reflection `1 − ρ̄` are distinct zeros with the same
ordinate. Their copies receive indices `n ≠ n'` with `γ_n = γ_{n'}`, both at least `N₀`. This
contradicts strict monotonicity.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Strict monotonicity of the ordered ordinates from `N₀` on. -/
theorem RigidOrdinates.lt_of_lt {h : ℝ} {N₀ : ℕ} (H : RigidOrdinates h N₀) {a b : ℕ}
    (ha : N₀ ≤ a) (hab : a < b) : xiOrderedPositiveOrdinate a < xiOrderedPositiveOrdinate b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hab with h1 | h1
    · exact (ih h1).trans (H.strict b (by omega))
    · subst h1; exact H.strict a ha

/-- Every positive zero copy has an index in the ordered enumeration. -/
theorem exists_xiOrderedPositiveZeroCopy_eq {q : XiZeroCopy} (hq : 0 < (q.1 : ℂ).im) :
    ∃ n, xiOrderedPositiveZeroCopy n = q := by
  obtain ⟨n, hn⟩ := xiOrderedPositiveZeroCopyMap_surjective ⟨q, hq⟩
  exact ⟨n, congrArg Subtype.val hn⟩

/-- An index whose ordinate exceeds `γ_{N₀}` is at least `N₀`. -/
theorem le_of_ordinate_gt {N₀ n : ℕ}
    (h : xiOrderedPositiveOrdinate N₀ < xiOrderedPositiveOrdinate n) : N₀ ≤ n := by
  by_contra hlt
  push Not at hlt
  have := xiOrderedPositiveOrdinate_monotone hlt.le
  linarith

/-- **Local RH.** Zeros above `γ_{N₀}` lie on the critical line. -/
theorem RigidOrdinates.re_eq_half {h : ℝ} {N₀ : ℕ} (H : RigidOrdinates h N₀) {ρ : ℂ}
    (hρ : xi ρ = 0) (him : xiOrderedPositiveOrdinate N₀ < ρ.im) : ρ.re = 1 / 2 := by
  have hpos : 0 < ρ.im := lt_of_le_of_lt (xiOrderedPositiveOrdinate_nonneg N₀) him
  set ρ' : ℂ := 1 - (starRingEnd ℂ) ρ with hρ'
  have hρ'0 : xi ρ' = 0 := by rw [hρ', xi_one_sub, xi_conj, hρ, map_zero]
  have him' : ρ'.im = ρ.im := by simp [hρ']
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  obtain ⟨q', hq'⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ'0
  have hqpos : 0 < (q.1 : ℂ).im := by rw [hq]; exact hpos
  have hq'pos : 0 < (q'.1 : ℂ).im := by rw [hq', him']; exact hpos
  obtain ⟨n, hn⟩ := exists_xiOrderedPositiveZeroCopy_eq hqpos
  obtain ⟨n', hn'⟩ := exists_xiOrderedPositiveZeroCopy_eq hq'pos
  have hγn : xiOrderedPositiveOrdinate n = ρ.im := by
    rw [← xiOrderedPositiveZeroCopy_im_eq, hn, hq]
  have hγn' : xiOrderedPositiveOrdinate n' = ρ.im := by
    rw [← xiOrderedPositiveZeroCopy_im_eq, hn', hq', him']
  have hN : N₀ ≤ n := le_of_ordinate_gt (by rw [hγn]; exact him)
  have hN' : N₀ ≤ n' := le_of_ordinate_gt (by rw [hγn']; exact him)
  have hnn : n = n' := by
    rcases lt_trichotomy n n' with hlt | heq | hgt
    · have := H.lt_of_lt hN hlt; linarith
    · exact heq
    · have := H.lt_of_lt hN' hgt; linarith
  have hqq : q = q' := by rw [← hn, ← hn', hnn]
  have : ρ = ρ' := by rw [← hq, ← hq', hqq]
  have hre := congrArg Complex.re this
  simp [hρ'] at hre
  linarith

/-- The ordered positive zero copies above `N₀` are `½ + iγ_n`. -/
theorem RigidOrdinates.orderedPositiveZeroCopy_eq {h : ℝ} {N₀ : ℕ} (H : RigidOrdinates h N₀)
    {n : ℕ} (hn : N₀ < n) :
    ((xiOrderedPositiveZeroCopy n).1 : ℂ) = 1 / 2 + (xiOrderedPositiveOrdinate n : ℂ) * I := by
  have him := xiOrderedPositiveZeroCopy_im_eq n
  have hgt : xiOrderedPositiveOrdinate N₀ < ((xiOrderedPositiveZeroCopy n).1 : ℂ).im := by
    rw [him]; exact H.lt_of_lt le_rfl hn
  have hre := H.re_eq_half (xi_xiZeroCopy_eq_zero _) hgt
  apply Complex.ext
  · rw [hre]; simp
  · rw [him]; simp

end

end RHTower
