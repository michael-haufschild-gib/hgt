import GaloisForLFunctions.RHTower.ChenGuptaLiHZeroDyadicReindex
import GaloisForLFunctions.RHTower.ChenGuptaLiRealSmoothBump
import Mathlib.Analysis.SumOverResidueClass

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The nonnegative-integer summand in CGL's positive coprime cutoff mass. -/
def cglSmoothBumpDyadicCoprimeTerm (w : CGLSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (n : ℕ) : ℝ :=
  ‖w.value ((n : ℝ) / N.value)‖ ^ 2 * if n.Coprime Q.value then 1 else 0

/-- Compact support and endpoint cancellation place every nonzero positive coprime term
inside CGL's literal dyadic block. -/
theorem cglSmoothBumpDyadicCoprimeTerm_support_subset_dyadicBlock
    (w : CGLSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    Function.support (cglSmoothBumpDyadicCoprimeTerm w N Q) ⊆
      cglCharacterDyadicBlock N := by
  have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  intro n hn
  by_contra hblock
  simp only [Function.mem_support] at hn
  have hblock' : n ∉ cglCharacterDyadicBlock N := by simpa using hblock
  have hcases : n ≤ N.value ∨ 2 * N.value < n := by
    rw [cglCharacterDyadicBlock, Finset.mem_Ioc] at hblock'
    omega
  rcases hcases with hle | hgt
  · rcases lt_or_eq_of_le hle with hlt | rfl
    · have hratio : (n : ℝ) / N.value < 1 := by
        apply (div_lt_iff₀ hNpos).2
        norm_num
        exact_mod_cast hlt
      have hout : (n : ℝ) / N.value ∉ Set.Icc (1 : ℝ) 2 := by
        intro hmem
        exact (not_le_of_gt hratio) hmem.1
      rw [cglSmoothBumpDyadicCoprimeTerm, w.outside_support _ hout] at hn
      simp at hn
    · have hNne : (N.value : ℝ) ≠ 0 := ne_of_gt hNpos
      rw [cglSmoothBumpDyadicCoprimeTerm] at hn
      have hquot : (N.value : ℝ) / N.value = 1 := div_self hNne
      rw [hquot, cglSmoothBump_value_one] at hn
      simp at hn
  · have hratio : 2 < (n : ℝ) / N.value := by
      apply (lt_div_iff₀ hNpos).2
      exact_mod_cast hgt
    have hout : (n : ℝ) / N.value ∉ Set.Icc (1 : ℝ) 2 := by
      intro hmem
      exact (not_le_of_gt hratio) hmem.2
    rw [cglSmoothBumpDyadicCoprimeTerm, w.outside_support _ hout] at hn
    simp at hn

/-- The positive coprime cutoff sequence has finite support. -/
theorem cglSmoothBumpDyadicCoprimeTerm_hasFiniteSupport
    (w : CGLSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    Function.HasFiniteSupport (cglSmoothBumpDyadicCoprimeTerm w N Q) :=
  (Finset.finite_toSet (cglCharacterDyadicBlock N)).subset
    (cglSmoothBumpDyadicCoprimeTerm_support_subset_dyadicBlock w N Q)

/-- Thus the positive coprime cutoff sequence is summable without an analytic assumption. -/
theorem cglSmoothBumpDyadicCoprimeTerm_summable
    (w : CGLSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    Summable (cglSmoothBumpDyadicCoprimeTerm w N Q) :=
  summable_of_hasFiniteSupport (cglSmoothBumpDyadicCoprimeTerm_hasFiniteSupport w N Q)

/-- The full positive-integer cutoff sum is its literal finite dyadic coprime sum. -/
theorem cglSmoothBumpDyadicCoprimeTerm_tsum_eq_dyadicCoprimeSum
    (w : CGLSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    ∑' n : ℕ, cglSmoothBumpDyadicCoprimeTerm w N Q n =
      ∑ n ∈ cglCharacterDyadicBlock N,
        ‖w.value ((n : ℝ) / N.value)‖ ^ 2 *
          if n.Coprime Q.value then 1 else 0 := by
  apply tsum_eq_sum
  intro n hn
  by_contra hterm
  exact hn (cglSmoothBumpDyadicCoprimeTerm_support_subset_dyadicBlock w N Q hterm)

/-- Exact split of the positive coprime cutoff sum into CGL's reduced residue progressions. -/
theorem cglSmoothBumpDyadicCoprimeTerm_tsum_eq_reducedResidueNatSum
    (w : CGLSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    ∑' n : ℕ, cglSmoothBumpDyadicCoprimeTerm w N Q n =
      ∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
        ∑' m : ℕ,
          ‖w.value (((a.val + Q.value * m : ℕ) : ℝ) / N.value)‖ ^ 2 := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  rw [Nat.sumByResidueClasses
    (cglSmoothBumpDyadicCoprimeTerm_summable w N Q) Q.value]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hunit : IsUnit a
  · simp only [hunit, ↓reduceIte]
    apply tsum_congr
    intro m
    unfold cglSmoothBumpDyadicCoprimeTerm
    have hcoprime : (a.val + Q.value * m).Coprime Q.value := by
      apply (ZMod.isUnit_iff_coprime _ _).mp
      simpa [Nat.cast_add, Nat.cast_mul] using hunit
    rw [if_pos hcoprime]
    simp
  · simp only [hunit, ↓reduceIte]
    have hterm : ∀ m : ℕ,
        cglSmoothBumpDyadicCoprimeTerm w N Q (a.val + Q.value * m) = 0 := by
      intro m
      unfold cglSmoothBumpDyadicCoprimeTerm
      have hcoprime : ¬(a.val + Q.value * m).Coprime Q.value := by
        intro hcoprime
        apply hunit
        have hrep : IsUnit (a.val : ZMod Q.value) :=
          (ZMod.isUnit_iff_coprime _ _).mpr (by
            simpa [Nat.cast_add, Nat.cast_mul] using hcoprime)
        rwa [ZMod.natCast_zmod_val] at hrep
      rw [if_neg hcoprime, mul_zero]
    simp_rw [hterm]
    simp

/-- The literal complex `w²` summand on one CGL affine residue lattice. -/
def cglRealSmoothBumpAffineHZeroTerm (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (a : ZMod Q.value) (k : ℤ) : ℂ :=
  w.toCGLSmoothBump.value (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value) *
    w.toCGLSmoothBump.value (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value)

/-- The negative tail of each affine residue progression vanishes, so its full integer lattice
sum equals its nonnegative progression. -/
theorem cglRealSmoothBumpAffineHZero_tsum_eq_natSum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus)
    (a : ZMod Q.value) :
    ∑' k : ℤ, cglRealSmoothBumpAffineHZeroTerm w N Q a k =
      ∑' m : ℕ, cglRealSmoothBumpAffineHZeroTerm w N Q a (m : ℤ) := by
  have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hQpos : (0 : ℝ) < Q.value := by exact_mod_cast Q.positive
  have hpos : Summable fun m : ℕ => cglRealSmoothBumpAffineHZeroTerm w N Q a (m : ℤ) := by
    apply summable_of_hasFiniteSupport
    refine (Set.finite_Iic (2 * N.value)).subset ?_
    intro m hm
    by_contra hbound
    simp only [Function.mem_support] at hm
    have hgt : 2 * N.value < m := lt_of_not_ge hbound
    have hqm : m ≤ Q.value * m := Nat.le_mul_of_pos_left m Q.positive
    have hnum : 2 * N.value < a.val + Q.value * m := by omega
    have hratio : 2 < ((a.val : ℝ) + Q.value * (m : ℝ)) / N.value := by
      apply (lt_div_iff₀ hNpos).2
      exact_mod_cast hnum
    have hout : ((a.val : ℝ) + Q.value * (m : ℝ)) / N.value ∉ Set.Icc (1 : ℝ) 2 := by
      intro hmem
      exact (not_le_of_gt hratio) hmem.2
    unfold cglRealSmoothBumpAffineHZeroTerm at hm
    simp only [Int.cast_natCast] at hm
    rw [w.toCGLSmoothBump.outside_support _ hout] at hm
    simp at hm
  have hnegpoint : ∀ m : ℕ,
      cglRealSmoothBumpAffineHZeroTerm w N Q a (-((m : ℤ) + 1)) = 0 := by
    intro m
    have ha : (a.val : ℝ) < Q.value := by exact_mod_cast a.val_lt
    have hmnonneg : 0 ≤ (m : ℝ) := by positivity
    have hcast : (((-((m : ℤ) + 1) : ℤ) : ℝ)) = -((m : ℝ) + 1) := by
      push_cast
      ring
    have hratio :
        ((a.val : ℝ) + (Q.value : ℝ) * ((-((m : ℤ) + 1) : ℤ) : ℝ)) / (N.value : ℝ) < 1 := by
      rw [hcast]
      apply (div_lt_iff₀ hNpos).2
      nlinarith
    have hout :
        ((a.val : ℝ) + (Q.value : ℝ) * ((-((m : ℤ) + 1) : ℤ) : ℝ)) / (N.value : ℝ) ∉
        Set.Icc (1 : ℝ) 2 := by
      intro hmem
      exact (not_le_of_gt hratio) hmem.1
    unfold cglRealSmoothBumpAffineHZeroTerm
    rw [w.toCGLSmoothBump.outside_support _ hout]
    simp
  have hneg : Summable fun m : ℕ =>
      cglRealSmoothBumpAffineHZeroTerm w N Q a (-((m : ℤ) + 1)) := by
    refine (summable_zero : Summable fun _ : ℕ => (0 : ℂ)).congr ?_
    intro m
    symm
    exact hnegpoint m
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  simp_rw [hnegpoint]
  simp

end RHTower
