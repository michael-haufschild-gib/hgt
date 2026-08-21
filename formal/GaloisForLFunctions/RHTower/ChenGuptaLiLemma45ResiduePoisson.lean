/-
# Chen--Gupta--Li Lemma 4.5 character residue completion

Partitions a finite normalized character kernel into residue classes and extends every positive affine ray to its full integer lattice. This is the exact input required for the affine Poisson formula in each coordinate of CGL Lemma 4.5.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45ResidueLattice

open scoped BigOperators

noncomputable section

namespace RHTower

/-- One positive affine residue ray carrying a character-pair `h_t` kernel. -/
def cglLemma45CharacterPairAffineNatTerm (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ)
    (a : ZMod Q.value) (m : ℕ) : ℂ :=
  χ a * (starRingEnd ℂ) (ψ a) *
    cglSmoothBumpHt w.toCGLSmoothBump t
      (((a.val : ℝ) + Q.value * (m : ℝ)) / N.value)

/-- Exact residue-class partition of the finite-support character `h_t` lattice sum. -/
theorem cglLemma45CharacterPairHtnatTerm_tsum_eq_residueNatSum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    ∑' n : ℕ, cglLemma45CharacterPairHtnatTerm w N Q χ ψ t n =
      ∑ a : ZMod Q.value, ∑' m : ℕ,
        cglLemma45CharacterPairAffineNatTerm w N Q χ ψ t a m := by
  letI : NeZero Q.value := ⟨Nat.ne_of_gt Q.positive⟩
  rw [Nat.sumByResidueClasses
    (cglLemma45CharacterPairHtnatTerm_summable w N Q χ ψ t) Q.value]
  apply Finset.sum_congr rfl
  intro a ha
  apply tsum_congr
  intro m
  unfold cglLemma45CharacterPairHtnatTerm cglLemma45CharacterPairAffineNatTerm
  rw [cglDirichletCharacter_eval_affine_residue,
    cglDirichletCharacter_eval_affine_residue]
  have harg : ((a.val + Q.value * m : ℕ) : ℝ) / N.value =
      ((a.val : ℝ) + Q.value * (m : ℝ)) / N.value := by
    norm_cast
  rw [harg]

/-- One full integer affine residue lattice carrying a character-pair `h_t` kernel. -/
def cglLemma45CharacterPairAffineIntTerm (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ)
    (a : ZMod Q.value) (k : ℤ) : ℂ :=
  χ a * (starRingEnd ℂ) (ψ a) *
    cglSmoothBumpHt w.toCGLSmoothBump t
      (((a.val : ℝ) + Q.value * (k : ℝ)) / N.value)

/-- Each positive affine ray has finite support, hence a closed summability certificate. -/
theorem cglLemma45CharacterPairAffineNatTerm_summable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ)
    (a : ZMod Q.value) :
    Summable (cglLemma45CharacterPairAffineNatTerm w N Q χ ψ t a) := by
  apply summable_of_hasFiniteSupport
  refine (Set.finite_Iic (2 * N.value)).subset ?_
  intro m hm
  simp only [Function.mem_support] at hm
  have hk : cglSmoothBumpHtValue w.toCGLSmoothBump t
      (((a.val : ℝ) + Q.value * (m : ℝ)) / N.value) ≠ 0 := by
    intro hzero
    apply hm
    have hvalue : cglSmoothBumpHt w.toCGLSmoothBump t
        (((a.val : ℝ) + Q.value * (m : ℝ)) / N.value) = 0 := by
      rw [cglSmoothBumpHt_apply]
      exact hzero
    unfold cglLemma45CharacterPairAffineNatTerm
    rw [hvalue]
    simp
  have hbounds : (((a.val : ℝ) + Q.value * (m : ℝ)) / N.value) ∈ Set.Icc (1 : ℝ) 2 :=
    cglSmoothBumpHtValue_support_subset w.toCGLSmoothBump t hk
  by_contra hbound
  have hgt : 2 * N.value < m := lt_of_not_ge hbound
  have hqm : m ≤ Q.value * m := Nat.le_mul_of_pos_left m Q.positive
  have hnum : 2 * N.value < a.val + Q.value * m := by omega
  have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hratio : 2 < ((a.val : ℝ) + Q.value * (m : ℝ)) / N.value := by
    apply (lt_div_iff₀ hNpos).2
    exact_mod_cast hnum
  exact (not_le_of_gt hratio) hbounds.2

/-- Compact support removes the negative part of every affine character ray. -/
theorem cglLemma45CharacterPairAffineIntTerm_tsum_eq_natSum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ)
    (a : ZMod Q.value) :
    ∑' k : ℤ, cglLemma45CharacterPairAffineIntTerm w N Q χ ψ t a k =
      ∑' m : ℕ, cglLemma45CharacterPairAffineNatTerm w N Q χ ψ t a m := by
  have hnat : ∀ m : ℕ,
      cglLemma45CharacterPairAffineIntTerm w N Q χ ψ t a (m : ℤ) =
        cglLemma45CharacterPairAffineNatTerm w N Q χ ψ t a m := by
    intro m
    unfold cglLemma45CharacterPairAffineIntTerm cglLemma45CharacterPairAffineNatTerm
    simp only [Int.cast_natCast]
  have hpos : Summable fun m : ℕ =>
      cglLemma45CharacterPairAffineIntTerm w N Q χ ψ t a (m : ℤ) := by
    refine (cglLemma45CharacterPairAffineNatTerm_summable w N Q χ ψ t a).congr ?_
    intro m
    symm
    exact hnat m
  have hnegpoint : ∀ m : ℕ,
      cglLemma45CharacterPairAffineIntTerm w N Q χ ψ t a (-((m : ℤ) + 1)) = 0 := by
    intro m
    have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
    have ha : (a.val : ℝ) < Q.value := by exact_mod_cast a.val_lt
    have hmnonneg : 0 ≤ (m : ℝ) := by positivity
    have hcast : (((-((m : ℤ) + 1) : ℤ) : ℝ)) = -((m : ℝ) + 1) := by
      push_cast
      ring
    have hratio :
        ((a.val : ℝ) + (Q.value : ℝ) * ((-((m : ℤ) + 1) : ℤ) : ℝ)) / N.value < 1 := by
      rw [hcast]
      apply (div_lt_iff₀ hNpos).2
      nlinarith
    have hout :
        ((a.val : ℝ) + (Q.value : ℝ) * ((-((m : ℤ) + 1) : ℤ) : ℝ)) / N.value ∉
          Set.Icc (1 : ℝ) 2 := by
      intro hmem
      exact (not_le_of_gt hratio) hmem.1
    unfold cglLemma45CharacterPairAffineIntTerm
    rw [cglSmoothBumpHt_apply, cglSmoothBumpHtValue,
      w.toCGLSmoothBump.outside_support _ hout]
    simp
  have hneg : Summable fun m : ℕ =>
      cglLemma45CharacterPairAffineIntTerm w N Q χ ψ t a (-((m : ℤ) + 1)) := by
    refine (summable_zero : Summable fun _ : ℕ => (0 : ℂ)).congr ?_
    intro m
    symm
    exact hnegpoint m
  calc
    ∑' k : ℤ, cglLemma45CharacterPairAffineIntTerm w N Q χ ψ t a k =
        ∑' m : ℕ, cglLemma45CharacterPairAffineIntTerm w N Q χ ψ t a (m : ℤ) +
          ∑' m : ℕ, cglLemma45CharacterPairAffineIntTerm w N Q χ ψ t a (-((m : ℤ) + 1)) :=
      tsum_of_nat_of_neg_add_one hpos hneg
    _ = ∑' m : ℕ, cglLemma45CharacterPairAffineIntTerm w N Q χ ψ t a (m : ℤ) := by
      simp_rw [hnegpoint]
      simp
    _ = _ := by
      apply tsum_congr
      exact hnat

end RHTower
