/-
# Chen--Gupta--Li Lemma 4.5 character residue lattice

The finite normalized character kernels from the cubic trace are extended to
the positive integer lattice.  Compact support proves this extension has no
extra terms, preparing the exact residue-class/Poisson decomposition.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45CubicKernel
import GaloisForLFunctions.RHTower.ChenGuptaLiHtFirstDerivative
import Mathlib.Analysis.SumOverResidueClass

open scoped BigOperators

noncomputable section

namespace RHTower

/-- A Dirichlet character is constant along each natural affine residue ray. -/
theorem cglDirichletCharacter_eval_affine_residue
    (Q : CGLPositiveModulus) (χ : DirichletCharacter ℂ Q.value)
    (a : ZMod Q.value) (m : ℕ) :
    χ ((a.val + Q.value * m : ℕ) : ZMod Q.value) = χ a := by
  have hres : (a.val : ZMod Q.value) + (Q.value : ZMod Q.value) *
      (m : ZMod Q.value) = a := by
    simp
  simpa only [Nat.cast_add, Nat.cast_mul] using congrArg χ hres

/-- The positive-integer character product times CGL's normalized `h_t`
kernel. -/
def cglLemma45CharacterPairHtnatTerm (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ) (n : ℕ) : ℂ :=
  χ n * (starRingEnd ℂ) (ψ n) *
    cglSmoothBumpHt w.toCGLSmoothBump t ((n : ℝ) / N.value)

/-- The character-weighted `h_t` lattice kernel has support in CGL's literal
open dyadic block.  The endpoint `n=N` vanishes because the cutoff vanishes at
one. -/
theorem cglLemma45CharacterPairHtnatTerm_support_subset_dyadicBlock
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    Function.support (cglLemma45CharacterPairHtnatTerm w N Q χ ψ t) ⊆
      cglCharacterDyadicBlock N := by
  intro n hn
  simp only [Function.mem_support] at hn
  have hk : cglSmoothBumpHtValue w.toCGLSmoothBump t ((n : ℝ) / N.value) ≠ 0 := by
    intro hzero
    apply hn
    simp [cglLemma45CharacterPairHtnatTerm, cglSmoothBumpHt_apply, hzero]
  have hratio : ((n : ℝ) / N.value) ∈ Set.Icc (1 : ℝ) 2 :=
    cglSmoothBumpHtValue_support_subset w.toCGLSmoothBump t hk
  have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hlow : N.value ≤ n := by
    have hlowReal : (N.value : ℝ) ≤ n := by
      simpa using (le_div_iff₀ hNpos).mp hratio.1
    exact_mod_cast hlowReal
  have hne : N.value ≠ n := by
    intro heq
    subst n
    apply hk
    have hdiv : (N.value : ℝ) / N.value = 1 := div_self (ne_of_gt hNpos)
    rw [cglSmoothBumpHtValue, hdiv, cglSmoothBump_value_one]
    simp
  have hupp : n ≤ 2 * N.value := by
    have huppReal : (n : ℝ) ≤ 2 * N.value := (div_le_iff₀ hNpos).mp hratio.2
    exact_mod_cast huppReal
  change n ∈ Finset.Ioc N.value (2 * N.value)
  exact Finset.mem_Ioc.mpr ⟨lt_of_le_of_ne hlow hne, hupp⟩

/-- The positive character kernel is summable for its closed finite-support
reason, with no analytic summability premise. -/
theorem cglLemma45CharacterPairHtnatTerm_summable
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    Summable (cglLemma45CharacterPairHtnatTerm w N Q χ ψ t) :=
  summable_of_hasFiniteSupport <|
    (Finset.finite_toSet (cglCharacterDyadicBlock N)).subset
      (cglLemma45CharacterPairHtnatTerm_support_subset_dyadicBlock w N Q χ ψ t)

/-- The full positive-integer character kernel equals its literal finite CGL
column sum exactly. -/
theorem cglLemma45CharacterPairHtnatTerm_tsum_eq_finSum
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (χ ψ : DirichletCharacter ℂ Q.value) (t : ℝ) :
    ∑' n : ℕ, cglLemma45CharacterPairHtnatTerm w N Q χ ψ t n =
      ∑ j : Fin N.value,
        χ (cglCharacterDyadicIndex N.value j) *
          (starRingEnd ℂ) (ψ (cglCharacterDyadicIndex N.value j)) *
          cglSmoothBumpHt w.toCGLSmoothBump t
            ((cglCharacterDyadicIndex N.value j : ℝ) / N.value) := by
  calc
    ∑' n : ℕ, cglLemma45CharacterPairHtnatTerm w N Q χ ψ t n =
        ∑ n ∈ cglCharacterDyadicBlock N, cglLemma45CharacterPairHtnatTerm w N Q χ ψ t n := by
      apply tsum_eq_sum
      intro n hn
      by_contra hterm
      apply hn
      apply cglLemma45CharacterPairHtnatTerm_support_subset_dyadicBlock w N Q χ ψ t
      simpa only [Function.mem_support] using hterm
    _ = _ := cglCharacterDyadicBlock_sum_eq_sum_fin N _

end RHTower
