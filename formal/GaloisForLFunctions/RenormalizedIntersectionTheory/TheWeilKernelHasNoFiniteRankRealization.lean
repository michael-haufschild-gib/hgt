import GaloisForLFunctions.RenormalizedIntersectionTheory.TheWeilKernelHasInfinitelyManyPositiveSquares
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep

/-!
# Weil's kernel has no finite-rank realization

A proved Hodge index exists for arithmetic surfaces `X → Spec O_K` (Faltings–Hriljac): on classes of
degree zero on the fibres and orthogonal to the vertical components the intersection pairing is
minus the Néron–Tate height. The numerical classes it controls form a finite-dimensional space
(Mordell–Weil plus vertical components). If the scaling classes `Γ_u`, `u ∈ ℚ_{>0}`, were divisor
classes on one such surface with `Γ_u · Γ_v = K_ζ(u⁻¹v)`, Weil's kernel would be a Hermitian form of
finite rank on `ℚ_{>0}`:

`K_ζ(x⁻¹y) = Σ_{i<r} ε_i f_i(x)^* f_i(y)`  (`HasFiniteRankRealization`),

the pole plane contributing two of the `r` terms. This module shows that this is impossible unless
`ζ` has infinitely many zeros right of the critical line.

* **Inertia of a finite-rank kernel** (`posIndex_le_of_realization`, `negIndex_le_of_realization`):
  every Gram matrix factors as `Aᴴ diag(ε) A` with `A` of size `r × n`, so its positive and negative
  indices are at most `r`.
* **The obstruction** (`rightZeros_infinite_of_realization`): on the finite stratum Weil's kernel has
  infinitely many positive squares (`posIndex_zetaKernel_eq_top_of_finite`), so a finite-rank
  realization forces infinitely many right zeros. Under RH there is none
  (`not_realization_of_riemannHypothesis`).

So a geometric producer of the Hodge index on scaling classes cannot be one arithmetic surface, nor
any finite-dimensional cohomology with a finite-dimensional height pairing: it must be a tower whose
ranks grow without bound, each finite Gram matrix being realized at some finite level.
-/

open Complex Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (rightZeros)
open Zeta23

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

variable {G : Type*} [Group G]

/-- `k` is a Hermitian form of rank at most `r` on `G`: `k(x⁻¹y) = Σ_{i<r} ε_i f_i(x)^* f_i(y)`. -/
def HasFiniteRankRealization (k : G → ℂ) (r : ℕ) : Prop :=
  ∃ (ε : Fin r → ℝ) (f : Fin r → G → ℂ),
    ∀ x y : G, k (x⁻¹ * y) = ∑ i, (ε i : ℂ) * conj (f i x) * f i y

/-- On a finite family the Gram matrix of a rank-`r` realization is `Aᴴ diag(ε) A`. -/
theorem gram_eq_of_realization {k : G → ℂ} {r : ℕ} {ε : Fin r → ℝ} {f : Fin r → G → ℂ}
    (hk : ∀ x y : G, k (x⁻¹ * y) = ∑ i, (ε i : ℂ) * conj (f i x) * f i y)
    {ι : Type*} [Fintype ι] (x : ι → G) :
    HeckeKreinToeplitz.gram k x = (Matrix.of fun i b => f i (x b))ᴴ *
      (diagonal (fun i => (ε i : ℂ)) * Matrix.of fun i b => f i (x b)) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [HeckeKreinToeplitz.gram, hk, Matrix.diagonal_mul, conjTranspose_apply, of_apply,
    Complex.star_def]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **A rank-`r` kernel has at most `r` positive squares on every finite family.** -/
theorem hermPosIndex_gram_le_of_realization {k : G → ℂ} {r : ℕ} {ε : Fin r → ℝ}
    {f : Fin r → G → ℂ} (hk : ∀ x y : G, k (x⁻¹ * y) = ∑ i, (ε i : ℂ) * conj (f i x) * f i y)
    {ι : Type*} [Fintype ι] (x : ι → G) : hermPosIndex (gram k x) ≤ r := by
  classical
  set A : Matrix (Fin r) ι ℂ := Matrix.of fun i b => f i (x b)
  obtain ⟨W, hW, hpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (HeckeKreinToeplitz.gram k x)
  have hzero : ∀ c : ι → ℂ, A *ᵥ c = 0 → hermQuad (HeckeKreinToeplitz.gram k x) c = 0 := by
    intro c hc
    rw [gram_eq_of_realization hk x, hermQuad, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    simp [A, hc]
  have hinj : Function.Injective (A.mulVecLin.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    by_contra hw0
    have hne : (w : ι → ℂ) ≠ 0 := fun h => hw0 (Subtype.ext h)
    have h1 := hpos w w.2 hne
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, Matrix.mulVecLin_apply] at hw
    rw [hzero _ hw] at h1
    exact lt_irrefl _ h1
  rw [← hW]
  calc Module.finrank ℂ W ≤ Module.finrank ℂ (Fin r → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = r := by simp

/-- **Positive index of a finite-rank kernel.** -/
theorem posIndex_le_of_realization {k : G → ℂ} {r : ℕ} (h : HasFiniteRankRealization k r) :
    posIndex k ≤ r := by
  obtain ⟨ε, f, hk⟩ := h
  unfold posIndex HeckeKreinToeplitz.negIndex
  refine iSup_le fun n => iSup_le fun x => ?_
  rw [gram_neg, hermNegIndex, neg_neg]
  exact_mod_cast hermPosIndex_gram_le_of_realization hk x

/-- **Negative index of a finite-rank kernel.** -/
theorem negIndex_le_of_realization {k : G → ℂ} {r : ℕ} (h : HasFiniteRankRealization k r) :
    HeckeKreinToeplitz.negIndex k ≤ r := by
  obtain ⟨ε, f, hk⟩ := h
  have hneg : HasFiniteRankRealization (fun g => -k g) r :=
    ⟨fun i => -ε i, f, fun x y => by
      show -k (x⁻¹ * y) = _
      rw [hk, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring⟩
  have h := posIndex_le_of_realization hneg
  unfold posIndex at h
  simpa only [neg_neg] using h

/-- **A finite-rank realization of Weil's kernel forces infinitely many right zeros.** -/
theorem rightZeros_infinite_of_realization {r : ℕ}
    (h : HasFiniteRankRealization zetaKernel r) : (rightZeros zetaZeroConfig).Infinite := by
  intro hfin
  have htop := posIndex_zetaKernel_eq_top_of_finite hfin
  have hle := posIndex_le_of_realization h
  rw [htop] at hle
  exact absurd hle (by simp)

/-- **Under RH Weil's kernel has no finite-rank realization**: no single finite-dimensional height
pairing carries the intersection numbers of all scaling classes. -/
theorem not_realization_of_riemannHypothesis (hRH : RiemannHypothesis) (r : ℕ) :
    ¬ HasFiniteRankRealization zetaKernel r := by
  intro h
  have h0 := riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp hRH
  rw [negIndex_zetaKernel, Set.encard_eq_zero] at h0
  exact rightZeros_infinite_of_realization h (h0 ▸ Set.finite_empty)

end GaloisForLFunctions.RenormalizedIntersectionTheory
