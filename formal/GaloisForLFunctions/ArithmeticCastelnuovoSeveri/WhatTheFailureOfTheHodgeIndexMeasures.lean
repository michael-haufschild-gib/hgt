import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SchurLendingOddHodgeIndexPastFirstPrime
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfRightZeros
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AlmostEveryPrimeSeesEveryRightZero
import GaloisForLFunctions.SquareRootThreshold.TheWidthBoundsTheEnergyNormalisedWeilFloor
import GaloisForLFunctions.SquareRootThreshold.TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster
import GaloisForLFunctions.RHTower.OffLineClusterWeilUnbounded

/-!
# What the failure of the Hodge index measures

On the scaling surface of `ℤ` (and on any tempered zero configuration `Z`), the failure of the
arithmetic Hodge index has two complementary invariants:

1. **The cardinal invariant (the Hodge defect):** the excess number of positive squares of the
   intersection form beyond the single positive square of the pole plane `⟨H, V⟩` — equivalently,
   by Haynsworth's signature law (`posIndex_intersectionGram`), the number of negative squares of
   Weil's quadratic form `W_Z`.
2. **The metric invariant (the defect floor):** the exponential growth rate in the degree `r` of
   the lower bound of the Castelnuovo–Severi defect `δ(x, x)` on cycles of degree `r`.

This module establishes the complete metrology of both invariants, answering §6.1 Question 2 of
the programme:

* **Exact degree-by-degree and global reflection-sector additivity (`hodgeDefectAt_eq_sectorHodgeDefectAt_add`,
  `rightZeros_encard_eq_sectorZeros_add`):** For any functional-equation-symmetric tempered
  configuration `Z`, the even (`s = 1`) and odd (`s = -1`) reflection sectors are mutually
  orthogonal under `W_Z` (`W_eq_zero_of_even_odd`), and the Hodge defect splits additively at
  **every** support degree `a`:
  $$\operatorname{hodgeDefectAt}(Z, a)
    = \operatorname{sectorHodgeDefectAt}(Z, 1, a) + \operatorname{sectorHodgeDefectAt}(Z, -1, a).$$
  Taking the supremum over `a` recovers the global cardinal decomposition
  $$(\operatorname{rightZeros} Z).\operatorname{encard}
    = (\operatorname{sectorZeros} Z\, 1).\operatorname{encard}
      + (\operatorname{sectorZeros} Z\, (-1)).\operatorname{encard},$$
  where the difference between the odd and even sector defects is the exact cardinal of real
  off-line zeros `{ρ ∈ rightZeros Z | Im ρ = 0}.encard`. For `ζ` (`zetaZeroConfig`), which has no
  real zeros in `(0, 1)`, the two reflection sectors carry identical global defect equal to half
  the total defect (`zeta_rightZeros_encard_eq_two_mul_sectorZeros`), while at every degree
  `a ≤ 181/500` past the first prime `(1/2) log 2` the odd sector contributes `0` and any full
  Hodge defect is purely even (`zeta_hodgeDefectAt_eq_even_sectorHodgeDefectAt_of_le`).

* **Symmetrized Hecke orbits carry each reflection sector (`cyclic_sector_pontryagin_law`):**
  For any spectrally generic seed test `g` and any dense shift set `D ⊆ ℝ`, the `s`-sector
  symmetrized Hecke translates
  $$\operatorname{symmTranslate}(s, d, g) := \tfrac{1}{2}\bigl(T_d g + s\,\operatorname{testNeg}(T_d g)\bigr)$$
  lie in sector `s` (`s = ±1`) and achieve the full sector Hodge defect `(sectorZeros Z s).encard`
  on finite subsets of `D`. For `ζ`, both the rational Hecke shift group `ratHeckeShifts` and any
  two-prime subgroup `twoPrimeShifts p q = ℤ log p + ℤ log q` (`p ≠ q`) carry the entire sector
  defect `{ρ ∈ rightZeros zetaZeroConfig | 0 < Im ρ}.encard` on a single generic test
  (`zeta_cyclic_sector_hodgeDefect_ratHecke`, `zeta_cyclic_sector_hodgeDefect_twoPrimes`).

* **Depth and multiplicity invariance (`iSup_hodgeDefectAt_eq_of_rightZeros_encard_eq`,
  `multiPairConfig_depth_invariance`, `offLineClusterConfig_hodgeDefect_vs_l2_floor`):**
  The Hodge defect depends solely on the set of distinct carrier points right of the critical line,
  never on their multiplicities `Z.mult` or their depths `Re ρ - 1/2 > 0`. On `multiPairConfig γ δ`,
  changing the depth profile `δ : Fin m → (0, 1/2)` at fixed ordinates `γ` leaves the global
  defect `2m`, the sector defects `m`, the visibility threshold `mπ / (2 Σ γ_k)`, and the
  saturation threshold `mπ / min γ_k` completely unchanged. On `RHTower.offLineClusterConfig`,
  every zero has fixed depth `1/4` and every `n`-test family has `hermNegIndex ≤ n`, whereas the
  unbounded off-line multiplicities `k + 1` drive the raw `L²`-normalised Weil floor at fixed
  degree to `-∞`.

* **Unconditional growth rate of the defect floor equals the zero width
  (`zetaZeroWidth_le_iff_scalingSubsurface_odd_h1_defect_floor`,
  `oddDefectFloorRate_eq_zetaZeroWidth`, `fullDefectFloorRate_eq_zetaZeroWidth`):**
  For every `C²_c` test `F`, the Chebyshev-gauge derivative of its autocorrelation is bounded
  uniformly by the `H¹` Sobolev energy `∫ (F² + (F')²)` (`abs_gaugeDerivative_autocorr_le_h1`),
  and the two-bump difference lag family has `H¹` energy bounded uniformly in the lag. Hence,
  **unconditionally** (with no `OffLineCopiesLocallyBounded` or non-clustering hypothesis),
  `zetaZeroWidth ≤ σ` iff at every rate `β > σ` the `H¹`-normalised Castelnuovo–Severi defect on
  `scalingSubsurface (oddRealTestsAt r)` (or `scalingSubsurface (realTestsAt r)`) is bounded below
  by `-C e^{2β r} ∫ (f² + (f')²)`. Consequently, the infimum of admissible defect-floor growth
  exponents on the scaling surface equals `zetaZeroWidth` unconditionally.
-/

open Complex Matrix Filter Topology MeasureTheory Set Finset
open scoped ComplexConjugate lp
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

set_option autoImplicit false

/-! ### 1. Hermitian inertia subadditivity and block-diagonal additivity -/

/-- On a tempered configuration, Weil's sesquilinear form is Hermitian-symmetric on `C²_c` tests. -/
theorem W_conj_symm (Z : ZeroConfig) (hZ : TemperedConfig Z) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    conj (Z.W g f) = Z.W f g := by
  rw [← inner_reflectVec_fesVec Z hZ hg hgc hf hfc, inner_reflectVec_symm,
    inner_reflectVec_fesVec Z hZ hf hfc hg hgc]

/-- The zero-side Gram matrix of a finite family of `C²_c` tests on a tempered configuration is
Hermitian. -/
theorem zeroGram_isHermitian (Z : ZeroConfig) (hZ : TemperedConfig Z) {ι : Type*}
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    (zeroGram Z f).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_def, zeroGram]
  exact W_conj_symm Z hZ (hf i) (hfc i) (hf j) (hfc j)

/-- The Hermitian quadratic form is additive in the matrix argument. -/
theorem hermQuad_add {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : ι → ℂ) :
    hermQuad (A + B) x = hermQuad A x + hermQuad B x := by
  simp only [hermQuad, Matrix.add_mulVec, dotProduct_add, Complex.add_re]

/-- Linear functional extracting the `k`-th negative-eigenspace coordinate of a Hermitian matrix. -/
def negEigenFunctional {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (k : {i : ι // hH.eigenvalues i < 0}) : (ι → ℂ) →ₗ[ℂ] ℂ :=
  (LinearMap.proj k.1).comp ((hH.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ).mulVecLin

/-- On the common kernel of its negative-eigenspace functionals, a Hermitian matrix has nonnegative
quadratic form. -/
theorem hermQuad_nonneg_of_negEigenFunctional_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (x : ι → ℂ)
    (hx : ∀ k, negEigenFunctional hH k x = 0) :
    0 ≤ hermQuad H x := by
  set U : Matrix ι ι ℂ := hH.eigenvectorUnitary
  set y : ι → ℂ := Uᴴ *ᵥ x
  have hUy : U *ᵥ y = x := by
    change U *ᵥ (Uᴴ *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, Unitary.coe_mul_star_self,
      Matrix.one_mulVec]
  have hquad : hermQuad H x = ∑ i, hH.eigenvalues i * Complex.normSq (y i) := by
    rw [← hUy, ← hermQuad_conjugate H U y, conjTranspose_mul_mul_eigenvectorUnitary hH,
      hermQuad_diagonal]
  rw [hquad]
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hi : hH.eigenvalues i < 0
  · have hy0 : y i = 0 := hx ⟨i, hi⟩
    rw [hy0, Complex.normSq_zero, mul_zero]
  · exact mul_nonneg (not_lt.mp hi) (Complex.normSq_nonneg _)

/-- **Subadditivity of the negative index.** For any two Hermitian matrices `A, B`,
`hermNegIndex (A + B) ≤ hermNegIndex A + hermNegIndex B`. -/
theorem negIndex_add_le {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hermNegIndex (A + B) ≤ hermNegIndex A + hermNegIndex B := by
  classical
  have hle := negIndex_le_card_of_nonneg_on_ker (A + B)
    (Sum.elim (negEigenFunctional hA) (negEigenFunctional hB)) fun x hx => by
      rw [hermQuad_add]
      exact add_nonneg
        (hermQuad_nonneg_of_negEigenFunctional_eq_zero hA x fun k => hx (Sum.inl k))
        (hermQuad_nonneg_of_negEigenFunctional_eq_zero hB x fun k => hx (Sum.inr k))
  rw [Fintype.card_sum, Fintype.card_subtype, Fintype.card_subtype,
    ← negIndex_eq_card_neg_eigenvalues hA, ← negIndex_eq_card_neg_eigenvalues hB] at hle
  exact hle

/-- The Hermitian quadratic form on a block-diagonal matrix `fromBlocks A 0 0 B` splits as the sum
of the quadratic forms on the two blocks. -/
theorem hermQuad_fromBlocks_zero {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) (x : α → ℂ) (y : β → ℂ) :
    hermQuad (fromBlocks A 0 0 B) (Sum.elim x y) = hermQuad A x + hermQuad B y := by
  simp only [hermQuad, star_sum_elim, fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
     sum_elim_dotProduct_sum_elim, Complex.add_re]

/-- **Superadditivity of the negative index on block-diagonal matrices.** For any matrices `A` and
`B`, `hermNegIndex A + hermNegIndex B ≤ hermNegIndex (fromBlocks A 0 0 B)`. -/
theorem add_le_negIndex_fromBlocks_zero {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    hermNegIndex A + hermNegIndex B ≤ hermNegIndex (fromBlocks A 0 0 B) := by
  obtain ⟨WA, hrankA, hWA⟩ := exists_isPosDefOn_finrank_eq_posIndex (-A)
  obtain ⟨WB, hrankB, hWB⟩ := exists_isPosDefOn_finrank_eq_posIndex (-B)
  set e : ((α → ℂ) × (β → ℂ)) ≃ₗ[ℂ] (α ⊕ β → ℂ) :=
    (LinearEquiv.sumArrowLEquivProdArrow α β ℕ ℂ).symm
  set W : Submodule ℂ (α ⊕ β → ℂ) := (WA.prod WB).map e.toLinearMap
  have hpd : IsPosDefOn (-(fromBlocks A 0 0 B)) W := by
    rintro z ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ hz0
    have hxy0 : x ≠ 0 ∨ y ≠ 0 := by
      by_contra h
      push Not at h
      apply hz0
      ext k
      rcases k with i | j <;> simp [e, h.1, h.2]
    have hform : hermQuad (-(fromBlocks A 0 0 B)) (e (x, y)) =
        hermQuad (-A) x + hermQuad (-B) y := by
      change -(hermQuad (fromBlocks A 0 0 B) (Sum.elim x y)) = -hermQuad A x + -hermQuad B y
      rw [hermQuad_fromBlocks_zero]
      ring
    rw [hform]
    have hAx : 0 ≤ hermQuad (-A) x := by
      by_cases hx0 : x = 0
      · subst hx0; simp [hermQuad]
      · exact (hWA x hx hx0).le
    have hBy : 0 ≤ hermQuad (-B) y := by
      by_cases hy0 : y = 0
      · subst hy0; simp [hermQuad]
      · exact (hWB y hy hy0).le
    rcases hxy0 with hx0 | hy0
    · linarith [hWA x hx hx0]
    · linarith [hWB y hy hy0]
  have hle := finrank_le_posIndex hpd
  have hrankW : Module.finrank ℂ W = hermNegIndex A + hermNegIndex B := by
    rw [Submodule.finrank_map_subtype_eq e, Module.finrank_prod, hrankA, hrankB,
      hermNegIndex, hermNegIndex]
  rwa [hrankW] at hle

/-! ### 2. Exact reflection-sector orthogonality, global partition, and degree-by-degree additivity -/

theorem paperFT_smul (c : ℂ) (f : ℝ → ℂ) (z : ℂ) :
    paperFT (c • f) z = c * paperFT f z := by
  simp only [paperFT, Pi.smul_apply, smul_eq_mul, mul_assoc, MeasureTheory.integral_const_mul]

theorem paperFT_add {f₁ f₂ : ℝ → ℂ} (h₁ : Continuous f₁) (h₁c : HasCompactSupport f₁)
    (h₂ : Continuous f₂) (h₂c : HasCompactSupport f₂) (z : ℂ) :
    paperFT (f₁ + f₂) z = paperFT f₁ z + paperFT f₂ z := by
  have hi₁ : Integrable fun u => f₁ u * cexp (I * z * u) :=
    (h₁.mul (by fun_prop)).integrable_of_hasCompactSupport h₁c.mul_right
  have hi₂ : Integrable fun u => f₂ u * cexp (I * z * u) :=
    (h₂.mul (by fun_prop)).integrable_of_hasCompactSupport h₂c.mul_right
  simp only [paperFT, Pi.add_apply, add_mul]
  exact integral_add hi₁ hi₂

theorem W_smul_left (Z : ZeroConfig) (c : ℂ) (f g : ℝ → ℂ) :
    Z.W (c • f) g = c * Z.W f g := by
  unfold ZeroConfig.W ZeroConfig.Wsummand
  simp only [paperFT_smul, mul_assoc, ← tsum_mul_left]

theorem W_smul_right (Z : ZeroConfig) (c : ℂ) (f g : ℝ → ℂ) :
    Z.W f (c • g) = conj c * Z.W f g := by
  unfold ZeroConfig.W ZeroConfig.Wsummand
  have h : (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * paperFT f (gammaOf ρ) *
      conj (paperFT (c • g) (conj (gammaOf ρ)))) =
      fun ρ : Z.carrier => conj c * ((Z.mult ρ : ℂ) * paperFT f (gammaOf ρ) *
        conj (paperFT g (conj (gammaOf ρ)))) := by
    funext ρ
    rw [paperFT_smul, map_mul]
    ring
  rw [h, tsum_mul_left]

theorem W_add_left (Z : ZeroConfig) (hZ : TemperedConfig Z) {f₁ f₂ g : ℝ → ℂ}
    (hf₁ : ContDiff ℝ 2 f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : ContDiff ℝ 2 f₂) (hf₂c : HasCompactSupport f₂)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Z.W (f₁ + f₂) g = Z.W f₁ g + Z.W f₂ g := by
  unfold ZeroConfig.W
  rw [← Summable.tsum_add (summable_Wsummand Z hZ hf₁ hf₁c hg hgc)
    (summable_Wsummand Z hZ hf₂ hf₂c hg hgc)]
  refine tsum_congr fun ρ => ?_
  simp only [ZeroConfig.Wsummand,
    paperFT_add hf₁.continuous hf₁c hf₂.continuous hf₂c]
  ring

theorem W_add_right (Z : ZeroConfig) (hZ : TemperedConfig Z) {f g₁ g₂ : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg₁ : ContDiff ℝ 2 g₁) (hg₁c : HasCompactSupport g₁)
    (hg₂ : ContDiff ℝ 2 g₂) (hg₂c : HasCompactSupport g₂) :
    Z.W f (g₁ + g₂) = Z.W f g₁ + Z.W f g₂ := by
  rw [← W_conj_symm Z hZ hf hfc (hg₁.add hg₂) (hg₁c.add hg₂c),
    W_add_left Z hZ hg₁ hg₁c hg₂ hg₂c hf hfc, map_add,
    W_conj_symm Z hZ hf hfc hg₁ hg₁c, W_conj_symm Z hZ hf hfc hg₂ hg₂c]

/-- **Reflection invariance of the Weil form.** On any functional-equation-symmetric configuration,
negating the argument of both tests leaves `W_Z` unchanged. -/
theorem W_testNeg {Z : ZeroConfig} (hFE : FESymmetric Z) (f g : ℝ → ℂ) :
    Z.W (testNeg f) (testNeg g) = Z.W f g := by
  unfold ZeroConfig.W
  rw [← (conjCarrier hFE).tsum_eq]
  exact tsum_congr fun ρ => (Wsummand_conj hFE f g ρ).symm

/-- **Orthogonality of the reflection sectors.** On any functional-equation-symmetric configuration,
every even test (`testNeg f = f`) and every odd test (`testNeg g = -g`) are orthogonal under `W_Z`. -/
theorem W_eq_zero_of_even_odd {Z : ZeroConfig} (hFE : FESymmetric Z) {f g : ℝ → ℂ}
    (hf : testNeg f = (1 : ℂ) • f) (hg : testNeg g = (-1 : ℂ) • g) :
    Z.W f g = 0 := by
  have h : Z.W f g = -Z.W f g := by
    calc Z.W f g = Z.W (testNeg f) (testNeg g) := (W_testNeg hFE f g).symm
      _ = Z.W f ((-1 : ℂ) • g) := by rw [hf, one_smul, hg]
      _ = -Z.W f g := by rw [W_smul_right]; simp
  linear_combination h / 2

/-- **Orthogonality of the reflection sectors (odd against even).** -/
theorem W_eq_zero_of_odd_even {Z : ZeroConfig} (hFE : FESymmetric Z) {f g : ℝ → ℂ}
    (hf : testNeg f = (-1 : ℂ) • f) (hg : testNeg g = (1 : ℂ) • g) :
    Z.W f g = 0 := by
  have h : Z.W f g = -Z.W f g := by
    calc Z.W f g = Z.W (testNeg f) (testNeg g) := (W_testNeg hFE f g).symm
      _ = Z.W ((-1 : ℂ) • f) g := by rw [hf, hg, one_smul]
      _ = -Z.W f g := by rw [W_smul_left]; simp
  linear_combination h / 2

/-- The real zeros of `Z` right of the critical line (`Re ρ > 1/2`, `Im ρ = 0`). -/
def realRightZeros (Z : ZeroConfig) : Set ℂ := {ρ ∈ rightZeros Z | ρ.im = 0}

/-- **The odd-sector zero set is the disjoint union of the even-sector zero set and the real right
zeros.** -/
theorem sectorZeros_neg_one_encard_eq_add_realRightZeros (Z : ZeroConfig) :
    (sectorZeros Z (-1)).encard = (sectorZeros Z 1).encard + (realRightZeros Z).encard := by
  have hunion : sectorZeros Z (-1) = sectorZeros Z 1 ∪ realRightZeros Z := by
    ext ρ
    simp only [sectorZeros_neg_one, sectorZeros_one, realRightZeros, mem_setOf_eq, mem_union]
    exact ⟨fun ⟨hρ, him⟩ => (lt_or_eq_of_le him).imp (fun h => ⟨hρ, h⟩) (fun h => ⟨hρ, h.symm⟩),
      by rintro (⟨hρ, him⟩ | ⟨hρ, him⟩); exacts [⟨hρ, him.le⟩, ⟨hρ, him.symm.le⟩]⟩
  have hdisj : Disjoint (sectorZeros Z 1) (realRightZeros Z) := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, him1⟩ ⟨_, him0⟩
    exact him1.ne' him0
  rw [hunion, Set.encard_union_eq hdisj]

/-- **Global cardinal additivity of the reflection sectors.** For any functional-equation-symmetric
zero configuration `Z`, the cardinal of `rightZeros Z` is the sum of the cardinals of the even and
odd sector zero sets:
`(rightZeros Z).encard = (sectorZeros Z 1).encard + (sectorZeros Z (-1)).encard`. -/
theorem rightZeros_encard_eq_sectorZeros_add {Z : ZeroConfig} (hFE : FESymmetric Z) :
    (rightZeros Z).encard = (sectorZeros Z 1).encard + (sectorZeros Z (-1)).encard := by
  set Sneg : Set ℂ := {ρ ∈ rightZeros Z | ρ.im < 0}
  have hunion : rightZeros Z = Sneg ∪ sectorZeros Z (-1) := by
    ext ρ
    simp only [Sneg, sectorZeros_neg_one, mem_setOf_eq, mem_union]
    exact ⟨fun hρ => (lt_or_ge ρ.im 0).imp (fun h => ⟨hρ, h⟩) (fun h => ⟨hρ, h⟩),
      by rintro (⟨hρ, _⟩ | ⟨hρ, _⟩) <;> exact hρ⟩
  have hdisj : Disjoint Sneg (sectorZeros Z (-1)) := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, hlt⟩ ⟨_, hge⟩
    exact not_lt.mpr hge hlt
  have himg : (starRingEnd ℂ) '' Sneg = sectorZeros Z 1 := by
    ext ρ
    simp only [mem_image, Sneg, sectorZeros_one, rightZeros, mem_setOf_eq]
    constructor
    · rintro ⟨τ, ⟨⟨hτC, hτre⟩, hτim⟩, rfl⟩
      refine ⟨⟨hFE.conj_mem τ hτC, by simpa using hτre⟩, ?_⟩
      simp only [Complex.conj_im, Left.neg_pos_iff]
      exact hτim
    · rintro ⟨⟨hρC, hρre⟩, hρim⟩
      refine ⟨conj ρ, ⟨⟨hFE.conj_mem ρ hρC, by simpa using hρre⟩, ?_⟩, conj_conj ρ⟩
      simp only [Complex.conj_im, Left.neg_neg_iff]
      exact hρim
  rw [hunion, Set.encard_union_eq hdisj, ← himg,
    (RingHom.injective (starRingEnd ℂ)).encard_image]

/-- For `ζ`, the total cardinal of right zeros is twice the cardinal of either reflection sector. -/
theorem zeta_rightZeros_encard_eq_two_mul_sectorZeros {s : ℂ} (hs : s = 1 ∨ s = -1) :
    (rightZeros zetaZeroConfig).encard = 2 * (sectorZeros zetaZeroConfig s).encard := by
  rw [rightZeros_encard_eq_sectorZeros_add zetaZeroConfig_feSymmetric,
    zeta_sectorZeros_eq (Or.inl rfl), zeta_sectorZeros_eq (Or.inr rfl),
    zeta_sectorZeros_eq hs, two_mul]

/-- The even projection `(1/2)(f + testNeg f)` of a test function. -/
def evenProj (f : ℝ → ℂ) : ℝ → ℂ := (2 : ℂ)⁻¹ • (f + testNeg f)

/-- The odd projection `(1/2)(f - testNeg f)` of a test function. -/
def oddProj (f : ℝ → ℂ) : ℝ → ℂ := (2 : ℂ)⁻¹ • (f - testNeg f)

theorem evenProj_add_oddProj (f : ℝ → ℂ) : evenProj f + oddProj f = f := by
  funext u
  simp only [evenProj, oddProj, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem evenProj_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (evenProj f) :=
  (hf.add (testNeg_contDiff hf)).const_smul (2 : ℂ)⁻¹

theorem oddProj_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (oddProj f) :=
  (hf.sub (testNeg_contDiff hf)).const_smul (2 : ℂ)⁻¹

theorem evenProj_hasCompactSupport {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (evenProj f) :=
  (hfc.add (testNeg_hasCompactSupport hfc)).smul_left

theorem oddProj_hasCompactSupport {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (oddProj f) :=
  (hfc.sub (testNeg_hasCompactSupport hfc)).smul_left

theorem testNeg_evenProj (f : ℝ → ℂ) : testNeg (evenProj f) = (1 : ℂ) • evenProj f := by
  funext u
  simp only [evenProj, testNeg, Pi.smul_apply, Pi.add_apply, smul_eq_mul, neg_neg, one_mul]
  ring

theorem testNeg_oddProj (f : ℝ → ℂ) : testNeg (oddProj f) = (-1 : ℂ) • oddProj f := by
  funext u
  simp only [oddProj, testNeg, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, neg_neg]
  ring

theorem evenProj_support {f : ℝ → ℂ} {a : ℝ} (hsupp : ∀ u, a < |u| → f u = 0) :
    ∀ u, a < |u| → evenProj f u = 0 := by
  intro u hu
  have hu' : a < |-u| := by rwa [abs_neg]
  simp [evenProj, testNeg, hsupp u hu, hsupp (-u) hu']

theorem oddProj_support {f : ℝ → ℂ} {a : ℝ} (hsupp : ∀ u, a < |u| → f u = 0) :
    ∀ u, a < |u| → oddProj f u = 0 := by
  intro u hu
  have hu' : a < |-u| := by rwa [abs_neg]
  simp [oddProj, testNeg, hsupp u hu, hsupp (-u) hu']

/-- On any functional-equation-symmetric tempered configuration, the Gram matrix of a finite family
`f` is the sum of the Gram matrices of its even and odd projections. -/
theorem zeroGram_eq_evenProj_add_oddProj (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) {ι : Type*} (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    zeroGram Z f = zeroGram Z (fun i => evenProj (f i)) + zeroGram Z (fun i => oddProj (f i)) := by
  ext i j
  simp only [Matrix.add_apply, zeroGram]
  conv_lhs => rw [← evenProj_add_oddProj (f i), ← evenProj_add_oddProj (f j)]
  rw [W_add_left Z hZ (evenProj_contDiff (hf i)) (evenProj_hasCompactSupport (hfc i))
    (oddProj_contDiff (hf i)) (oddProj_hasCompactSupport (hfc i))
    ((evenProj_contDiff (hf j)).add (oddProj_contDiff (hf j)))
    ((evenProj_hasCompactSupport (hfc j)).add (oddProj_hasCompactSupport (hfc j))),
    W_add_right Z hZ (evenProj_contDiff (hf i)) (evenProj_hasCompactSupport (hfc i))
      (evenProj_contDiff (hf j)) (evenProj_hasCompactSupport (hfc j))
      (oddProj_contDiff (hf j)) (oddProj_hasCompactSupport (hfc j)),
    W_add_right Z hZ (oddProj_contDiff (hf i)) (oddProj_hasCompactSupport (hfc i))
      (evenProj_contDiff (hf j)) (evenProj_hasCompactSupport (hfc j))
      (oddProj_contDiff (hf j)) (oddProj_hasCompactSupport (hfc j)),
    W_eq_zero_of_even_odd hFE (testNeg_evenProj (f i)) (testNeg_oddProj (f j)),
    W_eq_zero_of_odd_even hFE (testNeg_oddProj (f i)) (testNeg_evenProj (f j))]
  ring

/-- **Exact degree-by-degree sector additivity of the Hodge defect.** On any functional-equation-symmetric
tempered configuration `Z`, at every support degree `a : ℝ` the full Hodge defect is the sum of the
even-sector and odd-sector Hodge defects:
`hodgeDefectAt Z a = sectorHodgeDefectAt Z 1 a + sectorHodgeDefectAt Z (-1) a`. -/
theorem hodgeDefectAt_eq_sectorHodgeDefectAt_add (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) (a : ℝ) :
    hodgeDefectAt Z a = sectorHodgeDefectAt Z 1 a + sectorHodgeDefectAt Z (-1) a := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun n => iSup_le fun ⟨f, hf, hfc, hsupp⟩ => ?_
    have hG := zeroGram_eq_evenProj_add_oddProj Z hZ hFE f hf hfc
    have hle := negIndex_add_le
      (zeroGram_isHermitian Z hZ (fun i => evenProj (f i))
        (fun i => evenProj_contDiff (hf i)) (fun i => evenProj_hasCompactSupport (hfc i)))
      (zeroGram_isHermitian Z hZ (fun i => oddProj (f i))
        (fun i => oddProj_contDiff (hf i)) (fun i => oddProj_hasCompactSupport (hfc i)))
    rw [← hG] at hle
    have hle' : (hermNegIndex (zeroGram Z f) : ℕ∞) ≤
        (hermNegIndex (zeroGram Z fun i => evenProj (f i)) : ℕ∞) +
          (hermNegIndex (zeroGram Z fun i => oddProj (f i)) : ℕ∞) := by
      exact_mod_cast hle
    refine hle'.trans (add_le_add ?_ ?_)
    · exact le_iSup_of_le n (le_iSup_of_le ⟨fun i => evenProj (f i),
        fun i => evenProj_contDiff (hf i), fun i => evenProj_hasCompactSupport (hfc i),
        fun i => testNeg_evenProj (f i), fun i => evenProj_support (hsupp i)⟩ le_rfl)
    · exact le_iSup_of_le n (le_iSup_of_le ⟨fun i => oddProj (f i),
        fun i => oddProj_contDiff (hf i), fun i => oddProj_hasCompactSupport (hfc i),
        fun i => testNeg_oddProj (f i), fun i => oddProj_support (hsupp i)⟩ le_rfl)
  · -- Reverse inequality: concatenate any even family and any odd family supported in `[-a, a]`
    have hpair : ∀ (n₁ : ℕ) (f₁ : {f : Fin n₁ → ℝ → ℂ // (∀ i, ContDiff ℝ 2 (f i)) ∧
        (∀ i, HasCompactSupport (f i)) ∧ (∀ i, testNeg (f i) = (1 : ℂ) • f i) ∧
        ∀ i u, a < |u| → f i u = 0})
      (n₂ : ℕ) (f₂ : {f : Fin n₂ → ℝ → ℂ // (∀ i, ContDiff ℝ 2 (f i)) ∧
        (∀ i, HasCompactSupport (f i)) ∧ (∀ i, testNeg (f i) = (-1 : ℂ) • f i) ∧
        ∀ i u, a < |u| → f i u = 0}),
      (hermNegIndex (zeroGram Z f₁.1) : ℕ∞) + (hermNegIndex (zeroGram Z f₂.1) : ℕ∞) ≤
        hodgeDefectAt Z a := by
      rintro n₁ ⟨g, hg, hgc, hgs, hgsupp⟩ n₂ ⟨h, hh, hhc, hhs, hhsupp⟩
      set e := finSumFinEquiv (m := n₁) (n := n₂)
      set gh : Fin (n₁ + n₂) → ℝ → ℂ := fun k => Sum.elim g h (e.symm k)
      have hgh_cd : ∀ k, ContDiff ℝ 2 (gh k) := fun k => by
        rcases h : e.symm k with i | j <;> simp [gh, h, hg, hh]
      have hgh_cs : ∀ k, HasCompactSupport (gh k) := fun k => by
        rcases h : e.symm k with i | j <;> simp [gh, h, hgc, hhc]
      have hgh_supp : ∀ k u, a < |u| → gh k u = 0 := fun k u hu => by
        rcases h : e.symm k with i | j <;> simp [gh, h, hgsupp _ u hu, hhsupp _ u hu]
      -- Equivalence between `Fin n₁ ⊕ Fin n₂` and `Fin (n₁ + n₂)` via permutation matrix
      set P : Matrix (Fin n₁ ⊕ Fin n₂) (Fin (n₁ + n₂)) ℂ :=
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e 1
      have hblock : zeroGram Z (Sum.elim g h) =
          fromBlocks (zeroGram Z g) 0 0 (zeroGram Z h) := by
        ext i j
        rcases i with i | i <;> rcases j with j | j
        · rfl
        · simp [zeroGram, W_eq_zero_of_even_odd hFE (hgs i) (hhs j)]
        · simp [zeroGram, W_eq_zero_of_odd_even hFE (hhs i) (hgs j)]
        · rfl
      -- Direct subspace proof on `Fin (n₁ + n₂)` via `e`
      obtain ⟨W₁, hrank₁, hW₁⟩ := exists_isPosDefOn_finrank_eq_posIndex (-(fromBlocks (zeroGram Z g) 0 0 (zeroGram Z h)))
      have hle_block := add_le_negIndex_fromBlocks_zero (zeroGram Z g) (zeroGram Z h)
      set L : (Fin n₁ ⊕ Fin n₂ → ℂ) ≃ₗ[ℂ] (Fin (n₁ + n₂) → ℂ) :=
        LinearEquiv.funCongrLeft ℂ ℂ e.symm
      have hquad_L : ∀ v : Fin n₁ ⊕ Fin n₂ → ℂ,
          hermQuad (-(zeroGram Z gh)) (L v) =
            hermQuad (-(fromBlocks (zeroGram Z g) 0 0 (zeroGram Z h))) v := by
        intro v
        rw [← hblock, hermQuad_neg, hermQuad_neg]
        congr 1
        simp only [hermQuad, dotProduct, Matrix.mulVec]
        rw [← e.sum_comp]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← e.sum_comp]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [L, gh, zeroGram]
      have hpd_L : IsPosDefOn (-(zeroGram Z gh)) (W₁.map L.toLinearMap) := by
        rintro w ⟨v, hv, rfl⟩ hw0
        have hv0 : v ≠ 0 := fun h0 => hw0 (by simp [h0])
        rw [hquad_L]
        exact hW₁ v hv hv0
      have hle_gh : hermNegIndex (fromBlocks (zeroGram Z g) 0 0 (zeroGram Z h)) ≤
          hermNegIndex (zeroGram Z gh) := by
        have hfin := finrank_le_posIndex hpd_L
        rwa [Submodule.finrank_map_subtype_eq L, hrank₁] at hfin
      have htot : (hermNegIndex (zeroGram Z g) : ℕ∞) + (hermNegIndex (zeroGram Z h) : ℕ∞) ≤
          (hermNegIndex (zeroGram Z gh) : ℕ∞) := by
        exact_mod_cast hle_block.trans hle_gh
      exact htot.trans (le_iSup_of_le (n₁ + n₂)
        (le_iSup_of_le ⟨gh, hgh_cd, hgh_cs, hgh_supp⟩ le_rfl))
    rcases eq_top_or_lt_top (hodgeDefectAt Z a) with htop | hlt
    · rw [htop]; exact le_top
    · obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hlt.ne
      rw [← hc]
      have h1 : ∀ n₂ f₂, sectorHodgeDefectAt Z 1 a +
          (hermNegIndex (zeroGram Z f₂.1) : ℕ∞) ≤ (c : ℕ∞) := by
        intro n₂ f₂
        have hb : (hermNegIndex (zeroGram Z f₂.1) : ℕ∞) ≤ (c : ℕ∞) := by
          have := hpair 0 ⟨![] , by simp, by simp, by simp, by simp⟩ n₂ f₂
          simpa [ hc.symm] using this
        have hb' : hermNegIndex (zeroGram Z f₂.1) ≤ c := ENat.coe_le_coe.mp hb
        have hsub : sectorHodgeDefectAt Z 1 a ≤ ((c - hermNegIndex (zeroGram Z f₂.1) : ℕ) : ℕ∞) := by
          refine iSup_le fun n₁ => iSup_le fun f₁ => ?_
          have hp := hpair n₁ f₁ n₂ f₂
          rw [← hc, ← Nat.cast_add, ENat.coe_le_coe] at hp
          exact ENat.coe_le_coe.mpr (Nat.le_sub_of_add_le hp)
        calc sectorHodgeDefectAt Z 1 a + (hermNegIndex (zeroGram Z f₂.1) : ℕ∞)
            ≤ ((c - hermNegIndex (zeroGram Z f₂.1) : ℕ) : ℕ∞) +
                (hermNegIndex (zeroGram Z f₂.1) : ℕ∞) := add_le_add_right hsub _
          _ = (c : ℕ∞) := by
              rw [← Nat.cast_add, Nat.sub_add_cancel hb']
      rcases eq_top_or_lt_top (sectorHodgeDefectAt Z 1 a) with htop1 | hlt1
      · exfalso
        have := h1 0 ⟨![], by simp, by simp, by simp, by simp⟩
        rw [htop1, top_add] at this
        exact not_top_le_coe c this
      · obtain ⟨c₁, hc₁⟩ := ENat.ne_top_iff_exists.mp hlt1.ne
        rw [← hc₁]
        have hc₁_le : c₁ ≤ c := by
          have := h1 0 ⟨![], by simp, by simp, by simp, by simp⟩
          rw [← hc₁] at this
          simpa using this
        have hsub2 : sectorHodgeDefectAt Z (-1) a ≤ ((c - c₁ : ℕ) : ℕ∞) := by
          refine iSup_le fun n₂ => iSup_le fun f₂ => ?_
          have hp := h1 n₂ f₂
          rw [← hc₁, ← Nat.cast_add, ENat.coe_le_coe] at hp
          exact ENat.coe_le_coe.mpr (Nat.le_sub_of_add_le' hp)
        calc (c₁ : ℕ∞) + sectorHodgeDefectAt Z (-1) a
            ≤ (c₁ : ℕ∞) + ((c - c₁ : ℕ) : ℕ∞) := add_le_add_left hsub2 _
          _ = (c : ℕ∞) := by
              rw [← Nat.cast_add, Nat.add_sub_of_le hc₁_le]

/-- **Past the first prime, any Hodge defect of `ζ` is purely even.** For `a ≤ 181/500`, the odd
sector Hodge defect of `ζ` vanishes (`zeta_odd_sectorHodgeDefectAt_eq_zero`), so the full Hodge
defect at degree `a` equals the even-sector Hodge defect at degree `a`. -/
theorem zeta_hodgeDefectAt_eq_even_sectorHodgeDefectAt_of_le {a : ℝ} (ha : a ≤ 181 / 500) :
    hodgeDefectAt zetaZeroConfig a = sectorHodgeDefectAt zetaZeroConfig 1 a := by
  rw [hodgeDefectAt_eq_sectorHodgeDefectAt_add zetaZeroConfig zetaZeroConfig_tempered
    zetaZeroConfig_feSymmetric a, zeta_odd_sectorHodgeDefectAt_eq_zero ha, add_zero]

/-! ### 3. Symmetrized Hecke translates and the cyclic sector Pontryagin law -/

/-- The `s`-sector symmetrized Hecke translate `(1/2)(T_d g + s · testNeg (T_d g))`. -/
def symmTranslate (s : ℂ) (d : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  (2 : ℂ)⁻¹ • (translate d g + s • testNeg (translate d g))

theorem symmTranslate_contDiff {s : ℂ} {d : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (symmTranslate s d g) :=
  ((translate_contDiff d hg).add ((testNeg_contDiff (translate_contDiff d hg)).const_smul s)).const_smul
    (2 : ℂ)⁻¹

theorem symmTranslate_hasCompactSupport {s : ℂ} {d : ℝ} {g : ℝ → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (symmTranslate s d g) :=
  ((translate_hasCompactSupport d hgc).add
    ((testNeg_hasCompactSupport (translate_hasCompactSupport d hgc)).smul_left)).smul_left

theorem testNeg_symmTranslate {s : ℂ} (hs : s = 1 ∨ s = -1) (d : ℝ) (g : ℝ → ℂ) :
    testNeg (symmTranslate s d g) = s • symmTranslate s d g := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> ring
  funext u
  simp only [symmTranslate, testNeg, Pi.smul_apply, Pi.add_apply, smul_eq_mul, neg_neg]
  linear_combination (2 : ℂ)⁻¹ * translate d g u * hs2.symm

/-- Reindexing along `conjCarrier` is an isometry of `ℓ²(Z.carrier, ℂ)`. -/
theorem norm_negVec {Z : ZeroConfig} (hFE : FESymmetric Z) (u : ℓ²(Z.carrier, ℂ)) :
    ‖negVec hFE u‖ = ‖u‖ := by
  have hsq : ‖negVec hFE u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq_to_K ℂ _ _ _ _ (negVec hFE u),
      ← @inner_self_eq_norm_sq_to_K ℂ _ _ _ _ u]
    congr 1
    simp only [lp.inner_apply, negVec_apply]
    exact (conjCarrier hFE).tsum_eq fun ρ => inner ℂ (u ρ) (u ρ)
  exact sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp hsq

/-- The evaluation vector of `symmTranslate s d g` in `ℓ²(Z.carrier, ℂ)`. -/
theorem fesVec_symmTranslate (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    {s : ℂ} {d : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    fesVec Z hZ (symmTranslate s d g) =
      (2 : ℂ)⁻¹ • (fesVec Z hZ (translate d g) + s • negVec hFE (fesVec Z hZ (translate d g))) := by
  refine lp.ext (funext fun ρ => ?_)
  simp only [symmTranslate, fesVec_apply, lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, ← fesVec_negVec Z hZ hFE (translate_contDiff d hg)
      (translate_hasCompactSupport d hgc)]
  have h1 := translate_contDiff d hg
  have h2 := translate_hasCompactSupport d hgc
  rw [paperFT_smul, paperFT_add h1.continuous h2
    ((testNeg_contDiff h1).const_smul s).continuous ((testNeg_hasCompactSupport h2).smul_left),
    paperFT_smul]
  ring

/-- **Sector approximation by symmetrized Hecke translates.** For a spectrally generic test `g` and
a dense shift set `D`, every `s`-sector test `f` (`testNeg f = s • f`, `s = ±1`) is approximated in
`ℓ²(Z.carrier, ℂ)` by finite linear combinations of `symmTranslate s d g` with `d ∈ D`. -/
theorem exists_finset_symmTranslate_approx (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgen : SpectrallyGeneric Z g) {D : Set ℝ} (hD : DenseShifts D)
    {s : ℂ} (hs : s = 1 ∨ s = -1) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hfs : testNeg f = s • f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (d : Fin m → ℝ), (∀ j, d j ∈ D) ∧
      ‖fesVec Z hZ f - fesVec Z hZ (∑ j, c j • symmTranslate s (d j) g)‖ < ε := by
  obtain ⟨m, c, d, hdD, happrox⟩ :=
    exists_finset_translate_approx Z hZ hg hgc hgen hD hf hfc hε
  refine ⟨m, c, d, hdD, ?_⟩
  set F : ℝ → ℂ := ∑ j, c j • translate (d j) g
  have hFd : ContDiff ℝ 2 F := contDiff_sum_smul _ (fun j => translate_contDiff (d j) hg) c
  have hFc : HasCompactSupport F :=
    hasCompactSupport_sum_smul _ (fun j => translate_hasCompactSupport (d j) hgc) c
  set v : ℓ²(Z.carrier, ℂ) := fesVec Z hZ f - fesVec Z hZ F
  have hfv : negVec hFE (fesVec Z hZ f) = s • fesVec Z hZ f := by
    rw [← fesVec_negVec Z hZ hFE hf hfc, hfs]
    refine lp.ext (funext fun ρ => ?_)
    simp [fesVec_apply, paperFT_smul]
  have hsum : fesVec Z hZ (∑ j, c j • symmTranslate s (d j) g) =
      (2 : ℂ)⁻¹ • (fesVec Z hZ F + s • negVec hFE (fesVec Z hZ F)) := by
    refine lp.ext (funext fun ρ => ?_)
    simp only [fesVec_apply, lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, ← fesVec_negVec Z hZ hFE hFd hFc]
    rw [paperFT_sum_smul _ (fun j => (symmTranslate_contDiff hg).continuous)
      (fun j => symmTranslate_hasCompactSupport hgc)]
    have hF_ft : paperFT F (gammaOf ρ) * √(Z.mult ρ : ℝ) =
        ∑ j, c j * (fesVec Z hZ (translate (d j) g) : Z.carrier → ℂ) ρ := by
      simp only [F, paperFT_sum_smul _ (fun j => (translate_contDiff (d j) hg).continuous)
        (fun j => translate_hasCompactSupport (d j) hgc), fesVec_apply, Finset.sum_mul, mul_assoc]
    have hFt_ft : (fesVec Z hZ (testNeg F) : Z.carrier → ℂ) ρ =
        ∑ j, c j * (negVec hFE (fesVec Z hZ (translate (d j) g)) : Z.carrier → ℂ) ρ := by
      rw [fesVec_negVec Z hZ hFE hFd hFc]
      simp only [negVec_apply, fesVec_apply, F,
        paperFT_sum_smul _ (fun j => (translate_contDiff (d j) hg).continuous)
          (fun j => translate_hasCompactSupport (d j) hgc), Finset.sum_mul, mul_assoc]
    have hterm : ∀ j, c j * paperFT (symmTranslate s (d j) g) (gammaOf ρ) * √(Z.mult ρ : ℝ) =
        c j * (fesVec Z hZ (symmTranslate s (d j) g) : Z.carrier → ℂ) ρ := fun j => by
      simp [fesVec_apply, mul_assoc]
    rw [Finset.sum_mul]
    simp only [mul_assoc] at hterm ⊢
    rw [Finset.sum_congr rfl fun j _ => by
      rw [← mul_assoc, hterm j, fesVec_symmTranslate Z hZ hFE hg hgc]]
    simp only [lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [hF_ft, hFt_ft, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hdiff : fesVec Z hZ f - fesVec Z hZ (∑ j, c j • symmTranslate s (d j) g) =
      (2 : ℂ)⁻¹ • (v + s • negVec hFE v) := by
    rw [hsum]
    have hf_id : fesVec Z hZ f = (2 : ℂ)⁻¹ • (fesVec Z hZ f + s • negVec hFE (fesVec Z hZ f)) := by
      have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> ring
      rw [hfv, smul_smul, hs2, one_smul]
      ext ρ
      simp only [lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    have hneg_sub : negVec hFE v = negVec hFE (fesVec Z hZ f) - negVec hFE (fesVec Z hZ F) := by
      ext ρ; simp [v, negVec_apply]
    conv_lhs => rw [hf_id]
    rw [← smul_sub, hneg_sub, smul_sub]
    ext ρ
    simp only [v, lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply,
      Pi.sub_apply, smul_eq_mul]
    ring
  have hs_norm : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
  rw [hdiff, norm_smul, norm_inv, Complex.norm_ofNat]
  calc (2 : ℝ)⁻¹ * ‖v + s • negVec hFE v‖
      ≤ (2 : ℝ)⁻¹ * (‖v‖ + ‖s • negVec hFE v‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = ‖v‖ := by
        rw [norm_smul, hs_norm, one_mul, norm_negVec hFE v]
        ring
    _ < ε := happrox

/-- **Attainment of the sector Hodge defect on the symmetrized Hecke orbit.** -/
theorem exists_finset_symmTranslate_negIndex_ge (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgen : SpectrallyGeneric Z g) {D : Set ℝ} (hD : DenseShifts D)
    {s : ℂ} (hs : s = 1 ∨ s = -1) (n : ℕ) (hn : (n : ℕ∞) ≤ (sectorZeros Z s).encard) :
    ∃ S : Finset ℝ, (S : Set ℝ) ⊆ D ∧
      n ≤ hermNegIndex (zeroGram Z fun d : S => symmTranslate s d g) := by
  classical
  obtain ⟨f, hf, hfc, hfs, hneg⟩ := exists_sector_zeroGram_negIndex_ge Z hZ hFE hs n hn
  obtain ⟨δ, hδ, hcont⟩ :=
    continuity_of_negIndex Z (fun i => fesVec Z hZ (f i))
  have hex : ∀ i : Fin n, ∃ (m : ℕ) (c : Fin m → ℂ) (d : Fin m → ℝ), (∀ j, d j ∈ D) ∧
      ‖fesVec Z hZ (f i) - fesVec Z hZ (∑ j, c j • symmTranslate s (d j) g)‖ < δ :=
    fun i => exists_finset_symmTranslate_approx Z hZ hFE hg hgc hgen hD hs
      (hf i) (hfc i) (hfs i) hδ
  choose m c d hdD happrox using hex
  set S : Finset ℝ := Finset.univ.biUnion fun i => Finset.univ.image (d i)
  have hSD : (S : Set ℝ) ⊆ D := by
    intro x hx
    simp only [S, Finset.coe_biUnion, Finset.coe_univ, Set.biUnion_univ, Set.mem_iUnion,
      Finset.coe_image, Set.mem_image, Set.mem_univ, true_and] at hx
    obtain ⟨i, j, rfl⟩ := hx
    exact hdD i j
  set a : Fin n → S → ℂ := fun i t =>
    ∑ j ∈ Finset.univ.filter (fun j => d i j = (t : ℝ)), c i j
  have hsum_eq : ∀ i, (∑ j, c i j • symmTranslate s (d i j) g) =
      ∑ t : S, a i t • symmTranslate s (t : ℝ) g := by
    intro i
    have hmem : ∀ j, d i j ∈ S := fun j =>
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
    let d' : Fin (m i) → S := fun j => ⟨d i j, hmem j⟩
    change (∑ j, c i j • symmTranslate s (d' j : ℝ) g) =
      ∑ t : S, (∑ j ∈ Finset.univ.filter (fun j => d' j = t), c i j) • symmTranslate s (t : ℝ) g
    rw [← Finset.sum_fiberwise _ d']
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]
  set F : Fin n → ℝ → ℂ := fun i => ∑ t : S, a i t • symmTranslate s (t : ℝ) g
  have hFd : ∀ i, ContDiff ℝ 2 (F i) := fun i =>
    contDiff_sum_smul _ (fun _ => symmTranslate_contDiff hg) (a i)
  have hFc : ∀ i, HasCompactSupport (F i) := fun i =>
    hasCompactSupport_sum_smul _ (fun _ => symmTranslate_hasCompactSupport hgc) (a i)
  have hgram_f : gramReflect Z (fun i => fesVec Z hZ (f i)) = zeroGram Z f := by
    ext i j; exact inner_reflectVec_fesVec Z hZ (hf i) (hfc i) (hf j) (hfc j)
  have hgram_F : gramReflect Z (fun i => fesVec Z hZ (F i)) = zeroGram Z F := by
    ext i j; exact inner_reflectVec_fesVec Z hZ (hFd i) (hFc i) (hFd j) (hFc j)
  have hle_F : hermNegIndex (zeroGram Z f) ≤ hermNegIndex (zeroGram Z F) := by
    rw [← hgram_f, ← hgram_F]
    refine hcont (fun i => fesVec Z hZ (F i)) fun i => ?_
    rw [norm_sub_rev]
    simpa [F, hsum_eq i] using happrox i
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-(zeroGram Z F))
  set L : (Fin n → ℂ) →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun x t => ∑ i, conj (a i t) * x i
      map_add' := fun x y => by ext t; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by ext t; simp [Finset.mul_sum, mul_left_comm] }
  have hcombo : ∀ x : Fin n → ℂ,
      (∑ i, conj (x i) • F i) = ∑ t : S, conj (L x t) • symmTranslate s (t : ℝ) g := by
    intro x
    simp only [F, L, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, conj_conj,
      Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have hquad : ∀ x : Fin n → ℂ,
      hermQuad (-(zeroGram Z F)) x =
        hermQuad (-(zeroGram Z fun t : S => symmTranslate s (t : ℝ) g)) (L x) := by
    intro x
    rw [hermQuad_neg, hermQuad_neg, hermQuad_zeroGram_of_tempered Z hZ F hFd hFc,
      hermQuad_zeroGram_of_tempered Z hZ _ (fun _ => symmTranslate_contDiff hg)
        (fun _ => symmTranslate_hasCompactSupport hgc), hcombo]
  have hker : ∀ y ∈ W, L y = 0 → y = 0 := by
    intro y hy hLy
    by_contra hy0
    have hpos := hW y hy hy0
    rw [hquad, hLy] at hpos
    simp [hermQuad] at hpos
  have hinj : Function.Injective (L.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    exact Subtype.ext (hker y.1 y.2 (LinearMap.mem_ker.mp hy))
  have hW' : IsPosDefOn (-(zeroGram Z fun t : S => symmTranslate s (t : ℝ) g)) (W.map L) := by
    rintro z ⟨x, hx, rfl⟩ hz0
    have hx0 : x ≠ 0 := fun h0 => hz0 (by simp [h0])
    rw [← hquad]
    exact hW x hx hx0
  have hle_S : hermNegIndex (zeroGram Z F) ≤
      hermNegIndex (zeroGram Z fun t : S => symmTranslate s (t : ℝ) g) := by
    rw [hermNegIndex, ← hrank,
      ← ((Submodule.equivMapOfInjective L hinj W).symm).finrank_eq]
    exact finrank_le_posIndex hW'
  exact ⟨S, hSD, hneg.trans (hle_F.trans hle_S)⟩

/-- **The cyclic sector Pontryagin law.** For any functional-equation-symmetric tempered
configuration `Z`, any spectrally generic test `g`, any dense shift set `D`, and either reflection
sector `s = ±1`, finite subfamilies of `{symmTranslate s d g | d ∈ D}` achieve `n` negative squares
of `W_Z` iff `(n : ℕ∞) ≤ (sectorZeros Z s).encard`. -/
theorem cyclic_sector_pontryagin_law (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgen : SpectrallyGeneric Z g) {D : Set ℝ} (hD : DenseShifts D)
    {s : ℂ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    (∃ S : Finset ℝ, (S : Set ℝ) ⊆ D ∧
      n ≤ hermNegIndex (zeroGram Z fun d : S => symmTranslate s d g)) ↔
        (n : ℕ∞) ≤ (sectorZeros Z s).encard := by
  constructor
  · rintro ⟨S, _, hle⟩
    exact (ENat.coe_le_coe.mpr hle).trans (negIndex_sector_zeroGram_le Z hZ hFE hs
      (fun d : S => symmTranslate s d g) (fun _ => symmTranslate_contDiff hg)
      (fun _ => symmTranslate_hasCompactSupport hgc) (fun _ => testNeg_symmTranslate hs _ g))
  · exact exists_finset_symmTranslate_negIndex_ge Z hZ hFE hg hgc hgen hD hs n

/-- **For `ζ`, the symmetrized rational Hecke orbit of a single generic test carries each
reflection sector.** -/
theorem zeta_cyclic_sector_hodgeDefect_ratHecke {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgen : SpectrallyGeneric zetaZeroConfig g)
    {s : ℂ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    (∃ S : Finset ℝ, (S : Set ℝ) ⊆ ratHeckeShifts ∧
      1 + n ≤ hermPosIndex (intersectionGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        (fun d : S => symmTranslate s d g))) ↔
        (n : ℕ∞) ≤ {ρ ∈ rightZeros zetaZeroConfig | 0 < ρ.im}.encard := by
  rw [← zeta_sectorZeros_eq hs,
    ← cyclic_sector_pontryagin_law zetaZeroConfig zetaZeroConfig_tempered
      zetaZeroConfig_feSymmetric hg hgc hgen denseShifts_ratHeckeShifts hs n]
  refine exists_congr fun S => and_congr_right fun _ => ?_
  rw [posIndex_intersectionGram,
    ← zeta_zeroGram_eq_weilGram _ (fun _ => symmTranslate_contDiff hg)
      (fun _ => symmTranslate_hasCompactSupport hgc)]
  omega

/-- **For `ζ`, the symmetrized Hecke orbit of any two distinct primes carries each reflection
sector.** -/
theorem zeta_cyclic_sector_hodgeDefect_twoPrimes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgen : SpectrallyGeneric zetaZeroConfig g) {s : ℂ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    (∃ S : Finset ℝ, (S : Set ℝ) ⊆ twoPrimeShifts p q ∧
      1 + n ≤ hermPosIndex (intersectionGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        (fun d : S => symmTranslate s d g))) ↔
        (n : ℕ∞) ≤ {ρ ∈ rightZeros zetaZeroConfig | 0 < ρ.im}.encard := by
  rw [← zeta_sectorZeros_eq hs,
    ← cyclic_sector_pontryagin_law zetaZeroConfig zetaZeroConfig_tempered
      zetaZeroConfig_feSymmetric hg hgc hgen (denseShifts_twoPrimeShifts hp hq hpq) hs n]
  refine exists_congr fun S => and_congr_right fun _ => ?_
  rw [posIndex_intersectionGram,
    ← zeta_zeroGram_eq_weilGram _ (fun _ => symmTranslate_contDiff hg)
      (fun _ => symmTranslate_hasCompactSupport hgc)]
  omega

/-- The degree-filtered cyclic Hodge defect on a shift set `D` at shift radius `R`. -/
def cyclicHodgeDefectAt (Z : ZeroConfig) (g : ℝ → ℂ) (D : Set ℝ) (R : ℝ) : ℕ∞ :=
  ⨆ (S : {S : Finset ℝ // (S : Set ℝ) ⊆ D ∧ ∀ d ∈ S, |d| ≤ R}),
    (hermNegIndex (zeroGram Z fun d : S.1 => translate d g) : ℕ∞)

theorem cyclicHodgeDefectAt_mono (Z : ZeroConfig) (g : ℝ → ℂ) (D : Set ℝ) {R₁ R₂ : ℝ}
    (hR : R₁ ≤ R₂) :
    cyclicHodgeDefectAt Z g D R₁ ≤ cyclicHodgeDefectAt Z g D R₂ :=
  iSup_le fun ⟨S, hSD, hSR⟩ =>
    le_iSup_of_le ⟨S, hSD, fun d hd => (hSR d hd).trans hR⟩ le_rfl

/-- **Exhaustion of the Hodge defect by the degree-filtered cyclic Hecke orbit.** -/
theorem iSup_cyclicHodgeDefectAt (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (hgen : SpectrallyGeneric Z g)
    {D : Set ℝ} (hD : DenseShifts D) :
    (⨆ R : ℝ, cyclicHodgeDefectAt Z g D R) = (rightZeros Z).encard := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun R => iSup_le fun ⟨S, _⟩ => ?_
    exact negIndex_zeroGram_le_of_tempered Z hZ _
      (fun _ => translate_contDiff _ hg) (fun _ => translate_hasCompactSupport _ hgc)
  · refine ENat.le_of_forall_nat_le fun n hn => ?_
    obtain ⟨S, hSD, hle⟩ :=
      (cyclic_pontryagin_law Z hZ hg hgc hgen hD n).mpr hn
    set R : ℝ := S.sup' ⟨0, Finset.mem_insert_self 0 S⟩ (fun d => |d|)
    have hSR : ∀ d ∈ S, |d| ≤ R := fun d hd =>
      Finset.le_sup' (fun x => |x|) (Finset.mem_insert_of_mem hd)
    exact (ENat.coe_le_coe.mpr hle).trans
      (le_iSup_of_le R (le_iSup_of_le ⟨S, hSD, hSR⟩ le_rfl))

/-! ### 4. Depth and multiplicity invariance of the Hodge defect vs. multiplicity sensitivity -/

/-- **Multiplicity and depth-deformation invariance of the global Hodge defect.** Any two tempered
configurations whose right-zero sets have the same cardinal (in particular, configurations with the
same carrier and arbitrary positive multiplicities, or related by any depth-preserving-sign
bijection on off-line zeros) have identical global Hodge defect. -/
theorem iSup_hodgeDefectAt_eq_of_rightZeros_encard_eq (Z₁ Z₂ : ZeroConfig)
    (hZ₁ : TemperedConfig Z₁) (hZ₂ : TemperedConfig Z₂)
    (hcard : (rightZeros Z₁).encard = (rightZeros Z₂).encard) :
    (⨆ a : ℝ, hodgeDefectAt Z₁ a) = ⨆ a : ℝ, hodgeDefectAt Z₂ a := by
  rw [iSup_hodgeDefectAt Z₁ hZ₁, iSup_hodgeDefectAt Z₂ hZ₂, hcard]

/-- **Multiplicity and depth-deformation invariance of the sector Hodge defect.** -/
theorem iSup_sectorHodgeDefectAt_eq_of_sectorZeros_encard_eq (Z₁ Z₂ : ZeroConfig)
    (hZ₁ : TemperedConfig Z₁) (hFE₁ : FESymmetric Z₁)
    (hZ₂ : TemperedConfig Z₂) (hFE₂ : FESymmetric Z₂)
    {s : ℂ} (hs : s = 1 ∨ s = -1)
    (hcard : (sectorZeros Z₁ s).encard = (sectorZeros Z₂ s).encard) :
    (⨆ a : ℝ, sectorHodgeDefectAt Z₁ s a) = ⨆ a : ℝ, sectorHodgeDefectAt Z₂ s a := by
  rw [iSup_sectorHodgeDefectAt Z₁ hZ₁ hFE₁ hs, iSup_sectorHodgeDefectAt Z₂ hZ₂ hFE₂ hs, hcard]

/-- **Depth blindness on `multiPairConfig`.** For any `m` distinct positive ordinates `γ` and any
two depth profiles `δ₁, δ₂ : Fin m → ℝ` in `(0, 1/2)`, `multiPairConfig γ δ₁` and
`multiPairConfig γ δ₂` have the exact same global Hodge defect `2m`, the exact same visibility
threshold `mπ / (2 Σ γ_k)`, and the exact same saturation threshold `mπ / min γ_k`. -/
theorem multiPairConfig_depth_invariance {m : ℕ} (γ δ₁ δ₂ : Fin m → ℝ)
    (hγ : ∀ k, 0 < γ k) (hinj : Function.Injective γ)
    (hδ₁ : ∀ k, 0 < δ₁ k ∧ δ₁ k < 1 / 2) (hδ₂ : ∀ k, 0 < δ₂ k ∧ δ₂ k < 1 / 2) :
    ((⨆ a : ℝ, hodgeDefectAt (multiPairConfig γ δ₁ hγ hδ₁) a) = 2 * (m : ℕ∞) ∧
      (⨆ a : ℝ, hodgeDefectAt (multiPairConfig γ δ₂ hγ hδ₂) a) = 2 * (m : ℕ∞)) ∧
    (∀ a : ℝ, 0 ≤ a → a * (∑ k, γ k) < (m : ℝ) * Real.pi / 2 →
      hodgeDefectAt (multiPairConfig γ δ₁ hγ hδ₁) a = 0 ∧
        hodgeDefectAt (multiPairConfig γ δ₂ hγ hδ₂) a = 0) ∧
    (∀ {mγ : ℝ}, 0 < m → 0 < mγ → (∀ k, mγ ≤ γ k) →
      ∀ a : ℝ, (m : ℝ) * Real.pi / mγ < a →
        hodgeDefectAt (multiPairConfig γ δ₁ hγ hδ₁) a = 2 * (m : ℕ∞) ∧
          hodgeDefectAt (multiPairConfig γ δ₂ hγ hδ₂) a = 2 * (m : ℕ∞)) := by
  refine ⟨⟨?_, ?_⟩, fun a ha hlt => ⟨?_, ?_⟩, fun hm hmγ hle a ha => ⟨?_, ?_⟩⟩
  · rw [iSup_hodgeDefectAt _ (multiPairConfig_tempered γ δ₁ hγ hδ₁),
      encard_rightZeros_multiPairConfig γ δ₁ hγ hinj hδ₁]
  · rw [iSup_hodgeDefectAt _ (multiPairConfig_tempered γ δ₂ hγ hδ₂),
      encard_rightZeros_multiPairConfig γ δ₂ hγ hinj hδ₂]
  · exact hodgeDefectAt_multiPairConfig_eq_zero γ δ₁ hγ hδ₁ ha hlt
  · exact hodgeDefectAt_multiPairConfig_eq_zero γ δ₂ hγ hδ₂ ha hlt
  · exact hodgeDefectAt_multiPairConfig_eq γ δ₁ hγ hinj hδ₁ hm hmγ hle ha
  · exact hodgeDefectAt_multiPairConfig_eq γ δ₂ hγ hinj hδ₂ hm hmγ hle ha

/-- **Multiplicity separation on `offLineClusterConfig`.** Every zero of `offLineClusterConfig` has
fixed depth `1/4` and every `n`-test Gram matrix has `hermNegIndex ≤ n`, yet the unbounded off-line
multiplicities drive the `L²`-normalised Weil form to `-∞` at every fixed support degree `A > 0`. -/
theorem offLineClusterConfig_hodgeDefect_vs_l2_floor :
    (∀ ρ ∈ RHTower.offLineClusterConfig.carrier, |ρ.re - 1 / 2| = 1 / 4) ∧
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ),
      hermNegIndex (zeroGram RHTower.offLineClusterConfig f) ≤ n) ∧
    (∀ A > 0, ∀ M > 0, ∃ f : ℝ → ℂ, ContDiff ℝ ⊤ f ∧ HasCompactSupport f ∧
      (∀ t, A < |t| → f t = 0) ∧ (∫ t, ‖f t‖ ^ 2) > 0 ∧
      (RHTower.offLineClusterConfig.W f f).re ≤ -M * ∫ t, ‖f t‖ ^ 2) := by
  refine ⟨RHTower.offLineClusterConfig_depth, fun n f => ?_,
    RHTower.offLineClusterConfig_weil_unbounded_below⟩
  obtain ⟨W, hrank, _⟩ :=
    exists_isPosDefOn_finrank_eq_posIndex (-(zeroGram RHTower.offLineClusterConfig f))
  rw [hermNegIndex, ← hrank]
  have h := Submodule.finrank_le W
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
