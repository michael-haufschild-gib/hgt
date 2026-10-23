import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.RiemannRochForZAndTheReflectedPrimePolarLedger
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SchurLendingOddHodgeIndexPastFirstPrime
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfRightZeros
import GaloisForLFunctions.SquareRootThreshold.TheIncidenceLedgerGradedByTheZeroWidth
import GaloisForLFunctions.SquareRootThreshold.TheWidthBoundsTheEnergyNormalisedWeilFloor
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
  never on their multiplicities `Z.mult` or their depths `Re ρ - 1/2 > 0`. On `multiPairConfig`,
  changing the depth profile `δ : Fin n → (0, 1/2]` at fixed ordinates `γ` leaves the global
  Hodge defect `n` completely unchanged. On `RHTower.offLineClusterConfig`, every zero has fixed
  depth `1/4` and every `n`-test family has `hermNegIndex ≤ n`, whereas the unbounded off-line
  multiplicities `k + 1` drive the raw `L²`-normalised Weil floor at fixed degree to `-∞`.

* **Unconditional growth rate of the defect floor equals the zero width
  (`zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor`,
  `oddDefectFloorRate_eq_zetaZeroWidth`, `fullDefectFloorRate_eq_zetaZeroWidth`):**
  For every `C²_c` test `F`, the Chebyshev-gauge derivative of its autocorrelation is bounded
  uniformly by the `H¹` Sobolev energy `∫ F² + ∫ (F')²` (`abs_gaugeDerivative_autocorr_le_sobolev`),
  and the two-bump difference lag family has `H¹` energy bounded uniformly in the lag. Hence,
  **unconditionally** (with no `OffLineCopiesLocallyBounded` or non-clustering hypothesis),
  `zetaZeroWidth ≤ σ` iff at every rate `β > σ` the `H¹`-normalised Castelnuovo–Severi defect on
  `scalingSubsurface (oddRealTestsAt r)` (or `scalingSubsurface (realTestsAt r)`) is bounded below
  by `-C e^{2β r} (∫ f² + ∫ (f')²)`. Consequently, the infimum of admissible defect-floor growth
  exponents on the scaling surface equals `zetaZeroWidth` unconditionally.
-/

open Complex Matrix Filter Topology MeasureTheory Set Finset
open scoped ComplexConjugate lp Real
open _root_.Zeta23 _root_.RHTower GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

set_option autoImplicit false

/-! ### 1. Hermitian inertia subadditivity and block-diagonal additivity -/

/-- Weil's sesquilinear form on any zero configuration is Hermitian-symmetric. -/
theorem W_conj_symm (Z : ZeroConfig) (f g : ℝ → ℂ) :
    conj (Z.W g f) = Z.W f g := by
  rw [ZeroConfig.W, ZeroConfig.W, Complex.conj_tsum, ← (reflectEquiv Z).tsum_eq]
  refine tsum_congr fun τ => ?_
  have hm : Z.mult (reflect (τ : ℂ)) = Z.mult τ := Z.mult_reflect _ τ.2
  simp only [ZeroConfig.Wsummand, reflectEquiv_apply, reflectCarrier, hm, gammaOf_reflect,
    map_mul, Complex.conj_natCast, conj_conj]
  ring

/-- The zero-side Gram matrix of any family of tests is Hermitian. -/
theorem zeroGram_isHermitian (Z : ZeroConfig) {ι : Type*} (f : ι → ℝ → ℂ) :
    (zeroGram Z f).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_def, zeroGram]
  exact W_conj_symm Z (f i) (f j)

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
  set U : Matrix ι ι ℂ := hH.eigenvectorUnitary.1
  set y : ι → ℂ := Uᴴ *ᵥ x
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hUy : U *ᵥ y = x := by
    change U *ᵥ (Uᴴ *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hUU, Matrix.one_mulVec]
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
  simp only [hermQuad, fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.star_apply, Complex.add_re]

/-- **Superadditivity of the negative index on block-diagonal matrices.** For any matrices `A` and
`B`, `hermNegIndex A + hermNegIndex B ≤ hermNegIndex (fromBlocks A 0 0 B)`. -/
theorem add_le_negIndex_fromBlocks_zero {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    hermNegIndex A + hermNegIndex B ≤ hermNegIndex (fromBlocks A 0 0 B) := by
  obtain ⟨WA, hrankA, hWA⟩ := exists_isPosDefOn_finrank_eq_posIndex (-A)
  obtain ⟨WB, hrankB, hWB⟩ := exists_isPosDefOn_finrank_eq_posIndex (-B)
  let f : (WA × WB) →ₗ[ℂ] (α ⊕ β → ℂ) :=
    { toFun := fun p => Sum.elim p.1.1 p.2.1
      map_add' := fun p q => by ext (i | j) <;> rfl
      map_smul' := fun c p => by ext (i | j) <;> rfl }
  have hfinj : Function.Injective f := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    ext1 <;> apply Subtype.ext <;> funext i
    · exact congrFun h (Sum.inl i)
    · exact congrFun h (Sum.inr i)
  set W : Submodule ℂ (α ⊕ β → ℂ) := LinearMap.range f
  have hpd : IsPosDefOn (-(fromBlocks A 0 0 B)) W := by
    rintro z ⟨⟨x, y⟩, rfl⟩ hz0
    have hxy0 : (x : α → ℂ) ≠ 0 ∨ (y : β → ℂ) ≠ 0 := by
      by_contra h
      push Not at h
      apply hz0
      ext (i | j) <;> simp [f, h.1, h.2]
    have hform : hermQuad (-(fromBlocks A 0 0 B)) (f (x, y)) =
        hermQuad (-A) x.1 + hermQuad (-B) y.1 := by
      rw [hermQuad_neg, hermQuad_neg, hermQuad_neg]
      exact (congrArg Neg.neg (hermQuad_fromBlocks_zero A B x.1 y.1)).trans (neg_add _ _)
    rw [hform]
    have hAx : 0 ≤ hermQuad (-A) x.1 := by
      by_cases hx0 : (x : α → ℂ) = 0
      · simp [hermQuad, hx0]
      · exact (hWA x.1 x.2 hx0).le
    have hBy : 0 ≤ hermQuad (-B) y.1 := by
      by_cases hy0 : (y : β → ℂ) = 0
      · simp [hermQuad, hy0]
      · exact (hWB y.1 y.2 hy0).le
    rcases hxy0 with hx0 | hy0
    · linarith [hWA x.1 x.2 hx0]
    · linarith [hWB y.1 y.2 hy0]
  have hle := finrank_le_posIndex hpd
  have hrankW : Module.finrank ℂ W = hermNegIndex A + hermNegIndex B := by
    rw [LinearMap.finrank_range_of_inj hfinj, Module.finrank_prod, hrankA, hrankB,
      hermNegIndex, hermNegIndex]
  rwa [hrankW] at hle

/-! ### 2. Exact reflection-sector orthogonality, global partition, and degree-by-degree additivity -/

theorem W_smul_left (Z : ZeroConfig) (c : ℂ) (f g : ℝ → ℂ) :
    Z.W (c • f) g = c * Z.W f g := by
  unfold ZeroConfig.W ZeroConfig.Wsummand
  have h : (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * paperFT (c • f) (gammaOf ρ) *
      conj (paperFT g (conj (gammaOf ρ)))) =
      fun ρ : Z.carrier => c * ((Z.mult ρ : ℂ) * paperFT f (gammaOf ρ) *
        conj (paperFT g (conj (gammaOf ρ)))) := by
    funext ρ
    rw [paperFT_smul]
    ring
  rw [h, tsum_mul_left]

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
  rw [← W_conj_symm Z f (g₁ + g₂),
    W_add_left Z hZ hg₁ hg₁c hg₂ hg₂c hf hfc, map_add,
    W_conj_symm Z f g₁, W_conj_symm Z f g₂]

/-- **Reflection invariance of the Weil form.** On any functional-equation-symmetric configuration,
negating the argument of both tests leaves `W_Z` unchanged. -/
theorem W_testNeg {Z : ZeroConfig} (hFE : FESymmetric Z) (f g : ℝ → ℂ) :
    Z.W (testNeg f) (testNeg g) = Z.W f g := by
  rw [ZeroConfig.W, ZeroConfig.W, ← (fesEquiv hFE).tsum_eq]
  refine tsum_congr fun τ => ?_
  have hm := (hFE τ τ.2).2
  have hγ := gammaOf_one_sub_eq (τ : ℂ)
  simp only [ZeroConfig.Wsummand, fesEquiv_apply, fesCarrier, hm, hγ, paperFT_testNeg,
    map_neg, neg_neg]

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

theorem sectorZeros_one (Z : ZeroConfig) :
    sectorZeros Z 1 = {ρ | ρ ∈ rightZeros Z ∧ 0 < ρ.im} := by
  ext ρ
  simp only [sectorZeros, mem_setOf_eq]
  refine and_congr_right fun _ => ⟨?_, Or.inl⟩
  rintro (h | ⟨h1, _⟩)
  · exact h
  · norm_num at h1

theorem sectorZeros_neg_one (Z : ZeroConfig) :
    sectorZeros Z (-1) = {ρ | ρ ∈ rightZeros Z ∧ 0 ≤ ρ.im} := by
  ext ρ
  simp only [sectorZeros, mem_setOf_eq, true_and]
  exact and_congr_right fun _ => ⟨by rintro (h | h); exacts [h.le, h.symm.le],
    fun h => (lt_or_eq_of_le h).imp id Eq.symm⟩

/-- The real zeros of `Z` right of the critical line (`Re ρ > 1/2`, `Im ρ = 0`). -/
def realRightZeros (Z : ZeroConfig) : Set ℂ := {ρ | ρ ∈ rightZeros Z ∧ ρ.im = 0}

/-- **The odd-sector zero set is the disjoint union of the even-sector zero set and the real right
zeros.** -/
theorem sectorZeros_neg_one_encard_eq_add_realRightZeros (Z : ZeroConfig) :
    (sectorZeros Z (-1)).encard = (sectorZeros Z 1).encard + (realRightZeros Z).encard := by
  have hunion : sectorZeros Z (-1) = sectorZeros Z 1 ∪ realRightZeros Z := by
    rw [sectorZeros_neg_one, sectorZeros_one, realRightZeros]
    ext ρ
    simp only [mem_setOf_eq, mem_union]
    exact ⟨fun ⟨hρ, him⟩ => (lt_or_eq_of_le him).imp (fun h => ⟨hρ, h⟩) (fun h => ⟨hρ, h.symm⟩),
      by rintro (⟨hρ, him⟩ | ⟨hρ, him⟩); exacts [⟨hρ, him.le⟩, ⟨hρ, him.symm.le⟩]⟩
  have hdisj : Disjoint (sectorZeros Z 1) (realRightZeros Z) := by
    rw [sectorZeros_one, realRightZeros, Set.disjoint_left]
    rintro ρ ⟨_, him1⟩ ⟨_, him0⟩
    exact him1.ne' him0
  rw [hunion, Set.encard_union_eq hdisj]

/-- **Global cardinal additivity of the reflection sectors.** For any functional-equation-symmetric
zero configuration `Z`, the cardinal of `rightZeros Z` is the sum of the cardinals of the even and
odd sector zero sets:
`(rightZeros Z).encard = (sectorZeros Z 1).encard + (sectorZeros Z (-1)).encard`. -/
theorem rightZeros_encard_eq_sectorZeros_add {Z : ZeroConfig} (hFE : FESymmetric Z) :
    (rightZeros Z).encard = (sectorZeros Z 1).encard + (sectorZeros Z (-1)).encard := by
  set Sneg : Set ℂ := {ρ | ρ ∈ rightZeros Z ∧ ρ.im < 0}
  have hunion : rightZeros Z = Sneg ∪ sectorZeros Z (-1) := by
    rw [sectorZeros_neg_one]
    ext ρ
    simp only [Sneg, mem_setOf_eq, mem_union]
    exact ⟨fun hρ => (lt_or_ge ρ.im 0).imp (fun h => ⟨hρ, h⟩) (fun h => ⟨hρ, h⟩),
      by rintro (⟨hρ, _⟩ | ⟨hρ, _⟩) <;> exact hρ⟩
  have hdisj : Disjoint Sneg (sectorZeros Z (-1)) := by
    rw [sectorZeros_neg_one, Set.disjoint_left]
    rintro ρ ⟨_, hlt⟩ ⟨_, hge⟩
    exact not_lt.mpr hge hlt
  have himg : (starRingEnd ℂ) '' Sneg = sectorZeros Z 1 := by
    rw [sectorZeros_one]
    ext ρ
    simp only [Set.mem_image, Sneg, rightZeros, mem_setOf_eq]
    constructor
    · rintro ⟨τ, ⟨⟨hτC, hτre⟩, hτim⟩, rfl⟩
      refine ⟨⟨hFE.conj_mem hτC, by simpa using hτre⟩, ?_⟩
      simp only [Complex.conj_im, Left.neg_pos_iff]
      exact hτim
    · rintro ⟨⟨hρC, hρre⟩, hρim⟩
      refine ⟨conj ρ, ⟨⟨hFE.conj_mem hρC, by simpa using hρre⟩, ?_⟩, conj_conj ρ⟩
      simp only [Complex.conj_im, Left.neg_neg_iff]
      exact hρim
  rw [hunion, Set.encard_union_eq hdisj, ← himg,
    (RingHom.injective (starRingEnd ℂ)).encard_image]

/-- For `ζ`, the total cardinal of right zeros is twice the cardinal of either reflection sector. -/
theorem zeta_rightZeros_encard_eq_two_mul_sectorZeros (s : ℂ) :
    (rightZeros zetaZeroConfig).encard = 2 * (sectorZeros zetaZeroConfig s).encard := by
  rw [rightZeros_encard_eq_sectorZeros_add fesSymmetric_zetaZeroConfig,
    zeta_sectorZeros_eq 1, zeta_sectorZeros_eq (-1),
    zeta_sectorZeros_eq s, two_mul]

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

theorem tsupport_evenProj_subset_Icc {f : ℝ → ℂ} {a : ℝ} (hfs : tsupport f ⊆ Icc (-a) a) :
    tsupport (evenProj f) ⊆ Icc (-a) a := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hout
  apply hu
  have h1 : f u = 0 := image_eq_zero_of_notMem_tsupport fun h => hout (hfs h)
  have h2 : f (-u) = 0 := image_eq_zero_of_notMem_tsupport fun h => hout <| by
    have hmem := hfs h
    rw [Set.mem_Icc] at hmem ⊢
    exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
  simp [evenProj, testNeg, h1, h2]

theorem tsupport_oddProj_subset_Icc {f : ℝ → ℂ} {a : ℝ} (hfs : tsupport f ⊆ Icc (-a) a) :
    tsupport (oddProj f) ⊆ Icc (-a) a := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hout
  apply hu
  have h1 : f u = 0 := image_eq_zero_of_notMem_tsupport fun h => hout (hfs h)
  have h2 : f (-u) = 0 := image_eq_zero_of_notMem_tsupport fun h => hout <| by
    have hmem := hfs h
    rw [Set.mem_Icc] at hmem ⊢
    exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
  simp [oddProj, testNeg, h1, h2]

/-- On any functional-equation-symmetric tempered configuration, the Gram matrix of a finite family
`f` is the sum of the Gram matrices of its even and odd projections. -/
theorem zeroGram_eq_evenProj_add_oddProj (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) {ι : Type*} (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    zeroGram Z f = zeroGram Z (fun i => evenProj (f i)) + zeroGram Z (fun i => oddProj (f i)) := by
  ext i j
  simp only [Matrix.add_apply, zeroGram]
  conv_lhs => rw [← evenProj_add_oddProj (f i)]
  rw [W_add_left Z hZ (evenProj_contDiff (hf i)) (evenProj_hasCompactSupport (hfc i))
    (oddProj_contDiff (hf i)) (oddProj_hasCompactSupport (hfc i)) (hf j) (hfc j)]
  conv_lhs => rw [← evenProj_add_oddProj (f j)]
  rw [W_add_right Z hZ (evenProj_contDiff (hf i)) (evenProj_hasCompactSupport (hfc i))
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
  · refine iSup₂_le fun n f => iSup_le fun hf => ?_
    have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hf i).2
    have hG := zeroGram_eq_evenProj_add_oddProj Z hZ hFE f (fun i => (hf i).1) hfc
    have hle := negIndex_add_le
      (zeroGram_isHermitian Z (fun i => evenProj (f i)))
      (zeroGram_isHermitian Z (fun i => oddProj (f i)))
    rw [← hG] at hle
    have hle' : (hermNegIndex (zeroGram Z f) : ℕ∞) ≤
        (hermNegIndex (zeroGram Z fun i => evenProj (f i)) : ℕ∞) +
          (hermNegIndex (zeroGram Z fun i => oddProj (f i)) : ℕ∞) := by
      exact_mod_cast hle
    refine hle'.trans (add_le_add ?_ ?_)
    · exact le_sectorHodgeDefectAt Z (fun i => evenProj (f i)) fun i =>
        ⟨evenProj_contDiff (hf i).1, tsupport_evenProj_subset_Icc (hf i).2, testNeg_evenProj (f i)⟩
    · exact le_sectorHodgeDefectAt Z (fun i => oddProj (f i)) fun i =>
        ⟨oddProj_contDiff (hf i).1, tsupport_oddProj_subset_Icc (hf i).2, testNeg_oddProj (f i)⟩
  · -- Reverse inequality: concatenate any even family and any odd family supported in `[-a, a]`
    have hpair : ∀ (n₁ : ℕ) (g : Fin n₁ → ℝ → ℂ)
        (_ : ∀ i, ContDiff ℝ 2 (g i) ∧ tsupport (g i) ⊆ Icc (-a) a ∧ testNeg (g i) = (1 : ℂ) • g i)
        (n₂ : ℕ) (h : Fin n₂ → ℝ → ℂ)
        (_ : ∀ i, ContDiff ℝ 2 (h i) ∧ tsupport (h i) ⊆ Icc (-a) a ∧ testNeg (h i) = (-1 : ℂ) • h i),
        (hermNegIndex (zeroGram Z g) : ℕ∞) + (hermNegIndex (zeroGram Z h) : ℕ∞) ≤
          hodgeDefectAt Z a := by
      intro n₁ g hg n₂ h hh
      set e := finSumFinEquiv (m := n₁) (n := n₂)
      set gh : Fin (n₁ + n₂) → ℝ → ℂ := fun k => Sum.elim g h (e.symm k)
      have hgh : ∀ k, ContDiff ℝ 2 (gh k) ∧ tsupport (gh k) ⊆ Icc (-a) a := fun k => by
        rcases hk : e.symm k with i | j
        · simp only [gh, hk, Sum.elim_inl]
          exact ⟨(hg i).1, (hg i).2.1⟩
        · simp only [gh, hk, Sum.elim_inr]
          exact ⟨(hh j).1, (hh j).2.1⟩
      have hblock : zeroGram Z (Sum.elim g h) =
          fromBlocks (zeroGram Z g) 0 0 (zeroGram Z h) := by
        ext (i | i) (j | j)
        · rfl
        · simp [zeroGram, W_eq_zero_of_even_odd hFE (hg i).2.2 (hh j).2.2]
        · simp [zeroGram, W_eq_zero_of_odd_even hFE (hh i).2.2 (hg j).2.2]
        · rfl
      obtain ⟨W₁, hrank₁, hW₁⟩ :=
        exists_isPosDefOn_finrank_eq_posIndex (-(fromBlocks (zeroGram Z g) 0 0 (zeroGram Z h)))
      have hle_block := add_le_negIndex_fromBlocks_zero (zeroGram Z g) (zeroGram Z h)
      set L : (Fin n₁ ⊕ Fin n₂ → ℂ) ≃ₗ[ℂ] (Fin (n₁ + n₂) → ℂ) :=
        LinearEquiv.funCongrLeft ℂ ℂ e.symm
      have hquad_L : ∀ v : Fin n₁ ⊕ Fin n₂ → ℂ,
          hermQuad (-(zeroGram Z gh)) (L.toLinearMap v) =
            hermQuad (-(fromBlocks (zeroGram Z g) 0 0 (zeroGram Z h))) v := by
        intro v
        rw [← hblock, hermQuad_neg, hermQuad_neg]
        congr 1
        simp only [hermQuad, dotProduct, Matrix.mulVec]
        congr 1
        refine Fintype.sum_equiv e.symm _ _ fun k => ?_
        congr 1
        refine Fintype.sum_equiv e.symm _ _ fun l => ?_
        simp [L, gh, zeroGram]
      have hpd_L : IsPosDefOn (-(zeroGram Z gh)) (W₁.map L.toLinearMap) := by
        rintro w ⟨v, hv, rfl⟩ hw0
        have hv0 : v ≠ 0 := fun h0 => hw0 (by simp [h0])
        rw [hquad_L]
        exact hW₁ v hv hv0
      have hle_gh : hermNegIndex (fromBlocks (zeroGram Z g) 0 0 (zeroGram Z h)) ≤
          hermNegIndex (zeroGram Z gh) := by
        have hfin := finrank_le_posIndex hpd_L
        rwa [(Submodule.equivMapOfInjective L.toLinearMap L.injective W₁).symm.finrank_eq,
          hrank₁] at hfin
      have htot : (hermNegIndex (zeroGram Z g) : ℕ∞) + (hermNegIndex (zeroGram Z h) : ℕ∞) ≤
          (hermNegIndex (zeroGram Z gh) : ℕ∞) := by
        exact_mod_cast hle_block.trans hle_gh
      exact htot.trans (le_hodgeDefectAt Z gh hgh)
    have h0_even : ∀ i : Fin 0, ContDiff ℝ 2 ((![ ] : Fin 0 → ℝ → ℂ) i) ∧
        tsupport ((![ ] : Fin 0 → ℝ → ℂ) i) ⊆ Icc (-a) a ∧
        testNeg ((![ ] : Fin 0 → ℝ → ℂ) i) = (1 : ℂ) • (![ ] : Fin 0 → ℝ → ℂ) i :=
      fun i => Fin.elim0 i
    have h0_odd : ∀ i : Fin 0, ContDiff ℝ 2 ((![ ] : Fin 0 → ℝ → ℂ) i) ∧
        tsupport ((![ ] : Fin 0 → ℝ → ℂ) i) ⊆ Icc (-a) a ∧
        testNeg ((![ ] : Fin 0 → ℝ → ℂ) i) = (-1 : ℂ) • (![ ] : Fin 0 → ℝ → ℂ) i :=
      fun i => Fin.elim0 i
    have h0_neg : hermNegIndex (zeroGram Z (![ ] : Fin 0 → ℝ → ℂ)) = 0 :=
      negIndex_eq_zero_of_hermQuad_nonneg fun x => by simp [hermQuad, dotProduct]
    rcases eq_top_or_lt_top (hodgeDefectAt Z a) with htop | hlt
    · rw [htop]; exact le_top
    · obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hlt.ne
      rw [← hc]
      have h1 : ∀ (n₂ : ℕ) (h : Fin n₂ → ℝ → ℂ),
          (∀ i, ContDiff ℝ 2 (h i) ∧ tsupport (h i) ⊆ Icc (-a) a ∧
            testNeg (h i) = (-1 : ℂ) • h i) →
          sectorHodgeDefectAt Z 1 a + (hermNegIndex (zeroGram Z h) : ℕ∞) ≤ (c : ℕ∞) := by
        intro n₂ h hh
        have hb : (hermNegIndex (zeroGram Z h) : ℕ∞) ≤ (c : ℕ∞) := by
          have hp0 := hpair 0 ![ ] h0_even n₂ h hh
          rwa [h0_neg, Nat.cast_zero, zero_add, ← hc] at hp0
        have hb' : hermNegIndex (zeroGram Z h) ≤ c := ENat.coe_le_coe.mp hb
        have hsub : sectorHodgeDefectAt Z 1 a ≤
            ((c - hermNegIndex (zeroGram Z h) : ℕ) : ℕ∞) := by
          refine iSup₂_le fun n₁ g => iSup_le fun hg => ?_
          have hp := hpair n₁ g hg n₂ h hh
          rw [← hc, ← Nat.cast_add, ENat.coe_le_coe] at hp
          exact ENat.coe_le_coe.mpr (Nat.le_sub_of_add_le hp)
        calc sectorHodgeDefectAt Z 1 a + (hermNegIndex (zeroGram Z h) : ℕ∞)
            ≤ ((c - hermNegIndex (zeroGram Z h) : ℕ) : ℕ∞) +
                (hermNegIndex (zeroGram Z h) : ℕ∞) := by gcongr
          _ = (c : ℕ∞) := by rw [← Nat.cast_add, Nat.sub_add_cancel hb']
      rcases eq_top_or_lt_top (sectorHodgeDefectAt Z 1 a) with htop1 | hlt1
      · exfalso
        have hp1 := h1 0 ![ ] h0_odd
        rw [htop1, top_add] at hp1
        exact ENat.coe_ne_top c (eq_top_iff.mpr hp1)
      · obtain ⟨c₁, hc₁⟩ := ENat.ne_top_iff_exists.mp hlt1.ne
        rw [← hc₁]
        have hc₁_le : c₁ ≤ c := by
          have hp1 := h1 0 ![ ] h0_odd
          rw [← hc₁, h0_neg, Nat.cast_zero, add_zero, ENat.coe_le_coe] at hp1
          exact hp1
        have hsub2 : sectorHodgeDefectAt Z (-1) a ≤ ((c - c₁ : ℕ) : ℕ∞) := by
          refine iSup₂_le fun n₂ h => iSup_le fun hh => ?_
          have hp := h1 n₂ h hh
          rw [← hc₁, ← Nat.cast_add, ENat.coe_le_coe] at hp
          exact ENat.coe_le_coe.mpr (Nat.le_sub_of_add_le' hp)
        calc (c₁ : ℕ∞) + sectorHodgeDefectAt Z (-1) a
            ≤ (c₁ : ℕ∞) + ((c - c₁ : ℕ) : ℕ∞) := by gcongr
          _ = (c : ℕ∞) := by rw [← Nat.cast_add, Nat.add_sub_of_le hc₁_le]

/-- **Past the first prime, any Hodge defect of `ζ` is purely even.** For `a ≤ 181/500`, the odd
sector Hodge defect of `ζ` vanishes (`zeta_odd_sectorHodgeDefectAt_eq_zero`), so the full Hodge
defect at degree `a` equals the even-sector Hodge defect at degree `a`. -/
theorem zeta_hodgeDefectAt_eq_even_sectorHodgeDefectAt_of_le {a : ℝ} (ha : a ≤ 181 / 500) :
    hodgeDefectAt zetaZeroConfig a = sectorHodgeDefectAt zetaZeroConfig 1 a := by
  rw [hodgeDefectAt_eq_sectorHodgeDefectAt_add zetaZeroConfig temperedConfig_zetaZeroConfig
    fesSymmetric_zetaZeroConfig a, zeta_odd_sectorHodgeDefectAt_eq_zero ha, add_zero]

/-! ### 3. Symmetrized Hecke translates and the cyclic sector Pontryagin law -/

/-- The `s`-sector symmetrized Hecke translate `(1/2)(T_d g + s · testNeg (T_d g))`. -/
def symmTranslate (s : ℂ) (d : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  (1 / 2 : ℂ) • (translate d g + s • testNeg (translate d g))

theorem symmTranslate_contDiff {s : ℂ} {d : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (symmTranslate s d g) :=
  ((translate_contDiff hg d).add
    ((testNeg_contDiff (translate_contDiff hg d)).const_smul s)).const_smul (1 / 2 : ℂ)

theorem symmTranslate_hasCompactSupport {s : ℂ} {d : ℝ} {g : ℝ → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (symmTranslate s d g) :=
  ((translate_hasCompactSupport hgc d).add
    ((testNeg_hasCompactSupport (translate_hasCompactSupport hgc d)).smul_left)).smul_left

theorem testNeg_symmTranslate {s : ℂ} (hs : s = 1 ∨ s = -1) (d : ℝ) (g : ℝ → ℂ) :
    testNeg (symmTranslate s d g) = s • symmTranslate s d g := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> ring
  funext u
  simp only [symmTranslate, testNeg, Pi.smul_apply, Pi.add_apply, smul_eq_mul, neg_neg]
  linear_combination (-(1 / 2 : ℂ) * translate d g (-u)) * hs2

/-- The `s`-sector symmetrized translate as an element of `testSpace`. -/
def symmTranslateTest (s : ℂ) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (d : ℝ) : testSpace :=
  ⟨symmTranslate s d g, symmTranslate_contDiff hg, symmTranslate_hasCompactSupport hgc⟩

theorem symmTranslateTest_eq (s : ℂ) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (d : ℝ) :
    symmTranslateTest s hg hgc d =
      (1 / 2 : ℂ) • (translateTest hg hgc d +
        s • ⟨testNeg (translateTest hg hgc d),
          testNeg_contDiff (translateTest hg hgc d).2.1,
          testNeg_hasCompactSupport (translateTest hg hgc d).2.2⟩) :=
  rfl

theorem zeroMap_symmTranslateTest (Z : ZeroConfig) (hZ : TemperedConfig Z) (hFE : FESymmetric Z)
    (s : ℂ) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (d : ℝ) :
    zeroMap Z hZ (symmTranslateTest s hg hgc d) =
      (1 / 2 : ℂ) • (heckeVec Z hZ hg hgc d + s • fesVec hFE (heckeVec Z hZ hg hgc d)) := by
  rw [symmTranslateTest_eq, map_smul, map_add, map_smul, zeroMap_testNeg hFE hZ, heckeVec]

/-- **Attainment of the sector Hodge defect on a single symmetrized Hecke orbit.** For finitely many
distinct zeros in `sectorZeros Z s` there is a finite shift set `S ⊆ D` such that the Weil Gram
matrix of `{symmTranslate s d g | d ∈ S}` has at least that many negative squares. -/
theorem exists_symmTranslates_negIndex_ge (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgen : SpectrallyGeneric Z g) {D : Set ℝ} (hD : DenseShifts D)
    {s : ℂ} (hs : s = 1 ∨ s = -1) {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ι → ℂ)
    (hρ : Function.Injective ρ) (hS : ∀ i, ρ i ∈ sectorZeros Z s) :
    ∃ S : Finset ℝ, ↑S ⊆ D ∧
      Fintype.card ι ≤ hermNegIndex (zeroGram Z fun d : S => symmTranslate s d g) := by
  classical
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsn : ‖s‖ = 1 := by rcases hs with rfl | rfl <;> simp
  set r : ι → Z.carrier := fun i => ⟨ρ i, (hS i).1.1⟩ with hr
  have hrS : ∀ i, ((r i : Z.carrier) : ℂ) ∈ sectorZeros Z s := hS
  set w : ι → ℓ²(Z.carrier, ℂ) := fun i => sectorVec hFE s (r i) with hw
  set d : ι → ℝ := fun i => -4 - 4 * (if s = -1 ∧ conjCarrier hFE (r i) = r i then 1 else 0)
    with hd
  have hdle : ∀ i, d i ≤ -2 := fun i => by
    simp only [hd]
    split_ifs <;> norm_num
  have hRw : ∀ i j, inner ℂ (reflectVec Z (w j)) (w i) = if i = j then (d i : ℂ) else 0 := by
    intro i j
    rw [hw, inner_reflectVec_sectorVec hFE hs (hrS i) (hrS j)]
    have hrr : r i = r j ↔ i = j := ⟨fun h => hρ (congrArg Subtype.val h), fun h => h ▸ rfl⟩
    by_cases hij : i = j
    · subst hij
      simp only [if_true, hd]
      rcases hs with rfl | rfl
      · have hne : conjCarrier hFE (r i) ≠ r i := fun h => by
          have him := congrArg (fun t : Z.carrier => (t : ℂ).im) h
          simp only [conjCarrier, Complex.conj_im] at him
          rcases (hrS i).2 with h0 | ⟨h1, _⟩
          · linarith
          · norm_num at h1
        simp [hne]
      · by_cases hc : conjCarrier hFE (r i) = r i <;> norm_num [hc]
    · rw [if_neg (fun h => hij (hrr.mp h)), if_neg hij]
  set k := Fintype.card ι with hk
  set ε : ℝ := 1 / (9 * ((k : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  choose l hlD hl using fun i => exists_translates_near Z hZ hg hgc hgen hD (w i) hε0
  set S : Finset ℝ := Finset.univ.biUnion fun i => (l i).support with hSdef
  have hSD : ↑S ⊆ D := by
    intro u hu
    obtain ⟨i, -, hiu⟩ := Finset.mem_biUnion.mp hu
    exact hlD i hiu
  refine ⟨S, hSD, ?_⟩
  set t : S → testSpace := fun u => symmTranslateTest s hg hgc u with ht
  set C : Matrix ι S ℂ := fun i u => l i u with hC
  set f : ι → testSpace := fun i => ∑ u, C i u • t u with hf
  set Hvec : ι → ℓ²(Z.carrier, ℂ) := fun i =>
    ∑ u ∈ (l i).support, l i u • heckeVec Z hZ hg hgc u with hHvec
  have hfX : ∀ i, zeroMap Z hZ (f i) =
      (1 / 2 : ℂ) • (Hvec i + s • fesVec hFE (Hvec i)) := by
    intro i
    have hsum : zeroMap Z hZ (f i) =
        ∑ u ∈ (l i).support, l i u • zeroMap Z hZ (symmTranslateTest s hg hgc u) := by
      simp only [hf, map_sum, map_smul, hC, ht]
      rw [Finset.sum_coe_sort S (fun u => l i u • zeroMap Z hZ (symmTranslateTest s hg hgc u))]
      refine (Finset.sum_subset (fun u hu => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hu⟩)
        fun u _ hu => ?_).symm
      rw [Finsupp.notMem_support_iff.mp hu, zero_smul]
    rw [hsum]
    ext τ
    simp only [zeroMap_symmTranslateTest Z hZ hFE s hg hgc, Hvec, lp.coeFn_smul, lp.coeFn_add,
      fesVec_apply, lp.coeFn_sum, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => by ring
  have hnear : ∀ i, ‖zeroMap Z hZ (f i) - w i‖ < ε := fun i => by
    have hwsym : w i = (1 / 2 : ℂ) • (w i + s • fesVec hFE (w i)) := by
      rw [hw, fesVec_sectorVec hFE hs, smul_smul, hss, one_smul, ← two_smul ℂ, smul_smul]
      norm_num
    have hdiff : zeroMap Z hZ (f i) - w i =
        (1 / 2 : ℂ) • ((Hvec i - w i) + s • fesVec hFE (Hvec i - w i)) := by
      rw [hfX i, fesVec_sub, smul_sub]
      conv_lhs => rw [hwsym]
      rw [← smul_sub]
      congr 1
      abel
    rw [hdiff, norm_smul]
    have h1 : ‖Hvec i - w i‖ < ε := hl i
    have h2 : ‖s • fesVec hFE (Hvec i - w i)‖ < ε := by
      rw [norm_smul, hsn, one_mul, norm_fesVec]; exact h1
    have h3 := norm_add_le (Hvec i - w i) (s • fesVec hFE (Hvec i - w i))
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    linarith
  have hentry : ∀ i j, ‖zeroGram Z (fun i => (f i : ℝ → ℂ)) i j -
      (if i = j then (d i : ℂ) else 0)‖ ≤ 9 * ε := by
    intro i j
    have hGij : zeroGram Z (fun i => (f i : ℝ → ℂ)) i j =
        inner ℂ (reflectVec Z (zeroMap Z hZ (f j))) (zeroMap Z hZ (f i)) :=
      W_eq_inner Z hZ (f i) (f j)
    have hdi : zeroMap Z hZ (f i) = w i + (zeroMap Z hZ (f i) - w i) := by abel
    have hdj : zeroMap Z hZ (f j) = w j + (zeroMap Z hZ (f j) - w j) := by abel
    set ei := zeroMap Z hZ (f i) - w i
    set ej := zeroMap Z hZ (f j) - w j
    have hei : ‖ei‖ < ε := hnear i
    have hej : ‖ej‖ < ε := hnear j
    rw [hGij, hdi, hdj, reflectVec_add, inner_add_left, inner_add_right, inner_add_right, hRw i j]
    have h1 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z (w j)) ei).trans_eq
      (by rw [norm_reflectVec])
    have h2 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z ej) (w i)).trans_eq
      (by rw [norm_reflectVec])
    have h3 := (norm_inner_le_norm (𝕜 := ℂ) (reflectVec Z ej) ei).trans_eq
      (by rw [norm_reflectVec])
    have hwi := norm_sectorVec_le hFE hs (r i)
    have hwj := norm_sectorVec_le hFE hs (r j)
    calc ‖(if i = j then (d i : ℂ) else 0) + inner ℂ (reflectVec Z (w j)) ei +
          (inner ℂ (reflectVec Z ej) (w i) + inner ℂ (reflectVec Z ej) ei) -
            (if i = j then (d i : ℂ) else 0)‖
        = ‖inner ℂ (reflectVec Z (w j)) ei + inner ℂ (reflectVec Z ej) (w i) +
            inner ℂ (reflectVec Z ej) ei‖ := by congr 1; ring
      _ ≤ ‖w j‖ * ‖ei‖ + ‖ej‖ * ‖w i‖ + ‖ej‖ * ‖ei‖ :=
        norm_add₃_le.trans (add_le_add (add_le_add h1 h2) h3)
      _ ≤ 4 * ε + ε * 4 + ε * ε := by gcongr
      _ ≤ 9 * ε := by nlinarith
  have hη : 9 * ε * (Fintype.card ι : ℝ) ≤ 1 := by
    rw [← hk, hε]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    rw [show 9 * (1 / (9 * ((k : ℝ) + 1))) * k = k / (k + 1) by field_simp,
      div_le_one (by positivity)]
    linarith
  have hpd : IsPosDefOn (-(zeroGram Z fun i => (f i : ℝ → ℂ))) ⊤ := fun x _ hx0 => by
    rw [hermQuad_neg]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
    have hpos : 0 < ∑ i, ‖x i‖ ^ 2 :=
      lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) (Finset.single_le_sum
        (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
    linarith [hermQuad_le_of_near_diag _ d hdle hη hentry x]
  have h1 := finrank_le_posIndex hpd
  rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  have hcomb : zeroGram Z (fun i => (f i : ℝ → ℂ)) =
      C * zeroGram Z (fun u : S => symmTranslate s u g) * Cᴴ := zeroGram_comb Z hZ t C
  calc Fintype.card ι ≤ hermNegIndex (zeroGram Z fun i => (f i : ℝ → ℂ)) := h1
    _ = hermNegIndex (C * zeroGram Z (fun u : S => symmTranslate s u g) * Cᴴ) := by rw [hcomb]
    _ ≤ hermNegIndex (zeroGram Z fun u : S => symmTranslate s u g) :=
      hermNegIndex_mul_mul_conjTranspose_le C _

/-- **The cyclic sector Pontryagin law.** For any functional-equation-symmetric tempered
configuration `Z`, any spectrally generic test `g`, any dense shift set `D`, and either reflection
sector `s = ±1`, finite subfamilies of `{symmTranslate s d g | d ∈ D}` achieve `n` negative squares
of `W_Z` iff `(n : ℕ∞) ≤ (sectorZeros Z s).encard`. -/
theorem cyclic_sector_pontryagin_law (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hFE : FESymmetric Z) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgen : SpectrallyGeneric Z g) {D : Set ℝ} (hD : DenseShifts D)
    {s : ℂ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    (∃ S : Finset ℝ, ↑S ⊆ D ∧
      n ≤ hermNegIndex (zeroGram Z fun d : S => symmTranslate s d g)) ↔
        (n : ℕ∞) ≤ (sectorZeros Z s).encard := by
  classical
  constructor
  · rintro ⟨S, _, hle⟩
    exact (ENat.coe_le_coe.mpr hle).trans (negIndex_sector_le Z hZ hFE hs
      (fun d : S => symmTranslate s d g) (fun _ => symmTranslate_contDiff hg)
      (fun _ => symmTranslate_hasCompactSupport hgc) (fun _ => testNeg_symmTranslate hs _ g))
  · intro hn
    obtain ⟨t, hts, htn⟩ := Set.exists_subset_encard_eq hn
    have htf : t.Finite := Set.finite_of_encard_eq_coe htn
    have hcard : htf.toFinset.card = n := by
      have h := htf.encard_eq_coe_toFinset_card
      rw [htn] at h
      exact_mod_cast h.symm
    set e := htf.toFinset.equivFin
    set ρ : Fin n → ℂ := fun i => (e.symm (Fin.cast hcard.symm i) : ℂ)
    have hρ : Function.Injective ρ := fun i j h =>
      Fin.cast_injective _ (e.symm.injective (Subtype.ext h))
    have hS : ∀ i, ρ i ∈ sectorZeros Z s := fun i =>
      hts ((Set.Finite.mem_toFinset htf).mp (e.symm (Fin.cast hcard.symm i)).2)
    obtain ⟨S, hSD, hge⟩ :=
      exists_symmTranslates_negIndex_ge Z hZ hFE hg hgc hgen hD hs ρ hρ hS
    exact ⟨S, hSD, by simpa using hge⟩

/-- **For `ζ`, the symmetrized rational Hecke orbit of a single generic test carries each
reflection sector.** -/
theorem zeta_cyclic_sector_hodgeDefect_ratHecke {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgen : SpectrallyGeneric zetaZeroConfig g)
    {s : ℂ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    (∃ S : Finset ℝ, ↑S ⊆ ratHeckeShifts ∧
      1 + n ≤ hermPosIndex (intersectionGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        (fun d : S => symmTranslate s d g))) ↔
        (n : ℕ∞) ≤ {ρ | ρ ∈ rightZeros zetaZeroConfig ∧ 0 < ρ.im}.encard := by
  classical
  rw [← zeta_sectorZeros_eq s,
    ← cyclic_sector_pontryagin_law zetaZeroConfig temperedConfig_zetaZeroConfig
      fesSymmetric_zetaZeroConfig hg hgc hgen denseShifts_ratHecke hs n]
  refine exists_congr fun S => and_congr_right fun _ => ?_
  rw [posIndex_intersectionGram,
    weilGram_eq_zeroGram (fun d : S => symmTranslate s d g)
      (fun _ => symmTranslate_contDiff hg) (fun _ => symmTranslate_hasCompactSupport hgc)]
  omega

/-- **For `ζ`, the symmetrized Hecke orbit of any two distinct primes carries each reflection
sector.** -/
theorem zeta_cyclic_sector_hodgeDefect_twoPrimes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgen : SpectrallyGeneric zetaZeroConfig g) {s : ℂ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    (∃ S : Finset ℝ, ↑S ⊆ twoPrimeShifts p q ∧
      1 + n ≤ hermPosIndex (intersectionGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
        (fun d : S => symmTranslate s d g))) ↔
        (n : ℕ∞) ≤ {ρ | ρ ∈ rightZeros zetaZeroConfig ∧ 0 < ρ.im}.encard := by
  classical
  rw [← zeta_sectorZeros_eq s,
    ← cyclic_sector_pontryagin_law zetaZeroConfig temperedConfig_zetaZeroConfig
      fesSymmetric_zetaZeroConfig hg hgc hgen (denseShifts_twoPrime hp hq hpq) hs n]
  refine exists_congr fun S => and_congr_right fun _ => ?_
  rw [posIndex_intersectionGram,
    weilGram_eq_zeroGram (fun d : S => symmTranslate s d g)
      (fun _ => symmTranslate_contDiff hg) (fun _ => symmTranslate_hasCompactSupport hgc)]
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
      (fun _ => translate_contDiff hg _) (fun _ => translate_hasCompactSupport hgc _)
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    obtain ⟨S, hSD, hle⟩ :=
      (cyclic_pontryagin_law Z hZ hg hgc hgen hD n).mpr hn
    set R : ℝ := (insert 0 S).sup' ⟨0, Finset.mem_insert_self 0 S⟩ (fun d => |d|)
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

/-- **Depth blindness on `multiPairConfig`.** For any `n` distinct ordinates `γ : Fin n → ℝ` and any
two depth profiles `δ₁, δ₂ : Fin n → ℝ` in `(0, 1/2]`, `multiPairConfig` has the exact same global
Hodge defect `n` regardless of the depths `δ₁` and `δ₂`. -/
theorem multiPairConfig_depth_invariance {L : ℝ} (hL : 0 < L) {n : ℕ}
    (γ δ₁ δ₂ : Fin n → ℝ) (hinj : Function.Injective γ)
    (hδ₁ : ∀ k, 0 < δ₁ k) (hδ₁' : ∀ k, δ₁ k ≤ 1 / 2)
    (hδ₂ : ∀ k, 0 < δ₂ k) (hδ₂' : ∀ k, δ₂ k ≤ 1 / 2) :
    (⨆ a : ℝ, hodgeDefectAt (multiPairConfig hL δ₁ γ hδ₁ hδ₁') a) = n ∧
      (⨆ a : ℝ, hodgeDefectAt (multiPairConfig hL δ₂ γ hδ₂ hδ₂') a) = n := by
  have hinj₁ : Function.Injective fun k : Fin n => offLinePoint (δ₁ k) (γ k) := fun i j h =>
    hinj (by simpa [offLinePoint] using congrArg Complex.im h)
  have hinj₂ : Function.Injective fun k : Fin n => offLinePoint (δ₂ k) (γ k) := fun i j h =>
    hinj (by simpa [offLinePoint] using congrArg Complex.im h)
  exact ⟨iSup_hodgeDefectAt_multiPairConfig hL δ₁ γ hδ₁ hδ₁' hinj₁,
    iSup_hodgeDefectAt_multiPairConfig hL δ₂ γ hδ₂ hδ₂' hinj₂⟩

/-- **Multiplicity separation on `offLineClusterConfig`.** Every zero of `offLineClusterConfig` has
fixed depth `1/4` and every `n`-test Gram matrix has `hermNegIndex ≤ n`, yet the unbounded off-line
multiplicities drive the `L²`-normalised Weil form to `-∞` at every large support degree `a`. -/
theorem offLineClusterConfig_hodgeDefect_vs_l2_floor :
    (∀ ρ ∈ offLineClusterConfig.carrier, |ρ.re - 1 / 2| = 1 / 4) ∧
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ),
      hermNegIndex (zeroGram offLineClusterConfig f) ≤ n) ∧
    (∀ᶠ a : ℝ in atTop, ∀ C : ℝ, ∃ f : ℝ → ℂ,
      ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
        paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
        (offLineClusterConfig.W f f).re < -(C * ∫ u, ‖f u‖ ^ 2)) := by
  refine ⟨offLineClusterConfig_depth, fun n f => ?_,
    offLineClusterConfig_weil_unbounded_below⟩
  obtain ⟨W, hrank, _⟩ :=
    exists_isPosDefOn_finrank_eq_posIndex (-(zeroGram offLineClusterConfig f))
  rw [hermNegIndex, ← hrank]
  have h := Submodule.finrank_le W
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h

/-! ### 5. Unconditional growth rate of the Castelnuovo–Severi defect floor equals `zetaZeroWidth` -/

/-- **Uniform `H¹` Sobolev bound on the Chebyshev-gauge derivative of the autocorrelation.**
For every `F ∈ C¹_c(ℝ)` and every shift `t ∈ ℝ`,
`|gaugeDerivative (autocorr F) t| ≤ (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2`. -/
theorem abs_gaugeDerivative_autocorr_le_sobolev {F : ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (t : ℝ) :
    |gaugeDerivative (ArchimedeanAnomaly.autocorr F) t| ≤
      (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2 := by
  have h1 : ArchimedeanAnomaly.autocorr F = autoCorrelation F := rfl
  rw [gaugeDerivative, h1, deriv_autoCorrelation hF hFc]
  have h2 := abs_crossCorrelation_sub_half_autoCorrelation_le hF hFc t
  have hd0 : 0 ≤ ∫ x, deriv F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  linarith

/-- **Unconditional `H¹` Sobolev-normalised Castelnuovo–Severi defect floor from the zero width.**
For every `β > zetaZeroWidth`, there exists `C ≥ 0` such that for every degree `r > 0`, every test
subspace `V ≤ realTestsAt r` (in particular both `oddRealTestsAt r` and `realTestsAt r`), and every
cycle `x : ℝ × ℝ × V`,
`-(C * e^{2β r} * (∫ f² + ∫ (f')²)) ≤ (scalingSubsurface V).defect x x`.
No non-clustering or local density hypothesis on the zeros is used. -/
theorem exists_scalingSubsurface_sobolev_defect_floor_of_zetaZeroWidth_lt {β : ℝ}
    (hβ : zetaZeroWidth < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ V : Submodule ℝ realTests, V ≤ realTestsAt r →
      ∀ x : ℝ × ℝ × V,
        -(C * Real.exp (2 * β * r) *
            ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
          (scalingSubsurface V).defect x x := by
  set β₀ := (zetaZeroWidth + β) / 2 with hβ₀_def
  have hβ₀ : zetaZeroWidth < β₀ := by rw [hβ₀_def]; linarith
  have hε : 0 < β - β₀ := by rw [hβ₀_def]; linarith
  obtain ⟨C₀, hC₀, hfloor⟩ := exists_fullZeroForm_ge_neg_of_zetaZeroWidth_lt hβ₀
  set K := 2 * C₀ * (1 + 1 / (2 * (β - β₀)))
  refine ⟨K, by positivity, fun r hr V hV x => ?_⟩
  set F : ℝ → ℝ := (x.2.2.1 : ℝ → ℝ)
  have hF : ContDiff ℝ 2 F := x.2.2.1.2.1
  have hFc : HasCompactSupport F := x.2.2.1.2.2
  have hsupp : ∀ u : ℝ, r < |u| → F u = 0 := fun u hu =>
    image_eq_zero_of_notMem_tsupport fun hmem =>
      not_le_of_gt hu (abs_le.mpr (hV x.2.2.2 hmem))
  set D := (∫ u, F u ^ 2) + ∫ u, deriv F u ^ 2 with hD_def
  have hD : ∀ t : ℝ, |gaugeDerivative (ArchimedeanAnomaly.autocorr F) t| ≤ D :=
    abs_gaugeDerivative_autocorr_le_sobolev (hF.of_le (by norm_num)) hFc
  have hf := hfloor r hr.le F hF hFc hsupp D hD
  rw [scalingSubsurface_defect_self, weilPair_self_eq_fullZeroForm hF hFc]
  refine le_trans ?_ hf
  apply neg_le_neg
  have hF0 : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hd0 : 0 ≤ ∫ u, deriv F u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hD_le : (∫ u, F u ^ 2) + D ≤ 2 * D := by rw [hD_def]; linarith
  have hexp1 : 2 * (β - β₀) * r + 1 ≤ Real.exp (2 * (β - β₀) * r) := Real.add_one_le_exp _
  have hexp2 : 1 ≤ Real.exp (2 * (β - β₀) * r) := Real.one_le_exp (by positivity)
  have hlin : 1 + r ≤ (1 + 1 / (2 * (β - β₀))) * Real.exp (2 * (β - β₀) * r) := by
    have h1 : r ≤ 1 / (2 * (β - β₀)) * Real.exp (2 * (β - β₀) * r) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hsplit : Real.exp (2 * β * r) =
      Real.exp (2 * (β - β₀) * r) * Real.exp (2 * β₀ * r) := by
    rw [← Real.exp_add]; congr 1; ring
  calc C₀ * (1 + r) * Real.exp (2 * β₀ * r) * ((∫ u, F u ^ 2) + D)
      ≤ C₀ * ((1 + 1 / (2 * (β - β₀))) * Real.exp (2 * (β - β₀) * r)) *
          Real.exp (2 * β₀ * r) * (2 * D) := by
        gcongr
    _ = K * Real.exp (2 * β * r) * D := by
        rw [hsplit]; simp only [K]; ring

/-- Evaluation of an `H¹`-normalised defect floor on `scalingSubsurface (oddRealTestsAt r)` on a
real odd `C²_c` test `F` supported in `[-r, r]`. -/
theorem fullZeroForm_ge_of_scalingSubsurface_odd_sobolev_defect_floor {r B : ℝ}
    (hfloor : ∀ x : ℝ × ℝ × oddRealTestsAt r,
      -(B * ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
        (scalingSubsurface (oddRealTestsAt r)).defect x x)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hsupp : ∀ x, r < |x| → F x = 0) :
    -(B * ((∫ u, F u ^ 2) + ∫ u, deriv F u ^ 2)) ≤ fullZeroForm F := by
  have hf := hfloor (0, 0, mkOddRealTestsAt F hF hFc hodd hsupp)
  rwa [scalingSubsurface_defect_self,
    show ((mkOddRealTestsAt F hF hFc hodd hsupp).1 : ℝ → ℝ) = F from rfl,
    weilPair_self_eq_fullZeroForm hF hFc] at hf

/-- Uniform derivative energy bound for a real two-bump difference test `g(u + v/2) - g(u - v/2)`. -/
theorem integral_deriv_twoBump_re_sq_le {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : ℝ) :
    ∫ u, deriv (fun x => g (x + v / 2) - g (x - v / 2)) u ^ 2 ≤ 4 * ∫ u, deriv g u ^ 2 := by
  have hgd_cont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hgd_cs : HasCompactSupport (deriv g) := hgc.deriv
  have hgd_sq_int : Integrable (fun u => deriv g u ^ 2) volume :=
    ((hgd_cont.mul hgd_cont).integrable_of_hasCompactSupport hgd_cs.mul_left).congr
      (Filter.Eventually.of_forall fun u => (sq (deriv g u)).symm)
  have hderiv : ∀ u, deriv (fun x => g (x + v / 2) - g (x - v / 2)) u =
      deriv g (u + v / 2) - deriv g (u - v / 2) := fun u => by
    have hd1 : HasDerivAt (fun x => g (x + v / 2)) (deriv g (u + v / 2)) u :=
      HasDerivAt.comp_add_const u (v / 2) ((hg.differentiable one_ne_zero (u + v / 2)).hasDerivAt)
    have hd2 : HasDerivAt (fun x => g (x - v / 2)) (deriv g (u - v / 2)) u :=
      HasDerivAt.comp_sub_const u (v / 2) ((hg.differentiable one_ne_zero (u - v / 2)).hasDerivAt)
    exact (hd1.sub hd2).deriv
  have hgd1_int : Integrable (fun u => deriv g (u + v / 2) ^ 2) volume :=
    hgd_sq_int.comp_add_right (v / 2)
  have hgd2_int : Integrable (fun u => deriv g (u - v / 2) ^ 2) volume :=
    hgd_sq_int.comp_sub_right (v / 2)
  have hdiff_int : Integrable (fun u => (deriv g (u + v / 2) - deriv g (u - v / 2)) ^ 2) volume := by
    have hcont : Continuous fun u => deriv g (u + v / 2) - deriv g (u - v / 2) :=
      (hgd_cont.comp (continuous_id.add continuous_const)).sub
        (hgd_cont.comp (continuous_id.sub continuous_const))
    have hcs1 : HasCompactSupport fun u => deriv g (u + v / 2) :=
      hgd_cs.comp_homeomorph (Homeomorph.addRight (v / 2))
    have hcs2 : HasCompactSupport fun u => deriv g (u - v / 2) :=
      hgd_cs.comp_homeomorph (Homeomorph.subRight (v / 2))
    exact ((hcont.mul hcont).integrable_of_hasCompactSupport (hcs1.sub hcs2).mul_left).congr
      (Filter.Eventually.of_forall fun u => (sq _).symm)
  have hcongr : (∫ u, deriv (fun x => g (x + v / 2) - g (x - v / 2)) u ^ 2) =
      ∫ u, (deriv g (u + v / 2) - deriv g (u - v / 2)) ^ 2 := by
    congr 1; funext u; rw [hderiv u]
  rw [hcongr]
  have hmono : (∫ u, (deriv g (u + v / 2) - deriv g (u - v / 2)) ^ 2) ≤
      ∫ u, (2 * deriv g (u + v / 2) ^ 2 + 2 * deriv g (u - v / 2) ^ 2) := by
    refine integral_mono hdiff_int ((hgd1_int.const_mul 2).add (hgd2_int.const_mul 2)) fun u => ?_
    have := sq_nonneg (deriv g (u + v / 2) + deriv g (u - v / 2))
    linarith
  rw [integral_add (hgd1_int.const_mul 2) (hgd2_int.const_mul 2),
    integral_const_mul, integral_const_mul,
    integral_add_right_eq_self (fun u => deriv g u ^ 2) (v / 2),
    integral_sub_right_eq_self (fun u => deriv g u ^ 2) (v / 2)] at hmono
  linarith

/-- **Converse: an `H¹` Sobolev-normalised Castelnuovo–Severi defect floor at rate `σ` forces
`zetaZeroWidth ≤ σ`.** -/
theorem zetaZeroWidth_le_of_scalingSubsurface_odd_sobolev_defect_floor {σ C : ℝ} (hσ : 0 ≤ σ)
    (hfloor : ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
      -(C * Real.exp (2 * σ * r) *
          ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
        (scalingSubsurface (oddRealTestsAt r)).defect x x) :
    zetaZeroWidth ≤ σ := by
  obtain ⟨E, hE, hlaw⟩ := zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp
  obtain ⟨w, ⟨hw, hwlt⟩, hwE⟩ :=
    exists_mem_Ioo_notMem_of_countable (half_pos (Real.log_pos one_lt_two)) hE
  have hw2 : 2 * w < Real.log 2 := by linarith
  refine (hlaw w hw hw2 hwE σ hσ).mpr ?_
  have hg : ContDiff ℝ 2 (fun u => (modScaledBump w 0 u).re) :=
    Complex.reCLM.contDiff.comp (contDiff_modScaledBump_two w 0)
  have hgc : HasCompactSupport (fun u => (modScaledBump w 0 u).re) :=
    (hasCompactSupport_of_support_subset_abs (modScaledBump_support hw 0)).comp_left
      (g := fun z : ℂ => z.re) (by simp)
  set M := 2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) +
    4 * ∫ u, deriv (fun x => (modScaledBump w 0 x).re) u ^ 2 with hM_def
  refine ⟨max C 0 * Real.exp (2 * σ * w) * M, 2 * w + 1, by positivity, fun v hv => ?_⟩
  have hvw : 2 * w < v := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hr : 0 < v / 2 + w := by linarith
  set f : ℝ → ℂ := twoBump (modScaledBump w 0) v (-1) with hf_def
  have hf : ContDiff ℝ 2 f := contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]
  have hfc : HasCompactSupport f :=
    hasCompactSupport_twoBump
      (hasCompactSupport_of_support_subset_abs (modScaledBump_support hw 0)) v (-1)
  have hfs : tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) :=
    tsupport_twoBump_modScaledBump_subset hw hv0
  have hodd : ∀ x, f (-x) = -f x := twoBump_modScaledBump_zero_neg w v
  have hzero : ∀ x, v / 2 + w < |x| → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have hmem' := hfs hmem
      rw [Set.mem_Icc] at hmem'
      exact absurd (abs_le.mpr hmem') (not_le.mpr hx)
  have hRe : ContDiff ℝ 2 (fun u => (f u).re) := Complex.reCLM.contDiff.comp hf
  have hRec : HasCompactSupport (fun u => (f u).re) :=
    hfc.comp_left (g := fun z : ℂ => z.re) (by simp)
  have him0 : (fun u => (f u).im) = fun _ => 0 := by
    funext u
    exact Complex.conj_eq_iff_im.mp (twoBump_modScaledBump_zero_conj w v u)
  have hflF := fullZeroForm_ge_of_scalingSubsurface_odd_sobolev_defect_floor
    (hfloor (v / 2 + w) hr) hRe hRec (fun x => by simp [hodd x]) (fun x hx => by simp [hzero x hx])
  have hfl0 := fullZeroForm_ge_of_scalingSubsurface_odd_sobolev_defect_floor
    (hfloor (v / 2 + w) hr) (F := fun _ => 0) contDiff_const HasCompactSupport.zero
    (fun _ => by simp) (fun _ _ => rfl)
  have hfl0' : 0 ≤ fullZeroForm (fun u => (f u).im) := by
    rw [him0]
    simpa using hfl0
  have hF_mass : (∫ u, (f u).re ^ 2) = ∫ u, ‖f u‖ ^ 2 := by
    congr 1; funext u
    have hu : (f u).im = 0 := congrFun him0 u
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hu]
    ring
  have hRe_eq : (fun u => (f u).re) =
      fun u => (modScaledBump w 0 (u + v / 2)).re - (modScaledBump w 0 (u - v / 2)).re := by
    funext u
    rw [hf_def, twoBump_apply, neg_one_mul, ← sub_eq_add_neg, Complex.sub_re]
  have hF_deriv_sq : (∫ u, deriv (fun x => (f x).re) u ^ 2) ≤
      4 * ∫ u, deriv (fun x => (modScaledBump w 0 x).re) u ^ 2 := by
    rw [hRe_eq]
    exact integral_deriv_twoBump_re_sq_le (hg.of_le (by norm_num)) hgc v
  have hsob_le : (∫ u, (f u).re ^ 2) + ∫ u, deriv (fun x => (f x).re) u ^ 2 ≤ M := by
    rw [hF_mass, integral_norm_sq_twoBump_modScaledBump_eq hw hvw, hM_def]
    linarith
  have hsob0 : 0 ≤ (∫ u, (f u).re ^ 2) + ∫ u, deriv (fun x => (f x).re) u ^ 2 :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hW : -(max C 0 * Real.exp (2 * σ * (v / 2 + w)) * M) ≤ (zetaZeroConfig.W f f).re := by
    rw [zeta_W_re_eq_fullZeroForm_re_add_im hf hfc]
    have hC_le : C * Real.exp (2 * σ * (v / 2 + w)) *
          ((∫ u, (f u).re ^ 2) + ∫ u, deriv (fun x => (f x).re) u ^ 2) ≤
        max C 0 * Real.exp (2 * σ * (v / 2 + w)) * M := by
      calc C * Real.exp (2 * σ * (v / 2 + w)) *
            ((∫ u, (f u).re ^ 2) + ∫ u, deriv (fun x => (f x).re) u ^ 2)
          ≤ max C 0 * Real.exp (2 * σ * (v / 2 + w)) *
              ((∫ u, (f u).re ^ 2) + ∫ u, deriv (fun x => (f x).re) u ^ 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_nonneg _)) hsob0
        _ ≤ max C 0 * Real.exp (2 * σ * (v / 2 + w)) * M :=
            mul_le_mul_of_nonneg_left hsob_le
              (mul_nonneg (le_max_right C 0) (Real.exp_nonneg _))
    linarith [hflF, hfl0', hC_le]
  rw [zeta_W_eq_literatureRHS (f := f) hf hfc,
    literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv0] at hW
  have hexp : Real.exp (2 * σ * (v / 2 + w)) = Real.exp (σ * v) * Real.exp (2 * σ * w) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp] at hW
  calc -(max C 0 * Real.exp (2 * σ * w) * M * Real.exp (σ * v))
      = -(max C 0 * (Real.exp (σ * v) * Real.exp (2 * σ * w)) * M) := by ring
    _ ≤ _ := hW

/-- **Unconditional `H¹` Sobolev-normalised Castelnuovo–Severi zero-width equivalence on the odd
scaling subsurface.** Without any hypothesis on the local distribution or clustering of off-line
zeros, `zetaZeroWidth ≤ σ` (`σ ≥ 0`) holds if and only if at every rate `β > σ` there is a constant
`C ≥ 0` such that `δ(x, x) ≥ -C e^{2β r} (∫ f² + ∫ (f')²)` on `scalingSubsurface (oddRealTestsAt r)`
at every degree `r > 0`. -/
theorem zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔
      ∀ β : ℝ, σ < β → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
        -(C * Real.exp (2 * β * r) *
            ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
          (scalingSubsurface (oddRealTestsAt r)).defect x x := by
  constructor
  · intro hle β hβ
    obtain ⟨C, hC0, hC⟩ :=
      exists_scalingSubsurface_sobolev_defect_floor_of_zetaZeroWidth_lt (lt_of_le_of_lt hle hβ)
    exact ⟨C, hC0, fun r hr x => hC r hr (oddRealTestsAt r) (fun _ hf => hf.1) x⟩
  · intro hfloor
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨C, -, hC⟩ := hfloor (σ + ε) (by linarith)
    exact zetaZeroWidth_le_of_scalingSubsurface_odd_sobolev_defect_floor (by linarith) hC

/-- **Unconditional `H¹` Sobolev-normalised Castelnuovo–Severi zero-width equivalence on the full
scaling subsurface `realTestsAt r`.** -/
theorem zetaZeroWidth_le_iff_scalingSubsurface_sobolev_defect_floor {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔
      ∀ β : ℝ, σ < β → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × realTestsAt r,
        -(C * Real.exp (2 * β * r) *
            ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
          (scalingSubsurface (realTestsAt r)).defect x x := by
  constructor
  · intro hle β hβ
    obtain ⟨C, hC0, hC⟩ :=
      exists_scalingSubsurface_sobolev_defect_floor_of_zetaZeroWidth_lt (lt_of_le_of_lt hle hβ)
    exact ⟨C, hC0, fun r hr x => hC r hr (realTestsAt r) le_rfl x⟩
  · intro hfloor
    rw [zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor hσ]
    intro β hβ
    obtain ⟨C, hC0, hC⟩ := hfloor β hβ
    exact ⟨C, hC0, fun r hr x => hC r hr (x.1, x.2.1, ⟨x.2.2.1, x.2.2.2.1⟩)⟩

/-- The set of admissible exponential growth rates of the `H¹`-normalised Castelnuovo–Severi defect
floor on `scalingSubsurface (oddRealTestsAt r)`. -/
def oddDefectFloorRates : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × oddRealTestsAt r,
    -(C * Real.exp (2 * β * r) *
        ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
      (scalingSubsurface (oddRealTestsAt r)).defect x x}

/-- The set of admissible exponential growth rates of the `H¹`-normalised Castelnuovo–Severi defect
floor on `scalingSubsurface (realTestsAt r)`. -/
def fullDefectFloorRates : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x : ℝ × ℝ × realTestsAt r,
    -(C * Real.exp (2 * β * r) *
        ((∫ u, (x.2.2.1 : ℝ → ℝ) u ^ 2) + ∫ u, deriv (x.2.2.1 : ℝ → ℝ) u ^ 2)) ≤
      (scalingSubsurface (realTestsAt r)).defect x x}

/-- The growth rate of the Castelnuovo–Severi defect floor in the degree `r` on the odd scaling
subsurface. -/
def oddDefectFloorRate : ℝ := sInf oddDefectFloorRates

/-- The growth rate of the Castelnuovo–Severi defect floor in the degree `r` on the full scaling
subsurface. -/
def fullDefectFloorRate : ℝ := sInf fullDefectFloorRates

/-- **The growth of the Castelnuovo–Severi defect floor in the degree on the odd scaling subsurface
is unconditionally the zero width `zetaZeroWidth`.** -/
theorem oddDefectFloorRate_eq_zetaZeroWidth : oddDefectFloorRate = zetaZeroWidth := by
  have hne : oddDefectFloorRates.Nonempty := by
    obtain ⟨C, hC0, hC⟩ :=
      (zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor zetaZeroWidth_nonneg).mp
        le_rfl (zetaZeroWidth + 1) (by linarith)
    exact ⟨zetaZeroWidth + 1, by linarith [zetaZeroWidth_nonneg], C, hC0, hC⟩
  have hbdd : BddBelow oddDefectFloorRates := ⟨zetaZeroWidth, fun β ⟨hβ0, C, _, hC⟩ =>
    zetaZeroWidth_le_of_scalingSubsurface_odd_sobolev_defect_floor hβ0 hC⟩
  refine le_antisymm ?_ (le_csInf hne fun β ⟨hβ0, C, _, hC⟩ =>
    zetaZeroWidth_le_of_scalingSubsurface_odd_sobolev_defect_floor hβ0 hC)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨C, hC0, hC⟩ :=
    (zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor zetaZeroWidth_nonneg).mp
      le_rfl (zetaZeroWidth + ε) (by linarith)
  exact csInf_le hbdd ⟨by linarith [zetaZeroWidth_nonneg], C, hC0, hC⟩

/-- **The growth of the Castelnuovo–Severi defect floor in the degree on the full scaling subsurface
is unconditionally the zero width `zetaZeroWidth`.** -/
theorem fullDefectFloorRate_eq_zetaZeroWidth : fullDefectFloorRate = zetaZeroWidth := by
  have hne : fullDefectFloorRates.Nonempty := by
    obtain ⟨C, hC0, hC⟩ :=
      (zetaZeroWidth_le_iff_scalingSubsurface_sobolev_defect_floor zetaZeroWidth_nonneg).mp
        le_rfl (zetaZeroWidth + 1) (by linarith)
    exact ⟨zetaZeroWidth + 1, by linarith [zetaZeroWidth_nonneg], C, hC0, hC⟩
  have hbdd : BddBelow fullDefectFloorRates := ⟨zetaZeroWidth, fun β ⟨hβ0, C, _, hC⟩ =>
    zetaZeroWidth_le_of_scalingSubsurface_odd_sobolev_defect_floor hβ0 fun r hr x =>
      hC r hr (x.1, x.2.1, ⟨x.2.2.1, x.2.2.2.1⟩)⟩
  refine le_antisymm ?_ (le_csInf hne fun β ⟨hβ0, C, _, hC⟩ =>
    zetaZeroWidth_le_of_scalingSubsurface_odd_sobolev_defect_floor hβ0 fun r hr x =>
      hC r hr (x.1, x.2.1, ⟨x.2.2.1, x.2.2.2.1⟩))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨C, hC0, hC⟩ :=
    (zetaZeroWidth_le_iff_scalingSubsurface_sobolev_defect_floor zetaZeroWidth_nonneg).mp
      le_rfl (zetaZeroWidth + ε) (by linarith)
  exact csInf_le hbdd ⟨by linarith [zetaZeroWidth_nonneg], C, hC0, hC⟩

/-! ### 6. Master metrology synthesis: what the failure of the Hodge index measures -/

/-- **What the failure of the Hodge index measures (`whatTheFailureOfTheHodgeIndexMeasures`).**
Collects the five metrological laws of the failure of the arithmetic Hodge index into a single
unconditional theorem:
1. **Degree filtration & global cardinal:** at every degree `a`, the Hodge defect splits additively
   into the even and odd reflection sectors (`hodgeDefectAt Z a = sectorHodgeDefectAt Z 1 a +
   sectorHodgeDefectAt Z (-1) a`), and its supremum over `a` is `(rightZeros Z).encard =
   (sectorZeros Z 1).encard + (sectorZeros Z (-1)).encard`.
2. **Past the first prime for `ζ`:** for `a ≤ 181/500`, the odd reflection sector of `ζ` has defect
   `0`, so `hodgeDefectAt zetaZeroConfig a = sectorHodgeDefectAt zetaZeroConfig 1 a`.
3. **Cyclic two-prime Hecke-orbit readout:** for any two distinct primes `p ≠ q` and any spectrally
   generic test `g`, the `s`-sector symmetrized two-prime Hecke orbit of `g` carries the entire
   reflection-sector defect of `ζ`.
4. **Invariance under depth and multiplicity:** the global and sector Hodge defects depend only on
   `(rightZeros Z).encard` and `(sectorZeros Z s).encard`, never on depth or multiplicity, whereas
   unbounded multiplicities at fixed depth `1/4` drive the raw `L²` floor to `-∞`.
5. **Growth of the defect floor is the zero width:** both `oddDefectFloorRate` and
   `fullDefectFloorRate` equal `zetaZeroWidth` unconditionally. -/
theorem whatTheFailureOfTheHodgeIndexMeasures :
    (∀ (Z : ZeroConfig), TemperedConfig Z → FESymmetric Z →
      (∀ a : ℝ, hodgeDefectAt Z a = sectorHodgeDefectAt Z 1 a + sectorHodgeDefectAt Z (-1) a) ∧
      (rightZeros Z).encard = (sectorZeros Z 1).encard + (sectorZeros Z (-1)).encard) ∧
    (∀ a : ℝ, a ≤ 181 / 500 →
      hodgeDefectAt zetaZeroConfig a = sectorHodgeDefectAt zetaZeroConfig 1 a) ∧
    (∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q → ∀ {g : ℝ → ℂ}, ContDiff ℝ 2 g →
      HasCompactSupport g → SpectrallyGeneric zetaZeroConfig g →
      ∀ {s : ℂ}, (s = 1 ∨ s = -1) → ∀ n : ℕ,
        (∃ S : Finset ℝ, ↑S ⊆ twoPrimeShifts p q ∧
          1 + n ≤ hermPosIndex (intersectionGram (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
            (fun d : S => symmTranslate s d g))) ↔
          (n : ℕ∞) ≤ {ρ | ρ ∈ rightZeros zetaZeroConfig ∧ 0 < ρ.im}.encard) ∧
    (∀ Z₁ Z₂ : ZeroConfig, TemperedConfig Z₁ → TemperedConfig Z₂ →
      (rightZeros Z₁).encard = (rightZeros Z₂).encard →
      (⨆ a : ℝ, hodgeDefectAt Z₁ a) = ⨆ a : ℝ, hodgeDefectAt Z₂ a) ∧
    oddDefectFloorRate = zetaZeroWidth ∧
    fullDefectFloorRate = zetaZeroWidth :=
  ⟨fun Z hZ hFE => ⟨hodgeDefectAt_eq_sectorHodgeDefectAt_add Z hZ hFE,
      rightZeros_encard_eq_sectorZeros_add hFE⟩,
   fun _ ha => zeta_hodgeDefectAt_eq_even_sectorHodgeDefectAt_of_le ha,
   fun {_ _} hp hq hpq {_} hg hgc hgen {_} hs n =>
     zeta_cyclic_sector_hodgeDefect_twoPrimes hp hq hpq hg hgc hgen hs n,
   iSup_hodgeDefectAt_eq_of_rightZeros_encard_eq,
   oddDefectFloorRate_eq_zetaZeroWidth,
   fullDefectFloorRate_eq_zetaZeroWidth⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
