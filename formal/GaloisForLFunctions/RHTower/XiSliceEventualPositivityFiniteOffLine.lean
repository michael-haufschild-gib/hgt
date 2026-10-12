import GaloisForLFunctions.RHTower.XiSliceCoeffDensity
import GaloisForLFunctions.RHTower.XiLogDerivEventualPositivity

/-!
# Large-height slice positivity is "finitely many off-line zeros"

RH is equivalent to the nonnegativity of every Taylor coefficient `c_n(t)` of the slice product
`ξ(½ + x + it) ξ(½ − x + it)` at every height `t` (`riemannHypothesis_iff_xiSliceCoeff_nonneg`).

**Theorem** (`eventualSlicePositivity_iff_finiteOffLine`).  All slice coefficients are nonnegative
at every height `|t| ≥ T`, for some `T`, if and only if only finitely many zeros of `ξ` lie off the
critical line.

* Finitely many off-line zeros have bounded shadows `[γ − |β − ½|, γ + |β − ½|]`, and every slice
  coefficient is nonnegative off the shadows (`xiSliceCoeff_nonneg_of_not_mem_xiShadow`).
* A slice with nonnegative coefficients has no off-line zero at its own height
  (`re_eq_half_of_xiSliceCoeff_nonneg`), so off-line zeros have bounded ordinates.

The slice receiver reads an off-line zero at its exact ordinate.  So its large-height form is
strictly stronger than the large-height forms of the depth-margin receivers (Hadamard positivity on
`Re s ≥ σ`, finite cosine defects), which are "zeros approach the line"
(`eventualHadamardPositivity_iff_zerosApproachLine`).  The ladder of large-height receivers is

  finitely many off-line zeros  ⟹  zeros approach the line  ⟹  LH ∧ a zero-free half-plane

(`zerosApproachLine_of_finiteOffLine`).
-/

open Complex Set
open scoped ComplexOrder

namespace RHTower.BacklundConverse

open RHTower.LindelofSparse RHTower.CosineSparseCluster RHTower.DeBruijn RHTower.CosineDefectBudget

noncomputable section

/-- Only finitely many zero copies lie off the critical line. -/
def FiniteOffLine : Prop := {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite

/-- Every slice coefficient is nonnegative at every large height. -/
def EventualSlicePositivity : Prop :=
  ∃ T : ℝ, ∀ t : ℝ, T ≤ |t| → ∀ n : ℕ, 0 ≤ xiSliceCoeff t n

/-- **Finitely many off-line zeros give slice positivity at every large height.** -/
theorem eventualSlicePositivity_of_finiteOffLine (hF : FiniteOffLine) :
    EventualSlicePositivity := by
  obtain ⟨M, hM⟩ := (hF.image fun q => |(xiSpectralPoint q).re|).bddAbove
  refine ⟨M + 1, fun t ht n => xiSliceCoeff_nonneg_of_not_mem_xiShadow (fun hsh => ?_) n⟩
  obtain ⟨ζ, hζ, hlt⟩ := hsh
  rw [riemannHeat_zero] at hζ
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hζ
  have hre : (xiSpectralPoint q).re = ζ.re := by
    rw [spectral_re_eq, hq]; simp
  have him : (xiSpectralPoint q).im = ζ.im := by
    rw [spectral_im_eq, hq]; simp
  have hhalf := abs_spectral_im_lt_half q
  rw [him] at hhalf
  have hne : (xiSpectralPoint q).im ≠ 0 := by
    rw [him]; intro h0; rw [h0] at hlt; nlinarith [sq_nonneg (ζ.re - t)]
  have hbd : |ζ.re| ≤ M := by rw [← hre]; exact hM ⟨q, hne, rfl⟩
  have hclose : |ζ.re - t| < 1 / 2 := by
    have h1 : (ζ.re - t) ^ 2 < (1 / 2) ^ 2 := by
      nlinarith [sq_abs ζ.im, abs_nonneg ζ.im]
    exact abs_lt_of_sq_lt_sq h1 (by norm_num)
  have := abs_sub_abs_le_abs_sub t ζ.re
  rw [abs_sub_comm t ζ.re] at this
  linarith

/-- **Slice positivity at every large height leaves finitely many off-line zeros.** -/
theorem finiteOffLine_of_eventualSlicePositivity (hE : EventualSlicePositivity) :
    FiniteOffLine := by
  obtain ⟨T, hT⟩ := hE
  have hbound : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 → |(xiSpectralPoint q).re| < T := by
    intro q hq
    by_contra hge
    rw [not_lt, spectral_re_eq] at hge
    have hre := re_eq_half_of_xiSliceCoeff_nonneg (hT _ hge) (xi_xiZeroCopy_eq_zero q) rfl
    apply hq
    rw [spectral_im_eq, hre]; ring
  refine (xiZeroBall (⌈|T| + 1⌉₊)).finite_toSet.subset fun q hq => ?_
  simp only [Finset.mem_coe, mem_xiZeroBall]
  have h1 := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
  have h2 := abs_spectral_im_lt_half q
  have h3 : |T| + 1 ≤ (⌈|T| + 1⌉₊ : ℝ) := Nat.le_ceil _
  have h4 := (hbound q hq).trans_le (le_abs_self T)
  linarith

/-- **Large-height slice positivity is exactly "finitely many off-line zeros".** -/
theorem eventualSlicePositivity_iff_finiteOffLine : EventualSlicePositivity ↔ FiniteOffLine :=
  ⟨finiteOffLine_of_eventualSlicePositivity, eventualSlicePositivity_of_finiteOffLine⟩

/-- Finitely many off-line zeros make the zeros approach the line. -/
theorem zerosApproachLine_of_finiteOffLine (hF : FiniteOffLine) : ZerosApproachLine :=
  fun h hh => hF.subset fun q hq => by
    have hq' : h < (xiSpectralPoint q).im := hq
    show (xiSpectralPoint q).im ≠ 0
    linarith

/-- **Large-height slice positivity implies eventual Hadamard positivity and LH.** -/
theorem eventualHadamardPositivity_of_eventualSlicePositivity (hE : EventualSlicePositivity) :
    EventualHadamardPositivity :=
  eventualHadamardPositivity_of_zerosApproachLine
    (zerosApproachLine_of_finiteOffLine (finiteOffLine_of_eventualSlicePositivity hE))

end

end RHTower.BacklundConverse
