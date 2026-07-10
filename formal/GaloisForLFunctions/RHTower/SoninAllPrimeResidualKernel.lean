/-
The convergent all-prime Sonin residual kernel.

The raw Euler corner cannot be summed in any Schatten ideal because its linear prime energy is
the divergent series `sum_p 1/p`.  After deleting that universal principal shell, the actual
prime-power residual at `p^(k+2)` is weighted by `p^(-(k+2)/2)/(k+2)`.  The scale-independent
Hilbert--Schmidt estimate proved in `SoninTimeBandHilbertSchmidt` makes the sum of the resulting
block energies finite.

This file performs the actual assembly.  It uses the canonical Hilbert basis of the Sonin
`L²` space, places each weighted residual matrix on its own prime-power diagonal block, proves
that the complete block matrix is Hilbert--Schmidt, and forms its positive trace-class Gram
kernel.  No zero set and no RH statement enter the construction.
-/
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt
import GaloisForLFunctions.HilbertSchmidtCompact
import GaloisForLFunctions.HilbertSchmidtMatrix

noncomputable section

open scoped BigOperators

namespace RHTower

set_option maxHeartbeats 600000

private theorem tsum_sq_norm_inner_hilbertBasis
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (x : H) :
    ∑' i, ‖inner ℂ (b i) x‖ ^ 2 = ‖x‖ ^ 2 := by
  apply Complex.ofReal_injective
  calc
    ((∑' i, ‖inner ℂ (b i) x‖ ^ 2 : ℝ) : ℂ) =
        ∑' i, ((‖inner ℂ (b i) x‖ ^ 2 : ℝ) : ℂ) :=
      Complex.ofReal_tsum (fun i => ‖inner ℂ (b i) x‖ ^ 2)
    _ = ∑' i, inner ℂ x (b i) * inner ℂ (b i) x := by
      apply tsum_congr
      intro i
      rw [← inner_conj_symm, RCLike.norm_conj, RCLike.mul_conj]
      norm_cast
    _ = inner ℂ x x := b.tsum_inner_mul_inner x x
    _ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast

/-- The index of the canonical Hilbert basis of the actual Sonin `L²` space. -/
abbrev SoninHilbertIndex := (exists_hilbertBasis ℂ SoninL2).choose

/-- Prime powers paired with the canonical Sonin basis index. -/
abbrev SoninAllPrimeIndex := (Nat.Primes × ℕ) × SoninHilbertIndex

/-- The block-diagonal matrix of the actual logarithmically weighted, principal-subtracted Sonin
residuals.  Different prime-power blocks do not mix. -/
def soninAllPrimeResidualKernel (a : ℝ) :
    SoninAllPrimeIndex × SoninAllPrimeIndex → ℂ := fun z =>
  if z.1.1 = z.2.1 then
    inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 z.1.2)
      (centralSoninWeightedPrimePowerResidual a z.1.1
        (ContinuousLinearMap.hsBasis ℂ SoninL2 z.2.2))
  else 0

private theorem block_entries_summable
    {T : SoninL2 →L[ℂ] SoninL2} (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    Summable (fun ji : SoninHilbertIndex × SoninHilbertIndex =>
      ‖inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 ji.2)
        (T (ContinuousLinearMap.hsBasis ℂ SoninL2 ji.1))‖ ^ 2) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · intro j
    exact (ContinuousLinearMap.hsBasis ℂ SoninL2).orthonormal.inner_products_summable
      (T (ContinuousLinearMap.hsBasis ℂ SoninL2 j))
  · refine (hT.summable (ContinuousLinearMap.hsBasis ℂ SoninL2)).congr (fun j => ?_)
    exact (tsum_sq_norm_inner_hilbertBasis (ContinuousLinearMap.hsBasis ℂ SoninL2)
      (T (ContinuousLinearMap.hsBasis ℂ SoninL2 j))).symm

private theorem all_blocks_entries_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun pji : (Nat.Primes × ℕ) ×
        (SoninHilbertIndex × SoninHilbertIndex) =>
      ‖inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 pji.2.2)
        (centralSoninWeightedPrimePowerResidual a pji.1
          (ContinuousLinearMap.hsBasis ℂ SoninL2 pji.2.1))‖ ^ 2) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · intro pk
    change Summable (fun ji : SoninHilbertIndex × SoninHilbertIndex =>
      ‖inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 ji.2)
        (centralSoninWeightedPrimePowerResidual a pk
          (ContinuousLinearMap.hsBasis ℂ SoninL2 ji.1))‖ ^ 2)
    exact block_entries_summable
      (T := centralSoninWeightedPrimePowerResidual a pk)
      (centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha pk)
  · refine (summable_centralSoninWeightedPrimePowerResidual_hsNormSq a ha).congr
      (fun pk => ?_)
    have hT := centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha pk
    rw [ContinuousLinearMap.hsNormSq_eq hT
      (ContinuousLinearMap.hsBasis ℂ SoninL2)]
    rw [(block_entries_summable hT).tsum_prod]
    apply tsum_congr
    intro j
    exact (tsum_sq_norm_inner_hilbertBasis (ContinuousLinearMap.hsBasis ℂ SoninL2)
      (centralSoninWeightedPrimePowerResidual a pk
        (ContinuousLinearMap.hsBasis ℂ SoninL2 j))).symm

/-- The diagonal support where the row and column prime powers agree. -/
def soninAllPrimeBlockDiagonalSupport :
    Set (SoninAllPrimeIndex × SoninAllPrimeIndex) :=
  {z | z.1.1 = z.2.1}

private def soninAllPrimeBlockDiagonalEquiv :
    (Nat.Primes × ℕ) × (SoninHilbertIndex × SoninHilbertIndex) ≃
      soninAllPrimeBlockDiagonalSupport where
  toFun pji := ⟨((pji.1, pji.2.2), (pji.1, pji.2.1)), rfl⟩
  invFun z := (z.1.1.1, (z.1.2.2, z.1.1.2))
  left_inv pji := by
    rcases pji with ⟨pk, j, i⟩
    rfl
  right_inv z := by
    apply Subtype.ext
    rcases z with ⟨⟨⟨pk, i⟩, ⟨qk, j⟩⟩, h⟩
    change pk = qk at h
    subst qk
    rfl

/-- **Convergent all-prime residual.** The complete block-diagonal matrix assembled from the
actual weighted Sonin residuals is Hilbert--Schmidt. -/
theorem soninAllPrimeResidualKernel_isHS (a : ℝ) (ha : 0 < a) :
    HilbertSchmidt.IsHS (soninAllPrimeResidualKernel a) := by
  let energy : SoninAllPrimeIndex × SoninAllPrimeIndex → ℝ :=
    fun z => ‖soninAllPrimeResidualKernel a z‖ ^ 2
  have hcomp : Summable (fun pji : (Nat.Primes × ℕ) ×
      (SoninHilbertIndex × SoninHilbertIndex) =>
      energy (soninAllPrimeBlockDiagonalEquiv pji)) := by
    refine (all_blocks_entries_summable a ha).congr (fun pji => ?_)
    simp [energy, soninAllPrimeBlockDiagonalEquiv, soninAllPrimeResidualKernel]
  have hsub : Summable (energy ∘ Subtype.val :
      soninAllPrimeBlockDiagonalSupport → ℝ) :=
    (soninAllPrimeBlockDiagonalEquiv.summable_iff).mp hcomp
  have hindicator : Summable (soninAllPrimeBlockDiagonalSupport.indicator energy) :=
    summable_subtype_iff_indicator.mp hsub
  exact hindicator.congr fun z => by
    show soninAllPrimeBlockDiagonalSupport.indicator energy z =
      ‖soninAllPrimeResidualKernel a z‖ ^ 2
    by_cases hz : z ∈ soninAllPrimeBlockDiagonalSupport
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      have hne : z.1.1 ≠ z.2.1 := by
        simpa [soninAllPrimeBlockDiagonalSupport] using hz
      simp [soninAllPrimeResidualKernel, hne]

/-- The positive Gram kernel `K_aᴴ K_a` of the assembled all-prime residual. -/
def soninAllPrimeResidualEnergyKernel (a : ℝ) :
    SoninAllPrimeIndex × SoninAllPrimeIndex → ℂ :=
  HilbertSchmidt.hsComp (HilbertSchmidt.hsAdjoint (soninAllPrimeResidualKernel a))
    (soninAllPrimeResidualKernel a)

/-- The positive Gram kernel of the all-prime residual is trace class, presented as the
composition of two Hilbert--Schmidt kernels. -/
theorem soninAllPrimeResidualEnergyKernel_isHS (a : ℝ) (ha : 0 < a) :
    HilbertSchmidt.IsHS (soninAllPrimeResidualEnergyKernel a) :=
  HilbertSchmidt.isHS_hsComp
    (HilbertSchmidt.isHS_hsAdjoint (soninAllPrimeResidualKernel_isHS a ha))
    (soninAllPrimeResidualKernel_isHS a ha)

/-- The all-prime residual Gram kernel is self-adjoint. -/
theorem soninAllPrimeResidualEnergyKernel_selfAdjoint (a : ℝ) :
    HilbertSchmidt.hsAdjoint (soninAllPrimeResidualEnergyKernel a) =
      soninAllPrimeResidualEnergyKernel a := by
  rw [soninAllPrimeResidualEnergyKernel, HilbertSchmidt.hsAdjoint_hsComp,
    HilbertSchmidt.hsAdjoint_hsAdjoint]

/-- The trace of the all-prime residual Gram kernel is exactly the Hilbert--Schmidt energy of
the assembled residual. -/
theorem trace_soninAllPrimeResidualEnergyKernel
    (a : ℝ) (ha : 0 < a) :
    (∑' i : SoninAllPrimeIndex, soninAllPrimeResidualEnergyKernel a (i, i)) =
      (HilbertSchmidt.hsNormSq (soninAllPrimeResidualKernel a) : ℂ) := by
  rw [soninAllPrimeResidualEnergyKernel,
    HilbertSchmidt.hsTrace_hsComp
      (HilbertSchmidt.isHS_hsAdjoint (soninAllPrimeResidualKernel_isHS a ha))
      (soninAllPrimeResidualKernel_isHS a ha),
    HilbertSchmidt.hsAdjoint_hsAdjoint, HilbertSchmidt.hsInner_self]

/-- In particular the trace of the all-prime Gram kernel is real and nonnegative. -/
theorem trace_soninAllPrimeResidualEnergyKernel_re_nonneg
    (a : ℝ) (ha : 0 < a) :
    0 ≤ (∑' i : SoninAllPrimeIndex,
      soninAllPrimeResidualEnergyKernel a (i, i)).re := by
  rw [trace_soninAllPrimeResidualEnergyKernel a ha, Complex.ofReal_re]
  exact HilbertSchmidt.hsNormSq_nonneg _

/-- The Hilbert space on which the assembled all-prime kernel acts. -/
abbrev SoninAllPrimeL2 := lp (fun _ : SoninAllPrimeIndex => ℂ) 2

/-- The actual bounded all-prime residual operator represented by the source-built block kernel. -/
def soninAllPrimeResidualOperator (a : ℝ) (ha : 0 < a) :
    SoninAllPrimeL2 →L[ℂ] SoninAllPrimeL2 :=
  HilbertSchmidt.toOperator (soninAllPrimeResidualKernel_isHS a ha)

/-- The assembled all-prime residual operator is genuinely Hilbert--Schmidt. -/
theorem soninAllPrimeResidualOperator_isHilbertSchmidt (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsHilbertSchmidt (soninAllPrimeResidualOperator a ha) :=
  HilbertSchmidt.isHilbertSchmidt_toOperator (soninAllPrimeResidualKernel_isHS a ha)

/-- Its operator Hilbert--Schmidt energy agrees exactly with the block-kernel energy. -/
theorem hsNormSq_soninAllPrimeResidualOperator (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.hsNormSq (soninAllPrimeResidualOperator a ha) =
      HilbertSchmidt.hsNormSq (soninAllPrimeResidualKernel a) :=
  HilbertSchmidt.hsNormSq_toOperator (soninAllPrimeResidualKernel_isHS a ha)

/-- The assembled all-prime residual operator is compact. -/
theorem soninAllPrimeResidualOperator_isCompactOperator (a : ℝ) (ha : 0 < a) :
    IsCompactOperator (soninAllPrimeResidualOperator a ha) :=
  (soninAllPrimeResidualOperator_isHilbertSchmidt a ha).isCompactOperator

/-- The positive all-prime inverse-square candidate `K_a† K_a`. -/
def soninAllPrimeResidualEnergyOperator (a : ℝ) (ha : 0 < a) :
    SoninAllPrimeL2 →L[ℂ] SoninAllPrimeL2 :=
  ContinuousLinearMap.adjoint (soninAllPrimeResidualOperator a ha) ∘L
    soninAllPrimeResidualOperator a ha

/-- The positive all-prime energy operator is trace class. -/
theorem soninAllPrimeResidualEnergyOperator_isTraceClass (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.IsTraceClass (soninAllPrimeResidualEnergyOperator a ha) :=
  (soninAllPrimeResidualOperator_isHilbertSchmidt a ha).adjoint_comp_self_isTraceClass

/-- The positive all-prime energy operator is self-adjoint. -/
theorem adjoint_soninAllPrimeResidualEnergyOperator (a : ℝ) (ha : 0 < a) :
    ContinuousLinearMap.adjoint (soninAllPrimeResidualEnergyOperator a ha) =
      soninAllPrimeResidualEnergyOperator a ha := by
  rw [soninAllPrimeResidualEnergyOperator, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

/-- The all-prime energy operator has a nonnegative quadratic form. -/
theorem soninAllPrimeResidualEnergyOperator_re_inner_nonneg
    (a : ℝ) (ha : 0 < a) (x : SoninAllPrimeL2) :
    0 ≤ Complex.re
      (inner ℂ x (soninAllPrimeResidualEnergyOperator a ha x)) := by
  change 0 ≤ Complex.re
    (inner ℂ x
      (ContinuousLinearMap.adjoint (soninAllPrimeResidualOperator a ha)
        (soninAllPrimeResidualOperator a ha x)))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (E := SoninAllPrimeL2)

end RHTower
