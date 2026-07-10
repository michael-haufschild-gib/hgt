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

/-- Parseval identity in the orientation used by Sonin matrix entries. -/
theorem tsum_sq_norm_inner_hilbertBasis
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

/-- The squared matrix entries of all weighted prime-power residuals are summable jointly over
the prime power and both Sonin basis coordinates.  This is the convergence input for both the
diagonal direct-sum assembly and the coupled column assembly. -/
theorem summable_all_prime_residual_matrix_entries (a : ℝ) (ha : 0 < a) :
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
    refine (summable_all_prime_residual_matrix_entries a ha).congr (fun pji => ?_)
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

/-- The factor `K_a T_a^n` used to evaluate a polynomial against the positive energy
`T_a=K_aᴴK_a`.  At `n=0` this is `K_a`; for positive `n` it is the corresponding kernel
composition. -/
def soninAllPrimePolynomialPowerKernel (a : ℝ) (n : ℕ) :
    SoninAllPrimeIndex × SoninAllPrimeIndex → ℂ :=
  if n = 0 then soninAllPrimeResidualKernel a
  else HilbertSchmidt.hsComp (soninAllPrimeResidualKernel a)
    (HilbertSchmidt.hsPow (soninAllPrimeResidualEnergyKernel a) (n - 1))

theorem soninAllPrimePolynomialPowerKernel_isHS
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    HilbertSchmidt.IsHS (soninAllPrimePolynomialPowerKernel a n) := by
  by_cases hn : n = 0
  · simp [soninAllPrimePolynomialPowerKernel, hn, soninAllPrimeResidualKernel_isHS a ha]
  · rw [soninAllPrimePolynomialPowerKernel, if_neg hn]
    exact HilbertSchmidt.isHS_hsComp (soninAllPrimeResidualKernel_isHS a ha)
      (HilbertSchmidt.isHS_hsPow (soninAllPrimeResidualEnergyKernel_isHS a ha) (n - 1))

/-- The source Gram entry between the two factors `K_a T_a^m` and `K_a T_a^n`.
The missing Xi weld is precisely the assertion that, at the canonical cutoff, this entry
depends only on `m+n` and equals the corresponding centered reciprocal moment. -/
def soninAllPrimePolynomialGramEntry (a : ℝ) (m n : ℕ) : ℂ :=
  HilbertSchmidt.hsInner (soninAllPrimePolynomialPowerKernel a m)
    (soninAllPrimePolynomialPowerKernel a n)

theorem soninAllPrimePolynomialGramEntry_conj_symm (a : ℝ) (m n : ℕ) :
    soninAllPrimePolynomialGramEntry a m n =
      (starRingEnd ℂ) (soninAllPrimePolynomialGramEntry a n m) := by
  exact HilbertSchmidt.hsInner_conj_symm _ _

theorem soninAllPrimePolynomialGramEntry_self (a : ℝ) (n : ℕ) :
    soninAllPrimePolynomialGramEntry a n n =
      (HilbertSchmidt.hsNormSq (soninAllPrimePolynomialPowerKernel a n) : ℂ) := by
  exact HilbertSchmidt.hsInner_self _

private theorem hsInner_sum_right {ι κ : Type*} [DecidableEq κ]
    (s : Finset κ) (K : κ → ι × ι → ℂ) (L : ι × ι → ℂ)
    (hK : ∀ r ∈ s, HilbertSchmidt.IsHS (K r)) (hL : HilbertSchmidt.IsHS L) :
    HilbertSchmidt.hsInner L (∑ r ∈ s, K r) =
      ∑ r ∈ s, HilbertSchmidt.hsInner L (K r) := by
  rw [HilbertSchmidt.hsInner_conj_symm,
    HilbertSchmidt.hsInner_sum_left s K L hK hL, map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← HilbertSchmidt.hsInner_conj_symm]

/-- The source-built factor `K_a p(T_a)`.  Its Hilbert--Schmidt energy is the factorized form of
`Tr(T_a p(T_a)^2)` and is defined without an Xi zero divisor. -/
def soninAllPrimePolynomialProbeKernel (a : ℝ) (p : Polynomial ℝ) :
    SoninAllPrimeIndex × SoninAllPrimeIndex → ℂ :=
  ∑ n ∈ p.support,
    ((p.coeff n : ℝ) : ℂ) • soninAllPrimePolynomialPowerKernel a n

theorem soninAllPrimePolynomialProbeKernel_isHS
    (a : ℝ) (ha : 0 < a) (p : Polynomial ℝ) :
    HilbertSchmidt.IsHS (soninAllPrimePolynomialProbeKernel a p) := by
  rw [soninAllPrimePolynomialProbeKernel]
  apply HilbertSchmidt.isHS_sum p.support
  intro n hn
  exact (soninAllPrimePolynomialPowerKernel_isHS a ha n).smul ((p.coeff n : ℝ) : ℂ)

/-- A monomial probe selects exactly one source power.  Thus the diagonal entries of the
source trace-Hankel form are genuine Hilbert--Schmidt energies of `K_a T_a^n`, rather than
formal moment variables. -/
theorem soninAllPrimePolynomialProbeKernel_monomial (a : ℝ) (n : ℕ) :
    soninAllPrimePolynomialProbeKernel a (Polynomial.X ^ n) =
      soninAllPrimePolynomialPowerKernel a n := by
  simp [soninAllPrimePolynomialProbeKernel]

/-- The Sonin all-prime trace-Hankel quadratic functional in factorized form. -/
def soninAllPrimeTraceHankel (a : ℝ) (p : Polynomial ℝ) : ℂ :=
  (HilbertSchmidt.hsNormSq (soninAllPrimePolynomialProbeKernel a p) : ℂ)

/-- The source trace-Hankel value on `X^n` is the actual squared Hilbert--Schmidt norm of
`K_a T_a^n`.  These are the diagonal source moments that must match the centered Xi moments. -/
theorem soninAllPrimeTraceHankel_monomial (a : ℝ) (n : ℕ) :
    soninAllPrimeTraceHankel a (Polynomial.X ^ n) =
      (HilbertSchmidt.hsNormSq (soninAllPrimePolynomialPowerKernel a n) : ℂ) := by
  rw [soninAllPrimeTraceHankel, soninAllPrimePolynomialProbeKernel_monomial]

/-- Exact finite Gram expansion of the source trace-Hankel form.  This exposes every mixed
entry that must be identified with an Xi reciprocal moment; no spectral target is built into
the source operator. -/
theorem soninAllPrimeTraceHankel_eq_gram_sum (a : ℝ) (ha : 0 < a)
    (p : Polynomial ℝ) :
    soninAllPrimeTraceHankel a p =
      ∑ m ∈ p.support, ∑ n ∈ p.support,
        ((p.coeff m : ℝ) : ℂ) * ((p.coeff n : ℝ) : ℂ) *
          soninAllPrimePolynomialGramEntry a m n := by
  let P : ℕ → SoninAllPrimeIndex × SoninAllPrimeIndex → ℂ :=
    fun n => soninAllPrimePolynomialPowerKernel a n
  let c : ℕ → ℂ := fun n => ((p.coeff n : ℝ) : ℂ)
  have hP (n : ℕ) : HilbertSchmidt.IsHS (P n) :=
    soninAllPrimePolynomialPowerKernel_isHS a ha n
  have hcP (n : ℕ) : HilbertSchmidt.IsHS (c n • P n) := (hP n).smul (c n)
  rw [soninAllPrimeTraceHankel, ← HilbertSchmidt.hsInner_self]
  change HilbertSchmidt.hsInner (∑ n ∈ p.support, c n • P n)
      (∑ n ∈ p.support, c n • P n) = _
  rw [HilbertSchmidt.hsInner_sum_left p.support (fun n => c n • P n)
    (∑ n ∈ p.support, c n • P n)
    (fun n _ => hcP n)
    (HilbertSchmidt.isHS_sum p.support (fun n => c n • P n) (fun n _ => hcP n))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [HilbertSchmidt.hsInner_smul_left]
  rw [hsInner_sum_right p.support (fun n => c n • P n) (P m)
    (fun n _ => hcP n) (hP m)]
  simp only [HilbertSchmidt.hsInner_smul_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp [c, P, soninAllPrimePolynomialGramEntry]
  ring

/-- Every source-built Sonin trace-Hankel test is real. -/
theorem soninAllPrimeTraceHankel_im_eq_zero (a : ℝ) (p : Polynomial ℝ) :
    (soninAllPrimeTraceHankel a p).im = 0 := by
  simp [soninAllPrimeTraceHankel]

/-- **Unconditional source positivity.** Every real-polynomial trace-Hankel test of the assembled
positive all-prime Sonin operator is nonnegative. -/
theorem soninAllPrimeTraceHankel_re_nonneg (a : ℝ) (p : Polynomial ℝ) :
    0 ≤ (soninAllPrimeTraceHankel a p).re := by
  rw [soninAllPrimeTraceHankel, Complex.ofReal_re]
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

/-! ### Self-dual unit-cutoff specialization -/

/-- The unit-cutoff all-prime residual operator.  The value `a=1` removes the free scale in the
Fourier normalization where the physical and frequency cutoffs use the same coordinate. -/
def soninCanonicalAllPrimeResidualOperator :
    SoninAllPrimeL2 →L[ℂ] SoninAllPrimeL2 :=
  soninAllPrimeResidualOperator 1 zero_lt_one

/-- The unit-cutoff all-prime residual is unconditionally Hilbert--Schmidt. -/
theorem soninCanonicalAllPrimeResidualOperator_isHilbertSchmidt :
    ContinuousLinearMap.IsHilbertSchmidt soninCanonicalAllPrimeResidualOperator :=
  soninAllPrimeResidualOperator_isHilbertSchmidt 1 zero_lt_one

/-- The unit-cutoff positive energy operator. -/
def soninCanonicalAllPrimeResidualEnergyOperator :
    SoninAllPrimeL2 →L[ℂ] SoninAllPrimeL2 :=
  soninAllPrimeResidualEnergyOperator 1 zero_lt_one

/-- The unit-cutoff positive energy operator is unconditionally trace class. -/
theorem soninCanonicalAllPrimeResidualEnergyOperator_isTraceClass :
    ContinuousLinearMap.IsTraceClass soninCanonicalAllPrimeResidualEnergyOperator :=
  soninAllPrimeResidualEnergyOperator_isTraceClass 1 zero_lt_one

/-- The unit-cutoff positive energy operator is self-adjoint. -/
theorem adjoint_soninCanonicalAllPrimeResidualEnergyOperator :
    ContinuousLinearMap.adjoint soninCanonicalAllPrimeResidualEnergyOperator =
      soninCanonicalAllPrimeResidualEnergyOperator :=
  adjoint_soninAllPrimeResidualEnergyOperator 1 zero_lt_one

/-- The unit-cutoff positive energy operator has nonnegative quadratic form. -/
theorem soninCanonicalAllPrimeResidualEnergyOperator_re_inner_nonneg
    (x : SoninAllPrimeL2) :
    0 ≤ Complex.re
      (inner ℂ x (soninCanonicalAllPrimeResidualEnergyOperator x)) :=
  soninAllPrimeResidualEnergyOperator_re_inner_nonneg 1 zero_lt_one x

/-- The unit-cutoff source trace-Hankel functional. -/
def soninCanonicalAllPrimeTraceHankel (p : Polynomial ℝ) : ℂ :=
  soninAllPrimeTraceHankel 1 p

/-- The unit-cutoff source trace-Hankel functional is unconditionally nonnegative on every real
polynomial test. -/
theorem soninCanonicalAllPrimeTraceHankel_re_nonneg (p : Polynomial ℝ) :
    0 ≤ (soninCanonicalAllPrimeTraceHankel p).re :=
  soninAllPrimeTraceHankel_re_nonneg 1 p

end RHTower
