import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveOperatorHasTheAdjunctionEigenbasis
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveHorizonDefectHasTheClassEnergy

/-!
# The actual horizon defect is the arithmetic adjunction operator

Finite real class vectors belong to the original logarithmic operator domain.
The literal prime matrix computes their Hilbert quadratic form, and the affine
class-mass law identifies its negative with the actual matched horizon limit.
-/

noncomputable section

open Filter Topology Finset
open scoped Classical InnerProductSpace LinearPMap

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open HTGeometry ArithmeticIntersectionTheory ArithmeticEffectivityTheory ArithmeticElectrostatics

/-- A finite real class vector in the complete supported-integer Hilbert space. -/
def sieveClassVector {ι : Type*} [Fintype ι] {Q : Finset Nat.Primes}
    (d : ι → SieveClass Q) (b : ι → ℝ) : SieveClassL2 Q :=
  ∑ i, (b i : ℂ) • lp.single 2 (d i) (1 : ℂ)

theorem sieveClassVector_apply {ι : Type*} [Fintype ι] {Q : Finset Nat.Primes}
    (d : ι → SieveClass Q) (b : ι → ℝ) (m : SieveClass Q) :
    sieveClassVector d b m = ∑ i, (b i : ℂ) * if m = d i then 1 else 0 := by
  simp only [sieveClassVector, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]

theorem sieveClassVector_at {ι : Type*} [Fintype ι] {Q : Finset Nat.Primes}
    {d : ι → SieveClass Q} (hd : Function.Injective d) (b : ι → ℝ) (i : ι) :
    sieveClassVector d b (d i) = (b i : ℂ) := by
  rw [sieveClassVector_apply]
  have heq (j : ι) : d i = d j ↔ j = i :=
    ⟨fun h => (hd h).symm, fun h => by rw [h]⟩
  simp only [heq, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]

theorem sieveClassSingle_mem_domain (Q : Finset Nat.Primes) (m : SieveClass Q) :
    lp.single 2 m (1 : ℂ) ∈ (sieveAdjunctionOperator Q).domain := by
  have h : (lp.single 2 m (1 : ℂ) : SieveClassL2 Q) ∈
      _root_.RHTower.maximalRealDiagonalDomain (fun n : SieveClass Q => Real.log (n : ℕ)) := by
    simpa only [HilbertSchmidt.lpBasis_apply] using
      _root_.RHTower.lpBasis_mem_maximalRealDiagonalDomain
        (fun n : SieveClass Q => Real.log (n : ℕ)) m
  exact (sieveAdjunctionOperator_domain Q (lp.single 2 m (1 : ℂ) : SieveClassL2 Q)).mpr h

theorem sieveClassVector_mem_domain {ι : Type*} [Fintype ι] {Q : Finset Nat.Primes}
    (d : ι → SieveClass Q) (b : ι → ℝ) :
    sieveClassVector d b ∈ (sieveAdjunctionOperator Q).domain :=
  (sieveAdjunctionOperator Q).domain.sum_mem fun i _ =>
    (sieveAdjunctionOperator Q).domain.smul_mem _ (sieveClassSingle_mem_domain Q (d i))

theorem sievePrimeOperator_classVector {ι : Type*} [Fintype ι] {Q : Finset Nat.Primes}
    (d : ι → SieveClass Q) (b : ι → ℝ) (m : SieveClass Q) :
    sievePrimeOperator Q (sieveClassVector d b) m =
      ∑ i, (b i : ℂ) * (weilPrimeKernel (m : ℕ) (d i : ℕ) : ℂ) := by
  simp only [sieveClassVector, map_sum, map_smul, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, sievePrimeOperator_single]

/-- The actual Hilbert quadratic form has precisely the original class matrix. -/
theorem inner_sieveClassVector_adjunction {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → SieveClass Q}
    (hd : Function.Injective d) (b : ι → ℝ) :
    inner ℂ (sieveClassVector d b)
      (sieveAdjunctionOperator Q ⟨sieveClassVector d b, sieveClassVector_mem_domain d b⟩) =
      (((∑ i, (sieveEuler Q + Real.log (d i : ℕ)) * b i ^ 2) -
        ∑ i, ∑ j, b i * b j * weilPrimeKernel (d i : ℕ) (d j : ℕ) : ℝ) : ℂ) := by
  change inner ℂ (∑ i, (b i : ℂ) • lp.single 2 (d i) (1 : ℂ))
    (sieveAdjunctionOperator Q ⟨sieveClassVector d b, sieveClassVector_mem_domain d b⟩) = _
  rw [sum_inner]
  simp only [inner_smul_left, Complex.conj_ofReal, lp.inner_single_left,
    RCLike.inner_apply, map_one, mul_one, sieveAdjunctionOperator_apply]
  change (∑ i, (b i : ℂ) *
    ((((Real.log (d i : ℕ) + sieveEuler Q : ℝ) : ℂ) * sieveClassVector d b (d i)) -
      sievePrimeOperator Q (sieveClassVector d b) (d i))) = _
  simp_rw [sieveClassVector_at hd, sievePrimeOperator_classVector]
  calc
    _ = ∑ i, (((sieveEuler Q + Real.log (d i : ℕ)) * b i ^ 2 -
        ∑ j, b i * b j * weilPrimeKernel (d i : ℕ) (d j : ℕ) : ℝ) : ℂ) := by
      apply sum_congr rfl
      intro i _
      push_cast
      rw [mul_sub, mul_sum]
      congr 1
      · ring
      · exact sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [← Complex.ofReal_sum, sum_sub_distrib]

/-- For every finite real class vector, the actual matched horizon defect
converges to the negative quadratic form of the actual adjunction operator. -/
theorem tendsto_sieveHorizonDefect_adjunction (Q : Finset Nat.Primes)
    (S : Finset (SieveClass Q)) (b : S → ℝ) :
    Tendsto (fun M : ℕ =>
      (primeBilinear M
          (normalizedSieveProfile Q (fun i : S => ((i : SieveClass Q) : ℕ)) b)
          (normalizedSieveProfile Q (fun i : S => ((i : SieveClass Q) : ℕ)) b) -
        Real.log M * ∑ n ∈ Icc 1 M,
          normalizedSieveProfile Q (fun i : S => ((i : SieveClass Q) : ℕ)) b n ^ 2) / Real.log M)
      atTop (𝓝 (-Complex.re (inner ℂ
        (sieveClassVector (fun i : S => (i : SieveClass Q)) b)
        (sieveAdjunctionOperator Q
          ⟨sieveClassVector (fun i : S => (i : SieveClass Q)) b,
            sieveClassVector_mem_domain _ b⟩)))) := by
  have hd : ∀ i : S, SieveSupported Q (((i : SieveClass Q) : ℕ)) := fun i => i.val.property
  have hinj : Function.Injective (fun i : S => ((i : SieveClass Q) : ℕ)) :=
    fun _ _ h => Subtype.ext (Subtype.ext h)
  have h := tendsto_sieveProfile_matched_defect hd hinj b
  rw [inner_sieveClassVector_adjunction Subtype.val_injective, Complex.ofReal_re]
  convert h using 1
  congr 1
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

