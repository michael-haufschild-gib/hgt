import GaloisForLFunctions.RHTower.CCMRationalFiniteBruhatReal

/-!
# Common denominators on compact subsets of the rational finite adeles

Every finite adele has a nonzero integer denominator. The corresponding denominator stages are
open, so compactness gives one common denominator. Diagonal rationals in a compact set therefore
lie in one fractional integer lattice.

No enumeration of rational primes, numerical computation, Poisson formula, positivity, zero
spectrum, or Riemann-hypothesis premise occurs.
-/

noncomputable section

open scoped RestrictedProduct algebraMap

namespace GaloisForLFunctions
namespace RHTower

open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

/-- Every rational finite adele has a nonzero global integer denominator. -/
theorem ccmRationalFiniteAdele_exists_integerDenominator
    (x : CCMRationalFiniteAdele) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ v : HeightOneSpectrum ℤ,
      (algebraMap ℤ CCMRationalFiniteAdele d * x) v ∈
        v.adicCompletionIntegers ℚ := by
  classical
  have hbad :
      {v : HeightOneSpectrum ℤ |
        x v ∉ v.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp x.2
  let E : Finset (HeightOneSpectrum ℤ) := hbad.toFinset
  choose b hb hxb using fun v : HeightOneSpectrum ℤ =>
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (x v)
  let d : ℤ := ∏ v ∈ E, b v
  have hd : d ≠ 0 := by
    dsimp [d]
    exact Finset.prod_ne_zero_iff.mpr fun v hv =>
      nonZeroDivisors.ne_zero (hb v)
  refine ⟨d, hd, fun v => ?_⟩
  change algebraMap ℤ (v.adicCompletion ℚ) d * x v ∈
    v.adicCompletionIntegers ℚ
  by_cases hv : v ∈ E
  · let r : ℤ := ∏ w ∈ E.erase v, b w
    have hdr : d = b v * r := by
      dsimp [d, r]
      symm
      exact Finset.mul_prod_erase E b hv
    have hr :
        algebraMap ℤ (v.adicCompletion ℚ) r ∈
          v.adicCompletionIntegers ℚ :=
      coe_mem_adicCompletionIntegers (K := ℚ) v r
    have hxbv :
        algebraMap ℤ (v.adicCompletion ℚ) (b v) * x v ∈
          v.adicCompletionIntegers ℚ := by
      simpa [mul_comm] using hxb v
    rw [hdr, map_mul, mul_right_comm]
    exact mul_mem hxbv hr
  · have hv' :
        v ∉ {w : HeightOneSpectrum ℤ |
          x w ∉ w.adicCompletionIntegers ℚ} := by
      simpa [E] using hv
    have hxv : x v ∈ v.adicCompletionIntegers ℚ := by
      simpa using hv'
    exact mul_mem (coe_mem_adicCompletionIntegers (K := ℚ) v d) hxv

/-- Finite adeles whose denominators divide the nonzero integer parameter. -/
def ccmRationalFiniteAdeleIntegerDenominatorSet (d : ℤ) :
    Set CCMRationalFiniteAdele :=
  {x | ∀ v : HeightOneSpectrum ℤ,
    (algebraMap ℤ CCMRationalFiniteAdele d * x) v ∈
      v.adicCompletionIntegers ℚ}

/-- A fixed integer-denominator stage is open in the restricted-product topology. -/
theorem ccmRationalFiniteAdeleIntegerDenominatorSet_isOpen (d : ℤ) :
    IsOpen (ccmRationalFiniteAdeleIntegerDenominatorSet d) := by
  change IsOpen
    ((fun x : CCMRationalFiniteAdele =>
      algebraMap ℤ CCMRationalFiniteAdele d * x) ⁻¹'
        {y | ∀ v : HeightOneSpectrum ℤ,
          y v ∈ v.adicCompletionIntegers ℚ})
  have hOpen : IsOpen
      {y : CCMRationalFiniteAdele |
        ∀ v : HeightOneSpectrum ℤ,
          y v ∈ v.adicCompletionIntegers ℚ} :=
    RestrictedProduct.isOpen_forall_mem
      (fun v : HeightOneSpectrum ℤ =>
        Valued.isOpen_valuationSubring (v.adicCompletion ℚ))
  exact hOpen.preimage (continuous_const_mul _)

/-- Multiplying a valid denominator by another integer preserves denominator control. -/
theorem ccmRationalFiniteAdeleIntegerDenominatorSet_mul
    {d r : ℤ} {x : CCMRationalFiniteAdele}
    (hx : x ∈ ccmRationalFiniteAdeleIntegerDenominatorSet d) :
    x ∈ ccmRationalFiniteAdeleIntegerDenominatorSet (r * d) := by
  intro v
  change algebraMap ℤ (v.adicCompletion ℚ) (r * d) * x v ∈
    v.adicCompletionIntegers ℚ
  rw [map_mul, mul_assoc]
  exact mul_mem
    (coe_mem_adicCompletionIntegers (K := ℚ) v r)
    (hx v)

/-- A compact subset of the finite adeles has one common nonzero integer denominator. -/
theorem ccmRationalFiniteAdele_isCompact_exists_commonIntegerDenominator
    {K : Set CCMRationalFiniteAdele} (hK : IsCompact K) :
    ∃ d : ℤ, d ≠ 0 ∧
      K ⊆ ccmRationalFiniteAdeleIntegerDenominatorSet d := by
  classical
  let D := {d : ℤ // d ≠ 0}
  let U : D → Set CCMRationalFiniteAdele :=
    fun d => ccmRationalFiniteAdeleIntegerDenominatorSet d.1
  have hcover : K ⊆ ⋃ d, U d := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ :=
      ccmRationalFiniteAdele_exists_integerDenominator x
    exact Set.mem_iUnion.mpr ⟨⟨d, hd⟩, hdx⟩
  obtain ⟨t, ht⟩ :=
    hK.elim_finite_subcover U
      (fun d => ccmRationalFiniteAdeleIntegerDenominatorSet_isOpen d.1)
      hcover
  let d : ℤ := ∏ e ∈ t, e.1
  have hd : d ≠ 0 := by
    dsimp [d]
    exact Finset.prod_ne_zero_iff.mpr fun e he => e.2
  refine ⟨d, hd, fun x hx => ?_⟩
  have hxu := ht hx
  rw [Set.mem_iUnion] at hxu
  obtain ⟨e, hxu⟩ := hxu
  rw [Set.mem_iUnion] at hxu
  obtain ⟨he, hxe⟩ := hxu
  let r : ℤ := ∏ z ∈ t.erase e, z.1
  have hdr : d = r * e.1 := by
    dsimp [d, r]
    exact (Finset.prod_erase_mul t (fun z : D => z.1) he).symm
  rw [hdr]
  exact ccmRationalFiniteAdeleIntegerDenominatorSet_mul hxe

/--
Diagonal rationals in a compact finite-adele set lie in one fractional integer lattice.
-/
theorem ccmRationalFiniteAdele_isCompact_rationalDiagonalDenominator
    {K : Set CCMRationalFiniteAdele} (hK : IsCompact K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ q : ℚ,
      algebraMap ℚ CCMRationalFiniteAdele q ∈ K →
        algebraMap ℤ ℚ d * q ∈ (algebraMap ℤ ℚ).range := by
  obtain ⟨d, hd, hKd⟩ :=
    ccmRationalFiniteAdele_isCompact_exists_commonIntegerDenominator hK
  refine ⟨d, hd, fun q hq => ?_⟩
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ
  intro v
  have hv := hKd hq v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
  change Valued.v
      (algebraMap ℤ (v.adicCompletion ℚ) d *
        algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 at hv
  rw [IsScalarTower.algebraMap_apply ℤ ℚ (v.adicCompletion ℚ),
    ← map_mul,
    HeightOneSpectrum.algebraMap_adicCompletion ℤ ℚ v,
    Function.comp_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  exact hv

/--
The nonzero diagonal values of one rational finite Bruhat function have a common integer
denominator.
-/
theorem ccmRationalFiniteBruhat_exists_integerDenominator
    (φ : CCMRationalFiniteBruhatSchwartz) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ q : ℚ,
      φ.1 (algebraMap ℚ CCMRationalFiniteAdele q) ≠ 0 →
        algebraMap ℤ ℚ d * q ∈ (algebraMap ℤ ℚ).range := by
  obtain ⟨d, hd, hdiag⟩ :=
    ccmRationalFiniteAdele_isCompact_rationalDiagonalDenominator φ.2
  refine ⟨d, hd, fun q hq => hdiag q ?_⟩
  exact subset_tsupport (f := (φ.1 : CCMRationalFiniteAdele → ℂ)) hq

end RHTower
end GaloisForLFunctions
