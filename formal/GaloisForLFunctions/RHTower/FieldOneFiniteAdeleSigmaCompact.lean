import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleL2WeylMultiplier

/-!
# Sigma-compactness of the rational finite adeles

Every finite adele has only finitely many nonintegral coordinates.  At each
such coordinate, the local adic-completion denominator theorem supplies a
nonzero integer clearing that coordinate.  The product of these finitely many
integers clears every coordinate simultaneously.

Consequently

`𝔸_f = ⋃ d : ℤ, d⁻¹ Ẑ`,

where every `d⁻¹ Ẑ` is a continuous image of the compact-open integral
subgroup.  This proves sigma-compactness and, hence, sigma-finiteness of
additive Haar measure.

No strong approximation theorem, enumeration of primes, numerical
calculation, trace, spectral statement, or RH premise is used.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Filter Function IsDedekindDomain MeasureTheory Set
open scoped RestrictedProduct

/-- A single nonzero integer simultaneously clears every nonintegral
coordinate of a rational finite adele. -/
theorem fieldOneFiniteAdele_exists_integral_denominator_coordinates
    (x : FieldOneFiniteAdele) :
    ∃ d : ℤ, d ≠ 0 ∧
      ∀ v : HeightOneSpectrum ℤ,
        x v * algebraMap ℤ (v.adicCompletion ℚ) d ∈
          v.adicCompletionIntegers ℚ := by
  classical
  choose b hb hxb using fun v : HeightOneSpectrum ℤ =>
    IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers
      (K := ℚ) v (x v)
  let bad : Set (HeightOneSpectrum ℤ) :=
    {v | x v ∉ v.adicCompletionIntegers ℚ}
  have hbad : bad.Finite := by
    change
      {v : HeightOneSpectrum ℤ |
        ¬x v ∈ v.adicCompletionIntegers ℚ}.Finite
    rw [← Filter.eventually_cofinite]
    exact x.2
  let s : Finset (HeightOneSpectrum ℤ) := hbad.toFinset
  let d : ℤ := ∏ v ∈ s, b v
  refine ⟨d, ?_, ?_⟩
  · dsimp only [d]
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact nonZeroDivisors.ne_zero (hb v)
  · intro v
    by_cases hv : v ∈ s
    · have hfactor :
          d = b v * ∏ w ∈ s.erase v, b w := by
        dsimp only [d]
        rw [Finset.mul_prod_erase _ _ hv]
      rw [hfactor, map_mul, ← mul_assoc]
      exact mul_mem (hxb v)
        (IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers
          v (∏ w ∈ s.erase v, b w))
    · have hxv : x v ∈ v.adicCompletionIntegers ℚ := by
        by_contra hnot
        apply hv
        change v ∈ hbad.toFinset
        simpa only [Set.Finite.mem_toFinset, bad]
      exact mul_mem hxv
        (IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers
          v d)

/-- Global restricted-product form of simultaneous denominator clearing. -/
theorem fieldOneFiniteAdele_exists_integral_denominator
    (x : FieldOneFiniteAdele) :
    ∃ d : ℤ, d ≠ 0 ∧
      x * algebraMap ℤ FieldOneFiniteAdele d ∈
        fieldOneFiniteAdeleIntegralAddSubgroup := by
  rcases
      fieldOneFiniteAdele_exists_integral_denominator_coordinates x with
    ⟨d, hd, hdx⟩
  refine ⟨d, hd, ?_⟩
  intro v
  change
    x v * algebraMap ℤ (v.adicCompletion ℚ) d ∈
      v.adicCompletionIntegers ℚ
  exact hdx v

/-- Compact denominator dilate `d⁻¹ Ẑ`.  Indexing by all integers is harmless;
the zero-index member is compact too, while nonzero indices cover `𝔸_f`. -/
def fieldOneFiniteAdeleDenominatorCompact (d : ℤ) :
    Set FieldOneFiniteAdele :=
  (fun z =>
    z * algebraMap ℚ FieldOneFiniteAdele ((d : ℚ)⁻¹)) ''
      (fieldOneFiniteAdeleIntegralAddSubgroup :
        Set FieldOneFiniteAdele)

theorem fieldOneFiniteAdeleDenominatorCompact_isCompact (d : ℤ) :
    IsCompact (fieldOneFiniteAdeleDenominatorCompact d) := by
  exact fieldOneFiniteAdeleIntegralAddSubgroup_isCompact.image
    (continuous_id.mul continuous_const)

/-- Every finite adele belongs to one compact denominator dilate. -/
theorem fieldOneFiniteAdele_mem_denominatorCompact
    (x : FieldOneFiniteAdele) :
    ∃ d : ℤ, x ∈ fieldOneFiniteAdeleDenominatorCompact d := by
  rcases fieldOneFiniteAdele_exists_integral_denominator x with
    ⟨d, hd, hxd⟩
  refine
    ⟨d,
      ⟨x * algebraMap ℤ FieldOneFiniteAdele d, hxd, ?_⟩⟩
  change
    (x * algebraMap ℤ FieldOneFiniteAdele d) *
        algebraMap ℚ FieldOneFiniteAdele ((d : ℚ)⁻¹) =
      x
  rw [mul_assoc]
  change
    x *
        (algebraMap ℚ FieldOneFiniteAdele (d : ℚ) *
          algebraMap ℚ FieldOneFiniteAdele ((d : ℚ)⁻¹)) =
      x
  rw [← map_mul, mul_inv_cancel₀]
  · simp
  · exact_mod_cast hd

/-- Rational finite adeles are sigma-compact, via countably many compact
denominator dilates of integral finite adeles. -/
noncomputable instance fieldOneFiniteAdeleSigmaCompactSpace :
    SigmaCompactSpace FieldOneFiniteAdele := by
  let S : Set (Set FieldOneFiniteAdele) :=
    Set.range fieldOneFiniteAdeleDenominatorCompact
  apply SigmaCompactSpace.of_countable S (Set.countable_range _)
  · rintro K ⟨d, rfl⟩
    exact fieldOneFiniteAdeleDenominatorCompact_isCompact d
  · apply Set.eq_univ_of_forall
    intro x
    rcases fieldOneFiniteAdele_mem_denominatorCompact x with
      ⟨d, hxd⟩
    exact Set.mem_sUnion_of_mem hxd ⟨d, rfl⟩

/-- Additive Haar measure on the rational finite adeles is sigma-finite. -/
noncomputable instance fieldOneFiniteAdeleAddHaarSigmaFinite :
    SigmaFinite fieldOneFiniteAdeleAddHaar :=
  inferInstance

end

end GaloisForLFunctions.RHTower
