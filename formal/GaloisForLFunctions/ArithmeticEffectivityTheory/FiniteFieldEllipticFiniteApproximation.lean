import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticAdeleHaar
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Finite-place approximation on the actual elliptic curve

Density of the fraction field and the Dedekind localization approximation
theorem approximate every completed integer to any prescribed integral modulus.
Chinese remainders then combine the finitely many nontrivial congruences.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

open IsDedekindDomain
open scoped WithZero WithZeroMulInt

noncomputable section

local instance (v : FinitePlace) : IsTopologicalDivisionRing (v.adicCompletion K) :=
  Valued.isTopologicalDivisionRing (Γ₀ := ℤᵐ⁰)

local instance (v : FinitePlace) : ContinuousSub (v.adicCompletion K) where
  continuous_sub := by
    exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v).comp
      (((HeightOneSpectrum.adicCompletion.continuous_toCompletion K v).comp continuous_fst).sub
        ((HeightOneSpectrum.adicCompletion.continuous_toCompletion K v).comp continuous_snd))

private theorem finiteCompletion_value_map (v : FinitePlace) (z : K) :
    Valued.v (algebraMap K (v.adicCompletion K) z) = v.valuation K z :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) z

private theorem finiteCompletion_value_integer (v : FinitePlace) (a : RingOfIntegers) :
    Valued.v (algebraMap RingOfIntegers (v.adicCompletion K) a) = v.intValuation a := by
  calc
    _ = v.valuation K (algebraMap RingOfIntegers K a) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation (v := v) a
    _ = v.intValuation a := HeightOneSpectrum.valuation_of_algebraMap v a

theorem finiteCompletion_approx_integer (v : FinitePlace)
    (y : v.adicCompletion K) (hy : y ∈ v.adicCompletionIntegers K)
    (d : RingOfIntegers) (hd : d ≠ 0) :
    ∃ c : RingOfIntegers,
      (y - algebraMap RingOfIntegers (v.adicCompletion K) c) /
        algebraMap RingOfIntegers (v.adicCompletion K) d ∈ v.adicCompletionIntegers K := by
  let D := algebraMap RingOfIntegers (v.adicCompletion K) d
  have hdK : algebraMap RingOfIntegers K d ≠ 0 :=
    (IsFractionRing.injective RingOfIntegers K).ne hd
  have hD : D ≠ 0 := by
    change algebraMap RingOfIntegers (v.adicCompletion K) d ≠ 0
    rw [IsScalarTower.algebraMap_apply RingOfIntegers K (v.adicCompletion K)]
    exact (algebraMap K (v.adicCompletion K)).injective.ne hdK
  have hopen : IsOpen {z : v.adicCompletion K | (y - z) / D ∈ v.adicCompletionIntegers K} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
      ((continuous_const.sub continuous_id).mul continuous_const)
  obtain ⟨z, hz⟩ := (HeightOneSpectrum.denseRange_algebraMap K v).mem_nhds
    (hopen.mem_nhds (show (y - y) / D ∈ v.adicCompletionIntegers K by
      simpa only [sub_self, zero_div] using (zero_mem (v.adicCompletionIntegers K))))
  change (y - algebraMap K (v.adicCompletion K) z) / D ∈ v.adicCompletionIntegers K at hz
  have hDint : D ∈ v.adicCompletionIntegers K :=
    HeightOneSpectrum.coe_mem_adicCompletionIntegers v d
  have hdiff : y - algebraMap K (v.adicCompletion K) z ∈ v.adicCompletionIntegers K := by
    have h := mul_mem hz hDint
    rwa [div_mul_cancel₀ _ hD] at h
  have hzint : algebraMap K (v.adicCompletion K) z ∈ v.adicCompletionIntegers K := by
    have h := sub_mem hy hdiff
    rwa [sub_sub_cancel] at h
  have hzval : v.valuation K z ≤ 1 := by
    change Valued.v (algebraMap K (v.adicCompletion K) z) ≤ 1 at hzint
    rwa [finiteCompletion_value_map] at hzint
  have hdv : v.valuation K (algebraMap RingOfIntegers K d) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hdK
  obtain ⟨c, hc⟩ := v.exists_valuation_sub_lt_of_integer hzval (Units.mk0 _ hdv)
  have hcd : Valued.v
      (algebraMap K (v.adicCompletion K) z - algebraMap RingOfIntegers (v.adicCompletion K) c) ≤
        Valued.v D := by
    rw [IsScalarTower.algebraMap_apply RingOfIntegers K (v.adicCompletion K),
      ← map_sub, finiteCompletion_value_map,
      Valuation.map_sub_swap]
    change v.valuation K (algebraMap RingOfIntegers K c - z) ≤
      Valued.v (algebraMap RingOfIntegers (v.adicCompletion K) d)
    rw [finiteCompletion_value_integer]
    exact hc.le.trans_eq (HeightOneSpectrum.valuation_of_algebraMap v d)
  have hzc :
      (algebraMap K (v.adicCompletion K) z - algebraMap RingOfIntegers (v.adicCompletion K) c) / D ∈
        v.adicCompletionIntegers K := by
    change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (_ / D) ≤ 1
    rw [map_div₀]
    exact (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hD))).mpr hcd
  refine ⟨c, ?_⟩
  have h := add_mem hz hzc
  convert h using 1 <;> ring

/-- Every finite adele differs from an actual rational function by an integral adele. -/
theorem finiteAdele_exists_integral_difference (a : FiniteAdeles) :
    ∃ z : K, a - finiteAdeleEmbedding z ∈ integralFiniteAdeles := by
  classical
  obtain ⟨d, hd, had⟩ := finiteAdele_exists_integral_denominator a
  choose c hc using fun v : FinitePlace =>
    finiteCompletion_approx_integer v
      (a v * algebraMap RingOfIntegers (v.adicCompletion K) d) (had v) d hd
  let S : Set FinitePlace := {v | d ∈ v.asIdeal}
  have hS : S.Finite := by
    simpa only [S, Ideal.dvd_span_singleton] using
      (Ideal.finite_factors
        (show (Ideal.span {d} : Ideal RingOfIntegers) ≠ 0 from
          Ideal.span_singleton_eq_bot.not.mpr hd))
  letI : Fintype S := hS.fintype
  let I : S → Ideal RingOfIntegers :=
    fun v => v.1.asIdeal ^ multiplicity v.1.asIdeal (Ideal.span {d})
  have hI : Pairwise (fun v w : S => IsCoprime (I v) (I w)) := by
    intro v w hvw
    exact HeightOneSpectrum.isCoprime_pow_of_ne v.1 w.1
      (fun h => hvw (Subtype.ext h)) _ _
  obtain ⟨b, hb⟩ := Ideal.exists_forall_sub_mem_ideal hI (fun v : S => c v.1)
  have hbval (v : FinitePlace) : v.intValuation (b - c v) ≤ v.intValuation d := by
    by_cases hv : v ∈ S
    · rw [v.intValuation_eq_exp_neg_multiplicity hd,
        v.intValuation_le_pow_iff_mem]
      exact hb ⟨v, hv⟩
    · rw [HeightOneSpectrum.intValuation_eq_one_iff.mpr hv]
      exact v.intValuation_le_one _
  refine ⟨algebraMap RingOfIntegers K b / algebraMap RingOfIntegers K d, ?_⟩
  intro v
  have hdK : algebraMap RingOfIntegers K d ≠ 0 :=
    (IsFractionRing.injective RingOfIntegers K).ne hd
  have hD : algebraMap RingOfIntegers (v.adicCompletion K) d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply RingOfIntegers K (v.adicCompletion K)]
    exact (algebraMap K (v.adicCompletion K)).injective.ne hdK
  have hbc :
      (algebraMap RingOfIntegers (v.adicCompletion K) b -
        algebraMap RingOfIntegers (v.adicCompletion K) (c v)) /
          algebraMap RingOfIntegers (v.adicCompletion K) d ∈ v.adicCompletionIntegers K := by
    change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (_ / _) ≤ 1
    rw [map_div₀]
    apply (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hD))).mpr
    rw [← map_sub, finiteCompletion_value_integer, finiteCompletion_value_integer]
    exact hbval v
  have h := sub_mem (hc v) hbc
  change a v - algebraMap K (v.adicCompletion K)
    (algebraMap RingOfIntegers K b / algebraMap RingOfIntegers K d) ∈ _
  rw [map_div₀, ← IsScalarTower.algebraMap_apply RingOfIntegers K (v.adicCompletion K),
    ← IsScalarTower.algebraMap_apply RingOfIntegers K (v.adicCompletion K)]
  have he : a v - algebraMap RingOfIntegers (v.adicCompletion K) b /
      algebraMap RingOfIntegers (v.adicCompletion K) d =
      (a v * algebraMap RingOfIntegers (v.adicCompletion K) d -
        algebraMap RingOfIntegers (v.adicCompletion K) (c v)) /
          algebraMap RingOfIntegers (v.adicCompletion K) d -
      (algebraMap RingOfIntegers (v.adicCompletion K) b -
        algebraMap RingOfIntegers (v.adicCompletion K) (c v)) /
          algebraMap RingOfIntegers (v.adicCompletion K) d := by
    field_simp [hD]
    ring
  rw [he]
  exact h

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
