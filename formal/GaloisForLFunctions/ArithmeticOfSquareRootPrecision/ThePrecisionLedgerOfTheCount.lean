import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheGaugeStabilizerOfTheCount
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheIntegralityExponentIsTheZeroWidth

/-!
# The precision ledger of the count

The programme's equivalences in one place.

* **RH in eight currencies of precision** (`riemannHypothesis_precision_tfae`): RH; the count for
  `Λ`; its upper half; its lower half; precision exponent `½`; the Siegel half of integrality at
  square-root scale; the Liouville half at square-root scale; the count for `Λ` with the Euler
  factor at `2` deleted.
* **One exponent, three readings** (`zero_width_three_readings`): the zero width `Θ` is the
  precision exponent of `Λ`, the Siegel exponent and the Liouville exponent of integrality.
* **Strip in three readings** (`zeroReSup_lt_one_tfae`): `Θ < 1` iff `ψ(x) − x = O(x^θ)` for some
  `θ < 1` iff the Siegel half holds at some `θ < 1` iff the Liouville half does.
-/

noncomputable section

open Filter Asymptotics Real RHTower

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- **RH in eight currencies of precision.** -/
theorem riemannHypothesis_precision_tfae :
    List.TFAE [RiemannHypothesis,
      Count vonMangoldtWeight,
      UpperCount vonMangoldtWeight,
      LowerCount vonMangoldtWeight,
      precisionExponent vonMangoldtWeight = 1 / 2,
      SiegelHalf sqrtScale,
      LiouvilleHalf sqrtScale,
      Count (vonMangoldtWeight + (-1 : ℝ) • towerWeight 2)] := by
  tfae_have 1 ↔ 2 := count_vonMangoldt_iff.symm
  tfae_have 1 ↔ 3 := upperCount_vonMangoldt_iff.symm
  tfae_have 1 ↔ 4 := lowerCount_vonMangoldt_iff.symm
  tfae_have 1 ↔ 5 := riemannHypothesis_iff_precisionExponent
  tfae_have 1 ↔ 6 := riemannHypothesis_iff_siegelHalf_sqrtScale
  tfae_have 1 ↔ 7 := riemannHypothesis_iff_liouvilleHalf_sqrtScale
  tfae_have 1 ↔ 8 := (count_vonMangoldt_add_smul_towerWeight_iff Nat.prime_two (-1)).symm
  tfae_finish

/-- **One exponent, three readings**: the zero width is the precision exponent of `Λ`, the Siegel
exponent and the Liouville exponent of integrality. -/
theorem zero_width_three_readings :
    precisionExponent vonMangoldtWeight = zeroReSup ∧
      sInf {θ : ℝ | SiegelHalf fun x => x ^ θ} = zeroReSup ∧
      sInf {θ : ℝ | LiouvilleHalf fun x => x ^ θ} = zeroReSup :=
  ⟨precisionExponent_vonMangoldt, siegelExponent_eq_zeroReSup, liouvilleExponent_eq_zeroReSup⟩

/-- **A zero-free strip in three readings.** -/
theorem zeroReSup_lt_one_tfae :
    List.TFAE [zeroReSup < 1,
      ∃ θ : ℝ, θ < 1 ∧
        (fun x => partialSum vonMangoldtWeight x - x) =O[atTop] fun x => x ^ θ,
      ∃ θ : ℝ, θ < 1 ∧ SiegelHalf fun x => x ^ θ,
      ∃ θ : ℝ, θ < 1 ∧ LiouvilleHalf fun x => x ^ θ] := by
  tfae_have 1 → 2 := fun h => by
    obtain ⟨C, -, hC⟩ := exists_abs_chebyshevPsi_sub_le_rpow (b := (zeroReSup + 1) / 2)
      (by linarith)
    refine ⟨(zeroReSup + 1) / 2, by linarith, IsBigO.of_bound C ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact hC x hx
  tfae_have 2 → 1 := fun ⟨θ, hθ, h⟩ => by
    have := precisionExponent_le h
    rw [precisionExponent_vonMangoldt] at this
    linarith
  tfae_have 1 ↔ 3 := zeroReSup_lt_one_iff_siegelHalf
  tfae_have 1 ↔ 4 := zeroReSup_lt_one_iff_liouvilleHalf
  tfae_finish

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
