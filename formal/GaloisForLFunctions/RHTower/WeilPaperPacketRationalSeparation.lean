import GaloisForLFunctions.RHTower.WeilPaperPacketPrimitiveSampling

/-!
# Rational correlation remains free on positive integer-null fibres

The paper's prime-subset masks give positive smooth mixtures with equal mass and
zero integer defect. Their difference at `log 2 - log 3` can be any complex
number. Thus integer defects and total mass do not determine rational samples.
The constructive survivor is an exact family of positive null pairs, retaining
the full coprime energy identity from `WeilPaperPacketCoprimeFibre`.
-/

open Complex
noncomputable section
namespace RHTower.WeilWorkPBAP

open WeilOneSided

private def twoThreeRatio : PaperPacketCoprimePair 3 :=
  ⟨(⟨2, by decide⟩, ⟨3, by decide⟩), by decide⟩

private def unitRatio : PaperPacketCoprimePair 3 :=
  ⟨(⟨1, by decide⟩, ⟨1, by decide⟩), by decide⟩

/-- Coefficients producing a prescribed complex difference at the reduced ratio `2/3`. -/
def paperPacketTwoThreeCoeffs (z : ℂ) (m : PacketIndex 3) : ℂ :=
  if (m : ℕ) = 2 then z / (packetMass 3 4 : ℂ) else 1

/-- The actual repaired mixtures have an arbitrary prescribed complex sample difference. -/
theorem paperPacket_prime_null_two_three_sample (z : ℂ) :
    mixtureSample (paperPacketEvenPrimeNullMixture 3 (paperPacketTwoThreeCoeffs z))
        (Real.log 2 - Real.log 3) -
      mixtureSample (paperPacketOddPrimeNullMixture 3 (paperPacketTwoThreeCoeffs z))
        (Real.log 2 - Real.log 3) = z := by
  have hm : (packetMass 3 4 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (packetMass_pos 3 4).ne'
  calc
    _ = (packetMass 3 4 : ℂ) * (z / (packetMass 3 4 : ℂ)) := by
      simpa [twoThreeRatio, paperPacketNonunitCoeff, paperPacketTwoThreeCoeffs] using
        paperPacket_prime_null_primitive_sample 0 (paperPacketTwoThreeCoeffs z) twoThreeRatio
    _ = z := by field_simp [hm]

/-- The same construction preserves mass as well as every integer constraint. -/
theorem paperPacket_prime_null_two_three_mass (z : ℂ) :
    mixtureSample (paperPacketEvenPrimeNullMixture 3 (paperPacketTwoThreeCoeffs z)) 0 =
      mixtureSample (paperPacketOddPrimeNullMixture 3 (paperPacketTwoThreeCoeffs z)) 0 := by
  apply sub_eq_zero.mp
  simpa [unitRatio, paperPacketNonunitCoeff] using
    paperPacket_prime_null_primitive_sample 2 (paperPacketTwoThreeCoeffs z) unitRatio

/-- Positive integer-null mixtures with equal mass realize every complex sample difference. -/
theorem exists_positive_null_equal_mass_pair_rational_difference (z : ℂ) :
    ∃ a b : WeilTestFn →₀ ℝ,
      (∀ f, 0 ≤ a f) ∧ (∀ f, 0 ≤ b f) ∧
      defect a = 0 ∧ defect b = 0 ∧
      mixtureSample a 0 = mixtureSample b 0 ∧
      mixtureSample a (Real.log 2 - Real.log 3) -
        mixtureSample b (Real.log 2 - Real.log 3) = z ∧
      energy a - energy b =
        packetArchPairing 4 (paperPacketCoprimeCovariance (paperPacketTwoThreeCoeffs z)) :=
  ⟨paperPacketEvenPrimeNullMixture 3 (paperPacketTwoThreeCoeffs z),
    paperPacketOddPrimeNullMixture 3 (paperPacketTwoThreeCoeffs z),
    paperPacketEvenPrimeNullMixture_nonneg 3 _, paperPacketOddPrimeNullMixture_nonneg 3 _,
    defect_paperPacketEvenPrimeNullMixture 3 _, defect_paperPacketOddPrimeNullMixture 3 _,
    paperPacket_prime_null_two_three_mass z, paperPacket_prime_null_two_three_sample z,
    energy_paperPacket_prime_null_parity 3 _⟩

/-- No rule using integer defects and total mass recovers this rational sample,
even on the cone of nonnegative finite mixtures. -/
theorem no_rational_sample_factor_through_defect_and_mass :
    ¬ ∃ F : (LogIndex →₀ ℝ) → ℂ → ℂ,
      ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
        mixtureSample c (Real.log 2 - Real.log 3) = F (defect c) (mixtureSample c 0) := by
  rintro ⟨F, hF⟩
  obtain ⟨a, b, ha, hb, ha0, hb0, hm, hs, _⟩ :=
    exists_positive_null_equal_mass_pair_rational_difference 1
  rw [hF a ha, hF b hb, ha0, hb0, hm, sub_self] at hs
  exact zero_ne_one hs

end RHTower.WeilWorkPBAP
