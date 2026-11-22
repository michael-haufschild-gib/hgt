import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.NormPrimesOfMangoldt
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.TrivialClassShortInterval
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.FamilyRealization

/-! Count primes with a norm generator congruent to one in an imaginary quadratic field. -/

open GlobalTheory.Hk

namespace UpperTheory.T3

theorem shortNorm : ShortNorm := by
  obtain ⟨A, c, c', hA, hc, hc', hInt⟩ := ShortInt.trivialClass_shortInterval
  refine shortNorm_of_mangoldt hA hc hc' ?_
  intro d M X h hd hd4 hd100 hM hX hB hh hh1
  obtain ⟨𝓕, h𝓕, hprime⟩ := exists_lFam_ray d M hd hd4 hd100 hM
  refine ⟨𝓕.lam 0, fun n => ?_, hprime, ?_⟩
  · exact (Finset.single_le_sum (fun g _ => 𝓕.lam_nonneg g n) (Finset.mem_univ 0)).trans (𝓕.lam_le n)
  · rw [← h𝓕] at hB ⊢
    exact hInt 𝓕 X h hX hB hh hh1

end UpperTheory.T3
