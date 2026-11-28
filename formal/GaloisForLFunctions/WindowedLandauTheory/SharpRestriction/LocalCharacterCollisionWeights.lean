import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LocalCharacterCandidateFactors
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.CharacterWeightSum
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.ResiduePrimePowerSums
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LocalRowWeightBounds
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.SquarefreeDivisorWeights
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.SquarefreeFrobeniusCycles

/-! A root colliding with the chosen character value has a
minimal polynomial among the primary binomial divisors. A union
bound transfers their count to the squarefree polynomial mass. -/

noncomputable section

open Finset Polynomial WindowedLandauTheory.CyclotomicNorms
open WindowedLandauTheory.CyclotomicNorms.CycleTypeFiniteOrder

namespace WindowedLandauTheory.ConcN

open FiniteWeight

variable (g N : ℕ) [Fact g.Prime]

open Classical in
private theorem collision_weight_le (c₀ : (ZMod g)ˣ) (hg : 3 ≤ g) :
    ∑ c ∈ (squarefreeCoefficients g N).filter (fun c => ¬ avoidsCharacter g N c₀ c),
      squarefreeWeight g (monicOf c) ≤
    ∑ δ ∈ Icc 1 N, ((characterFactorCandidates g δ c₀).card : ℝ) * ((g : ℝ) ^ δ - 1)⁻¹ := by
  classical
  let μ (c : Fin N → ZMod g) := squarefreeWeight g (monicOf c)
  have hμ (c : Fin N → ZMod g) : 0 ≤ μ c := squarefreeWeight_nonneg g _
  have hsub : {c | c ∈ squarefreeCoefficients g N ∧ ¬ avoidsCharacter g N c₀ c} ⊆
      ⋃ δ ∈ Icc 1 N, ⋃ c' ∈ characterFactorCandidates g δ c₀,
        {c : Fin N → ZMod g | c ∈ squarefreeCoefficients g N ∧ monicOf c' ∣ monicOf c} := by
    rintro c ⟨hc, hb⟩
    have ⟨hs, h0⟩ := (Finset.mem_filter.mp hc).2
    have hGood : GoodPoly N (monicOf c) := ⟨monic_monicOf c, natDegree_monicOf c, h0, hs⟩
    unfold avoidsCharacter at hb
    push Not at hb
    obtain ⟨l, hl, -, x, hx, he⟩ := hb
    have hx0 := ne_zero_of_mem hGood hx
    have hfx : aeval x (monicOf c) = 0 := by
      rw [← eval_map_algebraMap]
      exact (mem_rootsBar hGood).mp hx
    have hxI : IsIntegral (ZMod g) x := ⟨monicOf c, monic_monicOf c, hfx⟩
    let P := minpoly (ZMod g) x
    have hP := minpoly.irreducible hxI
    have hm := minpoly.monic hxI
    have hdiv : P ∣ monicOf c := minpoly.dvd _ _ hfx
    have hdeg : P.natDegree ≤ N := by
      have h := natDegree_le_of_dvd hdiv (monic_monicOf c).ne_zero
      rwa [natDegree_monicOf] at h
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    refine ⟨P.natDegree, Finset.mem_Icc.mpr ⟨hP.natDegree_pos, hdeg⟩,
      (fun i : Fin P.natDegree => P.coeff i), minpoly_mem_characterFactorCandidates g x hxI hx0 c₀ hl he hg, hc, ?_⟩
    rwa [monicOf_coeffs P hm rfl]
  rw [← weight_eq_filter' μ (squarefreeCoefficients g N) (fun c => ¬ avoidsCharacter g N c₀ c)]
  refine (weight_mono μ hμ hsub).trans ((weight_biUnion_le μ hμ _ _).trans ?_)
  refine Finset.sum_le_sum fun δ hδ => (weight_biUnion_le μ hμ _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun c' hc' => ?_
  have hi := irreducible_of_mem_characterFactorCandidates g hc'
  rw [weight_eq_filter']
  have h := squarefree_divisor_weight_le g N (monicOf c') (monic_monicOf c')
    ((squarefreeCoefficients g N).filter (fun c => monicOf c' ∣ monicOf c))
    (fun c hc => Finset.mem_filter.mp hc)
  rw [squarefreeWeight_of_irreducible g _ hi (monic_monicOf c'), natDegree_monicOf] at h
  exact h

open Classical in
theorem local_character_collision_weight_le (q₁ d : ℕ) (c₀ : (ZMod g)ˣ)
    (hN : 1 ≤ N) (hq : q₁.Prime) (hd : d.Prime) (hqd : q₁ ≠ d)
    (hq2 : q₁ ≠ 2) (hd2 : d ≠ 2) (hmax : 16 ≤ max q₁ d)
    (h16 : 16 ∣ g - 1) (hqg : q₁ ∣ g - 1) (hdg : d ∣ g - 1) :
    ∑ c ∈ (squarefreeCoefficients g N).filter (fun c => ¬ avoidsCharacter g N c₀ c),
      squarefreeWeight g (monicOf c) ≤
    1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / ((g : ℝ) - 1) := by
  have hg : 2 ≤ g := (Fact.out : g.Prime).two_le
  have hg17 : 17 ≤ g := by have h := Nat.le_of_dvd (by omega) h16; omega
  have hgR : (1 : ℝ) < g := by exact_mod_cast (show 1 < g by omega)
  let b (δ : ℕ) := (characterFactorCandidates g δ c₀).card
  have hb1 : (b 1 : ℝ) * ((g : ℝ) - 1)⁻¹ ≤ 1 / (4 * (min q₁ d : ℕ)) := by
    have hc := characterFactorCandidates_count g 1 c₀
    rw [one_mul, pow_one] at hc
    have hs := prime_power_order_share g q₁ d hg hq hd hqd hq2 hd2 hmax h16 hqg hdg
    rw [Nat.cast_sub (by omega : 1 ≤ g), Nat.cast_one, div_eq_mul_inv] at hs
    refine (mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (sub_nonneg.mpr hgR.le))).trans hs
    exact_mod_cast hc
  have hb2 (δ : ℕ) (hδ : 2 ≤ δ) : δ * b δ ≤ δ * (g - 1) + (g ^ δ - 1) / (g - 1) :=
    (characterFactorCandidates_count g δ c₀).trans
      (prime_power_order_count g δ hg ((by norm_num : 4 ∣ 16).trans h16) (by omega))
  exact (collision_weight_le g N c₀ (by omega)).trans (character_weight_sum_le g N hN hg b _ hb1 hb2)

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.local_character_collision_weight_le
