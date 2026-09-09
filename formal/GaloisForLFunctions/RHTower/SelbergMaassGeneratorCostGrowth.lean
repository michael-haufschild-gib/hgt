import GaloisForLFunctions.RHTower.SelbergMaassGeneratorComparison
import GaloisForLFunctions.HTGeometry.FiniteRegularCostGrowth

/-!
# The actual all-word comparison cost cannot be uniform in congruence level

Distinct translation powers give at least N+1 literal deck classes. Combining
this injection with the finite word-counting bound proves explicit thresholds
and divergence of the constructed quadratic word-cost coefficient. Its least
cost also bounds every other valid choice of complete generator-word costs,
so changing representatives cannot remove the divergence. These results do
not classify the optimal source or Cayley-graph comparison constant.
-/

open Complex Set UpperHalfPlane ModularGroup Filter Topology
namespace GaloisForLFunctions.RHTower.SelbergMaassGeneratorCostGrowth
open SelbergMaassCongruenceTrace SelbergMaassGeneratorComparison
noncomputable section
local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

/-- Distinct translation powers through one level period give distinct literal deck classes. -/
def translationClass (N : ℕ) (j : Fin (N+1)) : Deck N :=
  QuotientGroup.mk (T^(j.val:ℤ))

theorem translationClass_injective (N : ℕ) : Function.Injective (translationClass N) := by
  intro j k h
  have hm : (T^(j.val:ℤ))⁻¹*T^(k.val:ℤ) ∈ CongruenceSubgroup.Gamma (N+1) :=
    QuotientGroup.eq.mp h
  rw [← zpow_neg,← zpow_add] at hm
  have he := (CongruenceSubgroup.Gamma_mem.mp hm).2.1
  simp only [ModularGroup.coe_T_zpow] at he
  have hz : (k.val:ZMod (N+1))-(j.val:ZMod (N+1))=0 := by
    have he' : -(j.val:ZMod (N+1))+(k.val:ZMod (N+1))=0 := by simpa using he
    linear_combination he'
  have hv := congrArg ZMod.val (sub_eq_zero.mp hz)
  apply Fin.ext
  simpa only [ZMod.val_natCast_of_lt j.isLt,ZMod.val_natCast_of_lt k.isLt] using hv.symm

/-- The actual congruence quotient has at least as many elements as its level. -/
theorem level_le_card_deck (N : ℕ) : N+1 ≤ Fintype.card (Deck N) := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (translationClass_injective N)

/-- Explicit level threshold forcing the constructed all-word comparison cost above k²/2. -/
theorem generatorConstant_gt_of_large_level (N k : ℕ) (hk : 0 < k)
    (hN : 2*5^k < N+1) : (k:ℝ)^2/2 < generatorConstant N := by
  by_contra h
  have hc := GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost.card_le_of_comparisonConstant_le
    (generatorS N) (generatorT N) (generators_generate N) k hk (le_of_not_gt h)
  have hl := level_le_card_deck N
  omega

/-- The actual level-dependent all-word coefficient diverges; mere group
generation cannot make this particular comparison recipe uniform in the level. -/
theorem generatorConstant_tendsto_atTop : Tendsto generatorConstant atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  obtain ⟨k,hk⟩ := exists_nat_gt (2*|B|+2)
  have hkR : 0 < (k:ℝ) := by linarith [abs_nonneg B]
  have hkN : 0 < k := by exact_mod_cast hkR
  have hB : B < (k:ℝ)^2/2 := by
    nlinarith [abs_nonneg B,le_abs_self B]
  filter_upwards [eventually_ge_atTop (2*5^k)] with N hN
  have hlevel : 2*5^k < N+1 := by omega
  exact le_trans hB.le (generatorConstant_gt_of_large_level N k hkN hlevel).le

/-- No fixed upper coefficient bounds this explicit all-word construction at all levels.
This does not exclude a sharper source or graph comparison with a different proof. -/
theorem not_exists_uniform_generatorConstant_bound :
    ¬ ∃ B : ℝ, ∀ N : ℕ, generatorConstant N ≤ B := by
  rintro ⟨B,hB⟩
  have hb := (tendsto_atTop.1 generatorConstant_tendsto_atTop) (B+1)
  obtain ⟨N,hN⟩ := hb.exists
  linarith [hB N]

/-- Least certified word cost is no larger than the cost of any other complete
choice of actual generator words at this level. -/
theorem generatorConstant_le_certifiedCost (N : ℕ) (c : Deck N → ℕ)
    (hcert : ∀ g : Deck N,
      GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost.GeneratedCost
        (generatorS N) (generatorT N) g (c g)) :
    generatorConstant N ≤ 1+(Fintype.card (Deck N):ℝ)⁻¹*∑ g : Deck N, (c g:ℝ)^2 := by
  classical
  have hmin (g : Deck N) :
      GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost.cost
        (generatorS N) (generatorT N) (generators_generate N) g ≤ c g :=
    Nat.find_min' _ (hcert g)
  unfold generatorConstant GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost.comparisonConstant
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro g _
  have h := hmin g
  have hr : (GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost.cost
      (generatorS N) (generatorT N) (generators_generate N) g:ℝ) ≤ (c g:ℝ) := by exact_mod_cast h
  nlinarith [show (0:ℝ) ≤ (GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost.cost
    (generatorS N) (generatorT N) (generators_generate N) g:ℝ) by positivity]

/-- Changing complete generator-word representatives cannot make the averaged
quadratic word-cost recipe uniformly bounded over the actual congruence levels. -/
theorem not_exists_uniform_certifiedCost_bound
    (c : ∀ N : ℕ, Deck N → ℕ)
    (hcert : ∀ (N : ℕ) (g : Deck N),
      GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost.GeneratedCost
        (generatorS N) (generatorT N) g (c N g)) :
    ¬ ∃ B : ℝ, ∀ N : ℕ,
      1+(Fintype.card (Deck N):ℝ)⁻¹*(∑ g : Deck N, (c N g:ℝ)^2) ≤ B := by
  rintro ⟨B,hB⟩
  apply not_exists_uniform_generatorConstant_bound
  exact ⟨B,fun N => (generatorConstant_le_certifiedCost N (c N) (hcert N)).trans (hB N)⟩

end
end GaloisForLFunctions.RHTower.SelbergMaassGeneratorCostGrowth
