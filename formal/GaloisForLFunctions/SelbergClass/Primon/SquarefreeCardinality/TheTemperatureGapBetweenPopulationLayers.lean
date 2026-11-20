import GaloisForLFunctions.SelbergClass.Primon.SquarefreeCardinality.ThePrimeFactorsOfEveryTemperatureDerivative
import Mathlib.Data.Nat.Squarefree

/-!
# The cold limit of every squarefree population layer

Distinct prime subsets have distinct integer energies. At fixed particle
number j there is one lowest energy Eⱼ. After multiplying the coefficient
by exp(β Eⱼ), the contribution of all higher energies is at most the tail
of one geometric series, independently of j and of the prime support.
Every extra particle at least doubles the minimum energy.
-/

open Finset Filter Topology Polynomial RHTower
namespace GaloisForLFunctions.SelbergClass.Primon

noncomputable section

/-- Minimum product of j distinct letters. The empty layer above the support size has value zero. -/
def leastPopulationEnergy (P : Finset ℕ) (j : ℕ) :=
  if h : j ≤ P.card then ((P.powersetCard j).image finitePrimeSubsetProduct).min'
    ((powersetCard_nonempty.mpr h).image _) else 0

theorem exists_ground_subset {P : Finset ℕ} {j : ℕ} (hj : j ≤ P.card) :
    ∃ S ∈ P.powersetCard j, finitePrimeSubsetProduct S = leastPopulationEnergy P j := by
  rw [leastPopulationEnergy,dif_pos hj]
  exact mem_image.mp (min'_mem _ _)

theorem leastPopulationEnergy_le {P S : Finset ℕ} {j : ℕ} (hS : S ∈ P.powersetCard j) :
    leastPopulationEnergy P j ≤ finitePrimeSubsetProduct S := by
  obtain ⟨hs,hc⟩ := mem_powersetCard.mp hS
  rw [leastPopulationEnergy,dif_pos (hc ▸ card_le_card hs)]
  exact min'_le _ _ (mem_image_of_mem _ hS)

theorem leastPopulationEnergy_zero (P : Finset ℕ) : leastPopulationEnergy P 0=1 := by
  simp [leastPopulationEnergy,finitePrimeSubsetProduct]

private theorem subset_energy_injective {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) :
    Set.InjOn finitePrimeSubsetProduct (P.powerset : Set (Finset ℕ)) := by
  intro S hS T hT he
  have hs := Nat.primeFactors_prod (fun p h => hp p (mem_powerset.mp hS h))
  have ht := Nat.primeFactors_prod (fun p h => hp p (mem_powerset.mp hT h))
  exact hs.symm.trans ((congrArg Nat.primeFactors he).trans ht)

theorem leastPopulationEnergy_pos {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) {j : ℕ} (hj : j ≤ P.card) :
    0 < leastPopulationEnergy P j := by
  obtain ⟨S,hS,he⟩ := exists_ground_subset hj
  rw [←he]
  exact prod_pos fun p h => (hp p ((mem_powersetCard.mp hS).1 h)).pos

/-- Successive minimum energies have strictly increasing differences. -/
theorem leastPopulationEnergy_double {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) {j : ℕ} (hj : j < P.card) :
    2*leastPopulationEnergy P j ≤ leastPopulationEnergy P (j+1) := by
  obtain ⟨S,hS,he⟩ := exists_ground_subset (Nat.succ_le_of_lt hj)
  obtain ⟨hs,hcard⟩ := mem_powersetCard.mp hS
  obtain ⟨p,hpS⟩ := card_pos.mp (show 0 < S.card by omega)
  have hE := leastPopulationEnergy_le (P:=P) (j:=j) (S:=S.erase p)
    (mem_powersetCard.mpr ⟨(erase_subset ..).trans hs,by rw [card_erase_of_mem hpS,hcard,Nat.add_sub_cancel]⟩)
  calc _ ≤ p*finitePrimeSubsetProduct (S.erase p) := Nat.mul_le_mul (hp p (hs hpS)).two_le hE
       _ = _ := (mul_prod_erase S id hpS).trans he

/-- At each population the real activity coefficient is the partial partition on that layer. -/
theorem squarefreeCardinality_coeff (P : Finset ℕ) (β : ℝ) (j : ℕ) :
    (squarefreeCardinalityPolynomial P β).coeff j =
      ∑ S ∈ P.powersetCard j, Real.exp (-(finitePrimeSubsetProduct S:ℝ)*β) := by
  rw [squarefreeCardinalityPolynomial,finsetSum_coeff,powersetCard_eq_filter,sum_filter]
  apply sum_congr rfl
  intro S _
  by_cases h : S.card=j <;> simp [coeff_C_mul,coeff_X_pow,h,eq_comm]

/-- One geometric series controls all excited states, uniformly in the size
of the prime support and the population. -/
theorem normalized_population_enclosure {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p)
    {j : ℕ} (hj : j ≤ P.card) {β : ℝ} (hb : 0 < β) :
    1 ≤ Real.exp (β*leastPopulationEnergy P j)*(squarefreeCardinalityPolynomial P β).coeff j ∧
    Real.exp (β*leastPopulationEnergy P j)*(squarefreeCardinalityPolynomial P β).coeff j ≤
      (1-Real.exp (-β))⁻¹ := by
  let E := leastPopulationEnergy P j
  let F := P.powersetCard j
  let q := Real.exp (-β)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  let v (S : Finset ℕ) := finitePrimeSubsetProduct S-E
  have hid (S : Finset ℕ) (hs : S ∈ F) :
      Real.exp (β*E)*Real.exp (-(finitePrimeSubsetProduct S:ℝ)*β) = q^(v S) := by
    rw [←Real.exp_add,←Real.exp_nat_mul]
    congr 1
    dsimp only [v]
    rw [Nat.cast_sub (leastPopulationEnergy_le hs)]
    ring
  have he : Real.exp (β*E)*(squarefreeCardinalityPolynomial P β).coeff j = ∑ S ∈ F, q^(v S) := by
    rw [squarefreeCardinality_coeff,mul_sum]
    exact sum_congr rfl hid
  rw [show Real.exp (β*leastPopulationEnergy P j)*(squarefreeCardinalityPolynomial P β).coeff j = _
    from he]
  obtain ⟨S,hS,hs⟩ := exists_ground_subset hj
  have hv : v S=0 := Nat.sub_eq_zero_of_le hs.le
  have h₁ := single_le_sum (s:=F) (f:=fun T => q^(v T)) (fun T _ => pow_nonneg hq _) hS
  rw [hv,pow_zero] at h₁
  refine ⟨h₁,?_⟩
  have hinj : Set.InjOn v F := by
    intro A hA B hB h
    apply subset_energy_injective hp (mem_powerset.mpr (mem_powersetCard.mp hA).1)
      (mem_powerset.mpr (mem_powersetCard.mp hB).1)
    have h₁ := leastPopulationEnergy_le hA
    have h₂ := leastPopulationEnergy_le hB
    dsimp only [v,E] at h
    omega
  have hlt : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb)
  have hsum := (summable_geometric_of_lt_one hq hlt).sum_le_tsum (F.image v) (fun k _ => pow_nonneg hq k)
  rwa [sum_image hinj,tsum_geometric_of_lt_one hq hlt] at hsum

/-- The unique ground subset has asymptotic weight one at every population. -/
theorem normalized_population_tendsto {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) {j : ℕ} (hj : j ≤ P.card) :
    Tendsto (fun β : ℝ => Real.exp (β*leastPopulationEnergy P j)*(squarefreeCardinalityPolynomial P β).coeff j)
      atTop (𝓝 1) := by
  have hq : Tendsto (fun β : ℝ => Real.exp (-β)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h := (tendsto_const_nhds (x:=(1:ℝ))).sub hq
  rw [sub_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using h.inv₀ one_ne_zero)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with β hb using (normalized_population_enclosure hp hj hb).1
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with β hb using (normalized_population_enclosure hp hj hb).2


end

end GaloisForLFunctions.SelbergClass.Primon
