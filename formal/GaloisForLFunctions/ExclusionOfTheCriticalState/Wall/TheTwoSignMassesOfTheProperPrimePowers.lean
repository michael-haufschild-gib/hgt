import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeNumberTheoremOnTheState

/-!
# The two sign masses of the proper-prime-power wave

Selecting each prime power independently gives a sharp extremum at every time.
At late times the two extrema converge to half the integrals of the two parts
of the state. Prime squares carry both limits.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private abbrev Powers := Nat.Primes × ℕ

/-- Atom of a proper prime power, read at physical time t. -/
def properPowerContribution (Φ : ℝ → ℝ) (t : ℝ) (j : Nat.Primes × ℕ) : ℝ :=
  vonMangoldtAtom (properPrimePowerIndex j)*Φ (t-Real.log (properPrimePowerIndex j))

private theorem atomWeight_nonneg (j : Powers) : 0 ≤ vonMangoldtAtom (properPrimePowerIndex j) := by
  unfold vonMangoldtAtom
  split_ifs <;> first | exact le_rfl | exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- For a summable real row, its positive mass is the largest sum after arbitrary thinning. -/
private theorem greatest_thinned_positive_mass {ι : Type*} {a : ι → ℝ}
    (ha : Summable fun j => |a j|) :
    IsGreatest {r : ℝ | ∃ c : ι → ℝ, (∀ j, c j ∈ Set.Icc 0 1) ∧ r=∑' j, c j*a j}
      (∑' j, max (a j) 0) := by
  have hmax (j : ι) : max (a j) 0 ≤ |a j| := max_le (le_abs_self _) (abs_nonneg _)
  have hp := Summable.of_nonneg_of_le (fun j => le_max_right (a j) 0) hmax ha
  constructor
  · refine ⟨fun j => if 0 ≤ a j then 1 else 0,fun j => ?_,tsum_congr fun j => ?_⟩
    · change (if 0 ≤ a j then (1:ℝ) else 0) ∈ Set.Icc 0 1
      split_ifs <;> exact ⟨by norm_num,by norm_num⟩
    · change max (a j) 0 = (if 0 ≤ a j then 1 else 0)*a j
      by_cases h : 0 ≤ a j
      · rw [if_pos h,one_mul,max_eq_left h]
      · rw [if_neg h,zero_mul,max_eq_right (le_of_not_ge h)]
  · rintro r ⟨c,hc,rfl⟩
    have hs : Summable fun j => c j*a j := Summable.of_norm_bounded ha (fun j => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hc j).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hc j).2)
    refine hs.tsum_le_tsum ?_ hp
    intro j
    rcases le_or_gt 0 (a j) with h | h
    · rw [max_eq_left h]
      exact mul_le_of_le_one_left h (hc j).2
    · rw [max_eq_right h.le]
      exact mul_nonpos_of_nonneg_of_nonpos (hc j).1 h.le

/-- The extremizing thinning may depend on both the prime and its exponent, at each time.
Its positive and negative sign masses converge separately. -/
theorem riemannHypothesis_or_properPower_sign_extrema : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ s : ℝ, s=1 ∨ s= -1 →
        let V := fun t : ℝ => ∑' j, max (s*properPowerContribution Φ t j) 0
        (∀ t : ℝ, IsGreatest
          {r : ℝ | ∃ c : (Nat.Primes × ℕ) → ℝ, (∀ j, c j ∈ Set.Icc 0 1) ∧
            r=∑' j, c j*(s*properPowerContribution Φ t j)} (V t)) ∧
        Tendsto V atTop (𝓝 ((∫ u, max (s*Φ u) 0)/2)) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl h
  obtain ⟨Φ,hΦ,he,htest⟩ := criticalState_tendsto_dominated_properPowerWave hW ht hF
  obtain ⟨_,_,Ψ,hΨ,heΨ,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq : Ψ=Φ := (Continuous.ae_eq_iff_eq volume hΨ hΦ).mp (heΨ.symm.trans he)
  subst Ψ
  obtain ⟨_,_,habs⟩ := properPowerWave_absolute_envelope (by norm_num : (0:ℝ)<2) hC hb
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,he,fun s hs => ?_⟩
  have hs1 : |s|=1 := by rcases hs with rfl | rfl <;> norm_num
  let g := fun u => max (s*Φ u) 0
  have hg : Continuous g := (continuous_const.mul hΦ).max continuous_const
  have hb (u : ℝ) : |g u| ≤ |Φ u| := by
    change |max (s*Φ u) 0| ≤ |Φ u|
    rw [abs_of_nonneg (le_max_right (s*Φ u) 0)]
    exact max_le ((le_abs_self _).trans_eq (by rw [abs_mul,hs1,one_mul])) (abs_nonneg _)
  constructor
  · intro t
    apply greatest_thinned_positive_mass
    simpa only [properPowerContribution,abs_mul,hs1,one_mul,abs_of_nonneg (atomWeight_nonneg _)]
      using (habs t).1
  · refine (htest g hg hb).congr (fun t => tsum_congr fun j => ?_)
    dsimp only [g,properPowerContribution]
    rw [mul_max_of_nonneg _ _ (atomWeight_nonneg j),mul_zero,mul_left_comm]

#print axioms riemannHypothesis_or_properPower_sign_extrema
end GaloisForLFunctions.ExclusionOfTheCriticalState
