import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.CountingPrimePairsInLogarithmicShells
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeWaveAtTheWallIsTheBoundedOrderOfTheWallLaw

/-!
# The distinct-prime contribution at short additive gaps

The Selberg sieve absorbs the two logarithms in the prime atom weights. The
exponential confinement of the profile then sums the unit logarithmic shells.
-/

noncomputable section
open Finset Filter MeasureTheory Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Contribution of an integer to the Mangoldt wave, with the ordinary-prime
coefficient at a prime. -/
def physicalPrimeAtom (Φ : ℝ → ℝ) (t : ℝ) (p : ℕ) := vonMangoldtAtom p * Φ (t-Real.log p)

/-- Absolute contribution from distinct prime pairs with first prime in one
unit log shell and positive additive gap at most K. -/
def shortPrimePairShell (Φ : ℝ → ℝ) (t : ℝ) (K j : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 K, ∑ p ∈ shellPrimePairs (t+j+1) d,
    |physicalPrimeAtom Φ t p * physicalPrimeAtom Φ t (p+d)|

/-- Every active pair belongs to exactly one shell. -/
theorem unique_shell_of_prime_pair {t : ℝ} {p d : ℕ} (hp : p.Prime) (hq : (p+d).Prime)
    (ht : Real.exp t < p) : ∃! j : ℕ, p ∈ shellPrimePairs (t+j+1) d := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have htlog : t < Real.log p := (Real.lt_log_iff_exp_lt hp0).2 ht
  have he (j : ℕ) : p ∈ shellPrimePairs (t+j+1) d ↔ ⌈Real.log p-t⌉₊ = j+1 := by
    rw [shellPrimePairs,mem_filter,mem_Icc,Nat.le_floor_iff (Real.exp_pos _).le,
      Nat.ceil_eq_iff (Nat.succ_ne_zero j),Nat.succ_sub_one,Nat.cast_succ]
    constructor
    · rintro ⟨⟨_,hu⟩,_,_,hl⟩
      have ha := (Real.lt_log_iff_exp_lt hp0).2 hl
      have hb := (Real.log_le_iff_le_exp hp0).2 hu
      exact ⟨by linarith only [ha],by linarith only [hb]⟩
    · rintro ⟨hl,hu⟩
      exact ⟨⟨hp.one_le,(Real.log_le_iff_le_exp hp0).1 (by linarith only [hu])⟩,
        hp,hq,(Real.lt_log_iff_exp_lt hp0).1 (by linarith only [hl])⟩
  have hc : 0 < ⌈Real.log p-t⌉₊ := Nat.ceil_pos.2 (sub_pos.2 htlog)
  refine ⟨⌈Real.log p-t⌉₊-1,(he _).2 (by omega),fun j hj => ?_⟩
  have := (he j).1 hj
  omega

private theorem atom_bound {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {p : ℕ} (hp : p.Prime)
    {t v : ℝ} (hv : 1 ≤ v) (hvp : v ≤ Real.log p) :
    |physicalPrimeAtom Φ t p| ≤ C * v * Real.exp (2*t-5*v/2) := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log p := (zero_le_one.trans hv).trans hvp
  have hd : Real.log p ≤ v*Real.exp (5*(Real.log p-v)/2) := by
    have h := Real.add_one_le_exp (5*(Real.log p-v)/2)
    calc Real.log p = v + (Real.log p-v) := by ring
      _ ≤ v*(1+5*(Real.log p-v)/2) := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr hvp),hvp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [h]) (zero_le_one.trans hv)
  have hs : Real.sqrt p = Real.exp (Real.log p/2) := by rw [Real.exp_half,Real.exp_log hp0]
  rw [physicalPrimeAtom,vonMangoldtAtom,if_pos hp.two_le,ArithmeticFunction.vonMangoldt_apply_prime hp,
    abs_mul,abs_of_nonneg (div_nonneg hlog (Real.sqrt_nonneg _)),hs]
  calc _ ≤ (Real.log p/Real.exp (Real.log p/2))*(C*Real.exp (2*(t-Real.log p))) :=
           mul_le_mul_of_nonneg_left (hb _) (div_nonneg hlog (Real.exp_pos _).le)
    _ = C * (Real.log p) * Real.exp (2*t-5*Real.log p/2) := by
           rw [div_eq_mul_inv,← Real.exp_neg,show 2*t-5*Real.log p/2 = -(Real.log p/2)+2*(t-Real.log p) by ring,Real.exp_add]
           ring
    _ ≤ C * (v*Real.exp (5*(Real.log p-v)/2)) * Real.exp (2*t-5*Real.log p/2) := by gcongr
    _ = _ := by
           have he : Real.exp (5*(Real.log p-v)/2) * Real.exp (2*t-5*Real.log p/2) = Real.exp (2*t-5*v/2) := by
             rw [← Real.exp_add]; congr 1; ring
           rw [← he]; ring

private theorem shortPrimePairShell_le {Φ : ℝ → ℝ} {C A : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {t : ℝ} (ht : 1 ≤ t) (K j : ℕ)
    (hc : (t+j+1)^2*(∑ d ∈ Icc 1 K, ((shellPrimePairs (t+j+1) d).card:ℝ)) ≤
      A*K*Real.exp (t+j+1)) :
    shortPrimePairShell Φ t K j ≤ (C^2*A*Real.exp 1)*K*(Real.exp (-4))^j := by
  let v := t+(j:ℝ)
  have hv : 1 ≤ v := by dsimp only [v]; linarith only [ht,(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  let w := C*v*Real.exp (2*t-5*v/2)
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have he (d p : ℕ) (hp : p ∈ shellPrimePairs (v+1) d) :
      |physicalPrimeAtom Φ t p * physicalPrimeAtom Φ t (p+d)| ≤ w*w := by
    obtain ⟨_,hp,hq,hl⟩ := mem_filter.1 hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    have hl' := (Real.lt_log_iff_exp_lt hp0).2 hl
    have h1 : v ≤ Real.log p := by linarith only [hl']
    have h2 : v ≤ Real.log (p+d:ℕ) := h1.trans (Real.log_le_log hp0 (by exact_mod_cast Nat.le_add_right p d))
    rw [abs_mul]
    exact mul_le_mul (atom_bound hC hb hp hv h1) (atom_bound hC hb hq hv h2) (abs_nonneg _) hw
  have hsum : shortPrimePairShell Φ t K j ≤ w*w*(∑ d ∈ Icc 1 K, ((shellPrimePairs (v+1) d).card:ℝ)) := by
    rw [shortPrimePairShell,mul_sum]
    apply sum_le_sum fun d _ => ?_
    calc _ ≤ ∑ _p ∈ shellPrimePairs (v+1) d, w*w := sum_le_sum fun p hp => he d p hp
      _ = _ := by rw [sum_const,nsmul_eq_mul,mul_comm]
  let N := ∑ d ∈ Icc 1 K, ((shellPrimePairs (v+1) d).card:ℝ)
  have hn : 0 ≤ N := sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hcount : v^2*N ≤ A*K*Real.exp (v+1) :=
    (mul_le_mul_of_nonneg_right (by nlinarith only [hv] : v^2 ≤ (v+1)^2) hn).trans hc
  calc _ ≤ w*w*N := hsum
    _ = (C^2*Real.exp (4*t-5*v))*(v^2*N) := by
      rw [show 4*t-5*v = (2*t-5*v/2)+(2*t-5*v/2) by ring,Real.exp_add]; dsimp only [w]; ring
    _ ≤ (C^2*Real.exp (4*t-5*v))*(A*K*Real.exp (v+1)) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by
      have he : Real.exp (4*t-5*v)*Real.exp (v+1) = Real.exp 1*(Real.exp (-4))^j := by
        rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add]
        congr 1; dsimp only [v]; ring
      calc _ = (C^2*A*K)*(Real.exp (4*t-5*v)*Real.exp (v+1)) := by ring
        _ = _ := by rw [he]; ring

/-- All positive additive prime gaps up to K contribute at most O(K) to the
absolute covariance, uniformly on the late ray. Every shell series converges. -/
theorem criticalState_short_prime_pair_bound {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ (Φ : ℝ → ℝ) (B : ℝ), Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 < B ∧ ∀ᶠ t : ℝ in atTop,
      ∀ K : ℕ, Summable (shortPrimePairShell Φ t K) ∧ (∑' j, shortPrimePairShell Φ t K j) ≤ B*K := by
  obtain ⟨_,_,Φ,hΦ,heq,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨A,hA,ha⟩ := eventually_shellPrimePairs_log_square_le
  obtain ⟨t₀,hh⟩ := eventually_atTop.1 ha
  let r := Real.exp (-4)
  have hr : 0 < r := Real.exp_pos _
  have hr' : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  let D := C^2*A*Real.exp 1
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hgap : 0 < 1-r := sub_pos.2 hr'
  refine ⟨Φ,1+D*(1-r)⁻¹,hΦ,heq,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max 1 t₀)] with t ht
  intro K
  have ht' := (le_max_left _ _).trans ht
  have hbound (j : ℕ) : shortPrimePairShell Φ t K j ≤ (D*K)*r^j :=
    shortPrimePairShell_le hC hb ht' K j (hh _ (by linarith only [(le_max_right _ _).trans ht,(Nat.cast_nonneg j : (0:ℝ) ≤ j)]) K)
  have hn (j : ℕ) : 0 ≤ shortPrimePairShell Φ t K j :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hg := (summable_geometric_of_lt_one hr.le hr').mul_left (D*K)
  have hs := Summable.of_nonneg_of_le hn hbound hg
  refine ⟨hs,(hs.tsum_le_tsum hbound hg).trans ?_⟩
  rw [tsum_mul_left,tsum_geometric_of_lt_one hr.le hr']
  calc _ = D*(1-r)⁻¹*K := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (Nat.cast_nonneg K)

/-- Unconditional arithmetic alternative for the critical state. -/
theorem riemannHypothesis_or_controlled_short_prime_pairs :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (B : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 < B ∧
      ∀ᶠ t : ℝ in atTop, ∀ K : ℕ, Summable (shortPrimePairShell Φ t K) ∧
        (∑' j, shortPrimePairShell Φ t K j) ≤ B*K := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨Φ,B,hΦ,heq,hB,h⟩ := criticalState_short_prime_pair_bound hW ht hF
  exact Or.inr ⟨W₀,F,Φ,B,hW,ht,hF,hΦ,heq,hB,h⟩

#print axioms unique_shell_of_prime_pair
#print axioms riemannHypothesis_or_controlled_short_prime_pairs

end GaloisForLFunctions.ExclusionOfTheCriticalState
