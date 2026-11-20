import GaloisForLFunctions.SelbergClass.Primon.SquarefreeCardinality.AlternatingActivityAtASeparatedPopulation

/-!
# Uniform bounds on the nonreal activity roots

Increasing the population doubles the ground energy. Above a population
threshold depending only on inverse temperature, consecutive populations
give opposite signs on the negative activity axis. Each such interval
contains a distinct root, uniformly over all finite prime sets. At low
temperature these intervals account for the entire degree.
-/

open Finset Polynomial RHTower
namespace GaloisForLFunctions.SelbergClass.Primon

noncomputable section

theorem population_ground_ge_two_pow {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p)
    {j : ℕ} (hj : j ≤ P.card) : 2^j ≤ leastPopulationEnergy P j := by
  induction j with
  | zero => simp [leastPopulationEnergy_zero]
  | succ j ih => exact (show 2^(j+1) ≤ 2*leastPopulationEnergy P j by
      rw [pow_succ,mul_comm]; exact Nat.mul_le_mul_left _ (ih (by omega))).trans
        (leastPopulationEnergy_double hp (by omega))

private theorem slope_strict {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p)
    {j : ℕ} (hj : j < P.card) : populationSlope P j < populationSlope P (j+1) := by
  have hx : 2*(leastPopulationEnergy P j:ℝ) ≤ leastPopulationEnergy P (j+1) := by
    exact_mod_cast leastPopulationEnergy_double hp hj
  have hy : 0 < (leastPopulationEnergy P j:ℝ) := Nat.cast_pos.mpr (leastPopulationEnergy_pos hp hj.le)
  unfold populationSlope populationHalfGap
  rw [Nat.add_sub_cancel]
  linarith only [hx,hy,Nat.cast_nonneg (α:=ℝ) (leastPopulationEnergy P (j-1))]

theorem squarefreeCardinality_degree (P : Finset ℕ) (β : ℝ) :
    (squarefreeCardinalityPolynomial P β).natDegree = P.card := by
  refine le_antisymm (natDegree_sum_le_of_forall_le _ _ fun S hS =>
    (natDegree_C_mul_le ..).trans ((natDegree_X_pow_le _).trans (card_le_card (mem_powerset.mp hS)))) ?_
  apply le_natDegree_of_ne_zero
  rw [squarefreeCardinality_coeff]
  exact (sum_pos' (fun _ _ => (Real.exp_pos _).le)
    ⟨P,mem_powersetCard.mpr ⟨Subset.rfl,rfl⟩,Real.exp_pos _⟩).ne'

/-- All real roots are strictly negative at every real temperature. -/
theorem squarefree_real_root_neg (P : Finset ℕ) (β x : ℝ)
    (h : (squarefreeCardinalityPolynomial P β).IsRoot x) : x < 0 := by
  by_contra! hx
  rw [IsRoot,squarefreeCardinalityPolynomial,eval_finsetSum] at h
  simp only [eval_mul,eval_C,eval_pow,eval_X] at h
  apply ne_of_gt _ h
  refine sum_pos' (fun _ _ => mul_nonneg (Real.exp_pos _).le (pow_nonneg hx _)) ⟨∅,?_,?_⟩
  · simp
  · simpa only [card_empty,pow_zero,mul_one] using Real.exp_pos _

/-- The thermal threshold gives a uniform bound J on the degree missed by
distinct negative roots, independent of the primes and of the degree. -/
theorem distinct_activity_roots_above_population {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p)
    {β : ℝ} (hb : 0 < β) (J : ℕ)
    (hJ : 2*Real.exp (-β*((2:ℝ)^(J-1)/2)) < 1-Real.exp (-β)) :
    P.card-J ≤ (squarefreeCardinalityPolynomial P β).roots.toFinset.card := by
  let m := P.card
  let F := squarefreeCardinalityPolynomial P β
  let y (i : ℕ) := -Real.exp (β*populationSlope P (m-i))
  have hsign {j : ℕ} (h₁ : J ≤ j) (h₂ : j ≤ m) :
      0 < (-1:ℝ)^j*F.eval (-Real.exp (β*populationSlope P j)) := by
    apply squarefree_negative_activity_sign hp h₂ hb
    have he : (2:ℝ)^(J-1) ≤ leastPopulationEnergy P (j-1) := by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.sub_le_sub_right h₁ 1)).trans
        (population_ground_ge_two_pow hp (j:=j-1) (by omega))
    have hd : (2:ℝ)^(J-1)/2 ≤ populationHalfGap P j := div_le_div_of_nonneg_right he (by norm_num)
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hd (neg_nonpos.mpr hb.le))) (by norm_num : (0:ℝ) ≤ 2)).trans_lt hJ
  by_cases hsmall : m < J
  · simpa only [show P.card-J=0 by change m-J=0; omega] using Nat.zero_le F.roots.toFinset.card
  have hy (i : ℕ) (hi : i < m-J) : y i < y (i+1) := by
    have hr : m-(i+1)+1=m-i := by omega
    have hs := slope_strict hp (j:=m-(i+1)) (by change m-(i+1)<m; omega)
    rw [hr] at hs
    exact neg_lt_neg (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hs hb))
  have halt (i : ℕ) (hi : i ≤ m-J) : 0 < (-1:ℝ)^i*(C ((-1:ℝ)^m)*F).eval (y i) := by
    have hs := hsign (j:=m-i) (by omega) (Nat.sub_le ..)
    have hpowers : (-1:ℝ)^i*(-1)^m=(-1)^(m-i) := by
      conv_lhs => rhs; rw [show m=m-i+i by omega,pow_add]
      calc _ = ((-1:ℝ)*(-1))^i*(-1)^(m-i) := by rw [mul_pow]; ring
           _ = _ := by norm_num
    rw [eval_mul,eval_C,←mul_assoc,hpowers]
    exact hs
  have h := GaloisForLFunctions.SignAlternation.card_roots_toFinset_ge_of_alternating hy halt
  rwa [roots_C_mul F (pow_ne_zero _ (by norm_num))] at h

/-- Every fixed positive inverse temperature allows only a bounded number
of missing distinct negative roots over all finite prime populations. -/
theorem uniform_activity_root_defect {β : ℝ} (hb : 0 < β) :
    ∃ J : ℕ, ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
      P.card-J ≤ (squarefreeCardinalityPolynomial P β).roots.toFinset.card := by
  let u := (1-Real.exp (-β))/2
  have hu : 0 < u := half_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hb)))
  obtain ⟨n,hn⟩ := exists_nat_gt ((-Real.log u)*2/β)
  have hpow (k : ℕ) : k ≤ 2^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; have := Nat.two_pow_pos k; omega
  have hle : (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hpow n
  have hlog := (div_lt_iff₀ hb).mp (hn.trans_le hle)
  have he := Real.exp_lt_exp.mpr (show -β*((2:ℝ)^n/2) < Real.log u by linarith only [hlog])
  rw [Real.exp_log hu] at he
  refine ⟨n+1, fun P hp => distinct_activity_roots_above_population hp hb (n+1) ?_⟩
  rw [Nat.add_sub_cancel]
  dsimp only [u] at he
  linarith only [he]

/-- When the vacuum gap separates the first two populations, every
activity root is real, negative and simple, for every finite prime set. -/
theorem squarefree_cold_roots {β : ℝ} (hb : 0 < β)
    (hgap : 2*Real.exp (-β/2) < 1-Real.exp (-β)) (P : Finset ℕ)
    (hp : ∀ p ∈ P, Nat.Prime p) :
    let F := squarefreeCardinalityPolynomial P β
    F.Splits ∧ F.roots.Nodup ∧ ∀ x : ℝ, F.IsRoot x → x < 0 := by
  let F := squarefreeCardinalityPolynomial P β
  have hd : P.card ≤ F.roots.toFinset.card := by
    apply distinct_activity_roots_above_population hp hb 0
    simpa using hgap
  have he := Multiset.toFinset_card_le F.roots
  have hc := card_roots' F
  have hdeg : F.natDegree=P.card := squarefreeCardinality_degree P β
  refine ⟨splits_iff_card_roots.mpr (by omega),Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega),
    squarefree_real_root_neg P β⟩

/-- The same explicit temperature works for all prime supports. -/
theorem squarefree_cold_roots_of_log_three {β : ℝ} (hb : 2*Real.log 3 ≤ β)
    (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p) :
    let F := squarefreeCardinalityPolynomial P β
    F.Splits ∧ F.roots.Nodup ∧ ∀ x : ℝ, F.IsRoot x → x < 0 := by
  have h₃ := Real.log_pos (by norm_num : (1:ℝ)<3)
  have hb₀ : 0 < β := by linarith only [h₃,hb]
  have h := Real.exp_le_exp.mpr (show -β/2 ≤ -Real.log 3 by linarith only [hb])
  rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<3)] at h
  have h' := Real.exp_lt_exp.mpr (show -β < -β/2 by linarith only [hb₀])
  exact squarefree_cold_roots hb₀ (by linarith only [h,h']) P hp


end

end GaloisForLFunctions.SelbergClass.Primon
