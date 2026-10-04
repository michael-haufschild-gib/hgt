import GaloisForLFunctions.RHTower.RoutePCausalBiasTransfer

/-! # Uniform reversible comparison of the actual finite prime bias -/

open Finset MeasureTheory

namespace RHTower.RoutePWindow

private theorem head_transfer {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (a b c k : ι → ℝ) (ha : ∀ p, 0 ≤ a p) (hk : ∀ p, 0 ≤ k p)
    (hstep : ∀ (p : ι) (f : ℝ → ℝ), Continuous f → (∀ t ≤ 0, f t = 0) →
      ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, (f t-b p*f (t-a p))^2) ≤
        k p*(∫ t in (0 : ℝ)..T, (f t-c p*f (t-a p))^2))
    (f : ℝ → ℝ) (hf : Continuous f) (hz : ∀ t ≤ 0, f t = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (head P a b f t)^2) ≤
      (∏ p ∈ P, k p)*(∫ t in (0 : ℝ)..T, (head P a c f t)^2) := by
  induction P using Finset.induction_on generalizing f with
  | empty => simp
  | @insert p P hp ih =>
    let g : ℝ → ℝ := fun t => f t-b p*f (t-a p)
    have hg : Continuous g := hf.sub
      ((hf.comp (continuous_id.sub continuous_const)).const_mul (b p))
    have hgz : ∀ t ≤ 0, g t = 0 := by
      intro t ht
      dsimp [g]
      rw [hz t ht, hz _ (by linarith [ha p])]
      simp
    have hIH := ih g hg hgz
    have hleft (t : ℝ) : head P a b g t = head (insert p P) a b f t := by
      rw [head_insert P a b f hp]
      exact head_difference P a b f (b p) (a p) t
    have hright (t : ℝ) : head P a c g t =
        head P a c f t-b p*head P a c f (t-a p) :=
      head_difference P a c f (b p) (a p) t
    simp_rw [hleft, hright] at hIH
    have h := hstep p (head P a c f) (continuous_head P a c f hf)
      (fun _ ht => head_zero_of_nonpos P a c f ha hz ht) T hT
    have hprod : 0 ≤ ∏ q ∈ P, k q := prod_nonneg (fun q _ => hk q)
    rw [prod_insert hp]
    calc
      _ ≤ (∏ q ∈ P, k q)*
          (∫ t in (0 : ℝ)..T, (head P a c f t-b p*head P a c f (t-a p))^2) := hIH
      _ ≤ (∏ q ∈ P, k q)*(k p*
          (∫ t in (0 : ℝ)..T, (head P a c f t-c p*head P a c f (t-a p))^2)) :=
        mul_le_mul_of_nonneg_left h hprod
      _ = _ := by simp_rw [head_insert P a c f hp]; ring

/-- No full-ray admission is needed to transfer a finite family of gains
in both directions. The cost sees only their differences. -/
theorem integral_head_gain_comparison {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (a b c : ι → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hb0 : ∀ p, 0 ≤ b p) (hb : ∀ p, b p ≤ 3/4)
    (hc0 : ∀ p, 0 ≤ c p) (hcb : ∀ p, c p ≤ b p)
    (f : ℝ → ℝ) (hf : Continuous f) (hz : ∀ t ≤ 0, f t = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (head P a b f t)^2) ≤
      (∏ p ∈ P, (1+33*(b p-c p)))*(∫ t in (0 : ℝ)..T, (head P a c f t)^2) ∧
    (∫ t in (0 : ℝ)..T, (head P a c f t)^2) ≤
      (∏ p ∈ P, (1+33*(b p-c p)))*(∫ t in (0 : ℝ)..T, (head P a b f t)^2) := by
  have hk (p : ι) : 0 ≤ 1+33*(b p-c p) := by linarith [hcb p]
  constructor
  · apply head_transfer P a b c _ ha hk _ f hf hz hT
    intro p g hg hgz S hS
    exact (difference_energy_comparison g hg hgz (ha p) hS
      (hb0 p) (hb p) (hc0 p) (hcb p)).1
  · apply head_transfer P a c b _ ha hk _ f hf hz hT
    intro p g hg hgz S hS
    exact (difference_energy_comparison g hg hgz (ha p) hS
      (hb0 p) (hb p) (hc0 p) (hcb p)).2

noncomputable def biasBudget : ℝ :=
  Real.exp (33*∑' n : ℕ, 1/((n : ℝ)*Real.sqrt (n : ℝ)))

theorem biasBudget_pos : 0 < biasBudget := Real.exp_pos _

private theorem summable_bias_cost :
    Summable (fun n : ℕ => 1/((n : ℝ)*Real.sqrt (n : ℝ))) := by
  have h := Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3/2)
  have he (n : ℕ) : (n : ℝ)*Real.sqrt (n : ℝ) = (n : ℝ)^(3/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, show (3/2 : ℝ) = 1+1/2 by norm_num,
      Real.rpow_add' (Nat.cast_nonneg n) (by norm_num : (1 : ℝ)+1/2 ≠ 0),
      Real.rpow_one]
  simpa only [he] using h

private theorem prime_bias_data (q : Nat.Primes → ℝ)
    (hq0 : ∀ p, 0 ≤ q p) (hq : ∀ p, q p ≤ 1/Real.sqrt (p : ℝ)) (p : Nat.Primes) :
    q p ≤ 3/4 ∧ meanGain q p ≤ q p ∧
      q p-meanGain q p ≤ 1/((p : ℝ)*Real.sqrt (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
  have hppos : 0 < (p : ℝ) := by linarith
  have hqs : (q p)^2 ≤ 1/(p : ℝ) := by
    have h := mul_self_le_mul_self (hq0 p) (hq p)
    simpa only [← sq, div_pow, one_pow, Real.sq_sqrt hppos.le] using h
  have hi : 1/(p : ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hp2
  have he : q p-meanGain q p = q p/(p : ℝ) := by unfold meanGain; ring
  refine ⟨by nlinarith [hq0 p], ?_, ?_⟩
  · have hn : 0 ≤ q p-meanGain q p := by rw [he]; exact div_nonneg (hq0 p) hppos.le
    linarith
  · rw [he]
    calc
      _ ≤ (1/Real.sqrt (p : ℝ))/(p : ℝ) := div_le_div_of_nonneg_right (hq p) hppos.le
      _ = _ := by ring

theorem prime_bias_product_le (P : Finset Nat.Primes) (q : Nat.Primes → ℝ)
    (hq0 : ∀ p, 0 ≤ q p) (hq : ∀ p, q p ≤ 1/Real.sqrt (p : ℝ)) :
    (∏ p ∈ P, (1+33*(q p-meanGain q p))) ≤ biasBudget := by
  have hsum : (∑ p ∈ P, 1/((p : ℝ)*Real.sqrt (p : ℝ))) ≤
      ∑' n : ℕ, 1/((n : ℝ)*Real.sqrt (n : ℝ)) := by
    calc
      _ = ∑ n ∈ P.image (fun p : Nat.Primes => (p : ℕ)),
          1/((n : ℝ)*Real.sqrt (n : ℝ)) := by
        rw [sum_image]
        intro p _ r _ hpr
        exact Subtype.ext hpr
      _ ≤ _ := summable_bias_cost.sum_le_tsum _ (fun _ _ => by positivity)
  calc
    _ ≤ Real.exp (∑ p ∈ P, 33*(q p-meanGain q p)) :=
      Real.prod_one_add_le_exp_sum P (fun p => mul_nonneg (by norm_num)
        (sub_nonneg.mpr (prime_bias_data q hq0 hq p).2.1))
    _ ≤ Real.exp (∑ p ∈ P, 33*(1/((p : ℝ)*Real.sqrt (p : ℝ)))) := by
      apply Real.exp_le_exp.mpr
      exact sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left
        (prime_bias_data q hq0 hq p).2.2 (by norm_num))
    _ = Real.exp (33*∑ p ∈ P, 1/((p : ℝ)*Real.sqrt (p : ℝ))) := by rw [mul_sum]
    _ ≤ biasBudget := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by norm_num))

/-- Uniform reversible comparison for every finite prime set and every
nonnegatively damped critical gain, with no energy-growth premise. -/
theorem integral_prime_bias_comparison (P : Finset Nat.Primes) (q : Nat.Primes → ℝ)
    (hq0 : ∀ p, 0 ≤ q p) (hq : ∀ p, q p ≤ 1/Real.sqrt (p : ℝ))
    (f : ℝ → ℝ) (hf : Continuous f) (hz : ∀ t ≤ 0, f t = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, (head P (fun p => Real.log (p : ℝ)) q f t)^2) ≤
      biasBudget*(∫ t in (0 : ℝ)..T,
        (head P (fun p => Real.log (p : ℝ)) (meanGain q) f t)^2) ∧
    (∫ t in (0 : ℝ)..T, (head P (fun p => Real.log (p : ℝ)) (meanGain q) f t)^2) ≤
      biasBudget*(∫ t in (0 : ℝ)..T, (head P (fun p => Real.log (p : ℝ)) q f t)^2) := by
  have ha (p : Nat.Primes) : 0 ≤ Real.log (p : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast p.property.one_lt.le
  have h := integral_head_gain_comparison P _ q (meanGain q) ha hq0
    (fun p => (prime_bias_data q hq0 hq p).1)
    (fun p => (prime_gain_bounds q p (hq0 p) (hq p)).1)
    (fun p => (prime_bias_data q hq0 hq p).2.1) f hf hz hT
  have hprod := prime_bias_product_le P q hq0 hq
  constructor
  · exact h.1.trans (mul_le_mul_of_nonneg_right hprod
      (intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)))
  · exact h.2.trans (mul_le_mul_of_nonneg_right hprod
      (intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)))

end RHTower.RoutePWindow
