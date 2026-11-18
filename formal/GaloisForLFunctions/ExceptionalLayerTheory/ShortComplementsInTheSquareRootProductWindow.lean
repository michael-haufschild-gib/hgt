import GaloisForLFunctions.ExceptionalLayerTheory.ReciprocalPrimeCancellationInTheCoprimeProduct

/-!
# Short complementary factors throughout the square-root product window

At every short complementary factor the complete prime interval through
the square-root product lies in the reciprocal prime cancellation range.
The lower prime cutoff may truncate the interval independently.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Ordinary primes above `F` in the product window, at a fixed cofactor. -/
def squareRootWindowPrimes (F L U v : ℕ) : Finset ℕ :=
  (Ico (max (F+1) (L/v+1)) (U/v+1)).filter Nat.Prime

/-- The full short-complement wing of the product window, including both
sharp product endpoints and any fixed first-prime threshold. -/
theorem short_complement_window_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X D R L U F : ℕ}, 1 ≤ X → 1 ≤ R →
      2 ≤ (X : ℝ)^(1/1000000 : ℝ) → (R : ℝ) ≤ (X : ℝ)^(1/400000 : ℝ) →
      Real.sqrt X ≤ (L : ℝ)+1 → (U : ℝ) ≤ (X : ℝ)^(500000001/1000000000 : ℝ) →
      |∑ v ∈ Icc 1 ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊, innerJump D v*
        ∑ p ∈ squareRootWindowPrimes F L U v, Real.log p*centeredPrimeWeight R (X/v/p)| ≤
        K*((D+1 : ℕ) : ℝ)*(X : ℝ)^(499701/1000000 : ℝ) := by
  obtain ⟨K,hK,hprime⟩ := centered_prime_subinterval
  obtain ⟨B,hB,hmass⟩ := mass_uniform
  refine ⟨(2+2*B)*K,by positivity,?_⟩
  intro X D R L U F hX hR hlarge hr hL hU
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  let P (a : ℝ) := (X : ℝ)^a
  have mul (a b : ℝ) : P a*P b=P (a+b) := (Real.rpow_add (zero_lt_one.trans_le hx) _ _).symm
  have powr (a b : ℝ) : (P a)^b=P (a*b) := (Real.rpow_mul (Nat.cast_nonneg X) _ _).symm
  have mono {a b : ℝ} (h : a ≤ b) : P a ≤ P b := Real.rpow_le_rpow_of_exponent_le hx h
  have one : P 1=X := Real.rpow_one _
  let q := ⌊P (1/1000000)⌋₊
  let M := (2+2*B)*((D+1 : ℕ) : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hD : (1 : ℝ) ≤ ((D+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos D
  have hj (v : ℕ) : |innerJump D v| ≤ M := by
    apply (innerJump_pointwise_bound D v).trans
    dsimp [M]; linarith only [hmass (D+1) (Nat.succ_pos D),hD]
  have term (v : ℕ) (hv : v ∈ Icc 1 q) :
      |innerJump D v*∑ p ∈ squareRootWindowPrimes F L U v,
        Real.log p*centeredPrimeWeight R (X/v/p)| ≤ M*(K*P (4997/10000)) := by
    obtain ⟨hv₁,hvq⟩ := mem_Icc.mp hv
    have hv₀ : (0 : ℝ) < v := by exact_mod_cast hv₁
    have hvX : (v : ℝ) ≤ P (1/1000000) := (by exact_mod_cast hvq : (v : ℝ) ≤ q).trans
      (Nat.floor_le (by dsimp [P]; positivity))
    have hvn : v ≤ X := by exact_mod_cast hvX.trans ((mono (by norm_num : (1/1000000 : ℝ) ≤ 1)).trans_eq one)
    let T := X/v
    have hT := (Nat.one_le_div_iff hv₁).mpr hvn
    have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have htx : (T : ℝ) ≤ X := by exact_mod_cast Nat.div_le_self X v
    have hquot : (X : ℝ) ≤ 2*T*(v : ℝ) := by
      have hh : X ≤ (T+1)*v := (Nat.lt_mul_div_succ X hv₁).le.trans_eq (Nat.mul_comm ..)
      have hle : T+1 ≤ 2*T := by dsimp only [T]; omega
      exact_mod_cast hh.trans (Nat.mul_le_mul_right v hle)
    have hscale : 2*(P (99999/100000)*(v : ℝ)) ≤ X := by
      have hh := mul_le_mul hlarge (mul_le_mul_of_nonneg_left hvX
        (by dsimp [P]; positivity : 0 ≤ P (99999/100000))) (by dsimp [P]; positivity)
        (by positivity)
      apply hh.trans
      change P (1/1000000)*(P (99999/100000)*P (1/1000000)) ≤ X
      rw [mul,mul,←one]; exact mono (by norm_num)
    have htlo : P (99999/100000) ≤ T := by
      have hh : P (99999/100000)*(v : ℝ) ≤ (T : ℝ)*v := by linarith only [hscale.trans hquot]
      exact le_of_mul_le_mul_right hh hv₀
    have lower_exp : (T : ℝ)^(49999/100000 : ℝ)*(v : ℝ) ≤ Real.sqrt X := by
      apply (mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg T) htx (by norm_num : (0 : ℝ) ≤ 49999/100000))
        hvX hv₀.le (by positivity)).trans
      change P (49999/100000)*P (1/1000000) ≤ Real.sqrt X
      rw [mul,Real.sqrt_eq_rpow]; exact mono (by norm_num)
    have hA : (T : ℝ)^(49999/100000 : ℝ) ≤ (L/v+1 : ℕ) := by
      have hh : L+1 ≤ (L/v+1)*v := (Nat.lt_mul_div_succ L hv₁).trans_eq (Nat.mul_comm ..)
      have hmul : (L : ℝ)+1 ≤ ((L/v+1 : ℕ) : ℝ)*v := by exact_mod_cast hh
      exact le_of_mul_le_mul_right ((lower_exp.trans hL).trans hmul) hv₀
    have divided {e f : ℝ} (hf : 0 ≤ f) (he : e ≤ 99999/100000*f) : P e ≤ (T : ℝ)^f :=
      ((mono he).trans_eq (powr _ _).symm).trans (Real.rpow_le_rpow (by dsimp [P]; positivity) htlo hf)
    have hright := hU.trans (divided (f := 50001/100000) (by norm_num) (by norm_num))
    have hup : ((U/v+1 : ℕ) : ℝ) ≤ 2*(T : ℝ)^(50001/100000 : ℝ) := by
      have hu : ((U/v : ℕ) : ℝ) ≤ U := by exact_mod_cast Nat.div_le_self U v
      push_cast; linarith only [hu,hright,Real.one_le_rpow ht (by norm_num : (0 : ℝ) ≤ 50001/100000)]
    have ht' := hprime R T (max (F+1) (L/v+1)) (U/v+1) hR hT
      ((show 1 ≤ F+1 from Nat.succ_pos F).trans (le_max_left ..)) (hr.trans (divided (by norm_num) (by norm_num)))
      (hA.trans (by exact_mod_cast (le_max_right (F+1) (L/v+1)))) hup
    rw [abs_mul]
    exact mul_le_mul (hj v) (ht'.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (Nat.cast_nonneg T) htx (by norm_num)) hK)) (abs_nonneg _) hM
  have hq : (q : ℝ) ≤ P (1/1000000) := Nat.floor_le (by dsimp [P]; positivity)
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum term).trans
  rw [sum_const,Nat.card_Icc,nsmul_eq_mul,show q+1-1=q by omega]
  have hsum := mul_le_mul_of_nonneg_right hq (by dsimp [P]; positivity : 0 ≤ M*(K*P (4997/10000)))
  apply hsum.trans_eq
  have id : P (1/1000000)*P (4997/10000)=P (499701/1000000) := (mul _ _).trans (by norm_num)
  change _=(2+2*B)*K*((D+1 : ℕ) : ℝ)*P (499701/1000000)
  rw [←id]; dsimp only [M]; ring

#print axioms short_complement_window_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
