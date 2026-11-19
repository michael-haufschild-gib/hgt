import GaloisForLFunctions.RHTower.RouteECofactorSquarefreeHarmonic
import GaloisForLFunctions.RestrictedFactorizationCalculus.RecoveringTheMobiusPrefixFromAnIncreasingPrimeCutoff

/-!
# Inverting one weighted reading at a moving prime cutoff

At each endpoint only the weighted sum with its own frozen prime cutoff
is observed. Positive increasing weights retain enough mass at the unit
for partial summation to close an induction over all smaller endpoints.
Euler deletion then recovers the unrestricted Möbius prefix.
-/

noncomputable section

open Finset
open scoped Classical
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The same prime cutoff is applied to every summand, including at the unit. -/
def weightedFrozenPrefix (v : ℕ → ℝ) (y X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X,coprimeMoebiusIndicator (primorial y) n*v n

private abbrev row (y X : ℕ) := coprimeMoebiusSum (primorial y) X
private abbrev variation (v : ℕ → ℝ) (y N : ℕ) :=
  ∑ n ∈ Icc 1 N,row y n*(v (n+1)-v n)

private theorem partial_summation (v : ℕ → ℝ) (y N : ℕ) :
    row y (N+1)*v (N+1)=weightedFrozenPrefix v y (N+1)+variation v y N := by
  induction N with
  | zero => simp [row,coprimeMoebiusSum,weightedFrozenPrefix,variation]
  | succ N ih =>
    have sumstep : row y (N+1+1)=row y (N+1)+coprimeMoebiusIndicator (primorial y) (N+1+1) :=
      sum_Icc_succ_top (by omega) _
    have wstep : weightedFrozenPrefix v y (N+1+1)=weightedFrozenPrefix v y (N+1)+
        coprimeMoebiusIndicator (primorial y) (N+1+1)*v (N+1+1) :=
      sum_Icc_succ_top (by omega) _
    have vstep : variation v y (N+1)=variation v y N+row y (N+1)*(v (N+1+1)-v (N+1)) :=
      sum_Icc_succ_top (by omega) _
    rw [sumstep,wstep,vstep]
    linarith only [ih]

private theorem variation_bound (v : ℕ → ℝ) (hv : Monotone v) (y N : ℕ) {H : ℝ}
    (h : ∀ k,1 ≤ k → k ≤ N → |row y k| ≤ H) :
    |variation v y N| ≤ H*(v (N+1)-v 1) := by
  induction N with
  | zero => simp [variation]
  | succ N ih =>
    have small := ih (fun k hk hl => h k hk (Nat.le_succ_of_le hl))
    have dn := sub_nonneg.mpr (hv (Nat.le_succ (N+1)))
    have last := mul_le_mul_of_nonneg_right (h (N+1) (Nat.succ_pos _) le_rfl) dn
    have step : variation v y (N+1)=variation v y N+row y (N+1)*(v (N+1+1)-v (N+1)) :=
      sum_Icc_succ_top (by omega) _
    rw [step]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_of_nonneg dn]
    linarith only [small,last]

/-- At square-root size the full logarithmic variation costs a constant
multiple of the endpoint price. Only strictly smaller rows are used. -/
theorem critical_variation_of_the_frozen_logarithmic_row (y X : ℕ) {H : ℝ} (hH : 0 ≤ H)
    (rows : ∀ k,k<X → |row y k| ≤ H*Real.sqrt k) :
    |row y X*Real.log X-weightedFrozenPrefix (fun k => Real.log k) y X| ≤ 2*H*Real.sqrt X := by
  cases X with
  | zero => simp [row,coprimeMoebiusSum,weightedFrozenPrefix]
  | succ N =>
    let v := fun k : ℕ => Real.log k
    rw [partial_summation v y N,add_sub_cancel_left]
    have step (k : ℕ) (hk : k ∈ Icc 1 N) :
        |row y k*(v (k+1)-v k)| ≤ H*(Real.sqrt k)⁻¹ := by
      have kp : (0:ℝ)<k := Nat.cast_pos.mpr (mem_Icc.mp hk).1
      have sk := Real.sqrt_pos.mpr kp
      have dk : 0 ≤ v (k+1)-v k := sub_nonneg.mpr (Real.log_le_log kp (Nat.cast_le.mpr (Nat.le_succ k)))
      have price := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0<(k:ℝ)+1) kp)
      rw [Real.log_div (by positivity : (k:ℝ)+1 ≠ 0) kp.ne'] at price
      have diff : v (k+1)-v k ≤ (k:ℝ)⁻¹ := by
        change Real.log (k+1:ℕ)-Real.log k ≤ _
        rw [Nat.cast_add,Nat.cast_one]
        exact price.trans_eq (by field_simp)
      rw [abs_mul,abs_of_nonneg dk]
      apply (mul_le_mul (rows k (Nat.lt_succ_of_le (mem_Icc.mp hk).2)) diff dk
        (mul_nonneg hH sk.le)).trans_eq
      have sq := Real.mul_self_sqrt kp.le
      calc H*Real.sqrt k*(k:ℝ)⁻¹ = H*(Real.sqrt k/(k:ℝ)) := by ring
           _ = _ := by congr 1; field_simp [kp.ne',sk.ne']; linarith only [sq]
    apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum step).trans ?_)
    rw [←mul_sum]
    have cap := (RHTower.Sieve.sum_sqrtInv_le N).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.le_succ N))) (by norm_num))
    exact (mul_le_mul_of_nonneg_left cap hH).trans_eq (by ring)

/-- A diagonal estimate may use strictly smaller rows at the same
prime wall. Monotone endpoint prices propagate to every higher wall
with precisely one finite Euler product. -/
theorem induction_above_a_moving_prime_cutoff (b : ℕ → ℕ) (hb : Monotone b)
    (A : ℕ → ℝ) (ha : Monotone A) (nonneg : ∀ n,0 ≤ A n) {s : ℝ} (hs : 0<s)
    (base : ∀ n,0<n →
      (∀ k,k<n → |row (b n) k| ≤ A k*deletionPrice s (b n)*(k:ℝ)^s) →
        |row (b n) n| ≤ A n*deletionPrice s (b n)*(n:ℝ)^s)
    (n y : ℕ) (hy : b n ≤ y) :
    |row y n| ≤ A n*deletionPrice s y*(n:ℝ)^s := by
  induction n using Nat.strong_induction_on generalizing y with
  | h n ih =>
    by_cases zero : n=0
    · simp [zero,row,coprimeMoebiusSum,Real.zero_rpow hs.ne']
    have np := Nat.pos_of_ne_zero zero
    induction y,hy using Nat.le_induction with
    | base => exact base n np (fun k hk => ih k hk (b n) (hb hk.le))
    | succ y hy prior =>
      apply extend_bound_across_one_prime_cutoff hs (nonneg n) y n prior
      intro hp
      have small := Nat.div_lt_self np hp.one_lt
      have high := (hb small.le).trans (hy.trans (Nat.le_succ _))
      exact (ih _ small (y+1) high).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ha small.le) (zero_le_one.trans (deletionPrice_one_le hs _)))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- A bound at the single frozen, weighted reading at each endpoint
controls every higher unweighted prime cutoff for that endpoint. -/
theorem all_higher_rows_from_one_weighted_reading (b : ℕ → ℕ) (hb : Monotone b)
    (v : ℕ → ℝ) (hv : Monotone v) (unit : 0<v 1) {s C : ℝ} (hs : 0<s) (hC : 0 ≤ C)
    (reading : ∀ n,|weightedFrozenPrefix v (b n) n| ≤ C*v 1*(n:ℝ)^s)
    (n y : ℕ) (hy : b n ≤ y) :
    |row y n| ≤ C*deletionPrice s y*(n:ℝ)^s := by
  apply induction_above_a_moving_prime_cutoff b hb (fun _ => C) (fun _ _ _ => le_rfl) (fun _ => hC) hs _ n y hy
  intro n np ih
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero np.ne'
  let X := N+1
  let y := b X
  let H := C*deletionPrice s y*(X:ℝ)^s
  have E := deletionPrice_one_le hs y
  have cap (k : ℕ) (_ : 1 ≤ k) (hk : k ≤ N) : |row y k| ≤ H := by
    have lt : k<X := by dsimp only [X]; omega
    have smaller := ih k lt
    exact smaller.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr lt.le) hs.le)
      (mul_nonneg hC (zero_le_one.trans E)))
  have price := variation_bound v hv y N cap
  have diag := reading X
  have enough : C*v 1*(X:ℝ)^s ≤ H*v 1 := by
    have bound := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC E)
      (Real.rpow_nonneg (Nat.cast_nonneg X) s)
    calc _ = C*(X:ℝ)^s*v 1 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right bound unit.le
  have vx : 0<v X := unit.trans_le (hv (Nat.succ_pos N))
  have iden := congrArg abs (partial_summation v y N)
  have tri := abs_add_le (weightedFrozenPrefix v y X) (variation v y N)
  change |row y X*v X|=_ at iden
  rw [abs_mul,abs_of_pos vx] at iden
  change |row y X| ≤ H
  apply le_of_mul_le_mul_right _ vx
  change |variation v y N| ≤ H*(v X-v 1) at price
  linarith only [iden,tri,diag.trans enough,price]

/-- Two finite Euler products recover the full unweighted prefix from
one increasing weight and one moving prime cutoff. -/
theorem full_prefix_from_one_weighted_reading (b : ℕ → ℕ) (hb : Monotone b)
    (v : ℕ → ℝ) (hv : Monotone v) (unit : 0<v 1) {s C : ℝ} (hs : 0<s) (hC : 0 ≤ C)
    (reading : ∀ n,|weightedFrozenPrefix v (b n) n| ≤ C*v 1*(n:ℝ)^s) (X : ℕ) :
    |coprimeMoebiusSum 1 X| ≤ C*(deletionPrice s (b X))^2*(X:ℝ)^s := by
  let y := b X
  have rows (n : ℕ) (hn : n ≤ X) : |row y n| ≤ C*deletionPrice s y*(n:ℝ)^s :=
    all_higher_rows_from_one_weighted_reading b hb v hv unit hs hC reading n y (hb hn)
  have res := restore_full_row_from_prime_cutoff hs X y
    (mul_nonneg hC (zero_le_one.trans (deletionPrice_one_le hs y))) rows
  change |row 0 X| ≤ _ at res
  rw [show row 0 X=coprimeMoebiusSum 1 X by simp [row]] at res
  exact res.trans_eq (by dsimp only [y]; ring)

/-- In the forward direction a frozen weighted reading costs at most
the final weight and one Euler product. -/
theorem weighted_reading_from_full_prefix (v : ℕ → ℝ) (hv : Monotone v) (unit : 0 ≤ v 1)
    {s C : ℝ} (hs : 0<s) (hC : 0 ≤ C) (h : ∀ n,|coprimeMoebiusSum 1 n| ≤ C*(n:ℝ)^s)
    (y X : ℕ) :
    |weightedFrozenPrefix v y X| ≤ 4*C*deletionPrice s y*(X:ℝ)^s*v X := by
  cases X with
  | zero => simp [weightedFrozenPrefix,Real.zero_rpow hs.ne']
  | succ N =>
    let X := N+1
    let H := 2*C*deletionPrice s y*(X:ℝ)^s
    have H0 : 0 ≤ H := mul_nonneg (mul_nonneg (by positivity)
      (zero_le_one.trans (deletionPrice_one_le hs _))) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have cap (k : ℕ) (hk : k ≤ X) : |row y k| ≤ H :=
      (all_frozen_rows_from_full_prefix hs hC h k y).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg k) (Nat.cast_le.mpr hk) hs.le)
          (mul_nonneg (by positivity) (zero_le_one.trans (deletionPrice_one_le hs _))))
    have paid := variation_bound v hv y N (fun k _ hk => cap _ (Nat.le_succ_of_le hk))
    have vx := unit.trans (hv (Nat.succ_pos N))
    have iden := partial_summation v y N
    have eq : weightedFrozenPrefix v y X=row y X*v X-variation v y N := by linarith only [iden]
    rw [eq]
    apply (abs_sub ..).trans
    rw [abs_mul,abs_of_nonneg vx]
    have a := mul_le_mul_of_nonneg_right (cap X le_rfl) vx
    have bnd := paid.trans (mul_le_mul_of_nonneg_left (sub_le_self (v X) unit) H0)
    calc _ ≤ H*v X+H*v X := add_le_add a bnd
         _ = _ := by dsimp only [H,X]; ring

#print axioms full_prefix_from_one_weighted_reading
#print axioms weighted_reading_from_full_prefix

end GaloisForLFunctions.RestrictedFactorizationCalculus
