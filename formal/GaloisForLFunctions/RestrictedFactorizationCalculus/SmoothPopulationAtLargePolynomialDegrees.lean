import GaloisForLFunctions.RestrictedFactorizationCalculus.PositiveSmoothPopulationOnEveryPolynomialBand

/-!
# The large-degree cost of a positive smooth population

Choosing a prime-extraction step of size r/(r+1) with r near log j
bounds the loss on the whole interval Z ≤ y^j by (C j log(j+1))^j.
The multiplicative constant C is absolute.
-/
noncomputable section
open Filter Finset
open scoped Topology Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev stepSize (j : ℕ) := ⌈Real.log ((j:ℝ)+1)⌉₊
private abbrev steps (j : ℕ) := j+j/stepSize j+1

/-- The explicit denominator in the smooth-population lower bound. -/
def polynomialSmoothPrice (j : ℕ) : ℝ := (48*Real.exp 16*(j:ℝ)*Real.log ((j:ℝ)+1))^j

private theorem log_wall {j : ℕ} (hj : 8 ≤ j) :
    1 ≤ Real.log ((j:ℝ)+1) ∧ Real.log ((j:ℝ)+1) ≤ (j:ℝ) := by
  have J : (8:ℝ) ≤ j := by exact_mod_cast hj
  have t := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
  have four : Real.log ((2:ℝ)^2) ≤ Real.log ((j:ℝ)+1) :=
    Real.log_le_log (by positivity) (by linarith only [J])
  rw [Real.log_pow] at four
  norm_num at t four
  exact ⟨by linarith only [t,four],by simpa using Real.log_le_sub_one_of_pos (by positivity : 0 < (j:ℝ)+1)⟩

private theorem step_cost {j : ℕ} (hj : 8 ≤ j) :
    (8*(stepSize j:ℝ))^(steps j)*((steps j).factorial:ℝ) ≤ polynomialSmoothPrice j := by
  let J : ℝ := j
  let L := Real.log (J+1)
  let r := stepSize j
  let k := steps j
  have jp : 0 < J := Nat.cast_pos.mpr (by omega)
  obtain ⟨L1,Lj⟩ := log_wall hj
  change 1 ≤ L at L1
  change L ≤ J at Lj
  have Lp := zero_lt_one.trans_le L1
  have rlo : L ≤ (r:ℝ) := Nat.le_ceil _
  have r1 := L1.trans rlo
  have rp := Lp.trans_le rlo
  have rhi : (r:ℝ) ≤ 2*L := by
    have h : (r:ℝ) < L+1 := Nat.ceil_lt_add_one Lp.le
    linarith only [h,L1]
  have kpos : 0 < k := Nat.succ_pos _
  have kp : 0 < (k:ℝ) := Nat.cast_pos.mpr kpos
  have k1 : (1:ℝ) ≤ k := Nat.one_le_cast.mpr kpos
  have ks : (k:ℝ) ≤ J+2*J/L := by
    have floor : ((j/r:ℕ):ℝ) ≤ J/L :=
      Nat.cast_div_le.trans (div_le_div_of_nonneg_left jp.le Lp rlo)
    have u : 1 ≤ J/L := (one_le_div Lp).mpr Lj
    change ((j+j/r+1:ℕ):ℝ) ≤ _
    push_cast
    change J+((j/r:ℕ):ℝ)+1 ≤ _
    linarith only [floor,u, show 2*J/L=J/L+J/L by ring]
  have k3 : (k:ℝ) ≤ 3*J := by
    have u : J/L ≤ J := div_le_self jp.le L1
    linarith only [ks,u,show 2*J/L=J/L+J/L by ring]
  let A := 8*(r:ℝ)*k
  let B := 48*J*L
  have A1 : 1 ≤ A := by
    change 1 ≤ (8:ℝ)*r*k
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) r1) k1
  have Ap := zero_lt_one.trans_le A1
  have Bp : 0 < B := by dsimp only [B];positivity
  have AB : A ≤ B := (mul_le_mul (mul_le_mul_of_nonneg_left rhi (by norm_num : (0:ℝ) ≤ 8))
    k3 kp.le (by positivity)).trans_eq (by dsimp only [B];ring)
  have logs := Real.log_le_log Ap AB
  have six : Real.log 48 ≤ 6 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<48) (by norm_num : (48:ℝ)≤2^6)
    rw [Real.log_pow] at h
    have two := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h two
    linarith only [h,two]
  have logJ : Real.log J ≤ L := Real.log_le_log jp (by linarith)
  have logL := Real.log_le_sub_one_of_pos Lp
  have size : Real.log A ≤ 8*L := by
    change Real.log A ≤ Real.log (48*J*L) at logs
    rw [Real.log_mul (by positivity) Lp.ne',Real.log_mul (by norm_num) jp.ne'] at logs
    linarith only [logs,six,logJ,logL,L1]
  have main : (k:ℝ)*Real.log A ≤ J*(Real.log B+16) := by
    have bound := mul_le_mul_of_nonneg_right ks (Real.log_nonneg A1)
    have left := mul_le_mul_of_nonneg_left logs jp.le
    have right := mul_le_mul_of_nonneg_left size (by positivity : 0 ≤ 2*J/L)
    rw [add_mul] at bound
    rw [show 2*J/L*(8*L)=16*J by field_simp [Lp.ne']; ring] at right
    linarith only [bound,left,right]
  have price : A^k ≤ (B*Real.exp 16)^j := by
    apply (Real.log_le_log_iff (pow_pos Ap _) (pow_pos (mul_pos Bp (Real.exp_pos _)) _)).mp
    rw [Real.log_pow,Real.log_pow,Real.log_mul Bp.ne' (Real.exp_pos _).ne',Real.log_exp]
    exact main
  have fact : ((k.factorial:ℕ):ℝ) ≤ (k:ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
  calc
    _ ≤ (8*(r:ℝ))^k*(k:ℝ)^k := mul_le_mul_of_nonneg_left fact (by positivity)
    _ = A^k := (mul_pow ..).symm
    _ ≤ _ := price.trans_eq (by unfold polynomialSmoothPrice;congr 1;dsimp only [B,J,L];ring)

/-- At every fixed degree j≥8, sufficiently large prime walls leave at
least Z/(C j log(j+1))^j smooth numbers through every Z≤y^j, with the
same absolute C at all degrees. -/
theorem smooth_population_at_large_degrees {j : ℕ} (hj : 8 ≤ j) :
    ∀ᶠ y : ℕ in atTop,∀ Z : ℕ,Z ≤ y^j →
      (Z:ℝ) ≤ polynomialSmoothPrice j*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card := by
  let r := stepSize j
  let k := steps j
  have r1 : (1:ℝ) ≤ r := (log_wall hj).1.trans (Nat.le_ceil _)
  have rp : 0 < r := Nat.one_le_cast.mp r1
  have cover : j*(r+1) ≤ k*r := by
    have rem := Nat.mod_lt j rp
    have eq := Nat.mod_add_div j r
    have step : j ≤ j/r*r+r := by rw [Nat.mul_comm (j/r) r];omega
    change j*(r+1) ≤ (j+j/r+1)*r
    simpa only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.add_assoc] using Nat.add_le_add_left step (j*r)
  filter_upwards [smooth_population_at_factorial_price r k rp,eventually_ge_atTop (1:ℕ)] with y pop yp
  intro Z range
  have qr : Z^(r+1) ≤ y^(k*r) :=
    (Nat.pow_le_pow_left range _).trans ((pow_mul y j (r+1)).symm.le.trans (Nat.pow_le_pow_right yp cover))
  have den : 0 < (8*(r:ℝ))^k*(k.factorial:ℝ) := by
    have := Nat.factorial_pos k;positivity
  have fract := pop Z qr
  rw [one_div_mul_eq_div,div_le_iff₀ den] at fract
  exact fract.trans ((mul_comm ..).le.trans
    (mul_le_mul_of_nonneg_right (step_cost hj) (Nat.cast_nonneg _)))

end GaloisForLFunctions.RestrictedFactorizationCalculus
