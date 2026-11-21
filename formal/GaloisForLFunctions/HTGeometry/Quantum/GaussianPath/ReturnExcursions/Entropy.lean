import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw
import GaloisForLFunctions.HTGeometry.ContinuousPlateauGrid

/-! # Time-grid and circuit-net sizes at the full near-Hilbert gate budget -/
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions
noncomputable section

/-- Hilbert dimension pays for the quadratic Hamiltonian speed and the
polynomial overhead of the grid at every sufficiently large register size. -/
theorem dimension_dominates_speed {n : ℕ} (hn : 64 ≤ n) : 64*(n+1)^2 ≤ 2^n := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      _ ≤ 2*(64*(n+1)^2) := by nlinarith only [hn,Nat.zero_le ((n-1)^2),Nat.mul_le_mul_left n hn]
      _ ≤ 2*2^n := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ, Nat.mul_comm]

/-- At budget P the per-gate net needs at most 33N bits since both
N² and 1+16P fit in 2^N. -/
theorem full_budget_net_card {n : ℕ} (hn : 64 ≤ n) :
    (atMostQuarterCircuitNet n (nearHilbertContinuousCircuitBudget n)).card ≤
      2^(33*n*nearHilbertContinuousCircuitBudget n+n+1) := by
  let P := nearHilbertContinuousCircuitBudget n
  let D := 2^n
  have hD : 0 < D := by dsimp [D]; positivity
  have hbudget : 64*(n+1)*P ≤ D := Nat.mul_div_le _ _
  have hP : P+1 ≤ D := by
    have hh := Nat.mul_le_mul_right P (show 2 ≤ 64*(n+1) by omega)
    omega
  have hnn : n*n ≤ D := by
    have hh := dimension_dominates_speed hn
    change n*n ≤ 2^n
    nlinarith only [hh,Nat.zero_le n,Nat.zero_le (n*n)]
  have hbase (j : ℕ) (hj : j ≤ P) : 1+16*j ≤ D := by
    have hh := Nat.mul_le_mul_right P (show 32 ≤ 64*(n+1) by omega)
    omega
  have hterm (j : ℕ) (hj : j ≤ P) :
      1+((n*n:ℕ):ℝ)^j*(1+16*(j:ℝ))^(32*j) ≤ (2:ℝ)^(33*n*P+1) := by
    have ha : ((n*n:ℕ):ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hnn
    have hb : 1+16*(j:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast hbase j hj
    have hprod := mul_le_mul (pow_le_pow_left₀ (by positivity) ha j)
      (pow_le_pow_left₀ (by positivity) hb (32*j)) (by positivity) (by positivity)
    rw [← pow_mul,← pow_mul,← pow_add,show n*j+n*(32*j)=33*n*j by ring] at hprod
    have hcap := hprod.trans (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left (33*n) hj))
    have hone : 1 ≤ (2:ℝ)^(33*n*P) := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith only [hcap,hone]
  have hsum : atMostQuarterCircuitEntropyBound n P ≤ (2:ℝ)^(33*n*P+n+1) := calc
    _ ≤ ∑ _j ∈ Finset.range (P+1), (2:ℝ)^(33*n*P+1) :=
      Finset.sum_le_sum fun j hj => hterm j (by simpa using Finset.mem_range.mp hj)
    _ = (P+1:ℕ)*(2:ℝ)^(33*n*P+1) := by simp
    _ ≤ (2:ℝ)^n*(2:ℝ)^(33*n*P+1) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hP) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega
  exact_mod_cast (atMostQuarterCircuitNet_card_real_le n P).trans hsum

/-- A grid interval of 2^b time units and an inverse exceptional fraction
of 2^e fit simultaneously whenever b+e ≤ 7D/16. -/
theorem full_budget_grid_card {n b e : ℕ} (hn : 64 ≤ n) (hbe : 16*(b+e) ≤ 7*2^n) :
    (2:ℕ)^e * (plateauGridCount ((2:ℝ)^b) (1/(2:ℝ)^n) *
      (atMostQuarterCircuitNet n (nearHilbertContinuousCircuitBudget n)).card) ≤ 2^(2^n-1) := by
  let P := nearHilbertContinuousCircuitBudget n
  let D := 2^n
  have hpay : 64*(n+1)*P ≤ D := Nat.mul_div_le _ _
  have hD := dimension_dominates_speed hn
  have hroom : 64*(2*n+3) ≤ D := by
    apply le_trans _ hD
    have hh := Nat.mul_le_mul_left n hn
    nlinarith only [hh,hn]
  have hex : e+(b+n+1)+(33*n*P+n+1) ≤ D-1 := by
    have hnn : 64*(n*P) ≤ D := by nlinarith only [hpay,Nat.zero_le P]
    change 16*(b+e) ≤ 7*D at hbe
    rw [Nat.mul_assoc 33 n P]
    omega
  have hgrid : plateauGridCount ((2:ℝ)^b) (1/(2:ℝ)^n) ≤ 2^(b+n+1) := by
    unfold plateauGridCount
    rw [div_div_eq_mul_div,div_one,← pow_add]
    rw [show (2:ℝ)^(b+n) = ((2^(b+n):ℕ):ℝ) by norm_cast,Nat.ceil_natCast,pow_succ]
    have hp : 0 < (2:ℕ)^(b+n) := by positivity
    omega
  calc
    _ ≤ 2^e*(2^(b+n+1)*2^(33*n*P+n+1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hgrid (full_budget_net_card hn))
    _ = 2^(e+(b+n+1)+(33*n*P+n+1)) := by rw [← Nat.mul_assoc,← pow_add,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hex

end
end GaloisForLFunctions.HTGeometry.ReturnExcursions
