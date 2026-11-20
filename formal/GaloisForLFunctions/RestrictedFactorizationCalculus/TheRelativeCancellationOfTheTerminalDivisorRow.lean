import GaloisForLFunctions.RestrictedFactorizationCalculus.TheTerminalAtomOfTheRoughInterior
import GaloisForLFunctions.RHTower.RouteEForbiddenSupportStability

/-!
# Relative cancellation in the terminal divisor row

The ratio of the signed magnitude to the absolute mass is invariant under
negating the exponent. At the log-square wall it tends uniformly to one
for all exponents of magnitude at least one half. The endpoint estimate
uses the logarithmic budget of the distinct prime divisors.
-/
noncomputable section
open Finset Filter
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Magnitude of the exact reading divided by the total possible absolute error
when each weighted coordinate may change by its own magnitude. -/
def terminalCancellationRatio (y n : ℕ) (s : ℝ) : ℝ :=
  |∑ q∈Icc 1 n,(q:ℝ)^s*interiorKernel y n (n-1) q| /
    ∑ q∈Icc 1 n,(q:ℝ)^s*|interiorKernel y n (n-1) q|

/-- Contribution of one surviving prime to the cancellation ratio. -/
def terminalPrimeFactor (u : ℝ) (p : ℕ) := (1-(p:ℝ)^(-u))/(1+(p:ℝ)^(-u))

private theorem raw_factor {p : ℕ} (hp : 1 ≤ p) (s : ℝ) :
    |1-(p:ℝ)^(-s)| / (1+(p:ℝ)^(-s))=terminalPrimeFactor |s| p := by
  have one : (1:ℝ) ≤ p := Nat.one_le_cast.mpr hp
  have pp := zero_lt_one.trans_le one
  rcases le_total 0 s with up|down
  · simp only [terminalPrimeFactor,abs_of_nonneg up,abs_of_nonneg (sub_nonneg.mpr
      (Real.rpow_le_one_of_one_le_of_nonpos one (neg_nonpos.mpr up)))]
  · rw [abs_of_nonpos down,terminalPrimeFactor,neg_neg,abs_of_nonpos (sub_nonpos.mpr
      (Real.one_le_rpow one (neg_nonneg.mpr down))),Real.rpow_neg pp.le]
    have pos := Real.rpow_pos_of_pos pp s
    field_simp [pos.ne',(by positivity : 1+(p:ℝ)^s ≠ 0)]
    ring

/-- The cancellation ratio factors prime by prime and depends only on the
absolute value of the weight exponent. -/
theorem terminal_cancellation_euler_product (y : ℕ) {n : ℕ} (np : 0 < n) (s : ℝ) :
    terminalCancellationRatio y n s =
      ∏ p∈n.primeFactors.filter (y < ·),terminalPrimeFactor |s| p := by
  obtain ⟨sgn,tot⟩ := terminal_signed_and_absolute_products y np s
  rw [terminalCancellationRatio,sgn,tot,abs_mul,abs_of_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr np) s),
    mul_div_mul_left _ _ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr np) s).ne',abs_prod,←prod_div_distrib]
  exact prod_congr rfl fun p hp => raw_factor (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos s

/-- The loss from one prime factor is at most twice its reciprocal weight. -/
theorem terminal_prime_factor_bounds {u : ℝ} (up : 0 ≤ u) {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ terminalPrimeFactor u p ∧ terminalPrimeFactor u p ≤ 1 ∧ 1-terminalPrimeFactor u p ≤ 2*(p:ℝ)^(-u) := by
  let w := (p:ℝ)^(-u)
  have w0 : 0 ≤ w := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have w1 : w ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.mpr hp) (neg_nonpos.mpr up)
  have den : 0 < 1+w := by positivity
  change 0 ≤ (1-w)/(1+w) ∧ (1-w)/(1+w) ≤ 1 ∧ 1-(1-w)/(1+w) ≤ 2*w
  refine ⟨div_nonneg (sub_nonneg.mpr w1) den.le,(div_le_one den).mpr (by linarith only [w0]),?_⟩
  rw [show 1-(1-w)/(1+w)=2*w/(1+w) by field_simp;ring]
  exact div_le_self (by positivity) (le_add_of_nonneg_right w0)

private theorem product_loss (S : Finset ℕ) {u : ℝ} (up : 0 ≤ u) (prime : ∀ p∈S,1 ≤ p) :
    1-∏ p∈S,terminalPrimeFactor u p ≤ 2*∑ p∈S,(p:ℝ)^(-u) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have members : ∀ q∈S,1 ≤ q := fun _ hq => prime _ (mem_insert_of_mem hq)
    obtain ⟨_,p1,loss⟩ := terminal_prime_factor_bounds up (prime _ (mem_insert_self ..))
    have upper := Finset.prod_le_one (fun q hq => (terminal_prime_factor_bounds up (members q hq)).1)
      (fun q hq => (terminal_prime_factor_bounds up (members q hq)).2.1)
    rw [prod_insert hp,sum_insert hp]
    nlinarith only [loss,ih members,mul_nonneg (sub_nonneg.mpr p1) (sub_nonneg.mpr upper)]

/-- A finite bound valid at any prime wall above one. -/
theorem terminal_cancellation_price {y n : ℕ} (hy : 1 < y) (np : 0 < n) (s : ℝ) :
    0 ≤ 1-terminalCancellationRatio y n s ∧
    1-terminalCancellationRatio y n s ≤ 2*((Real.log n)/(Real.log y))*(y:ℝ)^(-|s|) := by
  let S := n.primeFactors.filter (y < ·)
  have room (p : ℕ) (hp : p∈S) : (y:ℝ) ≤ p := Nat.cast_le.mpr (mem_filter.mp hp).2.le
  have yp : (1:ℝ) < y := by exact_mod_cast hy
  have prime (p : ℕ) (hp : p∈S) := (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos
  have card := _root_.RHTower.ForbiddenSupport.card_le_log_div_log np.ne' (filter_subset ..) yp room
  rw [terminal_cancellation_euler_product y np]
  change 0 ≤ 1-∏ p∈S,terminalPrimeFactor |s| p ∧ _
  refine ⟨sub_nonneg.mpr (Finset.prod_le_one (fun q hq => (terminal_prime_factor_bounds (abs_nonneg s) (prime q hq)).1)
    (fun q hq => (terminal_prime_factor_bounds (abs_nonneg s) (prime q hq)).2.1)),?_⟩
  have top := sum_le_sum (fun p (hp : p∈S) =>
    Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans yp) (room p hp) (neg_nonpos.mpr (abs_nonneg s)))
  simp only [sum_const,nsmul_eq_mul] at top
  exact (product_loss S (abs_nonneg s) prime).trans
    ((mul_le_mul_of_nonneg_left (top.trans (mul_le_mul_of_nonneg_right card
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (by norm_num : (0:ℝ) ≤ 2)).trans_eq (mul_assoc ..).symm)

private theorem wall_endpoint (n : ℕ) {s : ℝ} (hs : 1/2 ≤ |s|) (np : 0 < n)
    (hy : 1 < logSquareCutoff n) :
    1-terminalCancellationRatio (logSquareCutoff n) n s ≤ 4/Real.log (logSquareCutoff n) := by
  let L := ⌊Real.log ((n:ℝ)+1)⌋₊
  let y := logSquareCutoff n
  change 1-terminalCancellationRatio y n s ≤ 4/Real.log (y:ℝ)
  have L1 : 1 ≤ L := by
    change 1 < L^2 at hy
    by_contra! bad
    have hz : L=0 := by omega
    simp [hz] at hy
  have Lp : 0 < (L:ℝ) := Nat.cast_pos.mpr L1
  have yr : (y:ℝ)=(L:ℝ)^2 := Nat.cast_pow ..
  have y1 : 1 < (y:ℝ) := by exact_mod_cast hy
  have price := (terminal_cancellation_price hy np s).2
  have floor := Nat.lt_floor_add_one (Real.log ((n:ℝ)+1))
  have logle := (Real.log_le_log (Nat.cast_pos.mpr np) (by linarith : (n:ℝ) ≤ n+1)).trans floor.le
  have log2L : Real.log n ≤ 2*(L:ℝ) := by
    change Real.log n ≤ (L:ℝ)+1 at logle
    have one : (1:ℝ) ≤ L := Nat.one_le_cast.mpr L1
    linarith only [logle,one]
  have pow := Real.rpow_le_rpow_of_exponent_le y1.le (neg_le_neg hs)
  have eq : (y:ℝ)^(-(1/2:ℝ))=(L:ℝ)⁻¹ := by
    rw [yr,Real.rpow_neg (sq_nonneg _),←Real.sqrt_eq_rpow,Real.sqrt_sq Lp.le]
  rw [eq] at pow
  have den := Real.log_pos y1
  have logs := div_le_div_of_nonneg_right log2L den.le
  have estimate := mul_le_mul (mul_le_mul_of_nonneg_left logs (by norm_num : (0:ℝ) ≤ 2)) pow
    (Real.rpow_nonneg (Nat.cast_nonneg y) _) (by positivity)
  exact price.trans (estimate.trans_eq (by field_simp [Lp.ne',den.ne']; norm_num))

/-- At the actual log-square cutoff the terminal row loses a vanishing
fraction of its unsigned mass, uniformly up to the half-power endpoint
on both sides of zero. -/
theorem terminal_half_power_uniform_cancellation {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,∀ s : ℝ,1/2 ≤ |s| →
      |terminalCancellationRatio (logSquareCutoff n) n s-1| < ε := by
  have grows := Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp logSquareCutoff_tendsto_atTop)
  filter_upwards [grows.eventually_gt_atTop (4/ε),eventually_ge_atTop (1:ℕ),
    logSquareCutoff_tendsto_atTop.eventually_ge_atTop 2] with n lg np hy s hs
  have y1 : 1 < logSquareCutoff n := hy
  have pos := Real.log_pos (show 1 < (logSquareCutoff n:ℝ) by exact_mod_cast y1)
  rw [abs_sub_comm,abs_of_nonneg (terminal_cancellation_price y1 np s).1]
  apply (wall_endpoint n hs np y1).trans_lt
  apply (div_lt_iff₀ pos).mpr
  change 4/ε < Real.log (logSquareCutoff n) at lg
  exact ((div_lt_iff₀ ep).mp lg).trans_eq (mul_comm ..)

end GaloisForLFunctions.RestrictedFactorizationCalculus
