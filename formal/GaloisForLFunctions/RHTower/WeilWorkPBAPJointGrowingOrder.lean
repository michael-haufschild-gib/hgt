import GaloisForLFunctions.RHTower.WeilWorkPBAPJointGridGeometry
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointShortPrefix
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSchedule
import GaloisForLFunctions.RHTower.Sieve.MertensFirst

/-!
# Growing derivative orders on the actual PBAP short interval

The corpus ratio-window theorem selects an order throughout
`exp L / sqrt L <= t <= exp ((c * log (log L) + 1) * L)`.
The factorial endpoint cost, interval length and both landing-window
inequalities are proved at the literal width `b * L * log (log L) * exp (-L/2)`.
No numerical budget is supplied to the final schedule or prefix theorem.

The resulting prefix saving is explicit in `1 - c * log 2`; positivity
of that exponent is needed only when using its decay. This is a supporting
estimate for the uniform-profile certificate, not full PBAP positivity.
-/

open Real Set Filter Topology
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- The actual order cap for a growing frequency ceiling. -/
def jointUniformOrder (c L : ℝ) : ℕ := ⌈c*log (log L)+1⌉₊+1

theorem eventually_jointUniformOrder_bounds {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ jointUniformOrder c L ∧
      c*log (log L)+2 ≤ (jointUniformOrder c L:ℝ) ∧
      (jointUniformOrder c L:ℝ) ≤ c*log (log L)+3 := by
  filter_upwards [(tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (0:ℝ)]
    with L hL
  change 0 ≤ log (log L) at hL
  have hlo := Nat.le_ceil (c*log (log L)+1)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ c*log (log L)+1 by positivity)
  have hlo' : c*log (log L)+2 ≤ (jointUniformOrder c L:ℝ) := by
    dsimp only [jointUniformOrder]
    push_cast
    linarith
  have hhi' : (jointUniformOrder c L:ℝ) ≤ c*log (log L)+3 := by
    dsimp only [jointUniformOrder]
    push_cast
    linarith
  refine ⟨?_, hlo', hhi'⟩
  exact_mod_cast (show (2:ℝ) ≤ jointUniformOrder c L by nlinarith)

theorem eventually_jointUniformOrder_power {c q : ℝ} (hc : 0 < c) (hq : 1 ≤ q) :
    ∀ᶠ L : ℝ in atTop, q^(jointUniformOrder c L) ≤ q^3*(log L)^(c*log q) := by
  filter_upwards [eventually_jointUniformOrder_bounds hc, eventually_gt_atTop (1:ℝ)]
    with L hk hL
  have hq0 : 0 < q := by linarith
  have hlogq : 0 ≤ log q := log_nonneg hq
  have he3 : exp (3*log q) = q^3 := by
    calc
      _ = (exp (log q))^3 := Real.exp_nat_mul _ 3
      _ = q^3 := by rw [exp_log hq0]
  calc
    _ = exp ((jointUniformOrder c L:ℝ)*log q) := by
      rw [Real.exp_nat_mul, exp_log hq0]
    _ ≤ exp ((c*log (log L)+3)*log q) :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk.2.2 hlogq)
    _ = q^3*(log L)^(c*log q) := by
      rw [show (c*log (log L)+3)*log q = 3*log q+log (log L)*(c*log q) by ring,
        exp_add, he3, Real.rpow_def_of_pos (log_pos hL)]

theorem eventually_jointUniformOrder_two_pow {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, (2:ℝ)^(jointUniformOrder c L) ≤ 8*(log L)^(c*log 2) := by
  simpa only [show (2:ℝ)^3 = 8 by norm_num] using
    (eventually_jointUniformOrder_power hc (by norm_num : (1:ℝ) ≤ 2))

theorem eventually_jointUniformOrder_four_pow_sqrt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, (4:ℝ)^(jointUniformOrder c L) ≤ sqrt L := by
  have ht := (isLittleO_log_rpow_rpow_atTop (c*log 4) (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
  have ht' : Tendsto (fun L : ℝ => 64*(log L)^(c*log 4)/sqrt L) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, mul_zero, mul_div_assoc] using ht.const_mul 64
  have hsmall := ht'.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hsmall, eventually_jointUniformOrder_power hc (by norm_num : (1:ℝ) ≤ 4),
    eventually_gt_atTop (0:ℝ)] with L hs hk hL
  have hroot := sqrt_pos.mpr hL
  have hh := (div_lt_iff₀ hroot).mp hs
  norm_num only [show (4:ℝ)^3 = 64 by norm_num, one_mul] at hk hh
  exact hk.trans hh.le

private theorem log_order_factorial_le {k : ℕ} (hk : 1 ≤ k) :
    log ((4:ℝ)^k*(Nat.factorial (k-1):ℝ)) ≤ (log 4+1)*(k:ℝ)^2 := by
  have hfpos : (0:ℝ) < (Nat.factorial (k-1):ℝ) := by exact_mod_cast Nat.factorial_pos (k-1)
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hm0 : (0:ℝ) ≤ (k-1:ℕ) := Nat.cast_nonneg _
  have hm : ((k-1:ℕ):ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have hf := Sieve.log_factorial_le (k-1)
  have hl := mul_le_mul_of_nonneg_left (log_le_self hm0) hm0
  have hs : ((k-1:ℕ):ℝ)^2 ≤ (k:ℝ)^2 := by nlinarith
  have hfour : (k:ℝ)*log 4 ≤ (k:ℝ)^2*log 4 :=
    mul_le_mul_of_nonneg_right (by nlinarith) (log_nonneg (by norm_num))
  rw [log_mul (by positivity) hfpos.ne', log_pow]
  nlinarith

private theorem order_log_majorant_tendsto (c : ℝ) :
    Tendsto (fun L : ℝ => (log 4+1)*(c*log L+3)^2/L) atTop (𝓝 0) := by
  have h2 : Tendsto (fun L : ℝ => (log L)^2/L) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero] using tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 : Tendsto (fun L : ℝ => log L/L) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero, pow_one] using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h0 : Tendsto (fun L : ℝ => 9/L) atTop (𝓝 0) := tendsto_id.const_div_atTop 9
  have h := (((h2.const_mul (c^2)).add (h1.const_mul (6*c))).add h0).const_mul (log 4+1)
  have he : (fun L : ℝ => (log 4+1)*(c*log L+3)^2/L) =
      fun L : ℝ => (log 4+1)*(c^2*((log L)^2/L)+(6*c)*(log L/L)+9/L) := by
    funext L
    ring
  rw [he]
  simpa only [mul_zero, add_zero] using h

/-- The actual growing factorial cost is subexponential in separation. -/
theorem eventually_jointUniformOrder_factorial {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, (4:ℝ)^(jointUniformOrder c L)*
      (Nat.factorial (jointUniformOrder c L-1):ℝ) ≤ exp (L/2) := by
  have hsmall := (order_log_majorant_tendsto c).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  filter_upwards [hsmall, eventually_jointUniformOrder_bounds hc,
    eventually_gt_atTop (1:ℝ)] with L hs hk hL
  have hL0 : 0 < L := by linarith
  have hK : (jointUniformOrder c L:ℝ) ≤ c*log L+3 :=
    hk.2.2.trans (by nlinarith [mul_le_mul_of_nonneg_left (log_le_self (log_nonneg hL.le)) hc.le])
  have hKsq : (jointUniformOrder c L:ℝ)^2 ≤ (c*log L+3)^2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) (by
      have hl := log_nonneg hL.le
      positivity)).mpr hK
  have hconst : 0 ≤ log 4+1 := by have h := log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith
  have hlog : log ((4:ℝ)^(jointUniformOrder c L)*
      (Nat.factorial (jointUniformOrder c L-1):ℝ)) ≤ L/2 := by
    calc
      _ ≤ (log 4+1)*(jointUniformOrder c L:ℝ)^2 := log_order_factorial_le (by omega)
      _ ≤ (log 4+1)*(c*log L+3)^2 := mul_le_mul_of_nonneg_left hKsq hconst
      _ ≤ L/2 := by have hh := (div_lt_iff₀ hL0).mp hs; linarith
  have hfpos : (0:ℝ) < (Nat.factorial (jointUniformOrder c L-1):ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h := exp_le_exp.mpr hlog
  rw [exp_log (by positivity)] at h
  exact h

private theorem order_in_short_window {t U : ℝ} {n m K : ℕ}
    (ht : 0 < t) (hn : 1 ≤ n) (hnm : n < m) (hK : 2 ≤ K)
    (hstart : (4:ℝ)^K*exp U ≤ ((m-n:ℕ):ℝ)^2*((4:ℝ)^2*Sieve.blockLambda t n 2))
    (hwidth : (n:ℝ)*(4:ℝ)^K*exp (2*U) ≤ ((m-n:ℕ):ℝ)^2)
    (hdrop : (4:ℝ)^K*Sieve.blockLambda t n K ≤ exp (-U)) :
    ∃ k, 2 ≤ k ∧ k ≤ K ∧ (4:ℝ)^k*Sieve.blockLambda t n k ≤ exp (-U) ∧
      exp U ≤ ((m-n:ℕ):ℝ)^2*Sieve.blockLambda t n k := by
  let H : ℝ := ((m-n:ℕ):ℝ)
  let B : ℝ := (4:ℝ)^K*exp U/H^2
  let mu : ℕ → ℝ := fun k => (4:ℝ)^k*Sieve.blockLambda t n k
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hH : 0 < H := by dsimp only [H]; exact_mod_cast Nat.sub_pos_of_lt hnm
  have hHs : 0 < H^2 := sq_pos_of_pos hH
  have hratio (j : ℕ) (hj : 2 < j) : (1/(n:ℝ))*mu (j-1) ≤ mu j := by
    dsimp only [mu]
    calc
      _ = (4:ℝ)^(j-1)*((1/(n:ℝ))*Sieve.blockLambda t n (j-1)) := by ring
      _ ≤ (4:ℝ)^(j-1)*Sieve.blockLambda t n j :=
        mul_le_mul_of_nonneg_left (Sieve.blockLambda_ratio ht hn hj) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)) (Sieve.blockLambda_pos ht hn j).le
  have hfirst : B ≤ mu 2 := by
    apply (div_le_iff₀ hHs).mpr
    simpa only [mu, H, mul_comm] using hstart
  have hwide : B ≤ (1/(n:ℝ))*exp (-U) := by
    apply (div_le_iff₀ hHs).mpr
    have hcan : exp (-U)*exp (2*U) = exp U := by
      rw [← exp_add]
      congr 1
      ring
    calc
      _ = (4:ℝ)^K*(exp (-U)*exp (2*U)) := by rw [hcan]
      _ = (exp (-U)/(n:ℝ))*((n:ℝ)*(4:ℝ)^K*exp (2*U)) := by field_simp
      _ ≤ (exp (-U)/(n:ℝ))*H^2 :=
        mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ = _ := by ring
  obtain ⟨k, hk, hkK, hkB, hkV⟩ :=
    GaloisForLFunctions.HTGeometry.exists_mem_window_of_ratio_lower_bound
      (show 0 ≤ 1/(n:ℝ) by positivity) hratio hfirst hwide hK hdrop
  refine ⟨k, hk, hkK, hkV, ?_⟩
  have hm := (div_le_iff₀ hHs).mp hkB
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hkK) (exp_pos U).le
  have hh : (4:ℝ)^k*exp U ≤ (4:ℝ)^k*(H^2*Sieve.blockLambda t n k) := by
    exact hp.trans (hm.trans_eq (by dsimp only [mu]; ring))
  exact (mul_le_mul_iff_of_pos_left (by positivity : (0:ℝ) < 4^k)).mp hh

private theorem order_mu_two_eq (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (4:ℝ)^2*Sieve.blockLambda t n 2 = 2*t/(Real.pi*(n:ℝ)^2) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold Sieve.blockLambda
  norm_num only [Nat.reduceSub, Nat.factorial_one, Nat.cast_one, mul_one]
  field_simp
  ring

theorem jointUniformWidth_square_scale (b L : ℝ) :
    exp L*(jointUniformWidth b L)^2 = (b*log (log L))^2*L^2 := by
  have he : exp L*(exp (-L/2))^2 = 1 := by
    rw [← exp_nat_mul, ← exp_add]
    norm_num only [Nat.cast_ofNat]
    rw [show L+2*(-L/2)=0 by ring, exp_zero]
  unfold jointUniformWidth
  calc
    _ = (b*log (log L))^2*L^2*(exp L*(exp (-L/2))^2) := by ring
    _ = _ := by rw [he, mul_one]

private theorem middle_initial_budgets {N R b t : ℝ} {n m K : ℕ}
    (hN : 0 < N) (hR : 0 < R) (hn : 1 ≤ n) (hnN : (n:ℝ) ≤ N)
    (hpow : (4:ℝ)^K ≤ R) (hbR : Real.pi+1 ≤ b^2*R)
    (ht : N/R ≤ t) (hH : 4*b^2*R^4*N ≤ ((m-n:ℕ):ℝ)^2) :
    (4:ℝ)^K*R ≤ ((m-n:ℕ):ℝ)^2*((4:ℝ)^2*Sieve.blockLambda t n 2) ∧
      (n:ℝ)*(4:ℝ)^K*R^2 ≤ ((m-n:ℕ):ℝ)^2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmu : 2/(Real.pi*N*R) ≤ (4:ℝ)^2*Sieve.blockLambda t n 2 := by
    rw [order_mu_two_eq t hn]
    calc
      _ = (2*(N/R))/(Real.pi*N^2) := by field_simp
      _ ≤ (2*(N/R))/(Real.pi*(n:ℝ)^2) := by gcongr
      _ ≤ 2*t/(Real.pi*(n:ℝ)^2) := by gcongr
  have hpi : Real.pi ≤ 8*b^2*R := by nlinarith [Real.pi_pos]
  have hone : 1 ≤ 4*b^2*R := by nlinarith [Real.pi_pos]
  constructor
  · calc
      _ ≤ R^2 := by nlinarith [mul_le_mul_of_nonneg_right hpow hR.le]
      _ ≤ 8*b^2*R^3/Real.pi := by
        apply (le_div_iff₀ Real.pi_pos).mpr
        have hh := mul_le_mul_of_nonneg_right hpi (sq_nonneg R)
        nlinarith
      _ = (4*b^2*R^4*N)*(2/(Real.pi*N*R)) := by field_simp; ring
      _ ≤ _ := mul_le_mul hH hmu (by positivity) (sq_nonneg _)
  · calc
      _ ≤ N*R*R^2 := by gcongr
      _ = N*R^3 := by ring
      _ ≤ 4*b^2*R^4*N := by
        have hh := mul_le_mul_of_nonneg_right hone (show 0 ≤ N*R^3 by positivity)
        nlinarith
      _ ≤ _ := hH

private theorem middle_order_drop {L a t : ℝ} {n K : ℕ}
    (hL : 0 ≤ L) (hn : 1 ≤ n) (hnL : exp L ≤ 2*(n:ℝ))
    (hK : a+1 ≤ (K:ℝ)) (ht : 0 ≤ t) (htop : t ≤ exp (a*L))
    (hfac : (4:ℝ)^K*(Nat.factorial (K-1):ℝ) ≤ exp (L/2)) :
    (4:ℝ)^K*Sieve.blockLambda t n K ≤ exp (-L/2)/(2*Real.pi) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : exp ((K:ℝ)*L) ≤ (2*(n:ℝ))^K := by
    rw [exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos L).le hnL K
  have hnum : exp (L/2)*exp (a*L) ≤ exp (-L/2)*exp ((K:ℝ)*L) := by
    rw [← exp_add, ← exp_add]
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hK hL
    linarith
  calc
    _ = ((4:ℝ)^K*(Nat.factorial (K-1):ℝ))*t/
        (2*Real.pi*(2*(n:ℝ))^K) := by unfold Sieve.blockLambda; ring
    _ ≤ exp (L/2)*exp (a*L)/(2*Real.pi*(2*(n:ℝ))^K) := by gcongr
    _ ≤ (exp (-L/2)*exp ((K:ℝ)*L))/(2*Real.pi*(2*(n:ℝ))^K) := by gcongr
    _ ≤ (exp (-L/2)*(2*(n:ℝ))^K)/(2*Real.pi*(2*(n:ℝ))^K) := by gcongr
    _ = _ := by field_simp

private theorem eventually_middle_parameters {b : ℝ} (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, 1 < L ∧ 1 ≤ log (log L) ∧
      Real.pi+1 ≤ b^2*sqrt L ∧ sqrt L*exp (-L/2) ≤ 2*Real.pi := by
  have hr : Tendsto (fun L : ℝ => sqrt L) atTop atTop := by
    simpa only [sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/2))
  have hbroot := (hr.const_mul_atTop (sq_pos_of_pos hb)).eventually_ge_atTop (Real.pi+1)
  have ht : Tendsto (fun L : ℝ => sqrt L*exp (-L/2)) atTop (𝓝 0) := by
    have he (L : ℝ) : -(1/2:ℝ)*L = -L/2 := by ring
    simpa only [sqrt_eq_rpow, he] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2) (1/2) (by norm_num)
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (1:ℝ),
    hbroot, ht.eventually (gt_mem_nhds (by positivity : (0:ℝ) < 2*Real.pi))]
    with L hL hl hbL htL
  exact ⟨hL, hl, hbL, htL.le⟩

private theorem middle_actual_length {b L : ℝ} {n m : ℕ}
    (hb : 0 < b) (hL : 0 ≤ L) (hl : 1 ≤ log (log L))
    (hH : 2*exp L*jointUniformWidth b L ≤ ((m-n:ℕ):ℝ)) :
    4*b^2*(sqrt L)^4*exp L ≤ ((m-n:ℕ):ℝ)^2 := by
  have hW : 0 ≤ jointUniformWidth b L := by unfold jointUniformWidth; positivity
  have hr : (sqrt L)^4 = L^2 := by
    calc
      _ = ((sqrt L)^2)^2 := by ring
      _ = L^2 := by rw [sq_sqrt hL]
  have hbll : b ≤ b*log (log L) := by nlinarith
  calc
    _ = 4*b^2*L^2*exp L := by rw [hr]
    _ ≤ 4*(b*log (log L))^2*L^2*exp L := by gcongr
    _ = 4*(exp L*(jointUniformWidth b L)^2)*exp L := by
      rw [jointUniformWidth_square_scale]
      ring
    _ = (2*exp L*jointUniformWidth b L)^2 := by ring
    _ ≤ _ := (sq_le_sq₀ (by positivity) (Nat.cast_nonneg _)).mpr hH

/-- Every frequency in the actual growing middle range has an admissible short-interval order.
The threshold depends only on the two fixed positive parameters; every numerical budget is paid. -/
theorem eventually_jointUniformOrder_window {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      let W := jointUniformWidth b L
      let n := ⌊exp L*exp (-2*W)⌋₊
      let m := ⌈exp L*exp (2*W)⌉₊+1
      ∀ t : ℝ, exp L/sqrt L ≤ t → t ≤ exp ((c*log (log L)+1)*L) →
        ∃ k, 2 ≤ k ∧ k ≤ jointUniformOrder c L ∧
          (4:ℝ)^k*Sieve.blockLambda t n k ≤ exp (-(log L/2)) ∧
          exp (log L/2) ≤ ((m-n:ℕ):ℝ)^2*Sieve.blockLambda t n k := by
  filter_upwards [eventually_middle_parameters hb,
    eventually_jointUniformWidth_grid_geometry hb,
    eventually_jointUniformOrder_bounds hc,
    eventually_jointUniformOrder_four_pow_sqrt hc,
    eventually_jointUniformOrder_factorial hc] with L hp hg hK hpow hfac
  let W := jointUniformWidth b L
  let n := ⌊exp L*exp (-2*W)⌋₊
  let m := ⌈exp L*exp (2*W)⌉₊+1
  change ∀ t : ℝ, exp L/sqrt L ≤ t → t ≤ exp ((c*log (log L)+1)*L) → _
  intro t ht htop
  have hL : 0 < L := by linarith [hp.1]
  have hR : 0 < sqrt L := sqrt_pos.mpr hL
  have hn : 1 ≤ n := (by norm_num : (1:ℕ) ≤ 2).trans hg.1
  have ht0 : 0 < t := (div_pos (exp_pos L) hR).trans_le ht
  have hH := middle_actual_length hb hL.le hp.2.1 hg.2.2.2.2.2.1
  have hinit := middle_initial_budgets (exp_pos L) hR hn hg.2.2.1 hpow hp.2.2.1 ht hH
  have he : exp (log L/2) = sqrt L := by
    rw [sqrt_eq_rpow, rpow_def_of_pos hL]
    congr 1
    ring
  have he2 : exp (2*(log L/2)) = (sqrt L)^2 := by
    rw [show 2*(log L/2) = log L by ring, exp_log hL, sq_sqrt hL.le]
  apply order_in_short_window ht0 hn hg.2.2.2.1 hK.1
  · simpa only [he] using hinit.1
  · simpa only [he2] using hinit.2
  · have hd := middle_order_drop hL.le hn (by linarith [hg.2.1])
      (show c*log (log L)+1+1 ≤ (jointUniformOrder c L:ℝ) by linarith [hK.2.1])
      ht0.le htop hfac
    calc
      _ ≤ exp (-L/2)/(2*Real.pi) := hd
      _ ≤ 1/sqrt L := by
        apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi) hR).mpr
        nlinarith [hp.2.2.2]
      _ = exp (-(log L/2)) := by rw [exp_neg, he, one_div]

theorem eventually_jointUniformOrder_saving {c : ℝ} (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ k ≤ jointUniformOrder c L,
      exp (-(log L/2)/(2:ℝ)^k) ≤ exp (-((log L)^(1-c*log 2)/16)) := by
  filter_upwards [eventually_jointUniformOrder_two_pow hc, eventually_gt_atTop (1:ℝ)]
    with L hpow hL
  intro k hk
  have hl : 0 < log L := log_pos hL
  have hp : (2:ℝ)^k ≤ 8*(log L)^(c*log 2) :=
    (pow_le_pow_right₀ one_le_two hk).trans hpow
  have hr : (log L)^(1-c*log 2)/16 ≤ (log L/2)/(2:ℝ)^k := by
    calc
      _ = (log L/2)/(8*(log L)^(c*log 2)) := by
        rw [Real.rpow_sub hl, Real.rpow_one]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hp
  apply exp_le_exp.mpr
  rw [neg_div]
  exact neg_le_neg hr

/-- A uniform saving on every actual short prefix throughout the growing frequency range. -/
theorem eventually_jointUniformOrder_prefix {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,
      let W := jointUniformWidth b L
      let n := ⌊exp L*exp (-2*W)⌋₊
      let m := ⌈exp L*exp (2*W)⌉₊+1
      ∀ t : ℝ, exp L/sqrt L ≤ t → t ≤ exp ((c*log (log L)+1)*L) →
        ∀ r, n ≤ r → r ≤ m →
          ‖∑ j ∈ Finset.Ico n r, (j:ℂ)^(-(Complex.I*(t:ℂ)))‖ ≤
            512*((m-n:ℕ):ℝ)*exp (-((log L)^(1-c*log 2)/16)) := by
  filter_upwards [eventually_jointUniformOrder_window hb hc,
    eventually_jointUniformWidth_grid_geometry hb, eventually_jointUniformOrder_saving hc,
    eventually_gt_atTop (1:ℝ)] with L hw hg hs hL
  dsimp only
  intro t ht htop r hnr hrm
  have hL0 : 0 < L := by linarith
  have ht0 : 0 < t := (div_pos (exp_pos L) (sqrt_pos.mpr hL0)).trans_le ht
  obtain ⟨k, hk, hkK, hsmall, hlarge⟩ := hw t ht htop
  have hn : 1 ≤ ⌊exp L*exp (-2*jointUniformWidth b L)⌋₊ := by omega
  have hU : 0 ≤ log L/2 := div_nonneg (log_nonneg hL.le) (by norm_num)
  have h := joint_short_phase_prefix t ht0 k _ _ hk hn hg.2.2.2.1 hg.2.2.2.2.1
    (log L/2) hU hsmall hlarge r hnr hrm
  exact h.trans (mul_le_mul_of_nonneg_left (hs k hkK) (by positivity))

end RHTower.WeilWorkPBAP
