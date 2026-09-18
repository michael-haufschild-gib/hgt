import GaloisForLFunctions.RHTower.ZetaGateProductAFEBlockInequality
import GaloisForLFunctions.RHTower.Sieve.LevinsonGcdFormBound
import GaloisForLFunctions.RHTower.HighBlockParameters

/-!
# The block inequality with the crude parameters

The block `[a, v]` with `20 ≤ a ≤ v ≤ 2a` is windowed with the overhang `η = u^{95}` and scale
`x = a = u^{100}`, where `u = a^{1/100}`; the mollifier length satisfies `N ≤ u^8`.  All error
terms of the block inequality then carry an explicit negative power of `u` times the window mass
`q − p + 2η`.  This module collects the individual estimates.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-! ## The `χ`-pair window integral -/

theorem norm_integral_window_chiPairWeight_le {d p q η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) :
    ‖∫ t, blockWindowC p q η t * chiPairWeight d t‖
      ≤ (q - p + 2 * η) * (Real.exp 1 * ((q + η) / (2 * Real.pi)) ^ (2 * d)) := by
  set M : ℝ := Real.exp 1 * ((q + η) / (2 * Real.pi)) ^ (2 * d) with hM
  have hqη : 0 ≤ (q + η) / (2 * Real.pi) := by
    have : 0 ≤ q + η := by linarith
    positivity
  have hM0 : 0 ≤ M := mul_nonneg (Real.exp_pos 1).le (Real.rpow_nonneg hqη _)
  have hint : Integrable (fun t => blockWindowC p q η t * chiPairWeight d t) :=
    integrable_window_mul hη (continuous_chiPairWeight hd).continuousOn
  have hpt : ∀ t, ‖blockWindowC p q η t * chiPairWeight d t‖ ≤ ‖blockWindowC p q η t‖ * M := by
    intro t
    rw [norm_mul]
    by_cases ht : t ∈ Set.Icc (p - η) (q + η)
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have ht4 : 4 ≤ t := by linarith [ht.1]
      refine (norm_chiPairWeight_le hd.le hd4 ht4).trans ?_
      unfold chiModulusWeight
      rw [hM, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
      exact Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right ht.2 (by positivity)) (by linarith)
    · rw [blockWindowC_eq_zero hη ht, norm_zero, zero_mul, zero_mul]
  calc ‖∫ t, blockWindowC p q η t * chiPairWeight d t‖
      ≤ ∫ t, ‖blockWindowC p q η t * chiPairWeight d t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖blockWindowC p q η t‖ * M :=
        integral_mono hint.norm ((integrable_blockWindowC hη).norm.mul_const _) hpt
    _ = (∫ t, ‖blockWindowC p q η t‖) * M := integral_mul_const _ _
    _ ≤ (q - p + 2 * η) * M :=
        mul_le_mul_of_nonneg_right (integral_norm_blockWindowC_le hη hpq) hM0

/-! ## The gcd sum of the Barban–Vehov mollifier -/

/-- The real coefficients of `hbCoeff N`. -/
def hbReal (N : ℕ) (n : ℕ) : ℝ := Sieve.barbanVehovWeight N n / Real.log N

theorem hbCoeff_eq_ofReal (N n : ℕ) : hbCoeff N n = ((hbReal N n : ℝ) : ℂ) := rfl

theorem gcdSum₂_hbReal_le {d : ℝ} (hd0 : 0 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    gcdSum₂ d N (hbReal N)
      ≤ Sieve.coprimeLogMoebiusConst ^ 2 * (N : ℝ) ^ (2 * d) * (64 * (1 + Real.log N))
        / (Real.log N) ^ 2 := by
  rw [gcdSum₂_eq_gcd_form]
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have h := Sieve.sum_barbanVehov_gcd_rpow_div_le N (s := 1 + 2 * d) (by linarith)
  have e : ∑ P ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      hbReal N P.1 * hbReal N P.2 * (Nat.gcd P.1 P.2 : ℝ) ^ (1 + 2 * d) / ((P.1 : ℝ) * P.2)
      = (∑ P ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        Sieve.barbanVehovWeight N P.1 * Sieve.barbanVehovWeight N P.2
          * (Nat.gcd P.1 P.2 : ℝ) ^ (1 + 2 * d) / ((P.1 : ℝ) * P.2)) / (Real.log N) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun P _ => ?_
    unfold hbReal
    field_simp
  rw [e, show (1 + 2 * d - 1 : ℝ) = 2 * d by ring] at *
  rw [div_le_div_iff_of_pos_right (by positivity)]
  simpa [show (1 + 2 * d - 1 : ℝ) = 2 * d by ring] using h

/-! ## Tail sums -/

theorem tsum_succ_rpow_neg_nonneg (r : ℝ) : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-r) :=
  tsum_nonneg fun n => by positivity

theorem tsum_succ_rpow_neg_le {r r' : ℝ} (hr : 1 < r) (hrr' : r ≤ r') :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-r') ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (-r) :=
  (summable_nat_succ_rpow_neg (by linarith)).tsum_le_tsum
    (fun n => Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (by linarith))
    (summable_nat_succ_rpow_neg hr)

/-! ## The direct envelope with the block parameters -/

theorem mul_le_u_pow_sixteen {u : ℝ} (hu : 1 ≤ u) {N h k : ℕ} (hN : (N : ℝ) ≤ u ^ 8)
    (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) :
    (h : ℝ) * k ≤ u ^ 16 := by
  have hh' : (h : ℝ) ≤ u ^ 8 := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hh).2) hN
  have hk' : (k : ℝ) ≤ u ^ 8 := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hk).2) hN
  calc (h : ℝ) * k ≤ u ^ 8 * u ^ 8 := mul_le_mul hh' hk' (Nat.cast_nonneg _) (by positivity)
    _ = u ^ 16 := by ring

theorem one_le_mul_cast {h k : ℕ} (hh : 0 < h) (hk : 0 < k) : (1 : ℝ) ≤ (h : ℝ) * k := by
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have k1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- `(hk)^{s} ≤ u^{16 n}` for `s ≤ n` and `hk ≤ u^{16}`. -/
theorem mul_cast_rpow_le_u_pow {u : ℝ} (hu : 1 ≤ u) {N h k : ℕ} (hN : (N : ℝ) ≤ u ^ 8)
    (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) {s : ℝ} (n : ℕ) (hs : s ≤ n) :
    ((h : ℝ) * k) ^ s ≤ u ^ (16 * n) := by
  have h1 := one_le_mul_cast (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hk).1
  calc ((h : ℝ) * k) ^ s ≤ ((h : ℝ) * k) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hs
    _ = ((h : ℝ) * k) ^ n := Real.rpow_natCast _ n
    _ ≤ (u ^ 16) ^ n := pow_le_pow_left₀ (by positivity) (mul_le_u_pow_sixteen hu hN hh hk) n
    _ = u ^ (16 * n) := by rw [← pow_mul]

theorem mul_cast_rpow_neg_le_one {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {s : ℝ} (hs : 0 ≤ s) :
    ((h : ℝ) * k) ^ (-s) ≤ 1 := by
  have h1 := one_le_mul_cast hh hk
  calc ((h : ℝ) * k) ^ (-s) ≤ ((h : ℝ) * k) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = 1 := Real.rpow_zero _

/-- The direct off-diagonal envelope with `(A, K) = (20, 38)`, `x = u^{100}`, `η = u^{95}`. -/
theorem tsum_directOffDiagTerm_le_param {d u p q : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hu : 1 ≤ u)
    (hpq : p ≤ q) {N h k : ℕ} (hN : (N : ℝ) ≤ u ^ 8) (hh : h ∈ Finset.Icc 1 N)
    (hk : k ∈ Finset.Icc 1 N) {CA : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ {y : ℝ}, 0 < y → ‖smoothAFECutoff y‖ ≤ CA * y ^ (-(20 : ℝ))) :
    ∑' P : ℕ × ℕ, directOffDiagTerm (1 / 2 - d) (u ^ 100) p q (u ^ 95) h k P
      ≤ (q - p + 2 * u ^ 95)
        * ((blockWindowConst 38 * CA * 2 ^ 38
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) / u ^ 1306) := by
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have hu0 : 0 < u := by linarith
  have hbnd := tsum_directOffDiagTerm_le 38 hCA0 hCA (σ₀ := 1 / 2 - d) (x := u ^ 100) (p := p)
    (q := q) (η := u ^ 95) (by push_cast; linarith) (by positivity) (by positivity) hpq hh0 hk0
  have h19 : ((38 : ℕ) : ℝ) / 2 = 19 := by norm_num
  rw [h19] at hbnd
  refine hbnd.trans ?_
  have e1 : ((h : ℝ) * k) ^ (19 - (1 / 2 - d)) ≤ u ^ 304 := by
    have := mul_cast_rpow_le_u_pow hu hN hh hk (s := 19 - (1 / 2 - d)) 19 (by push_cast; linarith)
    simpa using this
  have hZ0 := tsum_succ_rpow_neg_nonneg (20 + (1 / 2 - d) - 19)
  have e2 : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(20 + (1 / 2 - d) - 19))) ^ 2
      ≤ (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hZ0 (tsum_succ_rpow_neg_le (by norm_num) (by linarith)) 2
  have hD0 : 0 ≤ directOffDiagConst 38 CA 20 (u ^ 100) p q (u ^ 95) :=
    directOffDiagConst_nonneg 38 hCA0 (by positivity) (by positivity) hpq
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by positivity
  calc directOffDiagConst 38 CA 20 (u ^ 100) p q (u ^ 95) * ((h : ℝ) * k) ^ (19 - (1 / 2 - d))
        * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(20 + (1 / 2 - d) - 19))) ^ 2
      ≤ directOffDiagConst 38 CA 20 (u ^ 100) p q (u ^ 95) * u ^ 304
        * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 := by
        gcongr
    _ = (q - p + 2 * u ^ 95)
        * ((blockWindowConst 38 * CA * 2 ^ 38
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) / u ^ 1306) := by
        unfold directOffDiagConst
        rw [show (u ^ 100) ^ (20 : ℝ) = u ^ 2000 by
          rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]]
        field_simp
        try ring

/-! ## The jet constant with the block parameters -/

/-- The absolute jet constant `Σ_j C(20,j) bwc_j (20−j)! 132^{20−j}`. -/
def jetStar : ℝ :=
  ∑ j ∈ Finset.range 21, (Nat.choose 20 j : ℝ) * blockWindowConst j
    * ((20 - j).factorial * (132 : ℝ) ^ (20 - j))

theorem jetStar_nonneg : 0 ≤ jetStar :=
  Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (by positivity) (blockWindowConst_nonneg j))
    (by positivity)

theorem windowCarrierJetConst_le_param {u L : ℝ} (hu : 1 ≤ u) (hL : u ^ 100 / 2 ≤ L) :
    windowCarrierJetConst 20 (u ^ 95) L (u ^ 5) ≤ jetStar / u ^ 1900 := by
  have hu0 : 0 < u := by linarith
  have hL0 : 0 < L := by
    have : 0 < u ^ 100 / 2 := by positivity
    linarith
  unfold windowCarrierJetConst jetStar
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj20 : j ≤ 20 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hbase : 33 * (1 + |u ^ 5|) / L ≤ 132 / u ^ 95 := by
    rw [abs_of_pos (by positivity)]
    have h1 : 1 + u ^ 5 ≤ 2 * u ^ 5 := by
      have : 1 ≤ u ^ 5 := one_le_pow₀ hu
      linarith
    calc 33 * (1 + u ^ 5) / L ≤ 33 * (2 * u ^ 5) / (u ^ 100 / 2) :=
          div_le_div₀ (by positivity) (by nlinarith) (by positivity) hL
      _ = 132 / u ^ 95 := by
          field_simp
          ring
  have hpow : (33 * (1 + |u ^ 5|) / L) ^ (20 - j) ≤ (132 / u ^ 95) ^ (20 - j) :=
    pow_le_pow_left₀ (by positivity) hbase _
  have hη : blockWindowConst j / (u ^ 95) ^ j = blockWindowConst j * (1 / u ^ 95) ^ j := by
    rw [one_div_pow, div_eq_mul_inv, one_div]
  have hc0 : (0 : ℝ) ≤ Nat.choose 20 j := by positivity
  have hb0 := blockWindowConst_nonneg j
  calc (Nat.choose 20 j : ℝ) * (blockWindowConst j / (u ^ 95) ^ j)
        * (((20 - j).factorial : ℝ) * (33 * (1 + |u ^ 5|) / L) ^ (20 - j))
      ≤ (Nat.choose 20 j : ℝ) * (blockWindowConst j / (u ^ 95) ^ j)
        * (((20 - j).factorial : ℝ) * (132 / u ^ 95) ^ (20 - j)) := by
        gcongr
    _ = (Nat.choose 20 j : ℝ) * blockWindowConst j
        * (((20 - j).factorial : ℝ) * (132 : ℝ) ^ (20 - j)) / u ^ 1900 := by
        rw [div_pow, ← pow_mul]
        have : (u ^ 95) ^ j * (u ^ 95) ^ (20 - j) = u ^ 1900 := by
          rw [← pow_add, Nat.add_sub_cancel' hj20]
          ring
        field_simp
        rw [← this]
        ring

/-! ## The dual envelope with the block parameters -/

theorem u_pow_le_u_pow {u : ℝ} (hu : 1 ≤ u) {m n : ℕ} (hmn : m ≤ n) : u ^ m ≤ u ^ n :=
  pow_le_pow_right₀ hu hmn

theorem one_div_u_pow_le {u : ℝ} (hu : 1 ≤ u) {m n : ℕ} (hmn : m ≤ n) : 1 / u ^ n ≤ 1 / u ^ m :=
  one_div_le_one_div_of_le (by positivity) (u_pow_le_u_pow hu hmn)

/-- `e^{-y} ≤ n! / y^n` for `y > 0`. -/
theorem exp_neg_le_factorial_div {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Real.exp (-y) ≤ (n.factorial : ℝ) / y ^ n := by
  have h := Real.pow_div_factorial_le_exp y hy.le n
  rw [Real.exp_neg, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (Real.exp_pos y)]
  rw [div_le_iff₀ (by positivity)] at h
  linarith

/-- `200!` as a real constant (kept opaque to the simplifier). -/
def fact200 : ℝ := (Nat.factorial 200 : ℝ)

theorem fact200_nonneg : 0 ≤ fact200 := by
  unfold fact200
  positivity

/-- The absolute constant of the oscillation part of the dual envelope. -/
def oscStar (C₁ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * Real.exp 1
    * (jetStar * (Real.exp 8 * 625) * Real.sqrt Real.pi * 2 ^ 20
      + C₁ * 256 * (Real.exp 16 * (fact200 * 2 ^ 200) * Real.sqrt (4 * Real.pi)))

theorem oscStar_nonneg {C₁ : ℝ} (hC₁ : 0 ≤ C₁) : 0 ≤ oscStar C₁ := by
  unfold oscStar
  have := jetStar_nonneg
  have := fact200_nonneg
  positivity

theorem dualOffDiagOscConstV_le_param {u p q C₁ : ℝ} (hu : 2 ≤ u) (hp : p = u ^ 100)
    (hpq : p ≤ q) (hq : q ≤ 2 * u ^ 100) (hC₁ : 0 ≤ C₁) :
    dualOffDiagOscConstV 20 C₁ (u ^ 100) p q (u ^ 95) (u ^ 5)
      ≤ (q - p + 2 * u ^ 95) * (oscStar C₁ / u ^ 1600) := by
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have h95 : u ^ 95 ≤ u ^ 100 / 2 := by
    have h5 : 2 ≤ u ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 5)
    have : u ^ 100 = u ^ 95 * u ^ 5 := by ring
    rw [this]
    nlinarith [pow_pos hu0 95]
  have hL : u ^ 100 / 2 ≤ p - u ^ 95 := by rw [hp]; linarith
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by
    have := pow_pos hu0 95
    linarith
  have hJ := windowCarrierJetConst_le_param hu1 hL
  have hq0 : 0 ≤ q := by
    have := pow_pos hu0 100
    rw [hp] at hpq
    linarith
  have hpow4 : (1 + (q + u ^ 95) + u ^ 5) ^ 4 ≤ 625 * u ^ 400 := by
    have h1 : (1 : ℝ) ≤ u ^ 100 := one_le_pow₀ hu1
    have h5 : u ^ 5 ≤ u ^ 100 := u_pow_le_u_pow hu1 (by norm_num)
    have h95' : u ^ 95 ≤ u ^ 100 := u_pow_le_u_pow hu1 (by norm_num)
    have hsum : 1 + (q + u ^ 95) + u ^ 5 ≤ 5 * u ^ 100 := by linarith
    calc (1 + (q + u ^ 95) + u ^ 5) ^ 4 ≤ (5 * u ^ 100) ^ 4 :=
          pow_le_pow_left₀ (by linarith [pow_pos hu0 95, pow_pos hu0 5]) hsum 4
      _ = 625 * u ^ 400 := by ring
  have hpow4' : (1 + (q + u ^ 95)) ^ 4 ≤ 256 * u ^ 400 := by
    have h1 : (1 : ℝ) ≤ u ^ 100 := one_le_pow₀ hu1
    have h95' : u ^ 95 ≤ u ^ 100 := u_pow_le_u_pow hu1 (by norm_num)
    have hsum : 1 + (q + u ^ 95) ≤ 4 * u ^ 100 := by linarith
    calc (1 + (q + u ^ 95)) ^ 4 ≤ (4 * u ^ 100) ^ 4 :=
          pow_le_pow_left₀ (by linarith [pow_pos hu0 95]) hsum 4
      _ = 256 * u ^ 400 := by ring
  have hexp : Real.exp (-((u ^ 5) ^ 2) / 2) ≤ fact200 * 2 ^ 200 / u ^ 2000 := by
    have hy : 0 < (u ^ 5) ^ 2 / 2 := by positivity
    have h := exp_neg_le_factorial_div hy 200
    rw [show -((u ^ 5) ^ 2) / 2 = -((u ^ 5) ^ 2 / 2) by ring]
    refine h.trans (le_of_eq ?_)
    rw [show ((Nat.factorial 200 : ℕ) : ℝ) = fact200 from rfl, div_pow, ← pow_mul, ← pow_mul]
    rw [div_div_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
    try ring
  have hJ0 := windowCarrierJetConst_nonneg 20 (η := u ^ 95) (L := p - u ^ 95) (by positivity)
    (by linarith [pow_pos hu0 100]) (u ^ 5)
  have hjs := jetStar_nonneg
  have hf := fact200_nonneg
  unfold dualOffDiagOscConstV
  have hA : windowCarrierJetConst 20 (u ^ 95) (p - u ^ 95) (u ^ 5)
        * (Real.exp 8 * (1 + (q + u ^ 95) + u ^ 5) ^ 4) * Real.sqrt Real.pi * 2 ^ 20
      ≤ (jetStar / u ^ 1900) * (Real.exp 8 * (625 * u ^ 400)) * Real.sqrt Real.pi * 2 ^ 20 := by
    gcongr
  have hB : C₁ * (1 + (q + u ^ 95)) ^ 4
        * (Real.exp 16 * Real.exp (-((u ^ 5) ^ 2) / 2) * Real.sqrt (4 * Real.pi))
      ≤ C₁ * (256 * u ^ 400)
        * (Real.exp 16 * (fact200 * 2 ^ 200 / u ^ 2000) * Real.sqrt (4 * Real.pi)) := by
    gcongr
  have hcoef : 0 ≤ (1 / (2 * Real.pi)) * ((u ^ 100)⁻¹ * Real.exp 1 * (q - p + 2 * u ^ 95)) := by
    have : 0 ≤ (u ^ 100)⁻¹ * Real.exp 1 * (q - p + 2 * u ^ 95) :=
      mul_nonneg (by positivity) hlen
    positivity
  have key : ∀ X Y : ℝ, (1 / (2 * Real.pi)) * ((u ^ 100)⁻¹ * Real.exp 1 * (q - p + 2 * u ^ 95))
      * (X + Y) = (q - p + 2 * u ^ 95) * ((1 / (2 * Real.pi)) * Real.exp 1
        * ((u ^ 100)⁻¹ * X + (u ^ 100)⁻¹ * Y)) := fun X Y => by ring
  have hX : (u ^ 100)⁻¹ * ((jetStar / u ^ 1900) * (Real.exp 8 * (625 * u ^ 400))
      * Real.sqrt Real.pi * 2 ^ 20)
      = (jetStar * (Real.exp 8 * 625) * Real.sqrt Real.pi * 2 ^ 20) / u ^ 1600 := by
    field_simp
    try ring
  have hY : (u ^ 100)⁻¹ * (C₁ * (256 * u ^ 400)
      * (Real.exp 16 * (fact200 * 2 ^ 200 / u ^ 2000) * Real.sqrt (4 * Real.pi)))
      ≤ (C₁ * 256 * (Real.exp 16 * (fact200 * 2 ^ 200) * Real.sqrt (4 * Real.pi))) / u ^ 1600 := by
    have e : (u ^ 100)⁻¹ * (C₁ * (256 * u ^ 400)
        * (Real.exp 16 * (fact200 * 2 ^ 200 / u ^ 2000) * Real.sqrt (4 * Real.pi)))
        = (C₁ * 256 * (Real.exp 16 * (fact200 * 2 ^ 200) * Real.sqrt (4 * Real.pi))) / u ^ 1700 := by
      field_simp
      try ring
    rw [e]
    have hnum : 0 ≤ C₁ * 256 * (Real.exp 16 * (fact200 * 2 ^ 200) * Real.sqrt (4 * Real.pi)) :=
      mul_nonneg (mul_nonneg hC₁ (by norm_num))
        (mul_nonneg (mul_nonneg (Real.exp_pos 16).le (mul_nonneg hf (pow_nonneg (by norm_num) 200)))
          (Real.sqrt_nonneg _))
    exact div_le_div_of_nonneg_left hnum (by positivity) (u_pow_le_u_pow hu1 (by norm_num))
  calc (1 / (2 * Real.pi)) * ((u ^ 100)⁻¹ * Real.exp 1 * (q - p + 2 * u ^ 95))
        * (windowCarrierJetConst 20 (u ^ 95) (p - u ^ 95) (u ^ 5)
            * (Real.exp 8 * (1 + (q + u ^ 95) + u ^ 5) ^ 4) * Real.sqrt Real.pi * 2 ^ 20
          + C₁ * (1 + (q + u ^ 95)) ^ 4
            * (Real.exp 16 * Real.exp (-((u ^ 5) ^ 2) / 2) * Real.sqrt (4 * Real.pi)))
      ≤ (1 / (2 * Real.pi)) * ((u ^ 100)⁻¹ * Real.exp 1 * (q - p + 2 * u ^ 95))
        * ((jetStar / u ^ 1900) * (Real.exp 8 * (625 * u ^ 400)) * Real.sqrt Real.pi * 2 ^ 20
          + C₁ * (256 * u ^ 400)
            * (Real.exp 16 * (fact200 * 2 ^ 200 / u ^ 2000)
              * Real.sqrt (4 * Real.pi))) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) hcoef
    _ = (q - p + 2 * u ^ 95) * ((1 / (2 * Real.pi)) * Real.exp 1
          * ((u ^ 100)⁻¹ * ((jetStar / u ^ 1900) * (Real.exp 8 * (625 * u ^ 400))
              * Real.sqrt Real.pi * 2 ^ 20)
            + (u ^ 100)⁻¹ * (C₁ * (256 * u ^ 400)
              * (Real.exp 16 * (fact200 * 2 ^ 200 / u ^ 2000) * Real.sqrt (4 * Real.pi))))) :=
        key _ _
    _ ≤ (q - p + 2 * u ^ 95) * ((1 / (2 * Real.pi)) * Real.exp 1
          * ((jetStar * (Real.exp 8 * 625) * Real.sqrt Real.pi * 2 ^ 20) / u ^ 1600
            + (C₁ * 256 * (Real.exp 16 * (fact200 * 2 ^ 200) * Real.sqrt (4 * Real.pi)))
              / u ^ 1600)) := by
        rw [hX]
        gcongr
    _ = (q - p + 2 * u ^ 95) * (oscStar C₁ / u ^ 1600) := by
        unfold oscStar
        ring

theorem neg_shift_exponent_le {d : ℝ} (hd8 : d ≤ 1 / 8) :
    -(1 / 2 - d + ((40 : ℕ) : ℝ)) ≤ -((40 : ℕ) : ℝ) := by
  push_cast
  linarith

theorem dualOffDiagShiftConst_le_param {d u p q C₂ : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hu : 1 ≤ u)
    (hp : p = u ^ 100) (hpq : p ≤ q) (hq : q ≤ 2 * u ^ 100) (hC₂ : 0 ≤ C₂) :
    dualOffDiagShiftConst 40 C₂ d (u ^ 100) p q (u ^ 95)
      ≤ (q - p + 2 * u ^ 95) * (C₂ * 4 ^ 81 * u ^ 4100) := by
  have hu0 : 0 < u := by linarith
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by
    have := pow_pos hu0 95
    linarith
  have hq0 : 0 ≤ q := by
    have := pow_pos hu0 100
    rw [hp] at hpq
    linarith
  unfold dualOffDiagShiftConst
  have h1 : (1 : ℝ) ≤ u ^ 100 := one_le_pow₀ hu
  have h95' : u ^ 95 ≤ u ^ 100 := u_pow_le_u_pow hu (by norm_num)
  have hsum : 1 + (q + u ^ 95) ≤ 4 * u ^ 100 := by linarith
  have hpow : (1 + (q + u ^ 95)) ^ (2 * ((40 : ℕ) + 1 / 2 : ℝ)) ≤ 4 ^ 81 * u ^ 8100 := by
    rw [show (2 * ((40 : ℕ) + 1 / 2 : ℝ)) = ((81 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (1 + (q + u ^ 95)) ^ 81 ≤ (4 * u ^ 100) ^ 81 :=
          pow_le_pow_left₀ (by linarith [pow_pos hu0 95]) hsum 81
      _ = 4 ^ 81 * u ^ 8100 := by rw [mul_pow, ← pow_mul]
  have hx : (u ^ 100) ^ (-(1 / 2 - d + (40 : ℕ) : ℝ)) ≤ 1 / u ^ 4000 := by
    calc (u ^ 100) ^ (-(1 / 2 - d + (40 : ℕ) : ℝ)) ≤ (u ^ 100) ^ (-((40 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le h1 (neg_shift_exponent_le hd8)
      _ = 1 / u ^ 4000 := by
          rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← pow_mul]
          norm_num
  calc (q - p + 2 * u ^ 95) * (C₂ * (1 + (q + u ^ 95)) ^ (2 * ((40 : ℕ) + 1 / 2 : ℝ))
        * (u ^ 100) ^ (-(1 / 2 - d + (40 : ℕ) : ℝ)))
      ≤ (q - p + 2 * u ^ 95) * (C₂ * (4 ^ 81 * u ^ 8100) * (1 / u ^ 4000)) := by
        gcongr
    _ = (q - p + 2 * u ^ 95) * (C₂ * 4 ^ 81 * u ^ 4100) := by
        field_simp
        try ring

/-- The absolute constant of the dual envelope. -/
def dualStar (C₁ C₂ : ℝ) : ℝ :=
  oscStar C₁ * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2
    + C₂ * 4 ^ 81 * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2

theorem dualStar_nonneg {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) : 0 ≤ dualStar C₁ C₂ := by
  unfold dualStar
  have := oscStar_nonneg hC₁
  positivity

/-- The dual off-diagonal envelope with `K = 20`, `K'' = 40`, `V = u^5`, `Y₀ = u^{110}`. -/
theorem tsum_dualOffDiagTerm_le_param {d u p q : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hu : 2 ≤ u)
    (hp : p = u ^ 100) (hpq : p ≤ q) (hq : q ≤ 2 * u ^ 100) {N h k : ℕ} (hN : (N : ℝ) ≤ u ^ 8)
    (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : ∀ (d x p q η Y₀ V : ℝ) (h k : ℕ), 0 < d → d ≤ 1 / 4 →
      0 < x → 0 < η → 4 ≤ p - η → p ≤ q → 0 < Y₀ → 0 ≤ V → 2 * V ≤ p - η → 0 < h → 0 < k →
      ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
        ≤ dualOffDiagOscConstV 20 C₁ x p q η V * ((h : ℝ) * k) ^ (((20 : ℕ) : ℝ) / 2 - 1 / 2 + d)
              * Y₀ ^ (((20 : ℕ) : ℝ) / 2 + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
          + dualOffDiagShiftConst 40 C₂ d x p q η * ((h : ℝ) * k) ^ (-(1 / 2 - d))
              * Y₀ ^ (-(((40 : ℕ) : ℝ) - 1)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2) :
    ∑' P : ℕ × ℕ, dualOffDiagTerm d (u ^ 100) p q (u ^ 95) h k P
      ≤ (q - p + 2 * u ^ 95) * (dualStar C₁ C₂ / u ^ 190) := by
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  have h95 : u ^ 95 ≤ u ^ 100 / 2 := by
    have h5 : 2 ≤ u ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 5)
    have : u ^ 100 = u ^ 95 * u ^ 5 := by ring
    rw [this]
    nlinarith [pow_pos hu0 95]
  have hL : u ^ 100 / 2 ≤ p - u ^ 95 := by rw [hp]; linarith
  have h4 : (4 : ℝ) ≤ p - u ^ 95 := by
    have : (2 : ℝ) ^ 100 ≤ u ^ 100 := pow_le_pow_left₀ (by norm_num) hu 100
    have h2 : (8 : ℝ) ≤ u ^ 100 / 2 := by
      have : (16 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
      linarith
    linarith
  have hV : 2 * u ^ 5 ≤ p - u ^ 95 := by
    have h5 : u ^ 5 ≤ u ^ 100 / 4 := by
      have : u ^ 100 = u ^ 5 * u ^ 95 := by ring
      have h95' : (4 : ℝ) ≤ u ^ 95 :=
        le_trans (by norm_num) (le_trans (pow_le_pow_left₀ (by norm_num) hu 95) le_rfl)
      rw [this]
      nlinarith [pow_pos hu0 5]
    linarith
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by
    have := pow_pos hu0 95
    linarith
  have hb := hsplit d (u ^ 100) p q (u ^ 95) (u ^ 110) (u ^ 5) h k hd (by linarith)
    (by positivity) (by positivity) h4 hpq (by positivity) (by positivity) hV hh0 hk0
  refine hb.trans ?_
  have hOsc := dualOffDiagOscConstV_le_param hu hp hpq hq hC₁
  have hSh := dualOffDiagShiftConst_le_param hd hd8 hu1 hp hpq hq hC₂
  have hOsc0 := dualOffDiagOscConstV_nonneg 20 hC₁ (x := u ^ 100) (by positivity) (by positivity)
    h4 hpq (V := u ^ 5) (by positivity)
  have hSh0 := dualOffDiagShiftConst_nonneg 40 (C := C₂) (d := d) (x := u ^ 100) hC₂ (by positivity)
    (by positivity) h4 hpq
  have e1 : ((h : ℝ) * k) ^ (((20 : ℕ) : ℝ) / 2 - 1 / 2 + d) ≤ u ^ 160 := by
    have := mul_cast_rpow_le_u_pow hu1 hN hh hk (s := ((20 : ℕ) : ℝ) / 2 - 1 / 2 + d) 10
      (by push_cast; linarith)
    simpa using this
  have e2 : (u ^ 110) ^ (((20 : ℕ) : ℝ) / 2 + 1) = u ^ 1210 := by
    rw [show (((20 : ℕ) : ℝ) / 2 + 1) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]
    try norm_num
  have e3 : ((h : ℝ) * k) ^ (-(1 / 2 - d)) ≤ 1 := mul_cast_rpow_neg_le_one hh0 hk0 (by linarith)
  have e4 : (u ^ 110) ^ (-(((40 : ℕ) : ℝ) - 1)) = 1 / u ^ 4290 := by
    rw [show (-(((40 : ℕ) : ℝ) - 1)) = -((39 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast, ← pow_mul]
    norm_num
  have hZ0 := tsum_succ_rpow_neg_nonneg (5 / 2 + d)
  have e5 : (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
      ≤ (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hZ0 (tsum_succ_rpow_neg_le (by norm_num) (by linarith)) 2
  have hZ2 := sq_nonneg (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ)))
  have hZ5 := sq_nonneg (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
  have hos := oscStar_nonneg hC₁
  rw [e2, e4]
  set W : ℝ := q - p + 2 * u ^ 95 with hW
  calc dualOffDiagOscConstV 20 C₁ (u ^ 100) p q (u ^ 95) (u ^ 5)
          * ((h : ℝ) * k) ^ (((20 : ℕ) : ℝ) / 2 - 1 / 2 + d) * u ^ 1210
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
        + dualOffDiagShiftConst 40 C₂ d (u ^ 100) p q (u ^ 95) * ((h : ℝ) * k) ^ (-(1 / 2 - d))
          * (1 / u ^ 4290) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2
      ≤ ((q - p + 2 * u ^ 95) * (oscStar C₁ / u ^ 1600)) * u ^ 160 * u ^ 1210
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2
        + ((q - p + 2 * u ^ 95) * (C₂ * 4 ^ 81 * u ^ 4100)) * 1
          * (1 / u ^ 4290) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 := by
        gcongr
    _ = W * (oscStar C₁ * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2
          * (u ^ 160 * u ^ 1210 / u ^ 1600)
        + C₂ * 4 ^ 81 * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 * (u ^ 4100 / u ^ 4290)) := by
        field_simp
        try ring
    _ ≤ W * (oscStar C₁ * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ))) ^ 2
          * (1 / u ^ 190)
        + C₂ * 4 ^ 81 * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2 * (1 / u ^ 190)) := by
        have f1 : u ^ 160 * u ^ 1210 / u ^ 1600 ≤ 1 / u ^ 190 := by
          rw [show u ^ 160 * u ^ 1210 / u ^ 1600 = 1 / u ^ 230 by field_simp; try ring]
          exact one_div_u_pow_le hu1 (by norm_num)
        have f2 : u ^ 4100 / u ^ 4290 = 1 / u ^ 190 := by
          field_simp
          try ring
        rw [f2]
        gcongr
    _ = W * (dualStar C₁ C₂ / u ^ 190) := by
        unfold dualStar
        ring

/-! ## The left-line pieces and the residue with the block parameters -/

theorem reducedProd_le (h k : ℕ) : ((reducedProd h k : ℕ) : ℝ) ≤ (h : ℝ) * k := by
  unfold reducedProd
  have h1 : h / Nat.gcd h k ≤ h := Nat.div_le_self _ _
  have h2 : k / Nat.gcd h k ≤ k := Nat.div_le_self _ _
  have := Nat.mul_le_mul h1 h2
  exact_mod_cast this

theorem one_le_reducedProd {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    (1 : ℝ) ≤ ((reducedProd h k : ℕ) : ℝ) := by
  obtain ⟨_, hh', hk', _, _, _⟩ := gcd_facts hh hk
  unfold reducedProd
  have := Nat.mul_pos hh' hk'
  exact_mod_cast this

/-- `(x/c)^{-1/4} ≤ 1/u^{21}` for `x = u^{100}`, `1 ≤ c ≤ u^{16}`. -/
theorem rpow_x_div_c_le {u c : ℝ} (hu : 1 ≤ u) (hc1 : 1 ≤ c) (hc : c ≤ u ^ 16) :
    (u ^ 100 / c) ^ (-(1 / 4 : ℝ)) ≤ 1 / u ^ 21 := by
  have hu0 : 0 < u := by linarith
  have h1 : u ^ 100 / u ^ 16 ≤ u ^ 100 / c := div_le_div_of_nonneg_left (by positivity) (by linarith) hc
  calc (u ^ 100 / c) ^ (-(1 / 4 : ℝ)) ≤ (u ^ 100 / u ^ 16) ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    _ = 1 / u ^ 21 := by
        rw [show u ^ 100 / u ^ 16 = (u ^ 21) ^ (4 : ℕ) by field_simp; try ring,
          ← Real.rpow_natCast (u ^ 21) 4, ← Real.rpow_mul (by positivity),
          show ((4 : ℕ) : ℝ) * (-(1 / 4 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, one_div]

/-- `(c x)^{1/4} ≤ u^{29}` for `x = u^{100}`, `c ≤ u^{16}`. -/
theorem rpow_c_mul_x_le {u c : ℝ} (hu : 1 ≤ u) (hc0 : 0 ≤ c) (hc : c ≤ u ^ 16) :
    (c * u ^ 100) ^ (1 / 4 : ℝ) ≤ u ^ 29 := by
  have hu0 : 0 < u := by linarith
  calc (c * u ^ 100) ^ (1 / 4 : ℝ) ≤ (u ^ 16 * u ^ 100) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hc (by positivity))
          (by norm_num)
    _ = u ^ 29 := by
        rw [show u ^ 16 * u ^ 100 = (u ^ 29) ^ (4 : ℕ) by ring, ← Real.rpow_natCast (u ^ 29) 4,
          ← Real.rpow_mul (by positivity), show ((4 : ℕ) : ℝ) * (1 / 4 : ℝ) = 1 by norm_num,
          Real.rpow_one]

/-- `(1+L)^{-(1/2-2d)} ≤ (2/u^{50}) (1+L)^{2d}` for `L ≥ u^{100}/2`. -/
theorem rpow_one_add_L_le {u L : ℝ} (hu : 1 ≤ u) (hL : u ^ 100 / 2 ≤ L) (d : ℝ) :
    (1 + L) ^ (-(1 / 2 - 2 * d)) ≤ (2 / u ^ 50) * (1 + L) ^ (2 * d) := by
  have hu0 : 0 < u := by linarith
  have hL0 : 0 < 1 + L := by
    have : 0 < u ^ 100 / 2 := by positivity
    linarith
  have hsplit : (1 + L) ^ (-(1 / 2 - 2 * d)) = (1 + L) ^ (-(1 / 2 : ℝ)) * (1 + L) ^ (2 * d) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL0.le _)
  have hge : (u ^ 50 / 2) ^ (2 : ℕ) ≤ 1 + L := by
    have : (u ^ 50 / 2) ^ (2 : ℕ) = u ^ 100 / 4 := by ring
    rw [this]
    have : 0 ≤ u ^ 100 := by positivity
    linarith
  calc (1 + L) ^ (-(1 / 2 : ℝ)) ≤ ((u ^ 50 / 2) ^ (2 : ℕ)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hge (by norm_num)
    _ = 2 / u ^ 50 := by
        rw [← Real.rpow_natCast (u ^ 50 / 2) 2, ← Real.rpow_mul (by positivity),
          show ((2 : ℕ) : ℝ) * (-(1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, inv_div]

theorem exp_neg_sq_le_param {u L : ℝ} (hu : 1 ≤ u) (hL : u ^ 100 / 2 ≤ L) :
    Real.exp (-(L ^ 2)) ≤ 32 / u ^ 400 := by
  have hu0 : 0 < u := by linarith
  have hL0 : 0 < L := by
    have : 0 < u ^ 100 / 2 := by positivity
    linarith
  have h1 : (u ^ 100 / 2) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hL 2
  have hy : 0 < (u ^ 100 / 2) ^ 2 := by positivity
  calc Real.exp (-(L ^ 2)) ≤ Real.exp (-((u ^ 100 / 2) ^ 2)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ (Nat.factorial 2 : ℝ) / ((u ^ 100 / 2) ^ 2) ^ 2 := exp_neg_le_factorial_div hy 2
    _ = 32 / u ^ 400 := by
        rw [Nat.factorial_two]
        push_cast
        field_simp
        ring

/-- The absolute constant of the pair error (without the `(1+L)^{2d}` factor of the dual
left-line piece). -/
def pairStar (CA C₁ C₂ K₁ : ℝ) : ℝ :=
  blockWindowConst 38 * CA * 2 ^ 38 * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2
    + dualStar C₁ C₂ + K₁ + 576 * Real.exp 1

theorem pairStar_nonneg {CA C₁ C₂ K₁ : ℝ} (hCA : 0 ≤ CA) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hK₁ : 0 ≤ K₁) : 0 ≤ pairStar CA C₁ C₂ K₁ := by
  unfold pairStar
  have := blockWindowConst_nonneg 38
  have := dualStar_nonneg hC₁ hC₂
  positivity

/-- **The pair error with the block parameters.** -/
theorem norm_pairError_le_param {d u p q : ℝ} (hd : 0 < d) (hd8 : d ≤ 1 / 8) (hu : 2 ≤ u)
    (hp : p = u ^ 100) (hpq : p ≤ q) (hq : q ≤ 2 * u ^ 100) {N h k : ℕ} (hN : (N : ℝ) ≤ u ^ 8)
    (hh : h ∈ Finset.Icc 1 N) (hk : k ∈ Finset.Icc 1 N) {CA C₁ C₂ K₁ K₂ : ℝ} (hCA0 : 0 ≤ CA)
    (hCA : ∀ {y : ℝ}, 0 < y → ‖smoothAFECutoff y‖ ≤ CA * y ^ (-(20 : ℝ)))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hsplit : ∀ (d x p q η Y₀ V : ℝ) (h k : ℕ), 0 < d → d ≤ 1 / 4 →
      0 < x → 0 < η → 4 ≤ p - η → p ≤ q → 0 < Y₀ → 0 ≤ V → 2 * V ≤ p - η → 0 < h → 0 < k →
      ∑' P : ℕ × ℕ, dualOffDiagTerm d x p q η h k P
        ≤ dualOffDiagOscConstV 20 C₁ x p q η V * ((h : ℝ) * k) ^ (((20 : ℕ) : ℝ) / 2 - 1 / 2 + d)
              * Y₀ ^ (((20 : ℕ) : ℝ) / 2 + 1) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 2 + d))) ^ 2
          + dualOffDiagShiftConst 40 C₂ d x p q η * ((h : ℝ) * k) ^ (-(1 / 2 - d))
              * Y₀ ^ (-(((40 : ℕ) : ℝ) - 1)) * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(2 : ℝ))) ^ 2)
    (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hK₁ : ∀ σ₀ c x : ℝ, 1 / 4 ≤ σ₀ → σ₀ ≤ 1 / 2 → 0 < c → 0 < x →
      ‖smoothLeft σ₀ c x‖ ≤ K₁ * (x / c) ^ (-(1 / 4 : ℝ)))
    (hK₂ : ∀ d c x τ : ℝ, 0 < d → d ≤ 1 / 8 → 0 < c → 0 < x →
      ‖dualLeft d c x τ‖ ≤ K₂ * (c * x) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (-(1 / 2 - 2 * d))) :
    ‖pairError d (u ^ 100) p q (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
      ≤ (q - p + 2 * u ^ 95)
        * ((pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d)) / u ^ 21) := by
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  obtain ⟨hg, hh', hk', hcop, hhg, hkg⟩ := gcd_facts hh0 hk0
  have h95 : u ^ 95 ≤ u ^ 100 / 2 := by
    have h5 : 2 ≤ u ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu 5)
    have : u ^ 100 = u ^ 95 * u ^ 5 := by ring
    rw [this]
    nlinarith [pow_pos hu0 95]
  have hL : u ^ 100 / 2 ≤ p - u ^ 95 := by rw [hp]; linarith
  have h4 : (4 : ℝ) ≤ p - u ^ 95 := by
    have : (2 : ℝ) ^ 100 ≤ u ^ 100 := pow_le_pow_left₀ (by norm_num) hu 100
    have h2 : (8 : ℝ) ≤ u ^ 100 / 2 := by
      have : (16 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
      linarith
    linarith
  have hlen : 0 ≤ q - p + 2 * u ^ 95 := by
    have := pow_pos hu0 95
    linarith
  have hx1 : (1 : ℝ) ≤ u ^ 100 := one_le_pow₀ hu1
  -- the reduced product
  have hcpos : (0 : ℝ) < ((reducedProd h k : ℕ) : ℝ) := by linarith [one_le_reducedProd hh0 hk0]
  have hc1 := one_le_reducedProd hh0 hk0
  have hcu : ((reducedProd h k : ℕ) : ℝ) ≤ u ^ 16 :=
    (reducedProd_le h k).trans (mul_le_u_pow_sixteen hu1 hN hh hk)
  have hred : ((h / Nat.gcd h k) * (k / Nat.gcd h k) : ℕ) = reducedProd h k := rfl
  have hbound := norm_pairError_le hd hd8 hx1 (by positivity) h4 hpq hg hh' hk' hhg hkg hK₁0 hK₂0
    (hK₁ (1 / 2 - d) _ (u ^ 100) (by linarith) (by linarith) (by rw [hred]; exact hcpos)
      (by positivity))
    (fun τ => hK₂ d _ (u ^ 100) τ hd hd8 (by rw [hred]; exact hcpos) (by positivity))
  rw [hred] at hbound
  refine hbound.trans ?_
  -- the pieces
  have e1 := tsum_directOffDiagTerm_le_param hd hd8 hu1 hpq hN hh hk hCA0 hCA
  have e2 := tsum_dualOffDiagTerm_le_param hd hd8 hu hp hpq hq hN hh hk hC₁ hC₂ hsplit
  have e3 : ((h : ℝ) * k) ^ (-(1 / 2 - d)) ≤ 1 := mul_cast_rpow_neg_le_one hh0 hk0 (by linarith)
  have e4 : ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 - d)) ≤ 1 := by
    calc ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 - d)) ≤ ((reducedProd h k : ℕ) : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
      _ = 1 := Real.rpow_zero _
  have e5 : ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 + d)) ≤ 1 := by
    calc ((reducedProd h k : ℕ) : ℝ) ^ (-(1 / 2 + d)) ≤ ((reducedProd h k : ℕ) : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
      _ = 1 := Real.rpow_zero _
  have e6 := rpow_x_div_c_le hu1 hc1 hcu
  have e7 := rpow_c_mul_x_le hu1 hcpos.le hcu
  have e8 := rpow_one_add_L_le hu1 hL d
  have e9 := exp_neg_sq_le_param hu1 hL
  have hZ := sq_nonneg (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)))
  have hbw := blockWindowConst_nonneg 38
  have hDS := dualStar_nonneg hC₁ hC₂
  have hLpow : 0 ≤ (1 + (p - u ^ 95)) ^ (2 * d) := Real.rpow_nonneg (by linarith) _
  have hps := pairStar_nonneg hCA0 hC₁ hC₂ hK₁0
  set W : ℝ := q - p + 2 * u ^ 95 with hW
  -- assemble
  calc _ ≤ W
        * ((blockWindowConst 38 * CA * 2 ^ 38
          * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) / u ^ 1306)
        + W * (dualStar C₁ C₂ / u ^ 190)
        + 1 * (1 * (K₁ * (1 / u ^ 21)) * W
            + 1 * (W * (K₂ * u ^ 29
              * ((2 / u ^ 50) * (1 + (p - u ^ 95)) ^ (2 * d)))))
        + W * (1 * (18 * Real.exp 1 * u ^ 100 * (32 / u ^ 400))) := by
        gcongr
    _ = W
        * ((blockWindowConst 38 * CA * 2 ^ 38
            * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) * (1 / u ^ 1306)
          + dualStar C₁ C₂ * (1 / u ^ 190) + K₁ * (1 / u ^ 21)
          + 2 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d) * (u ^ 29 / u ^ 50)
          + 576 * Real.exp 1 * (u ^ 100 / u ^ 400)) := by
        field_simp
        try ring
    _ ≤ W
        * ((blockWindowConst 38 * CA * 2 ^ 38
            * (∑' n : ℕ, ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2) * (1 / u ^ 21)
          + dualStar C₁ C₂ * (1 / u ^ 21) + K₁ * (1 / u ^ 21)
          + 2 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d) * (1 / u ^ 21)
          + 576 * Real.exp 1 * (1 / u ^ 21)) := by
        have f1 : 1 / u ^ 1306 ≤ 1 / u ^ 21 := one_div_u_pow_le hu1 (by norm_num)
        have f2 : 1 / u ^ 190 ≤ 1 / u ^ 21 := one_div_u_pow_le hu1 (by norm_num)
        have f3 : u ^ 29 / u ^ 50 = 1 / u ^ 21 := by field_simp; try ring
        have f4 : u ^ 100 / u ^ 400 ≤ 1 / u ^ 21 := by
          rw [show u ^ 100 / u ^ 400 = 1 / u ^ 300 by field_simp; try ring]
          exact one_div_u_pow_le hu1 (by norm_num)
        rw [f3]
        gcongr
    _ = W
        * ((pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (p - u ^ 95)) ^ (2 * d)) / u ^ 21) := by
        unfold pairStar
        ring

end RHTower.ZetaGateProductAFE

end
