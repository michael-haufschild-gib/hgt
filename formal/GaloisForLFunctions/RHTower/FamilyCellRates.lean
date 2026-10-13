import GaloisForLFunctions.RHTower.FamilyFrobeniusNontrivial
import GaloisForLFunctions.RHTower.ThmEUniform

/-!
# Rates for the family certificate in a modulus cell

For moduli `T^{κ_lo} ≤ q ≤ T^{κ_hi}` with `κ_hi < 1`, bandwidth `L = λ l` with `λ < 2` and
`λ − κ_lo < 1` (so that `X/q ≤ T^{λ−κ_lo}` and `√X ≤ T^{λ/2}` both save a power of `T`):

* the Frobenius majorant is `o(T l L²)` uniformly in the cell (`eventually_famMaj_le`);
* the parity-shift term `(1 + l)(M² T·2πL + C_P L l log l (l + M)²)` is `o(T l L²)` (`eventually_parity_le`).

The first is a deterministic bound of `famMaj` by `(log T)^k T^s` terms with `s < 1`, plus `72 T log T` and
`4(1 + c log T) T log² T` (`famMaj_le_bound`).
-/

open Real Filter Topology Zeta23 Zeta23.ThmE

noncomputable section

namespace RHTower

/-- **A deterministic bound for the Frobenius majorant.** -/
theorem famMaj_le_bound {q : ℕ} {T lT l L X lam κhi s5 c : ℝ}
    (hq : 1 ≤ q) (hT : 0 < T) (hlT : 1 ≤ lT) (hl1 : 1 ≤ l) (hlo : lT / 2 ≤ l) (hhi : l ≤ lT)
    (hL : L = lam * l) (h2 : lam ≤ 2) (hL1 : 1 ≤ L) (hlq : Real.log q ≤ lT)
    (hell0 : 0 ≤ ell1q q T) (hell : ell1q q T ≤ Real.log q + l + 1)
    (hsX : Real.sqrt X ≤ T ^ (lam / 2)) (hX0 : 0 ≤ X) (hXq : X / q ≤ T ^ s5) (hqT : (q : ℝ) ≤ T ^ κhi)
    (hy : Real.log (Real.log q + 8) ^ 2 ≤ c * lT) :
    famMaj q T L l X ≤ 64 * lT ^ 5 + 8 * lT ^ 7 + 72 * T * lT + 2 * lT ^ 2 * T ^ (lam / 2)
      + 4 * (1 + c * lT) * T * lT ^ 2 + 32 * lT ^ 5 * T ^ s5 + 2 * lT ^ 5 * T ^ κhi := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlT0 : 0 < lT := by linarith
  have hl0 : 0 < l := by linarith
  have hLle : L ≤ 2 * lT := by
    rw [hL]; nlinarith
  have hL0 : 0 < L := by linarith
  have h1q : 1 + Real.log q ≤ 2 * lT := by linarith
  have h1q0 : 0 ≤ 1 + Real.log q := by linarith
  have hlogL : Real.log L ≤ 2 * lT := by
    have := Real.log_le_sub_one_of_pos hL0; linarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogl : Real.log l ≤ lT := by
    have := Real.log_le_sub_one_of_pos hl0; linarith
  have hlogl0 : 0 ≤ Real.log l := Real.log_nonneg hl1
  have hTs5 : 0 ≤ T ^ s5 := by positivity
  have hTκ : 0 ≤ T ^ κhi := by positivity
  have hTl : 0 ≤ T ^ (lam / 2) := by positivity
  have hsq0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hXq0 : 0 ≤ X / q := by positivity
  have hy0 : 0 ≤ Real.log (Real.log q + 8) ^ 2 := sq_nonneg _
  have hlT5 : lT ^ 4 ≤ lT ^ 5 := pow_le_pow_right₀ hlT (by norm_num)
  -- the six terms
  have t1 : (1 + Real.log q) ^ 2 * l ^ 2 * Real.log L ≤ 8 * lT ^ 5 := by
    have a : (1 + Real.log q) ^ 2 ≤ (2 * lT) ^ 2 := pow_le_pow_left₀ h1q0 h1q 2
    have b : l ^ 2 ≤ lT ^ 2 := pow_le_pow_left₀ hl0.le hhi 2
    calc (1 + Real.log q) ^ 2 * l ^ 2 * Real.log L ≤ (2 * lT) ^ 2 * lT ^ 2 * (2 * lT) := by
          apply mul_le_mul (mul_le_mul a b (by positivity) (by positivity)) hlogL hlogL0
            (by positivity)
      _ = 8 * lT ^ 5 := by ring
  have t2 : T * L * ell1q q T ^ 2 / l ^ 2 ≤ 72 * T * lT := by
    have hell3 : ell1q q T ≤ 6 * l := by linarith
    have he2 : ell1q q T ^ 2 ≤ 36 * l ^ 2 := by
      have := pow_le_pow_left₀ hell0 hell3 2; nlinarith
    have hd : ell1q q T ^ 2 / l ^ 2 ≤ 36 := by rw [div_le_iff₀ (by positivity)]; exact he2
    have hd0 : 0 ≤ ell1q q T ^ 2 / l ^ 2 := by positivity
    calc T * L * ell1q q T ^ 2 / l ^ 2 = (T * L) * (ell1q q T ^ 2 / l ^ 2) := by ring
      _ ≤ (T * (2 * lT)) * 36 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hLle hT.le) hd hd0 (by positivity)
      _ = 72 * T * lT := by ring
  have t3 : (1 + Real.log q) * l * Real.sqrt X ≤ 2 * lT ^ 2 * T ^ (lam / 2) := by
    calc (1 + Real.log q) * l * Real.sqrt X ≤ (2 * lT) * lT * T ^ (lam / 2) :=
          mul_le_mul (mul_le_mul h1q hhi hl0.le (by positivity)) hsX hsq0 (by positivity)
      _ = 2 * lT ^ 2 * T ^ (lam / 2) := by ring
  have t4 : (1 + Real.log (Real.log q + 8) ^ 2) * T * L ^ 2 ≤ 4 * (1 + c * lT) * T * lT ^ 2 := by
    have hL2 : L ^ 2 ≤ (2 * lT) ^ 2 := pow_le_pow_left₀ hL0.le hLle 2
    calc (1 + Real.log (Real.log q + 8) ^ 2) * T * L ^ 2 ≤ (1 + c * lT) * T * (2 * lT) ^ 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hT.le) hL2 (by positivity)
          have : 0 ≤ 1 + c * lT := by linarith
          positivity
      _ = 4 * (1 + c * lT) * T * lT ^ 2 := by ring
  have t5 : L ^ 3 * (1 + Real.log L) * (X / q + L) ≤ 24 * lT ^ 5 * T ^ s5 + 48 * lT ^ 5 := by
    have hL3 : L ^ 3 ≤ (2 * lT) ^ 3 := pow_le_pow_left₀ hL0.le hLle 3
    have hlog3 : 1 + Real.log L ≤ 3 * lT := by linarith
    have hsum : X / q + L ≤ T ^ s5 + 2 * lT := by linarith
    calc L ^ 3 * (1 + Real.log L) * (X / q + L) ≤ (2 * lT) ^ 3 * (3 * lT) * (T ^ s5 + 2 * lT) := by
          apply mul_le_mul (mul_le_mul hL3 hlog3 (by linarith) (by positivity)) hsum
            (by positivity) (by positivity)
      _ = 24 * lT ^ 4 * T ^ s5 + 48 * lT ^ 5 := by ring
      _ ≤ 24 * lT ^ 5 * T ^ s5 + 48 * lT ^ 5 := by
          have := mul_le_mul_of_nonneg_right hlT5 hTs5
          nlinarith
  have t6 : L * l * Real.log l * ((1 + Real.log q) ^ 2 * l ^ 2 + q * l ^ 2 + (X / q + 1) * L ^ 2)
      ≤ 8 * lT ^ 7 + 2 * lT ^ 5 * T ^ κhi + 8 * lT ^ 5 * T ^ s5 + 8 * lT ^ 5 := by
    have a : (1 + Real.log q) ^ 2 ≤ (2 * lT) ^ 2 := pow_le_pow_left₀ h1q0 h1q 2
    have b : l ^ 2 ≤ lT ^ 2 := pow_le_pow_left₀ hl0.le hhi 2
    have hL2 : L ^ 2 ≤ (2 * lT) ^ 2 := pow_le_pow_left₀ hL0.le hLle 2
    have hin : (1 + Real.log q) ^ 2 * l ^ 2 + q * l ^ 2 + (X / q + 1) * L ^ 2
        ≤ (2 * lT) ^ 2 * lT ^ 2 + T ^ κhi * lT ^ 2 + (T ^ s5 + 1) * (2 * lT) ^ 2 := by
      have i1 := mul_le_mul a b (by positivity) (by positivity)
      have i2 := mul_le_mul hqT b (by positivity) hTκ
      have i3 := mul_le_mul (by linarith : X / q + 1 ≤ T ^ s5 + 1) hL2 (by positivity) (by positivity)
      linarith
    have hpre : L * l * Real.log l ≤ (2 * lT) * lT * lT :=
      mul_le_mul (mul_le_mul hLle hhi hl0.le (by positivity)) hlogl hlogl0 (by positivity)
    calc L * l * Real.log l * ((1 + Real.log q) ^ 2 * l ^ 2 + q * l ^ 2 + (X / q + 1) * L ^ 2)
        ≤ (2 * lT) * lT * lT * ((2 * lT) ^ 2 * lT ^ 2 + T ^ κhi * lT ^ 2 + (T ^ s5 + 1) * (2 * lT) ^ 2) :=
          mul_le_mul hpre hin (by positivity) (by positivity)
      _ = 8 * lT ^ 7 + 2 * lT ^ 5 * T ^ κhi + 8 * lT ^ 5 * T ^ s5 + 8 * lT ^ 5 := by ring
  unfold famMaj
  linarith

/-- `ℓ₁(q, T) ≤ log q + l + 1`. -/
theorem ell1q_le_log_add {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 0 < T) :
    ell1q q T ≤ Real.log q + Zeta23.l T + 1 := by
  rw [ell1q_eq_log_add hq hT]
  have := Real.log_two_lt_d9
  linarith

/-- `X/q ≤ T^{λ − κ}` for `X = e^{λ l}`, `q ≥ T^κ`. -/
theorem exp_div_le_rpow {lam κ T : ℝ} {q : ℕ} (hlam : 0 ≤ lam) (hT : 0 < T)
    (hl : Zeta23.l T ≤ Real.log T) (hq : T ^ κ ≤ q) :
    Real.exp (lam * Zeta23.l T) / q ≤ T ^ (lam - κ) := by
  have hX := exp_lam_l_le hlam hT hl
  have hTκ : 0 < T ^ κ := by positivity
  rw [Real.rpow_sub hT]
  calc Real.exp (lam * Zeta23.l T) / q ≤ T ^ lam / q :=
        div_le_div_of_nonneg_right hX (hTκ.le.trans hq)
    _ ≤ T ^ lam / T ^ κ := div_le_div_of_nonneg_left (by positivity) hTκ hq

/-- `log² (log q + 8) ≤ c log T` uniformly in `q ≤ T`, eventually. -/
theorem eventually_loglog_q_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ q : ℕ, 1 ≤ q → Real.log q ≤ Real.log T →
      Real.log (Real.log q + 8) ^ 2 ≤ c * Real.log T := by
  filter_upwards [eventually_log_sq_le (A := 1) zero_le_one hc] with T hT q hq hlq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have h1 : Real.log (Real.log q + 8) ≤ Real.log (1 * Real.log T + 8) :=
    Real.log_le_log (by positivity) (by linarith)
  have h0 : 0 ≤ Real.log (Real.log q + 8) := Real.log_nonneg (by linarith)
  exact (pow_le_pow_left₀ h0 h1 2).trans hT

/-- **The Frobenius majorant is `o(T l L²)` uniformly in a modulus cell.** -/
theorem eventually_famMaj_le {lam κlo κhi d : ℝ} (h0 : 0 < lam) (h2 : lam < 2) (hκ : lam - κlo < 1)
    (hκhi : κhi < 1) (hd : 0 < d) :
    ∀ᶠ T : ℝ in atTop, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ T ^ κhi → T ^ κlo ≤ q →
      famMaj q T (lam * Zeta23.l T) (Zeta23.l T) (Real.exp (lam * Zeta23.l T))
        ≤ d * (T * Zeta23.l T * (lam * Zeta23.l T) ^ 2) := by
  obtain ⟨D, hD⟩ : ∃ x : ℝ, x = d * lam ^ 2 / 8 := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; positivity
  filter_upwards [eventually_l_bounds, eventually_gt_atTop (0 : ℝ),
    eventually_log_pow_rpow_le 4 (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) ≤ 72)
      (by positivity : (0:ℝ) < D / 8),
    Real.tendsto_log_atTop.eventually_ge_atTop (576 / D),
    eventually_log_pow_rpow_le 0 (by linarith : lam / 2 < 1) (by norm_num : (0:ℝ) ≤ 2)
      (by positivity : (0:ℝ) < D / 8),
    eventually_loglog_q_le (by positivity : (0:ℝ) < D / 64),
    Real.tendsto_log_atTop.eventually_ge_atTop (64 / D),
    eventually_log_pow_rpow_le 2 hκ (by norm_num : (0:ℝ) ≤ 32) (by positivity : (0:ℝ) < D / 8),
    eventually_log_pow_rpow_le 2 hκhi (by norm_num : (0:ℝ) ≤ 2) (by positivity : (0:ℝ) < D / 8),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 / lam)]
    with T ⟨hlog1, hl1, hlo, hhi⟩ hT0 r1 r2 r3 r4 r5 r6 r7 r8 q hq hqT hqT'
  obtain ⟨lT, hlT⟩ : ∃ x : ℝ, x = Real.log T := ⟨_, rfl⟩
  rw [← hlT] at hlog1 hlo hhi r1 r2 r3 r5 r6 r7 r8
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq : Real.log q ≤ lT := by
    have h := Real.log_le_log (by positivity) hqT
    rw [Real.log_rpow hT0, ← hlT] at h
    have : κhi * lT ≤ lT := by nlinarith
    linarith
  have hy := r4 q hq (by rw [← hlT]; exact hlq)
  rw [← hlT] at hy
  have hL1 : 1 ≤ lam * Zeta23.l T := by
    rw [div_le_iff₀ h0] at r8
    nlinarith
  have hB := famMaj_le_bound (q := q) (T := T) (lT := lT) (l := Zeta23.l T) (L := lam * Zeta23.l T)
    (X := Real.exp (lam * Zeta23.l T)) (lam := lam) (κhi := κhi) (s5 := lam - κlo) (c := D / 64)
    hq hT0 hlog1 hl1 hlo hhi rfl h2.le hL1 hlq
    ((l_le_ell1q hq hT0).trans' (by linarith)) (ell1q_le_log_add hq hT0)
    (sqrt_exp_lam_l_le h0.le hT0 (by rw [← hlT] at *; exact hhi)) (Real.exp_pos _).le
    (exp_div_le_rpow h0.le hT0 (by rw [hlT] at hhi; exact hhi) hqT') hqT hy
  -- each piece against `(D/8) T lT³`
  have hlT0 : 0 < lT := by linarith
  have hT1 : 0 ≤ T := hT0.le
  have hlT3 : 0 < lT ^ 3 := by positivity
  have p1 : 64 * lT ^ 5 + 8 * lT ^ 7 ≤ D / 8 * T * lT ^ 3 := by
    rw [Real.rpow_zero, mul_one] at r1
    have h57 : lT ^ 5 ≤ lT ^ 7 := pow_le_pow_right₀ hlog1 (by norm_num)
    have : 72 * lT ^ 4 * lT ^ 3 ≤ D / 8 * T * lT ^ 3 := mul_le_mul_of_nonneg_right r1 hlT3.le
    have e : 72 * lT ^ 4 * lT ^ 3 = 72 * lT ^ 7 := by ring
    linarith
  have p2 : 72 * T * lT ≤ D / 8 * T * lT ^ 3 := by
    rw [div_le_iff₀ hD0] at r2
    have h1 : 72 * 8 ≤ D * lT := by linarith
    have h2' : lT ≤ lT ^ 2 := by nlinarith
    have h3 : 72 * 8 ≤ D * lT ^ 2 := le_trans h1 (mul_le_mul_of_nonneg_left h2' hD0.le)
    have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ T * lT)
    have e1 : D * lT ^ 2 * (T * lT) = 8 * (D / 8 * T * lT ^ 3) := by ring
    have e2 : 72 * 8 * (T * lT) = 8 * (72 * T * lT) := by ring
    linarith only [h4, e1, e2]
  have p3 : 2 * lT ^ 2 * T ^ (lam / 2) ≤ D / 8 * T * lT ^ 3 := by
    rw [pow_zero, mul_one] at r3
    have h1 : 2 * T ^ (lam / 2) * lT ^ 2 ≤ D / 8 * T * lT ^ 2 :=
      mul_le_mul_of_nonneg_right r3 (by positivity)
    have h2' : D / 8 * T * lT ^ 2 ≤ D / 8 * T * lT ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog1 (by norm_num)) (by positivity)
    linarith
  have p4 : 4 * (1 + D / 64 * lT) * T * lT ^ 2 ≤ D / 8 * T * lT ^ 3 := by
    rw [div_le_iff₀ hD0] at r5
    have h1 : 4 * (1 + D / 64 * lT) ≤ D / 8 * lT := by linarith
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ T * lT ^ 2)
    have e1 : 4 * (1 + D / 64 * lT) * T * lT ^ 2 = 4 * (1 + D / 64 * lT) * (T * lT ^ 2) := by ring
    have e2 : D / 8 * T * lT ^ 3 = D / 8 * lT * (T * lT ^ 2) := by ring
    linarith only [this, e1, e2]
  have p5 : 32 * lT ^ 5 * T ^ (lam - κlo) ≤ D / 8 * T * lT ^ 3 := by
    have := mul_le_mul_of_nonneg_right r6 hlT3.le
    have e : 32 * lT ^ 5 * T ^ (lam - κlo) = 32 * lT ^ 2 * T ^ (lam - κlo) * lT ^ 3 := by ring
    linarith only [this, e]
  have p6 : 2 * lT ^ 5 * T ^ κhi ≤ D / 8 * T * lT ^ 3 := by
    have := mul_le_mul_of_nonneg_right r7 hlT3.le
    have e : 2 * lT ^ 5 * T ^ κhi = 2 * lT ^ 2 * T ^ κhi * lT ^ 3 := by ring
    linarith only [this, e]
  have hfin : D * T * lT ^ 3 ≤ d * (T * Zeta23.l T * (lam * Zeta23.l T) ^ 2) := by
    have hl3 : lT ^ 3 ≤ 8 * Zeta23.l T ^ 3 := by
      have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ lT / 2) hlo 3
      nlinarith
    rw [hD]
    have e : d * (T * Zeta23.l T * (lam * Zeta23.l T) ^ 2) = d * lam ^ 2 / 8 * T * (8 * Zeta23.l T ^ 3) := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hl3 (by positivity)
  have hpos : 0 ≤ D * T * lT ^ 3 := by positivity
  linarith only [hB, p1, p2, p3, p4, p5, p6, hfin, hpos]

/-- **The parity-shift term is `o(T l L²)`.** -/
theorem eventually_parity_le {lam M CP d : ℝ} (h0 : 0 < lam) (hM : 0 ≤ M) (hCP : 0 ≤ CP) (hd : 0 < d) :
    ∀ᶠ T : ℝ in atTop,
      4 * ((1 + Zeta23.l T) * (M ^ 2 * (T * (2 * π * (lam * Zeta23.l T)))
        + CP * (lam * Zeta23.l T * Zeta23.l T * Real.log (Zeta23.l T) * (Zeta23.l T + M) ^ 2)))
      ≤ d * (T * Zeta23.l T * (lam * Zeta23.l T) ^ 2) := by
  filter_upwards [eventually_l_bounds, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (128 * π * M ^ 2 / (d * lam)),
    eventually_log_pow_rpow_le 3 (by norm_num : (0:ℝ) < 1)
      (by positivity : (0:ℝ) ≤ 256 * CP * (1 + M) ^ 2) (by positivity : (0:ℝ) < d * lam)]
    with T ⟨hlog1, hl1, hlo, hhi⟩ hT0 r1 r2
  obtain ⟨lT, hlT⟩ : ∃ x : ℝ, x = Real.log T := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ x : ℝ, x = Zeta23.l T := ⟨_, rfl⟩
  rw [← hlT] at hlog1 hlo hhi r1 r2
  rw [← hl] at hl1 hlo hhi ⊢
  rw [Real.rpow_zero, mul_one] at r2
  have hl0 : 0 < l := by linarith
  have hpi : 0 < π := Real.pi_pos
  have hlogl : Real.log l ≤ lT := by have := Real.log_le_sub_one_of_pos hl0; linarith
  have hlogl0 : 0 ≤ Real.log l := Real.log_nonneg hl1
  -- the `M²` part
  have q1 : 4 * ((1 + l) * (M ^ 2 * (T * (2 * π * (lam * l))))) ≤ d / 2 * (T * l * (lam * l) ^ 2) := by
    have h1 : 64 * π * M ^ 2 ≤ d * lam * l := by
      rw [div_le_iff₀ (by positivity)] at r1
      have := mul_le_mul_of_nonneg_right (by linarith : lT ≤ 2 * l) (by positivity : (0:ℝ) ≤ d * lam)
      nlinarith
    have e1 : 4 * ((1 + l) * (M ^ 2 * (T * (2 * π * (lam * l)))))
        = (1 + l) * (8 * π * M ^ 2) * (T * lam * l) := by ring
    have e2 : d / 2 * (T * l * (lam * l) ^ 2) = (d * lam * l) * l / 2 * (T * lam * l) := by ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have h2 : (1 + l) * (8 * π * M ^ 2) ≤ 2 * l * (8 * π * M ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h3 : 2 * l * (8 * π * M ^ 2) = l * (64 * π * M ^ 2) / 4 := by ring
    have h4 : l * (64 * π * M ^ 2) ≤ l * (d * lam * l) := mul_le_mul_of_nonneg_left h1 hl0.le
    have h5 : l * (d * lam * l) = d * lam * l * l := by ring
    nlinarith
  -- the end-effect part
  have q2 : 4 * ((1 + l) * (CP * (lam * l * l * Real.log l * (l + M) ^ 2)))
      ≤ d / 2 * (T * l * (lam * l) ^ 2) := by
    have hlM : l + M ≤ (1 + M) * lT := by nlinarith
    have hlM2 : (l + M) ^ 2 ≤ ((1 + M) * lT) ^ 2 := pow_le_pow_left₀ (by positivity) hlM 2
    have h1l : 1 + l ≤ 2 * lT := by linarith
    have hA : (1 + l) * (l * l * Real.log l * (l + M) ^ 2)
        ≤ (2 * lT) * (lT * lT * lT * ((1 + M) * lT) ^ 2) := by
      apply mul_le_mul h1l _ (by positivity) (by positivity)
      exact mul_le_mul (mul_le_mul (mul_le_mul hhi hhi hl0.le (by positivity)) hlogl hlogl0
        (by positivity)) hlM2 (by positivity) (by positivity)
    have e1 : 4 * ((1 + l) * (CP * (lam * l * l * Real.log l * (l + M) ^ 2)))
        = 4 * CP * lam * ((1 + l) * (l * l * Real.log l * (l + M) ^ 2)) := by ring
    rw [e1]
    have hC := mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ 4 * CP * lam)
    have e2 : 4 * CP * lam * ((2 * lT) * (lT * lT * lT * ((1 + M) * lT) ^ 2))
        = lam * lT ^ 3 / 32 * (256 * CP * (1 + M) ^ 2 * lT ^ 3) := by ring
    have hD := mul_le_mul_of_nonneg_left r2 (by positivity : (0:ℝ) ≤ lam * lT ^ 3 / 32)
    have hl3 : lT ^ 3 ≤ 8 * l ^ 3 := by
      have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ lT / 2) hlo 3
      nlinarith
    have hE : lam * lT ^ 3 / 32 * (d * lam * T) ≤ d / 2 * (T * l * (lam * l) ^ 2) := by
      have h1 : lam * lT ^ 3 / 32 * (d * lam * T) ≤ lam * (8 * l ^ 3) / 32 * (d * lam * T) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl3 h0.le) (by norm_num)
      have e3 : d / 2 * (T * l * (lam * l) ^ 2) = 2 * (lam * (8 * l ^ 3) / 32 * (d * lam * T)) := by ring
      have h2 : 0 ≤ lam * (8 * l ^ 3) / 32 * (d * lam * T) := by positivity
      linarith
    linarith
  have e : 4 * ((1 + l) * (M ^ 2 * (T * (2 * π * (lam * l))) + CP * (lam * l * l * Real.log l * (l + M) ^ 2)))
      = 4 * ((1 + l) * (M ^ 2 * (T * (2 * π * (lam * l))))) + 4 * ((1 + l) * (CP * (lam * l * l * Real.log l * (l + M) ^ 2))) := by
    ring
  rw [e]
  linarith

end RHTower
