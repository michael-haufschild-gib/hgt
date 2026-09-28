import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIHeightWindow
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIMeanSquare

/-!
# The Type-I case of Matomäki–Teräväinen (5.3)

For the Type-I piece `F = M₁ M₂` (`m₁ ∼ M₁ ≤ X^{1/2+ε}`, `M₂ < m₂ ≤ (1+δ)M₂`) the set `U` is cut
into the dyadic height windows `[T/2, T]`, `T = X 2^{-j} ≥ T₀ = exp(c (log X)^{1/2})`.  In each
window the amplifier `P₁(s)^k/k!` with `(2P)^k ≤ T^{1/5} < (2P)^{k+1}` and the arithmetic–geometric
mean split give `√(fourth moment of M₁ · amplified Deshouillers–Iwaniec moment of M₂)`.  With
`k! ≤ (P^k)^{1/a}`, `a ≥ 1.0999`, the saving `(P^k)^{-(1 - 1/a - ε_U/5)} ≤ T^{-0.0178}` beats every
polylogarithm, and the `O(log X)` windows are absorbed into `exp(-(log X)^{1/40})`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory Filter

noncomputable section

/-- **The window value.**  With `f = k!`, `p = P^k ≥ T^{99/500}`, `f ≤ p^{1/a}`,
`q = (P+1)^k ≤ p T^{1/1000}` and `η ≤ 1/1000`, the window bound
`f p^{ε_U/10} √(Λ R · (k+1) C T^η (16T/(N²p) + 4/(T³p)) · 2q/(pf))` is at most
`√(2 (k+1) C Λ R (16T/N² + 4/T³) T^{-3/200})`. -/
theorem typeI_window_value_le {f p q T C k₁ εU a η Λ R N : ℝ}
    (hf : 1 ≤ f) (hp : 1 ≤ p) (hT : 1 ≤ T) (hC : 0 < C) (hk₁ : 0 ≤ k₁) (hΛ : 0 ≤ Λ)
    (hR : 0 ≤ R) (hN : 0 < N) (hη : η ≤ 1 / 1000)
    (hfp : f ≤ p ^ (1 / a)) (hexp : 1 / a + εU / 5 ≤ 91 / 100)
    (hpT : T ^ (99 / 500 : ℝ) ≤ p) (hq0 : 0 ≤ q) (hqp : q ≤ p * T ^ (1 / 1000 : ℝ)) :
    f * p ^ (εU / 10) * Real.sqrt (Λ * R * (k₁ * C * T ^ η *
        (16 * T / (N ^ 2 * p) + 4 / (T ^ 3 * p)) * (2 * q / (p * f)))) ≤
      Real.sqrt (2 * k₁ * C * Λ * (R * (16 * T / N ^ 2 + 4 / T ^ 3)) * T ^ (-3 / 200 : ℝ)) := by
  have hp0 : 0 < p := by linarith
  have hf0 : 0 < f := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨D, hD⟩ : ∃ D, D = 16 * T / N ^ 2 + 4 / T ^ 3 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hsplit : 16 * T / (N ^ 2 * p) + 4 / (T ^ 3 * p) = D / p := by
    rw [hD]; field_simp
  rw [hsplit, ← hD]
  have hpow : (p ^ (εU / 10)) ^ 2 = p ^ (εU / 5) := by
    rw [← Real.rpow_mul_natCast hp0.le]; ring_nf
  have hkey : f * p ^ (εU / 5) * q / p ^ 2 * T ^ η ≤ T ^ (-3 / 200 : ℝ) := by
    have h1 : f * p ^ (εU / 5) ≤ p ^ (91 / 100 : ℝ) := by
      calc f * p ^ (εU / 5) ≤ p ^ (1 / a) * p ^ (εU / 5) := by gcongr
        _ = p ^ (1 / a + εU / 5) := (Real.rpow_add hp0 _ _).symm
        _ ≤ p ^ (91 / 100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp hexp
    have h2 : p ^ (91 / 100 : ℝ) = p ^ (-9 / 100 : ℝ) * p := by
      rw [← Real.rpow_add_one hp0.ne']; norm_num
    have h3 : p ^ (-9 / 100 : ℝ) ≤ (T ^ (99 / 500 : ℝ)) ^ (-9 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hpT (by norm_num)
    have h4 : (T ^ (99 / 500 : ℝ)) ^ (-9 / 100 : ℝ) = T ^ (-891 / 50000 : ℝ) := by
      rw [← Real.rpow_mul hT0.le]; norm_num
    have h5 : T ^ η ≤ T ^ (1 / 1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT hη
    have h6 : T ^ (-891 / 50000 : ℝ) * T ^ (1 / 1000 : ℝ) * T ^ (1 / 1000 : ℝ) ≤
        T ^ (-3 / 200 : ℝ) := by
      rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
      exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    have hq1 : f * p ^ (εU / 5) * q ≤ p ^ (91 / 100 : ℝ) * (p * T ^ (1 / 1000 : ℝ)) :=
      mul_le_mul h1 hqp hq0 (by positivity)
    calc f * p ^ (εU / 5) * q / p ^ 2 * T ^ η
        ≤ p ^ (91 / 100 : ℝ) * (p * T ^ (1 / 1000 : ℝ)) / p ^ 2 * T ^ (1 / 1000 : ℝ) := by
          gcongr
      _ = p ^ (-9 / 100 : ℝ) * T ^ (1 / 1000 : ℝ) * T ^ (1 / 1000 : ℝ) := by
          rw [h2]; field_simp
      _ ≤ T ^ (-891 / 50000 : ℝ) * T ^ (1 / 1000 : ℝ) * T ^ (1 / 1000 : ℝ) := by
          rw [← h4]; gcongr
      _ ≤ _ := h6
  have hx : 0 ≤ f * p ^ (εU / 10) := by positivity
  rw [show f * p ^ (εU / 10) = Real.sqrt ((f * p ^ (εU / 10)) ^ 2) from (Real.sqrt_sq hx).symm,
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hrad : (f * p ^ (εU / 10)) ^ 2 * (Λ * R * (k₁ * C * T ^ η * (D / p) * (2 * q / (p * f)))) =
      (f * p ^ (εU / 5) * q / p ^ 2 * T ^ η) * (2 * k₁ * C * Λ * (R * D)) := by
    rw [mul_pow, hpow]; field_simp
  rw [hrad]
  have hB : 0 ≤ 2 * k₁ * C * Λ * (R * D) := by positivity
  calc (f * p ^ (εU / 5) * q / p ^ 2 * T ^ η) * (2 * k₁ * C * Λ * (R * D))
      ≤ T ^ (-3 / 200 : ℝ) * (2 * k₁ * C * Λ * (R * D)) := mul_le_mul_of_nonneg_right hkey hB
    _ = _ := by ring

/-- **The height bracket.**  For `T ≤ X`, `M₁ ≤ X^{1/2+ε}`, `N ≥ M₂/2` and
`M₁ M₂ ≥ X/(2λ²)`: `T^{-1/200} (1 + T/M₁²)(16T/N² + 4/T³) ≤ 512 λ⁴ + 20`. -/
theorem typeI_height_bracket_le {T X M₁ M₂ N ε lam : ℝ} (hT : 2 ≤ T) (hTX : T ≤ X)
    (hM₁ : 1 / 2 ≤ M₁) (hM₁X : M₁ ≤ X ^ (1 / 2 + ε)) (hM₂ : 0 < M₂) (hN : M₂ / 2 ≤ N)
    (hprod : X / (2 * lam ^ 2) ≤ M₁ * M₂) (hlam : 1 ≤ lam) (hε1 : ε ≤ 1 / 10000) :
    T ^ (-1 / 200 : ℝ) * ((1 + T / M₁ ^ 2) * (16 * T / N ^ 2 + 4 / T ^ 3)) ≤
      512 * lam ^ 4 + 20 := by
  have hX0 : 0 < X := by linarith
  have hT0 : 0 < T := by linarith
  have hM₁0 : 0 < M₁ := by linarith
  have hN0 : 0 < N := by linarith
  have hlam0 : 0 < lam := by linarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = T ^ (-1 / 200 : ℝ) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hs1 : s ≤ 1 := by
    rw [hsdef]; exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  rw [← hsdef]
  have hMN : X ^ 2 ≤ 16 * lam ^ 4 * (M₁ * N) ^ 2 := by
    have h1 : X / (4 * lam ^ 2) ≤ M₁ * N := by
      have hmm : M₁ * M₂ ≤ 2 * (M₁ * N) := by nlinarith
      have h4 : X / (4 * lam ^ 2) = X / (2 * lam ^ 2) / 2 := by field_simp; ring
      rw [h4]; linarith
    have h2 : 0 ≤ X / (4 * lam ^ 2) := by positivity
    have h3 := pow_le_pow_left₀ h2 h1 2
    rw [div_pow, div_le_iff₀ (by positivity)] at h3
    calc X ^ 2 ≤ (M₁ * N) ^ 2 * (4 * lam ^ 2) ^ 2 := h3
      _ = 16 * lam ^ 4 * (M₁ * N) ^ 2 := by ring
  have hM₁sq : M₁ ^ 2 ≤ X ^ (1 + 2 * ε) := by
    have h := pow_le_pow_left₀ hM₁0.le hM₁X 2
    rw [← Real.rpow_natCast (X ^ (1 / 2 + ε)) 2, ← Real.rpow_mul hX0.le] at h
    calc M₁ ^ 2 ≤ X ^ ((1 / 2 + ε) * ((2 : ℕ) : ℝ)) := h
      _ = X ^ (1 + 2 * ε) := by congr 1; push_cast; ring
  have hXsplit : X ^ 2 = X ^ (1 + 2 * ε) * X ^ (1 - 2 * ε) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_natCast]; norm_num
  have hN2 : X ^ (1 - 2 * ε) ≤ 16 * lam ^ 4 * N ^ 2 := by
    have hpos : 0 < X ^ (1 + 2 * ε) := by positivity
    have h : X ^ (1 + 2 * ε) * X ^ (1 - 2 * ε) ≤ X ^ (1 + 2 * ε) * (16 * lam ^ 4 * N ^ 2) := by
      rw [← hXsplit]
      calc X ^ 2 ≤ 16 * lam ^ 4 * (M₁ * N) ^ 2 := hMN
        _ = M₁ ^ 2 * (16 * lam ^ 4 * N ^ 2) := by ring
        _ ≤ X ^ (1 + 2 * ε) * (16 * lam ^ 4 * N ^ 2) := by gcongr
    exact le_of_mul_le_mul_left h hpos
  have hsT : s * T ≤ X ^ (1 - 2 * ε) := by
    have h1 : s * T = T ^ (199 / 200 : ℝ) := by
      rw [hsdef, ← Real.rpow_add_one hT0.ne']; norm_num
    rw [h1]
    calc T ^ (199 / 200 : ℝ) ≤ X ^ (199 / 200 : ℝ) := Real.rpow_le_rpow hT0.le hTX (by norm_num)
      _ ≤ X ^ (1 - 2 * ε) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hA : s * (16 * T / N ^ 2) ≤ 256 * lam ^ 4 := by
    rw [show s * (16 * T / N ^ 2) = 16 * (s * T) / N ^ 2 by ring, div_le_iff₀ (by positivity)]
    linarith
  have hB : s * (4 / T ^ 3) ≤ 4 := by
    have hT3 : 1 ≤ T ^ 3 := one_le_pow₀ (by linarith)
    have : 4 / T ^ 3 ≤ 4 := div_le_self (by norm_num) hT3
    nlinarith
  have hC : s * (T / M₁ ^ 2 * (16 * T / N ^ 2)) ≤ 256 * lam ^ 4 := by
    have hsT2 : s * T ^ 2 ≤ X ^ 2 := by
      have : T ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hT0.le hTX 2
      nlinarith [sq_nonneg T]
    rw [show s * (T / M₁ ^ 2 * (16 * T / N ^ 2)) = 16 * (s * T ^ 2) / (M₁ * N) ^ 2 by
      field_simp, div_le_iff₀ (by positivity)]
    nlinarith
  have hD : s * (T / M₁ ^ 2 * (4 / T ^ 3)) ≤ 16 := by
    rw [show s * (T / M₁ ^ 2 * (4 / T ^ 3)) = 4 * s / (M₁ ^ 2 * T ^ 2) by field_simp,
      div_le_iff₀ (by positivity)]
    have hM₁T : 1 ≤ M₁ ^ 2 * T ^ 2 := by
      have : 1 ≤ M₁ * T := by nlinarith
      nlinarith
    nlinarith
  have hexp : s * ((1 + T / M₁ ^ 2) * (16 * T / N ^ 2 + 4 / T ^ 3)) =
      s * (16 * T / N ^ 2) + s * (4 / T ^ 3) + s * (T / M₁ ^ 2 * (16 * T / N ^ 2)) +
        s * (T / M₁ ^ 2 * (4 / T ^ 3)) := by ring
  rw [hexp]
  linarith

/-- **The amplifier degree at height `T`.**  `k = ⌊log T^{1/5} / log 2P⌋` satisfies
`(2P)^k ≤ T^{1/5}`, `P^k ≥ T^{99/500}`, `(P+1)^k ≤ P^k T^{1/1000}` and `k ≤ log X ≤ P^{1/a}`,
provided `2^{200} ≤ 2P ≤ T^{1/1000}` and `(log X)^a ≤ P`. -/
theorem typeI_amplifier_degree_facts {T P X a : ℝ} {k : ℕ}
    (hk : k = amplifierDegree (T ^ (1 / 5 : ℝ)) P) (hP : 1 ≤ P) (h2P : 2 ^ 200 ≤ 2 * P)
    (hPT : 2 * P ≤ T ^ (1 / 1000 : ℝ)) (hT : 1 ≤ T) (hTX : T ≤ X) (ha : 0 < a)
    (hPa : Real.log X ^ a ≤ P) :
    1 ≤ k ∧ (2 * P) ^ k ≤ T ^ (1 / 5 : ℝ) ∧ T ^ (99 / 500 : ℝ) ≤ P ^ k ∧
      (P + 1) ^ k ≤ P ^ k * T ^ (1 / 1000 : ℝ) ∧ (k : ℝ) ≤ P ^ (1 / a) ∧
      (k : ℝ) ≤ Real.log X := by
  have hT0 : 0 < T := by linarith
  have hP0 : 0 < P := by linarith
  have hT5 : 1 ≤ T ^ (1 / 5 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have h1000 : T ^ (1 / 1000 : ℝ) ≤ T ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hk1 : 1 ≤ k := hk ▸ one_le_amplifierDegree hP (hPT.trans h1000)
  have hkT : (2 * P) ^ k ≤ T ^ (1 / 5 : ℝ) := hk ▸ two_mul_pow_amplifierDegree_le hP hT5
  have hlt : T ^ (1 / 5 : ℝ) < (2 * P) ^ (k + 1) :=
    hk ▸ lt_two_mul_pow_amplifierDegree_succ hP (by positivity)
  -- `2^k ≤ T^{1/1000}`
  have h2k : (2 : ℝ) ^ k ≤ T ^ (1 / 1000 : ℝ) := by
    have h200 : ((2 : ℝ) ^ k) ^ 200 ≤ T ^ (1 / 5 : ℝ) := by
      calc ((2 : ℝ) ^ k) ^ 200 = ((2 : ℝ) ^ 200) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (2 * P) ^ k := pow_le_pow_left₀ (by positivity) h2P k
        _ ≤ _ := hkT
    have h := Real.rpow_le_rpow (by positivity) h200 (by norm_num : (0 : ℝ) ≤ ((200 : ℕ) : ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast (by positivity) (by norm_num), ← Real.rpow_mul hT0.le] at h
    calc (2 : ℝ) ^ k ≤ T ^ (1 / 5 * ((200 : ℕ) : ℝ)⁻¹) := h
      _ = T ^ (1 / 1000 : ℝ) := by norm_num
  have hpk : T ^ (99 / 500 : ℝ) ≤ P ^ k := by
    have hsplit : T ^ (1 / 5 : ℝ) = T ^ (99 / 500 : ℝ) * (T ^ (1 / 1000 : ℝ) * T ^ (1 / 1000 : ℝ)) := by
      rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]; norm_num
    have hup : (2 * P) ^ (k + 1) ≤ P ^ k * (T ^ (1 / 1000 : ℝ) * T ^ (1 / 1000 : ℝ)) := by
      calc (2 * P) ^ (k + 1) = P ^ k * ((2 : ℝ) ^ k * (2 * P)) := by ring
        _ ≤ P ^ k * (T ^ (1 / 1000 : ℝ) * T ^ (1 / 1000 : ℝ)) := by gcongr
    have hpos : 0 < T ^ (1 / 1000 : ℝ) * T ^ (1 / 1000 : ℝ) := by positivity
    have h := hlt.le.trans hup
    rw [hsplit] at h
    exact le_of_mul_le_mul_right h hpos
  have hq : (P + 1) ^ k ≤ P ^ k * T ^ (1 / 1000 : ℝ) := by
    calc (P + 1) ^ k ≤ (2 * P) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = P ^ k * (2 : ℝ) ^ k := by ring
      _ ≤ P ^ k * T ^ (1 / 1000 : ℝ) := by gcongr
  have hkX : (k : ℝ) ≤ Real.log X := by
    have he : Real.exp 1 ≤ 2 * P := by
      have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have h8 : (3 : ℝ) ≤ 2 ^ 200 := by norm_num
      linarith
    have h := amplifierDegree_le_log he hT5
    rw [← hk] at h
    have hT5X : T ^ (1 / 5 : ℝ) ≤ X := by
      calc T ^ (1 / 5 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
        _ = T := Real.rpow_one T
        _ ≤ X := hTX
    exact h.trans (Real.log_le_log (by positivity) hT5X)
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (hT.trans hTX)
  have hkP : (k : ℝ) ≤ P ^ (1 / a) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hlog0 a) hPa (by positivity : (0 : ℝ) ≤ 1 / a)
    rw [one_div, Real.rpow_rpow_inv hlog0 ha.ne'] at h
    rw [one_div]; exact hkX.trans h
  exact ⟨hk1, hkT, hpk, hq, hkP, hkX⟩

/-- **The long-factor scales.**  If `M₁ ≥ 1/2`, `M₁ ≤ X^{1/2+ε}` and `M₁ M₂ > Y/2 ≥ X/(2λ²)`
with `6λ² X^{1/2+ε} ≤ X`, then `M₂ ≥ 3`, so `N = ⌊M₂⌋ ≥ max(1, M₂/2)` and
`⌊(1+δ)M₂⌋ ≤ 2N` for `δ ≤ 1/2`. -/
theorem typeI_long_scale_facts {X Y δ ε lam M₁ M₂ : ℝ} (hlam1 : 1 ≤ lam)
    (hbig : 6 * lam ^ 2 * X ^ (1 / 2 + ε) ≤ X) (hM₁0 : 0 < M₁) (hM₁X : M₁ ≤ X ^ (1 / 2 + ε))
    (hY : X / lam ^ 2 ≤ Y) (hprod : Y / 2 < M₁ * M₂) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    X / (2 * lam ^ 2) ≤ M₁ * M₂ ∧ 1 ≤ ⌊M₂⌋₊ ∧ M₂ / 2 ≤ (⌊M₂⌋₊ : ℝ) ∧
      ⌊(1 + δ) * M₂⌋₊ ≤ 2 * ⌊M₂⌋₊ := by
  have hlam0 : 0 < lam := by linarith
  have hprod' : X / (2 * lam ^ 2) ≤ M₁ * M₂ := by
    have : X / (2 * lam ^ 2) = X / lam ^ 2 / 2 := by field_simp
    rw [this]; linarith
  have hM₂3 : 3 ≤ M₂ := by
    by_contra hlt
    push Not at hlt
    have h1 : M₁ * M₂ < 3 * X ^ (1 / 2 + ε) := by
      calc M₁ * M₂ < M₁ * 3 := mul_lt_mul_of_pos_left hlt hM₁0
        _ ≤ X ^ (1 / 2 + ε) * 3 := by linarith
        _ = 3 * X ^ (1 / 2 + ε) := by ring
    have h3 : X / (2 * lam ^ 2) < 3 * X ^ (1 / 2 + ε) := hprod'.trans_lt h1
    rw [div_lt_iff₀ (by positivity)] at h3
    linarith
  have hM₂0 : 0 ≤ M₂ := by linarith
  have hfl := Nat.lt_floor_add_one M₂
  have hN1 : 1 ≤ ⌊M₂⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hN2 : M₂ / 2 ≤ (⌊M₂⌋₊ : ℝ) := by linarith
  have hN' : ⌊(1 + δ) * M₂⌋₊ ≤ 2 * ⌊M₂⌋₊ := by
    have h : ⌊(1 + δ) * M₂⌋₊ < 2 * ⌊M₂⌋₊ + 1 := by
      rw [Nat.floor_lt (by positivity)]
      push_cast
      nlinarith
    omega
  exact ⟨hprod', hN1, hN2, hN'⟩

/-- The short factor vanishes when `M₁ < 1/2`: no integer lies in `(M₁, 2M₁]`. -/
theorem mtTypeIShortFactor_eq_zero {X Y δ ε : ℝ} (data : MTTypeIPieceData X Y δ ε)
    (h : data.M₁ < 1 / 2) (t : ℝ) : mtTypeIShortFactor data t = 0 := by
  unfold mtTypeIShortFactor perronPoly
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  dsimp only
  rw [mtRealIntervalAF_apply_of_pos _ _ _ (by omega)]
  have hn' : ¬ (data.M₁ < (n : ℝ) ∧ (n : ℝ) ≤ 2 * data.M₁) := by
    rintro ⟨-, h2⟩
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  rw [if_neg hn', zero_mul]

/-- An empty unit block vanishes. -/
theorem mtWattUnitBlock_eq_zero_of_le {N N' : ℕ} (h : N' ≤ N) (t : ℝ) :
    mtWattUnitBlock N N' t = 0 := by
  unfold mtWattUnitBlock perronPoly
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn1 := Finset.mem_Icc.1 hn
  dsimp only
  rw [mtRealIntervalAF_apply_of_pos _ _ _ (by omega)]
  have hn' : ¬ ((N : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (N' : ℝ)) := by
    rintro ⟨h1, -⟩
    have h1' : N < n := by exact_mod_cast h1
    omega
  rw [if_neg hn', zero_mul]

/-- **Dyadic height windows.**  For `U ⊆ [T₀, X]`, `U` is covered by the windows
`[X 2^{-j-1}, X 2^{-j}]`, `j ≤ log₂(2X/T₀)`. -/
theorem setIntegral_le_sum_height_windows {F : ℝ → ℝ} (hF : Continuous F)
    (hnn : ∀ t, 0 ≤ F t) {U : Set ℝ} {X T₀ : ℝ} (hT₀ : 0 < T₀) (hT₀X : T₀ ≤ X)
    (hU : U ⊆ Set.Icc T₀ X) :
    ∫ t in U, F t ≤ ∑ j : Fin (Nat.log 2 ⌊2 * X / T₀⌋₊ + 1),
      ∫ t in U ∩ Set.Icc (X * (1 / 2) ^ ((j : ℕ) + 1)) (X * (1 / 2) ^ (j : ℕ)), F t := by
  have hX0 : 0 < X := by linarith
  have hX' : 1 ≤ 2 * X / T₀ := by rw [le_div_iff₀ hT₀]; linarith
  refine setIntegral_le_sum_setIntegral_of_subset_iUnion (a := 0) (b := X) hF ?_ ?_ hnn
  · intro j t ht
    obtain ⟨h1, h2⟩ := hU ht.1
    exact ⟨by linarith, h2⟩
  · intro t ht
    obtain ⟨h1, h2⟩ := hU ht
    have hy : 1 / (2 * X / T₀) < t / X := by
      rw [one_div_div, div_lt_div_iff₀ (by positivity) hX0]; nlinarith
    have hy1 : t / X ≤ 1 := by rw [div_le_one hX0]; exact h2
    obtain ⟨j, hj, hlo, hhi⟩ := exists_half_pow_level hX' hy hy1
    rw [le_div_iff₀ hX0] at hlo
    rw [div_le_iff₀ hX0] at hhi
    refine Set.mem_iUnion.2 ⟨⟨j, hj⟩, ht, ?_, ?_⟩
    · show X * (1 / 2) ^ (j + 1) ≤ t
      linarith
    · show t ≤ X * (1 / 2) ^ j
      linarith

/-- **One window, absorbed.**  The window bound is at most
`√(1600 · 532 · C · 2^m Λ₀^{m+5} T₀^{-1/100})`, `Λ₀ ≥ λ + 1`. -/
theorem typeI_window_bound_le {I f p q T C k εU a L M₁ M₂ N X ε lam T₀ Λ₀ : ℝ} {m : ℕ}
    (hI : I ≤ f * p ^ (εU / 10) * Real.sqrt (800 * L ^ m * (1 + T / M₁ ^ 2) *
      ((k + 1) * C * T ^ (1 / 1000 : ℝ) * (16 * T / (N ^ 2 * p) + 4 / (T ^ 3 * p)) *
        (2 * q / (p * f)))))
    (hf : 1 ≤ f) (hp : 1 ≤ p) (hT : 2 ≤ T) (hTX : T ≤ X) (hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T)
    (hC : 0 < C) (hk : 0 ≤ k) (hklam : k ≤ lam) (hlam : 1 ≤ lam) (hlamΛ : lam + 1 ≤ Λ₀)
    (hL : 0 ≤ L) (hLΛ : L ≤ 2 * Λ₀)
    (hM₁ : 1 / 2 ≤ M₁) (hM₁X : M₁ ≤ X ^ (1 / 2 + ε)) (hM₂ : 0 < M₂) (hN : M₂ / 2 ≤ N)
    (hprod : X / (2 * lam ^ 2) ≤ M₁ * M₂) (hε1 : ε ≤ 1 / 10000)
    (hfp : f ≤ p ^ (1 / a)) (hexp : 1 / a + εU / 5 ≤ 91 / 100)
    (hpT : T ^ (99 / 500 : ℝ) ≤ p) (hq0 : 0 ≤ q) (hqp : q ≤ p * T ^ (1 / 1000 : ℝ)) :
    I ≤ Real.sqrt (1600 * C * 532 * 2 ^ m * Λ₀ ^ (m + 5) * T₀ ^ (-1 / 100 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hM₁0 : 0 < M₁ := by linarith
  have h1 := typeI_window_value_le (k₁ := k + 1) (Λ := 800 * L ^ m) (R := 1 + T / M₁ ^ 2)
    hf hp hT1 hC (by linarith) (by positivity) (by positivity) hN0 le_rfl hfp hexp hpT hq0 hqp
  refine hI.trans (h1.trans (Real.sqrt_le_sqrt ?_))
  have h2 := typeI_height_bracket_le hT hTX hM₁ hM₁X hM₂ hN hprod hlam hε1
  have hsplit : T ^ (-3 / 200 : ℝ) = T ^ (-1 / 200 : ℝ) * T ^ (-1 / 100 : ℝ) := by
    rw [← Real.rpow_add hT0]; norm_num
  have hT₀T' : T ^ (-1 / 100 : ℝ) ≤ T₀ ^ (-1 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hT₀ hT₀T (by norm_num)
  have hΛ1 : 1 ≤ Λ₀ := by linarith
  have hLm : L ^ m ≤ 2 ^ m * Λ₀ ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hL hLΛ m
  have hbr : 512 * lam ^ 4 + 20 ≤ 532 * Λ₀ ^ 4 := by
    have h4 : lam ^ 4 ≤ Λ₀ ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    have h5 : 1 ≤ Λ₀ ^ 4 := one_le_pow₀ hΛ1
    linarith
  have hk1 : k + 1 ≤ Λ₀ := by linarith
  have hbr' : T ^ (-1 / 200 : ℝ) * ((1 + T / M₁ ^ 2) * (16 * T / N ^ 2 + 4 / T ^ 3)) ≤
      532 * Λ₀ ^ 4 := h2.trans hbr
  calc 2 * (k + 1) * C * (800 * L ^ m) * ((1 + T / M₁ ^ 2) * (16 * T / N ^ 2 + 4 / T ^ 3)) *
        T ^ (-3 / 200 : ℝ)
      = 1600 * C * (k + 1) * L ^ m *
          (T ^ (-1 / 200 : ℝ) * ((1 + T / M₁ ^ 2) * (16 * T / N ^ 2 + 4 / T ^ 3))) *
          T ^ (-1 / 100 : ℝ) := by rw [hsplit]; ring
    _ ≤ 1600 * C * Λ₀ * (2 ^ m * Λ₀ ^ m) * (532 * Λ₀ ^ 4) * T₀ ^ (-1 / 100 : ℝ) := by
        gcongr
    _ = 1600 * C * 532 * 2 ^ m * Λ₀ ^ (m + 5) * T₀ ^ (-1 / 100 : ℝ) := by ring

/-- **The Type-I case of (5.3), explicit form, given Deshouillers–Iwaniec.**  Summing the
absorbed window bound over the `⌊log₂(2X/T₀)⌋ + 1` dyadic height windows. -/
theorem typeI_setIntegral_le_explicit (hDI : MTDeshouillersIwaniecBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X Y δ ε : ℝ} (data : MTTypeIPieceData X Y δ ε) {B : Finset ℕ}
      {P a εU lam T₀ : ℝ} {U : Set ℝ},
      MTUniformDivisorBounded 5 data.α → lam = Real.log X → 1 ≤ lam →
      (∀ p ∈ B, p.Prime) → (∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) → 2 ≤ P → 2 ^ 200 ≤ 2 * P →
      2 * P ≤ T₀ ^ (1 / 1000 : ℝ) → 0 < a → Real.log X ^ a ≤ P → 0 ≤ εU →
      1 / a + εU / 5 ≤ 91 / 100 → 2 ≤ T₀ → T₀ ≤ X → 6 * lam ^ 2 * X ^ (1 / 2 + ε) ≤ X →
      X / lam ^ 2 ≤ Y → ε ≤ 1 / 10000 → 0 ≤ δ → δ ≤ 1 / 2 →
      MeasurableSet U → U ⊆ Set.Icc T₀ X →
      (∀ t ∈ U, P ^ (-εU / 10) ≤
        ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
      ∫ t in U, ‖mtTypeIShortFactor data t * mtTypeILongFactor data t‖ ^ (2 : ℕ) ≤
        ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) *
          Real.sqrt (1600 * C * 532 * 2 ^ fourthMomentExponent 5 *
            (1 + Real.log (24 * X)) ^ (fourthMomentExponent 5 + 5) * T₀ ^ (-1 / 100 : ℝ)) := by
  obtain ⟨C, hC, hwin⟩ := setIntegral_typeI_window_le hDI (η := 1 / 1000) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro X Y δ ε data B P a εU lam T₀ U hα hlam hlam1 hBp hB hP h2P hPT₀ ha hPa hεU hexp hT₀
    hT₀X hbig hY hε1 hδ0 hδ hUm hUsub hS
  obtain ⟨m, hm⟩ : ∃ m, m = fourthMomentExponent 5 := ⟨_, rfl⟩
  rw [← hm]
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀, Λ₀ = 1 + Real.log (24 * X) := ⟨_, rfl⟩
  rw [← hΛ₀]
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hlamΛ : lam + 1 ≤ Λ₀ := by
    rw [hΛ₀, hlam, Real.log_mul (by norm_num) hX0.ne']
    have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    linarith
  have hΛ1 : 1 ≤ Λ₀ := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Real.sqrt (1600 * C * 532 * 2 ^ m * Λ₀ ^ (m + 5) *
      T₀ ^ (-1 / 100 : ℝ)) := ⟨_, rfl⟩
  rw [← hQ]
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact Real.sqrt_nonneg _
  have hcont : Continuous fun t => ‖mtTypeIShortFactor data t * mtTypeILongFactor data t‖ ^ 2 :=
    ((continuous_mtTypeIShortFactor data).mul (continuous_mtTypeILongFactor data)).norm.pow 2
  -- the short factor is empty below `1/2`
  by_cases hM₁ : data.M₁ < 1 / 2
  · have hz : ∀ t, ‖mtTypeIShortFactor data t * mtTypeILongFactor data t‖ ^ 2 = 0 := by
      intro t; rw [mtTypeIShortFactor_eq_zero data hM₁ t]; simp
    simp_rw [hz]
    simp only [integral_zero]
    positivity
  push Not at hM₁
  obtain ⟨hprod, hN1, hN2, hN'⟩ := typeI_long_scale_facts hlam1 hbig data.M₁_pos data.M₁_le hY
    data.product_mem.1 hδ0 hδ
  have hM₂0 := data.M₂_pos
  have hlong : ∀ t, mtTypeILongFactor data t =
      mtWattUnitBlock ⌊data.M₂⌋₊ ⌊(1 + δ) * data.M₂⌋₊ t := fun t =>
    perronPoly_mtRealUnitInterval_eq_mtWattUnitBlock hM₂0.le (by positivity) t
  -- the long factor is empty when no integer lies in `(M₂, (1+δ)M₂]`
  by_cases hNN' : ⌊(1 + δ) * data.M₂⌋₊ ≤ ⌊data.M₂⌋₊
  · have hz : ∀ t, ‖mtTypeIShortFactor data t * mtTypeILongFactor data t‖ ^ 2 = 0 := by
      intro t; rw [hlong t, mtWattUnitBlock_eq_zero_of_le hNN' t]; simp
    simp_rw [hz]
    simp only [integral_zero]
    positivity
  push Not at hNN'
  -- the logarithm of the short scale
  have hL0 : 0 ≤ 1 + Real.log (16 * data.M₁ ^ 2) := by
    have := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 16 * data.M₁ ^ 2); linarith
  have hLΛ : 1 + Real.log (16 * data.M₁ ^ 2) ≤ 2 * Λ₀ := by
    have hM₁X1 : data.M₁ ≤ X := by
      calc data.M₁ ≤ X ^ (1 / 2 + ε) := data.M₁_le
        _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
        _ = X := Real.rpow_one X
    have h16 : 16 * data.M₁ ^ 2 ≤ (24 * X) ^ 2 := by nlinarith
    have hlog := Real.log_le_log (by positivity) h16
    rw [Real.log_pow] at hlog
    rw [hΛ₀]; push_cast at hlog; linarith
  refine (setIntegral_le_sum_height_windows hcont (fun t => by positivity) (by linarith) hT₀X
    hUsub).trans ?_
  calc ∑ j : Fin (Nat.log 2 ⌊2 * X / T₀⌋₊ + 1),
        ∫ t in U ∩ Set.Icc (X * (1 / 2) ^ ((j : ℕ) + 1)) (X * (1 / 2) ^ (j : ℕ)),
          ‖mtTypeIShortFactor data t * mtTypeILongFactor data t‖ ^ 2
      ≤ ∑ _j : Fin (Nat.log 2 ⌊2 * X / T₀⌋₊ + 1), Q := by
        refine Finset.sum_le_sum fun j _ => ?_
        obtain ⟨T, hTdef⟩ : ∃ T, T = X * (1 / 2) ^ (j : ℕ) := ⟨_, rfl⟩
        have hEsub : U ∩ Set.Icc (X * (1 / 2) ^ ((j : ℕ) + 1)) (X * (1 / 2) ^ (j : ℕ)) ⊆
            Set.Icc (T / 2) T := by
          intro t ht
          refine ⟨?_, hTdef ▸ ht.2.2⟩
          have h := ht.2.1
          rw [pow_succ] at h
          rw [hTdef]; linarith
        rcases (U ∩ Set.Icc (X * (1 / 2) ^ ((j : ℕ) + 1)) (X * (1 / 2) ^ (j : ℕ))).eq_empty_or_nonempty
          with hE | ⟨t₀, ht₀⟩
        · rw [hE, setIntegral_empty]; exact hQ0
        have hT₀T : T₀ ≤ T := (hUsub ht₀.1).1.trans (hTdef ▸ ht₀.2.2)
        have hTX : T ≤ X := by
          rw [hTdef]
          have : (1 / 2 : ℝ) ^ (j : ℕ) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          nlinarith
        have hT2 : 2 ≤ T := hT₀.trans hT₀T
        have hPT : 2 * P ≤ T ^ (1 / 1000 : ℝ) :=
          hPT₀.trans (Real.rpow_le_rpow (by linarith) hT₀T (by norm_num))
        obtain ⟨k, hk⟩ : ∃ k, k = amplifierDegree (T ^ (1 / 5 : ℝ)) P := ⟨_, rfl⟩
        obtain ⟨hk1, hkT, hpk, hq, hkP, hkX⟩ := typeI_amplifier_degree_facts hk (by linarith) h2P
          hPT (by linarith) hTX ha hPa
        have hw := hwin data hα hM₁ hδ0 hN1 hNN' hN' hBp hB hP hk1 (Nat.le_ceil _) hT2 hkT hεU
          (hUm.inter measurableSet_Icc) hEsub (fun t ht => hS t ht.1)
        unfold fourthMomentBound at hw
        rw [← hm] at hw
        have hf : (1 : ℝ) ≤ k.factorial := by exact_mod_cast k.factorial_pos
        have hp1 : (1 : ℝ) ≤ P ^ k := one_le_pow₀ (by linarith)
        have hfp : (k.factorial : ℝ) ≤ (P ^ k) ^ (1 / a) :=
          factorial_le_pow_rpow_inv (by linarith) hkP
        rw [hQ]
        exact typeI_window_bound_le hw hf hp1 hT2 hTX (by linarith) hT₀T hC (Nat.cast_nonneg _)
          (hlam ▸ hkX) hlam1 hlamΛ hL0 hLΛ hM₁ data.M₁_le hM₂0 hN2 hprod hε1 hfp hexp hpk
          (by positivity) hq
    _ = ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) * Q := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Absorbing the window count.**  With `T₀ = exp(c (log X)^{1/2})`,
`(⌊log₂(2X/T₀)⌋ + 1) √(K Λ₀^{m+5} T₀^{-1/100}) ≤ exp(-(log X)^{1/40})` eventually. -/
theorem eventually_typeI_window_count_absorbed (m : ℕ) {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop,
      ((Nat.log 2 ⌊2 * X / Real.exp (c * Real.log X ^ ((1 : ℝ) / 2))⌋₊ + 1 : ℕ) : ℝ) *
        Real.sqrt (K * (1 + Real.log (24 * X)) ^ (m + 5) *
          Real.exp (c * Real.log X ^ ((1 : ℝ) / 2)) ^ (-1 / 100 : ℝ)) ≤
        Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) := by
  have hL : ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 1 ≤ c * L ^ ((1 : ℝ) / 2) ∧
      L ^ (1 / 30 : ℝ) + 2 * L ^ (1 / 40 : ℝ) ≤ c / 100 * L ^ ((1 : ℝ) / 2) := by
    have h1 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (1 / c)
    have h2 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 15)).eventually_ge_atTop (300 / c)
    filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with L h1 h2 hL1
    have hL0 : 0 < L := by linarith
    refine ⟨hL1, ?_, ?_⟩
    · rw [div_le_iff₀ hc] at h1; linarith
    · have h40 : L ^ (1 / 40 : ℝ) ≤ L ^ (1 / 30 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      have hsplit : L ^ ((1 : ℝ) / 2) = L ^ (7 / 15 : ℝ) * L ^ (1 / 30 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      have h30 : 0 ≤ L ^ (1 / 30 : ℝ) := Real.rpow_nonneg hL0.le _
      rw [div_le_iff₀ hc] at h2
      rw [hsplit]
      have : 300 * L ^ (1 / 30 : ℝ) ≤ L ^ (7 / 15 : ℝ) * c * L ^ (1 / 30 : ℝ) :=
        mul_le_mul_of_nonneg_right h2 h30
      nlinarith
  filter_upwards [Real.tendsto_log_atTop.eventually hL,
    eventually_polylog_mul_exp_neg_le (m + 7) (C := 9 * K) (by positivity),
    eventually_ge_atTop (1 : ℝ)] with X ⟨hL1, hcL, hexpL⟩ habs hX1
  have hX0 : 0 < X := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩
  rw [← hLdef] at hL1 hcL hexpL habs ⊢
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, T₀ = Real.exp (c * L ^ ((1 : ℝ) / 2)) := ⟨_, rfl⟩
  rw [← hT₀]
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀, Λ₀ = 1 + Real.log (24 * X) := ⟨_, rfl⟩
  rw [← hΛ₀] at habs ⊢
  have hLΛ : L + 1 ≤ Λ₀ := by
    rw [hΛ₀, hLdef, Real.log_mul (by norm_num) hX0.ne']
    have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    linarith
  have hΛ1 : 1 ≤ Λ₀ := by linarith
  have hT₀2 : 2 ≤ T₀ := by rw [hT₀]; linarith [Real.add_one_le_exp (c * L ^ ((1 : ℝ) / 2))]
  have hT₀pow : T₀ ^ (-1 / 100 : ℝ) = Real.exp (-(c / 100 * L ^ ((1 : ℝ) / 2))) := by
    rw [hT₀, ← Real.exp_mul]; ring_nf
  -- the window count
  have hJ : ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * Λ₀ := by
    push_cast
    rcases lt_or_ge (2 * X / T₀) 1 with h | h
    · have : ⌊2 * X / T₀⌋₊ = 0 := Nat.floor_eq_zero.2 h
      rw [this, Nat.log_zero_right]; push_cast; linarith
    · have hlog := natLog_two_floor_le h
      have hle : 2 * X / T₀ ≤ X := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      have hlogX := Real.log_le_log (by positivity) hle
      rw [← hLdef] at hlogX
      linarith
  have hQ0 : 0 ≤ K * Λ₀ ^ (m + 5) * T₀ ^ (-1 / 100 : ℝ) := by
    have : 0 ≤ T₀ ^ (-1 / 100 : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity
  have hexp2 : Real.exp (-(c / 100 * L ^ ((1 : ℝ) / 2))) ≤
      Real.exp (-L ^ (1 / 30 : ℝ)) * Real.exp (-(2 * L ^ (1 / 40 : ℝ))) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have hsq : (3 * Λ₀) ^ 2 * (K * Λ₀ ^ (m + 5) * T₀ ^ (-1 / 100 : ℝ)) ≤
      Real.exp (-L ^ (1 / 40 : ℝ)) ^ 2 := by
    rw [hT₀pow]
    have hE : 0 ≤ Real.exp (-(2 * L ^ (1 / 40 : ℝ))) := (Real.exp_pos _).le
    have hE1 : Real.exp (-L ^ (1 / 40 : ℝ)) / 4 ≤ 1 := by
      have : Real.exp (-L ^ (1 / 40 : ℝ)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg (by linarith) _))
      linarith
    have hsq2 : Real.exp (-L ^ (1 / 40 : ℝ)) ^ 2 = Real.exp (-(2 * L ^ (1 / 40 : ℝ))) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have hA : 0 ≤ 9 * K * Λ₀ ^ (m + 7) := by positivity
    calc (3 * Λ₀) ^ 2 * (K * Λ₀ ^ (m + 5) * Real.exp (-(c / 100 * L ^ ((1 : ℝ) / 2))))
        = 9 * K * Λ₀ ^ (m + 7) * Real.exp (-(c / 100 * L ^ ((1 : ℝ) / 2))) := by ring
      _ ≤ 9 * K * Λ₀ ^ (m + 7) *
          (Real.exp (-L ^ (1 / 30 : ℝ)) * Real.exp (-(2 * L ^ (1 / 40 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hexp2 hA
      _ = (9 * K * Λ₀ ^ (m + 7) * Real.exp (-L ^ (1 / 30 : ℝ))) *
          Real.exp (-(2 * L ^ (1 / 40 : ℝ))) := by ring
      _ ≤ (Real.exp (-L ^ (1 / 40 : ℝ)) / 4) * Real.exp (-(2 * L ^ (1 / 40 : ℝ))) :=
          mul_le_mul_of_nonneg_right habs hE
      _ ≤ 1 * Real.exp (-(2 * L ^ (1 / 40 : ℝ))) := mul_le_mul_of_nonneg_right hE1 hE
      _ = _ := by rw [one_mul, hsq2]
  calc ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) * Real.sqrt (K * Λ₀ ^ (m + 5) * T₀ ^ (-1 / 100 : ℝ))
      ≤ 3 * Λ₀ * Real.sqrt (K * Λ₀ ^ (m + 5) * T₀ ^ (-1 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_right hJ (Real.sqrt_nonneg _)
    _ = Real.sqrt ((3 * Λ₀) ^ 2 * (K * Λ₀ ^ (m + 5) * T₀ ^ (-1 / 100 : ℝ))) := by
        rw [Real.sqrt_mul (sq_nonneg (3 * Λ₀)), Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 3 * Λ₀)]
    _ ≤ Real.sqrt (Real.exp (-L ^ (1 / 40 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.exp (-L ^ (1 / 40 : ℝ)) := Real.sqrt_sq (Real.exp_pos _).le

/-- **The Type-I case of Matomäki–Teräväinen (5.3), given Deshouillers–Iwaniec.**  For
`P ∈ [(log X)^a, (log X)^{6/5}]`, `a ≥ 1.0999`, and `U ⊆ [exp(c (log X)^{1/2}), X]` on which the
prime polynomial is `≥ P^{-ε_U/10}`, the Type-I piece has mean square `≤ exp(-(log X)^{1/40})`. -/
theorem eventually_typeI_setIntegral_le (hDI : MTDeshouillersIwaniecBound) {a₀ ε εU c : ℝ}
    {A : ℕ} (hA : 1 ≤ A) (ha₀ : 10999 / 10000 ≤ a₀) (hε1 : ε ≤ 1 / 10000)
    (hεU : 0 < εU) (hεUε : εU ≤ ε) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ (a P : ℝ) (B : Finset ℕ), a₀ ≤ a →
      Real.log X ^ a ≤ P → P ≤ Real.log X ^ (6 / 5 : ℝ) →
      (∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ {Y : ℝ} (data : MTTypeIPieceData X Y (mtPaperWidth A X) ε),
      MTUniformDivisorBounded 5 data.α → X / Real.log X ^ 2 ≤ Y →
      ∀ U : Set ℝ, MeasurableSet U →
        U ⊆ Set.Icc (Real.exp (c * Real.log X ^ ((1 : ℝ) / 2))) X →
        (∀ t ∈ U, P ^ (-εU / 10) ≤
          ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
        ∫ t in U, ‖mtTypeIShortFactor data t * mtTypeILongFactor data t‖ ^ 2 ≤
          Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) := by
  obtain ⟨C, hC, hexpl⟩ := typeI_setIntegral_le_explicit hDI
  have hL : ∀ᶠ L : ℝ in atTop, 2 ^ 199 ≤ L ∧ 1 ≤ c * L ^ ((1 : ℝ) / 2) ∧
      c * L ^ ((1 : ℝ) / 2) ≤ L ∧
      2 * L ^ (6 / 5 : ℝ) ≤ Real.exp (c * L ^ ((1 : ℝ) / 2) * (1 / 1000)) := by
    have hlo := isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2) (by norm_num)
    have hb := hlo.bound (c := c / 2400) (by positivity)
    have h1 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (1 / c)
    have h2 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop c
    have h3 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop
      (2000 * Real.log 2 / c)
    filter_upwards [hb, h1, h2, h3, eventually_ge_atTop (2 ^ 199 : ℝ)] with L hb h1 h2 h3 hL
    have h199 : (1 : ℝ) ≤ 2 ^ 199 := one_le_pow₀ (by norm_num)
    have hL0 : 0 < L := by linarith
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    have hr0 : 0 < L ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hL0 _
    rw [Real.norm_of_nonneg hlogL, Real.norm_of_nonneg hr0.le] at hb
    refine ⟨hL, ?_, ?_, ?_⟩
    · rw [div_le_iff₀ hc] at h1; linarith
    · have hsq : L = L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hL0]; norm_num
      calc c * L ^ ((1 : ℝ) / 2) ≤ L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right h2 hr0.le
        _ = L := hsq.symm
    · have hpow : 2 * L ^ (6 / 5 : ℝ) = Real.exp (Real.log 2 + 6 / 5 * Real.log L) := by
        rw [Real.exp_add, Real.exp_log (by norm_num), Real.rpow_def_of_pos hL0]; ring_nf
      rw [hpow]
      apply Real.exp_le_exp.2
      rw [div_le_iff₀ hc] at h3
      linarith
  have hwidth : ∀ᶠ X : ℝ in atTop, mtPaperWidth A X ≤ 1 / 2 := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2] with X hX
    rw [mtPaperWidth, Real.rpow_neg (by linarith), Real.rpow_natCast]
    have h1 : (2 : ℝ) ≤ Real.log X ^ (10 * A) := by
      calc (2 : ℝ) ≤ Real.log X := hX
        _ = Real.log X ^ 1 := (pow_one _).symm
        _ ≤ Real.log X ^ (10 * A) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  filter_upwards [Real.tendsto_log_atTop.eventually hL, hwidth,
    eventually_polylog_le_rpow 2 (C := 6) (κ := 2 / 5) (by norm_num) (by norm_num),
    eventually_typeI_window_count_absorbed (fourthMomentExponent 5)
      (K := 1600 * C * 532 * 2 ^ fourthMomentExponent 5) (by positivity) hc,
    eventually_ge_atTop (1 : ℝ)] with X ⟨hL199, hcL1, hcLL, hPT⟩ hδX hpoly habs hX1
  intro a P B ha₀a hPa hP65 hBiff Y data hα hYlo U hU hUsub hS
  have hX0 : 0 < X := by linarith
  have h199 : (1 : ℝ) ≤ 2 ^ 199 := one_le_pow₀ (by norm_num)
  have hlam1 : 1 ≤ Real.log X := by linarith
  have ha1 : 1 ≤ a := by linarith
  have ha : 0 < a := by linarith
  have hlamP : Real.log X ≤ P := by
    calc Real.log X = Real.log X ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log X ^ a := Real.rpow_le_rpow_of_exponent_le hlam1 ha1
      _ ≤ P := hPa
  have hP : 2 ≤ P := by
    have : (2 : ℝ) ≤ 2 ^ 199 := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ 199 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    linarith
  have h2P : (2 : ℝ) ^ 200 ≤ 2 * P := by
    have : (2 : ℝ) ^ 200 = 2 * 2 ^ 199 := by norm_num
    linarith
  have hPT₀ : 2 * P ≤ Real.exp (c * Real.log X ^ ((1 : ℝ) / 2)) ^ (1 / 1000 : ℝ) := by
    rw [← Real.exp_mul]; linarith
  have hexp : 1 / a + εU / 5 ≤ 91 / 100 := by
    have h1 : 1 / a ≤ 1 / (10999 / 10000) := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : εU / 5 ≤ 1 / 50000 := by linarith
    have h3 : (1 : ℝ) / (10999 / 10000) + 1 / 50000 ≤ 91 / 100 := by norm_num
    linarith
  have hT₀2 : 2 ≤ Real.exp (c * Real.log X ^ ((1 : ℝ) / 2)) := by
    linarith [Real.add_one_le_exp (c * Real.log X ^ ((1 : ℝ) / 2))]
  have hT₀X : Real.exp (c * Real.log X ^ ((1 : ℝ) / 2)) ≤ X := by
    calc Real.exp (c * Real.log X ^ ((1 : ℝ) / 2)) ≤ Real.exp (Real.log X) := Real.exp_le_exp.2 hcLL
      _ = X := Real.exp_log hX0
  have hbig : 6 * Real.log X ^ 2 * X ^ (1 / 2 + ε) ≤ X := by
    have hlog24 : Real.log X ≤ 1 + Real.log (24 * X) := by
      rw [Real.log_mul (by norm_num) hX0.ne']
      have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
      linarith
    have h6 : 6 * Real.log X ^ 2 ≤ X ^ (2 / 5 : ℝ) := by
      have : Real.log X ^ 2 ≤ (1 + Real.log (24 * X)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hlog24 2
      linarith
    calc 6 * Real.log X ^ 2 * X ^ (1 / 2 + ε) ≤ X ^ (2 / 5 : ℝ) * X ^ (1 / 2 + ε) :=
          mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hX0.le _)
      _ = X ^ (2 / 5 + (1 / 2 + ε)) := (Real.rpow_add hX0 _ _).symm
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = X := Real.rpow_one X
  have hδ0 : 0 ≤ mtPaperWidth A X := Real.rpow_nonneg (Real.log_nonneg hX1) _
  have hBp : ∀ p ∈ B, p.Prime := fun p hp => ((hBiff p).1 hp).1
  have hBr : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P := fun p hp => ((hBiff p).1 hp).2
  exact (hexpl data hα rfl hlam1 hBp hBr hP h2P hPT₀ ha hPa hεU.le hexp hT₀2 hT₀X hbig hYlo
    hε1 hδ0 hδX hU hUsub hS).trans habs

end

end RHTower.Sieve
