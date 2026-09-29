import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeI_IIHeightWindow

/-!
# The Type-I/II case of Matomäki–Teräväinen (5.3)

`U ⊆ [T₀, X]`, `T₀ = exp(c (log X)^{1/2})`, is cut into the height windows `[T/2, T]`.

* **Over height** (`T ≤ ⌊M₃⌋`): the window costs `≤ 2·10⁶ (1 + log K)^e / T` with no twisted moment
  at all, since `M₃(1+it) ≪ 1/T` pointwise.
* **Under height** (`T > ⌊M₃⌋ ≥ M₃/2 ≥ X^{1/3}`): with `(2P)^k ≤ T^{ε/2} < (2P)^{k+1}`,
  `k! ≤ (P^k)^{1/a}`, `a ≥ 1.0999`, and divisor losses `X^{ε/1000}`, Watt's bound and the amplified
  mean value theorem give `√(10⁷ C λ⁴ X^{-ε/200})`: the Watt envelope satisfies
  `Q ≤ 86λ⁴X^{-ε}` (from `M₃²M₂ ≥ X^{1+ε}/(4λ⁴)`) and `(T/(M₁²M₂))Q ≤ 128λ⁴`, and the amplifier
  contributes `(P^k)^{1/a+ε_U/5-1} ≤ T^{-0.0438ε}`.

The `O(log X)` windows are absorbed into `exp(-(log X)^{1/40})`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory Filter

noncomputable section

/-- **The amplifier degree at height `T`, general exponent.**  `k = ⌊log T^θ / log 2P⌋` with
`2^L ≤ 2P`, `θ ≤ Lν`, `2P ≤ T^ν`, `ν ≤ θ`: `(2P)^k ≤ T^θ`, `P^k ≥ T^{θ-2ν}`,
`(P+1)^k ≤ P^k T^ν` and `k ≤ log X ≤ P^{1/a}`. -/
theorem amplifier_degree_facts_general {T P X a θ ν : ℝ} {k L : ℕ}
    (hk : k = amplifierDegree (T ^ θ) P) (hP : 1 ≤ P) (h2P : (2 : ℝ) ^ L ≤ 2 * P)
    (hL : 2 ≤ L) (hθL : θ ≤ L * ν) (hν : 0 ≤ ν) (hνθ : ν ≤ θ) (hθ1 : θ ≤ 1)
    (hPT : 2 * P ≤ T ^ ν) (hT : 1 ≤ T) (hTX : T ≤ X) (ha : 0 < a)
    (hPa : Real.log X ^ a ≤ P) :
    1 ≤ k ∧ (2 * P) ^ k ≤ T ^ θ ∧ T ^ (θ - 2 * ν) ≤ P ^ k ∧
      (P + 1) ^ k ≤ P ^ k * T ^ ν ∧ (k : ℝ) ≤ P ^ (1 / a) ∧ (k : ℝ) ≤ Real.log X := by
  have hT0 : 0 < T := by linarith
  have hP0 : 0 < P := by linarith
  have hTθ : 1 ≤ T ^ θ := Real.one_le_rpow hT (by linarith)
  have hνθ' : T ^ ν ≤ T ^ θ := Real.rpow_le_rpow_of_exponent_le hT hνθ
  have hk1 : 1 ≤ k := hk ▸ one_le_amplifierDegree hP (hPT.trans hνθ')
  have hkT : (2 * P) ^ k ≤ T ^ θ := hk ▸ two_mul_pow_amplifierDegree_le hP hTθ
  have hlt : T ^ θ < (2 * P) ^ (k + 1) :=
    hk ▸ lt_two_mul_pow_amplifierDegree_succ hP (by positivity)
  have h2k : (2 : ℝ) ^ k ≤ T ^ ν := by
    have hL' : ((2 : ℝ) ^ k) ^ L ≤ T ^ θ := by
      calc ((2 : ℝ) ^ k) ^ L = ((2 : ℝ) ^ L) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (2 * P) ^ k := pow_le_pow_left₀ (by positivity) h2P k
        _ ≤ _ := hkT
    have hL0 : (0 : ℝ) ≤ ((L : ℕ) : ℝ)⁻¹ := by positivity
    have h := Real.rpow_le_rpow (by positivity) hL' hL0
    rw [Real.pow_rpow_inv_natCast (by positivity) (by omega), ← Real.rpow_mul hT0.le] at h
    refine h.trans (Real.rpow_le_rpow_of_exponent_le hT ?_)
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    rw [← div_eq_mul_inv, div_le_iff₀ hLpos]
    linarith
  have hpk : T ^ (θ - 2 * ν) ≤ P ^ k := by
    have hsplit : T ^ θ = T ^ (θ - 2 * ν) * (T ^ ν * T ^ ν) := by
      rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]; ring_nf
    have hup : (2 * P) ^ (k + 1) ≤ P ^ k * (T ^ ν * T ^ ν) := by
      calc (2 * P) ^ (k + 1) = P ^ k * ((2 : ℝ) ^ k * (2 * P)) := by ring
        _ ≤ P ^ k * (T ^ ν * T ^ ν) := by gcongr
    have hpos : 0 < T ^ ν * T ^ ν := by positivity
    have h := hlt.le.trans hup
    rw [hsplit] at h
    exact le_of_mul_le_mul_right h hpos
  have hq : (P + 1) ^ k ≤ P ^ k * T ^ ν := by
    calc (P + 1) ^ k ≤ (2 * P) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = P ^ k * (2 : ℝ) ^ k := by ring
      _ ≤ P ^ k * T ^ ν := by gcongr
  have hkX : (k : ℝ) ≤ Real.log X := by
    have he : Real.exp 1 ≤ 2 * P := by
      have h3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have h8 : (4 : ℝ) ≤ 2 * P := by
        have : (2 : ℝ) ^ 2 ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hL
        norm_num at this
        linarith
      linarith
    have h := amplifierDegree_le_log he hTθ
    rw [← hk] at h
    have hTθX : T ^ θ ≤ X := by
      calc T ^ θ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT hθ1
        _ = T := Real.rpow_one T
        _ ≤ X := hTX
    exact h.trans (Real.log_le_log (by positivity) hTθX)
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (hT.trans hTX)
  have hkP : (k : ℝ) ≤ P ^ (1 / a) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hlog0 a) hPa (by positivity : (0 : ℝ) ≤ 1 / a)
    rw [one_div, Real.rpow_rpow_inv hlog0 ha.ne'] at h
    rw [one_div]; exact hkX.trans h
  exact ⟨hk1, hkT, hpk, hq, hkP, hkX⟩

/-- The product lower bound, squared and redistributed: `X² ≤ 16 λ⁴ M₁²M₂²N²` when
`N ≥ M₃/2` and `M₁M₂M₃ ≥ X/(2λ²)`. -/
theorem sq_le_of_product_lower {X M₁ M₂ M₃ N lam : ℝ} (hX : 0 ≤ X) (hlam : 0 < lam)
    (hM₃ : 0 < M₃) (hN : M₃ / 2 ≤ N) (hprod : X / (2 * lam ^ 2) ≤ M₁ * M₂ * M₃) :
    X ^ 2 ≤ 16 * lam ^ 4 * (M₁ ^ 2 * M₂ ^ 2 * N ^ 2) := by
  have h2 : 0 ≤ X / (2 * lam ^ 2) := by positivity
  have h3 := pow_le_pow_left₀ h2 hprod 2
  rw [div_pow, div_le_iff₀ (by positivity)] at h3
  have hM3N : M₃ ^ 2 ≤ 4 * N ^ 2 := by
    have h0 : 0 ≤ M₃ := hM₃.le
    have := pow_le_pow_left₀ h0 (by linarith : M₃ ≤ 2 * N) 2
    linarith [show (2 * N) ^ 2 = 4 * N ^ 2 by ring]
  have hp : 0 ≤ M₁ ^ 2 * M₂ ^ 2 := by positivity
  have hl : 0 ≤ (2 * lam ^ 2) ^ 2 := sq_nonneg _
  calc X ^ 2 ≤ (M₁ * M₂ * M₃) ^ 2 * (2 * lam ^ 2) ^ 2 := h3
    _ = (M₁ ^ 2 * M₂ ^ 2 * M₃ ^ 2) * (2 * lam ^ 2) ^ 2 := by ring
    _ ≤ (M₁ ^ 2 * M₂ ^ 2 * (4 * N ^ 2)) * (2 * lam ^ 2) ^ 2 := by
        gcongr
    _ = 16 * lam ^ 4 * (M₁ ^ 2 * M₂ ^ 2 * N ^ 2) := by ring

/-- The first Watt envelope term: `(T + 4M₂²√T)/(N²M₂) ≤ 80λ⁴X^{-ε}` and, times `T/(M₁²M₂)`,
`≤ 80λ⁴`. -/
theorem typeI_II_envelope_first_le {T X M₁ M₂ N ε lam : ℝ} (hT2 : 2 ≤ T) (hTX : T ≤ X)
    (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂) (hM₂X : M₂ ≤ X ^ (1 / 4 - ε))
    (hM₁₂ : M₁ ^ 2 * M₂ ≤ X ^ (1 - ε)) (hN : 0 < N)
    (hsq : X ^ 2 ≤ 16 * lam ^ 4 * (M₁ ^ 2 * M₂ ^ 2 * N ^ 2)) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10000) :
    (T + 4 * M₂ ^ 2 * Real.sqrt T) / (N ^ 2 * M₂) ≤ 80 * lam ^ 4 * X ^ (-ε) ∧
      T / (M₁ * M₁ * M₂) * ((T + 4 * M₂ ^ 2 * Real.sqrt T) / (N ^ 2 * M₂)) ≤ 80 * lam ^ 4 := by
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hT0 : 0 < T := by linarith
  have hM₁0 : 0 < M₁ := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hM₂sq : M₂ ^ 2 ≤ X ^ (1 / 2 - 2 * ε) := by
    have h := pow_le_pow_left₀ hM₂0.le hM₂X 2
    rw [← Real.rpow_natCast (X ^ (1 / 4 - ε)) 2, ← Real.rpow_mul hX0.le] at h
    calc M₂ ^ 2 ≤ X ^ ((1 / 4 - ε) * ((2 : ℕ) : ℝ)) := h
      _ = X ^ (1 / 2 - 2 * ε) := by congr 1; push_cast; ring
  have hsqrt : Real.sqrt T ≤ X ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow hT0.le hTX (by norm_num)
  have hM₂sqrt : M₂ ^ 2 * Real.sqrt T ≤ X := by
    calc M₂ ^ 2 * Real.sqrt T ≤ X ^ (1 / 2 - 2 * ε) * X ^ (1 / 2 : ℝ) :=
          mul_le_mul hM₂sq hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = X ^ (1 - 2 * ε) := by rw [← Real.rpow_add hX0]; ring_nf
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = X := Real.rpow_one X
  have hnum : T + 4 * M₂ ^ 2 * Real.sqrt T ≤ 5 * X := by linarith
  have hXsplit : X ^ 2 = X ^ (1 - ε) * X ^ (1 + ε) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_natCast]; norm_num
  have hN2M₂ : X ^ (1 + ε) ≤ 16 * lam ^ 4 * (N ^ 2 * M₂) := by
    have hpos : 0 < X ^ (1 - ε) := by positivity
    have h : X ^ (1 - ε) * X ^ (1 + ε) ≤ X ^ (1 - ε) * (16 * lam ^ 4 * (N ^ 2 * M₂)) := by
      rw [← hXsplit]
      calc X ^ 2 ≤ 16 * lam ^ 4 * (M₁ ^ 2 * M₂ ^ 2 * N ^ 2) := hsq
        _ = (M₁ ^ 2 * M₂) * (16 * lam ^ 4 * (N ^ 2 * M₂)) := by ring
        _ ≤ X ^ (1 - ε) * (16 * lam ^ 4 * (N ^ 2 * M₂)) := by gcongr
    exact le_of_mul_le_mul_left h hpos
  have hXe' : X ^ (1 + ε) * X ^ (-ε) = X := by
    rw [← Real.rpow_add hX0]; ring_nf; exact Real.rpow_one X
  constructor
  · rw [div_le_iff₀ (by positivity)]
    calc T + 4 * M₂ ^ 2 * Real.sqrt T ≤ 5 * (X ^ (1 + ε) * X ^ (-ε)) := by rw [hXe']; exact hnum
      _ ≤ 5 * (16 * lam ^ 4 * (N ^ 2 * M₂) * X ^ (-ε)) := by gcongr
      _ = 80 * lam ^ 4 * X ^ (-ε) * (N ^ 2 * M₂) := by ring
  · rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
    have hTX2 : T * (T + 4 * M₂ ^ 2 * Real.sqrt T) ≤ 5 * X ^ 2 := by
      calc T * (T + 4 * M₂ ^ 2 * Real.sqrt T) ≤ X * (5 * X) :=
            mul_le_mul hTX hnum (by positivity) hX0.le
        _ = 5 * X ^ 2 := by ring
    calc T * (T + 4 * M₂ ^ 2 * Real.sqrt T) ≤ 5 * X ^ 2 := hTX2
      _ ≤ 5 * (16 * lam ^ 4 * (M₁ ^ 2 * M₂ ^ 2 * N ^ 2)) := by linarith
      _ = 80 * lam ^ 4 * (M₁ * M₁ * M₂ * (N ^ 2 * M₂)) := by ring

/-- The second Watt envelope term: `(T + 2M₂)/(T⁴M₂) ≤ 6X^{-ε}` and, times `T/(M₁²M₂)`,
`≤ 48`, for `M₂ ≤ T`, `X ≤ T³`. -/
theorem typeI_II_envelope_second_le {T X M₁ M₂ ε : ℝ} (hT2 : 2 ≤ T) (hTX : T ≤ X)
    (hT3 : X ≤ T ^ 3) (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂) (hM₂T : M₂ ≤ T) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10000) :
    (T + 2 * M₂) / (T ^ 4 * M₂) ≤ 6 * X ^ (-ε) ∧
      T / (M₁ * M₁ * M₂) * ((T + 2 * M₂) / (T ^ 4 * M₂)) ≤ 48 := by
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hT0 : 0 < T := by linarith
  have hM₁0 : 0 < M₁ := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  have hXe : X * X ^ (-ε) = X ^ (1 - ε) := by
    rw [← Real.rpow_one_add' hX0.le (by linarith), show (1 : ℝ) + -ε = 1 - ε by ring]
  have hXeps : 1 ≤ X * X ^ (-ε) := by rw [hXe]; exact Real.one_le_rpow hX1 (by linarith)
  have hXε0 : 0 < X ^ (-ε) := by positivity
  have hTM : T * M₂ ≤ T * T := mul_le_mul_of_nonneg_left hM₂T hT0.le
  constructor
  · rw [div_le_iff₀ (by positivity)]
    have h1 : T + 2 * M₂ ≤ 6 * T * M₂ := by
      have : T ≤ 2 * T * M₂ := by
        have := mul_le_mul_of_nonneg_left hM₂ hT0.le
        linarith
      linarith
    have hT4 : T ≤ X ^ (-ε) * T ^ 4 := by
      calc T = T * 1 := by ring
        _ ≤ T * (X * X ^ (-ε)) := mul_le_mul_of_nonneg_left hXeps hT0.le
        _ ≤ T * (T ^ 3 * X ^ (-ε)) := by gcongr
        _ = X ^ (-ε) * T ^ 4 := by ring
    calc T + 2 * M₂ ≤ 6 * T * M₂ := h1
      _ = 6 * M₂ * T := by ring
      _ ≤ 6 * M₂ * (X ^ (-ε) * T ^ 4) := by gcongr
      _ = 6 * X ^ (-ε) * (T ^ 4 * M₂) := by ring
  · rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
    have hM : 1 ≤ 16 * (M₁ * M₁ * (M₂ * M₂)) := by
      have h1 : (1 / 4 : ℝ) ≤ M₁ * M₁ := by nlinarith
      have h2 : (1 / 4 : ℝ) ≤ M₂ * M₂ := by nlinarith
      have := mul_le_mul h1 h2 (by norm_num) (by positivity)
      linarith
    have hT2' : 4 ≤ T ^ 2 := by nlinarith
    have hmain : T * (T + 2 * M₂) ≤ 3 * T ^ 2 := by nlinarith
    have hT2le : T ^ 2 ≤ T ^ 4 / 4 := by nlinarith
    have hpos : 0 ≤ M₁ * M₁ * (M₂ * M₂) := by positivity
    calc T * (T + 2 * M₂) ≤ 3 * T ^ 2 := hmain
      _ ≤ 3 * T ^ 2 * (16 * (M₁ * M₁ * (M₂ * M₂))) := le_mul_of_one_le_right (by positivity) hM
      _ = 48 * (M₁ * M₁ * (M₂ * M₂)) * T ^ 2 := by ring
      _ ≤ 48 * (M₁ * M₁ * (M₂ * M₂)) * (T ^ 4 / 4) := by gcongr
      _ ≤ 48 * (M₁ * M₁ * M₂ * (T ^ 4 * M₂)) := by nlinarith

/-- The amplifier exponents at the sub-height scale: with `k! ≤ (P^k)^{1/a}`,
`T^{249ε/500} ≤ P^k ≤ T^{ε/2}`, `(P+1)^k ≤ P^k T^{ε/1000}` and `T ∈ [X^{1/3}, X]`:
`k!(P^k)^{ε_U/5}(P+1)^k/P^k ≤ X^{456ε/1000}` and `k!(P^k)^{ε_U/5}(P+1)^k/P^{2k} ≤ X^{-2191ε/150000}`. -/
theorem typeI_II_amplifier_exponents_le {f p q T X εU a ε : ℝ} (hp : 1 ≤ p)
    (hq0 : 0 ≤ q) (hfp : f ≤ p ^ (1 / a)) (hexp : 1 / a + εU / 5 ≤ 91 / 100)
    (hpT : T ^ (249 * ε / 500) ≤ p) (hpT' : p ≤ T ^ (ε / 2))
    (hqp : q ≤ p * T ^ (ε / 1000)) (hT1 : 1 ≤ T) (hTX : T ≤ X) (hT3 : X ^ (1 / 3 : ℝ) ≤ T)
    (hε : 0 < ε) :
    f * p ^ (εU / 5) * q / p ≤ X ^ (456 * ε / 1000) ∧
      f * p ^ (εU / 5) * q / p ^ 2 ≤ X ^ (-(2191 * ε / 150000)) := by
  have hp0 : 0 < p := by linarith
  have hT0 : 0 < T := by linarith
  have hX1 : 1 ≤ X := hT1.trans hTX
  have hX0 : 0 < X := by linarith
  have h1 : f * p ^ (εU / 5) ≤ p ^ (91 / 100 : ℝ) := by
    calc f * p ^ (εU / 5) ≤ p ^ (1 / a) * p ^ (εU / 5) := by gcongr
      _ = p ^ (1 / a + εU / 5) := (Real.rpow_add hp0 _ _).symm
      _ ≤ p ^ (91 / 100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp hexp
  have hq1 : f * p ^ (εU / 5) * q ≤ p ^ (91 / 100 : ℝ) * (p * T ^ (ε / 1000)) :=
    mul_le_mul h1 hqp hq0 (by positivity)
  constructor
  · calc f * p ^ (εU / 5) * q / p ≤ p ^ (91 / 100 : ℝ) * (p * T ^ (ε / 1000)) / p := by gcongr
      _ = p ^ (91 / 100 : ℝ) * T ^ (ε / 1000) := by field_simp
      _ ≤ (T ^ (ε / 2)) ^ (91 / 100 : ℝ) * T ^ (ε / 1000) := by gcongr
      _ = T ^ (456 * ε / 1000) := by
          rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]; ring_nf
      _ ≤ X ^ (456 * ε / 1000) := Real.rpow_le_rpow hT0.le hTX (by positivity)
  · have h2 : p ^ (91 / 100 : ℝ) = p ^ (-9 / 100 : ℝ) * p := by
      rw [← Real.rpow_add_one hp0.ne']; norm_num
    have h3 : p ^ (-9 / 100 : ℝ) ≤ (T ^ (249 * ε / 500)) ^ (-9 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hpT (by norm_num)
    have h4 : (T ^ (249 * ε / 500)) ^ (-9 / 100 : ℝ) * T ^ (ε / 1000) =
        T ^ (-(2191 * ε / 50000)) := by
      rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]; ring_nf
    have h5 : T ^ (-(2191 * ε / 50000)) ≤ (X ^ (1 / 3 : ℝ)) ^ (-(2191 * ε / 50000)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hT3 (by nlinarith)
    have h6 : (X ^ (1 / 3 : ℝ)) ^ (-(2191 * ε / 50000)) = X ^ (-(2191 * ε / 150000)) := by
      rw [← Real.rpow_mul hX0.le]; ring_nf
    calc f * p ^ (εU / 5) * q / p ^ 2 ≤ p ^ (91 / 100 : ℝ) * (p * T ^ (ε / 1000)) / p ^ 2 := by
          gcongr
      _ = p ^ (-9 / 100 : ℝ) * T ^ (ε / 1000) := by rw [h2]; field_simp
      _ ≤ (T ^ (249 * ε / 500)) ^ (-9 / 100 : ℝ) * T ^ (ε / 1000) := by gcongr
      _ = T ^ (-(2191 * ε / 50000)) := h4
      _ ≤ _ := h5.trans h6.le

/-- The numerical constants of the sub-height window. -/
theorem typeI_II_window_constants :
    5 * Real.pi * Real.exp 1 * 86 ≤ 3690 ∧ 5 * Real.pi / 2 * 128 ≤ 1006 := by
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpe : Real.pi * Real.exp 1 ≤ 3.1416 * 2.7182818286 :=
    mul_le_mul hpi.le he1.le (Real.exp_pos 1).le (by norm_num)
  constructor
  · nlinarith
  · linarith

/-- The radicand of the sub-height window, collected: `32 C S κ (5πe t₁ + (5π/2) t₂)` with
`S ≤ X^{6ε/1000}`, `κ ≤ 64`, `t₁ ≤ 86λ⁴X^{-544ε/1000}`, `t₂ ≤ 128λ⁴X^{-2191ε/150000}` is
`≤ 10⁷ C λ⁴ X^{-ε/200}`. -/
theorem typeI_II_radicand_le {C S κ t₁ t₂ X ε lam : ℝ} (hC : 0 < C) (hS0 : 0 ≤ S)
    (hS : S ≤ X ^ (6 * ε / 1000)) (hκ : κ ≤ 64) (ht₁0 : 0 ≤ t₁)
    (ht₁ : t₁ ≤ 86 * lam ^ 4 * X ^ (-(544 * ε / 1000))) (ht₂0 : 0 ≤ t₂)
    (ht₂ : t₂ ≤ 128 * lam ^ 4 * X ^ (-(2191 * ε / 150000))) (hX1 : 1 ≤ X) (hε : 0 < ε) :
    32 * C * S * κ * (5 * Real.pi * Real.exp 1 * t₁ + 5 * Real.pi / 2 * t₂) ≤
      10 ^ 7 * C * lam ^ 4 * X ^ (-(ε / 200)) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨hc1, hc2⟩ := typeI_II_window_constants
  have he1 : X ^ (6 * ε / 1000) * X ^ (-(544 * ε / 1000)) ≤ X ^ (-(ε / 200)) := by
    rw [← Real.rpow_add hX0]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have he2 : X ^ (6 * ε / 1000) * X ^ (-(2191 * ε / 150000)) ≤ X ^ (-(ε / 200)) := by
    rw [← Real.rpow_add hX0]; exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hl4 : 0 ≤ lam ^ 4 := by positivity
  have hpe : 0 ≤ 5 * Real.pi * Real.exp 1 := by positivity
  have hpe2 : 0 ≤ 5 * Real.pi / 2 := by positivity
  have hin : 5 * Real.pi * Real.exp 1 * t₁ + 5 * Real.pi / 2 * t₂ ≤
      5 * Real.pi * Real.exp 1 * (86 * lam ^ 4 * X ^ (-(544 * ε / 1000))) +
        5 * Real.pi / 2 * (128 * lam ^ 4 * X ^ (-(2191 * ε / 150000))) := by
    gcongr
  have hin0 : 0 ≤ 5 * Real.pi * Real.exp 1 * t₁ + 5 * Real.pi / 2 * t₂ := by positivity
  have hX6 : 0 ≤ X ^ (6 * ε / 1000) := by positivity
  have hsum : S * (5 * Real.pi * Real.exp 1 * t₁ + 5 * Real.pi / 2 * t₂) ≤
      4696 * (lam ^ 4 * X ^ (-(ε / 200))) := by
    calc S * (5 * Real.pi * Real.exp 1 * t₁ + 5 * Real.pi / 2 * t₂)
        ≤ X ^ (6 * ε / 1000) *
            (5 * Real.pi * Real.exp 1 * (86 * lam ^ 4 * X ^ (-(544 * ε / 1000))) +
              5 * Real.pi / 2 * (128 * lam ^ 4 * X ^ (-(2191 * ε / 150000)))) :=
          mul_le_mul hS hin hin0 hX6
      _ = lam ^ 4 * ((5 * Real.pi * Real.exp 1 * 86) *
            (X ^ (6 * ε / 1000) * X ^ (-(544 * ε / 1000))) +
          (5 * Real.pi / 2 * 128) * (X ^ (6 * ε / 1000) * X ^ (-(2191 * ε / 150000)))) := by ring
      _ ≤ lam ^ 4 * (3690 * X ^ (-(ε / 200)) + 1006 * X ^ (-(ε / 200))) := by gcongr
      _ = 4696 * (lam ^ 4 * X ^ (-(ε / 200))) := by ring
  have hq : 0 ≤ lam ^ 4 * X ^ (-(ε / 200)) := by positivity
  calc 32 * C * S * κ * (5 * Real.pi * Real.exp 1 * t₁ + 5 * Real.pi / 2 * t₂)
      = 32 * C * κ * (S * (5 * Real.pi * Real.exp 1 * t₁ + 5 * Real.pi / 2 * t₂)) := by ring
    _ ≤ 32 * C * 64 * (4696 * (lam ^ 4 * X ^ (-(ε / 200)))) := by gcongr
    _ = 9617408 * C * (lam ^ 4 * X ^ (-(ε / 200))) := by ring
    _ ≤ 10 ^ 7 * C * (lam ^ 4 * X ^ (-(ε / 200))) := by gcongr; norm_num
    _ = 10 ^ 7 * C * lam ^ 4 * X ^ (-(ε / 200)) := by ring

/-- **The sub-height window value, absorbed.**  With the envelope bounds `Q ≤ 86λ⁴X^{-ε}`,
`(T/(M₁²M₂))Q ≤ 128λ⁴`, `K_f ≤ 64M₁²M₂`, the divisor and coefficient bounds `≤ X^{ε/1000}` and
`η ≤ ε/1000`, the window bound is `≤ √(10⁷ C λ⁴ X^{-ε/200})`. -/
theorem typeI_II_window_value_le {f p q T C η εU a Bβ D Bf M₁ M₂ X ε lam Kf Q : ℝ}
    (hf : 1 ≤ f) (hp : 1 ≤ p) (hq0 : 0 ≤ q) (hC : 0 < C) (hfp : f ≤ p ^ (1 / a))
    (hexp : 1 / a + εU / 5 ≤ 91 / 100) (hpT : T ^ (249 * ε / 500) ≤ p) (hpT' : p ≤ T ^ (ε / 2))
    (hqp : q ≤ p * T ^ (ε / 1000)) (hT2 : 2 ≤ T) (hTX : T ≤ X) (hT3 : X ^ (1 / 3 : ℝ) ≤ T)
    (hη : η ≤ ε / 1000) (hBβ0 : 0 < Bβ) (hBβ : Bβ ≤ X ^ (ε / 1000)) (hD0 : 0 < D)
    (hD : D ≤ X ^ (ε / 1000)) (hBf0 : 0 < Bf) (hBf : Bf ≤ X ^ (ε / 1000)) (hM₁ : 1 / 2 ≤ M₁)
    (hM₂ : 1 / 2 ≤ M₂) (hKf : Kf ≤ 64 * (M₁ * M₁ * M₂)) (hQ0 : 0 ≤ Q)
    (hQ1 : Q ≤ 86 * lam ^ 4 * X ^ (-ε)) (hQ2 : T / (M₁ * M₁ * M₂) * Q ≤ 128 * lam ^ 4)
    (hε : 0 < ε) :
    f * p ^ (εU / 10) * Real.sqrt ((32 * C * T ^ η * Bβ ^ 2 * Q) *
        ((5 * Real.pi * Real.exp 1 / (M₁ * M₁ * M₂ * p) +
            5 * Real.pi / 2 * T / (M₁ * M₁ * M₂ * p) ^ 2) *
          (D * (Kf * Bf ^ 2 * (q / f))))) ≤
      Real.sqrt (10 ^ 7 * C * lam ^ 4 * X ^ (-(ε / 200))) := by
  have hp0 : 0 < p := by linarith
  have hf0 : 0 < f := by linarith
  have hT0 : 0 < T := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hM₁0 : 0 < M₁ := by linarith
  have hM₂0 : 0 < M₂ := by linarith
  obtain ⟨hA1, hA2⟩ := typeI_II_amplifier_exponents_le hp hq0 hfp hexp hpT hpT' hqp (by linarith)
    hTX hT3 hε
  have hpow : (p ^ (εU / 10)) ^ 2 = p ^ (εU / 5) := by
    rw [← Real.rpow_mul_natCast hp0.le]; ring_nf
  obtain ⟨M, hM⟩ : ∃ M, M = M₁ * M₁ * M₂ := ⟨_, rfl⟩
  rw [← hM] at hKf hQ2 ⊢
  have hM0 : 0 < M := by rw [hM]; positivity
  -- the small factors
  have hTη : T ^ η ≤ X ^ (ε / 1000) :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hη).trans
      (Real.rpow_le_rpow hT0.le hTX (by positivity))
  have hsmall : T ^ η * Bβ ^ 2 * D * Bf ^ 2 ≤ X ^ (6 * ε / 1000) := by
    have hX6 : X ^ (6 * ε / 1000) = X ^ (ε / 1000) * (X ^ (ε / 1000)) ^ 2 * X ^ (ε / 1000) *
        (X ^ (ε / 1000)) ^ 2 := by
      rw [show 6 * ε / 1000 = ε / 1000 * ((6 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_mul_natCast hX0.le]
      ring
    rw [hX6]
    have hB2 : Bβ ^ 2 ≤ (X ^ (ε / 1000)) ^ 2 := pow_le_pow_left₀ hBβ0.le hBβ 2
    have hF2 : Bf ^ 2 ≤ (X ^ (ε / 1000)) ^ 2 := pow_le_pow_left₀ hBf0.le hBf 2
    gcongr
  have hKM : Kf / M ≤ 64 := by rw [div_le_iff₀ hM0]; linarith
  -- the radicand identity
  have hrad : (f * p ^ (εU / 10)) ^ 2 * ((32 * C * T ^ η * Bβ ^ 2 * Q) *
      ((5 * Real.pi * Real.exp 1 / (M * p) + 5 * Real.pi / 2 * T / (M * p) ^ 2) *
        (D * (Kf * Bf ^ 2 * (q / f))))) =
      32 * C * (T ^ η * Bβ ^ 2 * D * Bf ^ 2) * (Kf / M) *
        (5 * Real.pi * Real.exp 1 * (f * p ^ (εU / 5) * q / p * Q) +
          5 * Real.pi / 2 * (f * p ^ (εU / 5) * q / p ^ 2 * (T / M * Q))) := by
    rw [mul_pow, hpow]; field_simp
  have hx : 0 ≤ f * p ^ (εU / 10) := by positivity
  rw [show f * p ^ (εU / 10) = Real.sqrt ((f * p ^ (εU / 10)) ^ 2) from (Real.sqrt_sq hx).symm,
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [hrad]
  have ht1 : f * p ^ (εU / 5) * q / p * Q ≤ 86 * lam ^ 4 * X ^ (-(544 * ε / 1000)) := by
    calc f * p ^ (εU / 5) * q / p * Q ≤ X ^ (456 * ε / 1000) * (86 * lam ^ 4 * X ^ (-ε)) :=
          mul_le_mul hA1 hQ1 hQ0 (by positivity)
      _ = 86 * lam ^ 4 * (X ^ (456 * ε / 1000) * X ^ (-ε)) := by ring
      _ = 86 * lam ^ 4 * X ^ (-(544 * ε / 1000)) := by rw [← Real.rpow_add hX0]; ring_nf
  have ht2 : f * p ^ (εU / 5) * q / p ^ 2 * (T / M * Q) ≤
      128 * lam ^ 4 * X ^ (-(2191 * ε / 150000)) := by
    have hTQ0 : 0 ≤ T / M * Q := by positivity
    calc f * p ^ (εU / 5) * q / p ^ 2 * (T / M * Q)
        ≤ X ^ (-(2191 * ε / 150000)) * (128 * lam ^ 4) := mul_le_mul hA2 hQ2 hTQ0 (by positivity)
      _ = _ := by ring
  exact typeI_II_radicand_le hC (by positivity) hsmall hKM (by positivity) ht1
    (by positivity) ht2 hX1 hε

/-- **The over-height window value.**  With `K = ⌈2M₁⌉⌈2M₂⌉ ≤ 16M₁M₂`, `M₁M₂ ≥ 1/4`,
`T ≥ 1`: the over-height bound is `≤ 2·10⁶ (1 + log K)^e / T`. -/
theorem typeI_II_overHeight_value_le {M₁ M₂ T K L : ℝ} (hM₁ : 1 / 2 ≤ M₁) (hM₂ : 1 / 2 ≤ M₂)
    (hT : 1 ≤ T) (hK0 : 0 ≤ K) (hK : K ≤ 16 * (M₁ * M₂)) (hL : 0 ≤ L) :
    (2 * (6 * Real.pi + 1) / T) ^ 2 *
        ((5 * Real.pi * Real.exp 1 / (M₁ * M₂) + 5 * Real.pi / 2 * T / (M₁ * M₂) ^ 2) * (K * L)) ≤
      2 * 10 ^ 6 * L / T := by
  have hT0 : 0 < T := by linarith
  have hM : 1 / 4 ≤ M₁ * M₂ := by nlinarith
  have hM0 : 0 < M₁ * M₂ := by linarith
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpe : Real.pi * Real.exp 1 ≤ 3.1416 * 2.7182818286 :=
    mul_le_mul hpi.le he1.le (Real.exp_pos 1).le (by norm_num)
  have hC0 : (2 * (6 * Real.pi + 1)) ^ 2 ≤ 1577 := by nlinarith [Real.pi_pos]
  have hKM1 : K / (M₁ * M₂) ≤ 16 := by rw [div_le_iff₀ hM0]; linarith
  have hKM2 : K / (M₁ * M₂) ^ 2 ≤ 64 := by
    rw [div_le_iff₀ (by positivity)]
    have : 16 * (M₁ * M₂) ≤ 64 * (M₁ * M₂) ^ 2 := by nlinarith
    linarith
  have hbr : (5 * Real.pi * Real.exp 1 / (M₁ * M₂) + 5 * Real.pi / 2 * T / (M₁ * M₂) ^ 2) * K ≤
      1187 * T := by
    have e : (5 * Real.pi * Real.exp 1 / (M₁ * M₂) + 5 * Real.pi / 2 * T / (M₁ * M₂) ^ 2) * K =
        5 * Real.pi * Real.exp 1 * (K / (M₁ * M₂)) + 5 * Real.pi / 2 * T * (K / (M₁ * M₂) ^ 2) := by
      field_simp
    rw [e]
    have h1 : 5 * Real.pi * Real.exp 1 * (K / (M₁ * M₂)) ≤ 5 * Real.pi * Real.exp 1 * 16 :=
      mul_le_mul_of_nonneg_left hKM1 (by positivity)
    have h2 : 5 * Real.pi / 2 * T * (K / (M₁ * M₂) ^ 2) ≤ 5 * Real.pi / 2 * T * 64 :=
      mul_le_mul_of_nonneg_left hKM2 (by positivity)
    have h3 : 5 * Real.pi * Real.exp 1 * 16 ≤ 684 * T := by nlinarith
    have h4 : 5 * Real.pi / 2 * T * 64 ≤ 503 * T := by nlinarith
    linarith
  have hsq : (2 * (6 * Real.pi + 1) / T) ^ 2 = (2 * (6 * Real.pi + 1)) ^ 2 / T ^ 2 := by
    rw [div_pow]
  rw [hsq]
  calc (2 * (6 * Real.pi + 1)) ^ 2 / T ^ 2 *
        ((5 * Real.pi * Real.exp 1 / (M₁ * M₂) + 5 * Real.pi / 2 * T / (M₁ * M₂) ^ 2) * (K * L))
      = (2 * (6 * Real.pi + 1)) ^ 2 / T ^ 2 *
          (((5 * Real.pi * Real.exp 1 / (M₁ * M₂) + 5 * Real.pi / 2 * T / (M₁ * M₂) ^ 2) * K) *
            L) := by ring
    _ ≤ 1577 / T ^ 2 * ((1187 * T) * L) := by gcongr
    _ = 1577 * 1187 * L / T := by field_simp
    _ ≤ 2 * 10 ^ 6 * L / T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hL) hT0.le

/-- The short Type-I/II factor `∑_{m ∼ M₁} α_m m^{-1-it}`. -/
def mtTypeI_IIShortFactor {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε) (t : ℝ) : ℂ :=
  perronPoly (fun n => mtRealIntervalAF data.α data.M₁ (2 * data.M₁) n) ⌈2 * data.M₁⌉₊ 1 t

/-- The twist factor `∑_{m ∼ M₂} β_m m^{-1-it}`. -/
def mtTypeI_IITwistFactor {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε) (t : ℝ) : ℂ :=
  perronPoly (fun n => mtRealIntervalAF data.β data.M₂ (2 * data.M₂) n) ⌈2 * data.M₂⌉₊ 1 t

/-- The long factor `∑_{M₃ < m ≤ (1+δ)M₃} m^{-1-it}`. -/
def mtTypeI_IILongFactor {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε) (t : ℝ) : ℂ :=
  perronPoly (fun n => mtRealIntervalAF (fun _ => (1 : ℂ)) data.M₃ ((1 + δ) * data.M₃) n)
    ⌈(1 + δ) * data.M₃⌉₊ 1 t

theorem continuous_mtTypeI_IIShortFactor {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε) :
    Continuous (mtTypeI_IIShortFactor data) := continuous_perronPoly _ _ 1

theorem continuous_mtTypeI_IITwistFactor {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε) :
    Continuous (mtTypeI_IITwistFactor data) := continuous_perronPoly _ _ 1

theorem continuous_mtTypeI_IILongFactor {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε) :
    Continuous (mtTypeI_IILongFactor data) := continuous_perronPoly _ _ 1

theorem mtTypeI_IILongFactor_eq {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε)
    (hδ : 0 ≤ δ) (t : ℝ) :
    mtTypeI_IILongFactor data t = mtWattUnitBlock ⌊data.M₃⌋₊ ⌊(1 + δ) * data.M₃⌋₊ t :=
  perronPoly_mtRealUnitInterval_eq_mtWattUnitBlock data.M₃_pos.le
    (by have := data.M₃_pos; positivity) t

/-- `⌈2M⌉ ≤ 4M` for `M ≥ 1/2`. -/
theorem natCeil_two_mul_le {M : ℝ} (hM : 1 / 2 ≤ M) : ((⌈2 * M⌉₊ : ℕ) : ℝ) ≤ 4 * M := by
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * M)
  linarith

/-- **An over-height window of the Type-I/II piece.** -/
theorem typeI_II_overHeight_window_bound {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε)
    (hα : MTUniformDivisorBounded 5 data.α) (hβ : MTUniformDivisorBounded 5 data.β)
    {T T₀ : ℝ} {E : Set ℝ} (hδ : 0 ≤ δ) (hM₁ : 1 / 2 ≤ data.M₁) (hM₂ : 1 / 2 ≤ data.M₂)
    (hN1 : 1 ≤ ⌊data.M₃⌋₊) (hNN' : ⌊data.M₃⌋₊ < ⌊(1 + δ) * data.M₃⌋₊)
    (hN' : ⌊(1 + δ) * data.M₃⌋₊ ≤ 2 * ⌊data.M₃⌋₊) (hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T) (hT2 : 2 ≤ T)
    (hTN : T ≤ (⌊data.M₃⌋₊ : ℝ)) (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (T / 2) T)
    (hM₁₂X : data.M₁ * data.M₂ ≤ X) (hX1 : 1 ≤ X) :
    ∫ t in E, ‖mtTypeI_IIShortFactor data t * mtTypeI_IITwistFactor data t *
        mtTypeI_IILongFactor data t‖ ^ (2 : ℕ) ≤
      2 * 10 ^ 6 * (2 * (1 + Real.log (24 * X))) ^ fourthMomentExponent 5 / T₀ := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hlong : ∀ t, mtTypeI_IILongFactor data t =
      mtWattUnitBlock ⌊data.M₃⌋₊ ⌊(1 + δ) * data.M₃⌋₊ t := mtTypeI_IILongFactor_eq data hδ
  simp_rw [hlong]
  have h := setIntegral_typeI_II_overHeight_le data.α data.β hα hβ hM₁ hM₂ hN1 hNN' hN' hT2 hTN
    hE hEsub
  refine h.trans ?_
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ((⌈2 * data.M₁⌉₊ * ⌈2 * data.M₂⌉₊ : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hK]
  have hK1 : 1 ≤ K := by
    rw [hK]
    have h1 : 1 ≤ ⌈2 * data.M₁⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 1 ≤ ⌈2 * data.M₂⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hK16 : K ≤ 16 * (data.M₁ * data.M₂) := by
    rw [hK]; push_cast
    have h1 := natCeil_two_mul_le hM₁
    have h2 := natCeil_two_mul_le hM₂
    calc ((⌈2 * data.M₁⌉₊ : ℕ) : ℝ) * ((⌈2 * data.M₂⌉₊ : ℕ) : ℝ) ≤ (4 * data.M₁) * (4 * data.M₂) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by linarith)
      _ = 16 * (data.M₁ * data.M₂) := by ring
  have hL0 : 0 ≤ 1 + Real.log K := by have := Real.log_nonneg hK1; linarith
  have hval := typeI_II_overHeight_value_le (T := T) (K := K)
    (L := (1 + Real.log K) ^ fourthMomentExponent 5) hM₁ hM₂ (by linarith) (by linarith) hK16
    (pow_nonneg hL0 (fourthMomentExponent 5))
  refine hval.trans ?_
  have hLK : 1 + Real.log K ≤ 2 * (1 + Real.log (24 * X)) := by
    have hKX : K ≤ (24 * X) ^ 2 := by nlinarith
    have hlog := Real.log_le_log (by linarith) hKX
    rw [Real.log_pow] at hlog
    push_cast at hlog
    have : 0 ≤ Real.log (24 * X) := Real.log_nonneg (by linarith)
    linarith
  have hpow : (1 + Real.log K) ^ fourthMomentExponent 5 ≤
      (2 * (1 + Real.log (24 * X))) ^ fourthMomentExponent 5 := pow_le_pow_left₀ hL0 hLK _
  calc 2 * 10 ^ 6 * (1 + Real.log K) ^ fourthMomentExponent 5 / T
      ≤ 2 * 10 ^ 6 * (2 * (1 + Real.log (24 * X))) ^ fourthMomentExponent 5 / T := by gcongr
    _ ≤ 2 * 10 ^ 6 * (2 * (1 + Real.log (24 * X))) ^ fourthMomentExponent 5 / T₀ := by
        have h24 : 0 ≤ 2 * (1 + Real.log (24 * X)) := by
          have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 24 * X); linarith
        exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (pow_nonneg h24 _)) hT₀ hT₀T

/-- The coefficient bounds of a Type-I/II piece below `X²`: the twist coefficients, the divisor
function up to the length, and the coefficients of `M₁²M₂` are all `≤ X^{ε/1000}`. -/
theorem typeI_II_coefficient_bounds {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε)
    (hα : MTUniformDivisorBounded 5 data.α) (hβ : MTUniformDivisorBounded 5 data.β) {L : ℕ}
    (hdiv : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ≤ X ^ (ε / 1000) ∧
      (n.divisors.card : ℝ) ^ 5 ≤ X ^ (ε / 1000) ∧ (n.divisors.card : ℝ) ^ 17 ≤ X ^ (ε / 1000))
    (hX2 : 2 ≤ X) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10000) (hM₁ : 1 / 2 ≤ data.M₁)
    (hM₂ : 1 / 2 ≤ data.M₂) (hL : (L : ℝ) ≤ X ^ 2) (hf2 : 8 * X ^ (1 - ε) ≤ X ^ 2) :
    (∀ m, ‖mtRealIntervalAF data.β data.M₂ (2 * data.M₂) m‖ ≤ X ^ (ε / 1000)) ∧
      (∀ n ∈ Finset.Icc 1 L, (n.divisors.card : ℝ) ≤ X ^ (ε / 1000)) ∧
      (∀ n, ‖(mtRealIntervalAF data.α data.M₁ (2 * data.M₁) *
        mtRealIntervalAF data.α data.M₁ (2 * data.M₁) *
          mtRealIntervalAF data.β data.M₂ (2 * data.M₂)) n‖ ≤ X ^ (ε / 1000)) := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hM₁0 : 0 < data.M₁ := by linarith
  have hM₂0 : 0 < data.M₂ := by linarith
  have hXe0 : 0 < X ^ (ε / 1000) := by positivity
  have hM₂X : data.M₂ ≤ X := by
    calc data.M₂ ≤ X ^ (1 / 4 - ε) := data.M₂_le
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = X := Real.rpow_one X
  refine ⟨?_, ?_, ?_⟩
  · intro m
    by_cases h0 : mtRealIntervalAF data.β data.M₂ (2 * data.M₂) m = 0
    · rw [h0, norm_zero]; exact hXe0.le
    obtain ⟨hm0, -, hmhi⟩ := mtRealIntervalAF_scaleSupported data.β data.M₂ (2 * data.M₂) h0
    have hb := (hβ.realInterval data.M₂ (2 * data.M₂)) hm0
    have hmX : (m : ℝ) ≤ X ^ 2 := by nlinarith
    exact hb.trans (hdiv m hm0 hmX).2.1
  · intro n hn
    obtain ⟨hn1, hnL⟩ := Finset.mem_Icc.1 hn
    exact (hdiv n hn1 ((Nat.cast_le.2 hnL).trans hL)).1
  · intro n
    set F := mtRealIntervalAF data.α data.M₁ (2 * data.M₁) *
      mtRealIntervalAF data.α data.M₁ (2 * data.M₁) *
        mtRealIntervalAF data.β data.M₂ (2 * data.M₂) with hF
    by_cases h0 : F n = 0
    · rw [h0, norm_zero]; exact hXe0.le
    have hscale : MTRealScaleSupported F (data.M₁ * data.M₁ * data.M₂)
        ((2 * data.M₁) * (2 * data.M₁) * (2 * data.M₂)) :=
      MTRealScaleSupported.mul (MTRealScaleSupported.mul
        (mtRealIntervalAF_scaleSupported data.α data.M₁ (2 * data.M₁))
        (mtRealIntervalAF_scaleSupported data.α data.M₁ (2 * data.M₁)) hM₁0.le hM₁0.le)
        (mtRealIntervalAF_scaleSupported data.β data.M₂ (2 * data.M₂)) (by positivity) hM₂0.le
    obtain ⟨hn0, -, hnhi⟩ := hscale h0
    have hsq := data.square_product_le
    have hnX : (n : ℝ) ≤ X ^ 2 := by
      have : (2 * data.M₁) * (2 * data.M₁) * (2 * data.M₂) = 8 * (data.M₁ ^ (2 : ℕ) * data.M₂) := by
        ring
      rw [this] at hnhi
      linarith
    have hcoef : MTUniformDivisorBounded (5 + 5 + 1 + 5 + 1) fun n => F n :=
      ((hα.realInterval _ _).arithmeticFunction_mul (hα.realInterval _ _)).arithmeticFunction_mul
        (hβ.realInterval _ _)
    exact (hcoef hn0).trans (hdiv n hn0 hnX).2.2

/-- The length of `M₁²M₂𝓜` is `≤ X²` once `(2P)^k ≤ X^{ε/2}` and `128 X^{1-ε/2} ≤ X²`. -/
theorem typeI_II_length_le {X M₁ M₂ ε A : ℝ} (hX1 : 1 ≤ X) (hε : 0 ≤ ε) (hM₁ : 1 / 2 ≤ M₁)
    (hM₂ : 1 / 2 ≤ M₂) (hsq : M₁ ^ (2 : ℕ) * M₂ ≤ X ^ (1 - ε)) (hA0 : 0 ≤ A)
    (hA : A ≤ X ^ (ε / 2)) (hlen : 128 * X ^ (1 - ε / 2) ≤ X ^ 2) :
    ((⌈2 * M₁⌉₊ * ⌈2 * M₁⌉₊ * ⌈2 * M₂⌉₊ * ⌈A⌉₊ : ℕ) : ℝ) ≤ X ^ 2 := by
  have hX0 : 0 < X := by linarith
  have h1 := natCeil_two_mul_le hM₁
  have h2 := natCeil_two_mul_le hM₂
  have hK := Nat.ceil_lt_add_one hA0
  have h3 : (1 : ℝ) ≤ X ^ (ε / 2) := Real.one_le_rpow hX1 (by positivity)
  have hsplit : X ^ (1 - ε) * X ^ (ε / 2) = X ^ (1 - ε / 2) := by
    rw [← Real.rpow_add hX0]; ring_nf
  push_cast
  have hM : (4 * M₁) * (4 * M₁) * (4 * M₂) = 64 * (M₁ ^ (2 : ℕ) * M₂) := by ring
  calc ((⌈2 * M₁⌉₊ : ℕ) : ℝ) * ((⌈2 * M₁⌉₊ : ℕ) : ℝ) * ((⌈2 * M₂⌉₊ : ℕ) : ℝ) * ((⌈A⌉₊ : ℕ) : ℝ)
      ≤ ((4 * M₁) * (4 * M₁) * (4 * M₂)) * (2 * X ^ (ε / 2)) := by
        gcongr
        linarith
    _ ≤ (64 * X ^ (1 - ε)) * (2 * X ^ (ε / 2)) := by rw [hM]; gcongr
    _ = 128 * (X ^ (1 - ε) * X ^ (ε / 2)) := by ring
    _ = 128 * X ^ (1 - ε / 2) := by rw [hsplit]
    _ ≤ X ^ 2 := hlen

/-- The Watt envelope bounds at a sub-height window, in piece-data form. -/
theorem typeI_II_envelope_bounds {X Y δ ε : ℝ} (data : MTTypeI_II_PieceData X Y δ ε)
    {T lam : ℝ} (hlam : 1 ≤ lam) (hM₁ : 1 / 2 ≤ data.M₁) (hM₂ : 1 / 2 ≤ data.M₂)
    (hN1 : 1 ≤ ⌊data.M₃⌋₊) (hN2 : data.M₃ / 2 ≤ (⌊data.M₃⌋₊ : ℝ))
    (hprod : X / (2 * lam ^ 2) ≤ data.M₁ * data.M₂ * data.M₃) (hT2 : 2 ≤ T) (hTX : T ≤ X)
    (hT3 : X ^ (1 / 3 : ℝ) ≤ T) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10000) :
    (T + 4 * data.M₂ ^ 2 * Real.sqrt T) / ((⌊data.M₃⌋₊ : ℝ) ^ 2 * data.M₂) +
        (T + 2 * data.M₂) / (T ^ 4 * data.M₂) ≤ 86 * lam ^ 4 * X ^ (-ε) ∧
      T / (data.M₁ * data.M₁ * data.M₂) *
          ((T + 4 * data.M₂ ^ 2 * Real.sqrt T) / ((⌊data.M₃⌋₊ : ℝ) ^ 2 * data.M₂) +
            (T + 2 * data.M₂) / (T ^ 4 * data.M₂)) ≤ 128 * lam ^ 4 := by
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hN0 : (0 : ℝ) < (⌊data.M₃⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊data.M₃⌋₊)
  have hsq := sq_le_of_product_lower hX0.le (by linarith) data.M₃_pos hN2 hprod
  obtain ⟨hQ₁, hQ₁'⟩ := typeI_II_envelope_first_le hT2 hTX hM₁ hM₂ data.M₂_le
    data.square_product_le hN0 hsq hε hε1
  have hT3' : X ≤ T ^ 3 := by
    have h := pow_le_pow_left₀ (by positivity) hT3 3
    rw [← Real.rpow_natCast (X ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hX0.le] at h
    norm_num at h
    exact h
  have hM₂T : data.M₂ ≤ T := by
    refine data.M₂_le.trans (le_trans ?_ hT3)
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  obtain ⟨hQ₂, hQ₂'⟩ := typeI_II_envelope_second_le hT2 hTX hT3' hM₁ hM₂ hM₂T hε hε1
  have hl4 : 1 ≤ lam ^ 4 := one_le_pow₀ hlam
  have hXε : 0 < X ^ (-ε) := by positivity
  have h6 : 6 * X ^ (-ε) ≤ 6 * lam ^ 4 * X ^ (-ε) := by
    have := mul_le_mul_of_nonneg_right hl4 hXε.le
    linarith
  constructor
  · linarith
  · rw [mul_add]; linarith

/-- **A sub-height window of the Type-I/II piece, given Watt.**  For `T ∈ [X^{1/3}, X]`, with
the amplifier degree `(2P)^k ≤ T^{ε/2} < (2P)^{k+1}` and divisor bounds `≤ X^{ε/1000}` below `X²`:
the window has mean square `≤ √(10⁷ C λ⁴ X^{-ε/200})`. -/
theorem typeI_II_subHeight_window_bound (hW : MTWattBound) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10000) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X Y δ : ℝ} (data : MTTypeI_II_PieceData X Y δ ε) {B : Finset ℕ}
      {P a εU lam T : ℝ} {E : Set ℝ},
      MTUniformDivisorBounded 5 data.α → MTUniformDivisorBounded 5 data.β →
      1 ≤ lam →
      (∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ≤ X ^ (ε / 1000) ∧
        (n.divisors.card : ℝ) ^ 5 ≤ X ^ (ε / 1000) ∧ (n.divisors.card : ℝ) ^ 17 ≤ X ^ (ε / 1000)) →
      (∀ p ∈ B, p.Prime) → (∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) → 2 ≤ P → (2 : ℝ) ^ 500 ≤ 2 * P →
      2 * P ≤ X ^ (ε / 3000) → 0 < a → Real.log X ^ a ≤ P → 1 / a + εU / 5 ≤ 91 / 100 →
      0 ≤ δ → 1 / 2 ≤ data.M₁ → 1 / 2 ≤ data.M₂ → 1 ≤ ⌊data.M₃⌋₊ →
      ⌊data.M₃⌋₊ < ⌊(1 + δ) * data.M₃⌋₊ → ⌊(1 + δ) * data.M₃⌋₊ ≤ 2 * ⌊data.M₃⌋₊ →
      data.M₃ / 2 ≤ (⌊data.M₃⌋₊ : ℝ) → X / (2 * lam ^ 2) ≤ data.M₁ * data.M₂ * data.M₃ →
      128 * X ^ (1 - ε / 2) ≤ X ^ 2 →
      2 ≤ T → T ≤ X → X ^ (1 / 3 : ℝ) ≤ T → MeasurableSet E → E ⊆ Set.Icc (T / 2) T →
      (∀ t ∈ E, P ^ (-εU / 10) ≤
        ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
      ∫ t in E, ‖mtTypeI_IIShortFactor data t * mtTypeI_IITwistFactor data t *
          mtTypeI_IILongFactor data t‖ ^ (2 : ℕ) ≤
        Real.sqrt (10 ^ 7 * C * lam ^ 4 * X ^ (-(ε / 200))) := by
  obtain ⟨C, hC, hwin⟩ := setIntegral_typeI_II_window_le hW (η := ε / 1000) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro X Y δ data B P a εU lam T E hα hβ hlam hdiv hBp hB hP h2P hPX ha hPa hexp hδ hM₁ hM₂
    hN1 hNN' hN' hN2 hprod hlen hT2 hTX hT3 hE hEsub hS
  have hT0 : 0 < T := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hP1 : (1 : ℝ) ≤ P := le_trans (by norm_num) hP
  have hP0 : (0 : ℝ) ≤ P := le_trans (by norm_num) hP
  have hlong : ∀ t, mtTypeI_IILongFactor data t =
      mtWattUnitBlock ⌊data.M₃⌋₊ ⌊(1 + δ) * data.M₃⌋₊ t := mtTypeI_IILongFactor_eq data hδ
  simp_rw [hlong]
  -- the amplifier degree
  have hPT : 2 * P ≤ T ^ (ε / 1000) := by
    refine hPX.trans ?_
    calc X ^ (ε / 3000) = (X ^ (1 / 3 : ℝ)) ^ (ε / 1000) := by
          rw [← Real.rpow_mul hX0.le]; ring_nf
      _ ≤ T ^ (ε / 1000) := Real.rpow_le_rpow (by positivity) hT3 (by positivity)
  obtain ⟨k, hk⟩ : ∃ k, k = amplifierDegree (T ^ (ε / 2)) P := ⟨_, rfl⟩
  have hθL : ε / 2 ≤ ((500 : ℕ) : ℝ) * (ε / 1000) := by push_cast; linarith
  obtain ⟨hk1, hkT, hpk, hq, hkP, hkX⟩ := amplifier_degree_facts_general (T := T) (P := P)
    (X := X) (a := a) (θ := ε / 2) (ν := ε / 1000) (L := 500) hk hP1 h2P (by norm_num) hθL
    (by positivity) (by linarith) (by linarith) hPT (by linarith) hTX ha hPa
  have hpk' : T ^ (249 * ε / 500) ≤ P ^ k := by
    rw [show 249 * ε / 500 = ε / 2 - 2 * (ε / 1000) by ring]; exact hpk
  have hPP : P ≤ 2 * P := by linarith only [hP0]
  have hpkT : P ^ k ≤ T ^ (ε / 2) := (pow_le_pow_left₀ hP0 hPP k).trans hkT
  have hkX' : (2 * P) ^ k ≤ X ^ (ε / 2) :=
    hkT.trans (Real.rpow_le_rpow hT0.le hTX (by positivity))
  have hLX := typeI_II_length_le hX1 hε.le hM₁ hM₂ data.square_product_le (by positivity) hkX'
    hlen
  have hf2 : 8 * X ^ (1 - ε) ≤ X ^ 2 := by
    have h1 : X ^ (1 - ε) ≤ X ^ (1 - ε / 2) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    linarith
  obtain ⟨hBβ, hD, hBf⟩ := typeI_II_coefficient_bounds data hα hβ hdiv (by linarith only [hT2, hTX])
    hε hε1 hM₁ hM₂ hLX hf2
  have hXe0 : 0 < X ^ (ε / 1000) := by positivity
  have hw := hwin data.α data.β hM₁ hM₂ hXe0 hBβ hN1 hNN' hN' hBp hB hP1 hk1
    (Nat.le_ceil _) hT2 hE hEsub hS hXe0 hD hXe0 hBf
  refine hw.trans ?_
  obtain ⟨hQ1, hQ2⟩ := typeI_II_envelope_bounds data hlam hM₁ hM₂ hN1 hN2 hprod hT2 hTX hT3 hε hε1
  have hKf : ((⌈2 * data.M₁⌉₊ * ⌈2 * data.M₁⌉₊ * ⌈2 * data.M₂⌉₊ : ℕ) : ℝ) ≤
      64 * (data.M₁ * data.M₁ * data.M₂) := by
    push_cast
    have h1 := natCeil_two_mul_le hM₁
    have h2 := natCeil_two_mul_le hM₂
    calc ((⌈2 * data.M₁⌉₊ : ℕ) : ℝ) * ((⌈2 * data.M₁⌉₊ : ℕ) : ℝ) * ((⌈2 * data.M₂⌉₊ : ℕ) : ℝ)
        ≤ (4 * data.M₁) * (4 * data.M₁) * (4 * data.M₂) := by gcongr
      _ = 64 * (data.M₁ * data.M₁ * data.M₂) := by ring
  have hf : (1 : ℝ) ≤ k.factorial := by exact_mod_cast k.factorial_pos
  have hp1 : (1 : ℝ) ≤ P ^ k := one_le_pow₀ hP1
  have hfp : (k.factorial : ℝ) ≤ (P ^ k) ^ (1 / a) := factorial_le_pow_rpow_inv hP0 hkP
  exact typeI_II_window_value_le hf hp1 (by positivity) hC hfp hexp hpk' hpkT hq hT2 hTX hT3
    le_rfl hXe0 le_rfl hXe0 le_rfl hXe0 le_rfl hM₁ hM₂ hKf (by positivity) hQ1 hQ2 hε

/-- A dyadic polynomial on `(M, 2M]` vanishes when `M < 1/2`. -/
theorem perronPoly_dyadic_eq_zero_of_lt (α : ℕ → ℂ) {M : ℝ} (h : M < 1 / 2) (t : ℝ) :
    perronPoly (fun n => mtRealIntervalAF α M (2 * M) n) ⌈2 * M⌉₊ 1 t = 0 := by
  unfold perronPoly
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
  dsimp only
  rw [mtRealIntervalAF_apply_of_pos _ _ _ (by omega)]
  have hn' : ¬ (M < (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) := by
    rintro ⟨-, h2⟩
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  rw [if_neg hn', zero_mul]

/-- `M₁M₂ ≤ X^{5/8-ε}` from `M₁²M₂ ≤ X^{1-ε}` and `M₂ ≤ X^{1/4-ε}`. -/
theorem typeI_II_short_product_le {X M₁ M₂ ε : ℝ} (hX : 0 < X) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hsq : M₁ ^ (2 : ℕ) * M₂ ≤ X ^ (1 - ε)) (hM₂X : M₂ ≤ X ^ (1 / 4 - ε)) :
    M₁ * M₂ ≤ X ^ (1 / 2 + (1 / 8 - ε)) := by
  have h2 : (M₁ * M₂) ^ 2 ≤ (X ^ (1 / 2 + (1 / 8 - ε))) ^ 2 := by
    rw [← Real.rpow_natCast (X ^ (1 / 2 + (1 / 8 - ε))) 2, ← Real.rpow_mul hX.le]
    calc (M₁ * M₂) ^ 2 = (M₁ ^ (2 : ℕ) * M₂) * M₂ := by ring
      _ ≤ X ^ (1 - ε) * X ^ (1 / 4 - ε) := mul_le_mul hsq hM₂X hM₂ (by positivity)
      _ = X ^ ((1 / 2 + (1 / 8 - ε)) * ((2 : ℕ) : ℝ)) := by
          rw [← Real.rpow_add hX]; congr 1; push_cast; ring
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h2

/-- **The Type-I/II case of (5.3), explicit form, given Watt.** -/
theorem typeI_II_setIntegral_le_explicit (hW : MTWattBound) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10000) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X Y δ : ℝ} (data : MTTypeI_II_PieceData X Y δ ε) {B : Finset ℕ}
      {P a εU lam T₀ : ℝ} {U : Set ℝ},
      MTUniformDivisorBounded 5 data.α → MTUniformDivisorBounded 5 data.β →
      lam = Real.log X → 1 ≤ lam →
      (∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ≤ X ^ (ε / 1000) ∧
        (n.divisors.card : ℝ) ^ 5 ≤ X ^ (ε / 1000) ∧ (n.divisors.card : ℝ) ^ 17 ≤ X ^ (ε / 1000)) →
      (∀ p ∈ B, p.Prime) → (∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) → 2 ≤ P → (2 : ℝ) ^ 500 ≤ 2 * P →
      2 * P ≤ X ^ (ε / 3000) → 0 < a → Real.log X ^ a ≤ P → 1 / a + εU / 5 ≤ 91 / 100 →
      2 ≤ T₀ → T₀ ≤ X → 6 * lam ^ 2 * X ^ (1 / 2 + (1 / 8 - ε)) ≤ X →
      4 * lam ^ 2 * X ^ (1 / 3 : ℝ) ≤ X ^ (3 / 8 : ℝ) → X / lam ^ 2 ≤ Y → 0 ≤ δ → δ ≤ 1 / 2 →
      128 * X ^ (1 - ε / 2) ≤ X ^ 2 → MeasurableSet U → U ⊆ Set.Icc T₀ X →
      (∀ t ∈ U, P ^ (-εU / 10) ≤
        ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
      ∫ t in U, ‖mtTypeI_IIShortFactor data t * mtTypeI_IITwistFactor data t *
          mtTypeI_IILongFactor data t‖ ^ (2 : ℕ) ≤
        ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) *
          (2 * 10 ^ 6 * (2 * (1 + Real.log (24 * X))) ^ fourthMomentExponent 5 / T₀ +
            Real.sqrt (10 ^ 7 * C * lam ^ 4 * X ^ (-(ε / 200)))) := by
  obtain ⟨C, hC, hsub⟩ := typeI_II_subHeight_window_bound hW hε hε1
  refine ⟨C, hC, ?_⟩
  intro X Y δ data B P a εU lam T₀ U hα hβ hlam hlam1 hdiv hBp hB hP h2P hPX ha hPa hexp hT₀
    hT₀X hbig hthird hY hδ0 hδ hlen hUm hUsub hS
  have hX1 : 1 ≤ X := le_trans (by norm_num) (hT₀.trans hT₀X)
  have hX0 : 0 < X := by linarith only [hX1]
  obtain ⟨A, hA⟩ : ∃ A, A = 2 * 10 ^ 6 * (2 * (1 + Real.log (24 * X))) ^ fourthMomentExponent 5 / T₀ :=
    ⟨_, rfl⟩
  obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = Real.sqrt (10 ^ 7 * C * lam ^ 4 * X ^ (-(ε / 200))) := ⟨_, rfl⟩
  rw [← hA, ← hBd]
  have hA0 : 0 ≤ A := by
    rw [hA]
    have h24 : 0 ≤ 2 * (1 + Real.log (24 * X)) := by
      have := Real.log_nonneg (by linarith only [hX1] : (1 : ℝ) ≤ 24 * X); linarith only [this]
    exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg h24 _)) (by linarith only [hT₀])
  have hBd0 : 0 ≤ Bd := by rw [hBd]; exact Real.sqrt_nonneg _
  have hRHS0 : 0 ≤ ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) * (A + Bd) := by positivity
  set F : ℝ → ℝ := fun t => ‖mtTypeI_IIShortFactor data t * mtTypeI_IITwistFactor data t *
    mtTypeI_IILongFactor data t‖ ^ 2 with hF
  have hcont : Continuous F := (((continuous_mtTypeI_IIShortFactor data).mul
    (continuous_mtTypeI_IITwistFactor data)).mul (continuous_mtTypeI_IILongFactor data)).norm.pow 2
  -- degenerate factors
  by_cases hM₁ : data.M₁ < 1 / 2
  · have hz : ∀ t, F t = 0 := by
      intro t; rw [hF]; dsimp only
      rw [mtTypeI_IIShortFactor, perronPoly_dyadic_eq_zero_of_lt data.α hM₁ t]; simp
    simp only [show F = fun _ => (0 : ℝ) from funext hz, integral_zero]; exact hRHS0
  push Not at hM₁
  by_cases hM₂ : data.M₂ < 1 / 2
  · have hz : ∀ t, F t = 0 := by
      intro t; rw [hF]; dsimp only
      rw [mtTypeI_IITwistFactor, perronPoly_dyadic_eq_zero_of_lt data.β hM₂ t]; simp
    simp only [show F = fun _ => (0 : ℝ) from funext hz, integral_zero]; exact hRHS0
  push Not at hM₂
  have hM₁0 : 0 < data.M₁ := by linarith only [hM₁]
  have hM₂0 : 0 < data.M₂ := by linarith only [hM₂]
  have hM₁₂ := typeI_II_short_product_le hX0 hM₁0.le hM₂0.le data.square_product_le data.M₂_le
  obtain ⟨hprod, hN1, hN2, hN'⟩ := typeI_long_scale_facts (M₁ := data.M₁ * data.M₂)
    (M₂ := data.M₃) hlam1 hbig (by positivity) hM₁₂ hY data.product_mem.1 hδ0 hδ
  have hlong : ∀ t, mtTypeI_IILongFactor data t =
      mtWattUnitBlock ⌊data.M₃⌋₊ ⌊(1 + δ) * data.M₃⌋₊ t := mtTypeI_IILongFactor_eq data hδ0
  by_cases hNN' : ⌊(1 + δ) * data.M₃⌋₊ ≤ ⌊data.M₃⌋₊
  · have hz : ∀ t, F t = 0 := by
      intro t; rw [hF]; dsimp only
      rw [hlong t, mtWattUnitBlock_eq_zero_of_le hNN' t]; simp
    simp only [show F = fun _ => (0 : ℝ) from funext hz, integral_zero]; exact hRHS0
  push Not at hNN'
  -- `M₃ ≥ X^{3/8}/(2λ²)`, so the sub-height windows lie above `X^{1/3}`
  have hlam0 : 0 < lam := by linarith only [hlam1]
  have hM₁₂X : data.M₁ * data.M₂ ≤ X := by
    refine hM₁₂.trans ?_
    calc X ^ (1 / 2 + (1 / 8 - ε)) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith only [hε])
      _ = X := Real.rpow_one X
  have hM₃lo : X ^ (3 / 8 : ℝ) / (2 * lam ^ 2) ≤ data.M₃ := by
    have h58 : data.M₁ * data.M₂ ≤ X ^ (5 / 8 : ℝ) := hM₁₂.trans
      (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith only [hε]))
    have e : X ^ (5 / 8 : ℝ) * (X ^ (3 / 8 : ℝ) / (2 * lam ^ 2)) = X / (2 * lam ^ 2) := by
      rw [← mul_div_assoc, ← Real.rpow_add hX0]; norm_num
    have hpos58 : 0 < X ^ (5 / 8 : ℝ) := by positivity
    have h1 : X / (2 * lam ^ 2) ≤ X ^ (5 / 8 : ℝ) * data.M₃ :=
      hprod.trans (mul_le_mul_of_nonneg_right h58 data.M₃_pos.le)
    rw [← e] at h1
    exact le_of_mul_le_mul_left h1 hpos58
  refine (setIntegral_le_sum_height_windows hcont (fun t => by positivity) (by linarith only [hT₀])
    hT₀X hUsub).trans ?_
  calc ∑ j : Fin (Nat.log 2 ⌊2 * X / T₀⌋₊ + 1),
        ∫ t in U ∩ Set.Icc (X * (1 / 2) ^ ((j : ℕ) + 1)) (X * (1 / 2) ^ (j : ℕ)), F t
      ≤ ∑ _j : Fin (Nat.log 2 ⌊2 * X / T₀⌋₊ + 1), (A + Bd) := by
        refine Finset.sum_le_sum fun j _ => ?_
        obtain ⟨T, hTdef⟩ : ∃ T, T = X * (1 / 2) ^ (j : ℕ) := ⟨_, rfl⟩
        have hEsub : U ∩ Set.Icc (X * (1 / 2) ^ ((j : ℕ) + 1)) (X * (1 / 2) ^ (j : ℕ)) ⊆
            Set.Icc (T / 2) T := by
          intro t ht
          refine ⟨?_, hTdef ▸ ht.2.2⟩
          have h := ht.2.1
          rw [pow_succ] at h
          rw [hTdef]; linarith only [h]
        rcases (U ∩ Set.Icc (X * (1 / 2) ^ ((j : ℕ) + 1)) (X * (1 / 2) ^ (j : ℕ))).eq_empty_or_nonempty
          with hE | ⟨t₀, ht₀⟩
        · rw [hE, setIntegral_empty]; positivity
        have hT₀T : T₀ ≤ T := (hUsub ht₀.1).1.trans (hTdef ▸ ht₀.2.2)
        have hTX : T ≤ X := by
          rw [hTdef]
          have : (1 / 2 : ℝ) ^ (j : ℕ) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          nlinarith
        have hT2 : 2 ≤ T := hT₀.trans hT₀T
        have hEm : MeasurableSet (U ∩ Set.Icc (X * (1 / 2) ^ ((j : ℕ) + 1)) (X * (1 / 2) ^ (j : ℕ))) :=
          hUm.inter measurableSet_Icc
        rcases le_or_gt T (⌊data.M₃⌋₊ : ℝ) with hTN | hTN
        · have h := typeI_II_overHeight_window_bound data hα hβ hδ0 hM₁ hM₂ hN1 hNN' hN'
            (by linarith only [hT₀]) hT₀T hT2 hTN hEm hEsub hM₁₂X hX1
          rw [← hA] at h
          linarith only [h, hBd0]
        · have hT3 : X ^ (1 / 3 : ℝ) ≤ T := by
            have h1 : X ^ (1 / 3 : ℝ) ≤ X ^ (3 / 8 : ℝ) / (4 * lam ^ 2) := by
              rw [le_div_iff₀ (by positivity)]; linarith only [hthird]
            have h2 : X ^ (3 / 8 : ℝ) / (4 * lam ^ 2) = X ^ (3 / 8 : ℝ) / (2 * lam ^ 2) / 2 := by
              field_simp; ring
            linarith only [h1, h2, hM₃lo, hN2, hTN]
          have h := hsub data hα hβ hlam1 hdiv hBp hB hP h2P hPX ha hPa hexp hδ0 hM₁ hM₂ hN1 hNN'
            hN' hN2 hprod hlen hT2 hTX hT3 hEm hEsub (fun t ht => hS t ht.1)
          rw [← hBd] at h
          linarith only [h, hA0]
    _ = ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) * (A + Bd) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Absorbing the Type-I/II windows.**  With `T₀ = exp(c (log X)^{1/2})`:
`(⌊log₂(2X/T₀)⌋ + 1)(2·10⁶ (2Λ₀)^e/T₀ + √(10⁷ C λ⁴ X^{-ε/200})) ≤ exp(-(log X)^{1/40})`. -/
theorem eventually_typeI_II_window_count_absorbed {C c ε : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      ((Nat.log 2 ⌊2 * X / Real.exp (c * Real.log X ^ ((1 : ℝ) / 2))⌋₊ + 1 : ℕ) : ℝ) *
        (2 * 10 ^ 6 * (2 * (1 + Real.log (24 * X))) ^ fourthMomentExponent 5 /
            Real.exp (c * Real.log X ^ ((1 : ℝ) / 2)) +
          Real.sqrt (10 ^ 7 * C * Real.log X ^ 4 * X ^ (-(ε / 200)))) ≤
        Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) := by
  have hL : ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 1 ≤ c * L ^ ((1 : ℝ) / 2) ∧
      L ^ (1 / 30 : ℝ) ≤ c * L ^ ((1 : ℝ) / 2) ∧ L ^ (1 / 40 : ℝ) ≤ ε / 400 * L := by
    have h1 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (1 / c)
    have h2 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 15)).eventually_ge_atTop (1 / c)
    have h3 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 39 / 40)).eventually_ge_atTop
      (400 / ε)
    filter_upwards [h1, h2, h3, eventually_ge_atTop (1 : ℝ)] with L h1 h2 h3 hL1
    have hL0 : 0 < L := by linarith
    refine ⟨hL1, ?_, ?_, ?_⟩
    · rw [div_le_iff₀ hc] at h1; linarith
    · have hsplit : L ^ ((1 : ℝ) / 2) = L ^ (7 / 15 : ℝ) * L ^ (1 / 30 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [div_le_iff₀ hc] at h2
      have h30 : 0 ≤ L ^ (1 / 30 : ℝ) := Real.rpow_nonneg hL0.le _
      rw [hsplit]
      have := mul_le_mul_of_nonneg_right h2 h30
      linarith
    · have hsplit : L = L ^ (39 / 40 : ℝ) * L ^ (1 / 40 : ℝ) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [div_le_iff₀ hε] at h3
      have h40 : 0 ≤ L ^ (1 / 40 : ℝ) := Real.rpow_nonneg hL0.le _
      have := mul_le_mul_of_nonneg_right h3 h40
      calc L ^ (1 / 40 : ℝ) = 400 * L ^ (1 / 40 : ℝ) / 400 := by ring
        _ ≤ L ^ (39 / 40 : ℝ) * ε * L ^ (1 / 40 : ℝ) / 400 := by gcongr
        _ = ε / 400 * (L ^ (39 / 40 : ℝ) * L ^ (1 / 40 : ℝ)) := by ring
        _ = ε / 400 * L := by rw [← hsplit]
  filter_upwards [Real.tendsto_log_atTop.eventually hL,
    eventually_polylog_mul_exp_neg_le (fourthMomentExponent 5 + 1)
      (C := 6 * 10 ^ 6 * 2 ^ fourthMomentExponent 5) (by positivity),
    eventually_polylog_mul_rpow_neg_le 6 (C := 9 * 10 ^ 7 * C) (κ := ε / 400) (by positivity)
      (by positivity),
    eventually_ge_atTop (1 : ℝ)] with X ⟨hL1, hcL1, hcL, hL40⟩ habsA habsB hX1
  have hX0 : 0 < X := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩
  rw [← hLdef] at hL1 hcL1 hcL hL40 habsA habsB ⊢
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, T₀ = Real.exp (c * L ^ ((1 : ℝ) / 2)) := ⟨_, rfl⟩
  rw [← hT₀]
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀, Λ₀ = 1 + Real.log (24 * X) := ⟨_, rfl⟩
  rw [← hΛ₀] at habsA habsB ⊢
  have hLΛ : L + 1 ≤ Λ₀ := by
    rw [hΛ₀, hLdef, Real.log_mul (by norm_num) hX0.ne']
    have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    linarith
  have hΛ1 : 1 ≤ Λ₀ := by linarith
  have hT₀2 : 2 ≤ T₀ := by rw [hT₀]; linarith [Real.add_one_le_exp (c * L ^ ((1 : ℝ) / 2))]
  have hT₀0 : 0 < T₀ := by linarith
  -- the window count
  have hJ : ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * Λ₀ := by
    push_cast
    rcases lt_or_ge (2 * X / T₀) 1 with h | h
    · have : ⌊2 * X / T₀⌋₊ = 0 := Nat.floor_eq_zero.2 h
      rw [this, Nat.log_zero_right]; push_cast; linarith
    · have hlog := natLog_two_floor_le h
      have hle : 2 * X / T₀ ≤ X := by
        rw [div_le_iff₀ hT₀0]; nlinarith
      have hlogX := Real.log_le_log (by positivity) hle
      rw [← hLdef] at hlogX
      linarith
  have hJ0 : (0 : ℝ) ≤ ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hE0 : 0 < Real.exp (-L ^ (1 / 40 : ℝ)) := Real.exp_pos _
  -- the over-height part
  have hpartA : ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) *
      (2 * 10 ^ 6 * (2 * Λ₀) ^ fourthMomentExponent 5 / T₀) ≤
      Real.exp (-L ^ (1 / 40 : ℝ)) / 4 := by
    have hA0 : 0 ≤ 2 * 10 ^ 6 * (2 * Λ₀) ^ fourthMomentExponent 5 / T₀ := by positivity
    have hinv : 1 / T₀ ≤ Real.exp (-L ^ (1 / 30 : ℝ)) := by
      rw [hT₀, one_div, ← Real.exp_neg]; exact Real.exp_le_exp.2 (by linarith)
    calc ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) *
          (2 * 10 ^ 6 * (2 * Λ₀) ^ fourthMomentExponent 5 / T₀)
        ≤ 3 * Λ₀ * (2 * 10 ^ 6 * (2 * Λ₀) ^ fourthMomentExponent 5 / T₀) :=
          mul_le_mul_of_nonneg_right hJ hA0
      _ = 6 * 10 ^ 6 * 2 ^ fourthMomentExponent 5 * Λ₀ ^ (fourthMomentExponent 5 + 1) *
            (1 / T₀) := by rw [mul_pow, pow_succ]; ring
      _ ≤ 6 * 10 ^ 6 * 2 ^ fourthMomentExponent 5 * Λ₀ ^ (fourthMomentExponent 5 + 1) *
            Real.exp (-L ^ (1 / 30 : ℝ)) := by gcongr
      _ ≤ _ := habsA
  -- the sub-height part
  have hpartB : ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) *
      Real.sqrt (10 ^ 7 * C * L ^ 4 * X ^ (-(ε / 200))) ≤ Real.exp (-L ^ (1 / 40 : ℝ)) / 2 := by
    have hXe : X ^ (-(ε / 400)) ≤ Real.exp (-L ^ (1 / 40 : ℝ)) := by
      rw [Real.rpow_def_of_pos hX0, ← hLdef]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hXsplit : X ^ (-(ε / 200)) = X ^ (-(ε / 400)) * X ^ (-(ε / 400)) := by
      rw [← Real.rpow_add hX0]; ring_nf
    have hL4 : L ^ 4 ≤ Λ₀ ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    have hXε0 : 0 < X ^ (-(ε / 400)) := by positivity
    have hsq : (3 * Λ₀) ^ 2 * (10 ^ 7 * C * L ^ 4 * X ^ (-(ε / 200))) ≤
        (Real.exp (-L ^ (1 / 40 : ℝ)) / 2) ^ 2 := by
      calc (3 * Λ₀) ^ 2 * (10 ^ 7 * C * L ^ 4 * X ^ (-(ε / 200)))
          ≤ (3 * Λ₀) ^ 2 * (10 ^ 7 * C * Λ₀ ^ 4 * X ^ (-(ε / 200))) := by gcongr
        _ = (9 * 10 ^ 7 * C * Λ₀ ^ 6 * X ^ (-(ε / 400))) * X ^ (-(ε / 400)) := by
            rw [hXsplit]; ring
        _ ≤ (Real.exp (-L ^ (1 / 40 : ℝ)) / 4) * Real.exp (-L ^ (1 / 40 : ℝ)) := by
            gcongr
        _ = (Real.exp (-L ^ (1 / 40 : ℝ)) / 2) ^ 2 := by ring
    calc ((Nat.log 2 ⌊2 * X / T₀⌋₊ + 1 : ℕ) : ℝ) * Real.sqrt (10 ^ 7 * C * L ^ 4 * X ^ (-(ε / 200)))
        ≤ 3 * Λ₀ * Real.sqrt (10 ^ 7 * C * L ^ 4 * X ^ (-(ε / 200))) :=
          mul_le_mul_of_nonneg_right hJ (Real.sqrt_nonneg _)
      _ = Real.sqrt ((3 * Λ₀) ^ 2 * (10 ^ 7 * C * L ^ 4 * X ^ (-(ε / 200)))) := by
          rw [Real.sqrt_mul (sq_nonneg (3 * Λ₀)), Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 3 * Λ₀)]
      _ ≤ Real.sqrt ((Real.exp (-L ^ (1 / 40 : ℝ)) / 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.exp (-L ^ (1 / 40 : ℝ)) / 2 := Real.sqrt_sq (by positivity)
  rw [mul_add]
  linarith

/-- **The Type-I/II case of Matomäki–Teräväinen (5.3), given Watt.**  For
`P ∈ [(log X)^a, (log X)^{6/5}]`, `a ≥ 1.0999`, and `U ⊆ [exp(c (log X)^{1/2}), X]` on which the
prime polynomial is `≥ P^{-ε_U/10}`, the Type-I/II piece has mean square
`≤ exp(-(log X)^{1/40})`. -/
theorem eventually_typeI_II_setIntegral_le (hW : MTWattBound) {a₀ ε εU c : ℝ} {A : ℕ}
    (hA : 1 ≤ A) (ha₀ : 10999 / 10000 ≤ a₀) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10000)
    (hεUε : εU ≤ ε) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ (a P : ℝ) (B : Finset ℕ), a₀ ≤ a →
      Real.log X ^ a ≤ P → P ≤ Real.log X ^ (6 / 5 : ℝ) →
      (∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ {Y : ℝ} (data : MTTypeI_II_PieceData X Y (mtPaperWidth A X) ε),
      MTUniformDivisorBounded 5 data.α → MTUniformDivisorBounded 5 data.β →
      X / Real.log X ^ 2 ≤ Y →
      ∀ U : Set ℝ, MeasurableSet U →
        U ⊆ Set.Icc (Real.exp (c * Real.log X ^ ((1 : ℝ) / 2))) X →
        (∀ t ∈ U, P ^ (-εU / 10) ≤
          ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
        ∫ t in U, ‖mtTypeI_IIShortFactor data t * mtTypeI_IITwistFactor data t *
            mtTypeI_IILongFactor data t‖ ^ 2 ≤
          Real.exp (-(Real.log X) ^ (1 / 40 : ℝ)) := by
  obtain ⟨C, hC, hexpl⟩ := typeI_II_setIntegral_le_explicit hW hε hε1
  have hL : ∀ᶠ L : ℝ in atTop, 2 ^ 499 ≤ L ∧ 1 ≤ c * L ^ ((1 : ℝ) / 2) ∧
      c * L ^ ((1 : ℝ) / 2) ≤ L := by
    have h1 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (1 / c)
    have h2 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop c
    filter_upwards [h1, h2, eventually_ge_atTop (2 ^ 499 : ℝ)] with L h1 h2 hL
    have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
    have hr0 : 0 < L ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hL0 _
    refine ⟨hL, ?_, ?_⟩
    · rw [div_le_iff₀ hc] at h1; linarith
    · have hsq : L = L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hL0]; norm_num
      calc c * L ^ ((1 : ℝ) / 2) ≤ L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right h2 hr0.le
        _ = L := hsq.symm
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
    eventually_card_divisors_pow_le_rpow 1 (η := ε / 1000) (by positivity),
    eventually_card_divisors_pow_le_rpow 5 (η := ε / 1000) (by positivity),
    eventually_card_divisors_pow_le_rpow 17 (η := ε / 1000) (by positivity),
    eventually_polylog_le_rpow 2 (C := 2) (κ := ε / 3000) (by norm_num) (by positivity),
    eventually_polylog_le_rpow 2 (C := 6) (κ := 3 / 8) (by norm_num) (by norm_num),
    eventually_polylog_le_rpow 2 (C := 4) (κ := 1 / 24) (by norm_num) (by norm_num),
    eventually_typeI_II_window_count_absorbed hC hc hε,
    eventually_ge_atTop (128 : ℝ)] with X ⟨hL499, hcL1, hcLL⟩ hδX hd1 hd5 hd17 hpolyP hpoly6 hpoly4
      habs hX128
  intro a P B ha₀a hPa hP65 hBiff Y data hα hβ hYlo U hU hUsub hS
  have hX0 : 0 < X := by linarith only [hX128]
  have hX1 : 1 ≤ X := by linarith only [hX128]
  have h499 : (1 : ℝ) ≤ 2 ^ 499 := one_le_pow₀ (by norm_num)
  have hlam1 : 1 ≤ Real.log X := le_trans h499 hL499
  have ha1 : 1 ≤ a := by linarith only [ha₀, ha₀a]
  have ha : 0 < a := by linarith only [ha1]
  have hlamP : Real.log X ≤ P := by
    calc Real.log X = Real.log X ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log X ^ a := Real.rpow_le_rpow_of_exponent_le hlam1 ha1
      _ ≤ P := hPa
  have h2P : (2 : ℝ) ^ 500 ≤ 2 * P := by
    have : (2 : ℝ) ^ 500 = 2 * 2 ^ 499 := by simpa using pow_succ' (2 : ℝ) 499
    rw [this]; exact mul_le_mul_of_nonneg_left (hL499.trans hlamP) (by norm_num)
  have hP : 2 ≤ P := by
    have : (2 : ℝ) ≤ 2 ^ 499 := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ 499 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact this.trans (hL499.trans hlamP)
  have hlog24 : Real.log X ≤ 1 + Real.log (24 * X) := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    linarith only [this]
  have hsq24 : Real.log X ^ 2 ≤ (1 + Real.log (24 * X)) ^ 2 :=
    pow_le_pow_left₀ (by linarith only [hlam1]) hlog24 2
  have hPX : 2 * P ≤ X ^ (ε / 3000) := by
    have h65 : Real.log X ^ (6 / 5 : ℝ) ≤ Real.log X ^ 2 := by
      rw [show Real.log X ^ 2 = Real.log X ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
      exact Real.rpow_le_rpow_of_exponent_le hlam1 (by norm_num)
    linarith only [hP65, h65, hsq24, hpolyP]
  have hexp : 1 / a + εU / 5 ≤ 91 / 100 := by
    have h1 : 1 / a ≤ 1 / (10999 / 10000) := one_div_le_one_div_of_le (by norm_num)
      (by linarith only [ha₀, ha₀a])
    have h2 : εU / 5 ≤ 1 / 50000 := by linarith only [hεUε, hε1]
    have h3 : (1 : ℝ) / (10999 / 10000) + 1 / 50000 ≤ 91 / 100 := by norm_num
    linarith only [h1, h2, h3]
  have hT₀2 : 2 ≤ Real.exp (c * Real.log X ^ ((1 : ℝ) / 2)) := by
    linarith only [Real.add_one_le_exp (c * Real.log X ^ ((1 : ℝ) / 2)), hcL1]
  have hT₀X : Real.exp (c * Real.log X ^ ((1 : ℝ) / 2)) ≤ X := by
    calc Real.exp (c * Real.log X ^ ((1 : ℝ) / 2)) ≤ Real.exp (Real.log X) :=
          Real.exp_le_exp.2 hcLL
      _ = X := Real.exp_log hX0
  have hbig : 6 * Real.log X ^ 2 * X ^ (1 / 2 + (1 / 8 - ε)) ≤ X := by
    have h6 : 6 * Real.log X ^ 2 ≤ X ^ (3 / 8 : ℝ) := by linarith only [hsq24, hpoly6]
    calc 6 * Real.log X ^ 2 * X ^ (1 / 2 + (1 / 8 - ε)) ≤
          X ^ (3 / 8 : ℝ) * X ^ (1 / 2 + (1 / 8 - ε)) :=
          mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hX0.le _)
      _ = X ^ (3 / 8 + (1 / 2 + (1 / 8 - ε))) := (Real.rpow_add hX0 _ _).symm
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith only [hε])
      _ = X := Real.rpow_one X
  have hthird : 4 * Real.log X ^ 2 * X ^ (1 / 3 : ℝ) ≤ X ^ (3 / 8 : ℝ) := by
    have h4 : 4 * Real.log X ^ 2 ≤ X ^ (1 / 24 : ℝ) := by linarith only [hsq24, hpoly4]
    calc 4 * Real.log X ^ 2 * X ^ (1 / 3 : ℝ) ≤ X ^ (1 / 24 : ℝ) * X ^ (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hX0.le _)
      _ = X ^ (3 / 8 : ℝ) := by rw [← Real.rpow_add hX0]; norm_num
  have hlen : 128 * X ^ (1 - ε / 2) ≤ X ^ 2 := by
    have h1 : X ^ (1 - ε / 2) ≤ X := by
      calc X ^ (1 - ε / 2) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1
            (by linarith only [hε])
        _ = X := Real.rpow_one X
    nlinarith
  have hδ0 : 0 ≤ mtPaperWidth A X := Real.rpow_nonneg (Real.log_nonneg hX1) _
  have hdiv : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X ^ 2 → (n.divisors.card : ℝ) ≤ X ^ (ε / 1000) ∧
      (n.divisors.card : ℝ) ^ 5 ≤ X ^ (ε / 1000) ∧ (n.divisors.card : ℝ) ^ 17 ≤ X ^ (ε / 1000) := by
    intro n hn hnX
    refine ⟨?_, hd5 n hn hnX, hd17 n hn hnX⟩
    simpa using hd1 n hn hnX
  have hBp : ∀ p ∈ B, p.Prime := fun p hp => ((hBiff p).1 hp).1
  have hBr : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P := fun p hp => ((hBiff p).1 hp).2
  exact (hexpl data hα hβ rfl hlam1 hdiv hBp hBr hP h2P hPX ha hPa hexp hT₀2 hT₀X hbig hthird
    hYlo hδ0 hδX hlen hU hUsub hS).trans habs

end

end RHTower.Sieve
