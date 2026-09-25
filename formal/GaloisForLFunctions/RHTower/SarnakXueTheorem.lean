import GaloisForLFunctions.RHTower.SarnakXueDimension
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# The Sarnak–Xue spectral gap for `Γ(p)`

With `R = 3 log p` (so `e^R = p³`), `K = 6(⌊log₂ p⌋ + 1)` and `ε = δ/4`, the multiplicity bound `dim_le`
becomes `(p - 1) ≤ c(δ) p^{1 - 3δ}` whenever an exceptional eigenvalue `λ = s(1-s)` with `s ≥ 5/6 + δ` exists
(`final_bound`). Hence for all large primes `p` no such eigenvalue exists (`sarnak_xue_gap`), i.e.
`λ₁(Γ(p)) ≥ 5/36 - η` in the exceptional range (`principal_congruence_gap`).
-/

namespace GaloisForLFunctions.RHTower.SarnakXueTheorem

/-- Parameter facts for `R = 3 log p`, `K = 6 (⌊log₂ p⌋ + 1)`. -/
theorem params {p : ℕ} (hp : 3 ≤ p) :
    let R := 3 * Real.log p
    let K := 6 * (Nat.log 2 p + 1)
    2 ≤ R ∧ Real.cosh (2 * R) < 2 ^ K ∧ Real.sqrt (2 ^ K) ≤ 8 * (p : ℝ) ^ 3 ∧
      ((2 : ℝ) ^ (K + 2)) ≤ 256 * (p : ℝ) ^ 6 ∧ Real.cosh R ≤ (p : ℝ) ^ 3 ∧
      (p : ℝ) ^ 3 / 2 ≤ Real.cosh R ∧ (K : ℝ) ≤ 6 * (Real.log p / Real.log 2 + 1) := by
  intro R K
  have hp0 : (0 : ℝ) < p := by positivity
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hexpR : Real.exp R = (p : ℝ) ^ 3 := by
    simp only [R]; rw [← Real.log_rpow hp0, Real.exp_log (by positivity)]; norm_cast
  set L := Nat.log 2 p
  have hL1 : (p : ℝ) < 2 ^ (L + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) p
  have hL2 : (2 : ℝ) ^ L ≤ p := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : p ≠ 0)
  have hK : (2 : ℝ) ^ K = ((2 : ℝ) ^ (L + 1)) ^ 6 := by simp only [K, L]; rw [← pow_mul, mul_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `3 log 3 ≥ 2`
    have : (1 : ℝ) ≤ Real.log p := by
      rw [Real.le_log_iff_exp_le hp0]
      have := Real.exp_one_lt_d9; linarith
    simp only [R]; linarith
  · have hc : Real.cosh (2 * R) ≤ Real.exp (2 * R) := by
      rw [Real.cosh_eq]; have := Real.exp_pos (-(2 * R))
      have : Real.exp (-(2 * R)) ≤ Real.exp (2 * R) := Real.exp_le_exp.mpr (by
        have : 0 ≤ R := by simp only [R]; have := Real.log_nonneg (by linarith : (1:ℝ) ≤ p); linarith
        linarith)
      linarith
    have he : Real.exp (2 * R) = (p : ℝ) ^ 6 := by
      rw [show 2 * R = R + R by ring, Real.exp_add, hexpR]; ring
    rw [hK]
    calc Real.cosh (2 * R) ≤ (p : ℝ) ^ 6 := hc.trans he.le
      _ < ((2 : ℝ) ^ (L + 1)) ^ 6 := pow_lt_pow_left₀ hL1 hp0.le (by norm_num)
  · rw [hK, show ((2 : ℝ) ^ (L + 1)) ^ 6 = (((2 : ℝ) ^ (L + 1)) ^ 3) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
    have : (2 : ℝ) ^ (L + 1) ≤ 2 * p := by rw [pow_succ]; linarith
    calc ((2 : ℝ) ^ (L + 1)) ^ 3 ≤ (2 * p) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
      _ = 8 * (p : ℝ) ^ 3 := by ring
  · rw [pow_add, hK]
    have : (2 : ℝ) ^ (L + 1) ≤ 2 * p := by rw [pow_succ]; linarith
    calc ((2 : ℝ) ^ (L + 1)) ^ 6 * 2 ^ 2 ≤ (2 * p) ^ 6 * 2 ^ 2 := by gcongr
      _ = 256 * (p : ℝ) ^ 6 := by ring
  · rw [← hexpR, Real.cosh_eq]
    have : Real.exp (-R) ≤ Real.exp R := Real.exp_le_exp.mpr (by
      have : 0 ≤ R := by simp only [R]; have := Real.log_nonneg (by linarith : (1:ℝ) ≤ p); linarith
      linarith)
    linarith
  · rw [← hexpR, Real.cosh_eq]; have := Real.exp_pos (-R); linarith
  · have hl : (L : ℝ) * Real.log 2 ≤ Real.log p := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hL2
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : (L : ℝ) ≤ Real.log p / Real.log 2 := by rw [le_div_iff₀ hlog2]; exact hl
    simp only [K]; push_cast; linarith

/-- `log x ≤ x^ε / ε`. -/
theorem log_le_rpow {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) : Real.log x ≤ x ^ ε / ε := by
  have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx ε)
  rw [Real.log_rpow hx] at this
  rw [le_div_iff₀ hε]; linarith

/-- The explicit final estimate: for `p ≥ 3`, `s ≥ 5/6 + δ`, `ε = δ/4`,
`3 V p³ kb / ((cosh R)^s/16)² ≤ c(δ, C, V) p^{1 - 3δ}` with explicit `c`. -/
theorem final_bound {p : ℕ} (hp : 3 ≤ p) {δ s C V : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 6)
    (hs : 5 / 6 + δ ≤ s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (hV : 0 ≤ V) :
    let R := 3 * Real.log p
    let K := 6 * (Nat.log 2 p + 1)
    let ε := δ / 4
    3 * V * (p : ℝ) ^ 3 *
      ((16 * Real.cosh R * Real.sqrt 2 * (32 * (1 + C * 9 ^ ε) * ((2 : ℝ) ^ (K + 2)) ^ ε *
        (4 + 2 * K * ((p : ℝ) + 1) / p + 4 * K * Real.sqrt (2 ^ K) / (p : ℝ) ^ 3))) /
        (Real.cosh R ^ s / 16) ^ 2) ≤
      (3 * V * 16 * 2 * (32 * (1 + C * 9 ^ (δ / 4))) * 256 ^ (δ / 4) * 40 * 256 * 4 * (7 + 9 / δ)) *
        (p : ℝ) ^ (1 - 3 * δ) := by
  intro R K ε
  obtain ⟨hR, hK, hsq, h2K, hcR, hcR', hKle⟩ := params hp
  have hx3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hx0 : (0 : ℝ) < p := by linarith
  set x : ℝ := (p : ℝ) with hxdef
  have hε : 0 < ε := by simp only [ε]; linarith
  have hε8 : ε ≤ 1 / 8 := by simp only [ε]; linarith
  set A := 32 * (1 + C * 9 ^ ε)
  have hA : 0 ≤ A := by positivity
  -- numerator pieces
  have hE : ((2 : ℝ) ^ (K + 2)) ^ ε ≤ 256 ^ ε * x ^ (6 * ε) := by
    calc ((2 : ℝ) ^ (K + 2)) ^ ε ≤ (256 * x ^ 6) ^ ε := Real.rpow_le_rpow (by positivity) h2K hε.le
      _ = 256 ^ ε * x ^ (6 * ε) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast x 6,
            ← Real.rpow_mul hx0.le]; norm_num
  have hinner : 4 + 2 * K * (x + 1) / x + 4 * K * Real.sqrt (2 ^ K) / x ^ 3 ≤ 40 * (1 + K) := by
    have h1 : 2 * (K : ℝ) * (x + 1) / x ≤ 4 * K := by
      rw [div_le_iff₀ hx0]; have : (0 : ℝ) ≤ K := by positivity
      nlinarith
    have h2 : 4 * (K : ℝ) * Real.sqrt (2 ^ K) / x ^ 3 ≤ 32 * K := by
      rw [div_le_iff₀ (by positivity)]; have : (0 : ℝ) ≤ K := by positivity
      nlinarith
    have : (0 : ℝ) ≤ K := by positivity
    linarith
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hnum : 16 * Real.cosh R * Real.sqrt 2 * (A * ((2 : ℝ) ^ (K + 2)) ^ ε *
      (4 + 2 * K * (x + 1) / x + 4 * K * Real.sqrt (2 ^ K) / x ^ 3)) ≤
      16 * x ^ 3 * 2 * (A * (256 ^ ε * x ^ (6 * ε)) * (40 * (1 + K))) := by
    have hc0 : 0 ≤ Real.cosh R := (Real.cosh_pos R).le
    have hinner0 : 0 ≤ 4 + 2 * K * (x + 1) / x + 4 * K * Real.sqrt (2 ^ K) / x ^ 3 := by positivity
    gcongr
  -- denominator
  have hden : x ^ (6 * s) / 1024 ≤ (Real.cosh R ^ s / 16) ^ 2 := by
    have h1 : (x ^ 3 / 2) ^ s ≤ Real.cosh R ^ s := Real.rpow_le_rpow (by positivity) hcR' (by linarith)
    have h2 : (x ^ 3 / 2) ^ s = x ^ (3 * s) / 2 ^ s := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast x 3, ← Real.rpow_mul hx0.le]
      norm_num
    have h3 : (2 : ℝ) ^ s ≤ 2 := by
      calc (2 : ℝ) ^ s ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
        _ = 2 := Real.rpow_one 2
    have h4 : x ^ (3 * s) / 2 ≤ Real.cosh R ^ s := by
      rw [h2] at h1
      calc x ^ (3 * s) / 2 ≤ x ^ (3 * s) / 2 ^ s := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) h3
        _ ≤ _ := h1
    have h5 : x ^ (6 * s) = (x ^ (3 * s)) ^ 2 := by
      rw [← Real.rpow_natCast (x ^ (3 * s)) 2, ← Real.rpow_mul hx0.le]; norm_num; ring_nf
    rw [h5]
    have h6 : 0 ≤ x ^ (3 * s) / 2 / 16 := by positivity
    calc (x ^ (3 * s)) ^ 2 / 1024 = (x ^ (3 * s) / 2 / 16) ^ 2 := by ring
      _ ≤ (Real.cosh R ^ s / 16) ^ 2 := by
          apply pow_le_pow_left₀ h6
          linarith
  -- the logarithmic factor
  have hK1 : (1 : ℝ) + K ≤ (7 + 9 / δ) * x ^ δ := by
    have hl2 := Real.log_two_gt_d9
    have hlog : Real.log x ≤ x ^ δ / δ := log_le_rpow hx0 hδ
    have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h1 : (K : ℝ) ≤ 6 + 9 * Real.log x := by
      have : 6 * (Real.log x / Real.log 2) ≤ 9 * Real.log x := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    have hxd : 1 ≤ x ^ δ := Real.one_le_rpow (by linarith) hδ.le
    have : 9 * Real.log x ≤ 9 / δ * x ^ δ := by
      rw [div_mul_eq_mul_div, mul_div_assoc]
      linarith
    nlinarith
  -- assemble
  have hxs : 0 < x ^ (6 * s) := Real.rpow_pos_of_pos hx0 _
  have hpow : x ^ 3 * x ^ 3 * x ^ (6 * ε) / x ^ (6 * s) * x ^ δ ≤ x ^ (1 - 3 * δ) := by
    rw [← Real.rpow_natCast x 3, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_sub hx0,
      ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    simp only [ε]; push_cast; linarith
  have hKnn : (0 : ℝ) ≤ 1 + K := by positivity
  have hnum0 : 0 ≤ 16 * Real.cosh R * Real.sqrt 2 * (A * ((2 : ℝ) ^ (K + 2)) ^ ε *
      (4 + 2 * K * (x + 1) / x + 4 * K * Real.sqrt (2 ^ K) / x ^ 3)) := by
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 ^ (K + 2) by positivity) ε
    have := (Real.cosh_pos R).le
    positivity
  calc 3 * V * x ^ 3 * ((16 * Real.cosh R * Real.sqrt 2 * (A * ((2 : ℝ) ^ (K + 2)) ^ ε *
        (4 + 2 * K * (x + 1) / x + 4 * K * Real.sqrt (2 ^ K) / x ^ 3))) / (Real.cosh R ^ s / 16) ^ 2)
      ≤ 3 * V * x ^ 3 * ((16 * x ^ 3 * 2 * (A * (256 ^ ε * x ^ (6 * ε)) * (40 * (1 + K)))) /
          (x ^ (6 * s) / 1024)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (3 * V * 16 * 2 * A * 256 ^ ε * 40 * 256 * 4) * (1 + K) *
          (x ^ 3 * x ^ 3 * x ^ (6 * ε) / x ^ (6 * s)) := by
        field_simp
        ring
    _ ≤ (3 * V * 16 * 2 * A * 256 ^ ε * 40 * 256 * 4) * ((7 + 9 / δ) * x ^ δ) *
          (x ^ 3 * x ^ 3 * x ^ (6 * ε) / x ^ (6 * s)) := by
        gcongr
    _ = (3 * V * 16 * 2 * A * 256 ^ ε * 40 * 256 * 4 * (7 + 9 / δ)) *
          (x ^ 3 * x ^ 3 * x ^ (6 * ε) / x ^ (6 * s) * x ^ δ) := by ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hpow
        positivity

open MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SarnakXueDimension

/-- **Sarnak–Xue spectral gap for `Γ(p)`.** For every `δ ∈ (0, 1/6]` there is `P` such that for every prime
`p = N + 1 > P` no Maass cusp form on `Γ(p)` has eigenvalue `λ = s(1-s)` with `5/6 + δ ≤ s ≤ 1`. -/
theorem sarnak_xue_gap {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 6) :
    ∃ P : ℕ, ∀ N : ℕ, P ≤ N → (N + 1).Prime → ∀ (lam : Ioo (0 : ℝ) (1 / 4)) (s : ℝ),
      s * (1 - s) = lam → 5 / 6 + δ ≤ s → s ≤ 1 →
        IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := _root_.RHTower.card_divisors_le_const_mul_rpow (show 0 < δ / 4 by linarith)
  set V := (volume fd).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set c := (3 * V * 16 * 2 * (32 * (1 + C * 9 ^ (δ / 4))) * 256 ^ (δ / 4) * 40 * 256 * 4 * (7 + 9 / δ))
  have hc : 0 ≤ c := by positivity
  refine ⟨⌈(2 * c + 1) ^ (1 / (3 * δ))⌉₊ + 2, fun N hN hp lam s hs hsδ hs1 => ⟨fun f => ?_⟩⟩
  have hN2 : 2 ≤ N := by omega
  have hp3 : 3 ≤ N + 1 := by omega
  have hdim := dim_le hp hN2 lam f hs (by linarith) (by linarith) (params hp3).1
    (6 * (Nat.log 2 (N + 1) + 1)) (params hp3).2.1 (show 0 < δ / 4 by linarith) hC0.le hC
  have hfin := final_bound hp3 hδ hδ1 hsδ hs1 hC0.le hV
  simp only [kb] at hdim
  have hmain := hdim.trans hfin
  -- contradiction for large `p`
  set x : ℝ := ((N + 1 : ℕ) : ℝ)
  have hx0 : 0 < x := by positivity
  have hxN : x / 2 ≤ (N : ℝ) := by
    simp only [x]; push_cast
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hbig : (2 * c + 1) ^ (1 / (3 * δ)) < x := by
    have := Nat.le_ceil ((2 * c + 1) ^ (1 / (3 * δ)))
    have h2 : ((⌈(2 * c + 1) ^ (1 / (3 * δ))⌉₊ : ℕ) : ℝ) + 2 ≤ (N : ℝ) := by exact_mod_cast hN
    simp only [x]; push_cast; linarith
  have hxpow : 2 * c + 1 < x ^ (3 * δ) := by
    have h1 := Real.rpow_lt_rpow (by positivity) hbig (show 0 < 3 * δ by linarith)
    rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith), Real.rpow_one] at h1
  have hsplit : x ^ (1 - 3 * δ) = x / x ^ (3 * δ) := by
    rw [Real.rpow_sub hx0, Real.rpow_one]
  rw [hsplit] at hmain
  have hxd : 0 < x ^ (3 * δ) := Real.rpow_pos_of_pos hx0 _
  have : x / 2 ≤ c * (x / x ^ (3 * δ)) := hxN.trans hmain
  rw [mul_div_assoc', le_div_iff₀ hxd] at this
  nlinarith

/-- **Uniform spectral gap for principal congruence subgroups of prime level.** For every `η > 0` there is
`P` such that for every prime `p = N + 1 > P` the principal congruence subgroup `Γ(p)` has no Maass cusp
form with eigenvalue `λ ∈ (0, 5/36 - η)`: `λ₁(Γ(p)) ≥ 5/36 - η` in the exceptional range. -/
theorem principal_congruence_gap {η : ℝ} (hη : 0 < η) :
    ∃ P : ℕ, ∀ N : ℕ, P ≤ N → (N + 1).Prime → ∀ lam : ℝ, 0 < lam → lam < 5 / 36 - η →
      IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) := by
  set δ := min (η / 2) (1 / 6)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 6 := min_le_right _ _
  have hδη : δ ≤ η / 2 := min_le_left _ _
  obtain ⟨P, hP⟩ := sarnak_xue_gap hδ hδ1
  refine ⟨P, fun N hN hp lam hlam0 hlam => ?_⟩
  have hl4 : lam < 1 / 4 := by linarith
  set s := (1 + Real.sqrt (1 - 4 * lam)) / 2
  have hr : 0 ≤ 1 - 4 * lam := by linarith
  have hsq := Real.sq_sqrt hr
  have hs : s * (1 - s) = lam := by simp only [s]; nlinarith
  have hsqrt0 : 0 ≤ Real.sqrt (1 - 4 * lam) := Real.sqrt_nonneg _
  have hsqrt1 : Real.sqrt (1 - 4 * lam) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  have hs1 : s ≤ 1 := by simp only [s]; linarith
  have hshalf : 1 / 2 ≤ s := by simp only [s]; linarith
  have hsδ : 5 / 6 + δ ≤ s := by
    by_contra hlt
    push Not at hlt
    have hkey : (5 / 6 + δ) * (1 - (5 / 6 + δ)) < s * (1 - s) := by nlinarith
    nlinarith
  exact hP N hN hp ⟨lam, hlam0, hl4⟩ s hs hsδ hs1

end GaloisForLFunctions.RHTower.SarnakXueTheorem
