import GaloisForLFunctions.RHTower.KuznetsovLargeSieveGammaZero

/-!
# The large sieve inequality for `Γ₀(Q)`: DI Theorem 2

Let `𝓛_K(a)` be the weighted spectral sum of `large_sieve_gamma0_level` (`sieveLHS`); it is nondecreasing
in `K` (`sieveLHS_mono`).  Evaluating the Gaussian-weighted bound at `K₁ = K + √(6 log(1 + N/Q))`
kills the term `K₁² e^{−K₁²/2}((N/Q)² + (N/Q)³)` and gives, for every `δ ∈ (0, 1/4]`
(`large_sieve_gamma0_cubic`),

`𝓛_K(a) ≤ C_δ |H| (K³ + K N^{1+3δ}/Q) Σ|a_n|²`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex Filter Topology
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry RHTower.Sieve KuznetsovGauss KuznetsovSeparation

noncomputable section

/-- The weighted spectral side `Σ_j c₀(κ_j+1)e^{−πκ_j}[λ_j ≤ ¼+K²]|Σ a_n ρ_j(n)|² + (Eisenstein part)`. -/
def sieveLHS (L Q N : ℕ) (K : ℝ) (a : ℕ → ℂ) : ENNReal :=
  (∑' j : CuspEigenIndex L, ENNReal.ofReal (sieveWeight K j.1 *
      ‖∑ k ∈ Finset.Ioc N (N + N), a k * cuspCoeff j k (gamma0Vec L Q)‖ ^ 2)) +
    ∫⁻ r in Icc (-K) K, ENNReal.ofReal ((4 * Real.pi)⁻¹ *
      (specWeightConst * (|r| + 1) * Real.exp (-(Real.pi * |r|))) *
        ∑ i, ‖∑ k ∈ Finset.Ioc N (N + N), a k * eisCoeff (1 / 2 + r * Complex.I) (gamma0Vec L Q)
          (cuspBasisVec L i) ((k : ℤ) * ((L + 1 : ℕ) : ℤ))‖ ^ 2)

theorem sieveWeight_mono {K K' : ℝ} (hK : 0 ≤ K) (hKK : K ≤ K') (lam : ℝ) :
    sieveWeight K lam ≤ sieveWeight K' lam := by
  unfold sieveWeight
  by_cases h : lam ≤ 1 / 4 + K ^ 2
  · have h' : lam ≤ 1 / 4 + K' ^ 2 := by nlinarith
    rw [if_pos h, if_pos h']
  · rw [if_neg h]
    split_ifs
    · have := specWeightConst_pos
      have : 0 ≤ specKappa lam := Real.sqrt_nonneg _
      positivity
    · exact le_rfl

theorem sieveLHS_mono (L Q N : ℕ) {K K' : ℝ} (hK : 0 ≤ K) (hKK : K ≤ K') (a : ℕ → ℂ) :
    sieveLHS L Q N K a ≤ sieveLHS L Q N K' a := by
  unfold sieveLHS
  refine add_le_add (ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal ?_) ?_
  · exact mul_le_mul_of_nonneg_right (sieveWeight_mono hK hKK _) (by positivity)
  · exact lintegral_mono_set (Icc_subset_Icc (by linarith) hKK)

/-! ## Real inequalities for the choice of `K₁` -/

theorem cube_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]

theorem sqrt_six_log_le {x η : ℝ} (hx : 0 ≤ x) (hη : 0 < η) :
    Real.sqrt (6 * Real.log (1 + x)) ≤ Real.sqrt (3 / η) * (1 + x) ^ η := by
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ 1 + x) (by positivity : 0 < 2 * η)
  have h2 : 6 * Real.log (1 + x) ≤ (Real.sqrt (3 / η) * (1 + x) ^ η) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    have : (6 : ℝ) * ((1 + x) ^ (2 * η) / (2 * η)) = 3 / η * (1 + x) ^ (η * ((2 : ℕ) : ℝ)) := by
      rw [show η * ((2 : ℕ) : ℝ) = 2 * η by push_cast; ring]
      field_simp
      ring
    linarith
  calc Real.sqrt (6 * Real.log (1 + x)) ≤ Real.sqrt ((Real.sqrt (3 / η) * (1 + x) ^ η) ^ 2) :=
        Real.sqrt_le_sqrt h2
    _ = _ := Real.sqrt_sq (by positivity)

theorem exp_neg_half_le {x K₁ : ℝ} (hx : 0 ≤ x) (h : 6 * Real.log (1 + x) ≤ K₁ ^ 2) :
    Real.exp (-K₁ ^ 2 / 2) ≤ ((1 + x) ^ 3)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  rw [← Real.exp_log (pow_pos h1 3), ← Real.exp_neg, Real.log_pow]
  refine Real.exp_le_exp.2 ?_
  push_cast
  linarith

theorem tail_le_real {N Q K₁ P₃ Z₂ Z₃ : ℝ} (hN : 0 ≤ N) (hQ : 0 < Q) (hK₁ : 1 ≤ K₁)
    (hP₃ : 0 ≤ P₃) (hZ₂ : 0 ≤ Z₂) (hZ₃ : 0 ≤ Z₃) (hlog : 6 * Real.log (1 + N / Q) ≤ K₁ ^ 2) :
    P₃ * K₁ ^ 2 * Real.exp (-K₁ ^ 2 / 2) * (N ^ 2 * (Q ^ (-(2 : ℝ)) * Z₂) +
      N ^ 3 * (Q ^ (-(3 : ℝ)) * Z₃)) ≤ P₃ * (Z₂ + Z₃) * K₁ ^ 3 := by
  set x := N / Q
  have hx : 0 ≤ x := by positivity
  have hE := exp_neg_half_le hx hlog
  have hQ2 : N ^ 2 * Q ^ (-(2 : ℝ)) = x ^ 2 := by
    rw [Real.rpow_neg hQ.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow]
    ring
  have hQ3 : N ^ 3 * Q ^ (-(3 : ℝ)) = x ^ 3 := by
    rw [Real.rpow_neg hQ.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow]
    ring
  have e : N ^ 2 * (Q ^ (-(2 : ℝ)) * Z₂) + N ^ 3 * (Q ^ (-(3 : ℝ)) * Z₃) = x ^ 2 * Z₂ + x ^ 3 * Z₃ := by
    rw [← hQ2, ← hQ3]; ring
  rw [e]
  have hx2 : x ^ 2 ≤ (1 + x) ^ 3 := by nlinarith [sq_nonneg x]
  have hx3 : x ^ 3 ≤ (1 + x) ^ 3 := pow_le_pow_left₀ hx (by linarith) 3
  have h2 : Real.exp (-K₁ ^ 2 / 2) * (x ^ 2 * Z₂ + x ^ 3 * Z₃) ≤ Z₂ + Z₃ := by
    have h1x : (0 : ℝ) < (1 + x) ^ 3 := by positivity
    calc Real.exp (-K₁ ^ 2 / 2) * (x ^ 2 * Z₂ + x ^ 3 * Z₃)
        ≤ ((1 + x) ^ 3)⁻¹ * ((1 + x) ^ 3 * Z₂ + (1 + x) ^ 3 * Z₃) := by gcongr
      _ = Z₂ + Z₃ := by field_simp
  have hKK : K₁ ^ 2 ≤ K₁ ^ 3 := pow_le_pow_right₀ hK₁ (by norm_num)
  calc P₃ * K₁ ^ 2 * Real.exp (-K₁ ^ 2 / 2) * (x ^ 2 * Z₂ + x ^ 3 * Z₃)
      = P₃ * K₁ ^ 2 * (Real.exp (-K₁ ^ 2 / 2) * (x ^ 2 * Z₂ + x ^ 3 * Z₃)) := by ring
    _ ≤ P₃ * K₁ ^ 2 * (Z₂ + Z₃) := by gcongr
    _ ≤ P₃ * K₁ ^ 3 * (Z₂ + Z₃) := by gcongr
    _ = _ := by ring

theorem y_cube_le {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (6 * Real.log (1 + x)) ^ 3 ≤ 27 * (1 + x) := by
  have h1 := sqrt_six_log_le hx (by norm_num : (0 : ℝ) < 1 / 3)
  have h2 : Real.sqrt (3 / (1 / 3)) = 3 := by
    rw [show (3 : ℝ) / (1 / 3) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h2] at h1
  have h3 : ((1 + x) ^ (1 / 3 : ℝ)) ^ 3 = 1 + x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  calc Real.sqrt (6 * Real.log (1 + x)) ^ 3 ≤ (3 * (1 + x) ^ (1 / 3 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 3
    _ = 27 * (1 + x) := by rw [mul_pow, h3]; norm_num

theorem y_le_rpow {N Q δ : ℝ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.sqrt (6 * Real.log (1 + N / Q)) ≤ 2 * Real.sqrt (3 / δ) * N ^ δ := by
  have hQ0 : 0 < Q := by linarith
  have hN0 : 0 < N := by linarith
  have hx : 0 ≤ N / Q := by positivity
  have h1 := sqrt_six_log_le hx hδ
  have hx1 : 1 + N / Q ≤ 2 * N := by
    have : N / Q ≤ N := div_le_self hN0.le hQ
    linarith
  have h2 : (1 + N / Q) ^ δ ≤ 2 * N ^ δ := by
    calc (1 + N / Q) ^ δ ≤ (2 * N) ^ δ := Real.rpow_le_rpow (by linarith) hx1 hδ.le
      _ = 2 ^ δ * N ^ δ := Real.mul_rpow (by norm_num) hN0.le
      _ ≤ 2 * N ^ δ := by
          have : (2 : ℝ) ^ δ ≤ 2 := by
            calc (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
              _ = 2 := Real.rpow_one 2
          have : 0 ≤ N ^ δ := by positivity
          nlinarith
  calc Real.sqrt (6 * Real.log (1 + N / Q)) ≤ Real.sqrt (3 / δ) * (1 + N / Q) ^ δ := h1
    _ ≤ Real.sqrt (3 / δ) * (2 * N ^ δ) := by gcongr
    _ = _ := by ring

theorem main_le_real {K N Q δ P Z y : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hδ : 0 < δ)
    (hP : 0 ≤ P) (hZ : 0 ≤ Z) (hy : y ≤ 2 * Real.sqrt (3 / δ) * N ^ δ) :
    P * (K + y) * N ^ (1 + 2 * δ) * (Q ^ (-(1 + δ / 2)) * Z) ≤
      P * Z * (1 + 2 * Real.sqrt (3 / δ)) * (K * N ^ (1 + 3 * δ) / Q) := by
  have hQ0 : 0 < Q := by linarith
  have hN0 : 0 < N := by linarith
  have hNδ : 1 ≤ N ^ δ := Real.one_le_rpow hN hδ.le
  have hs : 0 ≤ Real.sqrt (3 / δ) := Real.sqrt_nonneg _
  have hQs : Q ^ (-(1 + δ / 2)) ≤ Q⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  have h1 : K + y ≤ (1 + 2 * Real.sqrt (3 / δ)) * K * N ^ δ := by
    have ha : K ≤ K * N ^ δ := le_mul_of_one_le_right (by linarith) hNδ
    have hb : 2 * Real.sqrt (3 / δ) * N ^ δ ≤ 2 * Real.sqrt (3 / δ) * N ^ δ * K :=
      le_mul_of_one_le_right (by positivity) hK
    calc K + y ≤ K * N ^ δ + 2 * Real.sqrt (3 / δ) * N ^ δ * K := add_le_add ha (hy.trans hb)
      _ = _ := by ring
  have e : N ^ (1 + 3 * δ) = N ^ (1 + 2 * δ) * N ^ δ := by
    rw [← Real.rpow_add hN0]; ring_nf
  calc P * (K + y) * N ^ (1 + 2 * δ) * (Q ^ (-(1 + δ / 2)) * Z)
      = P * Z * ((K + y) * N ^ (1 + 2 * δ)) * Q ^ (-(1 + δ / 2)) := by ring
    _ ≤ P * Z * (((1 + 2 * Real.sqrt (3 / δ)) * K * N ^ δ) * N ^ (1 + 2 * δ)) * Q⁻¹ := by
        gcongr
    _ = _ := by rw [e]; ring

/-- The choice `K₁ = K + √(6 log(1 + N/Q))` in real numbers. -/
theorem cubic_bound_real {K N Q δ P P₃ Z Z₂ Z₃ : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hP : 0 ≤ P) (hP₃ : 0 ≤ P₃) (hZ : 0 ≤ Z) (hZ₂ : 0 ≤ Z₂)
    (hZ₃ : 0 ≤ Z₃) :
    Real.sqrt Real.pi / 2 * (K + Real.sqrt (6 * Real.log (1 + N / Q))) ^ 3 +
      (P * (K + Real.sqrt (6 * Real.log (1 + N / Q))) * N ^ (1 + 2 * δ) * (Q ^ (-(1 + δ / 2)) * Z) +
        P₃ * (K + Real.sqrt (6 * Real.log (1 + N / Q))) ^ 2 *
          Real.exp (-(K + Real.sqrt (6 * Real.log (1 + N / Q))) ^ 2 / 2) *
            (N ^ 2 * (Q ^ (-(2 : ℝ)) * Z₂) + N ^ 3 * (Q ^ (-(3 : ℝ)) * Z₃))) ≤
      (220 * (Real.sqrt Real.pi / 2 + P₃ * (Z₂ + Z₃)) + P * Z * (1 + 2 * Real.sqrt (3 / δ))) *
        (K ^ 3 + K * N ^ (1 + 3 * δ) / Q) := by
  have hQ0 : 0 < Q := by linarith
  have hN0 : 0 < N := by linarith
  have hx : 0 ≤ N / Q := by positivity
  set y := Real.sqrt (6 * Real.log (1 + N / Q))
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hK₁ : 1 ≤ K + y := by linarith
  have hlog : 6 * Real.log (1 + N / Q) ≤ (K + y) ^ 2 := by
    have h1 : 0 ≤ 6 * Real.log (1 + N / Q) := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + N / Q); linarith
    have h2 : y ^ 2 = 6 * Real.log (1 + N / Q) := Real.sq_sqrt h1
    nlinarith
  have htail := tail_le_real hN0.le hQ0 hK₁ hP₃ hZ₂ hZ₃ hlog
  have hmain := main_le_real hK hN hQ hδ hP hZ (y_le_rpow hN hQ hδ hδ1)
  set M := K * N ^ (1 + 3 * δ) / Q
  have hM : 0 ≤ M := by positivity
  have hxM : 1 + N / Q ≤ K ^ 3 + M := by
    have h1 : (1 : ℝ) ≤ K ^ 3 := one_le_pow₀ hK
    have h2 : N / Q ≤ M := by
      simp only [M]
      rw [div_le_div_iff_of_pos_right hQ0]
      have h3 : N ≤ N ^ (1 + 3 * δ) := Real.self_le_rpow_of_one_le hN (by linarith)
      calc N ≤ N ^ (1 + 3 * δ) := h3
        _ ≤ K * N ^ (1 + 3 * δ) := le_mul_of_one_le_left (by positivity) hK
    linarith
  have hK₁3 : (K + y) ^ 3 ≤ 4 * (K ^ 3 + 27 * (K ^ 3 + M)) := by
    have h1 := cube_add_le (by linarith : (0 : ℝ) ≤ K) hy
    have h2 := y_cube_le hx
    linarith
  set c₁ := Real.sqrt Real.pi / 2 + P₃ * (Z₂ + Z₃)
  have hc₁ : 0 ≤ c₁ := by positivity
  have hstep : Real.sqrt Real.pi / 2 * (K + y) ^ 3 + (P * (K + y) * N ^ (1 + 2 * δ) * (Q ^ (-(1 + δ / 2)) * Z) +
      P₃ * (K + y) ^ 2 * Real.exp (-(K + y) ^ 2 / 2) *
        (N ^ 2 * (Q ^ (-(2 : ℝ)) * Z₂) + N ^ 3 * (Q ^ (-(3 : ℝ)) * Z₃))) ≤
      c₁ * (K + y) ^ 3 + P * Z * (1 + 2 * Real.sqrt (3 / δ)) * M := by
    have e : c₁ * (K + y) ^ 3 = Real.sqrt Real.pi / 2 * (K + y) ^ 3 + P₃ * (Z₂ + Z₃) * (K + y) ^ 3 := by
      simp only [c₁]; ring
    linarith
  have h3 : 0 ≤ P * Z * (1 + 2 * Real.sqrt (3 / δ)) := by positivity
  calc _ ≤ c₁ * (K + y) ^ 3 + P * Z * (1 + 2 * Real.sqrt (3 / δ)) * M := hstep
    _ ≤ c₁ * (4 * (K ^ 3 + 27 * (K ^ 3 + M))) + P * Z * (1 + 2 * Real.sqrt (3 / δ)) * M := by gcongr
    _ ≤ (220 * c₁ + P * Z * (1 + 2 * Real.sqrt (3 / δ))) * (K ^ 3 + M) := by
        have hK3 : 0 ≤ K ^ 3 := by positivity
        have e : (220 * c₁ + P * Z * (1 + 2 * Real.sqrt (3 / δ))) * (K ^ 3 + M) =
            c₁ * (4 * (K ^ 3 + 27 * (K ^ 3 + M))) + P * Z * (1 + 2 * Real.sqrt (3 / δ)) * M +
              (108 * c₁ * K ^ 3 + 112 * c₁ * M + P * Z * (1 + 2 * Real.sqrt (3 / δ)) * K ^ 3) := by ring
        rw [e]
        have : 0 ≤ 108 * c₁ * K ^ 3 + 112 * c₁ * M + P * Z * (1 + 2 * Real.sqrt (3 / δ)) * K ^ 3 := by
          positivity
        linarith

open Classical in
/-- **The large sieve for `Γ₀(Q)` with the cubic weight**: `𝓛_K(a) ≤ C |H| (K³ + K N^{1+3δ}/Q) Σ|a|²`. -/
theorem large_sieve_gamma0_cubic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L Q : ℕ}, 2 ≤ L → Q ∣ L + 1 → ∀ (N : ℕ), 1 ≤ N → ∀ (K : ℝ), 1 ≤ K →
      ∀ (a : ℕ → ℂ), sieveLHS L Q N K a ≤
        ENNReal.ofReal (C * (Fintype.card (gamma0Deck L Q) : ℝ) *
          (K ^ 3 + K * (N : ℝ) ^ (1 + 3 * δ) / Q) * ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2) := by
  obtain ⟨P, P₃, hP, hP₃, hlevel⟩ := large_sieve_gamma0_level hδ hδ1
  have hZ := intZeta_nonneg (1 + δ / 2)
  have hZ₂ := intZeta_nonneg 2
  have hZ₃ := intZeta_nonneg 3
  set C' := 220 * (Real.sqrt Real.pi / 2 + P₃ * (intZeta 2 + intZeta 3)) +
    P * intZeta (1 + δ / 2) * (1 + 2 * Real.sqrt (3 / δ))
  have hC' : 0 ≤ C' := by positivity
  refine ⟨2 * C', by positivity, fun {L Q} hL hQ N hN K hK a => ?_⟩
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.pos_of_dvd_of_pos hQ (Nat.succ_pos L)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set y := Real.sqrt (6 * Real.log (1 + (N : ℝ) / Q))
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  set K₁ := K + y
  have hK₁ : 1 ≤ K₁ := by linarith
  have hA : 0 ≤ ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
  have hH : (0 : ℝ) ≤ (Fintype.card (gamma0Deck L Q) : ℝ) := Nat.cast_nonneg _
  refine (sieveLHS_mono L Q N (by linarith) (by linarith : K ≤ K₁) a).trans ?_
  refine (hlevel hL hQ N hN K₁ hK₁ a).trans (ENNReal.ofReal_le_ofReal ?_)
  have hb := cubic_bound_real hK hN1 hQ1 hδ (by linarith) hP hP₃ hZ hZ₂ hZ₃
  have hb' : 0 ≤ 2 * (Fintype.card (gamma0Deck L Q) : ℝ) := by positivity
  calc 2 * (Fintype.card (gamma0Deck L Q) : ℝ) * (Real.sqrt Real.pi / 2 * K₁ ^ 3 +
        (P * K₁ * (N : ℝ) ^ (1 + 2 * δ) * ((Q : ℝ) ^ (-(1 + δ / 2)) * intZeta (1 + δ / 2)) +
          P₃ * K₁ ^ 2 * Real.exp (-K₁ ^ 2 / 2) *
            ((N : ℝ) ^ 2 * ((Q : ℝ) ^ (-(2 : ℝ)) * intZeta 2) +
              (N : ℝ) ^ 3 * ((Q : ℝ) ^ (-(3 : ℝ)) * intZeta 3)))) *
        ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2
      ≤ 2 * (Fintype.card (gamma0Deck L Q) : ℝ) * (C' * (K ^ 3 + K * (N : ℝ) ^ (1 + 3 * δ) / Q)) *
        ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2 := by gcongr
    _ = _ := by ring

/-! ## Dyadic summation -/

theorem specKappa_le_iff {lam T : ℝ} (hT : 0 ≤ T) : specKappa lam ≤ T ↔ lam ≤ 1 / 4 + T ^ 2 := by
  rw [specKappa, Real.sqrt_le_left hT, max_le_iff]
  constructor
  · rintro ⟨h, -⟩; linarith
  · intro h; exact ⟨by linarith, sq_nonneg T⟩

/-- The number of dyadic levels below `K`. -/
def dyadicLevels (K : ℝ) : ℕ := Nat.log 2 ⌊K⌋₊

theorem two_pow_dyadicLevels_le {K : ℝ} (hK : 1 ≤ K) : (2 : ℝ) ^ dyadicLevels K ≤ K := by
  have h1 : ⌊K⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊K⌋₊ := Nat.le_floor (by exact_mod_cast hK)
    omega
  have h2 := Nat.pow_log_le_self 2 h1
  calc (2 : ℝ) ^ dyadicLevels K = ((2 ^ dyadicLevels K : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (⌊K⌋₊ : ℝ) := by exact_mod_cast h2
    _ ≤ K := Nat.floor_le (by linarith)

/-- **The dyadic covering of `[0, K]`**: `[κ ≤ K] ≤ Σ_{i ≤ I} (2^{i+1}/K)(κ+1)[κ ≤ K/2^i] + (κ+1)[κ ≤ 1]`. -/
theorem dyadic_indicator_le {κ K : ℝ} (hκ : 0 ≤ κ) (hK : 1 ≤ K) :
    (if κ ≤ K then (1 : ℝ) else 0) ≤
      ∑ i ∈ Finset.range (dyadicLevels K + 1),
        (2 * 2 ^ i / K) * ((κ + 1) * (if κ ≤ K / 2 ^ i then 1 else 0)) +
      (κ + 1) * (if κ ≤ 1 then 1 else 0) := by
  have hK0 : 0 < K := by linarith
  have hterm : ∀ i ∈ Finset.range (dyadicLevels K + 1),
      0 ≤ (2 * 2 ^ i / K) * ((κ + 1) * (if κ ≤ K / 2 ^ i then (1 : ℝ) else 0)) := fun i _ => by
    split_ifs <;> positivity
  have hsum := Finset.sum_nonneg hterm
  by_cases hκK : κ ≤ K
  · rw [if_pos hκK]
    by_cases hκ1 : κ ≤ 1
    · rw [if_pos hκ1]; linarith
    · push Not at hκ1
      rw [if_neg (not_le.2 hκ1), mul_zero, add_zero]
      set n := ⌊K / κ⌋₊
      have hκ0 : 0 < κ := by linarith
      have hKκ : 1 ≤ K / κ := by rw [le_div_iff₀ hκ0]; linarith
      have hn0 : n ≠ 0 := by
        have : 1 ≤ n := Nat.le_floor (by exact_mod_cast hKκ)
        omega
      set i := Nat.log 2 n
      have hi1 : (2 : ℝ) ^ i ≤ K / κ := by
        calc (2 : ℝ) ^ i = ((2 ^ i : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ (n : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hn0
          _ ≤ K / κ := Nat.floor_le (by positivity)
      have hi2 : K / κ < (2 : ℝ) ^ (i + 1) := by
        have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
        have h' : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ (i + 1) : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at h'
        linarith [Nat.lt_floor_add_one (K / κ)]
      have hiI : i ∈ Finset.range (dyadicLevels K + 1) := by
        rw [Finset.mem_range, Nat.lt_succ_iff]
        refine Nat.log_mono_right (Nat.floor_le_floor ?_)
        rw [div_le_iff₀ hκ0]; nlinarith
      have hle : κ ≤ K / 2 ^ i := by
        rw [le_div_iff₀ (by positivity)]
        rw [le_div_iff₀ hκ0] at hi1
        linarith
      have hval : 1 ≤ (2 * 2 ^ i / K) * ((κ + 1) * (if κ ≤ K / 2 ^ i then (1 : ℝ) else 0)) := by
        rw [if_pos hle, mul_one]
        have h2 : K < 2 ^ (i + 1) * κ := by rwa [div_lt_iff₀ hκ0] at hi2
        rw [pow_succ] at h2
        rw [div_mul_eq_mul_div, le_div_iff₀ hK0]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) i]
      have := Finset.single_le_sum hterm hiI
      linarith
  · rw [if_neg hκK]
    have : 0 ≤ (κ + 1) * (if κ ≤ 1 then (1 : ℝ) else 0) := by split_ifs <;> positivity
    linarith

/-- The spectral side of DI Theorem 2:
`Σ_{λ_j ≤ ¼+K²} e^{−πκ_j}|Σ a_n ρ_j(n)|² + (4π)⁻¹ ∫_{−K}^{K} e^{−π|r|} Σ_i |Σ a_n η_i(r, n)|² dr`. -/
def sieveDILHS (L Q N : ℕ) (K : ℝ) (a : ℕ → ℂ) : ENNReal :=
  (∑' j : CuspEigenIndex L, ENNReal.ofReal ((if j.1 ≤ 1 / 4 + K ^ 2 then
      Real.exp (-(Real.pi * specKappa j.1)) else 0) *
      ‖∑ k ∈ Finset.Ioc N (N + N), a k * cuspCoeff j k (gamma0Vec L Q)‖ ^ 2)) +
    ∫⁻ r in Icc (-K) K, ENNReal.ofReal ((4 * Real.pi)⁻¹ * Real.exp (-(Real.pi * |r|)) *
        ∑ i, ‖∑ k ∈ Finset.Ioc N (N + N), a k * eisCoeff (1 / 2 + r * Complex.I) (gamma0Vec L Q)
          (cuspBasisVec L i) ((k : ℤ) * ((L + 1 : ℕ) : ℤ))‖ ^ 2)

theorem sieveWeight_eq {T : ℝ} (hT : 0 ≤ T) (lam : ℝ) :
    sieveWeight T lam = specWeightConst * (specKappa lam + 1) * Real.exp (-(Real.pi * specKappa lam)) *
      (if specKappa lam ≤ T then 1 else 0) := by
  unfold sieveWeight
  by_cases h : lam ≤ 1 / 4 + T ^ 2
  · rw [if_pos h, if_pos ((specKappa_le_iff hT).2 h), mul_one]
  · rw [if_neg h, if_neg (fun h' => h ((specKappa_le_iff hT).1 h')), mul_zero]

/-- The real inequality behind the dyadic decomposition, for one spectral weight. -/
theorem dyadic_weight_le {κ K X : ℝ} (hκ : 0 ≤ κ) (hK : 1 ≤ K) (hX : 0 ≤ X) :
    (if κ ≤ K then Real.exp (-(Real.pi * κ)) else 0) * X ≤
      ∑ i ∈ Finset.range (dyadicLevels K + 1), (2 * 2 ^ i / (specWeightConst * K)) *
        (specWeightConst * (κ + 1) * Real.exp (-(Real.pi * κ)) * (if κ ≤ K / 2 ^ i then 1 else 0) * X) +
      specWeightConst⁻¹ * (specWeightConst * (κ + 1) * Real.exp (-(Real.pi * κ)) *
        (if κ ≤ 1 then 1 else 0) * X) := by
  have hc := specWeightConst_pos
  have hE : 0 ≤ Real.exp (-(Real.pi * κ)) * X := by positivity
  have h := mul_le_mul_of_nonneg_right (dyadic_indicator_le hκ hK) hE
  have e1 : (if κ ≤ K then Real.exp (-(Real.pi * κ)) else 0) * X =
      (if κ ≤ K then (1 : ℝ) else 0) * (Real.exp (-(Real.pi * κ)) * X) := by
    split_ifs <;> ring
  rw [e1]
  refine h.trans (le_of_eq ?_)
  rw [add_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  · field_simp

theorem aemeasurable_eisWeight (L Q N : ℕ) (a : ℕ → ℂ) (c : ℝ → ℝ) (hc : Continuous c) :
    AEMeasurable (fun r : ℝ => ENNReal.ofReal (c r *
      ∑ i, ‖∑ k ∈ Finset.Ioc N (N + N), a k * eisCoeff (1 / 2 + r * Complex.I) (gamma0Vec L Q)
        (cuspBasisVec L i) ((k : ℤ) * ((L + 1 : ℕ) : ℤ))‖ ^ 2)) volume := by
  refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
  refine hc.aemeasurable.mul ?_
  refine Finset.aemeasurable_fun_sum _ fun i _ => ?_
  refine (AEMeasurable.pow_const ?_ 2)
  refine (Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
    aestronglyMeasurable_const.mul (aestronglyMeasurable_eisCoeff_line _ _ _)).norm.aemeasurable

/-- **Dyadic summation**: `𝓛^{DI}_K ≤ Σ_{i ≤ I} (2^{i+1}/(c₀K)) 𝓛_{K/2^i} + c₀⁻¹ 𝓛_1`. -/
theorem sieveDILHS_le (L Q N : ℕ) {K : ℝ} (hK : 1 ≤ K) (a : ℕ → ℂ) :
    sieveDILHS L Q N K a ≤
      ∑ i ∈ Finset.range (dyadicLevels K + 1),
        ENNReal.ofReal (2 * 2 ^ i / (specWeightConst * K)) * sieveLHS L Q N (K / 2 ^ i) a +
      ENNReal.ofReal specWeightConst⁻¹ * sieveLHS L Q N 1 a := by
  have hc := specWeightConst_pos
  set R := Finset.range (dyadicLevels K + 1)
  set X : CuspEigenIndex L → ℝ := fun j =>
    ‖∑ k ∈ Finset.Ioc N (N + N), a k * cuspCoeff j k (gamma0Vec L Q)‖ ^ 2
  set Y : ℝ → ℝ := fun r => ∑ i, ‖∑ k ∈ Finset.Ioc N (N + N), a k *
    eisCoeff (1 / 2 + r * Complex.I) (gamma0Vec L Q) (cuspBasisVec L i) ((k : ℤ) * ((L + 1 : ℕ) : ℤ))‖ ^ 2
  have hX : ∀ j, 0 ≤ X j := fun j => by positivity
  have hY : ∀ r, 0 ≤ Y r := fun r => Finset.sum_nonneg fun i _ => by positivity
  have hKi : ∀ i, 0 ≤ K / 2 ^ i := fun i => by positivity
  -- the cusp part
  have hcusp : (∑' j : CuspEigenIndex L, ENNReal.ofReal ((if j.1 ≤ 1 / 4 + K ^ 2 then
        Real.exp (-(Real.pi * specKappa j.1)) else 0) * X j)) ≤
      ∑ i ∈ R, ENNReal.ofReal (2 * 2 ^ i / (specWeightConst * K)) *
          ∑' j : CuspEigenIndex L, ENNReal.ofReal (sieveWeight (K / 2 ^ i) j.1 * X j) +
        ENNReal.ofReal specWeightConst⁻¹ *
          ∑' j : CuspEigenIndex L, ENNReal.ofReal (sieveWeight 1 j.1 * X j) := by
    have hpt : ∀ j : CuspEigenIndex L, ENNReal.ofReal ((if j.1 ≤ 1 / 4 + K ^ 2 then
        Real.exp (-(Real.pi * specKappa j.1)) else 0) * X j) ≤
        ∑ i ∈ R, ENNReal.ofReal (2 * 2 ^ i / (specWeightConst * K)) *
          ENNReal.ofReal (sieveWeight (K / 2 ^ i) j.1 * X j) +
        ENNReal.ofReal specWeightConst⁻¹ * ENNReal.ofReal (sieveWeight 1 j.1 * X j) := by
      intro j
      have hκ : 0 ≤ specKappa j.1 := Real.sqrt_nonneg _
      have h := dyadic_weight_le hκ hK (hX j)
      have e : (if j.1 ≤ 1 / 4 + K ^ 2 then Real.exp (-(Real.pi * specKappa j.1)) else 0) =
          (if specKappa j.1 ≤ K then Real.exp (-(Real.pi * specKappa j.1)) else 0) := by
        by_cases h1 : j.1 ≤ 1 / 4 + K ^ 2
        · rw [if_pos h1, if_pos ((specKappa_le_iff (by linarith)).2 h1)]
        · rw [if_neg h1, if_neg (fun h' => h1 ((specKappa_le_iff (by linarith)).1 h'))]
      rw [e]
      refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => by positivity) (by positivity),
        ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_mul (by positivity), sieveWeight_eq (hKi i)]
      · rw [ENNReal.ofReal_mul (by positivity), sieveWeight_eq zero_le_one]
    refine (ENNReal.tsum_le_tsum hpt).trans (le_of_eq ?_)
    rw [ENNReal.tsum_add, Summable.tsum_finsetSum fun i _ => ENNReal.summable]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.tsum_mul_left]
    · rw [ENNReal.tsum_mul_left]
  -- the Eisenstein part
  set W : ℝ → ℝ := fun r => (4 * Real.pi)⁻¹ * (specWeightConst * (|r| + 1) * Real.exp (-(Real.pi * |r|))) * Y r
  have hW : ∀ r, 0 ≤ W r := fun r => by have := hY r; positivity
  have hWm : AEMeasurable (fun r => ENNReal.ofReal (W r)) volume := by
    have := aemeasurable_eisWeight L Q N a
      (fun r => (4 * Real.pi)⁻¹ * (specWeightConst * (|r| + 1) * Real.exp (-(Real.pi * |r|))))
      (by fun_prop)
    exact this
  have hind : ∀ T : ℝ, ∀ r, (Icc (-T) T).indicator (fun r => ENNReal.ofReal (W r)) r =
      ENNReal.ofReal (W r * (if |r| ≤ T then 1 else 0)) := fun T r => by
    by_cases h : |r| ≤ T
    · rw [Set.indicator_of_mem (Set.mem_Icc.2 (abs_le.1 h)), if_pos h, mul_one]
    · rw [Set.indicator_of_notMem (fun h' => h (abs_le.2 (Set.mem_Icc.1 h'))), if_neg h, mul_zero,
        ENNReal.ofReal_zero]
  have heis : ∫⁻ r in Icc (-K) K, ENNReal.ofReal ((4 * Real.pi)⁻¹ * Real.exp (-(Real.pi * |r|)) * Y r) ≤
      ∑ i ∈ R, ENNReal.ofReal (2 * 2 ^ i / (specWeightConst * K)) *
          (∫⁻ r in Icc (-(K / 2 ^ i)) (K / 2 ^ i), ENNReal.ofReal (W r)) +
        ENNReal.ofReal specWeightConst⁻¹ * (∫⁻ r in Icc (-1) 1, ENNReal.ofReal (W r)) := by
    have hpt : ∀ r, (Icc (-K) K).indicator
        (fun r => ENNReal.ofReal ((4 * Real.pi)⁻¹ * Real.exp (-(Real.pi * |r|)) * Y r)) r ≤
        ∑ i ∈ R, ENNReal.ofReal (2 * 2 ^ i / (specWeightConst * K)) *
          (Icc (-(K / 2 ^ i)) (K / 2 ^ i)).indicator (fun r => ENNReal.ofReal (W r)) r +
        ENNReal.ofReal specWeightConst⁻¹ * (Icc (-1) 1).indicator (fun r => ENNReal.ofReal (W r)) r := by
      intro r
      have h := dyadic_weight_le (abs_nonneg r) hK
        (by have := hY r; positivity : 0 ≤ (4 * Real.pi)⁻¹ * Y r)
      have e0 : (Icc (-K) K).indicator
          (fun r => ENNReal.ofReal ((4 * Real.pi)⁻¹ * Real.exp (-(Real.pi * |r|)) * Y r)) r =
          ENNReal.ofReal ((if |r| ≤ K then Real.exp (-(Real.pi * |r|)) else 0) * ((4 * Real.pi)⁻¹ * Y r)) := by
        by_cases h1 : |r| ≤ K
        · rw [Set.indicator_of_mem (Set.mem_Icc.2 (abs_le.1 h1)), if_pos h1]; ring_nf
        · rw [Set.indicator_of_notMem (fun h' => h1 (abs_le.2 (Set.mem_Icc.1 h'))), if_neg h1, zero_mul,
            ENNReal.ofReal_zero]
      rw [e0]
      simp only [hind]
      refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => by positivity) (by positivity),
        ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [W]
        ring
      · rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [W]
        ring
    rw [← lintegral_indicator measurableSet_Icc]
    refine (lintegral_mono hpt).trans (le_of_eq ?_)
    rw [lintegral_add_left' (Finset.aemeasurable_fun_sum _ fun i _ =>
        ((hWm.indicator measurableSet_Icc).const_mul _)),
      lintegral_finsetSum' _ fun i _ => (hWm.indicator measurableSet_Icc).const_mul _]
    have e1 : ∀ i ∈ R, ∫⁻ x, ENNReal.ofReal (2 * 2 ^ i / (specWeightConst * K)) *
        (Icc (-(K / 2 ^ i)) (K / 2 ^ i)).indicator (fun r => ENNReal.ofReal (W r)) x =
        ENNReal.ofReal (2 * 2 ^ i / (specWeightConst * K)) *
          (∫⁻ r in Icc (-(K / 2 ^ i)) (K / 2 ^ i), ENNReal.ofReal (W r)) := fun i _ => by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Icc]
    have e2 : ∫⁻ x, ENNReal.ofReal specWeightConst⁻¹ *
        (Icc (-1) 1).indicator (fun r => ENNReal.ofReal (W r)) x =
        ENNReal.ofReal specWeightConst⁻¹ * (∫⁻ r in Icc (-1) 1, ENNReal.ofReal (W r)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Icc]
    rw [Finset.sum_congr rfl e1, e2]
  -- combine
  have htot := add_le_add hcusp heis
  unfold sieveDILHS sieveLHS
  refine htot.trans (le_of_eq ?_)
  simp only [X, W, Y, mul_add, Finset.sum_add_distrib]
  ring

/-! ## DI Theorem 2 -/

theorem sum_range_div_two_pow_sq_le (K : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (K / 2 ^ i) ^ 2 ≤ 4 / 3 * K ^ 2 := by
  have e : ∑ i ∈ Finset.range n, (K / 2 ^ i) ^ 2 = K ^ 2 * ∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow, ← pow_mul, one_div_pow, show (4 : ℝ) ^ i = (2 ^ 2) ^ i by norm_num, ← pow_mul]
    field_simp
    ring
  rw [e]
  have hg : ∑ i ∈ Finset.range n, (1 / 4 : ℝ) ^ i ≤ 4 / 3 := by
    rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
    have : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    linarith
  have := sq_nonneg K
  nlinarith

theorem dyadicLevels_le_log {K : ℝ} (hK : 1 ≤ K) : (dyadicLevels K : ℝ) ≤ 2 * Real.log K := by
  have h1 := two_pow_dyadicLevels_le hK
  have h2 : (dyadicLevels K : ℝ) * Real.log 2 ≤ Real.log K := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have h3 := Real.log_two_gt_d9
  have h4 : 0 ≤ (dyadicLevels K : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The logarithmic number of levels is absorbed: `(2I + 3) N^{1+3δ}/Q ≤ 19K² + (3 + 4/δ) N^{1+4δ}/Q`. -/
theorem levels_term_le {K N Q δ : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    (2 * (dyadicLevels K : ℝ) + 3) * (N ^ (1 + 3 * δ) / Q) ≤
      19 * K ^ 2 + (3 + 4 / δ) * (N ^ (1 + 4 * δ) / Q) := by
  have hI := dyadicLevels_le_log hK
  have hQ0 : 0 < Q := by linarith
  have hN0 : 0 < N := by linarith
  have hM : 0 ≤ N ^ (1 + 3 * δ) / Q := by positivity
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  by_cases hKN : K ≤ N
  · -- `log K ≤ log N ≤ N^δ/δ`
    have h1 : Real.log K ≤ N ^ δ / δ :=
      (Real.log_le_log (by linarith) hKN).trans (Real.log_le_rpow_div hN0.le hδ)
    have hNδ : 1 ≤ N ^ δ := Real.one_le_rpow hN hδ.le
    have h2 : 2 * (dyadicLevels K : ℝ) + 3 ≤ (3 + 4 / δ) * N ^ δ := by
      have : 4 * (N ^ δ / δ) = 4 / δ * N ^ δ := by ring
      have h3 : 3 ≤ 3 * N ^ δ := by linarith
      nlinarith
    have e : N ^ (1 + 4 * δ) / Q = N ^ δ * (N ^ (1 + 3 * δ) / Q) := by
      rw [show 1 + 4 * δ = δ + (1 + 3 * δ) by ring, Real.rpow_add hN0]; ring
    have : 0 ≤ 19 * K ^ 2 := by positivity
    calc (2 * (dyadicLevels K : ℝ) + 3) * (N ^ (1 + 3 * δ) / Q)
        ≤ (3 + 4 / δ) * N ^ δ * (N ^ (1 + 3 * δ) / Q) := by gcongr
      _ = (3 + 4 / δ) * (N ^ (1 + 4 * δ) / Q) := by rw [e]; ring
      _ ≤ _ := by linarith
  · push Not at hKN
    have hK0 : 0 < K := by linarith
    -- `N^{1+3δ}/Q ≤ K^{7/4}` and `log K ≤ 4K^{1/4}`
    have h1 : N ^ (1 + 3 * δ) / Q ≤ K ^ (7 / 4 : ℝ) := by
      calc N ^ (1 + 3 * δ) / Q ≤ N ^ (1 + 3 * δ) := div_le_self (by positivity) hQ
        _ ≤ K ^ (1 + 3 * δ) := Real.rpow_le_rpow hN0.le hKN.le (by linarith)
        _ ≤ K ^ (7 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
    have h2 : Real.log K ≤ 4 * K ^ (1 / 4 : ℝ) := by
      have := Real.log_le_rpow_div hK0.le (by norm_num : (0 : ℝ) < 1 / 4)
      calc Real.log K ≤ K ^ (1 / 4 : ℝ) / (1 / 4) := this
        _ = 4 * K ^ (1 / 4 : ℝ) := by ring
    have hK14 : 1 ≤ K ^ (1 / 4 : ℝ) := Real.one_le_rpow hK (by norm_num)
    have h3 : 2 * (dyadicLevels K : ℝ) + 3 ≤ 19 * K ^ (1 / 4 : ℝ) := by nlinarith
    have h4 : K ^ (1 / 4 : ℝ) * K ^ (7 / 4 : ℝ) = K ^ 2 := by
      rw [← Real.rpow_add hK0]; norm_num
    have : 0 ≤ (3 + 4 / δ) * (N ^ (1 + 4 * δ) / Q) := by positivity
    calc (2 * (dyadicLevels K : ℝ) + 3) * (N ^ (1 + 3 * δ) / Q)
        ≤ 19 * K ^ (1 / 4 : ℝ) * K ^ (7 / 4 : ℝ) := by gcongr
      _ = 19 * K ^ 2 := by rw [mul_assoc, h4]
      _ ≤ _ := by linarith

open Classical in
/-- **DI Theorem 2 for `Γ₀(Q)` at the cusp `∞`.** For every `ε > 0` there is `C` with, for all
`Q ∣ L + 1`, `K ≥ 1`, `N ≥ 1` and coefficients `a` on `(N, 2N]`,

`Σ_{λ_j ≤ ¼+K²} e^{−πκ_j} |Σ a_n ρ_j(n)|² + (4π)⁻¹ ∫_{−K}^{K} e^{−π|r|} Σ_i |Σ a_n η_i(r, n)|² dr
  ≤ C |H| (K² + N^{1+ε}/Q) Σ |a_n|²`. -/
theorem large_sieve_gamma0 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L Q : ℕ}, 2 ≤ L → Q ∣ L + 1 → ∀ (N : ℕ), 1 ≤ N → ∀ (K : ℝ), 1 ≤ K →
      ∀ (a : ℕ → ℂ), sieveDILHS L Q N K a ≤
        ENNReal.ofReal (C * (Fintype.card (gamma0Deck L Q) : ℝ) *
          (K ^ 2 + (N : ℝ) ^ (1 + ε) / Q) * ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2) := by
  set δ := min ε 1 / 4
  have hδ : 0 < δ := by simp only [δ]; positivity
  have hδ1 : δ ≤ 1 / 4 := by simp only [δ]; have := min_le_right ε 1; linarith
  have hδε : 4 * δ ≤ ε := by simp only [δ]; have := min_le_left ε 1; linarith
  obtain ⟨C₁, hC₁, hcubic⟩ := large_sieve_gamma0_cubic hδ hδ1
  have hc := specWeightConst_pos
  set C := C₁ / specWeightConst * (23 + (3 + 4 / δ))
  refine ⟨C, by positivity, fun {L Q} hL hQ N hN K hK a => ?_⟩
  set H := (Fintype.card (gamma0Deck L Q) : ℝ)
  set A := ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2
  have hH : 0 ≤ H := Nat.cast_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ => by positivity
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.pos_of_dvd_of_pos hQ (Nat.succ_pos L)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set M := (N : ℝ) ^ (1 + 3 * δ) / Q
  have hM : 0 ≤ M := by positivity
  set R := Finset.range (dyadicLevels K + 1)
  have hKi : ∀ i ∈ R, 1 ≤ K / 2 ^ i := fun i hi => by
    rw [Finset.mem_range, Nat.lt_succ_iff] at hi
    rw [le_div_iff₀ (by positivity), one_mul]
    calc (2 : ℝ) ^ i ≤ 2 ^ dyadicLevels K := pow_le_pow_right₀ (by norm_num) hi
      _ ≤ K := two_pow_dyadicLevels_le hK
  -- each level
  have hlev : ∀ i ∈ R, ENNReal.ofReal (2 * 2 ^ i / (specWeightConst * K)) *
      sieveLHS L Q N (K / 2 ^ i) a ≤
      ENNReal.ofReal (2 * C₁ / specWeightConst * H * ((K / 2 ^ i) ^ 2 + M) * A) := fun i hi => by
    have h := hcubic hL hQ N hN (K / 2 ^ i) (hKi i hi) a
    have h2 : ENNReal.ofReal (2 * 2 ^ i / (specWeightConst * K)) * sieveLHS L Q N (K / 2 ^ i) a ≤
        ENNReal.ofReal (2 * 2 ^ i / (specWeightConst * K)) * ENNReal.ofReal (C₁ *
          (Fintype.card (gamma0Deck L Q) : ℝ) * ((K / 2 ^ i) ^ 3 + K / 2 ^ i * (N : ℝ) ^ (1 + 3 * δ) / Q) *
            ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2) := by gcongr
    refine h2.trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hK0 : 0 < K := by linarith
    simp only [M, H, A]
    field_simp
  have hbase : ENNReal.ofReal specWeightConst⁻¹ * sieveLHS L Q N 1 a ≤
      ENNReal.ofReal (C₁ / specWeightConst * H * (1 + M) * A) := by
    have h := hcubic hL hQ N hN 1 le_rfl a
    have h2 : ENNReal.ofReal specWeightConst⁻¹ * sieveLHS L Q N 1 a ≤
        ENNReal.ofReal specWeightConst⁻¹ * ENNReal.ofReal (C₁ *
          (Fintype.card (gamma0Deck L Q) : ℝ) * ((1 : ℝ) ^ 3 + 1 * (N : ℝ) ^ (1 + 3 * δ) / Q) *
            ∑ k ∈ Finset.Ioc N (N + N), ‖a k‖ ^ 2) := by gcongr
    refine h2.trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    simp only [M, H, A]
    field_simp
  refine (sieveDILHS_le L Q N hK a).trans ?_
  refine (add_le_add (Finset.sum_le_sum hlev) hbase).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real arithmetic
  have hsum : ∑ i ∈ R, 2 * C₁ / specWeightConst * H * ((K / 2 ^ i) ^ 2 + M) * A =
      2 * C₁ / specWeightConst * H * A * (∑ i ∈ R, (K / 2 ^ i) ^ 2 + (dyadicLevels K + 1) * M) := by
    have e : ∀ i ∈ R, 2 * C₁ / specWeightConst * H * ((K / 2 ^ i) ^ 2 + M) * A =
        2 * C₁ / specWeightConst * H * A * (K / 2 ^ i) ^ 2 + 2 * C₁ / specWeightConst * H * A * M :=
      fun i _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  rw [hsum]
  have hgeo := sum_range_div_two_pow_sq_le K (dyadicLevels K + 1)
  have hlog := levels_term_le hK hN1 hQ1 hδ hδ1
  have hNε : (N : ℝ) ^ (1 + 4 * δ) / Q ≤ (N : ℝ) ^ (1 + ε) / Q :=
    div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by positivity)
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hD : 0 ≤ C₁ / specWeightConst * H * A := by positivity
  have hpos : 0 ≤ 3 + 4 / δ := by positivity
  have key : 2 * (∑ i ∈ R, (K / 2 ^ i) ^ 2 + ((dyadicLevels K : ℝ) + 1) * M) + (1 + M) ≤
      (23 + (3 + 4 / δ)) * (K ^ 2 + (N : ℝ) ^ (1 + ε) / Q) := by
    have e : 2 * (((dyadicLevels K : ℝ) + 1) * M) + M = (2 * (dyadicLevels K : ℝ) + 3) * M := by ring
    have h5 : (3 + 4 / δ) * ((N : ℝ) ^ (1 + 4 * δ) / Q) ≤ (3 + 4 / δ) * ((N : ℝ) ^ (1 + ε) / Q) :=
      mul_le_mul_of_nonneg_left hNε hpos
    have h6 : 0 ≤ (N : ℝ) ^ (1 + ε) / Q := by positivity
    nlinarith
  calc 2 * C₁ / specWeightConst * H * A * (∑ i ∈ R, (K / 2 ^ i) ^ 2 + ((dyadicLevels K : ℝ) + 1) * M) +
        C₁ / specWeightConst * H * (1 + M) * A
      = C₁ / specWeightConst * H * A *
          (2 * (∑ i ∈ R, (K / 2 ^ i) ^ 2 + ((dyadicLevels K : ℝ) + 1) * M) + (1 + M)) := by ring
    _ ≤ C₁ / specWeightConst * H * A * ((23 + (3 + 4 / δ)) * (K ^ 2 + (N : ℝ) ^ (1 + ε) / Q)) := by
        gcongr
    _ = _ := by simp only [C]; ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
