import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weak Maynard large values below the Route T threshold

Maynard optimises the prime-gap square moment to `x^(5/4+ε)`.  Route T needs only an exponent
strictly below `3/2`.  This changes the large-values geometry.

If a large-value set is simultaneously controlled by two complementary Montgomery estimates,

`R ≤ T M^(1-2α)` and `R ≤ T N^(1-2β)`,

with `x = MN` and `x^σ = M^α N^β`, geometric interpolation gives the stronger identity

`R ≤ T x^(1/2-σ)`.

Consequently the `R` alternative required for a gap-square exponent `1+ν` already holds throughout
`σ ≤ 1/2+ν`.  Taking, for example, `ν = 49/100` leaves only the thin band `σ > 99/100`; the
fourth-moment additive-energy count `R*` is not needed below that band.

Two further lemmas record the exact unbalanced interpolation and the corresponding sixth-moment
interpolation.  They isolate the remaining high-`σ` problem as a product-length condition, rather
than an `R*` problem.
-/

namespace RHTower.Sieve

/-- The complementary Montgomery coefficient energies multiply to the total energy. -/
theorem maynard_pair_energy_identity
    {M N x α β σ : ℝ} (hM : 0 < M) (hN : 0 < N) (hx : x = M * N)
    (hscale : x ^ σ = M ^ α * N ^ β) :
    M ^ (1 - 2 * α) * N ^ (1 - 2 * β) = x ^ (1 - 2 * σ) := by
  have hx0 : 0 < x := by rw [hx]; positivity
  have hlog : σ * Real.log x = α * Real.log M + β * Real.log N := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hM,
      Real.rpow_def_of_pos hN, ← Real.exp_add] at hscale
    have h := Real.exp_injective hscale
    linarith
  rw [Real.rpow_def_of_pos hM, Real.rpow_def_of_pos hN,
    Real.rpow_def_of_pos hx0, ← Real.exp_add]
  congr 1
  rw [hx, Real.log_mul hM.ne' hN.ne'] at hlog ⊢
  linarith

/-- **Balanced Montgomery interpolation.**  Two complementary second-moment estimates give
`R ≤ T x^(1/2-σ)`, hence every weaker target `T x^(1+ν-2σ)` when `σ ≤ 1/2+ν`. -/
theorem maynard_balanced_montgomery
    {R T x σ ν A B : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (hx : 1 ≤ x)
    (hA : 0 ≤ A) (hRA : R ≤ T * A) (hRB : R ≤ T * B)
    (hAB : A * B = x ^ (1 - 2 * σ)) (hσ : σ ≤ 1 / 2 + ν) :
    R ≤ T * x ^ (1 + ν - 2 * σ) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hTA : 0 ≤ T * A := mul_nonneg hT hA
  have hmul : R * R ≤ (T * A) * (T * B) :=
    mul_le_mul hRA hRB hR hTA
  have hhalfSq : (x ^ (1 / 2 - σ)) ^ 2 = x ^ (1 - 2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
    ring_nf
  have hsq : R ^ 2 ≤ (T * x ^ (1 / 2 - σ)) ^ 2 := by
    calc
      R ^ 2 = R * R := by ring
      _ ≤ (T * A) * (T * B) := hmul
      _ = T ^ 2 * (A * B) := by ring
      _ = T ^ 2 * x ^ (1 - 2 * σ) := by rw [hAB]
      _ = T ^ 2 * (x ^ (1 / 2 - σ)) ^ 2 := by rw [hhalfSq]
      _ = (T * x ^ (1 / 2 - σ)) ^ 2 := by ring
  have hmid0 : 0 ≤ T * x ^ (1 / 2 - σ) :=
    mul_nonneg hT (Real.rpow_nonneg hx0 _)
  have hmid : R ≤ T * x ^ (1 / 2 - σ) := by
    nlinarith
  have hexp : 1 / 2 - σ ≤ 1 + ν - 2 * σ := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hx hexp
  exact hmid.trans (mul_le_mul_of_nonneg_left hpow hT)

/-- Balanced interpolation stated directly for a complementary factorisation. -/
theorem maynard_balanced_montgomery_of_split
    {R T M N x α β σ ν : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hM : 0 < M) (hN : 0 < N) (hx : x = M * N) (hx1 : 1 ≤ x)
    (hscale : x ^ σ = M ^ α * N ^ β)
    (hRM : R ≤ T * M ^ (1 - 2 * α))
    (hRN : R ≤ T * N ^ (1 - 2 * β)) (hσ : σ ≤ 1 / 2 + ν) :
    R ≤ T * x ^ (1 + ν - 2 * σ) := by
  exact maynard_balanced_montgomery hR hT hx1
    (Real.rpow_nonneg hM.le _) hRM hRN
    (maynard_pair_energy_identity hM hN hx hscale) hσ

/-- At `ν = 49/100`, complementary Montgomery bounds close every level with `σ ≤ 99/100`. -/
theorem maynard_balanced_montgomery_routeT
    {R T M N x α β σ : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hM : 0 < M) (hN : 0 < N) (hx : x = M * N) (hx1 : 1 ≤ x)
    (hscale : x ^ σ = M ^ α * N ^ β)
    (hRM : R ≤ T * M ^ (1 - 2 * α))
    (hRN : R ≤ T * N ^ (1 - 2 * β)) (hσ : σ ≤ 99 / 100) :
    R ≤ T * x ^ (149 / 100 - 2 * σ) := by
  have hσ' : σ ≤ 1 / 2 + 49 / 100 := by norm_num at hσ ⊢; exact hσ
  simpa only [show (1 : ℝ) + 49 / 100 = 149 / 100 by norm_num] using
    maynard_balanced_montgomery_of_split hR hT hM hN hx hx1 hscale hRM hRN hσ'

/-- The complementary coefficient energies when both Montgomery estimates are length-dominated. -/
theorem maynard_pair_length_energy_identity
    {M N x α β σ : ℝ} (hM : 0 < M) (hN : 0 < N) (hx : x = M * N)
    (hscale : x ^ σ = M ^ α * N ^ β) :
    M ^ (2 - 2 * α) * N ^ (2 - 2 * β) = x ^ (2 - 2 * σ) := by
  have hx0 : 0 < x := by rw [hx]; positivity
  have hpair := maynard_pair_energy_identity hM hN hx hscale
  rw [show (2 : ℝ) - 2 * α = 1 + (1 - 2 * α) by ring,
    show (2 : ℝ) - 2 * β = 1 + (1 - 2 * β) by ring,
    Real.rpow_add hM, Real.rpow_add hN, Real.rpow_one, Real.rpow_one]
  calc
    M * M ^ (1 - 2 * α) * (N * N ^ (1 - 2 * β)) =
        (M * N) * (M ^ (1 - 2 * α) * N ^ (1 - 2 * β)) := by ring
    _ = x * x ^ (1 - 2 * σ) := by rw [← hx, hpair]
    _ = x ^ (1 : ℝ) * x ^ (1 - 2 * σ) := by rw [Real.rpow_one]
    _ = x ^ (1 + (1 - 2 * σ)) := (Real.rpow_add hx0 _ _).symm
    _ = x ^ (2 - 2 * σ) := by congr 1; ring

/-- **Length-balanced Montgomery interpolation.**  Two complementary length-dominated
second-moment estimates give Maynard's first alternative exactly.  This is the dual of
`maynard_balanced_montgomery`: two factors below the height close the second alternative, while
two factors above the height close the first. -/
theorem maynard_balanced_length_montgomery
    {R C x σ A B : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hA : 0 ≤ A) (hRA : R ≤ C * A) (hRB : R ≤ C * B)
    (hAB : A * B = x ^ (2 - 2 * σ)) :
    R ≤ C * x ^ (1 - σ) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hCA : 0 ≤ C * A := mul_nonneg hC hA
  have hmul : R * R ≤ (C * A) * (C * B) :=
    mul_le_mul hRA hRB hR hCA
  have hpow : (x ^ (1 - σ)) ^ 2 = x ^ (2 - 2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
    ring_nf
  have hsq : R ^ 2 ≤ (C * x ^ (1 - σ)) ^ 2 := by
    calc
      R ^ 2 = R * R := by ring
      _ ≤ (C * A) * (C * B) := hmul
      _ = C ^ 2 * (A * B) := by ring
      _ = C ^ 2 * x ^ (2 - 2 * σ) := by rw [hAB]
      _ = C ^ 2 * (x ^ (1 - σ)) ^ 2 := by rw [hpow]
      _ = (C * x ^ (1 - σ)) ^ 2 := by ring
  have htarget : 0 ≤ C * x ^ (1 - σ) :=
    mul_nonneg hC (Real.rpow_nonneg hx0 _)
  nlinarith

/-- Length-balanced interpolation stated directly for a complementary factorisation. -/
theorem maynard_balanced_length_montgomery_of_split
    {R C M N x α β σ : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hM : 0 < M) (hN : 0 < N) (hx : x = M * N) (hx1 : 1 ≤ x)
    (hscale : x ^ σ = M ^ α * N ^ β)
    (hRM : R ≤ C * M ^ (2 - 2 * α))
    (hRN : R ≤ C * N ^ (2 - 2 * β)) :
    R ≤ C * x ^ (1 - σ) := by
  exact maynard_balanced_length_montgomery hR hC hx1
    (Real.rpow_nonneg hM.le _) hRM hRN
    (maynard_pair_length_energy_identity hM hN hx hscale)

/-- The mixed coefficient energies in the unbalanced Montgomery case. -/
theorem maynard_unbalanced_energy_identity
    {M N x α β σ : ℝ} (hM : 0 < M) (hN : 0 < N) (hx : x = M * N)
    (hscale : x ^ σ = M ^ α * N ^ β) :
    M ^ (1 - 2 * α) * N ^ (2 - 2 * β) = x ^ (2 - 2 * σ) / M := by
  have hx0 : 0 < x := by rw [hx]; positivity
  have hlog : σ * Real.log x = α * Real.log M + β * Real.log N := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hM,
      Real.rpow_def_of_pos hN, ← Real.exp_add] at hscale
    have h := Real.exp_injective hscale
    linarith
  rw [Real.rpow_def_of_pos hM, Real.rpow_def_of_pos hN,
    Real.rpow_def_of_pos hx0, div_eq_mul_inv,
    show M⁻¹ = Real.exp (-Real.log M) by
      rw [Real.exp_neg, Real.exp_log hM],
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [hx, Real.log_mul hM.ne' hN.ne'] at hlog ⊢
  linarith

/-- **Unbalanced Montgomery interpolation.**  If the short factor is height-dominated and the
long factor length-dominated, the Route-T `R` target follows exactly when
`x^(2σ-2ν) ≤ T M`. -/
theorem maynard_unbalanced_montgomery
    {R T M x σ ν A B : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hM : 0 < M) (hx : 1 ≤ x) (hA : 0 ≤ A)
    (hRA : R ≤ T * A) (hRB : R ≤ B)
    (hAB : A * B = x ^ (2 - 2 * σ) / M)
    (hfit : x ^ (2 * σ - 2 * ν) ≤ T * M) :
    R ≤ T * x ^ (1 + ν - 2 * σ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hTA : 0 ≤ T * A := mul_nonneg hT hA
  have hmul : R * R ≤ (T * A) * B := mul_le_mul hRA hRB hR hTA
  have hfactor0 : 0 ≤ T * x ^ (2 + 2 * ν - 4 * σ) := by positivity
  have hfit' := mul_le_mul_of_nonneg_left hfit hfactor0
  have hcompare : T * (x ^ (2 - 2 * σ) / M)
      ≤ (T * x ^ (1 + ν - 2 * σ)) ^ 2 := by
    rw [show T * (x ^ (2 - 2 * σ) / M) =
      (T * x ^ (2 - 2 * σ)) / M by ring]
    rw [div_le_iff₀ hM]
    calc
      T * x ^ (2 - 2 * σ)
          = (T * x ^ (2 + 2 * ν - 4 * σ)) * x ^ (2 * σ - 2 * ν) := by
              rw [show (2 : ℝ) - 2 * σ =
                (2 + 2 * ν - 4 * σ) + (2 * σ - 2 * ν) by ring,
                Real.rpow_add hx0]
              ring
      _ ≤ (T * x ^ (2 + 2 * ν - 4 * σ)) * (T * M) := hfit'
      _ = (T * x ^ (1 + ν - 2 * σ)) ^ 2 * M := by
              have hp : (x ^ (1 + ν - 2 * σ)) ^ 2 =
                  x ^ (2 + 2 * ν - 4 * σ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
                norm_num
                ring_nf
              rw [mul_pow, hp]
              ring
  have hsq : R ^ 2 ≤ (T * x ^ (1 + ν - 2 * σ)) ^ 2 := by
    calc
      R ^ 2 = R * R := by ring
      _ ≤ (T * A) * B := hmul
      _ = T * (A * B) := by ring
      _ = T * (x ^ (2 - 2 * σ) / M) := by rw [hAB]
      _ ≤ (T * x ^ (1 + ν - 2 * σ)) ^ 2 := hcompare
  have htarget0 : 0 ≤ T * x ^ (1 + ν - 2 * σ) := by positivity
  nlinarith

/-- Unbalanced interpolation stated directly for a complementary factorisation. -/
theorem maynard_unbalanced_montgomery_of_split
    {R T M N x α β σ ν : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hM : 0 < M) (hN : 0 < N) (hx : x = M * N) (hx1 : 1 ≤ x)
    (hscale : x ^ σ = M ^ α * N ^ β)
    (hRM : R ≤ T * M ^ (1 - 2 * α))
    (hRN : R ≤ N ^ (2 - 2 * β))
    (hfit : x ^ (2 * σ - 2 * ν) ≤ T * M) :
    R ≤ T * x ^ (1 + ν - 2 * σ) := by
  exact maynard_unbalanced_montgomery hR hT hM hx1
    (Real.rpow_nonneg hM.le _) hRM hRN
    (maynard_unbalanced_energy_identity hM hN hx hscale) hfit

/-- **Sixth/second-moment interpolation.**  A sixth-moment estimate on one factor and a
length-dominated second-moment estimate on its complement close the Route-T target whenever
`x^(2+2σ-4ν) ≤ (TM)^(3 : ℕ)`.  This is the exact residual condition for the high-`σ` lane. -/
theorem maynard_sixth_montgomery
    {R T M x σ ν A B : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hM : 0 < M) (hx : 1 ≤ x) (hA : 0 ≤ A)
    (hRA : R ≤ T * A) (hRB : R ≤ B)
    (henergy : A * B ^ 3 = x ^ (6 - 6 * σ) / M ^ 3)
    (hfit : x ^ (2 + 2 * σ - 4 * ν) ≤ (T * M) ^ 3) :
    R ≤ T * x ^ (1 + ν - 2 * σ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hTA : 0 ≤ T * A := mul_nonneg hT hA
  have hB0 : 0 ≤ B := le_trans hR hRB
  have hR3 : R ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ hR hRB 3
  have hmul : R * R ^ 3 ≤ (T * A) * B ^ 3 :=
    mul_le_mul hRA hR3 (by positivity) hTA
  have hfactor0 : 0 ≤ T * x ^ (4 + 4 * ν - 8 * σ) := by positivity
  have hfit' := mul_le_mul_of_nonneg_left hfit hfactor0
  have hcompare : T * (x ^ (6 - 6 * σ) / M ^ 3)
      ≤ (T * x ^ (1 + ν - 2 * σ)) ^ 4 := by
    have hM3 : 0 < M ^ 3 := by positivity
    rw [show T * (x ^ (6 - 6 * σ) / M ^ 3) =
      (T * x ^ (6 - 6 * σ)) / M ^ 3 by ring]
    rw [div_le_iff₀ hM3]
    calc
      T * x ^ (6 - 6 * σ)
          = (T * x ^ (4 + 4 * ν - 8 * σ)) * x ^ (2 + 2 * σ - 4 * ν) := by
              rw [show (6 : ℝ) - 6 * σ =
                (4 + 4 * ν - 8 * σ) + (2 + 2 * σ - 4 * ν) by ring,
                Real.rpow_add hx0]
              ring
      _ ≤ (T * x ^ (4 + 4 * ν - 8 * σ)) * (T * M) ^ 3 := hfit'
      _ = (T * x ^ (1 + ν - 2 * σ)) ^ 4 * M ^ 3 := by
              have hp : (x ^ (1 + ν - 2 * σ)) ^ 4 =
                  x ^ (4 + 4 * ν - 8 * σ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
                norm_num
                ring_nf
              calc
                (T * x ^ (4 + 4 * ν - 8 * σ)) * (T * M) ^ 3
                    = T ^ 4 * x ^ (4 + 4 * ν - 8 * σ) * M ^ 3 := by ring
                _ = T ^ 4 * (x ^ (1 + ν - 2 * σ)) ^ 4 * M ^ 3 := by rw [hp]
                _ = (T * x ^ (1 + ν - 2 * σ)) ^ 4 * M ^ 3 := by ring
  have hpow : R ^ 4 ≤ (T * x ^ (1 + ν - 2 * σ)) ^ 4 := by
    calc
      R ^ 4 = R * R ^ 3 := by ring
      _ ≤ (T * A) * B ^ 3 := hmul
      _ = T * (A * B ^ 3) := by ring
      _ = T * (x ^ (6 - 6 * σ) / M ^ 3) := by rw [henergy]
      _ ≤ (T * x ^ (1 + ν - 2 * σ)) ^ 4 := hcompare
  have htarget0 : 0 ≤ T * x ^ (1 + ν - 2 * σ) := by positivity
  exact le_of_pow_le_pow_left₀ (by norm_num) htarget0 hpow

end RHTower.Sieve
