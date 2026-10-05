import GaloisForLFunctions.RHTower.Matveev.FeldmanParameters

/-!
# Every extrapolation step gains

With the constants of `FeldmanParams`, `N = a n`, `X₀ = c n` and `|Λ| < e^{−C₀ n}`, every stage
`r < R` of the extrapolation satisfies its arithmetic threshold
`B^{T_r} · (bound for |Φ_{σ,τ}(x′)|) < D(N + 1, S)`.

The common divisor cancels the polynomial factor (`pow_le_feldmanDivisor_mul_exp`), so both the
growth term and the `Λ` term are `D` times `e^{O(n)}`:

* growth: `B^T (2/7)^{MX} G ≤ D · exp(Tn − MX + O(X q W) + O(n)) ≤ D/2`, because `M` dominates
  `q W` and `Mc` dominates every linear coefficient;
* `Λ` term: `B^T (2H + β) ≤ |Λ| · D · e^{C₀′ n} < D/2` once `|Λ| < e^{−(C₀′+1) n}`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Real

/-! ## Elementary exponential bounds -/

theorem natCast_add_one_le_exp (N : ℕ) : (N : ℝ) + 1 ≤ Real.exp N := by
  have := Real.add_one_le_exp (N : ℝ); linarith

theorem le_exp_self' (x : ℝ) : x ≤ Real.exp x := by
  have := Real.add_one_le_exp x; linarith

theorem pow_le_exp_of_le {x y : ℝ} (hx : 0 ≤ x) (h : x ≤ Real.exp y) (k : ℕ) :
    x ^ k ≤ Real.exp (k * y) := by
  rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ hx h k

theorem two_pow_le_exp (k : ℕ) : (2 : ℝ) ^ k ≤ Real.exp k := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  simpa using pow_le_exp_of_le (by norm_num) h k

theorem two_sevenths_pow_le (k : ℕ) : (2 / 7 : ℝ) ^ k ≤ Real.exp (-(k : ℝ)) := by
  have h : (2 / 7 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    linarith [Real.exp_one_lt_d9]
  simpa using pow_le_exp_of_le (by norm_num) h k

theorem pow_le_exp_mul_of_log_le {B : ℝ} {n : ℝ} (hB : 1 ≤ B) (hBn : Real.log B ≤ n) (k : ℕ) :
    B ^ k ≤ Real.exp (k * n) := by
  refine pow_le_exp_of_le (by linarith) ?_ k
  calc B = Real.exp (Real.log B) := (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp n := Real.exp_le_exp.mpr hBn

/-! ## The bounds of one stage -/

variable {m : ℕ}

/-- The coefficient bound for the Siegel system at the nodes `x < X₀`. -/
def feldmanCoeffBound (m N q S X₀ : ℕ) (B Wt : ℝ) : ℝ :=
  2 ^ N * ((X₀ : ℝ) + N + 1) ^ N / feldmanDivisor (N + 1) S * (2 * q * B) ^ (m * S) *
    Real.exp (X₀ * (q * Wt))

/-- The bound for the Siegel coefficients `|C(k, l)|`. -/
def feldmanCmax (m N q S X₀ : ℕ) (B Wt : ℝ) : ℝ :=
  ((N + 1) * q ^ (m + 1) : ℕ) * max 1 (feldmanCoeffBound m N q S X₀ B Wt)

/-- The coefficient bound with the divisor cancelled. -/
def feldmanCoeffMajorant (m N q S X₀ : ℕ) (B Wt : ℝ) : ℝ :=
  2 ^ N * Real.exp (X₀ + (N + 1) * (1 + feldmanKappa S)) * (2 * q * B) ^ (m * S) *
    Real.exp (X₀ * (q * Wt))

/-- The growth bound divided by the divisor. -/
def feldmanGrowthFactor (m N q S T : ℕ) (A W ρ : ℝ) : ℝ :=
  ((N + 1) * q ^ (m + 1) : ℕ) * (((N + 1) * q ^ (m + 1) : ℕ) * A) * 2 ^ N *
    Real.exp (ρ + (N + 1) * (1 + feldmanKappa S)) * (2 * q : ℝ) ^ T * Real.exp (ρ * (2 * q * W))

/-- The `Λ`-error bound divided by `|Λ|` and by the divisor. -/
def feldmanErrorFactor (m N q S T : ℕ) (A Wt ρ : ℝ) : ℝ :=
  ((N + 1) * q ^ (m + 1) : ℕ) * (((N + 1) * q ^ (m + 1) : ℕ) * A) * 2 ^ N *
    Real.exp (ρ + (N + 1) * (1 + feldmanKappa S)) * (2 * q : ℝ) ^ T * Real.exp (ρ * (q * Wt)) *
      (2 * (ρ * q))

/-- The factor by which the Hermite correction enlarges the `Λ`-error. -/
def feldmanHermiteFactor (X M T : ℕ) (W ρ : ℝ) : ℝ :=
  5 * (X * (((T : ℝ) + W) ^ M * (Real.exp (ρ + X) * (2 ^ M * (2 ^ X * Real.exp (ρ + X)) ^ (M * M)))))

theorem feldmanCoeffMajorant_one_le {N q S X₀ : ℕ} {B Wt : ℝ} (hB : 1 ≤ B) (hq : 1 ≤ q)
    (hWt : 0 ≤ Wt) : 1 ≤ feldmanCoeffMajorant m N q S X₀ B Wt := by
  unfold feldmanCoeffMajorant
  have hκ := feldmanKappa_nonneg S
  have h1 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have h2 : 1 ≤ Real.exp (X₀ + (N + 1) * (1 + feldmanKappa S)) := Real.one_le_exp (by positivity)
  have h3 : (1 : ℝ) ≤ (2 * q * B) ^ (m * S) := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    exact one_le_pow₀ (by nlinarith)
  have h4 : 1 ≤ Real.exp (X₀ * (q * Wt)) := Real.one_le_exp (by positivity)
  calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

theorem max_one_feldmanCoeffBound_le {N q S X₀ : ℕ} {B Wt : ℝ} (hB : 1 ≤ B) (hq : 1 ≤ q)
    (hWt : 0 ≤ Wt) :
    max 1 (feldmanCoeffBound m N q S X₀ B Wt) ≤ feldmanCoeffMajorant m N q S X₀ B Wt := by
  refine max_le (feldmanCoeffMajorant_one_le hB hq hWt) ?_
  unfold feldmanCoeffBound feldmanCoeffMajorant
  have hD : (0 : ℝ) < feldmanDivisor (N + 1) S := by exact_mod_cast feldmanDivisor_pos _ _
  have hK := pow_le_feldmanDivisor_mul_exp N S (Nat.cast_nonneg X₀ : (0 : ℝ) ≤ X₀)
  have hdiv : ((X₀ : ℝ) + N + 1) ^ N / feldmanDivisor (N + 1) S ≤
      Real.exp (X₀ + (N + 1) * (1 + feldmanKappa S)) := by
    rw [div_le_iff₀ hD]; linarith
  have hB0 : (0 : ℝ) ≤ 2 * q * B := by positivity
  calc 2 ^ N * ((X₀ : ℝ) + N + 1) ^ N / feldmanDivisor (N + 1) S * (2 * q * B) ^ (m * S) *
        Real.exp (X₀ * (q * Wt))
      = 2 ^ N * (((X₀ : ℝ) + N + 1) ^ N / feldmanDivisor (N + 1) S) * (2 * q * B) ^ (m * S) *
          Real.exp (X₀ * (q * Wt)) := by ring
    _ ≤ _ := by gcongr

theorem feldmanCmax_le {N q S X₀ : ℕ} {B Wt : ℝ} (hB : 1 ≤ B) (hq : 1 ≤ q) (hWt : 0 ≤ Wt) :
    feldmanCmax m N q S X₀ B Wt ≤
      ((N + 1) * q ^ (m + 1) : ℕ) * feldmanCoeffMajorant m N q S X₀ B Wt := by
  unfold feldmanCmax
  exact mul_le_mul_of_nonneg_left (max_one_feldmanCoeffBound_le hB hq hWt) (Nat.cast_nonneg _)

theorem feldmanCmax_nonneg {N q S X₀ : ℕ} {B Wt : ℝ} : 0 ≤ feldmanCmax m N q S X₀ B Wt := by
  unfold feldmanCmax
  exact mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (le_max_left _ _))

/-- **Growth against the divisor.** -/
theorem feldmanGrowthBound_le {N q S T : ℕ} {Cm A W ρ : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : Cm ≤ ((N + 1) * q ^ (m + 1) : ℕ) * A) (hρ : 0 ≤ ρ) :
    feldmanGrowthBound m N q T Cm W ρ ≤
      feldmanDivisor (N + 1) S * feldmanGrowthFactor m N q S T A W ρ := by
  unfold feldmanGrowthBound feldmanGrowthFactor
  have hK := pow_le_feldmanDivisor_mul_exp N S hρ
  have hA : (0 : ℝ) ≤ ((N + 1) * q ^ (m + 1) : ℕ) * A := hCm0.trans hCm
  calc ((N + 1) * q ^ (m + 1) : ℕ) * Cm * (2 ^ N * (ρ + N + 1) ^ N) * (2 * q : ℝ) ^ T *
        Real.exp (ρ * (2 * q * W))
      ≤ ((N + 1) * q ^ (m + 1) : ℕ) * (((N + 1) * q ^ (m + 1) : ℕ) * A) *
          (2 ^ N * (feldmanDivisor (N + 1) S * Real.exp (ρ + (N + 1) * (1 + feldmanKappa S)))) *
            (2 * q : ℝ) ^ T * Real.exp (ρ * (2 * q * W)) := by gcongr
    _ = _ := by ring

/-- **The `Λ`-error against the divisor.** -/
theorem feldmanErrorBound_le {N q S T : ℕ} {Cm A Wt ρ lam : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : Cm ≤ ((N + 1) * q ^ (m + 1) : ℕ) * A) (hρ : 0 ≤ ρ) :
    feldmanErrorBound m N q T Cm Wt ρ lam ≤
      |lam| * (feldmanDivisor (N + 1) S * feldmanErrorFactor m N q S T A Wt ρ) := by
  unfold feldmanErrorBound feldmanErrorFactor
  have hK := pow_le_feldmanDivisor_mul_exp N S hρ
  have hA : (0 : ℝ) ≤ ((N + 1) * q ^ (m + 1) : ℕ) * A := hCm0.trans hCm
  calc ((N + 1) * q ^ (m + 1) : ℕ) * Cm * (2 ^ N * (ρ + N + 1) ^ N) * (2 * q : ℝ) ^ T *
        Real.exp (ρ * (q * Wt)) * (2 * (ρ * q * |lam|))
      ≤ ((N + 1) * q ^ (m + 1) : ℕ) * (((N + 1) * q ^ (m + 1) : ℕ) * A) *
          (2 ^ N * (feldmanDivisor (N + 1) S * Real.exp (ρ + (N + 1) * (1 + feldmanKappa S)))) *
            (2 * q : ℝ) ^ T * Real.exp (ρ * (q * Wt)) * (2 * (ρ * q * |lam|)) := by gcongr
    _ = _ := by ring

/-- **The step bound splits into the growth term and the `Λ` term.** -/
theorem feldmanStepBound_le {N q T X M : ℕ} {Cm W Wt lam : ℝ} (hCm0 : 0 ≤ Cm) (hX : 1 ≤ X)
    (hTW : 1 ≤ (T : ℝ) + W) :
    feldmanStepBound m N q T X M Cm W Wt lam ≤
      (2 / 7 : ℝ) ^ (M * X) * feldmanGrowthBound m N q T Cm W (8 * X) +
        feldmanErrorBound m N q T Cm Wt (8 * X) lam * feldmanHermiteFactor X M T W (8 * X) := by
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  set β := feldmanErrorBound m N q T Cm Wt (8 * X) lam with hβ
  have hβ0 : 0 ≤ β := feldmanErrorBound_nonneg hCm0 (by positivity)
  set G := feldmanGrowthBound m N q T Cm W (8 * X) with hG
  have hG0 : 0 ≤ G := feldmanGrowthBound_nonneg hCm0 (by positivity)
  set P := (X : ℝ) * (((T : ℝ) + W) ^ M * (Real.exp (8 * X + X) *
    (2 ^ M * (2 ^ X * Real.exp (8 * X + X)) ^ (M * M)))) with hP
  have hP1 : 1 ≤ P := by
    have h1 : 1 ≤ ((T : ℝ) + W) ^ M := one_le_pow₀ hTW
    have h2 : 1 ≤ Real.exp (8 * X + X) := Real.one_le_exp (by positivity)
    have h3 : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
    have h4 : (1 : ℝ) ≤ (2 ^ X * Real.exp (8 * X + X)) ^ (M * M) :=
      one_le_pow₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) h2)
    rw [hP]
    calc (1 : ℝ) = 1 * (1 * (1 * (1 * 1))) := by ring
      _ ≤ _ := by gcongr
  have hHb : integerHermiteBound X M (8 * X) (((T : ℝ) + W) ^ M * β) = 2 * β * P := by
    unfold integerHermiteBound; rw [hP]; ring
  have h27 : (2 / 7 : ℝ) ^ (M * X) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h270 : (0 : ℝ) ≤ (2 / 7 : ℝ) ^ (M * X) := by positivity
  have hfac : feldmanHermiteFactor X M T W (8 * X) = 5 * P := by
    unfold feldmanHermiteFactor; rw [hP]
  unfold feldmanStepBound
  rw [← hβ, ← hG, hHb, hfac]
  have : (2 / 7 : ℝ) ^ (M * X) * (2 * β * P) ≤ 2 * β * P := by
    have : 0 ≤ 2 * β * P := by positivity
    nlinarith
  nlinarith

/-! ## The exponent budgets -/

variable {Wb : ℕ}

theorem natCast_feldman_le_exp (N q m : ℕ) :
    (((N + 1) * q ^ (m + 1) : ℕ) : ℝ) ≤ Real.exp (N + (m + 1) * q) := by
  push_cast
  rw [Real.exp_add]
  have h1 := natCast_add_one_le_exp N
  have h2 : (q : ℝ) ^ (m + 1) ≤ Real.exp ((m + 1 : ℕ) * (q : ℝ)) :=
    pow_le_exp_of_le (Nat.cast_nonneg q) (le_exp_self' q) (m + 1)
  push_cast at h2
  exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le

theorem feldmanCoeffMajorant_le_exp {N q S X₀ : ℕ} {B Wt n : ℝ} (hB : 1 ≤ B)
    (hBn : Real.log B ≤ n) :
    feldmanCoeffMajorant m N q S X₀ B Wt ≤
      Real.exp (N + (X₀ + (N + 1) * (1 + feldmanKappa S)) + (m * S : ℕ) * (2 * q + n) +
        X₀ * (q * Wt)) := by
  unfold feldmanCoeffMajorant
  have h2B : 2 * (q : ℝ) * B ≤ Real.exp (2 * q + n) := by
    rw [Real.exp_add]
    have hBe : B ≤ Real.exp n :=
      (Real.exp_log (by linarith : (0 : ℝ) < B)).symm.le.trans (Real.exp_le_exp.mpr hBn)
    exact mul_le_mul (le_exp_self' _) hBe (by linarith) (Real.exp_pos _).le
  have h3 := pow_le_exp_of_le (by positivity) h2B (m * S)
  have h1 := two_pow_le_exp N
  calc 2 ^ N * Real.exp (X₀ + (N + 1) * (1 + feldmanKappa S)) * (2 * q * B) ^ (m * S) *
        Real.exp (X₀ * (q * Wt))
      ≤ Real.exp N * Real.exp (X₀ + (N + 1) * (1 + feldmanKappa S)) *
          Real.exp ((m * S : ℕ) * (2 * q + n)) * Real.exp (X₀ * (q * Wt)) := by gcongr
    _ = _ := by simp only [← Real.exp_add]

/-- The exponent `C₀′` of the `Λ`-absorption. -/
def feldmanLambdaExponent (P : FeldmanParams m Wb) : ℝ :=
  P.S + 2 * P.a + 2 * (m + 1) * P.q + P.a + P.c + (P.a + 1) * (19 + 12 * P.R) +
    2 * P.q * m * P.S + m * P.S + P.c * P.q * Wb + P.a + 8 * (2 ^ P.R * P.c) +
    (P.a + 1) * (19 + 12 * P.R) + 2 * P.q * P.S + 8 * (2 ^ P.R * P.c) * P.q * Wb +
    16 * (2 ^ P.R * P.c) * P.q + 5 + (2 ^ P.R * P.c) + P.M * (P.S + Wb) + 9 * (2 ^ P.R * P.c) +
    P.M + 10 * P.M ^ 2 * (2 ^ P.R * P.c)

theorem feldmanLambdaExponent_nonneg (P : FeldmanParams m Wb) : 0 ≤ feldmanLambdaExponent P := by
  unfold feldmanLambdaExponent; positivity

/-- The stage order `T_r = S − rM` is at least one. -/
theorem one_le_stageOrder (P : FeldmanParams m Wb) {r : ℕ} (hr : r < P.R) :
    1 ≤ P.S - r * P.M := by
  have h := Nat.mul_le_mul_right P.M (show r ≤ P.R by omega)
  rw [P.S_eq]; omega

/-- The exponent inequality behind `feldman_growth_gain`. -/
theorem feldman_growth_exponent_le {n T S N X κ M c a q m R Wb W Wt : ℝ} (hn1 : 1 ≤ n)
    (hTS : T ≤ S) (hN : N = a * n) (ha : 0 ≤ a) (hXc : c * n ≤ X) (hc : 0 ≤ c)
    (hκ : κ ≤ 18 + 12 * R) (hR : 0 ≤ R) (hq0 : 0 ≤ q) (hm : 0 ≤ m) (hS0 : 0 ≤ S)
    (hW : W ≤ Wb) (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ Wb) (hM0 : 0 ≤ M)
    (hMge : 4 * (9 + 17 * q * Wb) ≤ M)
    (hgain : 4 * ((m + 1) * S * (1 + 2 * q) + 4 * a + 2 * (m + 1) * q +
      2 * (a + 1) * (19 + 12 * R) + 1) ≤ 3 * M * c) :
    T * n - M * X + (2 * (N + (m + 1) * q) + (N + (c * n + (N + 1) * (1 + κ)) +
      m * S * (2 * q + n) + c * n * (q * Wt)) + N + (8 * X + (N + 1) * (1 + κ)) + T * (2 * q) +
      8 * X * (2 * q * W)) ≤ -1 := by
  have hX0 : 0 ≤ X := le_trans (by positivity) hXc
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have p1 : T * n ≤ S * n := mul_le_mul_of_nonneg_right hTS (by linarith)
  have p2 : T * q ≤ S * q * n := by
    have h1 : T * q ≤ S * q := mul_le_mul_of_nonneg_right hTS hq0
    have h2 : S * q ≤ S * q * n := le_mul_of_one_le_right (by positivity) hn1
    linarith
  have p3 : (c * n) * (q * Wt) ≤ X * (q * Wb) :=
    mul_le_mul hXc (mul_le_mul_of_nonneg_left hWt hq0) (by positivity) hX0
  have p4 : X * (q * W) ≤ X * (q * Wb) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW hq0) hX0
  have p5 : (N + 1) * (1 + κ) ≤ (a + 1) * n * (19 + 12 * R) := by
    have h1 : (N + 1) * (1 + κ) ≤ (N + 1) * (19 + 12 * R) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : N + 1 ≤ (a + 1) * n := by rw [hN]; linarith
    have h3 : (N + 1) * (19 + 12 * R) ≤ (a + 1) * n * (19 + 12 * R) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  have p6 : (m + 1) * q ≤ (m + 1) * q * n := le_mul_of_one_le_right (by positivity) hn1
  have p7 : m * S * q ≤ m * S * q * n := le_mul_of_one_le_right (by positivity) hn1
  have p8 : 4 * (9 + 17 * q * Wb) * X ≤ M * X := mul_le_mul_of_nonneg_right hMge hX0
  have p9 : M * (c * n) ≤ M * X := mul_le_mul_of_nonneg_left hXc hM0
  have p10 := mul_le_mul_of_nonneg_right hgain (by linarith : (0 : ℝ) ≤ n)
  rw [hN] at p5 ⊢
  linarith

/-- **The growth term gains.** -/
theorem feldman_growth_gain (P : FeldmanParams m Wb) {n : ℕ} (r : ℕ) (hn : 1 ≤ n)
    {B W Wt : ℝ} (hB : 1 ≤ B) (hBn : Real.log B ≤ n) (hW : W ≤ Wb)
    (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ Wb) :
    B ^ (P.S - r * P.M) * ((2 / 7 : ℝ) ^ (P.M * (2 ^ r * (P.c * n))) *
      feldmanGrowthFactor m (P.a * n) P.q P.S (P.S - r * P.M)
        (feldmanCoeffMajorant m (P.a * n) P.q P.S (P.c * n) B Wt) W
        (8 * ((2 ^ r * (P.c * n) : ℕ) : ℝ))) ≤ 1 / 2 := by
  set T := P.S - r * P.M with hT
  set N := P.a * n with hN
  set X := 2 ^ r * (P.c * n) with hX
  set κ := feldmanKappa P.S with hκ
  set A := feldmanCoeffMajorant m N P.q P.S (P.c * n) B Wt with hA
  have hq1 : (1 : ℝ) ≤ P.q := by exact_mod_cast P.one_le_q
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTS : (T : ℝ) ≤ P.S := by exact_mod_cast Nat.sub_le _ _
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hκle : κ ≤ 18 + 12 * P.R := feldmanKappa_le P.logS
  have hκ0 : 0 ≤ κ := feldmanKappa_nonneg _
  have hXr : (X : ℝ) = 2 ^ r * (P.c * n) := by rw [hX]; push_cast; ring
  have hNr : (N : ℝ) = P.a * n := by rw [hN]; push_cast; ring
  have h2r : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hc0 : (0 : ℝ) ≤ P.c := Nat.cast_nonneg _
  have hXc : (P.c : ℝ) * n ≤ X := by rw [hXr]; nlinarith
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  -- the factor bounds
  have hBT := pow_le_exp_mul_of_log_le hB hBn T
  have h27 := two_sevenths_pow_le (P.M * X)
  have hU := natCast_feldman_le_exp N P.q m
  have hAe : A ≤ Real.exp (N + ((P.c * n : ℕ) + (N + 1) * (1 + κ)) +
      (m * P.S : ℕ) * (2 * P.q + n) + (P.c * n : ℕ) * (P.q * Wt)) :=
    feldmanCoeffMajorant_le_exp hB hBn
  have h2N := two_pow_le_exp N
  have h2qT : (2 * P.q : ℝ) ^ T ≤ Real.exp (T * (2 * P.q)) :=
    pow_le_exp_of_le (by positivity) (le_exp_self' _) T
  have hA0 : 0 ≤ A := le_trans zero_le_one (feldmanCoeffMajorant_one_le hB P.one_le_q hWt0)
  have hprod : B ^ T * ((2 / 7 : ℝ) ^ (P.M * X) *
      feldmanGrowthFactor m N P.q P.S T A W (8 * (X : ℝ))) ≤
      Real.exp (T * n) * (Real.exp (-((P.M * X : ℕ) : ℝ)) *
        (Real.exp (N + (m + 1) * P.q) * (Real.exp (N + (m + 1) * P.q) *
          Real.exp (N + ((P.c * n : ℕ) + (N + 1) * (1 + κ)) + (m * P.S : ℕ) * (2 * P.q + n) +
            (P.c * n : ℕ) * (P.q * Wt))) * Real.exp N *
          Real.exp (8 * (X : ℝ) + (N + 1) * (1 + κ)) * Real.exp (T * (2 * P.q)) *
          Real.exp (8 * (X : ℝ) * (2 * P.q * W)))) := by
    unfold feldmanGrowthFactor
    rw [← hκ]
    gcongr
  refine hprod.trans ?_
  simp only [← Real.exp_add]
  have hhalf : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  refine le_trans (Real.exp_le_exp.mpr ?_) hhalf
  have hE := feldman_growth_exponent_le (n := n) (T := T) (S := P.S) (N := N) (X := X)
    (κ := κ) (M := P.M) (c := P.c) (a := P.a) (q := P.q) (m := m) (R := P.R) (Wb := Wb) (W := W)
    (Wt := Wt) hn1 hTS hNr (Nat.cast_nonneg _) hXc hc0 hκle (Nat.cast_nonneg _)
    (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hW hWt0 hWt (Nat.cast_nonneg _)
    (by exact_mod_cast P.M_ge) (by exact_mod_cast P.gain)
  refine le_trans (le_of_eq ?_) hE
  push_cast
  ring

/-- The exponent inequality behind `feldman_error_gain`. -/
theorem feldman_error_exponent_le {n T S N X κ M c a q m R Wb W Wt Xc : ℝ} (hn1 : 1 ≤ n)
    (hT0 : 0 ≤ T) (hTS : T ≤ S) (hN : N = a * n) (ha : 0 ≤ a) (hX0 : 0 ≤ X) (hX : X ≤ Xc * n)
    (hc : 0 ≤ c) (hκ : κ ≤ 18 + 12 * R) (hR : 0 ≤ R) (hq0 : 0 ≤ q) (hm : 0 ≤ m) (hS0 : 0 ≤ S)
    (hW0 : 0 ≤ W) (hW : W ≤ Wb) (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ Wb) (hM0 : 0 ≤ M) :
    T * n + ((N + (m + 1) * q) + ((N + (m + 1) * q) + (N + (c * n + (N + 1) * (1 + κ)) +
      m * S * (2 * q + n) + c * n * (q * Wt))) + N + (8 * X + (N + 1) * (1 + κ)) + T * (2 * q) +
      8 * X * (q * Wt) + 2 * (8 * X * q)) + (5 + (X + (M * (T + W) + ((8 * X + X) +
      (M + M * M * (X + (8 * X + X))))))) ≤
    (S + 2 * a + 2 * (m + 1) * q + a + c + (a + 1) * (19 + 12 * R) + 2 * q * m * S + m * S +
      c * q * Wb + a + 8 * Xc + (a + 1) * (19 + 12 * R) + 2 * q * S + 8 * Xc * q * Wb +
      16 * Xc * q + 5 + Xc + M * (S + Wb) + 9 * Xc + M + 10 * M ^ 2 * Xc) * n := by
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have q1 : T * n ≤ S * n := mul_le_mul_of_nonneg_right hTS (by linarith)
  have q2 : (N + 1) * (1 + κ) ≤ (a + 1) * n * (19 + 12 * R) := by
    have h1 : (N + 1) * (1 + κ) ≤ (N + 1) * (19 + 12 * R) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : N + 1 ≤ (a + 1) * n := by rw [hN]; linarith
    have h3 : (N + 1) * (19 + 12 * R) ≤ (a + 1) * n * (19 + 12 * R) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  have q3 : (m + 1) * q ≤ (m + 1) * q * n := le_mul_of_one_le_right (by positivity) hn1
  have q4 : m * S * q ≤ m * S * q * n := le_mul_of_one_le_right (by positivity) hn1
  have q5 : (c * n) * (q * Wt) ≤ c * q * Wb * n := by
    have : (c * n) * (q * Wt) ≤ (c * n) * (q * Wb) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWt hq0) (by positivity)
    linarith
  have q6 : T * q ≤ S * q * n := by
    have h1 : T * q ≤ S * q := mul_le_mul_of_nonneg_right hTS hq0
    have h2 : S * q ≤ S * q * n := le_mul_of_one_le_right (by positivity) hn1
    linarith
  have q7 : X * (q * Wt) ≤ (Xc * n) * (q * Wb) :=
    mul_le_mul hX (mul_le_mul_of_nonneg_left hWt hq0) (by positivity) (by linarith)
  have q8 : X * q ≤ (Xc * n) * q := mul_le_mul_of_nonneg_right hX hq0
  have q10 : M * (T + W) ≤ M * (S + Wb) * n := by
    have h1 : M * (T + W) ≤ M * (S + Wb) := mul_le_mul_of_nonneg_left (by linarith) hM0
    have h2 : M * (S + Wb) ≤ M * (S + Wb) * n :=
      le_mul_of_one_le_right (by nlinarith) hn1
    linarith
  have q11 : M ≤ M * n := le_mul_of_one_le_right hM0 hn1
  have q12 : M * M * X ≤ M * M * (Xc * n) := mul_le_mul_of_nonneg_left hX (by positivity)
  rw [hN] at q2 ⊢
  nlinarith

/-- **The `Λ` term is `e^{O(n)}`.** -/
theorem feldman_error_gain (P : FeldmanParams m Wb) {n r : ℕ} (hn : 1 ≤ n) (hr : r < P.R)
    {B W Wt : ℝ} (hB : 1 ≤ B) (hBn : Real.log B ≤ n) (hW0 : 0 ≤ W) (hW : W ≤ Wb)
    (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ Wb) :
    B ^ (P.S - r * P.M) *
      (feldmanErrorFactor m (P.a * n) P.q P.S (P.S - r * P.M)
          (feldmanCoeffMajorant m (P.a * n) P.q P.S (P.c * n) B Wt) Wt
          (8 * ((2 ^ r * (P.c * n) : ℕ) : ℝ)) *
        feldmanHermiteFactor (2 ^ r * (P.c * n)) P.M (P.S - r * P.M) W
          (8 * ((2 ^ r * (P.c * n) : ℕ) : ℝ))) ≤
      Real.exp (feldmanLambdaExponent P * n) := by
  set T := P.S - r * P.M with hT
  set N := P.a * n with hN
  set X := 2 ^ r * (P.c * n) with hX
  set κ := feldmanKappa P.S with hκ
  set A := feldmanCoeffMajorant m N P.q P.S (P.c * n) B Wt with hA
  have hq1 : (1 : ℝ) ≤ P.q := by exact_mod_cast P.one_le_q
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTS : (T : ℝ) ≤ P.S := by exact_mod_cast Nat.sub_le _ _
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hκle : κ ≤ 18 + 12 * P.R := feldmanKappa_le P.logS
  have hκ0 : 0 ≤ κ := feldmanKappa_nonneg _
  have hNr : (N : ℝ) = P.a * n := by rw [hN]; push_cast; ring
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hXle : (X : ℝ) ≤ (2 ^ P.R * P.c) * n := by
    have h : X ≤ 2 ^ P.R * P.c * n := by
      rw [hX, ← mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by norm_num) hr.le))
    exact_mod_cast h
  have hBT := pow_le_exp_mul_of_log_le hB hBn T
  have hU := natCast_feldman_le_exp N P.q m
  have hAe : A ≤ Real.exp (N + ((P.c * n : ℕ) + (N + 1) * (1 + κ)) +
      (m * P.S : ℕ) * (2 * P.q + n) + (P.c * n : ℕ) * (P.q * Wt)) :=
    feldmanCoeffMajorant_le_exp hB hBn
  have h2N := two_pow_le_exp N
  have h2qT : (2 * P.q : ℝ) ^ T ≤ Real.exp (T * (2 * P.q)) :=
    pow_le_exp_of_le (by positivity) (le_exp_self' _) T
  have hA0 : 0 ≤ A := le_trans zero_le_one (feldmanCoeffMajorant_one_le hB P.one_le_q hWt0)
  have h2ρq : 2 * (8 * (X : ℝ) * P.q) ≤ Real.exp (2 * (8 * (X : ℝ) * P.q)) := le_exp_self' _
  have h5 : (5 : ℝ) ≤ Real.exp 5 := le_exp_self' 5
  have hXe : (X : ℝ) ≤ Real.exp X := le_exp_self' _
  have hTW : ((T : ℝ) + W) ^ P.M ≤ Real.exp (P.M * ((T : ℝ) + W)) :=
    pow_le_exp_of_le (by positivity) (le_exp_self' _) P.M
  have h2M := two_pow_le_exp P.M
  have h2X : ((2 : ℝ) ^ X * Real.exp (8 * (X : ℝ) + X)) ^ (P.M * P.M) ≤
      Real.exp ((P.M * P.M : ℕ) * (X + (8 * (X : ℝ) + X))) := by
    refine pow_le_exp_of_le (by positivity) ?_ _
    calc (2 : ℝ) ^ X * Real.exp (8 * (X : ℝ) + X) ≤ Real.exp X * Real.exp (8 * (X : ℝ) + X) :=
          mul_le_mul_of_nonneg_right (two_pow_le_exp X) (Real.exp_pos _).le
      _ = Real.exp (X + (8 * (X : ℝ) + X)) := by rw [← Real.exp_add]
  have hprod : B ^ T * (feldmanErrorFactor m N P.q P.S T A Wt (8 * (X : ℝ)) *
      feldmanHermiteFactor X P.M T W (8 * (X : ℝ))) ≤
      Real.exp (T * n) * ((Real.exp (N + (m + 1) * P.q) * (Real.exp (N + (m + 1) * P.q) *
          Real.exp (N + ((P.c * n : ℕ) + (N + 1) * (1 + κ)) + (m * P.S : ℕ) * (2 * P.q + n) +
            (P.c * n : ℕ) * (P.q * Wt))) * Real.exp N *
          Real.exp (8 * (X : ℝ) + (N + 1) * (1 + κ)) * Real.exp (T * (2 * P.q)) *
          Real.exp (8 * (X : ℝ) * (P.q * Wt)) * Real.exp (2 * (8 * (X : ℝ) * P.q))) *
        (Real.exp 5 * (Real.exp X * (Real.exp (P.M * ((T : ℝ) + W)) *
          (Real.exp (8 * (X : ℝ) + X) * (Real.exp P.M *
            Real.exp ((P.M * P.M : ℕ) * (X + (8 * (X : ℝ) + X))))))))) := by
    unfold feldmanErrorFactor feldmanHermiteFactor
    rw [← hκ]
    have hρq : 2 * (8 * (X : ℝ) * P.q) = 2 * (8 * (X : ℝ) * P.q) := rfl
    gcongr
  refine hprod.trans ?_
  simp only [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hE := feldman_error_exponent_le (n := n) (T := T) (S := P.S) (N := N) (X := X) (κ := κ)
    (M := P.M) (c := P.c) (a := P.a) (q := P.q) (m := m) (R := P.R) (Wb := Wb) (W := W) (Wt := Wt)
    (Xc := 2 ^ P.R * P.c) hn1 hT0 hTS hNr (Nat.cast_nonneg _) hX0 hXle (Nat.cast_nonneg _) hκle
    (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hW0 hW hWt0 hWt
    (Nat.cast_nonneg _)
  unfold feldmanLambdaExponent
  refine le_trans (le_of_eq ?_) hE
  push_cast
  ring

/-- **Every stage clears its arithmetic threshold.** -/
theorem feldman_stage_threshold (P : FeldmanParams m Wb) {n r : ℕ} (hn : 1 ≤ n) (hr : r < P.R)
    {B W Wt lam : ℝ} (hB : 1 ≤ B) (hBn : Real.log B ≤ n) (hW0 : 0 ≤ W) (hW : W ≤ Wb)
    (hWt0 : 0 ≤ Wt) (hWt : Wt ≤ Wb)
    (hlam : |lam| < Real.exp (-((feldmanLambdaExponent P + 1) * n))) :
    B ^ (P.S - r * P.M) * feldmanStepBound m (P.a * n) P.q (P.S - r * P.M) (2 ^ r * (P.c * n))
      P.M (feldmanCmax m (P.a * n) P.q P.S (P.c * n) B Wt) W Wt lam <
      feldmanDivisor (P.a * n + 1) P.S := by
  set T := P.S - r * P.M with hT
  set N := P.a * n with hN
  set X := 2 ^ r * (P.c * n) with hX
  set D : ℝ := ((feldmanDivisor (N + 1) P.S : ℕ) : ℝ) with hD
  set Cm := feldmanCmax m N P.q P.S (P.c * n) B Wt with hCmdef
  set A := feldmanCoeffMajorant m N P.q P.S (P.c * n) B Wt with hA
  have hD0 : 0 < D := by rw [hD]; exact_mod_cast feldmanDivisor_pos _ _
  have hCm0 : 0 ≤ Cm := feldmanCmax_nonneg
  have hCm : Cm ≤ ((N + 1) * P.q ^ (m + 1) : ℕ) * A := feldmanCmax_le hB P.one_le_q hWt0
  have hX1 : 1 ≤ X := by
    rw [hX]; exact Nat.one_le_iff_ne_zero.mpr (by
      have := P.one_le_c; positivity)
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast one_le_stageOrder P hr
  have hTW : (1 : ℝ) ≤ (T : ℝ) + W := by linarith
  have hstep := feldmanStepBound_le (m := m) (N := N) (q := P.q) (T := T) (X := X) (M := P.M)
    (W := W) (Wt := Wt) (lam := lam) hCm0 hX1 hTW
  have hρ : (0 : ℝ) ≤ 8 * (X : ℝ) := by positivity
  have hG := feldmanGrowthBound_le (S := P.S) (W := W) hCm0 hCm hρ (T := T)
  have hβ := feldmanErrorBound_le (S := P.S) (Wt := Wt) (lam := lam) hCm0 hCm hρ (T := T)
  have hgrowth := feldman_growth_gain P r hn hB hBn hW hWt0 hWt
  have herror := feldman_error_gain P hn hr hB hBn hW0 hW hWt0 hWt
  rw [← hT, ← hN, ← hX] at hgrowth herror
  rw [← hA] at hgrowth herror
  set Γ := feldmanGrowthFactor m N P.q P.S T A W (8 * (X : ℝ)) with hΓ
  set E := feldmanErrorFactor m N P.q P.S T A Wt (8 * (X : ℝ)) with hE
  set H := feldmanHermiteFactor X P.M T W (8 * (X : ℝ)) with hH
  have hH0 : 0 ≤ H := by
    rw [hH]; unfold feldmanHermiteFactor
    have : (0 : ℝ) ≤ (T : ℝ) + W := by linarith
    positivity
  have hB0 : (0 : ℝ) ≤ B ^ T := by positivity
  have h270 : (0 : ℝ) ≤ (2 / 7 : ℝ) ^ (P.M * X) := by positivity
  have hlamexp : |lam| * Real.exp (feldmanLambdaExponent P * n) < 1 / 2 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc |lam| * Real.exp (feldmanLambdaExponent P * n)
        < Real.exp (-((feldmanLambdaExponent P + 1) * n)) *
            Real.exp (feldmanLambdaExponent P * n) :=
          mul_lt_mul_of_pos_right hlam (Real.exp_pos _)
      _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
          linarith [Real.exp_one_gt_d9]
  have hlam0 : 0 ≤ |lam| := abs_nonneg _
  calc B ^ T * feldmanStepBound m N P.q T X P.M Cm W Wt lam
      ≤ B ^ T * ((2 / 7 : ℝ) ^ (P.M * X) * (D * Γ) + |lam| * (D * E) * H) := by
        refine mul_le_mul_of_nonneg_left (hstep.trans ?_) hB0
        gcongr
    _ = D * (B ^ T * ((2 / 7 : ℝ) ^ (P.M * X) * Γ)) + D * |lam| * (B ^ T * (E * H)) := by ring
    _ ≤ D * (1 / 2) + D * |lam| * Real.exp (feldmanLambdaExponent P * n) := by
        gcongr
    _ < D * (1 / 2) + D * (1 / 2) := by
        have : D * |lam| * Real.exp (feldmanLambdaExponent P * n) =
            D * (|lam| * Real.exp (feldmanLambdaExponent P * n)) := by ring
        rw [this]
        gcongr
    _ = D := by ring

end GaloisForLFunctions.RHTower.Matveev
