import GaloisForLFunctions.RHTower.WeightedBlockDirichletEnvelope
import GaloisForLFunctions.RHTower.CosineArcPeriodLowerBound

/-!
# A factorized Dirichlet polynomial whose large-value set resonates: the construction

With `M = m⁴`, `K₁ = 3M`, `K₂ = 4M`, the weighted block `B(u) = Σ_{K₁ ≤ k ≤ K₂} (k/K₂)^{20} k^{iu}`
and the factorized polynomial

`D(u) = (2^{iu} + 3^{iu}) · B(u) = Σ_{k} (k/K₂)^{20} (2k)^{iu} + Σ_k (k/K₂)^{20} (3k)^{iu}`

is a Dirichlet polynomial supported on `[6M, 12M]` with coefficients of modulus at most one, and
`|D(u)| = 2 |cos(λu/2)| · |B(u)|` with `λ = log(3/2)`.  This module records the modulus identity,
the two-sided envelope `|B(u)| = 4M(1 ± 1/400)/√(441 + u²) ± 2` for `0 ≤ u ≤ m²`, the window
`|D(u)| < 4m³` for `3m ≤ u ≤ m²`, and the core / outer / nonnegativity conditions on each period
of `cos(λu)` that feed the period lower bound.
-/

open Complex Set Finset intervalIntegral MeasureTheory Real

namespace RHTower

noncomputable section

/-- `λ = log(3/2)`. -/
def resLam : ℝ := Real.log (3 / 2)

theorem resLam_pos : 0 < resLam := Real.log_pos (by norm_num)

theorem resLam_ge : 1 / 3 ≤ resLam := by
  have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  unfold resLam; norm_num at this ⊢; linarith

theorem resLam_le : resLam ≤ 1 / 2 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  unfold resLam; linarith

/-- The period `P = 2π/λ`. -/
def resPeriod : ℝ := 2 * π / resLam

theorem resPeriod_pos : 0 < resPeriod := by unfold resPeriod; have := resLam_pos; positivity

theorem resPeriod_ge : 4 * π ≤ resPeriod := by
  unfold resPeriod
  rw [le_div_iff₀ resLam_pos]
  have := resLam_le; nlinarith [Real.pi_pos]

theorem resPeriod_le : resPeriod ≤ 6 * π := by
  unfold resPeriod
  rw [div_le_iff₀ resLam_pos]
  have := resLam_ge; nlinarith [Real.pi_pos]

theorem resPeriod_lt_nineteen : resPeriod < 19 := by
  have := resPeriod_le; have := Real.pi_lt_d2; linarith

theorem resPeriod_gt_twelve : 12 < resPeriod := by
  have := resPeriod_ge; have := Real.pi_gt_three; linarith

/-- The weighted block `Σ_{3m⁴ ≤ k ≤ 4m⁴} (k/(4m⁴))^{20} k^{iu}`. -/
def resBlock (m : ℕ) (u : ℝ) : ℂ := blockSum (3 * m ^ 4) (4 * m ^ 4) 20 u

/-- The factorized polynomial `(2^{iu} + 3^{iu}) · resBlock`. -/
def resPoly (m : ℕ) (u : ℝ) : ℂ :=
  ((2 : ℂ) ^ ((u : ℂ) * I) + (3 : ℂ) ^ ((u : ℂ) * I)) * resBlock m u

/-! ## The modulus identity -/

theorem norm_one_add_exp_ofReal_mul_I (x : ℝ) :
    ‖1 + Complex.exp ((x : ℂ) * I)‖ = 2 * |Real.cos (x / 2)| := by
  have hsplit : 1 + Complex.exp ((x : ℂ) * I) =
      Complex.exp (((x / 2 : ℝ) : ℂ) * I) *
        (Complex.exp (((x / 2 : ℝ) : ℂ) * I) + Complex.exp (-((x / 2 : ℝ) : ℂ) * I)) := by
    have h1 : Complex.exp (((x / 2 : ℝ) : ℂ) * I) * Complex.exp (-((x / 2 : ℝ) : ℂ) * I) = 1 := by
      rw [← Complex.exp_add]; simp
    have h2 : Complex.exp (((x / 2 : ℝ) : ℂ) * I) * Complex.exp (((x / 2 : ℝ) : ℂ) * I) =
        Complex.exp ((x : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [mul_add, h1, h2, add_comm]
  rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, ← Complex.two_cos,
    ← Complex.ofReal_cos, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_two]

theorem cpow_ofReal_mul_I_eq_exp {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ((x : ℂ)) ^ ((u : ℂ) * I) = Complex.exp (((Real.log x * u : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  push_cast; ring_nf

theorem norm_two_cpow_add_three_cpow (u : ℝ) :
    ‖(2 : ℂ) ^ ((u : ℂ) * I) + (3 : ℂ) ^ ((u : ℂ) * I)‖ = 2 * |Real.cos (resLam * u / 2)| := by
  have h2 := cpow_ofReal_mul_I_eq_exp (show (0 : ℝ) < 2 by norm_num) u
  have h3 := cpow_ofReal_mul_I_eq_exp (show (0 : ℝ) < 3 by norm_num) u
  push_cast at h2 h3
  rw [h2, h3]
  have hfac : Complex.exp (((Real.log 2 : ℝ) : ℂ) * (u : ℂ) * I) +
      Complex.exp (((Real.log 3 : ℝ) : ℂ) * (u : ℂ) * I) =
      Complex.exp (((Real.log 2 * u : ℝ) : ℂ) * I) *
        (1 + Complex.exp (((resLam * u : ℝ) : ℂ) * I)) := by
    rw [mul_add, mul_one, ← Complex.exp_add]
    congr 1
    · congr 1; push_cast; ring
    · congr 1
      unfold resLam
      rw [Real.log_div (by norm_num) (by norm_num)]
      push_cast; ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_one_add_exp_ofReal_mul_I]

theorem norm_resPoly (m : ℕ) (u : ℝ) :
    ‖resPoly m u‖ = 2 * |Real.cos (resLam * u / 2)| * ‖resBlock m u‖ := by
  unfold resPoly
  rw [norm_mul, norm_two_cpow_add_three_cpow]

/-! ## Continuity -/

theorem continuous_cpow_const_ofReal_mul_I {x : ℂ} (hx : x ∈ slitPlane) :
    Continuous fun u : ℝ => x ^ ((u : ℂ) * I) :=
  continuous_const.cpow (Complex.continuous_ofReal.mul continuous_const) (fun _ => hx)

theorem continuous_resBlock {m : ℕ} (hm : 1 ≤ m) : Continuous (resBlock m) := by
  unfold resBlock blockSum
  apply continuous_finsetSum
  intro k hk
  have hk1 : 1 ≤ k := by
    have h3 := (Finset.mem_Icc.mp hk).1
    have : 1 ≤ m ^ 4 := Nat.one_le_pow _ _ hm
    omega
  apply Continuous.div_const
  have hslit : (k : ℂ) ∈ slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp; omega
  have : (fun u : ℝ => (k : ℂ) ^ blockExponent 20 u) =
      fun u : ℝ => (k : ℂ) ^ ((20 : ℂ) + (u : ℂ) * I) := by
    ext u; rfl
  rw [this]
  exact continuous_const.cpow (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    (fun _ => hslit)

theorem continuous_resPoly {m : ℕ} (hm : 1 ≤ m) : Continuous (resPoly m) := by
  unfold resPoly
  refine Continuous.mul (Continuous.add ?_ ?_) (continuous_resBlock hm)
  · exact continuous_cpow_const_ofReal_mul_I (by rw [Complex.mem_slitPlane_iff]; left; norm_num)
  · exact continuous_cpow_const_ofReal_mul_I (by rw [Complex.mem_slitPlane_iff]; left; norm_num)

/-! ## The envelope at the critical parameters -/

theorem resBlock_envelope {m : ℕ} (hm : 5 ≤ m) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ (m : ℝ) ^ 2) :
    (399 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + u ^ 2) - 2 ≤ ‖resBlock m u‖ ∧
      ‖resBlock m u‖ ≤ (401 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + u ^ 2) + 2 := by
  unfold resBlock
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hX : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
  have h1 : 1 ≤ 3 * m ^ 4 := by
    have : 1 ≤ m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have h12 : 3 * m ^ 4 ≤ 4 * m ^ 4 := by omega
  have hlo := norm_blockSum_ge (u := u) h1 h12 (show 3 ≤ 20 by norm_num)
  have hhi := norm_blockSum_le (u := u) h1 h12 (show 3 ≤ 20 by norm_num)
  have hsub : ((4 * m ^ 4 - 3 * m ^ 4 : ℕ) : ℝ) = (m : ℝ) ^ 4 := by
    rw [Nat.cast_sub h12]; push_cast; ring
  rw [hsub] at hlo hhi
  push_cast at hlo hhi
  have hsq : Real.sqrt ((20 + 1) ^ 2 + u ^ 2) = Real.sqrt (441 + u ^ 2) := by
    norm_num
  rw [hsq] at hlo hhi
  have hsqrt : 0 < Real.sqrt (441 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have habs : |u| = u := abs_of_nonneg hu0
  rw [habs] at hlo hhi
  -- the remainder is at most 2
  have hrem : 1 + (m : ℝ) ^ 4 * ((20 + u) * (20 + 1 + u)) / (8 * (4 * (m : ℝ) ^ 4) ^ 2) ≤ 2 := by
    have hm2 : (20 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hm2' : (21 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hprod : (20 + u) * (20 + 1 + u) ≤ 4 * ((m : ℝ) ^ 2) ^ 2 := by nlinarith
    have : (m : ℝ) ^ 4 * ((20 + u) * (20 + 1 + u)) / (8 * (4 * (m : ℝ) ^ 4) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : ((m : ℝ) ^ 2) ^ 2 = (m : ℝ) ^ 4 := by ring
      nlinarith
    linarith
  -- the main-term envelopes
  have hmain_lo : (399 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + u ^ 2) ≤
      ((4 * (m : ℝ) ^ 4) ^ (20 + 1) - (3 * (m : ℝ) ^ 4) ^ (20 + 1)) /
        (Real.sqrt (441 + u ^ 2) * (4 * (m : ℝ) ^ 4) ^ 20) := by
    rw [div_le_div_iff₀ hsqrt (by positivity)]
    have hpow : (399 / 100 : ℝ) * (m : ℝ) ^ 4 * (4 * (m : ℝ) ^ 4) ^ 20 ≤
        (4 * (m : ℝ) ^ 4) ^ (20 + 1) - (3 * (m : ℝ) ^ 4) ^ (20 + 1) := by
      have : (4 * (m : ℝ) ^ 4) ^ (20 + 1) - (3 * (m : ℝ) ^ 4) ^ (20 + 1) -
          (399 / 100 : ℝ) * (m : ℝ) ^ 4 * (4 * (m : ℝ) ^ 4) ^ 20 =
          (4 ^ 21 - 3 ^ 21 - (399 / 100) * 4 ^ 20 : ℝ) * ((m : ℝ) ^ 4) ^ 21 := by ring
      have hc : (0 : ℝ) ≤ 4 ^ 21 - 3 ^ 21 - (399 / 100) * 4 ^ 20 := by norm_num
      nlinarith [mul_nonneg hc (pow_nonneg hX.le 21)]
    nlinarith [mul_le_mul_of_nonneg_right hpow hsqrt.le]
  have hmain_hi : ((4 * (m : ℝ) ^ 4) ^ (20 + 1) + (3 * (m : ℝ) ^ 4) ^ (20 + 1)) /
        (Real.sqrt (441 + u ^ 2) * (4 * (m : ℝ) ^ 4) ^ 20) ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + u ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) hsqrt]
    have hpow : (4 * (m : ℝ) ^ 4) ^ (20 + 1) + (3 * (m : ℝ) ^ 4) ^ (20 + 1) ≤
        (401 / 100 : ℝ) * (m : ℝ) ^ 4 * (4 * (m : ℝ) ^ 4) ^ 20 := by
      have : (401 / 100 : ℝ) * (m : ℝ) ^ 4 * (4 * (m : ℝ) ^ 4) ^ 20 -
          ((4 * (m : ℝ) ^ 4) ^ (20 + 1) + (3 * (m : ℝ) ^ 4) ^ (20 + 1)) =
          ((401 / 100) * 4 ^ 20 - 4 ^ 21 - 3 ^ 21 : ℝ) * ((m : ℝ) ^ 4) ^ 21 := by ring
      have hc : (0 : ℝ) ≤ (401 / 100) * 4 ^ 20 - 4 ^ 21 - 3 ^ 21 := by norm_num
      nlinarith [mul_nonneg hc (pow_nonneg hX.le 21)]
    nlinarith [mul_le_mul_of_nonneg_right hpow hsqrt.le]
  constructor
  · linarith
  · linarith

/-- Outside `3m ≤ u ≤ m²` (inside the envelope range) there are no large values. -/
theorem norm_resPoly_lt_of_window {m : ℕ} (hm : 5 ≤ m) {u : ℝ} (hu3 : 3 * (m : ℝ) ≤ u)
    (hu : u ≤ (m : ℝ) ^ 2) : ‖resPoly m u‖ < 4 * (m : ℝ) ^ 3 := by
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hu0 : 0 ≤ u := by linarith
  obtain ⟨-, hhi⟩ := resBlock_envelope hm hu0 hu
  rw [norm_resPoly]
  have hcos : |Real.cos (resLam * u / 2)| ≤ 1 := Real.abs_cos_le_one _
  have hsqrt : 3 * (m : ℝ) ≤ Real.sqrt (441 + u ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
  have hsqrt_pos : 0 < Real.sqrt (441 + u ^ 2) := by linarith
  have hdiv : (401 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + u ^ 2) ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ 4 / (3 * (m : ℝ)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt
  have hdiv' : (401 / 100 : ℝ) * (m : ℝ) ^ 4 / (3 * (m : ℝ)) = (401 / 300) * (m : ℝ) ^ 3 := by
    rw [div_eq_iff (by positivity)]; ring
  have hB : ‖resBlock m u‖ ≤ (401 / 300) * (m : ℝ) ^ 3 + 2 := by linarith
  have hBn : 0 ≤ ‖resBlock m u‖ := norm_nonneg _
  calc 2 * |Real.cos (resLam * u / 2)| * ‖resBlock m u‖ ≤ 2 * 1 * ((401 / 300) * (m : ℝ) ^ 3 + 2) := by
        gcongr
    _ < 4 * (m : ℝ) ^ 3 := by nlinarith

/-! ## Period conditions -/

/-- The outer threshold on the `k`-th period. -/
def resKappa (m : ℕ) (k : ℕ) : ℝ :=
  2 * (m : ℝ) ^ 3 / ((401 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) + 2)

theorem sqrt_two_lt : Real.sqrt 2 < 14143 / 10000 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

theorem sqrt_bound_of_le {m : ℕ} (hm : 1000 ≤ m) {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ (69 / 50) * (m : ℝ)) :
    Real.sqrt (441 + v ^ 2) ≤ (13802 / 10000) * (m : ℝ) := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

/-- **Core condition**: on a period with `(k+1)P ≤ 1.38 m`, the core arc lies in the large-value set. -/
theorem resPoly_core {m : ℕ} (hm : 1000 ≤ m) {k : ℕ}
    (hk : ((k : ℝ) + 1) * resPeriod ≤ (69 / 50) * (m : ℝ)) {u : ℝ}
    (hu : u ∈ Icc ((k : ℝ) * resPeriod) (((k : ℝ) + 1) * resPeriod))
    (hcos : Real.sqrt 2 / 2 ≤ |Real.cos (resLam * u / 2)|) :
    4 * (m : ℝ) ^ 3 ≤ ‖resPoly m u‖ := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriod_pos
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  have hu1 : u ≤ (69 / 50) * (m : ℝ) := le_trans hu.2 hk
  have hum : u ≤ (m : ℝ) ^ 2 := by nlinarith
  obtain ⟨hlo, -⟩ := resBlock_envelope (by omega) hu0 hum
  have hsqrt := sqrt_bound_of_le hm hu0 hu1
  have hsqrt_pos : 0 < Real.sqrt (441 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hdiv : (399 / 100 : ℝ) * (m : ℝ) ^ 4 / ((13802 / 10000) * (m : ℝ)) ≤
      (399 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + u ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) hsqrt_pos hsqrt
  have hdiv' : (399 / 100 : ℝ) * (m : ℝ) ^ 4 / ((13802 / 10000) * (m : ℝ)) =
      (399 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ 3 := by
    rw [div_eq_iff (by positivity)]; ring
  have hB : (399 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ 3 - 2 ≤ ‖resBlock m u‖ := by linarith
  rw [norm_resPoly]
  have hs2 := sqrt_two_lt
  have hs2' : (14142 / 10000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hBn : 0 ≤ (399 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ 3 - 2 := by nlinarith
  calc 4 * (m : ℝ) ^ 3
      ≤ 2 * (Real.sqrt 2 / 2) * ((399 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ 3 - 2) := by
        nlinarith
    _ ≤ 2 * |Real.cos (resLam * u / 2)| * ‖resBlock m u‖ := by gcongr

/-- **Outer condition**: on the `k`-th period (with `(k+1)P ≤ m²`), large values force
`|cos(λu/2)| ≥ κ_k`. -/
theorem resPoly_outer {m : ℕ} (hm : 5 ≤ m) {k : ℕ}
    (hk : ((k : ℝ) + 1) * resPeriod ≤ (m : ℝ) ^ 2) {u : ℝ}
    (hu : u ∈ Icc ((k : ℝ) * resPeriod) (((k : ℝ) + 1) * resPeriod))
    (hlarge : 4 * (m : ℝ) ^ 3 ≤ ‖resPoly m u‖) :
    resKappa m k ≤ |Real.cos (resLam * u / 2)| := by
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriod_pos
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  have hum : u ≤ (m : ℝ) ^ 2 := le_trans hu.2 hk
  obtain ⟨-, hhi⟩ := resBlock_envelope hm hu0 hum
  rw [norm_resPoly] at hlarge
  have hsqrt_mono : Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) ≤ Real.sqrt (441 + u ^ 2) := by
    apply Real.sqrt_le_sqrt
    have h1 := hu.1
    have hk0 : 0 ≤ (k : ℝ) * resPeriod := by positivity
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hdiv : (401 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + u ^ 2) ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) hsqrt_pos hsqrt_mono
  set Smax := (401 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) + 2
    with hSmax
  have hSpos : 0 < Smax := by rw [hSmax]; positivity
  have hB : ‖resBlock m u‖ ≤ Smax := by rw [hSmax]; linarith
  have hcos0 : 0 ≤ |Real.cos (resLam * u / 2)| := abs_nonneg _
  unfold resKappa
  rw [← hSmax, div_le_iff₀ hSpos]
  nlinarith [mul_le_mul_of_nonneg_left hB (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hcos0)]

theorem resKappa_pos {m : ℕ} (hm : 1 ≤ m) (k : ℕ) : 0 < resKappa m k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold resKappa
  have : 0 < Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  positivity

theorem resKappa_le_sqrt_two_div_two {m : ℕ} (hm : 1000 ≤ m) {k : ℕ}
    (hk : (k : ℝ) * resPeriod ≤ (69 / 50) * (m : ℝ)) :
    resKappa m k ≤ Real.sqrt 2 / 2 := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriod_pos
  have hk0 : 0 ≤ (k : ℝ) * resPeriod := by positivity
  have hsqrt := sqrt_bound_of_le hm hk0 hk
  have hsqrt_pos : 0 < Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hs2' : (14142 / 10000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold resKappa
  have hden : (401 / 100 : ℝ) * (m : ℝ) ^ 4 / ((13802 / 10000) * (m : ℝ)) ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) hsqrt_pos hsqrt
  have hden' : (401 / 100 : ℝ) * (m : ℝ) ^ 4 / ((13802 / 10000) * (m : ℝ)) =
      (401 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ 3 := by field_simp
  rw [div_le_iff₀ (by positivity)]
  have hA : (401 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ 3 + 2 ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) + 2 := by
    linarith
  have hB := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2)
  have hC := mul_le_mul_of_nonneg_right hs2'.le
    (by positivity : (0 : ℝ) ≤ (401 / 100 : ℝ) * (10000 / 13802) * (m : ℝ) ^ 3 + 2)
  have hm3 : (1000 : ℝ) ^ 3 ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hmR 3
  nlinarith

theorem resKappa_ge {m : ℕ} (hm : 1000 ≤ m) {k : ℕ}
    (hk : (k : ℝ) * resPeriod ≤ (69 / 50) * (m : ℝ)) :
    (k : ℝ) * resPeriod / ((201 / 100) * (m : ℝ)) ≤ resKappa m k := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriod_pos
  have hk0 : 0 ≤ (k : ℝ) * resPeriod := by positivity
  have hsqrt := sqrt_bound_of_le hm hk0 hk
  have hsqrt_ge : (k : ℝ) * resPeriod ≤ Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) := by
    rw [Real.le_sqrt hk0 (by positivity)]; linarith
  have hsqrt_pos : 0 < Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  unfold resKappa
  set s := Real.sqrt (441 + ((k : ℝ) * resPeriod) ^ 2) with hs
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- `kP · (4.01 m⁴/s + 2) ≤ 2m³ · 2.01 m`
  have hfrac : (401 / 100 : ℝ) * (m : ℝ) ^ 4 / s + 2 = ((401 / 100 : ℝ) * (m : ℝ) ^ 4 + 2 * s) / s := by
    field_simp
  rw [hfrac, ← mul_div_assoc, div_le_iff₀ hsqrt_pos]
  have h1 : (k : ℝ) * resPeriod * ((401 / 100 : ℝ) * (m : ℝ) ^ 4 + 2 * s) ≤
      s * ((401 / 100 : ℝ) * (m : ℝ) ^ 4 + 2 * s) := by
    apply mul_le_mul_of_nonneg_right hsqrt_ge; positivity
  have h2 : 2 * s ≤ (1 / 100 : ℝ) * (m : ℝ) ^ 4 := by
    have hm3 : (1000 : ℝ) ^ 3 ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hmR 3
    have hm4 : (1 / 100 : ℝ) * (m : ℝ) ^ 4 = (m : ℝ) * ((1 / 100) * (m : ℝ) ^ 3) := by ring
    rw [hm4]
    nlinarith [mul_le_mul_of_nonneg_left hm3 (by positivity : (0 : ℝ) ≤ m)]
  nlinarith

/-- **Nonnegativity condition**: on a period with `kP ≥ 1.44 m` (and `(k+1)P ≤ m²`), large
values force `|cos(λu/2)| ≥ √2/2`. -/
theorem resPoly_nonneg_period {m : ℕ} (hm : 1000 ≤ m) {k : ℕ}
    (hk : (36 / 25) * (m : ℝ) ≤ (k : ℝ) * resPeriod)
    (hk' : ((k : ℝ) + 1) * resPeriod ≤ (m : ℝ) ^ 2) {u : ℝ}
    (hu : u ∈ Icc ((k : ℝ) * resPeriod) (((k : ℝ) + 1) * resPeriod))
    (hlarge : 4 * (m : ℝ) ^ 3 ≤ ‖resPoly m u‖) :
    Real.sqrt 2 / 2 ≤ |Real.cos (resLam * u / 2)| := by
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hP := resPeriod_pos
  have hu0 : 0 ≤ u := le_trans (by positivity) hu.1
  have hum : u ≤ (m : ℝ) ^ 2 := le_trans hu.2 hk'
  have hu1 : (36 / 25) * (m : ℝ) ≤ u := le_trans hk hu.1
  obtain ⟨-, hhi⟩ := resBlock_envelope (by omega) hu0 hum
  rw [norm_resPoly] at hlarge
  have hsqrt_ge : (36 / 25) * (m : ℝ) ≤ Real.sqrt (441 + u ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; nlinarith
  have hsqrt_pos : 0 < Real.sqrt (441 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hdiv : (401 / 100 : ℝ) * (m : ℝ) ^ 4 / Real.sqrt (441 + u ^ 2) ≤
      (401 / 100 : ℝ) * (m : ℝ) ^ 4 / ((36 / 25) * (m : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt_ge
  have hdiv' : (401 / 100 : ℝ) * (m : ℝ) ^ 4 / ((36 / 25) * (m : ℝ)) =
      (401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ 3 := by field_simp
  have hB : ‖resBlock m u‖ ≤ (401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ 3 + 2 := by linarith
  have hcos0 : 0 ≤ |Real.cos (resLam * u / 2)| := abs_nonneg _
  have hs2 := sqrt_two_lt
  by_contra hcon
  push Not at hcon
  have : 2 * |Real.cos (resLam * u / 2)| * ‖resBlock m u‖ <
      2 * (Real.sqrt 2 / 2) * ((401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ 3 + 2) := by
    have hBn : 0 ≤ ‖resBlock m u‖ := norm_nonneg _
    have hpos : 0 < (401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ 3 + 2 := by positivity
    calc 2 * |Real.cos (resLam * u / 2)| * ‖resBlock m u‖
        ≤ 2 * |Real.cos (resLam * u / 2)| * ((401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ 3 + 2) := by
          gcongr
      _ < 2 * (Real.sqrt 2 / 2) * ((401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ 3 + 2) := by
          gcongr
  have hC := mul_lt_mul_of_pos_right hs2
    (by positivity : (0 : ℝ) < (401 / 100 : ℝ) * (25 / 36) * (m : ℝ) ^ 3 + 2)
  have hm3 : (1000 : ℝ) ^ 3 ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hmR 3
  nlinarith

end

end RHTower
