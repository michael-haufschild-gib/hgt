import GaloisForLFunctions.RHTower.WeilAbscissaRigidity
import GaloisForLFunctions.RHTower.ZetaNotchCriticalEnvelope
import GaloisForLFunctions.RHTower.ZetaNotchCriticalPairing
import GaloisForLFunctions.RHTower.ZetaNotchCriticalTail

/-!
# Weil-cone rigidity at the critical abscissa

**Theorem** (`eq_zero_of_positiveDefinite_neg_nullPotential_of_log_summable_crit`). Let `v : ℕ → ℝ`
with `v(0) = v(1) = 0` and `|v(n)| ≤ 2 log n + A`, and suppose `Σ_n |v(n)| (1 + log n) n^{−1/2} < ∞`.
If `−ψ_v` is positive definite, then `v = 0`.

**Corollary** (`eq_vonMangoldt_of_weilPositiveFull_of_log_summable`). A full-cone Weil-positive
`lam` with `Σ_n |lam(n) − Λ(n)| (1 + log n)/n < ∞` equals `Λ`.

**Proof.** Fix `n₀` and the truncation `P = P_y`, and run the mixed `|ζ|²` notch at every scale
`L ≥ 32` with the truncation `N = ⌈(1 + L)⁴⌉`.
* Pairing: the mixed test has double poles at `±i/2`, and its transform decays like
  `(1 + |w|) e^{−|w|/2}`. So `Σ_n v(n) Re M_Ω(log n) ≤ 0` needs exactly
  `Σ |v(n)| (1 + log n) n^{−1/2} < ∞`.
* Tail: past the pole of `ζ`, `‖M_Ω(log n)‖ ≤ C₁ (1 + L²)/n + C₂ n^{−1/2}`. The part beyond `N`
  is `≥ −(C₁ + C₂) S`.
* Finite part: at scale `u` with resonance width `δ = 1/u`, the notch remainder is
  `≤ D (u (1 + log n) n^{−1/2} + U(u))` with `U(u)/u = O(u^{−5})`. Integrated against the scale
  weight, this costs `O(S)` uniformly in `L`, against the main term `Y_N e_P 2e^{−1} log(L − 1)`.
* The main functional differs from its truncation by a tail of `Σ |v(n)| n^{−1/2}`, which tends
  to zero. Hence `Y ≤ 0`, and the fibre limit gives `v(n₀) = 0`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable

variable {P : Finset ℕ}

/-! ## The uniform part of the endpoint weight -/

/-- The uniform part `U(u) = u^{5/2} ((u/8)^{−K} + e^{−u²/128}) + u² e^{−u²/32}` of the endpoint
weight obeys `U(u) ≤ C u · u^{−(M+1)}` on `u ≥ 16` when `K ≥ M + 3`. -/
theorem exists_critUniform_le (M K : ℕ) (hK : M + 3 ≤ K) :
    ∃ CU, 0 ≤ CU ∧ ∀ u : ℝ, 16 ≤ u →
      u ^ (5 / 2 : ℝ) * dualTailFactor u K + u ^ 2 * Real.exp (-(u ^ 2) / 32) ≤
        CU * (u * (u ^ (M + 1))⁻¹) := by
  obtain ⟨B, hB0, hB⟩ := exists_pow_mul_exp_neg_le (M + 3)
  refine ⟨8 ^ K + 2 * B, by positivity, fun u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hB' : u ^ (M + 3) * Real.exp (-(u ^ 2 / 256)) ≤ B := by
    refine le_trans ?_ (hB u hu0.le)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu0.le (by linarith) _) (Real.exp_pos _).le
  have h52 : u ^ (5 / 2 : ℝ) ≤ u ^ 3 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
  have hpM : 0 < u ^ (M + 1) := by positivity
  have hkey : u ^ (M + 1) * u ^ 2 ≤ u ^ (M + 3) := le_of_eq (by ring)
  -- the three pieces, each times `u^{M+1}/u`
  have h1 : u ^ 3 * ((u / 8) ^ K)⁻¹ * u ^ (M + 1) ≤ 8 ^ K * u := by
    rw [div_pow, inv_div]
    have hK' : u ^ (M + 3) ≤ u ^ K := pow_le_pow_right₀ hu1 hK
    have hK0 : 0 < u ^ K := by positivity
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hK0]
    calc u ^ 3 * 8 ^ K * u ^ (M + 1) = 8 ^ K * u * (u ^ (M + 3)) := by ring
      _ ≤ 8 ^ K * u * u ^ K := mul_le_mul_of_nonneg_left hK' (by positivity)
  have h2 : u ^ 3 * Real.exp (-(u ^ 2) / 128) * u ^ (M + 1) ≤ B * u := by
    have he : Real.exp (-(u ^ 2) / 128) ≤ Real.exp (-(u ^ 2 / 256)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc u ^ 3 * Real.exp (-(u ^ 2) / 128) * u ^ (M + 1)
        = u * (u ^ (M + 3) * Real.exp (-(u ^ 2) / 128)) := by ring
      _ ≤ u * (u ^ (M + 3) * Real.exp (-(u ^ 2 / 256))) := by gcongr
      _ ≤ u * B := mul_le_mul_of_nonneg_left hB' hu0.le
      _ = B * u := by ring
  have h3 : u ^ 2 * Real.exp (-(u ^ 2) / 32) * u ^ (M + 1) ≤ B * u := by
    have he : Real.exp (-(u ^ 2) / 32) ≤ Real.exp (-(u ^ 2 / 256)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hp : u ^ 2 * u ^ (M + 1) ≤ u * u ^ (M + 3) := by
      calc u ^ 2 * u ^ (M + 1) = 1 * (u ^ (M + 1) * u ^ 2) := by ring
        _ ≤ u * (u ^ (M + 1) * u ^ 2) := mul_le_mul_of_nonneg_right hu1 (by positivity)
        _ = u * u ^ (M + 3) := by ring
    calc u ^ 2 * Real.exp (-(u ^ 2) / 32) * u ^ (M + 1)
        = (u ^ 2 * u ^ (M + 1)) * Real.exp (-(u ^ 2) / 32) := by ring
      _ ≤ (u * u ^ (M + 3)) * Real.exp (-(u ^ 2 / 256)) :=
          mul_le_mul hp he (Real.exp_pos _).le (by positivity)
      _ = u * (u ^ (M + 3) * Real.exp (-(u ^ 2 / 256))) := by ring
      _ ≤ u * B := mul_le_mul_of_nonneg_left hB' hu0.le
      _ = B * u := by ring
  have htot : (u ^ (5 / 2 : ℝ) * dualTailFactor u K + u ^ 2 * Real.exp (-(u ^ 2) / 32)) *
      u ^ (M + 1) ≤ (8 ^ K + 2 * B) * u := by
    have hd : u ^ (5 / 2 : ℝ) * dualTailFactor u K ≤
        u ^ 3 * ((u / 8) ^ K)⁻¹ + u ^ 3 * Real.exp (-(u ^ 2) / 128) := by
      unfold dualTailFactor
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_right h52 (by positivity)
    have := mul_le_mul_of_nonneg_right hd hpM.le
    nlinarith
  rw [← div_eq_mul_inv, mul_div_assoc', le_div_iff₀ hpM]
  linarith

/-! ## The scale error at the endpoint -/

/-- The endpoint scale error `Σ_{n∈F} |v(n)| (u (1 + log n) n^{−1/2} + U(u))`. -/
def critErrSum (v : ℕ → ℝ) (F : Finset ℕ) (K : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ F, |v n| * critWeight K u n

theorem measurable_critErrSum (v : ℕ → ℝ) (F : Finset ℕ) (K : ℕ) :
    Measurable (critErrSum v F K) := by
  unfold critErrSum critWeight dualTailFactor
  fun_prop

/-- **Gaussian envelope of the endpoint scale error** on `u > 16`. -/
theorem scaleWeight_div_mul_critErrSum_le {L : ℝ} (hL : 2 ≤ L) (v : ℕ → ℝ) (F : Finset ℕ)
    {K M : ℕ} {CU : ℝ} (hCU : 0 ≤ CU)
    (hU : ∀ u : ℝ, 16 ≤ u → u ^ (5 / 2 : ℝ) * dualTailFactor u K +
      u ^ 2 * Real.exp (-(u ^ 2) / 32) ≤ CU * (u * (u ^ (M + 1))⁻¹)) {u : ℝ} (hu : 16 < u) :
    scaleWeight L u / u * critErrSum v F K u ≤
      errConst (∑ n ∈ F, |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) (CU * ∑ n ∈ F, |v n|) L M *
        Real.exp (-((u - L) ^ 2 / 2)) := by
  have hu0 : 0 < u := by linarith
  set SF := ∑ n ∈ F, |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) with hSF
  set TF := ∑ n ∈ F, |v n| with hTF
  set Uu := u ^ (5 / 2 : ℝ) * dualTailFactor u K + u ^ 2 * Real.exp (-(u ^ 2) / 32) with hUu
  have hSF0 : 0 ≤ SF := Finset.sum_nonneg fun n _ => by
    have := Real.log_natCast_nonneg n
    positivity
  have hTF0 : 0 ≤ TF := Finset.sum_nonneg fun n _ => abs_nonneg _
  set G := Real.exp (-((u - L) ^ 2 / 2)) with hG
  have hG0 : 0 < G := Real.exp_pos _
  have hρ : scaleWeight L u ≤ G := scaleWeight_le_half L u
  have hρ0 := scaleWeight_pos L u
  have hsum : critErrSum v F K u = u * SF + TF * Uu := by
    unfold critErrSum critWeight
    rw [hSF, hTF, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hUu]; ring
  have hpoly := scaleWeight_mul_inv_pow_le hL M hu
  have hUb : scaleWeight L u / u * Uu ≤
      CU * ((((L / 2) ^ (M + 1))⁻¹ + Real.exp (-(L ^ 2 / 8))) * G) := by
    calc scaleWeight L u / u * Uu ≤ scaleWeight L u / u * (CU * (u * (u ^ (M + 1))⁻¹)) :=
          mul_le_mul_of_nonneg_left (hU u hu.le) (div_pos hρ0 hu0).le
      _ = CU * (scaleWeight L u * (u ^ (M + 1))⁻¹) := by field_simp
      _ ≤ CU * ((((L / 2) ^ (M + 1))⁻¹ + Real.exp (-(L ^ 2 / 8))) * G) :=
          mul_le_mul_of_nonneg_left hpoly hCU
  rw [hsum]
  unfold errConst
  have e : scaleWeight L u / u * (u * SF + TF * Uu) =
      scaleWeight L u * SF + TF * (scaleWeight L u / u * Uu) := by field_simp
  rw [e]
  have h1 : scaleWeight L u * SF ≤ G * SF := mul_le_mul_of_nonneg_right hρ hSF0
  have h2 := mul_le_mul_of_nonneg_left hUb hTF0
  have h3 : 0 ≤ CU * TF * (8 * Real.exp (-(L ^ 2 / 256))) * G := by positivity
  nlinarith

/-- **The endpoint scale error integral**. -/
theorem setIntegral_critErrSum_le {L : ℝ} (hL : 2 ≤ L) (v : ℕ → ℝ) (F : Finset ℕ)
    {K M : ℕ} {CU : ℝ} (hCU : 0 ≤ CU)
    (hU : ∀ u : ℝ, 16 ≤ u → u ^ (5 / 2 : ℝ) * dualTailFactor u K +
      u ^ 2 * Real.exp (-(u ^ 2) / 32) ≤ CU * (u * (u ^ (M + 1))⁻¹)) :
    IntegrableOn (fun u => scaleWeight L u / u * critErrSum v F K u) (Ioi 16) ∧
      ∫ u in Ioi 16, scaleWeight L u / u * critErrSum v F K u ≤
        errConst (∑ n ∈ F, |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹))
          (CU * ∑ n ∈ F, |v n|) L M * gaussHalf := by
  set E := errConst (∑ n ∈ F, |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹))
    (CU * ∑ n ∈ F, |v n|) L M with hE
  have hE0 : 0 ≤ E := by
    rw [hE, errConst]
    have h1 : 0 ≤ ∑ n ∈ F, |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) :=
      Finset.sum_nonneg fun n _ => by
        have := Real.log_natCast_nonneg n
        positivity
    have h2 : 0 ≤ CU * ∑ n ∈ F, |v n| :=
      mul_nonneg hCU (Finset.sum_nonneg fun n _ => abs_nonneg _)
    have h3 : 0 < L / 2 := by linarith
    positivity
  have hnn : ∀ u : ℝ, 16 < u → 0 ≤ scaleWeight L u / u * critErrSum v F K u := by
    intro u hu
    refine mul_nonneg (div_pos (scaleWeight_pos L u) (by linarith)).le
      (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (critWeight_nonneg K (by linarith) n))
  have hint : IntegrableOn (fun u => scaleWeight L u / u * critErrSum v F K u) (Ioi 16) := by
    refine ((integrable_gaussShift L).const_mul E).integrableOn.mono' ?_ ?_
    · exact (((Real.continuous_exp.comp (by fun_prop)).measurable.div measurable_id).mul
        (measurable_critErrSum v F K)).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu)]
      exact scaleWeight_div_mul_critErrSum_le hL v F hCU hU hu
  refine ⟨hint, ?_⟩
  calc ∫ u in Ioi 16, scaleWeight L u / u * critErrSum v F K u
      ≤ ∫ u in Ioi 16, E * Real.exp (-((u - L) ^ 2 / 2)) :=
        setIntegral_mono_on hint ((integrable_gaussShift L).const_mul E).integrableOn
          measurableSet_Ioi fun u hu => scaleWeight_div_mul_critErrSum_le hL v F hCU hU hu
    _ = E * ∫ u in Ioi 16, Real.exp (-((u - L) ^ 2 / 2)) := integral_const_mul _ _
    _ ≤ E * gaussHalf := by
        refine mul_le_mul_of_nonneg_left ?_ hE0
        rw [← integral_gaussShift L]
        exact setIntegral_le_integral (integrable_gaussShift L)
          (Eventually.of_forall fun _ => (Real.exp_pos _).le)

/-! ## Truncation at the endpoint -/

section Truncation

variable {v : ℕ → ℝ}

theorem inv_sqrt_le_weight (n : ℕ) :
    (Real.sqrt n)⁻¹ ≤ (1 + Real.log n) * (Real.sqrt n)⁻¹ :=
  le_mul_of_one_le_left (by positivity) (by linarith [Real.log_natCast_nonneg n])

theorem summable_inv_sqrt_of_weight
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) :
    Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹ :=
  Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => mul_le_mul_of_nonneg_left (inv_sqrt_le_weight n) (abs_nonneg _)) hs

/-- The finite masses at the endpoint: `Σ_{n≤N} |v(n)| w(n) ≤ S` and `Σ_{n≤N} |v(n)| ≤ N S`. -/
theorem finite_masses_le_crit (hv0 : v 0 = 0)
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) ≤
        ∑' n : ℕ, |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) ∧
      ∑ n ∈ Finset.range (N + 1), |v n| ≤
        N * ∑' n : ℕ, |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) := by
  have hw0 : ∀ n : ℕ, 0 ≤ |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) := fun n => by
    have := Real.log_natCast_nonneg n
    positivity
  have h1 := hs.sum_le_tsum (Finset.range (N + 1)) fun n _ => hw0 n
  refine ⟨h1, ?_⟩
  have hpt : ∀ n ∈ Finset.range (N + 1), |v n| ≤
      N * (|v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [hv0, abs_zero]; simp
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    have hsq : Real.sqrt n ≤ n := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hlog := Real.log_natCast_nonneg n
    have e : |v n| = |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) *
        (Real.sqrt n / (1 + Real.log n)) := by
      have h1 : (1 + Real.log n) ≠ 0 := by positivity
      rw [mul_assoc, show (1 + Real.log n) * (Real.sqrt n)⁻¹ * (Real.sqrt n / (1 + Real.log n)) = 1
        by field_simp, mul_one]
    calc |v n| = |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) * (Real.sqrt n / (1 + Real.log n)) := e
      _ ≤ |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) * N := by
          refine mul_le_mul_of_nonneg_left ?_ (hw0 n)
          rw [div_le_iff₀ (by linarith)]
          nlinarith
      _ = _ := by ring
  calc ∑ n ∈ Finset.range (N + 1), |v n| ≤ ∑ n ∈ Finset.range (N + 1),
        N * (|v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹)) := Finset.sum_le_sum hpt
    _ = N * ∑ n ∈ Finset.range (N + 1), |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)

/-- The tail `T_N = Σ_{n>N} |v(n)| n^{−1/2}`. -/
def sqrtTail (v : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' i : ℕ, |v (i + (N + 1))| * (Real.sqrt ((i + (N + 1) : ℕ) : ℝ))⁻¹

theorem sqrtTail_nonneg (v : ℕ → ℝ) (N : ℕ) : 0 ≤ sqrtTail v N :=
  tsum_nonneg fun i => by positivity

theorem sqrtTail_le (hs0 : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹) (N : ℕ) :
    sqrtTail v N ≤ ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ := by
  unfold sqrtTail
  rw [← hs0.sum_add_tsum_nat_add (N + 1)]
  have : 0 ≤ ∑ i ∈ Finset.range (N + 1), |v i| * (Real.sqrt i)⁻¹ :=
    Finset.sum_nonneg fun i _ => by positivity
  linarith

theorem tendsto_sqrtTail (v : ℕ → ℝ) : Tendsto (sqrtTail v) atTop (𝓝 0) := by
  have h := (tendsto_sum_nat_add fun n : ℕ => |v n| * (Real.sqrt n)⁻¹).comp
    (tendsto_add_atTop_nat 1)
  refine h.congr fun N => ?_
  simp only [Function.comp_apply, sqrtTail]

/-- **The pairing tail at the endpoint**: if `|m(n)| ≤ B₁/n + B₂ n^{−1/2}`, the pairing sum is
summable and its part beyond `N` is at least `−(B₁ N^{−1/2} + B₂) S₀`. -/
theorem pairing_tail_crit (hv0 : v 0 = 0) (hs0 : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) {m : ℕ → ℝ}
    (hm : ∀ n : ℕ, 1 ≤ n → |m n| ≤ B₁ * (n : ℝ)⁻¹ + B₂ * (Real.sqrt n)⁻¹) {N : ℕ} (hN : 1 ≤ N) :
    Summable (fun n => v n * m n) ∧
      ∑ n ∈ Finset.range (N + 1), v n * m n -
        (B₁ * (Real.sqrt N)⁻¹ + B₂) * sqrtTail v N ≤ ∑' n, v n * m n := by
  have hinv : ∀ n : ℕ, 1 ≤ n → (n : ℝ)⁻¹ ≤ (Real.sqrt n)⁻¹ := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_anti₀ (Real.sqrt_pos.mpr (by linarith))
      (by rw [Real.sqrt_le_left (by linarith)]; nlinarith)
  have hbound : ∀ n : ℕ, |v n * m n| ≤ (B₁ + B₂) * (|v n| * (Real.sqrt n)⁻¹) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hv0]; simp
    rw [abs_mul]
    have h := hm n hn
    have h1 := mul_le_mul_of_nonneg_left (hinv n hn) hB₁
    calc |v n| * |m n| ≤ |v n| * ((B₁ + B₂) * (Real.sqrt n)⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = (B₁ + B₂) * (|v n| * (Real.sqrt n)⁻¹) := by ring
  have hf : Summable fun n => v n * m n :=
    Summable.of_norm_bounded (hs0.mul_left (B₁ + B₂)) fun n => by
      rw [Real.norm_eq_abs]; exact hbound n
  refine ⟨hf, ?_⟩
  rw [← hf.sum_add_tsum_nat_add (N + 1)]
  have hN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have htail : ∀ i : ℕ, |v (i + (N + 1)) * m (i + (N + 1))| ≤
      (B₁ * (Real.sqrt N)⁻¹ + B₂) *
        (|v (i + (N + 1))| * (Real.sqrt ((i + (N + 1) : ℕ) : ℝ))⁻¹) := by
    intro i
    set n := i + (N + 1) with hn
    have hn1 : 1 ≤ n := by omega
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast (by omega : N ≤ n)
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
    have hn_inv : (n : ℝ)⁻¹ ≤ (Real.sqrt N)⁻¹ * (Real.sqrt n)⁻¹ := by
      rw [← mul_inv]
      refine inv_anti₀ (mul_pos hN0 hsn) ?_
      calc Real.sqrt N * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n :=
            mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hNn) hsn.le
        _ = n := Real.mul_self_sqrt (by linarith)
    rw [abs_mul]
    have h := hm n hn1
    calc |v n| * |m n| ≤ |v n| * (B₁ * (n : ℝ)⁻¹ + B₂ * (Real.sqrt n)⁻¹) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ ≤ |v n| * (B₁ * ((Real.sqrt N)⁻¹ * (Real.sqrt n)⁻¹) + B₂ * (Real.sqrt n)⁻¹) := by
          gcongr
      _ = (B₁ * (Real.sqrt N)⁻¹ + B₂) * (|v n| * (Real.sqrt n)⁻¹) := by ring
  have hs' := (summable_nat_add_iff (N + 1)).mpr hs0
  have hs2 : Summable fun i : ℕ => |v (i + (N + 1)) * m (i + (N + 1))| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) htail (hs'.mul_left _)
  have habs : |∑' i : ℕ, v (i + (N + 1)) * m (i + (N + 1))| ≤
      (B₁ * (Real.sqrt N)⁻¹ + B₂) * sqrtTail v N :=
    calc |∑' i : ℕ, v (i + (N + 1)) * m (i + (N + 1))|
        ≤ ∑' i : ℕ, |v (i + (N + 1)) * m (i + (N + 1))| := abs_tsum_le_tsum_abs hs2
      _ ≤ ∑' i : ℕ, (B₁ * (Real.sqrt N)⁻¹ + B₂) *
            (|v (i + (N + 1))| * (Real.sqrt ((i + (N + 1) : ℕ) : ℝ))⁻¹) :=
          hs2.tsum_le_tsum htail (hs'.mul_left _)
      _ = (B₁ * (Real.sqrt N)⁻¹ + B₂) * sqrtTail v N := by rw [tsum_mul_left]; rfl
  linarith [(abs_le.mp habs).1]

/-- **The main-term tail at the endpoint**: `Σ_n v(n) mainWeight(n) ≤ Σ_{n≤N} v(n) mainWeight(n)
+ 3√n₀ T_N`. -/
theorem mainWeight_tail_crit (hv0 : v 0 = 0) (hs0 : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹)
    {ε : ℝ} (hε : |ε| ≤ 1) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) (N : ℕ) :
    ∑' n, v n * mainWeight P ε n₀ n ≤ ∑ n ∈ Finset.range (N + 1), v n * mainWeight P ε n₀ n +
      3 * Real.sqrt n₀ * sqrtTail v N := by
  have hbound : ∀ n : ℕ, |v n * mainWeight P ε n₀ n| ≤
      3 * Real.sqrt n₀ * (|v n| * (Real.sqrt n)⁻¹) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hv0]; simp
    rw [abs_mul]
    calc |v n| * |mainWeight P ε n₀ n| ≤ |v n| * (3 * Real.sqrt n₀ * (Real.sqrt n)⁻¹) :=
          mul_le_mul_of_nonneg_left (abs_mainWeight_le hε hn₀ hn.ne') (abs_nonneg _)
      _ = _ := by ring
  have hf : Summable fun n => v n * mainWeight P ε n₀ n :=
    Summable.of_norm_bounded (hs0.mul_left _) fun n => by rw [Real.norm_eq_abs]; exact hbound n
  rw [← hf.sum_add_tsum_nat_add (N + 1)]
  have hs' := (summable_nat_add_iff (N + 1)).mpr hs0
  have hs2 : Summable fun i : ℕ => |v (i + (N + 1)) * mainWeight P ε n₀ (i + (N + 1))| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i => hbound _) (hs'.mul_left _)
  have h := le_abs_self (∑' i : ℕ, v (i + (N + 1)) * mainWeight P ε n₀ (i + (N + 1)))
  have h2 : |∑' i : ℕ, v (i + (N + 1)) * mainWeight P ε n₀ (i + (N + 1))| ≤
      3 * Real.sqrt n₀ * sqrtTail v N :=
    calc _ ≤ ∑' i : ℕ, |v (i + (N + 1)) * mainWeight P ε n₀ (i + (N + 1))| :=
          abs_tsum_le_tsum_abs hs2
      _ ≤ ∑' i : ℕ, 3 * Real.sqrt n₀ *
            (|v (i + (N + 1))| * (Real.sqrt ((i + (N + 1) : ℕ) : ℝ))⁻¹) :=
          hs2.tsum_le_tsum (fun i => hbound _) (hs'.mul_left _)
      _ = 3 * Real.sqrt n₀ * sqrtTail v N := by rw [tsum_mul_left]; rfl
  linarith

end Truncation

/-! ## The key inequality at the endpoint -/

/-- **The key inequality at the endpoint.** At every scale `L ≥ 32`, with `N = ⌈(1 + L)⁴⌉`, the
truncated main functional `Y_N` satisfies `Y ≤ Y_N + 3√n₀ T_N`, and
`Y_N e_P 2e^{−1} log(L − 1) ≤ E` when `Y_N ≥ 0`, with `E` independent of `L`. -/
theorem exists_scale_bound_crit (hP : ∀ p ∈ P, p.Prime) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀)
    {ε : ℝ} (hε : |ε| ≤ 1) {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹))
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    ∃ E : ℝ, ∀ L : ℝ, 32 ≤ L → ∃ YF : ℝ,
      ∑' n, v n * mainWeight P ε n₀ n ≤ YF + 3 * Real.sqrt n₀ * sqrtTail v ⌈(1 + L) ^ 4⌉₊ ∧
      (0 ≤ YF → YF * (∏ p : P, (1 - primeHalf p ^ 2)) * (2 * Real.exp (-1) * Real.log (L - 1)) ≤
        E) := by
  set S : ℝ := ∑' n : ℕ, |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by
    have := Real.log_natCast_nonneg n
    positivity
  have hs0 := summable_inv_sqrt_of_weight hs
  set S₀ : ℝ := ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ with hS₀def
  have hS₀S : S₀ ≤ S := hs0.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (inv_sqrt_le_weight n) (abs_nonneg _)) hs
  have hS₀0 : 0 ≤ S₀ := tsum_nonneg fun n => by positivity
  obtain ⟨CU, hCU0, hCU⟩ := exists_critUniform_le 4 7 (by norm_num)
  obtain ⟨D, hD0, hD⟩ := exists_norm_weightedMoment_sub_mainWeight_le_crit hP (K := 7)
    (by norm_num) ε hn₀
  obtain ⟨C₁, C₂, hC₁0, hC₂0, hgen⟩ := exists_sum_re_mixMoment_ge_of hP ε n₀
  obtain ⟨CQ, hCQ0, hQb1, hqb⟩ := exists_notchWeight_bound P ε n₀
  obtain ⟨T₁, T₂, hT₁0, hT₂0, hT⟩ := exists_norm_mixMoment_le_crit
    (differentiable_notchWeightC P ε n₀) hQb1 (notchWeightC_ofReal P ε n₀)
  obtain ⟨B, hB0, hB⟩ := exists_pow_mul_exp_neg_le 4
  set S' : ℝ := (1 + CU) * S with hS'
  have hS'0 : 0 ≤ S' := by positivity
  refine ⟨(T₁ + T₂) * S₀ + D * ((2 * S' + 2 * 3 ^ 4 * S' + 18 * S' * B) * gaussHalf) +
    2 * S * B * (C₁ + C₂), fun L hL => ?_⟩
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨hN1, hN2, hN3⟩ := truncation_bounds hL0 4 (θ := 1 / 2) (by norm_num) (by norm_num)
  set N : ℕ := ⌈(1 + L) ^ 4⌉₊ with hNdef
  refine ⟨∑ n ∈ Finset.range (N + 1), v n * mainWeight P ε n₀ n,
    mainWeight_tail_crit hv0 hs0 hε hn₀ N, fun hYF => ?_⟩
  set q := notchWeight P ε n₀ with hq
  -- the pairing
  have hQb : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖notchWeightC P ε n₀ z‖ ≤ CQ := fun z hz =>
    hQb1 z (by linarith)
  have hsr : Summable fun n : ℕ => |v n| * ((1 + Real.log n) * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    refine hs.congr fun n => ?_
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n)]
  have hpair := sum_mul_re_mixMoment_nonpos_crit hv0 hA ha hsr hPD L
    (differentiable_notchWeightC P ε n₀) hQb (notchWeightC_ofReal P ε n₀) (notchWeight_nonneg P ε n₀)
  -- the tail beyond `N`
  have hm : ∀ n : ℕ, 1 ≤ n → |(mixMoment L q (Real.log n)).re| ≤
      (T₁ * (1 + L ^ 2)) * (n : ℝ)⁻¹ + T₂ * (Real.sqrt n)⁻¹ := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    refine (Complex.abs_re_le_norm _).trans ((hT L hL0 _ (Real.log_natCast_nonneg n)).trans ?_)
    rw [Real.exp_neg, Real.exp_log hn0, show -(Real.log n / 2) = Real.log ((Real.sqrt n)⁻¹) by
      rw [Real.log_inv, Real.log_sqrt hn0.le], Real.exp_log (by positivity)]
  obtain ⟨-, htail⟩ := pairing_tail_crit hv0 hs0 (by positivity) hm hN1
  have hNs : (T₁ * (1 + L ^ 2)) * (Real.sqrt N)⁻¹ ≤ T₁ := by
    have hN3' : (1 + L ^ 2) * (Real.sqrt N)⁻¹ ≤ 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _)]; exact hN3
    calc (T₁ * (1 + L ^ 2)) * (Real.sqrt N)⁻¹ = T₁ * ((1 + L ^ 2) * (Real.sqrt N)⁻¹) := by ring
      _ ≤ T₁ * 1 := mul_le_mul_of_nonneg_left hN3' hT₁0
      _ = T₁ := mul_one _
  have hTN := sqrtTail_le hs0 N
  have hTN0 := sqrtTail_nonneg v N
  -- the finite part
  have hE : ∀ u, 16 ≤ u → (∑ n ∈ Finset.range (N + 1), v n * mainWeight P ε n₀ n) *
      (∏ p : P, (1 - primeHalf p ^ 2)) * (logWindow u).re -
      D * critErrSum v (Finset.range (N + 1)) 7 u ≤
      ∑ n ∈ Finset.range (N + 1), v n * (ZetaNotch.weightedMoment u q (Real.log n)).re := by
    intro u hu
    have h := sum_re_weightedMoment_ge_of_norm_le (u := u) (q := q)
      (c := fun n => mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2))
      (W := critWeight 7 u) (D := D) (fun n hn => hD hu hn) hv0 (Finset.range (N + 1))
    have e : (∑ n ∈ Finset.range (N + 1), v n * mainWeight P ε n₀ n) *
        (∏ p : P, (1 - primeHalf p ^ 2)) = ∑ n ∈ Finset.range (N + 1),
          v n * (mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2)) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun n _ => by ring
    rw [e]; exact h
  obtain ⟨hEint, hEb⟩ := setIntegral_critErrSum_le (show (2 : ℝ) ≤ L by linarith) v
    (Finset.range (N + 1)) hCU0 hCU (K := 7) (M := 4)
  have hfin := hgen (Finset.range (N + 1)) hL hD0 hE hEint hYF
  obtain ⟨hSF, hTF⟩ := finite_masses_le_crit hv0 hs N
  have hTF0 : 0 ≤ ∑ n ∈ Finset.range (N + 1), |v n| := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hTF' : ∑ n ∈ Finset.range (N + 1), |v n| ≤ 2 * (1 + L) ^ 4 * S :=
    hTF.trans (mul_le_mul_of_nonneg_right hN2 hS0)
  have hCTF : CU * ∑ n ∈ Finset.range (N + 1), |v n| ≤ 2 * (1 + L) ^ 4 * S' := by
    have := mul_le_mul_of_nonneg_left hTF' hCU0
    have h1 : 0 ≤ 2 * (1 + L) ^ 4 * S := by positivity
    nlinarith
  have hSF' : ∑ n ∈ Finset.range (N + 1), |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) ≤ S' := by
    have : S ≤ S' := by rw [hS']; nlinarith
    linarith
  have herr := errConst_le hL hB hSF' (mul_nonneg hCU0 hTF0) hCTF hS'0
  have hsmall := smallErr_le hL hB hTF0 hTF' hS0 hC₁0 hC₂0
  have hG0 := gaussHalf_nonneg
  have hDerr : D * (∫ u in Ioi 16, scaleWeight L u / u * critErrSum v (Finset.range (N + 1)) 7 u) ≤
      D * ((2 * S' + 2 * 3 ^ 4 * S' + 18 * S' * B) * gaussHalf) :=
    mul_le_mul_of_nonneg_left (hEb.trans (mul_le_mul_of_nonneg_right herr hG0)) hD0
  have htailb : (T₁ * (1 + L ^ 2) * (Real.sqrt N)⁻¹ + T₂) * sqrtTail v N ≤ (T₁ + T₂) * S₀ := by
    have h1 : T₁ * (1 + L ^ 2) * (Real.sqrt N)⁻¹ + T₂ ≤ T₁ + T₂ := by linarith
    calc (T₁ * (1 + L ^ 2) * (Real.sqrt N)⁻¹ + T₂) * sqrtTail v N ≤ (T₁ + T₂) * sqrtTail v N :=
          mul_le_mul_of_nonneg_right h1 hTN0
      _ ≤ (T₁ + T₂) * S₀ := mul_le_mul_of_nonneg_left hTN (by positivity)
  linarith

/-! ## The theorem -/

/-- **Weil-cone rigidity at the critical abscissa.** If `v(0) = v(1) = 0`,
`|v(n)| ≤ 2 log n + A`, `Σ_n |v(n)| (1 + log n) n^{−1/2} < ∞`, and `−ψ_v` is positive definite,
then `v = 0`. -/
theorem eq_zero_of_positiveDefinite_neg_nullPotential_of_log_summable_crit {v : ℕ → ℝ}
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹))
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    v = 0 := by
  refine eq_zero_of_forall_mainWeight_nonpos hv0 hv1 (summable_inv_sqrt_of_weight hs)
    fun y n₀ hn₀2 hy ε hε => ?_
  have hP : ∀ p ∈ primesUpTo y, p.Prime := prime_of_mem_primesUpTo
  have hεabs : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  obtain ⟨E, hE⟩ := exists_scale_bound_crit hP (isSmoothOver_primesUpTo hn₀2 hy) hεabs hv0 hA ha
    hs hPD
  have hτ : Tendsto (fun L : ℝ => 3 * Real.sqrt n₀ * sqrtTail v ⌈(1 + L) ^ 4⌉₊) atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => (1 + L) ^ 4) atTop atTop :=
      (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
    have h2 := ((tendsto_sqrtTail v).comp (tendsto_nat_ceil_atTop.comp h1)).const_mul
      (3 * Real.sqrt n₀)
    rw [mul_zero] at h2
    exact h2
  exact nonpos_of_scale_family_tendsto (eulerProduct_pos hP) hτ hE

/-- The same with `+ψ_v` positive definite. -/
theorem eq_zero_of_positiveDefinite_nullPotential_of_log_summable_crit {v : ℕ → ℝ}
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹))
    (hPD : PositiveDefiniteOnReal fun y => ((RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    v = 0 := by
  have hneg := eq_zero_of_positiveDefinite_neg_nullPotential_of_log_summable_crit
    (v := fun n => -v n) (by simp [hv0]) (by simp [hv1]) hA (fun n => by rw [abs_neg]; exact ha n)
    (by simpa only [abs_neg] using hs)
    (by simpa only [RHTower.WeilRegular.nullPotential_neg, neg_neg] using hPD)
  funext n
  have := congrFun hneg n
  simpa using this

/-- **Corollary (the critical endpoint of the Weil cone).** A full-cone Weil-positive `lam` with
`Σ_n |lam(n) − Λ(n)| (1 + log n)/n < ∞` equals `Λ` on all `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_log_summable {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam)
    (hs : Summable fun n : ℕ =>
      |lam n - ArithmeticFunction.vonMangoldt n| * ((1 + Real.log n) * (n : ℝ)⁻¹)) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  set v := RHTower.WeilExcess.weilDeviation lam with hv
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hv1 : v 1 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    RHTower.WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have hsv : Summable fun n : ℕ => |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
    · have := Real.log_natCast_nonneg n
      positivity
    rw [hv, RHTower.WeilExcess.weilDeviation]
    split_ifs with h2
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      rw [abs_div, abs_of_pos hsq]
      apply le_of_eq
      have e : (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt hn0.le]
      rw [e]
      field_simp
    · rw [abs_zero, zero_mul]
      have := Real.log_natCast_nonneg n
      positivity
  have h0 := eq_zero_of_positiveDefinite_neg_nullPotential_of_log_summable_crit hv0 hv1 hC0 hC hsv
    hPD
  intro n hn
  have h := congrFun h0 n
  rw [hv, RHTower.WeilExcess.weilDeviation, if_pos hn, Pi.zero_apply] at h
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h hsq.ne'

end RHTower.WeilAbscissa
