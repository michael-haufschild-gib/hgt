import GaloisForLFunctions.RHTower.WeilCriticalEndpointRigidity
import GaloisForLFunctions.RHTower.ZetaNotchShiftedPoleTest

/-!
# Weil-cone rigidity under absolute convergence at `s = 1`

**Theorem** (`eq_zero_of_positiveDefinite_neg_nullPotential_of_sqrt_summable`). Let `v : ℕ → ℝ`
with `v(0) = v(1) = 0` and `|v(n)| ≤ 2 log n + A`, and suppose `Σ_n |v(n)| n^{−1/2} < ∞`. If `−ψ_v`
is positive definite, then `v = 0`.

**Corollary** (`eq_vonMangoldt_of_weilPositiveFull_of_summable_div`). A full-cone Weil-positive
`lam` with `Σ_n |lam(n) − Λ(n)|/n < ∞` equals `Λ`. So the Dirichlet series of the deviation of any
second point of the Weil cone diverges absolutely at `s = 1`.

**Proof.** Run the notch at scale `L ≥ 32` with truncation `N = ⌈(1 + L)²⌉`.
* Pairing: the shifted-pole test (poles of the Gamma weight at `±2i`) needs only
  `Σ |v(n)| n^{−3/4} < ∞` and gives `Σ_n v(n) Re M_r(log n) ≤ 0`.
* Tail: `‖M_r(y)‖ ≤ C (1 + L) e^{−y}`, so the part beyond `N` is `≤ C T_N`, where
  `T_N = Σ_{n>N} |v(n)| n^{−1/2} → 0`.
* Defect: `M_r = M_Ω − M_{1−r}` with `‖M_{1−r}‖ ≤ C/(2 + L)`, against `Σ_{n≤N}|v(n)| = o(L)`.
* Finite part: the endpoint envelope gives errors `D Σ_{n≤N} |v(n)| (1 + log n) n^{−1/2}`, which is
  `o(log L)` because `Σ |v(n)| n^{−1/2}` converges (split at a fixed `K` with small tail).
* The main term `Y_N e_P 2e^{−1} log(L − 1)` therefore beats every error unless `Y ≤ 0`, and the
  fibre limit gives `v(n₀) = 0`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable

variable {P : Finset ℕ}

/-! ## Splitting the finite masses at a fixed height -/

section Split

variable {v : ℕ → ℝ}

theorem sum_range_eq_add_tail (f : ℕ → ℝ) {K N : ℕ} (hKN : K ≤ N) :
    ∑ n ∈ Finset.range (N + 1), f n =
      ∑ n ∈ Finset.range (K + 1), f n + ∑ i ∈ Finset.range (N - K), f (i + (K + 1)) := by
  rw [← Finset.sum_range_add_sum_Ico f (by omega : K + 1 ≤ N + 1), Finset.sum_Ico_eq_sum_range]
  congr 1
  rw [show N + 1 - (K + 1) = N - K by omega]
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm]

theorem sum_tail_le_sqrtTail (hs0 : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹) (K m : ℕ) :
    ∑ i ∈ Finset.range m, |v (i + (K + 1))| * (Real.sqrt ((i + (K + 1) : ℕ) : ℝ))⁻¹ ≤
      sqrtTail v K := by
  have hs' := (summable_nat_add_iff (K + 1)).mpr hs0
  exact hs'.sum_le_tsum _ fun i _ => by positivity

/-- `Σ_{n≤N} |v(n)| ≤ √K S₀ + √N T_K` for `K ≤ N`. -/
theorem sum_range_abs_le_split (hv0 : v 0 = 0)
    (hs0 : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹) {K N : ℕ} (hKN : K ≤ N) :
    ∑ n ∈ Finset.range (N + 1), |v n| ≤
      Real.sqrt K * ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ + Real.sqrt N * sqrtTail v K := by
  rw [sum_range_eq_add_tail _ hKN]
  have hpt : ∀ n : ℕ, n ≤ N → |v n| ≤ Real.sqrt N * (|v n| * (Real.sqrt n)⁻¹) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · rw [hv0, abs_zero]; simp
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
    have hle : Real.sqrt n ≤ Real.sqrt N := Real.sqrt_le_sqrt (by exact_mod_cast hn)
    calc |v n| = Real.sqrt n * (|v n| * (Real.sqrt n)⁻¹) := by field_simp
      _ ≤ Real.sqrt N * (|v n| * (Real.sqrt n)⁻¹) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
  have h1 : ∑ n ∈ Finset.range (K + 1), |v n| ≤
      Real.sqrt K * ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ := by
    calc ∑ n ∈ Finset.range (K + 1), |v n|
        ≤ ∑ n ∈ Finset.range (K + 1), Real.sqrt K * (|v n| * (Real.sqrt n)⁻¹) :=
          Finset.sum_le_sum fun n hn => by
            have : n ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
            rcases Nat.eq_zero_or_pos n with rfl | hn0
            · rw [hv0, abs_zero]; simp
            have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
            have hle : Real.sqrt n ≤ Real.sqrt K := Real.sqrt_le_sqrt (by exact_mod_cast this)
            calc |v n| = Real.sqrt n * (|v n| * (Real.sqrt n)⁻¹) := by field_simp
              _ ≤ Real.sqrt K * (|v n| * (Real.sqrt n)⁻¹) :=
                  mul_le_mul_of_nonneg_right hle (by positivity)
      _ = Real.sqrt K * ∑ n ∈ Finset.range (K + 1), |v n| * (Real.sqrt n)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ Real.sqrt K * ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ :=
          mul_le_mul_of_nonneg_left (hs0.sum_le_tsum _ fun n _ => by positivity) (by positivity)
  have h2 : ∑ i ∈ Finset.range (N - K), |v (i + (K + 1))| ≤ Real.sqrt N * sqrtTail v K := by
    calc ∑ i ∈ Finset.range (N - K), |v (i + (K + 1))|
        ≤ ∑ i ∈ Finset.range (N - K), Real.sqrt N *
            (|v (i + (K + 1))| * (Real.sqrt ((i + (K + 1) : ℕ) : ℝ))⁻¹) :=
          Finset.sum_le_sum fun i hi => hpt _ (by have := Finset.mem_range.mp hi; omega)
      _ = Real.sqrt N * ∑ i ∈ Finset.range (N - K),
            |v (i + (K + 1))| * (Real.sqrt ((i + (K + 1) : ℕ) : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ Real.sqrt N * sqrtTail v K :=
          mul_le_mul_of_nonneg_left (sum_tail_le_sqrtTail hs0 K _) (Real.sqrt_nonneg _)
  linarith

/-- `Σ_{n≤N} |v(n)|(1 + log n) n^{−1/2} ≤ (1 + log K) S₀ + (1 + log N) T_K` for `K ≤ N`. -/
theorem sum_range_weight_le_split (hs0 : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹)
    {K N : ℕ} (hKN : K ≤ N) :
    ∑ n ∈ Finset.range (N + 1), |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) ≤
      (1 + Real.log K) * ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ +
        (1 + Real.log N) * sqrtTail v K := by
  rw [sum_range_eq_add_tail _ hKN]
  have hlog : ∀ n M : ℕ, n ≤ M → Real.log n ≤ Real.log M := by
    intro n M h
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp only [Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg M
    exact Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast h)
  have h1 : ∑ n ∈ Finset.range (K + 1), |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) ≤
      (1 + Real.log K) * ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ := by
    calc ∑ n ∈ Finset.range (K + 1), |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹)
        ≤ ∑ n ∈ Finset.range (K + 1), (1 + Real.log K) * (|v n| * (Real.sqrt n)⁻¹) :=
          Finset.sum_le_sum fun n hn => by
            have h := hlog n K (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
            have : 0 ≤ |v n| * (Real.sqrt n)⁻¹ := by positivity
            calc |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹)
                = (1 + Real.log n) * (|v n| * (Real.sqrt n)⁻¹) := by ring
              _ ≤ (1 + Real.log K) * (|v n| * (Real.sqrt n)⁻¹) :=
                  mul_le_mul_of_nonneg_right (by linarith) this
      _ = (1 + Real.log K) * ∑ n ∈ Finset.range (K + 1), |v n| * (Real.sqrt n)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ (1 + Real.log K) * ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ :=
          mul_le_mul_of_nonneg_left (hs0.sum_le_tsum _ fun n _ => by positivity)
            (by have := Real.log_natCast_nonneg K; linarith)
  have h2 : ∑ i ∈ Finset.range (N - K), |v (i + (K + 1))| *
      ((1 + Real.log ((i + (K + 1) : ℕ) : ℝ)) * (Real.sqrt ((i + (K + 1) : ℕ) : ℝ))⁻¹) ≤
      (1 + Real.log N) * sqrtTail v K := by
    calc ∑ i ∈ Finset.range (N - K), |v (i + (K + 1))| *
          ((1 + Real.log ((i + (K + 1) : ℕ) : ℝ)) * (Real.sqrt ((i + (K + 1) : ℕ) : ℝ))⁻¹)
        ≤ ∑ i ∈ Finset.range (N - K), (1 + Real.log N) *
            (|v (i + (K + 1))| * (Real.sqrt ((i + (K + 1) : ℕ) : ℝ))⁻¹) :=
          Finset.sum_le_sum fun i hi => by
            have h := hlog (i + (K + 1)) N (by have := Finset.mem_range.mp hi; omega)
            have : 0 ≤ |v (i + (K + 1))| * (Real.sqrt ((i + (K + 1) : ℕ) : ℝ))⁻¹ := by positivity
            calc |v (i + (K + 1))| * ((1 + Real.log ((i + (K + 1) : ℕ) : ℝ)) *
                  (Real.sqrt ((i + (K + 1) : ℕ) : ℝ))⁻¹)
                = (1 + Real.log ((i + (K + 1) : ℕ) : ℝ)) *
                    (|v (i + (K + 1))| * (Real.sqrt ((i + (K + 1) : ℕ) : ℝ))⁻¹) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) this
      _ = (1 + Real.log N) * ∑ i ∈ Finset.range (N - K),
            |v (i + (K + 1))| * (Real.sqrt ((i + (K + 1) : ℕ) : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (1 + Real.log N) * sqrtTail v K :=
          mul_le_mul_of_nonneg_left (sum_tail_le_sqrtTail hs0 K _)
            (by have := Real.log_natCast_nonneg N; linarith)
  linarith

end Split

/-! ## The scale family with vanishing relative error -/

/-- **From the scale family to the sign, relative form**: if for every `ε > 0` and all large `L`
some truncation `Y_F` has `Y ≤ Y_F + τ(L)` with `τ(L) → 0`, and `Y_F ≥ 0` forces
`Y_F e 2e^{−1} log(L − 1) ≤ ε log(L − 1)`, then `Y ≤ 0`. -/
theorem nonpos_of_scale_family_relative {Y e : ℝ} {τ : ℝ → ℝ} (he : 0 < e)
    (hτ : Tendsto τ atTop (𝓝 0))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop, ∃ YF : ℝ, Y ≤ YF + τ L ∧
      (0 ≤ YF → YF * e * (2 * Real.exp (-1) * Real.log (L - 1)) ≤ ε * Real.log (L - 1))) :
    Y ≤ 0 := by
  by_contra hY
  push Not at hY
  set ε : ℝ := Y * e * Real.exp (-1) / 2 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨L, hL, hτL, hL3⟩ := ((h ε hε0).and ((hτ.eventually_le_const (by linarith :
    (0 : ℝ) < Y / 2)).and (eventually_ge_atTop 3))).exists
  obtain ⟨YF, h1, h2⟩ := hL
  have hYF : Y / 2 ≤ YF := by linarith
  have hlog : 0 < Real.log (L - 1) := Real.log_pos (by linarith)
  have h3 := h2 (by linarith)
  have h4 : Y / 2 * e * (2 * Real.exp (-1) * Real.log (L - 1)) ≤
      YF * e * (2 * Real.exp (-1) * Real.log (L - 1)) := by
    have := Real.exp_pos (-1)
    gcongr
  have h5 : Y / 2 * e * (2 * Real.exp (-1) * Real.log (L - 1)) = 2 * ε * Real.log (L - 1) := by
    rw [hε]; ring
  nlinarith

/-! ## The key inequality -/

theorem inv_one_add_bounds {L : ℝ} (hL : 32 ≤ L) :
    ((L / 2) ^ (4 + 1))⁻¹ + Real.exp (-(L ^ 2 / 8)) + 8 * Real.exp (-(L ^ 2 / 256)) ≤
      133 / (1 + L) ∧
    Real.exp (-(L - 16) ^ 2) + Real.exp (-L ^ 2) ≤ 2 / (1 + L) := by
  have hL0 : 0 < L := by linarith
  have h1L : 0 < 1 + L := by linarith
  have hexp_le : ∀ x : ℝ, 0 ≤ x → Real.exp (-x) ≤ (1 + x)⁻¹ := fun x hx => by
    rw [Real.exp_neg]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp x])
  have hA : ((L / 2) ^ (4 + 1))⁻¹ ≤ 4 / (1 + L) := by
    have h2 : L / 2 ≤ (L / 2) ^ (4 + 1) := le_self_pow₀ (by linarith) (by norm_num)
    calc ((L / 2) ^ (4 + 1))⁻¹ ≤ (L / 2)⁻¹ := inv_anti₀ (by positivity) h2
      _ = 2 / L := by rw [inv_div]
      _ ≤ 4 / (1 + L) := by rw [div_le_div_iff₀ hL0 h1L]; linarith
  have hB : Real.exp (-(L ^ 2 / 8)) ≤ 1 / (1 + L) := by
    refine (hexp_le _ (by positivity)).trans ?_
    rw [one_div]; exact inv_anti₀ h1L (by nlinarith)
  have hC : Real.exp (-(L ^ 2 / 256)) ≤ 16 / (1 + L) := by
    refine (hexp_le _ (by positivity)).trans ?_
    rw [inv_le_comm₀ (by positivity) (by positivity), inv_div, div_le_iff₀ (by norm_num)]
    nlinarith
  have hD : Real.exp (-(L - 16) ^ 2) ≤ 1 / (1 + L) := by
    refine (hexp_le _ (by positivity)).trans ?_
    rw [one_div]; exact inv_anti₀ h1L (by nlinarith)
  have hE : Real.exp (-L ^ 2) ≤ 1 / (1 + L) := by
    have : Real.exp (-L ^ 2) = Real.exp (-(L ^ 2)) := by ring_nf
    rw [this]
    refine (hexp_le _ (by positivity)).trans ?_
    rw [one_div]; exact inv_anti₀ h1L (by nlinarith)
  constructor
  · have : 4 / (1 + L) + 1 / (1 + L) + 8 * (16 / (1 + L)) = 133 / (1 + L) := by ring
    linarith
  · have : 1 / (1 + L) + 1 / (1 + L) = 2 / (1 + L) := by ring
    linarith

/-- The final collection of error terms. -/
theorem abs_error_collect {a c Csh u₁ u₂ u₃ u₄ u₅ : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hC : 0 ≤ Csh)
    (h₁ : 0 ≤ u₁) (h₂ : 0 ≤ u₂) (h₃ : 0 ≤ u₃) (h₄ : 0 ≤ u₄) (h₅ : 0 ≤ u₅) :
    a * (u₁ + u₂) + c * (u₃ + 2 * u₄) + Csh * u₅ ≤
      (a + 2 * c + Csh) * (u₁ + u₂ + u₃ + u₄ + u₅) := by
  have e : (a + 2 * c + Csh) * (u₁ + u₂ + u₃ + u₄ + u₅) - (a * (u₁ + u₂) + c * (u₃ + 2 * u₄) +
      Csh * u₅) = (2 * c + Csh) * (u₁ + u₂) + (a + c + Csh) * u₃ + (a + Csh) * u₄ +
        (a + 2 * c) * u₅ := by ring
  have : 0 ≤ (2 * c + Csh) * (u₁ + u₂) + (a + c + Csh) * u₃ + (a + Csh) * u₄ + (a + 2 * c) * u₅ := by
    positivity
  linarith

/-- `TF/(1 + L) ≤ a + 2T` from `TF ≤ a + √N T` and `√N ≤ 2(1 + L)`. -/
theorem div_one_add_le_split {TF a T L sN : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hTF : TF ≤ a + sN * T) (hsN : sN ≤ 2 * (1 + L)) : TF / (1 + L) ≤ a + 2 * T := by
  have h1L : 0 < 1 + L := by linarith
  rw [div_le_iff₀ h1L]
  have h1 : a ≤ a * (1 + L) := le_mul_of_one_le_right ha (by linarith)
  have h2 : sN * T ≤ 2 * (1 + L) * T := mul_le_mul_of_nonneg_right hsN hT
  nlinarith

/-- The small error terms of the key inequality, collected against `TF/(1 + L)`. -/
theorem abs_small_errors_le {L TF CU C₁ C₂ Cdf : ℝ} (hL : 32 ≤ L) (hTF0 : 0 ≤ TF) (hCU0 : 0 ≤ CU)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂) (hCdf0 : 0 ≤ Cdf) :
    CU * TF * (((L / 2) ^ (4 + 1))⁻¹ + Real.exp (-(L ^ 2 / 8)) + 8 * Real.exp (-(L ^ 2 / 256))) ≤
        133 * CU * (TF / (1 + L)) ∧
      TF * (C₁ * Real.exp (-(L - 16) ^ 2) + C₂ * Real.exp (-L ^ 2)) ≤
        2 * (C₁ + C₂) * (TF / (1 + L)) ∧
      Cdf / (2 + L) * TF ≤ Cdf * (TF / (1 + L)) := by
  have h1L : 0 < 1 + L := by linarith
  obtain ⟨hsmall1, hsmall2⟩ := inv_one_add_bounds hL
  refine ⟨?_, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hsmall1 (mul_nonneg hCU0 hTF0)
    have e : CU * TF * (133 / (1 + L)) = 133 * CU * (TF / (1 + L)) := by ring
    linarith
  · have he1 : Real.exp (-(L - 16) ^ 2) ≤ 2 / (1 + L) := by
      have := Real.exp_pos (-L ^ 2); linarith
    have he2 : Real.exp (-L ^ 2) ≤ 2 / (1 + L) := by
      have := Real.exp_pos (-(L - 16) ^ 2); linarith
    have e : TF * (C₁ * (2 / (1 + L)) + C₂ * (2 / (1 + L))) = 2 * (C₁ + C₂) * (TF / (1 + L)) := by
      ring
    calc TF * (C₁ * Real.exp (-(L - 16) ^ 2) + C₂ * Real.exp (-L ^ 2))
        ≤ TF * (C₁ * (2 / (1 + L)) + C₂ * (2 / (1 + L))) := by gcongr
      _ = _ := e
  · rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hTF0 h1L (by linarith)) hCdf0

/-- **The key inequality under absolute convergence at `s = 1`.** With `N = ⌈(1 + L)²⌉`, every
scale `L ≥ 32` has a truncation `Y_N` with `Y ≤ Y_N + 3√n₀ T_N`, and for every `K ≤ N`, when
`Y_N ≥ 0`,
`Y_N e_P 2e^{−1} log(L − 1) ≤ A + B ((1 + log K) S₀ + (1 + log N) T_K + √K S₀ + T_K + T_N)`. -/
theorem exists_scale_bound_abs (hP : ∀ p ∈ P, p.Prime) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀)
    {ε : ℝ} (hε : |ε| ≤ 1) {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs0 : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    ∃ A₀ B : ℝ, 0 ≤ A₀ ∧ 0 ≤ B ∧ ∀ L : ℝ, 32 ≤ L → ∃ YF : ℝ,
      ∑' n, v n * mainWeight P ε n₀ n ≤ YF + 3 * Real.sqrt n₀ * sqrtTail v ⌈(1 + L) ^ 2⌉₊ ∧
      (0 ≤ YF → ∀ K : ℕ, K ≤ ⌈(1 + L) ^ 2⌉₊ →
        YF * (∏ p : P, (1 - primeHalf p ^ 2)) * (2 * Real.exp (-1) * Real.log (L - 1)) ≤
          A₀ + B * ((1 + Real.log K) * ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ +
            (1 + Real.log ⌈(1 + L) ^ 2⌉₊) * sqrtTail v K +
            Real.sqrt K * ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ + sqrtTail v K +
            sqrtTail v ⌈(1 + L) ^ 2⌉₊)) := by
  set S₀ : ℝ := ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ with hS₀def
  have hS₀0 : 0 ≤ S₀ := tsum_nonneg fun n => by positivity
  obtain ⟨CU, hCU0, hCU⟩ := exists_critUniform_le 4 7 (by norm_num)
  obtain ⟨D, hD0, hD⟩ := exists_norm_weightedMoment_sub_mainWeight_le_crit hP (K := 7)
    (by norm_num) ε hn₀
  obtain ⟨C₁, C₂, hC₁0, hC₂0, hgen⟩ := exists_sum_re_mixMoment_ge_of hP ε n₀
  obtain ⟨CQ, hCQ0, hQb1, hqb⟩ := exists_notchWeight_bound P ε n₀
  obtain ⟨Csh, hCsh0, hsh⟩ := exists_norm_shiftMoment_le (differentiable_notchWeightC P ε n₀)
    hQb1 (notchWeightC_ofReal P ε n₀)
  obtain ⟨Cdf, hCdf0, hdf⟩ := exists_norm_defectMoment_le hqb
  have hG0 := gaussHalf_nonneg
  set B : ℝ := 2 * D * gaussHalf + 2 * (133 * D * CU * gaussHalf + 2 * (C₁ + C₂) + Cdf) + Csh
    with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨0, B, le_rfl, hB0, fun L hL => ?_⟩
  have hL0 : 0 ≤ L := by linarith
  have h1L : 0 < 1 + L := by linarith
  set N : ℕ := ⌈(1 + L) ^ 2⌉₊ with hNdef
  have hN1 : (1 + L) ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 2 * (1 + L) ^ 2 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (1 + L) ^ 2 by positivity)
    nlinarith
  have hNpos : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := le_trans (by nlinarith) hN1
    exact_mod_cast this
  have hsqN : Real.sqrt N ≤ 2 * (1 + L) := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hsqN' : 1 + L ≤ Real.sqrt N := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; exact hN1
  refine ⟨∑ n ∈ Finset.range (N + 1), v n * mainWeight P ε n₀ n,
    mainWeight_tail_crit hv0 hs0 hε hn₀ N, fun hYF K hKN => ?_⟩
  set q := notchWeight P ε n₀ with hq
  have hqc : Continuous q := continuous_notchWeight P ε n₀
  -- the pairing with the shifted-pole test
  have hs34 : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs0
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hv0]; simp
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)
  have hpair := sum_mul_re_shiftMoment_nonpos hv0 hA ha hs34 hPD L
    (differentiable_notchWeightC P ε n₀) (fun z hz => hQb1 z (by linarith))
    (notchWeightC_ofReal P ε n₀) (notchWeight_nonneg P ε n₀)
  -- the tail of the shifted-pole pairing
  have hm : ∀ n : ℕ, 1 ≤ n → |(shiftMoment L q (Real.log n)).re| ≤
      (Csh * (1 + L)) * (n : ℝ)⁻¹ + 0 * (Real.sqrt n)⁻¹ := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    refine (Complex.abs_re_le_norm _).trans ((hsh L hL0 _ (Real.log_natCast_nonneg n)).trans ?_)
    rw [Real.exp_neg, Real.exp_log hn0, zero_mul, add_zero]
  obtain ⟨-, htail⟩ := pairing_tail_crit hv0 hs0 (by positivity) hm hNpos
  have hTN0 := sqrtTail_nonneg v N
  have htail' : (Csh * (1 + L) * (Real.sqrt N)⁻¹ + 0) * sqrtTail v N ≤ Csh * sqrtTail v N := by
    rw [add_zero]
    refine mul_le_mul_of_nonneg_right ?_ hTN0
    have : (1 + L) * (Real.sqrt N)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; exact hsqN'
    calc Csh * (1 + L) * (Real.sqrt N)⁻¹ = Csh * ((1 + L) * (Real.sqrt N)⁻¹) := by ring
      _ ≤ Csh * 1 := mul_le_mul_of_nonneg_left this hCsh0
      _ = Csh := mul_one _
  -- the defect over the finite range
  have hTF0 : 0 ≤ ∑ n ∈ Finset.range (N + 1), |v n| := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hdefect : ∑ n ∈ Finset.range (N + 1), v n * (defectMoment L q (Real.log n)).re ≤
      Cdf / (2 + L) * ∑ n ∈ Finset.range (N + 1), |v n| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have h := (Complex.abs_re_le_norm _).trans (hdf L hL0 (Real.log n))
    calc v n * (defectMoment L q (Real.log n)).re ≤ |v n| * |(defectMoment L q (Real.log n)).re| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ |v n| * (Cdf / (2 + L)) := mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = Cdf / (2 + L) * |v n| := by ring
  have hsplit : ∑ n ∈ Finset.range (N + 1), v n * (mixMoment L q (Real.log n)).re =
      ∑ n ∈ Finset.range (N + 1), v n * (shiftMoment L q (Real.log n)).re +
        ∑ n ∈ Finset.range (N + 1), v n * (defectMoment L q (Real.log n)).re := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [shiftMoment_eq_sub L hqc hqb, Complex.sub_re]
    ring
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
  -- the error bookkeeping
  set SF := ∑ n ∈ Finset.range (N + 1), |v n| * ((1 + Real.log n) * (Real.sqrt n)⁻¹) with hSF
  set TF := ∑ n ∈ Finset.range (N + 1), |v n| with hTF
  have hSFb := sum_range_weight_le_split hs0 hKN
  have hTFb := sum_range_abs_le_split hv0 hs0 hKN
  have hTK0 := sqrtTail_nonneg v K
  -- `TF/(1 + L) ≤ √K S₀ + 2 T_K`
  have hTFL : TF / (1 + L) ≤ Real.sqrt K * S₀ + 2 * sqrtTail v K :=
    div_one_add_le_split hL0 (by positivity) hTK0 hTFb hsqN
  obtain ⟨hsm1, hsm2, hsm3⟩ := abs_small_errors_le hL hTF0 hCU0 hC₁0 hC₂0 hCdf0
  have herr : errConst SF (CU * TF) L 4 ≤ 2 * SF + 133 * CU * (TF / (1 + L)) := by
    unfold errConst; linarith only [hsm1]
  have hint := mul_le_mul_of_nonneg_left (hEb.trans (mul_le_mul_of_nonneg_right herr hG0)) hD0
  -- combine
  set c : ℝ := 133 * D * CU * gaussHalf + 2 * (C₁ + C₂) + Cdf with hc
  have hmain : (∑ n ∈ Finset.range (N + 1), v n * mainWeight P ε n₀ n) *
      (∏ p : P, (1 - primeHalf p ^ 2)) * (2 * Real.exp (-1) * Real.log (L - 1)) ≤
      2 * D * gaussHalf * SF + c * (TF / (1 + L)) + Csh * sqrtTail v N := by
    have e1 : D * ((2 * SF + 133 * CU * (TF / (1 + L))) * gaussHalf) =
        2 * D * gaussHalf * SF + 133 * D * CU * gaussHalf * (TF / (1 + L)) := by ring
    have e2 : c * (TF / (1 + L)) = 133 * D * CU * gaussHalf * (TF / (1 + L)) +
        2 * (C₁ + C₂) * (TF / (1 + L)) + Cdf * (TF / (1 + L)) := by rw [hc]; ring
    linarith only [hfin, hpair, htail, htail', hdefect, hsplit, hint, hsm2, hsm3, e1, e2]
  have hSF0 : 0 ≤ SF := Finset.sum_nonneg fun n _ => by
    have := Real.log_natCast_nonneg n
    positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hlogK := Real.log_natCast_nonneg K
  have hlogN := Real.log_natCast_nonneg N
  have hstep : 2 * D * gaussHalf * SF + c * (TF / (1 + L)) + Csh * sqrtTail v N ≤
      2 * D * gaussHalf * ((1 + Real.log K) * S₀ + (1 + Real.log N) * sqrtTail v K) +
        c * (Real.sqrt K * S₀ + 2 * sqrtTail v K) + Csh * sqrtTail v N := by
    have h1 := mul_le_mul_of_nonneg_left hSFb (by positivity : (0 : ℝ) ≤ 2 * D * gaussHalf)
    have h2 := mul_le_mul_of_nonneg_left hTFL hc0
    linarith only [h1, h2]
  have hcol := abs_error_collect (a := 2 * D * gaussHalf) (c := c) (Csh := Csh)
    (u₁ := (1 + Real.log K) * S₀) (u₂ := (1 + Real.log N) * sqrtTail v K)
    (u₃ := Real.sqrt K * S₀) (u₄ := sqrtTail v K) (u₅ := sqrtTail v N) (by positivity) hc0 hCsh0
    (by positivity) (by positivity) (by positivity) hTK0 hTN0
  have hBeq : B = 2 * D * gaussHalf + 2 * c + Csh := by rw [hB, hc]
  rw [hBeq, zero_add]
  linarith only [hmain, hstep, hcol]

/-! ## The theorem -/

theorem one_add_log_ceil_le {L : ℝ} (hL : 32 ≤ L) :
    1 + Real.log (⌈(1 + L) ^ 2⌉₊ : ℕ) ≤ 4 * Real.log (L - 1) := by
  have hN : ((⌈(1 + L) ^ 2⌉₊ : ℕ) : ℝ) ≤ 2 * (1 + L) ^ 2 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (1 + L) ^ 2 by positivity)
    nlinarith
  have hN1 : (1 : ℝ) ≤ ((⌈(1 + L) ^ 2⌉₊ : ℕ) : ℝ) := le_trans (by nlinarith) (Nat.le_ceil _)
  have h1 : Real.log (⌈(1 + L) ^ 2⌉₊ : ℕ) ≤ Real.log (2 * (1 + L) ^ 2) :=
    Real.log_le_log (by linarith) hN
  have h2 : Real.log (2 * (1 + L) ^ 2) = Real.log 2 + 2 * Real.log (1 + L) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have h3 : Real.log (1 + L) ≤ Real.log 2 + Real.log (L - 1) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have h4 : 3 ≤ Real.log (L - 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 3 < 21 := by
      have := Real.exp_one_lt_d9
      have e3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have hx : Real.exp 1 ^ 3 < (2.7182818286 : ℝ) ^ 3 :=
        pow_lt_pow_left₀ this (Real.exp_pos 1).le (by norm_num)
      have hy : (2.7182818286 : ℝ) ^ 3 < 21 := by norm_num
      rw [e3]; linarith
    linarith
  linarith

theorem tendsto_sqrtTail_ceil_sq (v : ℕ → ℝ) (c : ℝ) :
    Tendsto (fun L : ℝ => c * sqrtTail v ⌈(1 + L) ^ 2⌉₊) atTop (𝓝 0) := by
  have h1 : Tendsto (fun L : ℝ => (1 + L) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have h2 := ((tendsto_sqrtTail v).comp (tendsto_nat_ceil_atTop.comp h1)).const_mul c
  rw [mul_zero] at h2
  exact h2

/-- **Weil-cone rigidity under absolute convergence at `s = 1`.** If `v(0) = v(1) = 0`,
`|v(n)| ≤ 2 log n + A`, `Σ_n |v(n)| n^{−1/2} < ∞`, and `−ψ_v` is positive definite, then
`v = 0`. -/
theorem eq_zero_of_positiveDefinite_neg_nullPotential_of_sqrt_summable {v : ℕ → ℝ}
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs0 : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    v = 0 := by
  refine eq_zero_of_forall_mainWeight_nonpos hv0 hv1 hs0 fun y n₀ hn₀2 hy ε hε => ?_
  have hP : ∀ p ∈ primesUpTo y, p.Prime := prime_of_mem_primesUpTo
  have hεabs : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> simp
  obtain ⟨A₀, B, hA₀, hB, hE⟩ := exists_scale_bound_abs hP (isSmoothOver_primesUpTo hn₀2 hy)
    hεabs hv0 hA ha hs0 hPD
  set S₀ : ℝ := ∑' n : ℕ, |v n| * (Real.sqrt n)⁻¹ with hS₀
  have hS₀0 : 0 ≤ S₀ := tsum_nonneg fun n => by positivity
  refine nonpos_of_scale_family_relative (eulerProduct_pos hP)
    (tendsto_sqrtTail_ceil_sq v (3 * Real.sqrt n₀)) fun η hη => ?_
  -- a fixed height `K` with small tail
  obtain ⟨K, hK⟩ := ((tendsto_sqrtTail v).eventually_le_const
    (show (0 : ℝ) < η / (16 * B + 1) by positivity)).exists
  set CK : ℝ := A₀ + B * ((1 + Real.log K) * S₀ + Real.sqrt K * S₀ + sqrtTail v K + S₀) with hCK
  have hlogL : Tendsto (fun L : ℝ => Real.log (L - 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  filter_upwards [eventually_ge_atTop (32 : ℝ), eventually_ge_atTop (K : ℝ),
    hlogL.eventually_ge_atTop (2 * CK / η)] with L hL32 hLK hlog
  obtain ⟨YF, h1, h2⟩ := hE L hL32
  refine ⟨YF, h1, fun hYF => ?_⟩
  have hKN : K ≤ ⌈(1 + L) ^ 2⌉₊ := by
    have : (K : ℝ) ≤ (1 + L) ^ 2 := by nlinarith
    exact_mod_cast this.trans (Nat.le_ceil _)
  have hb := h2 hYF K hKN
  have hTN := sqrtTail_le hs0 ⌈(1 + L) ^ 2⌉₊
  have hTK0 := sqrtTail_nonneg v K
  have hlogN := one_add_log_ceil_le hL32
  have hlog0 : 0 < Real.log (L - 1) := Real.log_pos (by linarith)
  -- the tail part is at most `η/4 · log(L − 1)`
  have hpart : B * ((1 + Real.log (⌈(1 + L) ^ 2⌉₊ : ℕ)) * sqrtTail v K) ≤
      η / 4 * Real.log (L - 1) := by
    have h16 : 16 * B * sqrtTail v K ≤ η := by
      have h := mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℝ) ≤ 16 * B + 1)
      rw [mul_div_cancel₀ _ (by positivity)] at h
      nlinarith
    calc B * ((1 + Real.log (⌈(1 + L) ^ 2⌉₊ : ℕ)) * sqrtTail v K)
        ≤ B * ((4 * Real.log (L - 1)) * sqrtTail v K) := by gcongr
      _ = (16 * B * sqrtTail v K) / 4 * Real.log (L - 1) := by ring
      _ ≤ η / 4 * Real.log (L - 1) := by gcongr
  -- the constant part is at most `η/2 · log(L − 1)`
  have hconst : CK ≤ η / 2 * Real.log (L - 1) := by
    rw [div_le_iff₀ hη] at hlog
    linarith
  have hrest : A₀ + B * ((1 + Real.log K) * S₀ + Real.sqrt K * S₀ + sqrtTail v K +
      sqrtTail v ⌈(1 + L) ^ 2⌉₊) ≤ CK := by
    rw [hCK]
    have := mul_le_mul_of_nonneg_left hTN hB
    nlinarith
  have e : A₀ + B * ((1 + Real.log K) * S₀ + (1 + Real.log (⌈(1 + L) ^ 2⌉₊ : ℕ)) * sqrtTail v K +
      Real.sqrt K * S₀ + sqrtTail v K + sqrtTail v ⌈(1 + L) ^ 2⌉₊) =
      (A₀ + B * ((1 + Real.log K) * S₀ + Real.sqrt K * S₀ + sqrtTail v K +
        sqrtTail v ⌈(1 + L) ^ 2⌉₊)) +
      B * ((1 + Real.log (⌈(1 + L) ^ 2⌉₊ : ℕ)) * sqrtTail v K) := by ring
  rw [e] at hb
  nlinarith

/-- The same with `+ψ_v` positive definite. -/
theorem eq_zero_of_positiveDefinite_nullPotential_of_sqrt_summable {v : ℕ → ℝ}
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) {A : ℝ} (hA : 0 ≤ A) (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs0 : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    v = 0 := by
  have hneg := eq_zero_of_positiveDefinite_neg_nullPotential_of_sqrt_summable
    (v := fun n => -v n) (by simp [hv0]) (by simp [hv1]) hA (fun n => by rw [abs_neg]; exact ha n)
    (by simpa only [abs_neg] using hs0)
    (by simpa only [RHTower.WeilRegular.nullPotential_neg, neg_neg] using hPD)
  funext n
  have := congrFun hneg n
  simpa using this

/-- **Corollary (absolute divergence at `s = 1`).** A full-cone Weil-positive `lam` with
`Σ_n |lam(n) − Λ(n)|/n < ∞` equals `Λ` on all `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_summable_div {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam)
    (hs : Summable fun n : ℕ => |lam n - ArithmeticFunction.vonMangoldt n| * (n : ℝ)⁻¹) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  set v := RHTower.WeilExcess.weilDeviation lam with hv
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hv1 : v 1 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    RHTower.WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have hsv : Summable fun n : ℕ => |v n| * (Real.sqrt n)⁻¹ := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
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
      positivity
  have h0 := eq_zero_of_positiveDefinite_neg_nullPotential_of_sqrt_summable hv0 hv1 hC0 hC hsv hPD
  intro n hn
  have h := congrFun h0 n
  rw [hv, RHTower.WeilExcess.weilDeviation, if_pos hn, Pi.zero_apply] at h
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h hsq.ne'

end RHTower.WeilAbscissa
