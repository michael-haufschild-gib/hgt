import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothWindowContinuousForm

/-!
# The Nine Channels of the Smooth-Window Frobenius Form

Along `ν_X = μ + Π_X + P_X` the smooth form `∫ Ω ν (Φ² ⋆ ν)` splits into nine channels
(`smoothPair_sum_sum`). Each is evaluated by one mechanism:

* `Φ² ⋆ μ = μ ∫Φ² + O(E/τ)` (the Stirling increment bound), so the archimedean diagonal is
  `(∫Φ²) ∫Ω μ²` up to `S M E/s₀`;
* `Φ² ⋆ Π_X = O(√X/τ)`: decay passes through `Φ²`;
* `Φ² ⋆ P_X = −2 C_g` is again a prime polynomial, so every channel ending in `P_X` is a sum of
  cosine integrals `∫ Ω v cos(τ log n)`, each `O((S + 5)(ℓM + K/s₀))` by the half-period shift;
* the two prime–pole channels are bounded by Cauchy–Schwarz against the window mean squares
  `∫ Ω P_X²` and `∫ Ω C_g²`;
* the prime–prime channel is the exact coalescent kernel: the diagonal, the coalescent band, and a
  far / sum-frequency remainder paid by `‖Ω^{(k)}‖₁`.

`smoothPair_nuX_le` bounds the smooth form by the archimedean and prime diagonals, the coalescent
pair sum `coalSum`, and the explicit remainder `channelError`.
-/

open MeasureTheory Real Set Finset Filter
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide RHTower

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

variable {Φ : ℝ → ℝ}

/-! ## 1. Bilinear expansion -/

theorem integrable_PhiSq_sub_mul (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦ2a : Integrable fun x => Φ x ^ 2 * |x|) (hΦc : Continuous Φ) {v : ℝ → ℝ}
    (hvc : Continuous v) {M τ : ℝ} (hvb : ∀ τ', |v τ'| ≤ M * (1 + |τ - τ'|)) :
    Integrable fun τ' => Φ (τ - τ') ^ 2 * v τ' := by
  have hk : Integrable fun τ' => M * (Φ (τ - τ') ^ 2 + Φ (τ - τ') ^ 2 * |τ - τ'|) :=
    ((hΦ2.add hΦ2a).comp_sub_left τ).const_mul M
  refine hk.mono' (by fun_prop) (Eventually.of_forall fun τ' => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc Φ (τ - τ') ^ 2 * |v τ'| ≤ Φ (τ - τ') ^ 2 * (M * (1 + |τ - τ'|)) :=
        mul_le_mul_of_nonneg_left (hvb τ') (sq_nonneg _)
    _ = M * (Φ (τ - τ') ^ 2 + Φ (τ - τ') ^ 2 * |τ - τ'|) := by ring

/-- **Bilinearity of the smooth form** over finite sums of densities of linear growth. -/
theorem smoothPair_sum_sum (hΦc : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦ2a : Integrable fun x => Φ x ^ 2 * |x|) {Ω : ℝ → ℝ} (hΩc : Continuous Ω) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) {u : ι → ℝ → ℝ} {v : κ → ℝ → ℝ} (huc : ∀ i, Continuous (u i))
    (hΩu : ∀ i, Integrable fun τ => Ω τ * u i τ) (hvc : ∀ j, Continuous (v j)) {M : ℝ}
    (hvb : ∀ j τ τ', Ω τ ≠ 0 → |v j τ'| ≤ M * (1 + |τ - τ'|)) :
    smoothPair Φ Ω (fun τ => ∑ i ∈ s, u i τ) (fun τ => ∑ j ∈ t, v j τ)
      = ∑ i ∈ s, ∑ j ∈ t, smoothPair Φ Ω (u i) (v j) := by
  have hI : ∀ i j, Integrable fun τ => Ω τ * u i τ * convSq Φ (v j) τ := fun i j =>
    integrable_window_mul_convSq hΦc hΦ2 hΦ2a hΩc (huc i) (hvc j) (hΩu i) (hvb j)
  have hconv : ∀ τ, Ω τ ≠ 0 → convSq Φ (fun τ => ∑ j ∈ t, v j τ) τ = ∑ j ∈ t, convSq Φ (v j) τ := by
    intro τ hτ
    unfold convSq
    rw [← integral_finsetSum _ fun j _ =>
      integrable_PhiSq_sub_mul hΦ2 hΦ2a hΦc (hvc j) (fun τ' => hvb j τ τ' hτ)]
    exact integral_congr_ae (Eventually.of_forall fun τ' => by simp only [Finset.mul_sum])
  have hpt : ∀ τ, Ω τ * (∑ i ∈ s, u i τ) * convSq Φ (fun τ => ∑ j ∈ t, v j τ) τ
      = ∑ i ∈ s, ∑ j ∈ t, Ω τ * u i τ * convSq Φ (v j) τ := by
    intro τ
    by_cases hτ : Ω τ = 0
    · simp [hτ]
    · rw [hconv τ hτ, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
  unfold smoothPair
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hI i j

/-! ## 2. Channel tools -/

section Tools

variable {Ω : ℝ → ℝ} {s₀ s₁ : ℝ}

theorem integrable_window_mul (hΩc : Continuous Ω) (hΩS : ∀ τ, τ ∉ Icc s₀ s₁ → Ω τ = 0)
    {h : ℝ → ℝ} (hhc : Continuous h) : Integrable fun τ => Ω τ * h τ :=
  ((hΩc.mul hhc).integrableOn_Icc (a := s₀) (b := s₁)).integrable_of_forall_notMem_eq_zero
    fun τ hτ => by show Ω τ * h τ = 0; rw [hΩS τ hτ, zero_mul]

theorem integral_window_mul_le (hs : s₀ ≤ s₁) (hΩc : Continuous Ω)
    (hΩ1 : ∀ τ, Ω τ ≤ 1) (hΩS : ∀ τ, τ ∉ Icc s₀ s₁ → Ω τ = 0) {h : ℝ → ℝ} (hhc : Continuous h)
    (h0 : ∀ τ ∈ Icc s₀ s₁, 0 ≤ h τ) {C : ℝ} (hC : ∀ τ ∈ Icc s₀ s₁, h τ ≤ C) :
    ∫ τ, Ω τ * h τ ≤ C * (s₁ - s₀) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc s₀ s₁)
    (fun τ hτ => by rw [hΩS τ hτ, zero_mul])]
  calc ∫ τ in Icc s₀ s₁, Ω τ * h τ ≤ ∫ τ in Icc s₀ s₁, C :=
        setIntegral_mono_on ((hΩc.mul hhc).integrableOn_Icc) continuous_const.integrableOn_Icc
          measurableSet_Icc fun τ hτ =>
            (mul_le_of_le_one_left (h0 τ hτ) (hΩ1 τ)).trans (hC τ hτ)
    _ = C * (s₁ - s₀) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le hs, smul_eq_mul, mul_comm]

theorem integral_window_mul_le_interval (hs : s₀ ≤ s₁) (hΩc : Continuous Ω)
    (hΩ1 : ∀ τ, Ω τ ≤ 1) (hΩS : ∀ τ, τ ∉ Icc s₀ s₁ → Ω τ = 0) {h : ℝ → ℝ} (hhc : Continuous h)
    (h0 : ∀ τ, 0 ≤ h τ) :
    ∫ τ, Ω τ * h τ ≤ ∫ τ in s₀..s₁, h τ := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc s₀ s₁)
    (fun τ hτ => by rw [hΩS τ hτ, zero_mul]), intervalIntegral.integral_of_le hs,
    ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_mono_on ((hΩc.mul hhc).integrableOn_Icc) hhc.integrableOn_Icc
    measurableSet_Icc fun τ _ => mul_le_of_le_one_left (h0 τ) (hΩ1 τ)

/-- **Cauchy–Schwarz against a nonnegative window.** `∫ Ω|f| ≤ √(∫Ω) √(∫ Ω f²)`. -/
theorem integral_window_abs_le_sqrt (hΩ0 : ∀ τ, 0 ≤ Ω τ) {f : ℝ → ℝ} (hI0 : Integrable Ω)
    (hI1 : Integrable fun τ => Ω τ * |f τ|) (hI2 : Integrable fun τ => Ω τ * f τ ^ 2) :
    ∫ τ, Ω τ * |f τ| ≤ Real.sqrt (∫ τ, Ω τ) * Real.sqrt (∫ τ, Ω τ * f τ ^ 2) := by
  set S := ∫ τ, Ω τ with hS
  set J := ∫ τ, Ω τ * |f τ| with hJ
  set I := ∫ τ, Ω τ * f τ ^ 2 with hIdef
  have hquad : ∀ t : ℝ, 0 ≤ S * (t * t) + (-2 * J) * t + I := by
    intro t
    have h0 : 0 ≤ ∫ τ, Ω τ * (|f τ| - t) ^ 2 :=
      integral_nonneg fun τ => mul_nonneg (hΩ0 τ) (sq_nonneg _)
    have e : ∫ τ, Ω τ * (|f τ| - t) ^ 2 = I - 2 * t * J + t ^ 2 * S := by
      have hfun : (fun τ => Ω τ * (|f τ| - t) ^ 2)
          = fun τ => Ω τ * f τ ^ 2 - 2 * t * (Ω τ * |f τ|) + t ^ 2 * Ω τ := by
        funext τ; rw [sub_sq, sq_abs]; ring
      rw [hfun, integral_add (f := fun τ => Ω τ * f τ ^ 2 - 2 * t * (Ω τ * |f τ|))
        (g := fun τ => t ^ 2 * Ω τ) (hI2.sub (hI1.const_mul _)) (hI0.const_mul _),
        integral_sub (f := fun τ => Ω τ * f τ ^ 2) (g := fun τ => 2 * t * (Ω τ * |f τ|)) hI2
          (hI1.const_mul _), integral_const_mul, integral_const_mul]
    nlinarith [e, h0]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  have hJ2 : J ^ 2 ≤ S * I := by nlinarith
  have hS0 : 0 ≤ S := integral_nonneg hΩ0
  rw [← Real.sqrt_mul hS0]
  exact (le_abs_self J).trans (Real.abs_le_sqrt hJ2)

/-- **Multiplier channels.** If `|(Φ² ⋆ v) − c v| ≤ e` on the support of `Ω ≥ 0`, then
`|∫ Ω u (Φ² ⋆ v) − c ∫ Ω u v| ≤ e ∫ Ω|u|`. -/
theorem abs_smoothPair_sub_le {u v : ℝ → ℝ} {c e : ℝ}
    (hI1 : Integrable fun τ => Ω τ * u τ * convSq Φ v τ) (hI2 : Integrable fun τ => Ω τ * u τ * v τ)
    (hI3 : Integrable fun τ => Ω τ * |u τ|) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (he : ∀ τ, Ω τ ≠ 0 → |convSq Φ v τ - c * v τ| ≤ e) :
    |smoothPair Φ Ω u v - c * ∫ τ, Ω τ * u τ * v τ| ≤ e * ∫ τ, Ω τ * |u τ| := by
  unfold smoothPair
  rw [← integral_const_mul, ← integral_sub hI1 (hI2.const_mul c), ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun τ => abs_nonneg _) (hI3.const_mul e) (Eventually.of_forall fun τ => ?_))
  by_cases hτ : Ω τ = 0
  · simp [hτ]
  · calc |Ω τ * u τ * convSq Φ v τ - c * (Ω τ * u τ * v τ)|
        = Ω τ * |u τ| * |convSq Φ v τ - c * v τ| := by
          rw [show Ω τ * u τ * convSq Φ v τ - c * (Ω τ * u τ * v τ)
              = Ω τ * u τ * (convSq Φ v τ - c * v τ) by ring, abs_mul, abs_mul, abs_of_nonneg (hΩ0 τ)]
      _ ≤ Ω τ * |u τ| * e := mul_le_mul_of_nonneg_left (he τ hτ) (mul_nonneg (hΩ0 τ) (abs_nonneg _))
      _ = e * (Ω τ * |u τ|) := by ring

/-- **Bounded channels.** If `|Φ² ⋆ v| ≤ e` on the support of `Ω ≥ 0`, then
`|∫ Ω u (Φ² ⋆ v)| ≤ e ∫ Ω|u|`. -/
theorem abs_smoothPair_le {u v : ℝ → ℝ} {e : ℝ}
    (hI3 : Integrable fun τ => Ω τ * |u τ|) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (he : ∀ τ, Ω τ ≠ 0 → |convSq Φ v τ| ≤ e) :
    |smoothPair Φ Ω u v| ≤ e * ∫ τ, Ω τ * |u τ| := by
  unfold smoothPair
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun τ => abs_nonneg _) (hI3.const_mul e) (Eventually.of_forall fun τ => ?_))
  by_cases hτ : Ω τ = 0
  · simp [hτ]
  · show |Ω τ * u τ * convSq Φ v τ| ≤ e * (Ω τ * |u τ|)
    rw [abs_mul, abs_mul, abs_of_nonneg (hΩ0 τ)]
    calc Ω τ * |u τ| * |convSq Φ v τ| ≤ Ω τ * |u τ| * e :=
          mul_le_mul_of_nonneg_left (he τ hτ) (mul_nonneg (hΩ0 τ) (abs_nonneg _))
      _ = e * (Ω τ * |u τ|) := by ring

/-- Cosine-polynomial channels: `∫ Ω v Σ c_n cos(τ log n) = Σ c_n ∫ Ω v cos(τ log n)`. -/
theorem integral_window_mul_cosSum_eq {v : ℝ → ℝ} (hf : Integrable fun τ => Ω τ * v τ)
    (c : ℕ → ℝ) (X : ℝ) :
    ∫ τ, Ω τ * v τ * ∑ n ∈ primeRange X, c n * Real.cos (τ * Real.log n)
      = ∑ n ∈ primeRange X, c n * ∫ τ, Ω τ * v τ * Real.cos (τ * Real.log n) := by
  have hI : ∀ n : ℕ, Integrable fun τ => Ω τ * v τ * Real.cos (τ * Real.log n) := fun n =>
    hf.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun τ => by
      simpa using Real.abs_cos_le_one (τ * Real.log n))
  have hpt : ∀ τ, Ω τ * v τ * ∑ n ∈ primeRange X, c n * Real.cos (τ * Real.log n)
      = ∑ n ∈ primeRange X, c n * (Ω τ * v τ * Real.cos (τ * Real.log n)) := fun τ => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun n _ => (hI n).const_mul (c n)]
  exact Finset.sum_congr rfl fun n _ => integral_const_mul _ _

/-- **Prime cosine sums against a slowly varying windowed density.** With `|c_n| ≤ B a_n`,
`|Σ c_n ∫ Ω v cos(τ log n)| ≤ B (Σ a_n) · ½(S + 5)(5ℓM + (5K₁ + 25K₂)/s₀)`: every `n ≥ 2` has
`log n ≥ log 2` and half-period `π/log n < 5`. -/
theorem abs_sum_window_cos_le {v : ℝ → ℝ} {ℓ M K₁ K₂ : ℝ} (hs : s₀ ≤ s₁) (hs₀ : 0 < s₀)
    (hℓ : 0 ≤ ℓ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hΩc : Continuous Ω) (hvc : Continuous v)
    (hΩ0 : ∀ τ, 0 ≤ Ω τ) (hΩ1 : ∀ τ, Ω τ ≤ 1) (hΩL : ∀ s t, |Ω s - Ω t| ≤ ℓ * |s - t|)
    (hΩS : ∀ τ, τ ∉ Icc s₀ s₁ → Ω τ = 0) (hvM : ∀ τ ∈ Icc s₀ (s₁ + 5), |v τ| ≤ M)
    (hinc : ∀ t, s₀ ≤ t → ∀ r, |v (t + r) - v t| ≤ (K₁ * |r| + K₂ * r ^ 2) / t)
    {c : ℕ → ℝ} {B : ℝ} (hc : ∀ n, |c n| ≤ B * acoef n) (X : ℝ) :
    |∑ n ∈ primeRange X, c n * ∫ τ, Ω τ * v τ * Real.cos (τ * Real.log n)|
      ≤ B * (∑ n ∈ primeRange X, acoef n)
        * ((1 / 2) * ((s₁ - s₀ + 5) * (ℓ * 5 * M + (K₁ * 5 + K₂ * 5 ^ 2) / s₀))) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hvM s₀ ⟨le_rfl, by linarith⟩)
  have hB0 : 0 ≤ B := by
    have := (abs_nonneg _).trans (hc 2)
    have ha : 0 < acoef 2 := by
      unfold acoef
      have : (0:ℝ) < Λ 2 := by
        rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        exact Real.log_pos (by norm_num)
      positivity
    exact nonneg_of_mul_nonneg_left this ha
  set Sh := (1 / 2) * ((s₁ - s₀ + 5) * (ℓ * 5 * M + (K₁ * 5 + K₂ * 5 ^ 2) / s₀)) with hSh
  have hterm : ∀ n ∈ primeRange X, |c n * ∫ τ, Ω τ * v τ * Real.cos (τ * Real.log n)|
      ≤ B * acoef n * Sh := by
    intro n hn
    rcases acoef_eq_zero_or_two_le hn with hn0 | hn2
    · have : c n = 0 := abs_nonpos_iff.mp (by simpa [hn0] using hc n)
      rw [this, hn0]; simp
    have hy : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
    have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hδ5 : π / Real.log n ≤ 5 := by
      rw [div_le_iff₀ hy]
      have := Real.log_two_gt_d9; have := Real.pi_lt_d2; linarith
    have hδ0 : 0 < π / Real.log n := by positivity
    have h := abs_integral_window_mul_cos_le hs hs₀ hK₁ hK₂ hΩc hvc hΩ0 hΩ1 hΩL hΩS hy
      (fun τ hτ => hvM τ ⟨hτ.1, hτ.2.trans (by linarith)⟩) hinc
    have hmono : (1 / 2) * ((s₁ - s₀ + π / Real.log n) * (ℓ * (π / Real.log n) * M
        + (K₁ * (π / Real.log n) + K₂ * (π / Real.log n) ^ 2) / s₀)) ≤ Sh := by
      rw [hSh]
      refine mul_le_mul_of_nonneg_left (mul_le_mul (by linarith) (add_le_add ?_ ?_)
        (by positivity) (by linarith)) (by norm_num)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ5 hℓ) hM0
      · refine div_le_div_of_nonneg_right ?_ hs₀.le
        exact add_le_add (mul_le_mul_of_nonneg_left hδ5 hK₁)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0.le hδ5 2) hK₂)
    rw [abs_mul]
    exact mul_le_mul (hc n) (h.trans hmono) (abs_nonneg _) (mul_nonneg hB0 (acoef_nonneg n))
  calc |∑ n ∈ primeRange X, c n * ∫ τ, Ω τ * v τ * Real.cos (τ * Real.log n)|
      ≤ ∑ n ∈ primeRange X, |c n * ∫ τ, Ω τ * v τ * Real.cos (τ * Real.log n)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ primeRange X, B * acoef n * Sh := Finset.sum_le_sum hterm
    _ = B * (∑ n ∈ primeRange X, acoef n) * Sh := by
        rw [Finset.mul_sum, Finset.sum_mul]

end Tools

/-! ## 3. The channel theorem -/

/-- The explicit remainder of the nine-channel evaluation: `A = Σ a_n`, `E` the Stirling moment,
`CΦ = ∫Φ² + ∫Φ²|x|`, `IΦ = ∫Φ²`, `S` the window length, `M` the size of `μ`, `Sh` the cosine
shift bound, `D = ‖Ω^{(k)}‖₁`, `IP = ∫Ω P_X²`, `IC = ∫Ω C_g²`. -/
def channelError (A E CΦ IΦ S s₀ L M Sh D θ₀ X IP IC : ℝ) (k : ℕ) : ℝ :=
  S * M * E / s₀
    + S * M * (3 * Real.sqrt X * CΦ / s₀)
    + 2 * L * A * Sh
    + S * (3 * Real.sqrt X / s₀) * (M * IΦ + E / s₀)
    + S * (3 * Real.sqrt X / s₀) * (3 * Real.sqrt X * CΦ / s₀)
    + 2 * (3 * Real.sqrt X / s₀) * (Real.sqrt S * Real.sqrt IC)
    + (IΦ * ((1 / π) * A * Sh) + (1 / π) * A * S * E / s₀)
    + 3 * Real.sqrt X * CΦ / s₀ * (Real.sqrt S * Real.sqrt IP)
    + (1 / π) * (L * D) * ((θ₀ ^ k)⁻¹ + 1) * A ^ 2

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- **The smooth-window Frobenius form, channel by channel.** For a `C^k` window `0 ≤ Ω ≤ 1`,
`ℓ`-Lipschitz and supported in `[s₀, s₁]`, `s₀ ≥ 2`, with `|μ| ≤ M` on `[s₀, s₁ + 5]`:
`∫ Ω ν_X (Φ² ⋆ ν_X) ≤ (∫Φ²) ∫_{s₀}^{s₁} μ² + π⁻¹ (∫Ω) Σ a_n² g(log n) + coalSum + channelError`. -/
theorem smoothPair_nuX_le (hF : LocalHypsCoreW cϱ p F) {Ω : ℝ → ℝ} {s₀ s₁ ℓ : ℝ} {k : ℕ}
    (hs : s₀ ≤ s₁) (hs₀ : 2 ≤ s₀) (hℓ : 0 ≤ ℓ) (hΩk : ContDiff ℝ k Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hΩ1 : ∀ τ, Ω τ ≤ 1) (hΩL : ∀ s t, |Ω s - Ω t| ≤ ℓ * |s - t|)
    (hΩS : ∀ τ, τ ∉ Icc s₀ s₁ → Ω τ = 0) {K M M' : ℝ} (hK : 0 ≤ K) (hμc : Continuous Zeta23.mu)
    (hμinc : ∀ t, 2 ≤ t → ∀ r, |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    (hμM : ∀ τ ∈ Icc s₀ (s₁ + 5), |Zeta23.mu τ| ≤ M)
    (hM' : 0 ≤ M') (hμg : ∀ τ τ', Ω τ ≠ 0 → |Zeta23.mu τ'| ≤ M' * (1 + |τ - τ'|)) {θ₀ : ℝ}
    (hθ₀ : 0 < θ₀) :
    smoothPair F.Phi Ω (Zeta23.nuX p.X) (Zeta23.nuX p.X)
      ≤ (∫ x, F.Phi x ^ 2) * (∫ τ in s₀..s₁, Zeta23.mu τ ^ 2)
        + (1 / π) * (∫ τ, Ω τ) * ∑ n ∈ primeRange p.X, acoef n ^ 2 * F.g (Real.log n)
        + coalSum Ω F.g p.X θ₀
        + channelError (∑ n ∈ primeRange p.X, acoef n)
            (K * (∫ x, F.Phi x ^ 2 * |x|) + 10 * ∫ x, F.Phi x ^ 2 * x ^ 2)
            ((∫ x, F.Phi x ^ 2) + ∫ x, F.Phi x ^ 2 * |x|) (∫ x, F.Phi x ^ 2) (s₁ - s₀) s₀ p.L M
            ((1 / 2) * ((s₁ - s₀ + 5) * (ℓ * 5 * M + (K * 5 + 10 * 5 ^ 2) / s₀)))
            (∫ τ in (s₀ - 1)..(s₁ + 1), |iteratedDeriv k Ω τ|) θ₀ p.X
            (∫ τ, Ω τ * Zeta23.PX p.X τ ^ 2) (∫ τ, Ω τ * primeDirichletCos F.g p.X τ ^ 2) k := by
  -- notation
  set Φ := F.Phi with hΦdef
  set X := p.X with hXdef
  set A := ∑ n ∈ primeRange X, acoef n with hA
  set E := K * (∫ x, Φ x ^ 2 * |x|) + 10 * ∫ x, Φ x ^ 2 * x ^ 2 with hE
  set CΦ := (∫ x, Φ x ^ 2) + ∫ x, Φ x ^ 2 * |x| with hCΦ
  set IΦ := ∫ x, Φ x ^ 2 with hIΦ
  set S := s₁ - s₀ with hS
  set Sh := (1 / 2) * ((s₁ - s₀ + 5) * (ℓ * 5 * M + (K * 5 + 10 * 5 ^ 2) / s₀)) with hSh
  set IP := ∫ τ, Ω τ * Zeta23.PX X τ ^ 2 with hIP
  set IC := ∫ τ, Ω τ * primeDirichletCos F.g X τ ^ 2 with hIC
  have hΦc : Continuous Φ := hF.Phi_contDiff.continuous
  have hΦe := hF.Phi_even
  have hΦ2 := hF.Phi_sq_integrable
  have hΦ2a := hF.Phi_sq_mul_abs_integrable
  have hΦ2s := hF.Phi_sq_mul_sq_integrable
  have hFT := hF.Phi_sq_fourier
  have hΩc : Continuous Ω := hΩk.continuous
  have hs₀0 : 0 < s₀ := by linarith
  have hS0 : 0 ≤ S := by rw [hS]; linarith
  have hIΦ0 : 0 ≤ IΦ := integral_nonneg fun x => sq_nonneg _
  have hIa0 : 0 ≤ ∫ x, Φ x ^ 2 * |x| := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hIs0 : 0 ≤ ∫ x, Φ x ^ 2 * x ^ 2 := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hCΦ0 : 0 ≤ CΦ := by rw [hCΦ]; positivity
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hμM s₀ ⟨le_rfl, by linarith⟩)
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => acoef_nonneg n
  have hg0 := hF.g_nonneg
  have hgL : ∀ y, F.g y ≤ p.L := fun y => by
    have h := (hF.g_le_Aphi y).trans (hF.Aphi_le y)
    have hL := hF.L_pos
    refine h.trans (max_le (by linarith [abs_nonneg y]) hL.le)
  have hL0 : 0 ≤ p.L := hF.L_pos.le
  have hsX : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  -- components
  have hPic : Continuous (Zeta23.PiX X) := hF.PiX_cont
  have hPib : ∀ τ, |Zeta23.PiX X τ| ≤ 3 * Real.sqrt X / (1 + |τ|) := hF.PiX_bound
  have hPc : Continuous (Zeta23.PX X) := continuous_PX' X
  have hPb : ∀ τ, |Zeta23.PX X τ| ≤ (1 / π) * A := abs_PX_le' X
  have hPi3 : ∀ τ, |Zeta23.PiX X τ| ≤ 3 * Real.sqrt X := fun τ =>
    (hPib τ).trans (div_le_self (by positivity) (by linarith [abs_nonneg τ]))
  have hPiS : ∀ τ ∈ Icc s₀ s₁, |Zeta23.PiX X τ| ≤ 3 * Real.sqrt X / s₀ := fun τ hτ =>
    (hPib τ).trans (div_le_div_of_nonneg_left (by positivity) hs₀0
      (by rw [abs_of_pos (by linarith [hτ.1])]; linarith [hτ.1]))
  have hμS : ∀ τ ∈ Icc s₀ s₁, |Zeta23.mu τ| ≤ M := fun τ hτ => hμM τ ⟨hτ.1, by linarith [hτ.2]⟩
  have hsupp : ∀ τ, Ω τ ≠ 0 → τ ∈ Icc s₀ s₁ := fun τ hτ => by
    by_contra h; exact hτ (hΩS τ h)
  -- the convolutions on the support
  have hcμ : ∀ τ, Ω τ ≠ 0 → |convSq Φ Zeta23.mu τ - Zeta23.mu τ * IΦ| ≤ E / s₀ := by
    intro τ hτ
    have hτS := hsupp τ hτ
    have hτ0 : 0 < τ := by linarith [hτS.1]
    refine (abs_convSq_sub_le hΦe hΦ2 hΦ2a hΦ2s hΦc hμc (hμinc τ (by linarith [hτS.1]))).trans ?_
    exact div_le_div_of_nonneg_left hE0 hs₀0 hτS.1
  have hcμb : ∀ τ, Ω τ ≠ 0 → |convSq Φ Zeta23.mu τ| ≤ M * IΦ + E / s₀ := by
    intro τ hτ
    have h1 := hcμ τ hτ
    have h2 : |Zeta23.mu τ * IΦ| ≤ M * IΦ := by
      rw [abs_mul, abs_of_nonneg hIΦ0]
      exact mul_le_mul_of_nonneg_right (hμS τ (hsupp τ hτ)) hIΦ0
    calc |convSq Φ Zeta23.mu τ| = |(convSq Φ Zeta23.mu τ - Zeta23.mu τ * IΦ) + Zeta23.mu τ * IΦ| := by
          ring_nf
      _ ≤ E / s₀ + M * IΦ := (abs_add_le _ _).trans (add_le_add h1 h2)
      _ = M * IΦ + E / s₀ := by ring
  have hcPi : ∀ τ, Ω τ ≠ 0 → |convSq Φ (Zeta23.PiX X) τ| ≤ 3 * Real.sqrt X * CΦ / s₀ := by
    intro τ hτ
    have hτS := hsupp τ hτ
    refine (abs_convSq_le_of_decay hΦe hΦ2 hΦ2a (by positivity) hPib τ).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) hs₀0
      (by rw [abs_of_pos (by linarith [hτS.1])]; linarith [hτS.1])
  have hcP : ∀ τ, convSq Φ (Zeta23.PX X) τ = -2 * primeDirichletCos F.g X τ :=
    fun τ => integral_PhiSq_sub_mul_PX hΦe hΦ2 hFT X τ
  -- linear growth of the three components on the support
  set M'' := M' + 3 * Real.sqrt X + (1 / π) * A with hM''
  have hA' : 0 ≤ (1 / π) * A := by positivity
  set u : Fin 3 → ℝ → ℝ := ![Zeta23.mu, Zeta23.PiX X, Zeta23.PX X] with hu
  have huc : ∀ i, Continuous (u i) := by
    intro i; fin_cases i
    · exact hμc
    · exact hPic
    · exact hPc
  have hvb : ∀ j τ τ', Ω τ ≠ 0 → |u j τ'| ≤ M'' * (1 + |τ - τ'|) := by
    intro j τ τ' hτ
    have h1 : M'' ≤ M'' * (1 + |τ - τ'|) := le_mul_of_one_le_right (by positivity)
      (by linarith [abs_nonneg (τ - τ')])
    fin_cases j
    · show |Zeta23.mu τ'| ≤ _
      refine (hμg τ τ' hτ).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · show |Zeta23.PiX X τ'| ≤ _
      exact (hPi3 τ').trans (by linarith)
    · show |Zeta23.PX X τ'| ≤ _
      exact (hPb τ').trans (by linarith)
  have hnu : Zeta23.nuX X = fun τ => ∑ i : Fin 3, u i τ := by
    funext τ; simp [hu, Fin.sum_univ_three, Zeta23.nuX]
  have hexp := smoothPair_sum_sum hΦc hΦ2 hΦ2a hΩc Finset.univ Finset.univ huc
    (fun i => integrable_window_mul hΩc hΩS (huc i)) huc hvb
  rw [← hnu] at hexp
  rw [hexp]
  simp only [Fin.sum_univ_three, hu, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  -- integrability of the iterated integrands
  have hIc : ∀ {w v : ℝ → ℝ}, Continuous w → Continuous v →
      (∀ τ τ', Ω τ ≠ 0 → |v τ'| ≤ M'' * (1 + |τ - τ'|)) →
      Integrable fun τ => Ω τ * w τ * convSq Φ v τ := fun hw hv hb =>
    integrable_window_mul_convSq hΦc hΦ2 hΦ2a hΩc hw hv (integrable_window_mul hΩc hΩS hw) hb
  have hvμ := hvb 0
  have hvPi := hvb 1
  have hvP := hvb 2
  simp only [hu, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hvμ hvPi hvP
  have hI3 : ∀ {w : ℝ → ℝ}, Continuous w → Integrable fun τ => Ω τ * |w τ| := fun hw =>
    integrable_window_mul hΩc hΩS hw.abs
  have hIabsμ : ∫ τ, Ω τ * |Zeta23.mu τ| ≤ M * S :=
    integral_window_mul_le hs hΩc hΩ1 hΩS hμc.abs (fun _ _ => abs_nonneg _) hμS
  have hIabsPi : ∫ τ, Ω τ * |Zeta23.PiX X τ| ≤ 3 * Real.sqrt X / s₀ * S :=
    integral_window_mul_le hs hΩc hΩ1 hΩS hPic.abs (fun _ _ => abs_nonneg _) hPiS
  have hIabsP : ∫ τ, Ω τ * |Zeta23.PX X τ| ≤ (1 / π) * A * S :=
    integral_window_mul_le hs hΩc hΩ1 hΩS hPc.abs (fun _ _ => abs_nonneg _)
      (fun τ _ => hPb τ)
  have hIΩ : ∫ τ, Ω τ ≤ S := by
    have h := integral_window_mul_le hs hΩc hΩ1 hΩS (h := fun _ => (1:ℝ)) continuous_const
      (fun _ _ => zero_le_one) (C := 1) (fun _ _ => le_rfl)
    simpa using h
  have hΩi : Integrable Ω := by
    simpa using integrable_window_mul hΩc hΩS (h := fun _ => (1:ℝ)) continuous_const
  have hsqΩ : Real.sqrt (∫ τ, Ω τ) ≤ Real.sqrt S := Real.sqrt_le_sqrt hIΩ
  -- (μ, μ)
  have c00 : smoothPair Φ Ω Zeta23.mu Zeta23.mu
      ≤ IΦ * (∫ τ in s₀..s₁, Zeta23.mu τ ^ 2) + S * M * E / s₀ := by
    have hI2 : Integrable fun τ => Ω τ * Zeta23.mu τ * Zeta23.mu τ :=
      (integrable_window_mul hΩc hΩS (hμc.mul hμc)).congr (Eventually.of_forall fun τ => by
        simp only; ring)
    have h := abs_smoothPair_sub_le (hIc hμc hμc hvμ) hI2 (hI3 hμc) hΩ0
      (fun τ hτ => by rw [mul_comm IΦ]; exact hcμ τ hτ)
    have hsq : ∫ τ, Ω τ * Zeta23.mu τ * Zeta23.mu τ ≤ ∫ τ in s₀..s₁, Zeta23.mu τ ^ 2 := by
      have := integral_window_mul_le_interval hs hΩc hΩ1 hΩS (hμc.pow 2) (fun τ => sq_nonneg _)
      refine le_of_eq_of_le (integral_congr_ae (Eventually.of_forall fun τ => ?_)) this
      simp only; ring
    have h1 := (abs_le.mp h).2
    have h2 : E / s₀ * ∫ τ, Ω τ * |Zeta23.mu τ| ≤ E / s₀ * (M * S) :=
      mul_le_mul_of_nonneg_left hIabsμ (by positivity)
    have h3 : IΦ * ∫ τ, Ω τ * Zeta23.mu τ * Zeta23.mu τ ≤ IΦ * ∫ τ in s₀..s₁, Zeta23.mu τ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hIΦ0
    have e : E / s₀ * (M * S) = S * M * E / s₀ := by ring
    linarith
  -- (μ, Π)
  have c01 : smoothPair Φ Ω Zeta23.mu (Zeta23.PiX X) ≤ S * M * (3 * Real.sqrt X * CΦ / s₀) := by
    have h := abs_smoothPair_le (hI3 hμc) hΩ0 hcPi
    have := (le_abs_self _).trans h
    calc _ ≤ 3 * Real.sqrt X * CΦ / s₀ * ∫ τ, Ω τ * |Zeta23.mu τ| := this
      _ ≤ 3 * Real.sqrt X * CΦ / s₀ * (M * S) := mul_le_mul_of_nonneg_left hIabsμ (by positivity)
      _ = S * M * (3 * Real.sqrt X * CΦ / s₀) := by ring
  -- cosine-sum form of the channels ending in `P_X`
  have hcosμ : ∀ {c : ℕ → ℝ} {B : ℝ}, (∀ n, |c n| ≤ B * acoef n) →
      |∑ n ∈ primeRange X, c n * ∫ τ, Ω τ * Zeta23.mu τ * Real.cos (τ * Real.log n)|
        ≤ B * A * Sh := fun hc =>
    abs_sum_window_cos_le hs hs₀0 hℓ hK (by norm_num) hΩc hμc hΩ0 hΩ1 hΩL hΩS hμM
      (fun t ht r => hμinc t (by linarith) r) hc X
  -- (μ, P)
  have c02 : smoothPair Φ Ω Zeta23.mu (Zeta23.PX X) ≤ 2 * p.L * A * Sh := by
    have e : smoothPair Φ Ω Zeta23.mu (Zeta23.PX X)
        = ∑ n ∈ primeRange X, (-2 * (acoef n * F.g (Real.log n)))
            * ∫ τ, Ω τ * Zeta23.mu τ * Real.cos (τ * Real.log n) := by
      unfold smoothPair
      rw [← integral_window_mul_cosSum_eq (integrable_window_mul hΩc hΩS hμc)]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only
      rw [hcP τ]
      unfold primeDirichletCos
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e]
    refine (le_abs_self _).trans ((hcosμ (B := 2 * p.L) fun n => ?_).trans (le_of_eq (by ring)))
    rw [abs_mul, abs_mul, abs_of_nonneg (acoef_nonneg n), abs_of_nonneg (hg0 _),
      show |(-2:ℝ)| = 2 by norm_num]
    nlinarith [hgL (Real.log n), acoef_nonneg n, hg0 (Real.log n)]
  -- (Π, μ)
  have c10 : smoothPair Φ Ω (Zeta23.PiX X) Zeta23.mu ≤ S * (3 * Real.sqrt X / s₀) * (M * IΦ + E / s₀) := by
    have h := (le_abs_self _).trans (abs_smoothPair_le (hI3 hPic) hΩ0 hcμb)
    calc _ ≤ (M * IΦ + E / s₀) * ∫ τ, Ω τ * |Zeta23.PiX X τ| := h
      _ ≤ (M * IΦ + E / s₀) * (3 * Real.sqrt X / s₀ * S) :=
          mul_le_mul_of_nonneg_left hIabsPi (by positivity)
      _ = S * (3 * Real.sqrt X / s₀) * (M * IΦ + E / s₀) := by ring
  -- (Π, Π)
  have c11 : smoothPair Φ Ω (Zeta23.PiX X) (Zeta23.PiX X)
      ≤ S * (3 * Real.sqrt X / s₀) * (3 * Real.sqrt X * CΦ / s₀) := by
    have h := (le_abs_self _).trans (abs_smoothPair_le (hI3 hPic) hΩ0 hcPi)
    calc _ ≤ 3 * Real.sqrt X * CΦ / s₀ * ∫ τ, Ω τ * |Zeta23.PiX X τ| := h
      _ ≤ 3 * Real.sqrt X * CΦ / s₀ * (3 * Real.sqrt X / s₀ * S) :=
          mul_le_mul_of_nonneg_left hIabsPi (by positivity)
      _ = S * (3 * Real.sqrt X / s₀) * (3 * Real.sqrt X * CΦ / s₀) := by ring
  -- Cauchy–Schwarz pieces
  have hCc := continuous_primeDirichletCos F.g X
  have hCS_C : ∫ τ, Ω τ * |primeDirichletCos F.g X τ| ≤ Real.sqrt S * Real.sqrt IC :=
    (integral_window_abs_le_sqrt hΩ0 hΩi (hI3 hCc) (integrable_window_mul hΩc hΩS (hCc.pow 2))).trans
      (mul_le_mul_of_nonneg_right hsqΩ (Real.sqrt_nonneg _))
  have hCS_P : ∫ τ, Ω τ * |Zeta23.PX X τ| ≤ Real.sqrt S * Real.sqrt IP :=
    (integral_window_abs_le_sqrt hΩ0 hΩi (hI3 hPc) (integrable_window_mul hΩc hΩS (hPc.pow 2))).trans
      (mul_le_mul_of_nonneg_right hsqΩ (Real.sqrt_nonneg _))
  -- (Π, P)
  have c12 : smoothPair Φ Ω (Zeta23.PiX X) (Zeta23.PX X)
      ≤ 2 * (3 * Real.sqrt X / s₀) * (Real.sqrt S * Real.sqrt IC) := by
    unfold smoothPair
    simp_rw [hcP]
    refine (le_abs_self _).trans ((abs_integral_le_integral_abs).trans ?_)
    calc ∫ τ, |Ω τ * Zeta23.PiX X τ * (-2 * primeDirichletCos F.g X τ)|
        ≤ ∫ τ, 2 * (3 * Real.sqrt X / s₀) * (Ω τ * |primeDirichletCos F.g X τ|) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun τ => abs_nonneg _)
            ((hI3 hCc).const_mul _) (Eventually.of_forall fun τ => ?_)
          by_cases hτ : Ω τ = 0
          · simp [hτ]
          · show |Ω τ * Zeta23.PiX X τ * (-2 * primeDirichletCos F.g X τ)|
              ≤ 2 * (3 * Real.sqrt X / s₀) * (Ω τ * |primeDirichletCos F.g X τ|)
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hΩ0 τ)]
            have hb := hPiS τ (hsupp τ hτ)
            have : |(-2 : ℝ)| = 2 := by norm_num
            rw [this]
            have hC0 := abs_nonneg (primeDirichletCos F.g X τ)
            nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg (hΩ0 τ) hC0)]
      _ = 2 * (3 * Real.sqrt X / s₀) * ∫ τ, Ω τ * |primeDirichletCos F.g X τ| := integral_const_mul _ _
      _ ≤ 2 * (3 * Real.sqrt X / s₀) * (Real.sqrt S * Real.sqrt IC) :=
          mul_le_mul_of_nonneg_left hCS_C (by positivity)
  -- (P, μ)
  have c20 : smoothPair Φ Ω (Zeta23.PX X) Zeta23.mu
      ≤ IΦ * ((1 / π) * A * Sh) + (1 / π) * A * S * E / s₀ := by
    have hI2 : Integrable fun τ => Ω τ * Zeta23.PX X τ * Zeta23.mu τ :=
      (integrable_window_mul hΩc hΩS (hPc.mul hμc)).congr (Eventually.of_forall fun τ => by
        simp only; ring)
    have h := abs_smoothPair_sub_le (hIc hPc hμc hvμ) hI2 (hI3 hPc) hΩ0
      (fun τ hτ => by rw [mul_comm IΦ]; exact hcμ τ hτ)
    have hPμ : ∫ τ, Ω τ * Zeta23.PX X τ * Zeta23.mu τ
        = ∑ n ∈ primeRange X, (-(1 / π) * acoef n)
            * ∫ τ, Ω τ * Zeta23.mu τ * Real.cos (τ * Real.log n) := by
      rw [← integral_window_mul_cosSum_eq (integrable_window_mul hΩc hΩS hμc)]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only
      rw [PX_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by unfold ycoef; ring
    have hb : |∫ τ, Ω τ * Zeta23.PX X τ * Zeta23.mu τ| ≤ (1 / π) * A * Sh := by
      rw [hPμ]
      refine (hcosμ (B := 1 / π) fun n => ?_).trans (le_of_eq (by ring))
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / π),
        abs_of_nonneg (acoef_nonneg n)]
    have h1 := (abs_le.mp h).2
    have h2 : IΦ * ∫ τ, Ω τ * Zeta23.PX X τ * Zeta23.mu τ ≤ IΦ * ((1 / π) * A * Sh) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) hIΦ0
    have h3 : E / s₀ * ∫ τ, Ω τ * |Zeta23.PX X τ| ≤ E / s₀ * ((1 / π) * A * S) :=
      mul_le_mul_of_nonneg_left hIabsP (by positivity)
    have e : E / s₀ * ((1 / π) * A * S) = (1 / π) * A * S * E / s₀ := by ring
    linarith
  -- (P, Π)
  have c21 : smoothPair Φ Ω (Zeta23.PX X) (Zeta23.PiX X)
      ≤ 3 * Real.sqrt X * CΦ / s₀ * (Real.sqrt S * Real.sqrt IP) := by
    have h := (le_abs_self _).trans (abs_smoothPair_le (hI3 hPc) hΩ0 hcPi)
    exact h.trans (mul_le_mul_of_nonneg_left hCS_P (by positivity))
  -- (P, P)
  have c22 := smoothPair_PX_PX_le hΦe hΦ2 hFT hΩi hs hΩk hΩS hg0 hgL hθ₀ X
  -- assemble
  unfold channelError
  linarith [c00, c01, c02, c10, c11, c12, c20, c21, c22]

end GaloisForLFunctions.TransThresholdPairCorrelation
