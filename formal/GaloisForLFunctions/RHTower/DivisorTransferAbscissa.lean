import GaloisForLFunctions.RHTower.ExactNullCertificateDivisorTransfer

/-!
# The divisor transfer at an arbitrary abscissa `c > 1`

Let `R` be holomorphic on `½ ≤ Re s ≤ c` for some `c > 1`, with `ξ²R` decaying like `1/(1+t²)` on the
strip and `G²R` like `1/(1+t²)` on `Re s = c`, where `G(s) = s(s−1)Γ_ℝ(s)/2`.  Then
(`integral_xi_sq_mul_cpow_eq_tsum_at`)

`∫ ξ(½+it)² R(½+it) n^{−(½+it)} dt = 2π Σ_m d(m) Ψ_{R,c}(mn)`,  `Ψ_{R,c} = 𝓜^{−1}_c[G² R]`.

The proof shifts the line of integration from `Re s = ½` to `Re s = c` and expands
`ξ² = G² ζ² = G² Σ d(m) m^{−s}`; the interchange of sum and integral uses the absolute convergence of
`Σ d(m) m^{−c}` (the Dirichlet series of `ζ²` at `c > 1`), so no bound on `d(m)` beyond that is needed.

Consequently (`logNode_blind_of_certKernelAt_vanishes`) the test with spectral density `Ξ² R` is blind
at every `log n`, `n ≥ 2`, as soon as `Ψ_{R,c}` vanishes at every integer `n ≥ 2`.

The abscissa matters: for a self-reciprocal line profile `h` with logarithmic decay `e^{−a|v|}` the
multiplier `G² R = (Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜h(s)` is holomorphic only for `Re s < ½ + a`, so for the
decay class `a = 3/2` every abscissa `1 < c < 2` is admissible while `c = 3` is not.
-/

open Complex MeasureTheory ArithmeticFunction LSeries
open scoped ArithmeticFunction.zeta LSeries.notation

noncomputable section

namespace RHTower.ExactNullDivisorTransfer

/-- The kernel `Ψ_{R,c} = 𝓜^{−1}_c[G² R]` at the abscissa `c`. -/
def certKernelAt (c : ℝ) (R : ℂ → ℂ) (x : ℝ) : ℂ :=
  mellinInv c (fun s => archXi s ^ 2 * R s) x

/-- The divisor function has an absolutely convergent Dirichlet series on `Re s > 1`. -/
theorem lseriesSummable_divisorCard {c : ℝ} (hc : 1 < c) : LSeriesSummable divisorCard c := by
  rw [← one_convolution_one]
  have h1 : LSeriesSummable (fun _ => 1 : ℕ → ℂ) c :=
    LSeriesSummable_one_iff.mpr (by simpa using hc)
  exact h1.convolution h1

theorem summable_norm_divisorCard_mul_rpow {c : ℝ} (hc : 1 < c) {n : ℕ} (hn : 1 ≤ n) :
    Summable fun m : ℕ => ‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-c) := by
  have hs := (lseriesSummable_divisorCard hc).norm
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hs
  rw [norm_term_eq]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [divisorCard]
  · rw [if_neg hm.ne', Complex.ofReal_re]
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hle : ((m * n : ℕ) : ℝ) ^ (-c) ≤ (m : ℝ) ^ (-c) := by
      push_cast
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by linarith)
    calc ‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-c) ≤ ‖divisorCard m‖ * (m : ℝ) ^ (-c) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = ‖divisorCard m‖ / (m : ℝ) ^ c := by
          rw [Real.rpow_neg (by positivity), div_eq_mul_inv]

/-- **Divisor transfer at the abscissa `c > 1`.** -/
theorem integral_xi_sq_mul_cpow_eq_tsum_at (R : ℂ → ℂ) {c : ℝ} (hc : 1 < c)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → ‖xi s ^ 2 * R s‖ ≤ C / (1 + s.im ^ 2))
    {C' : ℝ} (hC' : ∀ t : ℝ, ‖archXi (c + t * I) ^ 2 * R (c + t * I)‖ ≤ C' / (1 + t ^ 2))
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-(1 / 2 + t * I)) =
      2 * Real.pi * ∑' m : ℕ, divisorCard m * certKernelAt c R ((m * n : ℕ) : ℝ) := by
  set Φ : ℂ → ℂ := fun s => xi s ^ 2 * R s * (n : ℂ) ^ (-s) with hΦ
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hc0 : (1 / 2 : ℝ) ≤ c := by linarith
  have hstrip : ∀ s : ℂ, s.re ∈ Set.uIcc (1 / 2 : ℝ) c → 1 / 2 ≤ s.re ∧ s.re ≤ c := by
    intro s hs
    rw [Set.uIcc_of_le hc0] at hs
    exact hs
  have hd : ∀ s : ℂ, s.re ∈ Set.uIcc (1 / 2 : ℝ) c → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have hx : DifferentiableAt ℂ xi s := xi_differentiable s
    have hcp : DifferentiableAt ℂ (fun s : ℂ => (n : ℂ) ^ (-s)) s :=
      (differentiableAt_id.neg).const_cpow (Or.inl hn0)
    exact ((hx.pow 2).mul (hR s h1 h2)).mul hcp
  have hb : ∀ s : ℂ, s.re ∈ Set.uIcc (1 / 2 : ℝ) c → ‖Φ s‖ ≤ C / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hstrip s hs
    have hcp := norm_natCast_cpow_neg_re_le_one hn (s := s) (by linarith)
    rw [hΦ, norm_mul]
    calc ‖xi s ^ 2 * R s‖ * ‖(n : ℂ) ^ (-s)‖ ≤ (C / (1 + s.im ^ 2)) * 1 :=
          mul_le_mul (hC s h1 h2) hcp (norm_nonneg _) (le_trans (norm_nonneg _) (hC s h1 h2))
      _ = C / (1 + s.im ^ 2) := mul_one _
  have hshift := GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay hd hb
  have hL : (∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-(1 / 2 + t * I))) =
      ∫ t : ℝ, Φ (((1 / 2 : ℝ) : ℂ) + t * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hΦ]; push_cast; ring_nf
  rw [hL, hshift]
  set K : ℝ → ℂ := fun t => archXi (c + t * I) ^ 2 * R (c + t * I) with hK
  set F : ℕ → ℝ → ℂ := fun m t =>
    divisorCard m * (((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I)) * K t) with hF
  have hre : ∀ t : ℝ, 1 < ((c : ℂ) + t * I).re := fun t => by simpa using hc
  have hser : ∀ t : ℝ, Φ ((c : ℂ) + t * I) = ∑' m, F m t := by
    intro t
    simp only [hΦ, hF, hK]
    push_cast
    rw [xi_eq_archXi_mul_zeta (hre t), mul_pow, riemannZeta_sq_eq_tsum (hre t)]
    rw [show archXi (c + t * I) ^ 2 * (∑' m : ℕ, divisorCard m * (m : ℂ) ^ (-(c + t * I))) *
        R (c + t * I) * (n : ℂ) ^ (-(c + t * I)) =
        (∑' m : ℕ, divisorCard m * (m : ℂ) ^ (-(c + t * I))) *
          ((n : ℂ) ^ (-(c + t * I)) * (archXi (c + t * I) ^ 2 * R (c + t * I))) by ring,
      ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    rw [Complex.natCast_mul_natCast_cpow]
    ring
  have hKcont : Continuous K := by
    rw [continuous_iff_continuousAt]
    intro t
    have hre0 : (0 : ℝ) < ((c : ℂ) + t * I).re := by simp; linarith
    have h3 : DifferentiableAt ℂ (fun s => archXi s ^ 2 * R s) ((c : ℂ) + t * I) :=
      ((differentiableAt_archXi hre0).pow 2).mul
        (hR _ (by simp; linarith) (by simp))
    exact ContinuousAt.comp (g := fun s => archXi s ^ 2 * R s) h3.continuousAt
      (by fun_prop : ContinuousAt (fun t : ℝ => (c : ℂ) + t * I) t)
  have hKint : Integrable K := by
    refine (integrable_inv_one_add_sq.const_mul C').mono' hKcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    simpa [hK, div_eq_mul_inv] using hC' t
  have hnorm_cpow : ∀ m : ℕ, ∀ t : ℝ, 1 ≤ m →
      ‖((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I))‖ = ((m * n : ℕ) : ℝ) ^ (-c) := by
    intro m t hm
    have hpos : (0 : ℝ) < ((m * n : ℕ) : ℝ) := by
      have : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    rw [show (((m * n : ℕ) : ℂ)) = ((((m * n : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hFint : ∀ m : ℕ, Integrable (F m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, divisorCard]
    have hcp : Continuous fun t : ℝ => ((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I)) := by
      have hb0 : ((m * n : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mp (Nat.one_le_iff_ne_zero.mpr (by positivity)))
      exact Continuous.const_cpow (by fun_prop) (Or.inl hb0)
    have hbound : ∀ t, ‖F m t‖ ≤ ‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-c) * ‖K t‖ := by
      intro t
      simp only [hF, norm_mul, hnorm_cpow m t hm]
      ring_nf; rfl
    refine ((hKint.norm.const_mul (‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-c)))).mono'
      ((continuous_const.mul (hcp.mul hKcont)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbound)
  have hFnorm : ∀ m : ℕ, ∫ t, ‖F m t‖ =
      ‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-c) * ∫ t, ‖K t‖ := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, divisorCard]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hF, norm_mul, hnorm_cpow m t hm]
    ring
  have hFsum : Summable fun m => ∫ t, ‖F m t‖ := by
    simp_rw [hFnorm]
    exact (summable_norm_divisorCard_mul_rpow hc hn).mul_right _
  rw [show (∫ t : ℝ, Φ ((c : ℂ) + t * I)) = ∫ t : ℝ, ∑' m, F m t from
    integral_congr_ae (Filter.Eventually.of_forall hser),
    ← integral_tsum_of_summable_integral_norm hFint hFsum, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hI : (∫ y : ℝ, (((m * n : ℕ) : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) •
      (fun s => archXi s ^ 2 * R s) ((c : ℂ) + y * I)) =
      ∫ t : ℝ, ((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I)) * K t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hK, smul_eq_mul]
    push_cast
    ring_nf
  simp only [hF]
  rw [integral_const_mul, certKernelAt, mellinInv, hI, Complex.real_smul]
  push_cast
  field_simp
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [mul_comm I]

/-- **Blindness from a vanishing kernel at the abscissa `c > 1`.** -/
theorem logNode_blind_of_certKernelAt_vanishes (R : ℂ → ℂ) {c : ℝ} (hc : 1 < c)
    (hR : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → ‖xi s ^ 2 * R s‖ ≤ C / (1 + s.im ^ 2))
    {C' : ℝ} (hC' : ∀ t : ℝ, ‖archXi (c + t * I) ^ 2 * R (c + t * I)‖ ≤ C' / (1 + t ^ 2))
    (hvan : ∀ n : ℕ, 2 ≤ n → certKernelAt c R n = 0) (n : ℕ) (hn : 2 ≤ n) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-((t : ℂ) * I)) = 0 := by
  rw [integral_xi_sq_logNode R (by omega), integral_xi_sq_mul_cpow_eq_tsum_at R hc hR hC hC'
    (by omega)]
  have : (∑' m : ℕ, divisorCard m * certKernelAt c R ((m * n : ℕ) : ℝ)) = 0 := by
    refine (tsum_congr fun m => ?_).trans tsum_zero
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [divisorCard_zero]
    · have hmn : 2 ≤ m * n := le_trans hn (Nat.le_mul_of_pos_left n hm)
      rw [hvan _ hmn, mul_zero]
  rw [this, mul_zero, mul_zero]

end RHTower.ExactNullDivisorTransfer
